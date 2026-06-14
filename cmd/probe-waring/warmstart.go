package main

import (
	"context"
	"fmt"
	"math"
	"math/cmplx"
	"math/rand/v2"
	"os"
	"runtime"
	"sync"
	"time"
)

// warmStartSearch attempts to find a rank-(r) decomposition by starting from
// the known rank-18 Conner decomposition and removing summands down to r, then
// re-optimizing. This is the structured ansatz: a rank-17 (or lower) solution,
// if it lies on the boundary of the rank-18 variety, is plausibly reachable by
// continuously deforming the 18-summand solution after dropping one summand.
//
// Strategies tried per restart:
//   - drop a random subset of (18-r) summands, jitter the rest, re-optimize.
//   - additionally try "merging": replace two summands by their sum direction.
func warmStartSearch(r int, timeout time.Duration, restarts, maxIter int, tol float64, rng *rand.Rand, verbose bool) rankResult {
	ctx, cancel := context.WithTimeout(context.Background(), timeout)
	defer cancel()

	p := newProblem(r)
	start := time.Now()

	// build the rank-18 oracle forms scaled so sum L^3 = tr(A^3).
	scale := complex(math.Pow(6, -1.0/3.0), 0)
	forms := oracleForms()
	base := make([][N]complex128, 18)
	for k, m := range forms {
		c := frobLin(m)
		for v := 0; v < N; v++ {
			base[k][v] = c[v] * scale
		}
	}

	workers := runtime.GOMAXPROCS(0)
	if workers > restarts {
		workers = restarts
	}
	if workers < 1 {
		workers = 1
	}

	var mu sync.Mutex
	best := math.Inf(1)
	var bestX []float64
	used := 0
	var cand *candidate
	baseSeed := rng.Uint64()

	var wg sync.WaitGroup
	for w := 0; w < workers; w++ {
		wg.Add(1)
		go func(wid int) {
			defer wg.Done()
			wrng := rand.New(rand.NewPCG(baseSeed+uint64(wid)*0x100000001b3, baseSeed^uint64(wid)+7))
			for i := wid; i < restarts; i += workers {
				select {
				case <-ctx.Done():
					return
				default:
				}
				x0 := warmStartVec(p, base, wrng)
				res := levenbergMarquardt(p, x0, maxIter, tol)

				mu.Lock()
				used++
				if res.resNorm < best {
					best = res.resNorm
					bestX = res.x
				}
				if verbose && used%200 == 0 {
					fmt.Fprintf(os.Stderr, "  [warm] rank %d restart %d: best=%.4e\n", r, used, best)
				}
				mu.Unlock()

				if res.resNorm < tol {
					polish := levenbergMarquardt(p, res.x, maxIter, tol*1e-2)
					cx, cn := res.x, res.resNorm
					if polish.resNorm < cn {
						cx, cn = polish.x, polish.resNorm
					}
					c := buildCandidate(p, cx, cn)
					mu.Lock()
					if cand == nil {
						cand = c
						best = cn
						bestX = cx
					}
					mu.Unlock()
					cancel()
					return
				}
			}
		}(w)
	}
	wg.Wait()

	rr := rankResult{
		Rank:         r,
		RestartsUsed: used,
		BestResNorm:  best,
		Seconds:      time.Since(start).Seconds(),
		Candidate:    cand,
	}
	if bestX != nil {
		rr.BestForms = formsOf(p, bestX)
	}
	return rr
}

// warmStartVec produces a length-(2*r*N) initial guess by selecting r of the
// 18 base summands at random and jittering them. The deficit (18-r) is handled
// by simply dropping summands; the residual of the resulting rank-r start is
// nonzero, and LM is asked to close it.
func warmStartVec(p *problem, base [][N]complex128, rng *rand.Rand) []float64 {
	// random permutation of the 18 indices; keep first r
	perm := rng.Perm(len(base))
	keep := perm[:p.r]
	x := make([]float64, p.nVars())
	jitter := 0.15
	for slot, bi := range keep {
		for v := 0; v < N; v++ {
			c := base[bi][v]
			c += complex(rng.NormFloat64()*jitter, rng.NormFloat64()*jitter)
			idx := 2 * (slot*N + v)
			x[idx] = real(c)
			x[idx+1] = imag(c)
		}
	}
	return x
}

// _ keeps cmplx imported even if unused after refactors.
var _ = cmplx.Abs
