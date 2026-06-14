package main

import (
	"context"
	"fmt"
	"sync"
)

// legSymmetry implements task STEP 2(c): build the tangency (mixed) flattening
// with the wedge on leg 0, 1, 2 of M_n; by the Z_3 cyclic symmetry all three
// ranks must agree. Disagreement => construction bug => stop. We also run the
// byleg flattening for completeness. Done at d'=3 and d'=4.
func legSymmetry(ctx context.Context, o *output, n int) error {
	dW := n * n
	for _, dPrime := range []int{3, 4} {
		for _, spec := range []flatSpec{specMixed, specByLeg} {
			if err := deadline(ctx); err != nil {
				return err
			}
			var ranks [3]int
			var wg sync.WaitGroup
			for leg := 0; leg < 3; leg++ {
				wg.Add(1)
				go func(leg int) {
					defer wg.Done()
					dense := mnDenseLeg(n, leg)
					M := buildFlatteningModP(dW, dW, dW, dense, dPrime, spec)
					ranks[leg] = rankModPU(M)
				}(leg)
			}
			wg.Wait()
			agree := ranks[0] == ranks[1] && ranks[1] == ranks[2]
			o.LegAgree = append(o.LegAgree, legAgreement{DPrime: dPrime, Spec: spec.String(), LegW: ranks, Agree: agree})
			fmt.Printf("leg-symmetry d'=%d spec=%s: ranks=%v agree=%v\n", dPrime, spec, ranks, agree)
			if !agree {
				return fmt.Errorf("LEG-SYMMETRY FAILED d'=%d spec=%s: ranks %v disagree; M_n cyclic symmetry violated => construction bug. Halting per doctrine",
					dPrime, spec, ranks)
			}
		}
	}
	return nil
}

// headlineRank computes the M_n flattening rank for a given spec at d' over the
// primary prime 2^61-1 and the small cross-check primes, in parallel (one
// goroutine per prime). Wedge on leg 0 (all legs agree by legSymmetry).
func headlineRank(ctx context.Context, n, dPrime int, spec flatSpec) rankResult {
	dW := n * n
	dense := mnDenseLeg(n, 0)
	rows := int(binom(dW, dPrime+2)) * dW * dW
	cols := int(binom(dW, dPrime)) * dW * dW

	rr := rankResult{
		DPrime: dPrime, Spec: spec.String(), Rows: rows, Cols: cols,
		RankSmall: map[string]int{},
	}

	var wg sync.WaitGroup
	var mu sync.Mutex

	wg.Add(1)
	go func() {
		defer wg.Done()
		M := buildFlatteningModP(dW, dW, dW, dense, dPrime, spec)
		rk := rankModPU(M)
		mu.Lock()
		rr.RankModP = rk
		mu.Unlock()
	}()
	for _, p := range crossPrimes {
		wg.Add(1)
		go func(p uint64) {
			defer wg.Done()
			M := buildFlatteningSmallP(dW, dW, dW, dense, dPrime, spec, p)
			rk := rankModSmall(M, p)
			mu.Lock()
			rr.RankSmall[fmt.Sprintf("%d", p)] = rk
			mu.Unlock()
		}(p)
	}
	wg.Wait()

	allAgree := true
	for _, rk := range rr.RankSmall {
		if rk != rr.RankModP {
			allAgree = false
		}
	}
	rr.AllAgree = allAgree
	return rr
}
