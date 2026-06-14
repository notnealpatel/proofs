// Command probe-waring searches for low-rank Waring decompositions of the
// cubic form sM_3 = tr(A^3) in the 9 entries of a 3x3 matrix A.
//
// Background (Wd1 task; gate verdict GO-MODIFIED from Sm1 infodump): the
// proven gap for R_s(sM_3) is 14 <= R_s(sM_3) <= 18. Conner (arXiv:1711.05796)
// gives an explicit rank-18 decomposition; 1706.05074 Conjecture 3.1 asserts
// R_s(sM_3) = 18. A certified decomposition of rank <= 17 refutes that
// conjecture. We search ranks 14, 15, 16, 17 (in that order of decisiveness)
// via Levenberg-Marquardt NLS with many random restarts.
package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"math"
	"math/cmplx"
	"math/rand/v2"
	"os"
	"runtime"
	"sync"
	"time"
)

func main() {
	var (
		ranksFlag = flag.String("ranks", "14,15,16,17", "comma-separated ranks to search")
		timeout   = flag.Duration("timeout", 5*time.Minute, "wall-clock budget per rank")
		restarts  = flag.Int("restarts", 2000, "max random restarts per rank")
		maxIter   = flag.Int("maxiter", 400, "max LM iterations per restart")
		seed      = flag.Uint64("seed", 1, "RNG seed")
		tol       = flag.Float64("tol", 1e-12, "residual-norm candidate threshold")
		out       = flag.String("out", "", "write JSON results to this path")
		selftest  = flag.Bool("selftest", true, "run oracle + planted self-tests first")
		verbose   = flag.Bool("v", false, "verbose per-restart logging")
		warm      = flag.Bool("warm", false, "use warm-start ansatz (drop summands from rank-18 oracle)")
	)
	flag.Parse()

	results := &runResults{
		StartedAt: time.Now().Format(time.RFC3339),
		Seed:      *seed,
		Timeout:   timeout.String(),
		Restarts:  *restarts,
		MaxIter:   *maxIter,
		Tol:       *tol,
	}

	if *selftest {
		st := runSelfTests()
		results.SelfTests = st
		if !st.OraclePass || !st.PlantedPass {
			fmt.Fprintf(os.Stderr, "SELF-TEST FAILED: oracle=%v planted=%v\n", st.OraclePass, st.PlantedPass)
			emit(results, *out)
			os.Exit(1)
		}
		fmt.Fprintf(os.Stderr, "self-tests passed: oracle resNorm=%.3e planted resNorm=%.3e\n",
			st.OracleResNorm, st.PlantedResNorm)
	}

	ranks := parseRanks(*ranksFlag)
	rng := rand.New(rand.NewPCG(*seed, *seed^0x9e3779b97f4a7c15))

	for _, r := range ranks {
		var rr rankResult
		if *warm {
			rr = warmStartSearch(r, *timeout, *restarts, *maxIter, *tol, rng, *verbose)
		} else {
			rr = searchRank(r, *timeout, *restarts, *maxIter, *tol, rng, *verbose)
		}
		results.Ranks = append(results.Ranks, rr)
		fmt.Fprintf(os.Stderr,
			"rank %d: restarts=%d best resNorm=%.6e candidate=%v (in %.1fs)\n",
			r, rr.RestartsUsed, rr.BestResNorm, rr.Candidate != nil, rr.Seconds)
		if rr.Candidate != nil {
			fmt.Fprintf(os.Stderr, "  *** CANDIDATE at rank %d, resNorm=%.3e ***\n", r, rr.Candidate.ResNorm)
		}
	}

	results.FinishedAt = time.Now().Format(time.RFC3339)
	emit(results, *out)
}

func parseRanks(s string) []int {
	var out []int
	cur := 0
	have := false
	for _, ch := range s {
		if ch >= '0' && ch <= '9' {
			cur = cur*10 + int(ch-'0')
			have = true
		} else if ch == ',' {
			if have {
				out = append(out, cur)
			}
			cur = 0
			have = false
		}
	}
	if have {
		out = append(out, cur)
	}
	return out
}

// searchRank performs parallel random-restart LM for a given rank within the
// budget. Restarts are distributed across GOMAXPROCS workers; the first
// sub-tol result triggers cancellation of the rest.
func searchRank(r int, timeout time.Duration, restarts, maxIter int, tol float64, rng *rand.Rand, verbose bool) rankResult {
	ctx, cancel := context.WithTimeout(context.Background(), timeout)
	defer cancel()

	p := newProblem(r)
	start := time.Now()

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
			wrng := rand.New(rand.NewPCG(baseSeed+uint64(wid)*0x100000001b3, baseSeed^uint64(wid)+1))
			for i := wid; i < restarts; i += workers {
				select {
				case <-ctx.Done():
					return
				default:
				}
				x0 := randomStart(p, wrng, 1.0)
				res := levenbergMarquardt(p, x0, maxIter, tol)

				mu.Lock()
				used++
				if res.resNorm < best {
					best = res.resNorm
					bestX = res.x
				}
				if verbose && used%500 == 0 {
					fmt.Fprintf(os.Stderr, "  rank %d restart %d: best=%.4e\n", r, used, best)
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

func formsOf(p *problem, x []float64) [][]cplx {
	L := p.unpack(x)
	out := make([][]cplx, len(L))
	for k := range L {
		row := make([]cplx, N)
		for v := 0; v < N; v++ {
			row[v] = cplx{real(L[k][v]), imag(L[k][v])}
		}
		out[k] = row
	}
	return out
}

func buildCandidate(p *problem, x []float64, resNorm float64) *candidate {
	c := &candidate{
		ResNorm: resNorm,
		Forms:   formsOf(p, x),
	}
	// attempt rational reconstruction / exact certification
	cert := certify(p, x)
	c.Certification = cert
	return c
}

func emit(r *runResults, out string) {
	b, err := json.MarshalIndent(r, "", "  ")
	if err != nil {
		fmt.Fprintf(os.Stderr, "json marshal error: %v\n", err)
		return
	}
	if out != "" {
		if err := os.WriteFile(out, b, 0o644); err != nil {
			fmt.Fprintf(os.Stderr, "write %s: %v\n", out, err)
		}
	}
	fmt.Println(string(b))
}

// --- JSON result types ---

type cplx struct {
	Re float64 `json:"re"`
	Im float64 `json:"im"`
}

type runResults struct {
	StartedAt  string       `json:"started_at"`
	FinishedAt string       `json:"finished_at"`
	Seed       uint64       `json:"seed"`
	Timeout    string       `json:"timeout_per_rank"`
	Restarts   int          `json:"max_restarts"`
	MaxIter    int          `json:"max_iter"`
	Tol        float64      `json:"tol"`
	SelfTests  *selfTests   `json:"self_tests"`
	Ranks      []rankResult `json:"ranks"`
}

type selfTests struct {
	OraclePass     bool    `json:"oracle_pass"`
	OracleResNorm  float64 `json:"oracle_res_norm"`
	PlantedPass    bool    `json:"planted_pass"`
	PlantedResNorm float64 `json:"planted_res_norm"`
	PlantedRank    int     `json:"planted_rank"`
}

type rankResult struct {
	Rank         int        `json:"rank"`
	RestartsUsed int        `json:"restarts_used"`
	BestResNorm  float64    `json:"best_res_norm"`
	Seconds      float64    `json:"seconds"`
	Candidate    *candidate `json:"candidate"`
	BestForms    [][]cplx   `json:"best_forms,omitempty"`
}

type candidate struct {
	ResNorm       float64        `json:"res_norm"`
	Forms         [][]cplx       `json:"forms"`
	Certification *certResult    `json:"certification"`
	Note          string         `json:"note,omitempty"`
	Extra         map[string]any `json:"extra,omitempty"`
}

// runSelfTests verifies (a) the 1711.05796 rank-18 oracle reproduces tr(A^3)
// exactly and (b) the searcher recovers a planted random rank-r sum of cubes.
func runSelfTests() *selfTests {
	st := &selfTests{}

	// (a) oracle: scale the 18 forms by 6^{-1/3} so sum L^3 = tr(A^3).
	p := newProblem(18)
	scale := complex(math.Pow(6, -1.0/3.0), 0)
	forms := oracleForms()
	L := make([][N]complex128, 18)
	for k, m := range forms {
		c := frobLin(m)
		for v := 0; v < N; v++ {
			L[k][v] = c[v] * scale
		}
	}
	res := cubeResidual(L, p.F, p.ts)
	st.OracleResNorm = residualNorm(res)
	st.OraclePass = st.OracleResNorm < 1e-9

	// (b) planted: build a random rank-15 complex sum of cubes, then ask the
	// searcher to recover it from random restarts.
	rng := rand.New(rand.NewPCG(42, 1234567))
	plantedRank := 15
	st.PlantedRank = plantedRank
	planted := make([][N]complex128, plantedRank)
	for k := 0; k < plantedRank; k++ {
		for v := 0; v < N; v++ {
			planted[k][v] = complex(rng.NormFloat64(), 0.3*rng.NormFloat64())
		}
	}
	pp := newProblemFromForms(plantedRank, planted)
	bestRes := math.Inf(1)
	for restart := 0; restart < 400; restart++ {
		x0 := randomStart(pp, rng, 1.0)
		r := levenbergMarquardt(pp, x0, 400, 1e-12)
		if r.resNorm < bestRes {
			bestRes = r.resNorm
		}
		if bestRes < 1e-12 {
			break
		}
	}
	st.PlantedResNorm = bestRes
	st.PlantedPass = bestRes < 1e-10
	return st
}

// newProblemFromForms builds a problem whose target tensor is sum_k forms[k]^3
// (used for planted-solution calibration).
func newProblemFromForms(r int, forms [][N]complex128) *problem {
	ts := triples()
	F := make(map[triple]complex128, len(ts))
	for _, t := range ts {
		var s complex128
		for _, c := range forms {
			s += c[t.a] * c[t.b] * c[t.c]
		}
		F[t] = s
	}
	fre := make([]float64, len(ts))
	fim := make([]float64, len(ts))
	for i, t := range ts {
		fre[i] = real(F[t])
		fim[i] = imag(F[t])
	}
	return &problem{r: r, ts: ts, F: F, Fre: fre, Fim: fim}
}

// oracleForms returns the 18 matrices m_i of Conner's decomposition.
// Note: the paper text prints a = -2^{-1/3}, but numerical verification shows
// the scalar summand must satisfy a^3 = -2, i.e. a = -2^{1/3}. We use that.
func oracleForms() [][3][3]complex128 {
	zeta := cmplx.Exp(complex(0, 2*math.Pi/3))
	z2 := zeta * zeta
	a := complex(-1, 0) * cmplx.Pow(2, complex(1.0/3.0, 0)) // a = -2^{1/3}, a^3 = -2
	return [][3][3]complex128{
		{{1, -1, 0}, {-1, 1, 0}, {0, 0, 0}},
		{{0, 0, 0}, {0, 1, -zeta}, {0, -z2, 1}},
		{{1, 0, -zeta}, {0, 0, 0}, {-z2, 0, 1}},
		{{0, 0, 0}, {0, 1, -z2}, {0, -zeta, 1}},
		{{1, 0, -1}, {0, 0, 0}, {-1, 0, 1}},
		{{1, -zeta, 0}, {-z2, 1, 0}, {0, 0, 0}},
		{{1, 0, -z2}, {0, 0, 0}, {-zeta, 0, 1}},
		{{1, -z2, 0}, {-zeta, 1, 0}, {0, 0, 0}},
		{{0, 0, 0}, {0, 1, -1}, {0, -1, 1}},
		{{a, 0, 0}, {0, a, 0}, {0, 0, a}},
		{{0, 1, 0}, {0, 0, zeta}, {z2, 0, 0}},
		{{0, 0, 1}, {z2, 0, 0}, {0, zeta, 0}},
		{{0, 1, 0}, {0, 0, z2}, {zeta, 0, 0}},
		{{0, 0, 1}, {1, 0, 0}, {0, 1, 0}},
		{{1, 0, 0}, {0, zeta, 0}, {0, 0, z2}},
		{{0, 0, 1}, {zeta, 0, 0}, {0, z2, 0}},
		{{1, 0, 0}, {0, z2, 0}, {0, 0, zeta}},
		{{0, 1, 0}, {0, 0, 1}, {1, 0, 0}},
	}
}
