// Command minpeak computes the minimum peeling peak of a tensor
// decomposition for <3,3,3> matrix multiplication.
//
// The peeling peak of a rank-r decomposition T = sum(tau_k) is the
// maximum nnz (number of nonzero entries) of any residual
// T - tau_{sigma(1)} - ... - tau_{sigma(j)} over all j, for a given
// permutation sigma. The min-peak minimizes this over all r!
// permutations.
//
// Four analysis modes:
//
//   - calibrate: file-order peeling trajectory, checked against known
//     sequences (Laderman, Smirnov). Aborts on mismatch.
//
//   - sample: random-order peak sampling (100k permutations, 8 workers).
//     Reports min, median, max peak.
//
//   - greedy: greedy min-next-nnz heuristic with random tie-breaking
//     (1000 restarts). Reports best peak found.
//
//   - exact: gauge-invariant min-peak via iterative threshold-DFS with
//     dead-subset memoization over the 2^r subset lattice. Per-threshold
//     budget 60s.
//
// Input: one or more JSON decomposition files as positional arguments.
// JSON schema: {"name": str, "r": int, "S": int, "T": [[a,b,c,val],...],
// "terms": [[[a,b,c,val],...],...]}, produced by export_decomp.sage.
//
// Known-good exact min-peaks: Laderman=34, Smirnov-1=45, Smirnov-2=45.
//
// Usage:
//
//	minpeak [flags] file1.json [file2.json ...]
//	minpeak --mode=calibrate,exact laderman.json smirnov-1.json smirnov-2.json
package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"math"
	"math/rand/v2"
	"os"
	"sort"
	"strings"
	"sync"
	"time"
)

// entry is a single nonzero in a term tensor.
type entry struct {
	A, B, C int
	Val     int64
}

// decomp is the on-disk JSON representation.
type decomp struct {
	Name  string      `json:"name"`
	R     int         `json:"r"`
	S     int         `json:"S"`
	T     [][]int64   `json:"T"`
	Terms [][][]int64 `json:"terms"`
}

// algorithm is the parsed, flat representation used for computation.
type algorithm struct {
	Name  string
	R     int
	T     [729]int64 // flat 9x9x9
	Terms [][]entry  // per-term sparse entries
}

func idx(a, b, c int) int { return a*81 + b*9 + c }

func loadAlgorithm(path string) (algorithm, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return algorithm{}, fmt.Errorf("read %s: %w", path, err)
	}
	var d decomp
	if err := json.Unmarshal(data, &d); err != nil {
		return algorithm{}, fmt.Errorf("parse %s: %w", path, err)
	}
	var alg algorithm
	alg.Name = d.Name
	alg.R = d.R
	for _, e := range d.T {
		if len(e) != 4 {
			return algorithm{}, fmt.Errorf("bad T entry in %s", path)
		}
		alg.T[idx(int(e[0]), int(e[1]), int(e[2]))] = e[3]
	}
	alg.Terms = make([][]entry, d.R)
	for k, term := range d.Terms {
		for _, e := range term {
			if len(e) != 4 {
				return algorithm{}, fmt.Errorf("bad term entry in %s term %d", path, k)
			}
			alg.Terms[k] = append(alg.Terms[k], entry{
				A: int(e[0]), B: int(e[1]), C: int(e[2]), Val: e[3],
			})
		}
	}
	return alg, nil
}

// ---------------------------------------------------------------
// Residual operations
// ---------------------------------------------------------------

func nnz(r *[729]int64) int {
	n := 0
	for _, v := range r {
		if v != 0 {
			n++
		}
	}
	return n
}

func subtractTerm(res *[729]int64, term []entry) int {
	delta := 0
	for _, e := range term {
		i := idx(e.A, e.B, e.C)
		old := res[i]
		res[i] -= e.Val
		nw := res[i]
		if old == 0 && nw != 0 {
			delta++
		} else if old != 0 && nw == 0 {
			delta--
		}
	}
	return delta
}

func addTerm(res *[729]int64, term []entry) int {
	delta := 0
	for _, e := range term {
		i := idx(e.A, e.B, e.C)
		old := res[i]
		res[i] += e.Val
		nw := res[i]
		if old == 0 && nw != 0 {
			delta++
		} else if old != 0 && nw == 0 {
			delta--
		}
	}
	return delta
}

// ---------------------------------------------------------------
// Calibration: file-order trajectory
// ---------------------------------------------------------------

func fileOrderTrajectory(alg *algorithm) []int {
	var res [729]int64
	copy(res[:], alg.T[:])
	traj := make([]int, alg.R+1)
	traj[0] = nnz(&res)
	for k := 0; k < alg.R; k++ {
		subtractTerm(&res, alg.Terms[k])
		traj[k+1] = nnz(&res)
	}
	return traj
}

// ---------------------------------------------------------------
// Random order sampling
// ---------------------------------------------------------------

func randomOrderPeak(alg *algorithm, rng *rand.Rand) int {
	var res [729]int64
	copy(res[:], alg.T[:])
	perm := rng.Perm(alg.R)
	peak := nnz(&res)
	for _, k := range perm {
		subtractTerm(&res, alg.Terms[k])
		n := nnz(&res)
		if n > peak {
			peak = n
		}
	}
	return peak
}

func samplePeaks(ctx context.Context, alg *algorithm, nSamples int) (minP, medP, maxP int) {
	numWorkers := 8
	samplesPerWorker := nSamples / numWorkers
	var mu sync.Mutex
	peaks := make([]int, 0, nSamples)

	var wg sync.WaitGroup
	for w := 0; w < numWorkers; w++ {
		wg.Add(1)
		go func(seed uint64) {
			defer wg.Done()
			rng := rand.New(rand.NewPCG(seed, seed^0xdeadbeef))
			local := make([]int, 0, samplesPerWorker)
			for i := 0; i < samplesPerWorker; i++ {
				select {
				case <-ctx.Done():
					return
				default:
				}
				local = append(local, randomOrderPeak(alg, rng))
			}
			mu.Lock()
			peaks = append(peaks, local...)
			mu.Unlock()
		}(uint64(w * 12345))
	}
	wg.Wait()

	if len(peaks) == 0 {
		return 0, 0, 0
	}
	sort.Ints(peaks)
	return peaks[0], peaks[len(peaks)/2], peaks[len(peaks)-1]
}

// ---------------------------------------------------------------
// Greedy min-next-nnz with random tie-breaking
// ---------------------------------------------------------------

func greedyMinPeak(alg *algorithm, rng *rand.Rand) int {
	var res [729]int64
	copy(res[:], alg.T[:])
	used := make([]bool, alg.R)
	peak := nnz(&res)

	for step := 0; step < alg.R; step++ {
		bestNnz := math.MaxInt
		var candidates []int
		for k := 0; k < alg.R; k++ {
			if used[k] {
				continue
			}
			subtractTerm(&res, alg.Terms[k])
			n := nnz(&res)
			addTerm(&res, alg.Terms[k])
			if n < bestNnz {
				bestNnz = n
				candidates = candidates[:0]
				candidates = append(candidates, k)
			} else if n == bestNnz {
				candidates = append(candidates, k)
			}
		}
		chosen := candidates[rng.IntN(len(candidates))]
		used[chosen] = true
		subtractTerm(&res, alg.Terms[chosen])
		n := nnz(&res)
		if n > peak {
			peak = n
		}
	}
	return peak
}

func greedyBestSearch(ctx context.Context, alg *algorithm, restarts int) int {
	best := math.MaxInt
	for i := 0; i < restarts; i++ {
		select {
		case <-ctx.Done():
			return best
		default:
		}
		rng := rand.New(rand.NewPCG(uint64(i*7919), uint64(i*6271+1)))
		p := greedyMinPeak(alg, rng)
		if p < best {
			best = p
		}
	}
	return best
}

// ---------------------------------------------------------------
// Exact min-peak via iterative threshold DFS
// ---------------------------------------------------------------

type exactSearch struct {
	alg       *algorithm
	threshold int
	dead      map[uint32]struct{}
	found     bool
	deadline  time.Time
	states    int64
}

func (s *exactSearch) dfs(res *[729]int64, mask uint32, curNnz int, depth int) {
	if s.found || time.Now().After(s.deadline) {
		return
	}
	s.states++

	if depth == s.alg.R {
		if curNnz == 0 {
			s.found = true
		}
		return
	}

	for k := 0; k < s.alg.R; k++ {
		if mask&(1<<k) != 0 {
			continue
		}
		newMask := mask | (1 << k)

		if _, ok := s.dead[newMask]; ok {
			continue
		}

		delta := subtractTerm(res, s.alg.Terms[k])
		newNnz := curNnz + delta

		if newNnz <= s.threshold {
			s.dfs(res, newMask, newNnz, depth+1)
			if s.found {
				addTerm(res, s.alg.Terms[k])
				return
			}
		}

		addTerm(res, s.alg.Terms[k])
	}

	s.dead[mask] = struct{}{}
}

func exactMinPeak(ctx context.Context, alg *algorithm, upperBound int) (int, bool, int, int64) {
	largestInfeasible := 26
	totalStates := int64(0)

	for B := 27; B <= upperBound; B++ {
		select {
		case <-ctx.Done():
			return 0, false, largestInfeasible, totalStates
		default:
		}

		deadline := time.Now().Add(60 * time.Second)
		s := &exactSearch{
			alg:       alg,
			threshold: B,
			dead:      make(map[uint32]struct{}),
			deadline:  deadline,
		}

		var res [729]int64
		copy(res[:], alg.T[:])
		initNnz := nnz(&res)

		if initNnz > B {
			largestInfeasible = B
			continue
		}

		s.dfs(&res, 0, initNnz, 0)
		totalStates += s.states

		if s.found {
			return B, true, largestInfeasible, totalStates
		}

		if time.Now().After(deadline) {
			fmt.Fprintf(os.Stderr, "  %s: B=%d timed out (%d states, %d dead)\n",
				alg.Name, B, s.states, len(s.dead))
			return 0, false, largestInfeasible, totalStates
		}

		largestInfeasible = B
		fmt.Fprintf(os.Stderr, "  %s: B=%d infeasible (%d states, %d dead)\n",
			alg.Name, B, s.states, len(s.dead))
	}

	return upperBound, false, largestInfeasible, totalStates
}

// ---------------------------------------------------------------
// Mode set
// ---------------------------------------------------------------

type modeSet struct {
	Calibrate bool
	Sample    bool
	Greedy    bool
	Exact     bool
}

func parseModes(s string) (modeSet, error) {
	if s == "all" || s == "" {
		return modeSet{true, true, true, true}, nil
	}
	var m modeSet
	for _, part := range strings.Split(s, ",") {
		switch strings.TrimSpace(part) {
		case "calibrate":
			m.Calibrate = true
		case "sample":
			m.Sample = true
		case "greedy":
			m.Greedy = true
		case "exact":
			m.Exact = true
		default:
			return modeSet{}, fmt.Errorf("unknown mode %q", part)
		}
	}
	return m, nil
}

// ---------------------------------------------------------------
// Main
// ---------------------------------------------------------------

func main() {
	var (
		modeFlag    = flag.String("mode", "all", "comma-separated modes: calibrate,sample,greedy,exact (default: all)")
		timeout     = flag.Duration("timeout", 10*time.Minute, "global timeout")
	)
	flag.Parse()

	if flag.NArg() == 0 {
		fmt.Fprintf(os.Stderr, "usage: minpeak [flags] file1.json [file2.json ...]\n")
		flag.PrintDefaults()
		os.Exit(1)
	}

	modes, err := parseModes(*modeFlag)
	if err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}

	ctx, cancel := context.WithTimeout(context.Background(), *timeout)
	defer cancel()

	startAll := time.Now()

	// Load all algorithms.
	algs := make([]algorithm, 0, flag.NArg())
	for _, path := range flag.Args() {
		alg, err := loadAlgorithm(path)
		if err != nil {
			fmt.Fprintf(os.Stderr, "error: %v\n", err)
			os.Exit(1)
		}
		algs = append(algs, alg)
	}

	// Known calibration sequences.
	type calibExpect struct {
		Name string
		Traj []int
	}
	calibExpects := []calibExpect{
		{"Laderman", []int{27, 32, 38, 43, 38, 30, 29, 43, 36, 28, 27, 26, 34, 27, 26, 18, 20, 13, 5, 4, 3, 2, 1, 0}},
		{"Smirnov-1", []int{27, 48, 70, 86, 97, 79, 56, 27, 39, 51, 63, 51, 39, 27, 39, 51, 63, 49, 35, 21, 15, 9, 3, 2, 1, 0}},
	}

	// File-order peaks are needed for summary and as upper bounds for exact.
	fileOrderPeaks := make([]int, len(algs))
	for i := range algs {
		traj := fileOrderTrajectory(&algs[i])
		for _, v := range traj {
			if v > fileOrderPeaks[i] {
				fileOrderPeaks[i] = v
			}
		}
	}

	// ----- Calibration -----
	if modes.Calibrate {
		fmt.Println("=== CALIBRATION ===")
		calibOK := true
		for _, alg := range algs {
			traj := fileOrderTrajectory(&alg)
			peak := 0
			for _, v := range traj {
				if v > peak {
					peak = v
				}
			}
			fmt.Printf("%-12s traj=%v  peak=%d\n", alg.Name, traj, peak)

			for _, ce := range calibExpects {
				if ce.Name == alg.Name {
					if len(traj) != len(ce.Traj) {
						fmt.Printf("  CALIB FAIL: len %d vs expected %d\n", len(traj), len(ce.Traj))
						calibOK = false
						continue
					}
					for j := range traj {
						if traj[j] != ce.Traj[j] {
							fmt.Printf("  CALIB FAIL at [%d]: got %d, expected %d\n", j, traj[j], ce.Traj[j])
							calibOK = false
						}
					}
				}
			}
		}

		// Smirnov-2: check peak = 97.
		for i := range algs {
			if algs[i].Name == "Smirnov-2" && fileOrderPeaks[i] != 97 {
				fmt.Printf("  CALIB FAIL: Smirnov-2 peak %d, expected 97\n", fileOrderPeaks[i])
				calibOK = false
			}
		}

		if !calibOK {
			fmt.Println("CALIBRATION FAILED -- aborting")
			os.Exit(1)
		}
		fmt.Println("CALIBRATION PASSED")
		fmt.Println()
	}

	// ----- Random sampling -----
	sampledMin := make([]int, len(algs))
	sampledMed := make([]int, len(algs))
	sampledMax := make([]int, len(algs))
	if modes.Sample {
		fmt.Println("=== RANDOM SAMPLING (100k orders) ===")
		for i := range algs {
			select {
			case <-ctx.Done():
				fmt.Println("Timeout during sampling")
			default:
			}
			t0 := time.Now()
			sampledMin[i], sampledMed[i], sampledMax[i] = samplePeaks(ctx, &algs[i], 100000)
			fmt.Printf("%-12s min=%d  median=%d  max=%d  (%.1fs)\n",
				algs[i].Name, sampledMin[i], sampledMed[i], sampledMax[i],
				time.Since(t0).Seconds())
		}
		fmt.Println()
	}

	// ----- Greedy -----
	greedyBests := make([]int, len(algs))
	if modes.Greedy {
		fmt.Println("=== GREEDY MIN-NEXT-NNZ (1000 restarts) ===")
		for i := range algs {
			select {
			case <-ctx.Done():
				fmt.Println("Timeout during greedy")
			default:
			}
			t0 := time.Now()
			greedyBests[i] = greedyBestSearch(ctx, &algs[i], 1000)
			fmt.Printf("%-12s best_peak=%d  (%.1fs)\n",
				algs[i].Name, greedyBests[i], time.Since(t0).Seconds())
		}
		fmt.Println()
	}

	// ----- Exact min-peak -----
	type exactResult struct {
		Peak          int
		Exact         bool
		LargestInfeas int
		States        int64
	}
	exactResults := make([]exactResult, len(algs))
	if modes.Exact {
		fmt.Println("=== EXACT MIN-PEAK SEARCH ===")
		for i := range algs {
			select {
			case <-ctx.Done():
				fmt.Printf("%-12s TIMEOUT before starting\n", algs[i].Name)
				continue
			default:
			}
			t0 := time.Now()
			ub := greedyBests[i]
			if ub == 0 || ub > 200 {
				ub = fileOrderPeaks[i]
			}
			if ub == 0 || ub > 200 {
				ub = 200
			}
			peak, exact, largestInfeas, states := exactMinPeak(ctx, &algs[i], ub)
			exactResults[i] = exactResult{peak, exact, largestInfeas, states}
			if exact {
				fmt.Printf("%-12s EXACT min-peak = %d  (%d states, %.1fs)\n",
					algs[i].Name, peak, states, time.Since(t0).Seconds())
			} else {
				fmt.Printf("%-12s BRACKET [%d, %d]  (%d states, %.1fs)\n",
					algs[i].Name, largestInfeas+1, ub,
					states, time.Since(t0).Seconds())
			}
		}
		fmt.Println()
	}

	// ----- Summary table -----
	fmt.Println("=== SUMMARY ===")
	fmt.Printf("%-12s  %4s  %9s  %6s  %19s  %18s\n",
		"Algorithm", "Rank", "File-Peak", "Greedy", "Sampled(min/med/max)", "Exact/Bracket")
	fmt.Printf("%-12s  %4s  %9s  %6s  %19s  %18s\n",
		"------------", "----", "---------", "------", "-------------------", "------------------")
	for i := range algs {
		var exactStr string
		if exactResults[i].Exact {
			exactStr = fmt.Sprintf("%d (exact)", exactResults[i].Peak)
		} else if exactResults[i].LargestInfeas > 0 {
			ub := greedyBests[i]
			if ub == 0 {
				ub = fileOrderPeaks[i]
			}
			if ub == 0 {
				ub = 200
			}
			exactStr = fmt.Sprintf("[%d, %d]", exactResults[i].LargestInfeas+1, ub)
		} else {
			exactStr = "N/A"
		}
		fmt.Printf("%-12s  %4d  %9d  %6d   %4d / %4d / %4d  %18s\n",
			algs[i].Name, algs[i].R, fileOrderPeaks[i], greedyBests[i],
			sampledMin[i], sampledMed[i], sampledMax[i],
			exactStr)
	}

	fmt.Printf("\nTotal wall-clock: %.1fs\n", time.Since(startAll).Seconds())
}
