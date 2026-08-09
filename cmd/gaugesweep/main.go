// Command gaugesweep sweeps the full sandwich-gauge orbit of Laderman's
// rank-23 decomposition of <3,3,3> over F_2.
//
// It enumerates all sandwich triples (X,Y,Z) in GL(3,F_2)^3 (168^3 =
// 4,741,632), applies each to the decomposition reduced mod 2, dedupes
// the distinct copies, and computes for each: exact min-peak up to a
// threshold cap (threshold-DFS with a lazily-cleared dead-subset bitset
// over the 2^23 lattice, bit-packed F_2 residuals) and total factor nnz.
// Copies whose min-peak exceeds -cap are bucketed as "over cap" rather
// than chased to their exact value; raise -cap for a fuller distribution
// at superlinear cost.
//
// Slot moves are omitted: they permute tensor axes and leave every
// nnz-based statistic invariant.
//
// Convention: T[(3i+j, 3j+k, 3i+k)] = 1 (project convention; C indexed
// (i,k) row-major). Gauge action derived from the trace form:
//   u' = X u Y^-1,  v' = Y v Z^-1,  w' = X^-T w Z^T.
// The base copy and sampled gauged copies are asserted to sum to T mod 2.
//
// Known-good results (2026-07-20, -cap 34): orbit = 1,185,408 distinct
// copies (sandwich stabilizer of order 4 = Burichenko's V in SL3^3);
// orbit min-peak 33 (648 copies), published-gauge min-peak 34 (54
// copies), all other copies proven > 34; orbit factor-nnz minimum 153 =
// published gauge.
package main

import (
	"context"
	"flag"
	"fmt"
	"math"
	"math/bits"
	"os"
	"os/signal"
	"runtime"
	"sort"
	"sync"
	"time"
)

// ---------------- 3x3 matrices over F_2, packed into 9 bits ----------------

// mat3 holds bit (3*r+c) for entry (r,c).
type mat3 uint16

func matFromRows(rows [3][3]int) mat3 {
	var m mat3
	for r := 0; r < 3; r++ {
		for c := 0; c < 3; c++ {
			if rows[r][c]&1 != 0 {
				m |= 1 << (3*r + c)
			}
		}
	}
	return m
}

func (m mat3) get(r, c int) int { return int(m>>(3*r+c)) & 1 }

func (m mat3) mul(n mat3) mat3 {
	var out mat3
	for r := 0; r < 3; r++ {
		for c := 0; c < 3; c++ {
			b := 0
			for k := 0; k < 3; k++ {
				b ^= m.get(r, k) & n.get(k, c)
			}
			if b != 0 {
				out |= 1 << (3*r + c)
			}
		}
	}
	return out
}

func (m mat3) transpose() mat3 {
	var out mat3
	for r := 0; r < 3; r++ {
		for c := 0; c < 3; c++ {
			if m.get(r, c) != 0 {
				out |= 1 << (3*c + r)
			}
		}
	}
	return out
}

func (m mat3) det() int {
	a := m.get(0, 0)&m.get(1, 1)&m.get(2, 2) ^ m.get(0, 1)&m.get(1, 2)&m.get(2, 0) ^ m.get(0, 2)&m.get(1, 0)&m.get(2, 1)
	b := m.get(0, 2)&m.get(1, 1)&m.get(2, 0) ^ m.get(0, 0)&m.get(1, 2)&m.get(2, 1) ^ m.get(0, 1)&m.get(1, 0)&m.get(2, 2)
	return a ^ b
}

const identity mat3 = 1<<0 | 1<<4 | 1<<8

func gl3f2() []mat3 {
	var out []mat3
	for v := 0; v < 512; v++ {
		m := mat3(v)
		if m.det() == 1 {
			out = append(out, m)
		}
	}
	return out
}

// invTable maps each GL(3,F_2) element to its inverse.
func invTable(gl []mat3) map[mat3]mat3 {
	inv := make(map[mat3]mat3, len(gl))
	for _, m := range gl {
		if _, done := inv[m]; done {
			continue
		}
		for _, n := range gl {
			if m.mul(n) == identity {
				inv[m] = n
				inv[n] = m
				break
			}
		}
	}
	return inv
}

// ---------------- Laderman factor matrices (mod 2) ----------------

// Rows of the 23x9 U and V listings from Scratch/residual_trajectory.sage;
// each row reshapes row-major to the 3x3 factor of that term. W is listed
// 9x23; column t reshapes row-major to the C-factor (index (i,k)).

var uRows = [23][9]int{
	{1, -1, -1, 1, -1, 0, 0, -1, -1},
	{1, 0, 0, 1, 0, 0, 0, 0, 0},
	{0, 0, 0, 0, 1, 0, 0, 0, 0},
	{-1, 0, 0, -1, 1, 0, 0, 0, 0},
	{0, 0, 0, -1, 1, 0, 0, 0, 0},
	{1, 0, 0, 0, 0, 0, 0, 0, 0},
	{1, 0, 0, 0, 0, 0, 1, 1, 0},
	{1, 0, 0, 0, 0, 0, 1, 0, 0},
	{0, 0, 0, 0, 0, 0, 1, 1, 0},
	{1, 1, -1, 0, -1, 1, 1, 1, 0},
	{0, 0, 0, 0, 0, 0, 0, 1, 0},
	{0, 0, 1, 0, 0, 0, 0, 1, 1},
	{0, 0, 1, 0, 0, 0, 0, 0, 1},
	{0, 0, 1, 0, 0, 0, 0, 0, 0},
	{0, 0, 0, 0, 0, 0, 0, -1, -1},
	{0, 0, 1, 0, 1, -1, 0, 0, 0},
	{0, 0, -1, 0, 0, 1, 0, 0, 0},
	{0, 0, 0, 0, 1, -1, 0, 0, 0},
	{0, 1, 0, 0, 0, 0, 0, 0, 0},
	{0, 0, 0, 0, 0, 1, 0, 0, 0},
	{0, 0, 0, 1, 0, 0, 0, 0, 0},
	{0, 0, 0, 0, 0, 0, 1, 0, 0},
	{0, 0, 0, 0, 0, 0, 0, 0, 1},
}

var vRows = [23][9]int{
	{0, 0, 0, 0, -1, 0, 0, 0, 0},
	{0, 1, 0, 0, 1, 0, 0, 0, 0},
	{1, -1, 0, 1, -1, -1, 1, 0, -1},
	{-1, 1, 0, 0, 1, 0, 0, 0, 0},
	{-1, 1, 0, 0, 0, 0, 0, 0, 0},
	{-1, 0, 0, 0, 0, 0, 0, 0, 0},
	{1, 0, -1, 0, 0, 1, 0, 0, 0},
	{0, 0, -1, 0, 0, 1, 0, 0, 0},
	{1, 0, -1, 0, 0, 0, 0, 0, 0},
	{0, 0, 0, 0, 0, 1, 0, 0, 0},
	{-1, 0, 1, 1, -1, -1, -1, 1, 0},
	{0, 0, 0, 0, 1, 0, 1, -1, 0},
	{0, 0, 0, 0, -1, 0, 0, 1, 0},
	{0, 0, 0, 0, 0, 0, 1, 0, 0},
	{0, 0, 0, 0, 0, 0, -1, 1, 0},
	{0, 0, 0, 0, 0, 1, -1, 0, 1},
	{0, 0, 0, 0, 0, 1, 0, 0, 1},
	{0, 0, 0, 0, 0, 0, 1, 0, -1},
	{0, 0, 0, 1, 0, 0, 0, 0, 0},
	{0, 0, 0, 0, 0, 0, 0, 1, 0},
	{0, 0, 1, 0, 0, 0, 0, 0, 0},
	{0, 1, 0, 0, 0, 0, 0, 0, 0},
	{0, 0, 0, 0, 0, 0, 0, 0, 1},
}

var wRows = [9][23]int{
	{0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0},
	{1, 0, 0, -1, 1, -1, 0, 0, 0, 0, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0},
	{0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0},
	{0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0},
	{0, 1, 0, 1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0},
	{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0},
	{0, 0, 0, 0, 0, 1, 1, -1, 0, 0, 1, 1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0},
	{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, -1, -1, 0, 0, 0, 0, 0, 0, 1, 0},
	{0, 0, 0, 0, 0, 1, 1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1},
}

const rank = 23

type triple struct{ u, v, w mat3 }

func ladermanTerms() [rank]triple {
	var out [rank]triple
	for t := 0; t < rank; t++ {
		var ur, vr, wr [3][3]int
		for r := 0; r < 3; r++ {
			for c := 0; c < 3; c++ {
				ur[r][c] = uRows[t][3*r+c]
				vr[r][c] = vRows[t][3*r+c]
				wr[r][c] = wRows[3*r+c][t]
			}
		}
		out[t] = triple{matFromRows(ur), matFromRows(vr), matFromRows(wr)}
	}
	return out
}

// ---------------- Tensor kernel: 729 bits in 12 words ----------------

const f2Words = (729 + 63) / 64

type f2Tensor [f2Words]uint64

func tsetIdx(a, b, c int) int { return a*81 + b*9 + c }

func (t *f2Tensor) flip(i int) { t[i>>6] ^= 1 << (uint(i) & 63) }

func (t *f2Tensor) nnz() int {
	n := 0
	for _, w := range t {
		n += bits.OnesCount64(w)
	}
	return n
}

func matmulTensor() f2Tensor {
	var T f2Tensor
	for i := 0; i < 3; i++ {
		for j := 0; j < 3; j++ {
			for k := 0; k < 3; k++ {
				T.flip(tsetIdx(3*i+j, 3*j+k, 3*i+k))
			}
		}
	}
	return T
}

// termTensor builds the outer-product bitmask of one term.
func termTensor(tr triple) f2Tensor {
	var out f2Tensor
	for a := 0; a < 9; a++ {
		if int(tr.u>>a)&1 == 0 {
			continue
		}
		for b := 0; b < 9; b++ {
			if int(tr.v>>b)&1 == 0 {
				continue
			}
			for c := 0; c < 9; c++ {
				if int(tr.w>>c)&1 != 0 {
					out.flip(tsetIdx(a, b, c))
				}
			}
		}
	}
	return out
}

func xorDelta(res, term *f2Tensor) int {
	delta := 0
	for w, tw := range term {
		if tw == 0 {
			continue
		}
		old := bits.OnesCount64(res[w])
		res[w] ^= tw
		delta += bits.OnesCount64(res[w]) - old
	}
	return delta
}

// ---------------- Exact min-peak (threshold DFS) ----------------

type searcher struct {
	terms     *[rank]f2Tensor
	threshold int
	dead      []uint64 // 2^23-bit dead-subset set
	touched   []uint32 // dead-set word indices written this threshold
	found     bool
	states    int64
	budget    int64
}

func (s *searcher) dfs(res *f2Tensor, mask uint32, curNnz, depth int) {
	if s.found || s.states > s.budget {
		return
	}
	s.states++
	if depth == rank {
		if curNnz == 0 {
			s.found = true
		}
		return
	}
	for k := 0; k < rank; k++ {
		if mask&(1<<k) != 0 {
			continue
		}
		newMask := mask | (1 << k)
		if s.dead[newMask>>6]&(1<<(newMask&63)) != 0 {
			continue
		}
		delta := xorDelta(res, &s.terms[k])
		if curNnz+delta <= s.threshold {
			s.dfs(res, newMask, curNnz+delta, depth+1)
			if s.found {
				xorDelta(res, &s.terms[k])
				return
			}
		}
		xorDelta(res, &s.terms[k])
	}
	w := mask >> 6
	if s.dead[w] == 0 {
		s.touched = append(s.touched, w)
	}
	s.dead[w] |= 1 << (mask & 63)
}

// exactMinPeak returns (minPeak, resolved, states); budget bounds total
// states across thresholds.
func exactMinPeak(T *f2Tensor, terms *[rank]f2Tensor, upper int, dead []uint64, budget int64) (int, bool, int64) {
	init := T.nnz()
	var total int64
	touched := make([]uint32, 0, 1<<14)
	for B := init; B <= upper; B++ {
		// Lazily clear only the dead-set words the previous threshold wrote.
		for _, w := range touched {
			dead[w] = 0
		}
		s := &searcher{terms: terms, threshold: B, dead: dead, touched: touched[:0], budget: budget - total}
		res := *T
		s.dfs(&res, 0, init, 0)
		touched = s.touched
		total += s.states
		if s.found {
			// Leave the dead set dirty for the caller; it is cleared on entry.
			for _, w := range touched {
				dead[w] = 0
			}
			return B, true, total
		}
		if total >= budget {
			for _, w := range touched {
				dead[w] = 0
			}
			return 0, false, total
		}
	}
	for _, w := range touched {
		dead[w] = 0
	}
	// Exhausted every threshold up to the cap without finding a witness:
	// min-peak is proven > upper.
	return 0, false, total
}

// fileOrderPeak peels terms in index order.
func fileOrderPeak(T *f2Tensor, terms *[rank]f2Tensor) int {
	res := *T
	peak := res.nnz()
	cur := peak
	for k := range terms {
		cur += xorDelta(&res, &terms[k])
		if cur > peak {
			peak = cur
		}
	}
	return peak
}

// ---------------- Gauge application, dedupe key ----------------

func applyGauge(base *[rank]triple, X, Y, Yinv, Zinv, XinvT, ZT mat3) [rank]triple {
	var out [rank]triple
	for i, t := range base {
		out[i] = triple{
			X.mul(t.u).mul(Yinv),
			Y.mul(t.v).mul(Zinv),
			XinvT.mul(t.w).mul(ZT),
		}
	}
	return out
}

// key hashes the unordered term multiset (FNV-1a over sorted packed terms).
func key(ts *[rank]triple) uint64 {
	var packed [rank]uint32
	for i, t := range ts {
		packed[i] = uint32(t.u) | uint32(t.v)<<9 | uint32(t.w)<<18
	}
	sort.Slice(packed[:], func(i, j int) bool { return packed[i] < packed[j] })
	h := uint64(14695981039346656037)
	for _, p := range packed {
		for s := 0; s < 32; s += 8 {
			h ^= uint64(p>>s) & 0xff
			h *= 1099511628211
		}
	}
	return h
}

func totalFactorNnz(ts *[rank]triple) int {
	n := 0
	for _, t := range ts {
		n += bits.OnesCount16(uint16(t.u)) + bits.OnesCount16(uint16(t.v)) + bits.OnesCount16(uint16(t.w))
	}
	return n
}

// ---------------- Main ----------------

var (
	capFlag     = flag.Int("cap", 34, "min-peak search cap; copies above it are bucketed, not resolved")
	budgetFlag  = flag.Int64("budget", 20_000_000, "per-copy DFS state budget")
	timeoutFlag = flag.Duration("timeout", 60*time.Minute, "global timeout")
)

func main() {
	flag.Parse()
	ctx, cancel := signal.NotifyContext(context.Background(), os.Interrupt)
	defer cancel()
	ctx, cancel2 := context.WithTimeout(ctx, *timeoutFlag)
	defer cancel2()

	T := matmulTensor()
	fmt.Printf("T nnz = %d\n", T.nnz())

	base := ladermanTerms()

	// Assert base decomposition sums to T.
	var acc f2Tensor
	for _, t := range base {
		tt := termTensor(t)
		for w := range acc {
			acc[w] ^= tt[w]
		}
	}
	if acc != T {
		fmt.Println("FATAL: base Laderman mod 2 does not sum to T")
		os.Exit(1)
	}
	fmt.Println("Base Laderman mod-2 assertion PASSED")

	gl := gl3f2()
	fmt.Printf("|GL(3,F_2)| = %d\n", len(gl))
	inv := invTable(gl)

	// Verify the gauge convention on a handful of non-identity gauges.
	{
		checked := 0
		for _, X := range gl[:5] {
			for _, Y := range gl[3:8] {
				for _, Z := range gl[7:12] {
					g := applyGauge(&base, X, Y, inv[Y], inv[Z], inv[X].transpose(), Z.transpose())
					var a f2Tensor
					for _, t := range g {
						tt := termTensor(t)
						for w := range a {
							a[w] ^= tt[w]
						}
					}
					if a != T {
						fmt.Printf("FATAL: gauge convention broken at X=%b Y=%b Z=%b\n", X, Y, Z)
						os.Exit(1)
					}
					checked++
				}
			}
		}
		fmt.Printf("Gauge convention verified on %d non-identity samples\n", checked)
	}

	// Baseline: identity gauge.
	var baseTens [rank]f2Tensor
	for i, t := range base {
		baseTens[i] = termTensor(t)
	}
	dead := make([]uint64, (1<<rank)/64)
	fop := fileOrderPeak(&T, &baseTens)
	basePeak, ok, st := exactMinPeak(&T, &baseTens, fop, dead, 1<<40)
	if !ok {
		fmt.Println("FATAL: baseline exact search unresolved")
		os.Exit(1)
	}
	fmt.Printf("Baseline (published gauge, mod 2): file-order peak=%d, EXACT min-peak=%d (%d states), factor nnz=%d\n",
		fop, basePeak, st, totalFactorNnz(&base))

	// Producer: enumerate 168^3 sandwiches, dedupe, feed distinct copies.
	type job struct {
		terms   [rank]triple
		x, y, z mat3
	}
	jobs := make(chan job, 1024)
	go func() {
		defer close(jobs)
		seen := make(map[uint64]struct{}, 2_000_000)
		count := 0
		for xi, X := range gl {
			XinvT := inv[X].transpose()
			for _, Y := range gl {
				Yinv := inv[Y]
				for _, Z := range gl {
					count++
					g := applyGauge(&base, X, Y, Yinv, inv[Z], XinvT, Z.transpose())
					k := key(&g)
					if _, dup := seen[k]; dup {
						continue
					}
					seen[k] = struct{}{}
					select {
					case jobs <- job{g, X, Y, Z}:
					case <-ctx.Done():
						return
					}
				}
			}
			if (xi+1)%42 == 0 {
				fmt.Fprintf(os.Stderr, "  producer: %d/168 X done, %d distinct so far\n", xi+1, len(seen))
			}
		}
		fmt.Fprintf(os.Stderr, "  producer done: %d triples, %d distinct copies\n", count, len(seen))
	}()

	// Workers.
	nw := runtime.NumCPU()
	var mu sync.Mutex
	peakDist := map[int]int{}
	nnzDist := map[int]int{}
	unresolved := 0
	overCap := 0
	processed := 0
	orbitMin := math.MaxInt
	orbitNnzMin := math.MaxInt
	var bestGauge [3]mat3
	start := time.Now()

	var wg sync.WaitGroup
	for w := 0; w < nw; w++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			deadW := make([]uint64, (1<<rank)/64)
			for j := range jobs {
				select {
				case <-ctx.Done():
					return
				default:
				}
				var tens [rank]f2Tensor
				for i, t := range j.terms {
					tens[i] = termTensor(t)
				}
				fp := fileOrderPeak(&T, &tens)
				// Values above the cap land in the over-cap bucket instead
				// of being chased exactly.
				budget := *budgetFlag
				peak, ok, st := exactMinPeak(&T, &tens, min(fp, *capFlag), deadW, budget)
				fnnz := totalFactorNnz(&j.terms)

				mu.Lock()
				processed++
				if !ok {
					if st >= budget {
						unresolved++ // budget abort: not proven either way
					} else {
						overCap++ // proven min-peak > 34
					}
				} else {
					peakDist[peak]++
					if peak < orbitMin {
						orbitMin = peak
						bestGauge = [3]mat3{j.x, j.y, j.z}
					}
				}
				nnzDist[fnnz]++
				if fnnz < orbitNnzMin {
					orbitNnzMin = fnnz
				}
				if processed%100000 == 0 {
					fmt.Fprintf(os.Stderr, "  %d copies processed (%.0fs), orbit-min so far %d\n",
						processed, time.Since(start).Seconds(), orbitMin)
				}
				mu.Unlock()
			}
		}()
	}
	wg.Wait()

	if err := ctx.Err(); err != nil {
		fmt.Printf("NOTE: stopped early: %v\n", err)
	}
	fmt.Printf("\nDistinct copies processed: %d (proven min-peak > %d: %d, budget-aborted: %d)\n",
		processed, *capFlag, overCap, unresolved)

	var pv []int
	for k := range peakDist {
		pv = append(pv, k)
	}
	sort.Ints(pv)
	fmt.Println("\n--- min-peak distribution (F_2) ---")
	for _, v := range pv {
		fmt.Printf("%4d  %d\n", v, peakDist[v])
	}
	fmt.Printf("ORBIT MIN-PEAK: %d  (gauge X=%09b Y=%09b Z=%09b)\n",
		orbitMin, uint16(bestGauge[0]), uint16(bestGauge[1]), uint16(bestGauge[2]))

	var nv []int
	for k := range nnzDist {
		nv = append(nv, k)
	}
	sort.Ints(nv)
	fmt.Println("\n--- factor nnz distribution ---")
	for _, v := range nv {
		fmt.Printf("%4d  %d\n", v, nnzDist[v])
	}
	fmt.Printf("ORBIT NNZ MIN: %d  (published: %d)\n", orbitNnzMin, totalFactorNnz(&base))
	fmt.Printf("\nTotal wall-clock: %.0fs\n", time.Since(start).Seconds())
}
