package main

// probe-koszul: computational probe for Koszul flattenings (Landsberg-Ottaviani,
// arXiv:1112.6007) of the matrix multiplication tensor M_n = <n,n,n>, with
// symmetry-adapted / structured restrictions of the A-leg (and optionally the
// B-leg). Tests whether any restriction subspace beats the LO certified bound
// 2n^2 - n on the small cases n = 2 (target > 6) and n = 3 (target > 15;
// R-bar(M_3) >= 16 is known so >= 16 would be a genuine finding).
//
// Task card: /home/neal/p/proofs/.tasks/research/Ko1.md
//
// Two rank modes:
//   - mod-p (uint64, p = 2^61-1): fast, used for random search. mod-p rank <=
//     true rank, equal w.h.p. for random data. Reported as mode "modp".
//   - exact Q (math/big.Rat): certified rank for structured (integer) families.
//     Reported as mode "exactQ".
//
// The certified border-rank bound is rank / C(d'_A - 1, p), reported as a
// floor (the bound is R-bar(M_n) >= ceil(rank / cost) when rank/cost is the
// exact attained value; we report both the raw ratio and its ceiling).

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"math"
	"math/rand"
	"os"
	"sort"
	"time"
)

// boundFromRank computes the certified bound rank / C(d'-1, p) and its ceiling.
func boundFromRank(rank, dPrime, p int) (ratio float64, ceil int, cost int64) {
	cost = binom(dPrime-1, p)
	if cost == 0 {
		return 0, 0, 0
	}
	ratio = float64(rank) / float64(cost)
	ceil = int(math.Ceil(ratio - 1e-9))
	return ratio, ceil, cost
}

// --- result record types ---

type unrestrictedRow struct {
	N      int     `json:"n"`
	P      int     `json:"p"`
	DimA   int     `json:"dim_a"` // = n^2 (unrestricted)
	Rank   int     `json:"rank"`
	Cost   int64   `json:"cost"`
	Ratio  float64 `json:"ratio"`
	Ceil   int     `json:"ceil_bound"`
	Mode   string  `json:"mode"`
	DomDim int     `json:"domain_dim"`
	CodDim int     `json:"codomain_dim"`
}

type replicationRow struct {
	N      int     `json:"n"`
	DPrime int     `json:"d_prime"`
	P      int     `json:"p"`
	Rank   int     `json:"rank"`
	Cost   int64   `json:"cost"`
	Ratio  float64 `json:"ratio"`
	Ceil   int     `json:"ceil_bound"`
	Mode   string  `json:"mode"`
	Expect int     `json:"expected_bound"`
	Pass   bool    `json:"pass"`
}

type searchRow struct {
	N       int     `json:"n"`
	DPrime  int     `json:"d_prime"`
	P       int     `json:"p"`
	Cost    int64   `json:"cost"`
	MaxRank int     `json:"max_rank"`
	Ratio   float64 `json:"best_ratio"`
	Ceil    int     `json:"best_ceil_bound"`
	Samples int     `json:"samples"`
	Mode    string  `json:"mode"`
}

type structuredRow struct {
	N      int     `json:"n"`
	Family string  `json:"family"`
	DPrime int     `json:"d_prime"`
	P      int     `json:"p"`
	Rank   int     `json:"rank"`
	Cost   int64   `json:"cost"`
	Ratio  float64 `json:"ratio"`
	Ceil   int     `json:"ceil_bound"`
	Mode   string  `json:"mode"`
	OK     bool    `json:"family_ok"` // family realized requested dimension
}

type twoSidedRow struct {
	N       int     `json:"n"`
	DPrimeA int     `json:"d_prime_a"`
	DPrimeB int     `json:"d_prime_b"`
	P       int     `json:"p"`
	Cost    int64   `json:"cost"`
	MaxRank int     `json:"max_rank"`
	Ratio   float64 `json:"best_ratio"`
	Ceil    int     `json:"best_ceil_bound"`
	Samples int     `json:"samples"`
	Mode    string  `json:"mode"`
}

type conclusion struct {
	N          int    `json:"n"`
	LOBound    int    `json:"lo_bound_2n2_minus_n"`
	BestCeil   int    `json:"best_ceil_bound_found"`
	BestSource string `json:"best_source"`
	ExceededLO bool   `json:"exceeded_lo"`
}

type output struct {
	GeneratedAt  string            `json:"generated_at"`
	Seed         int64             `json:"seed"`
	ModP         uint64            `json:"mod_p"`
	Replication  []replicationRow  `json:"replication"`
	Unrestricted []unrestrictedRow `json:"unrestricted_chart"`
	RandomSearch []searchRow       `json:"random_search"`
	Structured   []structuredRow   `json:"structured_search"`
	TwoSided     []twoSidedRow     `json:"two_sided_search"`
	Conclusions  []conclusion      `json:"conclusions"`
	Aborted      bool              `json:"aborted_on_deadline"`
}

func main() {
	timeout := flag.Duration("timeout", 10*time.Minute, "computation timeout")
	seed := flag.Int64("seed", 1, "base RNG seed")
	samples := flag.Int("samples", 200, "random A' samples per (d',p) cell")
	out := flag.String("out", "/home/neal/p/proofs/.tasks/research/infodumps/Ko1-results.json", "output JSON path")
	flag.Parse()

	ctx, cancel := context.WithTimeout(context.Background(), *timeout)
	defer cancel()

	o := &output{
		GeneratedAt: time.Now().UTC().Format(time.RFC3339),
		Seed:        *seed,
		ModP:        modP,
	}

	if err := run(ctx, o, *seed, *samples); err != nil {
		fmt.Fprintf(os.Stderr, "fatal: %v\n", err)
		// still write partial output below
	}

	writeOutput(o, *out)
}

func writeOutput(o *output, path string) {
	o.deriveConclusions()
	b, err := json.MarshalIndent(o, "", "  ")
	if err != nil {
		fmt.Fprintf(os.Stderr, "marshal: %v\n", err)
		return
	}
	if err := os.WriteFile(path, b, 0o644); err != nil {
		fmt.Fprintf(os.Stderr, "write %s: %v\n", path, err)
		return
	}
	fmt.Printf("wrote %s (%d bytes)\n", path, len(b))
}

func (o *output) deriveConclusions() {
	for _, n := range []int{2, 3} {
		lo := 2*n*n - n
		best := 0
		src := "none"
		consider := func(ceil int, source string) {
			if ceil > best {
				best = ceil
				src = source
			}
		}
		for _, r := range o.Replication {
			if r.N == n {
				consider(r.Ceil, fmt.Sprintf("replication d'=%d p=%d", r.DPrime, r.P))
			}
		}
		for _, r := range o.Unrestricted {
			if r.N == n {
				consider(r.Ceil, fmt.Sprintf("unrestricted p=%d", r.P))
			}
		}
		for _, r := range o.RandomSearch {
			if r.N == n {
				consider(r.Ceil, fmt.Sprintf("random d'=%d p=%d", r.DPrime, r.P))
			}
		}
		for _, r := range o.Structured {
			if r.N == n {
				consider(r.Ceil, fmt.Sprintf("structured %s d'=%d p=%d", r.Family, r.DPrime, r.P))
			}
		}
		for _, r := range o.TwoSided {
			if r.N == n {
				consider(r.Ceil, fmt.Sprintf("two-sided d'A=%d d'B=%d p=%d", r.DPrimeA, r.DPrimeB, r.P))
			}
		}
		o.Conclusions = append(o.Conclusions, conclusion{
			N:          n,
			LOBound:    lo,
			BestCeil:   best,
			BestSource: src,
			ExceededLO: best > lo,
		})
	}
}

func run(ctx context.Context, o *output, baseSeed int64, samples int) error {
	rng := rand.New(rand.NewSource(baseSeed))

	// ===== Part 1a: Replication with generic A' at LO parameters =====
	if err := replicate(ctx, o, rng); err != nil {
		return err
	}

	// ===== Part 1b: Unrestricted map at all p =====
	if err := unrestrictedChart(ctx, o); err != nil {
		o.Aborted = true
		return nil
	}

	// ===== Part 2: Random search =====
	if err := randomSearch(ctx, o, rng, samples); err != nil {
		o.Aborted = true
		return nil
	}

	// ===== Part 3: Structured search =====
	if err := structuredSearch(ctx, o, rng); err != nil {
		o.Aborted = true
		return nil
	}

	// ===== Part 4: Two-sided (stretch) =====
	if err := twoSidedSearch(ctx, o, rng, samples); err != nil {
		o.Aborted = true
		return nil
	}

	return nil
}

// replicate builds the LO-optimal restricted map for n=2 (d'=3,p=1) and
// n=3 (d'=5,p=2) using a generic mod-p A', and asserts the certified bounds
// 6 and 15. Hard assertion failures return an error per doctrine (do not
// loosen).
func replicate(ctx context.Context, o *output, rng *rand.Rand) error {
	cases := []struct {
		n, dPrime, p, expect int
	}{
		{2, 3, 1, 6},
		{3, 5, 2, 15},
	}
	for _, c := range cases {
		n2 := c.n * c.n
		// take the max rank over a few generic samples to be safe against an
		// unlucky degenerate R (generic R achieves the LO rank).
		bestRank := 0
		for s := 0; s < 8; s++ {
			R := randProjModP(rng, c.dPrime, n2)
			M := koszulMatrixModP(c.n, c.dPrime, c.p, R)
			rk := rankModPU(M)
			if rk > bestRank {
				bestRank = rk
			}
		}
		ratio, ceil, cost := boundFromRank(bestRank, c.dPrime, c.p)
		row := replicationRow{
			N: c.n, DPrime: c.dPrime, P: c.p, Rank: bestRank, Cost: cost,
			Ratio: ratio, Ceil: ceil, Mode: "modp", Expect: c.expect,
			Pass: ceil == c.expect,
		}
		o.Replication = append(o.Replication, row)
		fmt.Printf("replicate n=%d d'=%d p=%d: rank=%d cost=%d bound=%d (expect %d) pass=%v\n",
			c.n, c.dPrime, c.p, bestRank, cost, ceil, c.expect, row.Pass)
		if !row.Pass {
			return fmt.Errorf("REPLICATION FAILED n=%d d'=%d p=%d: certified bound %d != expected %d (rank=%d cost=%d). Halting per doctrine; do not loosen",
				c.n, c.dPrime, c.p, ceil, c.expect, bestRank, cost)
		}
	}
	return nil
}

// unrestrictedChart computes the UNRESTRICTED Koszul map (A' = A, d'=n^2) for
// n=2,3 at all valid p, charting where the slack is. Uses the identity
// projection (R = I_{n^2}), exact integer entries, exact-Q rank for n=2 (tiny)
// and mod-p for n=3 (larger).
func unrestrictedChart(ctx context.Context, o *output) error {
	for _, n := range []int{2, 3} {
		n2 := n * n
		for p := 1; p <= n2-1; p++ {
			select {
			case <-ctx.Done():
				return ctx.Err()
			default:
			}
			combP := binom(n2, p)
			combP1 := binom(n2, p+1)
			domDim := int(int64(n2) * combP)
			codDim := int(combP1 * int64(n2))
			// identity projection R = I_{n^2}
			rk, mode := rankUnrestricted(n, p)
			ratio, ceil, cost := boundFromRank(rk, n2, p)
			o.Unrestricted = append(o.Unrestricted, unrestrictedRow{
				N: n, P: p, DimA: n2, Rank: rk, Cost: cost, Ratio: ratio,
				Ceil: ceil, Mode: mode, DomDim: domDim, CodDim: codDim,
			})
			fmt.Printf("unrestricted n=%d p=%d: dom=%d cod=%d rank=%d cost=%d bound=%d (%s)\n",
				n, p, domDim, codDim, rk, cost, ceil, mode)
		}
	}
	return nil
}

func rankUnrestricted(n, p int) (int, string) {
	n2 := n * n
	I := make([][]int64, n2)
	for i := 0; i < n2; i++ {
		I[i] = make([]int64, n2)
		I[i][i] = 1
	}
	if n == 2 {
		M := koszulMatrixInt(n, n2, p, I)
		return rankExactQ(M), "exactQ"
	}
	// n==3: build mod-p directly (entries 0/±1, but mod-p is fine and faster)
	Iu := make([][]uint64, n2)
	for i := 0; i < n2; i++ {
		Iu[i] = make([]uint64, n2)
		Iu[i][i] = 1
	}
	M := koszulMatrixModP(n, n2, p, Iu)
	return rankModPU(M), "modp"
}

// randomSearch sweeps d' in [2, n^2], p in [1, d'-1]; for each cell samples
// `samples` random A' (mod-p) and records the best rank / cost.
func randomSearch(ctx context.Context, o *output, rng *rand.Rand, samples int) error {
	for _, n := range []int{2, 3} {
		n2 := n * n
		for dPrime := 2; dPrime <= n2; dPrime++ {
			for p := 1; p <= dPrime-1; p++ {
				select {
				case <-ctx.Done():
					return ctx.Err()
				default:
				}
				cost := binom(dPrime-1, p)
				if cost == 0 {
					continue
				}
				maxRank := 0
				for s := 0; s < samples; s++ {
					if s%32 == 0 {
						select {
						case <-ctx.Done():
							return ctx.Err()
						default:
						}
					}
					R := randProjModP(rng, dPrime, n2)
					M := koszulMatrixModP(n, dPrime, p, R)
					rk := rankModPU(M)
					if rk > maxRank {
						maxRank = rk
					}
				}
				ratio, ceil, _ := boundFromRank(maxRank, dPrime, p)
				o.RandomSearch = append(o.RandomSearch, searchRow{
					N: n, DPrime: dPrime, P: p, Cost: cost, MaxRank: maxRank,
					Ratio: ratio, Ceil: ceil, Samples: samples, Mode: "modp",
				})
				fmt.Printf("random n=%d d'=%d p=%d: cost=%d maxrank=%d bound=%d\n",
					n, dPrime, p, cost, maxRank, ceil)
			}
		}
	}
	return nil
}

// structuredSearch sweeps the structured families across d' and p. Each family
// has a natural dimension; we probe d' from 2 up to min(family dim, n^2) and
// p from 1..d'-1. Exact-Q rank for the integer families.
func structuredSearch(ctx context.Context, o *output, rng *rand.Rand) error {
	for _, n := range []int{2, 3} {
		n2 := n * n
		for dPrime := 2; dPrime <= n2; dPrime++ {
			for p := 1; p <= dPrime-1; p++ {
				select {
				case <-ctx.Done():
					return ctx.Err()
				default:
				}
				cost := binom(dPrime-1, p)
				if cost == 0 {
					continue
				}
				for _, fam := range structuredFamilies(n, dPrime, rng) {
					if fam.R == nil {
						continue
					}
					rk, mode := rankStructured(n, dPrime, p, fam.R, fam.ok)
					ratio, ceil, _ := boundFromRank(rk, dPrime, p)
					o.Structured = append(o.Structured, structuredRow{
						N: n, Family: fam.name, DPrime: dPrime, P: p,
						Rank: rk, Cost: cost, Ratio: ratio, Ceil: ceil,
						Mode: mode, OK: fam.ok,
					})
				}
			}
		}
	}
	// log the best structured ceil per n
	for _, n := range []int{2, 3} {
		best := 0
		var bs structuredRow
		for _, r := range o.Structured {
			if r.N == n && r.OK && r.Ceil > best {
				best = r.Ceil
				bs = r
			}
		}
		fmt.Printf("structured n=%d best: %s d'=%d p=%d bound=%d\n",
			n, bs.Family, bs.DPrime, bs.P, best)
	}
	return nil
}

type famSpec struct {
	name string
	R    [][]int64
	ok   bool
}

// structuredFamilies returns the structured A' candidates at the given
// dimension d'. Families whose natural dimension is below d' are skipped
// (returned with ok=false / nil where not realizable).
func structuredFamilies(n, dPrime int, rng *rand.Rand) []famSpec {
	var fs []famSpec
	n2 := n * n

	// (a) powers of a companion / random nonderogatory X (dim up to n)
	if dPrime <= n {
		X := companion(n, rng)
		R, ok := familyPowers(X, n, dPrime)
		fs = append(fs, famSpec{"powers_companion", R, ok})
		Xr := randIntMat(n, rng)
		Rr, okr := familyPowers(Xr, n, dPrime)
		fs = append(fs, famSpec{"powers_random", Rr, okr})
	}

	// (b) circulant (dim n) and Toeplitz (dim 2n-1)
	if dPrime <= n {
		fs = append(fs, famSpec{"circulant", familyCirculant(n, dPrime), true})
	}
	if dPrime <= 2*n-1 {
		fs = append(fs, famSpec{"toeplitz", familyToeplitz(n, dPrime), true})
	}

	// (c) symmetric (dim n(n+1)/2) and skew (dim n(n-1)/2)
	if dPrime <= n*(n+1)/2 {
		fs = append(fs, famSpec{"symmetric", familySymmetric(n, dPrime), true})
	}
	if dPrime <= n*(n-1)/2 {
		fs = append(fs, famSpec{"skew", familySkew(n, dPrime), true})
	}

	// (d) traceless sl_n (dim n^2-1)
	if dPrime <= n2-1 {
		fs = append(fs, famSpec{"traceless", familyTraceless(n, dPrime), true})
	}

	// (e) commutator-closed span (ad_X-invariant)
	{
		X := randIntMat(n, rng)
		R, ok := familyCommutant(X, n, dPrime, rng)
		fs = append(fs, famSpec{"commutant", R, ok})
	}

	return fs
}

func rankStructured(n, dPrime, p int, R [][]int64, ok bool) (int, string) {
	if !ok {
		return 0, "skip"
	}
	M := koszulMatrixInt(n, dPrime, p, R)
	// exact-Q rank for n=2 (small); mod-p for n=3 to keep big.Rat cost bounded
	if n == 2 {
		return rankExactQ(M), "exactQ"
	}
	// reduce mod p
	return rankModP(M), "modp"
}

// twoSidedSearch restricts both A and B. Sweeps small d'_B. Random mode.
func twoSidedSearch(ctx context.Context, o *output, rng *rand.Rand, samples int) error {
	// budget guard: only run if there is time left
	for _, n := range []int{2, 3} {
		n2 := n * n
		// focus near LO parameters and a bit beyond
		dAset := loNeighborhood(n)
		for _, dA := range dAset {
			for p := 1; p <= dA-1; p++ {
				for dB := 1; dB <= n2; dB++ {
					select {
					case <-ctx.Done():
						return ctx.Err()
					default:
					}
					cost := binom(dA-1, p)
					if cost == 0 {
						continue
					}
					maxRank := 0
					sm := samples
					if sm > 100 {
						sm = 100 // two-sided is a stretch goal; keep it cheap
					}
					for s := 0; s < sm; s++ {
						RA := randProjModP(rng, dA, n2)
						var RB [][]uint64
						if dB < n2 {
							RB = randProjModP(rng, dB, n2)
						}
						M := koszulMatrixModP2(n, dA, p, RA, dB, RB)
						rk := rankModPU(M)
						if rk > maxRank {
							maxRank = rk
						}
					}
					ratio, ceil, _ := boundFromRank(maxRank, dA, p)
					o.TwoSided = append(o.TwoSided, twoSidedRow{
						N: n, DPrimeA: dA, DPrimeB: dB, P: p, Cost: cost,
						MaxRank: maxRank, Ratio: ratio, Ceil: ceil,
						Samples: sm, Mode: "modp",
					})
				}
			}
		}
	}
	return nil
}

// loNeighborhood returns d'_A values to probe in the two-sided search: the LO
// optimum d'=2n-1 plus n^2 (full) and a couple neighbors.
func loNeighborhood(n int) []int {
	lo := 2*n - 1
	cand := map[int]bool{lo: true, lo + 1: true, n * n: true}
	if lo-1 >= 2 {
		cand[lo-1] = true
	}
	var out []int
	for d := range cand {
		if d >= 2 && d <= n*n {
			out = append(out, d)
		}
	}
	sort.Ints(out)
	return out
}
