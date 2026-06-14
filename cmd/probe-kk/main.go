package main

// probe-kk: Track B kill-or-continue. Computes the actual rank of the
// Dolezalek-Michalek (arXiv:2602.12762, Sec 3, Cor 3.5 / Prop 5.1) k=2
// wedge-(d'+2) "tangency" flattening of the 3x3 matrix-multiplication tensor
// M_3 (n=3, V_i = F_p^9) at d'=3 and d'=4, plus the Z_3 eigenspace data.
//
// Task card: /home/neal/p/proofs/.tasks/research/Kk1.md
//
// The canonical DM flattening is the "mixed" passenger split, VERIFIED to
// reproduce DM Prop 5.1 (M_2 -> rank 64) and DM Prop 3.6 (unit tensor ->
// q(q-1)*C(q-2,d')). It is the family's best member on M_3. The complementary
// "byleg" split is reported for completeness.
//
// Verdict (d'=3 mixed rank, cost C(7,3)=35):
//   rank >= 6371 (=14*13*35+1) : certifies R-bar(M_3) >= 15 (matches LO).
//   rank in [5461,6370]        : certifies R-bar(M_3) >= 14, one short of LO.
//   rank <= 5460               : weaker still.
// Any rank < 6371 means Track B (plain DM family) cannot beat LO on M_3.

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"math/rand"
	"os"
	"time"
)

func binom(n, k int) int64 {
	if k < 0 || k > n {
		return 0
	}
	if k > n-k {
		k = n - k
	}
	r := int64(1)
	for i := 0; i < k; i++ {
		r = r * int64(n-i) / int64(i+1)
	}
	return r
}

var crossPrimes = []uint64{1000003, 1000033, 1000037, 1000039, 1000081}

type sanityResult struct {
	Name      string `json:"name"`
	DPrime    int    `json:"d_prime"`
	Rank      int    `json:"rank"`
	Bound     int    `json:"bound"`
	Q         int    `json:"q"`
	WithinCap bool   `json:"ok"`
	Note      string `json:"note"`
}

type legAgreement struct {
	DPrime int    `json:"d_prime"`
	Spec   string `json:"spec"`
	LegW   [3]int `json:"leg_ranks"`
	Agree  bool   `json:"agree"`
}

type rankResult struct {
	DPrime    int            `json:"d_prime"`
	Spec      string         `json:"spec"`
	Rows      int            `json:"rows"`
	Cols      int            `json:"cols"`
	RankModP  int            `json:"rank_mod_2_61_minus_1"`
	RankSmall map[string]int `json:"rank_small_primes"`
	AllAgree  bool           `json:"all_primes_agree"`
	BestR     int            `json:"certified_R_bar_lower_bound"`
}

type eigenResult struct {
	DPrime          int    `json:"d_prime"`
	Spec            string `json:"spec"`
	BlocksIdentical bool   `json:"three_leg_blocks_identical"`
	RankSum         int    `json:"rank_direct_sum_all_three_legs"`
	RankPer         int    `json:"rank_single_leg"`
	Eig1            int    `json:"rank_eigenspace_omega_eq_1"`
	EigZeta         int    `json:"rank_eigenspace_omega_eq_zeta"`
	EigZeta2        int    `json:"rank_eigenspace_omega_eq_zeta2"`
	SumEig          int    `json:"sum_of_eigenspace_ranks"`
	Note            string `json:"note"`
}

type output struct {
	GeneratedAt string         `json:"generated_at"`
	N           int            `json:"n"`
	ModP        uint64         `json:"mod_p_primary"`
	CrossPrimes []uint64       `json:"cross_primes"`
	Sanity      []sanityResult `json:"sanity_gates"`
	LegAgree    []legAgreement `json:"leg_symmetry_check"`
	Ranks       []rankResult   `json:"flattening_ranks"`
	Eigen       []eigenResult  `json:"z3_eigenspaces"`
	BestRank3   int            `json:"best_d3_rank"`
	BestSpec    string         `json:"best_d3_spec"`
	BestRBound  int            `json:"best_R_bar_lower_bound"`
	Verdict     string         `json:"verdict"`
	TrackBDead  bool           `json:"track_b_dead_on_m3"`
	Aborted     bool           `json:"aborted_on_deadline"`
}

func main() {
	timeout := flag.Duration("timeout", 30*time.Minute, "overall computation timeout")
	seed := flag.Int64("seed", 1, "RNG seed for sanity-gate random tensors")
	outPath := flag.String("out", "/home/neal/p/proofs/.tasks/research/infodumps/Kk1-results.json", "output JSON path")
	flag.Parse()

	ctx, cancel := context.WithTimeout(context.Background(), *timeout)
	defer cancel()

	o := &output{
		GeneratedAt: time.Now().UTC().Format(time.RFC3339),
		N:           3,
		ModP:        modP,
		CrossPrimes: crossPrimes,
	}
	if err := run(ctx, o, *seed); err != nil {
		fmt.Fprintf(os.Stderr, "run error: %v\n", err)
		o.Aborted = true
	}
	writeOutput(o, *outPath)
}

func writeOutput(o *output, path string) {
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

func run(ctx context.Context, o *output, seed int64) error {
	n := 3
	rng := rand.New(rand.NewSource(seed))

	if err := sanityGates(ctx, o, n, rng); err != nil {
		return err
	}
	if err := legSymmetry(ctx, o, n); err != nil {
		return err
	}

	// STEP 3 + STEP 4: headline ranks at d'=3 and d'=4 for both flattening
	// specs, multi-prime. The mixed spec is DM's canonical tangency flattening.
	for _, dPrime := range []int{3, 4} {
		for _, spec := range []flatSpec{specMixed, specByLeg} {
			if err := deadline(ctx); err != nil {
				return err
			}
			rr := headlineRank(ctx, n, dPrime, spec)
			rr.BestR = bestRBound(rr.RankModP)
			o.Ranks = append(o.Ranks, rr)
			fmt.Printf("HEADLINE d'=%d spec=%s: %dx%d rank(2^61-1)=%d small-agree=%v => R-bar>=%d\n",
				dPrime, spec, rr.Rows, rr.Cols, rr.RankModP, rr.AllAgree, rr.BestR)
		}
	}

	// STEP 5: Z_3 eigenspaces (d'=3) for both specs.
	for _, spec := range []flatSpec{specMixed, specByLeg} {
		if err := z3Eigen(ctx, o, n, 3, spec); err != nil {
			fmt.Fprintf(os.Stderr, "z3 eigen spec=%s: %v\n", spec, err)
		}
	}

	deriveVerdict(o)
	return nil
}

// bestRBound: largest q+1 such that q(q-1)*35 < rank, i.e. the certified
// R-bar(M_3) lower bound from a d'=3 flattening of the given rank.
func bestRBound(rank int) int {
	best := 0
	for q := 1; q <= 30; q++ {
		if int64(q)*int64(q-1)*35 < int64(rank) {
			best = q + 1
		}
	}
	return best
}

func deriveVerdict(o *output) {
	best := -1
	bestSpec := ""
	for _, r := range o.Ranks {
		if r.DPrime == 3 && r.RankModP > best {
			best = r.RankModP
			bestSpec = r.Spec
		}
	}
	if best < 0 {
		o.Verdict = "incomplete: no d'=3 rank computed"
		return
	}
	o.BestRank3 = best
	o.BestSpec = bestSpec
	o.BestRBound = bestRBound(best)
	if best >= 6371 {
		o.TrackBDead = false
		o.Verdict = fmt.Sprintf(
			"best d'=3 rank=%d (spec %s) >= 6371: certifies R-bar(M_3) >= %d, matching Landsberg-Ottaviani by a different method (CHL's 17 still towers over it). Kk2's equivariant-refinement question becomes live.",
			best, bestSpec, o.BestRBound)
	} else {
		o.TrackBDead = true
		o.Verdict = fmt.Sprintf(
			"best d'=3 rank=%d (spec %s) < 6371: certifies only R-bar(M_3) >= %d, strictly worse than LO's 15 on M_3. Track B (plain DM family) is DEAD on M_3; Kk2 stays shelved.",
			best, bestSpec, o.BestRBound)
	}
}

func deadline(ctx context.Context) error {
	select {
	case <-ctx.Done():
		return ctx.Err()
	default:
		return nil
	}
}
