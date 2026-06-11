package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"math/rand"
	"os"
	"sort"
	"time"
)

// B1: measure the relationship between spreadness r*(F) and tau-inflation
// under the canonical Frankl-shift sweep S(F). For each family in the zoo we
// record k, n, |F|, r*(F) with its witness Z, tau(F), tau(S(F)), and the
// ratio tau(S(F))/tau(F). Hypothesis H: that ratio is bounded by a function
// of r*(F) alone, independent of k. Kill criterion: r*(F) >= 4 and
// tau(S(F))/tau(F) > 8 with the ratio growing in k.

type row struct {
	ID         string  `json:"id"`
	Desc       string  `json:"desc"`
	K          int     `json:"k"`
	N          int     `json:"n"`
	Fcard      int     `json:"f_card"`
	RStar      float64 `json:"r_star"`
	WitnessZ   []int   `json:"witness_z"`
	WitnessFZ  int     `json:"witness_fz"`
	WitnessF   int     `json:"witness_total"`
	TauF       int     `json:"tau_f"`
	TauSF      int     `json:"tau_sf"`
	TauExact   bool    `json:"tau_exact"`    // both tau computations finished within budget
	TauFExact  bool    `json:"tau_f_exact"`  // tau(F) exact (else a lower bound)
	TauSFExact bool    `json:"tau_sf_exact"` // tau(S(F)) exact (else a lower bound)
	Ratio      float64 `json:"ratio"`        // tau(S(F))/tau(F); when tau(F) is a lower bound this is an UPPER bound on the true ratio
	Seed       int64   `json:"seed,omitempty"`
	GenParams  string  `json:"gen_params,omitempty"`
	Members    [][]int `json:"members,omitempty"`         // included for small/extremal/killing rows
	ShiftedMem [][]int `json:"shifted_members,omitempty"` // killing/extremal only
}

type output struct {
	GeneratedAt string `json:"generated_at"`
	Calibration struct {
		TauFamilyB     int  `json:"tau_familyB"`
		TauShifted     int  `json:"tau_shifted_familyB"`
		EndpointIsStar bool `json:"endpoint_is_full_star_012"`
		Passed         bool `json:"passed"`
	} `json:"calibration"`
	Verdict string `json:"verdict"`
	Killed  *row   `json:"killing_witness,omitempty"`
	Rows    []row  `json:"rows"`
}

const (
	killRStar = 4.0
	killRatio = 8.0
	memberCap = 30 // include explicit member lists for families up to this size
)

func main() {
	timeout := flag.Duration("timeout", 5*time.Minute, "computation timeout")
	seed := flag.Int64("seed", 1, "base RNG seed for the random portions of the zoo")
	out := flag.String("out", "data/erdos20/trackB/spread_defect.json", "output JSON path")
	flag.Parse()

	ctx, cancel := context.WithTimeout(context.Background(), *timeout)
	defer cancel()

	if err := run(ctx, *seed, *out); err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
}

func run(ctx context.Context, baseSeed int64, outPath string) error {
	var o output
	o.GeneratedAt = time.Now().UTC().Format(time.RFC3339)

	// ---- Calibration (mandatory before scaling) ----
	familyB := buildFamilyB()
	o.Calibration.TauFamilyB, _ = maxSunflower(familyB)
	shiftedB := fullShiftSweep(familyB, 20)
	o.Calibration.TauShifted, _ = maxSunflower(shiftedB)
	o.Calibration.EndpointIsStar = isFullStar(shiftedB, []int{0, 1, 2}, 17)
	o.Calibration.Passed = o.Calibration.TauFamilyB == 2 &&
		o.Calibration.TauShifted == 17 && o.Calibration.EndpointIsStar
	fmt.Printf("calibration: tau(familyB)=%d tau(S(familyB))=%d endpointStar=%v passed=%v\n",
		o.Calibration.TauFamilyB, o.Calibration.TauShifted,
		o.Calibration.EndpointIsStar, o.Calibration.Passed)
	if !o.Calibration.Passed {
		return fmt.Errorf("calibration FAILED; refusing to proceed")
	}

	// familyB calibration row
	o.Rows = append(o.Rows, makeRow("familyB", "calibration witness (Counterexample.lean): 4-uniform Fin20, |F|=17", 4, 20, familyB))

	// ---- Zoo ----
	var killed *row

	addRow := func(r row) bool {
		o.Rows = append(o.Rows, r)
		// kill check: only on an EXACT tau. An inexact tau(F) is a lower bound,
		// so tau(S(F))/tau(F) is only an upper bound on the true ratio, and a
		// kill on it could be spurious. Such rows are surfaced for review but
		// never trigger an automatic H DEAD.
		if r.RStar >= killRStar && r.TauF > 0 && r.Ratio > killRatio && r.TauExact {
			rc := r
			killed = &rc
			return true
		}
		return false
	}

	// stars: all k-sets through a common element 0, varying k,n
	for _, kn := range [][2]int{{3, 8}, {3, 12}, {4, 10}, {4, 14}, {5, 12}} {
		if ctx.Err() != nil {
			return finish(ctx, &o, killed, outPath)
		}
		k, n := kn[0], kn[1]
		fam := buildStar(k, n)
		r := makeRow(fmt.Sprintf("star_k%d_n%d", k, n),
			fmt.Sprintf("full star: all %d-sets through element 0 on n=%d", k, n), k, n, fam)
		if addRow(r) {
			goto done
		}
	}

	// co-singleton families: all k-sets avoiding a fixed element (here element n-1)
	for _, kn := range [][2]int{{3, 8}, {4, 9}, {4, 11}} {
		if ctx.Err() != nil {
			return finish(ctx, &o, killed, outPath)
		}
		k, n := kn[0], kn[1]
		fam := buildCoSingleton(k, n)
		r := makeRow(fmt.Sprintf("cosingleton_k%d_n%d", k, n),
			fmt.Sprintf("co-singleton: all %d-sets on n=%d avoiding element %d", k, n, n-1), k, n, fam)
		if addRow(r) {
			goto done
		}
	}

	// random graded-density k-uniform samples
	{
		rng := rand.New(rand.NewSource(baseSeed))
		idx := 0
		for k := 3; k <= 5; k++ {
			for n := 10; n <= 20; n += 5 {
				maxSets := nChooseK(n, k)
				if maxSets > 400 {
					maxSets = 400
				}
				for _, frac := range []float64{0.1, 0.25, 0.5} {
					m := int(frac * float64(maxSets))
					if m < 2 {
						m = 2
					}
					for rep := 0; rep < 2; rep++ {
						if ctx.Err() != nil {
							return finish(ctx, &o, killed, outPath)
						}
						s := baseSeed*1000 + int64(idx)
						idx++
						fam := buildRandom(k, n, m, rng)
						r := makeRowSeeded(fmt.Sprintf("rand_k%d_n%d_m%d_r%d", k, n, len(fam), rep),
							fmt.Sprintf("random %d-uniform, n=%d, target |F|=%d", k, n, m),
							k, n, fam, s, fmt.Sprintf("k=%d n=%d target_m=%d frac=%.2f rep=%d", k, n, m, frac, rep))
						if addRow(r) {
							goto done
						}
					}
				}
			}
		}
	}

	// near-extremal tau<=2 families by exhaustive small search (erdos20/main.go style)
	for _, kn := range [][2]int{{3, 6}, {3, 7}, {4, 7}, {4, 8}} {
		if ctx.Err() != nil {
			return finish(ctx, &o, killed, outPath)
		}
		k, n := kn[0], kn[1]
		fams := searchHighRatioLowTau(ctx, k, n)
		for fi, fam := range fams {
			r := makeRow(fmt.Sprintf("extremal_k%d_n%d_%d", k, n, fi),
				fmt.Sprintf("search-found tau<=2 high-inflation %d-uniform on n=%d", k, n), k, n, fam)
			if addRow(r) {
				goto done
			}
		}
	}

	// ALWZ-style high-spread constructions: resample/reject until r* is large
	{
		for _, kn := range [][3]int{{3, 14, 5}, {3, 18, 6}, {4, 16, 6}, {4, 20, 7}, {5, 18, 7}, {5, 20, 8}} {
			if ctx.Err() != nil {
				return finish(ctx, &o, killed, outPath)
			}
			k, n, m := kn[0], kn[1], kn[2]
			for rep := 0; rep < 3; rep++ {
				if ctx.Err() != nil {
					return finish(ctx, &o, killed, outPath)
				}
				s := baseSeed*7000 + int64(k*100+n*10+rep)
				rng := rand.New(rand.NewSource(s))
				fam, rstar := buildHighSpread(k, n, m, rng, killRStar)
				if fam == nil {
					continue
				}
				r := makeRowSeeded(fmt.Sprintf("highspread_k%d_n%d_m%d_r%d", k, n, m, rep),
					fmt.Sprintf("ALWZ-style high-spread (reject-until r*>=%.0f) %d-uniform n=%d target r*=%.3f", killRStar, k, n, rstar),
					k, n, fam, s, fmt.Sprintf("k=%d n=%d m=%d rep=%d reject_threshold=%.1f", k, n, m, rep, killRStar))
				if addRow(r) {
					goto done
				}
			}
		}
	}

	// KILL-PROBE: r* is structurally capped at |F|^(1/k) (any single member,
	// used as Z, gives (|F|/1)^(1/k)). So entering the kill region r*>=4 at
	// uniformity k requires |F| >= 4^k (256 at k=4, 1024 at k=5). The other
	// stages cannot reach r*>=4 above k=3; this stage deliberately scales |F|
	// past 4^k for k=3,4,5 to test whether the ratio grows with k while r*
	// stays high -- the precise condition H's kill criterion names.
	{
		probes := []struct {
			k, n, m int
		}{
			{3, 22, 200}, {3, 24, 300},
			{4, 20, 400}, {4, 22, 600}, {4, 24, 900},
			{5, 22, 1300}, {5, 24, 1600}, {5, 25, 2000},
		}
		for _, p := range probes {
			for rep := 0; rep < 2; rep++ {
				if ctx.Err() != nil {
					return finish(ctx, &o, killed, outPath)
				}
				s := baseSeed*9000 + int64(p.k*1000+p.n*10+rep)
				rng := rand.New(rand.NewSource(s))
				fam := buildRandom(p.k, p.n, p.m, rng)
				r := makeRowSeeded(fmt.Sprintf("killprobe_k%d_n%d_m%d_r%d", p.k, p.n, p.m, rep),
					fmt.Sprintf("kill-probe random %d-uniform n=%d |F|=%d (scaled past 4^k for r*>=4)", p.k, p.n, len(fam)),
					p.k, p.n, fam, s, fmt.Sprintf("k=%d n=%d target_m=%d rep=%d", p.k, p.n, p.m, rep))
				if addRow(r) {
					goto done
				}
			}
		}
	}

done:
	return finish(ctx, &o, killed, outPath)
}

func finish(ctx context.Context, o *output, killed *row, outPath string) error {
	// verdict
	if killed != nil {
		o.Verdict = "H DEAD"
		o.Killed = killed
	} else {
		// determine support: H survives if no row crossed the kill threshold.
		// We additionally flag inconclusive if no high-r* family was actually
		// produced (cannot test the regime).
		maxR := 0.0
		for _, r := range o.Rows {
			if r.RStar < 1e9 && r.RStar > maxR {
				maxR = r.RStar
			}
		}
		if maxR < killRStar {
			o.Verdict = "INCONCLUSIVE"
		} else {
			o.Verdict = "H SUPPORTED"
		}
	}
	if ctx.Err() != nil {
		fmt.Fprintf(os.Stderr, "note: deadline reached; emitting partial results (%d rows)\n", len(o.Rows))
	}

	data, err := json.MarshalIndent(o, "", "  ")
	if err != nil {
		return fmt.Errorf("marshal output: %w", err)
	}
	if err := os.MkdirAll("data/erdos20/trackB", 0o755); err != nil {
		return fmt.Errorf("mkdir: %w", err)
	}
	if err := os.WriteFile(outPath, data, 0o644); err != nil {
		return fmt.Errorf("write %s: %w", outPath, err)
	}
	fmt.Printf("verdict: %s\nrows: %d\nwrote: %s\n", o.Verdict, len(o.Rows), outPath)
	reportExtremes(o)
	return nil
}

func reportExtremes(o *output) {
	if len(o.Rows) == 0 {
		return
	}
	byRatio := append([]row(nil), o.Rows...)
	sort.Slice(byRatio, func(a, b int) bool { return byRatio[a].Ratio > byRatio[b].Ratio })
	byR := append([]row(nil), o.Rows...)
	sort.Slice(byR, func(a, b int) bool {
		ra, rb := byR[a].RStar, byR[b].RStar
		if ra >= 1e9 {
			ra = 0
		}
		if rb >= 1e9 {
			rb = 0
		}
		return ra > rb
	})
	fmt.Printf("top ratio: %s ratio=%.3f r*=%.3f k=%d tau %d->%d\n",
		byRatio[0].ID, byRatio[0].Ratio, byRatio[0].RStar, byRatio[0].K, byRatio[0].TauF, byRatio[0].TauSF)
	fmt.Printf("top r*:    %s r*=%.3f ratio=%.3f k=%d tau %d->%d\n",
		byR[0].ID, byR[0].RStar, byR[0].Ratio, byR[0].K, byR[0].TauF, byR[0].TauSF)
}

// makeRow computes all measurements for a family and packages a row, including
// explicit member lists for small families.
func makeRow(id, desc string, k, n int, fam []uint) row {
	return makeRowSeeded(id, desc, k, n, fam, 0, "")
}

func makeRowSeeded(id, desc string, k, n int, fam []uint, seed int64, gen string) row {
	fam = sortFamily(fam)
	sp := computeSpread(fam)
	tauF, exactF := maxSunflower(fam)
	shifted := fullShiftSweep(fam, n)
	tauSF, exactSF := maxSunflower(shifted)
	ratio := 0.0
	if tauF > 0 {
		ratio = float64(tauSF) / float64(tauF)
	}
	r := row{
		ID:         id,
		Desc:       desc,
		K:          k,
		N:          n,
		Fcard:      len(fam),
		RStar:      sp.RStar,
		WitnessZ:   sp.WitnessZ,
		WitnessFZ:  sp.FZcard,
		WitnessF:   sp.Fcard,
		TauF:       tauF,
		TauSF:      tauSF,
		TauExact:   exactF && exactSF,
		TauFExact:  exactF,
		TauSFExact: exactSF,
		Ratio:      ratio,
		Seed:       seed,
		GenParams:  gen,
	}
	// include member lists for small families, and always for extremal rows.
	if len(fam) <= memberCap || (sp.RStar >= killRStar && ratio > killRatio) {
		r.Members = familyToSets(fam)
	}
	// include shifted members when this row is a kill or a notable inflation.
	if (sp.RStar >= killRStar && ratio > killRatio) || ratio >= 4.0 {
		r.ShiftedMem = familyToSets(shifted)
	}
	return r
}

func isFullStar(fam []uint, core []int, want int) bool {
	if len(fam) != want {
		return false
	}
	c := setToMask(core)
	for _, s := range fam {
		if s&c != c {
			return false
		}
	}
	return true
}
