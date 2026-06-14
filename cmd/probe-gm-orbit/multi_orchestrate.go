package main

// Oe1 driver: enumerate >=3-orbit S_4 configs (total orbit <= maxTotal) and, for
// the ones that PASS the coverage necessary-condition (union of orbit-type reach
// sets covers the 137-triple residual support), solve via sager Groebner exactly
// as Or2 did. Configs that FAIL coverage are recorded INFEASIBLE-BY-COVERAGE
// without a Groebner call (they provably contain a constant generator). This
// keeps the sweep cheap while still certifying the coverage-passing survivors
// (if any) by full Groebner.
//
// The coverage pre-screen (TestOe1ReachAndCoverage / the sager scripts) already
// proves NO config with total orbit <= 21 passes coverage. This driver makes that
// operational: it confirms every >=3-orbit config in budget is killed, and emits
// a Groebner certificate for the single most-ambitious (max-coverage) one as an
// end-to-end cross-check against Or2's pipeline.

import (
	"context"
	"fmt"
	"sort"
)

// enumerateMultiConfigs returns all multisets of >=minOrbits catalog orbit
// templates with total orbit size <= maxTotal. Same-type repeats are allowed
// (independent seeds). Configs are canonicalized by sorted catalog index to avoid
// permutation duplicates.
func enumerateMultiConfigs(cat []orbitTemplate, minOrbits, maxTotal int) []multiConfig {
	var out []multiConfig
	var rec func(start, remaining int, cur []orbitTemplate, curTotal int)
	rec = func(start, remaining int, cur []orbitTemplate, curTotal int) {
		if len(cur) >= minOrbits {
			cp := make([]orbitTemplate, len(cur))
			copy(cp, cur)
			out = append(out, multiConfig{orbits: cp})
		}
		for i := start; i < len(cat); i++ {
			if curTotal+cat[i].orbit > maxTotal {
				continue
			}
			rec(i, remaining, append(cur, cat[i]), curTotal+cat[i].orbit)
		}
	}
	rec(0, maxTotal, nil, 0)
	return out
}

// configCoverage returns the number of residual-support triples reached by the
// union of the config's orbit-type reach sets, and whether it covers all 137.
// Reach sets are cached per type by the caller for speed.
func configCoverage(cfg multiConfig, reachByType map[string]map[int]bool, support map[int]bool) (covered int, coversAll bool) {
	union := map[int]bool{}
	seen := map[string]bool{}
	for _, o := range cfg.orbits {
		if seen[o.name] {
			continue
		}
		seen[o.name] = true
		for idx := range reachByType[o.name] {
			if support[idx] {
				union[idx] = true
			}
		}
	}
	covered = len(union)
	coversAll = covered == len(support)
	return
}

// multiResultRecord is the Oe1-results.json entry for one >=3-orbit config.
type multiResultRecord struct {
	Config       string   `json:"config"`
	NumOrbits    int      `json:"num_orbits"`
	TotalOrbit   int      `json:"total_orbit"`
	TensorRank   int      `json:"tensor_rank"`
	Covered      int      `json:"residual_dirs_covered"` // of 137
	NumVars      int      `json:"num_vars"`
	Verdict      string   `json:"verdict"` // INFEASIBLE-BY-COVERAGE / INFEASIBLE / SOLUTION-FOUND / UNDECIDED
	ConstCert    string   `json:"const_certificate,omitempty"`
	Groebner     []string `json:"groebner,omitempty"`
	Note         string   `json:"note,omitempty"`
	GroebnerRun  bool     `json:"groebner_run"`
}

// sweepMultiConfigs builds and classifies every >=minOrbits config in budget.
// Coverage-failing configs get verdict INFEASIBLE-BY-COVERAGE (with the missed
// residual count and a sample constant certificate from the Go-built system).
// Coverage-passing configs (none exist at <=21, but the code does not assume it)
// are solved by sager Groebner end-to-end. Additionally, the single max-coverage
// config is ALWAYS run through sager as a cross-check certificate.
func sweepMultiConfigs(ctx context.Context, G *Group, basisRR []Mat, minOrbits, maxTotal int) []multiResultRecord {
	cat := orbitCatalog()
	support := residualSupport(basisRR)
	reachByType := map[string]map[int]bool{}
	for _, ot := range cat {
		reachByType[ot.name] = orbitReachSet(G, basisRR, ot)
	}

	cfgs := enumerateMultiConfigs(cat, minOrbits, maxTotal)
	// Sort by coverage desc so the most ambitious comes first.
	type scored struct {
		cfg     multiConfig
		covered int
		all     bool
	}
	scoredCfgs := make([]scored, 0, len(cfgs))
	for _, c := range cfgs {
		cov, all := configCoverage(c, reachByType, support)
		scoredCfgs = append(scoredCfgs, scored{cfg: c, covered: cov, all: all})
	}
	sort.SliceStable(scoredCfgs, func(i, j int) bool {
		if scoredCfgs[i].covered != scoredCfgs[j].covered {
			return scoredCfgs[i].covered > scoredCfgs[j].covered
		}
		return scoredCfgs[i].cfg.totalOrbit() < scoredCfgs[j].cfg.totalOrbit()
	})

	var recs []multiResultRecord
	maxCovRun := false
	for _, sc := range scoredCfgs {
		select {
		case <-ctx.Done():
			return recs
		default:
		}
		cfg := sc.cfg
		rec := multiResultRecord{
			Config:     cfg.label(),
			NumOrbits:  len(cfg.orbits),
			TotalOrbit: cfg.totalOrbit(),
			TensorRank: 1 + cfg.totalOrbit(),
			Covered:    sc.covered,
		}

		// Build the Go system to get nvars and (for coverage-fail) a constant cert.
		sys := buildMultiSystem(G, basisRR, cfg)
		rec.NumVars = sys.nvars

		if !sc.all {
			rec.Verdict = "INFEASIBLE-BY-COVERAGE"
			if c, v := constantInfeasible(sys); c {
				rec.ConstCert = v.String()
				rec.Note = fmt.Sprintf("union reaches %d/%d residual dirs; %d unreached => constant generator %s in the Go-built ideal (unit ideal)",
					sc.covered, len(support), len(support)-sc.covered, v.String())
			} else {
				// Coverage failed but the bare constant did not survive symbolic
				// combination -- still infeasible by coverage, but flag for a look.
				rec.Note = fmt.Sprintf("union reaches %d/%d residual dirs; %d unreached (coverage necessary condition fails)",
					sc.covered, len(support), len(support)-sc.covered)
			}

			// Cross-check the single MAX-coverage config end-to-end with sager
			// (one Groebner call) to certify the coverage-fail prediction matches
			// the actual Gröbner unit ideal, mirroring Or2.
			if !maxCovRun {
				maxCovRun = true
				rec.GroebnerRun = true
				res, raw, err := runSage(ctx, "Oe1-multi-"+cfg.label(), sageScript(sys))
				if err != nil {
					rec.Note += fmt.Sprintf(" | sager cross-check error: %v", err)
					_ = raw
				} else {
					rec.Groebner = res.Groebner
					rec.Note += fmt.Sprintf(" | sager Gröbner cross-check: %s", res.Verdict)
				}
			}
			recs = append(recs, rec)
			continue
		}

		// Coverage passes (does not occur at <=21, but handle it): full Gröbner.
		rec.GroebnerRun = true
		res, raw, err := runSage(ctx, "Oe1-multi-"+cfg.label(), sageScript(sys))
		if err != nil {
			rec.Verdict = "UNDECIDED"
			rec.Note = fmt.Sprintf("sager error: %v", err)
			_ = raw
		} else {
			rec.Verdict = res.Verdict
			rec.Groebner = res.Groebner
			if res.Verdict == "SOLUTION-FOUND" {
				rec.Note = "COVERAGE-PASSING SOLUTION CANDIDATE -- STOP and reconstruct (rank " +
					fmt.Sprint(rec.TensorRank) + ")"
			}
		}
		recs = append(recs, rec)
	}
	return recs
}

// decoupledCertify runs one end-to-end sager Gröbner cross-check on the best
// (most-covering, lowest-rank) DECOUPLED single-orbit config -- Z_2t alone,
// reaching 131/137 of the residual directions at rank 13. It must come back
// INFEASIBLE (unit ideal), confirming that even decoupled, the 6 unreachable
// antisymmetric directions force a constant generator. This gives the Family-3
// kill the same Go-construct + sager-Gröbner certification weight as Or2/Family1.
func decoupledCertify(ctx context.Context, G *Group, basisRR []Mat) multiResultRecord {
	cat := orbitCatalog()
	var z2t orbitTemplate
	for _, o := range cat {
		if o.name == "Z_2t" {
			z2t = o
		}
	}
	cfg := multiConfig{orbits: []orbitTemplate{z2t}}
	support := residualSupport(basisRR)
	dr := decoupledReachSet(G, basisRR, z2t)
	covered := 0
	for idx := range dr {
		if support[idx] {
			covered++
		}
	}
	sys := buildDecoupledSystem(G, basisRR, cfg)
	rec := multiResultRecord{
		Config:      "DECOUPLED:" + cfg.label(),
		NumOrbits:   1,
		TotalOrbit:  cfg.totalOrbit(),
		TensorRank:  1 + cfg.totalOrbit(),
		Covered:     covered,
		NumVars:     sys.nvars,
		GroebnerRun: true,
	}
	c, v := constantInfeasible(sys)
	res, raw, err := runSage(ctx, "Oe1-decoupled-"+cfg.label(), sageScript(sys))
	if err != nil {
		rec.Verdict = "UNDECIDED"
		rec.Note = fmt.Sprintf("sager error: %v", err)
		_ = raw
		return rec
	}
	rec.Verdict = res.Verdict
	rec.Groebner = res.Groebner
	if c {
		rec.ConstCert = v.String()
	}
	rec.Note = fmt.Sprintf("decoupled Z_2t reaches %d/%d residual dirs; misses the 6 antisymmetric (a1,a2,a3) directions => constant generator %s; sager Gröbner: %s",
		covered, len(support), v.String(), res.Verdict)
	return rec
}
