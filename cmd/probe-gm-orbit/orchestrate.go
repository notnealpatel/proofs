package main

// Orchestration: enumerate feasible orbit pairs, summarize the built systems for
// Or2-systems.json, and run Stage 2 (Sage Groebner) + Stage 3 (exact verify) to
// produce Or2-results.json records.

import (
	"context"
	"fmt"
	"math/big"
)

// pairChoice is an ordered pair of orbit templates to probe.
type pairChoice struct {
	t1, t2 orbitTemplate
}

// feasiblePairs enumerates unordered orbit-size pairs (allowing equal sizes and
// distinct conjugacy-class templates) with total orbit size <= maxTotal, per
// Or1 sec 3. Distinct stabilizer geometries of the same orbit size are kept
// separate (e.g. K_4 vs Z_4 at orbit 6; Z_2t vs Z_2d at orbit 12). To avoid
// duplicate (A,B)=(B,A) systems we only take i <= j over the catalog index.
func feasiblePairs(cat []orbitTemplate, maxTotal int) []pairChoice {
	var out []pairChoice
	for i := 0; i < len(cat); i++ {
		for j := i; j < len(cat); j++ {
			if cat[i].orbit+cat[j].orbit <= maxTotal {
				out = append(out, pairChoice{t1: cat[i], t2: cat[j]})
			}
		}
	}
	return out
}

// systemRecord is the Or2-systems.json entry for one pair: the constructed
// system's shape, logged against Or1's parameter/constraint estimates.
type systemRecord struct {
	Orbit1      string `json:"orbit1"`
	Orbit2      string `json:"orbit2"`
	OrbitSize1  int    `json:"orbit_size1"`
	OrbitSize2  int    `json:"orbit_size2"`
	TotalOrbit  int    `json:"total_orbit"`
	TensorRank  int    `json:"tensor_rank"`     // 1 + total orbit
	NumVars     int    `json:"num_vars"`        // free seed parameters
	NumConstr   int    `json:"num_constraints"` // nontrivial constraint polynomials
	MaxDegree   int    `json:"max_degree"`
	NumTriples  int    `json:"num_triples_examined"`
	Or1VarEst   int    `json:"or1_var_estimate"`   // Or1 sec 3 parameter estimate
	OverBudgetX string `json:"over_budget_factor"` // actual/estimate, flag if >10x
	SageProgram string `json:"sage_program"`       // emitted Stage-2 script
}

// summarizeSystem builds a systemRecord and emits the Sage program.
func summarizeSystem(pr pairChoice, sys *pairSystem) systemRecord {
	est := or1VarEstimate(pr.t1) + or1VarEstimate(pr.t2)
	over := "n/a"
	if est > 0 {
		over = ratString(sys.nvars, est)
	}
	return systemRecord{
		Orbit1:      pr.t1.name,
		Orbit2:      pr.t2.name,
		OrbitSize1:  pr.t1.orbit,
		OrbitSize2:  pr.t2.orbit,
		TotalOrbit:  pr.t1.orbit + pr.t2.orbit,
		TensorRank:  1 + pr.t1.orbit + pr.t2.orbit,
		NumVars:     sys.nvars,
		NumConstr:   sys.nonTrivial,
		MaxDegree:   sys.maxDegree,
		NumTriples:  sys.numTriples,
		Or1VarEst:   est,
		OverBudgetX: over,
		SageProgram: sageScript(sys),
	}
}

// or1VarEstimate returns Or1 sec 3's per-orbit parameter estimate by stabilizer
// type (S_3 -> 2, K_4/Z_4 -> 3, Z_3 -> 3, Z_2 -> 5).
func or1VarEstimate(t orbitTemplate) int {
	switch t.orbit {
	case 4:
		return 2
	case 6:
		return 3
	case 8:
		return 3
	case 12:
		return 5
	default:
		return 0
	}
}

// ratString returns "p/q" reduced, for the over-budget factor display.
func ratString(p, q int) string {
	return new(big.Rat).SetFrac(big.NewInt(int64(p)), big.NewInt(int64(q))).RatString()
}

// resultRecord is the Or2-results.json entry for one pair.
type resultRecord struct {
	Orbit1     string              `json:"orbit1"`
	Orbit2     string              `json:"orbit2"`
	TotalOrbit int                 `json:"total_orbit"`
	TensorRank int                 `json:"tensor_rank"`
	Verdict    string              `json:"verdict"` // SOLUTION-FOUND / INFEASIBLE / UNDECIDED / ERROR
	Note       string              `json:"note,omitempty"`
	Dimension  *int                `json:"dimension,omitempty"`
	NumPoints  *int                `json:"num_points,omitempty"`
	Groebner   []string            `json:"groebner,omitempty"`
	Points     []map[string]string `json:"points,omitempty"`
	Verified   *bool               `json:"verified_equals_mm,omitempty"`
}

// solveAndVerify runs Stage 2 (Sage Groebner) and, on SOLUTION-FOUND with
// rational points, Stage 3 (exact reconstruction check). It never discards the
// underlying error; on solver failure it records an ERROR/UNDECIDED verdict with
// the reason in Note so the campaign continues.
func solveAndVerify(ctx context.Context, G *Group, basisRR []Mat, pr pairChoice, sys *pairSystem) resultRecord {
	rec := resultRecord{
		Orbit1:     pr.t1.name,
		Orbit2:     pr.t2.name,
		TotalOrbit: pr.t1.orbit + pr.t2.orbit,
		TensorRank: 1 + pr.t1.orbit + pr.t2.orbit,
	}
	// Per Hu7 (route A-hybrid) SageMath OWNS the Stage-2 feasibility verdict:
	// Groebner over Q(sqrt3) is a solved problem delegated to a mature CAS, not
	// reimplemented in Go. The Go constant-generator scan below is a cheap
	// independent sanity check only; it never overrides Sage's verdict, it only
	// flags a disagreement (which would mean a bug in one of the two layers).
	certInfeas, certVal := constantInfeasible(sys)

	res, raw, err := runSage(ctx, "Or2-"+pr.t1.name+"_"+pr.t2.name, sageScript(sys))
	if err != nil {
		rec.Verdict = "UNDECIDED"
		rec.Note = fmt.Sprintf(" (sage error: %v)", err)
		_ = raw
		return rec
	}
	rec.Verdict = res.Verdict // Sage is authoritative.
	rec.Dimension = res.Dimension
	rec.NumPoints = res.NumPoints
	rec.Groebner = res.Groebner
	rec.Points = res.Points

	// Cross-check Go's cheap necessary-condition scan against Sage.
	switch {
	case certInfeas && res.Verdict != "INFEASIBLE":
		rec.Note = fmt.Sprintf(" (CONFLICT: Go found constant %s in the generators yet sage returned %s; investigate before trusting)",
			certVal.String(), res.Verdict)
	case certInfeas:
		rec.Note = fmt.Sprintf(" (Go sanity check agrees: constant %s among generators => unit ideal)", certVal.String())
	case res.Verdict == "INFEASIBLE":
		rec.Note = " (sage Groebner = [1], unit ideal; no constant generator, infeasibility is nonlinear)"
	case res.Verdict == "SOLUTION-FOUND":
		rec.Note = stage3Note(res)
		// Stage 3 (Go): exact reconstruction from a rational point, when available.
		if v, ok := tryStage3(G, basisRR, pr, sys, res); ok {
			rec.Verified = &v
		}
	}
	return rec
}

// stage3Note summarizes the Stage-3 situation for a SOLUTION-FOUND pair. Full
// reconstruction over Q(sqrt3) is performed when a point's coordinates are
// expressible there; otherwise we record that the human/Stage-3 follow-up is
// needed (the variety may live in a larger field).
func stage3Note(res *sageResult) string {
	if res.Dimension != nil && *res.Dimension > 0 {
		return fmt.Sprintf(" (positive-dim solution set, dim %d; family of decompositions)", *res.Dimension)
	}
	if res.NumPoints != nil {
		return fmt.Sprintf(" (%d isolated solution points; see points[] for Stage-3 reconstruction)", *res.NumPoints)
	}
	return ""
}
