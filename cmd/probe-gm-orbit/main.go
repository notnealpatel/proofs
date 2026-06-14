package main

// probe-gm-orbit: Track D probe for the Grochow-Moore group-orbit ansatz with
// MULTI-ORBIT, non-rank-1 seeds for <3,3,3> matrix multiplication
// (arXiv:1612.01527 line 401; task Or2). Tests whether any two-orbit S_4-
// symmetric decomposition with total orbit size <= 21 (tensor rank <= 22) is
// feasible -- which would be the first improvement on Laderman's rank 23 since
// 1976 -- or certifies infeasibility via a Groebner unit-ideal certificate.
//
// Pipeline (Hu7 route A-hybrid: Go builds, SageMath solves):
//   Stage 0  anchors: GM single-orbit rank-25 seed reconstructs MM exactly
//                     (foundations_test.go / anchor_test.go).
//   Stage 1  construct cubic polynomial constraint systems over Q(sqrt3) for
//                     every feasible orbit pair -> Or2-systems.json.
//   Stage 2  solve each via SageMath Groebner over Q(sqrt3): SOLUTION-FOUND /
//                     INFEASIBLE / UNDECIDED.
//   Stage 3  for any solution, reconstruct T and verify it equals <3,3,3>
//                     exactly over Q(sqrt3); report achieved tensor rank.
//
// Output: Or2-systems.json (the systems) and Or2-results.json (per-pair
// verdicts). Errors are never discarded; partial output is flushed on timeout.

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"os"
	"time"
)

func main() {
	timeout := flag.Duration("timeout", 30*time.Minute, "overall computation timeout")
	systemsOut := flag.String("systems", "/home/neal/p/proofs/.tasks/research/infodumps/Or2-systems.json", "output path for the polynomial systems")
	resultsOut := flag.String("results", "/home/neal/p/proofs/.tasks/research/infodumps/Or2-results.json", "output path for per-pair verdicts")
	maxTotal := flag.Int("maxtotal", 21, "max total orbit size (rank = 1 + total)")
	skipSolve := flag.Bool("skip-solve", false, "Stage 1 only: build systems, do not invoke SageMath")
	oe1 := flag.Bool("oe1", false, "Oe1 mode: sweep >=3-orbit S_4 configs instead of Or2's two-orbit run")
	oe1Out := flag.String("oe1-out", "/home/neal/p/proofs/.tasks/research/infodumps/Oe1-results.json", "Oe1 multi-orbit results path")
	minOrbits := flag.Int("min-orbits", 3, "Oe1: minimum number of orbits per config")
	flag.Parse()

	ctx, cancel := context.WithTimeout(context.Background(), *timeout)
	defer cancel()

	if *oe1 {
		if err := runOe1(ctx, *oe1Out, *minOrbits, *maxTotal); err != nil {
			fmt.Fprintf(os.Stderr, "probe-gm-orbit oe1: %v\n", err)
			os.Exit(1)
		}
		return
	}

	if err := run(ctx, *systemsOut, *resultsOut, *maxTotal, *skipSolve); err != nil {
		fmt.Fprintf(os.Stderr, "probe-gm-orbit: %v\n", err)
		os.Exit(1)
	}
}

// runOe1 sweeps the >=minOrbits S_4 configs with total orbit <= maxTotal,
// classifies each (INFEASIBLE-BY-COVERAGE / INFEASIBLE / SOLUTION-FOUND), and
// writes the per-config verdicts. If any coverage-passing config returns
// SOLUTION-FOUND it is flagged for reconstruction (rank < 23 would be a major
// result).
func runOe1(ctx context.Context, out string, minOrbits, maxTotal int) error {
	G := buildGroup()
	basisRR := rrStarBasis()
	fmt.Fprintf(os.Stderr, "probe-gm-orbit oe1: sweeping >=%d-orbit configs, total orbit <= %d (rank <= %d)\n",
		minOrbits, maxTotal, 1+maxTotal)
	recs := sweepMultiConfigs(ctx, G, basisRR, minOrbits, maxTotal)
	nCov, nSol, nInf := 0, 0, 0
	for _, r := range recs {
		switch r.Verdict {
		case "INFEASIBLE-BY-COVERAGE":
			nCov++
		case "SOLUTION-FOUND":
			nSol++
		case "INFEASIBLE":
			nInf++
		}
		fmt.Fprintf(os.Stderr, "  %-28s orbits=%d rank=%d cov=%d/137 vars=%d: %s\n",
			r.Config, r.NumOrbits, r.TensorRank, r.Covered, r.NumVars, r.Verdict)
	}

	// Family 3 (sigma-twist relaxed): end-to-end Gröbner cross-check on the best
	// decoupled single-orbit config (Z_2t, 131/137 covered) -- must be INFEASIBLE.
	dec := decoupledCertify(ctx, G, basisRR)
	recs = append(recs, dec)
	fmt.Fprintf(os.Stderr, "  %-28s orbits=%d rank=%d cov=%d/137 vars=%d: %s\n",
		dec.Config, dec.NumOrbits, dec.TensorRank, dec.Covered, dec.NumVars, dec.Verdict)

	fmt.Fprintf(os.Stderr, "probe-gm-orbit oe1: %d records; %d infeasible-by-coverage, %d unit-ideal, %d SOLUTION-FOUND\n",
		len(recs), nCov, nInf, nSol)
	return writeJSON(out, recs)
}

// run executes Stages 1-3 and writes both output files, flushing whatever is
// complete if the context is cancelled.
func run(ctx context.Context, systemsOut, resultsOut string, maxTotal int, skipSolve bool) error {
	G := buildGroup()
	basisRR := rrStarBasis()

	pairs := feasiblePairs(orbitCatalog(), maxTotal)
	fmt.Fprintf(os.Stderr, "probe-gm-orbit: %d feasible orbit pairs (max total orbit %d)\n", len(pairs), maxTotal)

	var systemRecs []systemRecord
	var resultRecs []resultRecord

	for _, pr := range pairs {
		select {
		case <-ctx.Done():
			fmt.Fprintf(os.Stderr, "probe-gm-orbit: timeout; flushing %d systems / %d results\n",
				len(systemRecs), len(resultRecs))
			writeJSON(systemsOut, systemRecs)
			writeJSON(resultsOut, resultRecs)
			return ctx.Err()
		default:
		}

		sys := buildPairSystem(G, basisRR, pr.t1, pr.t2)
		rec := summarizeSystem(pr, sys)
		systemRecs = append(systemRecs, rec)
		fmt.Fprintf(os.Stderr, "  built (%s/%s) orbits=%d+%d rank<=%d: %d vars, %d polys, deg %d\n",
			pr.t1.name, pr.t2.name, pr.t1.orbit, pr.t2.orbit, 1+pr.t1.orbit+pr.t2.orbit,
			sys.nvars, sys.nonTrivial, sys.maxDegree)

		if skipSolve {
			continue
		}

		res := solveAndVerify(ctx, G, basisRR, pr, sys)
		resultRecs = append(resultRecs, res)
		fmt.Fprintf(os.Stderr, "    verdict: %s%s\n", res.Verdict, res.Note)
	}

	if err := writeJSON(systemsOut, systemRecs); err != nil {
		return err
	}
	if !skipSolve {
		if err := writeJSON(resultsOut, resultRecs); err != nil {
			return err
		}
	}
	return nil
}

// writeJSON marshals v to path with indentation. Errors are returned, not
// discarded.
func writeJSON(path string, v any) error {
	data, err := json.MarshalIndent(v, "", "  ")
	if err != nil {
		return fmt.Errorf("marshal %s: %w", path, err)
	}
	if err := os.WriteFile(path, append(data, '\n'), 0o644); err != nil {
		return fmt.Errorf("write %s: %w", path, err)
	}
	return nil
}
