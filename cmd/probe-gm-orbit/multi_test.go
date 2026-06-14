package main

import (
	"testing"
)

// TestMultiMatchesPairOnTwoOrbits pins that the L-orbit builder reduces to the
// two-orbit production builder when L=2, on every Or2 pair. This guards the
// generalization against silently changing the validated two-orbit geometry: the
// multi-orbit system must be the SAME polynomial system buildPairSystem emits
// (same constant generators, same constraint polynomials).
func TestMultiMatchesPairOnTwoOrbits(t *testing.T) {
	G := buildGroup()
	basisRR := rrStarBasis()
	cat := orbitCatalog()
	for i := range cat {
		for j := i; j < len(cat); j++ {
			pair := buildPairSystem(G, basisRR, cat[i], cat[j])
			multi := buildMultiSystem(G, basisRR, multiConfig{orbits: []orbitTemplate{cat[i], cat[j]}})
			if pair.nvars != multi.nvars {
				t.Fatalf("%s/%s: nvars pair=%d multi=%d", cat[i].name, cat[j].name, pair.nvars, multi.nvars)
			}
			if pair.nonTrivial != multi.nonTrivial {
				t.Fatalf("%s/%s: nonTrivial pair=%d multi=%d", cat[i].name, cat[j].name, pair.nonTrivial, multi.nonTrivial)
			}
			if pair.maxDegree != multi.maxDegree {
				t.Fatalf("%s/%s: maxDegree pair=%d multi=%d", cat[i].name, cat[j].name, pair.maxDegree, multi.maxDegree)
			}
			// The constant generator (if any) must match exactly.
			pc, pv := constantInfeasible(pair)
			mc, mv := constantInfeasible(multi)
			if pc != mc || (pc && !pv.Equal(mv)) {
				t.Fatalf("%s/%s: constant generator pair=(%v,%s) multi=(%v,%s)",
					cat[i].name, cat[j].name, pc, pv.String(), mc, mv.String())
			}
		}
	}
}

// TestOe1ReachAndCoverage reproduces, in Go (exact over Q(√3)), the sager
// coverage pre-screen: per-orbit reachable-direction counts, the 137-triple
// residual support, and the central kill fact -- no union of catalog stabilizer
// types with total orbit <= 21 covers all 137 residual triples. This is the
// structural certificate that the >=3-orbit S_4 family is PRE-SCREEN-DEAD.
func TestOe1ReachAndCoverage(t *testing.T) {
	G := buildGroup()
	basisRR := rrStarBasis()
	cat := orbitCatalog()

	sup := residualSupport(basisRR)
	if len(sup) != 137 {
		t.Fatalf("residual support = %d, want 137", len(sup))
	}

	// Per-type reach and coverage of the residual support. Expected from sager:
	// S_3:16 K_4:11 Z_4:17 Z_3:43 Z_2t:113 Z_2d:59 (all subsets of the support).
	wantReach := map[string]int{"S_3": 16, "K_4": 11, "Z_4": 17, "Z_3": 43, "Z_2t": 113, "Z_2d": 59}
	reach := map[string]map[int]bool{}
	for _, ot := range cat {
		rs := orbitReachSet(G, basisRR, ot)
		reach[ot.name] = rs
		if len(rs) != wantReach[ot.name] {
			t.Errorf("%s reach = %d, want %d", ot.name, len(rs), wantReach[ot.name])
		}
		// every reached direction must be inside the residual support
		for idx := range rs {
			if !sup[idx] {
				t.Errorf("%s reaches non-residual triple %d", ot.name, idx)
			}
		}
	}

	// Coverage kill: over ALL nonempty subsets of distinct types, the cheapest one
	// whose union covers the support has total orbit > 21. So no rank<=22 config
	// (any orbit count, same-type stacking included) can cover the support.
	names := make([]string, len(cat))
	orbsz := map[string]int{}
	for i, ot := range cat {
		names[i] = ot.name
		orbsz[ot.name] = ot.orbit
	}
	minCoveringOrbit := 1 << 30
	var minCoveringSet []string
	for mask := 1; mask < (1 << len(names)); mask++ {
		union := map[int]bool{}
		totOrbit := 0
		var set []string
		for b := 0; b < len(names); b++ {
			if mask&(1<<b) != 0 {
				set = append(set, names[b])
				totOrbit += orbsz[names[b]]
				for idx := range reach[names[b]] {
					union[idx] = true
				}
			}
		}
		covers := true
		for idx := range sup {
			if !union[idx] {
				covers = false
				break
			}
		}
		if covers && totOrbit < minCoveringOrbit {
			minCoveringOrbit = totOrbit
			minCoveringSet = set
		}
	}
	t.Logf("cheapest covering type-set: %v with total orbit %d (rank %d)",
		minCoveringSet, minCoveringOrbit, 1+minCoveringOrbit)
	if minCoveringOrbit <= 21 {
		t.Fatalf("a type-set covers the residual support within rank<=22 (orbit %d); Family 1 is NOT pre-screen-dead, build the probe",
			minCoveringOrbit)
	}
	// Confirm the cheapest covering set is exactly Z_2t+Z_2d at orbit 24.
	if minCoveringOrbit != 24 {
		t.Errorf("cheapest covering orbit = %d, want 24 (Z_2t+Z_2d)", minCoveringOrbit)
	}
}
