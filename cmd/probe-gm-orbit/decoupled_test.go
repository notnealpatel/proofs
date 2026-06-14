package main

import "testing"

// TestOe1DecoupledReach reproduces in Go (exact over Q(√3)) the sager Family-3
// pre-screen: per-type DECOUPLED reach counts and the central kill fact -- the 6
// totally-antisymmetric (a1,a2,a3) determinant-permutation directions (residual
// ±1) are reachable by NO catalog stabilizer even with the sigma-twist relaxed.
// This is the structural certificate that the sigma-twist-relaxed family is
// PRE-SCREEN-DEAD.
func TestOe1DecoupledReach(t *testing.T) {
	G := buildGroup()
	basisRR := rrStarBasis()
	cat := orbitCatalog()
	sup := residualSupport(basisRR)

	// Decoupling enlarges reach for Z_4/Z_2t/Z_2d vs the twisted counts.
	wantDecoupled := map[string]int{"S_3": 16, "K_4": 11, "Z_4": 35, "Z_3": 43, "Z_2t": 131, "Z_2d": 89}
	reach := map[string]map[int]bool{}
	for _, ot := range cat {
		rs := decoupledReachSet(G, basisRR, ot)
		reach[ot.name] = rs
		if len(rs) != wantDecoupled[ot.name] {
			t.Errorf("%s decoupled reach = %d, want %d", ot.name, len(rs), wantDecoupled[ot.name])
		}
		for idx := range rs {
			if !sup[idx] {
				t.Errorf("%s decoupled reaches non-residual triple %d", ot.name, idx)
			}
		}
	}

	// The 6 antisymmetric directions (a1,a2,a3)=(6,7,8) and permutations.
	anti := [][3]int{{6, 7, 8}, {6, 8, 7}, {7, 6, 8}, {7, 8, 6}, {8, 6, 7}, {8, 7, 6}}
	for _, tr := range anti {
		idx := 81*tr[0] + 9*tr[1] + tr[2]
		// must be a residual direction (residual ±1)
		A, B, C := basisRR[tr[0]], basisRR[tr[1]], basisRR[tr[2]]
		r := trace(A).Mul(trace(B)).Mul(trace(C)).Sub(trProd(A, B, C))
		if r.IsZero() {
			t.Fatalf("antisymmetric triple %v has zero residual; expected ±1", tr)
		}
		// must be unreachable by EVERY catalog stabilizer (decoupled)
		for _, ot := range cat {
			if reach[ot.name][idx] {
				t.Fatalf("antisymmetric triple %v IS reached by decoupled %s -- Family 3 not pre-screen-dead, build the probe", tr, ot.name)
			}
		}
	}

	// Union of all decoupled catalog reach sets misses exactly the 6 antisym dirs.
	union := map[int]bool{}
	for _, ot := range cat {
		for idx := range reach[ot.name] {
			union[idx] = true
		}
	}
	missed := 0
	for idx := range sup {
		if !union[idx] {
			missed++
		}
	}
	if missed != 6 {
		t.Errorf("union of decoupled reach sets misses %d residual dirs, want 6 (the antisymmetric block)", missed)
	}
}
