package main

import "testing"

// TestOs1FindObstructedTriple locates, for the S_3/Z_3 pair, a rho⊗rho* basis
// triple (A,B,C) whose two-orbit symbolic contribution is IDENTICALLY zero. On
// such a triple the constraint reduces to the bare constant
// tr(A)tr(B)tr(C) - <T, A⊗B⊗C>; perturbing the target there forces a nonzero
// constant generator => unit ideal => INFEASIBLE. This is the lever the negative
// control pulls, and it is the SAME mechanism that produced Or2's 18 verdicts.
// Diagnostic (run with -v) feeding the negative control's choice of triple.
func TestOs1FindObstructedTriple(t *testing.T) {
	G := buildGroup()
	basisRR := rrStarBasis()
	t1, t2, fb1, fb2 := os1Pair(G)
	_ = t1
	_ = t2

	seedsSym := [][3]PolyMat{
		orbitSeedTriple(G.sigma, fb1, 0),
		orbitSeedTriple(G.sigma, fb2, len(fb1)),
	}
	gConj := make([][][3]PolyMat, 2)
	for k := 0; k < 2; k++ {
		gConj[k] = make([][3]PolyMat, len(G.elems))
		for gi, g := range G.elems {
			for f := 0; f < 3; f++ {
				gConj[k][gi][f] = conjPoly(G.rho[g], seedsSym[k][f])
			}
		}
	}
	names := []string{"id", "box_x", "box_y", "s1", "s2", "s3", "a1", "a2", "a3"}
	found := 0
	for ai := range basisRR {
		for bi := range basisRR {
			for ci := range basisRR {
				orbit := newPoly()
				for k := 0; k < 2; k++ {
					for gi := range G.elems {
						la := frobPoly(basisRR[ai], gConj[k][gi][0])
						lb := frobPoly(basisRR[bi], gConj[k][gi][1])
						lc := frobPoly(basisRR[ci], gConj[k][gi][2])
						orbit = addPoly(orbit, mulPoly(mulPoly(la, lb), lc))
					}
				}
				if orbit.isZero() {
					if found < 8 {
						t.Logf("obstructed triple idx (%d,%d,%d) = (%s,%s,%s): two-orbit contribution identically 0",
							ai, bi, ci, names[ai], names[bi], names[ci])
					}
					found++
				}
			}
		}
	}
	t.Logf("S_3/Z_3 two-orbit obstructed triples: %d of 729", found)
	if found == 0 {
		t.Fatal("expected at least one obstructed triple for S_3/Z_3")
	}

	// Confirm the canonical box⊗box obstruction triple (id, box_x, box_x) =
	// (0,1,1) is among them, with identically-zero orbit term. This is the exact
	// direction Or2 named as the geometric obstruction; the negative control
	// perturbs the target here.
	A, B, C := basisRR[0], basisRR[1], basisRR[1]
	orbit := newPoly()
	for k := 0; k < 2; k++ {
		for gi := range G.elems {
			la := frobPoly(A, gConj[k][gi][0])
			lb := frobPoly(B, gConj[k][gi][1])
			lc := frobPoly(C, gConj[k][gi][2])
			orbit = addPoly(orbit, mulPoly(mulPoly(la, lb), lc))
		}
	}
	if !orbit.isZero() {
		t.Fatalf("(id,box_x,box_x) orbit term is NOT identically zero: %v", orbit.terms)
	}
	t.Logf("(id,box_x,box_x): orbit term identically 0; tr(id)tr(box_x)tr(box_x) - trProd = %s",
		trace(A).Mul(trace(B)).Mul(trace(C)).Sub(trProd(A, B, C)).String())
}
