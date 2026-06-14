package main

import "testing"

// TestConstantObstruction locates, for the S_3/S_3 pair, the rho⊗rho* basis
// triples whose orbit contribution is IDENTICALLY zero (so the constraint
// collapses to the bare constant tr(A)tr(B)tr(C) - tr(ABC)). A nonzero such
// constant is the infeasibility certificate. This documents *why* the
// constrained two-orbit ansatz fails where GM's unconstrained single orbit
// works: certain Fourier projections cannot be reached from H-fixed seed spaces.
func TestConstantObstruction(t *testing.T) {
	G := buildGroup()
	basisRR := rrStarBasis()
	names := []string{"id", "box_x", "box_y", "s1", "s2", "s3", "a1", "a2", "a3"}

	fb := fixedBasis(G, G.subgroup(genS3)) // S_3-fixed seed space (dim 2)
	// symbolic seed for one S_3 orbit
	seeds := orbitSeedTriple(G.sigma, fb, 0)
	gConj := make([][3]PolyMat, len(G.elems))
	for gi, g := range G.elems {
		for f := 0; f < 3; f++ {
			gConj[gi][f] = conjPoly(G.rho[g], seeds[f])
		}
	}

	found := 0
	for ai := range basisRR {
		for bi := range basisRR {
			for ci := range basisRR {
				A, B, C := basisRR[ai], basisRR[bi], basisRR[ci]
				orbit := newPoly()
				for gi := range G.elems {
					la := frobPoly(A, gConj[gi][0])
					lb := frobPoly(B, gConj[gi][1])
					lc := frobPoly(C, gConj[gi][2])
					orbit = addPoly(orbit, mulPoly(mulPoly(la, lb), lc))
				}
				constVal := trace(A).Mul(trace(B)).Mul(trace(C)).Sub(trProd(A, B, C))
				if orbit.isZero() && !constVal.IsZero() {
					found++
					if found <= 6 {
						t.Logf("constant obstruction at (%s,%s,%s): orbit term ≡ 0 but residual = %s",
							names[ai], names[bi], names[ci], constVal.String())
					}
				}
			}
		}
	}
	if found == 0 {
		t.Fatalf("expected at least one constant-obstruction triple for S_3 single orbit")
	}
	t.Logf("total constant-obstruction triples (single S_3 orbit): %d", found)
}

// TestGMSeedAvoidsObstruction confirms GM's full-orbit (H = {e}) seed has a
// NONZERO orbit contribution exactly on the triples that obstruct the H-fixed
// ansatz, i.e. the obstruction is specific to the restricted seed space, not a
// modeling bug. We use GM's published rank-1 seed.
func TestGMSeedAvoidsObstruction(t *testing.T) {
	G := buildGroup()
	basisRR := rrStarBasis()
	// GM first-family seed (concrete), single full orbit.
	m := halfMat([n][n]int64{{-1, 1, 0}, {1, -1, 0}, {1, -1, 0}})
	m2 := conj(G.sigma, m)
	m3 := conj(matMulQ3(G.sigma, G.sigma), m)

	// The decomposition is valid, so EVERY triple residual is zero for GM's
	// seed (already covered by TestAnchorGMSingleOrbit). Here we additionally
	// confirm the orbit contribution is itself nonzero on the obstructed
	// triples (so the constant is cancelled by a live orbit term, which the
	// H-fixed space cannot produce).
	fbS3 := fixedBasis(G, G.subgroup(genS3))
	seedsSym := orbitSeedTriple(G.sigma, fbS3, 0)
	gConj := make([][3]PolyMat, len(G.elems))
	for gi, g := range G.elems {
		for f := 0; f < 3; f++ {
			gConj[gi][f] = conjPoly(G.rho[g], seedsSym[f])
		}
	}
	checked := 0
	for ai := range basisRR {
		for bi := range basisRR {
			for ci := range basisRR {
				A, B, C := basisRR[ai], basisRR[bi], basisRR[ci]
				symbOrbit := newPoly()
				for gi := range G.elems {
					la := frobPoly(A, gConj[gi][0])
					lb := frobPoly(B, gConj[gi][1])
					lc := frobPoly(C, gConj[gi][2])
					symbOrbit = addPoly(symbOrbit, mulPoly(mulPoly(la, lb), lc))
				}
				constVal := trace(A).Mul(trace(B)).Mul(trace(C)).Sub(trProd(A, B, C))
				if symbOrbit.isZero() && !constVal.IsZero() {
					// GM's full-orbit term on this triple:
					gmOrbit := q3Zero
					for _, g := range G.elems {
						gm := G.rho[g]
						f1 := frob(conj(gm, m), A)
						f2 := frob(conj(gm, m2), B)
						f3 := frob(conj(gm, m3), C)
						gmOrbit = gmOrbit.Add(f1.Mul(f2).Mul(f3))
					}
					// GM seed must supply exactly -constVal on this triple.
					if !gmOrbit.Add(constVal).IsZero() {
						t.Fatalf("GM orbit does not cancel constant at (%d,%d,%d): orbit=%s const=%s",
							ai, bi, ci, gmOrbit.String(), constVal.String())
					}
					checked++
				}
			}
		}
	}
	if checked == 0 {
		t.Fatal("no obstructed triples checked")
	}
	t.Logf("verified GM full-orbit cancels the constant on %d obstructed triples (H-fixed space cannot)", checked)
}
