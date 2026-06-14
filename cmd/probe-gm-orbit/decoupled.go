package main

// Oe1 Family 3: the GM group-orbit ansatz with the sigma-twist coupling RELAXED.
// GM couples m2=sigma m1 sigma^-1, m3=sigma^2 m1 sigma^-2 (1612.01527 eq z3orbit),
// which makes the ansatz Z_3-symmetric (invariant under cyclic rotation of the 3
// tensor factors) -- matching the MM tensor's own cyclic symmetry. Relaxing it
// lets m1, m2, m3 be INDEPENDENT free seeds in the same H-fixed space (3x the
// parameters per orbit), at the cost of the cyclic guarantee. The tensor rank is
// UNCHANGED: the orbit of the rank-1 tensor m1(x)m2(x)m3 under diagonal
// conjugation still has |orbit| = 24/|H| rank-1 terms whether or not the seeds
// are twist-coupled.
//
// Decoupling genuinely enlarges the reachable directions for some stabilizers
// (Z_4: 17->35, Z_2t: 113->131, Z_2d: 59->89 of the 137 residual directions),
// but 6 residual directions -- the totally-antisymmetric (a1,a2,a3) determinant
// permutations, residual +/-1 -- remain unreachable by EVERY catalog stabilizer
// (decoupled or twisted), because rho'^{(x)3}'s diagonal-trivial lives in the
// antisymmetric component that only an UNRESTRICTED (H={e}) seed populates. So
// every rank<=22 decoupled config still has a constant generator => unit ideal.

// buildDecoupledSystem constructs the cubic constraint system for an L-orbit
// config with INDEPENDENT m1,m2,m3 per orbit (sigma-twist relaxed) against the MM
// target. Each orbit owns 3*dim variables: m1 block, m2 block, m3 block. This is
// the Family-3 analogue of buildMultiSystem; reach/coverage is decided by
// decoupledReachSet upstream so this only ever runs on configs worth a Groebner
// cross-check.
func buildDecoupledSystem(G *Group, basisRR []Mat, cfg multiConfig) *pairSystem {
	L := len(cfg.orbits)
	fbs := make([][]Mat, L)
	// Each orbit: three independent seeds on consecutive variable blocks.
	seeds := make([][3]PolyMat, L)
	nvars := 0
	for k, o := range cfg.orbits {
		fbs[k] = fixedBasis(G, G.subgroup(o.gens))
		d := len(fbs[k])
		m1 := seedPolyMat(fbs[k], nvars)
		m2 := seedPolyMat(fbs[k], nvars+d)
		m3 := seedPolyMat(fbs[k], nvars+2*d)
		seeds[k] = [3]PolyMat{m1, m2, m3}
		nvars += 3 * d
	}

	gConj := make([][][3]PolyMat, L)
	for k := 0; k < L; k++ {
		gConj[k] = make([][3]PolyMat, len(G.elems))
		for gi, g := range G.elems {
			gm := G.rho[g]
			for f := 0; f < 3; f++ {
				gConj[k][gi][f] = conjPoly(gm, seeds[k][f])
			}
		}
	}

	sys := &pairSystem{nvars: nvars}
	for ai := range basisRR {
		A := basisRR[ai]
		for bi := range basisRR {
			B := basisRR[bi]
			for ci := range basisRR {
				C := basisRR[ci]
				sys.numTriples++
				constVal := trace(A).Mul(trace(B)).Mul(trace(C)).Sub(trProd(A, B, C))
				P := constPoly(constVal)
				for k := 0; k < L; k++ {
					for gi := range G.elems {
						la := frobPoly(A, gConj[k][gi][0])
						if la.isZero() {
							continue
						}
						lb := frobPoly(B, gConj[k][gi][1])
						if lb.isZero() {
							continue
						}
						lc := frobPoly(C, gConj[k][gi][2])
						if lc.isZero() {
							continue
						}
						P = addPoly(P, mulPoly(mulPoly(la, lb), lc))
					}
				}
				if !P.isZero() {
					sys.polys = append(sys.polys, P)
					sys.nonTrivial++
					if d := polyDegree(P); d > sys.maxDegree {
						sys.maxDegree = d
					}
				}
			}
		}
	}
	return sys
}

// decoupledReachSet returns the reachable-direction set for a single DECOUPLED
// orbit of stabilizer type t (independent m1,m2,m3 in the H-fixed space). Used by
// the Family-3 coverage pre-screen. Mirrors orbitReachSet but with three free
// seed blocks instead of the sigma-twisted triple.
func decoupledReachSet(G *Group, basisRR []Mat, t orbitTemplate) map[int]bool {
	fb := fixedBasis(G, G.subgroup(t.gens))
	d := len(fb)
	m1 := seedPolyMat(fb, 0)
	m2 := seedPolyMat(fb, d)
	m3 := seedPolyMat(fb, 2*d)
	seed := [3]PolyMat{m1, m2, m3}
	gConj := make([][3]PolyMat, len(G.elems))
	for gi, g := range G.elems {
		gm := G.rho[g]
		for f := 0; f < 3; f++ {
			gConj[gi][f] = conjPoly(gm, seed[f])
		}
	}
	reach := map[int]bool{}
	for ai := range basisRR {
		for bi := range basisRR {
			for ci := range basisRR {
				orb := newPoly()
				for gi := range G.elems {
					la := frobPoly(basisRR[ai], gConj[gi][0])
					if la.isZero() {
						continue
					}
					lb := frobPoly(basisRR[bi], gConj[gi][1])
					if lb.isZero() {
						continue
					}
					lc := frobPoly(basisRR[ci], gConj[gi][2])
					if lc.isZero() {
						continue
					}
					orb = addPoly(orb, mulPoly(mulPoly(la, lb), lc))
				}
				if !orb.isZero() {
					reach[81*ai+9*bi+ci] = true
				}
			}
		}
	}
	return reach
}
