package main

// Oe1 Track-D extension: the GM group-orbit ansatz with an ARBITRARY number of
// H-fixed orbits under S_4 (the two-orbit case is Or2/system.go; this generalizes
// it to >=3 orbits). The construction, sigma-twist, fixed-space seeds, and cubic
// constraint are identical to buildPairSystemTarget -- only the orbit count is
// variable. The two-orbit production path (buildPairSystem) is left byte-for-byte
// unchanged so Os1's TestOs1ProductionPathUnchanged still pins Or2's systems.
//
// Ansatz (Or1 sec 3, generalized to L orbits):
//
//	T = id^⊗3 + sum_{k=0}^{L-1} sum_{g in S_4}
//	        rho(g)^⊗3 (m1_k ⊗ sigma m1_k sigma^-1 ⊗ sigma^2 m1_k sigma^-2) rho(g)^†⊗3
//
// with each m1_k a free element of its orbit's H_k-fixed subspace; orbit k owns a
// contiguous block of variables. T is a valid <3,3,3> decomposition iff
// <T, A⊗B⊗C> = tr(ABC) on every rho⊗rho* basis triple.
//
// Tensor rank = 1 + sum_k (orbit size of orbit k). The interesting regime is
// rank <= 22 (total orbit <= 21), the only way to beat Laderman 23.

// multiConfig is an ordered list of orbit templates (orbits may repeat the same
// stabilizer type -- each is an independent seed with its own variable block).
type multiConfig struct {
	orbits []orbitTemplate
}

// totalOrbit returns sum of orbit sizes (tensor rank = 1 + this).
func (c multiConfig) totalOrbit() int {
	s := 0
	for _, o := range c.orbits {
		s += o.orbit
	}
	return s
}

// label renders the config as e.g. "S_3+S_3+K_4" for file/record naming.
func (c multiConfig) label() string {
	s := ""
	for i, o := range c.orbits {
		if i > 0 {
			s += "+"
		}
		s += o.name
	}
	return s
}

// orbitReachSet returns the set of rho⊗rho* basis-triple indices (flattened
// 81*ai+9*bi+ci) where a SINGLE orbit of stabilizer type t has a nonzero
// symbolic orbit-sum contribution (its "reachable directions"). Stacking more
// orbits of the SAME type does not enlarge this set, so the union over a config's
// distinct types determines which residual triples can be hit at all. This is the
// engine of the Oe1 coverage pre-screen.
func orbitReachSet(G *Group, basisRR []Mat, t orbitTemplate) map[int]bool {
	fb := fixedBasis(G, G.subgroup(t.gens))
	seed := orbitSeedTriple(G.sigma, fb, 0)
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

// residualSupport returns the set of basis-triple indices with nonzero MM
// residual tr(A)tr(B)tr(C) - tr(ABC). These are the directions a valid
// decomposition MUST reach; |support| = 137 (matches Or2's constraint count).
func residualSupport(basisRR []Mat) map[int]bool {
	sup := map[int]bool{}
	for ai := range basisRR {
		for bi := range basisRR {
			for ci := range basisRR {
				A, B, C := basisRR[ai], basisRR[bi], basisRR[ci]
				r := trace(A).Mul(trace(B)).Mul(trace(C)).Sub(trProd(A, B, C))
				if !r.IsZero() {
					sup[81*ai+9*bi+ci] = true
				}
			}
		}
	}
	return sup
}

// buildMultiSystem constructs the cubic constraint system for an L-orbit config
// against the MM target. Orbit k owns variables [base_k, base_k+dim_k). This is
// the L-orbit generalization of buildPairSystem; for L=2 it produces the SAME
// system as buildPairSystem (verified by TestMultiMatchesPairOnTwoOrbits).
func buildMultiSystem(G *Group, basisRR []Mat, cfg multiConfig) *pairSystem {
	return buildMultiSystemTarget(G, basisRR, cfg, func(A, B, C Mat) Q3 {
		return trProd(A, B, C)
	})
}

// buildMultiSystemTarget is buildMultiSystem against an arbitrary S_4-invariant
// target functional targetInner = <T, A⊗B⊗C>. Mirrors buildPairSystemTarget for
// L orbits.
func buildMultiSystemTarget(G *Group, basisRR []Mat, cfg multiConfig, targetInner func(A, B, C Mat) Q3) *pairSystem {
	L := len(cfg.orbits)

	// Fixed-space bases and per-orbit variable-block offsets.
	fbs := make([][]Mat, L)
	bases := make([]int, L)
	nvars := 0
	for k, o := range cfg.orbits {
		fbs[k] = fixedBasis(G, G.subgroup(o.gens))
		bases[k] = nvars
		nvars += len(fbs[k])
	}

	// Symbolic sigma-twisted seed triples, one per orbit, on their own var blocks.
	seeds := make([][3]PolyMat, L)
	for k := 0; k < L; k++ {
		seeds[k] = orbitSeedTriple(G.sigma, fbs[k], bases[k])
	}

	// Precompute conj(g, m_i) for every group element, orbit, and factor.
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

				constVal := trace(A).Mul(trace(B)).Mul(trace(C)).Sub(targetInner(A, B, C))
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
