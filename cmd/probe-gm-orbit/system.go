package main

// Stage 1: construct the polynomial constraint system for an orbit pair.
//
// Ansatz (multi-orbit, Or1 sec 3):
//
//	T = id^⊗3 + sum_{orbits k} sum_{g in S_4}
//	        rho(g)^⊗3 (m1_k ⊗ m2_k ⊗ m3_k) rho(g)^†⊗3
//
// with m2_k = sigma m1_k sigma^{-1}, m3_k = sigma^2 m1_k sigma^{-2}, and m1_k a
// free element of the H_k-fixed subspace (its coordinates are the variables).
//
// T is a valid decomposition iff <T, A⊗B⊗C> = tr(ABC) for every triple (A,B,C)
// of rho⊗rho* basis matrices. Expanding <T_ansatz, A⊗B⊗C>:
//
//	tr(A)tr(B)tr(C)
//	  + sum_k sum_g tr(A·conj(g,m1_k)) tr(B·conj(g,m2_k)) tr(C·conj(g,m3_k))
//
// so each constraint polynomial is
//
//	P_{A,B,C} = tr(A)tr(B)tr(C)
//	            + sum_k sum_g [ <A,m1_k,g> <B,m2_k,g> <C,m3_k,g> ]  -  tr(ABC)
//
// cubic in the seed variables. We emit the nonzero P_{A,B,C}.

// pairSystem is the constructed polynomial system for an orbit pair.
type pairSystem struct {
	nvars      int
	polys      []*Poly // nonzero constraint polynomials
	maxDegree  int
	numTriples int // total (A,B,C) triples examined (729)
	nonTrivial int // number that gave a nonzero polynomial
}

// orbitCatalog is the table of stabilizer subgroups keyed by orbit size, used to
// enumerate feasible pairs. For orbit size 6 and 12 there are multiple conjugacy
// classes; we include each so the system is built for every distinct geometry.
type orbitTemplate struct {
	name  string
	gens  []perm
	orbit int
}

func orbitCatalog() []orbitTemplate {
	return []orbitTemplate{
		{"S_3", genS3, 4},
		{"K_4", genK4, 6},
		{"Z_4", genZ4, 6},
		{"Z_3", genZ3, 8},
		{"Z_2t", genZ2t, 12},
		{"Z_2d", genZ2d, 12},
	}
}

// buildPairSystem constructs the constraint system for the ordered orbit pair
// (t1, t2) against the matrix-multiplication target <3,3,3>. The seed of orbit 1
// owns variables [0, dim1); orbit 2 owns [dim1, dim1+dim2).
//
// This is the production entry point used by the Or2 probe; it fixes the target
// inner product <T, A⊗B⊗C> = tr(ABC) (trProd). The verdict-producing path
// (symbolic orbit-sum + sigma-twist + cubic constraint construction) is
// factored into buildPairSystemTarget so a positive control (Os1) can drive the
// SAME path against a by-construction-feasible target without duplicating it.
func buildPairSystem(G *Group, basisRR []Mat, t1, t2 orbitTemplate) *pairSystem {
	return buildPairSystemTarget(G, basisRR, t1, t2, func(A, B, C Mat) Q3 {
		return trProd(A, B, C)
	})
}

// buildPairSystemTarget constructs the two-orbit constraint system for an
// arbitrary S_4-invariant target tensor T, supplied as its inner-product
// functional targetInner(A,B,C) = <T, A⊗B⊗C>. The ansatz is
//
//	T_ansatz = id^⊗3 + sum_{k in {0,1}} sum_{g in S_4}
//	    rho(g)^⊗3 (m1_k ⊗ sigma m1_k sigma^-1 ⊗ sigma^2 m1_k sigma^-2) rho(g)^†⊗3
//
// and the constraint per basis triple is <T_ansatz, A⊗B⊗C> = <T, A⊗B⊗C>, i.e.
//
//	P_{A,B,C} = tr(A)tr(B)tr(C) + [symbolic orbit sum] - targetInner(A,B,C).
//
// For targetInner = trProd this is exactly the MM system buildPairSystem emits;
// for targetInner = ansatzInner(seeds*) it is a system feasible by construction
// (P vanishes at the seed parameters of seeds*). Either way the symbolic
// orbit-sum, the sigma-twist coupling, the H-fixed seed spaces, and the cubic
// construction are byte-for-byte the SAME code that produces Or2's 18 verdicts.
func buildPairSystemTarget(G *Group, basisRR []Mat, t1, t2 orbitTemplate, targetInner func(A, B, C Mat) Q3) *pairSystem {
	fb1 := fixedBasis(G, G.subgroup(t1.gens))
	fb2 := fixedBasis(G, G.subgroup(t2.gens))
	nvars := len(fb1) + len(fb2)

	// Symbolic seeds m1 for each orbit, and their sigma-twisted partners. Orbit 1
	// owns variables [0, len(fb1)); orbit 2 owns [len(fb1), nvars).
	seeds := [][3]PolyMat{
		orbitSeedTriple(G.sigma, fb1, 0),
		orbitSeedTriple(G.sigma, fb2, len(fb1)),
	}

	// Precompute conj(g, m_i) for every group element and every orbit factor.
	// gConj[k][gi][f] = conj(rho(g), seed_k factor f). f in {0,1,2}.
	gConj := make([][][3]PolyMat, 2)
	for k := 0; k < 2; k++ {
		gConj[k] = make([][3]PolyMat, len(G.elems))
		for gi, g := range G.elems {
			gm := G.rho[g]
			for f := 0; f < 3; f++ {
				gConj[k][gi][f] = conjPoly(gm, seeds[k][f])
			}
		}
	}

	sys := &pairSystem{nvars: nvars}

	// Enumerate all 9^3 triples (A,B,C).
	for ai := range basisRR {
		A := basisRR[ai]
		for bi := range basisRR {
			B := basisRR[bi]
			for ci := range basisRR {
				C := basisRR[ci]
				sys.numTriples++

				// constant part: tr(A)tr(B)tr(C) - <T, A⊗B⊗C>
				constVal := trace(A).Mul(trace(B)).Mul(trace(C)).Sub(targetInner(A, B, C))
				P := constPoly(constVal)

				// orbit sum: sum_k sum_g <A,m1>_g <B,m2>_g <C,m3>_g
				for k := 0; k < 2; k++ {
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

// orbitSeedTriple builds (m1, m2, m3) = (m1, sigma m1 sigma^-1, sigma^2 m1
// sigma^-2) for the symbolic seed m1 = sum x_p basis[p].
func orbitSeedTriple(sigma Mat, basis []Mat, varBase int) [3]PolyMat {
	m1 := seedPolyMat(basis, varBase)
	return [3]PolyMat{
		twistSeed(sigma, m1, 0),
		twistSeed(sigma, m1, 1),
		twistSeed(sigma, m1, 2),
	}
}

// polyDegree returns the total degree of p.
func polyDegree(p *Poly) int {
	d := 0
	for _, t := range p.terms {
		if len(t.mono) > d {
			d = len(t.mono)
		}
	}
	return d
}
