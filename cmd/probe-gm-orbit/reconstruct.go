package main

// Stage 0 / Stage 3: concrete (non-symbolic) reconstruction and exact
// verification of an orbit decomposition.
//
// Given concrete seed matrices m1_k (one per orbit, as Mat over K), form
//
//	T_ansatz = id^⊗3 + sum_k sum_{g in S_4}
//	    rho(g)^⊗3 (m1_k ⊗ sigma m1_k sigma^-1 ⊗ sigma^2 m1_k sigma^-2) rho(g)^†⊗3
//
// and verify <T_ansatz, A⊗B⊗C> = tr(ABC) for all A,B,C in a basis of M_3(K).
// Equality on a full basis of triples certifies T_ansatz = MM exactly.

// ansatzInner returns <T_ansatz, A⊗B⊗C> for concrete seeds, evaluated exactly
// over K. seeds[k] = m1_k; the twists are applied internally.
func ansatzInner(G *Group, seeds []Mat, A, B, C Mat) Q3 {
	// id^⊗3 contribution: tr(A) tr(B) tr(C)
	val := trace(A).Mul(trace(B)).Mul(trace(C))

	for _, m1 := range seeds {
		m2 := conj(G.sigma, m1)                    // sigma m1 sigma^-1
		m3 := conj(matMulQ3(G.sigma, G.sigma), m1) // sigma^2 m1 sigma^-2
		for _, g := range G.elems {
			gm := G.rho[g]
			f1 := frob(conj(gm, m1), A)
			if f1.IsZero() {
				continue
			}
			f2 := frob(conj(gm, m2), B)
			if f2.IsZero() {
				continue
			}
			f3 := frob(conj(gm, m3), C)
			if f3.IsZero() {
				continue
			}
			val = val.Add(f1.Mul(f2).Mul(f3))
		}
	}
	return val
}

// basisM3 returns the 9 elementary matrices E_{ij} as a basis of M_3(K).
func basisM3() []Mat {
	var out []Mat
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			E := zeroMat()
			E[i][j] = q3One
			out = append(out, E)
		}
	}
	return out
}

// verifyDecomposition checks <T_ansatz, A⊗B⊗C> == tr(ABC) for all triples
// (A,B,C) over the M_3 basis (729 checks). Returns true iff the ansatz equals
// the matrix-multiplication tensor exactly, and on failure the first offending
// triple indices and the (got, want) values.
func verifyDecomposition(G *Group, seeds []Mat) (ok bool, badA, badB, badC int, got, want Q3) {
	basis := basisM3()
	for ai := range basis {
		for bi := range basis {
			for ci := range basis {
				g := ansatzInner(G, seeds, basis[ai], basis[bi], basis[ci])
				w := trProd(basis[ai], basis[bi], basis[ci])
				if !g.Equal(w) {
					return false, ai, bi, ci, g, w
				}
			}
		}
	}
	return true, 0, 0, 0, q3Zero, q3Zero
}
