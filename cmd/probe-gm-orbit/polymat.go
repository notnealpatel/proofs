package main

// 3x3 matrices whose entries are symbolic polynomials in the seed parameters.
// A seed m_1 = sum_p t_p B_p is a PolyMat; conjugation by rho(g) and the order-3
// twist by sigma act K-linearly on it, and tr(A * PolyMat) for a constant Mat A
// yields a linear Poly. The three orbit factors multiply into the cubic
// constraint polynomial.

// PolyMat is a 3x3 matrix of *Poly.
type PolyMat [n][n]*Poly

// zeroPolyMat returns the all-zero PolyMat.
func zeroPolyMat() PolyMat {
	var m PolyMat
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			m[i][j] = newPoly()
		}
	}
	return m
}

// seedPolyMat builds the symbolic seed sum_p x_{base+p} * basis[p] from a
// fixed-subspace basis, allocating variable indices base, base+1, ...
func seedPolyMat(basis []Mat, base int) PolyMat {
	m := zeroPolyMat()
	for p, B := range basis {
		xp := varPoly(base + p)
		for i := 0; i < n; i++ {
			for j := 0; j < n; j++ {
				if !B[i][j].IsZero() {
					m[i][j] = addPoly(m[i][j], scalePoly(B[i][j], xp))
				}
			}
		}
	}
	return m
}

// mulConstPolyMat returns the constant-times-poly product A * M (A constant Mat,
// M PolyMat).
func mulConstPolyMat(A Mat, M PolyMat) PolyMat {
	var C PolyMat
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			acc := newPoly()
			for k := 0; k < n; k++ {
				if !A[i][k].IsZero() {
					acc = addPoly(acc, scalePoly(A[i][k], M[k][j]))
				}
			}
			C[i][j] = acc
		}
	}
	return C
}

// mulPolyMatConst returns M * A (M PolyMat, A constant Mat).
func mulPolyMatConst(M PolyMat, A Mat) PolyMat {
	var C PolyMat
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			acc := newPoly()
			for k := 0; k < n; k++ {
				if !A[k][j].IsZero() {
					acc = addPoly(acc, scalePoly(A[k][j], M[i][k]))
				}
			}
			C[i][j] = acc
		}
	}
	return C
}

// conjPoly returns g * M * g^T for constant g and symbolic M.
func conjPoly(g Mat, M PolyMat) PolyMat {
	return mulPolyMatConst(mulConstPolyMat(g, M), dagger(g))
}

// twistSeed returns sigma^k * M * (sigma^k)^{-1}, the order-3 partner seeds.
// k in {0,1,2}; (sigma^k)^{-1} = (sigma^k)^T since sigma is orthogonal.
func twistSeed(sigma Mat, M PolyMat, k int) PolyMat {
	s := identMat()
	for i := 0; i < k; i++ {
		s = matMulQ3(s, sigma)
	}
	return mulPolyMatConst(mulConstPolyMat(s, M), dagger(s))
}

// frobPoly returns the linear Poly <M, A> = sum_ij A_ij M_ij, the Frobenius
// pairing of the symbolic PolyMat M against the constant Mat A. (This is the
// correct MM dual pairing; see frob in mat.go and the Or2/anchor note.)
func frobPoly(A Mat, M PolyMat) *Poly {
	acc := newPoly()
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			if !A[i][j].IsZero() {
				acc = addPoly(acc, scalePoly(A[i][j], M[i][j]))
			}
		}
	}
	return acc
}
