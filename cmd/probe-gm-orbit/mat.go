package main

// 3x3 matrices over K = Q(sqrt 3). These hold representation matrices rho(g),
// the order-3 element sigma = rho((123)), and the seed matrices m_i. Fixed 3x3
// size (n = 3, the <3,3,3> target).

const n = 3

// Mat is a 3x3 matrix over Q3, row-major M[i][j].
type Mat [n][n]Q3

func zeroMat() Mat {
	var m Mat
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			m[i][j] = q3Zero
		}
	}
	return m
}

func identMat() Mat {
	m := zeroMat()
	for i := 0; i < n; i++ {
		m[i][i] = q3One
	}
	return m
}

// matFromInts builds a Mat from a 3x3 integer table (rational parts only).
func matFromInts(rows [n][n]int64) Mat {
	var m Mat
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			m[i][j] = q3i(rows[i][j], 0)
		}
	}
	return m
}

// matMulQ3 returns A*B.
func matMulQ3(A, B Mat) Mat {
	var C Mat
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			s := q3Zero
			for k := 0; k < n; k++ {
				s = s.Add(A[i][k].Mul(B[k][j]))
			}
			C[i][j] = s
		}
	}
	return C
}

// transpose returns A^T.
func transpose(A Mat) Mat {
	var C Mat
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			C[i][j] = A[j][i]
		}
	}
	return C
}

// dagger returns the conjugate transpose. Over Q(sqrt3) all entries are real
// (sqrt3 is a real algebraic number, not complex), so dagger == transpose. The
// GM rho is real orthogonal, so rho(g)^dagger = rho(g)^T = rho(g)^{-1}.
func dagger(A Mat) Mat { return transpose(A) }

// addMat returns A+B.
func addMat(A, B Mat) Mat {
	var C Mat
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			C[i][j] = A[i][j].Add(B[i][j])
		}
	}
	return C
}

// scaleMat returns c*A.
func scaleMat(c Q3, A Mat) Mat {
	var C Mat
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			C[i][j] = c.Mul(A[i][j])
		}
	}
	return C
}

// trace returns tr(A).
func trace(A Mat) Q3 {
	s := q3Zero
	for i := 0; i < n; i++ {
		s = s.Add(A[i][i])
	}
	return s
}

// trProd returns tr(A*B*C). This is the matrix-multiplication tensor inner
// product <T, A⊗B⊗C> = tr(ABC) (GM eq. inner-product, 1612.01527).
func trProd(A, B, C Mat) Q3 {
	return trace(matMulQ3(matMulQ3(A, B), C))
}

// frob returns the Frobenius pairing <X, A> = tr(X^T A) = sum_pq X_pq A_pq.
// This is the correct dual pairing in which the MM tensor is
// T_MM = sum_{ijk} E_ij ⊗ E_jk ⊗ E_ki: pairing T_MM against A⊗B⊗C gives
// tr(ABC). (Using tr(XA) instead silently transposes one leg and breaks the
// GM anchor — verified against Sage; see Or2/anchor provenance note.)
func frob(X, A Mat) Q3 {
	s := q3Zero
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			s = s.Add(X[i][j].Mul(A[i][j]))
		}
	}
	return s
}

// conj returns g * X * g^{-1} = g X g^T (g orthogonal). This is the diagonal
// conjugation action of rho(g) on X in rho⊗rho*.
func conj(g, X Mat) Mat {
	return matMulQ3(matMulQ3(g, X), dagger(g))
}

// equalMat reports A == B entrywise.
func equalMat(A, B Mat) bool {
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			if !A[i][j].Equal(B[i][j]) {
				return false
			}
		}
	}
	return true
}
