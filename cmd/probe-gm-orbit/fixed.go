package main

// H-fixed subspaces of M_3(K) under the conjugation action X -> rho(h) X rho(h)^T.
// The seed matrix m_1 of an orbit with stabilizer H must lie in this subspace
// (Or1 sec 3 "Seed parametrization"). We return an orthonormal-free K-basis of
// the fixed space as a list of Mat; the seed's free parameters are the
// coefficients in this basis.

// vecIndex maps matrix entry (i,j) to a flat index 0..8 (row-major).
func vecIndex(i, j int) int { return i*n + j }

// vecToMat inflates a length-9 []Q3 back to a Mat.
func vecToMat(v []Q3) Mat {
	var m Mat
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			m[i][j] = v[vecIndex(i, j)]
		}
	}
	return m
}

// conjOperator returns the 9x9 matrix C over K such that C * vec(X) = vec(g X g^T),
// where vec is row-major. Built column by column by conjugating each basis
// matrix E_{ij}.
func conjOperator(G *Group, g perm) [][]Q3 {
	gm := G.rho[g]
	C := make([][]Q3, n*n)
	for r := range C {
		C[r] = make([]Q3, n*n)
	}
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			var E Mat = zeroMat()
			E[i][j] = q3One
			img := conj(gm, E) // g E g^T
			col := vecIndex(i, j)
			for a := 0; a < n; a++ {
				for b := 0; b < n; b++ {
					C[vecIndex(a, b)][col] = img[a][b]
				}
			}
		}
	}
	return C
}

// fixedBasis returns a K-basis (list of Mat) for the subspace of M_3(K) fixed
// by conjugation under every element of subgroup H. Computed as the null space
// of the stacked operators (C_h - I) over all h in H.
func fixedBasis(G *Group, H []perm) []Mat {
	var rows [][]Q3
	I9 := func() [][]Q3 {
		m := make([][]Q3, n*n)
		for r := range m {
			m[r] = make([]Q3, n*n)
			for c := range m[r] {
				if r == c {
					m[r][c] = q3One
				} else {
					m[r][c] = q3Zero
				}
			}
		}
		return m
	}()
	for _, h := range H {
		C := conjOperator(G, h)
		for r := 0; r < n*n; r++ {
			row := make([]Q3, n*n)
			for c := 0; c < n*n; c++ {
				row[c] = C[r][c].Sub(I9[r][c])
			}
			rows = append(rows, row)
		}
	}
	null := nullSpaceQ3(rows, n*n)
	out := make([]Mat, len(null))
	for i, v := range null {
		out[i] = vecToMat(v)
	}
	return out
}
