package main

// Exact linear algebra over K = Q(sqrt 3): row reduction and null-space, used
// to compute H-fixed subspaces of M_3(K) under the conjugation action. Vectors
// are []Q3; matrices are [][]Q3 (row-major).

// rrefQ3 reduces M in place to reduced row-echelon form and returns the list of
// pivot column indices. M is modified.
func rrefQ3(M [][]Q3) []int {
	if len(M) == 0 {
		return nil
	}
	cols := len(M[0])
	var pivots []int
	row := 0
	for col := 0; col < cols && row < len(M); col++ {
		// find a pivot in this column at or below `row`
		sel := -1
		for r := row; r < len(M); r++ {
			if !M[r][col].IsZero() {
				sel = r
				break
			}
		}
		if sel == -1 {
			continue
		}
		M[row], M[sel] = M[sel], M[row]
		// normalize pivot row
		inv := M[row][col].Inv()
		for c := 0; c < cols; c++ {
			M[row][c] = M[row][c].Mul(inv)
		}
		// eliminate the column from all other rows
		for r := 0; r < len(M); r++ {
			if r == row {
				continue
			}
			f := M[r][col]
			if f.IsZero() {
				continue
			}
			for c := 0; c < cols; c++ {
				M[r][c] = M[r][c].Sub(f.Mul(M[row][c]))
			}
		}
		pivots = append(pivots, col)
		row++
	}
	return pivots
}

// matRank returns the exact matrix rank of a 3x3 Mat over K, via RREF of its
// rows. Used by the Os1 control to certify that its planted seed matrices are
// genuinely non-rank-1 (i.e. the arbitrary-matrix-rank seed handling, not GM's
// published rank-1 special case, is exercised).
func matRank(m Mat) int {
	rows := make([][]Q3, n)
	for i := 0; i < n; i++ {
		rows[i] = make([]Q3, n)
		for j := 0; j < n; j++ {
			rows[i][j] = m[i][j]
		}
	}
	return len(rrefQ3(rows))
}

// nullSpaceQ3 returns a basis (list of vectors, each length cols) for the right
// null space {x : M x = 0} of the cols-wide matrix M, computed exactly over K.
func nullSpaceQ3(M [][]Q3, cols int) [][]Q3 {
	// copy so we don't mutate caller data
	work := make([][]Q3, len(M))
	for i := range M {
		work[i] = append([]Q3(nil), M[i]...)
	}
	pivots := rrefQ3(work)
	isPivot := make([]bool, cols)
	for _, p := range pivots {
		isPivot[p] = true
	}
	// pivot column -> its row index in rref
	pivotRow := make(map[int]int, len(pivots))
	for i, p := range pivots {
		pivotRow[p] = i
	}
	var basis [][]Q3
	for free := 0; free < cols; free++ {
		if isPivot[free] {
			continue
		}
		vec := make([]Q3, cols)
		for i := range vec {
			vec[i] = q3Zero
		}
		vec[free] = q3One
		for _, p := range pivots {
			// row p of rref: pivot var = - sum(free coeffs * free vars)
			coef := work[pivotRow[p]][free]
			vec[p] = coef.Neg()
		}
		basis = append(basis, vec)
	}
	return basis
}
