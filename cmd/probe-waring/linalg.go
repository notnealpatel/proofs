package main

import "math"

// solveSym solves A x = b for symmetric (not necessarily positive-definite)
// A using LU decomposition with partial pivoting. Returns false if singular.
func solveSym(A [][]float64, b []float64) ([]float64, bool) {
	n := len(b)
	// copy A into lu
	lu := make([][]float64, n)
	for i := range A {
		lu[i] = append([]float64(nil), A[i]...)
	}
	piv := make([]int, n)
	for i := range piv {
		piv[i] = i
	}
	for k := 0; k < n; k++ {
		// pivot
		p := k
		max := math.Abs(lu[k][k])
		for i := k + 1; i < n; i++ {
			if a := math.Abs(lu[i][k]); a > max {
				max = a
				p = i
			}
		}
		if max < 1e-300 {
			return nil, false
		}
		if p != k {
			lu[k], lu[p] = lu[p], lu[k]
			piv[k], piv[p] = piv[p], piv[k]
		}
		akk := lu[k][k]
		for i := k + 1; i < n; i++ {
			f := lu[i][k] / akk
			lu[i][k] = f
			row := lu[i]
			krow := lu[k]
			for j := k + 1; j < n; j++ {
				row[j] -= f * krow[j]
			}
		}
	}
	// permute b
	y := make([]float64, n)
	for i := 0; i < n; i++ {
		y[i] = b[piv[i]]
	}
	// forward solve L y = Pb (unit lower)
	for i := 0; i < n; i++ {
		for j := 0; j < i; j++ {
			y[i] -= lu[i][j] * y[j]
		}
	}
	// back solve U x = y
	x := make([]float64, n)
	for i := n - 1; i >= 0; i-- {
		s := y[i]
		for j := i + 1; j < n; j++ {
			s -= lu[i][j] * x[j]
		}
		x[i] = s / lu[i][i]
	}
	return x, true
}
