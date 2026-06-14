package main

import "math/rand"

// binom returns C(n,k) as int64 (values here stay well within range for the
// small parameters used: n <= 9, k <= 9 give at most C(9,4)=126... actually
// for two-sided we may go to C(2n^2,p) but those parameters are bounded).
func binom(n, k int) int64 {
	if k < 0 || k > n {
		return 0
	}
	if k > n-k {
		k = n - k
	}
	r := int64(1)
	for i := 0; i < k; i++ {
		r = r * int64(n-i) / int64(i+1)
	}
	return r
}

// ---- Random projection matrices (mod p) ----

// randProjModP returns a random d' x n^2 matrix over F_p (modP). Generic such
// matrices realize the LO bound; this is the workhorse for the random search.
func randProjModP(rng *rand.Rand, dPrime, n2 int) [][]uint64 {
	R := make([][]uint64, dPrime)
	for r := 0; r < dPrime; r++ {
		R[r] = make([]uint64, n2)
		for c := 0; c < n2; c++ {
			R[r][c] = uint64(rng.Int63n(int64(modP)))
		}
	}
	return R
}

// ---- Structured subspace families (over Q / integers) ----
//
// Each builder returns a d' x n^2 integer matrix R whose rows span a subspace
// A' of A = Mat_n (flattened, index a*n+b). A "slice" here is an n x n matrix
// flattened row-major to length n^2. We restrict A' to lie inside the chosen
// structured family of matrices. d' is the dimension of the family (or a
// requested sub-dimension when the family is larger).

// flatten turns an n x n integer matrix into a length-n^2 row (index a*n+b).
func flatten(m [][]int64, n int) []int64 {
	out := make([]int64, n*n)
	for a := 0; a < n; a++ {
		for b := 0; b < n; b++ {
			out[a*n+b] = m[a][b]
		}
	}
	return out
}

// matPow returns X^e as an n x n integer matrix (X^0 = I).
func matPow(X [][]int64, n, e int) [][]int64 {
	res := identity(n)
	for i := 0; i < e; i++ {
		res = matMul(res, X, n)
	}
	return res
}

func identity(n int) [][]int64 {
	I := make([][]int64, n)
	for a := 0; a < n; a++ {
		I[a] = make([]int64, n)
		I[a][a] = 1
	}
	return I
}

func matMul(A, B [][]int64, n int) [][]int64 {
	C := make([][]int64, n)
	for a := 0; a < n; a++ {
		C[a] = make([]int64, n)
		for c := 0; c < n; c++ {
			var s int64
			for k := 0; k < n; k++ {
				s += A[a][k] * B[k][c]
			}
			C[a][c] = s
		}
	}
	return C
}

// familyPowers: span of {I, X, X^2, ..., X^{d'-1}} for a companion / random X.
// This is the shape of LO's own S^{m+n-2}W trick (polynomials in a matrix).
// Returns the d' x n^2 matrix and false if the powers are linearly dependent
// (rank of the span < d').
func familyPowers(X [][]int64, n, dPrime int) ([][]int64, bool) {
	R := make([][]int64, dPrime)
	for e := 0; e < dPrime; e++ {
		R[e] = flatten(matPow(X, n, e), n)
	}
	// independence check over Q
	if rankExactQ(R) < dPrime {
		return R, false
	}
	return R, true
}

// companion builds the companion matrix of a monic polynomial with the given
// (random small) lower-degree coefficients c[0..n-1] so that X is a single
// n x n cyclic-shift-like nonderogatory matrix (its powers I..X^{n-1} are
// independent, spanning the full commutant-cyclic algebra of dimension n).
func companion(n int, rng *rand.Rand) [][]int64 {
	X := make([][]int64, n)
	for a := 0; a < n; a++ {
		X[a] = make([]int64, n)
	}
	for a := 0; a < n-1; a++ {
		X[a+1][a] = 1 // sub-diagonal ones
	}
	// last column = -coefficients (small random)
	for a := 0; a < n; a++ {
		X[a][n-1] = int64(rng.Intn(7) - 3)
	}
	return X
}

// randIntMat returns an n x n integer matrix with small random entries.
func randIntMat(n int, rng *rand.Rand) [][]int64 {
	X := make([][]int64, n)
	for a := 0; a < n; a++ {
		X[a] = make([]int64, n)
		for b := 0; b < n; b++ {
			X[a][b] = int64(rng.Intn(7) - 3)
		}
	}
	return X
}

// familyCirculant: the circulant matrices (dimension n). Basis: shift powers
// S^0..S^{n-1} where S is the cyclic permutation matrix. d' must be <= n; we
// take the first d' shift-power slices.
func familyCirculant(n, dPrime int) [][]int64 {
	S := make([][]int64, n)
	for a := 0; a < n; a++ {
		S[a] = make([]int64, n)
		S[a][(a+1)%n] = 1
	}
	R := make([][]int64, dPrime)
	for e := 0; e < dPrime; e++ {
		R[e] = flatten(matPow(S, n, e), n)
	}
	return R
}

// familyToeplitz: Toeplitz matrices (constant diagonals), dimension 2n-1.
// Diagonal index d ranges over -(n-1)..(n-1); basis matrix T_d has ones on
// that diagonal. We return the first d' of these (ordered by diagonal).
func familyToeplitz(n, dPrime int) [][]int64 {
	var basis [][]int64
	for diag := -(n - 1); diag <= n-1; diag++ {
		m := make([][]int64, n)
		for a := 0; a < n; a++ {
			m[a] = make([]int64, n)
			b := a + diag
			if b >= 0 && b < n {
				m[a][b] = 1
			}
		}
		basis = append(basis, flatten(m, n))
		if len(basis) == dPrime {
			break
		}
	}
	return basis
}

// familySymmetric: symmetric matrices Sym^2, dimension n(n+1)/2. Basis:
// E_{aa} and (E_{ab}+E_{ba}) for a<b. Returns first d' basis slices.
func familySymmetric(n, dPrime int) [][]int64 {
	var basis [][]int64
	for a := 0; a < n; a++ {
		m := make([][]int64, n)
		for r := 0; r < n; r++ {
			m[r] = make([]int64, n)
		}
		m[a][a] = 1
		basis = append(basis, flatten(m, n))
		if len(basis) == dPrime {
			return basis
		}
	}
	for a := 0; a < n; a++ {
		for b := a + 1; b < n; b++ {
			m := make([][]int64, n)
			for r := 0; r < n; r++ {
				m[r] = make([]int64, n)
			}
			m[a][b] = 1
			m[b][a] = 1
			basis = append(basis, flatten(m, n))
			if len(basis) == dPrime {
				return basis
			}
		}
	}
	return basis
}

// familySkew: skew-symmetric matrices, dimension n(n-1)/2. Basis E_{ab}-E_{ba}
// for a<b. Returns first d' slices.
func familySkew(n, dPrime int) [][]int64 {
	var basis [][]int64
	for a := 0; a < n; a++ {
		for b := a + 1; b < n; b++ {
			m := make([][]int64, n)
			for r := 0; r < n; r++ {
				m[r] = make([]int64, n)
			}
			m[a][b] = 1
			m[b][a] = -1
			basis = append(basis, flatten(m, n))
			if len(basis) == dPrime {
				return basis
			}
		}
	}
	return basis
}

// familyTraceless: sl_n (traceless matrices), dimension n^2-1. Basis: all
// off-diagonal E_{ab} (a!=b) plus the n-1 diagonal differences E_{aa}-E_{a+1,a+1}.
// Returns first d' slices.
func familyTraceless(n, dPrime int) [][]int64 {
	var basis [][]int64
	for a := 0; a < n; a++ {
		for b := 0; b < n; b++ {
			if a == b {
				continue
			}
			m := make([][]int64, n)
			for r := 0; r < n; r++ {
				m[r] = make([]int64, n)
			}
			m[a][b] = 1
			basis = append(basis, flatten(m, n))
			if len(basis) == dPrime {
				return basis
			}
		}
	}
	for a := 0; a < n-1; a++ {
		m := make([][]int64, n)
		for r := 0; r < n; r++ {
			m[r] = make([]int64, n)
		}
		m[a][a] = 1
		m[a+1][a+1] = -1
		basis = append(basis, flatten(m, n))
		if len(basis) == dPrime {
			return basis
		}
	}
	return basis
}

// familyCommutant: span closed under commutator with a fixed X. Concretely we
// take the span of {Y, [X,Y], [X,[X,Y]], ...} (the smallest ad_X-invariant
// subspace containing a random seed Y), truncated/extended to dimension d'.
// If the ad_X orbit of a single seed does not reach dimension d', we add
// further random seeds' orbits. Returns the d' x n^2 matrix and a flag whether
// the requested dimension was reached.
func familyCommutant(X [][]int64, n, dPrime int, rng *rand.Rand) ([][]int64, bool) {
	var rows [][]int64
	add := func(slice []int64) bool {
		cand := append(append([][]int64{}, rows...), slice)
		if rankExactQ(cand) > len(rows) {
			rows = cand
			return true
		}
		return false
	}
	commutator := func(Y [][]int64) [][]int64 {
		XY := matMul(X, Y, n)
		YX := matMul(Y, X, n)
		C := make([][]int64, n)
		for a := 0; a < n; a++ {
			C[a] = make([]int64, n)
			for b := 0; b < n; b++ {
				C[a][b] = XY[a][b] - YX[a][b]
			}
		}
		return C
	}
	tries := 0
	for len(rows) < dPrime && tries < 50 {
		tries++
		Y := randIntMat(n, rng)
		// build the ad_X orbit of Y
		queue := [][][]int64{Y}
		for len(queue) > 0 && len(rows) < dPrime {
			cur := queue[0]
			queue = queue[1:]
			if add(flatten(cur, n)) {
				queue = append(queue, commutator(cur))
			}
		}
	}
	if len(rows) < dPrime {
		// pad with rows of zeros would make it rank-deficient; instead report
		// failure but return what we have padded to d' so the caller can skip.
		for len(rows) < dPrime {
			rows = append(rows, make([]int64, n*n))
		}
		return rows, false
	}
	return rows, true
}
