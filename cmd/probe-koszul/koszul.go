package main

// Core construction of the (restricted) Koszul flattening for the matrix
// multiplication tensor M_n = sum_{i,j,k} e_{ij} (x) e_{jk} (x) e_{ki}.
//
// Indexing convention. A = B = C = C^{n^2}. A matrix unit e_{ab} (row a,
// col b, both in 0..n-1) is flattened to the index a*n + b in 0..n^2-1.
// The n^3 rank-one terms of M_n are (i,j,k) for i,j,k in 0..n-1, with
//   a_t = e_{ij}  (A index i*n+j)
//   b_t = e_{jk}  (B index j*n+k)
//   c_t = e_{ki}  (C index k*n+i).
//
// Restriction. A subspace A' <= A of dimension d' is given by a d' x n^2
// matrix R whose rows span A' (in coordinates of A). The A-leg of M_n is
// projected onto A' by replacing each a_t in A by its image under a
// surjection A -> A'. We realize the surjection coordinate-wise: a_t in A
// has coordinate vector u_t in C^{n^2} (the standard basis vector for index
// i*n+j); its image in A' (in the chosen basis of A', i.e. the rows of R) is
// any solution x of R^T x = u_t ... but that is the wrong direction.
//
// The clean, basis-free way (and the one LO use): pick a projection
// P: A -> A' described in A'-coordinates by a d' x n^2 matrix R, so that the
// image of basis vector u of A is the column R[:,u] of R. Then a_t maps to
// the column R[:, i*n+j] of R, an element of A' written in A'-coordinates.
// Different choices of P that share the same row space A' give the same rank
// up to the cofactor structure; LO's bound is achieved for generic R of the
// given dimension, so we sample/construct R directly as a d' x n^2 matrix and
// treat its rows as A'-coordinates of the projection.

import "math/bits"

// term is a single rank-one summand (i,j,k) of M_n.
type term struct {
	aRow, aCol int // a_t = e_{aRow,aCol}, A index aRow*n+aCol
	bIdx       int // B index of b_t = e_{jk}
	cIdx       int // C index of c_t = e_{ki}
}

// mnTerms enumerates the n^3 rank-one terms of M_n.
func mnTerms(n int) []term {
	ts := make([]term, 0, n*n*n)
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			for k := 0; k < n; k++ {
				ts = append(ts, term{
					aRow: i, aCol: j,
					bIdx: j*n + k,
					cIdx: k*n + i,
				})
			}
		}
	}
	return ts
}

// combinations enumerates all p-subsets of {0,...,d-1} as sorted int slices,
// in lexicographic order. The position in this list is the Lambda^p basis
// index. Returns the list and a lookup map from packed bitmask to position.
func combinations(d, p int) ([][]int, map[uint64]int) {
	if p < 0 || p > d {
		return nil, map[uint64]int{}
	}
	var out [][]int
	idx := map[uint64]int{}
	cur := make([]int, p)
	var rec func(start, depth int)
	rec = func(start, depth int) {
		if depth == p {
			cp := make([]int, p)
			copy(cp, cur)
			var mask uint64
			for _, v := range cp {
				mask |= uint64(1) << uint(v)
			}
			idx[mask] = len(out)
			out = append(out, cp)
			return
		}
		for v := start; v <= d-p+depth; v++ {
			cur[depth] = v
			rec(v+1, depth+1)
		}
	}
	rec(0, 0)
	return out, idx
}

// koszulMatrix builds the restricted Koszul flattening (M_n)_{A'}^{wedge p}
// as a dense matrix over the rationals (entries int64; all values here are
// small integers because R entries are integers in the structured/exact mode
// and the matrix is a signed sum of R-entries). For the mod-p / float random
// search we build with a generic field via the genericBuild path below.
//
// R is the d' x n^2 projection matrix (A'-coordinates). p is the Koszul
// degree. The matrix has:
//
//	rows    = C(d', p+1) * n^2      (Lambda^{p+1} A' (x) C)
//	columns = n^2 * C(d', p)        (B* (x) Lambda^p A')
//
// We return the matrix as [][]int64 (exact integer entries) suitable for both
// exact Q rank (math/big) and reduction mod p.
func koszulMatrixInt(n, dPrime, p int, R [][]int64) [][]int64 {
	terms := mnTerms(n)
	combP, _ := combinations(dPrime, p)
	combP1, idxP1 := combinations(dPrime, p+1)
	n2 := n * n

	nCols := n2 * len(combP)
	nRows := len(combP1) * n2
	M := make([][]int64, nRows)
	for r := range M {
		M[r] = make([]int64, nCols)
	}

	// For each term t, a_t in A has coordinate index aIdx = aRow*n+aCol. Its
	// image in A' has coordinates R[:, aIdx], i.e. column aIdx of R.
	for _, t := range terms {
		aIdx := t.aRow*n + t.aCol
		// column of R giving a_t's A'-coordinates
		// For each A'-basis direction e with nonzero coefficient coeff:
		for e := 0; e < dPrime; e++ {
			coeff := R[e][aIdx]
			if coeff == 0 {
				continue
			}
			eb := uint64(1) << uint(e)
			// For each Lambda^p basis element omega (column block):
			for colW, omega := range combP {
				var omegaMask uint64
				for _, v := range omega {
					omegaMask |= uint64(1) << uint(v)
				}
				if omegaMask&eb != 0 {
					continue // e ^ omega = 0
				}
				below := omegaMask & (eb - 1)
				sign := int64(1)
				if bits.OnesCount64(below)&1 == 1 {
					sign = -1
				}
				resMask := omegaMask | eb
				rowW := idxP1[resMask]
				// column index: B-leg b_t index then Lambda^p block
				col := t.bIdx*len(combP) + colW
				// row index: Lambda^{p+1} block then C-leg c_t index
				row := rowW*n2 + t.cIdx
				M[row][col] += sign * coeff
			}
		}
	}
	return M
}

// koszulMatrixModP builds the restricted Koszul flattening directly over F_p
// (modP) from a d' x n^2 projection matrix R with entries already reduced mod
// p. This avoids int64 overflow for random R whose entries are ~2^61. The
// matrix layout matches koszulMatrixInt. Returns the matrix as [][]uint64
// ready for rankModPU.
func koszulMatrixModP(n, dPrime, p int, R [][]uint64) [][]uint64 {
	terms := mnTerms(n)
	combP, _ := combinations(dPrime, p)
	combP1, idxP1 := combinations(dPrime, p+1)
	n2 := n * n

	nCols := n2 * len(combP)
	nRows := len(combP1) * n2
	M := make([][]uint64, nRows)
	for r := range M {
		M[r] = make([]uint64, nCols)
	}
	_ = combP1

	// Precompute omega masks for the Lambda^p blocks.
	omegaMasks := make([]uint64, len(combP))
	for c, omega := range combP {
		var mask uint64
		for _, v := range omega {
			mask |= uint64(1) << uint(v)
		}
		omegaMasks[c] = mask
	}

	for _, t := range terms {
		aIdx := t.aRow*n + t.aCol
		for e := 0; e < dPrime; e++ {
			coeff := R[e][aIdx]
			if coeff == 0 {
				continue
			}
			eb := uint64(1) << uint(e)
			for colW, omegaMask := range omegaMasks {
				if omegaMask&eb != 0 {
					continue
				}
				below := omegaMask & (eb - 1)
				resMask := omegaMask | eb
				rowW := idxP1[resMask]
				col := t.bIdx*len(combP) + colW
				row := rowW*n2 + t.cIdx
				if bits.OnesCount64(below)&1 == 1 {
					M[row][col] = subModP(M[row][col], coeff)
				} else {
					M[row][col] = addModP(M[row][col], coeff)
				}
			}
		}
	}
	return M
}

// koszulMatrixModP2 is the two-sided variant: in addition to the A-leg
// restriction R (d'_A x n^2), it restricts the B-leg by RB (d'_B x n^2). The
// B* factor of the domain is then C^{d'_B} with basis given by the rows of RB
// (B'-coordinates of the projection B -> B'). The per-rank-one cost is
// unchanged, C(d'_A - 1, p). Domain dim = d'_B * C(d'_A, p). If RB is nil the
// full B is used (equivalent to koszulMatrixModP).
func koszulMatrixModP2(n, dA, p int, R [][]uint64, dB int, RB [][]uint64) [][]uint64 {
	terms := mnTerms(n)
	combP, _ := combinations(dA, p)
	combP1, idxP1 := combinations(dA, p+1)
	n2 := n * n

	bDim := n2
	if RB != nil {
		bDim = dB
	}
	nCols := bDim * len(combP)
	nRows := len(combP1) * n2
	M := make([][]uint64, nRows)
	for r := range M {
		M[r] = make([]uint64, nCols)
	}

	omegaMasks := make([]uint64, len(combP))
	for c, omega := range combP {
		var mask uint64
		for _, v := range omega {
			mask |= uint64(1) << uint(v)
		}
		omegaMasks[c] = mask
	}

	for _, t := range terms {
		aIdx := t.aRow*n + t.aCol
		for e := 0; e < dA; e++ {
			coeffA := R[e][aIdx]
			if coeffA == 0 {
				continue
			}
			eb := uint64(1) << uint(e)
			for colW, omegaMask := range omegaMasks {
				if omegaMask&eb != 0 {
					continue
				}
				below := omegaMask & (eb - 1)
				resMask := omegaMask | eb
				rowW := idxP1[resMask]
				row := rowW*n2 + t.cIdx
				neg := bits.OnesCount64(below)&1 == 1
				if RB == nil {
					col := t.bIdx*len(combP) + colW
					v := coeffA
					if neg {
						M[row][col] = subModP(M[row][col], v)
					} else {
						M[row][col] = addModP(M[row][col], v)
					}
				} else {
					// distribute over B'-basis directions
					for be := 0; be < dB; be++ {
						coeffB := RB[be][t.bIdx]
						if coeffB == 0 {
							continue
						}
						v := mulModP(coeffA, coeffB)
						col := be*len(combP) + colW
						if neg {
							M[row][col] = subModP(M[row][col], v)
						} else {
							M[row][col] = addModP(M[row][col], v)
						}
					}
				}
			}
		}
	}
	return M
}
