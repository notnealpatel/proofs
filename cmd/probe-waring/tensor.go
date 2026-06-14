package main

import "math"

// N is the number of variables: the 9 entries of a 3x3 matrix A, indexed
// v = 3*i + j for entry A_{ij}, i,j in {0,1,2}.
const N = 9

// triple is an unordered index triple (a<=b<=c) over the N variables; it
// indexes a basis element of the fully symmetric cubic coefficient space.
type triple struct{ a, b, c int }

// triples enumerates all C(N+2,3) = 165 unordered triples a<=b<=c.
func triples() []triple {
	var ts []triple
	for a := 0; a < N; a++ {
		for b := a; b < N; b++ {
			for c := b; c < N; c++ {
				ts = append(ts, triple{a, b, c})
			}
		}
	}
	return ts
}

// numTriples is the dimension of the symmetric cubic coefficient space.
var numTriples = len(triples()) // 165

// targetTensor builds the fully symmetric coefficient tensor F of the cubic
// form f(A) = tr(A^3) = sum_{i,j,k} A_ij A_jk A_ki, expressed in the triple
// basis. F[t] is the coefficient such that for any linear form v,
//
//	sum over orderings of (v_a v_b v_c) collapses so that
//	f as symmetric tensor has entry F[t] at the symmetric position t.
//
// Convention: we store F[t] = the fully-symmetric tensor value T_{abc} (the
// value of the symmetric tensor at one ordering of the index triple, i.e.
// the average over the 3! orderings of the raw monomial-coefficient tensor).
// For a rank-one cube v^3, the symmetric tensor value at (a,b,c) is v_a v_b v_c.
// So the Waring equation reads, for every triple t=(a,b,c):
//
//	sum_k L[k]_a L[k]_b L[k]_c = F[t].
func targetTensor() map[triple]complex128 {
	// Raw symmetric 3-tensor S[a][b][c] (fully symmetric in a,b,c) such that
	// f(A) = sum_{a,b,c} S[a][b][c] x_a x_b x_c with the standard symmetric
	// tensor / polarization convention: f(A) = sum_{a<=b<=c} mult * S * monomial,
	// but more simply S[a][b][c] = (1/6) * sum over the 6 orderings of the raw
	// coefficient placement. We build S so that S[a][b][c] = v_a v_b v_c gives
	// the value of v^3's symmetric tensor.
	//
	// f(A) = sum_{i,j,k} A_ij A_jk A_ki. Each monomial term corresponds to an
	// ordered triple of variables (u,v,w) = (3i+j, 3j+k, 3k+i). We accumulate
	// 1 into the symmetric tensor for each such ordered occurrence, then divide
	// by the symmetry-orbit handling implicitly via full symmetrization.
	var S [N][N][N]complex128
	for i := 0; i < 3; i++ {
		for j := 0; j < 3; j++ {
			for k := 0; k < 3; k++ {
				u := 3*i + j
				v := 3*j + k
				w := 3*k + i
				// distribute 1 over all 6 orderings of (u,v,w) to symmetrize
				addSym(&S, u, v, w, 1.0/6.0)
			}
		}
	}
	F := make(map[triple]complex128, numTriples)
	for _, t := range triples() {
		F[t] = S[t.a][t.b][t.c]
	}
	return F
}

// addSym adds val to all 6 ordered positions of the symmetric tensor S at the
// (multiset) index {u,v,w}. This realizes full symmetrization of the raw
// coefficient placement: a monomial x_u x_v x_w contributes equally to each
// ordering of the symmetric tensor.
func addSym(S *[N][N][N]complex128, u, v, w int, val complex128) {
	perms := [6][3]int{
		{u, v, w}, {u, w, v}, {v, u, w},
		{v, w, u}, {w, u, v}, {w, v, u},
	}
	for _, p := range perms {
		S[p[0]][p[1]][p[2]] += val
	}
}

// frobLin returns the linear form coefficient vector for matrix m under the
// Frobenius pairing L_m(A) = sum_ij m_ij A_ij, indexed v=3i+j.
func frobLin(m [3][3]complex128) [N]complex128 {
	var c [N]complex128
	for i := 0; i < 3; i++ {
		for j := 0; j < 3; j++ {
			c[3*i+j] = m[i][j]
		}
	}
	return c
}

// cubeResidual computes, for a set of r linear forms L (each length N), the
// residual r[t] = sum_k L[k]_a L[k]_b L[k]_c - F[t] over all triples.
func cubeResidual(L [][N]complex128, F map[triple]complex128, ts []triple) []complex128 {
	res := make([]complex128, len(ts))
	for idx, t := range ts {
		var s complex128
		for _, c := range L {
			s += c[t.a] * c[t.b] * c[t.c]
		}
		res[idx] = s - F[t]
	}
	return res
}

// residualNorm returns the L2 norm of a complex residual vector.
func residualNorm(res []complex128) float64 {
	var s float64
	for _, z := range res {
		s += real(z)*real(z) + imag(z)*imag(z)
	}
	return math.Sqrt(s)
}
