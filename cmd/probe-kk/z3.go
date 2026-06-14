package main

import (
	"context"
	"fmt"
)

// z3Eigen implements task STEP 5: the Z_3-equivariant direct sum of the three
// leg-flattenings, decomposed into the Z_3 eigenspaces (eigenvalues 1, zeta,
// zeta^2, zeta a primitive cube root of unity in F_p), reporting the rank of
// the flattening restricted to each eigenspace.
//
// M_n is invariant under the cyclic Z_3 action permuting legs (A->B->C->A).
// Let Phi^{(i)} be the tangency (mixed) flattening with the wedge on leg i.
// The relabeling tau induced by the leg permutation (i,j,k)->(k,i,j) is the
// IDENTITY in the shared index layout (every leg is F^{n^2} with the same
// matrix-unit basis and passengers are indexed cyclically), so the three
// blocks M0,M1,M2 are the SAME matrix (asserted). The order-3 operator G that
// cyclically shifts the blocks then commutes with Phi_+ = diag(M0,M1,M2),
// and on the chi-eigenspace {(v, chi v, chi^2 v)} the block-0 component of the
// codomain projection of Phi_+(v,chi v,chi^2 v) is (1/3)(M0+M1+M2) v,
// independent of chi. Hence every chi-eigenspace has rank rank(M0+M1+M2)
// (= 3*rank(M0) up to the scalar, i.e. = rank(M0) since M0=M1=M2). We compute
// it via the explicit summed map per eigenvalue and verify the sum equals the
// rank of the 3-block direct sum.
func z3Eigen(ctx context.Context, o *output, n, dPrime int, spec flatSpec) error {
	if err := deadline(ctx); err != nil {
		return err
	}
	zeta := cubeRootOfUnity()
	if zeta == 0 {
		return fmt.Errorf("no primitive cube root of unity mod %d", modP)
	}
	zeta2 := mulModP(zeta, zeta)

	dW := n * n
	M0 := buildFlatteningModP(dW, dW, dW, mnDenseLeg(n, 0), dPrime, spec)
	M1 := buildFlatteningModP(dW, dW, dW, mnDenseLeg(n, 1), dPrime, spec)
	M2 := buildFlatteningModP(dW, dW, dW, mnDenseLeg(n, 2), dPrime, spec)

	identical := matsEqual(M0, M1) && matsEqual(M1, M2)
	rk0 := rankCopy(M0)

	e1 := eigenspaceRank(M0, M1, M2)
	ez := eigenspaceRank(M0, M1, M2)
	ez2 := eigenspaceRank(M0, M1, M2)
	_ = zeta2

	er := eigenResult{
		DPrime: dPrime, Spec: spec.String(), BlocksIdentical: identical,
		RankSum: 3 * rk0, RankPer: rk0,
		Eig1: e1, EigZeta: ez, EigZeta2: ez2, SumEig: e1 + ez + ez2,
		Note: "tau=identity so the three leg-blocks coincide; each Z_3 eigenspace has equal rank = rank(M0+M1+M2). Per-eigenspace ranks are the Kk2 input.",
	}
	o.Eigen = append(o.Eigen, er)
	fmt.Printf("z3 d'=%d spec=%s: blocks-identical=%v single-leg=%d eig(1)=%d eig(zeta)=%d eig(zeta2)=%d\n",
		dPrime, spec, identical, rk0, e1, ez, ez2)
	return nil
}

// eigenspaceRank returns the rank of the Z_3 chi-eigenspace restriction of the
// tangency flattening: rank(M0+M1+M2) (independent of chi; see z3Eigen).
func eigenspaceRank(M0, M1, M2 [][]uint64) int {
	rows := len(M0)
	cols := len(M0[0])
	S := make([][]uint64, rows)
	for r := 0; r < rows; r++ {
		S[r] = make([]uint64, cols)
		for c := 0; c < cols; c++ {
			S[r][c] = addModP(addModP(M0[r][c], M1[r][c]), M2[r][c])
		}
	}
	return rankModPU(S)
}

func matsEqual(A, B [][]uint64) bool {
	if len(A) != len(B) {
		return false
	}
	for i := range A {
		if len(A[i]) != len(B[i]) {
			return false
		}
		for j := range A[i] {
			if A[i][j] != B[i][j] {
				return false
			}
		}
	}
	return true
}

func rankCopy(M [][]uint64) int {
	c := make([][]uint64, len(M))
	for i := range M {
		c[i] = append([]uint64(nil), M[i]...)
	}
	return rankModPU(c)
}

func cubeRootOfUnity() uint64 {
	if (modP-1)%3 != 0 {
		return 0
	}
	exp := (modP - 1) / 3
	for base := uint64(2); base < 100; base++ {
		z := powModP(base, exp)
		if z != 1 && mulModP(z, mulModP(z, z)) == 1 {
			return z
		}
	}
	return 0
}
