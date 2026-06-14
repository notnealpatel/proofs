package main

import (
	"math/big"
	"testing"
)

// halfMat builds (1/2) * integer-matrix as a Mat.
func halfMat(rows [n][n]int64) Mat {
	var m Mat
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			m[i][j] = q3(big.NewRat(rows[i][j], 2), big.NewRat(0, 1))
		}
	}
	return m
}

// TestAnchorGMSingleOrbit reproduces GM 1612.01527 eq. first-family: the rank-25
// single-orbit S_4 decomposition of <3,3,3>. The published rank-1 seed
//
//	m = (1/2) [[-1, 1, 0], [1, -1, 0], [1, -1, 0]]
//
// summed over the full S_4 orbit (24 terms) plus id^⊗3 must equal the
// matrix-multiplication tensor exactly. This validates the rho⊗rho* basis,
// conjugation, sigma-twist, and reconstruction end to end (Stage 0).
func TestAnchorGMSingleOrbit(t *testing.T) {
	G := buildGroup()
	m := halfMat([n][n]int64{
		{-1, 1, 0},
		{1, -1, 0},
		{1, -1, 0},
	})
	// GM's seed has matrix rank 1 (rows are multiples of (-1,1,0)).
	ok, ai, bi, ci, got, want := verifyDecomposition(G, []Mat{m})
	if !ok {
		t.Fatalf("GM single-orbit seed failed to reconstruct MM at (E%d,E%d,E%d): got %s want %s",
			ai, bi, ci, got.String(), want.String())
	}
}

// TestAnchorGMSecondFamily checks the second published GM seed (eq.
// second-family), m' = (1/2)[[-1,1,1],[0,0,0],[1,-1,-1]], also reconstructs MM.
func TestAnchorGMSecondFamily(t *testing.T) {
	G := buildGroup()
	mp := halfMat([n][n]int64{
		{-1, 1, 1},
		{0, 0, 0},
		{1, -1, -1},
	})
	ok, ai, bi, ci, got, want := verifyDecomposition(G, []Mat{mp})
	if !ok {
		t.Fatalf("GM second-family seed failed at (E%d,E%d,E%d): got %s want %s",
			ai, bi, ci, got.String(), want.String())
	}
}
