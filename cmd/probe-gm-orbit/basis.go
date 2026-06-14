package main

import "math/big"

// The orthogonal basis of rho⊗rho* = id ⊕ box ⊕ rho ⊕ rho' from GM 1612.01527
// eq. s4-basis. These 9 matrices are the "test directions": the ansatz is a
// valid decomposition iff <T_ansatz, A⊗B⊗C> = tr(ABC) for all triples (A,B,C)
// from this basis (the orbit sum annihilates everything outside the diagonal
// trivial subspaces, so only basis triples are informative — GM sec 4.1).

// rrStarBasis returns the 9 basis matrices, in order:
//
//	0: id
//	1: box_x   2: box_y                 (2-dim irrep "beta")
//	3: s_1     4: s_2     5: s_3        (standard rho: off-diag symmetric)
//	6: a_1     7: a_2     8: a_3        (anti-standard rho': antisymmetric)
//
// box_x, box_y carry the sqrt(3) entries (the K = Q(sqrt 3) character field).
func rrStarBasis() []Mat {
	id := identMat()

	// box_x = diag(1, -1/2, -1/2)
	boxX := zeroMat()
	boxX[0][0] = q3i(1, 0)
	boxX[1][1] = q3rat(-1, 2)
	boxX[2][2] = q3rat(-1, 2)

	// box_y = diag(0, sqrt3/2, -sqrt3/2)
	boxY := zeroMat()
	boxY[1][1] = q3(big.NewRat(0, 1), big.NewRat(1, 2))  // (sqrt3)/2
	boxY[2][2] = q3(big.NewRat(0, 1), big.NewRat(-1, 2)) // -(sqrt3)/2

	// s_1: symmetric, 1s at (2,3),(3,2) -> 0-indexed (1,2),(2,1)
	s1 := zeroMat()
	s1[1][2] = q3One
	s1[2][1] = q3One
	// s_2: 1s at (1,3),(3,1) -> (0,2),(2,0)
	s2 := zeroMat()
	s2[0][2] = q3One
	s2[2][0] = q3One
	// s_3: 1s at (1,2),(2,1) -> (0,1),(1,0)
	s3 := zeroMat()
	s3[0][1] = q3One
	s3[1][0] = q3One

	// a_1: +1 at (2,3), -1 at (3,2) -> (1,2)=+1,(2,1)=-1
	a1 := zeroMat()
	a1[1][2] = q3One
	a1[2][1] = q3i(-1, 0)
	// a_2: -1 at (1,3), +1 at (3,1) -> (0,2)=-1,(2,0)=+1
	a2 := zeroMat()
	a2[0][2] = q3i(-1, 0)
	a2[2][0] = q3One
	// a_3: +1 at (1,2), -1 at (2,1) -> (0,1)=+1,(1,0)=-1
	a3 := zeroMat()
	a3[0][1] = q3One
	a3[1][0] = q3i(-1, 0)

	return []Mat{id, boxX, boxY, s1, s2, s3, a1, a2, a3}
}
