package main

// Exact arithmetic over the number field K = Q(sqrt 3), the character field of
// S_4 (the box / 2-dim irrep basis carries sqrt 3 entries; see GM 1612.01527
// eq. s4-basis). An element is a + b*sqrt3 with a, b in Q. All representation
// matrices and Fourier inner products live in K, so the constructed polynomial
// constraint systems have coefficients in K and Groebner is computed over K by
// SageMath downstream (Hu7 route A-hybrid).

import (
	"fmt"
	"math/big"
)

// Q3 is an element a + b*sqrt(3) of Q(sqrt 3), with a, b exact rationals.
type Q3 struct {
	A, B *big.Rat
}

// q3 builds a + b*sqrt3 from int64 numerators/denominators (denominators 1 by
// default via the helper below); kept minimal — most construction goes through
// q3i and the arithmetic ops.
func q3(a, b *big.Rat) Q3 { return Q3{A: a, B: b} }

// q3i builds the integer element a + b*sqrt3.
func q3i(a, b int64) Q3 {
	return Q3{A: big.NewRat(a, 1), B: big.NewRat(b, 1)}
}

// q3rat builds the rational scalar p/q (no sqrt3 part).
func q3rat(p, q int64) Q3 {
	return Q3{A: big.NewRat(p, q), B: big.NewRat(0, 1)}
}

var q3Zero = q3i(0, 0)
var q3One = q3i(1, 0)

// IsZero reports whether x == 0 in K.
func (x Q3) IsZero() bool {
	return x.A.Sign() == 0 && x.B.Sign() == 0
}

// Equal reports x == y.
func (x Q3) Equal(y Q3) bool {
	return x.A.Cmp(y.A) == 0 && x.B.Cmp(y.B) == 0
}

// Add returns x + y.
func (x Q3) Add(y Q3) Q3 {
	return Q3{
		A: new(big.Rat).Add(x.A, y.A),
		B: new(big.Rat).Add(x.B, y.B),
	}
}

// Sub returns x - y.
func (x Q3) Sub(y Q3) Q3 {
	return Q3{
		A: new(big.Rat).Sub(x.A, y.A),
		B: new(big.Rat).Sub(x.B, y.B),
	}
}

// Neg returns -x.
func (x Q3) Neg() Q3 {
	return Q3{
		A: new(big.Rat).Neg(x.A),
		B: new(big.Rat).Neg(x.B),
	}
}

// Mul returns x*y. (a+b√3)(c+d√3) = (ac+3bd) + (ad+bc)√3.
func (x Q3) Mul(y Q3) Q3 {
	ac := new(big.Rat).Mul(x.A, y.A)
	bd := new(big.Rat).Mul(x.B, y.B)
	bd.Mul(bd, big.NewRat(3, 1))
	ad := new(big.Rat).Mul(x.A, y.B)
	bc := new(big.Rat).Mul(x.B, y.A)
	return Q3{
		A: ac.Add(ac, bd),
		B: ad.Add(ad, bc),
	}
}

// Inv returns 1/x; panics if x == 0. Uses the conjugate a-b√3 and norm a^2-3b^2.
func (x Q3) Inv() Q3 {
	if x.IsZero() {
		panic("Q3.Inv: division by zero")
	}
	a2 := new(big.Rat).Mul(x.A, x.A)
	b2 := new(big.Rat).Mul(x.B, x.B)
	b2.Mul(b2, big.NewRat(3, 1))
	norm := a2.Sub(a2, b2) // a^2 - 3 b^2, nonzero since 3 is not a square in Q
	invNorm := new(big.Rat).Inv(norm)
	return Q3{
		A: new(big.Rat).Mul(x.A, invNorm),
		B: new(big.Rat).Mul(new(big.Rat).Neg(x.B), invNorm),
	}
}

// String renders x for human / Sage-readable output (Sage understands sqrt(3)).
func (x Q3) String() string {
	switch {
	case x.B.Sign() == 0:
		return x.A.RatString()
	case x.A.Sign() == 0:
		return fmt.Sprintf("(%s)*sqrt3", x.B.RatString())
	default:
		return fmt.Sprintf("(%s + (%s)*sqrt3)", x.A.RatString(), x.B.RatString())
	}
}
