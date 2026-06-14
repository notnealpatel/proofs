package main

import (
	"math"
	"math/big"
)

// certResult describes an attempt to certify a numerical candidate exactly.
type certResult struct {
	Status        string  `json:"status"` // "exact-rational", "numerical-only", "failed-reconstruction"
	MaxCoeffErr   float64 `json:"max_coeff_err"`
	RationalDenom int64   `json:"rational_denom_tried"`
	ExactResidual string  `json:"exact_residual,omitempty"`
	Detail        string  `json:"detail"`
}

// certify attempts to certify a numerical candidate. Strategy:
//  1. Try to recognize each (rescaled) linear-form coefficient as a small
//     rational (or rational combination of {1, zeta}). Cube-root and root-of-
//     unity scaling freedoms make naive rational rounding unreliable, so this
//     is a best-effort reconstruction.
//  2. If a rational reconstruction is found, recompute the residual with
//     big.Rat exact arithmetic and report the exact residual.
//  3. Otherwise report "numerical-only" with the achieved residual norm.
//
// Because the search runs over C with continuous scaling symmetry on each
// summand (L -> zeta^j * L with zeta^3 = 1 leaves L^3 invariant only up to the
// cube; actually any cube-root-of-unity rescaling of a summand preserves L^3),
// exact reconstruction of a generic numerical solution is genuinely hard. We
// flag numerical-only results prominently rather than overclaiming.
func certify(p *problem, x []float64) *certResult {
	L := p.unpack(x)

	// Best-effort: snap each coefficient to nearest k/D for D up to maxDen and
	// measure the worst-case rounding error. If small, recompute residual with
	// exact rationals.
	const maxDen = 720
	maxErr := 0.0
	denom := int64(1)
	type ratForm [N]struct{ re, im *big.Rat }
	rats := make([]ratForm, len(L))
	for k := range L {
		for v := 0; v < N; v++ {
			re, dr, er := nearestRational(real(L[k][v]), maxDen)
			im, di, ei := nearestRational(imag(L[k][v]), maxDen)
			rats[k][v].re = re
			rats[k][v].im = im
			if er > maxErr {
				maxErr = er
			}
			if ei > maxErr {
				maxErr = ei
			}
			denom = lcm(denom, lcm(dr, di))
		}
	}

	cr := &certResult{MaxCoeffErr: maxErr, RationalDenom: denom}

	if maxErr > 1e-6 {
		cr.Status = "numerical-only"
		cr.Detail = "coefficients do not snap to small rationals (expected: " +
			"complex solutions with root-of-unity / cube-root scalings rarely have " +
			"rational entries in this basis); reporting numerical residual only"
		return cr
	}

	// exact residual with big.Rat (real part only; if imaginary parts are
	// nonzero rationals we extend). We compute sum_k Re(L_k)^3-... but the form
	// is complex; do exact complex-rational arithmetic.
	exactNorm2 := big.NewRat(0, 1)
	for _, t := range p.ts {
		// sum over k of (re+im i)_a*(.)_b*(.)_c  - F[t]
		sumRe := big.NewRat(0, 1)
		sumIm := big.NewRat(0, 1)
		for k := range rats {
			pr, pi := mulRatC(rats[k][t.a].re, rats[k][t.a].im, rats[k][t.b].re, rats[k][t.b].im)
			pr, pi = mulRatC(pr, pi, rats[k][t.c].re, rats[k][t.c].im)
			sumRe.Add(sumRe, pr)
			sumIm.Add(sumIm, pi)
		}
		// subtract F[t] as nearest rational
		fr, _, _ := nearestRational(real(p.F[t]), maxDen)
		fi, _, _ := nearestRational(imag(p.F[t]), maxDen)
		sumRe.Sub(sumRe, fr)
		sumIm.Sub(sumIm, fi)
		t1 := new(big.Rat).Mul(sumRe, sumRe)
		t2 := new(big.Rat).Mul(sumIm, sumIm)
		exactNorm2.Add(exactNorm2, t1)
		exactNorm2.Add(exactNorm2, t2)
	}
	if exactNorm2.Sign() == 0 {
		cr.Status = "exact-rational"
		cr.ExactResidual = "0"
		cr.Detail = "EXACT rational Waring decomposition verified: residual is identically zero"
		return cr
	}
	cr.Status = "failed-reconstruction"
	cr.ExactResidual = exactNorm2.RatString()
	cr.Detail = "rational snap found but exact residual is nonzero; numerical solution does not certify rationally"
	return cr
}

func mulRatC(ar, ai, br, bi *big.Rat) (*big.Rat, *big.Rat) {
	// (ar+ai i)(br+bi i) = (ar br - ai bi) + (ar bi + ai br) i
	rr := new(big.Rat).Sub(new(big.Rat).Mul(ar, br), new(big.Rat).Mul(ai, bi))
	ri := new(big.Rat).Add(new(big.Rat).Mul(ar, bi), new(big.Rat).Mul(ai, br))
	return rr, ri
}

// nearestRational returns the closest p/q to x with q<=maxDen, plus q and the
// absolute error.
func nearestRational(x float64, maxDen int64) (*big.Rat, int64, float64) {
	best := big.NewRat(0, 1)
	bestErr := math.Abs(x)
	var bestDen int64 = 1
	for q := int64(1); q <= maxDen; q++ {
		pnum := math.Round(x * float64(q))
		approx := pnum / float64(q)
		e := math.Abs(approx - x)
		if e < bestErr {
			bestErr = e
			best = big.NewRat(int64(pnum), q)
			bestDen = q
		}
	}
	return best, bestDen, bestErr
}

func lcm(a, b int64) int64 {
	if a == 0 || b == 0 {
		return 1
	}
	g := gcd(a, b)
	return a / g * b
}

func gcd(a, b int64) int64 {
	for b != 0 {
		a, b = b, a%b
	}
	if a < 0 {
		return -a
	}
	return a
}
