package main

import (
	"math"
	"math/rand/v2"
)

// We parametrize r complex linear forms by a real vector x of length 2*r*N:
// for summand k and variable v, L[k][v] = x[base+2*(k*N+v)] + i*x[base+2*(k*N+v)+1].
// The residual map G(x) -> R^{2*numTriples} stacks (real, imag) of each triple
// residual r[t] = sum_k L[k]_a L[k]_b L[k]_c - F[t].
//
// We minimize ||G(x)||^2 by Levenberg-Marquardt with an analytic Jacobian.

type problem struct {
	r  int
	ts []triple
	F  map[triple]complex128
	// flattened target as (re,im) pairs aligned with ts
	Fre []float64
	Fim []float64
}

func newProblem(r int) *problem {
	ts := triples()
	F := targetTensor()
	fre := make([]float64, len(ts))
	fim := make([]float64, len(ts))
	for i, t := range ts {
		fre[i] = real(F[t])
		fim[i] = imag(F[t])
	}
	return &problem{r: r, ts: ts, F: F, Fre: fre, Fim: fim}
}

func (p *problem) nVars() int { return 2 * p.r * N }

// unpack converts the real parameter vector into complex linear forms.
func (p *problem) unpack(x []float64) [][N]complex128 {
	L := make([][N]complex128, p.r)
	for k := 0; k < p.r; k++ {
		for v := 0; v < N; v++ {
			idx := 2 * (k*N + v)
			L[k][v] = complex(x[idx], x[idx+1])
		}
	}
	return L
}

// residual returns the stacked real residual vector of length 2*len(ts):
// [Re r[0], Im r[0], Re r[1], Im r[1], ...].
func (p *problem) residual(x []float64) []float64 {
	L := p.unpack(x)
	m := len(p.ts)
	out := make([]float64, 2*m)
	for idx, t := range p.ts {
		var s complex128
		for k := 0; k < p.r; k++ {
			s += L[k][t.a] * L[k][t.b] * L[k][t.c]
		}
		s -= complex(p.Fre[idx], p.Fim[idx])
		out[2*idx] = real(s)
		out[2*idx+1] = imag(s)
	}
	return out
}

// cost is 0.5 * ||residual||^2.
func (p *problem) cost(x []float64) float64 {
	res := p.residual(x)
	var s float64
	for _, v := range res {
		s += v * v
	}
	return 0.5 * s
}

// jacobian builds the (2m) x (nVars) real Jacobian of the residual map.
// d r[t]/d L[k]_w for triple t=(a,b,c):
//
//	the term L[k]_a L[k]_b L[k]_c. Its derivative w.r.t. L[k]_w (complex):
//	sum over positions p in {a,b,c} with index==w of product of the other two.
//
// Then we split the complex derivative dC = u+iv of a complex residual r=Re+iIm
// w.r.t. complex variable z=xr+i*xi:
//
//	d Re(r)/d xr = Re(dC),  d Re(r)/d xi = -Im(dC)
//	d Im(r)/d xr = Im(dC),  d Im(r)/d xi =  Re(dC)
//
// since r is holomorphic in z (polynomial), dr/dz = dC and dr/d xr = dC,
// dr/d xi = i*dC.
func (p *problem) jacobian(x []float64) [][]float64 {
	L := p.unpack(x)
	m := len(p.ts)
	nv := p.nVars()
	J := make([][]float64, 2*m)
	for i := range J {
		J[i] = make([]float64, nv)
	}
	for idx, t := range p.ts {
		rowRe := J[2*idx]
		rowIm := J[2*idx+1]
		for k := 0; k < p.r; k++ {
			la, lb, lc := L[k][t.a], L[k][t.b], L[k][t.c]
			// complex partials w.r.t. each of the (possibly repeated) slots
			// dC[w] for w in distinct{a,b,c}
			// Use the symmetric monomial derivative:
			// d/dL_w (La Lb Lc) = (#positions equal to w) handled by chain rule.
			// We compute per-coordinate by summing contributions.
			contrib := map[int]complex128{}
			// position a: other two are lb,lc
			contrib[t.a] += lb * lc
			contrib[t.b] += la * lc
			contrib[t.c] += la * lb
			for w, dC := range contrib {
				colR := 2 * (k*N + w) // real part variable
				colI := colR + 1      // imag part variable
				dr, di := real(dC), imag(dC)
				// dr/d xr = dC: Re-> dr, Im-> di
				rowRe[colR] += dr
				rowIm[colR] += di
				// dr/d xi = i*dC = (-di) + i*dr
				rowRe[colI] += -di
				rowIm[colI] += dr
			}
		}
	}
	return J
}

// lmResult holds the outcome of one Levenberg-Marquardt run.
type lmResult struct {
	x         []float64
	cost      float64 // 0.5*||r||^2
	resNorm   float64 // ||r||_2
	iters     int
	converged bool
}

// levenbergMarquardt runs LM from initial x0 for up to maxIter iterations,
// stopping when residual norm < tol or step is negligible.
func levenbergMarquardt(p *problem, x0 []float64, maxIter int, tol float64) lmResult {
	x := append([]float64(nil), x0...)
	nv := p.nVars()
	lambda := 1e-3
	cost := p.cost(x)
	var lastRes float64
	for it := 0; it < maxIter; it++ {
		res := p.residual(x)
		lastRes = l2(res)
		if lastRes < tol {
			return lmResult{x: x, cost: cost, resNorm: lastRes, iters: it, converged: true}
		}
		J := p.jacobian(x)
		// Normal equations: (J^T J + lambda*diag(J^T J)) dx = -J^T res
		JTJ := matTtimesMat(J, nv)
		JTr := matTtimesVec(J, res, nv)
		// try step, adapt lambda
		accepted := false
		for tries := 0; tries < 12; tries++ {
			A := cloneSym(JTJ)
			for d := 0; d < nv; d++ {
				A[d][d] += lambda * (JTJ[d][d] + 1e-12)
			}
			dx, ok := solveSym(A, negate(JTr))
			if !ok {
				lambda *= 10
				continue
			}
			xn := addVec(x, dx)
			cn := p.cost(xn)
			if cn < cost {
				x = xn
				cost = cn
				lambda = math.Max(lambda*0.3, 1e-12)
				accepted = true
				break
			}
			lambda *= 5
		}
		if !accepted {
			// stuck
			return lmResult{x: x, cost: cost, resNorm: l2(p.residual(x)), iters: it, converged: false}
		}
	}
	return lmResult{x: x, cost: cost, resNorm: l2(p.residual(x)), iters: maxIter, converged: lastRes < tol}
}

func randomStart(p *problem, rng *rand.Rand, scale float64) []float64 {
	x := make([]float64, p.nVars())
	for i := range x {
		x[i] = rng.NormFloat64() * scale
	}
	return x
}

func l2(v []float64) float64 {
	var s float64
	for _, e := range v {
		s += e * e
	}
	return math.Sqrt(s)
}

func negate(v []float64) []float64 {
	out := make([]float64, len(v))
	for i, e := range v {
		out[i] = -e
	}
	return out
}

func addVec(a, b []float64) []float64 {
	out := make([]float64, len(a))
	for i := range a {
		out[i] = a[i] + b[i]
	}
	return out
}

// matTtimesMat computes J^T J (nv x nv symmetric) for J with 2m rows.
func matTtimesMat(J [][]float64, nv int) [][]float64 {
	out := make([][]float64, nv)
	for i := range out {
		out[i] = make([]float64, nv)
	}
	for _, row := range J {
		for i := 0; i < nv; i++ {
			ri := row[i]
			if ri == 0 {
				continue
			}
			oi := out[i]
			for j := i; j < nv; j++ {
				oi[j] += ri * row[j]
			}
		}
	}
	for i := 0; i < nv; i++ {
		for j := 0; j < i; j++ {
			out[i][j] = out[j][i]
		}
	}
	return out
}

func matTtimesVec(J [][]float64, v []float64, nv int) []float64 {
	out := make([]float64, nv)
	for r, row := range J {
		vr := v[r]
		if vr == 0 {
			continue
		}
		for i := 0; i < nv; i++ {
			out[i] += row[i] * vr
		}
	}
	return out
}

func cloneSym(a [][]float64) [][]float64 {
	out := make([][]float64, len(a))
	for i := range a {
		out[i] = append([]float64(nil), a[i]...)
	}
	return out
}
