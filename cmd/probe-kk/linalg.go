package main

import "math/bits"

// Mod-p arithmetic over the Mersenne prime p = 2^61 - 1, copied from
// cmd/probe-koszul (Ko1) for an independent, fast field. The DM
// wedge-(d'+2) flattening of M_3 is built directly over F_p; mod-p rank is
// always <= true rank and equals it with overwhelming probability for our
// (structured, integer-valued) matrices. We additionally cross-check the
// headline rank against several small word-sized primes (see primes.go).

const modP uint64 = (uint64(1) << 61) - 1

func mulModP(a, b uint64) uint64 {
	hi, lo := bits.Mul64(a, b)
	return reduce128(hi, lo)
}

func reduce128(hi, lo uint64) uint64 {
	const m = (uint64(1) << 61) - 1
	l0 := lo & m
	l1 := (lo >> 61) | ((hi << 3) & m)
	l2 := hi >> 58
	s := l0 + l1 + l2
	for s >= m {
		s = (s & m) + (s >> 61)
	}
	if s == m {
		s = 0
	}
	return s
}

func addModP(a, b uint64) uint64 {
	s := a + b
	if s >= modP || s < a {
		s -= modP
	}
	return s
}

func subModP(a, b uint64) uint64 {
	if a >= b {
		return a - b
	}
	return modP - (b - a)
}

func powModP(base, exp uint64) uint64 {
	r := uint64(1)
	base %= modP
	for exp > 0 {
		if exp&1 == 1 {
			r = mulModP(r, base)
		}
		base = mulModP(base, base)
		exp >>= 1
	}
	return r
}

func invModP(a uint64) uint64 {
	return powModP(a, modP-2)
}

// rankModPU computes the rank of a uint64 (already mod-p) matrix in place
// (the input is destroyed). Full Gauss-Jordan over F_p = F_{2^61-1}.
func rankModPU(a [][]uint64) int {
	if len(a) == 0 {
		return 0
	}
	return rankModPInPlace(a, len(a), len(a[0]))
}

func rankModPInPlace(a [][]uint64, rows, cols int) int {
	rank := 0
	for col := 0; col < cols && rank < rows; col++ {
		piv := -1
		for r := rank; r < rows; r++ {
			if a[r][col] != 0 {
				piv = r
				break
			}
		}
		if piv == -1 {
			continue
		}
		a[rank], a[piv] = a[piv], a[rank]
		inv := invModP(a[rank][col])
		prow := a[rank]
		for c := col; c < cols; c++ {
			if prow[c] != 0 {
				prow[c] = mulModP(prow[c], inv)
			}
		}
		for r := 0; r < rows; r++ {
			if r == rank {
				continue
			}
			f := a[r][col]
			if f == 0 {
				continue
			}
			arow := a[r]
			for c := col; c < cols; c++ {
				if prow[c] != 0 {
					arow[c] = subModP(arow[c], mulModP(f, prow[c]))
				}
			}
		}
		rank++
	}
	return rank
}

// --- generic small-prime arithmetic (for multi-prime cross-check) ---

// rankModSmall computes the rank of an integer-valued matrix (entries given
// already reduced into [0,p)) over F_p for an arbitrary odd prime p < 2^31,
// so products fit in uint64. The matrix is destroyed.
func rankModSmall(a [][]uint64, p uint64) int {
	rows := len(a)
	if rows == 0 {
		return 0
	}
	cols := len(a[0])
	rank := 0
	for col := 0; col < cols && rank < rows; col++ {
		piv := -1
		for r := rank; r < rows; r++ {
			if a[r][col] != 0 {
				piv = r
				break
			}
		}
		if piv == -1 {
			continue
		}
		a[rank], a[piv] = a[piv], a[rank]
		inv := invMod(a[rank][col], p)
		prow := a[rank]
		for c := col; c < cols; c++ {
			if prow[c] != 0 {
				prow[c] = (prow[c] * inv) % p
			}
		}
		for r := 0; r < rows; r++ {
			if r == rank {
				continue
			}
			f := a[r][col]
			if f == 0 {
				continue
			}
			arow := a[r]
			for c := col; c < cols; c++ {
				if prow[c] != 0 {
					v := (f * prow[c]) % p
					if arow[c] >= v {
						arow[c] -= v
					} else {
						arow[c] = p - (v - arow[c])
					}
				}
			}
		}
		rank++
	}
	return rank
}

func invMod(a, p uint64) uint64 {
	// extended Euclid
	var t, newt int64 = 0, 1
	var r, newr int64 = int64(p), int64(a)
	for newr != 0 {
		q := r / newr
		t, newt = newt, t-q*newt
		r, newr = newr, r-q*newr
	}
	if t < 0 {
		t += int64(p)
	}
	return uint64(t)
}
