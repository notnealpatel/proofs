package main

import (
	"math/big"
	"math/bits"
)

// modP is a prime near 2^61 used for the fast random-search rank computation.
// 2^61 - 1 is a Mersenne prime; products of two reduced residues fit in 122
// bits, so we use math/bits.Mul64 + a 128-bit reduction. Mod-p rank is always
// <= true rank, and for random data equals the true rank with overwhelming
// probability (probability of a spurious rank drop is O(rank / p)).
const modP uint64 = (uint64(1) << 61) - 1

// mulModP returns a*b mod modP for a,b in [0, modP).
func mulModP(a, b uint64) uint64 {
	hi, lo := bits.Mul64(a, b)
	return reduce128(hi, lo)
}

// reduce128 reduces the 128-bit value hi*2^64 + lo modulo p = 2^61 - 1.
// Uses 2^61 = 1 (mod p): split the 128-bit value into 61-bit limbs and sum.
func reduce128(hi, lo uint64) uint64 {
	const m = (uint64(1) << 61) - 1 // = modP
	// 128-bit value = lo + hi*2^64. Decompose into 61-bit limbs L0,L1,L2:
	//   L0 = bits [0,61)
	//   L1 = bits [61,122)
	//   L2 = bits [122,128)   (only 6 bits)
	// Since 2^61 = 1 and 2^122 = 1 (mod p), value = L0 + L1 + L2 (mod p).
	l0 := lo & m
	l1 := (lo >> 61) | ((hi << 3) & m) // bits 61..121
	l2 := hi >> 58                     // bits 122..127
	s := l0 + l1 + l2                  // each < 2^61, sum < 2^63: no overflow
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

// powModP computes base^exp mod modP.
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

// invModP computes the modular inverse via Fermat's little theorem.
func invModP(a uint64) uint64 {
	return powModP(a, modP-2)
}

// rankModP computes the rank of an integer matrix reduced mod modP using
// Gaussian elimination over F_p. The input M is consumed (copied internally).
// Returns the rank.
func rankModP(M [][]int64) int {
	rows := len(M)
	if rows == 0 {
		return 0
	}
	cols := len(M[0])
	// copy into uint64 mod p
	a := make([][]uint64, rows)
	for r := 0; r < rows; r++ {
		a[r] = make([]uint64, cols)
		for c := 0; c < cols; c++ {
			v := M[r][c] % int64(modP)
			if v < 0 {
				v += int64(modP)
			}
			a[r][c] = uint64(v)
		}
	}
	return rankModPInPlace(a, rows, cols)
}

// rankModPU computes the rank of a uint64 (already mod-p) matrix in place.
func rankModPU(a [][]uint64) int {
	if len(a) == 0 {
		return 0
	}
	return rankModPInPlace(a, len(a), len(a[0]))
}

func rankModPInPlace(a [][]uint64, rows, cols int) int {
	rank := 0
	for col := 0; col < cols && rank < rows; col++ {
		// find pivot
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
		// normalize pivot row
		prow := a[rank]
		for c := col; c < cols; c++ {
			if prow[c] != 0 {
				prow[c] = mulModP(prow[c], inv)
			}
		}
		// eliminate below and above
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

// rankExactQ computes the exact rank over Q of an integer matrix using
// fraction-free / big.Rat Gaussian elimination. Used for structured families
// where entries are exact integers and we want a certified (not probabilistic)
// rank. Slower but exact.
func rankExactQ(M [][]int64) int {
	rows := len(M)
	if rows == 0 {
		return 0
	}
	cols := len(M[0])
	a := make([][]*big.Rat, rows)
	for r := 0; r < rows; r++ {
		a[r] = make([]*big.Rat, cols)
		for c := 0; c < cols; c++ {
			a[r][c] = new(big.Rat).SetInt64(M[r][c])
		}
	}
	rank := 0
	zero := new(big.Rat)
	for col := 0; col < cols && rank < rows; col++ {
		piv := -1
		for r := rank; r < rows; r++ {
			if a[r][col].Cmp(zero) != 0 {
				piv = r
				break
			}
		}
		if piv == -1 {
			continue
		}
		a[rank], a[piv] = a[piv], a[rank]
		prow := a[rank]
		pinv := new(big.Rat).Inv(prow[col])
		for r := 0; r < rows; r++ {
			if r == rank {
				continue
			}
			if a[r][col].Cmp(zero) == 0 {
				continue
			}
			f := new(big.Rat).Mul(a[r][col], pinv)
			arow := a[r]
			for c := col; c < cols; c++ {
				if prow[c].Cmp(zero) != 0 {
					tmp := new(big.Rat).Mul(f, prow[c])
					arow[c].Sub(arow[c], tmp)
				}
			}
		}
		rank++
	}
	return rank
}
