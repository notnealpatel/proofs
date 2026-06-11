package main

import (
	"math"
	"math/big"
)

// spreadResult records r*(F) = 1/rho(F), the largest r for which F is
// r-spread (matching IsRSpread over ℚ: |F_Z| * r^|Z| <= |F| for all nonempty
// Z with F_Z != ∅). r*(F) = min over such Z of (|F|/|F_Z|)^(1/|Z|), and the
// minimizing Z is the "popular" witness that caps spreadness. We report the
// witness exactly as (Z, |F_Z|, |F|) plus a float approximation; the float is
// never used in the comparison logic (that is exact big.Int cross-multiply).
type spreadResult struct {
	RStar    float64 `json:"r_star"`        // 1/rho, float approximation
	WitnessZ []int   `json:"witness_z"`     // the minimizing Z (0-indexed)
	FZcard   int     `json:"witness_fz"`    // |F_Z| at the witness
	Fcard    int     `json:"witness_total"` // |F|
}

// computeSpread enumerates every nonempty Z that is a subset of some member
// (otherwise F_Z = ∅ and Z is irrelevant), and finds the Z minimizing
// (|F|/|F_Z|)^(1/|Z|). The comparison is exact: to decide whether candidate A
// = (a=|F|, b=|F_A|, p=|A|) gives a smaller value than the running best B =
// (a, c=|F_B|, q=|B|) -- note |F| is common -- we compare
//
//	(a/b)^(1/p)  <  (a/c)^(1/q)
//
// raise both sides to the positive power p*q:
//
//	(a/b)^q  <  (a/c)^p
//	a^q * c^p  <  a^p * b^q
//
// which is a pure integer comparison via big.Int. Z is enumerated over the
// union (deduped) of all subsets of all members.
func computeSpread(family []uint) spreadResult {
	N := len(family)
	if N == 0 {
		return spreadResult{RStar: math.Inf(1)}
	}
	// Collect all distinct nonempty Z that are subsets of some member, along
	// with |F_Z|. We enumerate subsets per member then accumulate counts over
	// the whole family so |F_Z| is exact.
	fzCount := make(map[uint]int)
	seen := make(map[uint]struct{})
	for _, s := range family {
		// enumerate nonempty subsets of s
		for sub := s; sub != 0; sub = (sub - 1) & s {
			seen[sub] = struct{}{}
		}
	}
	for z := range seen {
		cnt := 0
		for _, s := range family {
			if s&z == z {
				cnt++
			}
		}
		fzCount[z] = cnt
	}

	a := big.NewInt(int64(N)) // |F|, common numerator

	var bestZ uint
	haveBest := false
	var bestB *big.Int // |F_bestZ|
	var bestQ int      // |bestZ|

	// scratch big.Ints
	lhs := new(big.Int)
	rhs := new(big.Int)
	tmp := new(big.Int)

	for z, fz := range fzCount {
		p := bits_OnesCountU(z)
		b := big.NewInt(int64(fz))
		if !haveBest {
			bestZ, bestB, bestQ, haveBest = z, b, p, true
			continue
		}
		// compare candidate (b,p) vs best (bestB,bestQ):
		// candidate value (a/b)^(1/p) < best value (a/bestB)^(1/bestQ)
		// raise to p*bestQ:  a^bestQ * bestB^p  <  a^p * b^bestQ
		lhs.Exp(a, big.NewInt(int64(bestQ)), nil)
		tmp.Exp(bestB, big.NewInt(int64(p)), nil)
		lhs.Mul(lhs, tmp)

		rhs.Exp(a, big.NewInt(int64(p)), nil)
		tmp.Exp(b, big.NewInt(int64(bestQ)), nil)
		rhs.Mul(rhs, tmp)

		if lhs.Cmp(rhs) < 0 {
			bestZ, bestB, bestQ = z, b, p
		}
	}

	if !haveBest {
		return spreadResult{RStar: math.Inf(1)}
	}

	rstar := math.Pow(float64(N)/float64(bestB.Int64()), 1.0/float64(bestQ))
	return spreadResult{
		RStar:    rstar,
		WitnessZ: maskToSet(bestZ),
		FZcard:   int(bestB.Int64()),
		Fcard:    N,
	}
}
