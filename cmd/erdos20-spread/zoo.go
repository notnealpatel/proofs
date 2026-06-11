package main

import (
	"context"
	"math/rand"
)

func buildFamilyB() []uint {
	sets := [][]int{
		{0, 1, 2, 15}, {0, 1, 3, 15}, {0, 1, 4, 5}, {0, 4, 14, 16}, {0, 4, 14, 18},
		{0, 8, 9, 15}, {0, 8, 10, 15}, {1, 2, 3, 4}, {1, 2, 3, 7}, {1, 4, 5, 8},
		{1, 5, 6, 12}, {2, 9, 11, 12}, {2, 3, 12, 13}, {2, 3, 6, 12}, {3, 11, 12, 17},
		{3, 11, 14, 15}, {4, 14, 15, 19},
	}
	fam := make([]uint, 0, len(sets))
	for _, s := range sets {
		fam = append(fam, setToMask(s))
	}
	return sortFamily(fam)
}

// allKSets enumerates every k-subset bitmask of {0..n-1}.
func allKSets(n, k int) []uint {
	var res []uint
	var gen func(start, chosen int, cur uint)
	gen = func(start, chosen int, cur uint) {
		if chosen == k {
			res = append(res, cur)
			return
		}
		for i := start; i < n; i++ {
			gen(i+1, chosen+1, cur|(uint(1)<<uint(i)))
		}
	}
	gen(0, 0, 0)
	return res
}

// buildStar: all k-sets containing element 0.
func buildStar(k, n int) []uint {
	var fam []uint
	for _, s := range allKSets(n, k) {
		if s&1 != 0 {
			fam = append(fam, s)
		}
	}
	return sortFamily(fam)
}

// buildCoSingleton: all k-sets on {0..n-1} avoiding element n-1.
func buildCoSingleton(k, n int) []uint {
	top := uint(1) << uint(n-1)
	var fam []uint
	for _, s := range allKSets(n, k) {
		if s&top == 0 {
			fam = append(fam, s)
		}
	}
	return sortFamily(fam)
}

// buildRandom: sample m distinct k-sets uniformly from {0..n-1}.
func buildRandom(k, n, m int, rng *rand.Rand) []uint {
	pool := allKSets(n, k)
	if m > len(pool) {
		m = len(pool)
	}
	rng.Shuffle(len(pool), func(i, j int) { pool[i], pool[j] = pool[j], pool[i] })
	return sortFamily(pool[:m])
}

// buildHighSpread: resample/reject random m-set families until r* >= threshold,
// or give up after a bounded number of tries (returns nil). The reject loop is
// the ALWZ-style "no popular pair" engineering: sparse families with their
// members spread out so that no Z is over-represented.
func buildHighSpread(k, n, m int, rng *rand.Rand, threshold float64) ([]uint, float64) {
	pool := allKSets(n, k)
	if m > len(pool) {
		m = len(pool)
	}
	const maxTries = 4000
	var best []uint
	bestR := 0.0
	for t := 0; t < maxTries; t++ {
		rng.Shuffle(len(pool), func(i, j int) { pool[i], pool[j] = pool[j], pool[i] })
		fam := sortFamily(append([]uint(nil), pool[:m]...))
		sp := computeSpread(fam)
		if sp.RStar > bestR {
			bestR = sp.RStar
			best = fam
		}
		if sp.RStar >= threshold {
			return fam, sp.RStar
		}
	}
	// return the best we found even if below threshold (still informative)
	return best, bestR
}

// searchHighRatioLowTau exhaustively (for small n,k) scans families with
// tau(F) <= 2 and returns the few with the highest tau(S(F))/tau(F) ratio.
// Mirrors the erdos20/main.go counterexample search but keeps tau<=2 families
// for the spread-defect table. Bounded by ctx and a hard family-count cap.
func searchHighRatioLowTau(ctx context.Context, k, n int) [][]uint {
	ksets := allKSets(n, k)
	if len(ksets) > 22 {
		// 2^22 families is the practical ceiling for a tabletop sweep.
		return nil
	}
	total := (uint64(1) << uint(len(ksets))) - 1
	var best []cand
	consider := func(fam []uint) {
		tauF, _ := maxSunflower(fam)
		if tauF < 1 || tauF > 2 {
			return
		}
		shifted := fullShiftSweep(fam, n)
		tauSF, _ := maxSunflower(shifted)
		ratio := float64(tauSF) / float64(tauF)
		// keep only meaningfully-inflating families
		if ratio < 3.0 {
			return
		}
		best = append(best, cand{append([]uint(nil), fam...), ratio, tauF, tauSF})
	}
	for mask := uint64(1); mask <= total; mask++ {
		if mask&0x3FFFF == 0 && ctx.Err() != nil {
			break
		}
		// keep family sizes modest to bound tau cost
		if popcount64(mask) > 14 {
			continue
		}
		var fam []uint
		for i, s := range ksets {
			if mask&(uint64(1)<<uint(i)) != 0 {
				fam = append(fam, s)
			}
		}
		if len(fam) < 3 {
			continue
		}
		consider(fam)
	}
	// dedupe by ratio rank: keep top 3 distinct-ratio families
	sortCandDesc(best)
	var out [][]uint
	seenRatio := map[float64]bool{}
	for _, c := range best {
		if seenRatio[c.ratio] {
			continue
		}
		seenRatio[c.ratio] = true
		out = append(out, sortFamily(c.fam))
		if len(out) >= 3 {
			break
		}
	}
	return out
}

type cand struct {
	fam   []uint
	ratio float64
	tauF  int
	tauSF int
}

func sortCandDesc(c []cand) {
	for i := 1; i < len(c); i++ {
		for j := i; j > 0 && c[j].ratio > c[j-1].ratio; j-- {
			c[j], c[j-1] = c[j-1], c[j]
		}
	}
}

func popcount64(x uint64) int {
	c := 0
	for ; x != 0; x &= x - 1 {
		c++
	}
	return c
}

func nChooseK(n, k int) int {
	if k < 0 || k > n {
		return 0
	}
	if k > n-k {
		k = n - k
	}
	res := 1
	for i := 0; i < k; i++ {
		res = res * (n - i) / (i + 1)
	}
	return res
}
