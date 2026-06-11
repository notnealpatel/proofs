package main

import (
	"math/bits"
	"sort"
)

// A family is represented as a sorted []uint of bitmasks over the ground set
// {0..n-1}. Each member is a k-element subset. All routines here are an
// independent first-principles re-implementation of the Lean development's
// shift and sunflower conventions (Sunflower.lean, Counterexample.lean), and
// are calibrated against familyB (tau 2 -> 17) before any scaling.

func setToMask(elems []int) uint {
	var m uint
	for _, e := range elems {
		m |= uint(1) << uint(e)
	}
	return m
}

// maskToSet returns the sorted member list (0-indexed) of a bitmask.
func maskToSet(m uint) []int {
	elems := []int{}
	for b := m; b != 0; b &= b - 1 {
		elems = append(elems, bits.TrailingZeros(b))
	}
	return elems
}

func familyToSets(family []uint) [][]int {
	out := make([][]int, 0, len(family))
	for _, s := range family {
		out = append(out, maskToSet(s))
	}
	return out
}

func sortFamily(family []uint) []uint {
	cp := append([]uint(nil), family...)
	sort.Slice(cp, func(a, b int) bool { return cp[a] < cp[b] })
	return cp
}

// franklShiftSet: if i∉S and j∈S then insert i (S.erase j) else S.
// Matches franklShiftSet in Sunflower.lean.
func franklShiftSet(i, j int, s uint) uint {
	iBit := uint(1) << uint(i)
	jBit := uint(1) << uint(j)
	if s&iBit == 0 && s&jBit != 0 {
		return (s &^ jBit) | iBit
	}
	return s
}

// franklShift: family.image (S -> if franklShiftSet i j S ∈ family then S else
// franklShiftSet i j S). The membership test is against the INPUT family, and
// the image dedupes. Matches franklShift / franklShiftC in the Lean files.
func franklShift(i, j int, family []uint) []uint {
	fset := make(map[uint]struct{}, len(family))
	for _, s := range family {
		fset[s] = struct{}{}
	}
	out := make(map[uint]struct{}, len(family))
	for _, s := range family {
		ss := franklShiftSet(i, j, s)
		if _, ok := fset[ss]; ok {
			out[s] = struct{}{}
		} else {
			out[ss] = struct{}{}
		}
	}
	res := make([]uint, 0, len(out))
	for s := range out {
		res = append(res, s)
	}
	return sortFamily(res)
}

// fullShiftSweep: one full lex pass over pairs (i,j) with i<j, i ascending in
// the outer loop and j ascending in the inner loop, applying franklShift
// left-to-right and feeding each result into the next. This is exactly the
// `sweep`/`applyChain` convention of Counterexample.lean.
func fullShiftSweep(family []uint, n int) []uint {
	cur := append([]uint(nil), family...)
	for i := 0; i < n; i++ {
		for j := i + 1; j < n; j++ {
			cur = franklShift(i, j, cur)
		}
	}
	return cur
}

// maxSunflower computes tau(F): the largest k for which F contains a
// k-sunflower. A sunflower is a subfamily with a common kernel K such that
// every member contains K, every petal S\K is nonempty, and every pairwise
// intersection equals K. Equivalently, fixing a kernel K, the petals of the
// members containing K must be pairwise disjoint and nonempty; tau is the
// maximum over candidate kernels of the largest such pairwise-disjoint
// collection of petals. Candidate kernels are the empty set, every member,
// and every pairwise intersection (any sunflower's kernel is the common
// intersection, which for >=2 petals is a pairwise intersection, and for the
// 0/1-petal degenerate cases is bounded by the trivial answer).
// maxDisjointBudget caps the branch-and-bound at this many recursion nodes per
// kernel. On exhaustion we fall back to the best (a valid lower bound) and mark
// the result inexact. Generous enough that all spread families in the zoo
// resolve exactly; the cap only fires on pathological dense matchings, where a
// lower bound on tau still yields an UPPER bound on the ratio tau(S(F))/tau(F),
// keeping the kill test conservative (never a false kill).
const maxDisjointBudget = 40_000_000

// maxSunflower returns tau(F) and whether the value is exact. exact is false
// only if some kernel's set-packing search hit the node budget.
func maxSunflower(family []uint) (int, bool) {
	m := len(family)
	if m <= 1 {
		return m, true
	}
	best := 1
	exact := true
	kernels := make(map[uint]struct{})
	kernels[0] = struct{}{}
	for i := 0; i < m; i++ {
		kernels[family[i]] = struct{}{}
		for j := i + 1; j < m; j++ {
			kernels[family[i]&family[j]] = struct{}{}
		}
	}
	// Build the petal collection per kernel, then process kernels in descending
	// petal-count order so the high-yield star kernels raise `best` first. A
	// per-kernel upper bound (distinct petal elements divided by the smallest
	// petal size) lets us skip kernels whose packing cannot beat `best` --
	// crucially the empty kernel's expensive full-set matching, which is
	// dominated by a star kernel for the dense families and never binds.
	type kpetals struct {
		petals []uint
		ub     int
	}
	var ks []kpetals
	for kernel := range kernels {
		petals := make([]uint, 0, m)
		for _, s := range family {
			if s&kernel == kernel {
				petal := s &^ kernel
				if petal != 0 {
					petals = append(petals, petal)
				}
			}
		}
		if len(petals) <= 1 {
			continue
		}
		var union uint
		minSize := 64
		for _, p := range petals {
			union |= p
			if sz := bits_OnesCountU(p); sz < minSize {
				minSize = sz
			}
		}
		ub := len(petals)
		if minSize > 0 {
			if cap := bits_OnesCountU(union) / minSize; cap < ub {
				ub = cap
			}
		}
		ks = append(ks, kpetals{petals, ub})
	}
	// Order by descending upper bound: star-like kernels (singleton petals,
	// large ub) come first and raise `best`, which then prunes the costly
	// near-matching kernels (small ub) outright. Tie-break does not matter.
	sort.Slice(ks, func(a, b int) bool { return ks[a].ub > ks[b].ub })
	for _, kp := range ks {
		if kp.ub <= best {
			continue
		}
		sz, ok := maxDisjoint(kp.petals)
		if !ok {
			exact = false
		}
		if sz > best {
			best = sz
		}
	}
	return best, exact
}

// maxDisjoint returns the size of the largest pairwise-disjoint subcollection
// of the given masks (a maximum set packing) and whether the search completed
// within the node budget. It runs a branch-and-bound seeded by a greedy
// solution; elements are tried in descending support order; at each node we
// branch on taking the current mask (if compatible) or skipping it, pruning
// when the optimistic bound (current + remaining) cannot beat the best found.
func maxDisjoint(masks []uint) (int, bool) {
	n := len(masks)
	if n == 0 {
		return 0, true
	}
	ms := append([]uint(nil), masks...)
	sort.Slice(ms, func(a, b int) bool {
		return bits_OnesCountU(ms[a]) > bits_OnesCountU(ms[b])
	})
	// greedy lower bound to seed pruning
	best := greedyPacking(ms)
	exact := true
	nodes := 0
	var dfs func(idx, count int, used uint)
	dfs = func(idx, count int, used uint) {
		nodes++
		if nodes > maxDisjointBudget {
			exact = false
			return
		}
		if count > best {
			best = count
		}
		if count+(n-idx) <= best {
			return
		}
		if idx == n {
			return
		}
		if ms[idx]&used == 0 {
			dfs(idx+1, count+1, used|ms[idx])
		}
		dfs(idx+1, count, used)
	}
	dfs(0, 0, 0)
	return best, exact
}

// greedyPacking takes masks in their given order, accepting each if disjoint
// from those accepted so far. A valid lower bound on the maximum packing.
func greedyPacking(ms []uint) int {
	var used uint
	count := 0
	for _, m := range ms {
		if m&used == 0 {
			used |= m
			count++
		}
	}
	return count
}

func bits_OnesCountU(z uint) int {
	c := 0
	for ; z != 0; z &= z - 1 {
		c++
	}
	return c
}
