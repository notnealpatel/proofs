package main

import (
	"context"
	"flag"
	"fmt"
	"math"
	"math/bits"
	"os"
	"sort"
	"sync"
	"sync/atomic"
	"time"
)

func main() {
	timeout := flag.Duration("timeout", 5*time.Minute, "computation timeout")
	n := flag.Int("n", 6, "ground set size [n]")
	k := flag.Int("k", 3, "uniformity")
	workers := flag.Int("workers", 32, "parallel workers")
	flag.Parse()

	ctx, cancel := context.WithTimeout(context.Background(), *timeout)
	defer cancel()

	run(ctx, *n, *k, *workers)
}

type result struct {
	ratio   float64
	family  []uint
	shifted []uint
	tauF    int
	tauSF   int
}

func run(ctx context.Context, n, k, workers int) {
	ksets := enumerateKSets(n, k)
	total := (1 << len(ksets)) - 1
	fmt.Printf("n=%d k=%d: %d k-sets, %d families, %d workers\n", n, k, len(ksets), total, workers)

	start := time.Now()
	var checked atomic.Int64
	var found atomic.Bool

	var mu sync.Mutex
	best := result{}
	var bestRatio atomic.Int64 // float64 bits for race-free progress display

	var wg sync.WaitGroup

	for w := 0; w < workers; w++ {
		wg.Add(1)
		go func(workerID int) {
			defer wg.Done()
			var local result
			for mask := workerID + 1; mask <= total; mask += workers {
				if ctx.Err() != nil || found.Load() {
					return
				}

				family := maskToFamily(ksets, mask)
				if len(family) < 2 {
					checked.Add(1)
					continue
				}

				tauF := maxSunflower(family)
				if tauF < 2 {
					checked.Add(1)
					continue
				}

				shifted := fullShift(family, n)
				tauSF := maxSunflower(shifted)

				bound := 3 * tauF * tauF
				if tauSF > bound {
					found.Store(true)
					fmt.Fprintf(os.Stderr, "\n")
					fmt.Printf("COUNTEREXAMPLE: tau(F)=%d, tau(S(F))=%d, bound=3*%d^2=%d\n", tauF, tauSF, tauF, bound)
					fmt.Printf("  F = %v\n", bitsetsToSets(family))
					fmt.Printf("  S(F) = %v\n", bitsetsToSets(shifted))
					return
				}

				ratio := float64(tauSF) / float64(bound)
				if ratio > local.ratio {
					local = result{ratio, append([]uint(nil), family...), append([]uint(nil), shifted...), tauF, tauSF}
				}

				checked.Add(1)
			}

			mu.Lock()
			if local.ratio > best.ratio {
				best = local
				bestRatio.Store(int64(math.Float64bits(local.ratio)))
			}
			mu.Unlock()
		}(w)
	}

	done := make(chan struct{})
	go func() {
		wg.Wait()
		close(done)
	}()

	ticker := time.NewTicker(100 * time.Millisecond)
	defer ticker.Stop()
	for {
		select {
		case <-ticker.C:
			c := checked.Load()
			r := math.Float64frombits(uint64(bestRatio.Load()))
			fmt.Fprintf(os.Stderr, "\r  %s  checked %d / %d (%.1f%%) max_ratio=%.4f", time.Since(start).Truncate(time.Millisecond), c, total, 100*float64(c)/float64(total), r)
		case <-done:
			fmt.Fprintf(os.Stderr, "\r\033[2K")
			elapsed := time.Since(start).Truncate(time.Millisecond)
			if !found.Load() {
				fmt.Printf("checked %d families in %s, no counterexample found\n", checked.Load(), elapsed)
				fmt.Printf("tightest: tau(F)=%d, tau(S(F))=%d, bound=%d, ratio=%.4f\n", best.tauF, best.tauSF, 3*best.tauF*best.tauF, best.ratio)
				fmt.Printf("  F = %v\n", bitsetsToSets(best.family))
			}
			return
		}
	}
}

func enumerateKSets(n, k int) []uint {
	var result []uint
	var gen func(start, chosen int, current uint)
	gen = func(start, chosen int, current uint) {
		if chosen == k {
			result = append(result, current)
			return
		}
		for i := start; i < n; i++ {
			gen(i+1, chosen+1, current|(1<<i))
		}
	}
	gen(0, 0, 0)
	return result
}

func maskToFamily(ksets []uint, mask int) []uint {
	var family []uint
	for i, s := range ksets {
		if mask&(1<<i) != 0 {
			family = append(family, s)
		}
	}
	return family
}

func maxSunflower(family []uint) int {
	if len(family) <= 1 {
		return len(family)
	}

	best := 1
	m := len(family)

	kernels := make(map[uint]bool)
	kernels[0] = true
	for i := 0; i < m; i++ {
		kernels[family[i]] = true
		for j := i + 1; j < m; j++ {
			kernels[family[i]&family[j]] = true
		}
	}

	for kernel := range kernels {
		var petals []uint
		for _, s := range family {
			if s&kernel == kernel {
				petal := s &^ kernel
				if petal != 0 {
					petals = append(petals, petal)
				}
			}
		}
		if len(petals) <= best {
			continue
		}
		sz := maxDisjoint(petals)
		if sz > best {
			best = sz
		}
	}
	return best
}

func maxDisjoint(masks []uint) int {
	if len(masks) == 0 {
		return 0
	}
	return maxDisjointRec(masks, 0, 0)
}

func maxDisjointRec(masks []uint, idx int, used uint) int {
	if idx == len(masks) {
		return 0
	}
	skip := maxDisjointRec(masks, idx+1, used)
	if masks[idx]&used != 0 {
		return skip
	}
	take := 1 + maxDisjointRec(masks, idx+1, used|masks[idx])
	if take > skip {
		return take
	}
	return skip
}

func fullShift(family []uint, n int) []uint {
	fset := make(map[uint]bool, len(family))
	for _, s := range family {
		fset[s] = true
	}

	changed := true
	for changed {
		changed = false
		for i := 0; i < n; i++ {
			for j := i + 1; j < n; j++ {
				if shiftIJ(fset, i, j) {
					changed = true
				}
			}
		}
	}

	result := make([]uint, 0, len(fset))
	for s := range fset {
		result = append(result, s)
	}
	sort.Slice(result, func(a, b int) bool { return result[a] < result[b] })
	return result
}

func shiftIJ(fset map[uint]bool, i, j int) bool {
	iBit := uint(1 << i)
	jBit := uint(1 << j)
	changed := false

	var toAdd []uint
	var toRemove []uint
	for s := range fset {
		if s&iBit == 0 && s&jBit != 0 {
			shifted := (s &^ jBit) | iBit
			if !fset[shifted] {
				toAdd = append(toAdd, shifted)
				toRemove = append(toRemove, s)
				changed = true
			}
		}
	}
	for _, s := range toRemove {
		delete(fset, s)
	}
	for _, s := range toAdd {
		fset[s] = true
	}
	return changed
}

func bitsetsToSets(family []uint) [][]int {
	var result [][]int
	for _, s := range family {
		var elems []int
		for b := s; b != 0; b &= b - 1 {
			elems = append(elems, bits.TrailingZeros(b)+1)
		}
		result = append(result, elems)
	}
	return result
}
