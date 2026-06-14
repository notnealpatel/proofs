package main

import (
	"context"
	"fmt"
	"math/rand"
)

// sanityGates implements task STEP 2(a)/(b): build the d'=3 tangency (mixed)
// flattening for a random rank-1 tensor (must give rank 0, since q(q-1)=0)
// and random rank-q tensors for small q (rank <= q(q-1)*C(dW-2,d'), the DM
// Cor 3.5 generic bound). A violation means a construction bug.
//
// We also assert the DM Prop 3.6 tightness anchor: the UNIT tensor of rank
// q = dW achieves rank exactly q(q-1)*C(q-2,d'). This is the load-bearing
// correctness check (it caught the original leg-assignment bug).
func sanityGates(ctx context.Context, o *output, n int, rng *rand.Rand) error {
	dW := n * n // 9
	dimX, dimY := dW, dW
	dPrime := 3
	costFactor := int(binom(dW-2, dPrime)) // C(7,3) = 35

	// (a)/(b) random rank-q bound check.
	for _, q := range []int{1, 2, 3, 5} {
		if err := deadline(ctx); err != nil {
			return err
		}
		dense := randRankQDense(dW, dimX, dimY, q, rng)
		M := buildFlatteningModP(dW, dimX, dimY, dense, dPrime, specMixed)
		rk := rankModPU(M)
		bound := q * (q - 1) * costFactor
		within := rk <= bound
		o.Sanity = append(o.Sanity, sanityResult{
			Name: fmt.Sprintf("random_rank%d", q), DPrime: dPrime, Rank: rk,
			Bound: bound, Q: q, WithinCap: within,
			Note: fmt.Sprintf("cost factor C(%d,%d)=%d", dW-2, dPrime, costFactor),
		})
		fmt.Printf("sanity random q=%d: rank=%d bound=q(q-1)*%d=%d within=%v\n",
			q, rk, costFactor, bound, within)
		if !within {
			return fmt.Errorf("SANITY FAILED random_rank%d: rank %d exceeds DM Cor 3.5 bound %d (construction bug). Halting per doctrine",
				q, rk, bound)
		}
	}

	// Prop 3.6 tightness anchor: unit tensor q=dW achieves q(q-1)*C(q-2,d').
	if err := deadline(ctx); err != nil {
		return err
	}
	q := dW
	dense := unitDense(dW, q)
	M := buildFlatteningModP(dW, dimX, dimY, dense, dPrime, specMixed)
	rk := rankModPU(M)
	expect := q * (q - 1) * int(binom(q-2, dPrime))
	o.Sanity = append(o.Sanity, sanityResult{
		Name: "unit_tightness_anchor", DPrime: dPrime, Rank: rk, Bound: expect,
		Q: q, WithinCap: rk == expect,
		Note: fmt.Sprintf("DM Prop 3.6: unit tensor q=%d must achieve q(q-1)*C(q-2,%d)=%d exactly", q, dPrime, expect),
	})
	fmt.Printf("sanity unit-anchor q=%d: rank=%d Prop3.6-expect=%d match=%v\n", q, rk, expect, rk == expect)
	if rk != expect {
		return fmt.Errorf("SANITY FAILED unit anchor: rank %d != DM Prop 3.6 achieving rank %d (construction bug). Halting per doctrine",
			rk, expect)
	}
	return nil
}

// randRankQDense builds a dense generic rank-q tensor over F_p (entries in
// [0,modP)) as sum_{l=1}^q a_l (x) b_l (x) c_l, layout w*dimX*dimY + x*dimY + y.
func randRankQDense(dW, dimX, dimY, q int, rng *rand.Rand) []int64 {
	dense := make([]int64, dW*dimX*dimY)
	for l := 0; l < q; l++ {
		a := randVecModP(dW, rng)
		b := randVecModP(dimX, rng)
		c := randVecModP(dimY, rng)
		for w := 0; w < dW; w++ {
			if a[w] == 0 {
				continue
			}
			base := w * dimX * dimY
			for x := 0; x < dimX; x++ {
				if b[x] == 0 {
					continue
				}
				ab := mulModP(a[w], b[x])
				row := base + x*dimY
				for y := 0; y < dimY; y++ {
					if c[y] == 0 {
						continue
					}
					dense[row+y] = int64(addModP(uint64(dense[row+y]), mulModP(ab, c[y])))
				}
			}
		}
	}
	return dense
}

// unitDense builds the unit tensor sum_{l<q} e_l (x) e_l (x) e_l.
func unitDense(dW, q int) []int64 {
	dense := make([]int64, dW*dW*dW)
	for l := 0; l < q && l < dW; l++ {
		dense[l*dW*dW+l*dW+l] = 1
	}
	return dense
}

func randVecModP(d int, rng *rand.Rand) []uint64 {
	v := make([]uint64, d)
	for i := range v {
		v[i] = uint64(rng.Int63n(int64(modP)))
	}
	return v
}
