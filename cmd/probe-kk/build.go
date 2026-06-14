package main

// Construction of the Dolezalek-Michalek (DM, arXiv:2602.12762, Sec 3) k=2
// "wedge-(d'+2)" Kronecker-Koszul / tangency flattening of a 3-tensor
// T in V1 (x) V2 (x) V3, with the wedge on leg 1.
//
// DM data: r=3, k=2, lambda_{1,1}={1,2} (the two T-copies of leg 1 fused),
// lambda_{2,1}={1}, lambda_{2,2}={2}, lambda_{3,1}={1}, lambda_{3,2}={2}
// (singletons), d'_{1,1}=d' the only nonzero exterior degree. The
// Kronecker-Koszul tensor is
//
//   T_pi = sum_{a1,a2,b1,b2,c1,c2} sum_{|P|=d'}
//            T_{a1 b1 c1} T_{a2 b2 c2}
//            (e_{a1} ^ e_{a2} ^ w_P) (x) w_P^*
//            (x) f_{b1} (x) f_{b2} (x) g_{c1} (x) g_{c2}
//
// in  Lambda^{d'+2}V1 (x) Lambda^{d'}V1^* (x) V2(copy1) (x) V2(copy2)
//     (x) V3(copy1) (x) V3(copy2),  w_P = ^_{p in P} e_p.
//
// A Kronecker-Koszul flattening (Def, Cor 3.5) is any classical flattening of
// T_pi. We use the "tangency" flattening of DM eq (eq:mamu-tangency) /
// Prop 5.1, which we have VERIFIED reproduces DM's M_2 rank 64 exactly and the
// Prop 3.6 unit-tensor achieving rank q(q-1)*C(q-2,d'). In terms of the six
// T_pi legs the passenger split is the "mixed" one:
//
//   domain   = Lambda^{d'+2}V1^* (x) V2(copy1)^* (x) V3(copy2)^*   (R, b1, c2)
//   codomain = Lambda^{d'}V1^*   (x) V2(copy2)   (x) V3(copy1)     (P, b2, c1)
//
// (sizes for M_3, n=9, d'=3: domain C(9,5)*81 = 10206, codomain C(9,3)*81 =
//  6804). The complementary "byleg" split (V2copy1,V2copy2 -> one side; V3 ->
//  other) is also a valid Cor 3.5 flattening but gives a strictly lower rank
//  on M_3; "mixed" is DM's tangency flattening and the family's best member.
//
// Matrix entry, rows = codomain, cols = domain:
//   Phi[(P,b2,c1),(R,b1,c2)] =
//      sum over ordered (a1,a2) with {a1,a2} = R\P (P subset R, |R\P|=2):
//         sign(a1 ^ a2 ^ w_P -> e_R) * T_{a1 b1 c1} T_{a2 b2 c2}.

import "math/bits"

// flatSpec selects the passenger split of a Kronecker-Koszul flattening.
type flatSpec int

const (
	// specMixed is DM's tangency flattening: domain {R, V2copy1, V3copy2},
	// codomain {P, V2copy2, V3copy1}. Verified against DM Prop 5.1 (M_2 -> 64)
	// and Prop 3.6 (unit -> q(q-1)*C(q-2,d')). The family's best member.
	specMixed flatSpec = iota
	// specByLeg: domain {R, V2copy1, V2copy2}, codomain {P, V3copy1, V3copy2}.
	// Also a valid Cor 3.5 flattening (matches Prop 3.6) but lower rank on M_3.
	specByLeg
)

func (s flatSpec) String() string {
	switch s {
	case specMixed:
		return "mixed(tangency)"
	case specByLeg:
		return "byleg"
	}
	return "?"
}

// mnDenseLeg returns M_n as a dense coefficient slice (entries +1) with the
// chosen wedge leg placed first. Layout: w*d^2 + x*d + y where d = n^2,
// w is the wedge-leg index, (x,y) the two passenger legs in cyclic order
// (legW+1, legW+2). Leg 0 = A (e_{ij}), 1 = B (e_{jk}), 2 = C (e_{ki}).
func mnDenseLeg(n, legW int) []int64 {
	d := n * n
	dense := make([]int64, d*d*d)
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			for k := 0; k < n; k++ {
				idx := [3]int{i*n + j, j*n + k, k*n + i}
				w := idx[legW]
				x := idx[(legW+1)%3]
				y := idx[(legW+2)%3]
				dense[w*d*d+x*d+y] = 1
			}
		}
	}
	return dense
}

// combos returns all p-subsets of {0,...,d-1} as sorted []int (the Lambda^p
// basis, lex order) and a lookup from bitmask -> basis position.
func combos(d, p int) ([][]int, map[uint64]int) {
	if p < 0 || p > d {
		return nil, map[uint64]int{}
	}
	var out [][]int
	idx := map[uint64]int{}
	cur := make([]int, p)
	var rec func(start, depth int)
	rec = func(start, depth int) {
		if depth == p {
			cp := append([]int(nil), cur...)
			var mask uint64
			for _, v := range cp {
				mask |= uint64(1) << uint(v)
			}
			idx[mask] = len(out)
			out = append(out, cp)
			return
		}
		for v := start; v <= d-p+depth; v++ {
			cur[depth] = v
			rec(v+1, depth+1)
		}
	}
	rec(0, 0)
	return out, idx
}

// wedgeSign returns the sign of sorting (a1, a2, sorted(P)) into ascending
// order, or 0 if any two of {a1,a2}∪P coincide (the wedge is then zero).
func wedgeSign(a1, a2 int, pmask uint64) int {
	if a1 == a2 {
		return 0
	}
	if pmask&(uint64(1)<<uint(a1)) != 0 || pmask&(uint64(1)<<uint(a2)) != 0 {
		return 0
	}
	seq := make([]int, 0, 2+bits.OnesCount64(pmask))
	seq = append(seq, a1, a2)
	for v := 0; v < 64; v++ {
		if pmask&(uint64(1)<<uint(v)) != 0 {
			seq = append(seq, v)
		}
	}
	inv := 0
	for i := 0; i < len(seq); i++ {
		for j := i + 1; j < len(seq); j++ {
			if seq[i] > seq[j] {
				inv++
			}
		}
	}
	if inv&1 == 1 {
		return -1
	}
	return 1
}

// passengerIndex maps the four passenger coordinates to (codomain-passenger,
// domain-passenger) flat indices according to the flattening spec. dimX,dimY
// are the passenger leg dimensions (= n^2 for M_n).
func passengerIndex(spec flatSpec, b1, c1, b2, c2, dimX, dimY int) (rowPass, colPass int) {
	switch spec {
	case specMixed: // domain {b1,c2}, codomain {b2,c1}
		return b2*dimY + c1, b1*dimY + c2
	case specByLeg: // domain {b1,b2}, codomain {c1,c2}
		return c1*dimY + c2, b1*dimX + b2
	}
	panic("bad flatSpec")
}

// buildFlatteningModP builds the chosen Kronecker-Koszul flattening of a dense
// tensor T (wedge leg first, layout w*dimX*dimY + x*dimY + y) directly over
// F_p (modP). Returns rows=codomain, cols=domain:
//
//	rows = C(dimW, d') * dimX * dimY        (codomain)
//	cols = C(dimW, d'+2) * dimX * dimY      (domain)
func buildFlatteningModP(dimW, dimX, dimY int, dense []int64, dPrime int, spec flatSpec) [][]uint64 {
	combP, _ := combos(dimW, dPrime)
	_, idxR := combos(dimW, dPrime+2)
	nP := len(combP)
	nR := len(combosCount(dimW, dPrime+2))

	pmask := make([]uint64, nP)
	for pp, P := range combP {
		var m uint64
		for _, v := range P {
			m |= uint64(1) << uint(v)
		}
		pmask[pp] = m
	}

	rows := nR * dimX * dimY
	cols := nP * dimX * dimY
	M := make([][]uint64, rows)
	for r := range M {
		M[r] = make([]uint64, cols)
	}

	T := func(a, b, c int) uint64 {
		v := dense[a*dimX*dimY+b*dimY+c]
		return uint64(((v % int64(modP)) + int64(modP)) % int64(modP))
	}

	for a1 := 0; a1 < dimW; a1++ {
		for a2 := 0; a2 < dimW; a2++ {
			if a1 == a2 {
				continue
			}
			for pp := 0; pp < nP; pp++ {
				sg := wedgeSign(a1, a2, pmask[pp])
				if sg == 0 {
					continue
				}
				rmask := pmask[pp] | (uint64(1) << uint(a1)) | (uint64(1) << uint(a2))
				rPos := idxR[rmask]
				for b1 := 0; b1 < dimX; b1++ {
					for c1 := 0; c1 < dimY; c1++ {
						t1 := T(a1, b1, c1)
						if t1 == 0 {
							continue
						}
						for b2 := 0; b2 < dimX; b2++ {
							for c2 := 0; c2 < dimY; c2++ {
								t2 := T(a2, b2, c2)
								if t2 == 0 {
									continue
								}
								rp, cp := passengerIndex(spec, b1, c1, b2, c2, dimX, dimY)
								row := rPos*dimX*dimY + rp
								col := pp*dimX*dimY + cp
								v := mulModP(t1, t2)
								if sg < 0 {
									M[row][col] = subModP(M[row][col], v)
								} else {
									M[row][col] = addModP(M[row][col], v)
								}
							}
						}
					}
				}
			}
		}
	}
	return M
}

// buildFlatteningSmallP is the same over a small prime p < 2^31.
func buildFlatteningSmallP(dimW, dimX, dimY int, dense []int64, dPrime int, spec flatSpec, p uint64) [][]uint64 {
	combP, _ := combos(dimW, dPrime)
	_, idxR := combos(dimW, dPrime+2)
	nP := len(combP)
	nR := len(combosCount(dimW, dPrime+2))

	pmask := make([]uint64, nP)
	for pp, P := range combP {
		var m uint64
		for _, v := range P {
			m |= uint64(1) << uint(v)
		}
		pmask[pp] = m
	}

	rows := nR * dimX * dimY
	cols := nP * dimX * dimY
	M := make([][]uint64, rows)
	for r := range M {
		M[r] = make([]uint64, cols)
	}
	T := func(a, b, c int) uint64 {
		v := dense[a*dimX*dimY+b*dimY+c]
		return uint64(((v % int64(p)) + int64(p)) % int64(p))
	}
	for a1 := 0; a1 < dimW; a1++ {
		for a2 := 0; a2 < dimW; a2++ {
			if a1 == a2 {
				continue
			}
			for pp := 0; pp < nP; pp++ {
				sg := wedgeSign(a1, a2, pmask[pp])
				if sg == 0 {
					continue
				}
				rmask := pmask[pp] | (uint64(1) << uint(a1)) | (uint64(1) << uint(a2))
				rPos := idxR[rmask]
				for b1 := 0; b1 < dimX; b1++ {
					for c1 := 0; c1 < dimY; c1++ {
						t1 := T(a1, b1, c1)
						if t1 == 0 {
							continue
						}
						for b2 := 0; b2 < dimX; b2++ {
							for c2 := 0; c2 < dimY; c2++ {
								t2 := T(a2, b2, c2)
								if t2 == 0 {
									continue
								}
								rp, cp := passengerIndex(spec, b1, c1, b2, c2, dimX, dimY)
								row := rPos*dimX*dimY + rp
								col := pp*dimX*dimY + cp
								v := (t1 * t2) % p
								if sg < 0 {
									if M[row][col] >= v {
										M[row][col] -= v
									} else {
										M[row][col] = p - (v - M[row][col])
									}
								} else {
									M[row][col] = (M[row][col] + v) % p
								}
							}
						}
					}
				}
			}
		}
	}
	return M
}

// combosCount returns a slice of length C(d,p) (cheap dimension helper).
func combosCount(d, p int) []struct{} {
	return make([]struct{}, int(binom(d, p)))
}
