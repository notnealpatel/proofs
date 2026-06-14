package main

import (
	"math/rand"
	"testing"
)

// mmDense builds M_n as a dense tensor (wedge leg first via leg index).
func mmDense(n, legW int) []int64 { return mnDenseLeg(n, legW) }

// TestWedgeSign sanity-checks the exterior sign function.
func TestWedgeSign(t *testing.T) {
	cases := []struct {
		a1, a2 int
		pmask  uint64
		want   int
	}{
		{0, 1, 0, 1},
		{1, 0, 0, -1},
		{0, 0, 0, 0},
		{0, 1, 1 << 0, 0}, // a1 in P
	}
	for _, c := range cases {
		if got := wedgeSign(c.a1, c.a2, c.pmask); got != c.want {
			t.Errorf("wedgeSign(%d,%d,%b)=%d want %d", c.a1, c.a2, c.pmask, got, c.want)
		}
	}
}

// TestRank1Zero: a rank-1 tensor has q(q-1)=0, so its flattening rank is 0.
func TestRank1Zero(t *testing.T) {
	rng := rand.New(rand.NewSource(7))
	dW := 9
	dense := randRankQDense(dW, dW, dW, 1, rng)
	for _, spec := range []flatSpec{specMixed, specByLeg} {
		M := buildFlatteningModP(dW, dW, dW, dense, 3, spec)
		if rk := rankModPU(M); rk != 0 {
			t.Errorf("spec=%s rank-1 flattening rank=%d want 0", spec, rk)
		}
	}
}

// TestRankQBound: random rank-q tensors obey rank <= q(q-1)*C(dW-2,d').
func TestRankQBound(t *testing.T) {
	rng := rand.New(rand.NewSource(11))
	dW, dPrime := 9, 3
	cost := int(binom(dW-2, dPrime))
	for _, q := range []int{2, 3, 5} {
		dense := randRankQDense(dW, dW, dW, q, rng)
		for _, spec := range []flatSpec{specMixed, specByLeg} {
			M := buildFlatteningModP(dW, dW, dW, dense, dPrime, spec)
			rk := rankModPU(M)
			if rk > q*(q-1)*cost {
				t.Errorf("spec=%s q=%d rank=%d exceeds bound %d", spec, q, rk, q*(q-1)*cost)
			}
		}
	}
}

// TestProp36UnitAnchor: DM Prop 3.6 -- the unit tensor of rank q=dW achieves
// rank exactly q(q-1)*C(q-2,d') under the mixed (and byleg) flattening. This
// is the load-bearing correctness anchor.
func TestProp36UnitAnchor(t *testing.T) {
	dW, dPrime := 9, 3
	q := dW
	dense := unitDense(dW, q)
	want := q * (q - 1) * int(binom(q-2, dPrime))
	for _, spec := range []flatSpec{specMixed, specByLeg} {
		M := buildFlatteningModP(dW, dW, dW, dense, dPrime, spec)
		if rk := rankModPU(M); rk != want {
			t.Errorf("spec=%s unit q=%d rank=%d, DM Prop 3.6 achieving=%d", spec, q, rk, want)
		}
	}
}

// TestM2Tangency64: DM Prop 5.1 -- the tangency (mixed) flattening of M_2
// (n=2, ambient C^4, d'=1) has rank exactly 64. This is the literature anchor
// that pins the correct passenger split.
func TestM2Tangency64(t *testing.T) {
	n := 2
	dW := n * n
	dense := mmDense(n, 0)
	M := buildFlatteningModP(dW, dW, dW, dense, 1, specMixed)
	if rk := rankModPU(M); rk != 64 {
		t.Fatalf("M_2 tangency (mixed) rank=%d, want 64 (DM Prop 5.1)", rk)
	}
}

// TestM3LegSymmetry: the three cyclic leg choices of M_3 give equal rank.
func TestM3LegSymmetry(t *testing.T) {
	n := 3
	dW := n * n
	for _, spec := range []flatSpec{specMixed, specByLeg} {
		var ranks [3]int
		for leg := 0; leg < 3; leg++ {
			M := buildFlatteningModP(dW, dW, dW, mmDense(n, leg), 3, spec)
			ranks[leg] = rankModPU(M)
		}
		if ranks[0] != ranks[1] || ranks[1] != ranks[2] {
			t.Errorf("spec=%s M_3 leg ranks disagree: %v", spec, ranks)
		}
	}
}

// TestM3HeadlineRanks records the M_3 d'=3 ranks (mixed and byleg).
func TestM3HeadlineRanks(t *testing.T) {
	n := 3
	dW := n * n
	dense := mmDense(n, 0)
	for _, spec := range []flatSpec{specMixed, specByLeg} {
		M := buildFlatteningModP(dW, dW, dW, dense, 3, spec)
		rk := rankModPU(M)
		t.Logf("M_3 d'=3 spec=%s: %dx%d rank=%d R-bar>=%d", spec, len(M), len(M[0]), rk, bestRBound(rk))
	}
}

// TestCubeRoot: zeta^3=1, zeta!=1.
func TestCubeRoot(t *testing.T) {
	z := cubeRootOfUnity()
	if z == 0 || z == 1 || mulModP(z, mulModP(z, z)) != 1 {
		t.Fatalf("bad cube root of unity: %d", z)
	}
}
