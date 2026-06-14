package main

import (
	"math/big"
	"math/rand"
	"testing"
)

// TestSymbolicMatchesConcrete checks that the symbolic Stage-1 constraint
// polynomial for each basis triple, evaluated at arbitrary seed parameter
// values, equals the concrete reconstruction residual
// <T_ansatz, A⊗B⊗C> - tr(ABC). This certifies that the Stage-1 builder encodes
// exactly the decomposition condition that verifyDecomposition checks.
func TestSymbolicMatchesConcrete(t *testing.T) {
	G := buildGroup()
	basisRR := rrStarBasis()
	cat := orbitCatalog()
	var t1, t2 orbitTemplate
	for _, o := range cat {
		if o.name == "S_3" {
			t1 = o
		}
		if o.name == "Z_3" {
			t2 = o
		}
	}

	fb1 := fixedBasis(G, G.subgroup(t1.gens))
	fb2 := fixedBasis(G, G.subgroup(t2.gens))
	nvars := len(fb1) + len(fb2)

	// Symbolic seeds and their conjugates, mirroring buildPairSystem.
	seedsSym := [][3]PolyMat{
		orbitSeedTriple(G.sigma, fb1, 0),
		orbitSeedTriple(G.sigma, fb2, len(fb1)),
	}
	gConj := make([][][3]PolyMat, 2)
	for k := 0; k < 2; k++ {
		gConj[k] = make([][3]PolyMat, len(G.elems))
		for gi, g := range G.elems {
			for f := 0; f < 3; f++ {
				gConj[k][gi][f] = conjPoly(G.rho[g], seedsSym[k][f])
			}
		}
	}
	triplePoly := func(A, B, C Mat) *Poly {
		P := constPoly(trace(A).Mul(trace(B)).Mul(trace(C)).Sub(trProd(A, B, C)))
		for k := 0; k < 2; k++ {
			for gi := range G.elems {
				la := frobPoly(A, gConj[k][gi][0])
				lb := frobPoly(B, gConj[k][gi][1])
				lc := frobPoly(C, gConj[k][gi][2])
				P = addPoly(P, mulPoly(mulPoly(la, lb), lc))
			}
		}
		return P
	}

	rng := rand.New(rand.NewSource(7))
	randQ3 := func() Q3 {
		return q3(big.NewRat(int64(rng.Intn(7)-3), int64(rng.Intn(3)+1)),
			big.NewRat(int64(rng.Intn(5)-2), int64(rng.Intn(3)+1)))
	}
	for trial := 0; trial < 4; trial++ {
		vals := make([]Q3, nvars)
		for i := range vals {
			vals[i] = randQ3()
		}
		m1 := seedFromParams(fb1, vals, 0)
		m2 := seedFromParams(fb2, vals, len(fb1))
		seeds := []Mat{m1, m2}
		for ai := range basisRR {
			for bi := range basisRR {
				for ci := range basisRR {
					concrete := ansatzInner(G, seeds, basisRR[ai], basisRR[bi], basisRR[ci]).
						Sub(trProd(basisRR[ai], basisRR[bi], basisRR[ci]))
					symb := evalPoly(triplePoly(basisRR[ai], basisRR[bi], basisRR[ci]), vals)
					if !symb.Equal(concrete) {
						t.Fatalf("trial %d triple (%d,%d,%d): symbolic %s != concrete %s",
							trial, ai, bi, ci, symb.String(), concrete.String())
					}
				}
			}
		}
	}
}
