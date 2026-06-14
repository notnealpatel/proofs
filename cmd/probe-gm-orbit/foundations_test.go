package main

import "testing"

// TestGroupHomomorphism checks rho(g)rho(h) = rho(gh) over all pairs, i.e. the
// BFS-built rho is a genuine representation.
func TestGroupHomomorphism(t *testing.T) {
	G := buildGroup()
	if len(G.elems) != 24 {
		t.Fatalf("group order = %d, want 24", len(G.elems))
	}
	for _, g := range G.elems {
		for _, h := range G.elems {
			lhs := matMulQ3(G.rho[g], G.rho[h])
			rhs := G.rho[composePerm(g, h)]
			if !equalMat(lhs, rhs) {
				t.Fatalf("homomorphism fails at g=%v h=%v", g, h)
			}
		}
	}
}

// TestSigmaIsOrder3 checks sigma = rho((123)) has order 3 and matches the
// permutation (123).
func TestSigmaIsOrder3(t *testing.T) {
	G := buildGroup()
	if !equalMat(G.sigma, G.rho[G.sigmaP]) {
		t.Fatalf("sigma matrix != rho(sigmaP)")
	}
	s3 := matMulQ3(matMulQ3(G.sigma, G.sigma), G.sigma)
	if !equalMat(s3, identMat()) {
		t.Fatalf("sigma^3 != I")
	}
	if equalMat(G.sigma, identMat()) {
		t.Fatalf("sigma == I, expected order 3")
	}
}

// TestFixedDims reproduces the Sage foundations check (Or1 sec 3): dimensions of
// H-fixed subspaces of M_3 under rho⊗rho* conjugation.
func TestFixedDims(t *testing.T) {
	G := buildGroup()
	cases := []struct {
		name    string
		gens    []perm
		wantOrd int
		wantDim int
	}{
		{"S_3", genS3, 6, 2},
		{"K_4", genK4, 4, 3},
		{"Z_3", genZ3, 3, 3},
		{"Z_2t", genZ2t, 2, 5},
		{"Z_2d", genZ2d, 2, 5},
		{"Z_4", genZ4, 4, 3},
		{"D_4", genD4, 8, 2},
		{"A_4", genA4, 12, 1},
	}
	for _, c := range cases {
		H := G.subgroup(c.gens)
		if len(H) != c.wantOrd {
			t.Errorf("%s: |H| = %d, want %d", c.name, len(H), c.wantOrd)
		}
		basis := fixedBasis(G, H)
		if len(basis) != c.wantDim {
			t.Errorf("%s: fixed dim = %d, want %d", c.name, len(basis), c.wantDim)
		}
		// every basis matrix must actually be fixed by all of H
		for _, h := range H {
			for _, b := range basis {
				if !equalMat(conj(G.rho[h], b), b) {
					t.Errorf("%s: basis matrix not fixed by h=%v", c.name, h)
				}
			}
		}
	}
}
