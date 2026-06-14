package main

// The standard 3-dim irrep rho of S_4 and its subgroups, following GM
// 1612.01527 sec 4.1. Group elements are tracked as permutations of {0,1,2,3}
// (0-indexed images), and rho(g) is the corresponding signed-permutation /
// tetrahedron matrix. The whole group is enumerated by BFS from generators.

// perm is a permutation of {0,1,2,3}, stored as images: perm[i] = g(i).
type perm [4]int

// composePerm returns p∘q (apply q first): (p∘q)(i) = p(q(i)).
func composePerm(p, q perm) perm {
	var r perm
	for i := 0; i < 4; i++ {
		r[i] = p[q[i]]
	}
	return r
}

var identPerm = perm{0, 1, 2, 3}

// Group bundles the enumerated elements of S_4 with their rho-matrices.
type Group struct {
	elems  []perm       // all 24 permutations, in BFS order
	rho    map[perm]Mat // rho(g) for each element
	sigma  Mat          // rho((123))
	sigmaP perm         // (123) as a permutation
}

// generatorMats returns the GM signed-permutation generators for rho on
// (12),(23),(34), plus sigma = rho((123)). The permutations are 0-indexed:
// (12)->swap 0,1; (23)->swap 1,2; (34)->swap 2,3; (123)->0->1->2->0.
func generatorMats() (map[perm]Mat, perm, Mat) {
	g12 := matFromInts([n][n]int64{{0, 1, 0}, {1, 0, 0}, {0, 0, 1}})
	g23 := matFromInts([n][n]int64{{1, 0, 0}, {0, 0, 1}, {0, 1, 0}})
	g34 := matFromInts([n][n]int64{{0, -1, 0}, {-1, 0, 0}, {0, 0, 1}})
	sigma := matFromInts([n][n]int64{{0, 0, 1}, {1, 0, 0}, {0, 1, 0}}) // rho((123))

	p12 := perm{1, 0, 2, 3}
	p23 := perm{0, 2, 1, 3}
	p34 := perm{0, 1, 3, 2}
	p123 := perm{1, 2, 0, 3} // 0->1,1->2,2->0,3->3

	gens := map[perm]Mat{p12: g12, p23: g23, p34: g34}
	return gens, p123, sigma
}

// buildGroup enumerates S_4 via BFS, multiplying rho-matrices alongside the
// permutations so rho is correct by construction (homomorphism property is
// then verified in a unit test).
func buildGroup() *Group {
	gens, p123, sigma := generatorMats()

	rho := map[perm]Mat{identPerm: identMat()}
	elems := []perm{identPerm}
	frontier := []perm{identPerm}
	genPerms := make([]perm, 0, len(gens))
	for gp := range gens {
		genPerms = append(genPerms, gp)
	}
	for len(frontier) > 0 {
		var next []perm
		for _, e := range frontier {
			for _, gp := range genPerms {
				ne := composePerm(gp, e)
				if _, seen := rho[ne]; !seen {
					rho[ne] = matMulQ3(gens[gp], rho[e])
					elems = append(elems, ne)
					next = append(next, ne)
				}
			}
		}
		frontier = next
	}
	return &Group{elems: elems, rho: rho, sigma: sigma, sigmaP: p123}
}

// subgroup BFS-closes the given generator permutations into a subgroup (list of
// permutations). Used to define stabilizers H for the orbit seeds.
func (G *Group) subgroup(gens []perm) []perm {
	seen := map[perm]bool{identPerm: true}
	out := []perm{identPerm}
	frontier := []perm{identPerm}
	for len(frontier) > 0 {
		var next []perm
		for _, e := range frontier {
			for _, gp := range gens {
				ne := composePerm(gp, e)
				if !seen[ne] {
					seen[ne] = true
					out = append(out, ne)
					next = append(next, ne)
				}
			}
		}
		frontier = next
	}
	return out
}

// Named subgroup generators (0-indexed permutations), matching the Sage
// foundations check (Or2 provenance note). Orbit size = 24 / |H|.
var (
	genS3  = []perm{{0, 2, 1, 3}, {0, 1, 3, 2}} // <(23),(34)>: fixes 0, order 6, orbit 4
	genK4  = []perm{{1, 0, 3, 2}, {2, 3, 0, 1}} // <(12)(34),(13)(24)>: order 4, orbit 6
	genZ3  = []perm{{1, 2, 0, 3}}               // <(123)>: order 3, orbit 8
	genZ2t = []perm{{1, 0, 2, 3}}               // <(12)>: order 2, orbit 12 (transposition type)
	genZ2d = []perm{{1, 0, 3, 2}}               // <(12)(34)>: order 2, orbit 12 (double-transposition type)
	genZ4  = []perm{{1, 2, 3, 0}}               // <(1234)>: order 4, orbit 6
	genD4  = []perm{{1, 2, 3, 0}, {2, 1, 0, 3}} // <(1234),(13)>: order 8, orbit 3
	genA4  = []perm{{1, 2, 0, 3}, {1, 0, 3, 2}} // <(123),(12)(34)>: order 12, orbit 2
)
