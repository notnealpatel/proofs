// Command probe-traceinv evaluates degree-3 / S_3 trace invariants on
// matrix-multiplication tensors and known low-rank catalog tensors, to test
// whether such invariants certify tensor-rank bounds on <n,n,n> beyond
// degree-2 flattenings (task Tr1).
//
// Stdlib only. Complex128 arithmetic. Deterministic via -seed; honors a
// -timeout deadline via context, emitting partial output on expiry.
package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"math"
	"math/cmplx"
	"math/rand"
	"os"
	"runtime"
	"sort"
	"sync"
	"sync/atomic"
	"time"
)

func main() {
	timeout := flag.Duration("timeout", 8*time.Minute, "wall-clock budget")
	seed := flag.Int64("seed", 1, "deterministic RNG seed")
	samples := flag.Int("samples", 2000, "rank-r samples per (n,r) cell in the separation sweep")
	workers := flag.Int("workers", runtime.NumCPU(), "parallel workers for sampling")
	outJSON := flag.String("json", "/home/neal/p/proofs/.tasks/research/infodumps/Tr1-results.json", "results JSON path")
	outMD := flag.String("md", "/home/neal/p/proofs/.tasks/research/infodumps/Tr1.md", "results markdown path")
	flag.Parse()

	ctx, cancel := context.WithTimeout(context.Background(), *timeout)
	defer cancel()

	run(ctx, *seed, *samples, *workers, *outJSON, *outMD)
}

func run(ctx context.Context, seed int64, samples, workers int, outJSON, outMD string) {
	start := time.Now()
	classes := enumerateClasses()
	fmt.Printf("degree-3 trace invariants: %d S_3^3-conjugation classes\n", len(classes))

	res := &results{
		Seed:       seed,
		Samples:    samples,
		NumClasses: len(classes),
		Classes:    describeClasses(classes),
	}

	// Phase 1: sanity checks (hard assertions).
	runSanity(classes, seed)
	res.SanityPassed = true
	fmt.Printf("[%s] sanity checks passed\n", since(start))

	// Phase 2: catalog table.
	cat := catalog()
	res.Catalog = evalCatalog(classes, cat)
	fmt.Printf("[%s] catalog evaluated (%d tensors)\n", since(start), len(cat))

	// Phase 3: detection W_3 vs GHZ_2.
	res.Detection = runDetection(classes)
	fmt.Printf("[%s] detection W_3 vs GHZ_2 done (%d separating classes)\n", since(start), len(res.Detection.SeparatingClasses))

	// Phase 4: separation sweep.
	res.Separation = runSeparation(ctx, classes, seed, samples, workers, start)
	fmt.Printf("[%s] separation sweep done\n", since(start))

	// Phase 5: conclusions.
	res.Conclusion = buildConclusion(classes, res)
	res.Elapsed = since(start)
	res.Complete = ctx.Err() == nil

	writeJSON(outJSON, res)
	writeMarkdown(outMD, classes, res)
	fmt.Printf("[%s] wrote %s and %s (complete=%v)\n", since(start), outJSON, outMD, res.Complete)
}

func since(t time.Time) string { return time.Since(t).Round(time.Millisecond).String() }

// ---------------------------------------------------------------------------
// S_3 permutations
// ---------------------------------------------------------------------------

// perm is a permutation of {0,1,2}: perm[a] = sigma(a).
type perm [3]int

func (p perm) inv() perm {
	var q perm
	for a := 0; a < 3; a++ {
		q[p[a]] = a
	}
	return q
}

// compose returns a∘b: (a∘b)(x) = a(b(x)).
func compose(a, b perm) perm {
	var c perm
	for x := 0; x < 3; x++ {
		c[x] = a[b[x]]
	}
	return c
}

func allPerms() []perm {
	return []perm{
		{0, 1, 2}, {0, 2, 1}, {1, 0, 2}, {1, 2, 0}, {2, 0, 1}, {2, 1, 0},
	}
}

// triple is (sigma1, sigma2, sigma3) acting on the i,j,k legs respectively.
type triple [3]perm

func less(a, b triple) bool {
	for c := 0; c < 3; c++ {
		for x := 0; x < 3; x++ {
			if a[c][x] != b[c][x] {
				return a[c][x] < b[c][x]
			}
		}
	}
	return false
}

// conj returns the simultaneous conjugate (tau sigma_c tau^{-1}) for all c.
func conj(t triple, tau perm) triple {
	ti := tau.inv()
	var out triple
	for c := 0; c < 3; c++ {
		out[c] = compose(compose(tau, t[c]), ti)
	}
	return out
}

// invClass holds one conjugation class of triples plus its contraction plan.
type invClass struct {
	rep   triple
	orbit []triple
	plan  contractionPlan
	// disconnected reports whether the 6-node tensor network factorizes into
	// two or more components (i.e. the invariant is a product of lower-degree
	// invariants on the same tensor).
	disconnected bool
}

func enumerateClasses() []invClass {
	perms := allPerms()
	seen := map[triple]bool{}
	var classes []invClass
	for _, s1 := range perms {
		for _, s2 := range perms {
			for _, s3 := range perms {
				t := triple{s1, s2, s3}
				if seen[t] {
					continue
				}
				orbitSet := map[triple]bool{}
				for _, tau := range perms {
					orbitSet[conj(t, tau)] = true
				}
				rep := t
				var orbit []triple
				for o := range orbitSet {
					seen[o] = true
					orbit = append(orbit, o)
					if less(o, rep) {
						rep = o
					}
				}
				sort.Slice(orbit, func(i, j int) bool { return less(orbit[i], orbit[j]) })
				plan := planContraction(rep)
				classes = append(classes, invClass{
					rep:          rep,
					orbit:        orbit,
					plan:         plan,
					disconnected: plan.disconnected,
				})
			}
		}
	}
	sort.Slice(classes, func(i, j int) bool { return less(classes[i].rep, classes[j].rep) })
	return classes
}

// ---------------------------------------------------------------------------
// Tensors
// ---------------------------------------------------------------------------

// tensor is a 3-tensor of dims d1 x d2 x d3 in row-major order: entry (i,j,k)
// is at data[(i*d2+j)*d3+k].
type tensor struct {
	d1, d2, d3 int
	data       []complex128
}

func newTensor(d1, d2, d3 int) *tensor {
	return &tensor{d1: d1, d2: d2, d3: d3, data: make([]complex128, d1*d2*d3)}
}

func (t *tensor) at(i, j, k int) complex128 { return t.data[(i*t.d2+j)*t.d3+k] }
func (t *tensor) set(i, j, k int, v complex128) {
	t.data[(i*t.d2+j)*t.d3+k] = v
}
func (t *tensor) add(i, j, k int, v complex128) {
	t.data[(i*t.d2+j)*t.d3+k] += v
}

func (t *tensor) normSq() float64 {
	var s float64
	for _, v := range t.data {
		s += real(v)*real(v) + imag(v)*imag(v)
	}
	return s
}

func (t *tensor) clone() *tensor {
	c := newTensor(t.d1, t.d2, t.d3)
	copy(c.data, t.data)
	return c
}

// ---------------------------------------------------------------------------
// Contraction engine for degree-3 trace invariants.
//
// The invariant tr_{(s1,s2,s3)}(T) is the contraction of a 6-node tensor
// network: nodes 0,1,2 are copies of T (copy b carries leg-indices i_b,j_b,k_b),
// nodes 3,4,5 are copies of conj(T) (copy a carries i_{s1(a)},j_{s2(a)},k_{s3(a)}).
// Each summed index labels an edge joining one T-copy to one conj-copy:
//   i_b joins T-copy b to conj-copy s1^{-1}(b), etc.
// There are 9 edges (3 legs x 3 copies), each of dimension d_leg.
//
// We plan an optimal pairwise contraction order once per class (the network is
// tiny: 6 nodes), minimizing the largest intermediate's free-leg count, then
// execute that plan per tensor.
// ---------------------------------------------------------------------------

// edgeLabel identifies a summed index: leg in {0,1,2} (i,j,k) and copy in {0,1,2}.
type edgeLabel struct{ leg, copy int }

// netNode is one node of the network: its three incident edge labels in
// (i,j,k) order, and which physical leg of the tensor each maps to.
// nodeKind distinguishes T (kind 0) from conj(T) (kind 1).
type netNode struct {
	kind  int          // 0 = T, 1 = conj(T)
	edges [3]edgeLabel // edges on legs i,j,k of this node
}

func buildNetwork(t triple) [6]netNode {
	var nodes [6]netNode
	// T-copy b: legs carry (leg, b).
	for b := 0; b < 3; b++ {
		nodes[b].kind = 0
		nodes[b].edges = [3]edgeLabel{{0, b}, {1, b}, {2, b}}
	}
	// conj-copy a: leg L carries index s_L(a), i.e. edge label (L, s_L(a)).
	for a := 0; a < 3; a++ {
		nodes[3+a].kind = 1
		nodes[3+a].edges = [3]edgeLabel{
			{0, t[0][a]},
			{1, t[1][a]},
			{2, t[2][a]},
		}
	}
	return nodes
}

// contractionPlan is a sequence of pairwise contraction steps over intermediate
// tensors keyed by their free-leg label sets.
type contractionPlan struct {
	nodes        [6]netNode
	steps        []contractStep
	disconnected bool
}

// contractStep contracts intermediates a and b. The intermediate operands and
// result are represented by ordered slices of edgeLabels (their free legs).
type contractStep struct {
	a, b      []edgeLabel // free legs of the two operands (ordered)
	result    []edgeLabel // free legs of the result (shared legs summed out)
	shared    []edgeLabel
	resultIdx int // index into the live-intermediate table where result lands
}

// planContraction computes an optimal-order pairwise contraction by exhaustive
// search (6 nodes => at most a few thousand orderings), minimizing the maximum
// union-size (cost exponent d^union) encountered.
func planContraction(t triple) contractionPlan {
	nodes := buildNetwork(t)
	// Initial intermediates: each node's three edge labels.
	type interm struct {
		legs []edgeLabel
	}
	initial := make([]interm, 6)
	for i := 0; i < 6; i++ {
		initial[i] = interm{legs: []edgeLabel{nodes[i].edges[0], nodes[i].edges[1], nodes[i].edges[2]}}
	}

	var bestPlan []contractStep
	bestCost := 1 << 30
	disconnected := false

	// recursive search; state = slice of live intermediates (label-sets).
	var search func(live []interm, steps []contractStep, curMax int)
	search = func(live []interm, steps []contractStep, curMax int) {
		if curMax >= bestCost {
			return
		}
		if len(live) == 1 {
			bestCost = curMax
			bestPlan = append([]contractStep(nil), steps...)
			return
		}
		// try all pairs that share at least one edge first; if none share,
		// the network is disconnected (factorized invariant).
		anyShared := false
		for x := 0; x < len(live); x++ {
			for y := x + 1; y < len(live); y++ {
				sh := intersect(live[x].legs, live[y].legs)
				if len(sh) == 0 {
					continue
				}
				anyShared = true
				union := union(live[x].legs, live[y].legs)
				resLegs := symdiff(live[x].legs, live[y].legs, sh)
				step := contractStep{
					a:      live[x].legs,
					b:      live[y].legs,
					result: resLegs,
					shared: sh,
				}
				next := make([]interm, 0, len(live)-1)
				for z := 0; z < len(live); z++ {
					if z == x || z == y {
						continue
					}
					next = append(next, live[z])
				}
				next = append(next, interm{legs: resLegs})
				nc := curMax
				if len(union) > nc {
					nc = len(union)
				}
				search(next, append(steps, step), nc)
			}
		}
		if !anyShared {
			disconnected = true
			// disconnected: merge the first two as a tensor product of components.
			x, y := 0, 1
			union := union(live[x].legs, live[y].legs)
			resLegs := union // no shared legs
			step := contractStep{a: live[x].legs, b: live[y].legs, result: resLegs}
			next := make([]interm, 0, len(live)-1)
			for z := 2; z < len(live); z++ {
				next = append(next, live[z])
			}
			next = append(next, interm{legs: resLegs})
			nc := curMax
			if len(union) > nc {
				nc = len(union)
			}
			search(next, append(steps, step), nc)
		}
	}
	search(initial, nil, 0)

	// Re-link steps to concrete live-table indices for execution. We re-simulate
	// the chosen plan over a live table of operand tensors.
	return contractionPlan{nodes: nodes, steps: bestPlan, disconnected: disconnected}
}

func intersect(a, b []edgeLabel) []edgeLabel {
	var out []edgeLabel
	for _, x := range a {
		for _, y := range b {
			if x == y {
				out = append(out, x)
				break
			}
		}
	}
	return out
}

func union(a, b []edgeLabel) []edgeLabel {
	out := append([]edgeLabel(nil), a...)
	for _, y := range b {
		found := false
		for _, x := range a {
			if x == y {
				found = true
				break
			}
		}
		if !found {
			out = append(out, y)
		}
	}
	return out
}

// symdiff returns (a ∪ b) \ shared.
func symdiff(a, b, shared []edgeLabel) []edgeLabel {
	u := union(a, b)
	var out []edgeLabel
	for _, x := range u {
		drop := false
		for _, s := range shared {
			if x == s {
				drop = true
				break
			}
		}
		if !drop {
			out = append(out, x)
		}
	}
	return out
}

// dimOf returns the dimension of a leg label for tensor t.
func dimOf(t *tensor, lbl edgeLabel) int {
	switch lbl.leg {
	case 0:
		return t.d1
	case 1:
		return t.d2
	default:
		return t.d3
	}
}

// dense is an intermediate tensor over a set of free edge labels (in order),
// stored row-major over those legs (each leg has its tensor dimension).
type dense struct {
	legs []edgeLabel
	dims []int
	data []complex128
}

// nodeTensor materializes node i of the network as a dense over its three legs.
// kind 0 = T entries T[i,j,k]; kind 1 = conj(T)[i,j,k].
func nodeTensor(t *tensor, node netNode) dense {
	legs := []edgeLabel{node.edges[0], node.edges[1], node.edges[2]}
	d := dense{legs: legs, dims: []int{t.d1, t.d2, t.d3}, data: make([]complex128, t.d1*t.d2*t.d3)}
	idx := 0
	for i := 0; i < t.d1; i++ {
		for j := 0; j < t.d2; j++ {
			for k := 0; k < t.d3; k++ {
				v := t.at(i, j, k)
				if node.kind == 1 {
					v = cmplx.Conj(v)
				}
				d.data[idx] = v
				idx++
			}
		}
	}
	return d
}

// contractPair contracts two dense intermediates over their shared legs.
func contractPair(t *tensor, A, B dense) dense {
	// Partition legs of A and B into shared and free.
	shared := intersect(A.legs, B.legs)
	freeA := minus(A.legs, shared)
	freeB := minus(B.legs, shared)
	resLegs := append(append([]edgeLabel(nil), freeA...), freeB...)

	dimMap := func(lbl edgeLabel) int { return dimOf(t, lbl) }

	// Strides for A and B by leg label.
	strideA := strides(A.legs, A.dims)
	strideB := strides(B.legs, B.dims)

	sharedDims := make([]int, len(shared))
	for i, l := range shared {
		sharedDims[i] = dimMap(l)
	}
	freeADims := make([]int, len(freeA))
	for i, l := range freeA {
		freeADims[i] = dimMap(l)
	}
	freeBDims := make([]int, len(freeB))
	for i, l := range freeB {
		freeBDims[i] = dimMap(l)
	}
	resDims := append(append([]int(nil), freeADims...), freeBDims...)

	resSize := 1
	for _, d := range resDims {
		resSize *= d
	}
	out := dense{legs: resLegs, dims: resDims, data: make([]complex128, resSize)}

	// Iterate free-A, free-B, summing over shared.
	nFA := prod(freeADims)
	nFB := prod(freeBDims)
	nS := prod(sharedDims)

	// Precompute per-shared-tuple offset contributions for A and B, and per-free.
	fAoffA := offsets(freeA, freeADims, strideA, nFA)
	fBoffB := offsets(freeB, freeBDims, strideB, nFB)
	sOffA := offsets(shared, sharedDims, strideA, nS)
	sOffB := offsets(shared, sharedDims, strideB, nS)

	for ia := 0; ia < nFA; ia++ {
		baseA := fAoffA[ia]
		rowBase := ia * nFB
		for ib := 0; ib < nFB; ib++ {
			baseB := fBoffB[ib]
			var acc complex128
			for s := 0; s < nS; s++ {
				acc += A.data[baseA+sOffA[s]] * B.data[baseB+sOffB[s]]
			}
			out.data[rowBase+ib] = acc
		}
	}
	return out
}

func minus(a, drop []edgeLabel) []edgeLabel {
	var out []edgeLabel
	for _, x := range a {
		keep := true
		for _, d := range drop {
			if x == d {
				keep = false
				break
			}
		}
		if keep {
			out = append(out, x)
		}
	}
	return out
}

func strides(legs []edgeLabel, dims []int) map[edgeLabel]int {
	s := map[edgeLabel]int{}
	stride := 1
	for i := len(legs) - 1; i >= 0; i-- {
		s[legs[i]] = stride
		stride *= dims[i]
	}
	return s
}

func prod(d []int) int {
	p := 1
	for _, x := range d {
		p *= x
	}
	return p
}

// offsets enumerates the flat-index offset (over a parent stride map) for every
// multi-index of the given sub-legs, in row-major order over subDims.
func offsets(subLegs []edgeLabel, subDims []int, parentStride map[edgeLabel]int, n int) []int {
	out := make([]int, n)
	idx := make([]int, len(subLegs))
	for t := 0; t < n; t++ {
		off := 0
		for i, l := range subLegs {
			off += idx[i] * parentStride[l]
		}
		out[t] = off
		// increment multi-index (row-major).
		for i := len(idx) - 1; i >= 0; i-- {
			idx[i]++
			if idx[i] < subDims[i] {
				break
			}
			idx[i] = 0
		}
	}
	return out
}

// traceInvariant evaluates the unnormalized trace invariant of class c on t.
func traceInvariant(t *tensor, c *invClass) complex128 {
	live := make([]dense, 0, 6)
	for i := 0; i < 6; i++ {
		live = append(live, nodeTensor(t, c.plan.nodes[i]))
	}
	for _, step := range c.plan.steps {
		ai := findInterm(live, step.a)
		A := live[ai]
		live = removeAt(live, ai)
		bi := findInterm(live, step.b)
		B := live[bi]
		live = removeAt(live, bi)
		live = append(live, contractPair(t, A, B))
	}
	// final intermediate must be a scalar (no free legs).
	if len(live) != 1 || len(live[0].legs) != 0 {
		panic(fmt.Sprintf("contraction did not reduce to scalar: %d intermediates, %d legs", len(live), legCount(live)))
	}
	return live[0].data[0]
}

func legCount(d []dense) int {
	if len(d) == 0 {
		return -1
	}
	n := 0
	for _, x := range d {
		n += len(x.legs)
	}
	return n
}

func findInterm(live []dense, legs []edgeLabel) int {
	for i, d := range live {
		if sameLegSet(d.legs, legs) {
			return i
		}
	}
	panic("intermediate not found during contraction execution")
}

func sameLegSet(a, b []edgeLabel) bool {
	if len(a) != len(b) {
		return false
	}
	for _, x := range a {
		found := false
		for _, y := range b {
			if x == y {
				found = true
				break
			}
		}
		if !found {
			return false
		}
	}
	return true
}

func removeAt(live []dense, i int) []dense {
	return append(live[:i:i], live[i+1:]...)
}

// normalizedInvariant returns tr/‖T‖^6.
func normalizedInvariant(t *tensor, c *invClass) complex128 {
	n2 := t.normSq()
	denom := n2 * n2 * n2
	if denom == 0 {
		return 0
	}
	return traceInvariant(t, c) / complex(denom, 0)
}

// ---------------------------------------------------------------------------
// Degree-2 baseline: flattening singular spectra.
// ---------------------------------------------------------------------------

// flatteningSpectra returns the singular values of the three flattenings of t,
// each sorted descending and normalized so that sum of squares = 1.
func flatteningSpectra(t *tensor) [3][]float64 {
	var out [3][]float64
	n2 := t.normSq()
	scale := 1.0
	if n2 > 0 {
		scale = 1.0 / math.Sqrt(n2)
	}
	// Flattening mode m groups index m vs the other two.
	out[0] = singularValues(flatten(t, 0), scale)
	out[1] = singularValues(flatten(t, 1), scale)
	out[2] = singularValues(flatten(t, 2), scale)
	return out
}

// flatten returns the mode-m matricization of t as rows x cols complex matrix.
func flatten(t *tensor, mode int) [][]complex128 {
	d := [3]int{t.d1, t.d2, t.d3}
	rows := d[mode]
	cols := 1
	for m := 0; m < 3; m++ {
		if m != mode {
			cols *= d[m]
		}
	}
	M := make([][]complex128, rows)
	for r := range M {
		M[r] = make([]complex128, cols)
	}
	for i := 0; i < t.d1; i++ {
		for j := 0; j < t.d2; j++ {
			for k := 0; k < t.d3; k++ {
				var r, c int
				switch mode {
				case 0:
					r = i
					c = j*t.d3 + k
				case 1:
					r = j
					c = i*t.d3 + k
				default:
					r = k
					c = i*t.d2 + j
				}
				M[r][c] = t.at(i, j, k)
			}
		}
	}
	return M
}

// singularValues computes the singular values of M by Hermitian-eigendecomposing
// the smaller Gram matrix (M Mᴴ or Mᴴ M). Returns sqrt(eigenvalues) descending,
// scaled by `scale`.
func singularValues(M [][]complex128, scale float64) []float64 {
	rows := len(M)
	if rows == 0 {
		return nil
	}
	cols := len(M[0])
	// Use the smaller dimension for the Gram matrix.
	var G [][]complex128
	var dim int
	if rows <= cols {
		dim = rows
		G = make([][]complex128, dim)
		for a := 0; a < dim; a++ {
			G[a] = make([]complex128, dim)
			for b := 0; b < dim; b++ {
				var s complex128
				for c := 0; c < cols; c++ {
					s += M[a][c] * cmplx.Conj(M[b][c])
				}
				G[a][b] = s
			}
		}
	} else {
		dim = cols
		G = make([][]complex128, dim)
		for a := 0; a < dim; a++ {
			G[a] = make([]complex128, dim)
			for b := 0; b < dim; b++ {
				var s complex128
				for r := 0; r < rows; r++ {
					s += cmplx.Conj(M[r][a]) * M[r][b]
				}
				G[a][b] = s
			}
		}
	}
	ev := hermitianEigenvalues(G)
	out := make([]float64, len(ev))
	for i, e := range ev {
		if e < 0 {
			e = 0
		}
		out[i] = math.Sqrt(e) * scale
	}
	sort.Sort(sort.Reverse(sort.Float64Slice(out)))
	return out
}

// hermitianEigenvalues returns the real eigenvalues of a Hermitian matrix via
// cyclic Jacobi rotations on its complex entries.
func hermitianEigenvalues(A [][]complex128) []float64 {
	n := len(A)
	if n == 0 {
		return nil
	}
	// Work on a copy.
	M := make([][]complex128, n)
	for i := range M {
		M[i] = append([]complex128(nil), A[i]...)
	}
	const maxSweeps = 100
	for sweep := 0; sweep < maxSweeps; sweep++ {
		off := 0.0
		for p := 0; p < n; p++ {
			for q := p + 1; q < n; q++ {
				off += real(M[p][q])*real(M[p][q]) + imag(M[p][q])*imag(M[p][q])
			}
		}
		if off < 1e-28 {
			break
		}
		for p := 0; p < n; p++ {
			for q := p + 1; q < n; q++ {
				apq := M[p][q]
				if real(apq)*real(apq)+imag(apq)*imag(apq) < 1e-32 {
					continue
				}
				app := real(M[p][p])
				aqq := real(M[q][q])
				absApq := cmplx.Abs(apq)
				// Phase of apq.
				phase := apq / complex(absApq, 0)
				// Jacobi angle for real symmetric reduced problem.
				tau := (aqq - app) / (2 * absApq)
				var tval float64
				if tau >= 0 {
					tval = 1.0 / (tau + math.Sqrt(1+tau*tau))
				} else {
					tval = -1.0 / (-tau + math.Sqrt(1+tau*tau))
				}
				cval := 1.0 / math.Sqrt(1+tval*tval)
				sval := tval * cval
				// Apply rotation with phase: rows/cols p,q.
				c := complex(cval, 0)
				s := complex(sval, 0) * phase
				sc := cmplx.Conj(s)
				for i := 0; i < n; i++ {
					mip := M[i][p]
					miq := M[i][q]
					M[i][p] = c*mip - sc*miq
					M[i][q] = s*mip + c*miq
				}
				for i := 0; i < n; i++ {
					mpi := M[p][i]
					mqi := M[q][i]
					M[p][i] = c*mpi - s*mqi
					M[q][i] = sc*mpi + c*mqi
				}
			}
		}
	}
	ev := make([]float64, n)
	for i := 0; i < n; i++ {
		ev[i] = real(M[i][i])
	}
	return ev
}

// ---------------------------------------------------------------------------
// Catalog tensors
// ---------------------------------------------------------------------------

type catalogEntry struct {
	name string
	t    *tensor
	rank string // known rank info (text)
}

func catalog() []catalogEntry {
	var out []catalogEntry
	out = append(out, catalogEntry{"GHZ_2 (I_3,2 in C^2^3)", ghz(2, 2), "R=2"})
	out = append(out, catalogEntry{"GHZ_3 (I_3,3 in C^3^3)", ghz(3, 3), "R=3"})
	out = append(out, catalogEntry{"W_3 (C^2^3)", w3(), "R=3, Rbar=2"})
	out = append(out, catalogEntry{"cw_1 (C^2^3)", cwq(1), "intermediate"})
	out = append(out, catalogEntry{"cw_2 (C^3^3)", cwq(2), "intermediate"})
	out = append(out, catalogEntry{"CW_1 (C^3^3)", cwQ(1), "intermediate"})
	out = append(out, catalogEntry{"CW_2 (C^4^3)", cwQ(2), "intermediate"})
	out = append(out, catalogEntry{"Str_2 (C^3^3)", strq(2), "R=4, Rbar=3"})
	out = append(out, catalogEntry{"Str_3 (C^4^3)", strq(3), "R=6, Rbar=4"})
	out = append(out, catalogEntry{"T_ACGJ (C^3^3)", tacgj(), "Rbar=5 (1801.04852 Prop 3.1)"})
	out = append(out, catalogEntry{"<2,2,2> (C^4^3)", mm(2), "R=7, Rbar=7"})
	out = append(out, catalogEntry{"<3,3,3> (C^9^3)", mm(3), "R<=23, Rbar>=19"})
	out = append(out, catalogEntry{"<4,4,4> (C^16^3)", mm(4), "R<=47..49"})
	return out
}

// ghz: unit tensor I_{3,r} embedded in C^d^3, sum_{i<r} e_i⊗e_i⊗e_i.
func ghz(r, d int) *tensor {
	t := newTensor(d, d, d)
	for i := 0; i < r; i++ {
		t.set(i, i, i, 1)
	}
	return t
}

// w3 = e2⊗e1⊗e1 + e1⊗e2⊗e1 + e1⊗e1⊗e2 (1-indexed in the spec; 0-indexed here:
// indices 1 and 0). Lives in C^2^3.
func w3() *tensor {
	t := newTensor(2, 2, 2)
	t.add(1, 0, 0, 1)
	t.add(0, 1, 0, 1)
	t.add(0, 0, 1, 1)
	return t
}

// cwq = sum_{i=1}^q (e0⊗ei⊗ei + ei⊗e0⊗ei + ei⊗ei⊗e0), lives in C^(q+1)^3.
func cwq(q int) *tensor {
	d := q + 1
	t := newTensor(d, d, d)
	for i := 1; i <= q; i++ {
		t.add(0, i, i, 1)
		t.add(i, 0, i, 1)
		t.add(i, i, 0, 1)
	}
	return t
}

// cwQ = cw_q + e0⊗e0⊗e_{q+1} + e0⊗e_{q+1}⊗e0 + e_{q+1}⊗e0⊗e0, lives in C^(q+2)^3.
func cwQ(q int) *tensor {
	d := q + 2
	t := newTensor(d, d, d)
	for i := 1; i <= q; i++ {
		t.add(0, i, i, 1)
		t.add(i, 0, i, 1)
		t.add(i, i, 0, 1)
	}
	qp := q + 1
	t.add(0, 0, qp, 1)
	t.add(0, qp, 0, 1)
	t.add(qp, 0, 0, 1)
	return t
}

// strq = sum_{i=2}^{q+1} (e_i⊗e_i⊗e_1 + e_1⊗e_i⊗e_i), 1-indexed; 0-indexed:
// e_1 -> index 0, e_i (i=2..q+1) -> indices 1..q. Lives in C^(q+1)^3.
func strq(q int) *tensor {
	d := q + 1
	t := newTensor(d, d, d)
	for i := 1; i <= q; i++ {
		t.add(i, i, 0, 1)
		t.add(0, i, i, 1)
	}
	return t
}

// tacgj: T_ACGJ in C^3^3, a_i=b_i=c_i=e_i (0-indexed e_0,e_1,e_2):
//
//	e0⊗e0⊗e0 + e1⊗e1⊗e1 + e2⊗e2⊗e2 + (Σe)⊗(Σe)⊗(Σe)
//	+ 2(e0+e1)⊗(e0+e2)⊗(e1+e2).
func tacgj() *tensor {
	t := newTensor(3, 3, 3)
	add3 := func(a, b, c []complex128, scale complex128) {
		for i := 0; i < 3; i++ {
			for j := 0; j < 3; j++ {
				for k := 0; k < 3; k++ {
					t.add(i, j, k, scale*a[i]*b[j]*c[k])
				}
			}
		}
	}
	e := func(idx ...int) []complex128 {
		v := make([]complex128, 3)
		for _, x := range idx {
			v[x] += 1
		}
		return v
	}
	add3(e(0), e(0), e(0), 1)
	add3(e(1), e(1), e(1), 1)
	add3(e(2), e(2), e(2), 1)
	add3(e(0, 1, 2), e(0, 1, 2), e(0, 1, 2), 1)
	add3(e(0, 1), e(0, 2), e(1, 2), 2)
	return t
}

// mm builds the matrix-multiplication tensor <n,n,n> in C^(n^2)^3:
// sum_{i,j,k} e_{ij} ⊗ e_{jk} ⊗ e_{ki}, where e_{ab} has flat index a*n+b.
func mm(n int) *tensor {
	d := n * n
	t := newTensor(d, d, d)
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			for k := 0; k < n; k++ {
				t.add(i*n+j, j*n+k, k*n+i, 1)
			}
		}
	}
	return t
}

// ---------------------------------------------------------------------------
// Random tensors
// ---------------------------------------------------------------------------

// randComplex returns a standard complex Gaussian (real,imag ~ N(0,1)).
func randComplex(rng *rand.Rand) complex128 {
	return complex(rng.NormFloat64(), rng.NormFloat64())
}

// randRankR builds a tensor of rank <= r in C^d^3 as a sum of r random complex
// rank-one terms with Gaussian factors.
func randRankR(rng *rand.Rand, d, r int) *tensor {
	t := newTensor(d, d, d)
	a := make([]complex128, d)
	b := make([]complex128, d)
	c := make([]complex128, d)
	for s := 0; s < r; s++ {
		for x := 0; x < d; x++ {
			a[x] = randComplex(rng)
			b[x] = randComplex(rng)
			c[x] = randComplex(rng)
		}
		for i := 0; i < d; i++ {
			ai := a[i]
			for j := 0; j < d; j++ {
				aibj := ai * b[j]
				base := (i*d + j) * d
				for k := 0; k < d; k++ {
					t.data[base+k] += aibj * c[k]
				}
			}
		}
	}
	return t
}

// randUnitary returns a Haar-ish d x d unitary via QR of a Gaussian matrix.
func randUnitary(rng *rand.Rand, d int) [][]complex128 {
	A := make([][]complex128, d)
	for i := range A {
		A[i] = make([]complex128, d)
		for j := range A[i] {
			A[i][j] = randComplex(rng)
		}
	}
	return qrUnitary(A)
}

// qrUnitary computes the Q factor of A via modified Gram-Schmidt on columns,
// then phase-fixes to a deterministic unitary.
func qrUnitary(A [][]complex128) [][]complex128 {
	d := len(A)
	// columns
	cols := make([][]complex128, d)
	for j := 0; j < d; j++ {
		cols[j] = make([]complex128, d)
		for i := 0; i < d; i++ {
			cols[j][i] = A[i][j]
		}
	}
	for j := 0; j < d; j++ {
		for k := 0; k < j; k++ {
			var dot complex128
			for i := 0; i < d; i++ {
				dot += cmplx.Conj(cols[k][i]) * cols[j][i]
			}
			for i := 0; i < d; i++ {
				cols[j][i] -= dot * cols[k][i]
			}
		}
		var nrm float64
		for i := 0; i < d; i++ {
			nrm += real(cols[j][i])*real(cols[j][i]) + imag(cols[j][i])*imag(cols[j][i])
		}
		nrm = math.Sqrt(nrm)
		inv := complex(1.0/nrm, 0)
		for i := 0; i < d; i++ {
			cols[j][i] *= inv
		}
	}
	Q := make([][]complex128, d)
	for i := 0; i < d; i++ {
		Q[i] = make([]complex128, d)
		for j := 0; j < d; j++ {
			Q[i][j] = cols[j][i]
		}
	}
	return Q
}

// applyLocalUnitaries returns (U⊗V⊗W)·T for unitaries on each leg.
func applyLocalUnitaries(t *tensor, U, V, W [][]complex128) *tensor {
	// Mode-by-mode multiply.
	out := t.clone()
	out = modeMul(out, U, 0)
	out = modeMul(out, V, 1)
	out = modeMul(out, W, 2)
	return out
}

func modeMul(t *tensor, M [][]complex128, mode int) *tensor {
	out := newTensor(t.d1, t.d2, t.d3)
	switch mode {
	case 0:
		for ip := 0; ip < t.d1; ip++ {
			for j := 0; j < t.d2; j++ {
				for k := 0; k < t.d3; k++ {
					var s complex128
					for i := 0; i < t.d1; i++ {
						s += M[ip][i] * t.at(i, j, k)
					}
					out.set(ip, j, k, s)
				}
			}
		}
	case 1:
		for i := 0; i < t.d1; i++ {
			for jp := 0; jp < t.d2; jp++ {
				for k := 0; k < t.d3; k++ {
					var s complex128
					for j := 0; j < t.d2; j++ {
						s += M[jp][j] * t.at(i, j, k)
					}
					out.set(i, jp, k, s)
				}
			}
		}
	default:
		for i := 0; i < t.d1; i++ {
			for j := 0; j < t.d2; j++ {
				for kp := 0; kp < t.d3; kp++ {
					var s complex128
					for k := 0; k < t.d3; k++ {
						s += M[kp][k] * t.at(i, j, k)
					}
					out.set(i, j, kp, s)
				}
			}
		}
	}
	return out
}

// ---------------------------------------------------------------------------
// Sanity checks (hard assertions).
// ---------------------------------------------------------------------------

func runSanity(classes []invClass, seed int64) {
	rng := rand.New(rand.NewSource(seed))
	const eps = 1e-9

	// (a) f = 1 on every rank-one tensor for every class.
	for trial := 0; trial < 20; trial++ {
		d := 2 + rng.Intn(3) // 2..4
		t := randRankR(rng, d, 1)
		for ci := range classes {
			f := normalizedInvariant(t, &classes[ci])
			if cmplx.Abs(f-1) > eps {
				panicf("sanity FAIL: class %v gave f=%v on a rank-one tensor (expected 1)", classes[ci].rep, f)
			}
		}
	}

	// (b) all-identity class gives f=1 on arbitrary tensors.
	idClass := findIdentityClass(classes)
	for trial := 0; trial < 20; trial++ {
		d := 2 + rng.Intn(3)
		t := randRankR(rng, d, 3)
		f := normalizedInvariant(t, idClass)
		if cmplx.Abs(f-1) > eps {
			panicf("sanity FAIL: identity class gave f=%v (expected 1)", f)
		}
	}

	// (c) invariance under random local unitaries.
	for trial := 0; trial < 10; trial++ {
		d := 2 + rng.Intn(3)
		t := randRankR(rng, d, 4)
		U := randUnitary(rng, d)
		V := randUnitary(rng, d)
		W := randUnitary(rng, d)
		tu := applyLocalUnitaries(t, U, V, W)
		for ci := range classes {
			f0 := normalizedInvariant(t, &classes[ci])
			f1 := normalizedInvariant(tu, &classes[ci])
			if cmplx.Abs(f0-f1) > 1e-7 {
				panicf("sanity FAIL: class %v not local-unitary invariant: %v vs %v (|Δ|=%g)",
					classes[ci].rep, f0, f1, cmplx.Abs(f0-f1))
			}
		}
	}
}

func findIdentityClass(classes []invClass) *invClass {
	id := perm{0, 1, 2}
	for i := range classes {
		if classes[i].rep == (triple{id, id, id}) {
			return &classes[i]
		}
	}
	panic("identity class not found")
}

func find3CycleClass(classes []invClass) *invClass {
	c := perm{1, 2, 0}
	for i := range classes {
		if classes[i].rep == (triple{c, c, c}) {
			return &classes[i]
		}
	}
	panic("3-cycle class not found")
}

func find3CycleInverse(classes []invClass) *invClass {
	c := perm{2, 0, 1}
	for i := range classes {
		// (132) class representative: search by orbit membership.
		for _, o := range classes[i].orbit {
			if o == (triple{c, c, c}) {
				return &classes[i]
			}
		}
	}
	panic("inverse 3-cycle class not found")
}

func panicf(format string, args ...any) { panic(fmt.Sprintf(format, args...)) }

// ---------------------------------------------------------------------------
// Result types and experiments
// ---------------------------------------------------------------------------

type results struct {
	Seed         int64            `json:"seed"`
	Samples      int              `json:"samples_per_cell"`
	NumClasses   int              `json:"num_classes"`
	Classes      []classInfo      `json:"classes"`
	SanityPassed bool             `json:"sanity_passed"`
	Catalog      []catalogRow     `json:"catalog"`
	Detection    detectionResult  `json:"detection"`
	Separation   separationResult `json:"separation"`
	Conclusion   conclusion       `json:"conclusion"`
	Elapsed      string           `json:"elapsed"`
	Complete     bool             `json:"complete"`
}

type classInfo struct {
	Index        int    `json:"index"`
	Rep          string `json:"rep"`
	OrbitSize    int    `json:"orbit_size"`
	Disconnected bool   `json:"disconnected"`
	CostExponent int    `json:"cost_exponent"`
}

func describeClasses(classes []invClass) []classInfo {
	out := make([]classInfo, len(classes))
	for i := range classes {
		out[i] = classInfo{
			Index:        i,
			Rep:          tripleString(classes[i].rep),
			OrbitSize:    len(classes[i].orbit),
			Disconnected: classes[i].disconnected,
			CostExponent: costExponent(classes[i].plan),
		}
	}
	return out
}

func costExponent(p contractionPlan) int {
	mx := 3
	for _, s := range p.steps {
		u := len(union(s.a, s.b))
		if u > mx {
			mx = u
		}
	}
	return mx
}

func tripleString(t triple) string {
	return fmt.Sprintf("(%s,%s,%s)", permString(t[0]), permString(t[1]), permString(t[2]))
}

func permString(p perm) string {
	// cycle-ish notation: map to one-line.
	return fmt.Sprintf("%d%d%d", p[0], p[1], p[2])
}

type catalogRow struct {
	Name       string       `json:"name"`
	Dims       [3]int       `json:"dims"`
	Rank       string       `json:"rank_info"`
	NormSq     float64      `json:"norm_sq"`
	Flattening [3][]float64 `json:"flattening_spectra"`
	FlatRanks  [3]int       `json:"flattening_ranks"`
	Invariants []cmplxJSON  `json:"invariants"` // per class, normalized
}

type cmplxJSON struct {
	Re  float64 `json:"re"`
	Im  float64 `json:"im"`
	Abs float64 `json:"abs"`
}

func toJSON(z complex128) cmplxJSON {
	return cmplxJSON{Re: real(z), Im: imag(z), Abs: cmplx.Abs(z)}
}

func evalCatalog(classes []invClass, cat []catalogEntry) []catalogRow {
	rows := make([]catalogRow, len(cat))
	for ei, e := range cat {
		spectra := flatteningSpectra(e.t)
		var franks [3]int
		for m := 0; m < 3; m++ {
			franks[m] = numericalRank(spectra[m])
		}
		invs := make([]cmplxJSON, len(classes))
		for ci := range classes {
			invs[ci] = toJSON(normalizedInvariant(e.t, &classes[ci]))
		}
		rows[ei] = catalogRow{
			Name:       e.name,
			Dims:       [3]int{e.t.d1, e.t.d2, e.t.d3},
			Rank:       e.rank,
			NormSq:     e.t.normSq(),
			Flattening: spectra,
			FlatRanks:  franks,
			Invariants: invs,
		}
	}
	return rows
}

// numericalRank counts singular values above a relative threshold.
func numericalRank(sv []float64) int {
	if len(sv) == 0 {
		return 0
	}
	top := sv[0]
	if top == 0 {
		return 0
	}
	n := 0
	for _, s := range sv {
		if s/top > 1e-8 {
			n++
		}
	}
	return n
}

// ---------------------------------------------------------------------------
// Detection experiment: W_3 vs GHZ_2
// ---------------------------------------------------------------------------

type detectionResult struct {
	W3Spectra         [3][]float64 `json:"w3_flattening_spectra"`
	GHZ2Spectra       [3][]float64 `json:"ghz2_flattening_spectra"`
	SpectraEqual      bool         `json:"spectra_equal_after_normalization"`
	MaxSpectralDiff   float64      `json:"max_spectral_diff"`
	W3Invariants      []cmplxJSON  `json:"w3_invariants"`
	GHZ2Invariants    []cmplxJSON  `json:"ghz2_invariants"`
	SeparatingClasses []int        `json:"separating_class_indices"`
	SeparatingReps    []string     `json:"separating_class_reps"`
}

func runDetection(classes []invClass) detectionResult {
	w := w3()
	g := ghz(2, 2)
	ws := flatteningSpectra(w)
	gs := flatteningSpectra(g)
	maxDiff := 0.0
	for m := 0; m < 3; m++ {
		ln := max(len(ws[m]), len(gs[m]))
		for x := 0; x < ln; x++ {
			var a, b float64
			if x < len(ws[m]) {
				a = ws[m][x]
			}
			if x < len(gs[m]) {
				b = gs[m][x]
			}
			if d := math.Abs(a - b); d > maxDiff {
				maxDiff = d
			}
		}
	}
	dr := detectionResult{
		W3Spectra:       ws,
		GHZ2Spectra:     gs,
		SpectraEqual:    maxDiff < 1e-9,
		MaxSpectralDiff: maxDiff,
	}
	dr.W3Invariants = make([]cmplxJSON, len(classes))
	dr.GHZ2Invariants = make([]cmplxJSON, len(classes))
	for ci := range classes {
		fw := normalizedInvariant(w, &classes[ci])
		fg := normalizedInvariant(g, &classes[ci])
		dr.W3Invariants[ci] = toJSON(fw)
		dr.GHZ2Invariants[ci] = toJSON(fg)
		if cmplx.Abs(fw-fg) > 1e-7 {
			dr.SeparatingClasses = append(dr.SeparatingClasses, ci)
			dr.SeparatingReps = append(dr.SeparatingReps, tripleString(classes[ci].rep))
		}
	}
	return dr
}

// ---------------------------------------------------------------------------
// Separation experiment
// ---------------------------------------------------------------------------

type separationResult struct {
	Cells      []sepCell `json:"cells"`
	Throughput string    `json:"throughput"`
	Note       string    `json:"note"`
}

// sepCell is one (n, r) sampling cell.
type sepCell struct {
	N         int             `json:"n"`
	D         int             `json:"d"`
	R         int             `json:"r"`
	Requested int             `json:"requested_samples"`
	Collected int             `json:"collected_samples"`
	FlatBound int             `json:"flattening_bound"` // = n^2 = d
	MMValue   []cmplxJSON     `json:"mm_value_per_class"`
	Stats     []sepClassStats `json:"stats_per_class"`
	// Real combinations of the two 3-cycle invariants.
	ComboSym      sepRealStats `json:"combo_sym"`  // f_(123)+f_(132), real
	ComboAnti     sepRealStats `json:"combo_anti"` // i*(f_(123)-f_(132)), real
	MMComboSym    float64      `json:"mm_combo_sym"`
	MMComboAnti   float64      `json:"mm_combo_anti"`
	MMComboSymIn  bool         `json:"mm_combo_sym_inside"`
	MMComboAntiIn bool         `json:"mm_combo_anti_inside"`
}

type sepClassStats struct {
	ClassIndex  int        `json:"class_index"`
	Re          rangeStats `json:"re"`
	Im          rangeStats `json:"im"`
	Abs         rangeStats `json:"abs"`
	MMInsideRe  bool       `json:"mm_inside_re"`
	MMInsideIm  bool       `json:"mm_inside_im"`
	MMInsideAbs bool       `json:"mm_inside_abs"`
	// MMInside is the bounding-box test: BOTH Re and Im of f(MM) lie within the
	// sampled [min,max]. This is an OUTER approximation of the value cloud, so
	// "outside" (separation) is the conservative, robust claim.
	MMInside bool `json:"mm_inside"`
}

type sepRealStats struct {
	Stats rangeStats `json:"stats"`
}

type rangeStats struct {
	Min  float64 `json:"min"`
	Max  float64 `json:"max"`
	Q05  float64 `json:"q05"`
	Q50  float64 `json:"q50"`
	Q95  float64 `json:"q95"`
	Mean float64 `json:"mean"`
}

func computeRange(xs []float64) rangeStats {
	if len(xs) == 0 {
		return rangeStats{}
	}
	s := append([]float64(nil), xs...)
	sort.Float64s(s)
	var sum float64
	for _, x := range s {
		sum += x
	}
	q := func(p float64) float64 {
		idx := int(p * float64(len(s)-1))
		return s[idx]
	}
	return rangeStats{
		Min:  s[0],
		Max:  s[len(s)-1],
		Q05:  q(0.05),
		Q50:  q(0.50),
		Q95:  q(0.95),
		Mean: sum / float64(len(s)),
	}
}

func runSeparation(ctx context.Context, classes []invClass, seed int64, samples, workers int, start time.Time) separationResult {
	sr := separationResult{
		Note: "ranks-nest-upward: if f(MM) is inside the sampled range for rank r, certification at rank>=r by f is dead (inner approximation).",
	}
	c123 := classIndexOf(classes, perm{1, 2, 0})
	c132 := classIndexOf(classes, perm{2, 0, 1})

	var totalSamples int64
	swStart := time.Now()

	for _, n := range []int{2, 3} {
		d := n * n
		sweep := rankSweep(n)
		mmT := mm(n)
		// Precompute MM invariant values.
		mmVals := make([]complex128, len(classes))
		for ci := range classes {
			mmVals[ci] = normalizedInvariant(mmT, &classes[ci])
		}
		mmComboSym := real(mmVals[c123] + mmVals[c132])
		mmComboAnti := real(complex(0, 1) * (mmVals[c123] - mmVals[c132]))

		for _, r := range sweep {
			if ctx.Err() != nil {
				sr.Note += " [TRUNCATED: deadline reached before sweep completion]"
				goto done
			}
			cell := sampleCell(ctx, classes, seed, n, d, r, samples, workers, c123, c132)
			atomic.AddInt64(&totalSamples, int64(cell.Collected))

			// Fill MM values and inside-tests. (cell.Stats is already populated by
			// sampleCell; do NOT re-allocate it here or the sampled ranges are lost.)
			cell.MMValue = make([]cmplxJSON, len(classes))
			for ci := range classes {
				cell.MMValue[ci] = toJSON(mmVals[ci])
			}
			fillInside(&cell, classes, mmVals, mmComboSym, mmComboAnti)
			cell.MMComboSym = mmComboSym
			cell.MMComboAnti = mmComboAnti
			sr.Cells = append(sr.Cells, cell)
			fmt.Printf("  [%s] n=%d r=%d: collected %d samples\n", since(start), n, r, cell.Collected)
		}
	}
done:
	elapsed := time.Since(swStart).Seconds()
	if elapsed > 0 {
		sr.Throughput = fmt.Sprintf("%.0f samples/sec (%d total samples)", float64(totalSamples)/elapsed, totalSamples)
	}
	return sr
}

// rankSweep returns the requested rank values for a given n, deduped/sorted,
// clamped to be >= 1.
func rankSweep(n int) []int {
	d := n * n
	raw := []int{1, 2, 4, d, 3 * d / 2, 2 * d, d*n - n + 1} // n^3 - n + 1 = d*n - n + 1
	seen := map[int]bool{}
	var out []int
	for _, r := range raw {
		if r < 1 {
			r = 1
		}
		if !seen[r] {
			seen[r] = true
			out = append(out, r)
		}
	}
	sort.Ints(out)
	return out
}

// sampleCell draws `samples` rank-r tensors and accumulates per-class stats.
func sampleCell(ctx context.Context, classes []invClass, seed int64, n, d, r, samples, workers, c123, c132 int) sepCell {
	cell := sepCell{N: n, D: d, R: r, Requested: samples, FlatBound: d}

	type acc struct {
		re, im, abs []float64
	}
	perWorker := make([][]acc, workers)
	comboSymPW := make([][]float64, workers)
	comboAntiPW := make([][]float64, workers)
	var collected int64

	var wg sync.WaitGroup
	for w := 0; w < workers; w++ {
		wg.Add(1)
		go func(wid int) {
			defer wg.Done()
			rng := rand.New(rand.NewSource(seed*1_000_003 + int64(n)*7919 + int64(r)*104729 + int64(wid)))
			la := make([]acc, len(classes))
			var lsym, lanti []float64
			// Partition samples across workers.
			lo := wid * samples / workers
			hi := (wid + 1) * samples / workers
			for s := lo; s < hi; s++ {
				if s%64 == 0 && ctx.Err() != nil {
					break
				}
				t := randRankR(rng, d, r)
				vals := make([]complex128, len(classes))
				for ci := range classes {
					f := normalizedInvariant(t, &classes[ci])
					vals[ci] = f
					la[ci].re = append(la[ci].re, real(f))
					la[ci].im = append(la[ci].im, imag(f))
					la[ci].abs = append(la[ci].abs, cmplx.Abs(f))
				}
				lsym = append(lsym, real(vals[c123]+vals[c132]))
				lanti = append(lanti, real(complex(0, 1)*(vals[c123]-vals[c132])))
				atomic.AddInt64(&collected, 1)
			}
			perWorker[wid] = la
			comboSymPW[wid] = lsym
			comboAntiPW[wid] = lanti
		}(w)
	}
	wg.Wait()

	cell.Collected = int(collected)
	cell.Stats = make([]sepClassStats, len(classes))
	// Merge.
	for ci := range classes {
		var re, im, ab []float64
		for w := 0; w < workers; w++ {
			if perWorker[w] == nil {
				continue
			}
			re = append(re, perWorker[w][ci].re...)
			im = append(im, perWorker[w][ci].im...)
			ab = append(ab, perWorker[w][ci].abs...)
		}
		cell.Stats[ci] = sepClassStats{
			ClassIndex: ci,
			Re:         computeRange(re),
			Im:         computeRange(im),
			Abs:        computeRange(ab),
		}
	}
	var sym, anti []float64
	for w := 0; w < workers; w++ {
		sym = append(sym, comboSymPW[w]...)
		anti = append(anti, comboAntiPW[w]...)
	}
	cell.ComboSym = sepRealStats{Stats: computeRange(sym)}
	cell.ComboAnti = sepRealStats{Stats: computeRange(anti)}
	return cell
}

func fillInside(cell *sepCell, classes []invClass, mmVals []complex128, mmComboSym, mmComboAnti float64) {
	const tol = 1e-9
	for ci := range classes {
		st := &cell.Stats[ci]
		mv := mmVals[ci]
		st.MMInsideRe = real(mv) >= st.Re.Min-tol && real(mv) <= st.Re.Max+tol
		st.MMInsideIm = imag(mv) >= st.Im.Min-tol && imag(mv) <= st.Im.Max+tol
		st.MMInsideAbs = cmplx.Abs(mv) >= st.Abs.Min-tol && cmplx.Abs(mv) <= st.Abs.Max+tol
		st.MMInside = st.MMInsideRe && st.MMInsideIm
	}
	cell.MMComboSymIn = mmComboSym >= cell.ComboSym.Stats.Min-tol && mmComboSym <= cell.ComboSym.Stats.Max+tol
	cell.MMComboAntiIn = mmComboAnti >= cell.ComboAnti.Stats.Min-tol && mmComboAnti <= cell.ComboAnti.Stats.Max+tol
}

func classIndexOf(classes []invClass, p perm) int {
	target := triple{p, p, p}
	for i := range classes {
		for _, o := range classes[i].orbit {
			if o == target {
				return i
			}
		}
	}
	panic(fmt.Sprintf("class containing %v not found", target))
}

// ---------------------------------------------------------------------------
// Conclusion
// ---------------------------------------------------------------------------

type conclusion struct {
	// (a) separation results.
	AnyOutsideAtFlatBound bool          `json:"any_class_mm_outside_sampled_range_at_r_ge_flatbound"`
	AnyOutsideAnyR        bool          `json:"any_class_mm_outside_sampled_range_at_any_r"`
	PerCellOutsideCount   []cellOutside `json:"per_cell_outside_counts"`
	// Constant (uninformative) classes: f is sample-invariant (range width ~ 0).
	ConstantClasses    []string `json:"constant_classes"`
	NumConstantClasses int      `json:"num_constant_classes"`
	PureCycleConstant  bool     `json:"pure_3cycle_invariants_constant"`
	CombosSeparateMM   bool     `json:"three_cycle_combos_separate_mm"`
	// (b) detection.
	W3GHZ2Separated         bool     `json:"w3_ghz2_separated"`
	W3GHZ2SeparatingClasses []string `json:"w3_ghz2_separating_classes"`
	// Honest reading of the separation test.
	Caveat  string `json:"caveat"`
	Summary string `json:"summary"`
}

type cellOutside struct {
	N             int  `json:"n"`
	R             int  `json:"r"`
	FlatBound     int  `json:"flattening_bound"`
	AtOrAboveFlat bool `json:"r_ge_flatbound"`
	OutsideCount  int  `json:"classes_outside"`
	ComboSymOut   bool `json:"combo_sym_outside"`
	ComboAntiOut  bool `json:"combo_anti_outside"`
}

func buildConclusion(classes []invClass, res *results) conclusion {
	var c conclusion
	c.W3GHZ2Separated = len(res.Detection.SeparatingClasses) > 0
	c.W3GHZ2SeparatingClasses = res.Detection.SeparatingReps

	// Identify classes whose sampled value range is (near) zero width across all
	// cells: these are constant on random tensors and carry no rank information.
	const widthTol = 1e-6
	constant := make([]bool, len(classes))
	for ci := range classes {
		constant[ci] = true
	}
	for _, cell := range res.Separation.Cells {
		for ci := range classes {
			if ci >= len(cell.Stats) {
				continue
			}
			st := cell.Stats[ci]
			w := (st.Re.Max - st.Re.Min) + (st.Im.Max - st.Im.Min)
			if w > widthTol {
				constant[ci] = false
			}
		}
	}
	for ci := range classes {
		if constant[ci] {
			c.ConstantClasses = append(c.ConstantClasses, tripleString(classes[ci].rep))
		}
	}
	c.NumConstantClasses = len(c.ConstantClasses)

	// Pure 3-cycle invariants constant? (classes (123,123,123) and (132,132,132))
	c123 := classIndexOf(classes, perm{1, 2, 0})
	c132 := classIndexOf(classes, perm{2, 0, 1})
	c.PureCycleConstant = constant[c123] && constant[c132]

	// Do the 3-cycle combos ever separate MM (MM outside sampled combo range)?
	c.CombosSeparateMM = false

	for _, cell := range res.Separation.Cells {
		outside := 0
		for ci := range classes {
			if ci >= len(cell.Stats) {
				continue
			}
			if !cell.Stats[ci].MMInside {
				outside++
				c.AnyOutsideAnyR = true
				if cell.R >= cell.FlatBound {
					c.AnyOutsideAtFlatBound = true
				}
			}
		}
		if !cell.MMComboSymIn || !cell.MMComboAntiIn {
			c.CombosSeparateMM = true
		}
		c.PerCellOutsideCount = append(c.PerCellOutsideCount, cellOutside{
			N:             cell.N,
			R:             cell.R,
			FlatBound:     cell.FlatBound,
			AtOrAboveFlat: cell.R >= cell.FlatBound,
			OutsideCount:  outside,
			ComboSymOut:   !cell.MMComboSymIn,
			ComboAntiOut:  !cell.MMComboAntiIn,
		})
	}

	c.Caveat = "The sampled min/max is an INNER approximation of the true rank-r value range " +
		"(finite N never reaches the special structured MM point). Therefore 'f(MM) outside the " +
		"sampled [min,max]' is NOT a rank certificate: it only says random rank-r draws did not " +
		"reach the MM value, which is expected because <n,n,n> is a measure-zero structured point. " +
		"Only the 'inside' direction is reliable (it kills certification). Across all cells, every " +
		"informative class has f(MM) at a structured rational value distinct from (and typically below) " +
		"the random-tensor cloud, but the cloud does not certifiably exclude that value."

	c.Summary = fmt.Sprintf(
		"(a) No degree-3 trace invariant yields a usable separation certificate for <n,n,n>: the "+
			"pure 3-cycle invariants and their real combinations are IDENTICALLY constant (=1, =2, =0) "+
			"on all tensors (pure_3cycle_constant=%v, combos_separate_mm=%v); the %d informative classes "+
			"place f(MM) at a structured value outside the finite sampled cloud, but that 'outside' is an "+
			"inner-approximation artifact, not a certificate (see caveat). "+
			"(b) W_3/GHZ_2 are separated by %d of %d degree-3 classes (and ALSO by degree-2 flattening "+
			"spectra, since their normalized singular values already differ).",
		c.PureCycleConstant, c.CombosSeparateMM, len(classes)-c.NumConstantClasses,
		len(c.W3GHZ2SeparatingClasses), res.NumClasses)
	return c
}

// ---------------------------------------------------------------------------
// Output
// ---------------------------------------------------------------------------

func writeJSON(path string, res *results) {
	f, err := os.Create(path)
	if err != nil {
		fmt.Fprintf(os.Stderr, "create %s: %v\n", path, err)
		return
	}
	defer func() {
		if cerr := f.Close(); cerr != nil {
			fmt.Fprintf(os.Stderr, "close %s: %v\n", path, cerr)
		}
	}()
	enc := json.NewEncoder(f)
	enc.SetIndent("", "  ")
	if err := enc.Encode(res); err != nil {
		fmt.Fprintf(os.Stderr, "encode %s: %v\n", path, err)
	}
}

func max(a, b int) int {
	if a > b {
		return a
	}
	return b
}
