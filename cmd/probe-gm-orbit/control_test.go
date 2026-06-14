package main

import (
	"context"
	"testing"
	"time"
)

// os1Pair returns the two stabilizer templates used for the Os1 positive/
// negative controls: S_3 (orbit 4, fixed dim 2) and Z_3 (orbit 8, fixed dim 3).
// Two genuinely distinct stabilizers => the two-orbit accumulation (k=0 and k=1)
// over distinct seed spaces and distinct variable blocks (x0,x1 vs x2,x3,x4) is
// actually exercised, which the single-orbit GM anchor (k=0 only) does NOT
// validate. Total orbit 12, rank <= 13 — directly comparable to Or2's S_3/Z_3
// real verdict (which was INFEASIBLE).
func os1Pair(G *Group) (orbitTemplate, orbitTemplate, []Mat, []Mat) {
	cat := orbitCatalog()
	var t1, t2 orbitTemplate
	for _, o := range cat {
		switch o.name {
		case "S_3":
			t1 = o
		case "Z_3":
			t2 = o
		}
	}
	fb1 := fixedBasis(G, G.subgroup(t1.gens))
	fb2 := fixedBasis(G, G.subgroup(t2.gens))
	return t1, t2, fb1, fb2
}

// os1GoodParams are the chosen seed coordinates for the positive control. Orbit
// 1 (S_3) owns x0,x1; orbit 2 (Z_3) owns x2,x3,x4. The resulting concrete seeds
// m1* = 1*B0 + 2*B1 and m2* = 1*B0 - 1*B1 + 1*B2 are FULL matrix rank 3 (checked
// via sager: det 4 each), i.e. genuinely NOT rank-1 — they exercise the
// arbitrary-matrix-rank seed handling that GM's published rank-1 seed does not.
func os1GoodParams() []Q3 {
	return []Q3{
		q3i(1, 0),  // x0
		q3i(2, 0),  // x1
		q3i(1, 0),  // x2
		q3i(-1, 0), // x3
		q3i(1, 0),  // x4
	}
}

// TestOs1PositiveControl is the load-bearing Stage-0 anchor for the MULTI-ORBIT
// machinery. It drives the EXACT verdict-producing path
// (buildPairSystemTarget -> sageScript -> sager Groebner -> SOLUTION-FOUND ->
// seedFromParams -> reconstruct) against a tensor T' that is feasible BY
// CONSTRUCTION, and asserts the pipeline returns SOLUTION-FOUND (not the unit
// ideal) and reconstructs T' exactly. On the real Or2 run all 18 pairs were
// INFEASIBLE, so this SOLUTION-FOUND branch never fired; this test fires it.
func TestOs1PositiveControl(t *testing.T) {
	if testing.Short() {
		t.Skip("skipping Os1 sager round-trip in -short")
	}
	G := buildGroup()
	basisRR := rrStarBasis()
	t1, t2, fb1, fb2 := os1Pair(G)
	good := os1GoodParams()
	if len(good) != len(fb1)+len(fb2) {
		t.Fatalf("param count %d != nvars %d", len(good), len(fb1)+len(fb2))
	}

	// Concrete H-fixed seeds m1*, m2* (the planted solution).
	m1 := seedFromParams(fb1, good, 0)
	m2 := seedFromParams(fb2, good, len(fb1))
	seedsStar := []Mat{m1, m2}

	// Both seeds must be genuinely non-rank-1 (arbitrary-matrix-rank handling).
	if r := matRank(m1); r < 2 {
		t.Fatalf("m1* matrix rank %d; want >=2 (non-rank-1 control)", r)
	}
	if r := matRank(m2); r < 2 {
		t.Fatalf("m2* matrix rank %d; want >=2 (non-rank-1 control)", r)
	}

	// Both orbits must contribute non-trivially, else "two-orbit" is hollow and
	// the control would only exercise the single-orbit path the GM anchor already
	// covers. orbit(m1*) and orbit(m2*) must each move some basis-triple value.
	if !orbitContributes(G, basisRR, m1) {
		t.Fatal("orbit 1 (S_3 seed) contributes nothing; two-orbit path not exercised")
	}
	if !orbitContributes(G, basisRR, m2) {
		t.Fatal("orbit 2 (Z_3 seed) contributes nothing; two-orbit path not exercised")
	}

	// Target tensor T' = id^⊗3 + orbit(m1*) + orbit(m2*), as an inner-product
	// functional. SAME ansatzInner that reconstruction uses.
	target := targetFromSeeds(G, seedsStar)

	// Stage 1 (SAME builder as the 18 verdicts): symbolic two-orbit cubic system
	// against T'. Only the target term differs from Or2's MM system.
	sys := buildPairSystemTarget(G, basisRR, t1, t2, target)
	t.Logf("Os1 positive system: %d vars, %d nontrivial polys, max degree %d (S_3/Z_3, rank<=%d)",
		sys.nvars, sys.nonTrivial, sys.maxDegree, 1+t1.orbit+t2.orbit)

	// Sanity A: the planted solution x* must zero every constraint (feasible by
	// construction). If not, the builder is inconsistent with reconstruction.
	if ok, idx, val := allConstraintsVanishAt(sys, good); !ok {
		t.Fatalf("planted solution does NOT satisfy constraint %d (value %s): builder/reconstruct mismatch",
			idx, val.String())
	}

	// Sanity B: the system must have NO nonzero constant generator (a constant
	// generator => spurious unit ideal => the very false-INFEASIBLE failure mode
	// this audit guards against). For a feasible-by-construction target there can
	// be none, by Sanity A.
	if bad, c := constantInfeasible(sys); bad {
		t.Fatalf("feasible-by-construction system has constant generator %s (would be a spurious unit ideal)",
			c.String())
	}

	// Stage 2 (sager, the SAME Groebner step that certified the 18 unit ideals):
	// must return SOLUTION-FOUND, NOT INFEASIBLE.
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Minute)
	defer cancel()
	res, raw, err := runSage(ctx, "Os1-positive-S_3_Z_3", sageScript(sys))
	if err != nil {
		t.Fatalf("sager Stage-2 failed: %v\noutput:\n%s", err, raw)
	}
	if res.Verdict == "INFEASIBLE" {
		t.Fatalf("ANCHOR-FAILED: feasible-by-construction control returned INFEASIBLE (unit ideal %v). "+
			"Or2's machinery turns a TRUE feasible pair into a spurious unit ideal => verdicts UNTRUSTWORTHY.",
			res.Groebner)
	}
	if res.Verdict != "SOLUTION-FOUND" {
		t.Fatalf("expected SOLUTION-FOUND, got %q (reason %q)", res.Verdict, res.Reason)
	}
	t.Logf("Stage-2 sager verdict: SOLUTION-FOUND, dimension=%v, num_points=%v",
		intPtr(res.Dimension), intPtr(res.NumPoints))

	// Cross-check (Leg B, the decisive one): the planted solution x* must appear
	// among Sage's INDEPENDENTLY computed variety points. If Go's symbolic
	// orbit-sum were systematically wrong, the emitted polynomials would not
	// vanish at x* and Sage would not list it. Recovering x* from a CAS Groebner
	// solve of Go's emitted system closes the "Go built the wrong system" gap.
	plantedAmongPoints := false
	for _, pt := range res.Points {
		vals, okPt := pointToVals(pt, sys.nvars)
		if !okPt {
			continue
		}
		if q3VecEqual(vals, good) {
			plantedAmongPoints = true
			break
		}
	}
	if !plantedAmongPoints {
		t.Fatalf("planted x* not among Sage's %d variety points => Go's emitted system does NOT encode the "+
			"by-construction solution (symbolic builder suspect). points=%v", intPtr(res.NumPoints), res.Points)
	}
	t.Logf("Cross-check: planted x* = %v appears among Sage's variety points (CAS independently recovered it)",
		q3VecStr(good))

	// Stage 3 (the branch the real run NEVER fired): reconstruct from a Sage
	// solution point and verify T_ansatz = T' exactly. We try every returned
	// rational/sqrt3 point; at least one must reconstruct T'.
	reconstructed := false
	for _, pt := range res.Points {
		vals, okPt := pointToVals(pt, sys.nvars)
		if !okPt {
			continue
		}
		s1 := seedFromParams(fb1, vals, 0)
		s2 := seedFromParams(fb2, vals, len(fb1))
		ok, ba, bb, bc, got, want := verifyAgainstTarget(G, basisRR, []Mat{s1, s2}, target)
		if ok {
			reconstructed = true
			t.Logf("Stage-3 reconstructed T' exactly from a Sage solution point (planted-equal=%v)",
				q3VecEqual(vals, good))
			break
		}
		t.Logf("  point did not reconstruct (first bad triple %d,%d,%d: got %s want %s)",
			ba, bb, bc, got.String(), want.String())
	}

	// If Sage returned no Q(sqrt3)-expressible isolated point (e.g. positive-
	// dimensional family, QQbar reprs), fall back to the planted solution x*: it
	// MUST reconstruct T' exactly (this still exercises the full concrete
	// orbit-sum + sigma-twist reconstruction against the symbolic target).
	if !reconstructed {
		ok, ba, bb, bc, got, want := verifyAgainstTarget(G, basisRR, seedsStar, target)
		if !ok {
			t.Fatalf("planted x* failed to reconstruct T' at (%d,%d,%d): got %s want %s",
				ba, bb, bc, got.String(), want.String())
		}
		t.Logf("Stage-3 reconstructed T' exactly from the planted solution x* "+
			"(Sage points were not Q(sqrt3)-expressible; dimension=%v)", intPtr(res.Dimension))
		reconstructed = true
	}

	if !reconstructed {
		t.Fatal("no solution reconstructed T'")
	}
}

// TestOs1NegativeControl is the mandatory must-FAIL counterpart to
// TestOs1PositiveControl: a test that ALWAYS says feasible is as useless as one
// that always says infeasible. It takes the SAME by-construction-feasible target
// T' and perturbs it by eps on the obstructed box⊗box triple (id, box_x, box_x)
// — a Fourier projection the H-fixed two-orbit ansatz provably cannot reach
// (its orbit term is identically zero). The constraint system must then acquire
// a nonzero constant generator and the verdict must FLIP from SOLUTION-FOUND to
// INFEASIBLE (Sage Groebner = [1]). This confirms the verdict path discriminates
// — the same lever that produced Or2's 18 unit ideals.
func TestOs1NegativeControl(t *testing.T) {
	if testing.Short() {
		t.Skip("skipping Os1 sager round-trip in -short")
	}
	G := buildGroup()
	basisRR := rrStarBasis()
	t1, t2, fb1, fb2 := os1Pair(G)
	good := os1GoodParams()

	m1 := seedFromParams(fb1, good, 0)
	m2 := seedFromParams(fb2, good, len(fb1))
	seedsStar := []Mat{m1, m2}
	base := targetFromSeeds(G, seedsStar)

	// Perturb the target on (id, box_x, box_x) = indices (0,1,1), an obstructed
	// triple (orbit term identically 0). eps = 1 (any nonzero value works).
	const pa, pb, pc = 0, 1, 1
	eps := q3i(1, 0)
	perturbed := perturbTargetOnTriple(basisRR, base, pa, pb, pc, eps)

	sys := buildPairSystemTarget(G, basisRR, t1, t2, perturbed)
	t.Logf("Os1 negative system: %d vars, %d nontrivial polys", sys.nvars, sys.nonTrivial)

	// The planted x* must now FAIL at least one constraint (the perturbed triple),
	// confirming the perturbation actually broke feasibility at x*.
	if ok, _, _ := allConstraintsVanishAt(sys, good); ok {
		t.Fatal("perturbation did not break feasibility at x* (negative control is inert)")
	}

	// Go sanity: a nonzero constant generator should now be present (the obstructed
	// triple has zero orbit term, so its constraint is the bare constant -eps).
	bad, c := constantInfeasible(sys)
	if !bad {
		t.Fatal("expected a constant generator after perturbing an obstructed triple")
	}
	t.Logf("Go sanity: constant generator %s present => unit ideal expected", c.String())

	// Stage 2 (sager): must return INFEASIBLE / unit ideal. This is the full
	// Groebner path exercised on a must-FAIL input.
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Minute)
	defer cancel()
	res, raw, err := runSage(ctx, "Os1-negative-S_3_Z_3", sageScript(sys))
	if err != nil {
		t.Fatalf("sager Stage-2 failed: %v\noutput:\n%s", err, raw)
	}
	if res.Verdict != "INFEASIBLE" {
		t.Fatalf("ANCHOR concern: perturbed (infeasible-by-construction) control returned %q, not INFEASIBLE. "+
			"The verdict path does NOT discriminate => a test that always says feasible. Groebner=%v",
			res.Verdict, res.Groebner)
	}
	if len(res.Groebner) != 1 || res.Groebner[0] != "1" {
		t.Logf("note: INFEASIBLE but Groebner basis is %v (still a unit ideal certificate)", res.Groebner)
	}
	t.Logf("Stage-2 sager verdict FLIPPED to INFEASIBLE (Groebner=%v) as required", res.Groebner)
}

// TestOs1NegativeControlOffSpaceSeed is a second, independent negative control:
// build the target from a seed perturbed OFF the S_3-fixed space, then attempt
// to fit it with the (still H-fixed-constrained) two-orbit ansatz. The off-space
// component cannot be reached from the dim-2 S_3-fixed seed space, so the system
// must be INFEASIBLE. This exercises the "perturb the known-good seed off the
// fixed space" lever named in the task, distinct from the target-perturbation
// lever above.
func TestOs1NegativeControlOffSpaceSeed(t *testing.T) {
	if testing.Short() {
		t.Skip("skipping Os1 sager round-trip in -short")
	}
	G := buildGroup()
	basisRR := rrStarBasis()
	t1, t2, fb1, fb2 := os1Pair(G)
	good := os1GoodParams()

	// m1off = m1* + delta, where delta is NOT in the S_3-fixed space. A single
	// off-diagonal bump E_{0,1} is not S_3-fixed (S_3 here is <(23),(34)> fixing
	// index 0; conjugation moves E_{0,1}).
	m1 := seedFromParams(fb1, good, 0)
	delta := zeroMat()
	delta[0][1] = q3i(1, 0)
	m1off := addMat(m1, delta)
	// Confirm m1off is genuinely off the S_3-fixed space.
	offFixed := false
	for _, h := range G.subgroup(t1.gens) {
		if !equalMat(conj(G.rho[h], m1off), m1off) {
			offFixed = true
			break
		}
	}
	if !offFixed {
		t.Fatal("perturbed seed is still S_3-fixed; choose a different delta")
	}
	m2 := seedFromParams(fb2, good, len(fb1))

	// Target built from the OFF-space seed (full S_4 orbit of m1off, which is no
	// longer an orbit of size 4). The fitter is still constrained to H-fixed seeds.
	target := targetFromSeeds(G, []Mat{m1off, m2})
	sys := buildPairSystemTarget(G, basisRR, t1, t2, target)
	t.Logf("Os1 off-space-seed system: %d vars, %d nontrivial polys", sys.nvars, sys.nonTrivial)

	// The planted in-space x* must NOT satisfy this system (the off-space target
	// is unreachable from the fixed seed spaces).
	if ok, _, _ := allConstraintsVanishAt(sys, good); ok {
		t.Fatal("in-space x* unexpectedly satisfies the off-space-seed target (control inert)")
	}

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Minute)
	defer cancel()
	res, raw, err := runSage(ctx, "Os1-negative-offspace-S_3_Z_3", sageScript(sys))
	if err != nil {
		t.Fatalf("sager Stage-2 failed: %v\noutput:\n%s", err, raw)
	}
	if res.Verdict != "INFEASIBLE" {
		t.Fatalf("off-space-seed target returned %q, not INFEASIBLE (Groebner=%v); "+
			"the fixed-space constraint is not being enforced as expected", res.Verdict, res.Groebner)
	}
	t.Logf("Stage-2 sager verdict: INFEASIBLE (Groebner=%v) — off-space seed correctly rejected", res.Groebner)
}

// TestOs1ProductionPathUnchanged guards that factoring buildPairSystem through
// buildPairSystemTarget did NOT alter Or2's MM verdict path: the S_3/Z_3 MM
// system must still carry the box⊗box constant generator (-3/2) that Or2
// certified as its INFEASIBLE unit-ideal cause. A regression here would mean the
// refactor changed the very systems whose verdicts Os1 is auditing.
func TestOs1ProductionPathUnchanged(t *testing.T) {
	G := buildGroup()
	basisRR := rrStarBasis()
	t1, t2, _, _ := os1Pair(G)
	sys := buildPairSystem(G, basisRR, t1, t2) // MM target, production entry
	bad, c := constantInfeasible(sys)
	if !bad {
		t.Fatal("production S_3/Z_3 MM system lost its constant generator; refactor changed Or2's path")
	}
	// Or2 reported -3/2 (box⊗box) and +2 (antisym) constant residuals; the scan
	// returns the first one encountered. Assert it is one of those exact values.
	want32 := q3rat(-3, 2)
	want2 := q3i(2, 0)
	if !c.Equal(want32) && !c.Equal(want2) {
		t.Fatalf("unexpected constant generator %s; Or2's were -3/2 or 2", c.String())
	}
	t.Logf("production S_3/Z_3 MM system still infeasible-by-constant %s (matches Or2)", c.String())
}

// pointToVals parses a Sage variety point (var-name -> value string) into a Q3
// value vector indexed 0..nvars-1, succeeding only when every coordinate is
// expressible over Q(sqrt3).
func pointToVals(pt map[string]string, nvars int) ([]Q3, bool) {
	vals := make([]Q3, nvars)
	for i := 0; i < nvars; i++ {
		s, ok := pt[varName(i)]
		if !ok {
			return nil, false
		}
		v, ok := parseQ3(s)
		if !ok {
			return nil, false
		}
		vals[i] = v
	}
	return vals, true
}

// intPtr dereferences an *int for logging, or returns -1 for nil.
func intPtr(p *int) int {
	if p == nil {
		return -1
	}
	return *p
}
