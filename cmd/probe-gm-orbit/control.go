package main

// Os1 positive/negative control support: drive the SAME verdict-producing path
// (buildPairSystemTarget -> sageScript -> Sage Groebner -> SOLUTION-FOUND ->
// seedFromParams -> reconstruct) against a target tensor that is feasible BY
// CONSTRUCTION, closing the Stage-0 multi-orbit anchor gap that Or2 flagged.
//
// The Or2 probe only ever exercised the INFEASIBLE branch (all 18 pairs were
// unit ideals), so the SOLUTION-FOUND -> reconstruct round-trip never fired on
// the real run. These helpers fire it on a must-succeed input.

// verifyAgainstTarget checks <T_ansatz, A⊗B⊗C> == targetInner(A,B,C) for all 729
// basis triples (A,B,C) over the rho⊗rho* test basis, for concrete seeds. This
// is the target-parameterized analogue of verifyDecomposition (which hardcodes
// the MM target trProd). Equality on the full informative basis certifies
// T_ansatz = T exactly. Returns the first offending triple on failure.
func verifyAgainstTarget(G *Group, basisRR []Mat, seeds []Mat, targetInner func(A, B, C Mat) Q3) (ok bool, badA, badB, badC int, got, want Q3) {
	for ai := range basisRR {
		for bi := range basisRR {
			for ci := range basisRR {
				g := ansatzInner(G, seeds, basisRR[ai], basisRR[bi], basisRR[ci])
				w := targetInner(basisRR[ai], basisRR[bi], basisRR[ci])
				if !g.Equal(w) {
					return false, ai, bi, ci, g, w
				}
			}
		}
	}
	return true, 0, 0, 0, q3Zero, q3Zero
}

// targetFromSeeds returns the inner-product functional <T', A⊗B⊗C> for the
// tensor T' = id^⊗3 + sum_k orbit(m1_k) built from the concrete seeds via the
// SAME ansatzInner used in reconstruction. By construction the constraint system
// buildPairSystemTarget produces for this target vanishes at the parameters of
// these seeds, so it is feasible (variety non-empty) and cannot be the unit
// ideal.
func targetFromSeeds(G *Group, seeds []Mat) func(A, B, C Mat) Q3 {
	return func(A, B, C Mat) Q3 {
		return ansatzInner(G, seeds, A, B, C)
	}
}

// allConstraintsVanishAt reports whether every constraint polynomial of sys is
// zero at the parameter assignment vals (the by-construction feasibility check,
// independent of Sage). Returns the index of the first non-vanishing polynomial
// and its value when not all vanish.
func allConstraintsVanishAt(sys *pairSystem, vals []Q3) (bool, int, Q3) {
	for i, p := range sys.polys {
		v := evalPoly(p, vals)
		if !v.IsZero() {
			return false, i, v
		}
	}
	return true, -1, q3Zero
}

// perturbTargetOnTriple returns a target functional equal to base everywhere
// except it adds eps to the value on the single basis triple (pa,pb,pc) (indices
// into basisRR). When (pa,pb,pc) is an OBSTRUCTED triple (orbit term identically
// zero) this introduces a nonzero constant generator into the constraint system,
// driving it to the unit ideal => INFEASIBLE. This is the negative control: it
// pulls the SAME lever (constant on an unreachable Fourier projection) that
// produced Or2's 18 verdicts, but starting from a feasible target, so the
// verdict provably FLIPS from SOLUTION-FOUND to INFEASIBLE.
func perturbTargetOnTriple(basisRR []Mat, base func(A, B, C Mat) Q3, pa, pb, pc int, eps Q3) func(A, B, C Mat) Q3 {
	return func(A, B, C Mat) Q3 {
		v := base(A, B, C)
		if matEq(A, basisRR[pa]) && matEq(B, basisRR[pb]) && matEq(C, basisRR[pc]) {
			v = v.Add(eps)
		}
		return v
	}
}

// matEq is equalMat under a name local to the control helpers.
func matEq(a, b Mat) bool { return equalMat(a, b) }

// q3VecEqual reports whether two Q3 vectors are equal entrywise (same length
// assumed; false if lengths differ).
func q3VecEqual(a, b []Q3) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if !a[i].Equal(b[i]) {
			return false
		}
	}
	return true
}

// orbitContributes reports whether the S_4 orbit of the single seed m (with its
// sigma-twisted partners) has a nonzero Frobenius contribution on at least one
// rho⊗rho* basis triple, i.e. whether ansatzInner(G,[m],A,B,C) differs from the
// bare id^⊗3 value tr(A)tr(B)tr(C) somewhere. Used to certify that both orbits
// of the positive control genuinely participate (the two-orbit path is real, not
// a disguised single-orbit case).
func orbitContributes(G *Group, basisRR []Mat, m Mat) bool {
	for ai := range basisRR {
		for bi := range basisRR {
			for ci := range basisRR {
				A, B, C := basisRR[ai], basisRR[bi], basisRR[ci]
				inner := ansatzInner(G, []Mat{m}, A, B, C)
				id3 := trace(A).Mul(trace(B)).Mul(trace(C))
				if !inner.Sub(id3).IsZero() {
					return true
				}
			}
		}
	}
	return false
}

// q3VecStr renders a Q3 vector compactly, e.g. "(1, 2, -1, 1, 1)".
func q3VecStr(v []Q3) string {
	s := "("
	for i, x := range v {
		if i > 0 {
			s += ", "
		}
		s += x.String()
	}
	return s + ")"
}
