package main

// Cheap necessary-condition scan, used ONLY to cross-check Sage (which owns the
// Stage-2 verdict per Hu7). If the constraint system contains a nonzero CONSTANT
// generator c != 0, that constant is a unit in the ideal, so the ideal is the
// whole ring and the system is infeasible. This is a trivial special case of the
// unit ideal -- the full decision is Sage's Groebner basis -- but it is a useful
// independent sanity signal and explains the geometry: it arises whenever some
// rho⊗rho* basis triple (A,B,C) has an identically-zero orbit contribution
// (every frobPoly factor vanishes symbolically over the H-fixed seed spaces) yet
// a nonzero tr(A)tr(B)tr(C) - tr(ABC) residual, i.e. that Fourier projection is
// unreachable from the restricted seed spaces.

// constantInfeasible reports whether sys has a nonzero constant generator, and
// returns the certificate value (the constant) when so.
func constantInfeasible(sys *pairSystem) (bool, Q3) {
	for _, p := range sys.polys {
		if polyDegree(p) == 0 {
			// degree 0 and nonzero (isZero polys are never emitted)
			if t, ok := p.terms[""]; ok && !t.coeff.IsZero() {
				return true, t.coeff
			}
		}
	}
	return false, q3Zero
}
