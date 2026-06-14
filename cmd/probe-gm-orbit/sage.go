package main

// Stage 2: emit a pairSystem as a SageMath script that computes a Groebner basis
// of the constraint ideal over Q(sqrt 3), and decides feasibility:
//   - "1" in the basis  => unit ideal => INFEASIBLE (no decomposition exists).
//   - dimension >= 0     => SOLUTION-FOUND (a variety exists); we also dump the
//                           Groebner basis and, when zero-dimensional, the
//                           variety points for Stage 3 reconstruction.
// Per Hu7 (route A-hybrid) the Go program shells out to `sager -c "<script>"`.

import (
	"fmt"
	"sort"
	"strings"
)

// sageScript renders the Sage program for a system. It defines the polynomial
// ring K[x0..x{n-1}] with K = Q(sqrt3), builds the ideal, and prints a JSON
// line with the verdict.
func sageScript(sys *pairSystem) string {
	var b strings.Builder
	b.WriteString("import json\n")
	b.WriteString("K.<sqrt3> = QuadraticField(3)\n")
	if sys.nvars == 0 {
		// No free parameters: the only candidate is the all-zero seed, i.e.
		// id^⊗3 alone, which is not MM. Treat as trivially infeasible unless all
		// constants vanish. Encode as constants-only ideal.
		b.WriteString("R = K\n")
	} else {
		vars := make([]string, sys.nvars)
		for i := range vars {
			vars[i] = fmt.Sprintf("x%d", i)
		}
		fmt.Fprintf(&b, "R = PolynomialRing(K, %d, %q)\n", sys.nvars, strings.Join(vars, ","))
		fmt.Fprintf(&b, "%s = R.gens()\n", strings.Join(vars, ","))
	}
	b.WriteString("gens = [\n")
	for _, p := range sys.polys {
		fmt.Fprintf(&b, "  %s,\n", polyToSage(p))
	}
	b.WriteString("]\n")
	b.WriteString(sageDriver)
	return b.String()
}

// sageDriver is the fixed analysis tail appended after `gens = [...]`.
const sageDriver = `
if len(gens) == 0:
    print(json.dumps({"verdict":"DEGENERATE","reason":"no constraints"}))
else:
    I = R.ideal(gens)
    try:
        gb = I.groebner_basis()
    except Exception as e:
        print(json.dumps({"verdict":"ERROR","reason":str(e)}))
    else:
        gbs = [str(g) for g in gb]
        is_unit = (R.one() in I) if hasattr(R,'one') else any(str(g)=="1" for g in gb)
        if is_unit:
            print(json.dumps({"verdict":"INFEASIBLE","groebner":gbs}))
        else:
            try:
                d = I.dimension()
            except Exception as e:
                d = None
            out = {"verdict":"SOLUTION-FOUND","dimension":(int(d) if d is not None else None),"groebner":gbs}
            if d == 0:
                try:
                    V = I.variety(ring=QQbar)
                    out["num_points"] = len(V)
                    pts = []
                    for sol in V[:8]:
                        pts.append({str(k): str(v) for k,v in sol.items()})
                    out["points"] = pts
                except Exception as e:
                    out["variety_error"] = str(e)
            print(json.dumps(out))
`

// polyToSage renders a Poly as a Sage expression string in variables x0..x{k}.
// Coefficients are Q3 elements rendered with sqrt3 (Sage's generator name).
func polyToSage(p *Poly) string {
	if p.isZero() {
		return "R(0)"
	}
	// deterministic order for reproducible scripts
	keys := make([]string, 0, len(p.terms))
	for k := range p.terms {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	parts := make([]string, 0, len(keys))
	for _, k := range keys {
		t := p.terms[k]
		coeff := q3ToSage(t.coeff)
		if len(t.mono) == 0 {
			parts = append(parts, fmt.Sprintf("(%s)", coeff))
			continue
		}
		mono := make([]string, len(t.mono))
		for i, v := range t.mono {
			mono[i] = fmt.Sprintf("x%d", v)
		}
		parts = append(parts, fmt.Sprintf("(%s)*%s", coeff, strings.Join(mono, "*")))
	}
	return strings.Join(parts, " + ")
}

// q3ToSage renders a Q3 coefficient using Sage's `sqrt3` generator.
func q3ToSage(c Q3) string {
	switch {
	case c.B.Sign() == 0:
		return c.A.RatString()
	case c.A.Sign() == 0:
		return fmt.Sprintf("(%s)*sqrt3", c.B.RatString())
	default:
		return fmt.Sprintf("(%s) + (%s)*sqrt3", c.A.RatString(), c.B.RatString())
	}
}
