package main

import (
	"testing"
)

// matStr renders a Mat compactly for diagnostics.
func matStr(m Mat) string {
	s := ""
	for i := 0; i < n; i++ {
		s += "["
		for j := 0; j < n; j++ {
			if j > 0 {
				s += " "
			}
			s += m[i][j].String()
		}
		s += "]"
	}
	return s
}

// TestDumpFixedBases prints the H-fixed seed-space bases for the stabilizer
// catalog, so the Os1 positive control can choose concrete seeds that lie in the
// actual fixed spaces. Diagnostic only (run with -v); no assertions beyond the
// dimension sanity already covered by TestFixedDims.
func TestDumpFixedBases(t *testing.T) {
	G := buildGroup()
	for _, ot := range orbitCatalog() {
		fb := fixedBasis(G, G.subgroup(ot.gens))
		t.Logf("%s (orbit %d): fixed dim %d", ot.name, ot.orbit, len(fb))
		for p, B := range fb {
			t.Logf("  B[%d] = %s", p, matStr(B))
		}
	}
}
