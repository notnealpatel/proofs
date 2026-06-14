package main

// parseQ3 parses a Sage-emitted coordinate string into a Q3, succeeding only for
// values expressible over Q(sqrt 3). Sage variety points over QQbar print as
// decimal-ish algebraic reprs in general; we only accept exact rational / sqrt3
// forms (which is what genuine S_4 character-field solutions look like). On any
// unrecognized form we return ok=false and Stage 3 defers that point.
//
// Accepted forms (after stripping spaces), as sums of signed terms:
//   rational:        "3", "-1/2", "+7/3"
//   sqrt3 monomials: "sqrt3", "-sqrt3", "2*sqrt3", "-1/2*sqrt3"
// e.g. "-1/2*sqrt3 + 2"  ->  2 + (-1/2) sqrt3.

import (
	"math/big"
	"strings"
)

func parseQ3(s string) (Q3, bool) {
	s = strings.ReplaceAll(s, " ", "")
	if s == "" {
		return q3Zero, false
	}
	// split into signed terms
	terms := splitSignedTerms(s)
	a := big.NewRat(0, 1)
	b := big.NewRat(0, 1)
	for _, t := range terms {
		if t == "" {
			return q3Zero, false
		}
		neg := false
		switch t[0] {
		case '+':
			t = t[1:]
		case '-':
			neg = true
			t = t[1:]
		}
		isSqrt := false
		switch {
		case t == "sqrt3":
			t = "1"
			isSqrt = true
		case strings.HasSuffix(t, "*sqrt3"):
			t = strings.TrimSuffix(t, "*sqrt3")
			isSqrt = true
		}
		r, ok := new(big.Rat).SetString(t)
		if !ok {
			return q3Zero, false
		}
		if neg {
			r.Neg(r)
		}
		if isSqrt {
			b.Add(b, r)
		} else {
			a.Add(a, r)
		}
	}
	return q3(a, b), true
}

// splitSignedTerms splits a Sage scalar string into terms, keeping the leading
// sign of each. A leading term with no sign is returned as-is.
func splitSignedTerms(s string) []string {
	var terms []string
	start := 0
	for i := 1; i < len(s); i++ {
		if s[i] == '+' || s[i] == '-' {
			terms = append(terms, s[start:i])
			start = i
		}
	}
	terms = append(terms, s[start:])
	return terms
}
