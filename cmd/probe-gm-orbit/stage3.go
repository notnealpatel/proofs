package main

// Stage 3: exact reconstruction and verification of a found solution. Given a
// solution point from Sage (variable -> value string), parse the coordinates
// over Q(sqrt 3) when possible, rebuild the concrete seeds, and check the full
// decomposition equals <3,3,3> exactly via verifyDecomposition. Returns
// (verified, true) when a Q(sqrt3) point was checked; (false, false) when no
// point was expressible over Q(sqrt3) (the variety lives in a larger field and
// the human/Stage-3 follow-up takes over).

// tryStage3 attempts exact verification from the first Sage solution point whose
// coordinates all lie in Q(sqrt3).
func tryStage3(G *Group, basisRR []Mat, pr pairChoice, sys *pairSystem, res *sageResult) (bool, bool) {
	fb1 := fixedBasis(G, G.subgroup(pr.t1.gens))
	fb2 := fixedBasis(G, G.subgroup(pr.t2.gens))
	for _, pt := range res.Points {
		vals := make([]Q3, sys.nvars)
		good := true
		for i := 0; i < sys.nvars; i++ {
			key := varName(i)
			s, ok := pt[key]
			if !ok {
				good = false
				break
			}
			v, ok := parseQ3(s)
			if !ok {
				good = false
				break
			}
			vals[i] = v
		}
		if !good {
			continue
		}
		m1 := seedFromParams(fb1, vals, 0)
		m2 := seedFromParams(fb2, vals, len(fb1))
		ok, _, _, _, _, _ := verifyDecomposition(G, []Mat{m1, m2})
		return ok, true
	}
	return false, false
}

// varName returns the Sage variable name for index i.
func varName(i int) string {
	return "x" + itoa(i)
}

// itoa is a tiny non-allocating-ish integer to string (avoids importing strconv
// here for a single use; small indices only).
func itoa(i int) string {
	if i == 0 {
		return "0"
	}
	var buf [4]byte
	pos := len(buf)
	for i > 0 {
		pos--
		buf[pos] = byte('0' + i%10)
		i /= 10
	}
	return string(buf[pos:])
}
