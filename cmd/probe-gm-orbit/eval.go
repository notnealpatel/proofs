package main

// evalPoly evaluates p at the given variable assignment vals (vals[i] = value of
// variable i) over K. Used to cross-check the symbolic Stage-1 system against
// the concrete Stage-0/3 reconstruction.
func evalPoly(p *Poly, vals []Q3) Q3 {
	acc := q3Zero
	for _, t := range p.terms {
		prod := t.coeff
		for _, v := range t.mono {
			prod = prod.Mul(vals[v])
		}
		acc = acc.Add(prod)
	}
	return acc
}

// seedFromParams reconstructs the concrete seed m1 = sum_p vals[base+p]*basis[p]
// for an orbit, given its fixed-space basis and parameter values.
func seedFromParams(basis []Mat, vals []Q3, base int) Mat {
	m := zeroMat()
	for p, B := range basis {
		m = addMat(m, scaleMat(vals[base+p], B))
	}
	return m
}
