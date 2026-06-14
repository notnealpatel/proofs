package main

// Sparse multivariate polynomials over K = Q(sqrt 3) in the seed parameters.
// Variables are indexed 0..nvars-1 (the concatenated free parameters of the two
// orbit seeds). A monomial is the sorted multiset of variable indices; we key it
// by a canonical string. Degree never exceeds 3 (one linear factor per orbit
// term in the cubic constraint), so this representation stays tiny.

import (
	"sort"
	"strconv"
	"strings"
)

// monomial is a sorted slice of variable indices (with repetition). The empty
// slice is the constant monomial 1.
type monomial []int

func (m monomial) key() string {
	if len(m) == 0 {
		return ""
	}
	parts := make([]string, len(m))
	for i, v := range m {
		parts[i] = strconv.Itoa(v)
	}
	return strings.Join(parts, ",")
}

// mulMono returns the sorted product of two monomials.
func mulMono(a, b monomial) monomial {
	out := make(monomial, 0, len(a)+len(b))
	out = append(out, a...)
	out = append(out, b...)
	sort.Ints(out)
	return out
}

// Poly is a sparse polynomial: monomial-key -> (monomial, coefficient).
type Poly struct {
	terms map[string]polyTerm
}

type polyTerm struct {
	mono  monomial
	coeff Q3
}

func newPoly() *Poly { return &Poly{terms: map[string]polyTerm{}} }

// constPoly returns the constant polynomial c.
func constPoly(c Q3) *Poly {
	p := newPoly()
	if !c.IsZero() {
		p.terms[""] = polyTerm{mono: monomial{}, coeff: c}
	}
	return p
}

// varPoly returns the degree-1 polynomial x_i.
func varPoly(i int) *Poly {
	p := newPoly()
	m := monomial{i}
	p.terms[m.key()] = polyTerm{mono: m, coeff: q3One}
	return p
}

// addTerm accumulates coeff*mono into p (in place).
func (p *Poly) addTerm(mono monomial, coeff Q3) {
	if coeff.IsZero() {
		return
	}
	k := mono.key()
	if t, ok := p.terms[k]; ok {
		nc := t.coeff.Add(coeff)
		if nc.IsZero() {
			delete(p.terms, k)
		} else {
			p.terms[k] = polyTerm{mono: mono, coeff: nc}
		}
	} else {
		p.terms[k] = polyTerm{mono: mono, coeff: coeff}
	}
}

// addPoly returns p+q (new polynomial).
func addPoly(p, q *Poly) *Poly {
	r := newPoly()
	for _, t := range p.terms {
		r.addTerm(t.mono, t.coeff)
	}
	for _, t := range q.terms {
		r.addTerm(t.mono, t.coeff)
	}
	return r
}

// scalePoly returns c*p.
func scalePoly(c Q3, p *Poly) *Poly {
	r := newPoly()
	if c.IsZero() {
		return r
	}
	for _, t := range p.terms {
		r.addTerm(t.mono, c.Mul(t.coeff))
	}
	return r
}

// mulPoly returns p*q.
func mulPoly(p, q *Poly) *Poly {
	r := newPoly()
	for _, tp := range p.terms {
		for _, tq := range q.terms {
			r.addTerm(mulMono(tp.mono, tq.mono), tp.coeff.Mul(tq.coeff))
		}
	}
	return r
}

// isZero reports whether p is the zero polynomial (used to discard the trivially
// satisfied constraints 0 = 0).
func (p *Poly) isZero() bool { return len(p.terms) == 0 }
