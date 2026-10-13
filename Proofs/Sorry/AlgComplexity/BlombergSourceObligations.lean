/-!
# A250109: Blomberg source obligations

DOCUMENTATION ONLY: this module has no imports, definitions, theorems or
admissions. It preserves the complete historical/source card from
Formalize/A250109-blomberg-recurrence.md. The sources are OEIS A250109,
Blomberg/Barker (2016-12-04), and van Heesch (2014), pp. 3-5 and Table 3.

Current evidence was read from Proofs/AlgComplexity/Blomberg.lean: integer
binomial-inversion coefficients, triangular reconstruction/uniqueness,
offset-three formulas, six-times cubics and the step-four recurrence are
proved there. This is a coefficient sequence arising from the study of
multiplicative complexity, not a minimum AND-gate count. The ambient diagonal
uses n >= 4; OEIS index r = n - 3 starts at r = 1. The recurrence is guarded
by ambient n >= 16, equivalently r > 12. Casting and finite triangular
uniqueness identify residues, not integer lifts. Even p > n is insufficient:
coefficient(1,4) = -8 and -8 is congruent to 2 modulo 5, with 5 > 4.

The current source reconciliation uses van Heesch's 2014 thesis
(http://alexandria.tue.nl/extra1/afstversl/wsk-i/heesch2014.pdf). Printed p. 3
says that for odd "large enough" p the mod-p calculation agrees with Z, but
gives no quantified bound. Theorem 1 on p. 4 gives the integer triangular
recurrence, and Remark 3 on p. 5 says the coefficients are independent of
ambient n. This identifies the source's integer-recursion interpretation
with the independent integer coefficients already proved in Blomberg.lean,
backed by its integer triangular reconstruction and uniqueness; it is not
recovery of arbitrary residues, and the residue caveat above remains.

Table 3 on printed p. 8, column x = 3, lists a^N_{i,i+3} for i >= 1,
beginning -8, 0, -20, -20, -64, -48, -120, -120, -232. The source indexing
is therefore reconciled as OEIS a(r) = coefficient(r,r+3) = diagonal(r+3),
r >= 1. This is source identification using the existing integer coefficient
results, not a new formal proof claim.

Barker's generating function remains empirical source metadata, uncertified
here. A minimum-complexity theorem would require a genuine circuit model and
optimization proof; it is not a prerequisite to the proved coefficient
identities. The verbatim card below is preserved historical state: its pending
integer/residue and indexing reconciliation is superseded by the present
source reconciliation. This documentation adds no admission or proof and
makes no blanket claim of full source closure.

## Formalize/A250109-blomberg-recurrence.md (verbatim)

```text
seq:     A250109
claim:   blomberg-empirical-recurrence
status:  integer coefficient formulas and recurrence proved;
         remaining source/interpretation boundary must be explicit
stmt:    L (historical complexity-model estimate, not recurrence prerequisite)
proof:   unknown (superseded historical estimate); coefficient unit now
         proved; no minimum-complexity theorem
module:  Proofs/AlgComplexity/Blomberg.lean
source:  OEIS A250109: Lars Blomberg formulas and recurrence, 2016-12-04;
         Colin Barker empirical generating function, 2016-12-04;
         van Heesch (2014), printed pp. 3-5 and Table 3, p. 8

SOURCE CLAIM AND INDEXING
  OEIS calls this a sequence ARISING FROM the study of multiplicative
  complexity of symmetric functions, not a minimum gate count itself.
  It lists empirical piecewise cubics by index modulo 4 and
    a(r) = 3*a(r-4) - 3*a(r-8) + a(r-12) - 64, r > 12,
  beginning a(1..12)=(-8,0,-20,-20,-64,-48,-120,-120,
                      -232,-208,-364,-364).
  The source reports a 5000-term empirical fit and still says
  "No recurrence is known"; these are historical source assertions.

LANDED COEFFICIENT UNIT
  Over the integers, define weight(i,w)=binomial(w,i) mod 2 and
    coefficient(i,k)=sum_{m=i}^k (-1)^(k-m)*binomial(k,m)*weight(i,m).
  Blomberg.lean proves integer triangular reconstruction and uniqueness,
  the four-term offset-three formula, six-times piecewise cubic formulas,
  and the step-four recurrence. Its diagonal uses ambient n >= 4:
    diagonal(n)=coefficient(n-3,n),  a(r)=diagonal(r+3).
  Thus the proved recurrence begins at ambient n >= 16, not n > 12.
  These are genuine integer coefficient identities, not complexity bounds.

REPRESENTATION BOUNDARY
  Casting preserves the triangular equations over any commutative ring;
  both reduction modulo p and finite triangular uniqueness are proved.
  Residues do not select integer lifts: already coefficient(1,4)=-8
  reduces to 2 modulo 5, and every 2+5t has that same residue. Requiring
  p>n does not recover -8. If integer recovery is required, specify a
  lift convention and prove a sufficient coefficient bound first.
  The integer definition is independent of such a recovery claim.

REMAINING DISPOSITION
  Reconcile the exact source's integer-versus-residue convention and
  OEIS index with the landed coefficient package before claiming full
  source closure. A separate minimum-multiplication theorem would require
  an actual circuit/straight-line model and optimization statement;
  neither the OEIS title nor this recurrence states or proves that claim.
  The old card incorrectly made a missing circuit model a prerequisite
  for all recurrence work. Do not restore that blanket blocker or replace
  circuit complexity with bilinear rank. Barker's empirical rational
  generating function is source metadata, not separately certified here.
```
-/
