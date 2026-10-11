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
