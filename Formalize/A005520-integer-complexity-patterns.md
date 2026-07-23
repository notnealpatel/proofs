seq:     A005520
claim:   record-holder-patterns
status:  open
stmt:    M
proof:   unknown
module:  none (shares defs with A005245 file)
source:  OEIS A005520 comments (patterns over known
         terms)

CLAIM
  A005520(n) = smallest number of integer complexity
  n (fewest 1's under +,*; see A005245 file for the
  def). Observed patterns asserted in-entry:
  (i) after 1438, all known terms through 8206559
  are prime; (ii) all known terms a(45)..a(89) are
  ≡ -1 mod 120.

LEAN
  Same integer-complexity def as
  A005245-hamilton-ballinger.md, plus argmin/least
  element via Nat.find. Statements are then direct.

ROUTE
  No structural explanation known for either pattern;
  this is conjecture-mining raw material rather than
  a burndown target. Computational extension is the
  next signal (record tables exist in the literature
  around the entry).

EVIDENCE
  Patterns hold over all computed record terms
  per entry.
