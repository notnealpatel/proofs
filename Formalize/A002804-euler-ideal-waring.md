seq:     A002804
claim:   euler-ideal-waring
status:  open mathematics; faithful admission boundary implemented
stmt:    S (original estimate; genuine integer Waring definitions now exist)
proof:   hard-open
module:  Proofs/Enumerative/IdealWaring.lean;
         archive Proofs/Sorry/Enumerative/IdealWaring.lean
source:  OEIS A002804 comments; Mahler finiteness noted by
         Tomohiro Yamada, 2017-09-23; cf. A174420

EXACT CLAIM
  For every positive exponent n, the genuine integer Waring number is
    g(n) = 2^n + floor((3/2)^n) - 2.
  WaringAdmissible n s means every natural number is a sum of at most
  s n-th powers; the production module uses actual multisets and defines
  waringG by Nat.sInf with attainment/nonemptiness guards on its lemmas.
  The exact archived domain is n != 0. In particular idealWaring(1)=1,
  not 0; the independent exponent-one and exponent-two cases are proved.
  Integer Waring numbers are not Waring ranks of homogeneous forms.
  Proofs/CHILO/ConnerWaring.lean does not supply an inference between them.

ARITHMETIC ROUTE AND LIMITS
  Write 3^n=q*2^n+r with 0 <= r < 2^n. The ideal-Waring inequality is
  q+r <= 2^n. For n>0 its exact fractional-part threshold is
    frac((3/2)^n) <= (1-(3/4)^n)/(1-2^(-n)).
  The smaller bound 1-(3/4)^n is only sufficient. The former card's
  ellipsis was not an exact formula. The published conditional Waring
  engine relating this arithmetic to the upper bound is not locally proved.
  Mahler's finite-exception result and the external Kubina-Wunderlich
  computation through n=471600000 do not prove the uniform conjecture;
  the computation has not been replayed as a local Lean certificate.

IMPLEMENTATION STATUS
  Production defines the genuine objects and proves independent lower
  bounds, existence-guarded sInf facts, and the n=1,2 cases. The accepted
  admission split moves exactly waringAdmissible_idealWaring and its
  dependent waringG_eq_idealWaring to the matching Sorry module. The build,
  fresh all-owned production axiom audit, and separate archive signature
  audit and independent review passed; the boundary was adopted at
  3935f8aa7ad524d66da0c83342120e9ac62f779a. This card remains for
  metadata reconciliation before retirement. Acceptance is implementation, not a
  proof of the open formula or of the locally unformalized conditional engine.
