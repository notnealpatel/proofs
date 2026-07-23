seq:     A002804
claim:   euler-ideal-waring
status:  open (classical)
stmt:    S
proof:   hard-open
module:  Proofs/CHILO/ConnerWaring.lean (Waring-rank
         cousin; NO inference between integer Waring
         and Waring rank of forms)
source:  OEIS A002804 comments (formula conjectured
         correct for all n; Mahler finiteness noted
         by Tomohiro Yamada 2017-09-23); cf. A174420

CLAIM
  g(n) = 2^n + floor((3/2)^n) - 2 is the exact
  Waring number (every positive integer is a sum of
  g(n) n-th powers, g minimal) for ALL n. Equivalent
  to the ideal-Waring inequality
    frac((3/2)^n) <= 1 - (3/4)^n * ...
  (A174420 encodes the deficit; >= 0 for n >= 3 is
  the conjecture). Mahler: at most finitely many
  exceptions; none known; verified to
  n <= 471,600,000.

LEAN
  Statement S: Nat.pow, Int.floor/fract vocabulary
  only (for the inequality form). The full "g(n) is
  the Waring number" statement needs a Waring-number
  def (sup over deficient integers) — still S-M.

ROUTE
  Open (effective Mahler is the blocker in the
  literature). Statement-archive.

EVIDENCE
  Kubina-Wunderlich verification to 4.7 * 10^8.
