/-
  Erdős Problem #376 — central binomial coefficients coprime to 105.
  Status: open; $1000 (Graham).  Tier UA attack target (the Kummer
  equivalence layer, not the headline).

  Verbatim statement (`goof erdos fetch 376`, pulled 2026-08-05):

    "Are there infinitely many $n$ such that $\binom{2n}{n}$ is coprime
    to $105$?"

  DB remarks: EGRS75 — for any two odd primes p, q there are infinitely
  many n with (pq, C(2n,n)) = 1.  Equivalent via Kummer's theorem to:
  infinitely many n with only digits {0,1} in base 3, digits {0,1,2} in
  base 5, and digits {0,1,2,3} in base 7 (i.e. all digits < p/2).
  Sequence: OEIS A030979 (pulled 2026-08-05: 0, 1, 10, 756, 757, 3160,
  3186, 3187, 3250, 7560, 7561, 7651, 20007, 59548377, …).
  Bloom–Croot [BlCr25]: for three sufficiently large primes, infinitely
  many n with the P-divisible part ≤ n^ε.  Graham's $1000 is for the
  headline.

  Audit verdict (candidates doc): headline demoted (multi-base digit
  distribution is deep); the deliverable is the Kummer equivalence
  itself — coprimality iff digit conditions — a finite carry-counting
  argument over `Nat.digits`, reusable for #175/#699/#1093–#1095.

  Mathlib inventory (leandoc 2026-08-05): `Nat.centralBinom`,
  `Nat.digits`, `Nat.Coprime`; Kummer's theorem partially present as
  `Nat.Prime.pow_dvd_choose`?? — the precise carry-count form
  (`padicValNat.choose`-family: `sub_one_mul_padicValNat_choose_eq...`)
  exists in Mathlib's `NumberTheory/Padics/PadicVal` as
  `padicValNat_choose` (Kummer's theorem: v_p(C(n+k,k)) = number of
  carries when adding k and n in base p).  Re-check exact name via
  leandoc at campaign start; repo also has Kummer-adjacent machinery in
  `Proofs/Erdos/Erdos175/NotSquarefree.lean`
  (`padicValNat_two_centralBinom`).
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E376

/-- `DigitsBelow b n B`: every base-`b` digit of `n` is `< B`. -/
def DigitsBelow (b n B : ℕ) : Prop :=
  ∀ d ∈ Nat.digits b n, d < B

/-- Ground truth for the digit predicate: `756 = (1000000)₃`… actually
    `756 = 2·3⁵ + 3⁴ + ... ` — pinned instead on a transparent case:
    `10 = (101)₃` has digits {1, 0, 1} all < 2.  -- PROVABLE (decide). -/
example : DigitsBelow 3 10 2 ∧ ¬ DigitsBelow 3 5 2 := by
  sorry

/-- **The Kummer bridge, single prime (the Tier-UA deliverable)**: for
    an odd prime `p`, `p` does not divide `C(2n, n)` iff every base-`p`
    digit of `n` is `< p/2` (no carry when adding `n + n` in base `p`).
    Stated multiplicatively (`2 * d < p`).

    Proof sketch: Kummer — `v_p(C(2n,n))` equals the number of carries
    in `n + n` base `p`; a carry occurs at position `i` iff the running
    digit sum ≥ p, and for doubling this happens iff some digit
    `≥ p/2` (a digit `< p/2` never produces a carry even with an
    incoming carry, since `2d + 1 < p`; induct on digit positions).
    Mathlib: `padicValNat_choose` / `Nat.Prime.factorization_choose`
    (Legendre) + `Nat.digits` API (`Nat.digits_add_two_add_one`,
    `Nat.sum_digits_eq_sum_digits_add_sum_carries`-shaped lemmas; if
    the carry-sum form is absent, prove via Legendre:
    `v_p(C(2n,n)) = Σ_i (⌊2n/p^i⌋ − 2⌊n/p^i⌋)` where each summand is
    the carry indicator).  Effort M; reusable layer. -/
theorem prime_not_dvd_centralBinom_iff_digits (p n : ℕ) (hp : p.Prime)
    (hodd : Odd p) :
    ¬ p ∣ Nat.centralBinom n ↔ ∀ d ∈ Nat.digits p n, 2 * d < p := by
  sorry

/-- The three-prime specialization: `C(2n,n)` coprime to `105 = 3·5·7`
    iff the digits of `n` are `{0,1}` base 3, `{0,1,2}` base 5,
    `{0,1,2,3}` base 7.  -- PROVABLE from the bridge (Coprime to a
    product = coprime to each factor; `Nat.Coprime.mul_right`). -/
theorem coprime_105_iff_digits (n : ℕ) :
    Nat.Coprime (Nat.centralBinom n) 105 ↔
      DigitsBelow 3 n 2 ∧ DigitsBelow 5 n 3 ∧ DigitsBelow 7 n 4 := by
  sorry

/-- Sanity certificates against A030979: `n = 1, 10, 756, 757` satisfy
    the coprimality; `n = 2` does not (`C(4,2) = 6`).
    -- PROVABLE (decide via the digit side; the binomial side for 756
    is astronomically large, which is exactly why the digit equivalence
    is the useful computational form). -/
example : DigitsBelow 3 756 2 ∧ DigitsBelow 5 756 3 ∧ DigitsBelow 7 756 4 ∧
    ¬ Nat.Coprime (Nat.centralBinom 2) 105 := by
  sorry

/-- **Erdős #376, headline (OPEN, $1000)**: infinitely many `n` with
    `C(2n,n)` coprime to 105.  Archived; the known A030979 terms grow
    doubly-exponentially sparse and the problem is expected true but
    deep. -/
theorem erdos_376 :
    {n : ℕ | Nat.Coprime (Nat.centralBinom n) 105}.Infinite := by
  sorry

/-- **EGRS two-prime theorem** (EGRS75), archived stretch goal: for any
    two odd primes `p, q`, infinitely many `n` have `C(2n,n)` coprime
    to `p*q`.  The construction interleaves base-p and base-q digit
    patterns; read the actual EGRS proof before scoping (flagged in the
    candidates audit). -/
theorem egrs_two_primes (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hop : Odd p) (hoq : Odd q) (hpq : p ≠ q) :
    {n : ℕ | Nat.Coprime (Nat.centralBinom n) (p * q)}.Infinite := by
  sorry

end ErdosCandidates.E376

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - DB statement matches file header verbatim.
   - Kummer bridge: ¬ p ∣ C(2n,n) ↔ ∀ d ∈ digits p n, 2*d < p.  Verified against
     OEIS A030979 comment ("all base-p digits of k are smaller than p/2") and carry
     analysis (no cascading carry issue: c_0 = 0 and 2*d < p at each position
     propagates c_{i+1} = 0).
   - coprime_105_iff_digits: 105 = 3*5*7; digit bounds {0,1} base 3, {0,1,2} base 5,
     {0,1,2,3} base 7 match 2*d < 3, 2*d < 5, 2*d < 7 respectively.
   - A030979 terms verified: OEIS returns 0,1,10,756,757,3160,... matching the file header.
   - n=756 digit conditions verified: base-3 digits all < 2, base-5 digits all < 3,
     base-7 digits all < 4.  n=2 sanity: C(4,2) = 6, gcd(6,105) = 3 ≠ 1.
   - EGRS two-prime theorem correctly attributed (EGRS75) with hypotheses Odd p, Odd q,
     p ≠ q.  The p ≠ q guard is needed (two copies of the same prime is trivial).
   - Graham $1000 attribution confirmed in DB.
   - Bloom-Croot [BlCr25] summary matches DB sections accurately.
-/
