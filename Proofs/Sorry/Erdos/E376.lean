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

/-- Ground truth for the digit predicate: `756 = (1001000)₃ = 3⁶ + 3³`.
    The smaller case `10 = (101)₃` has digits {1, 0, 1} all < 2.
    -- PROVABLE (decide). -/
example : DigitsBelow 3 10 2 ∧ ¬ DigitsBelow 3 5 2 := by
  unfold DigitsBelow
  decide

/-- Doubling a digit list with no digit reaching half the base stays below its place bound. -/
private theorem double_ofDigits_lt (p : ℕ) (_hp : 2 ≤ p) (l : List ℕ)
    (hl : ∀ d ∈ l, 2 * d < p) : 2 * Nat.ofDigits p l < p ^ l.length := by
  induction l with
  | nil => simp
  | cons d l ih =>
    have hd : 2 * d < p := hl d (by simp)
    have ht : 2 * Nat.ofDigits p l < p ^ l.length :=
      ih (fun x hx => hl x (by simp [hx]))
    simp only [Nat.ofDigits_cons, List.length_cons, pow_succ]
    nlinarith

/-- Remainder bounds through a bound exceeding the digit length are equivalent to digit bounds. -/
private theorem remainder_iff_digits (p n b : ℕ) (hp : 2 ≤ p)
    (hb : (Nat.digits p n).length < b) :
    (∀ i ∈ Finset.Ico 1 b, 2 * (n % p ^ i) < p ^ i) ↔
      ∀ d ∈ Nat.digits p n, 2 * d < p := by
  constructor
  · intro h d hd
    obtain ⟨s, t, he⟩ := List.append_of_mem hd
    have hi : s.length + 1 ∈ Finset.Ico 1 b := by
      simp only [Finset.mem_Ico]
      have hlen : (Nat.digits p n).length = s.length + (1 + t.length) := by
        simp [he, Nat.add_comm]
      omega
    have hval := h (s.length + 1) hi
    rw [Nat.self_mod_pow_eq_ofDigits_take _ _ hp, he] at hval
    have ht : (s ++ d :: t).take (s.length + 1) = s ++ [d] := by
      rw [List.take_append]
      simp
    rw [ht, Nat.ofDigits_append] at hval
    simp only [Nat.ofDigits_cons, Nat.ofDigits_nil, mul_zero, add_zero, pow_succ] at hval
    have hpow : 0 < p ^ s.length := pow_pos (by omega) _
    have hm : (2 * d) * p ^ s.length < p * p ^ s.length := by
      calc
        (2 * d) * p ^ s.length ≤ 2 * (Nat.ofDigits p s + p ^ s.length * d) := by
          calc
            (2 * d) * p ^ s.length = 2 * (p ^ s.length * d) := by ring
            _ ≤ 2 * (Nat.ofDigits p s + p ^ s.length * d) :=
              Nat.mul_le_mul_left 2 (Nat.le_add_left _ _)
        _ < p * p ^ s.length := by simpa only [Nat.mul_comm] using hval
    exact (Nat.mul_lt_mul_right hpow).mp hm
  · intro h i hi
    rw [Nat.self_mod_pow_eq_ofDigits_take _ _ hp]
    have ht : 2 * Nat.ofDigits p ((Nat.digits p n).take i) <
        p ^ ((Nat.digits p n).take i).length :=
      double_ofDigits_lt p hp _ (fun d hd => h d (List.mem_of_mem_take hd))
    exact ht.trans_le (Nat.pow_le_pow_right (by omega) (List.length_take_le _ _))

/-- **The Kummer bridge, single prime (the Tier-UA deliverable)**: for
    an odd prime `p`, `p` does not divide `C(2n, n)` iff every base-`p`
    digit of `n` is `< p/2` (no carry when adding `n + n` in base `p`).
    Stated multiplicatively (`2 * d < p`).

    Proof sketch: Kummer — `v_p(C(2n,n))` equals the number of carries
    in `n + n` base `p`; at least one carry occurs iff some digit
    satisfies `p ≤ 2*d`. If every digit satisfies `2*d < p`, induction from the
    initial incoming carry `0` propagates carry `0` at every position.
    This does not assert `2*d + 1 < p` for an incoming carry `1`:
    that inequality fails at the maximal allowed digit of an odd base.
    Mathlib: `padicValNat_choose` / `Nat.Prime.factorization_choose`
    (Legendre) + `Nat.digits` API (`Nat.digits_add_two_add_one`,
    `Nat.sum_digits_eq_sum_digits_add_sum_carries`-shaped lemmas; if
    the carry-sum form is absent, prove via Legendre:
    `v_p(C(2n,n)) = Σ_i (⌊2n/p^i⌋ − 2⌊n/p^i⌋)` where each summand is
    the carry indicator).  Effort M; reusable layer. -/
theorem prime_not_dvd_centralBinom_iff_digits (p n : ℕ) (hp : p.Prime)
    (hodd : Odd p) :
    ¬ p ∣ Nat.centralBinom n ↔ ∀ d ∈ Nat.digits p n, 2 * d < p := by
  letI : Fact p.Prime := ⟨hp⟩
  let b := max (Nat.log p (n + n)) (Nat.digits p n).length + 1
  have hlog : Nat.log p (n + n) < b := by
    dsimp [b]
    omega
  have hlen : (Nat.digits p n).length < b := by
    dsimp [b]
    omega
  have hk := padicValNat_choose' (p := p) (n := n) (k := n) hlog
  have hcentral : Nat.centralBinom n = Nat.choose (n + n) n := by
    simp [Nat.centralBinom, two_mul]
  rw [dvd_iff_padicValNat_ne_zero (Nat.ne_of_gt (Nat.centralBinom_pos n))]
  rw [not_not, hcentral, hk]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp only [not_le, ← two_mul]
  exact remainder_iff_digits p n b hp.two_le hlen

/-- The three-prime specialization: `C(2n,n)` coprime to `105 = 3·5·7`
    iff the digits of `n` are `{0,1}` base 3, `{0,1,2}` base 5,
    `{0,1,2,3}` base 7.  -- PROVABLE from the bridge (Coprime to a
    product = coprime to each factor; `Nat.Coprime.mul_right`). -/
theorem coprime_105_iff_digits (n : ℕ) :
    Nat.Coprime (Nat.centralBinom n) 105 ↔
      DigitsBelow 3 n 2 ∧ DigitsBelow 5 n 3 ∧ DigitsBelow 7 n 4 := by
  have h3 : Nat.Prime 3 := by decide
  have h5 : Nat.Prime 5 := by decide
  have h7 : Nat.Prime 7 := by decide
  have hd3 : (∀ d ∈ Nat.digits 3 n, 2 * d < 3) ↔ DigitsBelow 3 n 2 := by
    unfold DigitsBelow
    constructor <;> intro h d hd <;> have hv := h d hd <;> omega
  have hd5 : (∀ d ∈ Nat.digits 5 n, 2 * d < 5) ↔ DigitsBelow 5 n 3 := by
    unfold DigitsBelow
    constructor <;> intro h d hd <;> have hv := h d hd <;> omega
  have hd7 : (∀ d ∈ Nat.digits 7 n, 2 * d < 7) ↔ DigitsBelow 7 n 4 := by
    unfold DigitsBelow
    constructor <;> intro h d hd <;> have hv := h d hd <;> omega
  change Nat.Coprime (Nat.centralBinom n) (3 * (5 * 7)) ↔ _
  rw [Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right]
  rw [Nat.coprime_comm (n := Nat.centralBinom n) (m := 3),
    Nat.coprime_comm (n := Nat.centralBinom n) (m := 5),
    Nat.coprime_comm (n := Nat.centralBinom n) (m := 7)]
  rw [h3.coprime_iff_not_dvd, h5.coprime_iff_not_dvd, h7.coprime_iff_not_dvd,
    prime_not_dvd_centralBinom_iff_digits 3 n h3 (by decide),
    prime_not_dvd_centralBinom_iff_digits 5 n h5 (by decide),
    prime_not_dvd_centralBinom_iff_digits 7 n h7 (by decide), hd3, hd5, hd7]

/-- Sanity certificates against A030979: `n = 1, 10, 756, 757` satisfy
    the coprimality; `n = 2` does not (`C(4,2) = 6`).
    -- PROVABLE (decide via the digit side; the binomial side for 756
    is astronomically large, which is exactly why the digit equivalence
    is the useful computational form). -/
example : DigitsBelow 3 756 2 ∧ DigitsBelow 5 756 3 ∧ DigitsBelow 7 756 4 ∧
    ¬ Nat.Coprime (Nat.centralBinom 2) 105 := by
  refine ⟨by unfold DigitsBelow; decide, by unfold DigitsBelow; decide,
    by unfold DigitsBelow; decide, ?_⟩
  rw [coprime_105_iff_digits]
  unfold DigitsBelow
  decide

/-- **Erdős #376, headline (OPEN, $1000)**: infinitely many `n` with
    `C(2n,n)` coprime to 105. Archived and not proved here. The live
    sources leave infinitude open; no growth-rate assertion is made. -/
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
