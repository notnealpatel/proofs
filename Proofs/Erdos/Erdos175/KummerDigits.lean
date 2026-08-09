/-
  Kummer's theorem — the base-`p` digit/carry layer.

  ══════════════════════════════════════════════════════════════════════
  SCOPE NOTE (read before citing this file)
  ══════════════════════════════════════════════════════════════════════

  Kummer's theorem itself is ALREADY IN MATHLIB, four times over, in
  `.lake/packages/mathlib/Mathlib/NumberTheory/Padics/PadicVal/Basic.lean`
  lines 612-657 (read 2026-08-05).  The two that matter here, reproduced line
  for line with a six-space quoting indent added and the proof bodies elided.
  Lines 622-628:

      /-- **Kummer's Theorem**

      The `p`-adic valuation of `(n + k).choose k` is the number of carries when `k` and `n` are added
      in base `p`. This sum is expressed over the finset `Ico 1 b` where `b` is any bound greater than
      `log p (n + k)`. -/
      theorem padicValNat_choose' {n k b : ℕ} [hp : Fact p.Prime] (hnb : log p (n + k) < b) :
          padicValNat p (choose (n + k) k) = #{i ∈ Finset.Ico 1 b | p ^ i ≤ k % p ^ i + n % p ^ i} := by

  Lines 632-638:

      /-- **Kummer's Theorem**
      Taking (`p - 1`) times the `p`-adic valuation of the binomial `n + k` over `k` equals the sum of the
      digits of `k` plus the sum of the digits of `n` minus the sum of digits of `n + k`, all base `p`.
      -/
      theorem sub_one_mul_padicValNat_choose_eq_sub_sum_digits' {k n : ℕ} [hp : Fact p.Prime] :
          (p - 1) * padicValNat p (choose (n + k) k) =
          (p.digits k).sum + (p.digits n).sum - (p.digits (n + k)).sum := by

  What Mathlib does NOT have — verified by `grep -rn "carr" Mathlib/Data/Nat/Digits/
  Mathlib/Data/Nat/Multiplicity.lean Mathlib/NumberTheory/Padics/PadicVal/
  Mathlib/Data/Nat/Choose/` on 2026-08-05, which returns only the eight
  docstring occurrences of the English word "carries" and no definition — is an
  actual carry function: the digitwise recursion

      c₀ = 0,   c_{i+1} = 1  iff  p ≤ mᵢ + nᵢ + cᵢ

  that the phrase "number of carries" names.  Mathlib states Kummer with the
  closed-form predicate `p ^ i ≤ k % p ^ i + n % p ^ i` instead.  THAT GAP is
  what this file closes:

  * `carry` — the digitwise carry recursion, as a `Bool`-valued function.
  * `carry_eq_true_iff` — the bridge `carry p m n i = true ↔
    p ^ i ≤ m % p ^ i + n % p ^ i`, which is what makes the two presentations
    interchangeable.
  * `padicValNat_choose_add_eq_card_carries` — Kummer restated over `carry`.
  * `prime_not_dvd_choose_add_iff_digitwise` — Kummer's carry-free criterion:
    `p ∤ C(m+n, m)` iff every base-`p` digit pair sums to less than `p`.
  * `prime_not_dvd_centralBinom_iff_digits` — the specialization used
    downstream: `p ∤ C(2n,n)` iff every base-`p` digit of `n` is `< p/2`.
  * `forall_div_pow_mod_iff_forall_mem_digits` — the general bridge between
    indexed digits `n / b ^ i % b` and `Nat.digits` list membership.

  ══════════════════════════════════════════════════════════════════════
  SOURCE PINS
  ══════════════════════════════════════════════════════════════════════

  Every quotation below is byte-exact, one source line per quoted line, with a
  six-space quoting indent added and nothing rewrapped.

  Erdős Problem #376 (`goof erdos fetch 376`, pulled 2026-08-05), the
  `statement` field:

      Are there infinitely many $n$ such that $\binom{2n}{n}$ is coprime to $105$?

  and the second paragraph of `sections[0]` of the same record:

      This is equivalent (via Kummer's theorem) to whether there are infinitely many $n$ which have only digits $0,1$ in base $3$, digits $0,1,2$ in base $5$, and digits $0,1,2,3$ in base $7$.

  OEIS A030979 (`goof oeis show A030979`, pulled 2026-08-05), the `name` field:

      Numbers k such that binomial(2k,k) is not divisible by 3, 5 or 7.

  and `comments[0]`:

      By Lucas's theorem, binomial(2k,k) is not divisible by a prime p iff all base-p digits of k are smaller than p/2.

  and `comments[2]`, which pins what is and is not open here:

      The Erdős et al. paper shows that for any two odd primes p and q there are an infinite number of k for which gcd(p*q,binomial(2k,k))=1; i.e., p and q do not divide binomial(2k,k). The paper does not deal with the case of three primes. - _T. D. Noe_, Apr 18 2007

  `prime_not_dvd_centralBinom_iff_digits` is exactly that comment, with
  "smaller than p/2" spelled `2 * d < p` to stay inside `ℕ` (no division), and
  proved from Kummer rather than Lucas.  Note it needs no `Odd p` hypothesis:
  at `p = 2` both sides say `n = 0`.

  ══════════════════════════════════════════════════════════════════════
  HONEST CLAIM BOUNDARY
  ══════════════════════════════════════════════════════════════════════

  Erdős #376 itself (Graham's $1000 question, whether infinitely many such `n`
  exist) is NOT proved here and is not attempted.  Nothing in this file is an
  advance on the open problem; it is the elementary equivalence layer that the
  problem statement's word "equivalent" refers to.

  No `native_decide`, no `axiom`, no `sorry`; see the `#print axioms` block at
  the end of the file.
-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.GetD

set_option autoImplicit false

namespace Erdos175

-- ════════════════════════════════════════════════════════════════════
-- §1 INDEXED DIGITS VERSUS `Nat.digits` MEMBERSHIP
-- ════════════════════════════════════════════════════════════════════

/-- A predicate holds at every indexed base-`b` digit `n / b ^ i % b` of `n`
    iff it holds at every member of `Nat.digits b n`, provided it holds at `0`.

    The `P 0` hypothesis is necessary and not cosmetic: indices `i` beyond the
    length of `Nat.digits b n` contribute the digit `0`, which is not a list
    member (`Nat.digits b n` has no trailing zeros). -/
theorem forall_div_pow_mod_iff_forall_mem_digits {b : ℕ} (hb : 2 ≤ b) (n : ℕ)
    (P : ℕ → Prop) (h0 : P 0) :
    (∀ i, P (n / b ^ i % b)) ↔ ∀ d ∈ Nat.digits b n, P d := by
  constructor
  · intro h d hd
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
    have hkey : (Nat.digits b n)[i] = n / b ^ i % b := by
      rw [← List.getD_eq_getElem (Nat.digits b n) 0 hi, Nat.getD_digits n i hb]
    rw [hkey]
    exact h i
  · intro h i
    rw [← Nat.getD_digits n i hb]
    by_cases hi : i < (Nat.digits b n).length
    · rw [List.getD_eq_getElem (Nat.digits b n) 0 hi]
      exact h _ (List.getElem_mem hi)
    · rw [List.getD_eq_default (Nat.digits b n) 0 (by omega)]
      exact h0

-- ════════════════════════════════════════════════════════════════════
-- §2 THE CARRY RECURSION
-- ════════════════════════════════════════════════════════════════════

/-- `carry p m n i` is `true` exactly when adding `m` and `n` in base `p`
    produces a carry *into* digit position `i`.  Schoolbook recursion: there
    is no carry into the units place, and there is a carry into place `i + 1`
    iff the two base-`p` digits at place `i` together with the incoming carry
    reach `p`. -/
def carry (p m n : ℕ) : ℕ → Bool
  | 0 => false
  | i + 1 => decide (p ≤ m / p ^ i % p + n / p ^ i % p + (carry p m n i).toNat)

/-- There is never a carry into the units place. -/
@[simp] theorem carry_zero (p m n : ℕ) : carry p m n 0 = false := rfl

/-- The schoolbook carry recursion, as an equation. -/
theorem carry_succ (p m n i : ℕ) :
    carry p m n (i + 1) =
      decide (p ≤ m / p ^ i % p + n / p ^ i % p + (carry p m n i).toNat) :=
  rfl

/-- Ground truth for `carry`, base ten: `47 + 58 = 105` carries out of the
    units place (`7 + 8 = 15`) and out of the tens place (`4 + 5 + 1 = 10`),
    and no further. -/
example : carry 10 47 58 0 = false ∧ carry 10 47 58 1 = true ∧
    carry 10 47 58 2 = true ∧ carry 10 47 58 3 = false := by decide

/-- Ground truth for `carry`, base three: `7 = (21)₃` and `5 = (12)₃` add with
    carries into places `1` and `2`, matching `C(12,7) = 792 = 2³ · 3² · 11`,
    whose `3`-adic valuation is `2`. -/
example : carry 3 7 5 1 = true ∧ carry 3 7 5 2 = true ∧
    carry 3 7 5 3 = false ∧ Nat.choose 12 7 = 792 := by decide

/-- Boundary: `m = 0` never carries. -/
example : ∀ i ∈ Finset.range 6, carry 10 0 58 i = false := by decide

/-- Boundary: `n = 0` never carries. -/
example : ∀ i ∈ Finset.range 6, carry 10 47 0 i = false := by decide

/-- Degenerate base `p = 0`: `0^1 = 0 ≤ m + n` so place 1 always carries. -/
example : carry 0 3 4 0 = false ∧ carry 0 3 4 1 = true := by decide

/-- Degenerate base `p = 1`: digits in base 1 are all 0, no carry. -/
example : ∀ i ∈ Finset.range 6, carry 1 3 4 i = false := by decide

/-- **The bridge to Mathlib's presentation of Kummer.**  The digitwise carry
    recursion agrees with the closed-form carry predicate
    `p ^ i ≤ m % p ^ i + n % p ^ i` that Mathlib's `padicValNat_choose'` uses. -/
theorem carry_eq_true_iff {p : ℕ} (hp : 1 < p) (m n i : ℕ) :
    carry p m n i = true ↔ p ^ i ≤ m % p ^ i + n % p ^ i := by
  induction i with
  | zero => simp [Nat.mod_one]
  | succ i ih =>
    have hp0 : 0 < p := by omega
    have hpi : 0 < p ^ i := pow_pos hp0 i
    -- The low part `A` of the two summands is `< 2 * p ^ i`, so `A / p ^ i`
    -- is the incoming carry bit.
    have hAlt : m % p ^ i + n % p ^ i < 2 * p ^ i := by
      have h1 : m % p ^ i < p ^ i := Nat.mod_lt _ hpi
      have h2 : n % p ^ i < p ^ i := Nat.mod_lt _ hpi
      omega
    have hdiv : (m % p ^ i + n % p ^ i) / p ^ i = (carry p m n i).toNat := by
      rcases Bool.eq_false_or_eq_true (carry p m n i) with hc | hc
      · rw [hc, Bool.toNat_true]
        refine Nat.div_eq_of_lt_le ?_ (by omega)
        simpa using ih.mp hc
      · rw [hc, Bool.toNat_false]
        refine Nat.div_eq_of_lt ?_
        have hlt : ¬ (p ^ i ≤ m % p ^ i + n % p ^ i) := by rw [← ih, hc]; simp
        omega
    -- Peel the top digit off each summand.
    have hX : m % p ^ (i + 1) + n % p ^ (i + 1) =
        (m % p ^ i + n % p ^ i) + p ^ i * (m / p ^ i % p + n / p ^ i % p) := by
      rw [Nat.mod_pow_succ, Nat.mod_pow_succ]; ring
    have hkey : p ^ (i + 1) ≤ m % p ^ (i + 1) + n % p ^ (i + 1) ↔
        p ≤ (carry p m n i).toNat + (m / p ^ i % p + n / p ^ i % p) := by
      rw [hX, pow_succ', ← Nat.le_div_iff_mul_le hpi,
        Nat.add_mul_div_left _ _ hpi, hdiv]
    rw [hkey, carry_succ, decide_eq_true_iff]
    omega

/-- Contrapositive form of `carry_eq_true_iff`. -/
theorem carry_eq_false_iff {p : ℕ} (hp : 1 < p) (m n i : ℕ) :
    carry p m n i = false ↔ m % p ^ i + n % p ^ i < p ^ i := by
  rw [← Bool.not_eq_true, carry_eq_true_iff hp]
  omega

/-- Carries stop once the place value exceeds the sum. -/
theorem carry_eq_false_of_add_lt {p m n i : ℕ} (hp : 1 < p) (h : m + n < p ^ i) :
    carry p m n i = false := by
  rw [carry_eq_false_iff hp, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- **Carry-free addition is digitwise addition.**  Adding `m` and `n` in
    base `p` produces no carry at all iff every pair of digits in the same
    place sums to less than `p`. -/
theorem forall_carry_eq_false_iff (p m n : ℕ) :
    (∀ i, carry p m n i = false) ↔ ∀ i, m / p ^ i % p + n / p ^ i % p < p := by
  constructor
  · intro h i
    have h1 := h (i + 1)
    rw [carry_succ, h i, Bool.toNat_false, decide_eq_false_iff_not] at h1
    omega
  · intro h i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [carry_succ, ih, Bool.toNat_false, decide_eq_false_iff_not]
      have hi : m / p ^ i % p + n / p ^ i % p < p := h i
      omega

-- ════════════════════════════════════════════════════════════════════
-- §3 KUMMER'S THEOREM OVER THE CARRY RECURSION
-- ════════════════════════════════════════════════════════════════════

/-- **Kummer's theorem, carry form.**  For a prime `p`, the `p`-adic valuation
    of `C(m + n, m)` is the number of carries produced by adding `m` and `n` in
    base `p`, counted over any window `Finset.Ico 1 b` with
    `Nat.log p (m + n) < b`.

    This is Mathlib's `padicValNat_choose'` transported along
    `carry_eq_true_iff`. -/
theorem padicValNat_choose_add_eq_card_carries {p m n b : ℕ} (hp : p.Prime)
    (hb : Nat.log p (m + n) < b) :
    padicValNat p ((m + n).choose m) =
      ((Finset.Ico 1 b).filter (fun i => carry p m n i = true)).card := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcomm : m + n = n + m := Nat.add_comm m n
  rw [hcomm, padicValNat_choose' (p := p) (n := n) (k := m) (b := b)
    (by rwa [← hcomm])]
  refine congrArg Finset.card (Finset.filter_congr fun i _ => ?_)
  exact (carry_eq_true_iff hp.one_lt m n i).symm

/-- Satisfiability of `padicValNat_choose_add_eq_card_carries`: every hypothesis
    holds jointly at `p = 3`, `m = 7`, `n = 5`, `b = 4`, and the conclusion is a
    nonzero count.  Independent check: `C(12,7) = 792 = 2³ · 3² · 11`, so
    `v₃ = 2`. -/
example : padicValNat 3 ((7 + 5).choose 7) = 2 := by
  rw [padicValNat_choose_add_eq_card_carries (b := 4) Nat.prime_three
    (Nat.log_lt_of_lt_pow (by norm_num) (by norm_num))]
  decide

/-- The number of carries is unaffected by widening the counting window, as
    long as the window starts at `1` and reaches past `Nat.log p (m + n)`. -/
theorem exists_carry_iff_exists_mem_Ico {p m n b : ℕ} (hp : 1 < p)
    (hb : Nat.log p (m + n) < b) :
    (∃ i, carry p m n i = true) ↔ ∃ i ∈ Finset.Ico 1 b, carry p m n i = true := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, Finset.mem_Ico.mpr ⟨?_, ?_⟩, hi⟩
    · rcases Nat.eq_zero_or_pos i with rfl | hpos
      · simp at hi
      · exact hpos
    · by_contra hbi
      have hbb : m + n < p ^ i :=
        lt_of_lt_of_le (Nat.lt_pow_succ_log_self hp (m + n))
          (Nat.pow_le_pow_right (by omega) (by omega))
      rw [carry_eq_false_of_add_lt hp hbb] at hi
      exact Bool.noConfusion hi
  · rintro ⟨i, -, hi⟩
    exact ⟨i, hi⟩

/-- **Kummer's divisibility criterion.**  A prime `p` divides `C(m + n, m)`
    iff adding `m` and `n` in base `p` produces at least one carry. -/
theorem prime_dvd_choose_add_iff_exists_carry {p m n : ℕ} (hp : p.Prime) :
    p ∣ (m + n).choose m ↔ ∃ i, carry p m n i = true := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hb : Nat.log p (m + n) < Nat.log p (m + n) + 1 := Nat.lt_succ_self _
  have hne : (m + n).choose m ≠ 0 := (Nat.choose_pos (Nat.le_add_right m n)).ne'
  rw [exists_carry_iff_exists_mem_Ico hp.one_lt hb]
  constructor
  · intro hdvd
    have h1 : 1 ≤ padicValNat p ((m + n).choose m) := by
      rw [← padicValNat_dvd_iff_le hne]
      simpa using hdvd
    rw [padicValNat_choose_add_eq_card_carries hp hb] at h1
    obtain ⟨i, hi⟩ := Finset.card_pos.mp h1
    obtain ⟨hmem, hcar⟩ := Finset.mem_filter.mp hi
    exact ⟨i, hmem, hcar⟩
  · rintro ⟨i, hmem, hcar⟩
    have h1 : 1 ≤ padicValNat p ((m + n).choose m) := by
      rw [padicValNat_choose_add_eq_card_carries hp hb]
      exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hmem, hcar⟩⟩
    simpa using (padicValNat_dvd_iff_le (p := p) (n := 1) hne).mpr h1

/-- **Kummer's carry-free criterion, digitwise form.**  A prime `p` does not
    divide `C(m + n, m)` iff at every place the base-`p` digits of `m` and `n`
    sum to less than `p`. -/
theorem prime_not_dvd_choose_add_iff_digitwise {p m n : ℕ} (hp : p.Prime) :
    ¬ p ∣ (m + n).choose m ↔ ∀ i, m / p ^ i % p + n / p ^ i % p < p := by
  rw [prime_dvd_choose_add_iff_exists_carry hp, not_exists]
  simp only [Bool.not_eq_true]
  exact forall_carry_eq_false_iff p m n

/-- Satisfiability of `prime_not_dvd_choose_add_iff_digitwise`, positive side:
    `5 = (12)₃` and `3 = (10)₃` add without carries in base three, and indeed
    `C(8,5) = 56 = 2³ · 7` is prime to `3`. -/
example : (∀ i, 5 / 3 ^ i % 3 + 3 / 3 ^ i % 3 < 3) ∧ (5 + 3).choose 5 = 56 :=
  ⟨(prime_not_dvd_choose_add_iff_digitwise (p := 3) Nat.prime_three).mp (by decide),
    by decide⟩

/-- Satisfiability, negative side: `7 = (21)₃` and `5 = (12)₃` do carry, and
    indeed `3 ∣ C(12,7) = 792`.  So the criterion is not constantly true. -/
example : ¬ (∀ i, 7 / 3 ^ i % 3 + 5 / 3 ^ i % 3 < 3) := fun h =>
  (by decide : ¬ ¬ (3 ∣ (7 + 5).choose 7))
    ((prime_not_dvd_choose_add_iff_digitwise (p := 3) Nat.prime_three).mpr h)

-- ════════════════════════════════════════════════════════════════════
-- §4 CENTRAL BINOMIAL COEFFICIENTS (THE #376 / #406 BRIDGE)
-- ════════════════════════════════════════════════════════════════════

/-- **The Erdős #376 digit criterion.**  For any prime `p`, the central
    binomial coefficient `C(2n, n)` is prime to `p` iff every base-`p` digit
    of `n` is smaller than `p / 2` (spelled `2 * d < p` to avoid division
    in `ℕ`).

    This is OEIS A030979's first comment, proved from Kummer rather than
    Lucas.  No oddness hypothesis on `p` is needed: at `p = 2` both sides say
    `n = 0` — the right side because `Nat.digits 2 n` has a nonzero leading
    digit, the left side because `Erdos175.padicValNat_two_centralBinom`
    (`NotSquarefree.lean`) gives `v₂(C(2n,n)) = (Nat.digits 2 n).sum`. -/
theorem prime_not_dvd_centralBinom_iff_digits {p n : ℕ} (hp : p.Prime) :
    ¬ p ∣ Nat.centralBinom n ↔ ∀ d ∈ Nat.digits p n, 2 * d < p := by
  have hcb : Nat.centralBinom n = (n + n).choose n := by
    rw [Nat.centralBinom_eq_two_mul_choose, two_mul]
  have h0 : 2 * 0 < p := by simpa using hp.pos
  rw [hcb, prime_not_dvd_choose_add_iff_digitwise hp,
    ← forall_div_pow_mod_iff_forall_mem_digits hp.two_le n (fun d => 2 * d < p) h0]
  exact forall_congr' fun i => by omega

/-- Ground truth against OEIS A030979: `10` is a term of the sequence (so
    `C(20,10) = 184756 = 2² · 11 · 13 · 17 · 19` is prime to `3`, `5` and `7`)
    while `2` is not (`C(4,2) = 6`). -/
example : ¬ (3 ∣ Nat.centralBinom 10) ∧ ¬ (5 ∣ Nat.centralBinom 10) ∧
    ¬ (7 ∣ Nat.centralBinom 10) ∧ (3 ∣ Nat.centralBinom 2) := by decide

/-- End-to-end use of `prime_not_dvd_centralBinom_iff_digits`, forward
    direction, at the A030979 term `n = 10`: the theorem turns `3 ∤ C(20,10)`
    into the digit bound, and `Nat.digits 3 10 = [1, 0, 1]` confirms it
    independently.  The digit list is nonempty, so the `∀ d ∈ …` is not
    vacuous. -/
example : (∀ d ∈ Nat.digits 3 10, 2 * d < 3) ∧ Nat.digits 3 10 = [1, 0, 1] :=
  ⟨(prime_not_dvd_centralBinom_iff_digits (p := 3) (n := 10) Nat.prime_three).mp
      (by decide),
    by decide⟩

/-- End-to-end use, reverse direction, at the non-term `n = 2`: the digit `2` of
    `2 = (2)₃` violates `2 * d < 3`, and the theorem delivers `3 ∣ C(4,2) = 6`. -/
example : 3 ∣ Nat.centralBinom 2 := by
  by_contra hnd
  have hdig := (prime_not_dvd_centralBinom_iff_digits (p := 3) (n := 2)
    Nat.prime_three).mp hnd
  have hmem : (2 : ℕ) ∈ Nat.digits 3 2 := by decide
  have hbad : 2 * 2 < 3 := hdig 2 hmem
  omega

/-- Degeneracy audit at the smallest prime.  At `p = 2` the digit criterion
    reads "every binary digit of `n` is `0`", which forces `n = 0` because
    `Nat.digits` never records a zero leading digit; and indeed `C(0,0) = 1` is
    odd while `C(2,1) = 2` and `C(6,3) = 20` are even.  So the theorem is not
    vacuous at `p = 2`, it is simply sharp there. -/
example : ¬ (2 ∣ Nat.centralBinom 0) ∧ (2 ∣ Nat.centralBinom 1) ∧
    (2 ∣ Nat.centralBinom 3) ∧ Nat.digits 2 0 = [] := by decide

end Erdos175

#print axioms Erdos175.forall_div_pow_mod_iff_forall_mem_digits
#print axioms Erdos175.carry_eq_true_iff
#print axioms Erdos175.carry_eq_false_iff
#print axioms Erdos175.carry_eq_false_of_add_lt
#print axioms Erdos175.forall_carry_eq_false_iff
#print axioms Erdos175.padicValNat_choose_add_eq_card_carries
#print axioms Erdos175.exists_carry_iff_exists_mem_Ico
#print axioms Erdos175.prime_dvd_choose_add_iff_exists_carry
#print axioms Erdos175.prime_not_dvd_choose_add_iff_digitwise
#print axioms Erdos175.prime_not_dvd_centralBinom_iff_digits
