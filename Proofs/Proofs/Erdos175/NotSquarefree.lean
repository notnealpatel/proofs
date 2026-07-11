/-
  Erdős Problem #175 — "C(2n,n) is not squarefree for n ≥ 5" — PARTIAL
  formalization: the elementary (non-analytic) part.

  Problem (https://www.erdosproblems.com/175, also Guy, "Unsolved Problems
  in Number Theory", B33): show that for any n ≥ 5 the central binomial
  coefficient C(2n,n) is not squarefree.

  Status of the full theorem: proved for all sufficiently large n by
  Sárközy (J. Number Theory, 1985), and for all n ≥ 5 independently by
  Granville–Ramaré (Mathematika, 1996) and Velammal (Hardy-Ramanujan J.,
  1995). The elementary reduction (already noted on the problem page) is
  that 4 ∣ C(2n,n) whenever n is not a power of 2, so only n = 2^k is
  hard; every known proof of the power-of-2 case uses analytic methods
  (explicit exponential-sum estimates).

  HONEST CLAIM BOUNDARY. The analytic part is NOT formalized here. This
  file proves, sorry-free:

  * `padicValNat_two_centralBinom` — Kummer's theorem at p = 2:
      v₂(C(2n,n)) = s₂(n), the binary digit sum of n. Specializes
      Mathlib's `sub_one_mul_padicValNat_choose_eq_sub_sum_digits`.
  * `sum_digits_two_eq_one_iff` — s₂(n) = 1 ↔ n is a power of 2
      (the small lemma missing from Mathlib).
  * `four_dvd_centralBinom`, `not_squarefree_centralBinom_of_not_two_pow`
      — for every n ≠ 0 not a power of two, 4 ∣ C(2n,n), hence C(2n,n)
      is not squarefree. Unbounded n; covers all n ≥ 3 with n ≠ 2^k.
  * `not_squarefree_centralBinom_two_pow` — for n = 2^k, 3 ≤ k ≤ 30,
      C(2n,n) is not squarefree. Certified via the p-adic valuation
      digit-sum formula at a per-k witness prime, never by computing the
      (astronomically large) binomial itself: the certificate
      s_p(2n) + 2(p-1) ≤ 2·s_p(n) forces v_p(C(2n,n)) ≥ 2. Witness
      primes (found computationally, verified by `native_decide`):
      p = 5 for k = 6 (v₅ = 3), p = 7 for k = 8 (v₇ = 2), p = 3 for all
      other 3 ≤ k ≤ 30. (SageMath check: p = 3 works for every
      3 ≤ k ≤ 200 except k ∈ {6, 8}.)
  * `not_squarefree_centralBinom` — ∀ n, 5 ≤ n ≤ 2^30 → ¬Squarefree
      C(2n,n): the statement of Erdős #175 for all n up to 2^30 > 10^9.
  * `squarefree_centralBinom_iff` — for n ≤ 2^30:
      Squarefree C(2n,n) ↔ n ∈ {0, 1, 2, 4}. (Convention: C(0) = 1 is
      squarefree; C(1) = 2, C(2) = 6, C(4) = 70. OEIS A046098.)

  Method notes. Kummer's digit-sum form of Legendre's formula is already
  in Mathlib; the only genuinely new ingredients are the binary digit-sum
  characterization of powers of two (strong induction on n via
  `Nat.digits_def'`) and the decide-friendly witness-prime certificates.
  `native_decide` is used exactly once (`witness_cert`), for digit sums
  of 2^k, 2^(k+1) in bases 3, 5, 7 — numbers ≤ 2^31, instant to check.

  Axiom audit (2026-07-11, `#print axioms` via `lake env lean`):
  `padicValNat_two_centralBinom`, `sum_digits_two_eq_one_iff`,
  `four_dvd_centralBinom`, `not_squarefree_centralBinom_of_not_two_pow`
  depend on exactly propext, Classical.choice, Quot.sound.
  `not_squarefree_centralBinom_two_pow`, `not_squarefree_centralBinom`,
  `squarefree_centralBinom_iff` additionally carry the per-use
  `native_decide` trust axiom of `witness_cert`
  (`Erdos175.witness_cert._native.native_decide.ax_1_1`, Lean ≥ 4.30's
  form of `Lean.ofReduceBool`). No `sorryAx` anywhere.

  References:
  [Sa85]   Sárközy, A., "On divisors of binomial coefficients, I",
           J. Number Theory 20 (1985), 70–80.
  [GrRa96] Granville, A. and Ramaré, O., "Explicit bounds on exponential
           sums and the scarcity of squarefree binomial coefficients",
           Mathematika 43 (1996), 73–107.
  [Ve95]   Velammal, G., "Is the binomial coefficient C(2n,n)
           squarefree?", Hardy-Ramanujan J. 18 (1995), 23–45.
-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.NormNum.Prime

namespace Erdos175

-- ════════════════════════════════════════════════════════════════════
-- §1 BINARY DIGIT SUMS: s₂(n) = 1 ↔ n IS A POWER OF TWO
-- ════════════════════════════════════════════════════════════════════

/-- The base-`b` digit sum of a nonzero number is positive (the leading
    digit is nonzero). -/
theorem sum_digits_pos (b : ℕ) {n : ℕ} (hn : n ≠ 0) :
    0 < (Nat.digits b n).sum := by
  have hne : Nat.digits b n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  have hlast : (Nat.digits b n).getLast hne ≠ 0 :=
    Nat.getLast_digit_ne_zero b hn
  have hle : (Nat.digits b n).getLast hne ≤ (Nat.digits b n).sum :=
    List.le_sum_of_mem (List.getLast_mem hne)
  omega

/-- If the binary digit sum of `n` is `1`, then `n` is a power of two.
    Strong induction: strip the last binary digit with `Nat.digits_def'`. -/
theorem exists_two_pow_of_sum_digits_eq_one : ∀ {n : ℕ},
    (Nat.digits 2 n).sum = 1 → ∃ k, n = 2 ^ k := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hsum
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp at hsum
    · rw [Nat.digits_def' (by norm_num : (1:ℕ) < 2) hn, List.sum_cons] at hsum
      rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
      · -- n even: the digit sum of n / 2 is still 1; recurse.
        obtain ⟨k, hk⟩ := ih (n / 2) (Nat.div_lt_self hn (by norm_num))
          (by omega)
        exact ⟨k + 1, by rw [pow_succ']; omega⟩
      · -- n odd: the digit sum of n / 2 is 0, forcing n / 2 = 0, n = 1.
        have hd : n / 2 = 0 := by
          by_contra hne
          have := sum_digits_pos 2 hne
          omega
        exact ⟨0, by rw [pow_zero]; omega⟩

/-- The binary digit sum of `n` equals `1` iff `n` is a power of two. -/
theorem sum_digits_two_eq_one_iff {n : ℕ} :
    (Nat.digits 2 n).sum = 1 ↔ ∃ k, n = 2 ^ k := by
  constructor
  · exact exists_two_pow_of_sum_digits_eq_one
  · rintro ⟨k, rfl⟩
    rw [← mul_one (2 ^ k),
      Nat.digits_base_pow_mul (by norm_num : (1:ℕ) < 2) (by norm_num),
      Nat.digits_def' (by norm_num : (1:ℕ) < 2) (by norm_num : (0:ℕ) < 1)]
    norm_num [List.sum_append, List.sum_replicate]

/-- The key elementary lemma (missing from Mathlib): a positive `n` that
    is not a power of two has binary digit sum at least `2`. -/
theorem two_le_sum_digits_two {n : ℕ} (hn : n ≠ 0) (h : ∀ k, n ≠ 2 ^ k) :
    2 ≤ (Nat.digits 2 n).sum := by
  have h0 := sum_digits_pos 2 hn
  have h1 : (Nat.digits 2 n).sum ≠ 1 := fun hs => by
    obtain ⟨k, hk⟩ := sum_digits_two_eq_one_iff.mp hs
    exact h k hk
  omega

-- ════════════════════════════════════════════════════════════════════
-- §2 KUMMER'S THEOREM SPECIALIZED TO CENTRAL BINOMIAL COEFFICIENTS
-- ════════════════════════════════════════════════════════════════════

/-- Kummer's theorem at `p = 2`: the 2-adic valuation of `C(2n,n)` is the
    binary digit sum of `n`. (Since `s₂(2n) = s₂(n)`, the digit-sum form
    `(p-1)·v_p(C(n,k)) = s_p(k) + s_p(n-k) - s_p(n)` collapses.) -/
theorem padicValNat_two_centralBinom (n : ℕ) :
    padicValNat 2 (Nat.centralBinom n) = (Nat.digits 2 n).sum := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.centralBinom_zero]
  · have h := sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := 2)
      (k := n) (n := 2 * n) (by omega)
    have hsub : 2 * n - n = n := by omega
    rw [hsub, Nat.digits_base_mul (by norm_num : (1:ℕ) < 2) hn,
      List.sum_cons] at h
    rw [Nat.centralBinom_eq_two_mul_choose]
    omega

/-- If `p` is prime and `v_p(m) ≥ 2` then `m` is not squarefree. -/
theorem not_squarefree_of_two_le_padicValNat {p m : ℕ} (hp : p.Prime)
    (h : 2 ≤ padicValNat p m) : ¬ Squarefree m := fun hsq => by
  have hdvd : p * p ∣ m := by
    have h1 : p ^ 2 ∣ p ^ padicValNat p m := pow_dvd_pow p h
    have h2 := h1.trans (pow_padicValNat_dvd (p := p) (n := m))
    rwa [pow_two] at h2
  exact absurd (Nat.isUnit_iff.mp (hsq p hdvd)) hp.one_lt.ne'

/-- Witness-prime certificate: if `s_p(2n) + 2(p-1) ≤ 2·s_p(n)` for a
    prime `p`, then `v_p(C(2n,n)) ≥ 2`. This is the digit-sum form of
    "adding `n + n` in base `p` produces at least two carries". -/
theorem two_le_padicValNat_centralBinom {p n : ℕ} (hp : p.Prime)
    (hcert : (Nat.digits p (2 * n)).sum + 2 * (p - 1) ≤
      2 * (Nat.digits p n).sum) :
    2 ≤ padicValNat p (Nat.centralBinom n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 := hp.two_le
  have h := sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := p)
    (k := n) (n := 2 * n) (by omega)
  have hsub : 2 * n - n = n := by omega
  rw [hsub] at h
  have hmul : (p - 1) * 2 ≤ (p - 1) * padicValNat p ((2 * n).choose n) := by
    rw [h]; omega
  rw [Nat.centralBinom_eq_two_mul_choose]
  exact Nat.le_of_mul_le_mul_left hmul (by omega)

-- ════════════════════════════════════════════════════════════════════
-- §3 MAIN RESULT, PART 1: n NOT A POWER OF TWO (UNBOUNDED)
-- ════════════════════════════════════════════════════════════════════

/-- The classical elementary observation: if `n ≠ 0` is not a power of
    two, then `4 ∣ C(2n,n)`. -/
theorem four_dvd_centralBinom {n : ℕ} (hn : n ≠ 0) (h : ∀ k, n ≠ 2 ^ k) :
    4 ∣ Nat.centralBinom n := by
  have h2 : 2 ≤ padicValNat 2 (Nat.centralBinom n) := by
    rw [padicValNat_two_centralBinom]
    exact two_le_sum_digits_two hn h
  rw [(by norm_num : (4:ℕ) = 2 ^ 2)]
  exact (pow_dvd_pow 2 h2).trans pow_padicValNat_dvd

/-- **Erdős #175, elementary part.** For every `n ≠ 0` that is not a
    power of two, `C(2n,n)` is not squarefree. -/
theorem not_squarefree_centralBinom_of_not_two_pow {n : ℕ} (hn : n ≠ 0)
    (h : ∀ k, n ≠ 2 ^ k) : ¬ Squarefree (Nat.centralBinom n) :=
  not_squarefree_of_two_le_padicValNat Nat.prime_two
    (by rw [padicValNat_two_centralBinom]; exact two_le_sum_digits_two hn h)

-- ════════════════════════════════════════════════════════════════════
-- §4 MAIN RESULT, PART 2: n = 2^k FOR 3 ≤ k ≤ 30
-- ════════════════════════════════════════════════════════════════════

/-- Witness prime for `n = 2^k`: `p = 5` for `k = 6`, `p = 7` for
    `k = 8`, and `p = 3` otherwise (correct for all `3 ≤ k ≤ 30`;
    computationally, `3` works for every `3 ≤ k ≤ 200` except `6`, `8`).

    Valuations certified below: e.g. v₃(C(16,8)) = 2, v₅(C(128,64)) = 3
    (note 9 ∤ C(128,64)), v₇(C(512,256)) = 2, v₃(C(2^31,2^30)) = 11. -/
def witness (k : ℕ) : ℕ :=
  if k = 6 then 5 else if k = 8 then 7 else 3

/-- Batched digit-sum certificates for all `3 ≤ k ≤ 30`: the witness
    prime is prime, and the carry certificate of
    `two_le_padicValNat_centralBinom` holds at `n = 2^k`. The check only
    involves digit sums of `2^k, 2^(k+1) ≤ 2^31` in bases `3, 5, 7`. -/
theorem witness_cert : ∀ k < 31, 3 ≤ k →
    (witness k).Prime ∧
      (Nat.digits (witness k) (2 ^ (k + 1))).sum + 2 * (witness k - 1) ≤
        2 * (Nat.digits (witness k) (2 ^ k)).sum := by
  native_decide

/-- **Erdős #175, bounded power-of-two part.** For `n = 2^k` with
    `3 ≤ k ≤ 30`, `C(2n,n)` is not squarefree. (For all `k ≥ 3` this is
    true but requires the analytic methods of Granville–Ramaré/Velammal,
    not formalized here.) -/
theorem not_squarefree_centralBinom_two_pow {k : ℕ} (h3 : 3 ≤ k)
    (h30 : k ≤ 30) : ¬ Squarefree (Nat.centralBinom (2 ^ k)) := by
  obtain ⟨hp, hcert⟩ := witness_cert k (by omega) h3
  refine not_squarefree_of_two_le_padicValNat hp
    (two_le_padicValNat_centralBinom hp ?_)
  rw [← pow_succ']
  exact hcert

-- ════════════════════════════════════════════════════════════════════
-- §5 COMBINED COVERAGE: ALL 5 ≤ n ≤ 2^30, AND THE CLASSIFICATION
-- ════════════════════════════════════════════════════════════════════

/-- **Erdős #175 for all n ≤ 2^30.** For every `5 ≤ n ≤ 2^30` (in
    particular the full range where squarefree values could conceivably
    have been missed by hand computation — 2^30 > 10^9), the central
    binomial coefficient `C(2n,n)` is not squarefree. The restriction
    `n ≤ 2^30` is needed only for `n` a power of two. -/
theorem not_squarefree_centralBinom {n : ℕ} (h5 : 5 ≤ n)
    (hle : n ≤ 2 ^ 30) : ¬ Squarefree (Nat.centralBinom n) := by
  by_cases hpow : ∃ k, n = 2 ^ k
  · obtain ⟨k, rfl⟩ := hpow
    have h3 : 3 ≤ k := by
      by_contra hc
      push Not at hc
      have hk2 : (2:ℕ) ^ k ≤ 2 ^ 2 :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at hk2
      omega
    have h30 : k ≤ 30 := by
      by_contra hc
      push Not at hc
      have hk31 : (2:ℕ) ^ 31 ≤ 2 ^ k :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h31 := hk31.trans hle
      norm_num at h31
    exact not_squarefree_centralBinom_two_pow h3 h30
  · push Not at hpow
    exact not_squarefree_centralBinom_of_not_two_pow (by omega) hpow

/-- `3` is not a power of two. -/
theorem three_ne_two_pow : ∀ k, (3 : ℕ) ≠ 2 ^ k
  | 0, h => by norm_num at h
  | 1, h => by norm_num at h
  | (k + 2), h => by
    have h4 : (4:ℕ) ≤ 2 ^ (k + 2) :=
      (by norm_num : (4:ℕ) = 2 ^ 2) ▸
        Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- **Classification up to 2^30.** For `n ≤ 2^30`, the central binomial
    coefficient `C(2n,n)` is squarefree exactly for `n ∈ {0, 1, 2, 4}`
    (with the convention `C(0) = centralBinom 0 = 1`, which is
    squarefree): `C(1) = 2`, `C(2) = 6`, `C(4) = 70`. Erdős #175 states
    this classification holds for all `n` (proved via analytic methods,
    not formalized here). Cf. OEIS A046098. -/
theorem squarefree_centralBinom_iff {n : ℕ} (hle : n ≤ 2 ^ 30) :
    Squarefree (Nat.centralBinom n) ↔ n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 4 := by
  constructor
  · intro hsq
    by_contra hne
    push Not at hne
    obtain ⟨h0, h1, h2, h4⟩ := hne
    rcases (by omega : n = 3 ∨ 5 ≤ n) with rfl | h5
    · exact not_squarefree_centralBinom_of_not_two_pow (by norm_num)
        three_ne_two_pow hsq
    · exact not_squarefree_centralBinom h5 hle hsq
  · have hp5 : Nat.Prime 5 := by norm_num
    have hp7 : Nat.Prime 7 := by norm_num
    rintro (rfl | rfl | rfl | rfl)
    · rw [Nat.centralBinom_zero]
      exact squarefree_one
    · rw [show Nat.centralBinom 1 = 2 from rfl]
      exact Nat.prime_two.prime.squarefree
    · rw [show Nat.centralBinom 2 = 6 from rfl,
        (by norm_num : (6:ℕ) = 2 * 3), Nat.squarefree_mul_iff]
      exact ⟨(Nat.coprime_primes Nat.prime_two Nat.prime_three).mpr
          (by norm_num),
        Nat.prime_two.prime.squarefree, Nat.prime_three.prime.squarefree⟩
    · rw [show Nat.centralBinom 4 = 70 from rfl,
        (by norm_num : (70:ℕ) = 2 * (5 * 7)), Nat.squarefree_mul_iff,
        Nat.squarefree_mul_iff]
      exact ⟨Nat.Coprime.mul_right
          ((Nat.coprime_primes Nat.prime_two hp5).mpr (by norm_num))
          ((Nat.coprime_primes Nat.prime_two hp7).mpr (by norm_num)),
        Nat.prime_two.prime.squarefree,
        (Nat.coprime_primes hp5 hp7).mpr (by norm_num),
        hp5.prime.squarefree, hp7.prime.squarefree⟩

end Erdos175
