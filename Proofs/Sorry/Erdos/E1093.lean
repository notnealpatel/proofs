/-
  Erdős Problem #1093 — deficiency of binomial coefficients.
  Status: open.  Tier UB archive target with decidable certificates.

  Verbatim statement (`goof erdos fetch 1093`, pulled 2026-08-05):

    "For $n\geq 2k$ we define the deficiency of $\binom{n}{k}$ as
    follows. If $\binom{n}{k}$ is divisible by a prime $p\leq k$ then
    the deficiency is undefined. Otherwise, the deficiency is the
    number of $0\leq i<k$ such that $n-i$ is $k$-smooth, that is,
    divisible only by primes $\leq k$.

    Are there infinitely many binomial coefficients with deficiency
    $1$? Are there only finitely many with deficiency $>1$?"

  DB remarks (Erdős–Lacampagne–Selfridge [ELS88], [ELS93]): if the
  deficiency exists and is ≥ 1 then n ≪ 2^k·√k.  58 deficiency-1
  examples with n ≤ 10⁵, e.g. C(7,3), C(13,4), C(14,4), C(23,5),
  C(62,6), C(94,10), C(95,10).  All known deficiency-2 examples:
  C(44,8), C(74,10), C(174,12), C(239,14), C(5179,27), C(8413,28),
  C(8414,28), C(96622,42); deficiency 3: C(46,10), C(47,10),
  C(241,16), C(2105,25), C(1119,27), C(6459,33); deficiency 4:
  C(47,11); deficiency 9: C(284,28).  (List corrected Dec 2025 per
  Kevin Barreto's comment.)  Barreto also gives a conditional positive
  answer to question 2 under two strong conjectures (xyz-type) —
  comment-sourced.

  Mathlib inventory (leandoc 2026-08-05): `Nat.smoothNumbers n` uses
  primes < n (STRICT) — so "k-smooth = primes ≤ k" is
  `Nat.smoothNumbers (k+1)`; we define an explicit `≤ k` predicate to
  keep the statement readable and prove the bridge as sanity.
  `Nat.primeFactors`, `Nat.choose` otherwise.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E1093

open scoped Nat

/-- `KSmooth k m`: every prime factor of `m` is `≤ k` (the problem's
    "k-smooth").  Note Mathlib's `Nat.smoothNumbers k` uses `< k`, so
    the bridge is `KSmooth k m ↔ m ∈ Nat.smoothNumbers (k+1)` for
    `m ≠ 0`. -/
def KSmooth (k m : ℕ) : Prop :=
  ∀ p ∈ m.primeFactors, p ≤ k

instance (k m : ℕ) : Decidable (KSmooth k m) := by
  unfold KSmooth; infer_instance

/-- Bridge to the Mathlib smooth-numbers API.  -- PROVABLE
    (`Nat.mem_smoothNumbers` + `Nat.lt_succ_iff`). -/
theorem kSmooth_iff_mem_smoothNumbers (k m : ℕ) (hm : m ≠ 0) :
    KSmooth k m ↔ m ∈ Nat.smoothNumbers (k + 1) := by
  simp only [KSmooth, Nat.mem_smoothNumbers, Nat.primeFactors, List.mem_toFinset]
  constructor
  · intro h
    exact ⟨hm, fun p hp => Nat.lt_succ_of_le (h p hp)⟩
  · intro h p hp
    exact Nat.le_of_lt_succ (h.2 p hp)

/-- `DeficiencyDefined n k`: no prime `≤ k` divides `C(n,k)` — the
    condition under which the deficiency is defined. -/
def DeficiencyDefined (n k : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≤ k → ¬ p ∣ n.choose k

/-- `deficiency n k`: the number of `0 ≤ i < k` with `n − i` being
    `k`-smooth.  (Total function; only meaningful under
    `DeficiencyDefined n k` and `2k ≤ n` — all theorems guard.) -/
def deficiency (n k : ℕ) : ℕ :=
  ((Finset.range k).filter (fun i => KSmooth k (n - i))).card

/-- Definedness can be checked over the finite set of natural numbers at most `k`. -/
private theorem deficiencyDefined_iff_bounded (n k : ℕ) :
    DeficiencyDefined n k ↔
      ∀ p : Fin (k + 1), p.val.Prime → ¬ p.val ∣ n.choose k := by
  constructor
  · intro h p hp
    exact h p.val hp (Nat.le_of_lt_succ p.isLt)
  · intro h p hp hpk
    exact h ⟨p, Nat.lt_succ_of_le hpk⟩ hp

/-- The coefficient `C(7,3)` is defined and has deficiency one. -/
theorem sanity_seven_three : DeficiencyDefined 7 3 ∧ deficiency 7 3 = 1 := by
  constructor
  · rw [deficiencyDefined_iff_bounded, Nat.choose_eq_descFactorial_div_factorial]
    decide
  · unfold deficiency KSmooth
    decide +kernel

/-- The coefficient `C(44,8)` is defined and has deficiency two. -/
theorem sanity_fortyFour_eight : DeficiencyDefined 44 8 ∧ deficiency 44 8 = 2 := by
  constructor
  · rw [deficiencyDefined_iff_bounded, Nat.choose_eq_descFactorial_div_factorial]
    decide
  · unfold deficiency KSmooth
    decide +kernel

/-- The coefficient `C(10,3)` is not defined, since two divides it. -/
theorem sanity_ten_three : ¬ DeficiencyDefined 10 3 := by
  rw [deficiencyDefined_iff_bounded, Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- The coefficient `C(5,4)` is defined with deficiency three, outside the size guard. -/
theorem sanity_five_four :
    DeficiencyDefined 5 4 ∧ deficiency 5 4 = 3 ∧ ¬ (2 * 4 ≤ 5) := by
  constructor
  · rw [deficiencyDefined_iff_bounded, Nat.choose_eq_descFactorial_div_factorial]
    decide
  · constructor
    · unfold deficiency KSmooth
      decide +kernel
    · decide

/-- Ground truth at C(7,3) = 35: defined (2, 3 ∤ 35), and among
    7, 6, 5 only 6 is 3-smooth — deficiency 1.  -- PROVABLE (decide). -/
example : DeficiencyDefined 7 3 ∧ deficiency 7 3 = 1 := by
  exact sanity_seven_three

/-- Ground truth at C(44,8): defined, deficiency 2 (the smallest
    deficiency-2 example).  -- PROVABLE (decide; C(44,8) =
    177232627? — kernel-computable). -/
example : DeficiencyDefined 44 8 ∧ deficiency 44 8 = 2 := by
  exact sanity_fortyFour_eight

/-- Non-degeneracy: C(10,3) = 120 is divisible by 2 ≤ 3, so its
    deficiency is undefined.  -- PROVABLE (decide). -/
example : ¬ DeficiencyDefined 10 3 := by
  exact sanity_ten_three

/-- **Erdős #1093, question 1 (OPEN)**: infinitely many binomial
    coefficients have (defined) deficiency exactly 1.  Encoded on the
    pair set with the `2k ≤ n` and definedness guards. -/
theorem erdos_1093_q1 :
    {q : ℕ × ℕ | 2 * q.2 ≤ q.1 ∧ 2 ≤ q.2 ∧ DeficiencyDefined q.1 q.2 ∧
      deficiency q.1 q.2 = 1}.Infinite := by
  sorry

/-- **Erdős #1093, question 2 (OPEN)**: only finitely many have
    deficiency > 1 (stated as `2 ≤ deficiency`).  All known examples
    are listed in the header; Barreto's conditional resolution rests
    on unproved xyz-type conjectures. -/
theorem erdos_1093_q2 :
    {q : ℕ × ℕ | 2 * q.2 ≤ q.1 ∧ 2 ≤ q.2 ∧ DeficiencyDefined q.1 q.2 ∧
      2 ≤ deficiency q.1 q.2}.Finite := by
  sorry

/-- Splitting the falling product `n (n-1) ⋯ (n-k+1)` around the factor `n - i`. -/
private theorem descFactorial_split (n k i : ℕ) (hik : i < k) (hkn : k ≤ n) :
    n.descFactorial k =
      (n - i) * ((n - i - 1).descFactorial (k - 1 - i) * n.descFactorial i) := by
  have hsplit := Nat.descFactorial_mul_descFactorial (n := n) hik.le
  have hni : n - i = (n - i - 1) + 1 := by omega
  have hki : k - i = (k - 1 - i) + 1 := by omega
  rw [← hsplit, hni, hki, Nat.succ_descFactorial_succ, ← hni, Nat.mul_assoc]

/-- If `C(n,k)` has no prime factor `≤ k` and `n - i` (`i < k`) is `k`-smooth, then
    `(n - i) · i! · (k-1-i)!` divides `k!`. -/
private theorem smooth_mul_factorials_dvd (n k i : ℕ) (hik : i < k) (hkn : k ≤ n)
    (hdef : DeficiencyDefined n k) (hsm : KSmooth k (n - i)) (hm : n - i ≠ 0) :
    (n - i) * ((k - 1 - i)! * i !) ∣ k ! := by
  have hdvdP : (n - i) * ((k - 1 - i)! * i !) ∣ k ! * n.choose k := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose, descFactorial_split n k i hik hkn]
    exact Nat.mul_dvd_mul_left _
      (Nat.mul_dvd_mul (Nat.factorial_dvd_descFactorial _ _)
        (Nat.factorial_dvd_descFactorial _ _))
  have hcop : Nat.Coprime ((n - i) * ((k - 1 - i)! * i !)) (n.choose k) := by
    apply Nat.coprime_of_dvd
    intro p hp hpA
    have hpk : p ≤ k := by
      rcases (Nat.Prime.dvd_mul hp).1 hpA with hpm | hpF
      · exact hsm p (Nat.mem_primeFactors.2 ⟨hp, hpm, hm⟩)
      · rcases (Nat.Prime.dvd_mul hp).1 hpF with h1 | h2
        · have := (Nat.Prime.dvd_factorial hp).1 h1
          omega
        · have := (Nat.Prime.dvd_factorial hp).1 h2
          omega
    exact hdef p hp hpk
  exact hcop.dvd_of_dvd_mul_right hdvdP

/-- Under the same hypotheses, `n - i ≤ k · 2^k`. -/
private theorem sub_le_mul_two_pow (n k i : ℕ) (hik : i < k) (hkn : k ≤ n)
    (hdef : DeficiencyDefined n k) (hsm : KSmooth k (n - i)) (hm : n - i ≠ 0) :
    n - i ≤ k * 2 ^ k := by
  have hdvd := smooth_mul_factorials_dvd n k i hik hkn hdef hsm hm
  have hle : (n - i) * ((k - 1 - i)! * i !) ≤ k ! := Nat.le_of_dvd (Nat.factorial_pos k) hdvd
  have hk : k = (k - 1) + 1 := by omega
  have hfact : k ! = k * (Nat.choose (k - 1) i) * ((k - 1 - i)! * i !) := by
    have hc := Nat.choose_mul_factorial_mul_factorial (n := k - 1) (k := i) (by omega)
    conv_lhs => rw [hk, Nat.factorial_succ, ← hc]
    rw [← hk]
    ring
  have hpos : 0 < (k - 1 - i)! * i ! := Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  rw [hfact] at hle
  have hmle : n - i ≤ k * Nat.choose (k - 1) i := Nat.le_of_mul_le_mul_right hle hpos
  calc n - i ≤ k * Nat.choose (k - 1) i := hmle
    _ ≤ k * 2 ^ (k - 1) := Nat.mul_le_mul_left _ (Nat.choose_le_two_pow _ _)
    _ ≤ k * 2 ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- **ELS93 bound**, the plausible lemma target: if the deficiency is
    defined and ≥ 1 (with `2k ≤ n`, `k ≥ 2`), then `n ≪ 2^k·√k` —
    stated with an explicit constant existential and `√k ≤ k` relaxed
    to the clean form `n ≤ C · 2^k · k` for a first landing (the √k
    refinement can follow). -/
theorem els93_bound :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ n k : ℕ, 2 * k ≤ n → 2 ≤ k →
      DeficiencyDefined n k → 1 ≤ deficiency n k →
      n ≤ C * 2 ^ k * k := by
  refine ⟨2, by norm_num, ?_⟩
  intro n k hkn hk hdef hdefic
  unfold deficiency at hdefic
  obtain ⟨i, hi⟩ := Finset.card_pos.1 (Nat.lt_of_succ_le hdefic)
  rw [Finset.mem_filter, Finset.mem_range] at hi
  obtain ⟨hik, hsm⟩ := hi
  have hm : n - i ≠ 0 := by omega
  have hmain : n - i ≤ k * 2 ^ k := sub_le_mul_two_pow n k i hik (by omega) hdef hsm hm
  have hik' : i ≤ k * 2 ^ k := hik.le.trans (Nat.le_mul_of_pos_right k (Nat.two_pow_pos k))
  calc n = (n - i) + i := by omega
    _ ≤ k * 2 ^ k + k * 2 ^ k := Nat.add_le_add hmain hik'
    _ = 2 * 2 ^ k * k := by ring

/-- Sanity: the guard `2k ≤ n` is load-bearing — without it question 2
    trivializes: `C(p, p−1) = p` has every `p − 1 − i` (i < p−1)
    among `1, …, p−1`, all `(p−1)`-smooth, so deficiency `p − 2 → ∞`
    (Barreto's comment).  Recorded as the explicit small instance
    deficiency C(5,4) = 3 with definedness.  -- PROVABLE (decide). -/
example : DeficiencyDefined 5 4 ∧ deficiency 5 4 = 3 ∧ ¬ (2 * 4 ≤ 5) := by
  exact sanity_five_four

end ErdosCandidates.E1093

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Statement matches DB verbatim (re-pulled 2026-08-05).
   - C(7,3)=35: 2 nmid 35, 3 nmid 35 (defined); among 7,6,5 only 6 is
     3-smooth. Deficiency 1. Correct.
   - C(44,8)=177232627: no prime <= 8 divides it (verified 2,3,5,7).
     8-smooth among 44..37: 42 (=2*3*7) and 40 (=2^3*5). Deficiency 2.
     Correct.
   - C(5,4)=5: defined (2 nmid 5, 3 nmid 5); among 5,4,3,2: 4,3,2 are
     4-smooth (3 of them). Deficiency 3, and 2*4=8 > 5. Correct.
   - Deficiency-2/3/4/9 lists match DB (post Barreto Dec 2025 correction).
   - Barreto conditional resolution (xyz-type conjectures): comment-sourced,
     matches DB comment post-2215.
   - KSmooth vs Nat.smoothNumbers bridge: correctly notes strict < in
     Mathlib vs <= in the problem; k+1 offset is right.
   - ELS93 bound n << 2^k * sqrt(k): matches DB sections.
-/

