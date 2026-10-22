/-
# A365794: a modulus-four counterexample

OEIS A365794, Seiichi Manyama (Nov 16 2023), and Peter Bala's periodicity
conjecture (Oct 23 2025).
For the entry's Stirling-sum formula, `a(n+2) ≡ -a(n) (mod 4)` and all
values are odd; the residues have period `4`. No positive divisor of
`φ(4) = 2` is an eventual period.
The identification of the Stirling sum with the displayed fractional-power
e.g.f. is not formalized; this is a formula-level refutation.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A365794Refutation

open Finset

/-- A365794: `a(n) = Σ_{k=0}^{n} 2^(n-k) · (∏_{j=0}^{k-1} (4j+3)) · S2(n,k)`,
the `n`-th coefficient of the e.g.f. `(3 - 2 e^{2x})^{-3/4}`.  The natural
subtraction `n - k` is guarded by `k ∈ range (n + 1)`, i.e. `k ≤ n`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), 2 ^ (n - k) * (∏ j ∈ range k, (4 * j + 3)) * Nat.stirlingSecond n k

/-- Example: the first 18 listed terms of A365794. -/
example : (List.range 18).map a =
    [1, 3, 27, 369, 6849, 160803, 4566987, 152204769, 5822610849, 251445000483,
      12098060349147, 641736701136369, 37204969609266849, 2340437711290748163,
      158770522442243864907, 11553653430580844747169, 897732793887437892390849,
      74182365989862425679675843] := by
  decide

/-- **Bala's conjecture (A365794, Peter Bala, Oct 23 2025).**
"the sequence a(n) taken modulo a positive integer k is eventually periodic
with the period dividing phi(k)": for every `k > 0` there are a positive
period `p ∣ φ(k)` and a threshold `N` with `a(n + p) ≡ a(n) (mod k)` for all
`n ≥ N`. -/
def Conjecture : Prop :=
  ∀ k : ℕ, 0 < k → ∃ p N : ℕ, 0 < p ∧ p ∣ Nat.totient k ∧
    ∀ n : ℕ, N ≤ n → a (n + p) % k = a n % k

/-- Modulo `4`, the product `∏_{j<k} (4j+3)` is `3^k`. -/
theorem prod_cast_zmod_four (k : ℕ) :
    ((∏ j ∈ range k, (4 * j + 3) : ℕ) : ZMod 4) = 3 ^ k := by
  push_cast
  have h4 : (4 : ZMod 4) = 0 := rfl
  simp [h4]

/-- Modulo `4` only the last two Stirling terms survive:
`a(m+2) ≡ 3^(m+2) + 2 · 3^(m+1) · C(m+2, 2) (mod 4)`. -/
theorem a_cast_zmod_four (m : ℕ) : (a (m + 2) : ZMod 4) =
    3 ^ (m + 2) + 2 * 3 ^ (m + 1) * ((m + 2).choose 2 : ℕ) := by
  have hS : (4 : ℕ) ∣ ∑ k ∈ range (m + 1),
      2 ^ (m + 2 - k) * (∏ j ∈ range k, (4 * j + 3)) * Nat.stirlingSecond (m + 2) k := by
    refine Finset.dvd_sum fun k hk => ?_
    have hk' : k < m + 1 := Finset.mem_range.mp hk
    have h2 : 2 ≤ m + 2 - k := by omega
    have hpow : (4 : ℕ) ∣ 2 ^ (m + 2 - k) :=
      (show (4 : ℕ) = 2 ^ 2 by norm_num) ▸ pow_dvd_pow 2 h2
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right hpow _) _
  unfold a
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hzero := (ZMod.natCast_eq_zero_iff _ 4).mpr hS
  have hsub : m + 2 - (m + 1) = 1 := by omega
  simp only [Nat.cast_add, hzero, zero_add, Nat.cast_mul, prod_cast_zmod_four,
    Nat.stirlingSecond_self, Nat.stirlingSecond_succ_self_left, Nat.sub_self, hsub]
  push_cast
  ring

/-- Powers of `3` in `ZMod 4` are `1` or `3`. -/
theorem three_pow_zmod_four (m : ℕ) : (3 : ZMod 4) ^ m = 1 ∨ (3 : ZMod 4) ^ m = 3 := by
  induction m with
  | zero => left; rfl
  | succ m ih =>
    rcases ih with h | h <;> rw [pow_succ, h] <;> decide

/-- `a(n + 2) ≡ -a(n) (mod 4)` for every `n`. -/
theorem a_add_two_zmod_four (n : ℕ) : (a (n + 2) : ZMod 4) = -(a n : ZMod 4) := by
  rcases n with _ | _ | m
  · decide
  · decide
  · rw [a_cast_zmod_four, show m + 1 + 1 + 2 = (m + 2) + 2 by ring, a_cast_zmod_four]
    have hc : ((m + 2 + 2).choose 2 : ℕ) = (m + 2).choose 2 + (m + 3) + (m + 2) := by
      simp only [Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right]
      ring
    rw [hc]
    push_cast
    generalize ((m + 2).choose 2 : ZMod 4) = c
    generalize (m : ZMod 4) = x
    rcases three_pow_zmod_four m with h | h <;>
    · simp only [pow_succ, h]
      revert c x
      decide

/-- Every term of A365794 is odd: `a(n) mod 4 ∈ {1, 3}`. -/
theorem a_cast_zmod_four_odd (n : ℕ) : (a n : ZMod 4) = 1 ∨ (a n : ZMod 4) = 3 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | m
    · decide
    · decide
    · rw [a_add_two_zmod_four]
      rcases ih m (by omega) with h | h <;> rw [h] <;> decide

/-- Supplement: `a(n) mod 4` is periodic with period `4 = 2 φ(4)` from the
start, `a(n + 4) ≡ a(n) (mod 4)`. -/
theorem a_add_four_mod_four (n : ℕ) : a (n + 4) % 4 = a n % 4 := by
  rw [← ZMod.natCast_eq_natCast_iff']
  rw [show n + 4 = (n + 2) + 2 by ring, a_add_two_zmod_four, a_add_two_zmod_four, neg_neg]

/-- At modulus `4`, `a(n+2) ≡ -a(n)` and every `a(n)` is odd.
Thus shift two fails at every index, so no positive divisor of
`φ(4) = 2` can be an eventual period. No conclusion about other moduli
is asserted. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  obtain ⟨p, N, hp, hpdvd, hper⟩ := hconj 4 (by norm_num)
  have htot : Nat.totient 4 = 2 := by decide
  rw [htot] at hpdvd
  have hp12 : p = 1 ∨ p = 2 := by
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpdvd
    omega
  have htwo : a (N + 2) % 4 = a N % 4 := by
    rcases hp12 with rfl | rfl
    · rw [hper (N + 1) (by omega), hper N le_rfl]
    · exact hper N le_rfl
  have hcast : (a (N + 2) : ZMod 4) = (a N : ZMod 4) :=
    (ZMod.natCast_eq_natCast_iff' _ _ 4).mpr htwo
  rw [a_add_two_zmod_four] at hcast
  rcases a_cast_zmod_four_odd N with h | h <;> rw [h] at hcast <;> exact absurd hcast (by decide)

end Candidates.A365794Refutation
