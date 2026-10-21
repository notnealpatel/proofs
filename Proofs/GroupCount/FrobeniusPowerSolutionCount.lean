import Mathlib

set_option autoImplicit false

namespace GroupCount.FrobeniusPowerSolutionCount

open Finset

section Decomposition

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

omit [Fintype G] [DecidableEq G] in
/-- `g ^ ((m : ℤ) * k) = 1` whenever `g ^ m = 1`. -/
lemma zpow_natCast_mul_eq_one {g : G} {m : ℕ} (h : g ^ m = 1) (k : ℤ) :
    g ^ ((m : ℤ) * k) = 1 := by
  rw [zpow_mul, zpow_natCast, h, one_zpow]

/-- Coprime splitting: for coprime `s, t`, the solutions of `x ^ (s * t) = 1` are in bijection
with pairs `(y, x)` with `y ^ t = 1`, `x ^ s = 1` and `x` in the centralizer of `y`
(via `g ↦ (t`-part`, s`-part`)` and `(y, x) ↦ x * y`). -/
lemma card_pow_mul_eq_one_eq_sum {s t : ℕ} (hst : Nat.Coprime s t) :
    #{x : G | x ^ (s * t) = 1} =
      ∑ y ∈ ({y : G | y ^ t = 1} : Finset G),
        #{x : G | x ^ s = 1 ∧ x * y = y * x} := by
  set a : ℤ := Nat.gcdA s t
  set b : ℤ := Nat.gcdB s t
  have hab : (s : ℤ) * a + (t : ℤ) * b = 1 := by
    have h := Nat.gcd_eq_gcd_ab s t
    rw [hst.gcd_eq_one, Nat.cast_one] at h
    exact h.symm
  rw [← card_sigma]
  refine card_bij' (fun g _ => (⟨g ^ ((s : ℤ) * a), g ^ ((t : ℤ) * b)⟩ : Σ _ : G, G))
    (fun yx _ => yx.2 * yx.1) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [mem_filter, mem_univ, true_and] at hg
    simp only [mem_sigma, mem_filter, mem_univ, true_and]
    refine ⟨?_, ?_, ?_⟩
    · rw [← zpow_natCast, ← zpow_mul, show (s : ℤ) * a * t = ((s * t : ℕ) : ℤ) * a by rw [Nat.cast_mul]; ring]
      exact zpow_natCast_mul_eq_one hg a
    · rw [← zpow_natCast, ← zpow_mul, show (t : ℤ) * b * s = ((s * t : ℕ) : ℤ) * b by rw [Nat.cast_mul]; ring]
      exact zpow_natCast_mul_eq_one hg b
    · exact (Commute.zpow_zpow_self g _ _).eq
  · intro yx hyx
    simp only [mem_sigma, mem_filter, mem_univ, true_and] at hyx
    obtain ⟨hy, hx, hc⟩ := hyx
    simp only [mem_filter, mem_univ, true_and]
    have hcomm : Commute yx.2 yx.1 := hc
    rw [hcomm.mul_pow, pow_mul, hx, one_pow, one_mul, mul_comm s t, pow_mul, hy, one_pow]
  · intro g _
    simp only
    rw [← zpow_add, add_comm, hab, zpow_one]
  · intro yx hyx
    simp only [mem_sigma, mem_filter, mem_univ, true_and] at hyx
    obtain ⟨hy, hx, hc⟩ := hyx
    have hcomm : Commute yx.2 yx.1 := hc
    have hxsa : yx.2 ^ ((s : ℤ) * a) = 1 := zpow_natCast_mul_eq_one hx a
    have hytb : yx.1 ^ ((t : ℤ) * b) = 1 := zpow_natCast_mul_eq_one hy b
    have hxtb : yx.2 ^ ((t : ℤ) * b) = yx.2 := by
      rw [← mul_one (yx.2 ^ ((t : ℤ) * b)), ← hxsa, ← zpow_add, add_comm, hab, zpow_one]
    have hysa : yx.1 ^ ((s : ℤ) * a) = yx.1 := by
      rw [← mul_one (yx.1 ^ ((s : ℤ) * a)), ← hytb, ← zpow_add, hab, zpow_one]
    rw [hcomm.mul_zpow, hcomm.mul_zpow, hxsa, one_mul, hysa, hxtb, hytb, mul_one]

end Decomposition

end GroupCount.FrobeniusPowerSolutionCount
