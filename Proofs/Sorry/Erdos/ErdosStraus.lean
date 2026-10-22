import Mathlib

set_option autoImplicit false

namespace ErdosStraus

/-- The literal Erdős–Straus equation with positive natural denominators.
The parameter `n` is required to be positive at division-bearing use sites. -/
def HasEgyptian4 (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

/-- The cleared Erdős–Straus equation with positive natural denominators. -/
def HasEgyptian4Cleared (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    4 * x * y * z = n * (y * z + x * z + x * y)

/-- The separate strict-denominator predicate, not the Erdős–Straus conjecture. -/
def HasEgyptian4Strict (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ x < y ∧ y < z ∧
    4 * x * y * z = n * (y * z + x * z + x * y)

example : HasEgyptian4 2 :=
  ⟨1, 2, 2, by norm_num, by norm_num, by norm_num, by norm_num⟩

example : HasEgyptian4Cleared 2 :=
  ⟨1, 2, 2, by norm_num, by norm_num, by norm_num, by norm_num⟩

example : HasEgyptian4Strict 3 :=
  ⟨1, 4, 12, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- For positive `n`, clearing denominators gives exactly the natural equation. -/
theorem hasEgyptian4_iff_cleared (n : ℕ) (hn : 1 ≤ n) :
    HasEgyptian4 n ↔ HasEgyptian4Cleared n := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  constructor
  · rintro ⟨x, y, z, hx, hy, hz, heq⟩
    have hxq : (x : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hx)
    have hyq : (y : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hy)
    have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hz)
    refine ⟨x, y, z, hx, hy, hz, ?_⟩
    have hcleared : (4 : ℚ) * x * y * z = n * (y * z + x * z + x * y) := by
      field_simp [hnq, hxq, hyq, hzq] at heq
      nlinarith only [heq]
    exact_mod_cast hcleared
  · rintro ⟨x, y, z, hx, hy, hz, heq⟩
    have hxq : (x : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hx)
    have hyq : (y : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hy)
    have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hz)
    refine ⟨x, y, z, hx, hy, hz, ?_⟩
    have hcleared : (4 : ℚ) * x * y * z = n * (y * z + x * z + x * y) := by
      exact_mod_cast heq
    field_simp [hnq, hxq, hyq, hzq]
    nlinarith only [hcleared]

/-- Scaling all three denominators by positive `k` scales the parameter by `k`. -/
theorem hasEgyptian4Cleared_mul {n k : ℕ} (h : HasEgyptian4Cleared n)
    (hk : 0 < k) : HasEgyptian4Cleared (n * k) := by
  rcases h with ⟨x, y, z, hx, hy, hz, heq⟩
  refine ⟨k * x, k * y, k * z, Nat.mul_pos hk hx, Nat.mul_pos hk hy,
    Nat.mul_pos hk hz, ?_⟩
  calc
    4 * (k * x) * (k * y) * (k * z) = k ^ 3 * (4 * x * y * z) := by ring
    _ = k ^ 3 * (n * (y * z + x * z + x * y)) := by rw [heq]
    _ = (n * k) * ((k * y) * (k * z) + (k * x) * (k * z) +
      (k * x) * (k * y)) := by ring

/-- A solution for every prime implies a solution for every natural `n ≥ 2`.
The prime-case premise is explicit; this does not prove the conjecture. -/
theorem erdosStraus_of_prime
    (h : ∀ p : ℕ, p.Prime → 2 ≤ p → HasEgyptian4Cleared p) :
    ∀ n : ℕ, 2 ≤ n → HasEgyptian4Cleared n := by
  intro n hn
  have hn_ne_one : n ≠ 1 := by omega
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hn_ne_one
  obtain ⟨k, hnk⟩ := hpdvd
  have hk : 0 < k := by
    by_contra hk
    have hk_zero : k = 0 := by omega
    rw [hk_zero, Nat.mul_zero] at hnk
    omega
  rw [hnk]
  exact hasEgyptian4Cleared_mul (h p hp hp.two_le) hk

example : 1 ≤ (2 : ℕ) ∧ HasEgyptian4 2 ∧ HasEgyptian4Cleared 2 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · exact ⟨1, 2, 2, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1, 2, 2, by norm_num, by norm_num, by norm_num, by norm_num⟩

example : HasEgyptian4Cleared 4 :=
  hasEgyptian4Cleared_mul (n := 2) (k := 2)
    ⟨1, 2, 2, by norm_num, by norm_num, by norm_num, by norm_num⟩ (by norm_num)

end ErdosStraus
