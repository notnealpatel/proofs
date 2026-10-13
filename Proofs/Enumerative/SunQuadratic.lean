import Mathlib

set_option autoImplicit false

namespace Candidates.A141386

/-- The triangular number `t(t+1)/2`, using natural division by the positive divisor 2. -/
def tri (t : ℕ) : ℕ := t * (t + 1) / 2

/-- Representability by two squares and five triangular numbers, in doubled form;
all three witnesses are natural numbers, including zero. -/
def Representable (n : ℕ) : Prop :=
  ∃ x y t : ℕ, 2 * n = 2 * x ^ 2 + 2 * y ^ 2 + 5 * (t * (t + 1))

/-- The literal two-square plus five-triangular-number representation. -/
def Representable' (n : ℕ) : Prop := ∃ x y t : ℕ, n = x ^ 2 + y ^ 2 + 5 * tri t

/-- The seven conjectured exceptions in A141386. -/
def exceptions : Finset ℕ := {3, 11, 12, 27, 129, 138, 273}

example : tri 0 = 0 := rfl
example : tri 3 = 6 := rfl
example : Representable 0 := ⟨0, 0, 0, rfl⟩
example : Representable' 0 := ⟨0, 0, 0, rfl⟩
example : (3 : ℕ) ∈ exceptions := by decide
example : (0 : ℕ) ∉ exceptions := by decide

/-- Doubling a triangular number recovers the consecutive product exactly. -/
theorem two_mul_tri (t : ℕ) : 2 * tri t = t * (t + 1) := by
  have hparity : t % 2 = 0 ∨ (t + 1) % 2 = 0 := by omega
  have hdvd : 2 ∣ t * (t + 1) := by
    rcases hparity with ht | ht
    · exact dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero ht) _
    · exact dvd_mul_of_dvd_right (Nat.dvd_of_mod_eq_zero ht) _
  exact Nat.mul_div_cancel' hdvd

/-- The doubled and literal representations are equivalent with the same witnesses. -/
theorem representable_iff_tri (n : ℕ) : Representable n ↔ Representable' n := by
  have hid (x y t : ℕ) :
      2 * (x ^ 2 + y ^ 2 + 5 * tri t) =
        2 * x ^ 2 + 2 * y ^ 2 + 5 * (t * (t + 1)) := by
    rw [← two_mul_tri t]
    ring
  constructor
  · rintro ⟨x, y, t, h⟩
    refine ⟨x, y, t, ?_⟩
    have heq : 2 * n = 2 * (x ^ 2 + y ^ 2 + 5 * tri t) := h.trans (hid x y t).symm
    omega
  · rintro ⟨x, y, t, h⟩
    exact ⟨x, y, t, by rw [h]; exact hid x y t⟩

/-- Every literal representation has square-root bounds on its witnesses. -/
theorem representation_bounds (n x y t : ℕ)
    (h : n = x ^ 2 + y ^ 2 + 5 * tri t) :
    x ≤ n.sqrt ∧ y ≤ n.sqrt ∧ t ≤ (2 * n).sqrt ∧ t ≤ n := by
  have hx : x * x ≤ n := by nlinarith
  have hy : y * y ≤ n := by nlinarith
  have htprod := two_mul_tri t
  have ht : t * t ≤ 2 * n := by nlinarith
  have htn : t ≤ n := by nlinarith
  exact ⟨Nat.le_sqrt.mpr hx, Nat.le_sqrt.mpr hy, Nat.le_sqrt.mpr ht, htn⟩

/-- Residual search, with a guard preventing truncated subtraction from
creating spurious witnesses. Both finite ranges include zero. -/
def search (n : ℕ) : Bool :=
  (List.range ((2 * n).sqrt + 1)).any fun t =>
    (List.range (n.sqrt + 1)).any fun x =>
      decide (5 * tri t + x ^ 2 ≤ n) &&
        decide ((n - 5 * tri t - x ^ 2).sqrt ^ 2 = n - 5 * tri t - x ^ 2)

example : search 0 = true := by decide
example : search 1 = true := by decide +kernel
example : search 3 = false := by decide +kernel

/-- The guarded residual search is equivalent to unbounded representability. -/
theorem search_eq_true_iff (n : ℕ) : search n = true ↔ Representable n := by
  rw [representable_iff_tri]
  simp only [search, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨t, ht, x, hx, hguard, hsquare⟩
    refine ⟨x, (n - 5 * tri t - x ^ 2).sqrt, t, ?_⟩
    omega
  · rintro ⟨x, y, t, h⟩
    obtain ⟨hx, hy, ht, htn⟩ := representation_bounds n x y t h
    have hres : n - 5 * tri t - x ^ 2 = y * y := by
      have hyy : y ^ 2 = y * y := by ring
      omega
    refine ⟨t, by omega, x, by omega, by omega, ?_⟩
    rw [hres, Nat.sqrt_eq]
    ring

/-- The original finite box loses no unbounded representations. -/
theorem representable_iff_bounded (n : ℕ) : Representable n ↔
    ∃ x ∈ Finset.range (n.sqrt + 1), ∃ y ∈ Finset.range (n.sqrt + 1),
      ∃ t ∈ Finset.range (n + 1),
        2 * n = 2 * x ^ 2 + 2 * y ^ 2 + 5 * (t * (t + 1)) := by
  constructor
  · intro h
    obtain ⟨x, y, t, heq⟩ := h
    have hlit : n = x ^ 2 + y ^ 2 + 5 * tri t := by
      have htri := two_mul_tri t
      nlinarith
    obtain ⟨hx, hy, ht, htn⟩ := representation_bounds n x y t hlit
    exact ⟨x, Finset.mem_range.mpr (by omega),
      y, Finset.mem_range.mpr (by omega),
      t, Finset.mem_range.mpr (by omega), heq⟩
  · rintro ⟨x, hx, y, hy, t, ht, heq⟩
    exact ⟨x, y, t, heq⟩

example : Representable 1 ∧ (1 : ℕ) ∉ exceptions := by
  exact ⟨⟨1, 0, 0, by norm_num⟩, by decide⟩
example : 0 ≤ (0 : ℕ).sqrt ∧ 0 ≤ (2 * (0 : ℕ)).sqrt := by decide

end Candidates.A141386
