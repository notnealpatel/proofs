import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace SchurNumbers

/-- A finite set is sum-free when it contains no solution of `x + y = z`,
including solutions with `x = y`. -/
def SumFree (S : Finset ℕ) : Prop := ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x + y ≠ z

instance (S : Finset ℕ) : Decidable (SumFree S) := by
  unfold SumFree
  infer_instance

/-- The color class restricted to the integers from `1` through `m`. -/
def colorClass (m : ℕ) (n : ℕ) (c : ℕ → Fin n) (i : Fin n) : Finset ℕ :=
  (Finset.Icc 1 m).filter (fun k => c k = i)

/-- A total coloring whose classes on `1` through `m` are sum-free.
The total-function requirement excludes zero colors, even when `m = 0`. -/
def SchurColorable (n m : ℕ) : Prop :=
  ∃ c : ℕ → Fin n, ∀ i : Fin n, SumFree (colorClass m n c i)

example : SumFree ({1} : Finset ℕ) := by decide
example : ¬ SumFree ({1, 2} : Finset ℕ) := by decide
example : colorClass 1 1 (fun _ => 0) 0 = {1} := by decide
example : SchurColorable 1 0 := by
  refine ⟨fun _ => 0, ?_⟩
  intro i
  fin_cases i
  exact (by decide : SumFree (colorClass 0 1 (fun _ => 0) 0))
example (m : ℕ) : ¬ SchurColorable 0 m := by
  rintro ⟨c, _⟩
  exact Fin.elim0 (c 0)

/-- Every subset of a sum-free finite set is sum-free. -/
theorem SumFree.subset {S T : Finset ℕ} (hT : SumFree T) (h : S ⊆ T) : SumFree S := by
  intro x hx y hy z hz
  exact hT x (h hx) y (h hy) z (h hz)

/-- Restricting the interval preserves a sum-free coloring. -/
theorem SchurColorable.mono {n m m' : ℕ} (h : SchurColorable n m) (hm : m' ≤ m) :
    SchurColorable n m' := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun i => (hc i).subset ?_⟩
  intro k hk
  simp only [colorClass, Finset.mem_filter, Finset.mem_Icc] at hk ⊢
  exact ⟨⟨hk.1.1, hk.1.2.trans hm⟩, hk.2⟩

private theorem no_monochromatic_sum {n m : ℕ} {c : ℕ → Fin n}
    (hc : ∀ i, SumFree (colorClass m n c i))
    {x y z : ℕ} (hx : x ∈ Finset.Icc 1 m) (hy : y ∈ Finset.Icc 1 m)
    (hz : z ∈ Finset.Icc 1 m) (hxy : x + y = z)
    (hcx : c x = c z) (hcy : c y = c z) : False := by
  exact hc (c z) x (Finset.mem_filter.mpr ⟨hx, hcx⟩)
    y (Finset.mem_filter.mpr ⟨hy, hcy⟩)
    z (Finset.mem_filter.mpr ⟨hz, rfl⟩) hxy

/-- The largest interval admitting one sum-free color has length one. -/
theorem schur_one : IsGreatest {m : ℕ | SchurColorable 1 m} 1 := by
  constructor
  · refine ⟨fun _ => 0, ?_⟩
    intro i
    fin_cases i
    exact (by decide : SumFree (colorClass 1 1 (fun _ => 0) 0))
  · intro m hm
    by_contra hle
    have h2 : 2 ≤ m := by omega
    obtain ⟨c, hc⟩ := SchurColorable.mono hm h2
    exact no_monochromatic_sum hc (by decide : 1 ∈ Finset.Icc 1 2)
      (by decide : 1 ∈ Finset.Icc 1 2) (by decide : 2 ∈ Finset.Icc 1 2)
      rfl (Subsingleton.elim _ _) (Subsingleton.elim _ _)

private theorem not_two_five : ¬ SchurColorable 2 5 := by
  rintro ⟨c, hc⟩
  have h11 : c 1 ≠ c 2 := by
    intro h
    exact no_monochromatic_sum hc (by decide : 1 ∈ Finset.Icc 1 5)
      (by decide : 1 ∈ Finset.Icc 1 5) (by decide : 2 ∈ Finset.Icc 1 5) rfl h h
  have h22 : c 2 ≠ c 4 := by
    intro h
    exact no_monochromatic_sum hc (by decide : 2 ∈ Finset.Icc 1 5)
      (by decide : 2 ∈ Finset.Icc 1 5) (by decide : 4 ∈ Finset.Icc 1 5) rfl h h
  have h13 : ¬ (c 1 = c 4 ∧ c 3 = c 4) := by
    rintro ⟨h1, h3⟩
    exact no_monochromatic_sum hc (by decide : 1 ∈ Finset.Icc 1 5)
      (by decide : 3 ∈ Finset.Icc 1 5) (by decide : 4 ∈ Finset.Icc 1 5) rfl h1 h3
  have h23 : ¬ (c 2 = c 5 ∧ c 3 = c 5) := by
    rintro ⟨h2, h3⟩
    exact no_monochromatic_sum hc (by decide : 2 ∈ Finset.Icc 1 5)
      (by decide : 3 ∈ Finset.Icc 1 5) (by decide : 5 ∈ Finset.Icc 1 5) rfl h2 h3
  have h14 : ¬ (c 1 = c 5 ∧ c 4 = c 5) := by
    rintro ⟨h1, h4⟩
    exact no_monochromatic_sum hc (by decide : 1 ∈ Finset.Icc 1 5)
      (by decide : 4 ∈ Finset.Icc 1 5) (by decide : 5 ∈ Finset.Icc 1 5) rfl h1 h4
  have hcolors : ∀ a b d e f : Fin 2, a ≠ b → b ≠ e →
      ¬ (a = e ∧ d = e) → ¬ (b = f ∧ d = f) → ¬ (a = f ∧ e = f) → False := by
    decide
  exact hcolors (c 1) (c 2) (c 3) (c 4) (c 5) h11 h22 h13 h23 h14

/-- The largest interval admitting two sum-free colors has length four. -/
theorem schur_two : IsGreatest {m : ℕ | SchurColorable 2 m} 4 := by
  constructor
  · let c : ℕ → Fin 2 := fun k => if k ∈ ({1, 4} : Finset ℕ) then 0 else 1
    refine ⟨c, ?_⟩
    intro i
    fin_cases i
    · change SumFree (colorClass 4 2 c 0)
      have hclass : colorClass 4 2 c 0 = {1, 4} := by decide
      rw [hclass]
      decide
    · change SumFree (colorClass 4 2 c 1)
      have hclass : colorClass 4 2 c 1 = {2, 3} := by decide
      rw [hclass]
      decide
  · intro m hm
    by_contra hle
    have h5 : 5 ≤ m := by omega
    exact not_two_five (SchurColorable.mono hm h5)

/-- The classical three-color partition witnesses an interval of length thirteen. -/
theorem schur_three_lower : SchurColorable 3 13 := by
  let c : ℕ → Fin 3 := fun k =>
    if k ∈ ({1, 4, 10, 13} : Finset ℕ) then 0
    else if k ∈ ({2, 3, 11, 12} : Finset ℕ) then 1 else 2
  refine ⟨c, ?_⟩
  intro i
  fin_cases i
  · change SumFree (colorClass 13 3 c 0)
    have hclass : colorClass 13 3 c 0 = {1, 4, 10, 13} := by decide
    rw [hclass]
    decide
  · change SumFree (colorClass 13 3 c 1)
    have hclass : colorClass 13 3 c 1 = {2, 3, 11, 12} := by decide
    rw [hclass]
    decide
  · change SumFree (colorClass 13 3 c 2)
    have hclass : colorClass 13 3 c 2 = {5, 6, 7, 8, 9} := by decide
    rw [hclass]
    decide

example : SchurColorable 1 1 := schur_one.1
example : SchurColorable 2 4 := schur_two.1
example : SchurColorable 3 13 := schur_three_lower

end SchurNumbers
