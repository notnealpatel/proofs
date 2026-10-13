import Mathlib

set_option autoImplicit false

namespace SchurNumbers

/-- Every finite coloring of the natural numbers has a monochromatic sum of two positive numbers. -/
theorem exists_mono_sum {κ : Type*} [Finite κ] (c : ℕ → κ) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ c x = c y ∧ c y = c (x + y) := by
  classical
  let fibers : κ → Set ℕ+ := fun i => {p | c (p : ℕ) = i}
  have hfin : (Set.range fibers).Finite := Set.finite_range fibers
  have hcover : (⊤ : Set ℕ+) ⊆ ⋃₀ Set.range fibers := by
    intro p _
    exact Set.mem_sUnion.mpr ⟨fibers (c (p : ℕ)), Set.mem_range_self _, rfl⟩
  obtain ⟨fiber, hfiber, a, ha⟩ :=
    Hindman.exists_FS_of_finite_cover (Set.range fibers) hfin hcover
  obtain ⟨i, rfl⟩ := hfiber
  have hx : c (a.head : ℕ) = i := ha (Hindman.FS.head a)
  have hy : c (a.tail.head : ℕ) = i :=
    ha (Hindman.FS.tail a a.tail.head (Hindman.FS.head a.tail))
  have hsum : c ((a.head + a.tail.head : ℕ+) : ℕ) = i :=
    ha (Hindman.FS.cons a a.tail.head (Hindman.FS.head a.tail))
  refine ⟨a.head, a.tail.head, PNat.pos _, PNat.pos _, hx.trans hy.symm, ?_⟩
  simpa only [PNat.add_coe] using hy.trans hsum.symm

/-- A finite palette admits a uniform bound for a monochromatic positive sum. -/
theorem exists_schur_bound {κ : Type*} [Finite κ] :
    ∃ N : ℕ, ∀ c : ℕ → κ, ∃ x y : ℕ,
      0 < x ∧ 0 < y ∧ x + y ≤ N ∧ c x = c y ∧ c y = c (x + y) := by
  classical
  by_contra h
  have hbad : ∀ N : ℕ, ∃ c : ℕ → κ, ¬ ∃ x y : ℕ,
      0 < x ∧ 0 < y ∧ x + y ≤ N ∧ c x = c y ∧ c y = c (x + y) := by
    intro N
    exact not_forall.mp (fun hN => h ⟨N, hN⟩)
  choose c hc using hbad
  let g : Finset ℕ → ℕ → κ := fun s => c (s.sup id)
  obtain ⟨χ, hχ⟩ := Finset.rado_selection g
  obtain ⟨x, y, hx, hy, hxy, hsum⟩ := exists_mono_sum χ
  let s : Finset ℕ := {x, y, x + y}
  have hxs : x ∈ s := by simp [s]
  have hys : y ∈ s := by simp [s]
  have hsums : x + y ∈ s := by simp [s]
  obtain ⟨t, hst, ht⟩ := hχ s
  have hbound : x + y ≤ t.sup id := Finset.le_sup (f := id) (hst hsums)
  have hxt : χ x = c (t.sup id) x := ht x hxs
  have hyt : χ y = c (t.sup id) y := ht y hys
  have hsumt : χ (x + y) = c (t.sup id) (x + y) := ht (x + y) hsums
  exact hc (t.sup id) ⟨x, y, hx, hy, hbound,
    hxt.symm.trans (hxy.trans hyt), hyt.symm.trans (hsum.trans hsumt)⟩

example : ∃ x y : ℕ, 0 < x ∧ 0 < y ∧
    (fun _ : ℕ => ()) x = (fun _ : ℕ => ()) y ∧
    (fun _ : ℕ => ()) y = (fun _ : ℕ => ()) (x + y) :=
  ⟨1, 1, by decide, by decide, rfl, rfl⟩

example : ∀ c : ℕ → Unit, ∃ x y : ℕ,
    0 < x ∧ 0 < y ∧ x + y ≤ 2 ∧ c x = c y ∧ c y = c (x + y) := by
  intro c
  exact ⟨1, 1, by decide, by decide, by decide,
    Subsingleton.elim _ _, Subsingleton.elim _ _⟩

end SchurNumbers
