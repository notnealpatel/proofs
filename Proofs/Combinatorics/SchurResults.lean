import Combinatorics.SchurNumbers
import Combinatorics.SchurFinite
import Combinatorics.SchurThreeCertificate

set_option autoImplicit false

namespace SchurNumbers

/-- For every positive number of colors, only finitely many interval lengths
admit a sum-free coloring. -/
theorem schur_finite (n : ℕ) (hn : 0 < n) : {m : ℕ | SchurColorable n m}.Finite := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨N, hN⟩ := exists_schur_bound (κ := Fin n)
  apply (Set.finite_Iio N).subset
  intro m hm
  change m < N
  by_contra hlt
  have hNm : N ≤ m := by omega
  obtain ⟨c, hc⟩ := hm
  obtain ⟨x, y, hx, hy, hsum, hxy, hyz⟩ := hN c
  have hxmem : x ∈ colorClass m n c (c (x + y)) := by
    simp only [colorClass, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, hxy.trans hyz⟩
  have hymem : y ∈ colorClass m n c (c (x + y)) := by
    simp only [colorClass, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, hyz⟩
  have hzmem : x + y ∈ colorClass m n c (c (x + y)) := by
    simp only [colorClass, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, hsum.trans hNm⟩, True.intro⟩
  exact hc (c (x + y)) x hxmem y hymem (x + y) hzmem rfl

/-- The largest interval admitting three sum-free colors has length thirteen. -/
theorem schur_three : IsGreatest {m : ℕ | SchurColorable 3 m} 13 := by
  constructor
  · exact schur_three_lower
  · intro m hm
    by_contra hle
    have h14 : 14 ≤ m := by omega
    obtain ⟨c, hc⟩ := SchurColorable.mono hm h14
    apply no_three_coloring c
    intro x y hx hy hsum hxy hyz
    have hxmem : x ∈ colorClass 14 3 c (c (x + y)) := by
      simp only [colorClass, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hx, by omega⟩, hxy.trans hyz⟩
    have hymem : y ∈ colorClass 14 3 c (c (x + y)) := by
      simp only [colorClass, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hy, by omega⟩, hyz⟩
    have hzmem : x + y ∈ colorClass 14 3 c (c (x + y)) := by
      simp only [colorClass, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, hsum⟩, True.intro⟩
    exact hc (c (x + y)) x hxmem y hymem (x + y) hzmem rfl

example : 0 < (1 : ℕ) ∧ SchurColorable 1 1 := ⟨by decide, schur_one.1⟩
example : SchurColorable 3 13 := schur_three_lower
example : Nonempty (Fin 1) := ⟨0⟩
example : Nonempty (Fin 3) := ⟨0⟩

end SchurNumbers
