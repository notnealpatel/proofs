import Mathlib
import Xlib.TPP

open Xlib.TPP
open scoped Pointwise

variable {G : Type*} [Group G] [DecidableEq G] {ℓ : ℕ}

-- Direct proof of right-quotient piFinset closure
theorem tripleProductPropertyR_piFinset' {S T U : Fin ℓ → Finset G}
    (h : ∀ t, TripleProductPropertyR (S t) (T t) (U t)) :
    TripleProductPropertyR (Fintype.piFinset S) (Fintype.piFinset T)
      (Fintype.piFinset U) := by
  intro q₁ hq₁ q₂ hq₂ q₃ hq₃ heq
  obtain ⟨s, hs, s', hs', rfl⟩ := mem_mul_inv.mp hq₁
  obtain ⟨t, ht, t', ht', rfl⟩ := mem_mul_inv.mp hq₂
  obtain ⟨u, hu, u', hu', rfl⟩ := mem_mul_inv.mp hq₃
  simp only [Fintype.mem_piFinset] at hs hs' ht ht' hu hu'
  -- At each coordinate, the right-quotient products multiply to 1
  have coord : ∀ i, s i * (s' i)⁻¹ * (t i * (t' i)⁻¹) * (u i * (u' i)⁻¹) = 1 := by
    intro i
    have := congr_fun heq i
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply] at this
    simpa only [mul_assoc] using this
  have key : ∀ i, s i * (s' i)⁻¹ = 1 ∧ t i * (t' i)⁻¹ = 1 ∧ u i * (u' i)⁻¹ = 1 := by
    intro i
    exact h i (s i * (s' i)⁻¹)
      (mem_mul_inv.mpr ⟨s i, hs i, s' i, hs' i, rfl⟩)
      (t i * (t' i)⁻¹)
      (mem_mul_inv.mpr ⟨t i, ht i, t' i, ht' i, rfl⟩)
      (u i * (u' i)⁻¹)
      (mem_mul_inv.mpr ⟨u i, hu i, u' i, hu' i, rfl⟩)
      (coord i)
  refine ⟨funext fun i => ?_, funext fun i => ?_, funext fun i => ?_⟩
  · show s i * (s' i)⁻¹ = 1; exact (key i).1
  · show t i * (t' i)⁻¹ = 1; exact (key i).2.1
  · show u i * (u' i)⁻¹ = 1; exact (key i).2.2
