import Mathlib
import Xlib.TPP
import Xlib.TPPProd

/-! Scratch: right-quotient TPP product closure via inversion bridge. -/

open Xlib.TPP

open scoped Pointwise

variable {G H : Type*} [Group G] [DecidableEq G] [Fintype G]
  [Group H] [DecidableEq H] [Fintype H]

-- Check if (S ×ˢ S')⁻¹ = S⁻¹ ×ˢ S'⁻¹
example (S : Finset G) (S' : Finset H) : (S ×ˢ S')⁻¹ = S⁻¹ ×ˢ S'⁻¹ := by
  ext ⟨a, b⟩
  simp [Finset.mem_inv', Finset.mem_product, Prod.inv_mk]
