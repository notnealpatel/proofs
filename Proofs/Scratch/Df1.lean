import Mathlib
import Xlib.TPP

/-! Scratch: test that `TripleProductPropertyR` works in the SimultaneousTPP per-triple slot. -/

open Xlib.TPP

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Test: SimultaneousTPP with right-quotient per-triple. -/
def SimultaneousTPP_R {n : ℕ}
    (A B C : Fin n → Finset G) : Prop :=
  (∀ i, TripleProductPropertyR (A i) (B i) (C i)) ∧
    (∀ i j k : Fin n,
      ∀ aᵢ ∈ A i, ∀ aⱼ' ∈ A j, ∀ bⱼ ∈ B j, ∀ bₖ' ∈ B k, ∀ cₖ ∈ C k, ∀ cᵢ' ∈ C i,
        aᵢ * (aⱼ')⁻¹ * bⱼ * (bₖ')⁻¹ * cₖ * (cᵢ')⁻¹ = 1 → i = j ∧ j = k)

#check @SimultaneousTPP_R
