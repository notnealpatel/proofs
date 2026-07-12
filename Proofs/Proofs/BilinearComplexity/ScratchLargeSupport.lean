import Mathlib.LinearAlgebra.Matrix.Rank

/-!
Scratch module: prove the "large support" lemma in isolation, then its proof
will be inlined into `SliceRank.lean`.
-/

open Finset in
/-- **Large-support lemma.** A subspace `V ⊆ (ι → K)` over a field contains a
vector whose number of nonzero coordinates is at least `finrank K V`. -/
theorem exists_mem_support_card_ge {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [Field K] [DecidableEq K] (V : Submodule K (ι → K)) :
    ∃ v ∈ V, Module.finrank K V ≤ (Finset.univ.filter fun i => v i ≠ 0).card := by
  sorry
