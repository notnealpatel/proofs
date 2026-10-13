import BilinearComplexity.MatMul22BorderRank
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.MvPolynomial

/-!
The one-direction continuity bridge from Euclidean closure of the complex
rank locus to polynomial-closure border rank. Combined with the n=2
Landsberg--Ottaviani specialization, this excludes rectangular matrix
multiplication from the Euclidean closure below rank 3ℓ. No reverse closure
equivalence or general rectangular Landsberg--Ottaviani theorem is asserted.
-/

set_option autoImplicit false

namespace BilinearComplexity

/-- Euclidean closure of the complex rank-at-most-r entry locus implies
polynomial-closure border rank at most r, by continuity of every polynomial. -/
theorem borderRankLE_of_mem_closure_rankLocus {a b c r : ℕ}
    {T : Tensor ℂ a b c}
    (hT : entries T ∈ closure (rankLocus ℂ a b c r)) : BorderRankLE T r := by
  apply borderRankLE_iff.mpr
  intro p hp
  have hzero : rankLocus ℂ a b c r ⊆
      {x | MvPolynomial.eval x p = (0 : ℂ)} := by
    intro x hx
    change MvPolynomial.eval x p = 0
    have heval := MvPolynomial.mem_vanishingIdeal_iff.mp hp x hx
    simpa only [MvPolynomial.aeval_eq_eval] using heval
  have hclosed : IsClosed {x | MvPolynomial.eval x p = (0 : ℂ)} :=
    isClosed_eq (MvPolynomial.continuous_eval p) continuous_const
  exact closure_minimal hzero hclosed hT

/-- A convergent sequence of complex tensors of rank at most r has
polynomial-closure border rank at most r. Convergence is entrywise in the
standard product topology. -/
theorem borderRankLE_of_tendsto_rankLE {a b c r : ℕ} {T : Tensor ℂ a b c}
    (S : ℕ → Tensor ℂ a b c) (hS : ∀ n, RankLE (S n) r)
    (hlim : Filter.Tendsto (entries ∘ S) Filter.atTop (nhds (entries T))) :
    BorderRankLE T r := by
  apply borderRankLE_of_mem_closure_rankLocus
  apply mem_closure_of_tendsto hlim
  exact Filter.Eventually.of_forall (fun n => ⟨S n, hS n, rfl⟩)

/-- Complex 2×2×ℓ matrix multiplication is outside the Euclidean closure of
rank-at-most-r tensors for 1 ≤ ℓ and r < 3ℓ. This is the n=2 specialization,
not the general rectangular Landsberg--Ottaviani theorem. -/
theorem matMul22_not_mem_closure_rankLocus {ℓ r : ℕ}
    (hℓ : 1 ≤ ℓ) (hr : r < 3 * ℓ) :
    entries (matMulTensor ℂ 2 2 ℓ) ∉
      closure (rankLocus ℂ 4 (2 * ℓ) (ℓ * 2) r) := by
  intro hclosure
  exact matMul22_not_borderRankLE hℓ hr
    (borderRankLE_of_mem_closure_rankLocus hclosure)

example : entries (0 : Tensor ℂ 1 1 1) ∈ closure (rankLocus ℂ 1 1 1 0) := by
  apply subset_closure
  refine ⟨0, ?_, rfl⟩
  refine ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, ?_⟩
  ext i j l
  simp

example : (∀ n : ℕ, RankLE ((fun _ : ℕ => (0 : Tensor ℂ 1 1 1)) n) 0) ∧
    Filter.Tendsto (entries ∘ (fun _ : ℕ => (0 : Tensor ℂ 1 1 1)))
      Filter.atTop (nhds (entries (0 : Tensor ℂ 1 1 1))) := by
  constructor
  · intro n
    refine ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, ?_⟩
    ext i j l
    simp
  · exact tendsto_const_nhds

example : 1 ≤ (1 : ℕ) ∧ 2 < 3 * (1 : ℕ) ∧ Nonempty (Fin 1) :=
  ⟨by decide, by decide, ⟨0⟩⟩

example : entries (matMulTensor ℂ 2 2 1) ∉ closure (rankLocus ℂ 4 2 2 2) :=
  matMul22_not_mem_closure_rankLocus (ℓ := 1) (r := 2) (by decide) (by decide)

end BilinearComplexity
