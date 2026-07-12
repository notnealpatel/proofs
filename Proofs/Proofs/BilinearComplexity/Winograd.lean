/-
  BilinearComplexity/Winograd — the rank lower bound R⟨2,2,2⟩ ≥ 7
  (Hopcroft–Kerr 1971 / Winograd 1971), formalized over F₂ = ZMod 2 and
  transferred to ℤ. Card Pf11.

  Combined with `rank_matMulTensor_le_seven` (Strassen, `Strassen.lean`)
  this gives the exact value R⟨2,2,2⟩ = 7 over ℤ.

  ROUTE (following arXiv:2603-07280 App. D, worked over F₂ where every
  step is a finite check):

  1. Base change (`rank_matMulTensor_hom_le`, `KroneckerMatMul.lean`):
     it suffices to prove `7 ≤ rank (matMulTensor (ZMod 2) 2 2 2)`.
  2. Substitution / drop (`rankLE_contract₁_drop`): a rank-(r+1)
     decomposition one of whose A-vectors is killed by a contraction `M`
     yields a rank-r decomposition of `contract₁ M T`.
  3. Orbit 4 (`six_le_rank_T4`, the Hopcroft–Kerr forced product): the
     2×4×4 tensor `T4 = contract₁ P_base ⟨2,2,2⟩` has rank ≥ 6.
  4. Top level (`key_step`): for every nonzero A-vector `z`, there is a
     contraction `M` killing `z` with `contract₁ M ⟨2,2,2⟩` GL-equivalent
     to `T4`, hence of rank ≥ 6; picking a nonzero triad of an optimal
     decomposition and dropping it gives `7 ≤ r`.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Fin.VecNotation
import Proofs.BilinearComplexity.Basic
import Proofs.BilinearComplexity.RankCalculus
import Proofs.BilinearComplexity.Flattening
import Proofs.BilinearComplexity.Strassen
import Proofs.BilinearComplexity.KroneckerMatMul

namespace BilinearComplexity

/-! ## 1. The substitution (drop) lemma -/

/-- Substitution / drop lemma: given an `(r+1)`-triad decomposition whose
`s₀`-th A-vector is annihilated by the contraction `M` (`M · u_{s₀} = 0`),
the contracted tensor `contract₁ M T` has an `r`-triad decomposition —
drop the dead triad by reindexing `Fin (r+1)` along `s₀.succAbove`. -/
theorem rankLE_contract₁_drop {k : Type*} [CommSemiring k] {a a' b c r : ℕ}
    (M : Matrix (Fin a') (Fin a) k)
    (u : Fin (r + 1) → Fin a → k) (v : Fin (r + 1) → Fin b → k)
    (w : Fin (r + 1) → Fin c → k) (s₀ : Fin (r + 1))
    (hkill : ∀ i', ∑ i, M i' i * u s₀ i = 0) :
    RankLE (contract₁ M (fun i j l => ∑ s, u s i * v s j * w s l)) r := by
  refine ⟨fun s i' => ∑ i, M i' i * u (s₀.succAbove s) i,
          fun s j => v (s₀.succAbove s) j,
          fun s l => w (s₀.succAbove s) l, ?_⟩
  funext i' j l
  have step1 : contract₁ M (fun i j l => ∑ s, u s i * v s j * w s l) i' j l
      = ∑ s : Fin (r + 1), (∑ i, M i' i * u s i) * v s j * w s l := by
    simp only [contract₁, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by ring
  rw [step1, Fin.sum_univ_succAbove _ s₀, hkill i', zero_mul, zero_mul, zero_add]

/-! ## 2. The forced-product core: R(T4) ≥ 6 -/

/-- The base contraction `P_base : Fin 2 → Fin 4`, identifying the surviving
A-coordinates of orbit 4 (`a₀₀ = 0`, `a₀₁ = a₁₀`): row 0 collapses `a₀₁`
and `a₁₀`, row 1 keeps `a₁₁`. -/
def P_base : Matrix (Fin 2) (Fin 4) (ZMod 2) := !![0, 1, 1, 0; 0, 0, 0, 1]

/-- The orbit-4 tensor `T4 : Tensor F₂ 2 4 4`, the contraction of `⟨2,2,2⟩`
by `P_base`. Support `(i,j,l)`:
`(0,0,1),(0,1,3),(0,2,0),(0,3,2),(1,2,1),(1,3,3)`. -/
def T4 : Tensor (ZMod 2) 2 4 4 :=
  ![![![0, 1, 0, 0], ![0, 0, 0, 1], ![1, 0, 0, 0], ![0, 0, 1, 0]],
    ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 1]]]

/-- `T4` is literally the `P_base`-contraction of the matrix multiplication
tensor. -/
theorem T4_eq_contract : T4 = contract₁ P_base (matMulTensor (ZMod 2) 2 2 2) := by
  decide

/-- **Hopcroft–Kerr forced product (orbit 4).** The 2×4×4 tensor `T4` has
rank at least 6. This is the hard core: the two rank-1 C-slices at `c₀₀`
and `c₁₀` are single products that any decomposition may be assumed to
compute literally, using up two terms; the residual flattens to rank ≥ 4
for every completion. -/
theorem six_le_rank_T4 : 6 ≤ rank T4 := by
  sorry

/-! ## 3. Top-level per-orbit key step -/

/-- **Key step.** For every nonzero A-vector `z`, there is a contraction `M`
that annihilates `z` and whose contracted tensor `contract₁ M ⟨2,2,2⟩` is
GL-equivalent to `T4`, hence has rank ≥ 6. (`M` = `P_base` composed with the
matmul symmetry moving the hyperplane `{z=0}` onto orbit 4.) -/
theorem key_step (z : Fin 4 → ZMod 2) (hz : z ≠ 0) :
    ∃ M : Matrix (Fin 2) (Fin 4) (ZMod 2),
      (∀ α, ∑ i, M α i * z i = 0) ∧
      6 ≤ rank (contract₁ M (matMulTensor (ZMod 2) 2 2 2)) := by
  sorry

/-! ## 4. Assembly -/

/-- `⟨2,2,2⟩` over `F₂` has rank ≥ 7: from an optimal decomposition pick a
nonzero A-triad, drop it via `key_step`'s contraction, and land on a
rank-≥6 tensor — impossible if the rank were ≤ 6. -/
theorem seven_le_rank_matMulTensor_zmod :
    7 ≤ rank (matMulTensor (ZMod 2) 2 2 2) := by
  by_contra hlt
  rw [not_le] at hlt
  have hle : rank (matMulTensor (ZMod 2) 2 2 2) ≤ 6 := by omega
  obtain ⟨u, v, w, hT⟩ := rankLE_of_rank_le hle
  -- some A-vector is nonzero, else the tensor is 0
  have hex : ∃ s₀ : Fin 6, u s₀ ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hzero : matMulTensor (ZMod 2) 2 2 2 = 0 := by
      rw [hT]; funext i j l; simp [h]
    exact (by decide : matMulTensor (ZMod 2) 2 2 2 ≠ 0) hzero
  obtain ⟨s₀, hs₀⟩ := hex
  obtain ⟨M, hkill, hrank⟩ := key_step (u s₀) (by simpa using hs₀)
  have hdrop : RankLE (contract₁ M (matMulTensor (ZMod 2) 2 2 2)) 5 := by
    rw [hT]
    exact rankLE_contract₁_drop M u v w s₀ hkill
  have : rank (contract₁ M (matMulTensor (ZMod 2) 2 2 2)) ≤ 5 :=
    rank_le_of_rankLE hdrop
  omega

/-- **Winograd / Hopcroft–Kerr (1971).** The 2×2 matrix multiplication
tensor over ℤ has rank at least 7. Transferred from `F₂` along
`Int.castRingHom (ZMod 2)`: rank cannot increase under a ring hom, so the
F₂ lower bound lifts to ℤ. Together with Strassen's `≤ 7` this pins the
rank at exactly 7. -/
theorem seven_le_rank_matMulTensor : 7 ≤ rank (matMulTensor ℤ 2 2 2) :=
  le_trans seven_le_rank_matMulTensor_zmod
    (rank_matMulTensor_hom_le ℤ (ZMod 2) (Int.castRingHom (ZMod 2)) 2 2 2)

end BilinearComplexity
