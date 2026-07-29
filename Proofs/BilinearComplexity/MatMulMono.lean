/-
  BilinearComplexity/MatMulMono — the generic sub-tensor lemma and
  monotonicity of the matrix-multiplication tensor's rank in every
  dimension.

  Pulling a tensor back along arbitrary index maps on each mode never
  increases rank: the decomposition vectors are simply precomposed with
  the maps — no injectivity, no contraction matrices. This strictly
  generalizes `RankCalculus`'s `RankLE.reindex` (which needs
  `Fin`-equivalences) to arbitrary functions, and is exactly the tool
  group-tensor restriction (Om5) will reuse.

    · `RankLE.comp h f g e`  — `RankLE T r → RankLE (T ∘ (f, g, e)) r`
                               for arbitrary `f g e`; `rank_comp_le` is
                               the rank corollary
                               `rank (T ∘ (f, g, e)) ≤ rank T`.
    · `packCastLE ha hb`     — the row-major corner embedding
                               `Fin (a*b) → Fin (a'*b')` sending packed
                               `(i, j)` to `(castLE ha i, castLE hb j)`.
    · `matMulTensor_comp_packCastLE` — `⟨a,b,c⟩` is the pullback of the
                               bigger `⟨a',b',c'⟩` along `packCastLE` on
                               each mode: the smaller matMul tensor is the
                               top-left corner sub-tensor of the bigger.
    · `rank_matMulTensor_mono` — `a ≤ a' → b ≤ b' → c ≤ c' →
                               R⟨a,b,c⟩ ≤ R⟨a',b',c'⟩`, with the cube
                               specialization `rank_matMulTensor_mono_cube`
                               (`n ≤ m → R⟨n,n,n⟩ ≤ R⟨m,m,m⟩`) that feeds
                               the padding argument for `ω ≤ log₂ 7` (Om4).

  Index pairs are packed row-major by `finProdFinEquiv` exactly as in
  `Basic.lean` (first component slow); `packCastLE` respects that packing.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib.Data.Fin.SuccPred
import BilinearComplexity.Basic

namespace BilinearComplexity

/-! ## 1. Generic sub-tensor lemma -/

section Comp

variable {k : Type*} [CommSemiring k]

/-- Pulling a tensor back along arbitrary index maps on each mode never
increases `RankLE`: precompose every decomposition vector with the
corresponding map. This is the strict generalization of `RankLE.reindex`
(which needs `Fin`-equivalences) to arbitrary functions — no injectivity
is required. -/
theorem RankLE.comp {a b c a' b' c' : ℕ} {T : Tensor k a' b' c'} {r : ℕ}
    (h : RankLE T r) (f : Fin a → Fin a') (g : Fin b → Fin b')
    (e : Fin c → Fin c') :
    RankLE (fun i j l => T (f i) (g j) (e l)) r := by
  obtain ⟨u, v, w, rfl⟩ := h
  exact ⟨fun s i => u s (f i), fun s j => v s (g j), fun s l => w s (e l), rfl⟩

/-- Rank never increases when a tensor is pulled back along arbitrary
index maps on each mode. -/
theorem rank_comp_le {a b c a' b' c' : ℕ} (T : Tensor k a' b' c')
    (f : Fin a → Fin a') (g : Fin b → Fin b') (e : Fin c → Fin c') :
    rank (fun i j l => T (f i) (g j) (e l)) ≤ rank T :=
  rank_le_of_rankLE ((rankLE_rank T).comp f g e)

end Comp

/-! ## 2. matMul rank monotonicity -/

/-- The row-major corner embedding of packed indices
`Fin (a*b) → Fin (a'*b')`: unpack `x` to `(i, j)`, embed each component by
`Fin.castLE`, and repack. It realizes the smaller `a × b` index grid as
the top-left corner of the bigger `a' × b'` grid. -/
def packCastLE {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    Fin (a * b) → Fin (a' * b') := fun x =>
  finProdFinEquiv ((finProdFinEquiv.symm x).1.castLE ha,
                   (finProdFinEquiv.symm x).2.castLE hb)

/-- The matrix multiplication tensor `⟨a,b,c⟩` is the pullback of the
bigger tensor `⟨a',b',c'⟩` along `packCastLE` on each mode: the smaller
matMul tensor is exactly the corner sub-tensor of the bigger one. The two
δ-conditions agree because the pack/unpack round-trip cancels
(`Equiv.symm_apply_apply`) and `Fin.castLE` is injective
(`Fin.castLE_inj`). -/
theorem matMulTensor_comp_packCastLE (k : Type*) [CommSemiring k]
    {a b c a' b' c' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    (fun i j l => matMulTensor k a' b' c'
        (packCastLE ha hb i) (packCastLE hb hc j) (packCastLE hc ha l))
      = matMulTensor k a b c := by
  funext i j l
  simp only [matMulTensor_apply, packCastLE, Equiv.symm_apply_apply,
    Fin.castLE_inj]

/-- Matrix multiplication tensor rank is monotone in every dimension:
`R⟨a,b,c⟩ ≤ R⟨a',b',c'⟩` whenever `a ≤ a'`, `b ≤ b'`, `c ≤ c'`. The smaller
tensor is a sub-tensor of the bigger one
(`matMulTensor_comp_packCastLE`), so `rank_comp_le` applies. -/
theorem rank_matMulTensor_mono (k : Type*) [CommSemiring k]
    {a b c a' b' c' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    rank (matMulTensor k a b c) ≤ rank (matMulTensor k a' b' c') := by
  rw [← matMulTensor_comp_packCastLE k ha hb hc]
  exact rank_comp_le (matMulTensor k a' b' c') (packCastLE ha hb)
    (packCastLE hb hc) (packCastLE hc ha)

/-- Cube specialization feeding the padding argument for `ω`: if `n ≤ m`
then `R⟨n,n,n⟩ ≤ R⟨m,m,m⟩`. -/
theorem rank_matMulTensor_mono_cube (k : Type*) [CommSemiring k] {n m : ℕ}
    (h : n ≤ m) :
    rank (matMulTensor k n n n) ≤ rank (matMulTensor k m m m) :=
  rank_matMulTensor_mono k h h h

end BilinearComplexity
