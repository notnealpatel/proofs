/-
  BilinearComplexity/Support — generic support-size layer over any
  `[DecidableEq k] [CommSemiring k]`: nonzero-entry count (`nnz`) for
  rectangular 3-tensors and Hamming weight (`wt`) for vectors.

  Foundation of the min-peak lemma farm (Pl25/Sm1).

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import BilinearComplexity.Basic

namespace BilinearComplexity

variable {k : Type*} [DecidableEq k] [CommSemiring k] {a b c : ℕ}

/-! ## 1. Nonzero-entry count for tensors -/

/-- `nnz T` : the number of nonzero entries of a rectangular 3-tensor
`T : Fin a → Fin b → Fin c → k`. Computable for decidable equality. -/
abbrev nnz (T : Tensor k a b c) : ℕ :=
  (Finset.univ.filter fun p : Fin a × Fin b × Fin c => T p.1 p.2.1 p.2.2 ≠ 0).card

theorem nnz_eq_zero_iff {T : Tensor k a b c} : nnz T = 0 ↔ T = 0 := by
  simp only [nnz, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h
    funext i j l
    simp only [Pi.zero_apply]
    by_contra hne
    exact hne (not_not.mp (h (Finset.mem_univ ⟨i, j, l⟩)))
  · intro h
    simp [h]

theorem nnz_zero : nnz (0 : Tensor k a b c) = 0 :=
  nnz_eq_zero_iff.mpr rfl

/-! ## 2. Hamming weight for vectors -/

/-- `wt u` : the Hamming weight (number of nonzero entries) of a vector
`u : Fin n → k`. -/
abbrev wt {n : ℕ} (u : Fin n → k) : ℕ :=
  (Finset.univ.filter fun i : Fin n => u i ≠ 0).card

theorem wt_eq_zero_iff {n : ℕ} {u : Fin n → k} : wt u = 0 ↔ u = 0 := by
  simp only [wt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h
    funext i
    simp only [Pi.zero_apply]
    by_contra hne
    exact hne (not_not.mp (h (Finset.mem_univ i)))
  · intro h
    simp [h]

/-! ## 3. Triad and the multiplicativity of nnz for rank-one tensors -/

/-- A rank-one triad `u ⊗ v ⊗ w` as a tensor. -/
abbrev triad {a b c : ℕ} (u : Fin a → k) (v : Fin b → k) (w : Fin c → k) :
    Tensor k a b c :=
  fun i j l => u i * v j * w l

/-- `nnz (triad u v w) = wt u * wt v * wt w`: a rank-one tensor's nonzero
count is the product of the component Hamming weights. -/
theorem nnz_triad {a b c : ℕ} (u : Fin a → k) (v : Fin b → k) (w : Fin c → k)
    [NoZeroDivisors k] :
    nnz (triad u v w) = wt u * wt v * wt w := by
  simp only [nnz, triad, wt]
  rw [show (Finset.univ.filter fun p : Fin a × Fin b × Fin c =>
      u p.1 * v p.2.1 * w p.2.2 ≠ 0) =
    (Finset.univ.filter fun i : Fin a => u i ≠ 0) ×ˢ
      ((Finset.univ.filter fun j : Fin b => v j ≠ 0) ×ˢ
        (Finset.univ.filter fun l : Fin c => w l ≠ 0)) from ?_]
  · rw [Finset.card_product, Finset.card_product, mul_assoc]
  · ext ⟨i, j, l⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h
      obtain ⟨h1, h2'⟩ := mul_ne_zero_iff.mp h1
      exact ⟨h1, h2', h2⟩
    · rintro ⟨h1, h2, h3⟩
      exact mul_ne_zero (mul_ne_zero h1 h2) h3

end BilinearComplexity
