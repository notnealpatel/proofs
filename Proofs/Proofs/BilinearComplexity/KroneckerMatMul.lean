/-
  BilinearComplexity/KroneckerMatMul — ring-hom transfer of tensor-rank
  bounds and the Kronecker identity for matrix multiplication tensors.

  Two capabilities the Omega campaign (roadmap priority 3) needs on top of
  the Pl7 rank calculus (`Basic.lean`, `RankCalculus.lean`) and the
  Strassen witness (`Strassen.lean`):

    · **Ring-hom transfer.** A `RingHom φ : k →+* k'` pushes an r-triad
      decomposition forward (`RankLE.map`), and fixes the matrix
      multiplication tensor entrywise (`matMulTensor_map`, since its entries
      are `0`/`1`), so `R⟨a,b,c⟩` over `k'` is at most `R⟨a,b,c⟩` over `k`
      (`rank_matMulTensor_hom_le`). Instantiated at `Int.castRingHom ℝ` this
      transports Strassen's `R⟨2,2,2⟩ ≤ 7` from ℤ (`Strassen.lean`) to ℝ
      (`rank_matMulTensor_le_seven_real`).

    · **Kronecker identity.** The Pl7 Kronecker product `kron` of two
      matrix multiplication tensors is, up to a mode-wise `Fin`-relabeling,
      the matrix multiplication tensor of the products:
      `⟨a,b,c⟩ ⊗ ⟨a',b',c'⟩ ≅ ⟨aa',bb',cc'⟩` (`reindex_kron_matMulTensor`).
      The relabeling `kronMulEquiv` is a middle-two-exchange on packed
      `Fin` products: unpack both factors, swap the middle two, repack.
      With `rank_reindex`/`rank_kron_le` this yields submultiplicativity
      `R⟨aa',bb',cc'⟩ ≤ R⟨a,b,c⟩·R⟨a',b',c'⟩` (`rank_matMulTensor_mul_le`),
      its `m`-fold iterate (`rank_matMulTensor_pow_le`), and the Strassen
      corollary `R⟨2ᵐ,2ᵐ,2ᵐ⟩ ≤ 7ᵐ` over ℝ
      (`rank_matMulTensor_two_pow_le_real`).

  INDEX PACKING (see `Basic.lean` header): all pairs are row-major
  `finProdFinEquiv`-packed (first component slow). `kronMulEquiv a b a' b'`
  identifies `Fin ((a*b)*(a'*b'))` with `Fin ((a*a')*(b*b'))` by unpacking
  to `((Fin a × Fin b) × (Fin a' × Fin b'))`, exchanging the two middle
  factors to `((Fin a × Fin a') × (Fin b × Fin b'))`, and repacking — this
  is exactly the reshuffle that turns a `kron` of matMul tensors into a
  single matMul tensor of the products.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Proofs.BilinearComplexity.RankCalculus
import Proofs.BilinearComplexity.Strassen

namespace BilinearComplexity

/-! ## Part A — ring-hom transfer -/

/-- A ring homomorphism `φ : k →+* k'` pushes an `r`-triad decomposition
forward: apply `φ` to every vector of the triads (`map_sum`, `map_mul`). -/
theorem RankLE.map {k k' : Type*} [CommSemiring k] [CommSemiring k']
    (φ : k →+* k') {a b c : ℕ} {T : Tensor k a b c} {r : ℕ}
    (h : RankLE T r) : RankLE (fun i j l => φ (T i j l)) r := by
  obtain ⟨u, v, w, rfl⟩ := h
  refine ⟨fun s i => φ (u s i), fun s j => φ (v s j), fun s l => φ (w s l), ?_⟩
  funext i j l
  simp only [map_sum, map_mul]

/-- A ring homomorphism fixes the matrix multiplication tensor entrywise:
its entries are `0`/`1`, and `φ` preserves both (`apply_ite`, `map_one`,
`map_zero`). -/
theorem matMulTensor_map (k k' : Type*) [CommSemiring k] [CommSemiring k']
    (φ : k →+* k') (a b c : ℕ) :
    (fun i j l => φ (matMulTensor k a b c i j l)) = matMulTensor k' a b c := by
  funext x y z
  simp only [matMulTensor_apply, apply_ite φ, map_one, map_zero]

/-- Tensor rank of the matrix multiplication tensor cannot increase under a
ring homomorphism: transfer the decomposition and rewrite by
`matMulTensor_map`. -/
theorem rank_matMulTensor_hom_le (k k' : Type*) [CommSemiring k]
    [CommSemiring k'] (φ : k →+* k') (a b c : ℕ) :
    rank (matMulTensor k' a b c) ≤ rank (matMulTensor k a b c) := by
  have h := (rankLE_rank (matMulTensor k a b c)).map φ
  rw [matMulTensor_map] at h
  exact rank_le_of_rankLE h

/-- **Strassen over ℝ**: `R⟨2,2,2⟩ ≤ 7` over the reals, transferred from the
ℤ witness (`Strassen.lean`) along `Int.castRingHom ℝ`. -/
theorem rank_matMulTensor_le_seven_real : rank (matMulTensor ℝ 2 2 2) ≤ 7 :=
  le_trans (rank_matMulTensor_hom_le ℤ ℝ (Int.castRingHom ℝ) 2 2 2)
    rank_matMulTensor_le_seven

/-! ## Part B — Kronecker identity and submultiplicativity -/

/-- `Fin ((a*b)*(a'*b')) ≃ Fin ((a*a')*(b*b'))`: unpack both factors to
`((Fin a × Fin b) × (Fin a' × Fin b'))`, exchange the two middle factors to
`((Fin a × Fin a') × (Fin b × Fin b'))`, and repack. This is the
reshuffle that turns `kron ⟨a,b,c⟩ ⟨a',b',c'⟩` into `⟨aa',bb',cc'⟩`. -/
def kronMulEquiv (a b a' b' : ℕ) :
    Fin ((a * b) * (a' * b')) ≃ Fin ((a * a') * (b * b')) :=
  finProdFinEquiv.symm.trans
    ((finProdFinEquiv.symm.prodCongr finProdFinEquiv.symm).trans
      ((Equiv.prodProdProdComm (Fin a) (Fin b) (Fin a') (Fin b')).trans
        ((finProdFinEquiv.prodCongr finProdFinEquiv).trans finProdFinEquiv)))

/-- **Kronecker identity for matrix multiplication tensors.** Relabeling the
three modes of `kron ⟨a,b,c⟩ ⟨a',b',c'⟩` by the middle-two-exchange
equivalences gives `⟨aa',bb',cc'⟩` on the nose. Both sides are entrywise
`0`/`1` indicators; the product of the two factor indicators is `1` exactly
when all six component index equalities hold, which is precisely the single
indicator of the product tensor after unpacking each packed equality into
its two components (`pair_eq`). -/
theorem reindex_kron_matMulTensor (k : Type*) [CommSemiring k]
    (a b c a' b' c' : ℕ) :
    reindex (kronMulEquiv a b a' b') (kronMulEquiv b c b' c')
        (kronMulEquiv c a c' a')
        (kron (matMulTensor k a b c) (matMulTensor k a' b' c'))
      = matMulTensor k (a * a') (b * b') (c * c') := by
  have pair_eq : ∀ {m n : ℕ} (x y : Fin (m * n)),
      (x = y) ↔ ((finProdFinEquiv.symm x).1 = (finProdFinEquiv.symm y).1
        ∧ (finProdFinEquiv.symm x).2 = (finProdFinEquiv.symm y).2) := by
    intro m n x y
    rw [← Prod.ext_iff, Equiv.apply_eq_iff_eq]
  funext i j l
  simp only [reindex, kron_apply, matMulTensor_apply, kronMulEquiv,
    Equiv.symm_trans_apply, Equiv.prodCongr_symm, Equiv.prodProdProdComm_symm,
    Equiv.symm_symm, Equiv.prodProdProdComm_apply, Prod.map_apply',
    Equiv.symm_apply_apply, ite_zero_mul_ite_zero, mul_one]
  refine if_congr ?_ rfl rfl
  simp only [pair_eq]
  tauto

/-- Submultiplicativity of matrix multiplication tensor rank under
products: `R⟨aa',bb',cc'⟩ ≤ R⟨a,b,c⟩·R⟨a',b',c'⟩`. Undo the Kronecker
identity, then apply reindex-invariance and Kronecker submultiplicativity. -/
theorem rank_matMulTensor_mul_le (k : Type*) [CommSemiring k]
    (a b c a' b' c' : ℕ) :
    rank (matMulTensor k (a * a') (b * b') (c * c'))
      ≤ rank (matMulTensor k a b c) * rank (matMulTensor k a' b' c') := by
  rw [← reindex_kron_matMulTensor k a b c a' b' c', rank_reindex]
  exact rank_kron_le _ _

/-- `m`-fold iterate of submultiplicativity: `R⟨nᵐ,nᵐ,nᵐ⟩ ≤ R⟨n,n,n⟩ᵐ`. -/
theorem rank_matMulTensor_pow_le (k : Type*) [CommSemiring k] (n m : ℕ) :
    rank (matMulTensor k (n ^ m) (n ^ m) (n ^ m))
      ≤ rank (matMulTensor k n n n) ^ m := by
  induction m with
  | zero =>
    simp only [pow_zero]
    exact rank_le_of_rankLE (rankLE_matMulTensor_one k)
  | succ m ih =>
    simp only [pow_succ]
    calc rank (matMulTensor k (n ^ m * n) (n ^ m * n) (n ^ m * n))
        ≤ rank (matMulTensor k (n ^ m) (n ^ m) (n ^ m))
            * rank (matMulTensor k n n n) :=
          rank_matMulTensor_mul_le k (n ^ m) (n ^ m) (n ^ m) n n n
      _ ≤ rank (matMulTensor k n n n) ^ m * rank (matMulTensor k n n n) :=
          Nat.mul_le_mul ih (le_refl _)

/-- **Strassen's asymptotic bound over ℝ**: `R⟨2ᵐ,2ᵐ,2ᵐ⟩ ≤ 7ᵐ`. The pow
lemma at `n := 2` over ℝ, then the real seven-bound raised to the `m`. -/
theorem rank_matMulTensor_two_pow_le_real (m : ℕ) :
    rank (matMulTensor ℝ (2 ^ m) (2 ^ m) (2 ^ m)) ≤ 7 ^ m :=
  le_trans (rank_matMulTensor_pow_le ℝ 2 m)
    (Nat.pow_le_pow_left rank_matMulTensor_le_seven_real m)

end BilinearComplexity
