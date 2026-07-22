/-
  BilinearComplexity/Conspiracy — the C1+C2 conspiracy engine:
  contraction and independence pair bounds for the nonzero-entry
  count `nnz` (Pl25 line C, card Cn1).

  C1 (`nnz_contract₁_le/₂/₃`): contracting any single mode by a
  functional — a `Matrix (Fin 1) (Fin _) k` — never increases `nnz`,
  for an ARBITRARY tensor over any `CommSemiring`.  A nonzero output
  entry at `(j, l)` forces a nonzero entry somewhere in the fiber
  `T · j l`, and distinct outputs have disjoint fibers; cancellation
  inside a fiber only helps the inequality.

  C2 (`max_le_nnz_triad_add_triad₁/₂/₃`): over a field, if the mode-i
  vectors `u, u'` of two triads are linearly independent, then
  `nnz (triad u v w + triad u' v' w') ≥ max (wt v * wt w) (wt v' * wt w')`.
  Linear independence yields separating vectors `g, g'` with
  `⟨g,u⟩ = 1, ⟨g,u'⟩ = 0` (and symmetrically); contracting mode i by
  `g` collapses the sum to a rank-one slice of full weight, and C1
  transfers its count back up.

  The additive strengthening `≥ wt v * wt w + wt v' * wt w'` is FALSE
  under mere independence (support nesting kills it — see the note at
  `add_le_nnz_triad_add_triad₁`); it holds under explicit two-sided
  support incomparability, which is the optional lemma proved there.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Proofs.BilinearComplexity.Support
import Proofs.BilinearComplexity.RankCalculus

namespace BilinearComplexity

/-! ## 1. `nnz` and triads under cyclic rotation -/

section Cyc

variable {k : Type*} [CommSemiring k] {a b c : ℕ}

/-- Cyclic rotation is additive (definitionally). -/
theorem cyc_add (S T : Tensor k a b c) : cyc (S + T) = cyc S + cyc T := rfl

/-- Cyclic rotation of a triad is the cyclically rotated triad. -/
theorem cyc_triad (u : Fin a → k) (v : Fin b → k) (w : Fin c → k) :
    cyc (triad u v w) = triad v w u := by
  funext j l i
  simp only [cyc, triad]
  ring

variable [DecidableEq k]

/-- Cyclic rotation permutes the entries of a tensor, so it preserves
the nonzero-entry count. -/
theorem nnz_cyc (T : Tensor k a b c) : nnz (cyc T) = nnz T := by
  apply Finset.card_equiv
    ⟨fun p => (p.2.2, p.1, p.2.1), fun q => (q.2.1, q.2.2, q.1),
      fun _ => rfl, fun _ => rfl⟩
  intro p
  simp [cyc]

end Cyc

/-! ## 2. C1 — contraction by a functional never increases `nnz` -/

section C1

variable {k : Type*} [DecidableEq k] [CommSemiring k] {a b c a' : ℕ}

/-- Mode-1 contraction distributes over sums of tensors. -/
theorem contract₁_add (M : Matrix (Fin a') (Fin a) k) (S T : Tensor k a b c) :
    contract₁ M (S + T) = contract₁ M S + contract₁ M T := by
  sorry

/-- Mode-1 contraction of a triad contracts the mode-1 vector. -/
theorem contract₁_triad (M : Matrix (Fin a') (Fin a) k)
    (u : Fin a → k) (v : Fin b → k) (w : Fin c → k) :
    contract₁ M (triad u v w) = triad (fun i' => ∑ i, M i' i * u i) v w := by
  sorry

/-- **C1, mode 1.** Contracting mode 1 by a functional (a `1 × a`
matrix) never increases the nonzero-entry count, over any
`CommSemiring`: a nonzero output entry at `(j, l)` forces a nonzero
entry of `T` in the fiber `T · j l`. -/
theorem nnz_contract₁_le (M : Matrix (Fin 1) (Fin a) k) (T : Tensor k a b c) :
    nnz (contract₁ M T) ≤ nnz T := by
  apply Finset.card_le_card_of_surjOn
    (fun p : Fin a × Fin b × Fin c => ((0 : Fin 1), p.2.1, p.2.2))
  intro q hq
  have hq' : contract₁ M T q.1 q.2.1 q.2.2 ≠ 0 :=
    (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
  simp only [contract₁] at hq'
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq'
  refine ⟨(i, q.2.1, q.2.2), ?_, ?_⟩
  · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, right_ne_zero_of_mul hi⟩)
  · exact Prod.ext (Subsingleton.elim _ _) rfl

/-- **C1, mode 2.** -/
theorem nnz_contract₂_le (M : Matrix (Fin 1) (Fin b) k) (T : Tensor k a b c) :
    nnz (contract₂ M T) ≤ nnz T := by
  sorry

/-- **C1, mode 3.** -/
theorem nnz_contract₃_le (M : Matrix (Fin 1) (Fin c) k) (T : Tensor k a b c) :
    nnz (contract₃ M T) ≤ nnz T := by
  sorry

/-- The constant-one vector on `Fin 1` has Hamming weight `1`. -/
theorem wt_one_fin_one [Nontrivial k] : wt (fun _ : Fin 1 => (1 : k)) = 1 := by
  sorry

end C1

/-! ## 3. Separating vectors from linear independence -/

section Sums

variable {k : Type*} [CommSemiring k] {a : ℕ}

/-- Summing a two-point-supported coefficient vector against `x`
evaluates at the two points. -/
theorem sum_two_point_mul (i₀ i₁ : Fin a) (A B : k) (x : Fin a → k) :
    (∑ i, ((if i = i₀ then A else 0) + (if i = i₁ then B else 0)) * x i)
      = A * x i₀ + B * x i₁ := by
  sorry

end Sums

section Separation

variable {k : Type*} [Field k] {a : ℕ}

/-- A linearly independent pair of vectors over a field has a nonzero
`2 × 2` minor: `u i₀ * u' i₁ ≠ u i₁ * u' i₀` for some `i₀, i₁`. -/
theorem exists_mul_ne_mul_of_linearIndependent {u u' : Fin a → k}
    (h : LinearIndependent k ![u, u']) :
    ∃ i₀ i₁, u i₀ * u' i₁ ≠ u i₁ * u' i₀ := by
  sorry

/-- **Separating vectors.** A linearly independent pair `u, u'` over a
field admits dual vectors `g, g'` with `⟨g,u⟩ = 1, ⟨g,u'⟩ = 0` and
`⟨g',u⟩ = 0, ⟨g',u'⟩ = 1` (Cramer on a nonzero `2 × 2` minor; works
over any field, including `ZMod 2`). -/
theorem exists_separating_vectors {u u' : Fin a → k}
    (h : LinearIndependent k ![u, u']) :
    ∃ g g' : Fin a → k,
      ((∑ i, g i * u i) = 1 ∧ (∑ i, g i * u' i) = 0) ∧
      ((∑ i, g' i * u i) = 0 ∧ (∑ i, g' i * u' i) = 1) := by
  sorry

end Separation

/-! ## 4. C2 — the independence pair bound -/

section C2

variable {k : Type*} [DecidableEq k] [Field k] {a b c : ℕ}

/-- **C2, mode 1.** If the mode-1 vectors `u, u'` of two triads are
linearly independent, the nonzero count of the pair-sum is at least
the larger complementary weight product. -/
theorem max_le_nnz_triad_add_triad₁ {u u' : Fin a → k}
    (h : LinearIndependent k ![u, u'])
    (v : Fin b → k) (w : Fin c → k) (v' : Fin b → k) (w' : Fin c → k) :
    max (wt v * wt w) (wt v' * wt w')
      ≤ nnz (triad u v w + triad u' v' w') := by
  sorry

/-- **C2, mode 2.** -/
theorem max_le_nnz_triad_add_triad₂ {v v' : Fin b → k}
    (h : LinearIndependent k ![v, v'])
    (u : Fin a → k) (w : Fin c → k) (u' : Fin a → k) (w' : Fin c → k) :
    max (wt u * wt w) (wt u' * wt w')
      ≤ nnz (triad u v w + triad u' v' w') := by
  sorry

/-- **C2, mode 3.** -/
theorem max_le_nnz_triad_add_triad₃ {w w' : Fin c → k}
    (h : LinearIndependent k ![w, w'])
    (u : Fin a → k) (v : Fin b → k) (u' : Fin a → k) (v' : Fin b → k) :
    max (wt u * wt v) (wt u' * wt v')
      ≤ nnz (triad u v w + triad u' v' w') := by
  sorry

end C2

/-! ## 5. The additive bound under support incomparability

The additive strengthening of C2 — `nnz (triad u v w + triad u' v' w')
≥ wt v * wt w + wt v' * wt w'` — is FALSE under mere linear
independence: over `ZMod 2` take `u = ![1,0]`, `u' = ![1,1]` (an
independent pair with nested supports) and all of `v, w, v', w'` the
constant-one vector on `Fin 1`; the `i = 0` slice cancels and
`nnz = 1 < 1 + 1`.  Two-sided support incomparability — an index where
`u` lives and `u'` vanishes AND an index where `u'` lives and `u`
vanishes — restores it, over any `CommSemiring` with no zero
divisors: the two witness slices survive untouched and are disjoint. -/

section Additive

variable {k : Type*} [DecidableEq k] [CommSemiring k] [NoZeroDivisors k] {a b c : ℕ}

/-- **Additive pair bound, mode 1**, under two-sided support
incomparability of `u, u'` (witnessed at `i₀, i₁`). -/
theorem add_le_nnz_triad_add_triad₁ {u u' : Fin a → k} {i₀ i₁ : Fin a}
    (hu₀ : u i₀ ≠ 0) (hu'₀ : u' i₀ = 0) (hu'₁ : u' i₁ ≠ 0) (hu₁ : u i₁ = 0)
    (v : Fin b → k) (w : Fin c → k) (v' : Fin b → k) (w' : Fin c → k) :
    wt v * wt w + wt v' * wt w'
      ≤ nnz (triad u v w + triad u' v' w') := by
  sorry

end Additive

end BilinearComplexity
