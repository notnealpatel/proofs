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

  Cn2 stratification (F₂ = `ZMod 2`, Pl25 line C, card Cn2): over F₂
  two NONZERO vectors are linearly independent iff they are UNEQUAL
  (`linearIndependent_pair_iff_ne`), so for a pair of triads with all
  six factors nonzero the conspiracy question stratifies by the set of
  unequal factor pairs — S0 (all equal): the sum annihilates in char 2
  (`tensor_add_self`); S1 (exactly one unequal): the sum collapses to
  a single triad (`triad_add_triad₁/₂/₃`) with EXACT count
  `wt (x + x') *` (shared weights) (`nnz_triad_add_triad₁/₂/₃`);
  S2/S3 (two/three unequal): C2 applies in every unequal mode
  (`max_le_nnz_triad_add_triad₁/₂/₃_of_ne`, conjunctions
  `pair_bounds_shared₁/₂/₃`, `pair_bounds_of_ne`), sharply
  (Scratch/Cn2Sharpness).  Capstone `pair_collapse₁_of_nnz_lt`:
  a pair-sum strictly below both cross-mode C2 bounds shares modes
  2 and 3, so its cancellation factors through mode 1.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
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

variable {k : Type*} [CommSemiring k] {a b c a' : ℕ}

/-- Mode-1 contraction distributes over sums of tensors. -/
theorem contract₁_add (M : Matrix (Fin a') (Fin a) k) (S T : Tensor k a b c) :
    contract₁ M (S + T) = contract₁ M S + contract₁ M T := by
  funext i' j l
  simp only [contract₁, Pi.add_apply, mul_add]
  exact Finset.sum_add_distrib

/-- Mode-1 contraction of a triad contracts the mode-1 vector. -/
theorem contract₁_triad (M : Matrix (Fin a') (Fin a) k)
    (u : Fin a → k) (v : Fin b → k) (w : Fin c → k) :
    contract₁ M (triad u v w) = triad (fun i' => ∑ i, M i' i * u i) v w := by
  funext i' j l
  simp only [contract₁, triad]
  rw [Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A triad whose mode-1 vector vanishes is the zero tensor. -/
theorem triad_zero₁ (v : Fin b → k) (w : Fin c → k) :
    triad (fun _ : Fin a => (0 : k)) v w = 0 := by
  funext i j l
  simp [triad]

variable [DecidableEq k]

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
  rw [contract₂_eq_cyc, nnz_cyc, nnz_cyc]
  exact (nnz_contract₁_le M (cyc T)).trans_eq (nnz_cyc T)

/-- **C1, mode 3.** -/
theorem nnz_contract₃_le (M : Matrix (Fin 1) (Fin c) k) (T : Tensor k a b c) :
    nnz (contract₃ M T) ≤ nnz T := by
  rw [contract₃_eq_cyc, nnz_cyc]
  exact (nnz_contract₁_le M (cyc (cyc T))).trans_eq
    ((nnz_cyc (cyc T)).trans (nnz_cyc T))

/-- The constant-one vector on `Fin 1` has Hamming weight `1`. -/
theorem wt_one_fin_one [Nontrivial k] : wt (fun _ : Fin 1 => (1 : k)) = 1 := by
  simp [wt]

end C1

/-! ## 3. Separating vectors from linear independence -/

section Sums

variable {k : Type*} [CommSemiring k] {a : ℕ}

/-- Summing a two-point-supported coefficient vector against `x`
evaluates at the two points. -/
theorem sum_two_point_mul (i₀ i₁ : Fin a) (A B : k) (x : Fin a → k) :
    (∑ i, ((if i = i₀ then A else 0) + (if i = i₁ then B else 0)) * x i)
      = A * x i₀ + B * x i₁ := by
  simp only [add_mul, ite_mul, zero_mul, Finset.sum_add_distrib,
    Fintype.sum_ite_eq']

end Sums

section Separation

variable {k : Type*} [Field k] {a : ℕ}

/-- A linearly independent pair of vectors over a field has a nonzero
`2 × 2` minor: `u i₀ * u' i₁ ≠ u i₁ * u' i₀` for some `i₀, i₁`. -/
theorem exists_mul_ne_mul_of_linearIndependent {u u' : Fin a → k}
    (h : LinearIndependent k ![u, u']) :
    ∃ i₀ i₁, u i₀ * u' i₁ ≠ u i₁ * u' i₀ := by
  by_contra hall
  push Not at hall
  rw [LinearIndependent.pair_iff] at h
  have hu : u ≠ 0 := by
    rintro rfl
    exact one_ne_zero (h 1 0 (by simp)).1
  obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
    by_contra h0
    push Not at h0
    exact hu (funext fun i => h0 i)
  have hrel : (u' j / u j) • u + (-1 : k) • u' = 0 := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    field_simp
    linear_combination -hall j i
  exact one_ne_zero (neg_eq_zero.mp (h (u' j / u j) (-1) hrel).2)

/-- **Separating vectors.** A linearly independent pair `u, u'` over a
field admits dual vectors `g, g'` with `⟨g,u⟩ = 1, ⟨g,u'⟩ = 0` and
`⟨g',u⟩ = 0, ⟨g',u'⟩ = 1` (Cramer on a nonzero `2 × 2` minor; works
over any field, including `ZMod 2`). -/
theorem exists_separating_vectors {u u' : Fin a → k}
    (h : LinearIndependent k ![u, u']) :
    ∃ g g' : Fin a → k,
      ((∑ i, g i * u i) = 1 ∧ (∑ i, g i * u' i) = 0) ∧
      ((∑ i, g' i * u i) = 0 ∧ (∑ i, g' i * u' i) = 1) := by
  obtain ⟨i₀, i₁, hD⟩ := exists_mul_ne_mul_of_linearIndependent h
  have hD0 : u i₀ * u' i₁ - u i₁ * u' i₀ ≠ 0 := sub_ne_zero.mpr hD
  set D := u i₀ * u' i₁ - u i₁ * u' i₀ with hDdef
  refine ⟨fun i => (if i = i₀ then u' i₁ / D else 0)
            + (if i = i₁ then -(u' i₀) / D else 0),
          fun i => (if i = i₀ then -(u i₁) / D else 0)
            + (if i = i₁ then u i₀ / D else 0),
          ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simp only [sum_two_point_mul]
    field_simp
    rw [hDdef]
    ring
  · simp only [sum_two_point_mul]
    field_simp
    ring
  · simp only [sum_two_point_mul]
    field_simp
    ring
  · simp only [sum_two_point_mul]
    field_simp
    rw [hDdef]
    ring

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
  obtain ⟨g, g', ⟨hg1, hg0⟩, hg'0, hg'1⟩ := exists_separating_vectors h
  apply max_le
  · have key : contract₁ (Matrix.of fun _ => g) (triad u v w + triad u' v' w')
        = triad (fun _ : Fin 1 => (1 : k)) v w := by
      rw [contract₁_add, contract₁_triad, contract₁_triad]
      simp only [Matrix.of_apply, hg1, hg0]
      rw [triad_zero₁, add_zero]
    have hle := nnz_contract₁_le (Matrix.of fun _ => g)
      (triad u v w + triad u' v' w')
    rwa [key, nnz_triad, wt_one_fin_one, one_mul] at hle
  · have key : contract₁ (Matrix.of fun _ => g') (triad u v w + triad u' v' w')
        = triad (fun _ : Fin 1 => (1 : k)) v' w' := by
      rw [contract₁_add, contract₁_triad, contract₁_triad]
      simp only [Matrix.of_apply, hg'0, hg'1]
      rw [triad_zero₁, zero_add]
    have hle := nnz_contract₁_le (Matrix.of fun _ => g')
      (triad u v w + triad u' v' w')
    rwa [key, nnz_triad, wt_one_fin_one, one_mul] at hle

/-- **C2, mode 2.** -/
theorem max_le_nnz_triad_add_triad₂ {v v' : Fin b → k}
    (h : LinearIndependent k ![v, v'])
    (u : Fin a → k) (w : Fin c → k) (u' : Fin a → k) (w' : Fin c → k) :
    max (wt u * wt w) (wt u' * wt w')
      ≤ nnz (triad u v w + triad u' v' w') := by
  have key := max_le_nnz_triad_add_triad₁ h w u w' u'
  rw [show triad v w u + triad v' w' u' = cyc (triad u v w + triad u' v' w') by
      rw [cyc_add, cyc_triad, cyc_triad], nnz_cyc] at key
  simpa [mul_comm] using key

/-- **C2, mode 3.** -/
theorem max_le_nnz_triad_add_triad₃ {w w' : Fin c → k}
    (h : LinearIndependent k ![w, w'])
    (u : Fin a → k) (v : Fin b → k) (u' : Fin a → k) (v' : Fin b → k) :
    max (wt u * wt v) (wt u' * wt v')
      ≤ nnz (triad u v w + triad u' v' w') := by
  have key := max_le_nnz_triad_add_triad₁ h u v u' v'
  rw [show triad w u v = cyc (cyc (triad u v w)) by rw [cyc_triad, cyc_triad],
    show triad w' u' v' = cyc (cyc (triad u' v' w')) by rw [cyc_triad, cyc_triad],
    ← cyc_add, ← cyc_add, nnz_cyc, nnz_cyc] at key
  exact key

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
  have hne : i₀ ≠ i₁ := by
    rintro rfl
    exact hu₀ hu₁
  set A := ({i₀} : Finset (Fin a)) ×ˢ
      ((Finset.univ.filter fun j : Fin b => v j ≠ 0) ×ˢ
       (Finset.univ.filter fun l : Fin c => w l ≠ 0)) with hA
  set B := ({i₁} : Finset (Fin a)) ×ˢ
      ((Finset.univ.filter fun j : Fin b => v' j ≠ 0) ×ˢ
       (Finset.univ.filter fun l : Fin c => w' l ≠ 0)) with hB
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j, l⟩ hmem hmem'
    simp only [hA, hB, Finset.mem_product, Finset.mem_singleton] at hmem hmem'
    exact hne (hmem.1.symm.trans hmem'.1)
  have hsub : A ∪ B ⊆ Finset.univ.filter
      (fun p : Fin a × Fin b × Fin c =>
        (triad u v w + triad u' v' w') p.1 p.2.1 p.2.2 ≠ 0) := by
    rintro ⟨i, j, l⟩ hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_union.mp hp with hmem | hmem
    · simp only [hA, Finset.mem_product, Finset.mem_singleton, Finset.mem_filter,
        Finset.mem_univ, true_and] at hmem
      obtain ⟨rfl, hv, hw⟩ := hmem
      simp only [Pi.add_apply, triad]
      rw [hu'₀, zero_mul, zero_mul, add_zero]
      exact mul_ne_zero (mul_ne_zero hu₀ hv) hw
    · simp only [hB, Finset.mem_product, Finset.mem_singleton, Finset.mem_filter,
        Finset.mem_univ, true_and] at hmem
      obtain ⟨rfl, hv', hw'⟩ := hmem
      simp only [Pi.add_apply, triad]
      rw [hu₁, zero_mul, zero_mul, zero_add]
      exact mul_ne_zero (mul_ne_zero hu'₁ hv') hw'
  calc wt v * wt w + wt v' * wt w' = A.card + B.card := by
        simp [hA, hB, wt, Finset.card_product]
    _ = (A ∪ B).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ _ := Finset.card_le_card hsub

end Additive

/-! ## 6. Pair collapse — sums sharing two modes (stratum S1) -/

section Collapse

variable {k : Type*} [CommSemiring k] {a b c : ℕ}

/-- Two triads sharing modes 2 and 3 sum to a single triad: the
cancellation factors through mode 1 and the sum again has rank ≤ 1. -/
theorem triad_add_triad₁ (u u' : Fin a → k) (v : Fin b → k) (w : Fin c → k) :
    triad u v w + triad u' v w = triad (u + u') v w := by
  funext i j l
  simp only [Pi.add_apply, triad]
  ring

/-- Two triads sharing modes 1 and 3 sum to a single triad. -/
theorem triad_add_triad₂ (u : Fin a → k) (v v' : Fin b → k) (w : Fin c → k) :
    triad u v w + triad u v' w = triad u (v + v') w := by
  funext i j l
  simp only [Pi.add_apply, triad]
  ring

/-- Two triads sharing modes 1 and 2 sum to a single triad. -/
theorem triad_add_triad₃ (u : Fin a → k) (v : Fin b → k) (w w' : Fin c → k) :
    triad u v w + triad u v w' = triad u v (w + w') := by
  funext i j l
  simp only [Pi.add_apply, triad]
  ring

variable [DecidableEq k] [NoZeroDivisors k]

/-- **S1 equality classification, mode 1.** Two triads sharing modes 2
and 3 have EXACT pair-sum count `wt (u + u') * wt v * wt w`: the
members are as dense as `u, u'` are, while the sum is sparse exactly
when `u + u'` is sparse.  This is the complete description of the
classic two-term conspiracy. -/
theorem nnz_triad_add_triad₁ (u u' : Fin a → k) (v : Fin b → k) (w : Fin c → k) :
    nnz (triad u v w + triad u' v w) = wt (u + u') * wt v * wt w := by
  rw [triad_add_triad₁, nnz_triad]

/-- **S1 equality classification, mode 2.** -/
theorem nnz_triad_add_triad₂ (u : Fin a → k) (v v' : Fin b → k) (w : Fin c → k) :
    nnz (triad u v w + triad u v' w) = wt u * wt (v + v') * wt w := by
  rw [triad_add_triad₂, nnz_triad]

/-- **S1 equality classification, mode 3.** -/
theorem nnz_triad_add_triad₃ (u : Fin a → k) (v : Fin b → k) (w w' : Fin c → k) :
    nnz (triad u v w + triad u v w') = wt u * wt v * wt (w + w') := by
  rw [triad_add_triad₃, nnz_triad]

end Collapse

/-! ## 7. F₂ stratification — annihilation and the equality dichotomy

Over `F₂ = ZMod 2` the only nonzero scalar is `1`, so two NONZERO
vectors are linearly independent iff they are unequal.  For a pair of
triads with all six factors nonzero this stratifies the conspiracy
question by the set of unequal factor pairs:

* **S0** (all three equal): `τ' = τ` and the sum annihilates in
  characteristic 2 (`tensor_add_self`, `nnz_tensor_add_self`).
* **S1** (exactly one unequal): the sum collapses to a single triad
  with exact count — section 6.
* **S2** (exactly two unequal): C2 applies in both unequal modes
  (`pair_bounds_shared₁/₂/₃`); the conjunction is sharp
  (Scratch/Cn2Sharpness).
* **S3** (all three unequal): C2 applies in all three modes
  (`pair_bounds_of_ne`); the conjunction is sharp
  (Scratch/Cn2Sharpness); no additive strengthening survives
  (support nesting, as in section 5).

Capstone `pair_collapse₁_of_nnz_lt`: a pair-sum strictly below both
cross-mode C2 bounds must share modes 2 and 3, so its cancellation
factors through mode 1 and the sum is again rank ≤ 1 — the
rank-1-specific locality that black-box vector families lack (Bw1). -/

section CharTwoAnnihilation

variable {k : Type*} [CommSemiring k] [CharP k 2] {a b c : ℕ}

/-- **S0 (char-2 annihilation).** In characteristic 2 a tensor plus
itself vanishes; in particular an identical pair of triads sums to
`0`.  Degenerate stratum of the pair classification. -/
theorem tensor_add_self (T : Tensor k a b c) : T + T = 0 := by
  funext i j l
  simp only [Pi.add_apply, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero _

/-- **S0 count.** -/
theorem nnz_tensor_add_self [DecidableEq k] (T : Tensor k a b c) :
    nnz (T + T) = 0 := by
  rw [tensor_add_self, nnz_zero]

end CharTwoAnnihilation

section F2

variable {a b c : ℕ}

/-- Over `F₂`, `x + y = 0` iff `x = y` (vector form of char-2
cancellation). -/
theorem add_eq_zero_iff_eq {n : ℕ} {x y : Fin n → ZMod 2} :
    x + y = 0 ↔ x = y := by
  constructor
  · intro h
    funext i
    have hi : x i + y i = 0 := congrFun h i
    exact CharTwo.add_eq_zero.mp hi
  · rintro rfl
    funext i
    exact CharTwo.add_self_eq_zero (x i)

/-- **The F₂ dichotomy.** Two NONZERO vectors over `F₂ = ZMod 2` are
linearly independent iff they are unequal: the only nonzero scalar is
`1`, so the only relations available are `x = 0`, `y = 0`, `x = y`.
This is what makes the pair-conspiracy strata clean over `F₂`. -/
theorem linearIndependent_pair_iff_ne {u u' : Fin a → ZMod 2}
    (hu : u ≠ 0) (hu' : u' ≠ 0) :
    LinearIndependent (ZMod 2) ![u, u'] ↔ u ≠ u' := by
  rw [LinearIndependent.pair_iff]
  constructor
  · rintro h rfl
    refine one_ne_zero (h 1 1 ?_).1
    rw [one_smul]
    exact add_eq_zero_iff_eq.mpr rfl
  · intro hne s t hst
    have hd : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    rcases hd s with rfl | rfl <;> rcases hd t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · exact absurd (by simpa using hst) hu'
    · exact absurd (by simpa using hst) hu
    · rw [one_smul, one_smul] at hst
      exact absurd (add_eq_zero_iff_eq.mp hst) hne

/-- **S0/S1 boundary.** Within the shared-modes-2,3 family over `F₂`
(nonzero shared factors), the pair-sum vanishes exactly on the
diagonal `u = u'`: S0 is precisely the annihilation locus inside the
closure of S1. -/
theorem nnz_triad_add_triad₁_eq_zero_iff {u u' : Fin a → ZMod 2}
    {v : Fin b → ZMod 2} {w : Fin c → ZMod 2} (hv : v ≠ 0) (hw : w ≠ 0) :
    nnz (triad u v w + triad u' v w) = 0 ↔ u = u' := by
  rw [nnz_triad_add_triad₁, Nat.mul_eq_zero, Nat.mul_eq_zero]
  simp only [wt_eq_zero_iff, hv, hw, or_false]
  exact add_eq_zero_iff_eq

/-- **C2 over F₂, mode 1, by inequality.** For nonzero unequal mode-1
factors the independence pair bound applies verbatim. -/
theorem max_le_nnz_triad_add_triad₁_of_ne {u u' : Fin a → ZMod 2}
    (hu : u ≠ 0) (hu' : u' ≠ 0) (hne : u ≠ u')
    (v : Fin b → ZMod 2) (w : Fin c → ZMod 2)
    (v' : Fin b → ZMod 2) (w' : Fin c → ZMod 2) :
    max (wt v * wt w) (wt v' * wt w')
      ≤ nnz (triad u v w + triad u' v' w') :=
  max_le_nnz_triad_add_triad₁ ((linearIndependent_pair_iff_ne hu hu').mpr hne)
    v w v' w'

/-- **C2 over F₂, mode 2, by inequality.** -/
theorem max_le_nnz_triad_add_triad₂_of_ne {v v' : Fin b → ZMod 2}
    (hv : v ≠ 0) (hv' : v' ≠ 0) (hne : v ≠ v')
    (u : Fin a → ZMod 2) (w : Fin c → ZMod 2)
    (u' : Fin a → ZMod 2) (w' : Fin c → ZMod 2) :
    max (wt u * wt w) (wt u' * wt w')
      ≤ nnz (triad u v w + triad u' v' w') :=
  max_le_nnz_triad_add_triad₂ ((linearIndependent_pair_iff_ne hv hv').mpr hne)
    u w u' w'

/-- **C2 over F₂, mode 3, by inequality.** -/
theorem max_le_nnz_triad_add_triad₃_of_ne {w w' : Fin c → ZMod 2}
    (hw : w ≠ 0) (hw' : w' ≠ 0) (hne : w ≠ w')
    (u : Fin a → ZMod 2) (v : Fin b → ZMod 2)
    (u' : Fin a → ZMod 2) (v' : Fin b → ZMod 2) :
    max (wt u * wt v) (wt u' * wt v')
      ≤ nnz (triad u v w + triad u' v' w') :=
  max_le_nnz_triad_add_triad₃ ((linearIndependent_pair_iff_ne hw hw').mpr hne)
    u v u' v'

/-- **S2, mode 1 shared.** Modes 2 and 3 are nonzero and unequal, mode
1 is shared: both cross-mode C2 bounds hold.  Sharp
(Scratch/Cn2Sharpness, up to mode relabelling). -/
theorem pair_bounds_shared₁ {v v' : Fin b → ZMod 2} {w w' : Fin c → ZMod 2}
    (hv : v ≠ 0) (hv' : v' ≠ 0) (hnev : v ≠ v')
    (hw : w ≠ 0) (hw' : w' ≠ 0) (hnew : w ≠ w')
    (u : Fin a → ZMod 2) :
    max (wt u * wt w) (wt u * wt w') ≤ nnz (triad u v w + triad u v' w') ∧
    max (wt u * wt v) (wt u * wt v') ≤ nnz (triad u v w + triad u v' w') :=
  ⟨max_le_nnz_triad_add_triad₂_of_ne hv hv' hnev u w u w',
   max_le_nnz_triad_add_triad₃_of_ne hw hw' hnew u v u v'⟩

/-- **S2, mode 2 shared.** -/
theorem pair_bounds_shared₂ {u u' : Fin a → ZMod 2} {w w' : Fin c → ZMod 2}
    (hu : u ≠ 0) (hu' : u' ≠ 0) (hneu : u ≠ u')
    (hw : w ≠ 0) (hw' : w' ≠ 0) (hnew : w ≠ w')
    (v : Fin b → ZMod 2) :
    max (wt v * wt w) (wt v * wt w') ≤ nnz (triad u v w + triad u' v w') ∧
    max (wt u * wt v) (wt u' * wt v) ≤ nnz (triad u v w + triad u' v w') :=
  ⟨max_le_nnz_triad_add_triad₁_of_ne hu hu' hneu v w v w',
   max_le_nnz_triad_add_triad₃_of_ne hw hw' hnew u v u' v⟩

/-- **S2, mode 3 shared.** -/
theorem pair_bounds_shared₃ {u u' : Fin a → ZMod 2} {v v' : Fin b → ZMod 2}
    (hu : u ≠ 0) (hu' : u' ≠ 0) (hneu : u ≠ u')
    (hv : v ≠ 0) (hv' : v' ≠ 0) (hnev : v ≠ v')
    (w : Fin c → ZMod 2) :
    max (wt v * wt w) (wt v' * wt w) ≤ nnz (triad u v w + triad u' v' w) ∧
    max (wt u * wt w) (wt u' * wt w) ≤ nnz (triad u v w + triad u' v' w) :=
  ⟨max_le_nnz_triad_add_triad₁_of_ne hu hu' hneu v w v' w,
   max_le_nnz_triad_add_triad₂_of_ne hv hv' hnev u w u' w⟩

/-- **S3.** All three factor pairs nonzero and unequal: C2 applies in
all three modes.  The three-way conjunction is sharp
(Scratch/Cn2Sharpness); the additive strengthening fails (support
nesting — same witness). -/
theorem pair_bounds_of_ne {u u' : Fin a → ZMod 2} {v v' : Fin b → ZMod 2}
    {w w' : Fin c → ZMod 2}
    (hu : u ≠ 0) (hu' : u' ≠ 0) (hneu : u ≠ u')
    (hv : v ≠ 0) (hv' : v' ≠ 0) (hnev : v ≠ v')
    (hw : w ≠ 0) (hw' : w' ≠ 0) (hnew : w ≠ w') :
    max (wt v * wt w) (wt v' * wt w') ≤ nnz (triad u v w + triad u' v' w') ∧
    max (wt u * wt w) (wt u' * wt w') ≤ nnz (triad u v w + triad u' v' w') ∧
    max (wt u * wt v) (wt u' * wt v') ≤ nnz (triad u v w + triad u' v' w') :=
  ⟨max_le_nnz_triad_add_triad₁_of_ne hu hu' hneu v w v' w',
   max_le_nnz_triad_add_triad₂_of_ne hv hv' hnev u w u' w',
   max_le_nnz_triad_add_triad₃_of_ne hw hw' hnew u v u' v'⟩

/-- **Collapse dichotomy (capstone).** Over `F₂`, a pair-sum of triads
with nonzero mode-2 and mode-3 factors that is strictly sparser than
BOTH cross-mode C2 bounds must share modes 2 and 3 — and then the
cancellation factors through mode 1: the sum collapses to the single
triad `(u + u') ⊗ v ⊗ w` (rank ≤ 1, and `= 0` exactly when `u' = u`).
This is the pair-level rank-1 factorization property that black-box
dense vector families lack (Bw1): conspiracies below the C2 threshold
exist only through shared-factor structure. -/
theorem pair_collapse₁_of_nnz_lt {u u' : Fin a → ZMod 2}
    {v v' : Fin b → ZMod 2} {w w' : Fin c → ZMod 2}
    (hv : v ≠ 0) (hv' : v' ≠ 0) (hw : w ≠ 0) (hw' : w' ≠ 0)
    (h₂ : nnz (triad u v w + triad u' v' w') < max (wt u * wt w) (wt u' * wt w'))
    (h₃ : nnz (triad u v w + triad u' v' w') < max (wt u * wt v) (wt u' * wt v')) :
    v' = v ∧ w' = w ∧ triad u v w + triad u' v' w' = triad (u + u') v w := by
  have hveq : v' = v := by
    by_contra hne
    exact absurd (max_le_nnz_triad_add_triad₂_of_ne hv hv' (Ne.symm hne) u w u' w')
      (not_le.mpr h₂)
  have hweq : w' = w := by
    by_contra hne
    exact absurd (max_le_nnz_triad_add_triad₃_of_ne hw hw' (Ne.symm hne) u v u' v')
      (not_le.mpr h₃)
  subst hveq
  subst hweq
  exact ⟨rfl, rfl, triad_add_triad₁ u u' v' w'⟩

end F2

/-! ## 8. Cn3 — triple classification, isolation, and reducibility over F₂

For three NONZERO vectors over `F₂ = ZMod 2` the exhaustive strata are
(a) all equal; (b) exactly two equal; (c) pairwise distinct and
dependent, forcedly `z = x + y`; (d) linearly independent.  Term `x`
of a triple is *isolatable* from `{y, z}` when a functional `g` has
`⟨g,x⟩ = 1, ⟨g,y⟩ = ⟨g,z⟩ = 0`; this happens iff `x ∉ span {y, z}`,
concretely iff `x ∉ {0, y, z, y + z}`.  Isolation profile by stratum:
(a) none, (b) exactly the odd term, (c) NONE (the irreducible ladder),
(d) all three.  An isolatable mode-1 factor makes C1 contraction
collapse the 3-sum onto that term, transferring its complementary
weight product below `nnz` — the REDUCIBLE half. -/

section TripleF2

variable {a b c : ℕ}

/-- Char-2 shim: `x + y + z = 0` iff the FIRST vector is the sum of the
other two. -/
theorem add_add_eq_zero_iff_left {n : ℕ} {x y z : Fin n → ZMod 2} :
    x + y + z = 0 ↔ x = y + z := by
  rw [add_assoc, add_eq_zero_iff_eq]

/-- Char-2 shim: `x + y + z = 0` iff the MIDDLE vector is the sum of the
other two. -/
theorem add_add_eq_zero_iff_mid {n : ℕ} {x y z : Fin n → ZMod 2} :
    x + y + z = 0 ↔ y = x + z := by
  rw [add_comm x y, add_assoc, add_eq_zero_iff_eq]

/-- Char-2 shim: `x + y + z = 0` iff the LAST vector is the sum of the
other two. -/
theorem add_add_eq_zero_iff_right {n : ℕ} {x y z : Fin n → ZMod 2} :
    x + y + z = 0 ↔ z = x + y := by
  rw [add_eq_zero_iff_eq, eq_comm]

/-- **Isolation.** Term `x` is isolatable from `{y, z}` (in one mode):
some functional `g` pairs to `1` against `x` and to `0` against `y`
and `z`.  Contraction by such a `g` kills the other two terms of a
triple of triads. -/
def Isolable (x y z : Fin a → ZMod 2) : Prop :=
  ∃ g : Fin a → ZMod 2,
    (∑ i, g i * x i) = 1 ∧ (∑ i, g i * y i) = 0 ∧ (∑ i, g i * z i) = 0

/-- Over `F₂` the span of a pair is the four-element set
`{0, y, z, y + z}`. -/
theorem mem_span_pair_f2 {x y z : Fin a → ZMod 2} :
    x ∈ Submodule.span (ZMod 2) {y, z} ↔
      x = 0 ∨ x = y ∨ x = z ∨ x = y + z := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨s, t, rfl⟩
    have hd : ∀ u : ZMod 2, u = 0 ∨ u = 1 := by decide
    rcases hd s with rfl | rfl <;> rcases hd t with rfl | rfl
    · exact Or.inl (by rw [zero_smul, zero_smul, add_zero])
    · exact Or.inr (Or.inr (Or.inl (by rw [zero_smul, one_smul, zero_add])))
    · exact Or.inr (Or.inl (by rw [one_smul, zero_smul, add_zero]))
    · exact Or.inr (Or.inr (Or.inr (by rw [one_smul, one_smul])))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, 0, by rw [zero_smul, zero_smul, add_zero]⟩
    · exact ⟨1, 0, by rw [one_smul, zero_smul, add_zero]⟩
    · exact ⟨0, 1, by rw [zero_smul, one_smul, zero_add]⟩
    · exact ⟨1, 1, by rw [one_smul, one_smul]⟩

/-- **Isolation criterion, span form.** Term `x` is isolatable from
`{y, z}` iff `x` is not in their span.  (⇐ is dual separation on the
quotient; ⇒ is linearity of the pairing.) -/
theorem isolable_iff_notMem_span {x y z : Fin a → ZMod 2} :
    Isolable x y z ↔ x ∉ Submodule.span (ZMod 2) {y, z} := by
  constructor
  · rintro ⟨g, hgx, hgy, hgz⟩ hmem
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hmem
    have e : (∑ i, g i * (s • y + t • z) i)
        = s * (∑ i, g i * y i) + t * (∑ i, g i * z i) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, hgy, hgz, mul_zero, mul_zero, add_zero] at hgx
    exact one_ne_zero hgx.symm
  · intro hx
    obtain ⟨f, hfx, hfmap⟩ :=
      Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
    have hker : ∀ u ∈ Submodule.span (ZMod 2) {y, z}, f u = 0 := by
      intro u hu
      have hmem : f u ∈ (Submodule.span (ZMod 2) {y, z}).map f :=
        Submodule.mem_map_of_mem hu
      rwa [hfmap, Submodule.mem_bot] at hmem
    have hfx1 : f x = 1 := by
      rcases (by decide : ∀ s : ZMod 2, s = 0 ∨ s = 1) (f x) with h | h
      · exact absurd h hfx
      · exact h
    have key : ∀ u : Fin a → ZMod 2,
        (∑ i, f (fun j => if i = j then 1 else 0) * u i) = f u := by
      intro u
      rw [LinearMap.pi_apply_eq_sum_univ f u]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]
    refine ⟨fun i => f (fun j => if i = j then 1 else 0), ?_, ?_, ?_⟩
    · exact (key x).trans hfx1
    · exact (key y).trans (hker y (Submodule.subset_span (Set.mem_insert _ _)))
    · exact (key z).trans (hker z (Submodule.subset_span
        (Set.mem_insert_of_mem _ rfl)))

/-- **Isolation criterion, concrete form.** Over `F₂`: term `x` is
isolatable from `{y, z}` iff `x ∉ {0, y, z, y + z}`. -/
theorem isolable_iff {x y z : Fin a → ZMod 2} :
    Isolable x y z ↔ x ≠ 0 ∧ x ≠ y ∧ x ≠ z ∧ x ≠ y + z := by
  rw [isolable_iff_notMem_span, mem_span_pair_f2]
  simp only [not_or]

/-- **The F₂ triple dichotomy.** Three NONZERO vectors over `F₂` are
linearly independent iff they are pairwise distinct and do not sum to
zero — the only nonzero scalars being `1`, the seven candidate
relations are `x = 0`, `y = 0`, `z = 0`, `x = y`, `x = z`, `y = z`,
`x + y + z = 0`. -/
theorem linearIndependent_triple_iff {x y z : Fin a → ZMod 2}
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    LinearIndependent (ZMod 2) ![x, y, z] ↔
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ x + y + z ≠ 0 := by
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro heq
      have h0 := h ![1, 1, 0] (by
        rw [Fin.sum_univ_three]
        show (1 : ZMod 2) • x + (1 : ZMod 2) • y + (0 : ZMod 2) • z = 0
        rw [one_smul, one_smul, zero_smul, add_zero]
        exact add_eq_zero_iff_eq.mpr heq) 0
      exact one_ne_zero h0
    · intro heq
      have h0 := h ![1, 0, 1] (by
        rw [Fin.sum_univ_three]
        show (1 : ZMod 2) • x + (0 : ZMod 2) • y + (1 : ZMod 2) • z = 0
        rw [one_smul, zero_smul, one_smul, add_zero]
        exact add_eq_zero_iff_eq.mpr heq) 0
      exact one_ne_zero h0
    · intro heq
      have h0 := h ![0, 1, 1] (by
        rw [Fin.sum_univ_three]
        show (0 : ZMod 2) • x + (1 : ZMod 2) • y + (1 : ZMod 2) • z = 0
        rw [zero_smul, one_smul, one_smul, zero_add]
        exact add_eq_zero_iff_eq.mpr heq) 1
      exact one_ne_zero h0
    · intro heq
      have h0 := h ![1, 1, 1] (by
        rw [Fin.sum_univ_three]
        show (1 : ZMod 2) • x + (1 : ZMod 2) • y + (1 : ZMod 2) • z = 0
        rw [one_smul, one_smul, one_smul]
        exact heq) 0
      exact one_ne_zero h0
  · rintro ⟨hxy, hxz, hyz, hs⟩ g hg
    have hg' : g 0 • x + g 1 • y + g 2 • z = 0 := by
      rw [Fin.sum_univ_three] at hg
      exact hg
    have hd : ∀ u : ZMod 2, u = 0 ∨ u = 1 := by decide
    rcases hd (g 0) with h0 | h0 <;> rcases hd (g 1) with h1 | h1 <;>
      rcases hd (g 2) with h2 | h2 <;> rw [h0, h1, h2] at hg'
    · intro i
      fin_cases i
      exacts [h0, h1, h2]
    · rw [zero_smul, zero_smul, one_smul, zero_add, zero_add] at hg'
      exact absurd hg' hz
    · rw [zero_smul, one_smul, zero_smul, zero_add, add_zero] at hg'
      exact absurd hg' hy
    · rw [zero_smul, one_smul, one_smul, zero_add] at hg'
      exact absurd (add_eq_zero_iff_eq.mp hg') hyz
    · rw [one_smul, zero_smul, zero_smul, add_zero, add_zero] at hg'
      exact absurd hg' hx
    · rw [one_smul, zero_smul, one_smul, add_zero] at hg'
      exact absurd (add_eq_zero_iff_eq.mp hg') hxz
    · rw [one_smul, one_smul, zero_smul, add_zero] at hg'
      exact absurd (add_eq_zero_iff_eq.mp hg') hxy
    · rw [one_smul, one_smul, one_smul] at hg'
      exact absurd hg' hs

/-- **Classification (a)/(b)/(c)/(d).** Three nonzero vectors over `F₂`
are: (a) all equal; (b) exactly two equal; (c) pairwise distinct with
`z = x + y` (dependent, all pairwise independent); or (d) linearly
independent.  Exhaustive. -/
theorem triple_stratification (x y z : Fin a → ZMod 2)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    (x = y ∧ y = z)
    ∨ ((x = y ∧ x ≠ z) ∨ (x = z ∧ x ≠ y) ∨ (y = z ∧ x ≠ y))
    ∨ (x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ z = x + y)
    ∨ LinearIndependent (ZMod 2) ![x, y, z] := by
  by_cases hxy : x = y
  · by_cases hyz : y = z
    · exact Or.inl ⟨hxy, hyz⟩
    · exact Or.inr (Or.inl (Or.inl ⟨hxy, fun hxz => hyz (hxy ▸ hxz)⟩))
  · by_cases hyz : y = z
    · exact Or.inr (Or.inl (Or.inr (Or.inr ⟨hyz, hxy⟩)))
    · by_cases hxz : x = z
      · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨hxz, hxy⟩)))
      · by_cases hsum : z = x + y
        · exact Or.inr (Or.inr (Or.inl ⟨hxy, hxz, hyz, hsum⟩))
        · refine Or.inr (Or.inr (Or.inr ?_))
          rw [linearIndependent_triple_iff hx hy hz]
          exact ⟨hxy, hxz, hyz,
            fun h => hsum (add_add_eq_zero_iff_right.mp h)⟩

/-- **(a): no isolation.** If all three vectors are equal, no term is
isolatable. -/
theorem not_isolable_of_all_eq {x y z : Fin a → ZMod 2}
    (hxy : x = y) (hyz : y = z) :
    ¬ Isolable x y z ∧ ¬ Isolable y x z ∧ ¬ Isolable z x y := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact (isolable_iff.mp h).2.1 hxy
  · exact (isolable_iff.mp h).2.1 hxy.symm
  · exact (isolable_iff.mp h).2.1 (hxy.trans hyz).symm

/-- **(b): exactly the odd term is isolatable.** If `x = y ≠ z` with
`z ≠ 0`, then `z` is isolatable from `{x, y}` while neither `x` nor
`y` is isolatable. -/
theorem isolable_odd_of_two_eq {x y z : Fin a → ZMod 2}
    (hxy : x = y) (hz : z ≠ 0) (hne : z ≠ x) :
    Isolable z x y ∧ ¬ Isolable x y z ∧ ¬ Isolable y x z := by
  refine ⟨isolable_iff.mpr
      ⟨hz, hne, fun h => hne (h.trans hxy.symm), fun h => ?_⟩,
    fun h => (isolable_iff.mp h).2.1 hxy,
    fun h => (isolable_iff.mp h).2.1 hxy.symm⟩
  rw [← hxy, add_eq_zero_iff_eq.mpr rfl] at h
  exact hz h

/-- **(c): NO term is isolatable — the irreducible triple.** If
`x + y + z = 0` then any functional takes value `0` on one of the
three whenever it kills the other two (`f(x) = 1, f(y) = 0` forces
`f(z) = 1`).  No nonzero/distinctness hypotheses are needed. -/
theorem not_isolable_of_sum_eq_zero {x y z : Fin a → ZMod 2}
    (h : x + y + z = 0) :
    ¬ Isolable x y z ∧ ¬ Isolable y x z ∧ ¬ Isolable z x y := by
  refine ⟨fun hI => ?_, fun hI => ?_, fun hI => ?_⟩
  · exact (isolable_iff.mp hI).2.2.2 (add_add_eq_zero_iff_left.mp h)
  · exact (isolable_iff.mp hI).2.2.2 (add_add_eq_zero_iff_mid.mp h)
  · exact (isolable_iff.mp hI).2.2.2 (add_add_eq_zero_iff_right.mp h)

/-- **(d): every term is isolatable.** -/
theorem isolable_all_of_linearIndependent {x y z : Fin a → ZMod 2}
    (h : LinearIndependent (ZMod 2) ![x, y, z]) :
    Isolable x y z ∧ Isolable y x z ∧ Isolable z x y := by
  have hx : x ≠ 0 := h.ne_zero 0
  have hy : y ≠ 0 := h.ne_zero 1
  have hz : z ≠ 0 := h.ne_zero 2
  obtain ⟨hxy, hxz, hyz, hs⟩ := (linearIndependent_triple_iff hx hy hz).mp h
  exact ⟨isolable_iff.mpr ⟨hx, hxy, hxz,
      fun he => hs (add_add_eq_zero_iff_left.mpr he)⟩,
    isolable_iff.mpr ⟨hy, fun he => hxy he.symm, hyz,
      fun he => hs (add_add_eq_zero_iff_mid.mpr he)⟩,
    isolable_iff.mpr ⟨hz, fun he => hxz he.symm, fun he => hyz he.symm,
      fun he => hs (add_add_eq_zero_iff_right.mpr he)⟩⟩

/-- **Reducibility, mode 1.** If the mode-1 factor `u₁` is isolatable
from `{u₂, u₃}`, C1 contraction by the isolating functional collapses
the 3-sum onto term 1 at full complementary weight: the triple cannot
conspire below `wt v₁ * wt w₁`. -/
theorem le_nnz_triple_of_isolable₁ {u₁ u₂ u₃ : Fin a → ZMod 2}
    (h : Isolable u₁ u₂ u₃)
    (v₁ : Fin b → ZMod 2) (w₁ : Fin c → ZMod 2)
    (v₂ : Fin b → ZMod 2) (w₂ : Fin c → ZMod 2)
    (v₃ : Fin b → ZMod 2) (w₃ : Fin c → ZMod 2) :
    wt v₁ * wt w₁
      ≤ nnz (triad u₁ v₁ w₁ + triad u₂ v₂ w₂ + triad u₃ v₃ w₃) := by
  obtain ⟨g, hg1, hg2, hg3⟩ := h
  have key : contract₁ (Matrix.of fun _ => g)
      (triad u₁ v₁ w₁ + triad u₂ v₂ w₂ + triad u₃ v₃ w₃)
      = triad (fun _ : Fin 1 => (1 : ZMod 2)) v₁ w₁ := by
    rw [contract₁_add, contract₁_add, contract₁_triad, contract₁_triad,
      contract₁_triad]
    simp only [Matrix.of_apply, hg1, hg2, hg3]
    rw [triad_zero₁, triad_zero₁, add_zero, add_zero]
  have hle := nnz_contract₁_le (Matrix.of fun _ => g)
    (triad u₁ v₁ w₁ + triad u₂ v₂ w₂ + triad u₃ v₃ w₃)
  rwa [key, nnz_triad, wt_one_fin_one, one_mul] at hle

/-- **C2 for triples, mode 1 (stratum (d)).** Linearly independent
mode-1 factors isolate every term, so the 3-sum dominates ALL three
complementary weight products. -/
theorem triple_bounds₁_of_linearIndependent {u₁ u₂ u₃ : Fin a → ZMod 2}
    (h : LinearIndependent (ZMod 2) ![u₁, u₂, u₃])
    (v₁ : Fin b → ZMod 2) (w₁ : Fin c → ZMod 2)
    (v₂ : Fin b → ZMod 2) (w₂ : Fin c → ZMod 2)
    (v₃ : Fin b → ZMod 2) (w₃ : Fin c → ZMod 2) :
    max (max (wt v₁ * wt w₁) (wt v₂ * wt w₂)) (wt v₃ * wt w₃)
      ≤ nnz (triad u₁ v₁ w₁ + triad u₂ v₂ w₂ + triad u₃ v₃ w₃) := by
  obtain ⟨h1, h2, h3⟩ := isolable_all_of_linearIndependent h
  refine max_le (max_le ?_ ?_) ?_
  · exact le_nnz_triple_of_isolable₁ h1 v₁ w₁ v₂ w₂ v₃ w₃
  · have hb := le_nnz_triple_of_isolable₁ h2 v₂ w₂ v₁ w₁ v₃ w₃
    rwa [add_comm (triad u₂ v₂ w₂) (triad u₁ v₁ w₁)] at hb
  · have hb := le_nnz_triple_of_isolable₁ h3 v₃ w₃ v₁ w₁ v₂ w₂
    rwa [add_rotate] at hb

/-! ### The (c)-mode ladder — exact slice decomposition

In a mode where the triple is stratum (c) — third factor = sum of the
first two — the 3-tensor sum decomposes EXACTLY along that mode: each
slice is `0` or one of the three 2D pair-sums `Pᵢⱼ = vᵢ⊗wᵢ + vⱼ⊗wⱼ`,
selected by the support pattern of `(u₁, u₂)`.  One dimension down the
same decomposition resolves each 2D pair into Hamming weights.  The
recursion 3D → 2D → 1D is the ladder; its quantitative consequence
(`le_nnz_triple_ccc`) is that a mode-(c)-EVERYWHERE triple can never
have a sparse sum with uniformly dense factors. -/

/-- Char-2 cancellation: `x + (x + y) = y`. -/
theorem add_add_cancel₁ {n : ℕ} {x y : Fin n → ZMod 2} : x + (x + y) = y := by
  rw [← add_assoc, add_eq_zero_iff_eq.mpr rfl, zero_add]

/-- Char-2 cancellation: `x + (y + x) = y`. -/
theorem add_add_cancel₂ {n : ℕ} {x y : Fin n → ZMod 2} : x + (y + x) = y := by
  rw [add_comm y x, add_add_cancel₁]

/-- 2D nonzero-entry count (matrix-shaped arrays). -/
abbrev nnz₂ {k : Type*} [DecidableEq k] {b c : ℕ} (M : Fin b → Fin c → k) : ℕ :=
  (Finset.univ.filter fun q : Fin b × Fin c => M q.1 q.2 ≠ 0).card

/-- Splitting a filter count by a second predicate. -/
theorem card_filter_and_split {n : ℕ} (p q : Fin n → Prop)
    [DecidablePred p] [DecidablePred q] :
    (Finset.univ.filter fun i => p i).card
      = (Finset.univ.filter fun i => p i ∧ q i).card
        + (Finset.univ.filter fun i => p i ∧ ¬ q i).card := by
  rw [← Finset.filter_filter, ← Finset.filter_filter]
  exact (Finset.card_filter_add_card_filter_not _).symm

/-- Filter counts of conjunctions are symmetric. -/
theorem card_filter_and_comm {n : ℕ} (p q : Fin n → Prop)
    [DecidablePred p] [DecidablePred q] :
    (Finset.univ.filter fun i => p i ∧ q i).card
      = (Finset.univ.filter fun i => q i ∧ p i).card := by
  rw [Finset.filter_and, Finset.filter_and, Finset.inter_comm]

/-- Over `F₂` the support of a sum is the symmetric difference of the
supports. -/
theorem wt_add_eq_card_add_card {n : ℕ} (x y : Fin n → ZMod 2) :
    wt (x + y)
      = (Finset.univ.filter fun i => x i ≠ 0 ∧ y i = 0).card
        + (Finset.univ.filter fun i => x i = 0 ∧ y i ≠ 0).card := by
  have hd : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  have key : (Finset.univ.filter fun i => (x + y) i ≠ 0)
      = Finset.univ.filter
          fun i => (x i ≠ 0 ∧ y i = 0) ∨ (x i = 0 ∧ y i ≠ 0) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hd (x i) with hx | hx <;> rcases hd (y i) with hy | hy <;>
      rw [Pi.add_apply, hx, hy] <;> decide
  have hdisj : Disjoint
      (Finset.univ.filter fun i => x i ≠ 0 ∧ y i = 0)
      (Finset.univ.filter fun i => x i = 0 ∧ y i ≠ 0) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    exact ((Finset.mem_filter.mp hi).2.1) ((Finset.mem_filter.mp hi').2.1)
  rw [wt, key, Finset.filter_or, Finset.card_union_of_disjoint hdisj]

/-- **Ladder, 2D rung.** Over `F₂` a two-generator matrix
`x ⊗ F + y ⊗ G` counts exactly: rows split by the support pattern of
`(x, y)` into copies of `F`, `G`, and `H = F + G`. -/
theorem nnz₂_two_generator {b c : ℕ} (x y : Fin b → ZMod 2)
    (F G H : Fin c → ZMod 2) (hH : ∀ l, H l = F l + G l) :
    nnz₂ (fun j l => x j * F l + y j * G l)
      = (Finset.univ.filter fun j => x j ≠ 0 ∧ y j = 0).card * wt F
        + (Finset.univ.filter fun j => x j = 0 ∧ y j ≠ 0).card * wt G
        + (Finset.univ.filter fun j => x j ≠ 0 ∧ y j ≠ 0).card * wt H := by
  have hd : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  set A := (Finset.univ.filter fun j => x j ≠ 0 ∧ y j = 0) ×ˢ
    (Finset.univ.filter fun l : Fin c => F l ≠ 0) with hA
  set B := (Finset.univ.filter fun j => x j = 0 ∧ y j ≠ 0) ×ˢ
    (Finset.univ.filter fun l : Fin c => G l ≠ 0) with hB
  set C := (Finset.univ.filter fun j => x j ≠ 0 ∧ y j ≠ 0) ×ˢ
    (Finset.univ.filter fun l : Fin c => H l ≠ 0) with hC
  have hmain : (Finset.univ.filter fun q : Fin b × Fin c =>
      x q.1 * F q.2 + y q.1 * G q.2 ≠ 0) = A ∪ B ∪ C := by
    ext ⟨j, l⟩
    simp only [hA, hB, hC, Finset.mem_union, Finset.mem_product,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hd (x j) with hx | hx <;> rcases hd (y j) with hy | hy <;>
      simp [hx, hy, hH]
  have hab : Disjoint A B := by
    rw [Finset.disjoint_left]
    rintro ⟨j, l⟩ hj hj'
    rw [hA, Finset.mem_product, Finset.mem_filter] at hj
    rw [hB, Finset.mem_product, Finset.mem_filter] at hj'
    exact hj'.1.2.1 hj.1.2.1
  have habc : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_left]
    rintro ⟨j, l⟩ hj hj'
    rw [hC, Finset.mem_product, Finset.mem_filter] at hj'
    rcases Finset.mem_union.mp hj with hj | hj
    · rw [hA, Finset.mem_product, Finset.mem_filter] at hj
      exact hj'.1.2.2 hj.1.2.2
    · rw [hB, Finset.mem_product, Finset.mem_filter] at hj
      exact hj'.1.2.1 hj.1.2.1
  calc nnz₂ (fun j l => x j * F l + y j * G l)
      = (Finset.univ.filter fun q : Fin b × Fin c =>
          x q.1 * F q.2 + y q.1 * G q.2 ≠ 0).card := rfl
    _ = (A ∪ B ∪ C).card := by rw [hmain]
    _ = A.card + B.card + C.card := by
        rw [Finset.card_union_of_disjoint habc, Finset.card_union_of_disjoint hab]
    _ = _ := by
        rw [hA, hB, hC, Finset.card_product, Finset.card_product,
          Finset.card_product]
        rfl

/-- **Ladder, 3D rung.** Over `F₂` a two-generator tensor
`x ⊗ F + y ⊗ G` (with `F, G` matrices) counts exactly: mode-1 slices
split by the support pattern of `(x, y)` into copies of `F`, `G`, and
`H = F + G`. -/
theorem nnz_two_generator₁ (x y : Fin a → ZMod 2)
    (F G H : Fin b → Fin c → ZMod 2) (hH : ∀ j l, H j l = F j l + G j l) :
    nnz (fun i j l => x i * F j l + y i * G j l : Tensor (ZMod 2) a b c)
      = (Finset.univ.filter fun i => x i ≠ 0 ∧ y i = 0).card * nnz₂ F
        + (Finset.univ.filter fun i => x i = 0 ∧ y i ≠ 0).card * nnz₂ G
        + (Finset.univ.filter fun i => x i ≠ 0 ∧ y i ≠ 0).card * nnz₂ H := by
  have hd : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  set A := (Finset.univ.filter fun i => x i ≠ 0 ∧ y i = 0) ×ˢ
    (Finset.univ.filter fun q : Fin b × Fin c => F q.1 q.2 ≠ 0) with hA
  set B := (Finset.univ.filter fun i => x i = 0 ∧ y i ≠ 0) ×ˢ
    (Finset.univ.filter fun q : Fin b × Fin c => G q.1 q.2 ≠ 0) with hB
  set C := (Finset.univ.filter fun i => x i ≠ 0 ∧ y i ≠ 0) ×ˢ
    (Finset.univ.filter fun q : Fin b × Fin c => H q.1 q.2 ≠ 0) with hC
  have hmain : (Finset.univ.filter fun p : Fin a × Fin b × Fin c =>
      x p.1 * F p.2.1 p.2.2 + y p.1 * G p.2.1 p.2.2 ≠ 0) = A ∪ B ∪ C := by
    ext ⟨i, j, l⟩
    simp only [hA, hB, hC, Finset.mem_union, Finset.mem_product,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hd (x i) with hx | hx <;> rcases hd (y i) with hy | hy <;>
      simp [hx, hy, hH]
  have hab : Disjoint A B := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j, l⟩ hj hj'
    rw [hA, Finset.mem_product, Finset.mem_filter] at hj
    rw [hB, Finset.mem_product, Finset.mem_filter] at hj'
    exact hj'.1.2.1 hj.1.2.1
  have habc : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j, l⟩ hj hj'
    rw [hC, Finset.mem_product, Finset.mem_filter] at hj'
    rcases Finset.mem_union.mp hj with hj | hj
    · rw [hA, Finset.mem_product, Finset.mem_filter] at hj
      exact hj'.1.2.2 hj.1.2.2
    · rw [hB, Finset.mem_product, Finset.mem_filter] at hj
      exact hj'.1.2.1 hj.1.2.1
  calc nnz (fun i j l => x i * F j l + y i * G j l : Tensor (ZMod 2) a b c)
      = (Finset.univ.filter fun p : Fin a × Fin b × Fin c =>
          x p.1 * F p.2.1 p.2.2 + y p.1 * G p.2.1 p.2.2 ≠ 0).card := rfl
    _ = (A ∪ B ∪ C).card := by rw [hmain]
    _ = A.card + B.card + C.card := by
        rw [Finset.card_union_of_disjoint habc, Finset.card_union_of_disjoint hab]
    _ = _ := by
        rw [hA, hB, hC, Finset.card_product, Finset.card_product,
          Finset.card_product]
        rfl

/-- **The (c)-mode exact formula.** A triple of triads whose mode-1
factors are stratum (c) — `u₃ = u₁ + u₂` — has nonzero count EXACTLY
determined by the support pattern of `(u₁, u₂)` and the three 2D
pair-sums `Pᵢⱼ = vᵢ⊗wᵢ + vⱼ⊗wⱼ`; there is no interaction across
mode-1 slices.  Valid for ARBITRARY `v`s and `w`s. -/
theorem nnz_triple_ladder₁ (u₁ u₂ : Fin a → ZMod 2)
    (v₁ v₂ v₃ : Fin b → ZMod 2) (w₁ w₂ w₃ : Fin c → ZMod 2) :
    nnz (triad u₁ v₁ w₁ + triad u₂ v₂ w₂ + triad (u₁ + u₂) v₃ w₃)
      = (Finset.univ.filter fun i => u₁ i ≠ 0 ∧ u₂ i = 0).card
          * nnz₂ (fun j l => v₁ j * w₁ l + v₃ j * w₃ l)
        + (Finset.univ.filter fun i => u₁ i = 0 ∧ u₂ i ≠ 0).card
          * nnz₂ (fun j l => v₂ j * w₂ l + v₃ j * w₃ l)
        + (Finset.univ.filter fun i => u₁ i ≠ 0 ∧ u₂ i ≠ 0).card
          * nnz₂ (fun j l => v₁ j * w₁ l + v₂ j * w₂ l) := by
  have e : (triad u₁ v₁ w₁ + triad u₂ v₂ w₂ + triad (u₁ + u₂) v₃ w₃)
      = (fun i j l => u₁ i * (v₁ j * w₁ l + v₃ j * w₃ l)
          + u₂ i * (v₂ j * w₂ l + v₃ j * w₃ l) : Tensor (ZMod 2) a b c) := by
    funext i j l
    show u₁ i * v₁ j * w₁ l + u₂ i * v₂ j * w₂ l
        + (u₁ i + u₂ i) * v₃ j * w₃ l = _
    ring
  rw [e]
  exact nnz_two_generator₁ u₁ u₂
    (fun j l => v₁ j * w₁ l + v₃ j * w₃ l)
    (fun j l => v₂ j * w₂ l + v₃ j * w₃ l)
    (fun j l => v₁ j * w₁ l + v₂ j * w₂ l)
    fun j l => by linear_combination -CharTwo.add_self_eq_zero (v₃ j * w₃ l)

/-- **2D pair lower bound.** Over `F₂`, `nnz (v⊗w + v'⊗w')` dominates
`(max of the three v-side weights) * (min of the three w-side
weights)` — the three weights being those of `v, v', v + v'` (resp.
`w, w', w + w'`). -/
theorem le_nnz₂_pair {b c : ℕ} {M m : ℕ} (v v' : Fin b → ZMod 2)
    (w w' : Fin c → ZMod 2)
    (hM : M ≤ max (max (wt v) (wt v')) (wt (v + v')))
    (h₁ : m ≤ wt w) (h₂ : m ≤ wt w') (h₃ : m ≤ wt (w + w')) :
    M * m ≤ nnz₂ (fun j l => v j * w l + v' j * w' l) := by
  rw [nnz₂_two_generator v v' w w' (w + w') fun l => rfl]
  have hv : wt v
      = (Finset.univ.filter fun j => v j ≠ 0 ∧ v' j = 0).card
        + (Finset.univ.filter fun j => v j ≠ 0 ∧ v' j ≠ 0).card :=
    card_filter_and_split _ _
  have hv' : wt v'
      = (Finset.univ.filter fun j => v j = 0 ∧ v' j ≠ 0).card
        + (Finset.univ.filter fun j => v j ≠ 0 ∧ v' j ≠ 0).card := by
    rw [card_filter_and_split (fun j => v' j ≠ 0) (fun j => v j = 0),
      card_filter_and_comm]
    congr 1
    exact card_filter_and_comm _ _
  have hvv' : wt (v + v')
      = (Finset.univ.filter fun j => v j ≠ 0 ∧ v' j = 0).card
        + (Finset.univ.filter fun j => v j = 0 ∧ v' j ≠ 0).card :=
    wt_add_eq_card_add_card v v'
  have hsum : M ≤ (Finset.univ.filter fun j => v j ≠ 0 ∧ v' j = 0).card
      + (Finset.univ.filter fun j => v j = 0 ∧ v' j ≠ 0).card
      + (Finset.univ.filter fun j => v j ≠ 0 ∧ v' j ≠ 0).card := by
    refine hM.trans (max_le (max_le ?_ ?_) ?_) <;> omega
  calc M * m
      ≤ ((Finset.univ.filter fun j => v j ≠ 0 ∧ v' j = 0).card
          + (Finset.univ.filter fun j => v j = 0 ∧ v' j ≠ 0).card
          + (Finset.univ.filter fun j => v j ≠ 0 ∧ v' j ≠ 0).card) * m := by
        gcongr
    _ = (Finset.univ.filter fun j => v j ≠ 0 ∧ v' j = 0).card * m
        + (Finset.univ.filter fun j => v j = 0 ∧ v' j ≠ 0).card * m
        + (Finset.univ.filter fun j => v j ≠ 0 ∧ v' j ≠ 0).card * m := by
        ring
    _ ≤ _ := by gcongr

/-- **Density transfer for the irreducible stratum.** For a
mode-(c)-EVERYWHERE triple — `u₃ = u₁ + u₂`, `v₃ = v₁ + v₂`,
`w₃ = w₁ + w₂` — the sum's nonzero count dominates
`(max u-weight) * (max v-weight) * (min w-weight)`.  Since each
member's count is at most the product of the three maxima, the sum can
undercut the densest member only by the `w`-side weight spread: NO
uniformly dense irreducible triple has a sparse sum.  (By the mode
symmetry of the construction the same holds with the roles of the
modes permuted.) -/
theorem le_nnz_triple_ccc (u₁ u₂ : Fin a → ZMod 2) (v₁ v₂ : Fin b → ZMod 2)
    (w₁ w₂ : Fin c → ZMod 2) :
    max (max (wt u₁) (wt u₂)) (wt (u₁ + u₂))
      * max (max (wt v₁) (wt v₂)) (wt (v₁ + v₂))
      * min (min (wt w₁) (wt w₂)) (wt (w₁ + w₂))
      ≤ nnz (triad u₁ v₁ w₁ + triad u₂ v₂ w₂
          + triad (u₁ + u₂) (v₁ + v₂) (w₁ + w₂)) := by
  rw [nnz_triple_ladder₁]
  have h13 : max (max (wt v₁) (wt v₂)) (wt (v₁ + v₂))
      * min (min (wt w₁) (wt w₂)) (wt (w₁ + w₂))
      ≤ nnz₂ (fun j l => v₁ j * w₁ l + (v₁ + v₂) j * (w₁ + w₂) l) := by
    refine le_nnz₂_pair v₁ (v₁ + v₂) w₁ (w₁ + w₂) ?_ ?_ ?_ ?_
    · rw [add_add_cancel₁]
      exact max_le (max_le (le_max_of_le_left (le_max_left _ _))
        (le_max_right _ _)) (le_max_of_le_left (le_max_right _ _))
    · exact le_trans (min_le_left _ _) (min_le_left _ _)
    · exact min_le_right _ _
    · rw [add_add_cancel₁]
      exact le_trans (min_le_left _ _) (min_le_right _ _)
  have h23 : max (max (wt v₁) (wt v₂)) (wt (v₁ + v₂))
      * min (min (wt w₁) (wt w₂)) (wt (w₁ + w₂))
      ≤ nnz₂ (fun j l => v₂ j * w₂ l + (v₁ + v₂) j * (w₁ + w₂) l) := by
    refine le_nnz₂_pair v₂ (v₁ + v₂) w₂ (w₁ + w₂) ?_ ?_ ?_ ?_
    · rw [add_add_cancel₂]
      exact max_le (max_le (le_max_right _ _)
        (le_max_of_le_left (le_max_left _ _)))
        (le_max_of_le_left (le_max_right _ _))
    · exact le_trans (min_le_left _ _) (min_le_right _ _)
    · exact min_le_right _ _
    · rw [add_add_cancel₂]
      exact le_trans (min_le_left _ _) (min_le_left _ _)
  have h12 : max (max (wt v₁) (wt v₂)) (wt (v₁ + v₂))
      * min (min (wt w₁) (wt w₂)) (wt (w₁ + w₂))
      ≤ nnz₂ (fun j l => v₁ j * w₁ l + v₂ j * w₂ l) := by
    refine le_nnz₂_pair v₁ v₂ w₁ w₂ (le_refl _) ?_ ?_ ?_
    · exact le_trans (min_le_left _ _) (min_le_left _ _)
    · exact le_trans (min_le_left _ _) (min_le_right _ _)
    · exact min_le_right _ _
  have hu₁ : wt u₁
      = (Finset.univ.filter fun i => u₁ i ≠ 0 ∧ u₂ i = 0).card
        + (Finset.univ.filter fun i => u₁ i ≠ 0 ∧ u₂ i ≠ 0).card :=
    card_filter_and_split _ _
  have hu₂ : wt u₂
      = (Finset.univ.filter fun i => u₁ i = 0 ∧ u₂ i ≠ 0).card
        + (Finset.univ.filter fun i => u₁ i ≠ 0 ∧ u₂ i ≠ 0).card := by
    rw [card_filter_and_split (fun i => u₂ i ≠ 0) (fun i => u₁ i = 0),
      card_filter_and_comm]
    congr 1
    exact card_filter_and_comm _ _
  have hu₃ : wt (u₁ + u₂)
      = (Finset.univ.filter fun i => u₁ i ≠ 0 ∧ u₂ i = 0).card
        + (Finset.univ.filter fun i => u₁ i = 0 ∧ u₂ i ≠ 0).card :=
    wt_add_eq_card_add_card u₁ u₂
  have hMu : max (max (wt u₁) (wt u₂)) (wt (u₁ + u₂))
      ≤ (Finset.univ.filter fun i => u₁ i ≠ 0 ∧ u₂ i = 0).card
        + (Finset.univ.filter fun i => u₁ i = 0 ∧ u₂ i ≠ 0).card
        + (Finset.univ.filter fun i => u₁ i ≠ 0 ∧ u₂ i ≠ 0).card := by
    refine max_le (max_le ?_ ?_) ?_ <;> omega
  calc max (max (wt u₁) (wt u₂)) (wt (u₁ + u₂))
      * max (max (wt v₁) (wt v₂)) (wt (v₁ + v₂))
      * min (min (wt w₁) (wt w₂)) (wt (w₁ + w₂))
      = max (max (wt u₁) (wt u₂)) (wt (u₁ + u₂))
        * (max (max (wt v₁) (wt v₂)) (wt (v₁ + v₂))
          * min (min (wt w₁) (wt w₂)) (wt (w₁ + w₂))) := by
        rw [mul_assoc]
    _ ≤ ((Finset.univ.filter fun i => u₁ i ≠ 0 ∧ u₂ i = 0).card
          + (Finset.univ.filter fun i => u₁ i = 0 ∧ u₂ i ≠ 0).card
          + (Finset.univ.filter fun i => u₁ i ≠ 0 ∧ u₂ i ≠ 0).card)
        * (max (max (wt v₁) (wt v₂)) (wt (v₁ + v₂))
          * min (min (wt w₁) (wt w₂)) (wt (w₁ + w₂))) := by
        gcongr
    _ = (Finset.univ.filter fun i => u₁ i ≠ 0 ∧ u₂ i = 0).card
          * (max (max (wt v₁) (wt v₂)) (wt (v₁ + v₂))
            * min (min (wt w₁) (wt w₂)) (wt (w₁ + w₂)))
        + (Finset.univ.filter fun i => u₁ i = 0 ∧ u₂ i ≠ 0).card
          * (max (max (wt v₁) (wt v₂)) (wt (v₁ + v₂))
            * min (min (wt w₁) (wt w₂)) (wt (w₁ + w₂)))
        + (Finset.univ.filter fun i => u₁ i ≠ 0 ∧ u₂ i ≠ 0).card
          * (max (max (wt v₁) (wt v₂)) (wt (v₁ + v₂))
            * min (min (wt w₁) (wt w₂)) (wt (w₁ + w₂))) := by
        ring
    _ ≤ _ := by
        gcongr <;> [exact h13; exact h23; exact h12]

end TripleF2

section TripleCollapse

variable {k : Type*} [CommSemiring k] [CharP k 2] {a b c : ℕ}

/-- **(a), triad level.** A triple of identical tensors collapses to a
single copy in characteristic 2. -/
theorem tensor_add_add_self (T : Tensor k a b c) : T + T + T = T := by
  rw [tensor_add_self, zero_add]

/-- **(b), triad level.** If two of three tensors are equal, the triple
sum collapses to the remaining single term in characteristic 2 (the
equal pair annihilates). -/
theorem tensor_add_add_of_eq {T T' S : Tensor k a b c} (h : T' = T) :
    T + T' + S = S := by
  rw [h, tensor_add_self, zero_add]

end TripleCollapse

end BilinearComplexity
