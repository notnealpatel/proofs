import Combinatorics.PermutationBoundaryStandardization

set_option autoImplicit false

namespace PermutationBoundaryPerturbation

open PermutationOrderCounting PermutationBoundaryStandardization

attribute [local instance] Classical.propDecidable

private theorem remaining_value {n : ℕ} (p r m : Fin n)
    (hr : r ≠ p) (π : FixedFirst p m) : π.val r ≠ m := by
  intro h
  exact hr (π.val.injective (h.trans π.property.symm))

private noncomputable def exchange {n : ℕ} (p r m : Fin n) (hr : r ≠ p)
    (x : FixedFirst p m × {a : Fin n // a ≠ m}) :
    FixedFirst p m × {a : Fin n // a ≠ m} :=
  (⟨x.1.val.trans (Equiv.swap (x.1.val r) x.2.val), by
      change Equiv.swap (x.1.val r) x.2.val (x.1.val p) = m
      rw [x.1.property]
      exact Equiv.swap_apply_of_ne_of_ne
        (remaining_value p r m hr x.1).symm x.2.property.symm⟩,
    ⟨x.1.val r, remaining_value p r m hr x.1⟩)

example (π : FixedFirst (0 : Fin 3) 0) :
    (exchange 0 1 0 (by decide) (π, ⟨2, by decide⟩)).2.val = π.val 1 := rfl

private theorem exchange_value {n : ℕ} (p r m : Fin n) (hr : r ≠ p)
    (x : FixedFirst p m × {a : Fin n // a ≠ m}) :
    (exchange p r m hr x).1.val r = x.2.val := Equiv.swap_apply_left _ _

private theorem exchange_involutive {n : ℕ} (p r m : Fin n) (hr : r ≠ p) :
    Function.Involutive (exchange p r m hr) := by
  intro x
  apply Prod.ext
  · apply Subtype.ext
    apply Equiv.ext
    intro i
    change Equiv.swap ((exchange p r m hr x).1.val r) (x.1.val r)
      (Equiv.swap (x.1.val r) x.2.val (x.1.val i)) = x.1.val i
    rw [exchange_value, Equiv.swap_comm]
    exact Equiv.swap_apply_self _ _ _
  · apply Subtype.ext
    exact exchange_value p r m hr x

/-- Exchanging the observed label with a free label gives the exact one-fixed-label
marginal, for every predicate on the remaining labels. -/
theorem marginal_card {n : ℕ} (p r m : Fin n) (hr : r ≠ p) (P : Fin n → Prop) :
    Nat.card {π : FixedFirst p m // P (π.val r)} * Nat.card {a : Fin n // a ≠ m} =
    Nat.card (FixedFirst p m) * Nat.card {a : Fin n // a ≠ m ∧ P a} := by
  classical
  let f := exchange p r m hr
  let e : ({π : FixedFirst p m // P (π.val r)} × {a : Fin n // a ≠ m}) ≃
      (FixedFirst p m × {a : Fin n // a ≠ m ∧ P a}) :=
    { toFun := fun x => ((f (x.1.val, x.2)).1,
        ⟨x.1.val.val r, remaining_value p r m hr x.1.val, x.1.property⟩)
      invFun := fun y => (⟨(f (y.1, ⟨y.2.val, y.2.property.1⟩)).1, by
        change P ((exchange p r m hr _).1.val r)
        rw [exchange_value]
        exact y.2.property.2⟩,
        (f (y.1, ⟨y.2.val, y.2.property.1⟩)).2)
      left_inv := by
        intro x
        have h := exchange_involutive p r m hr (x.1.val, x.2)
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg Prod.fst h
        · exact congrArg (fun z : FixedFirst p m × {a : Fin n // a ≠ m} => z.2) h
      right_inv := by
        intro y
        have h := exchange_involutive p r m hr (y.1, ⟨y.2.val, y.2.property.1⟩)
        apply Prod.ext
        · exact congrArg (fun z : FixedFirst p m × {a : Fin n // a ≠ m} => z.1) h
        · apply Subtype.ext
          exact congrArg (fun z => z.2.val) h }
  simpa only [Nat.card_prod] using Nat.card_congr e

/-- At a position other than the prescribed one, precisely the fraction
`m/(n-1)` of the labels are strictly below the prescribed label `m`. -/
theorem lower_marginal_card {n : ℕ} (p r m : Fin n) (hr : r ≠ p) :
    Nat.card {π : FixedFirst p m // π.val r < m} * (n - 1) =
      Nat.card (FixedFirst p m) * m.val := by
  classical
  have hc : Nat.card {a : Fin n // a ≠ m} = n - 1 := by
    rw [Nat.card_eq_fintype_card,
      Fintype.card_of_subtype (Finset.univ.erase m) (by simp)]
    simp
  have hl : Nat.card {a : Fin n // a ≠ m ∧ a < m} = m.val := by
    rw [Nat.card_eq_fintype_card,
      Fintype.card_of_subtype (Finset.Iio m) (by
        intro a
        simp only [Finset.mem_Iio]
        exact ⟨fun h => ⟨ne_of_lt h, h⟩, fun h => h.2⟩)]
    exact Fin.card_Iio m
  simpa only [hc, hl] using marginal_card p r m hr (fun a => a < m)

/-- Postcomposing labels with the transposition of `m` and zero identifies the
prescribed-first-label fiber with the minimum-first fiber. -/
noncomputable def swapFirst {n : ℕ} [NeZero n] (m : Fin n) :
    FixedFirst (0 : Fin n) m ≃ FixedFirst (0 : Fin n) 0 where
  toFun π := ⟨π.val.trans (Equiv.swap m 0), by
    change Equiv.swap m 0 (π.val 0) = 0
    rw [π.property, Equiv.swap_apply_left]⟩
  invFun π := ⟨π.val.trans (Equiv.swap m 0), by
    change Equiv.swap m 0 (π.val 0) = m
    rw [π.property, Equiv.swap_apply_right]⟩
  left_inv π := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    exact Equiv.swap_apply_self m 0 (π.val i)
  right_inv π := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    exact Equiv.swap_apply_self m 0 (π.val i)

example {n : ℕ} [NeZero n] (m : Fin n) (π : FixedFirst (0 : Fin n) m) (i : Fin n) :
    (swapFirst m π).val i = Equiv.swap m 0 (π.val i) := rfl

private theorem comparisons_off_bad {n t : ℕ} [NeZero n] [NeZero t]
    (e : Fin t ↪ Fin n) (he : e 0 = 0) (m : Fin n)
    (π : FixedFirst (0 : Fin n) m)
    (hg : ¬ ∃ i : Fin t, i ≠ 0 ∧ π.val (e i) < m) (i j : Fin t) :
    (swapFirst m π).val (e i) < (swapFirst m π).val (e j) ↔
      π.val (e i) < π.val (e j) := by
  have hgt (a : Fin t) (ha : a ≠ 0) : m < π.val (e a) := by
    have hne : e a ≠ 0 := by
      intro h
      exact ha (e.injective (h.trans he.symm))
    exact lt_of_le_of_ne (not_lt.mp (fun h => hg ⟨a, ha, h⟩))
      (remaining_value 0 (e a) m hne π).symm
  have hfix (a : Fin t) (ha : a ≠ 0) :
      (swapFirst m π).val (e a) = π.val (e a) := by
    apply Equiv.swap_apply_of_ne_of_ne
    · exact ne_of_gt (hgt a ha)
    · exact ne_of_gt (lt_of_le_of_lt (Fin.zero_le m) (hgt a ha))
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j; simp
    · rw [hfix j hj, he, π.property, (swapFirst m π).property]
      exact iff_of_true (lt_of_le_of_lt (Fin.zero_le m) (hgt j hj)) (hgt j hj)
  · by_cases hj : j = 0
    · subst j
      rw [hfix i hi, he, π.property, (swapFirst m π).property]
      exact iff_of_false (not_lt_of_ge (Fin.zero_le _)) (not_lt_of_gt (hgt i hi))
    · rw [hfix i hi, hfix j hj]

/-- Away from a selected nonfirst label below `m`, swapping the first label to zero
preserves the actual short-overlap avoidance event. -/
theorem shortAvoid_swapFirst_iff (K n : ℕ) (hK : 4 ≤ K) (hn : 2 * K - 2 ≤ n)
    [NeZero n] [NeZero (2 * K - 2)] (m : Fin n) (π : FixedFirst (0 : Fin n) m)
    (hg : ¬ ∃ i : Fin (2 * K - 2), i ≠ 0 ∧
      π.val (boundaryEmbedding K n (by omega) hn i) < m) :
    ShortAvoid K (swapFirst m π).val ↔ ShortAvoid K π.val := by
  let e := boundaryEmbedding K n (by omega) hn
  have he : e 0 = 0 := boundaryEmbedding_zero K n (by omega) hn
  have hs : standardize e (swapFirst m π).val = standardize e π.val := by
    apply rank_unique
    intro i j
    exact (standardize_lt_iff e π.val i j).trans
      (comparisons_off_bad e he m π hg i j).symm
  rw [← shortAvoid_standardize_iff K n (by omega) hn (swapFirst m π).val,
    ← shortAvoid_standardize_iff K n (by omega) hn π.val]
  exact congrArg (ShortAvoid K) hs ▸ Iff.rfl

private theorem bad_card_bound {n t : ℕ} [NeZero n] [NeZero t]
    (e : Fin t ↪ Fin n) (he : e 0 = 0) (m : Fin n) :
    Nat.card {π : FixedFirst (0 : Fin n) m //
      ∃ i : Fin t, i ≠ 0 ∧ π.val (e i) < m} * (n - 1) ≤
      Nat.card (FixedFirst (0 : Fin n) m) * ((t - 1) * m.val) := by
  classical
  let I := {i : Fin t // i ≠ 0}
  let X := FixedFirst (0 : Fin n) m
  let D := {π : X // ∃ i : Fin t, i ≠ 0 ∧ π.val (e i) < m}
  let Y := Σ i : I, {π : X // π.val (e i.val) < m}
  let f : D → Y := fun π =>
    ⟨⟨Classical.choose π.property, (Classical.choose_spec π.property).1⟩,
      ⟨π.val, (Classical.choose_spec π.property).2⟩⟩
  have hinj : Function.Injective f := by
    intro π τ h
    apply Subtype.ext
    exact congrArg (fun y : Y => y.2.val) h
  have hc : Nat.card D ≤ ∑ i : I, Nat.card {π : X // π.val (e i.val) < m} := by
    simpa only [Y, Nat.card_sigma] using Nat.card_le_card_of_injective f hinj
  have hI : Fintype.card I = t - 1 := by
    rw [Fintype.card_of_subtype (Finset.univ.erase (0 : Fin t)) (by simp)]
    simp
  have hm (i : I) : Nat.card {π : X // π.val (e i.val) < m} * (n - 1) =
      Nat.card X * m.val := by
    apply lower_marginal_card
    intro hi
    exact i.property (e.injective (hi.trans he.symm))
  calc
    Nat.card D * (n - 1) ≤
        (∑ i : I, Nat.card {π : X // π.val (e i.val) < m}) * (n - 1) :=
      Nat.mul_le_mul_right _ hc
    _ = ∑ i : I, Nat.card X * m.val := by rw [Finset.sum_mul]; simp only [hm]
    _ = Nat.card X * ((t - 1) * m.val) := by
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, hI]
      ring

private theorem event_card_le {X : Type*} [Fintype X] (A B D : X → Prop)
    (h : ∀ x, A x → B x ∨ D x) :
    Nat.card {x // A x} ≤ Nat.card {x // B x} + Nat.card {x // D x} := by
  classical
  have hc := Nat.card_le_card_of_injective
    (fun x : {x // A x} => (⟨x.val, h x.val x.property⟩ : {x // B x ∨ D x}))
    (by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : {x // B x ∨ D x} => z.val) hxy)
  have ho : Nat.card {x // B x ∨ D x} ≤ Nat.card {x // B x} + Nat.card {x // D x} := by
    simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_or B D
  exact hc.trans ho

/-- The actual short-avoidance fraction with first label `m` differs from the
minimum-first boundary fraction by at most `(2*K-3)*m/(n-1)`. -/
theorem shortAvoid_fraction_perturbation (K n : ℕ) (hK : 4 ≤ K)
    (hn : 2 * K - 2 ≤ n) (m : Fin n) :
    |(Fintype.card {π : FixedFirst (⟨0, by omega⟩ : Fin n) m // ShortAvoid K π.val} : ℝ) /
        Fintype.card (FixedFirst (⟨0, by omega⟩ : Fin n) m) -
      (Fintype.card {π : FixedFirst (⟨0, by omega⟩ : Fin (2 * K - 2)) ⟨0, by omega⟩ //
        ShortAvoid K π.val} : ℝ) /
        Fintype.card (FixedFirst (⟨0, by omega⟩ : Fin (2 * K - 2)) ⟨0, by omega⟩)| ≤
      ((2 * K : ℝ) - 3) * m.val / ((n : ℝ) - 1) := by
  classical
  rw [← shortAvoid_fraction K n (by omega) hn]
  letI : NeZero n := ⟨by omega⟩
  letI : NeZero (2 * K - 2) := ⟨by omega⟩
  have hz : (⟨0, by omega⟩ : Fin n) = 0 := by apply Fin.ext; rfl
  rw [hz]
  simp only [← Nat.card_eq_fintype_card]
  let X := FixedFirst (0 : Fin n) m
  let Z := FixedFirst (0 : Fin n) 0
  let A : X → Prop := fun π => ShortAvoid K π.val
  let B : X → Prop := fun π => ShortAvoid K (swapFirst m π).val
  let D : X → Prop := fun π => ∃ i : Fin (2 * K - 2), i ≠ 0 ∧
    π.val (boundaryEmbedding K n (by omega) hn i) < m
  have hXZ : Nat.card X = Nat.card Z := Nat.card_congr (swapFirst m)
  have hB : Nat.card {π // B π} = Nat.card {π : Z // ShortAvoid K π.val} := by
    exact Nat.card_congr ((swapFirst m).subtypeEquiv (fun π => Iff.rfl))
  have heq (π : X) (hg : ¬ D π) : A π ↔ B π :=
    (shortAvoid_swapFirst_iff K n hK hn m π hg).symm
  have hAB : Nat.card {π // A π} ≤ Nat.card {π // B π} + Nat.card {π // D π} := by
    apply event_card_le
    intro π hπ
    by_cases hd : D π
    · exact Or.inr hd
    · exact Or.inl ((heq π hd).mp hπ)
  have hBA : Nat.card {π // B π} ≤ Nat.card {π // A π} + Nat.card {π // D π} := by
    apply event_card_le
    intro π hπ
    by_cases hd : D π
    · exact Or.inr hd
    · exact Or.inl ((heq π hd).mpr hπ)
  have hD := bad_card_bound (boundaryEmbedding K n (by omega) hn)
    (boundaryEmbedding_zero K n (by omega) hn) m
  have hF : (0 : ℝ) < Nat.card X := by
    exact_mod_cast (Nat.card_pos_iff.mpr ⟨fixedFirst_nonempty 0 m, inferInstance⟩ :
      0 < Nat.card X)
  have hnR : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hnD : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hbound : (Nat.card {π // D π} : ℝ) / Nat.card X ≤
      ((2 * K : ℝ) - 3) * m.val / ((n : ℝ) - 1) := by
    apply (div_le_div_iff₀ hF hnD).mpr
    have hc : (Nat.card {π // D π} : ℝ) * (n - 1 : ℕ) ≤
        (Nat.card X : ℝ) * (((2 * K - 2) - 1 : ℕ) * m.val) := by
      exact_mod_cast hD
    have hcastN : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
    have hcastK : (((2 * K - 2) - 1 : ℕ) : ℝ) = (2 * K : ℝ) - 3 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * K - 2),
        Nat.cast_sub (by omega : 2 ≤ 2 * K)]
      push_cast
      ring
    rw [hcastN, hcastK] at hc
    nlinarith
  rw [← hB, ← hXZ]
  change |(Nat.card {π // A π} : ℝ) / Nat.card X -
    (Nat.card {π // B π} : ℝ) / Nat.card X| ≤ _
  apply le_trans _ hbound
  apply abs_le.mpr
  have hab : (Nat.card {π // A π} : ℝ) ≤
      Nat.card {π // B π} + Nat.card {π // D π} := by exact_mod_cast hAB
  have hba : (Nat.card {π // B π} : ℝ) ≤
      Nat.card {π // A π} + Nat.card {π // D π} := by exact_mod_cast hBA
  constructor
  · rw [← sub_div, ← neg_div]
    apply (div_le_div_iff_of_pos_right hF).mpr
    linarith
  · rw [← sub_div]
    apply (div_le_div_iff_of_pos_right hF).mpr
    linarith

example : Nonempty (FixedFirst (0 : Fin 6) 3) ∧ 4 ≤ (4 : ℕ) ∧ 2 * 4 - 2 ≤ (6 : ℕ) :=
  ⟨fixedFirst_nonempty 0 3, by decide, by decide⟩

example : (1 : Fin 3) ≠ 0 ∧ Nonempty (FixedFirst (0 : Fin 3) 1) :=
  ⟨by decide, fixedFirst_nonempty 0 1⟩

example : ∃ π : FixedFirst (0 : Fin 6) 0,
    ¬ ∃ i : Fin 6, i ≠ 0 ∧ π.val (boundaryEmbedding 4 6 (by decide) (by decide) i) < 0 := by
  refine ⟨⟨Equiv.refl _, rfl⟩, ?_⟩
  rintro ⟨i, _, hi⟩
  exact (not_lt_of_ge (Fin.zero_le _)) hi


end PermutationBoundaryPerturbation
