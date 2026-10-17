import Combinatorics.PermutationTwoAnchorKernel

set_option autoImplicit false

namespace PermutationTwoBlockCounting

open PermutationBoundaryStandardization PermutationTwoAnchorKernel

/-- The first of the two equally long blocks. -/
def leftBlock (s : ℕ) : Fin (s + 1) ↪ Fin (2 * (s + 1)) where
  toFun i := ⟨i.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun x : Fin (2 * (s + 1)) => x.val) h

/-- The second block, in its original increasing position order. -/
def rightBlock (s : ℕ) : Fin (s + 1) ↪ Fin (2 * (s + 1)) where
  toFun i := ⟨s + 1 + i.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change s + 1 + i.val = s + 1 + j.val at hv
    omega

example (s : ℕ) (i : Fin (s + 1)) : (leftBlock s i).val = i.val := rfl
example (s : ℕ) (i : Fin (s + 1)) : (rightBlock s i).val = s + 1 + i.val := rfl
example : leftBlock 0 0 = (0 : Fin 2) ∧ rightBlock 0 0 = (1 : Fin 2) := by decide

private def blockEquiv (s : ℕ) : Fin (s + 1) ⊕ Fin (s + 1) ≃ Fin (2 * (s + 1)) :=
  finSumFinEquiv.trans (finCongr (by omega))

private theorem blockEquiv_left (s : ℕ) (i : Fin (s + 1)) :
    blockEquiv s (Sum.inl i) = leftBlock s i := rfl

private theorem blockEquiv_right (s : ℕ) (i : Fin (s + 1)) :
    blockEquiv s (Sum.inr i) = rightBlock s i := rfl

private theorem compl_card {s : ℕ} (A : Finset (Fin (2 * (s + 1))))
    (hA : A.card = s + 1) : Aᶜ.card = s + 1 := by
  rw [Finset.card_compl, Fintype.card_fin, hA]
  omega

private noncomputable def assemble {s : ℕ} (A : Finset (Fin (2 * (s + 1))))
    (hA : A.card = s + 1) (α β : Equiv.Perm (Fin (s + 1))) :
    Equiv.Perm (Fin (2 * (s + 1))) := by
  classical
  let eA : Fin (s + 1) ≃ {x // x ∈ A} := (A.orderIsoOfFin hA).toEquiv
  let eB : Fin (s + 1) ≃ {x // x ∈ Aᶜ} := (Aᶜ.orderIsoOfFin (compl_card A hA)).toEquiv
  let eB' : {x // x ∈ Aᶜ} ≃ {x // ¬x ∈ A} := Equiv.subtypeEquivRight (by simp)
  exact (blockEquiv s).symm.trans
    ((Equiv.sumCongr (α.trans eA) (β.trans (eB.trans eB'))).trans
      (Equiv.sumCompl (fun x => x ∈ A)))

private theorem assemble_left {s : ℕ} (A : Finset (Fin (2 * (s + 1))))
    (hA : A.card = s + 1) (α β : Equiv.Perm (Fin (s + 1))) (i : Fin (s + 1)) :
    assemble A hA α β (leftBlock s i) = A.orderEmbOfFin hA (α i) := by
  classical
  rw [← blockEquiv_left]
  simp [assemble]

private theorem assemble_right {s : ℕ} (A : Finset (Fin (2 * (s + 1))))
    (hA : A.card = s + 1) (α β : Equiv.Perm (Fin (s + 1))) (i : Fin (s + 1)) :
    assemble A hA α β (rightBlock s i) = Aᶜ.orderEmbOfFin (compl_card A hA) (β i) := by
  classical
  rw [← blockEquiv_right]
  simp [assemble]

private theorem assemble_standardize {s : ℕ} (A : Finset (Fin (2 * (s + 1))))
    (hA : A.card = s + 1) (α β : Equiv.Perm (Fin (s + 1))) :
    standardize (leftBlock s) (assemble A hA α β) = α ∧
      standardize (rightBlock s) (assemble A hA α β) = β := by
  constructor
  · apply rank_unique
    intro i j
    change α i < α j ↔ assemble A hA α β (leftBlock s i) <
      assemble A hA α β (leftBlock s j)
    rw [assemble_left, assemble_left]
    exact (A.orderEmbOfFin hA).lt_iff_lt.symm
  · apply rank_unique
    intro i j
    change β i < β j ↔ assemble A hA α β (rightBlock s i) <
      assemble A hA α β (rightBlock s j)
    rw [assemble_right, assemble_right]
    exact (Aᶜ.orderEmbOfFin (compl_card A hA)).lt_iff_lt.symm

private theorem image_card {s : ℕ} (e : Fin (s + 1) ↪ Fin (2 * (s + 1)))
    (π : Equiv.Perm (Fin (2 * (s + 1)))) :
    (Finset.univ.image (fun i => π (e i))).card = s + 1 := by
  classical
  have hi : Function.Injective (fun i => π (e i)) := π.injective.comp e.injective
  rw [Finset.card_image_of_injective _ hi]
  exact Fintype.card_fin _

private theorem image_right {s : ℕ} (π : Equiv.Perm (Fin (2 * (s + 1)))) :
    Finset.univ.image (fun i => π (rightBlock s i)) =
      (Finset.univ.image (fun i => π (leftBlock s i)))ᶜ := by
  classical
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_compl]
  constructor
  · rintro ⟨i, rfl⟩ ⟨j, hj⟩
    have h := congrArg Fin.val (π.injective hj)
    change j.val = s + 1 + i.val at h
    omega
  · intro hx
    obtain ⟨y, rfl⟩ := π.surjective x
    by_cases hy : y.val < s + 1
    · exact False.elim (hx ⟨⟨y.val, hy⟩, congrArg π (Fin.ext rfl)⟩)
    · refine ⟨⟨y.val - (s + 1), by omega⟩, congrArg π ?_⟩
      apply Fin.ext
      change s + 1 + (y.val - (s + 1)) = y.val
      omega

private theorem recover_left {s : ℕ} (π : Equiv.Perm (Fin (2 * (s + 1))))
    (α : Equiv.Perm (Fin (s + 1))) (hα : standardize (leftBlock s) π = α)
    (i : Fin (s + 1)) :
    (Finset.univ.image (fun j => π (leftBlock s j))).orderEmbOfFin
      (image_card (leftBlock s) π) (α i) = π (leftBlock s i) := by
  have h := orderEmb_image_rank ((leftBlock s).trans π.toEmbedding) i
  change (Finset.univ.image (fun j => π (leftBlock s j))).orderEmbOfFin _
    (standardize (leftBlock s) π i) = _ at h
  simpa only [hα, Function.Embedding.trans_apply, Equiv.toEmbedding_apply] using h

private theorem recover_right {s : ℕ} (π : Equiv.Perm (Fin (2 * (s + 1))))
    (β : Equiv.Perm (Fin (s + 1))) (hβ : standardize (rightBlock s) π = β)
    (i : Fin (s + 1)) :
    (Finset.univ.image (fun j => π (leftBlock s j)))ᶜ.orderEmbOfFin
      (compl_card _ (image_card (leftBlock s) π)) (β i) = π (rightBlock s i) := by
  have h := orderEmb_image_rank ((rightBlock s).trans π.toEmbedding) i
  change (Finset.univ.image (fun j => π (rightBlock s j))).orderEmbOfFin _
    (standardize (rightBlock s) π i) = _ at h
  simpa only [hβ, image_right, Function.Embedding.trans_apply, Equiv.toEmbedding_apply] using h

/-- Actual permutations with both standardized blocks and both global endpoint labels
prescribed are equivalent to left-label subsets with the corresponding two ordered ranks.
The second ordered rank is in the complement, not in the left-label subset. -/
noncomputable def fiberSubsetEquiv {s : ℕ} (α β : Equiv.Perm (Fin (s + 1)))
    (p q : Fin (2 * (s + 1))) :
    {π : Equiv.Perm (Fin (2 * (s + 1))) //
      standardize (leftBlock s) π = α ∧ standardize (rightBlock s) π = β ∧
      π (leftBlock s 0) = p ∧ π (rightBlock s (Fin.last s)) = q} ≃
    {A : {A : Finset (Fin (2 * (s + 1))) // A.card = s + 1} //
      A.val.orderEmbOfFin A.property (α 0) = p ∧
      A.valᶜ.orderEmbOfFin (compl_card A.val A.property) (β (Fin.last s)) = q} := by
  classical
  let f (π : {π : Equiv.Perm (Fin (2 * (s + 1))) //
      standardize (leftBlock s) π = α ∧ standardize (rightBlock s) π = β ∧
      π (leftBlock s 0) = p ∧ π (rightBlock s (Fin.last s)) = q}) :
      {A : {A : Finset (Fin (2 * (s + 1))) // A.card = s + 1} //
        A.val.orderEmbOfFin A.property (α 0) = p ∧
        A.valᶜ.orderEmbOfFin (compl_card A.val A.property) (β (Fin.last s)) = q} :=
    ⟨⟨Finset.univ.image (fun i => π.val (leftBlock s i)), image_card _ _⟩,
      (recover_left π.val α π.property.1 0).trans π.property.2.2.1,
      (recover_right π.val β π.property.2.1 (Fin.last s)).trans π.property.2.2.2⟩
  apply Equiv.ofBijective f
  constructor
  · intro π τ h
    have hA := congrArg (fun A => A.val.val) h
    change Finset.univ.image (fun i => π.val (leftBlock s i)) =
      Finset.univ.image (fun i => τ.val (leftBlock s i)) at hA
    apply Subtype.ext
    apply Equiv.ext
    intro x
    obtain ⟨y, rfl⟩ := (blockEquiv s).surjective x
    cases y with
    | inl i =>
      rw [blockEquiv_left]
      exact (recover_left π.val α π.property.1 i).symm.trans
        (by simpa only [hA] using recover_left τ.val α τ.property.1 i)
    | inr i =>
      rw [blockEquiv_right]
      exact (recover_right π.val β π.property.2.1 i).symm.trans
        (by simpa only [hA] using recover_right τ.val β τ.property.2.1 i)
  · intro A
    let π := assemble A.val.val A.val.property α β
    have hstd := assemble_standardize A.val.val A.val.property α β
    refine ⟨⟨π, hstd.1, hstd.2, ?_, ?_⟩, ?_⟩
    · exact (assemble_left A.val.val A.val.property α β 0).trans A.property.1
    · exact (assemble_right A.val.val A.val.property α β (Fin.last s)).trans A.property.2
    · apply Subtype.ext
      apply Subtype.ext
      change Finset.univ.image (fun i => assemble A.val.val A.val.property α β
        (leftBlock s i)) = A.val.val
      simp only [assemble_left]
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        exact A.val.val.orderEmbOfFin_mem A.val.property (α i)
      · intro hx
        obtain ⟨i, hi⟩ := (A.val.val.orderIsoOfFin A.val.property).surjective ⟨x, hx⟩
        exact ⟨α.symm i, by simpa using congrArg Subtype.val hi⟩

private theorem filter_compl_count {n : ℕ} (A : Finset (Fin n)) (q : Fin n) :
    (A.filter (fun x => x < q)).card + (Aᶜ.filter (fun x => x < q)).card = q.val := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := Finset.Iio q) (fun x => x ∈ A)
  have h₁ : (Finset.Iio q).filter (fun x => x ∈ A) = A.filter (fun x => x < q) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Iio]
    exact and_comm
  have h₂ : (Finset.Iio q).filter (fun x => ¬x ∈ A) = Aᶜ.filter (fun x => x < q) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Iio, Finset.mem_compl]
    exact and_comm
  simpa only [h₁, h₂, Fin.card_Iio] using h

private noncomputable def augmentEquiv {s : ℕ} (r t : Fin (s + 1))
    (p q : Fin (2 * (s + 1))) (hpq : p < q) (k : Fin (s + 2))
    (hrk : r.val < k.val) (hk : k.val + t.val = q.val) :
    {A : {A : Finset (Fin (2 * (s + 1))) // A.card = s + 1} //
      A.val.orderEmbOfFin A.property r = p ∧
      A.valᶜ.orderEmbOfFin (compl_card A.val A.property) t = q} ≃
    {B : {B : Finset (Fin (2 * (s + 1))) // B.card = s + 2} //
      B.val.orderEmbOfFin B.property ⟨r.val, by omega⟩ = p ∧
      B.val.orderEmbOfFin B.property k = q} := by
  classical
  let f (A : {A : {A : Finset (Fin (2 * (s + 1))) // A.card = s + 1} //
      A.val.orderEmbOfFin A.property r = p ∧
      A.valᶜ.orderEmbOfFin (compl_card A.val A.property) t = q}) :
      {B : {B : Finset (Fin (2 * (s + 1))) // B.card = s + 2} //
        B.val.orderEmbOfFin B.property ⟨r.val, by omega⟩ = p ∧
        B.val.orderEmbOfFin B.property k = q} := by
    have hp := (orderEmb_eq_iff_filter_card _ _ r p).mp A.property.1
    have hq := (orderEmb_eq_iff_filter_card _ _ t q).mp A.property.2
    have hqn : q ∉ A.val.val := Finset.mem_compl.mp hq.1
    have hc : (insert q A.val.val).card = s + 2 := by
      rw [Finset.card_insert_of_notMem hqn, A.val.property]
    refine ⟨⟨insert q A.val.val, hc⟩, ?_, ?_⟩
    · apply (orderEmb_eq_iff_filter_card _ _ _ _).mpr
      refine ⟨Finset.mem_insert_of_mem hp.1, ?_⟩
      simpa [Finset.filter_insert, not_lt_of_ge hpq.le] using hp.2
    · apply (orderEmb_eq_iff_filter_card _ _ _ _).mpr
      refine ⟨Finset.mem_insert_self _ _, ?_⟩
      have hsum := filter_compl_count A.val.val q
      rw [hq.2] at hsum
      simp only [Finset.filter_insert, lt_self_iff_false, if_false]
      omega
  apply Equiv.ofBijective f
  constructor
  · intro A B h
    have he := congrArg (fun B => B.val.val) h
    change insert q A.val.val = insert q B.val.val at he
    have hA := (orderEmb_eq_iff_filter_card _ _ t q).mp A.property.2
    have hB := (orderEmb_eq_iff_filter_card _ _ t q).mp B.property.2
    apply Subtype.ext
    apply Subtype.ext
    have he' := congrArg (fun C => C.erase q) he
    simpa [Finset.mem_compl.mp hA.1, Finset.mem_compl.mp hB.1] using he'
  · intro B
    have hp := (orderEmb_eq_iff_filter_card _ _ (⟨r.val, by omega⟩ : Fin (s + 2)) p).mp B.property.1
    have hq := (orderEmb_eq_iff_filter_card _ _ k q).mp B.property.2
    let A := B.val.val.erase q
    have hA : A.card = s + 1 := by
      dsimp [A]
      rw [Finset.card_erase_of_mem hq.1, B.val.property]
      omega
    have hAp : A.orderEmbOfFin hA r = p := by
      apply (orderEmb_eq_iff_filter_card _ _ _ _).mpr
      refine ⟨Finset.mem_erase.mpr ⟨hpq.ne, hp.1⟩, ?_⟩
      simpa [A, Finset.filter_erase, Finset.erase_eq_of_notMem,
        not_lt_of_ge hpq.le] using hp.2
    have hAq : Aᶜ.orderEmbOfFin (compl_card A hA) t = q := by
      apply (orderEmb_eq_iff_filter_card _ _ _ _).mpr
      refine ⟨by simp [A], ?_⟩
      have hsum := filter_compl_count A q
      have hbelow : (A.filter (fun x => x < q)).card = k.val := by
        simpa [A, Finset.filter_erase] using hq.2
      rw [hbelow] at hsum
      omega
    refine ⟨⟨⟨A, hA⟩, hAp, hAq⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change insert q (B.val.val.erase q) = B.val.val
    exact Finset.insert_erase hq.1

/-- The actual two-block standardized fiber has the three-binomial shuffle weight.
Endpoint labels are global, whereas the two permutation values in the binomial
parameters are local ranks. The last factor is in its unsymmetrized form. -/
theorem card_fiber (s : ℕ) (α β : Equiv.Perm (Fin (s + 1)))
    (a b : ℕ) (ha : a ≤ (β (Fin.last s)).val) (hb : b ≤ s - (α 0).val) :
    Fintype.card {π : Equiv.Perm (Fin (2 * (s + 1))) //
      standardize (leftBlock s) π = α ∧ standardize (rightBlock s) π = β ∧
      (π (leftBlock s 0)).val = (α 0).val + a ∧
      (π (rightBlock s (Fin.last s))).val = (α 0).val + b + (β (Fin.last s)).val + 1} =
      Nat.choose ((α 0).val + a) (α 0).val *
        Nat.choose (b + (β (Fin.last s)).val - a) b *
        Nat.choose (2 * (s + 1) - 1 - ((α 0).val + b + (β (Fin.last s)).val + 1))
          (s - (α 0).val - b) := by
  classical
  let r := α 0
  let t := β (Fin.last s)
  have hr : r.val ≤ s := by omega
  have ht : t.val ≤ s := by omega
  let p : Fin (2 * (s + 1)) := ⟨r.val + a, by dsimp [r, t] at *; omega⟩
  let q : Fin (2 * (s + 1)) := ⟨r.val + b + t.val + 1, by dsimp [r, t] at *; omega⟩
  let k : Fin (s + 2) := ⟨r.val + b + 1, by dsimp [r] at *; omega⟩
  have hpq : p < q := by change r.val + a < r.val + b + t.val + 1; dsimp [t] at *; omega
  have hrk : r.val < k.val := by dsimp [k]; omega
  have hk : k.val + t.val = q.val := by dsimp [k, q]; omega
  let e := (fiberSubsetEquiv α β p q).trans
    ((augmentEquiv r t p q hpq k hrk hk).trans
      (anchoredSubsetIntervalEquiv p q hpq ⟨r.val, by omega⟩ k (by exact hrk)))
  have he : Fintype.card {π : Equiv.Perm (Fin (2 * (s + 1))) //
      standardize (leftBlock s) π = α ∧ standardize (rightBlock s) π = β ∧
      (π (leftBlock s 0)).val = r.val + a ∧
      (π (rightBlock s (Fin.last s))).val = r.val + b + t.val + 1} =
      Fintype.card (↥((Finset.Iio p).powersetCard r.val) ×
        ↥((Finset.Ioo p q).powersetCard (k.val - r.val - 1)) ×
        ↥((Finset.Ioi q).powersetCard (s + 2 - 1 - k.val))) := by
    apply Fintype.card_congr
    exact (Equiv.subtypeEquivRight (fun π => by
      simp only [Fin.ext_iff]
      rfl)).trans e
  have hmid : q.val - p.val - 1 = b + t.val - a := by dsimp [p, q]; omega
  have hkc : k.val - r.val - 1 = b := by dsimp [k]; omega
  have hlast : s + 2 - 1 - k.val = s - r.val - b := by dsimp [k]; omega
  rw [he]
  simp only [Fintype.card_prod, Fintype.card_coe, Finset.card_powersetCard,
    Fin.card_Iio, Fin.card_Ioo, Fin.card_Ioi, hmid, hkc, hlast]
  exact (Nat.mul_assoc _ _ _).symm

example {s : ℕ} (α β : Equiv.Perm (Fin (s + 1)))
    (p q : Fin (2 * (s + 1))) :
    ∀ π, ((fiberSubsetEquiv α β p q) π).val.val =
      Finset.univ.image (fun i => π.val (leftBlock s i)) := fun _ => rfl

example {s : ℕ} (r t : Fin (s + 1)) (p q : Fin (2 * (s + 1)))
    (hpq : p < q) (k : Fin (s + 2)) (hrk : r.val < k.val)
    (hk : k.val + t.val = q.val) :
    ∀ A, ((augmentEquiv r t p q hpq k hrk hk) A).val.val = insert q A.val.val :=
  fun _ => rfl

example : (0 : ℕ) ≤ ((Equiv.refl (Fin 1)) (Fin.last 0)).val ∧
    (0 : ℕ) ≤ 0 - ((Equiv.refl (Fin 1)) 0).val := by decide

example : Fintype.card {π : Equiv.Perm (Fin 2) //
    standardize (leftBlock 0) π = Equiv.refl _ ∧
    standardize (rightBlock 0) π = Equiv.refl _ ∧
    (π (leftBlock 0 0)).val = 0 ∧
    (π (rightBlock 0 (Fin.last 0))).val = 1} = 1 := by
  simpa using card_fiber 0 (Equiv.refl _) (Equiv.refl _) 0 0 (by decide) (by decide)

example : Nonempty {π : Equiv.Perm (Fin 2) //
    standardize (leftBlock 0) π = Equiv.refl _ ∧
    standardize (rightBlock 0) π = Equiv.refl _ ∧
    (π (leftBlock 0 0)).val = 0 ∧
    (π (rightBlock 0 (Fin.last 0))).val = 1} := by
  refine ⟨⟨Equiv.refl _, ?_, ?_, rfl, rfl⟩⟩
  · apply rank_unique
    intro i j
    rfl
  · apply rank_unique
    intro i j
    change i.val < j.val ↔ 0 + 1 + i.val < 0 + 1 + j.val
    omega

end PermutationTwoBlockCounting
