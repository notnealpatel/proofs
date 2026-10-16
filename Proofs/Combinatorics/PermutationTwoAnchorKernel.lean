import Combinatorics.PermutationBoundaryStandardization
import Combinatorics.PermutationEndpointCounting

set_option autoImplicit false

namespace PermutationTwoAnchorKernel

open PermutationBoundaryStandardization PermutationEndpointCounting

/-- Prescribing all selected labels leaves exactly the bijections of their complements. -/
noncomputable def completionEquiv {n L : ℕ} (e f : Fin L ↪ Fin n) :
    {π : Equiv.Perm (Fin n) // ∀ i, π (e i) = f i} ≃
      ({x : Fin n // x ∉ Set.range e} ≃ {x : Fin n // x ∉ Set.range f}) := by
  classical
  let g : Set.range e ≃ Set.range f :=
    (Equiv.ofInjective e e.injective).symm.trans (Equiv.ofInjective f f.injective)
  have hg (i : Fin L) : (g ⟨e i, ⟨i, rfl⟩⟩).val = f i := by simp [g]
  let restrict (π : {π : Equiv.Perm (Fin n) // ∀ i, π (e i) = f i}) :
      {x : Fin n // x ∉ Set.range e} ≃ {x : Fin n // x ∉ Set.range f} :=
    { toFun := fun x => ⟨π.val x, by
        rintro ⟨i, hi⟩
        exact x.property ⟨i, π.val.injective ((π.property i).trans hi)⟩⟩
      invFun := fun y => ⟨π.val.symm y, by
        rintro ⟨i, hi⟩
        apply y.property
        refine ⟨i, ?_⟩
        rw [← π.property i, hi, Equiv.apply_symm_apply]⟩
      left_inv := by intro x; apply Subtype.ext; exact π.val.symm_apply_apply x
      right_inv := by intro y; apply Subtype.ext; exact π.val.apply_symm_apply y }
  let extend (c : {x : Fin n // x ∉ Set.range e} ≃
      {x : Fin n // x ∉ Set.range f}) :
      {π : Equiv.Perm (Fin n) // ∀ i, π (e i) = f i} :=
    ⟨Equiv.subtypeCongr g c, by
      intro i
      change ((Equiv.sumCompl (fun x => x ∈ Set.range f))
        ((Equiv.sumCongr g c) ((Equiv.sumCompl (fun x => x ∈ Set.range e)).symm (e i)))) = f i
      simp [Equiv.sumCompl, hg]⟩
  exact
    { toFun := restrict
      invFun := extend
      left_inv := by
        intro π
        apply Subtype.ext
        apply Equiv.ext
        intro x
        by_cases hx : x ∈ Set.range e
        · obtain ⟨i, rfl⟩ := hx
          exact (extend (restrict π)).property i |>.trans (π.property i).symm
        · change (Equiv.subtypeCongr g (restrict π)) x = π.val x
          have hx' : ¬ ∃ i, e i = x := hx
          simp [Equiv.subtypeCongr, Equiv.sumCompl, hx', restrict]
      right_inv := by
        intro c
        apply Equiv.ext
        intro x
        apply Subtype.ext
        change (Equiv.subtypeCongr g c) x.val = (c x).val
        have hx' : ¬ ∃ i, e i = x.val := x.property
        simp [Equiv.subtypeCongr, Equiv.sumCompl, hx'] }

example : Nonempty {π : Equiv.Perm (Fin 2) //
    ∀ i, π ((Function.Embedding.refl (Fin 2)) i) = i} := ⟨⟨Equiv.refl _, fun _ => rfl⟩⟩

/-- There are `(n-L)!` ways to complete any prescribed injective selected list. -/
theorem card_completion {n L : ℕ} (e f : Fin L ↪ Fin n) :
    Fintype.card {π : Equiv.Perm (Fin n) // ∀ i, π (e i) = f i} =
      (n - L).factorial := by
  classical
  have hc (g : Fin L ↪ Fin n) :
      Fintype.card {x : Fin n // x ∉ Set.range g} = n - L := by
    have hr : Fintype.card (Set.range g) = L := by
      simpa using (Fintype.card_congr (Equiv.ofInjective g g.injective)).symm
    have h := Fintype.card_compl_set (Set.range g)
    rw [← Nat.card_eq_fintype_card] at h ⊢
    exact h.trans (by rw [Fintype.card_fin, hr])
  rw [Fintype.card_congr (completionEquiv e f)]
  rw [Fintype.card_equiv (Fintype.equivOfCardEq ((hc e).trans (hc f).symm)), hc e]

/-- A standardized two-anchor fiber is a selected anchored label list together with
an arbitrary completion of that entire list. -/
noncomputable def standardizedFiberEquiv {n L : ℕ} (e : Fin L ↪ Fin n)
    (i j : Fin L) (a b : Fin n) (σ : Equiv.Perm (Fin L)) :
    {π : FixedTwo (e i) (e j) a b // standardize e π.val = σ} ≃
      (Σ f : {f : Fin L ↪ Fin n // rank f = σ ∧ f i = a ∧ f j = b},
        {π : Equiv.Perm (Fin n) // ∀ k, π (e k) = f.val k}) := by
  classical
  let assemble :
      (Σ f : {f : Fin L ↪ Fin n // rank f = σ ∧ f i = a ∧ f j = b},
        {π : Equiv.Perm (Fin n) // ∀ k, π (e k) = f.val k}) →
      {π : FixedTwo (e i) (e j) a b // standardize e π.val = σ} := fun z =>
    ⟨⟨z.2.val, (z.2.property i).trans z.1.property.2.1,
        (z.2.property j).trans z.1.property.2.2⟩, by
      have he : e.trans z.2.val.toEmbedding = z.1.val := by
        apply Function.Embedding.ext
        intro k
        exact z.2.property k
      change rank (e.trans z.2.val.toEmbedding) = σ
      rw [he, z.1.property.1]⟩
  apply (Equiv.ofBijective assemble ?_).symm
  constructor
  · rintro ⟨f, π⟩ ⟨g, τ⟩ h
    have hp : π.val = τ.val := congrArg (fun x => x.val.val) h
    have hf : f = g := by
      apply Subtype.ext
      apply Function.Embedding.ext
      intro k
      exact (π.property k).symm.trans ((congrArg (fun p => p (e k)) hp).trans
        (τ.property k))
    subst g
    have hπτ : π = τ := Subtype.ext hp
    subst τ
    rfl
  · intro π
    refine ⟨⟨⟨e.trans π.val.val.toEmbedding, π.property,
      π.val.property.1, π.val.property.2⟩, ⟨π.val.val, fun _ => rfl⟩⟩, ?_⟩
    rfl

/-- Every anchored selected label list of rank `σ` contributes exactly `(n-L)!`
actual permutations to its two-anchor standardized fiber. -/
theorem card_standardizedFiber {n L : ℕ} (e : Fin L ↪ Fin n)
    (i j : Fin L) (a b : Fin n) (σ : Equiv.Perm (Fin L)) :
    Fintype.card {π : FixedTwo (e i) (e j) a b // standardize e π.val = σ} =
      Fintype.card {f : Fin L ↪ Fin n // rank f = σ ∧ f i = a ∧ f j = b} *
        (n - L).factorial := by
  classical
  rw [Fintype.card_congr (standardizedFiberEquiv e i j a b σ), Fintype.card_sigma]
  simp only [card_completion, Finset.sum_const, Finset.card_univ, smul_eq_mul]

example : Fintype.card {π : FixedTwo (0 : Fin 2) 1 0 1 //
    standardize (Function.Embedding.refl (Fin 2)) π.val = Equiv.refl _} =
      Fintype.card {f : Fin 2 ↪ Fin 2 // rank f = Equiv.refl _ ∧ f 0 = 0 ∧ f 1 = 1} *
        (2 - 2).factorial :=
  card_standardizedFiber (Function.Embedding.refl (Fin 2)) 0 1 0 1 (Equiv.refl _)

example : Nonempty {π : FixedTwo (0 : Fin 2) 1 0 1 //
    standardize (Function.Embedding.refl (Fin 2)) π.val = Equiv.refl _} := by
  refine ⟨⟨⟨Equiv.refl _, rfl, rfl⟩, ?_⟩⟩
  apply rank_unique
  intro i j
  rfl

example {n L : ℕ} (e f : Fin L ↪ Fin n)
    (π : {π : Equiv.Perm (Fin n) // ∀ i, π (e i) = f i})
    (x : {x : Fin n // x ∉ Set.range e}) :
    ((completionEquiv e f π) x).val = π.val x.val := rfl

example {n L : ℕ} (e : Fin L ↪ Fin n) (i j : Fin L)
    (a b : Fin n) (σ : Equiv.Perm (Fin L))
    (z : Σ f : {f : Fin L ↪ Fin n // rank f = σ ∧ f i = a ∧ f j = b},
      {π : Equiv.Perm (Fin n) // ∀ k, π (e k) = f.val k}) :
    ((standardizedFiberEquiv e i j a b σ).symm z).val.val = z.2.val := rfl

/-- Increasing prescribed labels force increasing endpoint ranks; the reverse-rank
standardized fiber is empty, not a truncated-subtraction contribution. -/
theorem card_standardizedFiber_eq_zero {n L : ℕ} (e : Fin L ↪ Fin n)
    (i j : Fin L) (a b : Fin n) (σ : Equiv.Perm (Fin L))
    (hab : a < b) (hσ : ¬ σ i < σ j) :
    Fintype.card {π : FixedTwo (e i) (e j) a b // standardize e π.val = σ} = 0 := by
  classical
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun π => ?_⟩
  apply hσ
  rw [← π.property, standardize_lt_iff, π.val.property.1, π.val.property.2]
  exact hab

example : Fintype.card {π : FixedTwo (0 : Fin 2) 1 0 1 //
    standardize (Function.Embedding.refl (Fin 2)) π.val = Equiv.swap 0 1} = 0 :=
  card_standardizedFiber_eq_zero (Function.Embedding.refl (Fin 2))
    0 1 0 1 (Equiv.swap 0 1) (by decide) (by decide)

example : Nonempty {f : Fin 2 ↪ Fin 3 //
    rank f = Equiv.refl _ ∧ f 0 = 0 ∧ f 1 = 1} := by
  let f : Fin 2 ↪ Fin 3 := ⟨fun i => ⟨i.val, by omega⟩, by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin 3 => x.val) h)⟩
  refine ⟨⟨f, ?_, rfl, rfl⟩⟩
  apply rank_unique
  intro i j
  rfl

/-- Sorting the selected labels and evaluating at an entry's rank recovers that entry. -/
theorem orderEmb_image_rank {n L : ℕ} (f : Fin L ↪ Fin n) (k : Fin L) :
    (Finset.univ.image f).orderEmbOfFin (by simp [Finset.card_image_of_injective,
      f.injective]) (rank f k) = f k := by
  classical
  have hc : (Finset.univ.image f).card = L := by
    rw [Finset.card_image_of_injective _ f.injective]
    simp
  have hm : StrictMono (fun q => f ((rank f).symm q)) := by
    intro q r hqr
    apply (rank_lt_iff f _ _).mp
    simpa only [Equiv.apply_symm_apply] using hqr
  have he := Finset.orderEmbOfFin_unique hc
    (f := fun q => f ((rank f).symm q)) (fun q => by simp) hm
  have hk := congrFun he (rank f k)
  simpa only [Equiv.symm_apply_apply] using hk.symm

/-- Anchored rank lists are exactly selected label subsets whose increasing enumeration
has the prescribed labels at the prescribed ranks. -/
noncomputable def anchoredListSubsetEquiv {n L : ℕ} (i j : Fin L)
    (a b : Fin n) (σ : Equiv.Perm (Fin L)) :
    {f : Fin L ↪ Fin n // rank f = σ ∧ f i = a ∧ f j = b} ≃
      {s : {s : Finset (Fin n) // s.card = L} //
        s.val.orderEmbOfFin s.property (σ i) = a ∧
        s.val.orderEmbOfFin s.property (σ j) = b} := by
  classical
  let chooseList (s : {s : {s : Finset (Fin n) // s.card = L} //
      s.val.orderEmbOfFin s.property (σ i) = a ∧
      s.val.orderEmbOfFin s.property (σ j) = b}) :
      {f : Fin L ↪ Fin n // rank f = σ ∧ f i = a ∧ f j = b} :=
    ⟨σ.toEmbedding.trans (s.val.val.orderEmbOfFin s.val.property).toEmbedding, by
      constructor
      · apply rank_unique
        intro k l
        exact (s.val.val.orderEmbOfFin s.val.property).lt_iff_lt.symm
      · exact s.property⟩
  let chooseSet (f : {f : Fin L ↪ Fin n // rank f = σ ∧ f i = a ∧ f j = b}) :
      {s : {s : Finset (Fin n) // s.card = L} //
        s.val.orderEmbOfFin s.property (σ i) = a ∧
        s.val.orderEmbOfFin s.property (σ j) = b} :=
    ⟨⟨Finset.univ.image f.val, by
      rw [Finset.card_image_of_injective _ f.val.injective]
      simp⟩, by
      constructor
      · have hi := orderEmb_image_rank f.val i
        rw [f.property.1] at hi
        exact hi.trans f.property.2.1
      · have hj := orderEmb_image_rank f.val j
        rw [f.property.1] at hj
        exact hj.trans f.property.2.2⟩
  exact
    { toFun := chooseSet
      invFun := chooseList
      left_inv := by
        intro f
        apply Subtype.ext
        apply Function.Embedding.ext
        intro k
        change (Finset.univ.image f.val).orderEmbOfFin
          (by rw [Finset.card_image_of_injective _ f.val.injective]; simp) (σ k) = f.val k
        have hk := orderEmb_image_rank f.val k
        rw [f.property.1] at hk
        exact hk
      right_inv := by
        intro s
        apply Subtype.ext
        apply Subtype.ext
        change Finset.univ.image (fun k => s.val.val.orderEmbOfFin s.val.property (σ k)) = s.val.val
        change Finset.univ.image ((s.val.val.orderEmbOfFin s.val.property) ∘ σ) = s.val.val
        rw [← Finset.image_image]
        have hu : Finset.univ.image σ = Finset.univ := by
          ext k
          simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
          exact σ.surjective k
        rw [hu, Finset.image_orderEmbOfFin_univ] }

example {n L : ℕ} (i j : Fin L) (a b : Fin n) (σ : Equiv.Perm (Fin L))
    (f : {f : Fin L ↪ Fin n // rank f = σ ∧ f i = a ∧ f j = b}) :
    ((anchoredListSubsetEquiv i j a b σ) f).val.val = Finset.univ.image f.val := rfl

/-- The actual two-anchor standardized fiber counts anchored ordered subsets, with
exactly `(n-L)!` completions per subset and no selected-position factorial. -/
theorem card_standardizedFiber_subsets {n L : ℕ} (e : Fin L ↪ Fin n)
    (i j : Fin L) (a b : Fin n) (σ : Equiv.Perm (Fin L)) :
    Fintype.card {π : FixedTwo (e i) (e j) a b // standardize e π.val = σ} =
      Fintype.card {s : {s : Finset (Fin n) // s.card = L} //
        s.val.orderEmbOfFin s.property (σ i) = a ∧
        s.val.orderEmbOfFin s.property (σ j) = b} * (n - L).factorial := by
  classical
  rw [card_standardizedFiber, Fintype.card_congr (anchoredListSubsetEquiv i j a b σ)]

/-- In a sorted selected subset, exactly `r` selected labels precede entry `r`. -/
theorem card_filter_lt_orderEmb {n L : ℕ} (s : Finset (Fin n)) (hs : s.card = L)
    (r : Fin L) : (s.filter (fun x => x < s.orderEmbOfFin hs r)).card = r.val := by
  classical
  conv_lhs => arg 1; arg 2; rw [← Finset.image_orderEmbOfFin_univ s hs]
  rw [Finset.filter_image, Finset.card_image_of_injective _ (s.orderEmbOfFin hs).injective]
  simp only [(s.orderEmbOfFin hs).lt_iff_lt]
  change (Finset.univ.filter (fun k : Fin L => k.val < r.val)).card = r.val
  rw [Fin.card_filter_val_lt, Nat.min_eq_right (Nat.le_of_lt r.isLt)]

/-- The label at a specified selected rank is characterized by membership and the
number of selected labels strictly below it. -/
theorem orderEmb_eq_iff_filter_card {n L : ℕ} (s : Finset (Fin n)) (hs : s.card = L)
    (r : Fin L) (a : Fin n) :
    s.orderEmbOfFin hs r = a ↔ a ∈ s ∧ (s.filter (fun x => x < a)).card = r.val := by
  constructor
  · intro h
    subst a
    exact ⟨s.orderEmbOfFin_mem hs r, card_filter_lt_orderEmb s hs r⟩
  · rintro ⟨ha, hc⟩
    obtain ⟨q, hq⟩ := (s.orderIsoOfFin hs).surjective ⟨a, ha⟩
    have hqa : s.orderEmbOfFin hs q = a := congrArg Subtype.val hq
    have hqc := card_filter_lt_orderEmb s hs q
    rw [hqa, hc] at hqc
    have hqr : q = r := Fin.ext hqc.symm
    simpa only [hqr] using hqa

/-- Joining independent lower, middle, and upper interval choices with the two
anchors recovers those three choices and their exact selected-label counts. -/
theorem interval_union_stats {n : ℕ} (a b : Fin n) (hab : a < b)
    (A B C : Finset (Fin n)) (hA : A ⊆ Finset.Iio a)
    (hB : B ⊆ Finset.Ioo a b) (hC : C ⊆ Finset.Ioi b) :
    let s := insert a (insert b (A ∪ B ∪ C))
    s.card = A.card + B.card + C.card + 2 ∧
    s.filter (fun x => x < a) = A ∧
    s.filter (fun x => a < x ∧ x < b) = B ∧
    s.filter (fun x => b < x) = C ∧
    (s.filter (fun x => x < b)).card = A.card + B.card + 1 := by
  classical
  have ha (x : Fin n) (hx : x ∈ A) : x < a := Finset.mem_Iio.mp (hA hx)
  have hb (x : Fin n) (hx : x ∈ B) : a < x ∧ x < b := Finset.mem_Ioo.mp (hB hx)
  have hc (x : Fin n) (hx : x ∈ C) : b < x := Finset.mem_Ioi.mp (hC hx)
  have hdAB : Disjoint A B := Finset.disjoint_left.mpr (by
    intro x hx hy
    exact (not_lt_of_ge (le_of_lt (ha x hx))) (hb x hy).1)
  have hdABC : Disjoint (A ∪ B) C := Finset.disjoint_left.mpr (by
    intro x hx hy
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (not_lt_of_ge (le_of_lt ((ha x hx).trans hab))) (hc x hy)
    · exact (not_lt_of_ge (le_of_lt (hb x hx).2)) (hc x hy))
  have hna : a ∉ insert b (A ∪ B ∪ C) := by
    simp only [Finset.mem_insert, Finset.mem_union, not_or]
    exact ⟨hab.ne, ⟨⟨fun h => (ha a h).false,
      fun h => (hb a h).1.false⟩, fun h => (hab.trans (hc a h)).false⟩⟩
  have hnb : b ∉ A ∪ B ∪ C := by
    simp only [Finset.mem_union, not_or]
    exact ⟨⟨fun h => (hab.trans (ha b h)).false,
      fun h => (hb b h).2.false⟩, fun h => (hc b h).false⟩
  let s := insert a (insert b (A ∪ B ∪ C))
  have hlow : s.filter (fun x => x < a) = A := by
    ext x
    simp only [s, Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
    constructor
    · rintro ⟨hx, hxa⟩
      rcases hx with rfl | rfl | (hx | hx) | hx
      · exact False.elim (lt_irrefl _ hxa)
      · exact False.elim ((hab.trans hxa).false)
      · exact hx
      · exact False.elim (((hb x hx).1.trans hxa).false)
      · exact False.elim ((hab.trans ((hc x hx).trans hxa)).false)
    · intro hx
      exact ⟨Or.inr (Or.inr (Or.inl (Or.inl hx))), ha x hx⟩
  have hmid : s.filter (fun x => a < x ∧ x < b) = B := by
    ext x
    simp only [s, Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
    constructor
    · rintro ⟨hx, hax, hxb⟩
      rcases hx with rfl | rfl | (hx | hx) | hx
      · exact False.elim hax.false
      · exact False.elim hxb.false
      · exact False.elim ((hax.trans (ha x hx)).false)
      · exact hx
      · exact False.elim (((hc x hx).trans hxb).false)
    · intro hx
      exact ⟨Or.inr (Or.inr (Or.inl (Or.inr hx))), hb x hx⟩
  have hupp : s.filter (fun x => b < x) = C := by
    ext x
    simp only [s, Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
    constructor
    · rintro ⟨hx, hbx⟩
      rcases hx with rfl | rfl | (hx | hx) | hx
      · exact False.elim ((hab.trans hbx).false)
      · exact False.elim hbx.false
      · exact False.elim ((hbx.trans ((ha x hx).trans hab)).false)
      · exact False.elim ((hbx.trans (hb x hx).2).false)
      · exact hx
    · intro hx
      exact ⟨Or.inr (Or.inr (Or.inr hx)), hc x hx⟩
  have hbelow : s.filter (fun x => x < b) = insert a (A ∪ B) := by
    ext x
    simp only [s, Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
    constructor
    · rintro ⟨hx, hxb⟩
      rcases hx with rfl | rfl | (hx | hx) | hx
      · exact Or.inl rfl
      · exact False.elim hxb.false
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hx)
      · exact False.elim (((hc x hx).trans hxb).false)
    · rintro (rfl | hx | hx)
      · exact ⟨Or.inl rfl, hab⟩
      · exact ⟨Or.inr (Or.inr (Or.inl (Or.inl hx))), (ha x hx).trans hab⟩
      · exact ⟨Or.inr (Or.inr (Or.inl (Or.inr hx))), (hb x hx).2⟩
  refine ⟨?_, hlow, hmid, hupp, ?_⟩
  · rw [Finset.card_insert_of_notMem hna, Finset.card_insert_of_notMem hnb,
      Finset.card_union_of_disjoint hdABC, Finset.card_union_of_disjoint hdAB]
  · rw [hbelow, Finset.card_insert_of_notMem (by
      intro h
      exact hna (Finset.mem_insert_of_mem (Finset.mem_union_left C h))),
      Finset.card_union_of_disjoint hdAB]

/-- A selected subset with two increasing prescribed ranks is equivalent to three
independent fixed-cardinality choices below, between, and above its anchors. -/
noncomputable def anchoredSubsetIntervalEquiv {n L : ℕ} (a b : Fin n) (hab : a < b)
    (r t : Fin L) (hrt : r < t) :
    {s : {s : Finset (Fin n) // s.card = L} //
      s.val.orderEmbOfFin s.property r = a ∧ s.val.orderEmbOfFin s.property t = b} ≃
    (↥((Finset.Iio a).powersetCard r.val) ×
      ↥((Finset.Ioo a b).powersetCard (t.val - r.val - 1)) ×
      ↥((Finset.Ioi b).powersetCard (L - 1 - t.val))) := by
  classical
  let Choices := ↥((Finset.Iio a).powersetCard r.val) ×
    ↥((Finset.Ioo a b).powersetCard (t.val - r.val - 1)) ×
    ↥((Finset.Ioi b).powersetCard (L - 1 - t.val))
  have stats (z : Choices) := interval_union_stats a b hab z.1.val z.2.1.val z.2.2.val
    (Finset.mem_powersetCard.mp z.1.property).1
    (Finset.mem_powersetCard.mp z.2.1.property).1
    (Finset.mem_powersetCard.mp z.2.2.property).1
  let assemble (z : Choices) :
      {s : {s : Finset (Fin n) // s.card = L} //
        s.val.orderEmbOfFin s.property r = a ∧ s.val.orderEmbOfFin s.property t = b} := by
    let s := insert a (insert b (z.1.val ∪ z.2.1.val ∪ z.2.2.val))
    have hA := (Finset.mem_powersetCard.mp z.1.property).2
    have hB := (Finset.mem_powersetCard.mp z.2.1.property).2
    have hC := (Finset.mem_powersetCard.mp z.2.2.property).2
    have hs : s.card = L := by
      have h := (stats z).1
      dsimp [s]
      omega
    refine ⟨⟨s, hs⟩, ?_, ?_⟩
    · apply (orderEmb_eq_iff_filter_card s hs r a).mpr
      refine ⟨Finset.mem_insert_self _ _, ?_⟩
      rw [(stats z).2.1, hA]
    · apply (orderEmb_eq_iff_filter_card s hs t b).mpr
      refine ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), ?_⟩
      have h := (stats z).2.2.2.2
      change (s.filter (fun x => x < b)).card = _ at h
      omega
  apply (Equiv.ofBijective assemble ?_).symm
  constructor
  · intro z w h
    have hv : insert a (insert b (z.1.val ∪ z.2.1.val ∪ z.2.2.val)) =
        insert a (insert b (w.1.val ∪ w.2.1.val ∪ w.2.2.val)) :=
      congrArg (fun s => s.val.val) h
    apply Prod.ext
    · apply Subtype.ext
      exact (stats z).2.1.symm.trans
        ((congrArg (fun s => s.filter (fun x => x < a)) hv).trans (stats w).2.1)
    · apply Prod.ext
      · apply Subtype.ext
        exact (stats z).2.2.1.symm.trans
          ((congrArg (fun s => s.filter (fun x => a < x ∧ x < b)) hv).trans (stats w).2.2.1)
      · apply Subtype.ext
        exact (stats z).2.2.2.1.symm.trans
          ((congrArg (fun s => s.filter (fun x => b < x)) hv).trans (stats w).2.2.2.1)
  · intro s
    let A := s.val.val.filter (fun x => x < a)
    let B := s.val.val.filter (fun x => a < x ∧ x < b)
    let C := s.val.val.filter (fun x => b < x)
    have hA : A ⊆ Finset.Iio a := by intro x hx; exact Finset.mem_Iio.mpr (Finset.mem_filter.mp hx).2
    have hB : B ⊆ Finset.Ioo a b := by intro x hx; exact Finset.mem_Ioo.mpr (Finset.mem_filter.mp hx).2
    have hC : C ⊆ Finset.Ioi b := by intro x hx; exact Finset.mem_Ioi.mpr (Finset.mem_filter.mp hx).2
    have hr := (orderEmb_eq_iff_filter_card s.val.val s.val.property r a).mp s.property.1
    have ht := (orderEmb_eq_iff_filter_card s.val.val s.val.property t b).mp s.property.2
    have hrec : insert a (insert b (A ∪ B ∪ C)) = s.val.val := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_union, A, B, C, Finset.mem_filter]
      constructor
      · rintro (rfl | rfl | (hx | hx) | hx)
        · exact hr.1
        · exact ht.1
        · exact hx.1
        · exact hx.1
        · exact hx.1
      · intro hx
        by_cases hxa : x = a
        · exact Or.inl hxa
        by_cases hxb : x = b
        · exact Or.inr (Or.inl hxb)
        by_cases hlt : x < a
        · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨hx, hlt⟩)))
        by_cases hltb : x < b
        · exact Or.inr (Or.inr (Or.inl (Or.inr ⟨hx, by omega, hltb⟩)))
        · exact Or.inr (Or.inr (Or.inr ⟨hx, by omega⟩))
    have hst := interval_union_stats a b hab A B C hA hB hC
    rw [hrec] at hst
    have hcA : A.card = r.val := hr.2
    have hcB : B.card = t.val - r.val - 1 := by
      have hh := hst.2.2.2.2
      have hh' := ht.2
      omega
    have hcC : C.card = L - 1 - t.val := by
      have hh := hst.1
      have hs := s.val.property
      omega
    refine ⟨(⟨A, Finset.mem_powersetCard.mpr ⟨hA, hcA⟩⟩,
      ⟨B, Finset.mem_powersetCard.mpr ⟨hB, hcB⟩⟩,
      ⟨C, Finset.mem_powersetCard.mpr ⟨hC, hcC⟩⟩), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hrec

example {n L : ℕ} (a b : Fin n) (hab : a < b) (r t : Fin L) (hrt : r < t)
    (z : ↥((Finset.Iio a).powersetCard r.val) ×
      ↥((Finset.Ioo a b).powersetCard (t.val - r.val - 1)) ×
      ↥((Finset.Ioi b).powersetCard (L - 1 - t.val))) :
    ((anchoredSubsetIntervalEquiv a b hab r t hrt).symm z).val.val =
      insert a (insert b (z.1.val ∪ z.2.1.val ∪ z.2.2.val)) := rfl

/-- The exact number of anchored injective lists of a prescribed increasing rank
pattern is the product of the three interval binomial coefficients. -/
theorem card_anchoredList {n L : ℕ} (i j : Fin L) (a b : Fin n)
    (σ : Equiv.Perm (Fin L)) (hab : a < b) (hσ : σ i < σ j) :
    Fintype.card {f : Fin L ↪ Fin n // rank f = σ ∧ f i = a ∧ f j = b} =
      Nat.choose a.val (σ i).val *
        Nat.choose (b.val - a.val - 1) ((σ j).val - (σ i).val - 1) *
        Nat.choose (n - 1 - b.val) (L - 1 - (σ j).val) := by
  classical
  rw [Fintype.card_congr ((anchoredListSubsetEquiv i j a b σ).trans
    (anchoredSubsetIntervalEquiv a b hab (σ i) (σ j) hσ))]
  simp only [Fintype.card_prod, Fintype.card_coe, Finset.card_powersetCard,
    Fin.card_Iio, Fin.card_Ioo, Fin.card_Ioi, Nat.mul_assoc]

/-- The full actual two-anchor standardized fiber has the three-binomial weight
multiplied by the factorial number of unselected-position completions. -/
theorem card_standardizedFiber_binomial {n L : ℕ} (e : Fin L ↪ Fin n)
    (i j : Fin L) (a b : Fin n) (σ : Equiv.Perm (Fin L))
    (hab : a < b) (hσ : σ i < σ j) :
    Fintype.card {π : FixedTwo (e i) (e j) a b // standardize e π.val = σ} =
      (Nat.choose a.val (σ i).val *
        Nat.choose (b.val - a.val - 1) ((σ j).val - (σ i).val - 1) *
        Nat.choose (n - 1 - b.val) (L - 1 - (σ j).val)) * (n - L).factorial := by
  rw [card_standardizedFiber, card_anchoredList i j a b σ hab hσ]

example : Nonempty {s : {s : Finset (Fin 2) // s.card = 2} //
    s.val.orderEmbOfFin s.property (0 : Fin 2) = 0 ∧
    s.val.orderEmbOfFin s.property (1 : Fin 2) = 1} := by
  let E := anchoredSubsetIntervalEquiv (0 : Fin 2) 1 (by decide)
    (0 : Fin 2) 1 (by decide)
  exact ⟨E.symm (⟨∅, by simp⟩, ⟨∅, by simp⟩, ⟨∅, by simp⟩)⟩

example : Fintype.card {f : Fin 2 ↪ Fin 3 //
    rank f = Equiv.refl _ ∧ f 0 = 0 ∧ f 1 = 1} = 1 := by
  simpa using card_anchoredList (0 : Fin 2) 1 (0 : Fin 3) 1 (Equiv.refl _)
    (by decide) (by decide)

end PermutationTwoAnchorKernel
