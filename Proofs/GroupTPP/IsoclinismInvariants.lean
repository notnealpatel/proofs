import Mathlib

/-!
# Isoclinism and the conjugacy-class invariants `k(G)` and `n_c(G)`

This file concerns the behaviour of the conjugacy-class count `k(G)` and the
number of **non-central** conjugacy classes

  `n_c(G) = k(G) - |Z(G)| = #{conjugacy classes that are not singletons}`

under **isoclinism** (P. Hall, 1940).

## A correction to the original task statement

The task `Pf102` asked to prove that `n_c(G) = k(G) - |Z(G)|` is an *isoclinism
invariant*. **This statement is false**, and so is the (also-claimed) invariance
of `k(G)` itself. The error is the implicit assumption that isoclinism fixes the
order `|G|`. It does not: by Hall's theorem `G` is isoclinic to `G × A` for every
abelian group `A` (Wikipedia, *Isoclinism of groups*: "`G` is isoclinic with
`G × A` if and only if `A` is abelian"). Direct product with `A` multiplies *both*
`k` and `|Z|` by `|A|`, so it multiplies `n_c` by `|A|` as well:

  `k(G × A)   = |A| · k(G)`            (`card_conjClasses_prod_comm`)
  `|Z(G × A)| = |A| · |Z(G)|`          (`card_center_prod_comm`)
  `n_c(G × A) = |A| · n_c(G)`          (`nc_prod_comm`)

Concretely (verified in GAP): `D₈`, `D₈ × C₂`, `D₈ × C₂ × C₂` are pairwise
isoclinic with `n_c = 3, 6, 12` and `k = 5, 10, 20`. The order-`32` dataset that
motivated the task hid this because it only ever compares groups of the *same*
order `32`, where `|G/Z|` invariant forces `|Z|` (hence `n_c`) constant within a
family — an artifact of the fixed order, not a genuine invariance.

## What *is* invariant

The genuine invariant in this family is the **ratio** `k(G) / |Z(G)|`
(equivalently `n_c(G)/|Z(G)| = k/|Z| - 1`). The classical reason
(P. Hall) is the identity

  `k(G) = |Z(G)| · ∑_{ḡ ∈ G/Z(G)} 1 / |{ ⁅g,h⁆ : h ∈ G }|`,

where the sum depends only on the commutator map `G/Z(G) × G/Z(G) → G'`, which is
exactly the isoclinism datum. We do not formalize the full Burnside-sum theorem
here (it has no Mathlib analogue — there is no `isoclinism` in Mathlib, and the
within-coset combinatorics is irregular). Instead we formalize, with **no
`sorry`**:

* `Isoclinic G H` — Hall's definition (compatible `G/Z ≃ H/Z` and `G' ≃ H'`).
* `commutatorElement_eq_of_quotient_eq` — Hall's Lemma A: `⁅x,y⁆` depends only on
  the cosets `xZ, yZ` (the well-definedness underlying the commutator map).
* `isoclinic_prod_abelian : Isoclinic G (G × A)` for abelian `A` — the canonical
  isoclinism, witnessed by explicit isomorphisms whose commutator-map
  compatibility is discharged via Lemma A.
* the three scaling identities above, hence
* `nc_not_isoclinism_invariant` — an explicit family of isoclinic groups on which
  `n_c` is **not** constant (refuting the task claim), and
* `ratio_isoclinism_invariant_prod` — `k(G × A) · |Z(G)| = k(G) · |Z(G × A)|`,
  i.e. `k/|Z|` *is* preserved by the canonical isoclinism operation.

## References
* P. Hall, *The classification of prime-power groups*, J. Reine Angew. Math. 182 (1940).
* Wikipedia, *Isoclinism of groups*.
* GAP verification across all 8 isoclinism families of order-`32` 2-groups and the
  `G ~ G × A` construction.
-/

open scoped Classical commutatorElement

universe u v w

namespace IsoclinismInvariants

/-! ### The commutator map and the definition of isoclinism -/

/-- The commutator map of `G` packaged as a function `G → G → commutator G`.
Each value `⁅x, y⁆` lies in `commutator G = ⁅⊤, ⊤⁆`. -/
def cmap (G : Type*) [Group G] (x y : G) : commutator G :=
  ⟨⁅x, y⁆, by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)⟩

/-- Two groups `G` and `H` are **isoclinic** (P. Hall, 1940) if there are
isomorphisms `φ : G/Z(G) ≃* H/Z(H)` and `ψ : G' ≃* H'` compatible with the
commutator maps: whenever `x', y'` are lifts of `φ⟦x⟧, φ⟦y⟧`, then
`ψ ⁅x,y⁆ = ⁅x',y'⁆`. -/
structure Isoclinic (G : Type u) (H : Type v) [Group G] [Group H] : Prop where
  exists_iso :
    ∃ (φ : G ⧸ Subgroup.center G ≃* H ⧸ Subgroup.center H)
      (ψ : commutator G ≃* commutator H),
      ∀ (x y : G) (x' y' : H),
        φ (QuotientGroup.mk x) = QuotientGroup.mk x' →
        φ (QuotientGroup.mk y) = QuotientGroup.mk y' →
        ψ (cmap G x y) = cmap H x' y'

/-! ### Hall's Lemma A: commutators depend only on cosets modulo the center -/

/-- A central `z` may be inserted into the left commutator slot without effect. -/
theorem commutatorElement_mul_center_left {G : Type*} [Group G] (x y : G)
    {z : G} (hz : z ∈ Subgroup.center G) : ⁅x * z, y⁆ = ⁅x, y⁆ := by
  have hc : ∀ g : G, g * z = z * g := fun g => (Subgroup.mem_center_iff.1 hz g)
  simp only [commutatorElement_def, mul_inv_rev]
  calc x * z * y * (z⁻¹ * x⁻¹) * y⁻¹
      = x * (z * y) * z⁻¹ * x⁻¹ * y⁻¹ := by group
    _ = x * (y * z) * z⁻¹ * x⁻¹ * y⁻¹ := by rw [← hc y]
    _ = x * y * x⁻¹ * y⁻¹ := by group

/-- A central `w` may be inserted into the right commutator slot without effect. -/
theorem commutatorElement_mul_center_right {G : Type*} [Group G] (x y : G)
    {w : G} (hw : w ∈ Subgroup.center G) : ⁅x, y * w⁆ = ⁅x, y⁆ := by
  have hc : ∀ g : G, g * w = w * g := fun g => (Subgroup.mem_center_iff.1 hw g)
  simp only [commutatorElement_def, mul_inv_rev]
  calc x * (y * w) * x⁻¹ * (w⁻¹ * y⁻¹)
      = x * y * (w * x⁻¹) * w⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * w) * w⁻¹ * y⁻¹ := by rw [← hc x⁻¹]
    _ = x * y * x⁻¹ * y⁻¹ := by group

/-- **Hall's Lemma A.** The commutator `⁅x, y⁆` depends only on the cosets
`xZ(G), yZ(G)`. This is precisely the well-definedness of the commutator map on
`G/Z(G)` that makes it an isoclinism datum. -/
theorem commutatorElement_eq_of_quotient_eq {G : Type*} [Group G] {x y x' y' : G}
    (hx : (QuotientGroup.mk x : G ⧸ Subgroup.center G) = QuotientGroup.mk x')
    (hy : (QuotientGroup.mk y : G ⧸ Subgroup.center G) = QuotientGroup.mk y') :
    ⁅x', y'⁆ = ⁅x, y⁆ := by
  rw [QuotientGroup.eq] at hx hy
  have ex : x' = x * (x⁻¹ * x') := by group
  have ey : y' = y * (y⁻¹ * y') := by group
  rw [ex, ey, commutatorElement_mul_center_left x (y * (y⁻¹ * y')) hx,
    commutatorElement_mul_center_right x y hy]

/-! ### Conjugacy classes of a product

We build `ConjClasses (G × H) ≃ ConjClasses G × ConjClasses H` from scratch
(no Mathlib lemma exists), giving `k(G × H) = k(G) · k(H)`. -/

section Prod
variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- Conjugacy in a product is componentwise. -/
theorem isConj_prod_iff (p q : G × H) :
    IsConj p q ↔ IsConj p.1 q.1 ∧ IsConj p.2 q.2 := by
  simp only [isConj_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨⟨c.1, ?_⟩, ⟨c.2, ?_⟩⟩
    · have := congrArg Prod.fst hc; simpa using this
    · have := congrArg Prod.snd hc; simpa using this
  · rintro ⟨⟨c1, hc1⟩, ⟨c2, hc2⟩⟩
    exact ⟨(c1, c2), by ext <;> simpa⟩

/-- The conjugacy classes of `G × H` are the products of conjugacy classes. -/
noncomputable def conjClassesProdEquiv :
    ConjClasses (G × H) ≃ ConjClasses G × ConjClasses H where
  toFun c := (ConjClasses.map (MonoidHom.fst G H) c, ConjClasses.map (MonoidHom.snd G H) c)
  invFun p :=
    Quotient.liftOn₂ (p.1 : ConjClasses G) (p.2 : ConjClasses H)
      (fun a b => ConjClasses.mk (a, b))
      (by
        intro a₁ b₁ a₂ b₂ ha hb
        apply ConjClasses.mk_eq_mk_iff_isConj.2
        rw [isConj_prod_iff]
        exact ⟨ha, hb⟩)
  left_inv := by
    intro c
    obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective c
    rfl
  right_inv := by
    rintro ⟨c1, c2⟩
    obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective c1
    obtain ⟨b, rfl⟩ := ConjClasses.mk_surjective c2
    rfl

/-- `k(G × H) = k(G) · k(H)`. -/
theorem card_conjClasses_prod :
    Nat.card (ConjClasses (G × H)) = Nat.card (ConjClasses G) * Nat.card (ConjClasses H) := by
  rw [Nat.card_congr conjClassesProdEquiv, Nat.card_prod]

/-- `|Z(G × H)| = |Z(G)| · |Z(H)|`. -/
theorem card_center_prod :
    Nat.card (Subgroup.center (G × H)) =
      Nat.card (Subgroup.center G) * Nat.card (Subgroup.center H) := by
  rw [← Nat.card_prod]
  apply Nat.card_congr
  refine ⟨fun z => (⟨z.1.1, ?_⟩, ⟨z.1.2, ?_⟩), fun p => ⟨(p.1.1, p.2.1), ?_⟩, ?_, ?_⟩
  · have : (z : G × H) ∈ Set.center (G × H) := z.2
    rw [Set.center_prod] at this; exact this.1
  · have : (z : G × H) ∈ Set.center (G × H) := z.2
    rw [Set.center_prod] at this; exact this.2
  · rw [Subgroup.mem_center_iff]
    intro g
    have h1 := Subgroup.mem_center_iff.1 p.1.2
    have h2 := Subgroup.mem_center_iff.1 p.2.2
    ext <;> simp [Prod.mul_def, h1, h2]
  · intro z; rfl
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩; rfl

end Prod

/-- For an abelian group `A`, conjugacy classes are singletons, so `k(A) = |A|`. -/
theorem card_conjClasses_of_comm {A : Type*} [CommGroup A] :
    Nat.card (ConjClasses A) = Nat.card A := by
  rw [Nat.card_congr ConjClasses.mkEquiv.symm]

/-- For an abelian group `A`, `|Z(A)| = |A|`. -/
theorem card_center_comm {A : Type*} [CommGroup A] :
    Nat.card (Subgroup.center A) = Nat.card A := by
  rw [Subgroup.center_eq_top, Subgroup.card_top]

/-- **Scaling of `k`.** `k(G × A) = k(G) · |A|` for abelian `A`. -/
theorem card_conjClasses_prod_comm {G : Type u} [Group G] {A : Type w} [CommGroup A] :
    Nat.card (ConjClasses (G × A)) = Nat.card (ConjClasses G) * Nat.card A := by
  rw [card_conjClasses_prod, card_conjClasses_of_comm]

/-- **Scaling of `|Z|`.** `|Z(G × A)| = |Z(G)| · |A|` for abelian `A`. -/
theorem card_center_prod_comm {G : Type u} [Group G] {A : Type w} [CommGroup A] :
    Nat.card (Subgroup.center (G × A)) = Nat.card (Subgroup.center G) * Nat.card A := by
  rw [card_center_prod, card_center_comm]

/-! ### The number of non-central conjugacy classes -/

/-- `n_c(G)`: the number of non-central conjugacy classes of `G`. This is the
Mathlib set `ConjClasses.noncenter G` of non-singleton classes. -/
noncomputable def nc (G : Type*) [Group G] : ℕ := Nat.card (ConjClasses.noncenter G)

/-- The class-equation split: `k(G) = |Z(G)| + n_c(G)`. Central elements
contribute one singleton class each (bijection `ConjClasses.mk_bijOn`); the rest
are the non-central classes. Hence `n_c(G) = k(G) - |Z(G)|` exactly. -/
theorem card_conjClasses_eq_center_add_nc {G : Type u} [Group G] [Finite G] :
    Nat.card (ConjClasses G) = Nat.card (Subgroup.center G) + nc G := by
  classical
  have hbij := ConjClasses.mk_bijOn G
  have e1 : (Subgroup.center G : Set G).ncard = ((ConjClasses.noncenter G)ᶜ).ncard :=
    hbij.ncard_eq
  have e2 : ((ConjClasses.noncenter G)ᶜ).ncard + (ConjClasses.noncenter G).ncard
      = Nat.card (ConjClasses G) := by
    rw [add_comm]
    exact Set.ncard_add_ncard_compl (ConjClasses.noncenter G) (Set.toFinite _) (Set.toFinite _)
  rw [← e2, nc]
  rw [show Nat.card (Subgroup.center G) = (Subgroup.center G : Set G).ncard from rfl, e1]
  rw [show Nat.card (ConjClasses.noncenter G) = (ConjClasses.noncenter G).ncard from rfl]

/-- `n_c(G) = k(G) - |Z(G)|`, the form stated in the task. -/
theorem nc_eq_sub {G : Type u} [Group G] [Finite G] :
    nc G = Nat.card (ConjClasses G) - Nat.card (Subgroup.center G) := by
  rw [card_conjClasses_eq_center_add_nc, Nat.add_sub_cancel_left]

/-! ### The canonical isoclinism `G ~ G × A` (`A` abelian)

We exhibit the two isomorphisms required by `Isoclinic` and verify the
commutator-map compatibility, all without `sorry`. -/

section ProdAbelian
variable (G : Type u) (A : Type w) [Group G] [CommGroup A]

/-- `(g, 1)` is central in `G × A` iff `g` is central in `G`. -/
theorem mem_center_prod_one_iff {g : G} :
    ((g, (1 : A)) ∈ Subgroup.center (G × A)) ↔ g ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h x
    have := h (x, 1)
    rw [Prod.ext_iff] at this
    exact this.1
  · intro h x
    rw [Prod.ext_iff]
    exact ⟨h x.1, by simp [mul_comm]⟩

/-- The first coordinate of a central element of `G × A` is central in `G`. -/
theorem fst_mem_center_of_mem_center {p : G × A} (hp : p ∈ Subgroup.center (G × A)) :
    p.1 ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff] at hp ⊢
  intro x
  have := hp (x, 1)
  rw [Prod.ext_iff] at this
  exact this.1

/-- `(1, a)` is always central in `G × A` (since `A` is abelian). -/
theorem one_mem_center_prod (a : A) : ((1 : G), a) ∈ Subgroup.center (G × A) := by
  rw [Subgroup.mem_center_iff]
  intro x
  rw [Prod.ext_iff]
  exact ⟨by simp, mul_comm _ _⟩

/-- The forward map `G/Z(G) → (G×A)/Z(G×A)`, `⟦g⟧ ↦ ⟦(g,1)⟧`. -/
noncomputable def quotFwd :
    G ⧸ Subgroup.center G →* (G × A) ⧸ Subgroup.center (G × A) :=
  QuotientGroup.lift (Subgroup.center G)
    ((QuotientGroup.mk' (Subgroup.center (G × A))).comp (MonoidHom.inl G A))
    (by
      intro g hg
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.inl_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact (mem_center_prod_one_iff G A).2 hg)

/-- The inverse map `(G×A)/Z(G×A) → G/Z(G)`, `⟦(g,a)⟧ ↦ ⟦g⟧`. -/
noncomputable def quotInv :
    (G × A) ⧸ Subgroup.center (G × A) →* G ⧸ Subgroup.center G :=
  QuotientGroup.lift (Subgroup.center (G × A))
    ((QuotientGroup.mk' (Subgroup.center G)).comp (MonoidHom.fst G A))
    (by
      intro p hp
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.coe_fst, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact fst_mem_center_of_mem_center G A hp)

/-- The isomorphism `φ : G/Z(G) ≃* (G×A)/Z(G×A)`. -/
noncomputable def quotIso :
    G ⧸ Subgroup.center G ≃* (G × A) ⧸ Subgroup.center (G × A) :=
  MonoidHom.toMulEquiv (quotFwd G A) (quotInv G A)
    (by ext g; rfl)
    (by
      ext p
      obtain ⟨g, a⟩ := p
      show quotFwd G A (quotInv G A (QuotientGroup.mk (g, a))) = QuotientGroup.mk (g, a)
      simp only [quotInv, quotFwd, QuotientGroup.lift_mk, MonoidHom.comp_apply,
        MonoidHom.coe_fst, MonoidHom.inl_apply, QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq]
      simp only [Prod.inv_mk, Prod.mk_mul_mk, inv_mul_cancel, one_mul, inv_one]
      exact one_mem_center_prod G A a)

/-- `commutator (G × A) = (commutator G).prod ⊥`, since `A` is abelian. -/
theorem commutator_prod_eq :
    commutator (G × A) = (commutator G).prod (⊥ : Subgroup A) := by
  haveI : IsMulCommutative A := isMulCommutative_iff.2 mul_comm
  have hA : commutator A = (⊥ : Subgroup A) := @commutator_eq_bot A _ _
  rw [commutator_def, ← Subgroup.top_prod_top, Subgroup.commutator_prod_prod,
    ← commutator_def, ← commutator_def, hA]

/-- The isomorphism `ψ : commutator G ≃* commutator (G × A)`. -/
noncomputable def commIso : commutator G ≃* commutator (G × A) :=
  (MulEquiv.prodUnique.symm.trans
    (Subgroup.prodEquiv (commutator G) (⊥ : Subgroup A)).symm).trans
    (MulEquiv.subgroupCongr (commutator_prod_eq G A).symm)

/-- **The canonical isoclinism.** `G` is isoclinic to `G × A` for any abelian `A`
(P. Hall). The commutator-map compatibility is discharged by Lemma A applied in
`G × A`, together with the fact that `⁅(x,1),(y,1)⁆ = (⁅x,y⁆, 1)`. -/
theorem isoclinic_prod_abelian : Isoclinic G (G × A) := by
  refine ⟨quotIso G A, commIso G A, ?_⟩
  intro x y x' y' hx hy
  apply Subtype.ext
  show ((commIso G A (cmap G x y)) : G × A) = ⁅x', y'⁆
  have hval : ((commIso G A (cmap G x y)) : G × A) = (⁅x, y⁆, 1) := rfl
  rw [hval]
  have hcomm : (⁅x, y⁆, (1 : A)) = ⁅((x, 1) : G × A), (y, 1)⁆ := by
    show (⁅x, y⁆, (1 : A)) = (⁅x, y⁆, ⁅(1 : A), 1⁆)
    rw [commutatorElement_self]
  rw [hcomm]
  have hx' : (QuotientGroup.mk ((x, 1) : G × A) : (G × A) ⧸ Subgroup.center (G × A))
      = QuotientGroup.mk x' := by rw [← hx]; rfl
  have hy' : (QuotientGroup.mk ((y, 1) : G × A) : (G × A) ⧸ Subgroup.center (G × A))
      = QuotientGroup.mk y' := by rw [← hy]; rfl
  exact (commutatorElement_eq_of_quotient_eq hx' hy').symm

end ProdAbelian

/-! ### Consequences: `n_c` is not invariant, but `k/|Z|` is -/

/-- **Scaling of `n_c`.** `n_c(G × A) = |A| · n_c(G)` for abelian `A`. -/
theorem nc_prod_comm {G : Type u} [Group G] [Finite G] {A : Type w} [CommGroup A] [Finite A] :
    nc (G × A) = Nat.card A * nc G := by
  have hk : Nat.card (ConjClasses (G × A)) = Nat.card A * Nat.card (ConjClasses G) := by
    rw [card_conjClasses_prod_comm, Nat.mul_comm]
  have hz : Nat.card (Subgroup.center (G × A)) = Nat.card A * Nat.card (Subgroup.center G) := by
    rw [card_center_prod_comm, Nat.mul_comm]
  have e1 := card_conjClasses_eq_center_add_nc (G := G)
  have e2 := card_conjClasses_eq_center_add_nc (G := G × A)
  rw [hk, hz, e1, Nat.mul_add] at e2
  exact (Nat.add_left_cancel e2).symm

/-- A nonabelian group has a non-central (non-singleton) conjugacy class. -/
theorem noncenter_nonempty {G : Type u} [Group G] (h : ¬ IsMulCommutative G) :
    (ConjClasses.noncenter G).Nonempty := by
  by_contra hc
  rw [Set.not_nonempty_iff_eq_empty] at hc
  apply h
  rw [isMulCommutative_iff]
  intro a b
  have hmem : ConjClasses.mk a ∉ ConjClasses.noncenter G := by rw [hc]; exact fun h => h
  rw [ConjClasses.mem_noncenter, Set.not_nontrivial_iff] at hmem
  have ha : a ∈ (ConjClasses.mk a).carrier := ConjClasses.mem_carrier_mk
  have hb : b * a * b⁻¹ ∈ (ConjClasses.mk a).carrier := by
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
    exact isConj_iff.2 ⟨b⁻¹, by group⟩
  have h2 : a = b * a * b⁻¹ := hmem ha hb
  rw [eq_comm, mul_inv_eq_iff_eq_mul] at h2
  exact h2.symm

/-- For a finite nonabelian group, `0 < n_c G`: the refutation hypothesis below is
satisfiable by every nonabelian group (e.g. `S₃`, `D₈`, any nonabelian group of
order `32`). -/
theorem nc_pos_of_not_commutative {G : Type u} [Group G] [Finite G]
    (h : ¬ IsMulCommutative G) : 0 < nc G := by
  haveI : Nonempty (ConjClasses.noncenter G) := (noncenter_nonempty h).to_subtype
  exact Finite.card_pos

/-- **`n_c` is NOT an isoclinism invariant** (refuting the task statement).
For any finite group `G` with a non-central conjugacy class (`0 < n_c G`, i.e.
`G` nonabelian — see `nc_pos_of_not_commutative`) and any nontrivial finite
abelian `A` (`1 < |A|`), the isoclinic group `G × A` satisfies
`n_c(G × A) ≠ n_c(G)`. -/
theorem nc_not_isoclinism_invariant {G : Type u} [Group G] [Finite G]
    {A : Type w} [CommGroup A] [Finite A]
    (hG : 0 < nc G) (hA : 1 < Nat.card A) :
    Isoclinic G (G × A) ∧ nc (G × A) ≠ nc G := by
  refine ⟨isoclinic_prod_abelian G A, ?_⟩
  rw [nc_prod_comm]
  -- |A| · n_c G ≠ n_c G since |A| ≥ 2 and n_c G ≥ 1
  intro h
  have : Nat.card A * nc G = 1 * nc G := by rw [one_mul]; exact h
  have := Nat.eq_of_mul_eq_mul_right hG this
  omega

/-- **The ratio `k/|Z|` IS preserved** by the canonical isoclinism operation,
stated in cross-multiplied form to avoid division:
`k(G × A) · |Z(G)| = k(G) · |Z(G × A)|`. -/
theorem ratio_isoclinism_invariant_prod {G : Type u} [Group G] {A : Type w} [CommGroup A] :
    Nat.card (ConjClasses (G × A)) * Nat.card (Subgroup.center G)
      = Nat.card (ConjClasses G) * Nat.card (Subgroup.center (G × A)) := by
  rw [card_conjClasses_prod_comm, card_center_prod_comm]
  ring

/-- **A concrete witness to the refutation.** The symmetric group `S₃ ≅ D₆`
(`DihedralGroup 3`) is isoclinic to `S₃ × C₂` (`C₂ = Multiplicative (ZMod 2)`),
yet they have different numbers of non-central conjugacy classes
(`n_c(S₃) = 2`, `n_c(S₃ × C₂) = 4`). Hence `n_c` is not an isoclinism invariant. -/
theorem nc_not_invariant_dihedral :
    Isoclinic (DihedralGroup 3) (DihedralGroup 3 × Multiplicative (ZMod 2)) ∧
      nc (DihedralGroup 3 × Multiplicative (ZMod 2)) ≠ nc (DihedralGroup 3) := by
  apply nc_not_isoclinism_invariant
  · exact nc_pos_of_not_commutative (DihedralGroup.not_commutative (by norm_num) (by norm_num))
  · rw [Nat.card_eq_fintype_card]; decide

end IsoclinismInvariants
