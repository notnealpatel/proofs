import Mathlib
import Xlib.TPP

/-!
# The character-lift API and the lift law for `β₀(C₂ × G)`

Track C of the lift-law campaign (Pf13, `Pf13-lift-law.md`). This file
provides the REUSABLE lift API:

* `Xlib.TPP.IsTPPTriple` — the instance-free collision form of the subgroup
  TPP (`s t u = 1 → s = t = u = 1`), with bridges to
  `SubgroupTripleProductProperty` and to `stppCapacity`.
* `Xlib.TPP.charLift` — the graph `{(χ h, h) : h ∈ H} ≤ A × G` of a
  character `χ : H →* A` (deliverable 1).
* `Xlib.TPP.liftTPP_iff_signKilled` — the graph triple is a subgroup-TPP
  triple of `A × G` iff the `G`-internal sign-killed condition holds
  (deliverable 2; Pf13 Theorem 1, Case A equivalence).
* `Xlib.TPP.eq_prod_top_of_sgn_mem` / `Xlib.TPP.eq_charLift_of_sgn_not_mem`
  — the Goursat trichotomy for `C₂ × G` (Pf13 Lemma G), Goursat-free.
* `Xlib.TPP.SigmaMaxLift` — `Σ_max^lift(G, 2)`, the maximum `|Σ|` over
  sign-killed configurations.
* `Xlib.TPP.stppCapacity_prod_eq_two_mul_max` — the **lift law**
  `β₀(C₂ × G) = 2 · max(β₀(G), Σ_max^lift(G, 2))` (deliverable 3; Pf13
  Theorem 1 at p = 2).
* `Xlib.TPP.two_mul_sigmaCard_le_stppCapacity` — the per-witness bound
  turning each census eligible-config + character-combo into a Lean
  witness.

`C₂` is represented as `Multiplicative (ZMod 2)`: an `abbrev`, so the
`CommGroup`/`Fintype`/`DecidableEq` instances of `ZMod 2` apply directly
and ground facts about `C₂` are `decide`-checkable; multiplicative, so
`C₂ × G` is a `Group` and the `Xlib.TPP` API applies verbatim.

## References

* Pf13, *The lift law, proved by Goursat case analysis*
  (`.tasks/f5exp/docs/Pf13-lift-law.md`).
* `goursat-grounding.md` — Goursat specialization to `C₂ × G` and the
  Mathlib infrastructure audit.
* I. Murthy, *Capacity of the triple product property*, [arXiv:2512.16730].
-/

namespace Xlib.TPP

/-! ### The subgroup-TPP collision form

For *subgroups*, the left-quotient TPP is equivalent to the collision form
`s * t * u = 1 → s = t = u = 1` (Murthy 2602.15796 Def 2.1 / Pf13 D1–D2),
since quotients of subgroup elements are again subgroup elements. The
collision form is instance-free and is the workhorse of the lift API. -/

section CollisionForm

variable {Γ : Type*} [Group Γ]

/-- The **collision form** of the subgroup TPP: `(H, K, L)` is a TPP triple
iff the only solution of `s * t * u = 1` with `s ∈ H`, `t ∈ K`, `u ∈ L` is
`s = t = u = 1`. Equivalent to `SubgroupTripleProductProperty`
(`subgroupTripleProductProperty_iff_isTPPTriple`) but requires no
decidability or finiteness instances. -/
def IsTPPTriple (H K L : Subgroup Γ) : Prop :=
  ∀ s ∈ H, ∀ t ∈ K, ∀ u ∈ L, s * t * u = 1 → s = 1 ∧ t = 1 ∧ u = 1

instance {H K L : Subgroup Γ} [Fintype Γ] [DecidableEq Γ]
    [DecidablePred (· ∈ H)] [DecidablePred (· ∈ K)] [DecidablePred (· ∈ L)] :
    Decidable (IsTPPTriple H K L) := by
  unfold IsTPPTriple; infer_instance

/-- Cyclic invariance of the collision form: `s t u = 1 ↔ t u s = 1`
(Pf13 D3, cyclic generator). -/
theorem IsTPPTriple.rotate {H K L : Subgroup Γ} (h : IsTPPTriple H K L) :
    IsTPPTriple K L H := by
  intro s hs t ht u hu hstu
  have hst : s * t = u⁻¹ := mul_eq_one_iff_eq_inv.mp hstu
  have h1 : u * s * t = 1 := by rw [mul_assoc, hst, mul_inv_cancel]
  obtain ⟨hu1, hs1, ht1⟩ := h u hu s hs t ht h1
  exact ⟨hs1, ht1, hu1⟩

/-- A collision-form TPP triple satisfies the left-quotient
`TripleProductProperty` on carrier finsets — for *any* `Fintype` instances
on the carriers (instance-parametric on purpose: `stppCapacity` fixes its
own classical instances). -/
theorem IsTPPTriple.tripleProductProperty_toFinset {H K L : Subgroup Γ}
    [Fintype (H : Set Γ)] [Fintype (K : Set Γ)] [Fintype (L : Set Γ)]
    (h : IsTPPTriple H K L) :
    TripleProductProperty (H : Set Γ).toFinset (K : Set Γ).toFinset
      (L : Set Γ).toFinset := by
  intro s hs s' hs' t ht t' ht' u hu u' hu' heq
  rw [Set.mem_toFinset, SetLike.mem_coe] at hs hs' ht ht' hu hu'
  have hq : (s'⁻¹ * s) * (t'⁻¹ * t) * (u'⁻¹ * u) = 1 := by
    rw [← heq]; group
  obtain ⟨h1, h2, h3⟩ := h _ (H.mul_mem (H.inv_mem hs') hs)
    _ (K.mul_mem (K.inv_mem ht') ht) _ (L.mul_mem (L.inv_mem hu') hu) hq
  exact ⟨(inv_mul_eq_one.mp h1).symm, (inv_mul_eq_one.mp h2).symm,
    (inv_mul_eq_one.mp h3).symm⟩

/-- Converse of `IsTPPTriple.tripleProductProperty_toFinset`. -/
theorem IsTPPTriple.of_tripleProductProperty_toFinset {H K L : Subgroup Γ}
    [Fintype (H : Set Γ)] [Fintype (K : Set Γ)] [Fintype (L : Set Γ)]
    (h : TripleProductProperty (H : Set Γ).toFinset (K : Set Γ).toFinset
      (L : Set Γ).toFinset) :
    IsTPPTriple H K L := by
  intro s hs t ht u hu hstu
  have hmem : ∀ {M : Subgroup Γ} [Fintype (M : Set Γ)] {x : Γ}, x ∈ M →
      x ∈ (M : Set Γ).toFinset := fun hx => Set.mem_toFinset.mpr hx
  have key : (1 : Γ)⁻¹ * s * 1⁻¹ * t * 1⁻¹ * u = 1 := by simpa using hstu
  exact h s (hmem hs) 1 (hmem H.one_mem) t (hmem ht) 1 (hmem K.one_mem)
    u (hmem hu) 1 (hmem L.one_mem) key

/-- The subgroup TPP of `Xlib.TPP` is exactly the collision form. -/
theorem subgroupTripleProductProperty_iff_isTPPTriple
    [Fintype Γ] [DecidableEq Γ] {H K L : Subgroup Γ}
    [DecidablePred (· ∈ H)] [DecidablePred (· ∈ K)] [DecidablePred (· ∈ L)] :
    SubgroupTripleProductProperty H K L ↔ IsTPPTriple H K L :=
  ⟨fun h => IsTPPTriple.of_tripleProductProperty_toFinset h,
   fun h => h.tripleProductProperty_toFinset⟩

/-- A collision-form TPP triple lower-bounds the subgroup capacity `β₀`. -/
theorem IsTPPTriple.le_stppCapacity [Fintype Γ] [DecidableEq Γ]
    {H K L : Subgroup Γ} (h : IsTPPTriple H K L) :
    Nat.card H * Nat.card K * Nat.card L ≤ stppCapacity Γ := by
  classical
  unfold stppCapacity
  refine le_trans ?_ (Finset.le_sup (Finset.mem_univ (H, K, L)))
  simp only
  split_ifs with hc
  · exact le_refl _
  · exact (hc h.tripleProductProperty_toFinset).elim

/-- `β₀` bounded above by a uniform bound on collision-form TPP triples. -/
theorem stppCapacity_le_of_forall [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (h : ∀ H K L : Subgroup Γ, IsTPPTriple H K L →
      Nat.card H * Nat.card K * Nat.card L ≤ N) :
    stppCapacity Γ ≤ N := by
  classical
  unfold stppCapacity
  refine Finset.sup_le ?_
  rintro ⟨H, K, L⟩ -
  simp only
  split_ifs with hc
  · exact h H K L (.of_tripleProductProperty_toFinset hc)
  · exact Nat.zero_le _

/-- `β₀` is achieved by a collision-form TPP triple. -/
theorem exists_isTPPTriple_card_eq_stppCapacity
    (Γ : Type*) [Group Γ] [Fintype Γ] [DecidableEq Γ] :
    ∃ H K L : Subgroup Γ, IsTPPTriple H K L ∧
      stppCapacity Γ = Nat.card H * Nat.card K * Nat.card L := by
  classical
  have hbot : IsTPPTriple (⊥ : Subgroup Γ) ⊥ ⊥ := by
    intro s hs t ht u hu _
    rw [Subgroup.mem_bot] at hs ht hu
    exact ⟨hs, ht, hu⟩
  obtain ⟨⟨H, K, L⟩, -, hsup⟩ :=
    Finset.exists_mem_eq_sup
      (Finset.univ : Finset (Subgroup Γ × Subgroup Γ × Subgroup Γ))
      ⟨(⊥, ⊥, ⊥), Finset.mem_univ _⟩
      (fun p =>
        if TripleProductProperty (p.1 : Set Γ).toFinset (p.2.1 : Set Γ).toFinset
            (p.2.2 : Set Γ).toFinset
        then Nat.card p.1 * Nat.card p.2.1 * Nat.card p.2.2
        else 0)
  have hcap : stppCapacity Γ =
      if TripleProductProperty (H : Set Γ).toFinset (K : Set Γ).toFinset
          (L : Set Γ).toFinset
      then Nat.card H * Nat.card K * Nat.card L
      else 0 := hsup
  by_cases hc : TripleProductProperty (H : Set Γ).toFinset (K : Set Γ).toFinset
      (L : Set Γ).toFinset
  · rw [if_pos hc] at hcap
    exact ⟨H, K, L, .of_tripleProductProperty_toFinset hc, hcap⟩
  · exfalso
    rw [if_neg hc] at hcap
    have h1 := hbot.le_stppCapacity (Γ := Γ)
    rw [hcap] at h1
    simp at h1

end CollisionForm

/-! ### The character lift `charLift`

For `H ≤ G` and a character `χ : H →* A`, the **graph**
`{(χ h, h) : h ∈ H} ≤ A × G`. This is the type-(ii) constructor of the
Goursat trichotomy for `C₂ × G` (goursat-grounding.md); with `χ = 1` it
degenerates to `1 × H` (type (i)). The sign group is kept abstract here —
the lift-law counting below instantiates `A := C₂`. -/

section CharLift

variable {G : Type*} [Group G] {A : Type*} [Group A]

/-- The **character lift**: the graph `{(χ h, h) : h ∈ H}` of a character
`χ : H →* A`, as a subgroup of `A × G` (sign coordinate first). -/
def charLift {H : Subgroup G} (χ : H →* A) : Subgroup (A × G) :=
  (χ.prod H.subtype).range

theorem mem_charLift {H : Subgroup G} {χ : H →* A} {p : A × G} :
    p ∈ charLift χ ↔ ∃ h : H, ((χ h : A), (h : G)) = p := by
  simp only [charLift, MonoidHom.mem_range, MonoidHom.prod_apply,
    Subgroup.coe_subtype]

theorem charLift_mem {H : Subgroup G} (χ : H →* A) (h : H) :
    ((χ h : A), (h : G)) ∈ charLift χ :=
  mem_charLift.mpr ⟨h, rfl⟩

/-- The graph has the order of its base subgroup: the projection to `G` is
injective on the graph. -/
theorem card_charLift {H : Subgroup G} (χ : H →* A) :
    Nat.card (charLift χ) = Nat.card H := by
  have hinj : Function.Injective (χ.prod H.subtype) := by
    intro a b hab
    have h2 := congrArg Prod.snd hab
    simp only [MonoidHom.prod_apply, Subgroup.coe_subtype] at h2
    exact Subtype.ext h2
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

/-- The **sign-killed condition** (Pf13 D5(b), the exact lemma-(ii)
semantics): every nontrivial collision `s * t * u = 1` in `G` has
`χS s * χT t * χU u ≠ 1`. Over `A = C₂` this reads: every nontrivial
collision is `ψ`-odd. No twist-count, covering, intersection, or
blockedness condition is imposed. -/
def SignKilled {HS HT HU : Subgroup G}
    (χS : HS →* A) (χT : HT →* A) (χU : HU →* A) : Prop :=
  ∀ (s : HS) (t : HT) (u : HU), (s : G) * t * u = 1 →
    ¬(s = 1 ∧ t = 1 ∧ u = 1) → χS s * χT t * χU u ≠ 1

instance {HS HT HU : Subgroup G} (χS : HS →* A) (χT : HT →* A) (χU : HU →* A)
    [Fintype HS] [Fintype HT] [Fintype HU] [DecidableEq G] [DecidableEq A] :
    Decidable (SignKilled χS χT χU) := by
  unfold SignKilled; infer_instance

/-- **The lift correspondence, collision form** (Pf13 Theorem 1, Case A
equivalence `(*)`): the graph triple is a TPP triple of `A × G` iff the
sign-killed condition holds in `G`. Both directions are the same two-line
product computation `(χS s, s)(χT t, t)(χU u, u) = (χS s · χT t · χU u, stu)`. -/
theorem isTPPTriple_charLift_iff {HS HT HU : Subgroup G}
    (χS : HS →* A) (χT : HT →* A) (χU : HU →* A) :
    IsTPPTriple (charLift χS) (charLift χT) (charLift χU) ↔
      SignKilled χS χT χU := by
  constructor
  · intro h s t u hcol hne hψ
    have hprod : ((χS s : A), (s : G)) * ((χT t : A), (t : G)) *
        ((χU u : A), (u : G)) = 1 := by
      simp only [Prod.mk_mul_mk, Prod.mk_eq_one]
      exact ⟨hψ, hcol⟩
    obtain ⟨h1, h2, h3⟩ := h _ (charLift_mem χS s) _ (charLift_mem χT t)
      _ (charLift_mem χU u) hprod
    rw [Prod.mk_eq_one] at h1 h2 h3
    exact hne ⟨OneMemClass.coe_eq_one.mp h1.2, OneMemClass.coe_eq_one.mp h2.2,
      OneMemClass.coe_eq_one.mp h3.2⟩
  · intro hSK x hx y hy z hz hxyz
    obtain ⟨a, rfl⟩ := mem_charLift.mp hx
    obtain ⟨b, rfl⟩ := mem_charLift.mp hy
    obtain ⟨c, rfl⟩ := mem_charLift.mp hz
    rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.mk_eq_one] at hxyz
    obtain ⟨hψ, hcol⟩ := hxyz
    by_cases habc : a = 1 ∧ b = 1 ∧ c = 1
    · obtain ⟨rfl, rfl, rfl⟩ := habc
      simp [Prod.mk_eq_one]
    · exact absurd hψ (hSK a b c hcol habc)

/-- **`liftTPP_iff_signKilled`** (deliverable 2 of the lift API): the graph
triple `(charLift χS, charLift χT, charLift χU)` is a subgroup-TPP triple of
`A × G` iff the `G`-internal sign-killed condition holds. -/
theorem liftTPP_iff_signKilled [Fintype G] [DecidableEq G]
    [Fintype A] [DecidableEq A] {HS HT HU : Subgroup G}
    (χS : HS →* A) (χT : HT →* A) (χU : HU →* A)
    [DecidablePred (· ∈ charLift χS)] [DecidablePred (· ∈ charLift χT)]
    [DecidablePred (· ∈ charLift χU)] :
    SubgroupTripleProductProperty (charLift χS) (charLift χT) (charLift χU) ↔
      SignKilled χS χT χU :=
  subgroupTripleProductProperty_iff_isTPPTriple.trans
    (isTPPTriple_charLift_iff χS χT χU)

end CharLift

/-! ### The sign homomorphism `ψ` and `|Σ|` -/

section SignSum

variable {G : Type*} [Group G] {A : Type*} [CommGroup A]

/-- The **sign homomorphism** `ψ : HS × HT × HU →* A`,
`ψ(s, t, u) = χS s · χT t · χU u` (Pf13 D4). -/
def signSum {HS HT HU : Subgroup G}
    (χS : HS →* A) (χT : HT →* A) (χU : HU →* A) : (HS × HT × HU) →* A :=
  χS.comp (MonoidHom.fst HS (HT × HU)) *
    (χT.comp (MonoidHom.fst HT HU)).comp (MonoidHom.snd HS (HT × HU)) *
    (χU.comp (MonoidHom.snd HT HU)).comp (MonoidHom.snd HS (HT × HU))

@[simp] theorem signSum_apply {HS HT HU : Subgroup G}
    (χS : HS →* A) (χT : HT →* A) (χU : HU →* A) (p : HS × HT × HU) :
    signSum χS χT χU p = χS p.1 * χT p.2.1 * χU p.2.2 := rfl

/-- `|Σ|` of a configuration (Pf13 D4): the number of `ψ`-even element
triples, `Σ = ψ⁻¹(1) ≤ HS × HT × HU`. -/
noncomputable def sigmaCard {HS HT HU : Subgroup G}
    (χS : HS →* A) (χT : HT →* A) (χU : HU →* A) : ℕ :=
  Nat.card (signSum χS χT χU).ker

end SignSum

/-! ### The lift law for `C₂ × G` -/

section LiftLaw

/-- The two-element sign group `C₂ = Multiplicative (ZMod 2)`. -/
abbrev C₂ : Type := Multiplicative (ZMod 2)

/-- The nontrivial sign `σ ∈ C₂`. -/
abbrev sgn : C₂ := Multiplicative.ofAdd 1

private theorem sgn_mul_self : sgn * sgn = 1 := by decide

private theorem sgn_ne_one : sgn ≠ 1 := by decide

private theorem C₂_eq_or_eq_sgn_mul : ∀ c c' : C₂, c = c' ∨ c = sgn * c' := by
  decide

private theorem C₂_inv_mul_of_ne : ∀ c c' : C₂, c ≠ c' → c⁻¹ * c' = sgn := by
  decide

private theorem C₂_eq_of_ne_one : ∀ c c' : C₂, c ≠ 1 → c' ≠ 1 → c = c' := by
  decide

private theorem card_C₂ : Nat.card C₂ = 2 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

variable {G : Type*} [Group G]

/-- `Nat.card` of a product of subgroups (via `Subgroup.prodEquiv`). -/
private theorem card_subgroup_prod {Γ₁ Γ₂ : Type*} [Group Γ₁] [Group Γ₂]
    (A : Subgroup Γ₁) (B : Subgroup Γ₂) :
    Nat.card (A.prod B) = Nat.card A * Nat.card B := by
  rw [Nat.card_congr (Subgroup.prodEquiv A B).toEquiv, Nat.card_prod]

/-- First-isomorphism count: `|ker f| · |range f| = |Γ|`. -/
private theorem card_ker_mul_card_range {Γ₁ A : Type*} [Group Γ₁] [Group A]
    (f : Γ₁ →* A) :
    Nat.card f.ker * Nat.card f.range = Nat.card Γ₁ := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, mul_comm]

private theorem card_triple {HS HT HU : Subgroup G} :
    Nat.card (HS × HT × HU) = Nat.card HS * Nat.card HT * Nat.card HU := by
  rw [Nat.card_prod, Nat.card_prod, mul_assoc]

/-- Goursat trichotomy for `C₂ × G`, full case (Pf13 Lemma G(iii)): a
subgroup containing the central sign `(σ, 1)` is a full product `C₂ × W`. -/
theorem eq_prod_top_of_sgn_mem {P : Subgroup (C₂ × G)}
    (hz : ((sgn, (1 : G)) : C₂ × G) ∈ P) :
    ∃ W : Subgroup G, P = (⊤ : Subgroup C₂).prod W := by
  refine ⟨P.map (MonoidHom.snd C₂ G), ?_⟩
  ext ⟨c, g⟩
  rw [Subgroup.mem_prod]
  simp only [Subgroup.mem_top, true_and]
  constructor
  · intro h
    exact Subgroup.mem_map.mpr ⟨(c, g), h, rfl⟩
  · intro hg
    obtain ⟨⟨c', g'⟩, hmem, hg2⟩ := Subgroup.mem_map.mp hg
    have hgg : g' = g := hg2
    subst hgg
    rcases C₂_eq_or_eq_sgn_mul c c' with rfl | hcc
    · exact hmem
    · rw [hcc]
      have hmul := P.mul_mem hz hmem
      simpa [Prod.mk_mul_mk] using hmul

/-- Goursat trichotomy for `C₂ × G`, graph case (Pf13 Lemma G(i)–(ii)): a
subgroup avoiding the central sign `(σ, 1)` is the graph of a unique
character on its projection. Full Goursat is not needed: each base element
has a unique sign lift, and uniqueness makes the lift a homomorphism. -/
theorem eq_charLift_of_sgn_not_mem {P : Subgroup (C₂ × G)}
    (hz : ((sgn, (1 : G)) : C₂ × G) ∉ P) :
    ∃ (H : Subgroup G) (χ : H →* C₂), P = charLift χ := by
  have huniq : ∀ (c₁ c₂ : C₂) (g : G), (c₁, g) ∈ P → (c₂, g) ∈ P → c₁ = c₂ := by
    intro c₁ c₂ g h₁ h₂
    by_contra hne
    have hd : ((c₁, g) : C₂ × G)⁻¹ * (c₂, g) ∈ P := P.mul_mem (P.inv_mem h₁) h₂
    have he : ((c₁⁻¹ * c₂, g⁻¹ * g) : C₂ × G) ∈ P := by
      simpa [Prod.inv_mk, Prod.mk_mul_mk] using hd
    rw [inv_mul_cancel, C₂_inv_mul_of_ne c₁ c₂ hne] at he
    exact hz he
  have hex : ∀ h : P.map (MonoidHom.snd C₂ G), ∃ c : C₂,
      ((c, (h : G)) : C₂ × G) ∈ P := by
    intro h
    obtain ⟨⟨c, g⟩, hmem, hg2⟩ := Subgroup.mem_map.mp h.2
    have hgg : g = (h : G) := hg2
    exact ⟨c, by rwa [hgg] at hmem⟩
  choose f hf using hex
  have hmul : ∀ a b : P.map (MonoidHom.snd C₂ G), f (a * b) = f a * f b := by
    intro a b
    refine huniq _ _ _ (hf (a * b)) ?_
    have hm := P.mul_mem (hf a) (hf b)
    rw [Prod.mk_mul_mk] at hm
    rwa [Subgroup.coe_mul]
  refine ⟨P.map (MonoidHom.snd C₂ G), MonoidHom.mk' f hmul, ?_⟩
  ext ⟨c, g⟩
  rw [mem_charLift]
  constructor
  · intro hcg
    have hgH : g ∈ P.map (MonoidHom.snd C₂ G) :=
      Subgroup.mem_map.mpr ⟨(c, g), hcg, rfl⟩
    exact ⟨⟨g, hgH⟩, by rw [MonoidHom.mk'_apply, huniq _ _ g (hf ⟨g, hgH⟩) hcg]⟩
  · rintro ⟨h, heq⟩
    rw [← heq]
    exact hf h

/-- **`SigmaMaxLift`** (Pf13 D6, `Σ_max^lift(G, 2)`): the maximum `|Σ|` over
sign-killed configurations in `G`.

Deviation from Pf13 D5 recorded: no `k ≥ 1` twist-count condition is
imposed. The all-trivial-character configurations admitted here are exactly
the TPP triples of `G` (with `|Σ| = |HS||HT||HU| ≤ β₀(G)`), so the value of
`max (stppCapacity G) (SigmaMaxLift G)` is unchanged — this is the k = 0
subcase absorption of Pf13 Theorem 1, Case A. -/
noncomputable def SigmaMaxLift (G : Type*) [Group G] : ℕ :=
  sSup { n | ∃ (HS HT HU : Subgroup G) (χS : HS →* C₂) (χT : HT →* C₂)
    (χU : HU →* C₂), SignKilled χS χT χU ∧ n = sigmaCard χS χT χU }

variable [Fintype G]

private theorem bddAbove_sigmaSet :
    BddAbove { n | ∃ (HS HT HU : Subgroup G) (χS : HS →* C₂) (χT : HT →* C₂)
      (χU : HU →* C₂), SignKilled χS χT χU ∧ n = sigmaCard χS χT χU } := by
  refine ⟨Nat.card G ^ 3, ?_⟩
  rintro n ⟨HS, HT, HU, χS, χT, χU, -, rfl⟩
  calc sigmaCard χS χT χU ≤ Nat.card (HS × HT × HU) :=
        Subgroup.card_le_card_group _
    _ = Nat.card HS * Nat.card HT * Nat.card HU := card_triple
    _ ≤ Nat.card G * Nat.card G * Nat.card G := by
        gcongr <;> exact Subgroup.card_le_card_group _
    _ = Nat.card G ^ 3 := by ring

/-- A sign-killed configuration witnesses `SigmaMaxLift`. -/
theorem sigmaCard_le_sigmaMaxLift {HS HT HU : Subgroup G}
    {χS : HS →* C₂} {χT : HT →* C₂} {χU : HU →* C₂}
    (h : SignKilled χS χT χU) :
    sigmaCard χS χT χU ≤ SigmaMaxLift G :=
  le_csSup bddAbove_sigmaSet ⟨HS, HT, HU, χS, χT, χU, h, rfl⟩

/-- `SigmaMaxLift` is achieved by a sign-killed configuration. -/
private theorem exists_sigmaMaxLift_witness :
    ∃ (HS HT HU : Subgroup G) (χS : HS →* C₂) (χT : HT →* C₂) (χU : HU →* C₂),
      SignKilled χS χT χU ∧ SigmaMaxLift G = sigmaCard χS χT χU := by
  have hbotSK : SignKilled (1 : (⊥ : Subgroup G) →* C₂)
      (1 : (⊥ : Subgroup G) →* C₂) (1 : (⊥ : Subgroup G) →* C₂) := by
    intro s t u _ hne
    exact absurd ⟨Subtype.ext (Subgroup.mem_bot.mp s.2),
      Subtype.ext (Subgroup.mem_bot.mp t.2),
      Subtype.ext (Subgroup.mem_bot.mp u.2)⟩ hne
  have hne : { n | ∃ (HS HT HU : Subgroup G) (χS : HS →* C₂) (χT : HT →* C₂)
      (χU : HU →* C₂), SignKilled χS χT χU ∧ n = sigmaCard χS χT χU }.Nonempty :=
    ⟨_, ⟨⊥, ⊥, ⊥, (1 : (⊥ : Subgroup G) →* C₂), (1 : (⊥ : Subgroup G) →* C₂),
      (1 : (⊥ : Subgroup G) →* C₂), hbotSK, rfl⟩⟩
  exact Nat.sSup_mem hne bddAbove_sigmaSet

end LiftLaw

end Xlib.TPP
