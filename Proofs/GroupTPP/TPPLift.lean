import Mathlib
import GroupTPP.TPP

/-!
# The character-lift API and the lift law for `β₀(C₂ × G)`

Track C of the lift-law campaign (Pf13, `Pf13-lift-law.md`). This file
provides the REUSABLE lift API:

* `GroupTPP.TPP.IsTPPTriple` — the instance-free collision form of the subgroup
  TPP (`s t u = 1 → s = t = u = 1`), with bridges to
  `SubgroupTripleProductProperty` and to `stppCapacity`.
* `GroupTPP.TPP.charLift` — the graph `{(χ h, h) : h ∈ H} ≤ A × G` of a
  character `χ : H →* A` (deliverable 1).
* `GroupTPP.TPP.liftTPP_iff_signKilled` — the graph triple is a subgroup-TPP
  triple of `A × G` iff the `G`-internal sign-killed condition holds
  (deliverable 2; Pf13 Theorem 1, Case A equivalence).
* `GroupTPP.TPP.eq_prod_top_of_sgn_mem` / `GroupTPP.TPP.eq_charLift_of_sgn_not_mem`
  — the Goursat trichotomy for `C₂ × G` (Pf13 Lemma G), Goursat-free.
* `GroupTPP.TPP.SigmaMaxLift` — `Σ_max^lift(G, 2)`, the maximum `|Σ|` over
  sign-killed configurations.
* `GroupTPP.TPP.stppCapacity_prod_eq_two_mul_max` — the **lift law**
  `β₀(C₂ × G) = 2 · max(β₀(G), Σ_max^lift(G, 2))` (deliverable 3; Pf13
  Theorem 1 at p = 2).
* `GroupTPP.TPP.two_mul_sigmaCard_le_stppCapacity` — the per-witness bound
  turning each census eligible-config + character-combo into a Lean
  witness.

`C₂` is represented as `Multiplicative (ZMod 2)`: an `abbrev`, so the
`CommGroup`/`Fintype`/`DecidableEq` instances of `ZMod 2` apply directly
and ground facts about `C₂` are `decide`-checkable; multiplicative, so
`C₂ × G` is a `Group` and the `GroupTPP.TPP` API applies verbatim.

## References

* Pf13, *The lift law, proved by Goursat case analysis*
  (`.tasks/f5exp/docs/Pf13-lift-law.md`).
* `goursat-grounding.md` — Goursat specialization to `C₂ × G` and the
  Mathlib infrastructure audit.
* I. Murthy, *Capacity of the triple product property*, [arXiv:2512.16730].
-/

namespace GroupTPP.TPP

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

/-- The subgroup TPP of `GroupTPP.TPP` is exactly the collision form. -/
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

/-- Case-A upper count (Pf13 Theorem 1, Case A): `|Π| ≤ 2 |Σ|`, since `Σ` is
the kernel of `ψ : Π →* C₂` and the image has order at most `2`. -/
private theorem card_triple_le_two_mul_sigmaCard {HS HT HU : Subgroup G}
    (χS : HS →* C₂) (χT : HT →* C₂) (χU : HU →* C₂) :
    Nat.card (HS × HT × HU) ≤ 2 * sigmaCard χS χT χU := by
  have h1 := card_ker_mul_card_range (signSum χS χT χU)
  have h2 : Nat.card (signSum χS χT χU).range ≤ 2 := by
    have h3 := Subgroup.card_le_card_group (signSum χS χT χU).range
    rwa [card_C₂] at h3
  calc Nat.card (HS × HT × HU)
      = Nat.card (signSum χS χT χU).ker * Nat.card (signSum χS χT χU).range :=
        h1.symm
    _ ≤ Nat.card (signSum χS χT χU).ker * 2 := Nat.mul_le_mul le_rfl h2
    _ = 2 * sigmaCard χS χT χU := by rw [mul_comm]; rfl

/-- Twisted exact count (Pf13 Theorem 1, Case A, `k ≥ 1` subcase):
if `ψ ≠ 1` then `ψ` is onto `C₂` and `|Π| = 2 |Σ|`. -/
private theorem card_triple_eq_two_mul_sigmaCard_of_ne_one
    {HS HT HU : Subgroup G} {χS : HS →* C₂} {χT : HT →* C₂} {χU : HU →* C₂}
    (hψ : signSum χS χT χU ≠ 1) :
    Nat.card (HS × HT × HU) = 2 * sigmaCard χS χT χU := by
  have hrange : (signSum χS χT χU).range = ⊤ := by
    obtain ⟨p, hp⟩ := DFunLike.ne_iff.mp hψ
    have hp' : signSum χS χT χU p ≠ 1 := by simpa using hp
    rw [Subgroup.eq_top_iff']
    intro c
    by_cases hc : c = 1
    · exact hc ▸ Subgroup.one_mem _
    · have heq : signSum χS χT χU p = c := C₂_eq_of_ne_one _ c hp' hc
      exact heq ▸ MonoidHom.mem_range.mpr ⟨p, rfl⟩
  have h1 := card_ker_mul_card_range (signSum χS χT χU)
  rw [hrange, Subgroup.card_top, card_C₂] at h1
  rw [← h1, mul_comm]
  rfl

/-- Untwisted count (Pf13 Theorem 1, Case A, `k = 0` subcase): if `ψ = 1`
then `Σ` is all of `Π`. -/
private theorem sigmaCard_eq_of_signSum_eq_one {HS HT HU : Subgroup G}
    {χS : HS →* C₂} {χT : HT →* C₂} {χU : HU →* C₂}
    (hψ : signSum χS χT χU = 1) :
    sigmaCard χS χT χU = Nat.card (HS × HT × HU) := by
  unfold sigmaCard
  rw [MonoidHom.ker_eq_top_iff.mpr hψ, Subgroup.card_top]

/-- Untwisted sign-killed configurations are honest TPP triples of `G`
(Pf13 Theorem 1, Case A, `k = 0`): with `ψ = 1` the sign-killed condition
says there are no nontrivial collisions at all. -/
private theorem isTPPTriple_of_signKilled_of_eq_one {HS HT HU : Subgroup G}
    {χS : HS →* C₂} {χT : HT →* C₂} {χU : HU →* C₂}
    (hSK : SignKilled χS χT χU) (hψ : signSum χS χT χU = 1) :
    IsTPPTriple HS HT HU := by
  intro s hs t ht u hu hstu
  by_contra hne
  have hone : χS ⟨s, hs⟩ * χT ⟨t, ht⟩ * χU ⟨u, hu⟩ = 1 := by
    have hcong := DFunLike.congr_fun hψ (⟨s, hs⟩, ⟨t, ht⟩, ⟨u, hu⟩)
    simpa using hcong
  refine hSK ⟨s, hs⟩ ⟨t, ht⟩ ⟨u, hu⟩ hstu (fun hcon => hne ?_) hone
  exact ⟨OneMemClass.coe_eq_one.mpr hcon.1, OneMemClass.coe_eq_one.mpr hcon.2.1,
    OneMemClass.coe_eq_one.mpr hcon.2.2⟩

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

variable [DecidableEq G]

/-- Case-B lift (Pf13 Theorem 1, Case B): an honest TPP triple of `G` lifts
to `(1 × H, 1 × K, C₂ × L)`, doubling the size. -/
theorem two_mul_le_stppCapacity_of_isTPPTriple {H K L : Subgroup G}
    (h : IsTPPTriple H K L) :
    2 * (Nat.card H * Nat.card K * Nat.card L) ≤ stppCapacity (C₂ × G) := by
  have hlift : IsTPPTriple ((⊥ : Subgroup C₂).prod H) ((⊥ : Subgroup C₂).prod K)
      ((⊤ : Subgroup C₂).prod L) := by
    rintro ⟨cs, s⟩ hs ⟨ct, t⟩ ht ⟨cu, u⟩ hu hprod
    rw [Subgroup.mem_prod] at hs ht hu
    rw [Subgroup.mem_bot] at hs ht
    obtain ⟨rfl, hs⟩ := hs
    obtain ⟨rfl, ht⟩ := ht
    obtain ⟨-, hu⟩ := hu
    rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.mk_eq_one] at hprod
    obtain ⟨hc, hg⟩ := hprod
    obtain ⟨hs1, ht1, hu1⟩ := h s hs t ht u hu hg
    refine ⟨?_, ?_, ?_⟩ <;> rw [Prod.mk_eq_one]
    · exact ⟨rfl, hs1⟩
    · exact ⟨rfl, ht1⟩
    · exact ⟨by simpa using hc, hu1⟩
  have hle := hlift.le_stppCapacity
  simp only [card_subgroup_prod, Subgroup.card_bot, Subgroup.card_top, card_C₂,
    one_mul] at hle
  calc 2 * (Nat.card H * Nat.card K * Nat.card L)
      = Nat.card H * Nat.card K * (2 * Nat.card L) := by ring
    _ ≤ stppCapacity (C₂ × G) := hle

/-- **Per-witness capacity bound** (Pf13 8.1, "eligibility implies
realizability"): a sign-killed configuration gives `2 |Σ| ≤ β₀(C₂ × G)`.
This is the seam consumed by census certificates: `SignKilled` is decidable
on concrete data, and this bound turns each census eligible-config +
character-combo into a Lean witness. -/
theorem two_mul_sigmaCard_le_stppCapacity {HS HT HU : Subgroup G}
    {χS : HS →* C₂} {χT : HT →* C₂} {χU : HU →* C₂}
    (h : SignKilled χS χT χU) :
    2 * sigmaCard χS χT χU ≤ stppCapacity (C₂ × G) := by
  by_cases hψ : signSum χS χT χU = 1
  · rw [sigmaCard_eq_of_signSum_eq_one hψ, card_triple]
    exact two_mul_le_stppCapacity_of_isTPPTriple
      (isTPPTriple_of_signKilled_of_eq_one h hψ)
  · rw [← card_triple_eq_two_mul_sigmaCard_of_ne_one hψ, card_triple]
    have hTPP := (isTPPTriple_charLift_iff χS χT χU).mpr h
    have hle := hTPP.le_stppCapacity
    rwa [card_charLift, card_charLift, card_charLift] at hle

/-- Case-B bound: a TPP triple of `C₂ × G` whose first two members avoid the
central sign and whose third contains it has size at most `2 β₀(G)`
(Pf13 Theorem 1, Case B). -/
private theorem caseB_core {P Q R : Subgroup (C₂ × G)} (h : IsTPPTriple P Q R)
    (hP : ((sgn, (1 : G)) : C₂ × G) ∉ P) (hQ : ((sgn, (1 : G)) : C₂ × G) ∉ Q)
    (hR : ((sgn, (1 : G)) : C₂ × G) ∈ R) :
    Nat.card P * Nat.card Q * Nat.card R ≤ 2 * stppCapacity G := by
  obtain ⟨H₁, χ₁, rfl⟩ := eq_charLift_of_sgn_not_mem hP
  obtain ⟨H₂, χ₂, rfl⟩ := eq_charLift_of_sgn_not_mem hQ
  obtain ⟨W, rfl⟩ := eq_prod_top_of_sgn_mem hR
  have hbase : IsTPPTriple H₁ H₂ W := by
    intro s hs t ht w hw hstw
    have h3 : (((χ₁ ⟨s, hs⟩ * χ₂ ⟨t, ht⟩)⁻¹ : C₂), w) ∈
        (⊤ : Subgroup C₂).prod W :=
      Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, hw⟩
    have hprod : (((χ₁ ⟨s, hs⟩ : C₂), s) : C₂ × G) * ((χ₂ ⟨t, ht⟩ : C₂), t) *
        ((χ₁ ⟨s, hs⟩ * χ₂ ⟨t, ht⟩)⁻¹, w) = 1 := by
      rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.mk_eq_one]
      exact ⟨mul_inv_cancel _, hstw⟩
    obtain ⟨e1, e2, e3⟩ := h _ (charLift_mem χ₁ ⟨s, hs⟩)
      _ (charLift_mem χ₂ ⟨t, ht⟩) _ h3 hprod
    rw [Prod.mk_eq_one] at e1 e2 e3
    exact ⟨e1.2, e2.2, e3.2⟩
  have hle := hbase.le_stppCapacity
  rw [card_charLift, card_charLift, card_subgroup_prod, Subgroup.card_top,
    card_C₂]
  calc Nat.card H₁ * Nat.card H₂ * (2 * Nat.card W)
      = 2 * (Nat.card H₁ * Nat.card H₂ * Nat.card W) := by ring
    _ ≤ 2 * stppCapacity G := Nat.mul_le_mul le_rfl hle

/-- **The lift law, upper bound**: every subgroup TPP triple of `C₂ × G` is
Goursat-classified and counted (Pf13 Theorem 1, Cases A and B). -/
theorem stppCapacity_prod_le :
    stppCapacity (C₂ × G) ≤ 2 * max (stppCapacity G) (SigmaMaxLift G) := by
  refine stppCapacity_le_of_forall ?_
  intro P Q R hTPP
  by_cases hP : ((sgn, (1 : G)) : C₂ × G) ∈ P
  · by_cases hQ : ((sgn, (1 : G)) : C₂ × G) ∈ Q
    · -- two members sharing the central sign: impossible
      exfalso
      have hcol : ((sgn, (1 : G)) : C₂ × G) * (sgn, (1 : G)) * 1 = 1 := by
        rw [mul_one, Prod.mk_mul_mk, Prod.mk_eq_one]
        exact ⟨sgn_mul_self, mul_one 1⟩
      have h1 := (hTPP _ hP _ hQ _ R.one_mem hcol).1
      rw [Prod.mk_eq_one] at h1
      exact sgn_ne_one h1.1
    · by_cases hR : ((sgn, (1 : G)) : C₂ × G) ∈ R
      · exfalso
        have hcol : ((sgn, (1 : G)) : C₂ × G) * 1 * (sgn, (1 : G)) = 1 := by
          rw [mul_one, Prod.mk_mul_mk, Prod.mk_eq_one]
          exact ⟨sgn_mul_self, mul_one 1⟩
        have h1 := (hTPP _ hP _ Q.one_mem _ hR hcol).1
        rw [Prod.mk_eq_one] at h1
        exact sgn_ne_one h1.1
      · -- Case B, full member in slot 1: rotate to (Q, R, P)
        have hb := caseB_core hTPP.rotate hQ hR hP
        have hcomm : Nat.card P * Nat.card Q * Nat.card R
            = Nat.card Q * Nat.card R * Nat.card P := by ring
        rw [hcomm]
        exact le_trans hb (Nat.mul_le_mul le_rfl (le_max_left _ _))
  · by_cases hQ : ((sgn, (1 : G)) : C₂ × G) ∈ Q
    · by_cases hR : ((sgn, (1 : G)) : C₂ × G) ∈ R
      · exfalso
        have hcol : (1 : C₂ × G) * (sgn, (1 : G)) * (sgn, (1 : G)) = 1 := by
          rw [one_mul, Prod.mk_mul_mk, Prod.mk_eq_one]
          exact ⟨sgn_mul_self, mul_one 1⟩
        have h1 := (hTPP _ P.one_mem _ hQ _ hR hcol).2.1
        rw [Prod.mk_eq_one] at h1
        exact sgn_ne_one h1.1
      · -- Case B, full member in slot 2: rotate twice to (R, P, Q)
        have hb := caseB_core hTPP.rotate.rotate hR hP hQ
        have hcomm : Nat.card P * Nat.card Q * Nat.card R
            = Nat.card R * Nat.card P * Nat.card Q := by ring
        rw [hcomm]
        exact le_trans hb (Nat.mul_le_mul le_rfl (le_max_left _ _))
    · by_cases hR : ((sgn, (1 : G)) : C₂ × G) ∈ R
      · -- Case B, full member in slot 3
        exact le_trans (caseB_core hTPP hP hQ hR)
          (Nat.mul_le_mul le_rfl (le_max_left _ _))
      · -- Case A: all three members are graphs
        obtain ⟨HS, χS, rfl⟩ := eq_charLift_of_sgn_not_mem hP
        obtain ⟨HT, χT, rfl⟩ := eq_charLift_of_sgn_not_mem hQ
        obtain ⟨HU, χU, rfl⟩ := eq_charLift_of_sgn_not_mem hR
        have hSK := (isTPPTriple_charLift_iff χS χT χU).mp hTPP
        rw [card_charLift, card_charLift, card_charLift, ← card_triple]
        refine le_trans (card_triple_le_two_mul_sigmaCard χS χT χU) ?_
        exact Nat.mul_le_mul le_rfl
          (le_trans (sigmaCard_le_sigmaMaxLift hSK) (le_max_right _ _))

/-- **The lift law** (Pf13 Theorem 1 at p = 2, maxima-transport form):

`β₀(C₂ × G) = 2 · max(β₀(G), Σ_max^lift(G, 2))`

for every finite group `G`. Census maxima compose formally through
`SigmaMaxLift`; the lower bound is witnessed by the Case-B lift of a
`β₀(G)`-achiever and the graph lift of a `Σ_max^lift`-achiever, the upper
bound by the Goursat trichotomy. -/
theorem stppCapacity_prod_eq_two_mul_max :
    stppCapacity (C₂ × G) = 2 * max (stppCapacity G) (SigmaMaxLift G) := by
  refine le_antisymm stppCapacity_prod_le ?_
  have h1 : 2 * stppCapacity G ≤ stppCapacity (C₂ × G) := by
    obtain ⟨H, K, L, hTPP, hcard⟩ := exists_isTPPTriple_card_eq_stppCapacity G
    rw [hcard]
    exact two_mul_le_stppCapacity_of_isTPPTriple hTPP
  have h2 : 2 * SigmaMaxLift G ≤ stppCapacity (C₂ × G) := by
    obtain ⟨HS, HT, HU, χS, χT, χU, hSK, hval⟩ :=
      exists_sigmaMaxLift_witness (G := G)
    rw [hval]
    exact two_mul_sigmaCard_le_stppCapacity hSK
  omega

end LiftLaw

end GroupTPP.TPP
