import Mathlib
import Xlib.TPP

/-!
# TPP is closed under direct products

The triple product property is closed under finite group direct products:
a TPP triple in `G` and a TPP triple in `H` give a TPP triple of product
finsets in `G × H`, with cardinalities multiplying. This lifts to the
iterated power `Fin ℓ → G` via `Fintype.piFinset`.

## Main results

* `Xlib.TPP.TripleProductProperty.prod` — binary product closure.
* `Xlib.TPP.TripleProductProperty.piFinset` — iterated closure on `Fin ℓ → G`.
* `Xlib.TPP.le_tppCapacity_pi` — capacity corollary: TPP in `G` gives
  `(|S|·|T|·|U|)^ℓ ≤ β(Fin ℓ → G)`.
-/

namespace Xlib.TPP

/-! ### Binary product closure -/

/-- **Product closure of the TPP.** If `(S, T, U)` has the TPP in `G` and
`(S', T', U')` has the TPP in `H`, then `(S ×ˢ S', T ×ˢ T', U ×ˢ U')` has
the TPP in `G × H`. The proof projects the TPP hypothesis to each
coordinate. -/
theorem TripleProductProperty.prod
    {G : Type*} {H : Type*}
    [Group G] [DecidableEq G] [Group H] [DecidableEq H]
    {S T U : Finset G} {S' T' U' : Finset H}
    (hG : TripleProductProperty S T U)
    (hH : TripleProductProperty S' T' U') :
    TripleProductProperty (S ×ˢ S') (T ×ˢ T') (U ×ˢ U') := by
  intro s hs s' hs' t ht t' ht' u hu u' hu'
  rw [Finset.mem_product] at hs hs' ht ht' hu hu'
  intro heq
  have heq1 : s'.1⁻¹ * s.1 * t'.1⁻¹ * t.1 * u'.1⁻¹ * u.1 = 1 := by
    have := congr_arg Prod.fst heq
    simp only [Prod.fst_mul, Prod.fst_inv, Prod.fst_one] at this
    exact this
  have heq2 : s'.2⁻¹ * s.2 * t'.2⁻¹ * t.2 * u'.2⁻¹ * u.2 = 1 := by
    have := congr_arg Prod.snd heq
    simp only [Prod.snd_mul, Prod.snd_inv, Prod.snd_one] at this
    exact this
  obtain ⟨hs1, ht1, hu1⟩ := hG s.1 hs.1 s'.1 hs'.1 t.1 ht.1 t'.1 ht'.1
    u.1 hu.1 u'.1 hu'.1 heq1
  obtain ⟨hs2, ht2, hu2⟩ := hH s.2 hs.2 s'.2 hs'.2 t.2 ht.2 t'.2 ht'.2
    u.2 hu.2 u'.2 hu'.2 heq2
  exact ⟨Prod.ext hs1 hs2, Prod.ext ht1 ht2, Prod.ext hu1 hu2⟩

/-! ### Iterated product closure on `Fin ℓ → G` -/

/-- **Iterated product closure.** If `(S, T, U)` has the TPP in `G`, then
the constant-fibre `piFinset` triple has the TPP in `Fin ℓ → G`. -/
theorem TripleProductProperty.piFinset
    {G : Type*} [Group G] [DecidableEq G]
    {S T U : Finset G}
    (h : TripleProductProperty S T U) (ℓ : ℕ) :
    TripleProductProperty
      (Fintype.piFinset fun _ : Fin ℓ => S)
      (Fintype.piFinset fun _ : Fin ℓ => T)
      (Fintype.piFinset fun _ : Fin ℓ => U) := by
  intro s hs s' hs' t ht t' ht' u hu u' hu'
  rw [Fintype.mem_piFinset] at hs hs' ht ht' hu hu'
  intro heq
  have coord : ∀ i : Fin ℓ, (s' i)⁻¹ * s i * (t' i)⁻¹ * t i * (u' i)⁻¹ * u i = 1 := by
    intro i
    have := congr_fun heq i
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply] at this
    exact this
  refine ⟨funext fun i => ?_, funext fun i => ?_, funext fun i => ?_⟩
  · exact (h (s i) (hs i) (s' i) (hs' i) (t i) (ht i) (t' i) (ht' i)
      (u i) (hu i) (u' i) (hu' i) (coord i)).1
  · exact (h (s i) (hs i) (s' i) (hs' i) (t i) (ht i) (t' i) (ht' i)
      (u i) (hu i) (u' i) (hu' i) (coord i)).2.1
  · exact (h (s i) (hs i) (s' i) (hs' i) (t i) (ht i) (t' i) (ht' i)
      (u i) (hu i) (u' i) (hu' i) (coord i)).2.2

/-! ### Capacity corollary -/

/-- **Capacity corollary.** A TPP triple in `G` gives
`(|S| · |T| · |U|)^ℓ ≤ β(Fin ℓ → G)`. -/
theorem le_tppCapacity_pi
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {S T U : Finset G}
    (h : TripleProductProperty S T U) (ℓ : ℕ) :
    (S.card * T.card * U.card) ^ ℓ
      ≤ tppCapacity (Fin ℓ → G) := by
  have htpp := h.piFinset ℓ
  have hle := le_tppCapacity htpp
  rw [Fintype.card_piFinset_const, Fintype.card_piFinset_const,
    Fintype.card_piFinset_const] at hle
  rwa [← mul_pow, ← mul_pow] at hle

/-! ### The subgroup-TPP collision form

For *subgroups*, the left-quotient TPP is equivalent to the collision form
`s * t * u = 1 → s = t = u = 1` (Murthy 2602.15796 Def 2.1 / Pf13 D1–D2),
since quotients of subgroup elements are again subgroup elements. The
collision form is instance-free and is the workhorse of the lift API below. -/

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
  sorry

/-- A collision-form TPP triple satisfies the left-quotient
`TripleProductProperty` on carrier finsets — for *any* `Fintype` instances
on the carriers (instance-parametric on purpose: `stppCapacity` fixes its
own classical instances). -/
theorem IsTPPTriple.tripleProductProperty_toFinset {H K L : Subgroup Γ}
    [Fintype (H : Set Γ)] [Fintype (K : Set Γ)] [Fintype (L : Set Γ)]
    (h : IsTPPTriple H K L) :
    TripleProductProperty (H : Set Γ).toFinset (K : Set Γ).toFinset
      (L : Set Γ).toFinset := by
  sorry

/-- Converse of `IsTPPTriple.tripleProductProperty_toFinset`. -/
theorem IsTPPTriple.of_tripleProductProperty_toFinset {H K L : Subgroup Γ}
    [Fintype (H : Set Γ)] [Fintype (K : Set Γ)] [Fintype (L : Set Γ)]
    (h : TripleProductProperty (H : Set Γ).toFinset (K : Set Γ).toFinset
      (L : Set Γ).toFinset) :
    IsTPPTriple H K L := by
  sorry

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
  sorry

/-- `β₀` is achieved by a collision-form TPP triple. -/
theorem exists_isTPPTriple_card_eq_stppCapacity
    (Γ : Type*) [Group Γ] [Fintype Γ] [DecidableEq Γ] :
    ∃ H K L : Subgroup Γ, IsTPPTriple H K L ∧
      stppCapacity Γ = Nat.card H * Nat.card K * Nat.card L := by
  sorry

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
  sorry

theorem charLift_mem {H : Subgroup G} (χ : H →* A) (h : H) :
    ((χ h : A), (h : G)) ∈ charLift χ :=
  mem_charLift.mpr ⟨h, rfl⟩

/-- The graph has the order of its base subgroup: the projection to `G` is
injective on the graph. -/
theorem card_charLift {H : Subgroup G} (χ : H →* A) :
    Nat.card (charLift χ) = Nat.card H := by
  sorry

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
  sorry

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

/-! ### The lift law for `C₂ × G`

`C₂` is represented as `Multiplicative (ZMod 2)`: an `abbrev`, so the
`CommGroup`/`Fintype`/`DecidableEq` instances of `ZMod 2` apply directly and
ground facts about `C₂` are `decide`-checkable; multiplicative, so `C₂ × G`
is a `Group` and the `Xlib.TPP` API applies verbatim. -/

section LiftLaw

/-- The two-element sign group `C₂ = Multiplicative (ZMod 2)`. -/
abbrev C₂ : Type := Multiplicative (ZMod 2)

/-- The nontrivial sign `σ ∈ C₂`. -/
abbrev sgn : C₂ := Multiplicative.ofAdd 1

variable {G : Type*} [Group G]

/-- Goursat trichotomy for `C₂ × G`, full case (Pf13 Lemma G(iii)): a
subgroup containing the central sign `(σ, 1)` is a full product `C₂ × W`. -/
theorem eq_prod_top_of_sgn_mem {P : Subgroup (C₂ × G)}
    (hz : ((sgn, (1 : G)) : C₂ × G) ∈ P) :
    ∃ W : Subgroup G, P = (⊤ : Subgroup C₂).prod W := by
  sorry

/-- Goursat trichotomy for `C₂ × G`, graph case (Pf13 Lemma G(i)–(ii)): a
subgroup avoiding the central sign `(σ, 1)` is the graph of a unique
character on its projection. Full Goursat is not needed: each base element
has a unique sign lift, and uniqueness makes the lift a homomorphism. -/
theorem eq_charLift_of_sgn_not_mem {P : Subgroup (C₂ × G)}
    (hz : ((sgn, (1 : G)) : C₂ × G) ∉ P) :
    ∃ (H : Subgroup G) (χ : H →* C₂), P = charLift χ := by
  sorry

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

variable [Fintype G] [DecidableEq G]

/-- A sign-killed configuration witnesses `SigmaMaxLift`. -/
theorem sigmaCard_le_sigmaMaxLift {HS HT HU : Subgroup G}
    {χS : HS →* C₂} {χT : HT →* C₂} {χU : HU →* C₂}
    (h : SignKilled χS χT χU) :
    sigmaCard χS χT χU ≤ SigmaMaxLift G := by
  sorry

/-- **Per-witness capacity bound** (Pf13 8.1, "eligibility implies
realizability"): a sign-killed configuration gives
`2 |Σ| ≤ β₀(C₂ × G)`. This is the seam consumed by census certificates:
`SignKilled` is decidable on concrete data, and this bound turns each
census eligible-config + character-combo into a Lean witness. -/
theorem two_mul_sigmaCard_le_stppCapacity {HS HT HU : Subgroup G}
    {χS : HS →* C₂} {χT : HT →* C₂} {χU : HU →* C₂}
    (h : SignKilled χS χT χU) :
    2 * sigmaCard χS χT χU ≤ stppCapacity (C₂ × G) := by
  sorry

/-- Case-B lift (Pf13 Theorem 1, Case B): an honest TPP triple of `G` lifts
to `(1 × H, 1 × K, C₂ × L)`, doubling the size. -/
theorem two_mul_le_stppCapacity_of_isTPPTriple {H K L : Subgroup G}
    (h : IsTPPTriple H K L) :
    2 * (Nat.card H * Nat.card K * Nat.card L) ≤ stppCapacity (C₂ × G) := by
  sorry

/-- **The lift law, upper bound**: every subgroup TPP triple of `C₂ × G` is
Goursat-classified and counted (Pf13 Theorem 1, Cases A and B). -/
theorem stppCapacity_prod_le :
    stppCapacity (C₂ × G) ≤ 2 * max (stppCapacity G) (SigmaMaxLift G) := by
  sorry

/-- **The lift law** (Pf13 Theorem 1 at p = 2, maxima-transport form):

`β₀(C₂ × G) = 2 · max(β₀(G), Σ_max^lift(G, 2))`

for every finite group `G`. Census maxima compose formally through
`SigmaMaxLift`; the lower bound is witnessed by the Case-B lift of a
`β₀(G)`-achiever and the graph lift of a `Σ_max^lift`-achiever, the upper
bound by the Goursat trichotomy. -/
theorem stppCapacity_prod_eq_two_mul_max :
    stppCapacity (C₂ × G) = 2 * max (stppCapacity G) (SigmaMaxLift G) := by
  sorry

end LiftLaw

end Xlib.TPP
