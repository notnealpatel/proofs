import GroupTPP.TPP

/-!
# A normal member in a subgroup TPP triple forces `|S|·|T|·|U| ≤ |G|`

This file formalizes **Hedtke–Murthy, Theorem 3.5** [arXiv:1104.5097, Thm 3.5]:
if `(S, T, U)` is a *subgroup* Triple Product Property triple in a finite group
`G` and at least one of `S, T, U` is **normal** in `G`, then
`|S| · |T| · |U| ≤ |G|`.

This is the nonabelian analogue of the abelian barrier
(`GroupTPP.TPP.card_mul_card_mul_card_le`): once one factor is normal, the product
bound that fails for general nonabelian triples (which can reach
`|S|·|T|·|U| > |G|`) is restored. It is the theoretical justification for
restricting subgroup TPP searches to *nonnormal* subgroups [arXiv:1104.5097,
Observation 4.1].

## Proof strategy

Assume (WLOG, by relabelling) `S` is the normal member. The engine is a single
injectivity statement, the **normal-quotient injection**:

> `GroupTPP.TPP.SubgroupTPP.injOn_quot` — the map `↥T × ↥U → G ⧸ S`,
> `(t, u) ↦ ↑(t * u)`, is injective.

Given `↑(t * u) = ↑(t' * u')`, `QuotientGroup.eq` produces `σ ∈ S` with
`(t*u)⁻¹ * (t'*u') = σ`. Normality of `S` lets us *transport* `σ` across `u`:
`τ := u * σ * u⁻¹ ∈ S`, and a short computation rearranges the relation into the
TPP equation `τ⁻¹ * (t⁻¹ * t') * (u' * u⁻¹) = 1`. Reading this as
`(S-quotient)·(T-quotient)·(U-quotient)` — with the `U`-quotient `u' * u⁻¹`
realized inside the *subgroup* `U` — the elementwise TPP forces `t = t'` and
`u = u'`.

An injection `↥T × ↥U ↪ G ⧸ S` gives `|T|·|U| ≤ |G ⧸ S| = [G : S]`, and Lagrange
`|G| = |G ⧸ S| · |S|` upgrades this to `|S|·|T|·|U| ≤ |G|`.

## Main results

* `GroupTPP.TPP.SubgroupTPP.injOn_quot` — the normal-quotient injection.
* `GroupTPP.TPP.SubgroupTPP.card_mul_card_le_index_of_normal_left` — `|T|·|U| ≤ [G:S]`.
* `GroupTPP.TPP.card_mul_card_mul_card_le_of_normal` — Theorem 3.5 in `Nat.card`
  form: a normal member (in any of the three slots) forces the product bound.
* `GroupTPP.TPP.card_mul_card_mul_card_le_toFinset_of_normal` — the same bound in the
  `Finset`-carrier phrasing that mirrors `GroupTPP.TPP.card_mul_card_mul_card_le`.

## References

* J. Hedtke, I. Murthy, *Search and test algorithms for Triple Product Property
  triples*, [arXiv:1104.5097], Theorem 3.5.
-/

open scoped BigOperators

namespace GroupTPP.TPP

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-! ### Permutation symmetry of the TPP

The elementwise condition `s'⁻¹*s*t'⁻¹*t*u'⁻¹*u = 1 → …` is invariant under all
permutations of `(S, T, U)` (Cohn–Umans [math/0307321, Lem. 2.1]). We prove this
from two generators of `S₃`: the **cyclic shift** `(S,T,U) ↦ (T,U,S)` (free,
because `A*B*C = 1 ↔ C*A*B = 1`) and the **reversal** `(S,T,U) ↦ (U,T,S)` (from
inverting the relation: `(A*B*C)⁻¹ = C⁻¹*B⁻¹*A⁻¹`). All three normal-slot cases of
Theorem 3.5 then reduce to the single normal-in-slot-`S` injection. -/

omit [Fintype G] [DecidableEq G] in
/-- **Cyclic-shift symmetry.** `TripleProductProperty S T U → … T U S`.
Free from the conjugation-invariance of `· = 1`: the relation
`(t'⁻¹t)(u'⁻¹u)(s'⁻¹s) = 1` is equivalent to `(s'⁻¹s)(t'⁻¹t)(u'⁻¹u) = 1`. -/
theorem TripleProductProperty.cyclic {S T U : Finset G}
    (h : TripleProductProperty S T U) : TripleProductProperty T U S := by
  intro t ht t' ht' u hu u' hu' s hs s' hs' hrel
  have hrel' : s'⁻¹ * s * t'⁻¹ * t * u'⁻¹ * u = 1 := by
    have heq : s'⁻¹ * s * t'⁻¹ * t * u'⁻¹ * u
        = (s'⁻¹ * s) * (t'⁻¹ * t * u'⁻¹ * u * s'⁻¹ * s) * (s'⁻¹ * s)⁻¹ := by group
    rw [heq, hrel]; group
  obtain ⟨hs', ht', hu'⟩ := h s hs s' hs' t ht t' ht' u hu u' hu' hrel'
  exact ⟨ht', hu', hs'⟩

omit [Fintype G] [DecidableEq G] in
/-- **Reversal symmetry.** `TripleProductProperty S T U → … U T S`.
From inverting the relation: `(u'⁻¹u)(t'⁻¹t)(s'⁻¹s) = 1` inverts to
`(s⁻¹s')(t⁻¹t')(u⁻¹u') = 1`, an `(S,T,U)` relation with primes swapped. -/
theorem TripleProductProperty.reverse {S T U : Finset G}
    (h : TripleProductProperty S T U) : TripleProductProperty U T S := by
  intro u hu u' hu' t ht t' ht' s hs s' hs' hrel
  have hrel' : s⁻¹ * s' * t⁻¹ * t' * u⁻¹ * u' = 1 := by
    have heq : s⁻¹ * s' * t⁻¹ * t' * u⁻¹ * u'
        = (u'⁻¹ * u * t'⁻¹ * t * s'⁻¹ * s)⁻¹ := by group
    rw [heq, hrel, inv_one]
  obtain ⟨hs', ht', hu'⟩ := h s' hs' s hs t' ht' t ht u' hu' u hu hrel'
  exact ⟨hu'.symm, ht'.symm, hs'.symm⟩

/-! ### Carrier-membership bridge

`SubgroupTripleProductProperty` is stated through the carrier finsets
`(H : Set G).toFinset`. The following turns subgroup membership into membership
in those finsets, so the elementwise TPP can be fed honest subgroup elements. -/

omit [Fintype G] [DecidableEq G] in
/-- Membership in a subgroup carrier finset is subgroup membership. -/
@[simp] theorem mem_carrier_toFinset {H : Subgroup G} [Fintype (H : Set G)]
    {g : G} : g ∈ (H : Set G).toFinset ↔ g ∈ H := by
  rw [Set.mem_toFinset]; rfl

/-! ### The normal-quotient injection

The heart of the proof: when `S` is normal, the pair-product map into `G ⧸ S` is
injective on `↥T × ↥U`. -/

omit [DecidableEq G] in
/-- **Normal-quotient injection.** Let `(S, T, U)` be a subgroup TPP triple with
`S` normal in `G`. Then `↥T × ↥U → G ⧸ S`, `(t, u) ↦ ↑(t * u)`, is injective.

Commutativity is *not* assumed: normality of `S` is what lets the displaced
`S`-factor `σ` be conjugated back (`τ = u σ u⁻¹ ∈ S`) into the slot the
elementwise TPP expects. -/
theorem SubgroupTPP.injOn_quot {S T U : Subgroup G}
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] [DecidablePred (· ∈ U)]
    (h : SubgroupTripleProductProperty S T U) (hSnorm : S.Normal) :
    Function.Injective
      (fun p : (↥T) × (↥U) => (QuotientGroup.mk ((p.1 : G) * (p.2 : G)) : G ⧸ S)) := by
  -- unfold the subgroup TPP to its elementwise form on carrier finsets
  rw [SubgroupTripleProductProperty] at h
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ heq
  simp only at heq
  -- `heq : ↑(a*b) = ↑(c*d)` in `G ⧸ S`; extract the witnessing `σ ∈ S`
  rw [QuotientGroup.eq] at heq
  set σ : G := (a * b)⁻¹ * (c * d) with hσdef
  have hσ : σ ∈ S := heq
  -- conjugate `σ` back across `b` (normality of `S`): `τ = b σ b⁻¹ ∈ S`
  set τ : G := b * σ * b⁻¹ with hτdef
  have hτ : τ ∈ S := hSnorm.conj_mem σ hσ b
  -- the TPP equation `τ⁻¹ * a⁻¹ * c * d * b⁻¹ = 1`, in the slot ordering
  -- `(s'⁻¹*s)*(t'⁻¹*t)*(u'⁻¹*u)` with s=1,s'=τ,t=c,t'=a,u=d*b⁻¹,u'=1
  have hquot : τ⁻¹ * (1 : G) * a⁻¹ * c * (1 : G)⁻¹ * (d * b⁻¹) = 1 := by
    rw [hτdef, hσdef]; group
  -- feed the elementwise TPP honest carrier-finset memberships
  have h1S : (1 : G) ∈ (S : Set G).toFinset := mem_carrier_toFinset.mpr (one_mem S)
  have hτS : τ ∈ (S : Set G).toFinset := mem_carrier_toFinset.mpr hτ
  have hcT : c ∈ (T : Set G).toFinset := mem_carrier_toFinset.mpr hc
  have haT : a ∈ (T : Set G).toFinset := mem_carrier_toFinset.mpr ha
  have hdbU : d * b⁻¹ ∈ (U : Set G).toFinset :=
    mem_carrier_toFinset.mpr (mul_mem hd (inv_mem hb))
  have h1U : (1 : G) ∈ (U : Set G).toFinset := mem_carrier_toFinset.mpr (one_mem U)
  obtain ⟨_, htt, huu⟩ :=
    h (1 : G) h1S τ hτS c hcT a haT (d * b⁻¹) hdbU (1 : G) h1U hquot
  -- `htt : c = a` and `huu : d * b⁻¹ = 1`, i.e. `a = c` and `b = d`
  have hac : a = c := htt.symm
  have hbd : b = d := (mul_inv_eq_one.mp huu).symm
  subst hac hbd
  rfl

/-! ### Cardinality assembly -/

omit [Fintype G] [DecidableEq G] in
/-- Cardinality of a subgroup as the carrier-finset cardinality (used to align
the `Nat.card` bound with the `Finset`-carrier statement). -/
private theorem natCard_eq_carrier_card {H : Subgroup G} [Fintype (H : Set G)] :
    Nat.card H = (H : Set G).toFinset.card :=
  Nat.card_eq_card_toFinset (H : Set G)

omit [DecidableEq G] in
/-- With `S` normal, the product `|T|·|U|` is bounded by the index `[G : S]`,
i.e. `|G ⧸ S|`. Immediate from the normal-quotient injection. -/
theorem SubgroupTPP.card_mul_card_le_index_of_normal_left
    {S T U : Subgroup G}
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] [DecidablePred (· ∈ U)]
    (h : SubgroupTripleProductProperty S T U) (hSnorm : S.Normal) :
    Nat.card T * Nat.card U ≤ Nat.card (G ⧸ S) := by
  have hinj := SubgroupTPP.injOn_quot h hSnorm
  have hle := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod] at hle

omit [DecidableEq G] in
/-- **Theorem 3.5, normal-in-slot-`S` case.** If `(S, T, U)` is a subgroup TPP
triple and `S` is normal in `G`, then `|S| · |T| · |U| ≤ |G|`.

Multiply the index bound `|T|·|U| ≤ |G ⧸ S|` by `|S|` and apply Lagrange
`|G| = |G ⧸ S| · |S|`. -/
theorem card_mul_card_mul_card_le_of_normal_left {S T U : Subgroup G}
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] [DecidablePred (· ∈ U)]
    (h : SubgroupTripleProductProperty S T U) (hSnorm : S.Normal) :
    Nat.card S * Nat.card T * Nat.card U ≤ Nat.card G := by
  have hidx := SubgroupTPP.card_mul_card_le_index_of_normal_left h hSnorm
  have hLag : Nat.card G = Nat.card (G ⧸ S) * Nat.card S :=
    S.card_eq_card_quotient_mul_card_subgroup
  calc Nat.card S * Nat.card T * Nat.card U
      = Nat.card S * (Nat.card T * Nat.card U) := mul_assoc ..
    _ ≤ Nat.card S * Nat.card (G ⧸ S) := Nat.mul_le_mul_left _ hidx
    _ = Nat.card G := by rw [hLag, mul_comm]

/-! ### Theorem 3.5 -/

omit [DecidableEq G] in
/-- **Hedtke–Murthy, Theorem 3.5** [arXiv:1104.5097]. If `(S, T, U)` is a subgroup
TPP triple and **at least one** of `S, T, U` is normal in `G`, then
`|S| · |T| · |U| ≤ |G|`.

The three cases are reduced to the normal-in-slot-`S` lemma
`card_mul_card_mul_card_le_of_normal_left` by the cyclic symmetry
`TripleProductProperty.cyclic`, which rotates the normal member into the first
slot. This is the nonabelian companion to `GroupTPP.TPP.card_mul_card_mul_card_le`:
the bound that fails for general nonabelian subgroup triples is restored as soon
as one member is normal. -/
theorem card_mul_card_mul_card_le_of_normal {S T U : Subgroup G}
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] [DecidablePred (· ∈ U)]
    (h : SubgroupTripleProductProperty S T U)
    (hN : S.Normal ∨ T.Normal ∨ U.Normal) :
    Nat.card S * Nat.card T * Nat.card U ≤ Nat.card G := by
  rcases hN with hSnorm | hTnorm | hUnorm
  · -- S normal: direct.
    exact card_mul_card_mul_card_le_of_normal_left h hSnorm
  · -- T normal: rotate to `(T, U, S)` (one cyclic shift), bound `|T||U||S|`.
    have hcyc : SubgroupTripleProductProperty T U S := h.cyclic
    have hb := card_mul_card_mul_card_le_of_normal_left hcyc hTnorm
    calc Nat.card S * Nat.card T * Nat.card U
        = Nat.card T * Nat.card U * Nat.card S := by ring
      _ ≤ Nat.card G := hb
  · -- U normal: rotate to `(U, S, T)` (two cyclic shifts), bound `|U||S||T|`.
    have hcyc : SubgroupTripleProductProperty U S T := h.cyclic.cyclic
    have hb := card_mul_card_mul_card_le_of_normal_left hcyc hUnorm
    calc Nat.card S * Nat.card T * Nat.card U
        = Nat.card U * Nat.card S * Nat.card T := by ring
      _ ≤ Nat.card G := hb

omit [DecidableEq G] in
/-- **Theorem 3.5, carrier-finset phrasing.** The same bound as
`card_mul_card_mul_card_le_of_normal`, stated through the carrier finsets and
`Fintype.card G`, to mirror the abelian-barrier API
`GroupTPP.TPP.card_mul_card_mul_card_le`. -/
theorem card_mul_card_mul_card_le_toFinset_of_normal {S T U : Subgroup G}
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] [DecidablePred (· ∈ U)]
    (h : SubgroupTripleProductProperty S T U)
    (hN : S.Normal ∨ T.Normal ∨ U.Normal) :
    (S : Set G).toFinset.card * (T : Set G).toFinset.card *
        (U : Set G).toFinset.card ≤ Fintype.card G := by
  have hb := card_mul_card_mul_card_le_of_normal h hN
  rw [← natCard_eq_carrier_card, ← natCard_eq_carrier_card, ← natCard_eq_carrier_card,
    ← Nat.card_eq_fintype_card]
  exact hb

end GroupTPP.TPP
