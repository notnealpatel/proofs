import Mathlib
import GroupTPP.TPP

/-!
# Basic TPP triples: the WLOG reduction and the Hedtke–Murthy test

This file formalizes two results of Hedtke–Murthy [arXiv:1104.5097] about
**basic** Triple Product Property triples (those containing the identity in
each set):

1. the **"WLOG basic" reduction**: *any* TPP triple can be left-translated,
   factor by factor, to a basic TPP triple, and the translation preserves the
   three cardinalities;
2. **Theorem 3.1**, the set-theoretic characterization of the TPP by two
   quotient-set identities — the test that every GAP/Sage TPP search
   implementation actually runs — together with its subgroup specialization.

The reduction (1) is remarked on by Hedtke–Murthy
[arXiv:1104.5097, just after Lemma `lemm:Neumann`, "Note that any TPP triple
can be translated to a basic TPP triple"], resting on the
**translation-invariance** of the TPP, originally Neumann's Observation 2.1
[ibid., Lemma `lemm:Neumann`]: if `(S, T, U)` is a TPP triple then so is
`(dSa, dTb, dUc)`.

The TPP in `GroupTPP.TPP` is the *left-quotient* form
`s'⁻¹ s · t'⁻¹ t · u'⁻¹ u = 1 → s = s' ∧ t = t' ∧ u = u'`
(matching Murthy / Wikipedia). For this convention the invariant translations
are exactly the **left** translations `S ↦ d • S`, acting independently on each
factor: a left translate has the *same* left-quotient set as the original,
because `(d s')⁻¹ (d s) = s'⁻¹ s`. (Neumann's right translates `S ↦ S a`
conjugate the right-quotient set, the convention used in [1104.5097].) No
commutativity and no finiteness are needed.

This reduction is *why* `GroupTPP.TPP.inter_ST_eq_one_of_basic` and its siblings —
the basic-triple pairwise-intersection equalities `S ∩ T = T ∩ U = S ∩ U = 1` —
are not a loss of generality: they apply to the translated representative of
*every* TPP triple, which has the same cardinalities, hence the same
`|S| · |T| · |U|`.

## Main definitions

* `GroupTPP.HedtkeBasic.IsBasic` — `(S, T, U)` is *basic* when `1 ∈ S ∩ T ∩ U`.

## Main results

* `GroupTPP.TPP.TripleProductProperty.smul` — **translation invariance**: if
  `(S, T, U)` has the TPP then so does `(d • S, e • T, f • U)` for any
  `d e f : G`.
* `GroupTPP.HedtkeBasic.exists_basic_of_tpp` — **Hedtke's WLOG-basic reduction**:
  every TPP triple of nonempty sets left-translates to a *basic* TPP triple
  with the same three cardinalities (hence the same product `|S|·|T|·|U|`).
* `GroupTPP.HedtkeBasic.tripleProductProperty_iff_leftQuot` and
  `GroupTPP.HedtkeBasic.IsBasic.tpp_iff` — **Hedtke–Murthy Theorem 3.1**
  [arXiv:1104.5097], mirrored to the left-quotient convention: for a basic
  (indeed, for any nonempty) triple, the TPP is *equivalent* to
  `Q(T) ∩ Q(U) = {1}` and `Q(S) ∩ Q(T)·Q(U) = {1}`.
* `GroupTPP.HedtkeBasic.subgroupTripleProductProperty_iff` — the subgroup
  specialization `K ⊓ L = ⊥ ∧ H ∩ K·L = {1}` (using `Q(H) = H`): the tier-0
  computational test run by the TPP group sieve (`Scratch/GroupSieve/`) and
  the GAP searches of [arXiv:1104.5097].

## References

* J. Hedtke, I. Murthy (notation), *Search and test algorithms for Triple
  Product Property triples*, [arXiv:1104.5097]; the translation remark follows
  Lemma `lemm:Neumann` (P. Neumann, Observation 2.1).
* H. Cohn, C. Umans, *A group-theoretic approach to fast matrix
  multiplication*, [arXiv:math/0307321].
-/

open scoped Pointwise

namespace GroupTPP.TPP

variable {G : Type*} [Group G]

/-- **Translation invariance of the TPP** (Neumann's Observation 2.1,
Hedtke–Murthy [arXiv:1104.5097, Lemma `lemm:Neumann`], adapted to the
left-quotient convention).

If `(S, T, U)` has the Triple Product Property, then so does the factorwise
**left**-translate `(d • S, e • T, f • U)` for *any* `d e f : G`. The proof is a
pure cancellation: writing each translated element as `d * a` (`a` in the
original set), every left quotient `(d a')⁻¹ (d a)` collapses to `a'⁻¹ a`, so
the TPP hypothesis on the translate is *literally* the TPP hypothesis on the
original. No commutativity or finiteness is used. -/
theorem TripleProductProperty.smul [DecidableEq G] {S T U : Finset G}
    (h : TripleProductProperty S T U) (d e f : G) :
    TripleProductProperty (d • S) (e • T) (f • U) := by
  intro s hs s' hs' t ht t' ht' u hu u' hu' heq
  rw [Finset.mem_smul_finset] at hs hs' ht ht' hu hu'
  obtain ⟨a, ha, rfl⟩ := hs
  obtain ⟨a', ha', rfl⟩ := hs'
  obtain ⟨b, hb, rfl⟩ := ht
  obtain ⟨b', hb', rfl⟩ := ht'
  obtain ⟨c, hc, rfl⟩ := hu
  obtain ⟨c', hc', rfl⟩ := hu'
  -- The translated hypothesis collapses to the original left-quotient equation,
  -- since each left quotient `(d a')⁻¹ (d a)` cancels the translation to `a'⁻¹ a`.
  simp only [smul_eq_mul] at heq
  have hquot : a'⁻¹ * a * b'⁻¹ * b * c'⁻¹ * c = 1 := by
    rw [← heq]; group
  obtain ⟨hsa, hsb, hsc⟩ := h a ha a' ha' b hb b' hb' c hc c' hc' hquot
  exact ⟨by rw [hsa], by rw [hsb], by rw [hsc]⟩

/-! ### The basic-triple reduction -/

end GroupTPP.TPP

namespace GroupTPP.HedtkeBasic

variable {G : Type*} [Group G]

open GroupTPP.TPP

/-- A triple `(S, T, U)` of subsets is **basic** (Hedtke–Murthy
[arXiv:1104.5097, Def. "basic TPP triple", after P. Neumann]) when the identity
lies in all three: `1 ∈ S`, `1 ∈ T`, `1 ∈ U` (i.e. `1 ∈ S ∩ T ∩ U`). -/
def IsBasic (S T U : Finset G) : Prop :=
  (1 : G) ∈ S ∧ (1 : G) ∈ T ∧ (1 : G) ∈ U

/-- **Hedtke's WLOG-basic reduction** [arXiv:1104.5097, the remark following
Lemma `lemm:Neumann`]: every TPP triple of nonempty sets can be left-translated,
factor by factor, to a **basic** TPP triple with the *same* three
cardinalities.

Concretely, choosing `s₀ ∈ S`, `t₀ ∈ T`, `u₀ ∈ U`, the translate
`(s₀⁻¹ • S, t₀⁻¹ • T, u₀⁻¹ • U)` has the TPP (translation invariance), contains
the identity in each set (since `s₀⁻¹ • s₀ = 1`, etc.), and preserves
cardinalities (left translation is a bijection). This is why the basic-triple
intersection identities `S ∩ T = T ∩ U = S ∩ U = 1`
(`GroupTPP.TPP.inter_ST_eq_one_of_basic`) lose no generality. -/
theorem exists_basic_of_tpp [DecidableEq G] {S T U : Finset G}
    (h : TripleProductProperty S T U) (hS : S.Nonempty) (hT : T.Nonempty)
    (hU : U.Nonempty) :
    ∃ S' T' U' : Finset G,
      TripleProductProperty S' T' U' ∧ IsBasic S' T' U' ∧
        S'.card = S.card ∧ T'.card = T.card ∧ U'.card = U.card := by
  obtain ⟨s₀, hs₀⟩ := hS
  obtain ⟨t₀, ht₀⟩ := hT
  obtain ⟨u₀, hu₀⟩ := hU
  refine ⟨s₀⁻¹ • S, t₀⁻¹ • T, u₀⁻¹ • U, h.smul s₀⁻¹ t₀⁻¹ u₀⁻¹, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact Finset.mem_smul_finset.mpr ⟨s₀, hs₀, by simp⟩
    · exact Finset.mem_smul_finset.mpr ⟨t₀, ht₀, by simp⟩
    · exact Finset.mem_smul_finset.mpr ⟨u₀, hu₀, by simp⟩
  · exact Finset.card_smul_finset _ _
  · exact Finset.card_smul_finset _ _
  · exact Finset.card_smul_finset _ _

/-- **The payoff of the WLOG-basic reduction.** Combining
`exists_basic_of_tpp` with the basic-triple intersection identities
`GroupTPP.TPP.inter_ST_eq_one_of_basic` (and its `TU` / `SU` siblings), *every* TPP
triple of nonempty sets left-translates to a TPP triple whose three pairwise
intersections are each exactly the trivial subgroup `{1}`, with the same three
cardinalities.

This is Hedtke–Murthy's Observation `ob:Intersec`
[arXiv:1104.5097, "It is sufficient to search TPP triples with
`S ∩ T = T ∩ U = S ∩ U = 1`"]: the intersection equalities `(***)`, which a
priori require a *basic* triple, in fact constrain a representative of every TPP
triple, so they may be assumed without loss of generality. -/
theorem exists_pairwise_inter_one_of_tpp [DecidableEq G] {S T U : Finset G}
    (h : TripleProductProperty S T U) (hS : S.Nonempty) (hT : T.Nonempty)
    (hU : U.Nonempty) :
    ∃ S' T' U' : Finset G,
      TripleProductProperty S' T' U' ∧
        S' ∩ T' = {1} ∧ T' ∩ U' = {1} ∧ S' ∩ U' = {1} ∧
          S'.card = S.card ∧ T'.card = T.card ∧ U'.card = U.card := by
  obtain ⟨S', T', U', hTPP', ⟨h1S, h1T, h1U⟩, hcS, hcT, hcU⟩ :=
    exists_basic_of_tpp h hS hT hU
  exact ⟨S', T', U', hTPP',
    inter_ST_eq_one_of_basic hTPP' h1S h1T h1U,
    inter_TU_eq_one_of_basic hTPP' h1S h1T h1U,
    inter_SU_eq_one_of_basic hTPP' h1S h1T h1U,
    hcS, hcT, hcU⟩

/-! ### Hedtke–Murthy Theorem 3.1: the computational TPP test

Hedtke–Murthy [arXiv:1104.5097, Thm 3.1] characterize basic TPP triples by two
quotient-set identities — the test that every GAP/Sage TPP search
implementation actually runs. The paper works with the *right* quotient set
`Q(X) = {x y⁻¹}`; mirrored to this library's left-quotient convention
(`GroupTPP.TPP.leftQuot`, `Q(X) = {x'⁻¹ x}`), the characterization keeps exactly
the same shape:

  `TPP(S, T, U) ↔ Q(T) ∩ Q(U) = {1} ∧ Q(S) ∩ Q(T)·Q(U) = {1}`.

Basicness enters only through nonemptiness: the forward direction needs
`S, T, U ≠ ∅` (so that `1` lies in each quotient set), and the reverse
direction is unconditional. We therefore prove the iff for nonempty triples
(`tripleProductProperty_iff_leftQuot`), then specialize to basic triples
(`IsBasic.tpp_iff`, the statement of Thm 3.1) and to subgroup carriers
(`subgroupTripleProductProperty_iff`), where `Q(H) = H` collapses the
conditions to `K ⊓ L = ⊥` and `H ∩ K·L = {1}`.

The mirrored shape was checked exhaustively before proving: over all `32³`
basic triples (and all nonempty triples) of `DihedralGroup 3`, and over all
subgroup triples of S₃, D₄, Q₈, A₄, D₆, C₃×C₄ and S₄; the iff genuinely
fails for empty sets (the TPP is vacuously true, the quotient conditions are
not). -/

/-- Condition (iii) of **Hedtke–Murthy Theorem 3.1** [arXiv:1104.5097],
forward direction, mirrored to left quotients: for a TPP triple of nonempty
sets, `Q(S) ∩ Q(T)·Q(U) = {1}`.

If `g = s'⁻¹ s = (t'⁻¹ t) · (u'⁻¹ u)` is a common element, then
`(s⁻¹ s')(t'⁻¹ t)(u'⁻¹ u) = g⁻¹ · g = 1` is a TPP equation, so the TPP forces
`s' = s`, i.e. `g = 1`. The companion condition (ii), `Q(T) ∩ Q(U) = {1}`, is
`GroupTPP.TPP.leftQuot_inter_TU`. -/
theorem leftQuot_inter_mul [DecidableEq G] {S T U : Finset G}
    (h : TripleProductProperty S T U) (hS : S.Nonempty) (hT : T.Nonempty)
    (hU : U.Nonempty) : leftQuot S ∩ (leftQuot T * leftQuot U) = {1} := by
  rw [Finset.eq_singleton_iff_unique_mem]
  refine ⟨Finset.mem_inter.mpr ⟨one_mem_leftQuot hS, ?_⟩, ?_⟩
  · simpa using Finset.mul_mem_mul (one_mem_leftQuot hT) (one_mem_leftQuot hU)
  · intro g hg
    rw [Finset.mem_inter] at hg
    obtain ⟨hgS, hgTU⟩ := hg
    obtain ⟨s, hs, s', hs', hsg⟩ := mem_leftQuot.mp hgS
    obtain ⟨qt, hqt, qu, hqu, hmul⟩ := Finset.mem_mul.mp hgTU
    obtain ⟨t, ht, t', ht', htg⟩ := mem_leftQuot.mp hqt
    obtain ⟨u, hu, u', hu', hug⟩ := mem_leftQuot.mp hqu
    have hquot : s⁻¹ * s' * t'⁻¹ * t * u'⁻¹ * u = 1 := by
      have hre : s⁻¹ * s' * t'⁻¹ * t * u'⁻¹ * u
          = (s'⁻¹ * s)⁻¹ * ((t'⁻¹ * t) * (u'⁻¹ * u)) := by group
      rw [hre, htg, hug, hmul, hsg, inv_mul_cancel]
    have hss' := (h s' hs' s hs t ht t' ht' u hu u' hu' hquot).1
    rw [← hsg, hss', inv_mul_cancel]

/-- **Hedtke–Murthy Theorem 3.1** [arXiv:1104.5097], reverse direction,
mirrored to left quotients — the direction that makes the quotient-set test
sufficient. No nonemptiness or basicness is needed.

Given a TPP equation `(s'⁻¹ s)(t'⁻¹ t)(u'⁻¹ u) = 1`, the element `(s'⁻¹ s)⁻¹`
equals `(t'⁻¹ t)(u'⁻¹ u)`, hence lies in `Q(S) ∩ Q(T)·Q(U) = {1}` (quotient
sets are inverse-closed); this forces `s = s'`, after which
`t'⁻¹ t = (u'⁻¹ u)⁻¹` lies in `Q(T) ∩ Q(U) = {1}`, forcing `t = t'` and then
`u = u'`. -/
theorem tripleProductProperty_of_leftQuot [DecidableEq G] {S T U : Finset G}
    (hTU : leftQuot T ∩ leftQuot U = {1})
    (hSTU : leftQuot S ∩ (leftQuot T * leftQuot U) = {1}) :
    TripleProductProperty S T U := by
  intro s hs s' hs' t ht t' ht' u hu u' hu' heq
  have hqs : s'⁻¹ * s ∈ leftQuot S := mem_leftQuot.mpr ⟨s, hs, s', hs', rfl⟩
  have hqt : t'⁻¹ * t ∈ leftQuot T := mem_leftQuot.mpr ⟨t, ht, t', ht', rfl⟩
  have hqu : u'⁻¹ * u ∈ leftQuot U := mem_leftQuot.mpr ⟨u, hu, u', hu', rfl⟩
  -- the TPP equation says `(s'⁻¹ s)⁻¹ = (t'⁻¹ t) · (u'⁻¹ u)`
  have hinv : (s'⁻¹ * s)⁻¹ = (t'⁻¹ * t) * (u'⁻¹ * u) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← heq]; group
  -- so `(s'⁻¹ s)⁻¹ ∈ Q(S) ∩ Q(T)·Q(U) = {1}`, forcing `s = s'`
  have hmemS : (s'⁻¹ * s)⁻¹ ∈ leftQuot S ∩ (leftQuot T * leftQuot U) := by
    refine Finset.mem_inter.mpr ⟨inv_mem_leftQuot hqs, ?_⟩
    rw [hinv]
    exact Finset.mul_mem_mul hqt hqu
  rw [hSTU, Finset.mem_singleton] at hmemS
  have hss : s = s' := (inv_mul_eq_one.mp (inv_eq_one.mp hmemS)).symm
  -- then `(t'⁻¹ t)(u'⁻¹ u) = 1`, so `t'⁻¹ t ∈ Q(T) ∩ Q(U) = {1}`
  have htu1 : (t'⁻¹ * t) * (u'⁻¹ * u) = 1 := by rw [← hinv]; exact hmemS
  have hmemT : t'⁻¹ * t ∈ leftQuot T ∩ leftQuot U := by
    refine Finset.mem_inter.mpr ⟨hqt, ?_⟩
    have h2 := inv_mem_leftQuot hqu
    rwa [inv_eq_of_mul_eq_one_left htu1] at h2
  rw [hTU, Finset.mem_singleton] at hmemT
  have htt : t = t' := (inv_mul_eq_one.mp hmemT).symm
  -- and finally `u'⁻¹ u = 1`
  rw [hmemT, one_mul] at htu1
  exact ⟨hss, htt, (inv_mul_eq_one.mp htu1).symm⟩

/-- **Hedtke–Murthy Theorem 3.1** [arXiv:1104.5097] for nonempty triples,
mirrored to the left-quotient convention: `(S, T, U)` has the Triple Product
Property iff `Q(T) ∩ Q(U) = {1}` and `Q(S) ∩ Q(T)·Q(U) = {1}`.

The paper states this for *basic* triples (see `IsBasic.tpp_iff`); basicness
is used only to make the three sets nonempty. -/
theorem tripleProductProperty_iff_leftQuot [DecidableEq G] {S T U : Finset G}
    (hS : S.Nonempty) (hT : T.Nonempty) (hU : U.Nonempty) :
    TripleProductProperty S T U ↔
      leftQuot T ∩ leftQuot U = {1} ∧
        leftQuot S ∩ (leftQuot T * leftQuot U) = {1} :=
  ⟨fun h => ⟨leftQuot_inter_TU h hS hT hU, leftQuot_inter_mul h hS hT hU⟩,
    fun h => tripleProductProperty_of_leftQuot h.1 h.2⟩

/-- **Hedtke–Murthy Theorem 3.1** [arXiv:1104.5097], as stated in the paper:
a *basic* triple (`1 ∈ S ∩ T ∩ U`) has the Triple Product Property iff
`Q(T) ∩ Q(U) = {1}` and `Q(S) ∩ Q(T)·Q(U) = {1}`. Combined with the
WLOG-basic reduction `exists_basic_of_tpp`, this makes the TPP
algorithmically testable by set algebra alone; it is the test used by all
GAP/Sage TPP search implementations. -/
theorem IsBasic.tpp_iff [DecidableEq G] {S T U : Finset G}
    (hb : IsBasic S T U) :
    TripleProductProperty S T U ↔
      leftQuot T ∩ leftQuot U = {1} ∧
        leftQuot S ∩ (leftQuot T * leftQuot U) = {1} := by
  obtain ⟨h1S, h1T, h1U⟩ := hb
  exact tripleProductProperty_iff_leftQuot ⟨1, h1S⟩ ⟨1, h1T⟩ ⟨1, h1U⟩

/-! ### The subgroup specialization: the group sieve's tier-0 test -/

/-- The left-quotient set of a subgroup carrier is the carrier itself:
subgroups are closed under `x'⁻¹ * x`, and every `h ∈ H` is the quotient
`1⁻¹ * h`. This is the `Q(H) = H` remark of [arXiv:1104.5097, §2]. -/
private theorem leftQuot_coe_subgroup [Fintype G] [DecidableEq G]
    (H : Subgroup G) [DecidablePred (· ∈ H)] :
    leftQuot (H : Set G).toFinset = (H : Set G).toFinset := by
  ext g
  simp only [mem_leftQuot, Set.mem_toFinset, SetLike.mem_coe]
  constructor
  · rintro ⟨x, hx, x', hx', rfl⟩
    exact H.mul_mem (H.inv_mem hx') hx
  · intro hg
    exact ⟨g, hg, 1, H.one_mem, by rw [inv_one, one_mul]⟩

/-- The carrier finsets of two subgroups intersect in `{1}` iff the subgroups
intersect trivially in the subgroup lattice. -/
private theorem toFinset_inter_toFinset_eq_singleton_iff [Fintype G]
    [DecidableEq G] (K L : Subgroup G) [DecidablePred (· ∈ K)]
    [DecidablePred (· ∈ L)] :
    (K : Set G).toFinset ∩ (L : Set G).toFinset = {1} ↔ K ⊓ L = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall, Finset.ext_iff]
  simp only [Finset.mem_inter, Set.mem_toFinset, SetLike.mem_coe,
    Finset.mem_singleton, Subgroup.mem_inf]
  constructor
  · exact fun hiff x hx => (hiff x).mp hx
  · intro hall x
    exact ⟨fun hx => hall x hx, fun hx => hx ▸ ⟨K.one_mem, L.one_mem⟩⟩

/-- **The computational subgroup TPP test** (Hedtke–Murthy Theorem 3.1
specialized to subgroups, [arXiv:1104.5097]): three subgroups `(H, K, L)`
satisfy the TPP iff `K ⊓ L = ⊥` and the carrier of `H` meets the pointwise
product `K·L` only in the identity. Since `Q(H) = H` for a subgroup
(`leftQuot_coe_subgroup`), both quotient-set conditions of `IsBasic.tpp_iff`
collapse to plain intersection tests.

This is the tier-0 test that TPP search implementations run on subgroup
triples — in this repository, the `tpp_holds_fast` intersection test of the
group sieve (`Scratch/GroupSieve/`), and the GAP subgroup searches of
[arXiv:1104.5097] — in place of the `O(|H|²|K|²|L|²)` definition. -/
theorem subgroupTripleProductProperty_iff [Fintype G] [DecidableEq G]
    {H K L : Subgroup G} [DecidablePred (· ∈ H)] [DecidablePred (· ∈ K)]
    [DecidablePred (· ∈ L)] :
    SubgroupTripleProductProperty H K L ↔
      K ⊓ L = ⊥ ∧
        (H : Set G).toFinset ∩ ((K : Set G).toFinset * (L : Set G).toFinset)
          = {1} := by
  have hb : IsBasic (H : Set G).toFinset (K : Set G).toFinset
      (L : Set G).toFinset :=
    ⟨Set.mem_toFinset.mpr H.one_mem, Set.mem_toFinset.mpr K.one_mem,
      Set.mem_toFinset.mpr L.one_mem⟩
  unfold SubgroupTripleProductProperty
  rw [hb.tpp_iff, leftQuot_coe_subgroup H, leftQuot_coe_subgroup K,
    leftQuot_coe_subgroup L, toFinset_inter_toFinset_eq_singleton_iff K L]

end GroupTPP.HedtkeBasic
