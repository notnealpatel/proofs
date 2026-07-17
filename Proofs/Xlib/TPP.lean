import Mathlib

/-!
# The Triple Product Property and the abelian barrier

This file formalizes the **Triple Product Property** (TPP) of Cohn–Umans
[math/0307321, Definition `definition:realize`], the associated *TPP capacity*
`β(G)` and its subgroup variant `β₀(G)` (Murthy [2512.16730], Defs 2–3), and
the **abelian barrier**: for a commutative group `G`, every TPP triple
`(S, T, U)` satisfies `|S| · |T| · |U| ≤ |G|`, hence `β(G) = |G|`.

The abelian barrier is the foundational negative result of the Cohn–Umans
group-theoretic approach to fast matrix multiplication: it is exactly why the
search for good matrix-multiplication algorithms must use *nonabelian* groups
(CU [math/0307321], pseudo-exponent lemma, CU.tex:478–500; Murthy thesis
[0709.1223], Lemma 4.3 / Corollary 4.4).

## Main definitions

* `Xlib.TPP.TripleProductProperty` — the TPP predicate on `S T U : Finset G`.
* `Xlib.TPP.SubgroupTripleProductProperty` — the TPP on subgroup carriers.
* `Xlib.TPP.tppCapacity` — `β(G)`, the sup of `|S| · |T| · |U|` over TPP triples.
* `Xlib.TPP.stppCapacity` — `β₀(G)`, the same sup over subgroup triples.
* `Xlib.TPP.rho0` — `ρ₀(G) = β₀(G) / |G|`, the subgroup-TPP ratio, as a real.
* `Xlib.TPP.TripleProductPropertyR` — the *right-quotient* TPP
  (`Q(X) = X * X⁻¹`, the Neumann/Hedtke–Murthy convention).

## Main results

* `Xlib.TPP.TripleProductProperty.injOn_mul` — under the TPP in a *commutative*
  group, `(s, t, u) ↦ s * t * u` is injective on `S ×ˢ T ×ˢ U`.
* `Xlib.TPP.card_mul_card_mul_card_le` — the abelian barrier,
  `|S| · |T| · |U| ≤ |G|`.
* `Xlib.TPP.tppCapacity_eq_card` — `β(G) = |G|` for commutative `G`.
* `Xlib.TPP.card_le_tppCapacity` — the trivial lower bound `|G| ≤ β(G)`.
* `Xlib.TPP.stppCapacity_le_tppCapacity` — `β₀(G) ≤ β(G)`.
* `Xlib.TPP.card_inter_ST_le_one` (and `…_TU`, `…_SU`) — Hedtke's pairwise
  intersection bound: two of `S, T, U` meet in ≤ 1 point (third nonempty).
* `Xlib.TPP.card_add_card_add_card_le` — Hedtke's Corollary 6,
  `|S| + |T| + |U| ≤ |G| + 2` for a TPP triple of nonempty subsets.
* `Xlib.TPP.tripleProductPropertyR_iff_inv` — the inversion bridge between the
  two TPP conventions, `TPP_R(S, T, U) ↔ TPP(S⁻¹, T⁻¹, U⁻¹)`; for the *same*
  ordered triple they are **not** equivalent.

## References

* H. Cohn, C. Umans, *A group-theoretic approach to fast matrix
  multiplication*, [arXiv:math/0307321].
* J. Hedtke, *Triple product property triples and ω* [arXiv:1101.5598]; and
  *TPP search algorithms* [arXiv:1104.5097] (disjointness corollaries,
  originally due to Murthy [arXiv:0908.3671]).
* I. Murthy, *Capacity of the triple product property*, [arXiv:2512.16730].
-/

open scoped BigOperators

namespace Xlib.TPP

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-! ### The Triple Product Property -/

/-- The **Triple Product Property** (Cohn–Umans, math/0307321, Def `realize`).

For finsets `S T U : Finset G` in a finite group `G`, the triple `(S, T, U)`
has the TPP when, for all `s s' ∈ S`, `t t' ∈ T`, `u u' ∈ U`,
`s'⁻¹ * s * t'⁻¹ * t * u'⁻¹ * u = 1` forces `s = s'`, `t = t'`, `u = u'`.

Writing `q_S(s, s') = s'⁻¹ * s` for the left quotient, this says the only way
for the product of the three quotient terms to be the identity is for each
quotient to be trivial. (Cohn–Umans phrase the equivalent condition on the
*right* quotient sets `Q(S) = {s₁ s₂⁻¹}`; the element-wise left-quotient form
here is the Murthy/Wikipedia rendering and is what the rest of this file uses.) -/
def TripleProductProperty (S T U : Finset G) : Prop :=
  ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ T, ∀ t' ∈ T, ∀ u ∈ U, ∀ u' ∈ U,
    s'⁻¹ * s * t'⁻¹ * t * u'⁻¹ * u = 1 → s = s' ∧ t = t' ∧ u = u'

/-- The TPP is decidable: its body is a finite nesting of bounded quantifiers
over finsets whose leaves are decidable group equations. -/
instance (S T U : Finset G) : Decidable (TripleProductProperty S T U) := by
  unfold TripleProductProperty; infer_instance

/-! ### The abelian barrier -/

/-- In a commutative group, `s * t * u = s' * t' * u'` rearranges into the TPP
hypothesis `s'⁻¹ * s * t'⁻¹ * t * u'⁻¹ * u = 1`. This is the only place
commutativity is used in the abelian barrier. -/
private theorem prod_eq_imp_quot_eq_one {H : Type*} [CommGroup H]
    (s t u s' t' u' : H) (heq : s * t * u = s' * t' * u') :
    s'⁻¹ * s * t'⁻¹ * t * u'⁻¹ * u = 1 := by
  have key : s'⁻¹ * s * t'⁻¹ * t * u'⁻¹ * u = (s * t * u) * (s' * t' * u')⁻¹ := by
    simp only [mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
  rw [key, heq, mul_inv_cancel]

/-- Under the TPP **in a commutative group**, the map `(s, t, u) ↦ s * t * u`
is injective on `S ×ˢ T ×ˢ U`.

This is the engine of the abelian `β(G) = |G|` barrier
(Cohn–Umans, CU.tex:497; Murthy thesis, Lemma 4.3). Commutativity is what lets
`s * t * u = s' * t' * u'` be rearranged into the TPP hypothesis
`s'⁻¹ * s * t'⁻¹ * t * u'⁻¹ * u = 1`. -/
theorem TripleProductProperty.injOn_mul {H : Type*} [CommGroup H] [Fintype H]
    [DecidableEq H] {S T U : Finset H} (h : TripleProductProperty S T U) :
    Set.InjOn (fun p : H × H × H => p.1 * p.2.1 * p.2.2)
      ((S ×ˢ T ×ˢ U : Finset (H × H × H)) : Set (H × H × H)) := by
  intro p hp q hq heq
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hq
  obtain ⟨hps, hpt, hpu⟩ := hp
  obtain ⟨hqs, hqt, hqu⟩ := hq
  simp only at heq
  have hquot : q.1⁻¹ * p.1 * q.2.1⁻¹ * p.2.1 * q.2.2⁻¹ * p.2.2 = 1 :=
    prod_eq_imp_quot_eq_one p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2 heq
  obtain ⟨h1, h2, h3⟩ :=
    h p.1 hps q.1 hqs p.2.1 hpt q.2.1 hqt p.2.2 hpu q.2.2 hqu hquot
  exact Prod.ext h1 (Prod.ext h2 h3)

/-- **The abelian barrier.** In a commutative group, any TPP triple satisfies
`|S| · |T| · |U| ≤ |G|` (Cohn–Umans, CU.tex:497–499; Murthy thesis, Cor 4.4). -/
theorem card_mul_card_mul_card_le {H : Type*} [CommGroup H] [Fintype H]
    [DecidableEq H] {S T U : Finset H} (h : TripleProductProperty S T U) :
    S.card * T.card * U.card ≤ Fintype.card H := by
  have hcard :
      (S ×ˢ T ×ˢ U : Finset (H × H × H)).card ≤ (Finset.univ : Finset H).card :=
    Finset.card_le_card_of_injOn (fun p => p.1 * p.2.1 * p.2.2)
      (fun _ _ => Finset.mem_univ _) h.injOn_mul
  rw [Finset.card_product, Finset.card_product, ← mul_assoc] at hcard
  simpa using hcard

/-! ### TPP capacity `β(G)` -/

/-- The set of all TPP triples of `G`, as a `Finset` of triples of finsets:
the full powerset cubed, filtered to the TPP. Finite because
`Finset.univ.powerset` is finite. -/
noncomputable def tppTriples (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    Finset (Finset G × Finset G × Finset G) :=
  ((Finset.univ.powerset ×ˢ Finset.univ.powerset ×ˢ Finset.univ.powerset :
      Finset (Finset G × Finset G × Finset G))).filter
    (fun p => TripleProductProperty p.1 p.2.1 p.2.2)

/-- The **TPP capacity** `β(G)` (Murthy 2512.16730, Def 2): the maximum of
`|S| · |T| · |U|` over all TPP triples `(S, T, U)` in `G`. -/
noncomputable def tppCapacity (G : Type*)
    [Group G] [Fintype G] [DecidableEq G] : ℕ :=
  (tppTriples G).sup (fun p => p.1.card * p.2.1.card * p.2.2.card)

/-- Membership in `tppTriples`: a triple is in it iff it satisfies the TPP. -/
theorem mem_tppTriples {S T U : Finset G} :
    (S, T, U) ∈ tppTriples G ↔ TripleProductProperty S T U := by
  simp only [tppTriples, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset,
    Finset.subset_univ, true_and, and_true]

/-- A witnessing TPP triple lower-bounds the capacity. -/
theorem le_tppCapacity {S T U : Finset G} (h : TripleProductProperty S T U) :
    S.card * T.card * U.card ≤ tppCapacity G :=
  Finset.le_sup (f := fun p => p.1.card * p.2.1.card * p.2.2.card)
    (mem_tppTriples.mpr h)

omit [DecidableEq G] in
/-- The trivial triple `(univ, {1}, {1})` satisfies the TPP. -/
theorem tpp_trivial : TripleProductProperty (Finset.univ : Finset G) {1} {1} := by
  intro s _ s' _ t ht t' ht' u hu u' hu' heq
  rw [Finset.mem_singleton] at ht ht' hu hu'
  subst ht ht' hu hu'
  refine ⟨?_, rfl, rfl⟩
  simp only [inv_one, mul_one] at heq
  exact (inv_mul_eq_one.mp heq).symm

/-- **Trivial lower bound:** `|G| ≤ β(G)`, witnessed by `(univ, {1}, {1})`. -/
theorem card_le_tppCapacity : Fintype.card G ≤ tppCapacity G := by
  have h := le_tppCapacity (tpp_trivial (G := G))
  simpa using h

/-- **Abelian capacity barrier:** for a commutative group, `β(G) = |G|`.
This is `ρ(G) = 1`, the reason the matrix-multiplication program needs
nonabelian groups. -/
theorem tppCapacity_eq_card {H : Type*} [CommGroup H] [Fintype H]
    [DecidableEq H] : tppCapacity H = Fintype.card H := by
  refine le_antisymm ?_ card_le_tppCapacity
  refine Finset.sup_le ?_
  rintro ⟨S, T, U⟩ hp
  exact card_mul_card_mul_card_le (mem_tppTriples.mp hp)

/-! ### Subgroup TPP and the subgroup capacity `β₀(G)` -/

/-- The **subgroup Triple Product Property**: the TPP holds for the carrier
finsets of three subgroups `H K L : Subgroup G` (Cohn–Umans, math/0307321,
the special case `Q(H) = H`). -/
def SubgroupTripleProductProperty
    (H K L : Subgroup G)
    [DecidablePred (· ∈ H)] [DecidablePred (· ∈ K)] [DecidablePred (· ∈ L)] :
    Prop :=
  TripleProductProperty (H : Set G).toFinset (K : Set G).toFinset
    (L : Set G).toFinset

open scoped Classical in
/-- The **subgroup TPP capacity** `β₀(G)` (Murthy 2512.16730, Def 3): the
maximum of `|H| · |K| · |L|` over subgroup triples `(H, K, L)` whose carriers
satisfy the TPP. Non-TPP triples contribute `0`. -/
noncomputable def stppCapacity (G : Type*)
    [Group G] [Fintype G] [DecidableEq G] : ℕ :=
  (Finset.univ : Finset (Subgroup G × Subgroup G × Subgroup G)).sup
    (fun p =>
      if TripleProductProperty (p.1 : Set G).toFinset (p.2.1 : Set G).toFinset
          (p.2.2 : Set G).toFinset
      then Nat.card p.1 * Nat.card p.2.1 * Nat.card p.2.2
      else 0)

omit [Fintype G] [DecidableEq G] in
/-- The order of a subgroup equals the cardinality of its carrier finset. -/
private theorem natCard_eq_toFinset_card (H : Subgroup G)
    [Fintype (H : Set G)] :
    Nat.card H = (H : Set G).toFinset.card :=
  Nat.card_eq_card_toFinset (H : Set G)

/-- **`β₀(G) ≤ β(G)`:** every subgroup TPP triple is a TPP triple, so the
subgroup capacity is bounded by the full capacity. -/
theorem stppCapacity_le_tppCapacity : stppCapacity G ≤ tppCapacity G := by
  classical
  refine Finset.sup_le ?_
  rintro ⟨H, K, L⟩ _
  by_cases hTPP : TripleProductProperty (H : Set G).toFinset (K : Set G).toFinset
      (L : Set G).toFinset
  · simp only [hTPP, if_true]
    have hb := le_tppCapacity hTPP
    rwa [← natCard_eq_toFinset_card H, ← natCard_eq_toFinset_card K,
      ← natCard_eq_toFinset_card L] at hb
  · simp only [hTPP, if_false]
    exact Nat.zero_le _

/-! ### The subgroup-TPP ratio `ρ₀(G)` -/

/-- The **subgroup-TPP ratio** `ρ₀(G) = β₀(G) / |G|` (Murthy 2602.15796, eq. `TPPRho0`),
as a real number. -/
noncomputable def rho0 (G : Type*) [Group G] [Fintype G] [DecidableEq G] : ℝ :=
  (stppCapacity G : ℝ) / (Fintype.card G : ℝ)

/-! ### Hedtke disjointness corollaries

The pairwise-intersection bounds of Hedtke [arXiv:1104.5097, Thm 4 / `(***)`]
and the sum bound [Hedtke, Cor 6]. Hedtke's TPP is stated for *nonempty*
subsets, and the intersection statement `S ∩ T = {1}` is for *basic* triples
(`1 ∈ S ∩ T ∩ U`). We first prove the underlying mechanism: each pairwise
intersection has at most one element provided the *third* set is nonempty
(which holds automatically for basic triples). -/

omit [Fintype G] in
/-- If `(S, T, U)` has the TPP and `U` is nonempty, then `S ∩ T` has at most one
element. (Hedtke [1104.5097] Thm 4: setting `s = a, s' = b, t = b, t' = a` and
any common `u`, the TPP forces `a = b`.) -/
theorem card_inter_ST_le_one {S T U : Finset G} (h : TripleProductProperty S T U)
    (hU : U.Nonempty) : (S ∩ T).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_inter] at ha hb
  obtain ⟨haS, haT⟩ := ha
  obtain ⟨hbS, hbT⟩ := hb
  obtain ⟨u₀, hu₀⟩ := hU
  have hquot : b⁻¹ * a * a⁻¹ * b * u₀⁻¹ * u₀ = 1 := by
    group
  exact (h a haS b hbS b hbT a haT u₀ hu₀ u₀ hu₀ hquot).1

omit [Fintype G] in
/-- If `(S, T, U)` has the TPP and `S` is nonempty, then `T ∩ U` has at most one
element. -/
theorem card_inter_TU_le_one {S T U : Finset G} (h : TripleProductProperty S T U)
    (hS : S.Nonempty) : (T ∩ U).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_inter] at ha hb
  obtain ⟨haT, haU⟩ := ha
  obtain ⟨hbT, hbU⟩ := hb
  obtain ⟨s₀, hs₀⟩ := hS
  have hquot : s₀⁻¹ * s₀ * b⁻¹ * a * a⁻¹ * b = 1 := by
    group
  exact (h s₀ hs₀ s₀ hs₀ a haT b hbT b hbU a haU hquot).2.1

omit [Fintype G] in
/-- If `(S, T, U)` has the TPP and `T` is nonempty, then `S ∩ U` has at most one
element. -/
theorem card_inter_SU_le_one {S T U : Finset G} (h : TripleProductProperty S T U)
    (hT : T.Nonempty) : (S ∩ U).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_inter] at ha hb
  obtain ⟨haS, haU⟩ := ha
  obtain ⟨hbS, hbU⟩ := hb
  obtain ⟨t₀, ht₀⟩ := hT
  have hquot : b⁻¹ * a * t₀⁻¹ * t₀ * a⁻¹ * b = 1 := by
    group
  exact (h a haS b hbS t₀ ht₀ t₀ ht₀ b hbU a haU hquot).1

omit [Fintype G] in
/-- **Basic TPP triple intersections** (Hedtke [1104.5097] `(***)`). For a
*basic* TPP triple — one with `1 ∈ S ∩ T ∩ U` — each pairwise intersection is
exactly the trivial subgroup `{1}`. -/
theorem inter_ST_eq_one_of_basic {S T U : Finset G}
    (h : TripleProductProperty S T U) (hS : (1 : G) ∈ S) (hT : (1 : G) ∈ T)
    (hU : (1 : G) ∈ U) : S ∩ T = {1} := by
  rw [Finset.eq_singleton_iff_unique_mem]
  refine ⟨Finset.mem_inter.mpr ⟨hS, hT⟩, ?_⟩
  intro x hx
  have hcard := card_inter_ST_le_one h ⟨1, hU⟩
  rw [Finset.card_le_one] at hcard
  exact hcard x hx 1 (Finset.mem_inter.mpr ⟨hS, hT⟩)

omit [Fintype G] in
/-- For a basic TPP triple, `T ∩ U = {1}`. -/
theorem inter_TU_eq_one_of_basic {S T U : Finset G}
    (h : TripleProductProperty S T U) (hS : (1 : G) ∈ S) (hT : (1 : G) ∈ T)
    (hU : (1 : G) ∈ U) : T ∩ U = {1} := by
  rw [Finset.eq_singleton_iff_unique_mem]
  refine ⟨Finset.mem_inter.mpr ⟨hT, hU⟩, ?_⟩
  intro x hx
  have hcard := card_inter_TU_le_one h ⟨1, hS⟩
  rw [Finset.card_le_one] at hcard
  exact hcard x hx 1 (Finset.mem_inter.mpr ⟨hT, hU⟩)

omit [Fintype G] in
/-- For a basic TPP triple, `S ∩ U = {1}`. -/
theorem inter_SU_eq_one_of_basic {S T U : Finset G}
    (h : TripleProductProperty S T U) (hS : (1 : G) ∈ S) (hT : (1 : G) ∈ T)
    (hU : (1 : G) ∈ U) : S ∩ U = {1} := by
  rw [Finset.eq_singleton_iff_unique_mem]
  refine ⟨Finset.mem_inter.mpr ⟨hS, hU⟩, ?_⟩
  intro x hx
  have hcard := card_inter_SU_le_one h ⟨1, hT⟩
  rw [Finset.card_le_one] at hcard
  exact hcard x hx 1 (Finset.mem_inter.mpr ⟨hS, hU⟩)

/-! ### Quotient sets and Hedtke's sum bound `|S| + |T| + |U| ≤ |G| + 2`

To match the ordering of `TripleProductProperty` (which uses the left quotient
`s'⁻¹ * s`), we work with the **left quotient set** `Q(X) = {x'⁻¹ * x : x, x' ∈ X}`.
Hedtke's Corollary 6 [arXiv:1104.5097] then follows from `|X| ≤ |Q(X)|`, the
pairwise relation `Q(X) ∩ Q(Y) = {1}`, and disjoint counting. -/

/-- The **left quotient set** `Q(X) = {x'⁻¹ * x : x, x' ∈ X}`, as a `Finset`.
This is the quotient set matching the `TripleProductProperty` ordering. -/
def leftQuot (X : Finset G) : Finset G :=
  (X ×ˢ X).image (fun p => p.2⁻¹ * p.1)

omit [Fintype G] in
@[simp] theorem mem_leftQuot {X : Finset G} {g : G} :
    g ∈ leftQuot X ↔ ∃ x ∈ X, ∃ x' ∈ X, x'⁻¹ * x = g := by
  simp only [leftQuot, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨x, x', ⟨hx, hx'⟩, rfl⟩; exact ⟨x, hx, x', hx', rfl⟩
  · rintro ⟨x, hx, x', hx', rfl⟩; exact ⟨x, x', ⟨hx, hx'⟩, rfl⟩

omit [Fintype G] in
/-- The identity lies in every quotient set of a nonempty finset. -/
theorem one_mem_leftQuot {X : Finset G} (hX : X.Nonempty) : (1 : G) ∈ leftQuot X := by
  obtain ⟨x, hx⟩ := hX
  exact mem_leftQuot.mpr ⟨x, hx, x, hx, inv_mul_cancel x⟩

omit [Fintype G] in
/-- Quotient sets are closed under inversion. -/
theorem inv_mem_leftQuot {X : Finset G} {g : G} (hg : g ∈ leftQuot X) :
    g⁻¹ ∈ leftQuot X := by
  obtain ⟨x, hx, x', hx', rfl⟩ := mem_leftQuot.mp hg
  exact mem_leftQuot.mpr ⟨x', hx', x, hx, by group⟩

omit [Fintype G] in
/-- `|X| ≤ |Q(X)|`: for fixed `x₀ ∈ X`, the map `x ↦ x₀⁻¹ * x` injects `X` into
`Q(X)`. -/
theorem card_le_card_leftQuot {X : Finset G} (hX : X.Nonempty) :
    X.card ≤ (leftQuot X).card := by
  obtain ⟨x₀, hx₀⟩ := hX
  have hsub : X.image (fun x => x₀⁻¹ * x) ⊆ leftQuot X := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
    exact mem_leftQuot.mpr ⟨x, hx, x₀, hx₀, rfl⟩
  calc X.card = (X.image (fun x => x₀⁻¹ * x)).card :=
        (Finset.card_image_of_injective X (fun a b h => by simpa using h)).symm
    _ ≤ (leftQuot X).card := Finset.card_le_card hsub

omit [Fintype G] in
/-- **Pairwise quotient intersection** (Hedtke [1104.5097] `(**)`): for a TPP
triple, `Q(S) ∩ Q(T) = {1}` (using `U` nonempty). If `g ∈ Q(S) ∩ Q(T)` then
`g ∈ Q(S)` and `g⁻¹ ∈ Q(T)`, so their product (times a trivial `U`-quotient) is
`1`, and the TPP forces `g = 1`. -/
theorem leftQuot_inter_ST {S T U : Finset G} (h : TripleProductProperty S T U)
    (hS : S.Nonempty) (hT : T.Nonempty) (hU : U.Nonempty) :
    leftQuot S ∩ leftQuot T = {1} := by
  obtain ⟨u₀, hu₀⟩ := hU
  rw [Finset.eq_singleton_iff_unique_mem]
  refine ⟨Finset.mem_inter.mpr ⟨one_mem_leftQuot hS, one_mem_leftQuot hT⟩, ?_⟩
  intro g hg
  rw [Finset.mem_inter] at hg
  obtain ⟨hgS, hgT⟩ := hg
  obtain ⟨s, hs, s', hs', hsg⟩ := mem_leftQuot.mp hgS
  obtain ⟨t, ht, t', ht', htg⟩ := mem_leftQuot.mp (inv_mem_leftQuot hgT)
  have hquot : s'⁻¹ * s * t'⁻¹ * t * u₀⁻¹ * u₀ = 1 := by
    have hreassoc : s'⁻¹ * s * t'⁻¹ * t * u₀⁻¹ * u₀
        = (s'⁻¹ * s) * (t'⁻¹ * t) * (u₀⁻¹ * u₀) := by group
    rw [hreassoc, hsg, htg]; group
  have hss' := (h s hs s' hs' t ht t' ht' u₀ hu₀ u₀ hu₀ hquot).1
  rw [← hsg, hss', inv_mul_cancel]

omit [Fintype G] in
/-- For a TPP triple, `Q(S) ∩ Q(U) = {1}`. -/
theorem leftQuot_inter_SU {S T U : Finset G} (h : TripleProductProperty S T U)
    (hS : S.Nonempty) (hT : T.Nonempty) (hU : U.Nonempty) :
    leftQuot S ∩ leftQuot U = {1} := by
  obtain ⟨t₀, ht₀⟩ := hT
  rw [Finset.eq_singleton_iff_unique_mem]
  refine ⟨Finset.mem_inter.mpr ⟨one_mem_leftQuot hS, one_mem_leftQuot hU⟩, ?_⟩
  intro g hg
  rw [Finset.mem_inter] at hg
  obtain ⟨hgS, hgU⟩ := hg
  obtain ⟨s, hs, s', hs', hsg⟩ := mem_leftQuot.mp hgS
  obtain ⟨u, hu, u', hu', hug⟩ := mem_leftQuot.mp (inv_mem_leftQuot hgU)
  have hquot : s'⁻¹ * s * t₀⁻¹ * t₀ * u'⁻¹ * u = 1 := by
    have hreassoc : s'⁻¹ * s * t₀⁻¹ * t₀ * u'⁻¹ * u
        = (s'⁻¹ * s) * (t₀⁻¹ * t₀) * (u'⁻¹ * u) := by group
    rw [hreassoc, hsg, hug]; group
  have hss' := (h s hs s' hs' t₀ ht₀ t₀ ht₀ u hu u' hu' hquot).1
  rw [← hsg, hss', inv_mul_cancel]

omit [Fintype G] in
/-- For a TPP triple, `Q(T) ∩ Q(U) = {1}`. -/
theorem leftQuot_inter_TU {S T U : Finset G} (h : TripleProductProperty S T U)
    (hS : S.Nonempty) (hT : T.Nonempty) (hU : U.Nonempty) :
    leftQuot T ∩ leftQuot U = {1} := by
  obtain ⟨s₀, hs₀⟩ := hS
  rw [Finset.eq_singleton_iff_unique_mem]
  refine ⟨Finset.mem_inter.mpr ⟨one_mem_leftQuot hT, one_mem_leftQuot hU⟩, ?_⟩
  intro g hg
  rw [Finset.mem_inter] at hg
  obtain ⟨hgT, hgU⟩ := hg
  obtain ⟨t, ht, t', ht', htg⟩ := mem_leftQuot.mp hgT
  obtain ⟨u, hu, u', hu', hug⟩ := mem_leftQuot.mp (inv_mem_leftQuot hgU)
  have hquot : s₀⁻¹ * s₀ * t'⁻¹ * t * u'⁻¹ * u = 1 := by
    have hreassoc : s₀⁻¹ * s₀ * t'⁻¹ * t * u'⁻¹ * u
        = (s₀⁻¹ * s₀) * (t'⁻¹ * t) * (u'⁻¹ * u) := by group
    rw [hreassoc, htg, hug]; group
  have htt' := (h s₀ hs₀ s₀ hs₀ t ht t' ht' u hu u' hu' hquot).2.1
  rw [← htg, htt', inv_mul_cancel]

omit [Fintype G] in
/-- Helper: if `A ∩ B = {1}`, then `A.erase 1` and `B.erase 1` are disjoint. -/
private theorem disjoint_erase_of_inter_eq_one {A B : Finset G}
    (hAB : A ∩ B = {1}) : Disjoint (A.erase 1) (B.erase 1) := by
  rw [Finset.disjoint_left]
  intro x hxA hxB
  rw [Finset.mem_erase] at hxA hxB
  have : x ∈ A ∩ B := Finset.mem_inter.mpr ⟨hxA.2, hxB.2⟩
  rw [hAB, Finset.mem_singleton] at this
  exact hxA.1 this

/-- **Quotient-set sum bound:** `|Q(S)| + |Q(T)| + |Q(U)| ≤ |G| + 2`. The
quotient sets share only the identity pairwise, so their `1`-erasures are
pairwise-disjoint subsets of `univ.erase 1`. -/
theorem card_leftQuot_sum_le {S T U : Finset G} (h : TripleProductProperty S T U)
    (hS : S.Nonempty) (hT : T.Nonempty) (hU : U.Nonempty) :
    (leftQuot S).card + (leftQuot T).card + (leftQuot U).card
      ≤ Fintype.card G + 2 := by
  set A := leftQuot S with hA
  set B := leftQuot T with hB
  set C := leftQuot U with hC
  have h1A : (1 : G) ∈ A := one_mem_leftQuot hS
  have h1B : (1 : G) ∈ B := one_mem_leftQuot hT
  have h1C : (1 : G) ∈ C := one_mem_leftQuot hU
  -- pairwise disjointness of the erasures
  have dAB : Disjoint (A.erase 1) (B.erase 1) :=
    disjoint_erase_of_inter_eq_one (leftQuot_inter_ST h hS hT hU)
  have dAC : Disjoint (A.erase 1) (C.erase 1) :=
    disjoint_erase_of_inter_eq_one (leftQuot_inter_SU h hS hT hU)
  have dBC : Disjoint (B.erase 1) (C.erase 1) :=
    disjoint_erase_of_inter_eq_one (leftQuot_inter_TU h hS hT hU)
  -- the disjoint union of erasures sits inside univ.erase 1
  have hsub : (A.erase 1) ∪ (B.erase 1) ∪ (C.erase 1) ⊆ (Finset.univ : Finset G).erase 1 := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_univ, and_true] at hx ⊢
    rcases hx with (⟨hx, _⟩ | ⟨hx, _⟩) | ⟨hx, _⟩ <;> exact hx
  -- card of the disjoint union is the sum of erasure cards
  have hunion_card :
      ((A.erase 1) ∪ (B.erase 1) ∪ (C.erase 1)).card
        = (A.erase 1).card + (B.erase 1).card + (C.erase 1).card := by
    rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint dAB]
    exact Finset.disjoint_union_left.mpr ⟨dAC, dBC⟩
  -- the union card is bounded by |univ.erase 1| = |G| - 1
  have hbound :
      (A.erase 1).card + (B.erase 1).card + (C.erase 1).card
        ≤ ((Finset.univ : Finset G).erase 1).card := by
    rw [← hunion_card]; exact Finset.card_le_card hsub
  -- convert erasures back via card_erase_add_one (avoiding ℕ subtraction)
  have eA := Finset.card_erase_add_one h1A
  have eB := Finset.card_erase_add_one h1B
  have eC := Finset.card_erase_add_one h1C
  have eUniv := Finset.card_erase_add_one (Finset.mem_univ (1 : G))
  rw [Finset.card_univ] at eUniv
  omega

/-- **Hedtke's Corollary 6** [arXiv:1104.5097]: for a TPP triple of nonempty
subsets, `|S| + |T| + |U| ≤ |G| + 2`. Combines `|X| ≤ |Q(X)|` with the quotient
sum bound. (Attributed to Murthy [0908.3671]; this is the element-count barrier
complementing the product barrier `β(G)`.) -/
theorem card_add_card_add_card_le {S T U : Finset G}
    (h : TripleProductProperty S T U) (hS : S.Nonempty) (hT : T.Nonempty)
    (hU : U.Nonempty) : S.card + T.card + U.card ≤ Fintype.card G + 2 := by
  have hS' := card_le_card_leftQuot hS
  have hT' := card_le_card_leftQuot hT
  have hU' := card_le_card_leftQuot hU
  have hsum := card_leftQuot_sum_le h hS hT hU
  omega

/-! ### The right-quotient TPP and the inversion bridge

`TripleProductProperty` above is the elementwise *left-quotient* convention
(`s'⁻¹ * s`; the Murthy/Wikipedia rendering). The literature also uses the
set-level *right-quotient* convention on `Q_r(X) = X * X⁻¹` (Neumann;
Hedtke–Murthy; `DihedralTPP.IsTPP`), formalized as `TripleProductPropertyR`
below. For the **same** ordered triple the two are **not** equivalent — see
the docstring of `TripleProductPropertyR`. The correct bridge inverts the
sets: `Q_l(X) = X⁻¹ * X = Q_r(X⁻¹)`, so
`TripleProductPropertyR S T U ↔ TripleProductProperty S⁻¹ T⁻¹ U⁻¹`. -/

section RightQuotient

open scoped Pointwise

omit [Fintype G] in
/-- Double inversion of a finset is the identity. (Mathlib has no
`InvolutiveInv (Finset G)` instance, so generic `inv_inv` does not apply;
we record the group case here.) -/
@[simp] theorem finset_inv_inv (X : Finset G) : X⁻¹⁻¹ = X := by
  ext g; simp

omit [Fintype G] in
/-- Membership in the right quotient set `Q_r(X) = X * X⁻¹` (Pointwise), the
right-quotient analogue of `mem_leftQuot`. -/
theorem mem_mul_inv {X : Finset G} {g : G} :
    g ∈ X * X⁻¹ ↔ ∃ x ∈ X, ∃ x' ∈ X, x * x'⁻¹ = g := by
  rw [Finset.mem_mul]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact ⟨y, hy, z⁻¹, Finset.mem_inv'.mp hz, by rw [inv_inv]⟩
  · rintro ⟨x, hx, x', hx', rfl⟩
    exact ⟨x, hx, x'⁻¹, Finset.inv_mem_inv hx', rfl⟩

omit [Fintype G] in
/-- **Quotient-set glue:** the left quotient set is the pointwise product
`X⁻¹ * X = X⁻¹ * (X⁻¹)⁻¹`, i.e. `Q_l(X) = Q_r(X⁻¹)` (see `leftQuot_inv`). -/
theorem leftQuot_eq_inv_mul (X : Finset G) : leftQuot X = X⁻¹ * X := by
  ext g
  rw [mem_leftQuot, Finset.mem_mul]
  constructor
  · rintro ⟨x, hx, x', hx', rfl⟩
    exact ⟨x'⁻¹, Finset.inv_mem_inv hx', x, hx, rfl⟩
  · rintro ⟨y, hy, x, hx, rfl⟩
    exact ⟨x, hx, y⁻¹, Finset.mem_inv'.mp hy, by rw [inv_inv]⟩

omit [Fintype G] in
/-- `Q_r(X) = Q_l(X⁻¹)`: the right quotient set of `X` is the left quotient
set of `X⁻¹`. This is the definitional heart of the inversion bridge. -/
theorem leftQuot_inv (X : Finset G) : leftQuot X⁻¹ = X * X⁻¹ := by
  rw [leftQuot_eq_inv_mul, finset_inv_inv]

omit [Fintype G] in
/-- **Set-level form of the TPP:** `(S, T, U)` has the (left) TPP iff the only
way three left-quotients `q₁ ∈ Q_l(S)`, `q₂ ∈ Q_l(T)`, `q₃ ∈ Q_l(U)` multiply
to `1` is `q₁ = q₂ = q₃ = 1`. The elementwise conclusion `s = s'` matches the
set-level conclusion `q₁ = 1` via `inv_mul_eq_one`. -/
theorem tripleProductProperty_iff_leftQuot {S T U : Finset G} :
    TripleProductProperty S T U ↔
      ∀ q₁ ∈ leftQuot S, ∀ q₂ ∈ leftQuot T, ∀ q₃ ∈ leftQuot U,
        q₁ * q₂ * q₃ = 1 → q₁ = 1 ∧ q₂ = 1 ∧ q₃ = 1 := by
  constructor
  · intro h q₁ hq₁ q₂ hq₂ q₃ hq₃ heq
    obtain ⟨s, hs, s', hs', rfl⟩ := mem_leftQuot.mp hq₁
    obtain ⟨t, ht, t', ht', rfl⟩ := mem_leftQuot.mp hq₂
    obtain ⟨u, hu, u', hu', rfl⟩ := mem_leftQuot.mp hq₃
    have hquot : s'⁻¹ * s * t'⁻¹ * t * u'⁻¹ * u = 1 := by
      have hreassoc : s'⁻¹ * s * t'⁻¹ * t * u'⁻¹ * u
          = s'⁻¹ * s * (t'⁻¹ * t) * (u'⁻¹ * u) := by group
      rw [hreassoc]; exact heq
    obtain ⟨h1, h2, h3⟩ := h s hs s' hs' t ht t' ht' u hu u' hu' hquot
    exact ⟨by rw [h1, inv_mul_cancel], by rw [h2, inv_mul_cancel],
      by rw [h3, inv_mul_cancel]⟩
  · intro h s hs s' hs' t ht t' ht' u hu u' hu' heq
    have h1 : s'⁻¹ * s ∈ leftQuot S := mem_leftQuot.mpr ⟨s, hs, s', hs', rfl⟩
    have h2 : t'⁻¹ * t ∈ leftQuot T := mem_leftQuot.mpr ⟨t, ht, t', ht', rfl⟩
    have h3 : u'⁻¹ * u ∈ leftQuot U := mem_leftQuot.mpr ⟨u, hu, u', hu', rfl⟩
    have heq' : s'⁻¹ * s * (t'⁻¹ * t) * (u'⁻¹ * u) = 1 := by
      have hreassoc : s'⁻¹ * s * (t'⁻¹ * t) * (u'⁻¹ * u)
          = s'⁻¹ * s * t'⁻¹ * t * u'⁻¹ * u := by group
      rw [hreassoc]; exact heq
    obtain ⟨e1, e2, e3⟩ := h _ h1 _ h2 _ h3 heq'
    exact ⟨(inv_mul_eq_one.mp e1).symm, (inv_mul_eq_one.mp e2).symm,
      (inv_mul_eq_one.mp e3).symm⟩

/-- The **right-quotient Triple Product Property**: the set-level TPP on the
right quotient sets `Q_r(X) = X * X⁻¹` (the Neumann/Hedtke–Murthy convention;
syntactically the shape of `DihedralTPP.IsTPP`): whenever `q₁ ∈ S * S⁻¹`,
`q₂ ∈ T * T⁻¹`, `q₃ ∈ U * U⁻¹` multiply to `1`, all three are `1`.

**Warning (same-triple NON-equivalence).** For the *same* ordered triple this
is **not** equivalent to the left-quotient `TripleProductProperty`: an
exhaustive check over all 250,047 nonempty-subset triples of `S₃` finds 1,746
triples satisfying each convention but not the other. Counterexample in `S₃`:
`S = {e}`, `T = {e, (23)}`, `U = {(13), (132)}` is left-TPP but not right-TPP
(right fails via `e · (23) · (23) = 1` with `(23) ∈ Q_r(T)` and
`(23) ∈ Q_r(U)`); the `decide` example below reproduces this in
`DihedralGroup 3 ≅ S₃`. Do not attempt a same-triple equivalence. The correct
bridge inverts the sets (`Q_l(X) = X⁻¹ * X = Q_r(X⁻¹)`):
`TripleProductPropertyR S T U ↔ TripleProductProperty S⁻¹ T⁻¹ U⁻¹`, which is
`tripleProductPropertyR_iff_inv`. -/
def TripleProductPropertyR (S T U : Finset G) : Prop :=
  ∀ q₁ ∈ S * S⁻¹, ∀ q₂ ∈ T * T⁻¹, ∀ q₃ ∈ U * U⁻¹,
    q₁ * q₂ * q₃ = 1 → q₁ = 1 ∧ q₂ = 1 ∧ q₃ = 1

/-- The right-quotient TPP is decidable: bounded quantifiers over the finsets
`X * X⁻¹` with decidable group equations at the leaves. -/
instance (S T U : Finset G) : Decidable (TripleProductPropertyR S T U) := by
  unfold TripleProductPropertyR; infer_instance

omit [Fintype G] in
/-- **The inversion bridge:** the right-quotient TPP for `(S, T, U)` is the
left-quotient TPP for `(S⁻¹, T⁻¹, U⁻¹)`, since `Q_r(X) = Q_l(X⁻¹)`. (For the
*same* triple the two conventions are not equivalent; see the docstring of
`TripleProductPropertyR`.) -/
theorem tripleProductPropertyR_iff_inv {S T U : Finset G} :
    TripleProductPropertyR S T U ↔ TripleProductProperty S⁻¹ T⁻¹ U⁻¹ := by
  unfold TripleProductPropertyR
  rw [tripleProductProperty_iff_leftQuot, leftQuot_inv, leftQuot_inv, leftQuot_inv]

omit [Fintype G] in
/-- Mirror of `tripleProductPropertyR_iff_inv`: the left-quotient TPP for
`(S, T, U)` is the right-quotient TPP for `(S⁻¹, T⁻¹, U⁻¹)`. -/
theorem tripleProductProperty_iff_inv {S T U : Finset G} :
    TripleProductProperty S T U ↔ TripleProductPropertyR S⁻¹ T⁻¹ U⁻¹ := by
  rw [tripleProductPropertyR_iff_inv, finset_inv_inv, finset_inv_inv, finset_inv_inv]

/-- **Capacity transfer:** a right-quotient TPP triple satisfies the same
`tppCapacity` bound, via the inversion bridge (`Finset.card_inv` preserves the
three cardinalities). `β(G)` is therefore convention-independent, and no
separate right-quotient capacity is needed. -/
theorem TripleProductPropertyR.le_tppCapacity {S T U : Finset G}
    (h : TripleProductPropertyR S T U) :
    S.card * T.card * U.card ≤ tppCapacity G := by
  have hb := Xlib.TPP.le_tppCapacity (tripleProductPropertyR_iff_inv.mp h)
  simpa only [Finset.card_inv] using hb

-- The two conventions genuinely differ on the same ordered triple: in
-- `DihedralGroup 3 ≅ S₃` (identity `r 0`), the triple
-- `({r 0}, {r 0, sr 0}, {r 1, sr 1})` is left-TPP but not right-TPP
-- (right fails via `1 * sr 0 * sr 0 = 1` with `sr 0 ∈ Q_r(T) ∩ Q_r(U)`).
example :
    TripleProductProperty
        ({DihedralGroup.r 0} : Finset (DihedralGroup 3))
        {DihedralGroup.r 0, DihedralGroup.sr 0}
        {DihedralGroup.r 1, DihedralGroup.sr 1} ∧
      ¬ TripleProductPropertyR
        ({DihedralGroup.r 0} : Finset (DihedralGroup 3))
        {DihedralGroup.r 0, DihedralGroup.sr 0}
        {DihedralGroup.r 1, DihedralGroup.sr 1} := by
  decide

end RightQuotient

end Xlib.TPP
