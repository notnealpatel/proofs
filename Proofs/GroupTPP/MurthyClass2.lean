import GroupTPP.TPP

/-!
# Murthy's class-2 bound: `ρ₀(G) < √(|G : Z(G)|)`

This file formalizes **Theorem 3.1** of Murthy, *On the triple product property for
subgroups of finite nilpotent groups of class 2* [arXiv:2602.15796]:

> For any group `G` of nilpotency class `2` (nonabelian with `{1} < G' ≤ Z(G) < G`),
> the subgroup-TPP ratio satisfies `ρ₀(G) < √(|G : Z(G)|)`.

Here `ρ₀(G) = β₀(G) / |G|` is `GroupTPP.TPP.rho0`, with `β₀(G) = stppCapacity G` the
subgroup-TPP capacity; both are defined in `GroupTPP.TPP`.

## Foundations note

The paper's nilpotency class `2` (eq. `NilpClassTwo`) is **nonabelian** groups with
`{1} < G' ≤ Z(G) < G`. The strict bound is *false* for abelian `G`: there
`|G : Z(G)| = 1`, `ρ₀ = 1`, and `1 < √1` fails. We therefore take the hypothesis as
`commutator G ≤ Subgroup.center G` **together with** `commutator G ≠ ⊥` (nonabelian).

## Proof strategy

Murthy's proof is **strong induction on `|G|`** (paper lines 472–505). It is *not* a
single coset-counting lemma: three of the four case-leaves descend to a strictly
smaller class-2 section (a subgroup `H < G` or a quotient `G ⧸ N`), and only the
extremal leaf closes directly. A direct (non-inductive) proof is not known.

The strong induction ranges over all finite class-2 groups *of a fixed universe* `u`;
this works because subgroups `↥H` and quotients `G ⧸ N` of `G : Type u` are themselves
`Type u`, so the inductive hypothesis applies to them (see `rho0_lt_sqrt_index_center`).

### Status — **complete and `sorry`-free**

The full strong-induction proof of Theorem 3.1 is formalized with no `sorry`/`admit`.
The supporting results, all proved here, include: the `√`→`ℕ` reduction
(`rho0_lt_sqrt_of_sq_lt`), the trivial lower bound `|G| ≤ β₀(G)` (`card_le_stppCapacity`),
maximal-triple extraction (`exists_maximal_subgroupTPP`), Observation 2.11
(`obs_abelian_normal_product`), **Lemma 3.6** (`rho0_quotient_lt_sqrt_index_center`),
**Lemma 2.10** (`rho0_le_rho0_quotient`, the Neumann quotient), **Proposition 2.7**
(`rho0_le_rho0_subgroup`, the subgroup split), **Corollary 2.13(1)**
(`commutator_not_le_of_maximal`), the abelian barrier (`rho0_le_one_of_isMulCommutative`),
class-2 inheritance by quotients (`isClass2_quotient`) and subgroups (`isClass2_subgroup`,
`comm_le_center_subgroup`), the central-index monotonicities (`index_center_quotient_le`,
`index_center_subgroup_le`), full `S₃` invariance of the subgroup TPP (`subgroupTPP_cyclic`,
`subgroupTPP_swap`), the abelian-join lemma (`isMulCommutative_sup`), and the
normalizer-normality lemma (`normal_of_abelian_sup`).

The inductive step `inductive_step` wires these into the paper's five-leaf case tree
(Leaf 0 `ρ₀ ≤ 1`; Case (ii) central quotient; the WLOG reduction of Case (i); Sub-case A
`⁅S,T⁆ = ⊥`; Case (i.a) `SZ(G)T < G`; and Case (i.b) — the internal semidirect product
`G = SZ(G) ⋊ T`, whose extremal leaf forces `|S| = |T| = |U| = √|G:Z(G)|`).

## References

* I. Murthy, *On the triple product property for subgroups of finite nilpotent groups
  of class 2*, [arXiv:2602.15796], Theorem 3.1.
-/

open scoped BigOperators Pointwise

namespace GroupTPP.MurthyClass2

open GroupTPP.TPP

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-! ### Class-2 hypothesis -/

/-- `G` has **nilpotency class exactly 2**: `{1} < G' ≤ Z(G) < G`, i.e. `G` is
nonabelian (`commutator G ≠ ⊥`) with central commutator subgroup
(`commutator G ≤ center G`). The `Z(G) < G` clause is automatic from nonabelian. -/
structure IsClass2 (G : Type*) [Group G] : Prop where
  comm_le_center : commutator G ≤ Subgroup.center G
  comm_ne_bot : commutator G ≠ ⊥

omit [Fintype G] [DecidableEq G] in
/-- A class-2 group is nonabelian, hence its center is a proper subgroup. -/
theorem IsClass2.center_ne_top (h : IsClass2 G) : Subgroup.center G ≠ ⊤ := by
  intro hc
  apply h.comm_ne_bot
  rw [commutator_eq_bot_iff_center_eq_top]
  exact hc

omit [DecidableEq G] in
/-- In a class-2 group the center has index `> 1`, hence `≥ 2`. -/
theorem IsClass2.one_lt_index_center (h : IsClass2 G) :
    1 < (Subgroup.center G).index :=
  Subgroup.one_lt_index_of_ne_top h.center_ne_top

omit [DecidableEq G] in
/-- In a class-2 group the center has nonzero index. -/
theorem IsClass2.index_center_ne_zero (h : IsClass2 G) :
    (Subgroup.center G).index ≠ 0 := by
  have := h.one_lt_index_center
  omega

/-! ### Reduction of the `√`-bound to a squared `ℕ` inequality

The real-valued goal `ρ₀(G) < √(|G:Z(G)|)` is equivalent to the denominator-cleared
squared inequality `β₀(G)² < |G|² · |G:Z(G)|` over `ℕ`. This lets us keep all the
heavy combinatorics in `ℕ` and lift once at the end with `Real.lt_sqrt_of_sq_lt`. -/

/-- **Reduction lemma.** To prove `ρ₀(G) < √(|G:Z(G)|)` it suffices to prove the
squared natural-number inequality `β₀(G)² < |G|² · |G:Z(G)|`. -/
theorem rho0_lt_sqrt_of_sq_lt
    (h : (stppCapacity G) ^ 2 < (Fintype.card G) ^ 2 * (Subgroup.center G).index) :
    rho0 G < Real.sqrt ((Subgroup.center G).index : ℝ) := by
  have hG : (0 : ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcast : (stppCapacity G : ℝ) ^ 2
      < (Fintype.card G : ℝ) ^ 2 * ((Subgroup.center G).index : ℝ) := by
    exact_mod_cast h
  rw [rho0, Real.lt_sqrt (by positivity), div_pow, div_lt_iff₀ (by positivity)]
  calc (stppCapacity G : ℝ) ^ 2
      < (Fintype.card G : ℝ) ^ 2 * ((Subgroup.center G).index : ℝ) := hcast
    _ = ((Subgroup.center G).index : ℝ) * (Fintype.card G : ℝ) ^ 2 := by ring

/-! ### Extraction of a maximal subgroup-TPP triple

`β₀(G)` is a `Finset.sup` over the (nonempty) finset of all subgroup triples. Since
the trivial triple `(⊤, ⊥, ⊥)` contributes `|G| > 0`, the sup is attained at a triple
that *does* satisfy the TPP, and equals `|S|·|T|·|U|` for that triple. -/

omit [DecidableEq G] in
open scoped Classical in
/-- The carrier finset of the top subgroup is all of `G`. -/
private theorem coe_top_toFinset :
    ((⊤ : Subgroup G) : Set G).toFinset = (Finset.univ : Finset G) := by
  ext x; rw [Set.mem_toFinset]; simp

omit [DecidableEq G] in
open scoped Classical in
/-- The carrier finset of the trivial subgroup is `{1}`. -/
private theorem coe_bot_toFinset :
    ((⊥ : Subgroup G) : Set G).toFinset = ({1} : Finset G) := by
  ext x; rw [Set.mem_toFinset, Finset.mem_singleton]; simp

open scoped Classical in
/-- **Trivial lower bound** `|G| ≤ β₀(G)`, witnessed by the subgroup triple
`(⊤, ⊥, ⊥)` (which has the TPP, since `(univ, {1}, {1})` does). -/
theorem card_le_stppCapacity : Fintype.card G ≤ stppCapacity G := by
  have hTPP : TripleProductProperty ((⊤ : Subgroup G) : Set G).toFinset
      ((⊥ : Subgroup G) : Set G).toFinset ((⊥ : Subgroup G) : Set G).toFinset := by
    rw [coe_top_toFinset, coe_bot_toFinset]; exact tpp_trivial
  have hmem : (⊤, ⊥, ⊥) ∈ (Finset.univ : Finset (Subgroup G × Subgroup G × Subgroup G)) :=
    Finset.mem_univ _
  have hcard : Nat.card (⊤ : Subgroup G) * Nat.card (⊥ : Subgroup G) * Nat.card (⊥ : Subgroup G)
      = Fintype.card G := by simp [Nat.card_eq_fintype_card]
  rw [stppCapacity]
  have hle := Finset.le_sup (f := fun p : Subgroup G × Subgroup G × Subgroup G =>
      if TripleProductProperty (p.1 : Set G).toFinset (p.2.1 : Set G).toFinset
          (p.2.2 : Set G).toFinset
      then Nat.card p.1 * Nat.card p.2.1 * Nat.card p.2.2 else 0) hmem
  simp only [if_pos hTPP] at hle
  rw [hcard] at hle
  exact hle

open scoped Classical in
/-- **Capacity lower bound from a witness.** Any subgroup-TPP triple `(S, T, U)`
lower-bounds `β₀(G)`: `|S|·|T|·|U| ≤ β₀(G)`. (The subgroup analogue of
`GroupTPP.TPP.le_tppCapacity`.) -/
theorem le_stppCapacity {S T U : Subgroup G}
    (hTPP : TripleProductProperty (S : Set G).toFinset (T : Set G).toFinset
      (U : Set G).toFinset) :
    Nat.card S * Nat.card T * Nat.card U ≤ stppCapacity G := by
  have hmem : (S, T, U) ∈ (Finset.univ : Finset (Subgroup G × Subgroup G × Subgroup G)) :=
    Finset.mem_univ _
  rw [stppCapacity]
  have hle := Finset.le_sup (f := fun p : Subgroup G × Subgroup G × Subgroup G =>
      if TripleProductProperty (p.1 : Set G).toFinset (p.2.1 : Set G).toFinset
          (p.2.2 : Set G).toFinset
      then Nat.card p.1 * Nat.card p.2.1 * Nat.card p.2.2 else 0) hmem
  simp only [if_pos hTPP] at hle
  exact hle

open scoped Classical in
/-- The defining `sup` of `β₀(G)` is attained: there is a subgroup TPP triple whose
size equals `β₀(G)`. -/
theorem exists_maximal_subgroupTPP :
    ∃ S T U : Subgroup G,
      TripleProductProperty (S : Set G).toFinset (T : Set G).toFinset (U : Set G).toFinset ∧
      stppCapacity G = Nat.card S * Nat.card T * Nat.card U := by
  obtain ⟨p, _, hp⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ : Finset (Subgroup G × Subgroup G × Subgroup G))
      Finset.univ_nonempty
      (fun p =>
        if TripleProductProperty (p.1 : Set G).toFinset (p.2.1 : Set G).toFinset
            (p.2.2 : Set G).toFinset
        then Nat.card p.1 * Nat.card p.2.1 * Nat.card p.2.2 else 0)
  rw [stppCapacity, hp]
  by_cases hTPP : TripleProductProperty (p.1 : Set G).toFinset (p.2.1 : Set G).toFinset
      (p.2.2 : Set G).toFinset
  · exact ⟨p.1, p.2.1, p.2.2, hTPP, by simp [hTPP]⟩
  · -- The else-branch gives `0`, but the sup is `≥ |G| > 0`; contradiction.
    exfalso
    have hpos : 0 < stppCapacity G := lt_of_lt_of_le Fintype.card_pos card_le_stppCapacity
    rw [stppCapacity, hp] at hpos
    simp only [hTPP, if_false] at hpos
    exact lt_irrefl 0 hpos

/-! ### Supporting lemmas for the induction (Murthy §2–3)

The full proof of Theorem 3.1 is strong induction on `|G|`. It relies on the
following non-inductive results from Murthy's paper. They are stated here with the
signatures the induction consumes; their proofs are substantial standalone tasks
(see the dependency-ordered task list at the end of this file).
-/

omit [Fintype G] [DecidableEq G] in
/-- **Observation 2.11** (`ObsNilpClassTwo`, paper line 292). In a class-2 group, if
`H ∩ Z(G) = ⊥` then `H ⊔ Z(G)` is a normal subgroup with
`|H ⊔ Z(G)| = |H| · |Z(G)|`.

Normality holds because `commutator G ≤ Z(G) ≤ H ⊔ Z(G)`
(`Subgroup.Normal.of_commutator_le`); equivalently, `G ⧸ Z(G)` is abelian so every
subgroup containing `Z(G)` is normal. The cardinality is the disjoint-product count,
proved via `relIndex` Lagrange identities. -/
theorem obs_abelian_normal_product (h : IsClass2 G) {H : Subgroup G}
    (hdisj : H ⊓ Subgroup.center G = ⊥) :
    (H ⊔ Subgroup.center G).Normal ∧
      Nat.card (H ⊔ Subgroup.center G : Subgroup G) =
        Nat.card H * Nat.card (Subgroup.center G) := by
  refine ⟨Subgroup.Normal.of_commutator_le (G := G)
    (le_trans h.comm_le_center le_sup_right), ?_⟩
  set Z := Subgroup.center G with hZ
  have e1 : (⊥ : Subgroup G).relIndex Z * Z.relIndex (Z ⊔ H)
      = (⊥ : Subgroup G).relIndex (Z ⊔ H) :=
    Subgroup.relIndex_mul_relIndex (H := ⊥) (K := Z) (L := Z ⊔ H) bot_le le_sup_left
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left,
    Subgroup.relIndex_sup_left] at e1
  have hZH : Z ⊓ H = ⊥ := by rw [inf_comm]; exact hdisj
  have e2 : Z.relIndex H = Nat.card H := by
    have hbot : Z.subgroupOf H = ⊥ := by rw [← Subgroup.inf_subgroupOf_right, hZH]; simp
    rw [Subgroup.relIndex, hbot, Subgroup.index_bot]
  rw [e2, sup_comm] at e1
  rw [← e1, mul_comm]

/-! ### Subgroup-TPP characterization

For subgroup carriers, the Cohn–Umans TPP (general subset form, as in `GroupTPP.TPP`) is
equivalent to the simpler `s·t·u = 1 ⟹ s = t = u = 1` (paper Definition 2.1). These
two directions are used pervasively by the quotient and split lemmas. -/

omit [DecidableEq G] in
open scoped Classical in
/-- For subgroups, the general TPP yields the `s·t·u = 1 ⟹ s=t=u=1` form. -/
theorem subgroupTPP_stu {S T U : Subgroup G}
    (hTPP : TripleProductProperty (S : Set G).toFinset (T : Set G).toFinset
      (U : Set G).toFinset)
    {s t u : G} (hs : s ∈ S) (ht : t ∈ T) (hu : u ∈ U) (hstu : s * t * u = 1) :
    s = 1 ∧ t = 1 ∧ u = 1 := by
  have h1S : (1 : G) ∈ (S : Set G).toFinset := by rw [Set.mem_toFinset]; exact S.one_mem
  have h1T : (1 : G) ∈ (T : Set G).toFinset := by rw [Set.mem_toFinset]; exact T.one_mem
  have h1U : (1 : G) ∈ (U : Set G).toFinset := by rw [Set.mem_toFinset]; exact U.one_mem
  have hsF : s ∈ (S : Set G).toFinset := by rw [Set.mem_toFinset]; exact hs
  have htF : t ∈ (T : Set G).toFinset := by rw [Set.mem_toFinset]; exact ht
  have huF : u ∈ (U : Set G).toFinset := by rw [Set.mem_toFinset]; exact hu
  have heq : (1:G)⁻¹ * s * (1:G)⁻¹ * t * (1:G)⁻¹ * u = 1 := by
    simp only [inv_one, one_mul, mul_one]; rw [mul_assoc] at hstu ⊢; exact hstu
  exact hTPP s hsF 1 h1S t htF 1 h1T u huF 1 h1U heq

omit [DecidableEq G] in
open scoped Classical in
/-- For subgroups, the `s·t·u = 1 ⟹ s=t=u=1` form yields the general TPP. -/
theorem subgroupTPP_of_stu {S T U : Subgroup G}
    (hstu : ∀ s ∈ S, ∀ t ∈ T, ∀ u ∈ U, s * t * u = 1 → s = 1 ∧ t = 1 ∧ u = 1) :
    TripleProductProperty (S : Set G).toFinset (T : Set G).toFinset (U : Set G).toFinset := by
  intro s hsF s' hs'F t htF t' ht'F u huF u' hu'F heq
  rw [Set.mem_toFinset] at hsF hs'F htF ht'F huF hu'F
  have ha : s'⁻¹ * s ∈ S := S.mul_mem (S.inv_mem hs'F) hsF
  have hb : t'⁻¹ * t ∈ T := T.mul_mem (T.inv_mem ht'F) htF
  have hc : u'⁻¹ * u ∈ U := U.mul_mem (U.inv_mem hu'F) huF
  have habc : (s'⁻¹ * s) * (t'⁻¹ * t) * (u'⁻¹ * u) = 1 := by rw [← heq]; group
  obtain ⟨ea, eb, ec⟩ := hstu _ ha _ hb _ hc habc
  rw [inv_mul_eq_one] at ea eb ec
  exact ⟨ea.symm, eb.symm, ec.symm⟩

omit [DecidableEq G] in
open scoped Classical in
/-- **Cyclic invariance of the subgroup TPP.** If `(S, T, U)` is a subgroup-TPP triple then so
is the cyclic shift `(T, U, S)`. (For the `stu` characterisation, `t·u·s = 1 ⟹ s·t·u = 1` by
left-multiplying by `s` and using `t·u = s⁻¹`.) This is the part of Cohn–Umans Lemma 2.1
needed to choose *which* member to call the distinguished one in the induction. -/
theorem subgroupTPP_cyclic {S T U : Subgroup G}
    (hTPP : TripleProductProperty (S : Set G).toFinset (T : Set G).toFinset
      (U : Set G).toFinset) :
    TripleProductProperty (T : Set G).toFinset (U : Set G).toFinset (S : Set G).toFinset := by
  apply subgroupTPP_of_stu
  intro t ht u hu s hs htus
  have hstu : s * t * u = 1 := by
    have : s * (t * u * s) = s * 1 := by rw [htus]
    calc s * t * u = s * (t * u * s) * s⁻¹ := by group
      _ = s * 1 * s⁻¹ := by rw [htus]
      _ = 1 := by group
  obtain ⟨es, et, eu⟩ := subgroupTPP_stu hTPP hs ht hu hstu
  exact ⟨et, eu, es⟩

omit [DecidableEq G] in
open scoped Classical in
/-- **Transposition invariance of the subgroup TPP.** If `(S, T, U)` is a subgroup-TPP triple
then so is `(S, U, T)`. (Inverting `s·u·t = 1` gives `t⁻¹·u⁻¹·s⁻¹ = 1`, the `stu` form for the
cyclic shift `(T, U, S)`.) Together with `subgroupTPP_cyclic` this yields full `S₃`-invariance,
the rest of Cohn–Umans Lemma 2.1. -/
theorem subgroupTPP_swap {S T U : Subgroup G}
    (hTPP : TripleProductProperty (S : Set G).toFinset (T : Set G).toFinset
      (U : Set G).toFinset) :
    TripleProductProperty (S : Set G).toFinset (U : Set G).toFinset (T : Set G).toFinset := by
  have hTUS : TripleProductProperty (T : Set G).toFinset (U : Set G).toFinset
      (S : Set G).toFinset := subgroupTPP_cyclic hTPP
  apply subgroupTPP_of_stu
  intro s hs u hu t ht hsut
  have hinv : t⁻¹ * u⁻¹ * s⁻¹ = 1 := by
    have : (s * u * t)⁻¹ = 1 := by rw [hsut, inv_one]
    rw [mul_inv_rev, mul_inv_rev] at this
    rw [← this]; group
  obtain ⟨et, eu, es⟩ :=
    subgroupTPP_stu hTUS (T.inv_mem ht) (U.inv_mem hu) (S.inv_mem hs) hinv
  refine ⟨?_, ?_, ?_⟩
  · rw [← inv_inv s, es, inv_one]
  · rw [← inv_inv u, eu, inv_one]
  · rw [← inv_inv t, et, inv_one]

omit [DecidableEq G] in
open scoped Classical in
/-- The image of a subgroup-TPP triple in `G ⧸ N` satisfies the `s·t·u=1` TPP form,
when `N ≤ S`. This is the TPP-lifting half of the Neumann quotient lemma: lifting
`s̄t̄ū = 1` to `s·t·u ∈ N ≤ S`, absorb the `N`-ambiguity into the first member. -/
theorem quotient_subgroupTPP_stu {S T U : Subgroup G}
    (hTPP : TripleProductProperty (S : Set G).toFinset (T : Set G).toFinset
      (U : Set G).toFinset)
    {N : Subgroup G} [N.Normal] (hNS : N ≤ S)
    {x y z : G ⧸ N}
    (hx : x ∈ S.map (QuotientGroup.mk' N)) (hy : y ∈ T.map (QuotientGroup.mk' N))
    (hz : z ∈ U.map (QuotientGroup.mk' N)) (hxyz : x * y * z = 1) :
    x = 1 ∧ y = 1 ∧ z = 1 := by
  rw [Subgroup.mem_map] at hx hy hz
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  obtain ⟨u, hu, rfl⟩ := hz
  simp only [QuotientGroup.mk'_apply] at hxyz ⊢
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff] at hxyz
  have hν : s * t * u ∈ S := hNS hxyz
  have hνs : (s * t * u)⁻¹ * s ∈ S := S.mul_mem (S.inv_mem hν) hs
  have hstu' : ((s * t * u)⁻¹ * s) * t * u = 1 := by group
  obtain ⟨ea, eb, ec⟩ := subgroupTPP_stu hTPP hνs ht hu hstu'
  refine ⟨?_, ?_, ?_⟩
  · rw [QuotientGroup.eq_one_iff]; rw [inv_mul_eq_one] at ea; rw [← ea]; exact hxyz
  · rw [QuotientGroup.eq_one_iff, eb]; exact N.one_mem
  · rw [QuotientGroup.eq_one_iff, ec]; exact N.one_mem

omit [Fintype G] [DecidableEq G] in
/-- Lagrange relative-index identity: `H.relIndex K · |H ⊓ K| = |K|`. (Used by both the
Neumann quotient cardinality and Lemma 3.6.) -/
theorem relIndex_mul_card_inf (H K : Subgroup G) :
    H.relIndex K * Nat.card (H ⊓ K : Subgroup G) = Nat.card K := by
  have h1 : (H.subgroupOf K).index * Nat.card (H.subgroupOf K) = Nat.card K :=
    Subgroup.index_mul_card (H.subgroupOf K)
  have hcard : Nat.card (H.subgroupOf K) = Nat.card (H ⊓ K : Subgroup G) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [Subgroup.relIndex, ← hcard]; exact h1

omit [DecidableEq G] in
/-- In a finite group, a relative index is bounded by the absolute index:
`H.relIndex K ≤ H.index`. (The number of `H`-cosets that `K` meets is at most the total
number of `H`-cosets.) -/
theorem relIndex_le_index (H K : Subgroup G) : H.relIndex K ≤ H.index := by
  have hne : H.relIndex (⊤ : Subgroup G) ≠ 0 := by
    rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite
  calc H.relIndex K ≤ H.relIndex (⊤ : Subgroup G) :=
        Subgroup.relIndex_le_of_le_right le_top hne
    _ = H.index := Subgroup.relIndex_top_right H

omit [DecidableEq G] in
open scoped Classical in
/-- **Pairwise triviality of a subgroup-TPP triple** (subgroup `⊓` form of Hedtke's `(***)`):
the first two members of a subgroup-TPP triple meet trivially, `S ⊓ T = ⊥`. -/
theorem subgroupTPP_inf_ST {S T U : Subgroup G}
    (hTPP : TripleProductProperty (S : Set G).toFinset (T : Set G).toFinset
      (U : Set G).toFinset) :
    S ⊓ T = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxS, hxT⟩ := hx
  have : x = 1 := by
    have hstu : x * x⁻¹ * 1 = 1 := by group
    exact (subgroupTPP_stu hTPP hxS (T.inv_mem hxT) U.one_mem hstu).1
  rw [this]; exact Subgroup.mem_bot.mpr rfl

omit [DecidableEq G] in
open scoped Classical in
/-- For a subgroup-TPP triple, the first and third members meet trivially, `S ⊓ U = ⊥`. -/
theorem subgroupTPP_inf_SU {S T U : Subgroup G}
    (hTPP : TripleProductProperty (S : Set G).toFinset (T : Set G).toFinset
      (U : Set G).toFinset) :
    S ⊓ U = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxS, hxU⟩ := hx
  have : x = 1 := by
    have hstu : x * 1 * x⁻¹ = 1 := by group
    exact (subgroupTPP_stu hTPP hxS T.one_mem (U.inv_mem hxU) hstu).1
  rw [this]; exact Subgroup.mem_bot.mpr rfl

omit [Fintype G] [DecidableEq G] in
open scoped Classical in
/-- The order of the image `S.map (mk' N)` equals the relative index `N.relIndex S`
(`relIndex_ker` specialised to the canonical projection, whose kernel is `N`). -/
theorem card_map_mk'_eq_relIndex (S : Subgroup G) (N : Subgroup G) [N.Normal] :
    Nat.card (S.map (QuotientGroup.mk' N)) = N.relIndex S := by
  have hrel : (QuotientGroup.mk' N).ker.relIndex S = Nat.card (S.map (QuotientGroup.mk' N)) :=
    Subgroup.relIndex_ker (K := S) (QuotientGroup.mk' N)
  rw [QuotientGroup.ker_mk'] at hrel
  exact hrel.symm

open scoped Classical in
/-- **Lemma 2.10** (Neumann quotient lemma, `LemNeuQuoSubTPP`, paper lines 299–333).
If `(S, T, U)` is a subgroup-TPP triple of `G` and `N ⊴ G` with `N ≤ S`, then
`G ⧸ N` realizes a subgroup-TPP triple of size `|S||T||U| / |N|`, so
`ρ₀(G) ≤ ρ₀(G ⧸ N)`.

The TPP of the image triple is `subgroupTPP_of_stu ∘ quotient_subgroupTPP_stu`; the
cardinality bookkeeping (`|S.map| · |N| = |S|` from `N ≤ S`; `|T.map| = |T|`,
`|U.map| = |U|` from `S ⊓ T = S ⊓ U = ⊥`) is the rest. -/
theorem rho0_le_rho0_quotient
    {S T U : Subgroup G}
    (hTPP : TripleProductProperty (S : Set G).toFinset (T : Set G).toFinset
      (U : Set G).toFinset)
    (hmax : stppCapacity G = Nat.card S * Nat.card T * Nat.card U)
    {N : Subgroup G} [N.Normal] (hNS : N ≤ S) :
    rho0 G ≤ rho0 (G ⧸ N) := by
  -- The image triple is a subgroup-TPP triple of `G ⧸ N`.
  have hTPP' : TripleProductProperty
      ((S.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)).toFinset
      ((T.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)).toFinset
      ((U.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)).toFinset := by
    apply subgroupTPP_of_stu
    intro x hx y hy z hz hxyz
    exact quotient_subgroupTPP_stu hTPP hNS
      (Subgroup.mem_map.mpr (by simpa using hx))
      (Subgroup.mem_map.mpr (by simpa using hy))
      (Subgroup.mem_map.mpr (by simpa using hz)) hxyz
  have hcap := le_stppCapacity (G := G ⧸ N) hTPP'
  -- Pairwise-trivial intersections, lifted to `N`.
  have hNT : N ⊓ T = ⊥ := by
    have : N ⊓ T ≤ S ⊓ T := inf_le_inf_right T hNS
    rw [subgroupTPP_inf_ST hTPP] at this
    exact le_bot_iff.mp this
  have hNU : N ⊓ U = ⊥ := by
    have : N ⊓ U ≤ S ⊓ U := inf_le_inf_right U hNS
    rw [subgroupTPP_inf_SU hTPP] at this
    exact le_bot_iff.mp this
  -- Cardinality identities for the three images.
  have hcS : Nat.card (S.map (QuotientGroup.mk' N)) * Nat.card N = Nat.card S := by
    rw [card_map_mk'_eq_relIndex]
    have := relIndex_mul_card_inf N S
    rwa [inf_of_le_left hNS] at this
  have hcT : Nat.card (T.map (QuotientGroup.mk' N)) = Nat.card T := by
    rw [card_map_mk'_eq_relIndex]
    have := relIndex_mul_card_inf N T
    rw [hNT] at this
    simpa using this
  have hcU : Nat.card (U.map (QuotientGroup.mk' N)) = Nat.card U := by
    rw [card_map_mk'_eq_relIndex]
    have := relIndex_mul_card_inf N U
    rw [hNU] at this
    simpa using this
  -- Lagrange for `N` in `G`.
  have hlag : Nat.card (G ⧸ N) * Nat.card N = Nat.card G :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup N).symm
  -- The ℕ-level core: `β₀(G) · |G⧸N| ≤ β₀(G⧸N) · |G|`.
  have hcore : stppCapacity G * Nat.card (G ⧸ N) ≤ stppCapacity (G ⧸ N) * Nat.card G := by
    set s' := Nat.card (S.map (QuotientGroup.mk' N)) with hs'
    set q := Nat.card (G ⧸ N) with hq
    set n := Nat.card N with hn
    calc stppCapacity G * q
        = (Nat.card S * Nat.card T * Nat.card U) * q := by rw [hmax]
      _ = (s' * n * Nat.card T * Nat.card U) * q := by rw [hcS]
      _ = (s' * Nat.card T * Nat.card U) * (q * n) := by ring
      _ ≤ stppCapacity (G ⧸ N) * (q * n) := by
          apply Nat.mul_le_mul_right
          rw [← hcT, ← hcU] at *
          exact hcap
      _ = stppCapacity (G ⧸ N) * Nat.card G := by rw [hlag]
  -- Convert the ℕ inequality to the ℝ statement `ρ₀(G) ≤ ρ₀(G ⧸ N)`.
  rw [rho0, rho0]
  rw [div_le_div_iff₀ (by exact_mod_cast Fintype.card_pos) (by exact_mod_cast Fintype.card_pos)]
  have hcardGr : (Fintype.card G : ℝ) = (Nat.card G : ℝ) := by rw [Nat.card_eq_fintype_card]
  have hcardQr : (Fintype.card (G ⧸ N) : ℝ) = (Nat.card (G ⧸ N) : ℝ) := by
    rw [Nat.card_eq_fintype_card]
  rw [hcardGr, hcardQr]
  have : (stppCapacity G : ℝ) * (Nat.card (G ⧸ N) : ℝ)
      ≤ (stppCapacity (G ⧸ N) : ℝ) * (Nat.card G : ℝ) := by exact_mod_cast hcore
  linarith

omit [Fintype G] [DecidableEq G] in
/-- The image of the center under a quotient map lands in the center of the quotient
(a surjection sends central elements to central elements). -/
theorem map_center_le_center (N : Subgroup G) [N.Normal] :
    (Subgroup.center G).map (QuotientGroup.mk' N) ≤ Subgroup.center (G ⧸ N) := by
  rintro x hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨g, hg, rfl⟩ := hx
  rw [Subgroup.mem_center_iff]
  intro y
  induction y using QuotientGroup.induction_on with
  | _ b =>
    rw [Subgroup.mem_center_iff] at hg
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hg b]

omit [DecidableEq G] in
/-- **Key index inequality** behind Lemma 3.6: passing to a quotient does not increase
the central index, `|(G ⧸ N) : Z(G ⧸ N)| ≤ |G : Z(G)|`.

`|Z(G)| = |Z(G)N/N| · |Z(G) ∩ N| ≤ |Z(G/N)| · |N|` (image-of-center bound +
`Z(G) ∩ N ⊆ N`); combined with `iᴳ·|Z(G)| = |G| = i_{G/N}·|Z(G/N)|·|N|`, cancel
`|Z(G)| > 0`. -/
theorem index_center_quotient_le (N : Subgroup G) [N.Normal] :
    (Subgroup.center (G ⧸ N)).index ≤ (Subgroup.center G).index := by
  set cG := Nat.card (Subgroup.center G) with hcG
  set cQ := Nat.card (Subgroup.center (G ⧸ N)) with hcQ
  set n := Nat.card N with hn
  have hkerN : (QuotientGroup.mk' N).ker = N := QuotientGroup.ker_mk' N
  have step1 : Nat.card ((Subgroup.center G).map (QuotientGroup.mk' N)) *
      Nat.card (N ⊓ Subgroup.center G : Subgroup G) = cG := by
    have hrel : (QuotientGroup.mk' N).ker.relIndex (Subgroup.center G)
        = Nat.card ((Subgroup.center G).map (QuotientGroup.mk' N)) :=
      Subgroup.relIndex_ker (K := Subgroup.center G) (QuotientGroup.mk' N)
    rw [hkerN] at hrel
    have := relIndex_mul_card_inf N (Subgroup.center G)
    rw [hrel] at this
    rw [hcG]; exact this
  have step2 : Nat.card ((Subgroup.center G).map (QuotientGroup.mk' N)) ≤ cQ :=
    Nat.card_mono (Set.toFinite _) (map_center_le_center N)
  have step3 : Nat.card (N ⊓ Subgroup.center G : Subgroup G) ≤ n :=
    Nat.card_mono (Set.toFinite _) inf_le_left
  have key : cG ≤ cQ * n := by rw [← step1]; exact Nat.mul_le_mul step2 step3
  have hiG : (Subgroup.center G).index * cG = Nat.card G :=
    Subgroup.index_mul_card (Subgroup.center G)
  have hiQ : (Subgroup.center (G ⧸ N)).index * cQ = Nat.card (G ⧸ N) :=
    Subgroup.index_mul_card (Subgroup.center (G ⧸ N))
  have hquotcard : Nat.card (G ⧸ N) * n = Nat.card G := by
    rw [hn]; exact (Subgroup.card_eq_card_quotient_mul_card_subgroup N).symm
  have hcombine : (Subgroup.center (G ⧸ N)).index * (cQ * n)
      = (Subgroup.center G).index * cG := by
    rw [← mul_assoc, hiQ, hquotcard, hiG]
  have hcGpos : 0 < cG := by rw [hcG]; exact Nat.card_pos
  have hle : (Subgroup.center (G ⧸ N)).index * cG ≤ (Subgroup.center G).index * cG :=
    calc (Subgroup.center (G ⧸ N)).index * cG
        ≤ (Subgroup.center (G ⧸ N)).index * (cQ * n) := Nat.mul_le_mul_left _ key
      _ = (Subgroup.center G).index * cG := hcombine
  exact Nat.le_of_mul_le_mul_right hle hcGpos

omit [DecidableEq G] in
open scoped Classical in
/-- **Lemma 3.6** (`LemQuoNilpClassTwo`, paper lines 364–372): the `√`-plumbing that
makes the inductive bound on a quotient usable. If `N ⊴ G` and
`ρ₀(G ⧸ N) < √(|(G ⧸ N) : Z(G ⧸ N)|)`, then `ρ₀(G ⧸ N) < √(|G : Z(G)|)`.

Immediate from `index_center_quotient_le` and `√`-monotonicity. -/
theorem rho0_quotient_lt_sqrt_index_center {N : Subgroup G} [N.Normal]
    (hquot : rho0 (G ⧸ N) < Real.sqrt ((Subgroup.center (G ⧸ N)).index : ℝ)) :
    rho0 (G ⧸ N) < Real.sqrt ((Subgroup.center G).index : ℝ) := by
  refine lt_of_lt_of_le hquot ?_
  apply Real.sqrt_le_sqrt
  exact_mod_cast index_center_quotient_le N

omit [DecidableEq G] in
open scoped Classical in
/-- **TPP restriction to a subgroup.** If `(S, T, U)` is a subgroup-TPP triple of `G`, then the
restricted triple `(S.subgroupOf H, T.subgroupOf H, (U ⊓ H).subgroupOf H)` is a subgroup-TPP
triple of `↥H` (for any `H`). This is the "`(S, T, U₀)` is a TPP triple of `H`" step in the
proof of Proposition 2.7; correctness needs no containment hypotheses because membership in
`X.subgroupOf H` already records membership of the underlying element in `X`. -/
theorem subgroupTPP_restrict {S T U : Subgroup G}
    (hTPP : TripleProductProperty (S : Set G).toFinset (T : Set G).toFinset
      (U : Set G).toFinset)
    {H : Subgroup G} :
    TripleProductProperty
      ((S.subgroupOf H : Subgroup H) : Set H).toFinset
      ((T.subgroupOf H : Subgroup H) : Set H).toFinset
      (((U ⊓ H).subgroupOf H : Subgroup H) : Set H).toFinset := by
  apply subgroupTPP_of_stu
  intro s hs t ht u hu hstu
  rw [Subgroup.mem_subgroupOf] at hs ht hu
  have hsG : (s : G) ∈ S := hs
  have htG : (t : G) ∈ T := ht
  have huG : (u : G) ∈ U := (Subgroup.mem_inf.mp hu).1
  have hstuG : (s : G) * (t : G) * (u : G) = 1 := by
    have := congrArg (Subgroup.subtype H) hstu
    simpa using this
  obtain ⟨es, et, eu⟩ := subgroupTPP_stu hTPP hsG htG huG hstuG
  refine ⟨?_, ?_, ?_⟩
  · exact Subtype.ext es
  · exact Subtype.ext et
  · exact Subtype.ext eu

open scoped Classical in
/-- **Proposition 2.7** (subgroup form, `PropTPPSplit`, paper line 268). If a maximal
subgroup-TPP triple `(S, T, U)` of `G` has `S, T ⊆ H` for a subgroup `H`, then
`ρ₀(G) ≤ ρ₀(H)`. -/
theorem rho0_le_rho0_subgroup
    {S T U : Subgroup G}
    (hTPP : TripleProductProperty (S : Set G).toFinset (T : Set G).toFinset
      (U : Set G).toFinset)
    (hmax : stppCapacity G = Nat.card S * Nat.card T * Nat.card U)
    {H : Subgroup G} (hSH : S ≤ H) (hTH : T ≤ H) :
    rho0 G ≤ rho0 H := by
  -- Cardinalities of the restricted subgroups of `↥H`.
  have hcardS : Nat.card (S.subgroupOf H) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv
  have hcardT : Nat.card (T.subgroupOf H) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv
  have hcardU0 : Nat.card ((U ⊓ H).subgroupOf H) = Nat.card (U ⊓ H : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  -- The restricted triple is a TPP triple of `↥H`, so it lower-bounds `β₀(↥H)`.
  have hrestrict := le_stppCapacity (G := H) (subgroupTPP_restrict (H := H) hTPP)
  rw [hcardS, hcardT, hcardU0] at hrestrict
  -- `|U| ≤ [G:H] · |H ⊓ U|`.
  have hUbound : Nat.card U ≤ H.index * Nat.card (H ⊓ U : Subgroup G) := by
    have heq := relIndex_mul_card_inf H U
    calc Nat.card U = H.relIndex U * Nat.card (H ⊓ U : Subgroup G) := heq.symm
      _ ≤ H.index * Nat.card (H ⊓ U : Subgroup G) :=
          Nat.mul_le_mul_right _ (relIndex_le_index H U)
  have hUH : Nat.card (H ⊓ U : Subgroup G) = Nat.card (U ⊓ H : Subgroup G) := by
    rw [inf_comm]
  have hidx : H.index * Nat.card H = Nat.card G := Subgroup.index_mul_card H
  -- The ℕ-level core: `β₀(G) · |H| ≤ β₀(↥H) · |G|`.
  have hcore : stppCapacity G * Nat.card H ≤ stppCapacity (H : Type _) * Nat.card G := by
    calc stppCapacity G * Nat.card H
        = (Nat.card S * Nat.card T * Nat.card U) * Nat.card H := by rw [hmax]
      _ ≤ (Nat.card S * Nat.card T * (H.index * Nat.card (H ⊓ U : Subgroup G))) * Nat.card H := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hUbound)
      _ = (Nat.card S * Nat.card T * Nat.card (U ⊓ H : Subgroup G)) * (H.index * Nat.card H) := by
          rw [hUH]; ring
      _ = (Nat.card S * Nat.card T * Nat.card (U ⊓ H : Subgroup G)) * Nat.card G := by rw [hidx]
      _ ≤ stppCapacity (H : Type _) * Nat.card G := Nat.mul_le_mul_right _ hrestrict
  -- Convert the ℕ inequality to the ℝ statement `ρ₀(G) ≤ ρ₀(H)`.
  rw [rho0, rho0]
  rw [div_le_div_iff₀ (by exact_mod_cast Fintype.card_pos) (by exact_mod_cast Fintype.card_pos)]
  have hcardGr : (Fintype.card G : ℝ) = (Nat.card G : ℝ) := by
    rw [Nat.card_eq_fintype_card]
  have hcardHr : (Fintype.card H : ℝ) = (Nat.card H : ℝ) := by
    rw [Nat.card_eq_fintype_card]
  rw [hcardGr, hcardHr]
  have : (stppCapacity G : ℝ) * (Nat.card H : ℝ)
      ≤ (stppCapacity (H : Type _) : ℝ) * (Nat.card G : ℝ) := by exact_mod_cast hcore
  linarith

omit [Fintype G] [DecidableEq G] in
/-- The commutator subgroup of a quotient is the image of the commutator subgroup:
`commutator (G ⧸ N) = (commutator G).map (mk' N)`. (The projection is surjective, so its
range is `⊤`.) -/
theorem commutator_map_mk' (N : Subgroup G) [N.Normal] :
    commutator (G ⧸ N) = (commutator G).map (QuotientGroup.mk' N) := by
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N),
    ← commutator_def]

omit [Fintype G] [DecidableEq G] in
/-- **Class-2 is inherited by quotients** by a central subgroup not swallowing the commutator.
If `IsClass2 G`, `N ≤ Z(G)` and `commutator G ⊄ N`, then `IsClass2 (G ⧸ N)`. -/
theorem isClass2_quotient (h : IsClass2 G) {N : Subgroup G} [N.Normal]
    (hNcomm : ¬ commutator G ≤ N) :
    IsClass2 (G ⧸ N) where
  comm_le_center := by
    rw [commutator_map_mk']
    exact le_trans (Subgroup.map_mono h.comm_le_center) (map_center_le_center N)
  comm_ne_bot := by
    rw [commutator_map_mk']
    intro hbot
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    exact hNcomm hbot

open scoped Classical in
/-- **Abelian barrier for `ρ₀`** (Theorem `ThmRhoAbelianGroups`, paper line 198): a
commutative (`IsMulCommutative`) finite group has `ρ₀ ≤ 1`, equivalently `β₀ = |G|`.
Reduces to `GroupTPP.TPP.tppCapacity_eq_card` via a local `CommGroup` instance. -/
theorem rho0_le_one_of_isMulCommutative {H : Type*} [Group H] [Fintype H] [DecidableEq H]
    [hc : IsMulCommutative H] : rho0 H ≤ 1 := by
  letI : CommGroup H := { (inferInstance : Group H) with mul_comm := hc.is_comm.comm }
  have hcap : stppCapacity H ≤ Fintype.card H :=
    le_trans stppCapacity_le_tppCapacity (le_of_eq tppCapacity_eq_card)
  rw [rho0, div_le_one (by exact_mod_cast Fintype.card_pos)]
  exact_mod_cast hcap

omit [DecidableEq G] in
/-- In a class-2 group, `1 < √(|G : Z(G)|)`. (The center index is `≥ 2`.) -/
theorem one_lt_sqrt_index_center (h : IsClass2 G) :
    1 < Real.sqrt ((Subgroup.center G).index : ℝ) := by
  rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
  apply Real.sqrt_lt_sqrt (by norm_num)
  have := h.one_lt_index_center
  exact_mod_cast this

/-- **The `ρ₀ ≤ 1` leaf.** If the maximal subgroup-TPP capacity does not exceed `|G|`
(i.e. `ρ₀(G) ≤ 1`), then in a class-2 group `ρ₀(G) < √(|G : Z(G)|)`, because the bound
is `> 1`. -/
theorem rho0_lt_sqrt_of_le_card (h : IsClass2 G)
    (hle : stppCapacity G ≤ Fintype.card G) :
    rho0 G < Real.sqrt ((Subgroup.center G).index : ℝ) := by
  have hrho : rho0 G ≤ 1 := by
    rw [rho0, div_le_one (by exact_mod_cast Fintype.card_pos)]
    exact_mod_cast hle
  exact lt_of_le_of_lt hrho (one_lt_sqrt_index_center h)

omit [Fintype G] [DecidableEq G] in
/-- A central element of `G` lying in `H` is central in `H`:
`(center G).subgroupOf H ≤ center ↥H`. -/
theorem center_subgroupOf_le_center (H : Subgroup G) :
    (Subgroup.center G).subgroupOf H ≤ Subgroup.center (H : Subgroup G) := by
  intro x hx
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_center_iff] at hx
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (hx (y : G))

omit [DecidableEq G] in
/-- **Subgroup central-index monotonicity** (subgroup analogue of `index_center_quotient_le`,
needed for case (i.a) of Theorem 3.1). If `Z(G) ≤ H` then `|↥H : Z(↥H)| ≤ |G : Z(G)|`.

From `|H| ≤ |G|` and `|Z(G)| ≤ |Z(↥H)|` (a central element in `H` is `H`-central), via the
two Lagrange identities `index · |center| = |group|`. -/
theorem index_center_subgroup_le {H : Subgroup G} (hZH : Subgroup.center G ≤ H) :
    (Subgroup.center (H : Subgroup G)).index ≤ (Subgroup.center G).index := by
  set cG := Nat.card (Subgroup.center G) with hcG
  set cH := Nat.card (Subgroup.center (H : Subgroup G)) with hcH
  -- `|Z(G)| ≤ |Z(↥H)|`.
  have hZcard : cG ≤ cH := by
    have h1 : Nat.card ((Subgroup.center G).subgroupOf H) = cG :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZH).toEquiv
    rw [hcH, ← h1]
    exact Subgroup.card_le_of_le (center_subgroupOf_le_center H)
  -- `|H| ≤ |G|`.
  have hHcard : Nat.card (H : Subgroup G) ≤ Nat.card G := by
    have := Subgroup.card_le_of_le (le_top : H ≤ ⊤)
    rwa [Nat.card_congr Subgroup.topEquiv.toEquiv] at this
  -- Lagrange.
  have hiH : (Subgroup.center (H : Subgroup G)).index * cH = Nat.card (H : Subgroup G) :=
    Subgroup.index_mul_card (Subgroup.center (H : Subgroup G))
  have hiG : (Subgroup.center G).index * cG = Nat.card G :=
    Subgroup.index_mul_card (Subgroup.center G)
  have hcGpos : 0 < cG := by rw [hcG]; exact Nat.card_pos
  -- `index(↥H) · cG ≤ index(↥H) · cH = |H| ≤ |G| = index(G) · cG`.
  have hle : (Subgroup.center (H : Subgroup G)).index * cG ≤ (Subgroup.center G).index * cG :=
    calc (Subgroup.center (H : Subgroup G)).index * cG
        ≤ (Subgroup.center (H : Subgroup G)).index * cH := Nat.mul_le_mul_left _ hZcard
      _ = Nat.card (H : Subgroup G) := hiH
      _ ≤ Nat.card G := hHcard
      _ = (Subgroup.center G).index * cG := hiG.symm
  exact Nat.le_of_mul_le_mul_right hle hcGpos

open scoped Classical in
/-- **Corollary 2.13(1)** (`Corr2LemNeuQuoSubTPP`, paper line 329): a member of a *non-trivial*
maximal subgroup-TPP triple cannot contain the commutator subgroup. If `commutator G ≤ S`,
quotienting by `commutator G` (Lemma 2.10) lands in the abelian `G ⧸ G'`, forcing
`ρ₀(G) ≤ ρ₀(G ⧸ G') ≤ 1`, contradicting non-triviality `ρ₀(G) > 1`. -/
theorem commutator_not_le_of_maximal (_h : IsClass2 G)
    {S T U : Subgroup G}
    (hTPP : TripleProductProperty (S : Set G).toFinset (T : Set G).toFinset
      (U : Set G).toFinset)
    (hmax : stppCapacity G = Nat.card S * Nat.card T * Nat.card U)
    (hnontriv : Fintype.card G < stppCapacity G)
    (hcomm : commutator G ≤ S) : False := by
  have hquot : rho0 G ≤ rho0 (G ⧸ commutator G) :=
    rho0_le_rho0_quotient hTPP hmax hcomm
  have hcommut : IsMulCommutative (G ⧸ commutator G) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).mpr le_rfl
  have hone : rho0 (G ⧸ commutator G) ≤ 1 := rho0_le_one_of_isMulCommutative
  have hgt : (1 : ℝ) < rho0 G := by
    rw [rho0, lt_div_iff₀ (by exact_mod_cast Fintype.card_pos), one_mul]
    exact_mod_cast hnontriv
  linarith

open scoped Classical in
/-- **The quotient leaf** (shared by case ii and case i.b-`N>1` of Theorem 3.1). Given the
inductive hypothesis `IH`, a maximal subgroup-TPP triple `(S, T, U)`, and a nontrivial normal
subgroup `N ≤ S` with `commutator G ⊄ N`, the bound `ρ₀(G) < √(|G : Z(G)|)` holds.

`G ⧸ N` is class-2 of strictly smaller order, so `IH` plus `rho0_quotient_lt_sqrt_index_center`
gives `ρ₀(G ⧸ N) < √(|G:Z(G)|)`, and `rho0_le_rho0_quotient` gives `ρ₀(G) ≤ ρ₀(G ⧸ N)`. The
type universe `w` is held fixed so the inductive hypothesis applies to `G ⧸ N : Type w`. -/
theorem quotient_leaf.{v} {w : Type v} {u : ℕ} [Group w] [Fintype w] [DecidableEq w]
    (IH : ∀ m < u, ∀ (G' : Type v) [Group G'] [Fintype G'] [DecidableEq G'],
      Nat.card G' = m → IsClass2 G' → rho0 G' < Real.sqrt ((Subgroup.center G').index : ℝ))
    (hcard : Nat.card w = u) (h : IsClass2 w)
    {S T U : Subgroup w}
    (hTPP : TripleProductProperty (S : Set w).toFinset (T : Set w).toFinset
      (U : Set w).toFinset)
    (hmax : stppCapacity w = Nat.card S * Nat.card T * Nat.card U)
    {N : Subgroup w} [N.Normal] (hNS : N ≤ S) (hNbot : N ≠ ⊥)
    (hNcomm : ¬ commutator w ≤ N) :
    rho0 w < Real.sqrt ((Subgroup.center w).index : ℝ) := by
  have hclass2Q : IsClass2 (w ⧸ N) := isClass2_quotient h hNcomm
  -- `|w ⧸ N| < |w| = u`.
  have hNcard : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot (H := N)).mpr hNbot
  have hlag : Nat.card (w ⧸ N) * Nat.card N = Nat.card w :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup N).symm
  have hlt : Nat.card (w ⧸ N) < u := by
    rw [← hcard]
    nlinarith [hlag, hNcard, Nat.card_pos (α := w ⧸ N)]
  -- Inductive hypothesis on the quotient, lifted to `|w : Z(w)|`.
  have hIH : rho0 (w ⧸ N) < Real.sqrt ((Subgroup.center (w ⧸ N)).index : ℝ) :=
    IH (Nat.card (w ⧸ N)) hlt (w ⧸ N) rfl hclass2Q
  have hlift : rho0 (w ⧸ N) < Real.sqrt ((Subgroup.center w).index : ℝ) :=
    rho0_quotient_lt_sqrt_index_center hIH
  exact lt_of_le_of_lt (rho0_le_rho0_quotient hTPP hmax hNS) hlift

omit [Fintype G] [DecidableEq G] in
/-- **Class-2 restricts to subgroups (commutator-central half).** For any subgroup `H` of a
class-2 group, `commutator ↥H ≤ center ↥H`: a commutator of `H`-elements is a `G`-commutator,
hence central in `G`, hence central in `H`. (The full `IsClass2 ↥H` additionally needs
`H` nonabelian, which is *not* automatic and is where Proposition 2.6 enters.) -/
theorem comm_le_center_subgroup (h : IsClass2 G) (H : Subgroup G) :
    commutator (H : Subgroup G) ≤ Subgroup.center (H : Subgroup G) := by
  intro x hx
  have hxG : (H.subtype x : G) ∈ commutator G := by
    have : (H.subtype x) ∈ (commutator (H : Subgroup G)).map H.subtype :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [Subgroup.map_subtype_commutator] at this
    have hle : ⁅H, H⁆ ≤ commutator G := by
      rw [commutator_def]; exact Subgroup.commutator_mono le_top le_top
    exact hle this
  have hxC : (x : G) ∈ Subgroup.center G := h.comm_le_center hxG
  rw [Subgroup.mem_center_iff] at hxC ⊢
  intro y
  exact Subtype.ext (hxC (y : G))

omit [Fintype G] [DecidableEq G] in
/-- `⁅S, S⁆ ≤ commutator G`: the commutator subgroup of a subgroup `S` of `G`, viewed in `G`,
sits inside the ambient commutator subgroup. -/
theorem commutatorSubgroup_le_commutator (S : Subgroup G) : ⁅S, S⁆ ≤ commutator G := by
  rw [commutator_def]; exact Subgroup.commutator_mono le_top le_top

omit [Fintype G] [DecidableEq G] in
/-- **Observation 2.11 abelian half.** In a class-2 group, a subgroup `S` meeting the center
trivially is abelian: `⁅S, S⁆ ≤ S ⊓ commutator G ≤ S ⊓ Z(G) = ⊥`. -/
theorem isMulCommutative_of_inf_center_bot (h : IsClass2 G) {S : Subgroup G}
    (hS : S ⊓ Subgroup.center G = ⊥) : IsMulCommutative (S : Subgroup G) := by
  have hSS : ⁅S, S⁆ = ⊥ := by
    rw [eq_bot_iff, ← hS]
    refine le_inf (Subgroup.commutator_le_self S) ?_
    exact le_trans (commutatorSubgroup_le_commutator S) h.comm_le_center
  -- `commutator ↥S = ⊥` since its image under the injective `subtype` is `⁅S,S⁆ = ⊥`.
  have hcomm : commutator (S : Subgroup G) = ⊥ := by
    have hmap : (commutator (S : Subgroup G)).map S.subtype = ⊥ := by
      rw [Subgroup.map_subtype_commutator, hSS]
    rwa [Subgroup.map_eq_bot_iff, Subgroup.ker_subtype, le_bot_iff] at hmap
  exact (commutator_eq_bot_iff (G := (S : Subgroup G))).mp hcomm

omit [Fintype G] [DecidableEq G] in
/-- **The join of two commuting abelian subgroups is abelian.** If `↥S` and `↥T` are abelian and
`⁅S, T⁆ = ⊥` (they centralise each other), then `↥(S ⊔ T)` is abelian. (Via the centraliser
characterisation `K ≤ centralizer K ↔ IsMulCommutative K`.) -/
theorem isMulCommutative_sup {S T : Subgroup G} (hS : IsMulCommutative (S : Subgroup G))
    (hT : IsMulCommutative (T : Subgroup G)) (hST : ⁅S, T⁆ = ⊥) :
    IsMulCommutative (↥(S ⊔ T)) := by
  rw [← Subgroup.le_centralizer_iff_isMulCommutative]
  have hSc : S ≤ Subgroup.centralizer (S : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hS
  have hTc : T ≤ Subgroup.centralizer (T : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hT
  have hST' : S ≤ Subgroup.centralizer (T : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hST
  have hTS' : T ≤ Subgroup.centralizer (S : Set G) :=
    Subgroup.le_centralizer_iff.mp hST'
  -- `S ⊔ T ≤ centralizer S` and `≤ centralizer T`.
  have h1 : S ⊔ T ≤ Subgroup.centralizer (S : Set G) := sup_le hSc hTS'
  have h2 : S ⊔ T ≤ Subgroup.centralizer (T : Set G) := sup_le hST' hTc
  refine sup_le ?_ ?_
  · exact Subgroup.le_centralizer_iff.mpr h1
  · exact Subgroup.le_centralizer_iff.mpr h2

omit [Fintype G] [DecidableEq G] in
/-- **Class-2 is inherited by a subgroup that makes two non-commuting members generate it.**
If `IsClass2 G`, `⁅S, T⁆ ≠ ⊥`, and `S, T ≤ H`, then `IsClass2 ↥H`. The commutator-central half
is `comm_le_center_subgroup`; nonabelianness follows since `⁅S,T⁆ ≤ ⁅H,H⁆`, the image of
`commutator ↥H` under the subtype, so `commutator ↥H = ⊥` would force `⁅S,T⁆ = ⊥`. -/
theorem isClass2_subgroup (h : IsClass2 G) {S T H : Subgroup G} (hST : ⁅S, T⁆ ≠ ⊥)
    (hSH : S ≤ H) (hTH : T ≤ H) : IsClass2 (H : Subgroup G) where
  comm_le_center := comm_le_center_subgroup h H
  comm_ne_bot := by
    intro hbot
    apply hST
    have himg : (commutator (H : Subgroup G)).map H.subtype = ⁅H, H⁆ :=
      Subgroup.map_subtype_commutator H
    rw [hbot, Subgroup.map_bot] at himg
    rw [eq_bot_iff]
    calc ⁅S, T⁆ ≤ ⁅H, H⁆ := Subgroup.commutator_mono hSH hTH
      _ = ⊥ := himg.symm

omit [Fintype G] [DecidableEq G] in
/-- Any subgroup commutes with the center: `⁅S, Z(G)⁆ = ⊥`. -/
theorem commutator_center_eq_bot (S : Subgroup G) : ⁅S, Subgroup.center G⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro s _ z hz
  rw [SetLike.mem_coe, Subgroup.mem_center_iff] at hz
  exact (hz s).symm

omit [Fintype G] [DecidableEq G] in
/-- An abelian subgroup `A` normalises every subgroup it contains: if `IsMulCommutative ↥A`
and `N ≤ A` then `A ≤ normalizer N`. (Every `a ∈ A` commutes with every `n ∈ N ≤ A`.) -/
theorem le_normalizer_of_le_isMulCommutative {A N : Subgroup G}
    (hA : IsMulCommutative (A : Subgroup G)) (hNA : N ≤ A) :
    A ≤ Subgroup.normalizer (N : Set G) := by
  haveI : IsMulCommutative (A : Subgroup G) := hA
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hcomm : a * x = x * a := setLike_mul_comm ha (hNA hx)
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]; exact hx
  · intro hx
    -- `a⁻¹ * (a x a⁻¹) * a = x`, and `a⁻¹ ∈ A` commutes with `a x a⁻¹ ∈ N`.
    have hax : a * x * a⁻¹ ∈ N := hx
    have hcomm : a⁻¹ * (a * x * a⁻¹) = (a * x * a⁻¹) * a⁻¹ :=
      setLike_mul_comm (A.inv_mem ha) (hNA hax)
    have hxeq : x = a⁻¹ * (a * x * a⁻¹) * a := by group
    rw [hxeq, hcomm]
    have hsimp : a * x * a⁻¹ * a⁻¹ * a = a * x * a⁻¹ := by group
    rw [hsimp]; exact hx

omit [Fintype G] [DecidableEq G] in
/-- **Normality from two abelian subgroups generating the group.** If `↥A`, `↥B` are abelian,
`A ⊔ B = ⊤`, and `N ≤ A`, `N ≤ B`, then `N` is normal in `G`. (Both `A` and `B` normalise `N`,
so `N.normalizer ⊇ A ⊔ B = ⊤`.) -/
theorem normal_of_abelian_sup {A B N : Subgroup G}
    (hA : IsMulCommutative (A : Subgroup G)) (hB : IsMulCommutative (B : Subgroup G))
    (hAB : A ⊔ B = ⊤) (hNA : N ≤ A) (hNB : N ≤ B) : N.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hAB]
  exact sup_le (le_normalizer_of_le_isMulCommutative hA hNA)
    (le_normalizer_of_le_isMulCommutative hB hNB)

omit [Fintype G] [DecidableEq G] in
/-- A subgroup contained in the center is normal (conjugation fixes central elements). -/
theorem normal_of_le_center {K : Subgroup G} (hK : K ≤ Subgroup.center G) : K.Normal where
  conj_mem n hn g := by
    have hc := hK hn
    rw [Subgroup.mem_center_iff] at hc
    rw [hc g, mul_assoc, mul_inv_cancel, mul_one]
    exact hn

/-- **Inductive step of Theorem 3.1.** Given the inductive hypothesis `IH` — that the
bound holds for every class-2 group of the same universe with strictly smaller order —
the bound holds for `G`. The proof extracts a maximal subgroup-TPP triple `(S, T, U)`
and case-splits on `S₀ = S ∩ Z(G)` (paper lines 487–505):

* `ρ₀(G) ≤ 1`: immediate, since `1 < √|G:Z(G)|` (the center index is `≥ 2`).
* `S ∩ Z(G) > ⊥` (case ii): quotient by `S₀` via `rho0_le_rho0_quotient`, then
  `IH` on `G ⧸ S₀` and `rho0_quotient_lt_sqrt_index_center`.
* `S ∩ Z(G) = ⊥`, `H = SZ(G)T < G` (case i.a): `rho0_le_rho0_subgroup` + `IH` on `H`
  (`H` is class-2 with `|Z(H)| ≥ |Z(G)|`).
* `S ∩ Z(G) = ⊥`, `H = G`, `N = SZ(G) ∩ T > ⊥` (case i.b, N>1): quotient by `N`.
* `S ∩ Z(G) = ⊥`, `H = G`, `N = ⊥` (case i.b, extremal): direct computation
  `|S| = |T| = |U| = √|G:Z(G)|`, giving `ρ₀(G) = √|G:Z(G)| / |Z(G)| < √|G:Z(G)|`. -/
theorem inductive_step.{v} {u : ℕ}
    (IH : ∀ m < u, ∀ (G' : Type v) [Group G'] [Fintype G'] [DecidableEq G'],
      Nat.card G' = m → IsClass2 G' → rho0 G' < Real.sqrt ((Subgroup.center G').index : ℝ))
    (G : Type v) [Group G] [Fintype G] [DecidableEq G] (hcard : Nat.card G = u)
    (h : IsClass2 G) :
    rho0 G < Real.sqrt ((Subgroup.center G).index : ℝ) := by
  classical
  -- **Leaf 0: `ρ₀(G) ≤ 1`.** If the capacity does not exceed `|G|`, the bound `> 1` closes it.
  by_cases htriv : stppCapacity G ≤ Fintype.card G
  · exact rho0_lt_sqrt_of_le_card h htriv
  rw [not_le] at htriv
  -- Otherwise the maximal triple is non-trivial: `ρ₀(G) > 1`.
  -- Extract a maximal subgroup-TPP triple `(S, T, U)` with `β₀(G) = |S||T||U|`.
  obtain ⟨S, T, U, hTPP, hmax⟩ := exists_maximal_subgroupTPP (G := G)
  -- Corollary 2.13: no member contains the commutator subgroup.
  have hSnc : ¬ commutator G ≤ S := fun hc =>
    commutator_not_le_of_maximal h hTPP hmax htriv hc
  -- **Case split on `S₀ = S ⊓ Z(G)`.**
  -- The two cyclic shifts of the maximal triple are also maximal subgroup-TPP triples.
  have hTPP_TUS : TripleProductProperty (T : Set G).toFinset (U : Set G).toFinset
      (S : Set G).toFinset := subgroupTPP_cyclic hTPP
  have hTPP_UST : TripleProductProperty (U : Set G).toFinset (S : Set G).toFinset
      (T : Set G).toFinset := subgroupTPP_cyclic hTPP_TUS
  have hmax_TUS : stppCapacity G = Nat.card T * Nat.card U * Nat.card S := by rw [hmax]; ring
  have hmax_UST : stppCapacity G = Nat.card U * Nat.card S * Nat.card T := by rw [hmax]; ring
  -- Corollary 2.13 for all three members.
  have hTnc : ¬ commutator G ≤ T := fun hc =>
    commutator_not_le_of_maximal h hTPP_TUS hmax_TUS htriv hc
  have hUnc : ¬ commutator G ≤ U := fun hc =>
    commutator_not_le_of_maximal h hTPP_UST hmax_UST htriv hc
  -- Local closer for the "member `X` meets the centre nontrivially" branch: quotient by the
  -- central `X ⊓ Z(G)` using the appropriately-cyclically-permuted triple.
  have central_branch : ∀ {X Y Z : Subgroup G},
      TripleProductProperty (X : Set G).toFinset (Y : Set G).toFinset (Z : Set G).toFinset →
      stppCapacity G = Nat.card X * Nat.card Y * Nat.card Z →
      ¬ commutator G ≤ X → X ⊓ Subgroup.center G ≠ ⊥ →
      rho0 G < Real.sqrt ((Subgroup.center G).index : ℝ) := by
    intro X Y Z hXYZ hmaxX hXnc hXZbot
    have hle : X ⊓ Subgroup.center G ≤ X := inf_le_left
    haveI : (X ⊓ Subgroup.center G).Normal := normal_of_le_center inf_le_right
    exact quotient_leaf IH hcard h hXYZ hmaxX hle hXZbot
      (fun hc => hXnc (le_trans hc hle))
  set S₀ := S ⊓ Subgroup.center G with hS₀
  by_cases hS₀bot : S₀ = ⊥
  · -- **Case (i): `S ⊓ Z(G) = ⊥`.** First eliminate the cases where `T` or `U` meets `Z(G)`.
    by_cases hT₀ : T ⊓ Subgroup.center G = ⊥
    · by_cases hU₀ : U ⊓ Subgroup.center G = ⊥
      · -- **All three members meet `Z(G)` trivially** (case i).
        -- `S` and `T` are abelian (Observation 2.11).
        have hSab : IsMulCommutative (S : Subgroup G) := isMulCommutative_of_inf_center_bot h hS₀bot
        have hTab : IsMulCommutative (T : Subgroup G) := isMulCommutative_of_inf_center_bot h hT₀
        by_cases hSTcomm : ⁅S, T⁆ = ⊥
        · -- **Sub-case A: `S` and `T` commute.** Then `↥(S ⊔ T)` is abelian, and the
          -- subgroup-split (`S, T ≤ S ⊔ T`) gives `ρ₀(G) ≤ ρ₀(↥(S⊔T)) ≤ 1 < √index`.
          have hHab : IsMulCommutative (↥(S ⊔ T)) := isMulCommutative_sup hSab hTab hSTcomm
          have hsplit : rho0 G ≤ rho0 (↥(S ⊔ T)) :=
            rho0_le_rho0_subgroup hTPP hmax le_sup_left le_sup_right
          have hone : rho0 (↥(S ⊔ T)) ≤ 1 := rho0_le_one_of_isMulCommutative
          exact lt_of_le_of_lt (le_trans hsplit hone) (one_lt_sqrt_index_center h)
        · -- **Sub-case B: `⁅S, T⁆ ≠ ⊥`.** Set `H = S ⊔ Z(G) ⊔ T`; it is class-2.
          set H := S ⊔ Subgroup.center G ⊔ T with hH
          have hSH : S ≤ H := le_trans le_sup_left le_sup_left
          have hTH : T ≤ H := le_sup_right
          have hZH : Subgroup.center G ≤ H := le_trans le_sup_right le_sup_left
          have hclass2H : IsClass2 (H : Subgroup G) := isClass2_subgroup h hSTcomm hSH hTH
          by_cases hHtop : H = ⊤
          · -- **Case (i.b): `H = SZ(G)T = G`** (paper line 499).
            -- `K = S ⊔ Z(G)` is abelian (`S` abelian, `Z(G)` central, commuting).
            set K := S ⊔ Subgroup.center G with hK
            have hKab : IsMulCommutative (↥K) :=
              isMulCommutative_sup hSab inferInstance (commutator_center_eq_bot S)
            -- `N = K ⊓ T` is normal (both `K` and `T` abelian, `K ⊔ T = H = ⊤`).
            set N := K ⊓ T with hN
            have hKT_top : K ⊔ T = ⊤ := by rw [← hH]; exact hHtop
            haveI hNnormal : N.Normal :=
              normal_of_abelian_sup hKab hTab hKT_top inf_le_left inf_le_right
            have hNT : N ≤ T := inf_le_right
            by_cases hNbot : N = ⊥
            · -- **Sub-case (i.b, `N = ⊥`): the extremal semidirect leaf.** `G = K ⋊ T`.
              -- `K` is normal (it is `S ⊔ Z(G)`, normal by Observation 2.11).
              haveI hKnormal : K.Normal :=
                (obs_abelian_normal_product h hS₀bot).1
              -- `|K| = |S|·|Z(G)|` (Observation 2.11).
              have hKcard : Nat.card (K : Subgroup G) = Nat.card S * Nat.card (Subgroup.center G) :=
                (obs_abelian_normal_product h hS₀bot).2
              -- `G = K ⋊ T`: `K ⊓ T = ⊥` and `K ⊔ T = ⊤`, so `IsComplement' K T`.
              have hKTdisj : Disjoint K T := disjoint_iff.mpr hNbot
              have hKTmul : (K : Set G) * (T : Set G) = (Set.univ : Set G) := by
                rw [← Subgroup.normal_mul, hKT_top, Subgroup.coe_top]
              have hcompl : Subgroup.IsComplement' K T :=
                Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hKTdisj hKTmul
              -- `|S|·|Z(G)|·|T| = |G|`.
              have hSZT : Nat.card S * Nat.card (Subgroup.center G) * Nat.card T = Nat.card G := by
                rw [← hKcard]; exact hcompl.card_mul
              -- `U` is abelian too (Observation 2.11).
              have hUab : IsMulCommutative (U : Subgroup G) :=
                isMulCommutative_of_inf_center_bot h hU₀
              -- The swapped triple `(S, U, T)` is also maximal.
              have hTPP_SUT : TripleProductProperty (S : Set G).toFinset (U : Set G).toFinset
                  (T : Set G).toFinset := subgroupTPP_swap hTPP
              have hmax_SUT : stppCapacity G = Nat.card S * Nat.card U * Nat.card T := by
                rw [hmax]; ring
              -- **`|U| = |T|` via the analysis of `K ⊔ U` / `K ⊓ U`.** Every non-extremal
              -- branch closes the goal; only `G = K ⋊ U` continues, giving `|S||Z||U| = |G|`.
              have huT : Nat.card U = Nat.card T ∨
                  rho0 G < Real.sqrt ((Subgroup.center G).index : ℝ) := by
                by_cases hSUcomm : ⁅S, U⁆ = ⊥
                · -- `S, U` commute ⇒ `↥(S ⊔ U)` abelian ⇒ split closes the goal.
                  right
                  have hUUab : IsMulCommutative (↥(S ⊔ U)) := isMulCommutative_sup hSab hUab hSUcomm
                  have hsplit : rho0 G ≤ rho0 (↥(S ⊔ U)) :=
                    rho0_le_rho0_subgroup hTPP_SUT hmax_SUT le_sup_left le_sup_right
                  exact lt_of_le_of_lt (le_trans hsplit rho0_le_one_of_isMulCommutative)
                    (one_lt_sqrt_index_center h)
                · -- `⁅S, U⁆ ≠ ⊥`: `H' = S ⊔ Z(G) ⊔ U` is class-2.
                  set H' := S ⊔ Subgroup.center G ⊔ U with hH'
                  have hSH' : S ≤ H' := le_trans le_sup_left le_sup_left
                  have hUH' : U ≤ H' := le_sup_right
                  have hZH' : Subgroup.center G ≤ H' := le_trans le_sup_right le_sup_left
                  have hclass2H' : IsClass2 (H' : Subgroup G) := isClass2_subgroup h hSUcomm hSH' hUH'
                  by_cases hH'top : H' = ⊤
                  · -- `K ⊔ U = ⊤`. Split on `N' = K ⊓ U`.
                    have hKU_top : K ⊔ U = ⊤ := by rw [← hH']; exact hH'top
                    set N' := K ⊓ U with hN'
                    haveI : N'.Normal := normal_of_abelian_sup hKab hUab hKU_top inf_le_left inf_le_right
                    by_cases hN'bot : N' = ⊥
                    · -- `G = K ⋊ U`: `|S||Z||U| = |G|`, hence `|U| = |T|`.
                      left
                      have hKUdisj : Disjoint K U := disjoint_iff.mpr hN'bot
                      have hKUmul : (K : Set G) * (U : Set G) = (Set.univ : Set G) := by
                        rw [← Subgroup.normal_mul, hKU_top, Subgroup.coe_top]
                      have hcomplU : Subgroup.IsComplement' K U :=
                        Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hKUdisj hKUmul
                      have hSZU : Nat.card S * Nat.card (Subgroup.center G) * Nat.card U
                          = Nat.card G := by rw [← hKcard]; exact hcomplU.card_mul
                      have hSZpos : 0 < Nat.card S * Nat.card (Subgroup.center G) :=
                        Nat.mul_pos Nat.card_pos Nat.card_pos
                      have : Nat.card S * Nat.card (Subgroup.center G) * Nat.card U
                          = Nat.card S * Nat.card (Subgroup.center G) * Nat.card T := by
                        rw [hSZU, hSZT]
                      exact Nat.eq_of_mul_eq_mul_left hSZpos this
                    · -- `N' > ⊥`: quotient by `N'` via the cyclic triple `(U, S, T)`.
                      right
                      exact quotient_leaf IH hcard h hTPP_UST hmax_UST (inf_le_right)
                        hN'bot (fun hc => hUnc (le_trans hc inf_le_right))
                  · -- `K ⊔ U = H' < ⊤`: split via `(S, U, T)` + IH on `↥H'`.
                    right
                    have hsplit : rho0 G ≤ rho0 (↥H') :=
                      rho0_le_rho0_subgroup hTPP_SUT hmax_SUT hSH' hUH'
                    have hH'lt : Nat.card (H' : Subgroup G) < u := by
                      rw [← hcard]
                      have hidx : H'.index * Nat.card (H' : Subgroup G) = Nat.card G :=
                        Subgroup.index_mul_card H'
                      have hidx1 : 1 < H'.index := Subgroup.one_lt_index_of_ne_top hH'top
                      nlinarith [hidx, hidx1, Nat.card_pos (α := H')]
                    have hIH : rho0 (↥H') < Real.sqrt ((Subgroup.center (↥H')).index : ℝ) :=
                      IH (Nat.card (H' : Subgroup G)) hH'lt (↥H') rfl hclass2H'
                    have hidxle : Real.sqrt ((Subgroup.center (↥H')).index : ℝ)
                        ≤ Real.sqrt ((Subgroup.center G).index : ℝ) := by
                      apply Real.sqrt_le_sqrt
                      exact_mod_cast index_center_subgroup_le hZH'
                    exact lt_of_le_of_lt hsplit (lt_of_lt_of_le hIH hidxle)
              -- If any branch already closed the goal, done; else `|U| = |T|`.
              rcases huT with huT | hdone
              · -- **`|S| = |T|`** by the symmetric analysis with first member `T` and the
                -- decomposition `G = (T ⊔ Z(G)) ⋊ U`, giving `|T|·|Z(G)|·|U| = |G|`.
                set KT := T ⊔ Subgroup.center G with hKT
                have hKTab : IsMulCommutative (↥KT) :=
                  isMulCommutative_sup hTab inferInstance (commutator_center_eq_bot T)
                have hKTcard : Nat.card (KT : Subgroup G)
                    = Nat.card T * Nat.card (Subgroup.center G) :=
                  (obs_abelian_normal_product h hT₀).2
                -- The swap of `(T, U, S)` is `(T, S, U)`.
                have hTPP_TSU : TripleProductProperty (T : Set G).toFinset (S : Set G).toFinset
                    (U : Set G).toFinset := subgroupTPP_swap hTPP_TUS
                have hmax_TSU : stppCapacity G = Nat.card T * Nat.card S * Nat.card U := by
                  rw [hmax]; ring
                have hsT : Nat.card S = Nat.card T ∨
                    rho0 G < Real.sqrt ((Subgroup.center G).index : ℝ) := by
                  by_cases hTUcomm : ⁅T, U⁆ = ⊥
                  · -- `T, U` commute ⇒ `↥(T ⊔ U)` abelian ⇒ split via `(T, U, S)` closes.
                    right
                    have : IsMulCommutative (↥(T ⊔ U)) := isMulCommutative_sup hTab hUab hTUcomm
                    have hsplit : rho0 G ≤ rho0 (↥(T ⊔ U)) :=
                      rho0_le_rho0_subgroup hTPP_TUS hmax_TUS le_sup_left le_sup_right
                    exact lt_of_le_of_lt (le_trans hsplit rho0_le_one_of_isMulCommutative)
                      (one_lt_sqrt_index_center h)
                  · set HT := T ⊔ Subgroup.center G ⊔ U with hHT
                    have hTHT : T ≤ HT := le_trans le_sup_left le_sup_left
                    have hUHT : U ≤ HT := le_sup_right
                    have hZHT : Subgroup.center G ≤ HT := le_trans le_sup_right le_sup_left
                    have hclass2HT : IsClass2 (HT : Subgroup G) :=
                      isClass2_subgroup h hTUcomm hTHT hUHT
                    by_cases hHTtop : HT = ⊤
                    · have hKTU_top : KT ⊔ U = ⊤ := by rw [← hHT]; exact hHTtop
                      haveI hKTnormal : KT.Normal := (obs_abelian_normal_product h hT₀).1
                      set NT := KT ⊓ U with hNT'
                      haveI : NT.Normal :=
                        normal_of_abelian_sup hKTab hUab hKTU_top inf_le_left inf_le_right
                      by_cases hNTbot : NT = ⊥
                      · -- `G = KT ⋊ U`: `|T||Z||U| = |G|`. With `|U| = |T|`, get `|S| = |T|`.
                        left
                        have hKTUdisj : Disjoint KT U := disjoint_iff.mpr hNTbot
                        have hKTUmul : (KT : Set G) * (U : Set G) = (Set.univ : Set G) := by
                          rw [← Subgroup.normal_mul, hKTU_top, Subgroup.coe_top]
                        have hcomplTU : Subgroup.IsComplement' KT U :=
                          Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hKTUdisj hKTUmul
                        have hTZU : Nat.card T * Nat.card (Subgroup.center G) * Nat.card U
                            = Nat.card G := by rw [← hKTcard]; exact hcomplTU.card_mul
                        -- `|T||Z||U| = |G| = |S||Z||T|` and `|U| = |T|` ⇒ `|S| = |T|`.
                        have hZpos : 0 < Nat.card (Subgroup.center G) := Nat.card_pos
                        have hTpos : 0 < Nat.card T := Nat.card_pos
                        have key : Nat.card T * (Nat.card (Subgroup.center G) * Nat.card T)
                            = Nat.card S * (Nat.card (Subgroup.center G) * Nat.card T) := by
                          rw [← mul_assoc, ← mul_assoc]
                          rw [show Nat.card T * Nat.card (Subgroup.center G) * Nat.card T
                              = Nat.card T * Nat.card (Subgroup.center G) * Nat.card U by rw [huT]]
                          rw [hTZU, hSZT]
                        have hZTpos : 0 < Nat.card (Subgroup.center G) * Nat.card T :=
                          Nat.mul_pos hZpos hTpos
                        exact (Nat.eq_of_mul_eq_mul_right hZTpos key).symm
                      · -- `NT > ⊥`: quotient via `(U, S, T)`.
                        right
                        exact quotient_leaf IH hcard h hTPP_UST hmax_UST inf_le_right
                          hNTbot (fun hc => hUnc (le_trans hc inf_le_right))
                    · -- `KT ⊔ U = HT < ⊤`: split via `(T, U, S)` + IH on `↥HT`.
                      right
                      have hsplit : rho0 G ≤ rho0 (↥HT) :=
                        rho0_le_rho0_subgroup hTPP_TUS hmax_TUS hTHT hUHT
                      have hHTlt : Nat.card (HT : Subgroup G) < u := by
                        rw [← hcard]
                        have hidx : HT.index * Nat.card (HT : Subgroup G) = Nat.card G :=
                          Subgroup.index_mul_card HT
                        have hidx1 : 1 < HT.index := Subgroup.one_lt_index_of_ne_top hHTtop
                        nlinarith [hidx, hidx1, Nat.card_pos (α := HT)]
                      have hIH : rho0 (↥HT) < Real.sqrt ((Subgroup.center (↥HT)).index : ℝ) :=
                        IH (Nat.card (HT : Subgroup G)) hHTlt (↥HT) rfl hclass2HT
                      have hidxle : Real.sqrt ((Subgroup.center (↥HT)).index : ℝ)
                          ≤ Real.sqrt ((Subgroup.center G).index : ℝ) := by
                        apply Real.sqrt_le_sqrt
                        exact_mod_cast index_center_subgroup_le hZHT
                      exact lt_of_le_of_lt hsplit (lt_of_lt_of_le hIH hidxle)
                rcases hsT with hsT | hdone
                · -- **All equal: `|S| = |T| = |U|`.** Close via `rho0_lt_sqrt_of_sq_lt`.
                  apply rho0_lt_sqrt_of_sq_lt
                  -- Abbreviations.  `m = |T|`, `z = |Z(G)|`.
                  set m := Nat.card T with hm
                  set z := Nat.card (Subgroup.center G) with hz
                  have hzpos : 0 < z := Nat.card_pos
                  have hmpos : 0 < m := Nat.card_pos
                  have hZ2 : 2 ≤ z := by
                    rw [hz]
                    refine (Subgroup.one_lt_card_iff_ne_bot (H := Subgroup.center G)).mpr ?_
                    intro hc
                    exact h.comm_ne_bot (le_bot_iff.mp (le_trans h.comm_le_center hc.le))
                  -- `|G| = m² · z` (from `hSZT` with `|S| = |T|`).
                  have hGval : Nat.card G = m * m * z := by rw [← hSZT, hsT]; ring
                  -- `index = m²` (`index · z = |G| = m² · z`, cancel `z`).
                  have hindex : (Subgroup.center G).index * z = Nat.card G :=
                    Subgroup.index_mul_card (Subgroup.center G)
                  have hidxval : (Subgroup.center G).index = m * m := by
                    have : (Subgroup.center G).index * z = (m * m) * z := by rw [hindex, hGval]
                    exact Nat.eq_of_mul_eq_mul_right hzpos this
                  -- `β₀(G) = |S||T||U| = m³`, `|G| = m²z`, `index = m²`.
                  rw [hmax, hsT, huT, hidxval]
                  have hFG : Fintype.card G = m * m * z := by
                    rw [← Nat.card_eq_fintype_card]; exact hGval
                  rw [hFG]
                  -- `(m·m·m)² < (m²z)² · m²` ⟺ `m⁶ · 1 < m⁶ · z²`, true since `z ≥ 2`.
                  have hlhs : (m * m * m) ^ 2 = (m ^ 6) * 1 := by ring
                  have hrhs : (m * m * z) ^ 2 * (m * m) = (m ^ 6) * z ^ 2 := by ring
                  rw [hlhs, hrhs]
                  have hm6 : 0 < m ^ 6 := by positivity
                  have hz2 : 1 < z ^ 2 := by nlinarith [hZ2]
                  exact mul_lt_mul_of_pos_left hz2 hm6
                · exact hdone
              · exact hdone
            · -- **Sub-case (i.b, `N > ⊥`): quotient by `N`** via the cyclic triple `(T, U, S)`.
              have hNcomm : ¬ commutator G ≤ N := fun hc => hTnc (le_trans hc hNT)
              exact quotient_leaf IH hcard h hTPP_TUS hmax_TUS hNT hNbot hNcomm
          · -- **Case (i.a): `H < G`.** Subgroup-split + IH on `↥H`.
            have hsplit : rho0 G ≤ rho0 (↥H) := rho0_le_rho0_subgroup hTPP hmax hSH hTH
            -- `|H| < |G|`.
            have hHlt : Nat.card (H : Subgroup G) < u := by
              rw [← hcard]
              have hidx : H.index * Nat.card (H : Subgroup G) = Nat.card G :=
                Subgroup.index_mul_card H
              have hidx1 : 1 < H.index := Subgroup.one_lt_index_of_ne_top hHtop
              nlinarith [hidx, hidx1, Nat.card_pos (α := H)]
            -- IH on `↥H`, then lift the index via `index_center_subgroup_le`.
            have hIH : rho0 (↥H) < Real.sqrt ((Subgroup.center (↥H)).index : ℝ) :=
              IH (Nat.card (H : Subgroup G)) hHlt (↥H) rfl hclass2H
            have hidxle : Real.sqrt ((Subgroup.center (↥H)).index : ℝ)
                ≤ Real.sqrt ((Subgroup.center G).index : ℝ) := by
              apply Real.sqrt_le_sqrt
              exact_mod_cast index_center_subgroup_le hZH
            exact lt_of_le_of_lt hsplit (lt_of_lt_of_le hIH hidxle)
      · exact central_branch hTPP_UST hmax_UST hUnc hU₀
    · exact central_branch hTPP_TUS hmax_TUS hTnc hT₀
  · -- **Case (ii): `S ⊓ Z(G) > ⊥`.** Quotient by the nontrivial central `S₀`.
    exact central_branch hTPP hmax hSnc hS₀bot

/-! ### Main theorem (Murthy Theorem 3.1) -/

universe u

/-- **Murthy Theorem 3.1** (`ThmNilpClassTwo`, arXiv:2602.15796): for a group `G` of
nilpotency class exactly `2`, the subgroup-TPP ratio satisfies
`ρ₀(G) < √(|G : Z(G)|)`.

The strong induction on `|G|` is wired here; the mathematical content lives in
`inductive_step`. Subgroups `↥H` and quotients `G ⧸ N` of `G : Type u` are themselves
`Type u`, so the inductive hypothesis (universally quantified over `Type u`) applies to
them directly — this is why a single fixed universe `u` suffices. -/
theorem rho0_lt_sqrt_index_center
    (G : Type u) [Group G] [Fintype G] [DecidableEq G] (h : IsClass2 G) :
    rho0 G < Real.sqrt ((Subgroup.center G).index : ℝ) := by
  -- Strong induction on `Nat.card G`, with the statement quantified over all
  -- finite class-2 groups in universe `u` of a given order.
  have key : ∀ n : ℕ, ∀ (G' : Type u) [Group G'] [Fintype G'] [DecidableEq G'],
      Nat.card G' = n → IsClass2 G' →
      rho0 G' < Real.sqrt ((Subgroup.center G').index : ℝ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro G' _ _ _ hcard hclass
      exact inductive_step IH G' hcard hclass
  exact key (Nat.card G) G rfl h

/-! ### Proof map (complete, `sorry`-free)

The whole of Theorem 3.1 is formalized. The four originally-planned tasks are all done:

* **Task A — `rho0_quotient_lt_sqrt_index_center` (Lemma 3.6).** ✓ via
  `index_center_quotient_le` + `√`-monotonicity.
* **Task B — `rho0_le_rho0_subgroup` (Proposition 2.7 subgroup split).** ✓ The coset count
  `|U| ≤ |G:H| · |U ⊓ H|` (`relIndex_mul_card_inf` + `relIndex_le_index`), the restriction
  `subgroupTPP_restrict`, and `le_stppCapacity` assemble the ℕ inequality
  `β₀(G)·|H| ≤ β₀(↥H)·|G|`, lifted by `div_le_div_iff₀`.
* **Task C — `rho0_le_rho0_quotient` (Lemma 2.10 Neumann quotient).** ✓ The image triple's
  TPP is `subgroupTPP_of_stu ∘ quotient_subgroupTPP_stu`; the cardinalities use
  `card_map_mk'_eq_relIndex`, `relIndex_mul_card_inf`, and the pairwise-trivial
  `subgroupTPP_inf_ST/SU` to give `|S'|·|N| = |S|`, `|T'| = |T|`, `|U'| = |U|`.
* **Task D — `inductive_step`.** The full case tree of the paper (lines 487–505):
  * **Leaf 0** `ρ₀(G) ≤ 1` (`rho0_lt_sqrt_of_le_card`);
  * **Case (ii)** `S ⊓ Z(G) > ⊥`: central quotient via `quotient_leaf`;
  * **WLOG reduction of Case (i)**: cyclic invariance (`subgroupTPP_cyclic`) dispatches any
    member meeting `Z(G)` nontrivially;
  * **Sub-case A** `⁅S,T⁆ = ⊥`: `↥(S ⊔ T)` is abelian (`isMulCommutative_sup`), so the
    subgroup split gives `ρ₀(G) ≤ 1`;
  * **Case (i.a)** `H = SZ(G)T < G`: `isClass2_subgroup` + IH + `index_center_subgroup_le`;
  * **Case (i.b)** `H = SZ(G)T = G`: the internal semidirect product `G = SZ(G) ⋊ T`. If
    `N = (S ⊔ Z(G)) ⊓ T > ⊥` (normal by `normal_of_abelian_sup`), quotient via the cyclic
    triple `(T, U, S)`. If `N = ⊥`, `Subgroup.IsComplement'.card_mul` gives
    `|S|·|Z(G)|·|T| = |G|`; the analogous decompositions for the permuted triples
    (`subgroupTPP_swap` for the transpositions), each non-extremal branch of which closes
    the goal directly, force `|S| = |T| = |U| = √|G:Z(G)|`, and `rho0_lt_sqrt_of_sq_lt`
    with `|Z(G)| ≥ 2` yields the strict bound `ρ₀(G) = √|G:Z(G)|/|Z(G)| < √|G:Z(G)|`.
-/

end GroupTPP.MurthyClass2
