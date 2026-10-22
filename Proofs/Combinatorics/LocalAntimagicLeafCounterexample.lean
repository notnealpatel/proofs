/-
# Counterexample to the local antimagic leaf conjecture

## Source

André Ebling Brondani and Francisca Andrea Macedo França,
*Counterexamples to the local antimagic leaf conjecture*, arXiv:2610.22783.

The leaf conjecture (Conjecture 2.2; Bača et al. 2022; Premalatha,
Arumugam, Lee and Wang 2020) asserts `χ_la(T) ≤ ℓ(T)+2` for trees of
order at least three. Theorem 3.4 refutes it with
`T₃ = Cat(8,7,25)`, for which `χ_la(T₃) = 43 = ℓ(T₃)+3`.

This module formalizes: Lemma 3.1 (`weight_mem_Icc`); Corollary 3.3 with
`S` the set of all internal vertices (`weight_injective_of_separated`, which
only needs adjacent internal vertices to be distinguished, and
`chiLA_eq_card_of_forall_injective`, which takes the existence of a local
antimagic labeling as a hypothesis since Haslegrave's theorem is not in
Mathlib); Theorem 3.4 (`chiLA_T3`, `thm_3_4`), including an explicit local
antimagic labeling of `T₃`; and the disproof of the leaf conjecture
(`not_leaf_conjecture`).  Not formalized: Theorem 3.5 (`T₄`) and the unbounded
family of Section 4.

## Conventions

A bijective edge labeling `f : G.edgeSet ≃ Fin m` stands for the paper's
`f : E(G) → [m]` via `e ↦ f e + 1`.  The induced weight `f⁺(v)` is the sum of
the labels over `G.incidenceFinset v`.  The local antimagic chromatic number is
the `sInf` of the numbers of distinct induced weights over local antimagic
labelings with `m = |E(G)|`; it is `0` (junk) when no such labeling exists, a
case excluded for `T₃` by an explicit labeling.
-/
import Mathlib

set_option autoImplicit false

namespace LocalAntimagicLeaf

open Finset

/-! ## Sums of distinct natural numbers -/

/-- A finite set of `d` distinct natural numbers has sum at least
`0 + 1 + ⋯ + (d - 1)`, i.e. `d (d - 1) ≤ 2 ∑ s`. -/
theorem card_mul_pred_le_two_mul_sum (s : Finset ℕ) :
    s.card * (s.card - 1) ≤ 2 * ∑ x ∈ s, x := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have hna : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hsub : s ⊆ Finset.range a := fun x hx => Finset.mem_range.2 (hlt x hx)
    have hc : s.card ≤ a := by simpa using Finset.card_le_card hsub
    rw [Finset.sum_insert hna, Finset.card_insert_of_notMem hna]
    rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · rw [h0]; omega
    · have hexp : (s.card + 1) * (s.card + 1 - 1) = s.card * (s.card - 1) + 2 * s.card := by
        cases h : s.card with
        | zero => omega
        | succ k => simp only [Nat.add_sub_cancel]; ring
      nlinarith

/-- A set of `d` distinct elements of `{0, …, m - 1}` has sum at most
`(m - d) + ⋯ + (m - 1)`, i.e. `2 ∑ s + d (d + 1) ≤ 2 m d`. -/
theorem two_mul_sum_add_le_of_subset_range (s : Finset ℕ) :
    ∀ m, s ⊆ Finset.range m → 2 * ∑ x ∈ s, x + s.card * (s.card + 1) ≤ 2 * m * s.card := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    intro m hm
    have hna : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hsub : s ⊆ Finset.range a := fun x hx => Finset.mem_range.2 (hlt x hx)
    have ham : a < m := Finset.mem_range.1 (hm (Finset.mem_insert_self a s))
    have h1 := ih a hsub
    rw [Finset.sum_insert hna, Finset.card_insert_of_notMem hna]
    nlinarith

/-! ## Labelings, induced weights and the local antimagic chromatic number -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The lower end `L_m(d) = d (d + 1) / 2` of the weight interval of a vertex of degree `d`
(it does not depend on `m`). -/
def weightLower (d : ℕ) : ℕ := d * (d + 1) / 2

/-- The upper end `U_m(d) = d (2m - d + 1) / 2` of the weight interval of a vertex of
degree `d` in a graph with `m` edges (meaningful for `d ≤ m`). -/
def weightUpper (m d : ℕ) : ℕ := d * (2 * m - d + 1) / 2

example : weightLower 9 = 45 := by decide
example : weightUpper 42 9 = 342 := by decide
example : weightLower 26 = 351 := by decide
example : weightUpper 42 26 = 767 := by decide
example : weightUpper 42 1 = 42 := by decide

/-- The label in `{1, …, m}` that the bijection `f : E(G) ≃ Fin m` assigns to the edge `e`
(namely `f e + 1`), extended by `0` to non-edges. -/
def edgeLabel (G : SimpleGraph V) [DecidableRel G.Adj] {m : ℕ} (f : G.edgeSet ≃ Fin m) (e : Sym2 V) : ℕ :=
  if h : e ∈ G.edgeSet then (f ⟨e, h⟩ : ℕ) + 1 else 0

/-- The induced weight `f⁺(v) = ∑_{e ∈ E_G(v)} f(e)` of the vertex `v`. -/
def weight (G : SimpleGraph V) [DecidableRel G.Adj] {m : ℕ} (f : G.edgeSet ≃ Fin m)
    (v : V) : ℕ :=
  ∑ e ∈ G.incidenceFinset v, edgeLabel G f e

/-- A bijective edge labeling is local antimagic if adjacent vertices receive distinct
induced weights. -/
def IsLocalAntimagic (G : SimpleGraph V) [DecidableRel G.Adj] {m : ℕ}
    (f : G.edgeSet ≃ Fin m) : Prop :=
  ∀ u v, G.Adj u v → weight G f u ≠ weight G f v

/-- The set `C(f) = {f⁺(v) : v ∈ V(G)}` of induced vertex weights. -/
def weightSet (G : SimpleGraph V) [DecidableRel G.Adj] {m : ℕ} (f : G.edgeSet ≃ Fin m) :
    Finset ℕ :=
  Finset.univ.image (weight G f)

/-- The local antimagic chromatic number `χ_la(G) = min_f |C(f)|`, the minimum over
local antimagic bijections `f : E(G) → [|E(G)|]` (junk value `0` if there is none). -/
noncomputable def chiLA (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {k | ∃ f : G.edgeSet ≃ Fin (Fintype.card G.edgeSet),
    IsLocalAntimagic G f ∧ (weightSet G f).card = k}

/-- The number `ℓ(G)` of leaves (vertices of degree one). -/
def leafCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  #{v | G.degree v = 1}

section General

variable (G : SimpleGraph V) [DecidableRel G.Adj] {m : ℕ} (f : G.edgeSet ≃ Fin m)

/-- The zero-based label of an edge, extended by `0` to non-edges. -/
private def edgeIndex (e : Sym2 V) : ℕ :=
  if h : e ∈ G.edgeSet then (f ⟨e, h⟩ : ℕ) else 0

omit [Fintype V] [DecidableEq V] in
private theorem edgeLabel_eq_edgeIndex_add_one {e : Sym2 V} (he : e ∈ G.edgeSet) :
    edgeLabel G f e = edgeIndex G f e + 1 := by
  simp [edgeLabel, edgeIndex, he]

private theorem edgeIndex_injOn (v : V) :
    Set.InjOn (edgeIndex G f) (G.incidenceFinset v : Set (Sym2 V)) := by
  intro e₁ he₁ e₂ he₂ h
  rw [SimpleGraph.coe_incidenceFinset] at he₁ he₂
  have h₁ : e₁ ∈ G.edgeSet := he₁.1
  have h₂ : e₂ ∈ G.edgeSet := he₂.1
  simp only [edgeIndex, h₁, h₂, dite_true] at h
  have hsub := f.injective (Fin.ext h)
  exact congrArg Subtype.val hsub

/-- The weight is the sum of the zero-based labels plus the degree. -/
private theorem weight_eq_sum_image_add_degree (v : V) :
    weight G f v = ∑ x ∈ (G.incidenceFinset v).image (edgeIndex G f), x + G.degree v := by
  rw [Finset.sum_image (edgeIndex_injOn G f v), ← SimpleGraph.card_incidenceFinset_eq_degree,
    Finset.card_eq_sum_ones, ← Finset.sum_add_distrib, weight]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [SimpleGraph.mem_incidenceFinset] at he
  exact edgeLabel_eq_edgeIndex_add_one G f he.1

private theorem image_edgeIndex_subset_range (v : V) :
    (G.incidenceFinset v).image (edgeIndex G f) ⊆ Finset.range m := by
  intro x hx
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx
  rw [SimpleGraph.mem_incidenceFinset] at he
  simp [edgeIndex, he.1]

private theorem card_image_edgeIndex (v : V) :
    ((G.incidenceFinset v).image (edgeIndex G f)).card = G.degree v := by
  rw [Finset.card_image_of_injOn (edgeIndex_injOn G f v),
    SimpleGraph.card_incidenceFinset_eq_degree]

include f in
/-- The degree of a vertex is at most the number `m` of labels. -/
theorem degree_le (v : V) : G.degree v ≤ m := by
  have h := Finset.card_le_card (image_edgeIndex_subset_range G f v)
  rwa [card_image_edgeIndex, Finset.card_range] at h

/-- Doubled form of Lemma 3.1: `d (d + 1) ≤ 2 f⁺(v)` and `2 f⁺(v) + d² ≤ d (2m + 1)`. -/
theorem weight_bounds_two_mul (v : V) :
    G.degree v * (G.degree v + 1) ≤ 2 * weight G f v ∧
      2 * weight G f v + G.degree v * G.degree v ≤ G.degree v * (2 * m + 1) := by
  have hlo := card_mul_pred_le_two_mul_sum ((G.incidenceFinset v).image (edgeIndex G f))
  have hhi := two_mul_sum_add_le_of_subset_range ((G.incidenceFinset v).image (edgeIndex G f))
    m (image_edgeIndex_subset_range G f v)
  rw [card_image_edgeIndex] at hlo hhi
  rw [weight_eq_sum_image_add_degree]
  set d := G.degree v
  set S := ∑ x ∈ (G.incidenceFinset v).image (edgeIndex G f), x
  constructor
  · rcases Nat.eq_zero_or_pos d with h0 | hpos
    · rw [h0]; omega
    · have hexp : d * (d + 1) = d * (d - 1) + 2 * d := by
        obtain ⟨k, hk⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
        rw [hk, Nat.add_sub_cancel]; ring
      omega
  · nlinarith

/-- **Lemma 3.1.** Under a bijective labeling `f : E(G) → [m]`, a vertex of degree `d`
has induced weight in `[L_m(d), U_m(d)] = [d(d+1)/2, d(2m-d+1)/2]`. -/
theorem weight_mem_Icc (v : V) :
    weightLower (G.degree v) ≤ weight G f v ∧ weight G f v ≤ weightUpper m (G.degree v) := by
  obtain ⟨hlo, hhi⟩ := weight_bounds_two_mul G f v
  have hdm := degree_le G f v
  set d := G.degree v
  set w := weight G f v
  constructor
  · rw [weightLower]
    omega
  · rw [weightUpper]
    have hsplit : d * (2 * m + 1) = d * (2 * m - d + 1) + d * d := by
      obtain ⟨k, hk⟩ : ∃ k, 2 * m = d + k := ⟨2 * m - d, by omega⟩
      rw [hk, Nat.add_sub_cancel_left]; ring
    omega

/-- A leaf has induced weight equal to the label of its unique edge. -/
private theorem exists_weight_eq_of_degree_eq_one {v : V} (hv : G.degree v = 1) :
    ∃ e ∈ G.incidenceFinset v, weight G f v = edgeLabel G f e := by
  rw [← SimpleGraph.card_incidenceFinset_eq_degree, Finset.card_eq_one] at hv
  obtain ⟨e, he⟩ := hv
  refine ⟨e, by rw [he]; exact Finset.mem_singleton_self e, ?_⟩
  rw [weight, he, Finset.sum_singleton]

/-- Two nonadjacent leaves have distinct induced weights. -/
theorem weight_ne_of_degree_eq_one {u v : V} (huv : u ≠ v) (hu : G.degree u = 1)
    (hv : G.degree v = 1) (hnadj : ¬ G.Adj u v) : weight G f u ≠ weight G f v := by
  obtain ⟨e₁, he₁, hw₁⟩ := exists_weight_eq_of_degree_eq_one G f hu
  obtain ⟨e₂, he₂, hw₂⟩ := exists_weight_eq_of_degree_eq_one G f hv
  intro heq
  rw [SimpleGraph.mem_incidenceFinset] at he₁ he₂
  have hlab : edgeLabel G f e₁ = edgeLabel G f e₂ := by rw [← hw₁, ← hw₂]; exact heq
  have h₁ : e₁ ∈ G.edgeSet := he₁.1
  have h₂ : e₂ ∈ G.edgeSet := he₂.1
  simp only [edgeLabel, h₁, h₂, dite_true, Nat.add_right_cancel_iff] at hlab
  have he : e₁ = e₂ := congrArg Subtype.val (f.injective (Fin.ext hlab))
  have hmem : u ∈ e₁ ∧ v ∈ e₁ := ⟨he₁.2, he ▸ he₂.2⟩
  rw [Sym2.mem_and_mem_iff huv] at hmem
  exact hnadj (by rw [← SimpleGraph.mem_edgeSet, ← hmem]; exact h₁)

/-- **Separation criterion** (injectivity part of Corollary 3.3, with `S` the set of all
internal vertices).  Suppose no two leaves are adjacent, every non-leaf `v` satisfies
`m < L_m(d(v))`, and any two distinct nonadjacent non-leaves have disjoint weight intervals.
If `f` distinguishes adjacent non-leaves (in particular, if `f` is local antimagic), then all
induced weights are pairwise distinct. -/
theorem weight_injective_of_separated
    (hleaf : ∀ u v, G.degree u = 1 → G.degree v = 1 → ¬ G.Adj u v)
    (hlarge : ∀ v, G.degree v ≠ 1 → m < weightLower (G.degree v))
    (hsep : ∀ u v, u ≠ v → G.degree u ≠ 1 → G.degree v ≠ 1 → ¬ G.Adj u v →
      weightUpper m (G.degree u) < weightLower (G.degree v) ∨
        weightUpper m (G.degree v) < weightLower (G.degree u))
    (hadj : ∀ u v, G.Adj u v → G.degree u ≠ 1 → G.degree v ≠ 1 → weight G f u ≠ weight G f v) :
    Function.Injective (weight G f) := by
  intro u v heq
  by_contra huv
  have hu := weight_mem_Icc G f u
  have hv := weight_mem_Icc G f v
  have hupper1 : weightUpper m 1 = m := by
    simp only [weightUpper]; omega
  by_cases hdu : G.degree u = 1 <;> by_cases hdv : G.degree v = 1
  · exact weight_ne_of_degree_eq_one G f huv hdu hdv (hleaf u v hdu hdv) heq
  · have h1 := hlarge v hdv
    rw [hdu, hupper1] at hu
    omega
  · have h1 := hlarge u hdu
    rw [hdv, hupper1] at hv
    omega
  · by_cases hadjuv : G.Adj u v
    · exact hadj u v hadjuv hdu hdv heq
    · rcases hsep u v huv hdu hdv hadjuv with h | h <;> omega

/-- Corollary 3.3 (injectivity) for local antimagic labelings. -/
theorem weight_injective_of_separated_of_isLocalAntimagic (hf : IsLocalAntimagic G f)
    (hleaf : ∀ u v, G.degree u = 1 → G.degree v = 1 → ¬ G.Adj u v)
    (hlarge : ∀ v, G.degree v ≠ 1 → m < weightLower (G.degree v))
    (hsep : ∀ u v, u ≠ v → G.degree u ≠ 1 → G.degree v ≠ 1 → ¬ G.Adj u v →
      weightUpper m (G.degree u) < weightLower (G.degree v) ∨
        weightUpper m (G.degree v) < weightLower (G.degree u)) :
    Function.Injective (weight G f) :=
  weight_injective_of_separated G f hleaf hlarge hsep fun u v h _ _ => hf u v h

/-- If the induced weights are pairwise distinct, then `|C(f)| = |V(G)|`. -/
theorem card_weightSet_of_injective (hinj : Function.Injective (weight G f)) :
    (weightSet G f).card = Fintype.card V := by
  rw [weightSet, Finset.card_image_of_injective _ hinj, Finset.card_univ]

/-- An injective weight function makes `f` local antimagic. -/
theorem isLocalAntimagic_of_injective (hinj : Function.Injective (weight G f)) :
    IsLocalAntimagic G f :=
  fun _ _ h heq => G.ne_of_adj h (hinj heq)

/-- The induced weight as a sum over neighbours: `f⁺(v) = ∑_{w ∼ v} f(vw)`. -/
theorem weight_eq_sum_neighborFinset (v : V) :
    weight G f v = ∑ w ∈ G.neighborFinset v, edgeLabel G f s(v, w) := by
  rw [weight]
  symm
  refine Finset.sum_nbij (fun w => s(v, w)) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    rw [SimpleGraph.mem_incidenceFinset]
    exact ⟨hw, Sym2.mem_mk_left v w⟩
  · intro w₁ _ w₂ _ h
    exact Sym2.congr_right.1 h
  · intro e he
    rw [Finset.mem_coe, SimpleGraph.mem_incidenceFinset] at he
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 he.2
    refine ⟨w, ?_, rfl⟩
    rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset]
    exact he.1

end General

/-- **Corollary 3.3.** If every local antimagic labeling of `G` (with labels `1, …, |E(G)|`)
has pairwise distinct induced weights, and some local antimagic labeling exists, then
`χ_la(G) = |V(G)|`. -/
theorem chiLA_eq_card_of_forall_injective (G : SimpleGraph V) [DecidableRel G.Adj]
    (hex : ∃ f : G.edgeSet ≃ Fin (Fintype.card G.edgeSet), IsLocalAntimagic G f)
    (hinj : ∀ f : G.edgeSet ≃ Fin (Fintype.card G.edgeSet), IsLocalAntimagic G f →
      Function.Injective (weight G f)) :
    chiLA G = Fintype.card V := by
  have hset : {k | ∃ f : G.edgeSet ≃ Fin (Fintype.card G.edgeSet),
      IsLocalAntimagic G f ∧ (weightSet G f).card = k} = {Fintype.card V} := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact card_weightSet_of_injective G f (hinj f hf)
    · rintro rfl
      obtain ⟨f, hf⟩ := hex
      exact ⟨f, hf, card_weightSet_of_injective G f (hinj f hf)⟩
  rw [chiLA, hset, csInf_singleton]


/-! ## The caterpillar `T₃ = Cat(8, 7, 25)`

Vertices `0, 1, 2` are the internal path `(a, b, c)`; vertices `3, …, 10` are the
`8` leaves at `a`, vertices `11, …, 17` the `7` leaves at `b`, and vertices
`18, …, 42` the `25` leaves at `c`.  Every vertex other than `0` is joined to its parent. -/

/-- The parent of a vertex of `T₃` (the root `a = 0` is its own parent). -/
def T3parent (v : Fin 43) : Fin 43 :=
  if v.val = 2 then 1 else if v.val ≤ 10 then 0 else if v.val ≤ 17 then 1 else 2

/-- The caterpillar `T₃ = Cat(8, 7, 25)`: each non-root vertex is adjacent to its parent. -/
def T3 : SimpleGraph (Fin 43) where
  Adj u v := u ≠ v ∧ (T3parent u = v ∨ T3parent v = u)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel T3.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ (T3parent u = v ∨ T3parent v = u)))

/-- The intended degree sequence of `T₃`: `d(a) = d(b) = 9`, `d(c) = 26`, leaves `1`. -/
def T3deg (v : Fin 43) : ℕ := if v.val ≤ 1 then 9 else if v.val = 2 then 26 else 1

/-- The degrees of `T₃`. -/
theorem T3_degree : ∀ v, T3.degree v = T3deg v := by decide

example : T3.neighborFinset 0 = {1, 3, 4, 5, 6, 7, 8, 9, 10} := by decide
example : T3.neighborFinset 1 = {0, 2, 11, 12, 13, 14, 15, 16, 17} := by decide
example : T3.Adj 2 42 ∧ ¬ T3.Adj 0 2 ∧ ¬ T3.Adj 3 4 := by decide

/-- Every non-root vertex of `T₃` has a smaller parent. -/
theorem T3parent_lt : ∀ v : Fin 43, v ≠ 0 → T3parent v < v := by decide

/-- `T₃` has `40` leaves. -/
theorem T3_leafCount : leafCount T3 = 40 := by decide

/-- `T₃` has `42` edges. -/
theorem T3_card_edgeSet : Fintype.card T3.edgeSet = 42 := by
  have hsum := T3.sum_degrees_eq_twice_card_edges
  have h84 : ∑ v, T3.degree v = 84 := by
    simp only [T3_degree]
    decide
  rw [SimpleGraph.edgeFinset_card] at hsum
  omega

/-- Every vertex of `T₃` is reachable from the root `0`. -/
theorem T3_reachable_zero (v : Fin 43) : T3.Reachable v 0 := by
  induction v using WellFoundedLT.induction with
  | _ v ih =>
    by_cases hv : v = 0
    · rw [hv]
    · have hlt := T3parent_lt v hv
      have hadj : T3.Adj v (T3parent v) := ⟨(ne_of_lt hlt).symm, Or.inl rfl⟩
      exact hadj.reachable.trans (ih _ hlt)

/-- `T₃` is a tree. -/
theorem T3_isTree : T3.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.connected_iff]
    exact ⟨fun u v => (T3_reachable_zero u).trans (T3_reachable_zero v).symm, ⟨0⟩⟩
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, T3_card_edgeSet, Fintype.card_fin]


/-- No two leaves of `T₃` are adjacent. -/
theorem T3_leaf_not_adj : ∀ u v, T3.degree u = 1 → T3.degree v = 1 → ¬ T3.Adj u v := by
  simp only [T3_degree]
  decide

/-- Condition (i) of Proposition 3.2 for `T₃`: every internal vertex has `42 < L(d)`. -/
theorem T3_large : ∀ v, T3.degree v ≠ 1 → 42 < weightLower (T3.degree v) := by
  simp only [T3_degree]
  decide

/-- Condition (ii) of Proposition 3.2 for `T₃`: the only nonadjacent pair of internal
vertices, `a` and `c`, has disjoint intervals `I₄₂(9) = [45, 342]`, `I₄₂(26) = [351, 767]`. -/
theorem T3_sep : ∀ u v, u ≠ v → T3.degree u ≠ 1 → T3.degree v ≠ 1 → ¬ T3.Adj u v →
    weightUpper 42 (T3.degree u) < weightLower (T3.degree v) ∨
      weightUpper 42 (T3.degree v) < weightLower (T3.degree u) := by
  simp only [T3_degree]
  decide

/-- Any bijective labeling of `T₃` uses exactly `42` labels. -/
theorem T3_label_count {m : ℕ} (f : T3.edgeSet ≃ Fin m) : m = 42 := by
  have h := Fintype.card_congr f
  rwa [Fintype.card_fin, T3_card_edgeSet, eq_comm] at h

/-- Every bijective labeling of `T₃` that distinguishes the adjacent internal pairs
`(a, b)` and `(b, c)` induces pairwise distinct vertex weights. -/
theorem T3_weight_injective_of_internal {m : ℕ} (f : T3.edgeSet ≃ Fin m)
    (hadj : ∀ u v, T3.Adj u v → T3.degree u ≠ 1 → T3.degree v ≠ 1 →
      weight T3 f u ≠ weight T3 f v) :
    Function.Injective (weight T3 f) := by
  obtain rfl := T3_label_count f
  exact weight_injective_of_separated T3 f T3_leaf_not_adj T3_large T3_sep hadj

/-- **Theorem 3.4 (core).** Every local antimagic labeling of `T₃` induces `43` pairwise
distinct vertex weights. -/
theorem T3_weight_injective {m : ℕ} (f : T3.edgeSet ≃ Fin m) (hf : IsLocalAntimagic T3 f) :
    Function.Injective (weight T3 f) :=
  T3_weight_injective_of_internal f fun u v h _ _ => hf u v h


/-! ## An explicit local antimagic labeling of `T₃`

The edge joining a non-root vertex `c` to its parent receives the label `c ∈ {1, …, 42}`. -/

/-- Each edge of `T₃` joins its larger endpoint, which is not the root, to that endpoint's
parent. -/
theorem T3_adj_eq : ∀ u v : Fin 43, T3.Adj u v →
    u ⊔ v ≠ 0 ∧ s(u, v) = s(u ⊔ v, T3parent (u ⊔ v)) := by
  decide

/-- The larger endpoint of an edge of `T₃` is not the root. -/
theorem T3_sup_ne_zero {e : Sym2 (Fin 43)} (he : e ∈ T3.edgeSet) : e.sup ≠ 0 := by
  induction e using Sym2.ind with
  | h u v => exact (T3_adj_eq u v he).1

/-- Each edge of `T₃` is `{c, parent c}` for its larger endpoint `c`. -/
theorem T3_edge_eq {e : Sym2 (Fin 43)} (he : e ∈ T3.edgeSet) :
    e = s(e.sup, T3parent e.sup) := by
  induction e using Sym2.ind with
  | h u v => exact (T3_adj_eq u v he).2

/-- The labeling of `T₃` giving the edge `{c, parent c}` the zero-based label `c - 1`. -/
def T3label : T3.edgeSet ≃ Fin 42 where
  toFun e := ⟨(e.1.sup : ℕ) - 1, by have := (e.1.sup).isLt; omega⟩
  invFun k := ⟨s(k.succ, T3parent k.succ),
    (show T3.Adj k.succ (T3parent k.succ) from
      ⟨(ne_of_lt (T3parent_lt k.succ (Fin.succ_ne_zero k))).symm, Or.inl rfl⟩)⟩
  left_inv e := by
    obtain ⟨e, he⟩ := e
    have h0 := T3_sup_ne_zero he
    have hsucc : (Fin.succ ⟨(e.sup : ℕ) - 1, by have := e.sup.isLt; omega⟩ : Fin 43) = e.sup := by
      ext
      have : (e.sup : ℕ) ≠ 0 := fun h => h0 (Fin.ext h)
      simp only [Fin.val_succ]
      omega
    apply Subtype.ext
    simp only
    rw [hsucc]
    exact (T3_edge_eq he).symm
  right_inv k := by
    have hlt := T3parent_lt k.succ (Fin.succ_ne_zero k)
    ext
    simp only [Sym2.sup_mk, Fin.val_succ, sup_eq_left.2 hlt.le]
    omega

/-- Under `T3label`, the label of an edge is its larger endpoint. -/
theorem edgeLabel_T3label {e : Sym2 (Fin 43)} (he : e ∈ T3.edgeSet) :
    edgeLabel T3 T3label e = (e.sup : ℕ) := by
  have h0 : (e.sup : ℕ) ≠ 0 := fun h => T3_sup_ne_zero he (Fin.ext h)
  simp only [edgeLabel, he, dite_true, T3label, Equiv.coe_fn_mk]
  omega

/-- Under `T3label`, the weight of `v` is the sum of the larger endpoints of its edges. -/
theorem weight_T3label (v : Fin 43) :
    weight T3 T3label v = ∑ w ∈ T3.neighborFinset v, ((s(v, w).sup : Fin 43) : ℕ) := by
  rw [weight_eq_sum_neighborFinset]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [SimpleGraph.mem_neighborFinset] at hw
  exact edgeLabel_T3label hw

/-- `T3label` induces weights `53`, `101`, `752` at `a`, `b`, `c`. -/
theorem weight_T3label_internal :
    weight T3 T3label 0 = 53 ∧ weight T3 T3label 1 = 101 ∧ weight T3 T3label 2 = 752 := by
  simp only [weight_T3label]
  decide

/-- `T3label` is a local antimagic labeling of `T₃` (indeed antimagic). -/
theorem T3label_isLocalAntimagic : IsLocalAntimagic T3 T3label := by
  refine isLocalAntimagic_of_injective T3 T3label (T3_weight_injective_of_internal T3label ?_)
  obtain ⟨h0, h1, h2⟩ := weight_T3label_internal
  have key : ∀ u v : Fin 43, T3.Adj u v → T3deg u ≠ 1 → T3deg v ≠ 1 →
      (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) := by
    decide
  intro u v huv hu hv
  rw [T3_degree] at hu hv
  rcases key u v huv hu hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

/-! ## Theorem 3.4 and the disproof of the leaf conjecture -/

/-- **Theorem 3.4** (Brondani–França, arXiv:2610.22783): `χ_la(T₃) = 43 = |V(T₃)|`. -/
theorem chiLA_T3 : chiLA T3 = 43 := by
  have hcard : Fintype.card T3.edgeSet = 42 := T3_card_edgeSet
  rw [chiLA_eq_card_of_forall_injective T3 ?_ ?_, Fintype.card_fin]
  · exact ⟨T3label.trans (finCongr hcard.symm), by
      intro u v huv
      have hw : ∀ x, weight T3 (T3label.trans (finCongr hcard.symm)) x = weight T3 T3label x := by
        intro x
        simp only [weight, edgeLabel, Equiv.trans_apply, finCongr_apply, Fin.val_cast]
      rw [hw, hw]
      exact T3label_isLocalAntimagic u v huv⟩
  · exact fun f hf => T3_weight_injective f hf

/-- **Theorem 3.4** (Brondani–França, arXiv:2610.22783): `χ_la(T₃) = ℓ(T₃) + 3`, where the
caterpillar `T₃ = Cat(8, 7, 25)` is a tree with `40` leaves. -/
theorem thm_3_4 : T3.IsTree ∧ leafCount T3 = 40 ∧ chiLA T3 = leafCount T3 + 3 := by
  refine ⟨T3_isTree, T3_leafCount, ?_⟩
  rw [chiLA_T3, T3_leafCount]

/-- **The leaf conjecture is false** (Brondani–França, arXiv:2610.22783, disproving
Conjecture 2.2 of Bača et al. and Premalatha et al.): it is not true that every tree `T` of
order at least three satisfies `χ_la(T) ≤ ℓ(T) + 2`. -/
theorem not_leaf_conjecture :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
      T.IsTree → 3 ≤ Fintype.card V → chiLA T ≤ leafCount T + 2 := by
  intro h
  have h3 := h (Fin 43) T3 T3_isTree (by simp)
  rw [chiLA_T3, T3_leafCount] at h3
  omega

end LocalAntimagicLeaf
