/-
# Majority C-colouring of the Hamming graph `K_3 □ K_3 □ K_3`

## Source

arXiv 2608.27669, *Majority C-coloring in Cartesian products*, by
Cs. Bujtás, M. Dettlaff, H. Furmańczyk, A. Laskowska and Zs. Tuza.

Definition (Section 1.1, equation (1)): a surjective map
`φ : V(G) → [p]` is a *majority C-coloring* if every vertex `v ∈ V_i`
satisfies `|N_G(v) ∩ V_i| ≥ deg_G(v) / 2`; the *majority C-chromatic
number* `χ̄_≥(G)` is the maximum number of colours in such a colouring.

The third open problem of the concluding remarks asks:

> Determine `χ̄_≥(K_n^{□,k})` if `k ≥ 3` is odd and `n ≥ 3`.

The paper only gives `n^{(k-1)/2} ≤ χ̄_≥(K_n^{□,k})` (Proposition
`prop:imbalanced`(ii)) and the improvement of Theorem `thm:Ham-power-odd`
for `n = 5` or `n ≥ 7`; for `n = k = 3` it leaves `3 ≤ χ̄_≥ ≤ 5` open.

## Result

`χ̄_≥(K_3 □ K_3 □ K_3) = 4`.

* Lower bound: colour `(x, y, z)` by `z` when `y ∈ {0, 1}` and by a fourth
  colour when `y = 2`; the classes are three prisms `K_3 □ K_2` (inner
  degree 3 of 6) and one layer `K_3 □ K_3` (inner degree 4 of 6).
* Upper bound: every colour class `S` has `|S| ≥ 6` (every vertex of `S`
  has at least 3 neighbours in `S`, and the neighbourhood of a vertex is
  three disjoint edges), so there are at most `⌊27 / 6⌋ = 4` classes.
-/
import Mathlib

set_option autoImplicit false

namespace MajorityColoringCubeK3Product

open SimpleGraph Finset

/-! ## Definitions -/

/-- The majority condition of arXiv 2608.27669, equation (1): every vertex
shares its colour with at least half of its neighbours, i.e.
`deg_G(v) ≤ 2 · |N_G(v) ∩ V_{c(v)}|`. -/
def IsMajorityCColoring {V α : Type*} (G : SimpleGraph V) [∀ v, Fintype (G.neighborSet v)]
    [DecidableEq α] (c : V → α) : Prop :=
  ∀ v, G.degree v ≤ 2 * #{w ∈ G.neighborFinset v | c w = c v}

/-- The majority C-chromatic number `χ̄_≥(G)`: the largest `p` admitting a
surjective majority C-colouring `V(G) → [p]`.  (As an `sSup` in `ℕ` it is
only meaningful once the set is shown nonempty and bounded; the main
theorem below proves the stronger `IsGreatest` statement.) -/
noncomputable def majorityCChromaticNumber {V : Type*} (G : SimpleGraph V)
    [∀ v, Fintype (G.neighborSet v)] : ℕ :=
  sSup {p | ∃ c : V → Fin p, Function.Surjective c ∧ IsMajorityCColoring G c}

/-- Vertex type of `K_3 □ K_3 □ K_3`: triples `(x, (y, z))` over `Fin 3`. -/
abbrev V3 := Fin 3 × Fin 3 × Fin 3

/-- The three-dimensional Hamming graph `K_3 □ K_3 □ K_3`, as the Mathlib
Cartesian (box) product of complete graphs. -/
def K333 : SimpleGraph V3 :=
  (⊤ : SimpleGraph (Fin 3)) □ ((⊤ : SimpleGraph (Fin 3)) □ (⊤ : SimpleGraph (Fin 3)))

/-- Adjacency in `K_3 □ K_3 □ K_3`: the triples differ in exactly one
coordinate. -/
theorem K333_adj (x y : V3) : K333.Adj x y ↔
    (x.1 ≠ y.1 ∧ x.2 = y.2) ∨ (x.2.1 ≠ y.2.1 ∧ x.2.2 = y.2.2 ∧ x.1 = y.1) ∨
      (x.2.2 ≠ y.2.2 ∧ x.2.1 = y.2.1 ∧ x.1 = y.1) := by
  simp only [K333, boxProd_adj, top_adj, ne_eq]
  tauto

/-- Decidable adjacency for `K_3 □ K_3 □ K_3`, via `K333_adj`. -/
instance : DecidableRel K333.Adj := fun x y => decidable_of_iff' _ (K333_adj x y)

/-- The explicit four-colouring: `(x, y, z) ↦ z` if `y ≠ 2`, and colour `3`
on the layer `y = 2`. -/
def fourColoring (v : V3) : Fin 4 := if v.2.1 = 2 then 3 else Fin.castSucc v.2.2

/-! ## Examples -/

set_option maxRecDepth 10000 in
/-- `K_3 □ K_3 □ K_3` is 6-regular. -/
theorem K333_degree : ∀ v : V3, K333.degree v = 6 := by decide

example : K333.Adj (0, 0, 0) (1, 0, 0) ∧ ¬ K333.Adj (0, 0, 0) (1, 1, 0) := by decide

set_option maxRecDepth 10000 in
/-- The paper's Proposition `prop:imbalanced` colouring by the first
coordinate (3 colours) is a majority C-colouring. -/
example : IsMajorityCColoring K333 (fun v : V3 => v.1) := by
  unfold IsMajorityCColoring; decide

set_option maxRecDepth 10000 in
/-- The colouring by all coordinates (27 colours) is not. -/
example : ¬ IsMajorityCColoring K333 (fun v : V3 => v) := by
  unfold IsMajorityCColoring; decide

/-! ## Lower bound -/

set_option maxRecDepth 10000 in
/-- `fourColoring` is a majority C-colouring of `K_3 □ K_3 □ K_3`. -/
theorem fourColoring_isMajority : IsMajorityCColoring K333 fourColoring := by
  unfold IsMajorityCColoring; decide

/-- `fourColoring` uses all four colours. -/
theorem fourColoring_surjective : Function.Surjective fourColoring := by decide

/-! ## Upper bound -/

/-- Two adjacent vertices of `K_3 □ K_3 □ K_3` have at most one common
neighbour (the third point of their line). -/
theorem K333_common_neighbour_unique (v a w w' : V3) (hva : K333.Adj v a)
    (hvw : K333.Adj v w) (haw : K333.Adj a w) (hvw' : K333.Adj v w') (haw' : K333.Adj a w') :
    w = w' := by
  obtain ⟨v1, v2, v3⟩ := v
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨w1, w2, w3⟩ := w
  obtain ⟨b1, b2, b3⟩ := w'
  simp only [K333, boxProd_adj, top_adj, Prod.mk.injEq, ne_eq, Fin.ext_iff]
    at hva hvw haw hvw' haw' ⊢
  omega

/-- In any graph, three vertices cannot each have exactly one neighbour
among themselves (a 1-regular graph has an even number of vertices). -/
theorem false_of_card_three_of_unique_neighbour {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (T : Finset V) (hT : #T = 3)
    (hex : ∀ a ∈ T, ∃ b ∈ T, G.Adj a b)
    (huniq : ∀ a ∈ T, ∀ b ∈ T, ∀ b' ∈ T, G.Adj a b → G.Adj a b' → b = b') : False := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.1 hT
  have ha : a ∈ ({a, b, c} : Finset V) := by simp
  have hb : b ∈ ({a, b, c} : Finset V) := by simp
  have hc : c ∈ ({a, b, c} : Finset V) := by simp
  have hmem : ∀ x ∈ ({a, b, c} : Finset V), x = a ∨ x = b ∨ x = c := by simp
  obtain ⟨x, hx, hax⟩ := hex a ha
  rcases hmem x hx with hxa | hxb | hxc
  · rw [hxa] at hax
    exact G.irrefl hax
  · -- `a ~ b`; the neighbour of `c` is `a` or `b`
    rw [hxb] at hax
    obtain ⟨y, hy, hcy⟩ := hex c hc
    rcases hmem y hy with hya | hyb | hyc
    · rw [hya] at hcy
      exact hbc (huniq a ha b hb c hc hax hcy.symm)
    · rw [hyb] at hcy
      exact hac (huniq b hb a ha c hc hax.symm hcy.symm)
    · rw [hyc] at hcy
      exact G.irrefl hcy
  · -- `a ~ c`; the neighbour of `b` is `a` or `c`
    rw [hxc] at hax
    obtain ⟨y, hy, hby⟩ := hex b hb
    rcases hmem y hy with hya | hyb | hyc
    · rw [hya] at hby
      exact hbc (huniq a ha c hc b hb hax hby.symm).symm
    · rw [hyb] at hby
      exact G.irrefl hby
    · rw [hyc] at hby
      exact hab (huniq c hc a ha b hb hax.symm hby.symm)

/-- Load-bearing lemma: a nonempty vertex set `S` of `K_3 □ K_3 □ K_3` in
which every vertex has at least 3 neighbours inside `S` has at least 6
vertices. -/
theorem six_le_card_of_three_le_inner_degree (S : Finset V3) (hne : S.Nonempty)
    (hS : ∀ u ∈ S, 3 ≤ #{w ∈ K333.neighborFinset u | w ∈ S}) : 6 ≤ #S := by
  obtain ⟨v, hv⟩ := hne
  by_contra hlt
  rw [not_le] at hlt
  set T : Finset V3 := {w ∈ K333.neighborFinset v | w ∈ S} with hTdef
  set R : Finset V3 := {w ∈ S | w ≠ v ∧ ¬ K333.Adj v w} with hRdef
  have hT : 3 ≤ #T := hS v hv
  have hsum : 1 + #T + #R ≤ #S := by
    have hdisj : Disjoint T R := by
      rw [Finset.disjoint_left]
      intro w hwT hwR
      simp only [hTdef, hRdef, mem_filter, mem_neighborFinset] at hwT hwR
      exact hwR.2.2 hwT.1
    have hvn : v ∉ T ∪ R := by
      simp [hTdef, hRdef]
    have hsub : insert v (T ∪ R) ⊆ S := by
      intro w hw
      simp only [hTdef, hRdef, mem_insert, mem_union, mem_filter] at hw
      rcases hw with rfl | hw | hw
      · exact hv
      · exact hw.2
      · exact hw.1
    calc 1 + #T + #R = #(insert v (T ∪ R)) := by
          rw [card_insert_of_notMem hvn, card_union_of_disjoint hdisj]; ring
      _ ≤ #S := card_le_card hsub
  -- every `a ∈ T` has at most one neighbour in `T`
  have hcommon : ∀ a ∈ T, #{w ∈ K333.neighborFinset a | w ∈ T} ≤ 1 := by
    intro a ha
    rw [card_le_one]
    intro w hw w' hw'
    simp only [hTdef, mem_filter, mem_neighborFinset] at ha hw hw'
    exact K333_common_neighbour_unique v a w w' ha.1 hw.2.1 hw.1 hw'.2.1 hw'.1
  -- the `S`-neighbours of `a ∈ T` lie in `{v} ∪ (N(a) ∩ T) ∪ R`
  have hloc : ∀ a ∈ T,
      #{w ∈ K333.neighborFinset a | w ∈ S} ≤ 1 + #{w ∈ K333.neighborFinset a | w ∈ T} + #R := by
    intro a ha
    have hsub : {w ∈ K333.neighborFinset a | w ∈ S} ⊆
        insert v ({w ∈ K333.neighborFinset a | w ∈ T} ∪ R) := by
      intro w hw
      simp only [mem_filter, mem_neighborFinset] at hw
      simp only [hTdef, hRdef, mem_insert, mem_union, mem_filter, mem_neighborFinset]
      by_cases hwv : w = v
      · exact Or.inl hwv
      · by_cases hadj : K333.Adj v w
        · exact Or.inr (Or.inl ⟨hw.1, hadj, hw.2⟩)
        · exact Or.inr (Or.inr ⟨hw.2, hwv, hadj⟩)
    calc #{w ∈ K333.neighborFinset a | w ∈ S}
        ≤ #(insert v ({w ∈ K333.neighborFinset a | w ∈ T} ∪ R)) := card_le_card hsub
      _ ≤ #({w ∈ K333.neighborFinset a | w ∈ T} ∪ R) + 1 := card_insert_le _ _
      _ ≤ #{w ∈ K333.neighborFinset a | w ∈ T} + #R + 1 := by
          gcongr; exact card_union_le _ _
      _ = 1 + #{w ∈ K333.neighborFinset a | w ∈ T} + #R := by ring
  -- hence each `a ∈ T` has a neighbour in `T`, and `|T| = 3`
  have hTsub : T ⊆ S := by
    intro w hw
    simp only [hTdef, mem_filter] at hw
    exact hw.2
  have hpos : ∀ a ∈ T, 1 ≤ #{w ∈ K333.neighborFinset a | w ∈ T} := by
    intro a ha
    have h1 := hS a (hTsub ha)
    have h2 := hloc a ha
    have h3 := hcommon a ha
    omega
  have hT3 : #T = 3 := by
    obtain ⟨a, ha⟩ : T.Nonempty := card_pos.1 (by omega)
    have h1 := hS a (hTsub ha)
    have h2 := hloc a ha
    have h3 := hcommon a ha
    omega
  refine false_of_card_three_of_unique_neighbour K333 T hT3 ?_ ?_
  · intro a ha
    obtain ⟨b, hb⟩ := card_pos.1 (hpos a ha)
    simp only [mem_filter, mem_neighborFinset] at hb
    exact ⟨b, hb.2, hb.1⟩
  · intro a ha b hb b' hb' hab hab'
    have hle := hcommon a ha
    rw [card_le_one] at hle
    exact hle b (by simp [hab, hb]) b' (by simp [hab', hb'])

/-- Every colour class of a majority C-colouring of `K_3 □ K_3 □ K_3` has
at least 6 vertices. -/
theorem six_le_card_fiber {α : Type*} [DecidableEq α] (c : V3 → α)
    (hc : IsMajorityCColoring K333 c) (i : α) (hi : i ∈ univ.image c) :
    6 ≤ #{v ∈ (univ : Finset V3) | c v = i} := by
  obtain ⟨v, -, hvi⟩ := mem_image.1 hi
  refine six_le_card_of_three_le_inner_degree _ ⟨v, by simp [hvi]⟩ ?_
  intro u hu
  simp only [mem_filter, mem_univ, true_and] at hu
  have hmaj := hc u
  rw [K333_degree u] at hmaj
  have hcongr : #{w ∈ K333.neighborFinset u | w ∈ ({v ∈ (univ : Finset V3) | c v = i})} =
      #{w ∈ K333.neighborFinset u | c w = c u} := by
    congr 1
    refine filter_congr ?_
    intro w _
    simp [hu]
  rw [hcongr]
  omega

/-- Upper bound: any majority C-colouring of `K_3 □ K_3 □ K_3`, with colours
in an arbitrary type, uses at most 4 colours. -/
theorem card_image_le_four {α : Type*} [DecidableEq α] (c : V3 → α)
    (hc : IsMajorityCColoring K333 c) : #(univ.image c) ≤ 4 := by
  have hsum := card_eq_sum_card_image c (univ : Finset V3)
  have hlow : #(univ.image c) * 6 ≤ ∑ i ∈ univ.image c, #{v ∈ (univ : Finset V3) | c v = i} := by
    rw [← smul_eq_mul, ← sum_const]
    exact sum_le_sum (fun i hi => six_le_card_fiber c hc i hi)
  have h27 : #(univ : Finset V3) = 27 := by simp
  omega

/-! ## Main theorem -/

/-- `4` is the greatest number of colours of a surjective majority
C-colouring of `K_3 □ K_3 □ K_3` (arXiv 2608.27669, smallest open instance
of the concluding open problem on `χ̄_≥(K_n^{□,k})` for odd `k ≥ 3`). -/
theorem isGreatest_K333 :
    IsGreatest {p | ∃ c : V3 → Fin p, Function.Surjective c ∧ IsMajorityCColoring K333 c} 4 := by
  refine ⟨⟨fourColoring, fourColoring_surjective, fourColoring_isMajority⟩, ?_⟩
  rintro p ⟨c, hsurj, hc⟩
  have himg : univ.image c = univ := by
    ext i
    simp only [mem_image, mem_univ, true_and, iff_true]
    exact hsurj i
  have h := card_image_le_four c hc
  rw [himg, card_univ, Fintype.card_fin] at h
  exact h

/-- **Main theorem.** The majority C-chromatic number of the Hamming graph
`K_3 □ K_3 □ K_3` is `4`: `χ̄_≥(K_3^{□,3}) = 4` (arXiv 2608.27669 leaves
`3 ≤ χ̄_≥(K_3^{□,3}) ≤ 5` open). -/
theorem majorityCChromaticNumber_K333 : majorityCChromaticNumber K333 = 4 :=
  isGreatest_K333.csSup_eq

end MajorityColoringCubeK3Product
