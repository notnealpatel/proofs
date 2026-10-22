/-
# Row budgets for majority colourings of cylinders

ZeHua Lu, *Exact majority C-colourings of balanced Hamming graphs and grids*,
arXiv:2609.31674, Section 5.1, Lemma 9 and the counting bound for Theorem 2(1).
For `m ≥ 4`, `n ≥ 2`, each majority class `S` of `C_m □ P_n` has row budget
`B(S) = ∑_y ⌊|S ∩ L_y|/2⌋ ≥ 2`. Summing over a partition into `c` classes
gives `2c ≤ n⌊m/2⌋`.

An explicit nine-class partition attains the bound at `(m,n) = (7,6)`.
This refutes Bujtás–Dettlaff–Furmańczyk–Laskowska, arXiv:2608.27669v1,
Conjecture 4, which predicts 10 classes there.

Majority means `d(v) ≤ 2 d_S(v)`, equivalently `⌈d(v)/2⌉ ≤ d_S(v)`.
The hypothesis `2 ≤ n` is necessary: the bound fails for `C_4 □ P_1`.
Neighbour-set degrees are independent of the chosen `Fintype` instance.
-/
import Mathlib

set_option autoImplicit false

open SimpleGraph Finset

namespace MajorityColouringCylinderRowBudget

/-- Adjacency in Mathlib's path graph `pathGraph n` is decidable: `u ~ v` iff
`u + 1 = v` or `v + 1 = u` as natural numbers. -/
instance instDecidableRelPathGraphAdj (n : ℕ) : DecidableRel (pathGraph n).Adj :=
  fun _ _ => decidable_of_iff' _ pathGraph_adj

/-- A **majority class** of a locally finite graph `G` (arXiv:2609.31674, §1): a
nonempty vertex set `S` such that every `v ∈ S` has at least half of its
neighbours in `S`, i.e. `deg v ≤ 2 · |N(v) ∩ S|` (equivalently
`|N(v) ∩ S| ≥ ⌈deg v / 2⌉`). -/
def IsMajorityClass {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]
    (S : Finset V) : Prop :=
  S.Nonempty ∧ ∀ v ∈ S, G.degree v ≤ 2 * #(G.neighborFinset v ∩ S)

/-- Majority classes are decidable (used for finite checks). -/
instance instDecidableIsMajorityClass {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [G.LocallyFinite] (S : Finset V) : Decidable (IsMajorityClass G S) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The **majority C-colouring number** `M(G)` of a finite graph: the largest
number of parts of a partition of `V(G)` into majority classes
(arXiv:2609.31674, §1). Defined as a supremum in `ℕ`; it is meaningful when the
set of attainable part counts is nonempty, which holds for every finite graph
with at least one vertex (the trivial partition `{V}`). -/
noncomputable def majorityColouringNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite] : ℕ :=
  sSup {c | ∃ P : Finpartition (univ : Finset V), #P.parts = c ∧
    ∀ S ∈ P.parts, IsMajorityClass G S}

/-- The row `L_y ∩ S` of a vertex set `S` of `C_m □ P_n` at height `y`. -/
abbrev rowSlice {m n : ℕ} (S : Finset (Fin m × Fin n)) (y : Fin n) :
    Finset (Fin m × Fin n) :=
  S.filter (fun w => w.2 = y)

/-- The **row budget** `B(S) = ∑_y ⌊|S ∩ L_y| / 2⌋` of a vertex set `S` of
`C_m □ P_n` (arXiv:2609.31674, Lemma 9). -/
def rowBudget {m n : ℕ} (S : Finset (Fin m × Fin n)) : ℕ :=
  ∑ y : Fin n, #(rowSlice S y) / 2

/-! ### Examples -/

/-- A boundary vertex of `C_7 □ P_6` has degree three. -/
example : (cycleGraph 7 □ pathGraph 6).degree (3, 0) = 3 := by decide

/-- An interior vertex of `C_7 □ P_6` has degree four. -/
example : (cycleGraph 7 □ pathGraph 6).degree (3, 2) = 4 := by decide

/-- A singleton is never a majority class in `C_7 □ P_6`. -/
example : ¬ IsMajorityClass (cycleGraph 7 □ pathGraph 6) {(0, 0)} := by decide

/-- A `2 × 2` block on the boundary rows is a majority class. -/
example : IsMajorityClass (cycleGraph 7 □ pathGraph 6) {(0, 0), (1, 0), (0, 1), (1, 1)} := by
  decide

/-- A horizontal pair on the boundary row is not a majority class (each vertex has
degree three but only one neighbour in the pair). -/
example : ¬ IsMajorityClass (cycleGraph 7 □ pathGraph 6) {(0, 0), (1, 0)} := by decide

/-- The row budget of a `2 × 2` block is two. -/
example : rowBudget ({(0, 0), (1, 0), (0, 1), (1, 1)} : Finset (Fin 7 × Fin 6)) = 2 := by
  decide

/-- The row budget of a full row of `C_7` is `⌊7/2⌋ = 3`. -/
example : rowBudget ((univ : Finset (Fin 7)) ×ˢ ({0} : Finset (Fin 6))) = 3 := by decide

/-! ### Lemma 9: the row budget -/

/-- In `C_{k+3} □ P_n` with `n ≥ 2`, every vertex has degree at least three. -/
lemma three_le_degree (k n : ℕ) (hn : 2 ≤ n) (v : Fin (k + 3) × Fin n) :
    3 ≤ (cycleGraph (k + 3) □ pathGraph n).degree v := by
  rw [degree_boxProd, cycleGraph_degree_three_le]
  have hpos : 0 < (pathGraph n).degree v.2 := by
    rw [degree, Finset.card_pos]
    by_cases hy : v.2.val + 1 < n
    · exact ⟨⟨v.2.val + 1, hy⟩, by rw [mem_neighborFinset, pathGraph_adj]; left; rfl⟩
    · refine ⟨⟨v.2.val - 1, by omega⟩, ?_⟩
      rw [mem_neighborFinset, pathGraph_adj]
      right
      simp only
      omega
  omega

/-- For `v ∈ S`, the `S`-neighbours of `v` split into horizontal ones (other
vertices of `S` in the row of `v`) and vertical ones:
`|N(v) ∩ S| + 1 ≤ |S ∩ L_{v.2}| + |N_vert(v) ∩ S|`. -/
lemma card_neighborFinset_inter_add_one_le (k n : ℕ) (S : Finset (Fin (k + 3) × Fin n))
    (v : Fin (k + 3) × Fin n) (hv : v ∈ S) :
    #((cycleGraph (k + 3) □ pathGraph n).neighborFinset v ∩ S) + 1 ≤
      #(rowSlice S v.2) + #(({v.1} ×ˢ (pathGraph n).neighborFinset v.2) ∩ S) := by
  rw [neighborFinset_boxProd, Finset.disjUnion_eq_union, Finset.union_inter_distrib_right]
  have hA : ((cycleGraph (k + 3)).neighborFinset v.1 ×ˢ {v.2}) ∩ S ⊆
      (rowSlice S v.2).erase v := by
    intro w hw
    simp only [mem_inter, mem_product, mem_singleton, mem_neighborFinset] at hw
    simp only [mem_erase, mem_filter]
    refine ⟨?_, hw.2, hw.1.2⟩
    rintro rfl
    exact hw.1.1.ne rfl
  have hcA := card_le_card hA
  rw [card_erase_of_mem (by simp [hv])] at hcA
  have hpos : 0 < #(rowSlice S v.2) := card_pos.mpr ⟨v, by simp [hv]⟩
  have hunion := card_union_le (((cycleGraph (k + 3)).neighborFinset v.1 ×ˢ {v.2}) ∩ S)
    (({v.1} ×ˢ (pathGraph n).neighborFinset v.2) ∩ S)
  omega

/-- If a vertex `v` of a majority class `S` has at most one vertical
`S`-neighbour, then the row of `v` contains at least two vertices of `S`. -/
lemma two_le_card_rowSlice (k n : ℕ) (hn : 2 ≤ n) (S : Finset (Fin (k + 3) × Fin n))
    (hS : IsMajorityClass (cycleGraph (k + 3) □ pathGraph n) S)
    (v : Fin (k + 3) × Fin n) (hv : v ∈ S)
    (hvert : #(({v.1} ×ˢ (pathGraph n).neighborFinset v.2) ∩ S) ≤ 1) :
    2 ≤ #(rowSlice S v.2) := by
  have h3 := three_le_degree k n hn v
  have hmaj := hS.2 v hv
  have hle := card_neighborFinset_inter_add_one_le k n S v hv
  omega

/-- If a vertex `v = (x, y)` of a majority class `S` has no vertical
`S`-neighbour, then both of its cycle neighbours, in particular `(x + 1, y)`,
lie in `S`. -/
lemma add_one_mem_of_vertical_eq_empty (k n : ℕ) (hn : 2 ≤ n)
    (S : Finset (Fin (k + 3) × Fin n))
    (hS : IsMajorityClass (cycleGraph (k + 3) □ pathGraph n) S)
    (v : Fin (k + 3) × Fin n) (hv : v ∈ S)
    (hvert : ({v.1} ×ˢ (pathGraph n).neighborFinset v.2) ∩ S = ∅) :
    (v.1 + 1, v.2) ∈ S := by
  have h3 := three_le_degree k n hn v
  have hmaj := hS.2 v hv
  rw [neighborFinset_boxProd, Finset.disjUnion_eq_union, Finset.union_inter_distrib_right,
    hvert, Finset.union_empty] at hmaj
  have hsub : ((cycleGraph (k + 3)).neighborFinset v.1 ×ˢ {v.2}) ∩ S ⊆
      (cycleGraph (k + 3)).neighborFinset v.1 ×ˢ {v.2} := inter_subset_left
  have hcard : #((cycleGraph (k + 3)).neighborFinset v.1 ×ˢ {v.2}) = 2 := by
    rw [card_product, card_singleton, mul_one, ← degree, cycleGraph_degree_three_le]
  have heq := eq_of_subset_of_card_le hsub (by have := card_le_card hsub; omega)
  have hmem : (v.1 + 1, v.2) ∈ (cycleGraph (k + 3)).neighborFinset v.1 ×ˢ {v.2} := by
    rw [cycleGraph_neighborFinset]
    simp
  rw [← heq] at hmem
  exact (mem_inter.mp hmem).2

/-- A vertex in the lowest occupied row of `S` has at most one vertical
`S`-neighbour (the one directly above it). -/
lemma card_vertical_le_one_of_min (k n : ℕ) (S : Finset (Fin (k + 3) × Fin n))
    (v : Fin (k + 3) × Fin n) (hmin : ∀ w ∈ S, v.2 ≤ w.2) :
    #(({v.1} ×ˢ (pathGraph n).neighborFinset v.2) ∩ S) ≤ 1 := by
  rw [card_le_one]
  intro a ha b hb
  simp only [mem_inter, mem_product, mem_singleton, mem_neighborFinset, pathGraph_adj] at ha hb
  have ha' := hmin a ha.2
  have hb' := hmin b hb.2
  rw [Fin.le_def] at ha' hb'
  exact Prod.ext (ha.1.1.trans hb.1.1.symm) (Fin.ext (by omega))

/-- A vertex in the highest occupied row of `S` has at most one vertical
`S`-neighbour (the one directly below it). -/
lemma card_vertical_le_one_of_max (k n : ℕ) (S : Finset (Fin (k + 3) × Fin n))
    (v : Fin (k + 3) × Fin n) (hmax : ∀ w ∈ S, w.2 ≤ v.2) :
    #(({v.1} ×ˢ (pathGraph n).neighborFinset v.2) ∩ S) ≤ 1 := by
  rw [card_le_one]
  intro a ha b hb
  simp only [mem_inter, mem_product, mem_singleton, mem_neighborFinset, pathGraph_adj] at ha hb
  have ha' := hmax a ha.2
  have hb' := hmax b hb.2
  rw [Fin.le_def] at ha' hb'
  exact Prod.ext (ha.1.1.trans hb.1.1.symm) (Fin.ext (by omega))

open Fin.NatCast in
/-- A majority class contained in a single row `L_y` is the whole row. -/
lemma mem_of_subset_row (k n : ℕ) (hn : 2 ≤ n) (S : Finset (Fin (k + 3) × Fin n))
    (hS : IsMajorityClass (cycleGraph (k + 3) □ pathGraph n) S) (y : Fin n)
    (hrow : ∀ w ∈ S, w.2 = y) (v : Fin (k + 3) × Fin n) (hv : v ∈ S) (x : Fin (k + 3)) :
    (x, y) ∈ S := by
  have hstep : ∀ w ∈ S, (w.1 + 1, w.2) ∈ S := by
    intro w hw
    refine add_one_mem_of_vertical_eq_empty k n hn S hS w hw
      (eq_empty_of_forall_notMem fun a ha => ?_)
    simp only [mem_inter, mem_product, mem_singleton, mem_neighborFinset] at ha
    have h1 := hrow a ha.2
    have h2 := hrow w hw
    have hadj := ha.1.2
    rw [h1, h2] at hadj
    exact hadj.ne rfl
  have hall : ∀ j : ℕ, (v.1 + (Nat.cast j : Fin (k + 3)), y) ∈ S := by
    intro j
    induction j with
    | zero =>
      rw [Nat.cast_zero, add_zero, ← hrow v hv]
      exact hv
    | succ j ih =>
      have hnext := hstep _ ih
      simpa [add_assoc] using hnext
  have hx := hall (x - v.1).val
  simpa [Fin.cast_val_eq_self] using hx

/-- **Lemma 9 (row budget), arXiv:2609.31674.** For `m ≥ 4`, `n ≥ 2` and any
majority class `S` of `C_m □ P_n`, `B(S) = ∑_y ⌊|S ∩ L_y|/2⌋ ≥ 2`. Here
`m = k + 3` with `1 ≤ k`. -/
theorem two_le_rowBudget (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n)
    (S : Finset (Fin (k + 3) × Fin n))
    (hS : IsMajorityClass (cycleGraph (k + 3) □ pathGraph n) S) :
    2 ≤ rowBudget S := by
  unfold rowBudget
  obtain ⟨v₀, hv₀, hmin⟩ := S.exists_min_image Prod.snd hS.1
  obtain ⟨v₁, hv₁, hmax⟩ := S.exists_max_image Prod.snd hS.1
  by_cases hsame : v₀.2 = v₁.2
  · -- `S` occupies a single row, so it is the whole row.
    have hrow : ∀ w ∈ S, w.2 = v₀.2 := fun w hw =>
      le_antisymm (hsame ▸ hmax w hw) (hmin w hw)
    have hsub : (univ : Finset (Fin (k + 3))).image (fun x => (x, v₀.2)) ⊆
        rowSlice S v₀.2 := by
      intro w hw
      obtain ⟨x, -, rfl⟩ := mem_image.mp hw
      exact mem_filter.mpr ⟨mem_of_subset_row k n hn S hS v₀.2 hrow v₀ hv₀ x, rfl⟩
    have hcard : k + 3 ≤ #(rowSlice S v₀.2) := by
      have hle := card_le_card hsub
      rwa [card_image_of_injective _ (fun a b h => (Prod.ext_iff.mp h).1), card_univ,
        Fintype.card_fin] at hle
    have hsingle := single_le_sum (f := fun y => #(rowSlice S y) / 2)
      (fun _ _ => Nat.zero_le _) (mem_univ v₀.2)
    have hdiv : 2 ≤ #(rowSlice S v₀.2) / 2 := by omega
    exact hdiv.trans hsingle
  · -- The lowest and highest occupied rows are distinct and each holds two vertices.
    have h₀ := two_le_card_rowSlice k n hn S hS v₀ hv₀
      (card_vertical_le_one_of_min k n S v₀ hmin)
    have h₁ := two_le_card_rowSlice k n hn S hS v₁ hv₁
      (card_vertical_le_one_of_max k n S v₁ hmax)
    have hpair := sum_le_sum_of_subset (f := fun y => #(rowSlice S y) / 2)
      (subset_univ ({v₀.2, v₁.2} : Finset (Fin n)))
    rw [sum_pair hsame] at hpair
    have hd₀ : 1 ≤ #(rowSlice S v₀.2) / 2 := by omega
    have hd₁ : 1 ≤ #(rowSlice S v₁.2) / 2 := by omega
    exact le_trans (by omega) hpair

/-! ### The counting bound `2c ≤ n ⌊m/2⌋` -/

/-- Superadditivity of `⌊·/2⌋`: `∑ ⌊f i / 2⌋ ≤ ⌊(∑ f i) / 2⌋`. -/
lemma sum_div_two_le {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    ∑ i ∈ s, f i / 2 ≤ (∑ i ∈ s, f i) / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num), sum_mul]
  exact sum_le_sum fun i _ => Nat.div_mul_le_self (f i) 2

/-- The parts of a partition of `Fin m × Fin n` meet each row in at most `m`
vertices altogether. -/
lemma sum_card_rowSlice_le {m n : ℕ} (P : Finpartition (univ : Finset (Fin m × Fin n)))
    (y : Fin n) : ∑ S ∈ P.parts, #(rowSlice S y) ≤ m := by
  have h : ∑ S ∈ P.parts, #(rowSlice S y) = #(rowSlice (univ : Finset (Fin m × Fin n)) y) := by
    simp only [card_filter]
    have hb := sum_biUnion (f := fun i : Fin m × Fin n => if i.2 = y then 1 else 0) P.disjoint
    rw [P.biUnion_parts] at hb
    exact hb.symm
  rw [h]
  calc #(rowSlice (univ : Finset (Fin m × Fin n)) y)
        ≤ #((univ : Finset (Fin m)) ×ˢ {y}) :=
        card_le_card (fun w hw => by
          simp only [mem_filter] at hw
          exact mem_product.mpr ⟨mem_univ _, mem_singleton.mpr hw.2⟩)
    _ = m := by simp

/-- **Row-budget bound, arXiv:2609.31674 §5.1 (upper bound of Theorem 2(1)).**
For `m ≥ 4` and `n ≥ 2`, every partition of `V(C_m □ P_n)` into majority classes
has `c` parts with `2c ≤ n ⌊m/2⌋`. -/
theorem two_mul_card_parts_le (m n : ℕ) (hm : 4 ≤ m) (hn : 2 ≤ n)
    (P : Finpartition (univ : Finset (Fin m × Fin n)))
    (hP : ∀ S ∈ P.parts, IsMajorityClass (cycleGraph m □ pathGraph n) S) :
    2 * #P.parts ≤ n * (m / 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  calc 2 * #P.parts = ∑ _S ∈ P.parts, 2 := by rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ S ∈ P.parts, ∑ y : Fin n, #(rowSlice S y) / 2 :=
        sum_le_sum fun S hS => two_le_rowBudget k n (by omega) hn S (hP S hS)
    _ = ∑ y : Fin n, ∑ S ∈ P.parts, #(rowSlice S y) / 2 := sum_comm
    _ ≤ ∑ y : Fin n, (∑ S ∈ P.parts, #(rowSlice S y)) / 2 :=
        sum_le_sum fun y _ => sum_div_two_le _ _
    _ ≤ ∑ _y : Fin n, (k + 3) / 2 :=
        sum_le_sum fun y _ => Nat.div_le_div_right (sum_card_rowSlice_le P y)
    _ = n * ((k + 3) / 2) := by simp

/-! ### The explicit nine-colouring of `C_7 □ P_6` -/

/-- A surjective colouring all of whose colour classes satisfy `Q` yields a
partition of the vertex set into exactly `k` parts, each satisfying `Q`. -/
lemma exists_finpartition_of_colouring {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (c : V → Fin k) (hc : Function.Surjective c) (Q : Finset V → Prop)
    (hQ : ∀ i, Q (univ.filter (fun v => c v = i))) :
    ∃ P : Finpartition (univ : Finset V), #P.parts = k ∧ ∀ S ∈ P.parts, Q S := by
  let _ : DecidableRel (Setoid.ker c).r := fun a b => decidable_of_iff (c a = c b) Iff.rfl
  let P := Finpartition.ofSetoid (Setoid.ker c)
  have hparts : P.parts =
      (univ : Finset (Fin k)).image (fun i => univ.filter (fun v => c v = i)) := by
    change (univ.image fun a => univ.filter (fun b => (Setoid.ker c).r a b)) = _
    ext T
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨c a, ?_⟩
      ext b
      simp only [mem_filter, mem_univ, true_and]
      exact eq_comm
    · rintro ⟨i, rfl⟩
      obtain ⟨a, rfl⟩ := hc i
      refine ⟨a, ?_⟩
      ext b
      simp only [mem_filter, mem_univ, true_and]
      exact eq_comm
  refine ⟨P, ?_, ?_⟩
  · rw [hparts, card_image_of_injective, card_univ, Fintype.card_fin]
    intro i j hij
    obtain ⟨a, rfl⟩ := hc i
    have h := Finset.ext_iff.mp hij a
    simp only [mem_filter, mem_univ, true_and] at h
    exact h.mp trivial
  · intro S hS
    rw [hparts] at hS
    obtain ⟨i, -, rfl⟩ := mem_image.mp hS
    exact hQ i

/-- The nine-colouring of `C_7 □ P_6` from arXiv:2609.31674 §5.1: rows are paired
(`y / 2`), and columns are cut into the blocks `{0,1}`, `{2,3}`, `{4,5,6}`. -/
def nineColouring (v : Fin 7 × Fin 6) : Fin 9 :=
  ⟨3 * (v.2.val / 2) + min (v.1.val / 2) 2, by omega⟩

/-- The colouring matches the paper's display: the first row reads
`A A B B C C C`, the third row `D D E E F F F`. -/
example : (List.finRange 7).map (fun x => (nineColouring (x, 0)).val) = [0, 0, 1, 1, 2, 2, 2] ∧
    (List.finRange 7).map (fun x => (nineColouring (x, 2)).val) = [3, 3, 4, 4, 5, 5, 5] := by
  decide

/-- **Lower bound at `(7, 6)`, arXiv:2609.31674 §5.1.** `C_7 □ P_6` has a
partition into nine majority classes. -/
theorem exists_nine_class_partition_C7_P6 :
    ∃ P : Finpartition (univ : Finset (Fin 7 × Fin 6)), #P.parts = 9 ∧
      ∀ S ∈ P.parts, IsMajorityClass (cycleGraph 7 □ pathGraph 6) S := by
  refine exists_finpartition_of_colouring nineColouring (by decide) _ ?_
  decide

/-- **`M(C_7 □ P_6) = 9`** (arXiv:2609.31674, Theorem 2(1) at `(m, n) = (7, 6)`). -/
theorem majorityColouringNumber_C7_P6 :
    majorityColouringNumber (cycleGraph 7 □ pathGraph 6) = 9 := by
  apply IsGreatest.csSup_eq
  refine ⟨exists_nine_class_partition_C7_P6, ?_⟩
  rintro c ⟨P, rfl, hP⟩
  have hbound := two_mul_card_parts_le 7 6 (by norm_num) (by norm_num) P hP
  omega

/-- **Conjecture 4 of arXiv:2608.27669v1 fails at `C_7 □ P_6`.** The conjecture
predicts `M(C_m □ P_n) = 1 + ⌊m/2⌋⌊n/2⌋`, which is `10` at `(m, n) = (7, 6)`;
in fact no partition of `C_7 □ P_6` into `1 + ⌊7/2⌋⌊6/2⌋` majority classes
exists. -/
theorem not_exists_partition_C7_P6 :
    ¬ ∃ P : Finpartition (univ : Finset (Fin 7 × Fin 6)),
      #P.parts = 1 + (7 / 2) * (6 / 2) ∧
        ∀ S ∈ P.parts, IsMajorityClass (cycleGraph 7 □ pathGraph 6) S := by
  rintro ⟨P, hcard, hP⟩
  have hbound := two_mul_card_parts_le 7 6 (by norm_num) (by norm_num) P hP
  omega

/-- **Conjecture 4 of arXiv:2608.27669v1 is false**, stated for the majority
colouring number: `M(C_7 □ P_6) ≠ 1 + ⌊7/2⌋⌊6/2⌋`. -/
theorem not_conjecture4_C7_P6 :
    majorityColouringNumber (cycleGraph 7 □ pathGraph 6) ≠ 1 + (7 / 2) * (6 / 2) := by
  rw [majorityColouringNumber_C7_P6]
  norm_num

/-! ### Boundary: the hypothesis `2 ≤ n` is necessary -/

/-- For `n = 1` the bound `2c ≤ n ⌊m/2⌋` fails: `C_4 □ P_1` has a partition into
two majority classes (two horizontal pairs), while `1 · ⌊4/2⌋ < 2 · 2`. -/
theorem n_one_counterexample :
    ∃ P : Finpartition (univ : Finset (Fin 4 × Fin 1)),
      (∀ S ∈ P.parts, IsMajorityClass (cycleGraph 4 □ pathGraph 1) S) ∧
        1 * (4 / 2) < 2 * #P.parts := by
  obtain ⟨P, hcard, hP⟩ := exists_finpartition_of_colouring
    (fun v : Fin 4 × Fin 1 => (⟨v.1.val / 2, by omega⟩ : Fin 2)) (by decide)
    (IsMajorityClass (cycleGraph 4 □ pathGraph 1)) (by decide)
  exact ⟨P, hP, by rw [hcard]; norm_num⟩

end MajorityColouringCylinderRowBudget
