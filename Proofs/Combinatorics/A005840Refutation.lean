/-
# A005840 — Mathar's connected-threshold-graph conjecture is false

R. J. Mathar's conjecture in OEIS A005840 (April 29, 2019) identifies
A285868, read with offset 1, with the number of connected labeled threshold
graphs. David Galvin's comment (October 18, 2021) instead identifies A317057.

At `n = 4`, A285868 predicts 20 graphs. The 23 explicit, pairwise distinct
connected threshold graphs below give a counterexample.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A005840Refutation

open SimpleGraph

/-! ## Definition layer -/

/-- A graph `G` is a **threshold graph** when every nonempty finite set `s` of
vertices contains a vertex that is isolated or dominating in the subgraph
induced on `s`.

This is the hereditary form of the Chvátal–Hammer creation definition (a
threshold graph is built from the empty graph by repeatedly adding an isolated
or a dominating vertex): in a creation sequence the last-added vertex of `s` is
isolated or dominating in `G[s]`; conversely the condition lets one peel off an
isolated or dominating vertex one at a time. -/
def IsThreshold {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ s : Finset V, s.Nonempty →
    ∃ v ∈ s, (∀ w ∈ s, ¬ G.Adj v w) ∨ (∀ w ∈ s, w ≠ v → G.Adj v w)

/-- The number of connected labeled threshold graphs on the vertex set
`Fin n` (A317057 for `n ≥ 1`). -/
noncomputable def connectedThresholdCount (n : ℕ) : ℕ :=
  Nat.card {G : SimpleGraph (Fin n) // G.Connected ∧ IsThreshold G}

/-- The triangle A285867: `T(n, k) = S2(n, k) * k! + S2(n, k-1) * (k-1)!`,
with `S2` the Stirling numbers of the second kind (A048993) and the second
summand absent for `k = 0`. -/
def a285867 (n k : ℕ) : ℕ :=
  Nat.stirlingSecond n k * k.factorial +
    if k = 0 then 0 else Nat.stirlingSecond n (k - 1) * (k - 1).factorial

/-- A285868 (offset 0): the row sums `∑_{k=0}^{n} T(n, k)` of A285867. -/
def a285868 (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), a285867 n k

/-- The first rows of A285867, `1 | 0 1 | 0 1 3 | 0 1 7 12`. -/
example : a285867 0 0 = 1 ∧ a285867 1 0 = 0 ∧ a285867 1 1 = 1 ∧
    a285867 2 2 = 3 ∧ a285867 3 2 = 7 ∧ a285867 3 3 = 12 := by decide

/-- The first listed terms of A285868, `1, 1, 4, 20, 126, 962`. -/
theorem a285868_values :
    a285868 0 = 1 ∧ a285868 1 = 1 ∧ a285868 2 = 4 ∧ a285868 3 = 20 ∧
      a285868 4 = 126 ∧ a285868 5 = 962 := by decide

/-! ## The conjecture -/

/-- Mathar's conjecture (OEIS A005840, April 29, 2019): A285868 read
with offset 1 counts connected labeled threshold graphs on `n ≥ 1` vertices.
The predicted count is `a285868 (n-1)`; indexing by `n+1` avoids subtraction. -/
def Conjecture : Prop :=
  ∀ n : ℕ, connectedThresholdCount (n + 1) = a285868 n

/-! ## Connected threshold graphs on four vertices -/

/-- A graph with a dominating vertex is connected. -/
lemma connected_of_dominating {V : Type*} (G : SimpleGraph V) (v : V)
    (hv : ∀ w, w ≠ v → G.Adj v w) : G.Connected := by
  have hreach : ∀ a, G.Reachable a v := by
    intro a
    by_cases ha : a = v
    · rw [ha]
    · exact (hv a ha).reachable.symm
  haveI : Nonempty V := ⟨v⟩
  exact ⟨fun a b => (hreach a).trans (hreach b).symm⟩

/-- The graph on `Fin 4` with the listed edges. -/
def ofEdges (l : List (Fin 4 × Fin 4)) : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel fun a b => (a, b) ∈ l

/-- Adjacency in `ofEdges l` is decidable (unfolds to list membership). -/
instance (l : List (Fin 4 × Fin 4)) : DecidableRel (ofEdges l).Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ((a, b) ∈ l ∨ (b, a) ∈ l)))

/-- The 23 connected threshold graphs on `Fin 4`, each paired with a
dominating vertex. -/
def witnessData : List (List (Fin 4 × Fin 4) × Fin 4) :=
  [([(0, 1), (0, 2), (0, 3)], 0),
   ([(0, 1), (0, 2), (0, 3), (1, 2)], 0),
   ([(0, 1), (0, 2), (0, 3), (1, 3)], 0),
   ([(0, 1), (1, 2), (1, 3)], 1),
   ([(0, 1), (0, 2), (1, 2), (1, 3)], 1),
   ([(0, 1), (0, 3), (1, 2), (1, 3)], 1),
   ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)], 0),
   ([(0, 1), (0, 2), (0, 3), (2, 3)], 0),
   ([(0, 2), (1, 2), (2, 3)], 2),
   ([(0, 1), (0, 2), (1, 2), (2, 3)], 2),
   ([(0, 2), (0, 3), (1, 2), (2, 3)], 2),
   ([(0, 1), (0, 2), (0, 3), (1, 2), (2, 3)], 0),
   ([(0, 3), (1, 3), (2, 3)], 3),
   ([(0, 1), (0, 3), (1, 3), (2, 3)], 3),
   ([(0, 2), (0, 3), (1, 3), (2, 3)], 3),
   ([(0, 1), (0, 2), (0, 3), (1, 3), (2, 3)], 0),
   ([(0, 1), (1, 2), (1, 3), (2, 3)], 1),
   ([(0, 2), (1, 2), (1, 3), (2, 3)], 2),
   ([(0, 1), (0, 2), (1, 2), (1, 3), (2, 3)], 1),
   ([(0, 3), (1, 2), (1, 3), (2, 3)], 3),
   ([(0, 1), (0, 3), (1, 2), (1, 3), (2, 3)], 1),
   ([(0, 2), (0, 3), (1, 2), (1, 3), (2, 3)], 2),
   ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)], 0)]

/-- There are 23 witness records. -/
lemma witnessData_length : witnessData.length = 23 := rfl

/-- The `i`-th witness graph. -/
def witness (i : Fin 23) : SimpleGraph (Fin 4) :=
  ofEdges (witnessData.get (i.cast witnessData_length.symm)).1

/-- The `i`-th witness's recorded dominating vertex. -/
def witnessDom (i : Fin 23) : Fin 4 :=
  (witnessData.get (i.cast witnessData_length.symm)).2

/-- Adjacency in each witness graph is decidable. -/
instance (i : Fin 23) : DecidableRel (witness i).Adj := fun a b =>
  inferInstanceAs
    (Decidable ((ofEdges (witnessData.get (i.cast witnessData_length.symm)).1).Adj a b))

/-- Each witness's recorded vertex is adjacent to every other vertex. -/
lemma witness_dominating :
    ∀ i : Fin 23, ∀ w : Fin 4, w ≠ witnessDom i → (witness i).Adj (witnessDom i) w := by
  decide

/-- Each witness graph is a threshold graph. -/
lemma witness_threshold : ∀ i : Fin 23, IsThreshold (witness i) := by
  unfold IsThreshold
  decide

/-- Distinct witness indices give graphs differing in some adjacency. -/
lemma witness_distinct :
    ∀ i j : Fin 23, i ≠ j → ∃ a b : Fin 4, ¬ ((witness i).Adj a b ↔ (witness j).Adj a b) := by
  decide

/-- The witness graphs are pairwise distinct. -/
lemma witness_injective : Function.Injective witness := by
  intro i j hij
  by_contra hne
  obtain ⟨a, b, hab⟩ := witness_distinct i j hne
  exact hab (by rw [hij])

/-- The path `P₄` (`0 - 1 - 2 - 3`), one of
the three forbidden induced subgraphs `P₄, C₄, 2K₂`, is not a threshold
graph. -/
example : ¬ IsThreshold (ofEdges [(0, 1), (1, 2), (2, 3)]) := by
  unfold IsThreshold
  decide

/-- `C₄` is not a threshold graph. -/
example : ¬ IsThreshold (ofEdges [(0, 1), (1, 2), (2, 3), (0, 3)]) := by
  unfold IsThreshold
  decide

/-- `2K₂` is not a threshold graph. -/
example : ¬ IsThreshold (ofEdges [(0, 1), (2, 3)]) := by
  unfold IsThreshold
  decide

/-- The star `K₁,₃` is a threshold graph. -/
example : IsThreshold (ofEdges [(0, 1), (0, 2), (0, 3)]) := by
  unfold IsThreshold
  decide

/-- `K₄` is a threshold graph. -/
example : IsThreshold (ofEdges [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]) := by
  unfold IsThreshold
  decide

/-- There is exactly one connected threshold graph on one
vertex (A317057(1) = 1). -/
theorem connectedThresholdCount_one : connectedThresholdCount 1 = 1 := by
  have hsub : Subsingleton (SimpleGraph (Fin 1)) := by
    refine ⟨fun G H => ?_⟩
    ext a b
    have hab : a = b := Subsingleton.elim a b
    subst hab
    simp
  have hbot : (⊥ : SimpleGraph (Fin 1)).Connected ∧ IsThreshold (⊥ : SimpleGraph (Fin 1)) :=
    ⟨connected_of_dominating _ 0 (fun w hw => absurd (Subsingleton.elim w 0) hw),
      fun s ⟨v, hv⟩ => ⟨v, hv, Or.inl fun w _ => by simp⟩⟩
  rw [connectedThresholdCount, Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun G H => Subtype.ext (hsub.elim G.1 H.1)⟩, ⟨⟨⊥, hbot⟩⟩⟩

/-- There are at least 23 connected threshold graphs on four labeled
vertices. -/
theorem twentythree_le_connectedThresholdCount_four : 23 ≤ connectedThresholdCount 4 := by
  let f : Fin 23 → {G : SimpleGraph (Fin 4) // G.Connected ∧ IsThreshold G} := fun i =>
    ⟨witness i, connected_of_dominating _ (witnessDom i) (witness_dominating i),
      witness_threshold i⟩
  have hf : Function.Injective f := fun i j hij =>
    witness_injective (congrArg Subtype.val hij)
  have hle := Nat.card_le_card_of_injective f hf
  simpa [connectedThresholdCount] using hle

/-! ## The refutation -/

/-- Mathar's A005840 conjecture fails at `n = 4`: A285868 with offset 1
predicts 20 connected labeled threshold graphs, but `witness` gives
23 pairwise distinct threshold graphs with dominating vertices. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  have heq : connectedThresholdCount 4 = 20 := by
    rw [hconj 3, a285868_values.2.2.2.1]
  have hle := twentythree_le_connectedThresholdCount_four
  omega

end Candidates.A005840Refutation
