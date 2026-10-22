/-
# Chvátal–Lovász: every finite digraph has a quasi-kernel

V. Chvátal and L. Lovász, *Every directed graph has a semi-kernel*,
Hypergraph Seminar (1974). Also cited as [CL] in J. Ai, G. Gutin, X. Liu
and X. Meng, *Small and large quasi-kernels: a weighted transfer theorem*,
arXiv:2610.23487, Section 1.

## Conventions

* Digraphs are Mathlib's `Digraph V` on a finite vertex type.
* Independence quantifies over *pairs of distinct* vertices.  For the
  paper's loopless digraphs this is the paper's notion
  (`isIndependent_iff_of_loopless`); the theorem below holds for every
  `Digraph`, loops allowed, so no looplessness hypothesis is needed.
* "Reachable by a directed path of length at most two" is the disjunction
  of length 0, 1, 2 walks starting in `Q`.  For loopless digraphs a walk of
  length at most two reaching `z ∉ Q` contains a path of length at most two,
  so walks and paths give the same set.
-/
import Mathlib

set_option autoImplicit false

namespace ChvatalLovaszQuasiKernel

variable {V : Type*}

/-- A set `Q` of vertices of `G` is *independent* if there is no arc between
any pair of distinct vertices of `Q`. -/
def IsIndependent (G : Digraph V) (Q : Finset V) : Prop :=
  ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → ¬ G.Adj x y

/-- `z` lies in `N^{≤2}[Q]`: it is reachable from `Q` by a directed path of
length at most two (length `0`, `1`, or `2`). -/
def ReachLeTwo (G : Digraph V) (Q : Finset V) (z : V) : Prop :=
  z ∈ Q ∨ (∃ q ∈ Q, G.Adj q z) ∨ ∃ q ∈ Q, ∃ w, G.Adj q w ∧ G.Adj w z

/-- `Q` is a *quasi-kernel* of `G`: `Q` is independent and every vertex is
reachable from `Q` by a directed path of length at most two. -/
def IsQuasiKernel (G : Digraph V) (Q : Finset V) : Prop :=
  IsIndependent G Q ∧ ∀ z, ReachLeTwo G Q z

/-- For a loopless digraph, independence over distinct pairs agrees with the
paper's "no arc between any pair of vertices of `Q`". -/
theorem isIndependent_iff_of_loopless (G : Digraph V) (hloop : ∀ v, ¬ G.Adj v v)
    (Q : Finset V) : IsIndependent G Q ↔ ∀ x ∈ Q, ∀ y ∈ Q, ¬ G.Adj x y := by
  constructor
  · intro h x hx y hy hxy
    by_cases hne : x = y
    · subst hne
      exact hloop x hxy
    · exact h x hx y hy hne hxy
  · intro h x hx y hy _
    exact h x hx y hy

/-! ## Example: the directed 4-cycle (the paper's tightness example) -/

/-- The directed 4-cycle `0 → 1 → 2 → 3 → 0`. -/
def cycle4 : Digraph (Fin 4) where
  Adj i j := j = i + 1

instance : DecidableRel cycle4.Adj := fun i j => inferInstanceAs (Decidable (j = i + 1))

/-- `{0, 2}` is a quasi-kernel of the directed 4-cycle. -/
example : IsQuasiKernel cycle4 {0, 2} := by
  unfold IsQuasiKernel IsIndependent ReachLeTwo
  decide

/-- `{0}` is not a quasi-kernel of the directed 4-cycle: `3` is at distance 3. -/
example : ¬ IsQuasiKernel cycle4 {0} := by
  unfold IsQuasiKernel IsIndependent ReachLeTwo
  decide

/-- `{0, 1}` is not independent in the directed 4-cycle. -/
example : ¬ IsIndependent cycle4 {0, 1} := by
  unfold IsIndependent
  decide

/-! ## The relative statement, by strong induction on the vertex set -/

/-- Relative Chvátal–Lovász: inside every finite vertex set `S`, there is an
independent `Q ⊆ S` from which every vertex of `S` is reached by a directed
path of length at most two whose middle vertex lies in `S`. -/
theorem exists_relQuasiKernel (G : Digraph V) (S : Finset V) :
    ∃ Q ⊆ S, IsIndependent G Q ∧ ∀ z ∈ S,
      z ∈ Q ∨ (∃ q ∈ Q, G.Adj q z) ∨ ∃ q ∈ Q, ∃ w ∈ S, G.Adj q w ∧ G.Adj w z := by
  classical
  induction S using Finset.strongInduction with
  | H S ih =>
  rcases S.eq_empty_or_nonempty with hS | ⟨v, hv⟩
  · subst hS
    exact ⟨∅, subset_refl _, fun x hx => absurd hx (Finset.notMem_empty x),
      fun z hz => absurd hz (Finset.notMem_empty z)⟩
  -- delete the closed out-neighbourhood of `v`
  set S' : Finset V := S.filter (fun x => x ≠ v ∧ ¬ G.Adj v x) with hS'
  have hS'sub : S' ⊆ S := Finset.filter_subset _ _
  have hvS' : v ∉ S' := by simp [hS']
  have hlt : S' ⊂ S := Finset.ssubset_iff_subset_ne.mpr
    ⟨hS'sub, fun h => hvS' (h ▸ hv)⟩
  obtain ⟨Q', hQ'S', hQ'ind, hQ'reach⟩ := ih S' hlt
  have hmemS' : ∀ x, x ∈ S' ↔ x ∈ S ∧ x ≠ v ∧ ¬ G.Adj v x := fun x => by
    simp [hS']
  -- every vertex of `S` outside `S'` is `v` or an out-neighbour of `v`
  have hcases : ∀ z ∈ S, z ∉ S' → z = v ∨ G.Adj v z := by
    intro z hz hz'
    rw [hmemS'] at hz'
    by_contra hcon
    push Not at hcon
    exact hz' ⟨hz, hcon.1, hcon.2⟩
  by_cases hadj : ∃ q ∈ Q', G.Adj q v
  · -- `Q'` already reaches `v` and its out-neighbours
    obtain ⟨q, hq, hqv⟩ := hadj
    refine ⟨Q', hQ'S'.trans hS'sub, hQ'ind, fun z hz => ?_⟩
    by_cases hzS' : z ∈ S'
    · rcases hQ'reach z hzS' with h | h | ⟨q₁, hq₁, w, hw, h₁, h₂⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨q₁, hq₁, w, hS'sub hw, h₁, h₂⟩)
    · rcases hcases z hz hzS' with rfl | hvz
      · exact Or.inr (Or.inl ⟨q, hq, hqv⟩)
      · exact Or.inr (Or.inr ⟨q, hq, v, hv, hqv, hvz⟩)
  · -- `v` can be added to `Q'`
    push Not at hadj
    refine ⟨insert v Q', Finset.insert_subset hv (hQ'S'.trans hS'sub), ?_, fun z hz => ?_⟩
    · intro x hx y hy hxy
      rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact absurd rfl hxy
      · exact ((hmemS' y).mp (hQ'S' hy)).2.2
      · exact hadj x hx
      · exact hQ'ind x hx y hy hxy
    · by_cases hzS' : z ∈ S'
      · rcases hQ'reach z hzS' with h | ⟨q₁, hq₁, h⟩ | ⟨q₁, hq₁, w, hw, h₁, h₂⟩
        · exact Or.inl (Finset.mem_insert_of_mem h)
        · exact Or.inr (Or.inl ⟨q₁, Finset.mem_insert_of_mem hq₁, h⟩)
        · exact Or.inr (Or.inr ⟨q₁, Finset.mem_insert_of_mem hq₁, w, hS'sub hw, h₁, h₂⟩)
      · rcases hcases z hz hzS' with rfl | hvz
        · exact Or.inl (Finset.mem_insert_self _ _)
        · exact Or.inr (Or.inl ⟨v, Finset.mem_insert_self _ _, hvz⟩)

/-- **Chvátal–Lovász (1974).** Every finite digraph has a quasi-kernel: an
independent set `Q` from which every vertex is reachable by a directed path of
length at most two.  Cited in arXiv:2610.23487, Section 1, as [CL]. -/
theorem exists_isQuasiKernel [Finite V] (G : Digraph V) : ∃ Q, IsQuasiKernel G Q := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  obtain ⟨Q, -, hind, hreach⟩ := exists_relQuasiKernel G (Finset.univ : Finset V)
  refine ⟨Q, hind, fun z => ?_⟩
  rcases hreach z (Finset.mem_univ z) with h | h | ⟨q, hq, w, -, h₁, h₂⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨q, hq, w, h₁, h₂⟩)

end ChvatalLovaszQuasiKernel
