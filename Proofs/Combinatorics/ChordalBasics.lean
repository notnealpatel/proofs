import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic

set_option autoImplicit false

namespace ErdosCandidates.E81

open SimpleGraph

/-- No induced subgraph on at least four vertices is isomorphic to the cycle
on that many vertices. -/
def Chordal {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∀ (s : Finset V), 4 ≤ s.card →
    IsEmpty ((G.induce (s : Set V)) ≃g cycleGraph s.card)

/-- A family of cliques of size at least two containing every edge exactly once. -/
noncomputable def CliqueEdgePartition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : Finset (Finset V)) : Prop := by
  classical
  exact (∀ s ∈ P, G.IsClique (s : Set V) ∧ 2 ≤ s.card) ∧
    ∀ e ∈ G.edgeFinset, ∃! s, s ∈ P ∧ ∀ v ∈ e, v ∈ s

private theorem cycle_not_adj_zero_two (k : ℕ) :
    ¬ (cycleGraph (k + 4)).Adj (0 : Fin (k + 4)) 2 := by
  change ¬ (cycleGraph ((k + 2) + 2)).Adj 0 2
  rw [cycleGraph_adj]
  intro h
  rcases h with h | h
  · have hv := congrArg Fin.val h
    change ((k+4 - 2 % (k+4)) + 0) % (k+4) = 1 % (k+4) at hv
    have ht : 2 % (k+4) = 2 := Nat.mod_eq_of_lt (by omega)
    have ho : 1 % (k+4) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [ht, ho, Nat.add_zero, Nat.mod_eq_of_lt (by omega)] at hv
    omega
  · have hv := congrArg Fin.val h
    change ((k+4 - 0) + 2 % (k+4)) % (k+4) = 1 % (k+4) at hv
    have ht : 2 % (k+4) = 2 := Nat.mod_eq_of_lt (by omega)
    have ho : 1 % (k+4) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [ht, ho, Nat.sub_zero, Nat.add_mod_left, ht] at hv
    omega

/-- Every finite complete graph is chordal, including the empty complete graph. -/
theorem chordal_top {V : Type*} [Fintype V] [DecidableEq V] :
    Chordal (⊤ : SimpleGraph V) := by
  intro s hs
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs
  constructor
  intro f
  have hk' : s.card = k + 4 := by omega
  let f' : ((⊤ : SimpleGraph V).induce (s : Set V)) ≃g cycleGraph (k + 4) :=
    hk' ▸ f
  let x := f'.symm (0 : Fin (k + 4))
  let y := f'.symm (2 : Fin (k + 4))
  have hzero : (0 : Fin (k + 4)) ≠ 2 := by
    intro heq
    have hv := congrArg Fin.val heq
    change 0 = 2 % (k + 4) at hv
    rw [Nat.mod_eq_of_lt (by omega)] at hv
    omega
  have hxy : x ≠ y := fun h => hzero (f'.symm.injective h)
  have hval : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
  have hadj : ((⊤ : SimpleGraph V).induce (s : Set V)).Adj x y := hval
  have hcycle : (cycleGraph (k + 4)).Adj 0 2 := by
    have hmap := (f'.map_adj_iff).mpr hadj
    simpa only [x, y, RelIso.apply_symm_apply] using hmap
  exact cycle_not_adj_zero_two k hcycle

/-- The complete graph on five vertices is chordal. -/
theorem chordal_top_fin5 : Chordal (⊤ : SimpleGraph (Fin 5)) := chordal_top

/-- The four-cycle is not chordal: its full induced subgraph is itself. -/
theorem not_chordal_cycleGraph_four : ¬ Chordal (cycleGraph 4) := by
  intro h
  have hempty := h Finset.univ (by simp)
  have f : (cycleGraph 4).induce (↑(Finset.univ : Finset (Fin 4))) ≃g cycleGraph 4 := by
    rw [Finset.coe_univ]
    exact (cycleGraph 4).induceUnivIso
  exact hempty.false f

/-- The single full triangle is an edge partition of the complete graph on three vertices. -/
theorem cliqueEdgePartition_top_fin3 :
    CliqueEdgePartition (⊤ : SimpleGraph (Fin 3)) {(Finset.univ : Finset (Fin 3))} := by
  classical
  constructor
  · intro s hs
    have hs' : s = Finset.univ := Finset.mem_singleton.mp hs
    subst s
    exact ⟨IsClique.top _, by decide⟩
  · intro e he
    refine ⟨Finset.univ, ?_, ?_⟩
    · exact ⟨Finset.mem_singleton_self _, fun v hv => Finset.mem_univ v⟩
    · intro s hs
      exact Finset.mem_singleton.mp hs.1

example : Chordal (⊤ : SimpleGraph (Fin 0)) := chordal_top
example : Chordal (⊤ : SimpleGraph (Fin 1)) := chordal_top
example : Chordal (⊤ : SimpleGraph (Fin 5)) := chordal_top_fin5
example : ¬ Chordal (cycleGraph 4) := not_chordal_cycleGraph_four
example : CliqueEdgePartition (⊤ : SimpleGraph (Fin 3))
    {(Finset.univ : Finset (Fin 3))} := cliqueEdgePartition_top_fin3

end ErdosCandidates.E81
