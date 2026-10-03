import Erdos.Erdos64.SubcubicFunnelH7
import Mathlib.Combinatorics.SimpleGraph.Sum
import Erdos.Erdos64.SubcubicFunnelLocal

set_option autoImplicit false

namespace Erdos64.SubcubicFunnel
open SimpleGraph

/-- K4 with each edge at its center subdivided once, in the order
`(s,t,a,a',b,c,c')`. The triangle is `{2,3,5}`. -/
def h7Symm : SimpleGraph (Fin 7) where
  Adj i j := (i, j) ∈ ([(2,3), (3,5), (5,2), (4,0), (0,2), (4,1), (1,3), (4,6), (6,5)] : List (Fin 7 × Fin 7)) ∨
    (j, i) ∈ ([(2,3), (3,5), (5,2), (4,0), (0,2), (4,1), (1,3), (4,6), (6,5)] : List (Fin 7 × Fin 7))
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro i; fin_cases i <;> decide⟩

instance : DecidableRel h7Symm.Adj := fun _i _j => inferInstanceAs (Decidable (_ ∨ _))

/-- Adjacency is exactly the nine specified undirected edges. -/
theorem h7Symm_adj_iff (i j : Fin 7) : h7Symm.Adj i j ↔
    (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 5) ∨ (i = 5 ∧ j = 2) ∨ (i = 4 ∧ j = 0) ∨ (i = 0 ∧ j = 2) ∨ (i = 4 ∧ j = 1) ∨ (i = 1 ∧ j = 3) ∨ (i = 4 ∧ j = 6) ∨ (i = 6 ∧ j = 5) ∨ (i = 3 ∧ j = 2) ∨ (i = 5 ∧ j = 3) ∨ (i = 2 ∧ j = 5) ∨ (i = 0 ∧ j = 4) ∨ (i = 2 ∧ j = 0) ∨ (i = 1 ∧ j = 4) ∨ (i = 3 ∧ j = 1) ∨ (i = 6 ∧ j = 4) ∨ (i = 5 ∧ j = 6) := by
  fin_cases i <;> fin_cases j <;> decide

example : h7Symm.Adj 2 3 ∧ h7Symm.Adj 4 6 ∧ ¬ h7Symm.Adj 4 2 := by decide


set_option maxHeartbeats 1000000 in
private theorem four_neighbors {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v ≤ 3)
    {v a b c d : V} (ha : G.Adj v a) (hb : G.Adj v b)
    (hc : G.Adj v c) (hd : G.Adj v d) :
    a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d := by
  classical
  by_cases hab : a = b
  · exact Or.inl hab
  by_cases hac : a = c
  · exact Or.inr (Or.inl hac)
  by_cases hbc : b = c
  · exact Or.inr (Or.inr (Or.inr (Or.inl hbc)))
  have hn : [a,b,c].Nodup := by simp [hab, hac, hbc]
  have he := neighbor_eq_of_three hdeg hn ha hb hc hd
  rcases he with he | he | he
  · exact Or.inr (Or.inr (Or.inl he.symm))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he.symm))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr he.symm))))

set_option maxHeartbeats 1000000 in
private theorem mixed_labels_ne {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) (f : h7 ↪g G) (g : h7Symm ↪g G)
    (i j : Fin 7) : f i ≠ g j := by
  have fn01 : f 0 ≠ f 1 := fun h => (by decide : (0 : Fin 7) ≠ 1) (f.injective h)
  have fn02 : f 0 ≠ f 2 := fun h => (by decide : (0 : Fin 7) ≠ 2) (f.injective h)
  have fn03 : f 0 ≠ f 3 := fun h => (by decide : (0 : Fin 7) ≠ 3) (f.injective h)
  have fn04 : f 0 ≠ f 4 := fun h => (by decide : (0 : Fin 7) ≠ 4) (f.injective h)
  have fn05 : f 0 ≠ f 5 := fun h => (by decide : (0 : Fin 7) ≠ 5) (f.injective h)
  have fn06 : f 0 ≠ f 6 := fun h => (by decide : (0 : Fin 7) ≠ 6) (f.injective h)
  have fn12 : f 1 ≠ f 2 := fun h => (by decide : (1 : Fin 7) ≠ 2) (f.injective h)
  have fn13 : f 1 ≠ f 3 := fun h => (by decide : (1 : Fin 7) ≠ 3) (f.injective h)
  have fn14 : f 1 ≠ f 4 := fun h => (by decide : (1 : Fin 7) ≠ 4) (f.injective h)
  have fn15 : f 1 ≠ f 5 := fun h => (by decide : (1 : Fin 7) ≠ 5) (f.injective h)
  have fn16 : f 1 ≠ f 6 := fun h => (by decide : (1 : Fin 7) ≠ 6) (f.injective h)
  have fn23 : f 2 ≠ f 3 := fun h => (by decide : (2 : Fin 7) ≠ 3) (f.injective h)
  have fn24 : f 2 ≠ f 4 := fun h => (by decide : (2 : Fin 7) ≠ 4) (f.injective h)
  have fn25 : f 2 ≠ f 5 := fun h => (by decide : (2 : Fin 7) ≠ 5) (f.injective h)
  have fn26 : f 2 ≠ f 6 := fun h => (by decide : (2 : Fin 7) ≠ 6) (f.injective h)
  have fn34 : f 3 ≠ f 4 := fun h => (by decide : (3 : Fin 7) ≠ 4) (f.injective h)
  have fn35 : f 3 ≠ f 5 := fun h => (by decide : (3 : Fin 7) ≠ 5) (f.injective h)
  have fn36 : f 3 ≠ f 6 := fun h => (by decide : (3 : Fin 7) ≠ 6) (f.injective h)
  have fn45 : f 4 ≠ f 5 := fun h => (by decide : (4 : Fin 7) ≠ 5) (f.injective h)
  have fn46 : f 4 ≠ f 6 := fun h => (by decide : (4 : Fin 7) ≠ 6) (f.injective h)
  have fn56 : f 5 ≠ f 6 := fun h => (by decide : (5 : Fin 7) ≠ 6) (f.injective h)
  have fe00 : ¬ G.Adj (f 0) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 0 0) hh
  have fe01 : ¬ G.Adj (f 0) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 0 1) hh
  have fe02 : G.Adj (f 0) (f 2) := f.map_rel_iff.mpr (by decide)
  have fe03 : G.Adj (f 0) (f 3) := f.map_rel_iff.mpr (by decide)
  have fe04 : ¬ G.Adj (f 0) (f 4) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 0 4) hh
  have fe05 : ¬ G.Adj (f 0) (f 5) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 0 5) hh
  have fe06 : ¬ G.Adj (f 0) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 0 6) hh
  have fe10 : ¬ G.Adj (f 1) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 1 0) hh
  have fe11 : ¬ G.Adj (f 1) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 1 1) hh
  have fe12 : ¬ G.Adj (f 1) (f 2) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 1 2) hh
  have fe13 : ¬ G.Adj (f 1) (f 3) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 1 3) hh
  have fe14 : ¬ G.Adj (f 1) (f 4) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 1 4) hh
  have fe15 : G.Adj (f 1) (f 5) := f.map_rel_iff.mpr (by decide)
  have fe16 : G.Adj (f 1) (f 6) := f.map_rel_iff.mpr (by decide)
  have fe20 : G.Adj (f 2) (f 0) := f.map_rel_iff.mpr (by decide)
  have fe21 : ¬ G.Adj (f 2) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 2 1) hh
  have fe22 : ¬ G.Adj (f 2) (f 2) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 2 2) hh
  have fe23 : G.Adj (f 2) (f 3) := f.map_rel_iff.mpr (by decide)
  have fe24 : G.Adj (f 2) (f 4) := f.map_rel_iff.mpr (by decide)
  have fe25 : ¬ G.Adj (f 2) (f 5) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 2 5) hh
  have fe26 : ¬ G.Adj (f 2) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 2 6) hh
  have fe30 : G.Adj (f 3) (f 0) := f.map_rel_iff.mpr (by decide)
  have fe31 : ¬ G.Adj (f 3) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 3 1) hh
  have fe32 : G.Adj (f 3) (f 2) := f.map_rel_iff.mpr (by decide)
  have fe33 : ¬ G.Adj (f 3) (f 3) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 3 3) hh
  have fe34 : ¬ G.Adj (f 3) (f 4) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 3 4) hh
  have fe35 : ¬ G.Adj (f 3) (f 5) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 3 5) hh
  have fe36 : G.Adj (f 3) (f 6) := f.map_rel_iff.mpr (by decide)
  have fe40 : ¬ G.Adj (f 4) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 4 0) hh
  have fe41 : ¬ G.Adj (f 4) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 4 1) hh
  have fe42 : G.Adj (f 4) (f 2) := f.map_rel_iff.mpr (by decide)
  have fe43 : ¬ G.Adj (f 4) (f 3) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 4 3) hh
  have fe44 : ¬ G.Adj (f 4) (f 4) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 4 4) hh
  have fe45 : G.Adj (f 4) (f 5) := f.map_rel_iff.mpr (by decide)
  have fe46 : ¬ G.Adj (f 4) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 4 6) hh
  have fe50 : ¬ G.Adj (f 5) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 5 0) hh
  have fe51 : G.Adj (f 5) (f 1) := f.map_rel_iff.mpr (by decide)
  have fe52 : ¬ G.Adj (f 5) (f 2) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 5 2) hh
  have fe53 : ¬ G.Adj (f 5) (f 3) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 5 3) hh
  have fe54 : G.Adj (f 5) (f 4) := f.map_rel_iff.mpr (by decide)
  have fe55 : ¬ G.Adj (f 5) (f 5) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 5 5) hh
  have fe56 : G.Adj (f 5) (f 6) := f.map_rel_iff.mpr (by decide)
  have fe60 : ¬ G.Adj (f 6) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 6 0) hh
  have fe61 : G.Adj (f 6) (f 1) := f.map_rel_iff.mpr (by decide)
  have fe62 : ¬ G.Adj (f 6) (f 2) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 6 2) hh
  have fe63 : G.Adj (f 6) (f 3) := f.map_rel_iff.mpr (by decide)
  have fe64 : ¬ G.Adj (f 6) (f 4) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 6 4) hh
  have fe65 : G.Adj (f 6) (f 5) := f.map_rel_iff.mpr (by decide)
  have fe66 : ¬ G.Adj (f 6) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7.Adj 6 6) hh
  have fs2 (x : V) (hx : G.Adj (f 2) x) : x = f 0 ∨ x = f 3 ∨ x = f 4 :=
    neighbor_eq_of_three hdeg (List.Nodup.map f.injective (by decide : ([0,3,4] : List (Fin 7)).Nodup)) fe20 fe23 fe24 hx
  have fs3 (x : V) (hx : G.Adj (f 3) x) : x = f 0 ∨ x = f 2 ∨ x = f 6 :=
    neighbor_eq_of_three hdeg (List.Nodup.map f.injective (by decide : ([0,2,6] : List (Fin 7)).Nodup)) fe30 fe32 fe36 hx
  have fs5 (x : V) (hx : G.Adj (f 5) x) : x = f 1 ∨ x = f 4 ∨ x = f 6 :=
    neighbor_eq_of_three hdeg (List.Nodup.map f.injective (by decide : ([1,4,6] : List (Fin 7)).Nodup)) fe51 fe54 fe56 hx
  have fs6 (x : V) (hx : G.Adj (f 6) x) : x = f 1 ∨ x = f 3 ∨ x = f 5 :=
    neighbor_eq_of_three hdeg (List.Nodup.map f.injective (by decide : ([1,3,5] : List (Fin 7)).Nodup)) fe61 fe63 fe65 hx
  have gn01 : g 0 ≠ g 1 := fun h => (by decide : (0 : Fin 7) ≠ 1) (g.injective h)
  have gn02 : g 0 ≠ g 2 := fun h => (by decide : (0 : Fin 7) ≠ 2) (g.injective h)
  have gn03 : g 0 ≠ g 3 := fun h => (by decide : (0 : Fin 7) ≠ 3) (g.injective h)
  have gn04 : g 0 ≠ g 4 := fun h => (by decide : (0 : Fin 7) ≠ 4) (g.injective h)
  have gn05 : g 0 ≠ g 5 := fun h => (by decide : (0 : Fin 7) ≠ 5) (g.injective h)
  have gn06 : g 0 ≠ g 6 := fun h => (by decide : (0 : Fin 7) ≠ 6) (g.injective h)
  have gn12 : g 1 ≠ g 2 := fun h => (by decide : (1 : Fin 7) ≠ 2) (g.injective h)
  have gn13 : g 1 ≠ g 3 := fun h => (by decide : (1 : Fin 7) ≠ 3) (g.injective h)
  have gn14 : g 1 ≠ g 4 := fun h => (by decide : (1 : Fin 7) ≠ 4) (g.injective h)
  have gn15 : g 1 ≠ g 5 := fun h => (by decide : (1 : Fin 7) ≠ 5) (g.injective h)
  have gn16 : g 1 ≠ g 6 := fun h => (by decide : (1 : Fin 7) ≠ 6) (g.injective h)
  have gn23 : g 2 ≠ g 3 := fun h => (by decide : (2 : Fin 7) ≠ 3) (g.injective h)
  have gn24 : g 2 ≠ g 4 := fun h => (by decide : (2 : Fin 7) ≠ 4) (g.injective h)
  have gn25 : g 2 ≠ g 5 := fun h => (by decide : (2 : Fin 7) ≠ 5) (g.injective h)
  have gn26 : g 2 ≠ g 6 := fun h => (by decide : (2 : Fin 7) ≠ 6) (g.injective h)
  have gn34 : g 3 ≠ g 4 := fun h => (by decide : (3 : Fin 7) ≠ 4) (g.injective h)
  have gn35 : g 3 ≠ g 5 := fun h => (by decide : (3 : Fin 7) ≠ 5) (g.injective h)
  have gn36 : g 3 ≠ g 6 := fun h => (by decide : (3 : Fin 7) ≠ 6) (g.injective h)
  have gn45 : g 4 ≠ g 5 := fun h => (by decide : (4 : Fin 7) ≠ 5) (g.injective h)
  have gn46 : g 4 ≠ g 6 := fun h => (by decide : (4 : Fin 7) ≠ 6) (g.injective h)
  have gn56 : g 5 ≠ g 6 := fun h => (by decide : (5 : Fin 7) ≠ 6) (g.injective h)
  have ge00 : ¬ G.Adj (g 0) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 0) hh
  have ge01 : ¬ G.Adj (g 0) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 1) hh
  have ge02 : G.Adj (g 0) (g 2) := g.map_rel_iff.mpr (by decide)
  have ge03 : ¬ G.Adj (g 0) (g 3) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 3) hh
  have ge04 : G.Adj (g 0) (g 4) := g.map_rel_iff.mpr (by decide)
  have ge05 : ¬ G.Adj (g 0) (g 5) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 5) hh
  have ge06 : ¬ G.Adj (g 0) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 6) hh
  have ge10 : ¬ G.Adj (g 1) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 0) hh
  have ge11 : ¬ G.Adj (g 1) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 1) hh
  have ge12 : ¬ G.Adj (g 1) (g 2) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 2) hh
  have ge13 : G.Adj (g 1) (g 3) := g.map_rel_iff.mpr (by decide)
  have ge14 : G.Adj (g 1) (g 4) := g.map_rel_iff.mpr (by decide)
  have ge15 : ¬ G.Adj (g 1) (g 5) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 5) hh
  have ge16 : ¬ G.Adj (g 1) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 6) hh
  have ge20 : G.Adj (g 2) (g 0) := g.map_rel_iff.mpr (by decide)
  have ge21 : ¬ G.Adj (g 2) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 1) hh
  have ge22 : ¬ G.Adj (g 2) (g 2) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 2) hh
  have ge23 : G.Adj (g 2) (g 3) := g.map_rel_iff.mpr (by decide)
  have ge24 : ¬ G.Adj (g 2) (g 4) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 4) hh
  have ge25 : G.Adj (g 2) (g 5) := g.map_rel_iff.mpr (by decide)
  have ge26 : ¬ G.Adj (g 2) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 6) hh
  have ge30 : ¬ G.Adj (g 3) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 0) hh
  have ge31 : G.Adj (g 3) (g 1) := g.map_rel_iff.mpr (by decide)
  have ge32 : G.Adj (g 3) (g 2) := g.map_rel_iff.mpr (by decide)
  have ge33 : ¬ G.Adj (g 3) (g 3) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 3) hh
  have ge34 : ¬ G.Adj (g 3) (g 4) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 4) hh
  have ge35 : G.Adj (g 3) (g 5) := g.map_rel_iff.mpr (by decide)
  have ge36 : ¬ G.Adj (g 3) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 6) hh
  have ge40 : G.Adj (g 4) (g 0) := g.map_rel_iff.mpr (by decide)
  have ge41 : G.Adj (g 4) (g 1) := g.map_rel_iff.mpr (by decide)
  have ge42 : ¬ G.Adj (g 4) (g 2) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 2) hh
  have ge43 : ¬ G.Adj (g 4) (g 3) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 3) hh
  have ge44 : ¬ G.Adj (g 4) (g 4) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 4) hh
  have ge45 : ¬ G.Adj (g 4) (g 5) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 5) hh
  have ge46 : G.Adj (g 4) (g 6) := g.map_rel_iff.mpr (by decide)
  have ge50 : ¬ G.Adj (g 5) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 0) hh
  have ge51 : ¬ G.Adj (g 5) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 1) hh
  have ge52 : G.Adj (g 5) (g 2) := g.map_rel_iff.mpr (by decide)
  have ge53 : G.Adj (g 5) (g 3) := g.map_rel_iff.mpr (by decide)
  have ge54 : ¬ G.Adj (g 5) (g 4) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 4) hh
  have ge55 : ¬ G.Adj (g 5) (g 5) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 5) hh
  have ge56 : G.Adj (g 5) (g 6) := g.map_rel_iff.mpr (by decide)
  have ge60 : ¬ G.Adj (g 6) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 0) hh
  have ge61 : ¬ G.Adj (g 6) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 1) hh
  have ge62 : ¬ G.Adj (g 6) (g 2) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 2) hh
  have ge63 : ¬ G.Adj (g 6) (g 3) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 3) hh
  have ge64 : G.Adj (g 6) (g 4) := g.map_rel_iff.mpr (by decide)
  have ge65 : G.Adj (g 6) (g 5) := g.map_rel_iff.mpr (by decide)
  have ge66 : ¬ G.Adj (g 6) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 6) hh
  have gs2 (x : V) (hx : G.Adj (g 2) x) : x = g 0 ∨ x = g 3 ∨ x = g 5 :=
    neighbor_eq_of_three hdeg (List.Nodup.map g.injective (by decide : ([0,3,5] : List (Fin 7)).Nodup)) ge20 ge23 ge25 hx
  have gs3 (x : V) (hx : G.Adj (g 3) x) : x = g 1 ∨ x = g 2 ∨ x = g 5 :=
    neighbor_eq_of_three hdeg (List.Nodup.map g.injective (by decide : ([1,2,5] : List (Fin 7)).Nodup)) ge31 ge32 ge35 hx
  have gs4 (x : V) (hx : G.Adj (g 4) x) : x = g 0 ∨ x = g 1 ∨ x = g 6 :=
    neighbor_eq_of_three hdeg (List.Nodup.map g.injective (by decide : ([0,1,6] : List (Fin 7)).Nodup)) ge40 ge41 ge46 hx
  have gs5 (x : V) (hx : G.Adj (g 5) x) : x = g 2 ∨ x = g 3 ∨ x = g 6 :=
    neighbor_eq_of_three hdeg (List.Nodup.map g.injective (by decide : ([2,3,6] : List (Fin 7)).Nodup)) ge52 ge53 ge56 hx
  have collision00 (he : f 0 = g 0) : f 2 = g 2 ∨ f 2 = g 4 ∨ f 3 = g 2 ∨ f 3 = g 4 := by
    have hh := four_neighbors hdeg fe02 fe03 (he.symm ▸ ge02) (he.symm ▸ ge04)
    grind
  have collision01 (he : f 0 = g 1) : f 2 = g 3 ∨ f 2 = g 4 ∨ f 3 = g 3 ∨ f 3 = g 4 := by
    have hh := four_neighbors hdeg fe02 fe03 (he.symm ▸ ge13) (he.symm ▸ ge14)
    grind
  have collision06 (he : f 0 = g 6) : f 2 = g 4 ∨ f 2 = g 5 ∨ f 3 = g 4 ∨ f 3 = g 5 := by
    have hh := four_neighbors hdeg fe02 fe03 (he.symm ▸ ge64) (he.symm ▸ ge65)
    grind
  have collision10 (he : f 1 = g 0) : f 5 = g 2 ∨ f 5 = g 4 ∨ f 6 = g 2 ∨ f 6 = g 4 := by
    have hh := four_neighbors hdeg fe15 fe16 (he.symm ▸ ge02) (he.symm ▸ ge04)
    grind
  have collision11 (he : f 1 = g 1) : f 5 = g 3 ∨ f 5 = g 4 ∨ f 6 = g 3 ∨ f 6 = g 4 := by
    have hh := four_neighbors hdeg fe15 fe16 (he.symm ▸ ge13) (he.symm ▸ ge14)
    grind
  have collision16 (he : f 1 = g 6) : f 5 = g 4 ∨ f 5 = g 5 ∨ f 6 = g 4 ∨ f 6 = g 5 := by
    have hh := four_neighbors hdeg fe15 fe16 (he.symm ▸ ge64) (he.symm ▸ ge65)
    grind
  have collision40 (he : f 4 = g 0) : f 2 = g 2 ∨ f 2 = g 4 ∨ f 5 = g 2 ∨ f 5 = g 4 := by
    have hh := four_neighbors hdeg fe42 fe45 (he.symm ▸ ge02) (he.symm ▸ ge04)
    grind
  have collision41 (he : f 4 = g 1) : f 2 = g 3 ∨ f 2 = g 4 ∨ f 5 = g 3 ∨ f 5 = g 4 := by
    have hh := four_neighbors hdeg fe42 fe45 (he.symm ▸ ge13) (he.symm ▸ ge14)
    grind
  have collision46 (he : f 4 = g 6) : f 2 = g 4 ∨ f 2 = g 5 ∨ f 5 = g 4 ∨ f 5 = g 5 := by
    have hh := four_neighbors hdeg fe42 fe45 (he.symm ▸ ge64) (he.symm ▸ ge65)
    grind
  fin_cases i <;> fin_cases j <;> intro he <;> grind

/-- Induced H7 and symmetric subdivided-K4 copies cannot intersect in any
finite subcubic graph. No forbidden-cycle hypothesis is needed. -/
theorem h7_h7Symm_disjoint {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v ≤ 3)
    (f : h7 ↪g G) (g : h7Symm ↪g G) :
    Disjoint (Set.range f) (Set.range g) := by
  rw [Set.disjoint_left]
  rintro x ⟨i, rfl⟩ ⟨j, he⟩
  exact mixed_labels_ne hdeg f g i j he.symm

/-- Eight pairwise distinct cyclically adjacent vertices give a genuine simple C8,
using the foundation four-path intersection theorem in contraposition. -/
private theorem cycle_eight_of_tuple {V : Type*} {G : SimpleGraph V}
    {a b c d e f g h : V} (hd : [a,b,c,d,e,f,g,h].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hde : G.Adj d e)
    (hef : G.Adj e f) (hfg : G.Adj f g) (hgh : G.Adj g h) (hha : G.Adj h a) :
    HasSimpleCycleOfLength G 8 := by
  have hdist := hd
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    List.nodup_nil, and_true] at hdist
  let p : Path4 G a e := ⟨b,c,d,hab,hbc,hcd,hde,by simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil]; grind⟩
  let q : Path4 G a e := ⟨h,g,f,hha.symm,hgh.symm,hfg.symm,hef.symm,by simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil]; grind⟩
  by_contra hn
  obtain ⟨z, hz, hzq⟩ := p.internal_intersects hn q
  simp only [Path4.Internal, p, q] at hz hzq
  grind
set_option maxHeartbeats 1000000 in
/-- With the center and all ports aligned, a proper overlap forces the simple C8
`g2-g3-g5-f6-f5-f3-f2-f0-g2`. Otherwise the triangle labels also align. -/
private theorem center_aligned {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v ≤ 3)
    (h8 : ¬ HasSimpleCycleOfLength G 8) (f g : h7Symm ↪g G)
    (hc : f 4 = g 4) (h0 : f 0 = g 0) (h1 : f 1 = g 1) (h6 : f 6 = g 6) :
    ∀ i, f i = g i := by
  have fn01 : f 0 ≠ f 1 := fun h => (by decide : (0 : Fin 7) ≠ 1) (f.injective h)
  have fn02 : f 0 ≠ f 2 := fun h => (by decide : (0 : Fin 7) ≠ 2) (f.injective h)
  have fn03 : f 0 ≠ f 3 := fun h => (by decide : (0 : Fin 7) ≠ 3) (f.injective h)
  have fn04 : f 0 ≠ f 4 := fun h => (by decide : (0 : Fin 7) ≠ 4) (f.injective h)
  have fn05 : f 0 ≠ f 5 := fun h => (by decide : (0 : Fin 7) ≠ 5) (f.injective h)
  have fn06 : f 0 ≠ f 6 := fun h => (by decide : (0 : Fin 7) ≠ 6) (f.injective h)
  have fn12 : f 1 ≠ f 2 := fun h => (by decide : (1 : Fin 7) ≠ 2) (f.injective h)
  have fn13 : f 1 ≠ f 3 := fun h => (by decide : (1 : Fin 7) ≠ 3) (f.injective h)
  have fn14 : f 1 ≠ f 4 := fun h => (by decide : (1 : Fin 7) ≠ 4) (f.injective h)
  have fn15 : f 1 ≠ f 5 := fun h => (by decide : (1 : Fin 7) ≠ 5) (f.injective h)
  have fn16 : f 1 ≠ f 6 := fun h => (by decide : (1 : Fin 7) ≠ 6) (f.injective h)
  have fn23 : f 2 ≠ f 3 := fun h => (by decide : (2 : Fin 7) ≠ 3) (f.injective h)
  have fn24 : f 2 ≠ f 4 := fun h => (by decide : (2 : Fin 7) ≠ 4) (f.injective h)
  have fn25 : f 2 ≠ f 5 := fun h => (by decide : (2 : Fin 7) ≠ 5) (f.injective h)
  have fn26 : f 2 ≠ f 6 := fun h => (by decide : (2 : Fin 7) ≠ 6) (f.injective h)
  have fn34 : f 3 ≠ f 4 := fun h => (by decide : (3 : Fin 7) ≠ 4) (f.injective h)
  have fn35 : f 3 ≠ f 5 := fun h => (by decide : (3 : Fin 7) ≠ 5) (f.injective h)
  have fn36 : f 3 ≠ f 6 := fun h => (by decide : (3 : Fin 7) ≠ 6) (f.injective h)
  have fn45 : f 4 ≠ f 5 := fun h => (by decide : (4 : Fin 7) ≠ 5) (f.injective h)
  have fn46 : f 4 ≠ f 6 := fun h => (by decide : (4 : Fin 7) ≠ 6) (f.injective h)
  have fn56 : f 5 ≠ f 6 := fun h => (by decide : (5 : Fin 7) ≠ 6) (f.injective h)
  have fe00 : ¬ G.Adj (f 0) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 0) hh
  have fe01 : ¬ G.Adj (f 0) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 1) hh
  have fe02 : G.Adj (f 0) (f 2) := f.map_rel_iff.mpr (by decide)
  have fe03 : ¬ G.Adj (f 0) (f 3) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 3) hh
  have fe04 : G.Adj (f 0) (f 4) := f.map_rel_iff.mpr (by decide)
  have fe05 : ¬ G.Adj (f 0) (f 5) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 5) hh
  have fe06 : ¬ G.Adj (f 0) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 6) hh
  have fe10 : ¬ G.Adj (f 1) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 0) hh
  have fe11 : ¬ G.Adj (f 1) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 1) hh
  have fe12 : ¬ G.Adj (f 1) (f 2) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 2) hh
  have fe13 : G.Adj (f 1) (f 3) := f.map_rel_iff.mpr (by decide)
  have fe14 : G.Adj (f 1) (f 4) := f.map_rel_iff.mpr (by decide)
  have fe15 : ¬ G.Adj (f 1) (f 5) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 5) hh
  have fe16 : ¬ G.Adj (f 1) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 6) hh
  have fe20 : G.Adj (f 2) (f 0) := f.map_rel_iff.mpr (by decide)
  have fe21 : ¬ G.Adj (f 2) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 1) hh
  have fe22 : ¬ G.Adj (f 2) (f 2) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 2) hh
  have fe23 : G.Adj (f 2) (f 3) := f.map_rel_iff.mpr (by decide)
  have fe24 : ¬ G.Adj (f 2) (f 4) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 4) hh
  have fe25 : G.Adj (f 2) (f 5) := f.map_rel_iff.mpr (by decide)
  have fe26 : ¬ G.Adj (f 2) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 6) hh
  have fe30 : ¬ G.Adj (f 3) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 0) hh
  have fe31 : G.Adj (f 3) (f 1) := f.map_rel_iff.mpr (by decide)
  have fe32 : G.Adj (f 3) (f 2) := f.map_rel_iff.mpr (by decide)
  have fe33 : ¬ G.Adj (f 3) (f 3) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 3) hh
  have fe34 : ¬ G.Adj (f 3) (f 4) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 4) hh
  have fe35 : G.Adj (f 3) (f 5) := f.map_rel_iff.mpr (by decide)
  have fe36 : ¬ G.Adj (f 3) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 6) hh
  have fe40 : G.Adj (f 4) (f 0) := f.map_rel_iff.mpr (by decide)
  have fe41 : G.Adj (f 4) (f 1) := f.map_rel_iff.mpr (by decide)
  have fe42 : ¬ G.Adj (f 4) (f 2) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 2) hh
  have fe43 : ¬ G.Adj (f 4) (f 3) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 3) hh
  have fe44 : ¬ G.Adj (f 4) (f 4) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 4) hh
  have fe45 : ¬ G.Adj (f 4) (f 5) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 5) hh
  have fe46 : G.Adj (f 4) (f 6) := f.map_rel_iff.mpr (by decide)
  have fe50 : ¬ G.Adj (f 5) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 0) hh
  have fe51 : ¬ G.Adj (f 5) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 1) hh
  have fe52 : G.Adj (f 5) (f 2) := f.map_rel_iff.mpr (by decide)
  have fe53 : G.Adj (f 5) (f 3) := f.map_rel_iff.mpr (by decide)
  have fe54 : ¬ G.Adj (f 5) (f 4) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 4) hh
  have fe55 : ¬ G.Adj (f 5) (f 5) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 5) hh
  have fe56 : G.Adj (f 5) (f 6) := f.map_rel_iff.mpr (by decide)
  have fe60 : ¬ G.Adj (f 6) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 0) hh
  have fe61 : ¬ G.Adj (f 6) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 1) hh
  have fe62 : ¬ G.Adj (f 6) (f 2) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 2) hh
  have fe63 : ¬ G.Adj (f 6) (f 3) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 3) hh
  have fe64 : G.Adj (f 6) (f 4) := f.map_rel_iff.mpr (by decide)
  have fe65 : G.Adj (f 6) (f 5) := f.map_rel_iff.mpr (by decide)
  have fe66 : ¬ G.Adj (f 6) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 6) hh
  have fs2 (x : V) (hx : G.Adj (f 2) x) : x = f 0 ∨ x = f 3 ∨ x = f 5 :=
    neighbor_eq_of_three hdeg (List.Nodup.map f.injective (by decide : ([0,3,5] : List (Fin 7)).Nodup)) fe20 fe23 fe25 hx
  have fs3 (x : V) (hx : G.Adj (f 3) x) : x = f 1 ∨ x = f 2 ∨ x = f 5 :=
    neighbor_eq_of_three hdeg (List.Nodup.map f.injective (by decide : ([1,2,5] : List (Fin 7)).Nodup)) fe31 fe32 fe35 hx
  have fs4 (x : V) (hx : G.Adj (f 4) x) : x = f 0 ∨ x = f 1 ∨ x = f 6 :=
    neighbor_eq_of_three hdeg (List.Nodup.map f.injective (by decide : ([0,1,6] : List (Fin 7)).Nodup)) fe40 fe41 fe46 hx
  have fs5 (x : V) (hx : G.Adj (f 5) x) : x = f 2 ∨ x = f 3 ∨ x = f 6 :=
    neighbor_eq_of_three hdeg (List.Nodup.map f.injective (by decide : ([2,3,6] : List (Fin 7)).Nodup)) fe52 fe53 fe56 hx
  have gn01 : g 0 ≠ g 1 := fun h => (by decide : (0 : Fin 7) ≠ 1) (g.injective h)
  have gn02 : g 0 ≠ g 2 := fun h => (by decide : (0 : Fin 7) ≠ 2) (g.injective h)
  have gn03 : g 0 ≠ g 3 := fun h => (by decide : (0 : Fin 7) ≠ 3) (g.injective h)
  have gn04 : g 0 ≠ g 4 := fun h => (by decide : (0 : Fin 7) ≠ 4) (g.injective h)
  have gn05 : g 0 ≠ g 5 := fun h => (by decide : (0 : Fin 7) ≠ 5) (g.injective h)
  have gn06 : g 0 ≠ g 6 := fun h => (by decide : (0 : Fin 7) ≠ 6) (g.injective h)
  have gn12 : g 1 ≠ g 2 := fun h => (by decide : (1 : Fin 7) ≠ 2) (g.injective h)
  have gn13 : g 1 ≠ g 3 := fun h => (by decide : (1 : Fin 7) ≠ 3) (g.injective h)
  have gn14 : g 1 ≠ g 4 := fun h => (by decide : (1 : Fin 7) ≠ 4) (g.injective h)
  have gn15 : g 1 ≠ g 5 := fun h => (by decide : (1 : Fin 7) ≠ 5) (g.injective h)
  have gn16 : g 1 ≠ g 6 := fun h => (by decide : (1 : Fin 7) ≠ 6) (g.injective h)
  have gn23 : g 2 ≠ g 3 := fun h => (by decide : (2 : Fin 7) ≠ 3) (g.injective h)
  have gn24 : g 2 ≠ g 4 := fun h => (by decide : (2 : Fin 7) ≠ 4) (g.injective h)
  have gn25 : g 2 ≠ g 5 := fun h => (by decide : (2 : Fin 7) ≠ 5) (g.injective h)
  have gn26 : g 2 ≠ g 6 := fun h => (by decide : (2 : Fin 7) ≠ 6) (g.injective h)
  have gn34 : g 3 ≠ g 4 := fun h => (by decide : (3 : Fin 7) ≠ 4) (g.injective h)
  have gn35 : g 3 ≠ g 5 := fun h => (by decide : (3 : Fin 7) ≠ 5) (g.injective h)
  have gn36 : g 3 ≠ g 6 := fun h => (by decide : (3 : Fin 7) ≠ 6) (g.injective h)
  have gn45 : g 4 ≠ g 5 := fun h => (by decide : (4 : Fin 7) ≠ 5) (g.injective h)
  have gn46 : g 4 ≠ g 6 := fun h => (by decide : (4 : Fin 7) ≠ 6) (g.injective h)
  have gn56 : g 5 ≠ g 6 := fun h => (by decide : (5 : Fin 7) ≠ 6) (g.injective h)
  have ge00 : ¬ G.Adj (g 0) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 0) hh
  have ge01 : ¬ G.Adj (g 0) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 1) hh
  have ge02 : G.Adj (g 0) (g 2) := g.map_rel_iff.mpr (by decide)
  have ge03 : ¬ G.Adj (g 0) (g 3) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 3) hh
  have ge04 : G.Adj (g 0) (g 4) := g.map_rel_iff.mpr (by decide)
  have ge05 : ¬ G.Adj (g 0) (g 5) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 5) hh
  have ge06 : ¬ G.Adj (g 0) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 6) hh
  have ge10 : ¬ G.Adj (g 1) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 0) hh
  have ge11 : ¬ G.Adj (g 1) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 1) hh
  have ge12 : ¬ G.Adj (g 1) (g 2) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 2) hh
  have ge13 : G.Adj (g 1) (g 3) := g.map_rel_iff.mpr (by decide)
  have ge14 : G.Adj (g 1) (g 4) := g.map_rel_iff.mpr (by decide)
  have ge15 : ¬ G.Adj (g 1) (g 5) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 5) hh
  have ge16 : ¬ G.Adj (g 1) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 6) hh
  have ge20 : G.Adj (g 2) (g 0) := g.map_rel_iff.mpr (by decide)
  have ge21 : ¬ G.Adj (g 2) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 1) hh
  have ge22 : ¬ G.Adj (g 2) (g 2) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 2) hh
  have ge23 : G.Adj (g 2) (g 3) := g.map_rel_iff.mpr (by decide)
  have ge24 : ¬ G.Adj (g 2) (g 4) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 4) hh
  have ge25 : G.Adj (g 2) (g 5) := g.map_rel_iff.mpr (by decide)
  have ge26 : ¬ G.Adj (g 2) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 6) hh
  have ge30 : ¬ G.Adj (g 3) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 0) hh
  have ge31 : G.Adj (g 3) (g 1) := g.map_rel_iff.mpr (by decide)
  have ge32 : G.Adj (g 3) (g 2) := g.map_rel_iff.mpr (by decide)
  have ge33 : ¬ G.Adj (g 3) (g 3) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 3) hh
  have ge34 : ¬ G.Adj (g 3) (g 4) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 4) hh
  have ge35 : G.Adj (g 3) (g 5) := g.map_rel_iff.mpr (by decide)
  have ge36 : ¬ G.Adj (g 3) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 6) hh
  have ge40 : G.Adj (g 4) (g 0) := g.map_rel_iff.mpr (by decide)
  have ge41 : G.Adj (g 4) (g 1) := g.map_rel_iff.mpr (by decide)
  have ge42 : ¬ G.Adj (g 4) (g 2) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 2) hh
  have ge43 : ¬ G.Adj (g 4) (g 3) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 3) hh
  have ge44 : ¬ G.Adj (g 4) (g 4) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 4) hh
  have ge45 : ¬ G.Adj (g 4) (g 5) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 5) hh
  have ge46 : G.Adj (g 4) (g 6) := g.map_rel_iff.mpr (by decide)
  have ge50 : ¬ G.Adj (g 5) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 0) hh
  have ge51 : ¬ G.Adj (g 5) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 1) hh
  have ge52 : G.Adj (g 5) (g 2) := g.map_rel_iff.mpr (by decide)
  have ge53 : G.Adj (g 5) (g 3) := g.map_rel_iff.mpr (by decide)
  have ge54 : ¬ G.Adj (g 5) (g 4) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 4) hh
  have ge55 : ¬ G.Adj (g 5) (g 5) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 5) hh
  have ge56 : G.Adj (g 5) (g 6) := g.map_rel_iff.mpr (by decide)
  have ge60 : ¬ G.Adj (g 6) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 0) hh
  have ge61 : ¬ G.Adj (g 6) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 1) hh
  have ge62 : ¬ G.Adj (g 6) (g 2) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 2) hh
  have ge63 : ¬ G.Adj (g 6) (g 3) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 3) hh
  have ge64 : G.Adj (g 6) (g 4) := g.map_rel_iff.mpr (by decide)
  have ge65 : G.Adj (g 6) (g 5) := g.map_rel_iff.mpr (by decide)
  have ge66 : ¬ G.Adj (g 6) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 6) hh
  have gs2 (x : V) (hx : G.Adj (g 2) x) : x = g 0 ∨ x = g 3 ∨ x = g 5 :=
    neighbor_eq_of_three hdeg (List.Nodup.map g.injective (by decide : ([0,3,5] : List (Fin 7)).Nodup)) ge20 ge23 ge25 hx
  have gs3 (x : V) (hx : G.Adj (g 3) x) : x = g 1 ∨ x = g 2 ∨ x = g 5 :=
    neighbor_eq_of_three hdeg (List.Nodup.map g.injective (by decide : ([1,2,5] : List (Fin 7)).Nodup)) ge31 ge32 ge35 hx
  have gs4 (x : V) (hx : G.Adj (g 4) x) : x = g 0 ∨ x = g 1 ∨ x = g 6 :=
    neighbor_eq_of_three hdeg (List.Nodup.map g.injective (by decide : ([0,1,6] : List (Fin 7)).Nodup)) ge40 ge41 ge46 hx
  have gs5 (x : V) (hx : G.Adj (g 5) x) : x = g 2 ∨ x = g 3 ∨ x = g 6 :=
    neighbor_eq_of_three hdeg (List.Nodup.map g.injective (by decide : ([2,3,6] : List (Fin 7)).Nodup)) ge52 ge53 ge56 hx
  by_cases ht : f 2 = g 2
  · intro i
    fin_cases i <;> grind (splits := 15)
  · have hd : [g 2, g 3, g 5, f 6, f 5, f 3, f 2, f 0].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil]
      grind (splits := 15)
    exact False.elim (h8 (cycle_eight_of_tuple hd ge23 ge35
      (h6.symm ▸ ge56) fe65 fe53 fe32 fe20 (h0.symm ▸ ge02)))
set_option maxHeartbeats 1000000 in
/-- With the triangle and ports aligned, distinct centers force the simple C8
`g4-f6-f4-f0-f2-f5-f3-f1-g4`. Thus every label agrees. -/
private theorem triangle_aligned {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v ≤ 3)
    (h8 : ¬ HasSimpleCycleOfLength G 8) (f g : h7Symm ↪g G)
    (h0 : f 0 = g 0) (h1 : f 1 = g 1) (h6 : f 6 = g 6)
    (h2 : f 2 = g 2) (h3 : f 3 = g 3) (h5 : f 5 = g 5) :
    ∀ i, f i = g i := by
  have fn01 : f 0 ≠ f 1 := fun h => (by decide : (0 : Fin 7) ≠ 1) (f.injective h)
  have fn02 : f 0 ≠ f 2 := fun h => (by decide : (0 : Fin 7) ≠ 2) (f.injective h)
  have fn03 : f 0 ≠ f 3 := fun h => (by decide : (0 : Fin 7) ≠ 3) (f.injective h)
  have fn04 : f 0 ≠ f 4 := fun h => (by decide : (0 : Fin 7) ≠ 4) (f.injective h)
  have fn05 : f 0 ≠ f 5 := fun h => (by decide : (0 : Fin 7) ≠ 5) (f.injective h)
  have fn06 : f 0 ≠ f 6 := fun h => (by decide : (0 : Fin 7) ≠ 6) (f.injective h)
  have fn12 : f 1 ≠ f 2 := fun h => (by decide : (1 : Fin 7) ≠ 2) (f.injective h)
  have fn13 : f 1 ≠ f 3 := fun h => (by decide : (1 : Fin 7) ≠ 3) (f.injective h)
  have fn14 : f 1 ≠ f 4 := fun h => (by decide : (1 : Fin 7) ≠ 4) (f.injective h)
  have fn15 : f 1 ≠ f 5 := fun h => (by decide : (1 : Fin 7) ≠ 5) (f.injective h)
  have fn16 : f 1 ≠ f 6 := fun h => (by decide : (1 : Fin 7) ≠ 6) (f.injective h)
  have fn23 : f 2 ≠ f 3 := fun h => (by decide : (2 : Fin 7) ≠ 3) (f.injective h)
  have fn24 : f 2 ≠ f 4 := fun h => (by decide : (2 : Fin 7) ≠ 4) (f.injective h)
  have fn25 : f 2 ≠ f 5 := fun h => (by decide : (2 : Fin 7) ≠ 5) (f.injective h)
  have fn26 : f 2 ≠ f 6 := fun h => (by decide : (2 : Fin 7) ≠ 6) (f.injective h)
  have fn34 : f 3 ≠ f 4 := fun h => (by decide : (3 : Fin 7) ≠ 4) (f.injective h)
  have fn35 : f 3 ≠ f 5 := fun h => (by decide : (3 : Fin 7) ≠ 5) (f.injective h)
  have fn36 : f 3 ≠ f 6 := fun h => (by decide : (3 : Fin 7) ≠ 6) (f.injective h)
  have fn45 : f 4 ≠ f 5 := fun h => (by decide : (4 : Fin 7) ≠ 5) (f.injective h)
  have fn46 : f 4 ≠ f 6 := fun h => (by decide : (4 : Fin 7) ≠ 6) (f.injective h)
  have fn56 : f 5 ≠ f 6 := fun h => (by decide : (5 : Fin 7) ≠ 6) (f.injective h)
  have fe00 : ¬ G.Adj (f 0) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 0) hh
  have fe01 : ¬ G.Adj (f 0) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 1) hh
  have fe02 : G.Adj (f 0) (f 2) := f.map_rel_iff.mpr (by decide)
  have fe03 : ¬ G.Adj (f 0) (f 3) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 3) hh
  have fe04 : G.Adj (f 0) (f 4) := f.map_rel_iff.mpr (by decide)
  have fe05 : ¬ G.Adj (f 0) (f 5) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 5) hh
  have fe06 : ¬ G.Adj (f 0) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 6) hh
  have fe10 : ¬ G.Adj (f 1) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 0) hh
  have fe11 : ¬ G.Adj (f 1) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 1) hh
  have fe12 : ¬ G.Adj (f 1) (f 2) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 2) hh
  have fe13 : G.Adj (f 1) (f 3) := f.map_rel_iff.mpr (by decide)
  have fe14 : G.Adj (f 1) (f 4) := f.map_rel_iff.mpr (by decide)
  have fe15 : ¬ G.Adj (f 1) (f 5) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 5) hh
  have fe16 : ¬ G.Adj (f 1) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 6) hh
  have fe20 : G.Adj (f 2) (f 0) := f.map_rel_iff.mpr (by decide)
  have fe21 : ¬ G.Adj (f 2) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 1) hh
  have fe22 : ¬ G.Adj (f 2) (f 2) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 2) hh
  have fe23 : G.Adj (f 2) (f 3) := f.map_rel_iff.mpr (by decide)
  have fe24 : ¬ G.Adj (f 2) (f 4) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 4) hh
  have fe25 : G.Adj (f 2) (f 5) := f.map_rel_iff.mpr (by decide)
  have fe26 : ¬ G.Adj (f 2) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 6) hh
  have fe30 : ¬ G.Adj (f 3) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 0) hh
  have fe31 : G.Adj (f 3) (f 1) := f.map_rel_iff.mpr (by decide)
  have fe32 : G.Adj (f 3) (f 2) := f.map_rel_iff.mpr (by decide)
  have fe33 : ¬ G.Adj (f 3) (f 3) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 3) hh
  have fe34 : ¬ G.Adj (f 3) (f 4) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 4) hh
  have fe35 : G.Adj (f 3) (f 5) := f.map_rel_iff.mpr (by decide)
  have fe36 : ¬ G.Adj (f 3) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 6) hh
  have fe40 : G.Adj (f 4) (f 0) := f.map_rel_iff.mpr (by decide)
  have fe41 : G.Adj (f 4) (f 1) := f.map_rel_iff.mpr (by decide)
  have fe42 : ¬ G.Adj (f 4) (f 2) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 2) hh
  have fe43 : ¬ G.Adj (f 4) (f 3) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 3) hh
  have fe44 : ¬ G.Adj (f 4) (f 4) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 4) hh
  have fe45 : ¬ G.Adj (f 4) (f 5) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 5) hh
  have fe46 : G.Adj (f 4) (f 6) := f.map_rel_iff.mpr (by decide)
  have fe50 : ¬ G.Adj (f 5) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 0) hh
  have fe51 : ¬ G.Adj (f 5) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 1) hh
  have fe52 : G.Adj (f 5) (f 2) := f.map_rel_iff.mpr (by decide)
  have fe53 : G.Adj (f 5) (f 3) := f.map_rel_iff.mpr (by decide)
  have fe54 : ¬ G.Adj (f 5) (f 4) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 4) hh
  have fe55 : ¬ G.Adj (f 5) (f 5) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 5) hh
  have fe56 : G.Adj (f 5) (f 6) := f.map_rel_iff.mpr (by decide)
  have fe60 : ¬ G.Adj (f 6) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 0) hh
  have fe61 : ¬ G.Adj (f 6) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 1) hh
  have fe62 : ¬ G.Adj (f 6) (f 2) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 2) hh
  have fe63 : ¬ G.Adj (f 6) (f 3) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 3) hh
  have fe64 : G.Adj (f 6) (f 4) := f.map_rel_iff.mpr (by decide)
  have fe65 : G.Adj (f 6) (f 5) := f.map_rel_iff.mpr (by decide)
  have fe66 : ¬ G.Adj (f 6) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 6) hh
  have fs2 (x : V) (hx : G.Adj (f 2) x) : x = f 0 ∨ x = f 3 ∨ x = f 5 :=
    neighbor_eq_of_three hdeg (List.Nodup.map f.injective (by decide : ([0,3,5] : List (Fin 7)).Nodup)) fe20 fe23 fe25 hx
  have fs3 (x : V) (hx : G.Adj (f 3) x) : x = f 1 ∨ x = f 2 ∨ x = f 5 :=
    neighbor_eq_of_three hdeg (List.Nodup.map f.injective (by decide : ([1,2,5] : List (Fin 7)).Nodup)) fe31 fe32 fe35 hx
  have fs4 (x : V) (hx : G.Adj (f 4) x) : x = f 0 ∨ x = f 1 ∨ x = f 6 :=
    neighbor_eq_of_three hdeg (List.Nodup.map f.injective (by decide : ([0,1,6] : List (Fin 7)).Nodup)) fe40 fe41 fe46 hx
  have fs5 (x : V) (hx : G.Adj (f 5) x) : x = f 2 ∨ x = f 3 ∨ x = f 6 :=
    neighbor_eq_of_three hdeg (List.Nodup.map f.injective (by decide : ([2,3,6] : List (Fin 7)).Nodup)) fe52 fe53 fe56 hx
  have gn01 : g 0 ≠ g 1 := fun h => (by decide : (0 : Fin 7) ≠ 1) (g.injective h)
  have gn02 : g 0 ≠ g 2 := fun h => (by decide : (0 : Fin 7) ≠ 2) (g.injective h)
  have gn03 : g 0 ≠ g 3 := fun h => (by decide : (0 : Fin 7) ≠ 3) (g.injective h)
  have gn04 : g 0 ≠ g 4 := fun h => (by decide : (0 : Fin 7) ≠ 4) (g.injective h)
  have gn05 : g 0 ≠ g 5 := fun h => (by decide : (0 : Fin 7) ≠ 5) (g.injective h)
  have gn06 : g 0 ≠ g 6 := fun h => (by decide : (0 : Fin 7) ≠ 6) (g.injective h)
  have gn12 : g 1 ≠ g 2 := fun h => (by decide : (1 : Fin 7) ≠ 2) (g.injective h)
  have gn13 : g 1 ≠ g 3 := fun h => (by decide : (1 : Fin 7) ≠ 3) (g.injective h)
  have gn14 : g 1 ≠ g 4 := fun h => (by decide : (1 : Fin 7) ≠ 4) (g.injective h)
  have gn15 : g 1 ≠ g 5 := fun h => (by decide : (1 : Fin 7) ≠ 5) (g.injective h)
  have gn16 : g 1 ≠ g 6 := fun h => (by decide : (1 : Fin 7) ≠ 6) (g.injective h)
  have gn23 : g 2 ≠ g 3 := fun h => (by decide : (2 : Fin 7) ≠ 3) (g.injective h)
  have gn24 : g 2 ≠ g 4 := fun h => (by decide : (2 : Fin 7) ≠ 4) (g.injective h)
  have gn25 : g 2 ≠ g 5 := fun h => (by decide : (2 : Fin 7) ≠ 5) (g.injective h)
  have gn26 : g 2 ≠ g 6 := fun h => (by decide : (2 : Fin 7) ≠ 6) (g.injective h)
  have gn34 : g 3 ≠ g 4 := fun h => (by decide : (3 : Fin 7) ≠ 4) (g.injective h)
  have gn35 : g 3 ≠ g 5 := fun h => (by decide : (3 : Fin 7) ≠ 5) (g.injective h)
  have gn36 : g 3 ≠ g 6 := fun h => (by decide : (3 : Fin 7) ≠ 6) (g.injective h)
  have gn45 : g 4 ≠ g 5 := fun h => (by decide : (4 : Fin 7) ≠ 5) (g.injective h)
  have gn46 : g 4 ≠ g 6 := fun h => (by decide : (4 : Fin 7) ≠ 6) (g.injective h)
  have gn56 : g 5 ≠ g 6 := fun h => (by decide : (5 : Fin 7) ≠ 6) (g.injective h)
  have ge00 : ¬ G.Adj (g 0) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 0) hh
  have ge01 : ¬ G.Adj (g 0) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 1) hh
  have ge02 : G.Adj (g 0) (g 2) := g.map_rel_iff.mpr (by decide)
  have ge03 : ¬ G.Adj (g 0) (g 3) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 3) hh
  have ge04 : G.Adj (g 0) (g 4) := g.map_rel_iff.mpr (by decide)
  have ge05 : ¬ G.Adj (g 0) (g 5) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 5) hh
  have ge06 : ¬ G.Adj (g 0) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 6) hh
  have ge10 : ¬ G.Adj (g 1) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 0) hh
  have ge11 : ¬ G.Adj (g 1) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 1) hh
  have ge12 : ¬ G.Adj (g 1) (g 2) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 2) hh
  have ge13 : G.Adj (g 1) (g 3) := g.map_rel_iff.mpr (by decide)
  have ge14 : G.Adj (g 1) (g 4) := g.map_rel_iff.mpr (by decide)
  have ge15 : ¬ G.Adj (g 1) (g 5) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 5) hh
  have ge16 : ¬ G.Adj (g 1) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 6) hh
  have ge20 : G.Adj (g 2) (g 0) := g.map_rel_iff.mpr (by decide)
  have ge21 : ¬ G.Adj (g 2) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 1) hh
  have ge22 : ¬ G.Adj (g 2) (g 2) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 2) hh
  have ge23 : G.Adj (g 2) (g 3) := g.map_rel_iff.mpr (by decide)
  have ge24 : ¬ G.Adj (g 2) (g 4) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 4) hh
  have ge25 : G.Adj (g 2) (g 5) := g.map_rel_iff.mpr (by decide)
  have ge26 : ¬ G.Adj (g 2) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 6) hh
  have ge30 : ¬ G.Adj (g 3) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 0) hh
  have ge31 : G.Adj (g 3) (g 1) := g.map_rel_iff.mpr (by decide)
  have ge32 : G.Adj (g 3) (g 2) := g.map_rel_iff.mpr (by decide)
  have ge33 : ¬ G.Adj (g 3) (g 3) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 3) hh
  have ge34 : ¬ G.Adj (g 3) (g 4) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 4) hh
  have ge35 : G.Adj (g 3) (g 5) := g.map_rel_iff.mpr (by decide)
  have ge36 : ¬ G.Adj (g 3) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 6) hh
  have ge40 : G.Adj (g 4) (g 0) := g.map_rel_iff.mpr (by decide)
  have ge41 : G.Adj (g 4) (g 1) := g.map_rel_iff.mpr (by decide)
  have ge42 : ¬ G.Adj (g 4) (g 2) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 2) hh
  have ge43 : ¬ G.Adj (g 4) (g 3) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 3) hh
  have ge44 : ¬ G.Adj (g 4) (g 4) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 4) hh
  have ge45 : ¬ G.Adj (g 4) (g 5) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 5) hh
  have ge46 : G.Adj (g 4) (g 6) := g.map_rel_iff.mpr (by decide)
  have ge50 : ¬ G.Adj (g 5) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 0) hh
  have ge51 : ¬ G.Adj (g 5) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 1) hh
  have ge52 : G.Adj (g 5) (g 2) := g.map_rel_iff.mpr (by decide)
  have ge53 : G.Adj (g 5) (g 3) := g.map_rel_iff.mpr (by decide)
  have ge54 : ¬ G.Adj (g 5) (g 4) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 4) hh
  have ge55 : ¬ G.Adj (g 5) (g 5) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 5) hh
  have ge56 : G.Adj (g 5) (g 6) := g.map_rel_iff.mpr (by decide)
  have ge60 : ¬ G.Adj (g 6) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 0) hh
  have ge61 : ¬ G.Adj (g 6) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 1) hh
  have ge62 : ¬ G.Adj (g 6) (g 2) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 2) hh
  have ge63 : ¬ G.Adj (g 6) (g 3) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 3) hh
  have ge64 : G.Adj (g 6) (g 4) := g.map_rel_iff.mpr (by decide)
  have ge65 : G.Adj (g 6) (g 5) := g.map_rel_iff.mpr (by decide)
  have ge66 : ¬ G.Adj (g 6) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 6) hh
  have gs2 (x : V) (hx : G.Adj (g 2) x) : x = g 0 ∨ x = g 3 ∨ x = g 5 :=
    neighbor_eq_of_three hdeg (List.Nodup.map g.injective (by decide : ([0,3,5] : List (Fin 7)).Nodup)) ge20 ge23 ge25 hx
  have gs3 (x : V) (hx : G.Adj (g 3) x) : x = g 1 ∨ x = g 2 ∨ x = g 5 :=
    neighbor_eq_of_three hdeg (List.Nodup.map g.injective (by decide : ([1,2,5] : List (Fin 7)).Nodup)) ge31 ge32 ge35 hx
  have gs4 (x : V) (hx : G.Adj (g 4) x) : x = g 0 ∨ x = g 1 ∨ x = g 6 :=
    neighbor_eq_of_three hdeg (List.Nodup.map g.injective (by decide : ([0,1,6] : List (Fin 7)).Nodup)) ge40 ge41 ge46 hx
  have gs5 (x : V) (hx : G.Adj (g 5) x) : x = g 2 ∨ x = g 3 ∨ x = g 6 :=
    neighbor_eq_of_three hdeg (List.Nodup.map g.injective (by decide : ([2,3,6] : List (Fin 7)).Nodup)) ge52 ge53 ge56 hx
  by_cases hc : f 4 = g 4
  · intro i
    fin_cases i <;> grind
  · have hd : [g 4, f 6, f 4, f 0, f 2, f 5, f 3, f 1].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil]
      grind
    exact False.elim (h8 (cycle_eight_of_tuple hd
      (h6.symm ▸ ge46) fe64 fe40 fe02 fe25 fe53 fe31 (h1.symm ▸ ge14)))

set_option maxHeartbeats 1000000 in
/-- A shared label-2 triangle vertex aligns the unique triangle and its ports,
up to interchanging the two other triangle vertices and their associated ports. -/
private theorem triangle_checkpoint {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v ≤ 3)
    (f g : h7Symm ↪g G) (h2 : f 2 = g 2) :
    (f 0 = g 0 ∧ f 1 = g 1 ∧ f 6 = g 6 ∧ f 2 = g 2 ∧ f 3 = g 3 ∧ f 5 = g 5) ∨
    (f 0 = g 0 ∧ f 1 = g 6 ∧ f 6 = g 1 ∧ f 2 = g 2 ∧ f 3 = g 5 ∧ f 5 = g 3) := by
  have fn01 : f 0 ≠ f 1 := fun h => (by decide : (0 : Fin 7) ≠ 1) (f.injective h)
  have fn02 : f 0 ≠ f 2 := fun h => (by decide : (0 : Fin 7) ≠ 2) (f.injective h)
  have fn03 : f 0 ≠ f 3 := fun h => (by decide : (0 : Fin 7) ≠ 3) (f.injective h)
  have fn04 : f 0 ≠ f 4 := fun h => (by decide : (0 : Fin 7) ≠ 4) (f.injective h)
  have fn05 : f 0 ≠ f 5 := fun h => (by decide : (0 : Fin 7) ≠ 5) (f.injective h)
  have fn06 : f 0 ≠ f 6 := fun h => (by decide : (0 : Fin 7) ≠ 6) (f.injective h)
  have fn12 : f 1 ≠ f 2 := fun h => (by decide : (1 : Fin 7) ≠ 2) (f.injective h)
  have fn13 : f 1 ≠ f 3 := fun h => (by decide : (1 : Fin 7) ≠ 3) (f.injective h)
  have fn14 : f 1 ≠ f 4 := fun h => (by decide : (1 : Fin 7) ≠ 4) (f.injective h)
  have fn15 : f 1 ≠ f 5 := fun h => (by decide : (1 : Fin 7) ≠ 5) (f.injective h)
  have fn16 : f 1 ≠ f 6 := fun h => (by decide : (1 : Fin 7) ≠ 6) (f.injective h)
  have fn23 : f 2 ≠ f 3 := fun h => (by decide : (2 : Fin 7) ≠ 3) (f.injective h)
  have fn24 : f 2 ≠ f 4 := fun h => (by decide : (2 : Fin 7) ≠ 4) (f.injective h)
  have fn25 : f 2 ≠ f 5 := fun h => (by decide : (2 : Fin 7) ≠ 5) (f.injective h)
  have fn26 : f 2 ≠ f 6 := fun h => (by decide : (2 : Fin 7) ≠ 6) (f.injective h)
  have fn34 : f 3 ≠ f 4 := fun h => (by decide : (3 : Fin 7) ≠ 4) (f.injective h)
  have fn35 : f 3 ≠ f 5 := fun h => (by decide : (3 : Fin 7) ≠ 5) (f.injective h)
  have fn36 : f 3 ≠ f 6 := fun h => (by decide : (3 : Fin 7) ≠ 6) (f.injective h)
  have fn45 : f 4 ≠ f 5 := fun h => (by decide : (4 : Fin 7) ≠ 5) (f.injective h)
  have fn46 : f 4 ≠ f 6 := fun h => (by decide : (4 : Fin 7) ≠ 6) (f.injective h)
  have fn56 : f 5 ≠ f 6 := fun h => (by decide : (5 : Fin 7) ≠ 6) (f.injective h)
  have fe00 : ¬ G.Adj (f 0) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 0) hh
  have fe01 : ¬ G.Adj (f 0) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 1) hh
  have fe02 : G.Adj (f 0) (f 2) := f.map_rel_iff.mpr (by decide)
  have fe03 : ¬ G.Adj (f 0) (f 3) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 3) hh
  have fe04 : G.Adj (f 0) (f 4) := f.map_rel_iff.mpr (by decide)
  have fe05 : ¬ G.Adj (f 0) (f 5) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 5) hh
  have fe06 : ¬ G.Adj (f 0) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 6) hh
  have fe10 : ¬ G.Adj (f 1) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 0) hh
  have fe11 : ¬ G.Adj (f 1) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 1) hh
  have fe12 : ¬ G.Adj (f 1) (f 2) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 2) hh
  have fe13 : G.Adj (f 1) (f 3) := f.map_rel_iff.mpr (by decide)
  have fe14 : G.Adj (f 1) (f 4) := f.map_rel_iff.mpr (by decide)
  have fe15 : ¬ G.Adj (f 1) (f 5) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 5) hh
  have fe16 : ¬ G.Adj (f 1) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 6) hh
  have fe20 : G.Adj (f 2) (f 0) := f.map_rel_iff.mpr (by decide)
  have fe21 : ¬ G.Adj (f 2) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 1) hh
  have fe22 : ¬ G.Adj (f 2) (f 2) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 2) hh
  have fe23 : G.Adj (f 2) (f 3) := f.map_rel_iff.mpr (by decide)
  have fe24 : ¬ G.Adj (f 2) (f 4) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 4) hh
  have fe25 : G.Adj (f 2) (f 5) := f.map_rel_iff.mpr (by decide)
  have fe26 : ¬ G.Adj (f 2) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 6) hh
  have fe30 : ¬ G.Adj (f 3) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 0) hh
  have fe31 : G.Adj (f 3) (f 1) := f.map_rel_iff.mpr (by decide)
  have fe32 : G.Adj (f 3) (f 2) := f.map_rel_iff.mpr (by decide)
  have fe33 : ¬ G.Adj (f 3) (f 3) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 3) hh
  have fe34 : ¬ G.Adj (f 3) (f 4) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 4) hh
  have fe35 : G.Adj (f 3) (f 5) := f.map_rel_iff.mpr (by decide)
  have fe36 : ¬ G.Adj (f 3) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 6) hh
  have fe40 : G.Adj (f 4) (f 0) := f.map_rel_iff.mpr (by decide)
  have fe41 : G.Adj (f 4) (f 1) := f.map_rel_iff.mpr (by decide)
  have fe42 : ¬ G.Adj (f 4) (f 2) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 2) hh
  have fe43 : ¬ G.Adj (f 4) (f 3) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 3) hh
  have fe44 : ¬ G.Adj (f 4) (f 4) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 4) hh
  have fe45 : ¬ G.Adj (f 4) (f 5) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 5) hh
  have fe46 : G.Adj (f 4) (f 6) := f.map_rel_iff.mpr (by decide)
  have fe50 : ¬ G.Adj (f 5) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 0) hh
  have fe51 : ¬ G.Adj (f 5) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 1) hh
  have fe52 : G.Adj (f 5) (f 2) := f.map_rel_iff.mpr (by decide)
  have fe53 : G.Adj (f 5) (f 3) := f.map_rel_iff.mpr (by decide)
  have fe54 : ¬ G.Adj (f 5) (f 4) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 4) hh
  have fe55 : ¬ G.Adj (f 5) (f 5) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 5) hh
  have fe56 : G.Adj (f 5) (f 6) := f.map_rel_iff.mpr (by decide)
  have fe60 : ¬ G.Adj (f 6) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 0) hh
  have fe61 : ¬ G.Adj (f 6) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 1) hh
  have fe62 : ¬ G.Adj (f 6) (f 2) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 2) hh
  have fe63 : ¬ G.Adj (f 6) (f 3) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 3) hh
  have fe64 : G.Adj (f 6) (f 4) := f.map_rel_iff.mpr (by decide)
  have fe65 : G.Adj (f 6) (f 5) := f.map_rel_iff.mpr (by decide)
  have fe66 : ¬ G.Adj (f 6) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 6) hh
  have fs2 (x : V) (hx : G.Adj (f 2) x) : x = f 0 ∨ x = f 3 ∨ x = f 5 :=
    neighbor_eq_of_three hdeg (List.Nodup.map f.injective (by decide : ([0,3,5] : List (Fin 7)).Nodup)) fe20 fe23 fe25 hx
  have fs3 (x : V) (hx : G.Adj (f 3) x) : x = f 1 ∨ x = f 2 ∨ x = f 5 :=
    neighbor_eq_of_three hdeg (List.Nodup.map f.injective (by decide : ([1,2,5] : List (Fin 7)).Nodup)) fe31 fe32 fe35 hx
  have fs4 (x : V) (hx : G.Adj (f 4) x) : x = f 0 ∨ x = f 1 ∨ x = f 6 :=
    neighbor_eq_of_three hdeg (List.Nodup.map f.injective (by decide : ([0,1,6] : List (Fin 7)).Nodup)) fe40 fe41 fe46 hx
  have fs5 (x : V) (hx : G.Adj (f 5) x) : x = f 2 ∨ x = f 3 ∨ x = f 6 :=
    neighbor_eq_of_three hdeg (List.Nodup.map f.injective (by decide : ([2,3,6] : List (Fin 7)).Nodup)) fe52 fe53 fe56 hx
  have gn01 : g 0 ≠ g 1 := fun h => (by decide : (0 : Fin 7) ≠ 1) (g.injective h)
  have gn02 : g 0 ≠ g 2 := fun h => (by decide : (0 : Fin 7) ≠ 2) (g.injective h)
  have gn03 : g 0 ≠ g 3 := fun h => (by decide : (0 : Fin 7) ≠ 3) (g.injective h)
  have gn04 : g 0 ≠ g 4 := fun h => (by decide : (0 : Fin 7) ≠ 4) (g.injective h)
  have gn05 : g 0 ≠ g 5 := fun h => (by decide : (0 : Fin 7) ≠ 5) (g.injective h)
  have gn06 : g 0 ≠ g 6 := fun h => (by decide : (0 : Fin 7) ≠ 6) (g.injective h)
  have gn12 : g 1 ≠ g 2 := fun h => (by decide : (1 : Fin 7) ≠ 2) (g.injective h)
  have gn13 : g 1 ≠ g 3 := fun h => (by decide : (1 : Fin 7) ≠ 3) (g.injective h)
  have gn14 : g 1 ≠ g 4 := fun h => (by decide : (1 : Fin 7) ≠ 4) (g.injective h)
  have gn15 : g 1 ≠ g 5 := fun h => (by decide : (1 : Fin 7) ≠ 5) (g.injective h)
  have gn16 : g 1 ≠ g 6 := fun h => (by decide : (1 : Fin 7) ≠ 6) (g.injective h)
  have gn23 : g 2 ≠ g 3 := fun h => (by decide : (2 : Fin 7) ≠ 3) (g.injective h)
  have gn24 : g 2 ≠ g 4 := fun h => (by decide : (2 : Fin 7) ≠ 4) (g.injective h)
  have gn25 : g 2 ≠ g 5 := fun h => (by decide : (2 : Fin 7) ≠ 5) (g.injective h)
  have gn26 : g 2 ≠ g 6 := fun h => (by decide : (2 : Fin 7) ≠ 6) (g.injective h)
  have gn34 : g 3 ≠ g 4 := fun h => (by decide : (3 : Fin 7) ≠ 4) (g.injective h)
  have gn35 : g 3 ≠ g 5 := fun h => (by decide : (3 : Fin 7) ≠ 5) (g.injective h)
  have gn36 : g 3 ≠ g 6 := fun h => (by decide : (3 : Fin 7) ≠ 6) (g.injective h)
  have gn45 : g 4 ≠ g 5 := fun h => (by decide : (4 : Fin 7) ≠ 5) (g.injective h)
  have gn46 : g 4 ≠ g 6 := fun h => (by decide : (4 : Fin 7) ≠ 6) (g.injective h)
  have gn56 : g 5 ≠ g 6 := fun h => (by decide : (5 : Fin 7) ≠ 6) (g.injective h)
  have ge00 : ¬ G.Adj (g 0) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 0) hh
  have ge01 : ¬ G.Adj (g 0) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 1) hh
  have ge02 : G.Adj (g 0) (g 2) := g.map_rel_iff.mpr (by decide)
  have ge03 : ¬ G.Adj (g 0) (g 3) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 3) hh
  have ge04 : G.Adj (g 0) (g 4) := g.map_rel_iff.mpr (by decide)
  have ge05 : ¬ G.Adj (g 0) (g 5) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 5) hh
  have ge06 : ¬ G.Adj (g 0) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 6) hh
  have ge10 : ¬ G.Adj (g 1) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 0) hh
  have ge11 : ¬ G.Adj (g 1) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 1) hh
  have ge12 : ¬ G.Adj (g 1) (g 2) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 2) hh
  have ge13 : G.Adj (g 1) (g 3) := g.map_rel_iff.mpr (by decide)
  have ge14 : G.Adj (g 1) (g 4) := g.map_rel_iff.mpr (by decide)
  have ge15 : ¬ G.Adj (g 1) (g 5) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 5) hh
  have ge16 : ¬ G.Adj (g 1) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 6) hh
  have ge20 : G.Adj (g 2) (g 0) := g.map_rel_iff.mpr (by decide)
  have ge21 : ¬ G.Adj (g 2) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 1) hh
  have ge22 : ¬ G.Adj (g 2) (g 2) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 2) hh
  have ge23 : G.Adj (g 2) (g 3) := g.map_rel_iff.mpr (by decide)
  have ge24 : ¬ G.Adj (g 2) (g 4) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 4) hh
  have ge25 : G.Adj (g 2) (g 5) := g.map_rel_iff.mpr (by decide)
  have ge26 : ¬ G.Adj (g 2) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 6) hh
  have ge30 : ¬ G.Adj (g 3) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 0) hh
  have ge31 : G.Adj (g 3) (g 1) := g.map_rel_iff.mpr (by decide)
  have ge32 : G.Adj (g 3) (g 2) := g.map_rel_iff.mpr (by decide)
  have ge33 : ¬ G.Adj (g 3) (g 3) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 3) hh
  have ge34 : ¬ G.Adj (g 3) (g 4) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 4) hh
  have ge35 : G.Adj (g 3) (g 5) := g.map_rel_iff.mpr (by decide)
  have ge36 : ¬ G.Adj (g 3) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 6) hh
  have ge40 : G.Adj (g 4) (g 0) := g.map_rel_iff.mpr (by decide)
  have ge41 : G.Adj (g 4) (g 1) := g.map_rel_iff.mpr (by decide)
  have ge42 : ¬ G.Adj (g 4) (g 2) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 2) hh
  have ge43 : ¬ G.Adj (g 4) (g 3) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 3) hh
  have ge44 : ¬ G.Adj (g 4) (g 4) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 4) hh
  have ge45 : ¬ G.Adj (g 4) (g 5) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 5) hh
  have ge46 : G.Adj (g 4) (g 6) := g.map_rel_iff.mpr (by decide)
  have ge50 : ¬ G.Adj (g 5) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 0) hh
  have ge51 : ¬ G.Adj (g 5) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 1) hh
  have ge52 : G.Adj (g 5) (g 2) := g.map_rel_iff.mpr (by decide)
  have ge53 : G.Adj (g 5) (g 3) := g.map_rel_iff.mpr (by decide)
  have ge54 : ¬ G.Adj (g 5) (g 4) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 4) hh
  have ge55 : ¬ G.Adj (g 5) (g 5) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 5) hh
  have ge56 : G.Adj (g 5) (g 6) := g.map_rel_iff.mpr (by decide)
  have ge60 : ¬ G.Adj (g 6) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 0) hh
  have ge61 : ¬ G.Adj (g 6) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 1) hh
  have ge62 : ¬ G.Adj (g 6) (g 2) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 2) hh
  have ge63 : ¬ G.Adj (g 6) (g 3) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 3) hh
  have ge64 : G.Adj (g 6) (g 4) := g.map_rel_iff.mpr (by decide)
  have ge65 : G.Adj (g 6) (g 5) := g.map_rel_iff.mpr (by decide)
  have ge66 : ¬ G.Adj (g 6) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 6) hh
  have gs2 (x : V) (hx : G.Adj (g 2) x) : x = g 0 ∨ x = g 3 ∨ x = g 5 :=
    neighbor_eq_of_three hdeg (List.Nodup.map g.injective (by decide : ([0,3,5] : List (Fin 7)).Nodup)) ge20 ge23 ge25 hx
  have gs3 (x : V) (hx : G.Adj (g 3) x) : x = g 1 ∨ x = g 2 ∨ x = g 5 :=
    neighbor_eq_of_three hdeg (List.Nodup.map g.injective (by decide : ([1,2,5] : List (Fin 7)).Nodup)) ge31 ge32 ge35 hx
  have gs4 (x : V) (hx : G.Adj (g 4) x) : x = g 0 ∨ x = g 1 ∨ x = g 6 :=
    neighbor_eq_of_three hdeg (List.Nodup.map g.injective (by decide : ([0,1,6] : List (Fin 7)).Nodup)) ge40 ge41 ge46 hx
  have gs5 (x : V) (hx : G.Adj (g 5) x) : x = g 2 ∨ x = g 3 ∨ x = g 6 :=
    neighbor_eq_of_three hdeg (List.Nodup.map g.injective (by decide : ([2,3,6] : List (Fin 7)).Nodup)) ge52 ge53 ge56 hx
  grind (splits := 15)

/-- The six paired permutations of the triangle vertices and their associated
ports, fixing the center. Each row is an exact map in the prescribed Fin-7 labeling. -/
private def symmLabelPerm (p : Fin 6) : Fin 7 → Fin 7 :=
  (![ (![0,1,2,3,4,5,6]), (![0,6,2,5,4,3,1]),
      (![1,0,3,2,4,5,6]), (![1,6,3,5,4,2,0]),
      (![6,0,5,2,4,3,1]), (![6,1,5,3,4,2,0])] : Fin 6 → Fin 7 → Fin 7) p

example : symmLabelPerm 0 = id := by funext i; fin_cases i <;> rfl
example : symmLabelPerm 3 0 = 1 ∧ symmLabelPerm 3 2 = 3 := by decide

/-- Each paired label permutation is a graph automorphism of the exact symmetric graph. -/
private noncomputable def symmAuto (p : Fin 6) : h7Symm ≃g h7Symm where
  toEquiv := Equiv.ofBijective (symmLabelPerm p) (by fin_cases p <;> decide)
  map_rel_iff' := by
    intro i j
    change h7Symm.Adj (symmLabelPerm p i) (symmLabelPerm p j) ↔ h7Symm.Adj i j
    fin_cases p <;> fin_cases i <;> fin_cases j <;> decide

example : symmAuto 0 4 = 4 := rfl

set_option maxHeartbeats 1000000 in
/-- A shared saturated center identifies its three ports up to a permutation.
The six alternatives are proved from induced adjacency and degree exhaustion. -/
private theorem center_checkpoint {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) (f g : h7Symm ↪g G) (hc : f 4 = g 4) :
    (f 0 = g 0 ∧ f 1 = g 1 ∧ f 6 = g 6) ∨
    (f 0 = g 0 ∧ f 1 = g 6 ∧ f 6 = g 1) ∨
    (f 0 = g 1 ∧ f 1 = g 0 ∧ f 6 = g 6) ∨
    (f 0 = g 1 ∧ f 1 = g 6 ∧ f 6 = g 0) ∨
    (f 0 = g 6 ∧ f 1 = g 0 ∧ f 6 = g 1) ∨
    (f 0 = g 6 ∧ f 1 = g 1 ∧ f 6 = g 0) := by
  have fn01 : f 0 ≠ f 1 := fun h => (by decide : (0 : Fin 7) ≠ 1) (f.injective h)
  have fn02 : f 0 ≠ f 2 := fun h => (by decide : (0 : Fin 7) ≠ 2) (f.injective h)
  have fn03 : f 0 ≠ f 3 := fun h => (by decide : (0 : Fin 7) ≠ 3) (f.injective h)
  have fn04 : f 0 ≠ f 4 := fun h => (by decide : (0 : Fin 7) ≠ 4) (f.injective h)
  have fn05 : f 0 ≠ f 5 := fun h => (by decide : (0 : Fin 7) ≠ 5) (f.injective h)
  have fn06 : f 0 ≠ f 6 := fun h => (by decide : (0 : Fin 7) ≠ 6) (f.injective h)
  have fn12 : f 1 ≠ f 2 := fun h => (by decide : (1 : Fin 7) ≠ 2) (f.injective h)
  have fn13 : f 1 ≠ f 3 := fun h => (by decide : (1 : Fin 7) ≠ 3) (f.injective h)
  have fn14 : f 1 ≠ f 4 := fun h => (by decide : (1 : Fin 7) ≠ 4) (f.injective h)
  have fn15 : f 1 ≠ f 5 := fun h => (by decide : (1 : Fin 7) ≠ 5) (f.injective h)
  have fn16 : f 1 ≠ f 6 := fun h => (by decide : (1 : Fin 7) ≠ 6) (f.injective h)
  have fn23 : f 2 ≠ f 3 := fun h => (by decide : (2 : Fin 7) ≠ 3) (f.injective h)
  have fn24 : f 2 ≠ f 4 := fun h => (by decide : (2 : Fin 7) ≠ 4) (f.injective h)
  have fn25 : f 2 ≠ f 5 := fun h => (by decide : (2 : Fin 7) ≠ 5) (f.injective h)
  have fn26 : f 2 ≠ f 6 := fun h => (by decide : (2 : Fin 7) ≠ 6) (f.injective h)
  have fn34 : f 3 ≠ f 4 := fun h => (by decide : (3 : Fin 7) ≠ 4) (f.injective h)
  have fn35 : f 3 ≠ f 5 := fun h => (by decide : (3 : Fin 7) ≠ 5) (f.injective h)
  have fn36 : f 3 ≠ f 6 := fun h => (by decide : (3 : Fin 7) ≠ 6) (f.injective h)
  have fn45 : f 4 ≠ f 5 := fun h => (by decide : (4 : Fin 7) ≠ 5) (f.injective h)
  have fn46 : f 4 ≠ f 6 := fun h => (by decide : (4 : Fin 7) ≠ 6) (f.injective h)
  have fn56 : f 5 ≠ f 6 := fun h => (by decide : (5 : Fin 7) ≠ 6) (f.injective h)
  have fe00 : ¬ G.Adj (f 0) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 0) hh
  have fe01 : ¬ G.Adj (f 0) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 1) hh
  have fe02 : G.Adj (f 0) (f 2) := f.map_rel_iff.mpr (by decide)
  have fe03 : ¬ G.Adj (f 0) (f 3) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 3) hh
  have fe04 : G.Adj (f 0) (f 4) := f.map_rel_iff.mpr (by decide)
  have fe05 : ¬ G.Adj (f 0) (f 5) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 5) hh
  have fe06 : ¬ G.Adj (f 0) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 6) hh
  have fe10 : ¬ G.Adj (f 1) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 0) hh
  have fe11 : ¬ G.Adj (f 1) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 1) hh
  have fe12 : ¬ G.Adj (f 1) (f 2) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 2) hh
  have fe13 : G.Adj (f 1) (f 3) := f.map_rel_iff.mpr (by decide)
  have fe14 : G.Adj (f 1) (f 4) := f.map_rel_iff.mpr (by decide)
  have fe15 : ¬ G.Adj (f 1) (f 5) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 5) hh
  have fe16 : ¬ G.Adj (f 1) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 6) hh
  have fe20 : G.Adj (f 2) (f 0) := f.map_rel_iff.mpr (by decide)
  have fe21 : ¬ G.Adj (f 2) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 1) hh
  have fe22 : ¬ G.Adj (f 2) (f 2) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 2) hh
  have fe23 : G.Adj (f 2) (f 3) := f.map_rel_iff.mpr (by decide)
  have fe24 : ¬ G.Adj (f 2) (f 4) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 4) hh
  have fe25 : G.Adj (f 2) (f 5) := f.map_rel_iff.mpr (by decide)
  have fe26 : ¬ G.Adj (f 2) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 6) hh
  have fe30 : ¬ G.Adj (f 3) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 0) hh
  have fe31 : G.Adj (f 3) (f 1) := f.map_rel_iff.mpr (by decide)
  have fe32 : G.Adj (f 3) (f 2) := f.map_rel_iff.mpr (by decide)
  have fe33 : ¬ G.Adj (f 3) (f 3) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 3) hh
  have fe34 : ¬ G.Adj (f 3) (f 4) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 4) hh
  have fe35 : G.Adj (f 3) (f 5) := f.map_rel_iff.mpr (by decide)
  have fe36 : ¬ G.Adj (f 3) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 6) hh
  have fe40 : G.Adj (f 4) (f 0) := f.map_rel_iff.mpr (by decide)
  have fe41 : G.Adj (f 4) (f 1) := f.map_rel_iff.mpr (by decide)
  have fe42 : ¬ G.Adj (f 4) (f 2) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 2) hh
  have fe43 : ¬ G.Adj (f 4) (f 3) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 3) hh
  have fe44 : ¬ G.Adj (f 4) (f 4) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 4) hh
  have fe45 : ¬ G.Adj (f 4) (f 5) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 5) hh
  have fe46 : G.Adj (f 4) (f 6) := f.map_rel_iff.mpr (by decide)
  have fe50 : ¬ G.Adj (f 5) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 0) hh
  have fe51 : ¬ G.Adj (f 5) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 1) hh
  have fe52 : G.Adj (f 5) (f 2) := f.map_rel_iff.mpr (by decide)
  have fe53 : G.Adj (f 5) (f 3) := f.map_rel_iff.mpr (by decide)
  have fe54 : ¬ G.Adj (f 5) (f 4) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 4) hh
  have fe55 : ¬ G.Adj (f 5) (f 5) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 5) hh
  have fe56 : G.Adj (f 5) (f 6) := f.map_rel_iff.mpr (by decide)
  have fe60 : ¬ G.Adj (f 6) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 0) hh
  have fe61 : ¬ G.Adj (f 6) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 1) hh
  have fe62 : ¬ G.Adj (f 6) (f 2) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 2) hh
  have fe63 : ¬ G.Adj (f 6) (f 3) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 3) hh
  have fe64 : G.Adj (f 6) (f 4) := f.map_rel_iff.mpr (by decide)
  have fe65 : G.Adj (f 6) (f 5) := f.map_rel_iff.mpr (by decide)
  have fe66 : ¬ G.Adj (f 6) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 6) hh
  have fs2 (x : V) (hx : G.Adj (f 2) x) : x = f 0 ∨ x = f 3 ∨ x = f 5 :=
    neighbor_eq_of_three hdeg (List.Nodup.map f.injective (by decide : ([0,3,5] : List (Fin 7)).Nodup)) fe20 fe23 fe25 hx
  have fs3 (x : V) (hx : G.Adj (f 3) x) : x = f 1 ∨ x = f 2 ∨ x = f 5 :=
    neighbor_eq_of_three hdeg (List.Nodup.map f.injective (by decide : ([1,2,5] : List (Fin 7)).Nodup)) fe31 fe32 fe35 hx
  have fs4 (x : V) (hx : G.Adj (f 4) x) : x = f 0 ∨ x = f 1 ∨ x = f 6 :=
    neighbor_eq_of_three hdeg (List.Nodup.map f.injective (by decide : ([0,1,6] : List (Fin 7)).Nodup)) fe40 fe41 fe46 hx
  have fs5 (x : V) (hx : G.Adj (f 5) x) : x = f 2 ∨ x = f 3 ∨ x = f 6 :=
    neighbor_eq_of_three hdeg (List.Nodup.map f.injective (by decide : ([2,3,6] : List (Fin 7)).Nodup)) fe52 fe53 fe56 hx
  have gn01 : g 0 ≠ g 1 := fun h => (by decide : (0 : Fin 7) ≠ 1) (g.injective h)
  have gn02 : g 0 ≠ g 2 := fun h => (by decide : (0 : Fin 7) ≠ 2) (g.injective h)
  have gn03 : g 0 ≠ g 3 := fun h => (by decide : (0 : Fin 7) ≠ 3) (g.injective h)
  have gn04 : g 0 ≠ g 4 := fun h => (by decide : (0 : Fin 7) ≠ 4) (g.injective h)
  have gn05 : g 0 ≠ g 5 := fun h => (by decide : (0 : Fin 7) ≠ 5) (g.injective h)
  have gn06 : g 0 ≠ g 6 := fun h => (by decide : (0 : Fin 7) ≠ 6) (g.injective h)
  have gn12 : g 1 ≠ g 2 := fun h => (by decide : (1 : Fin 7) ≠ 2) (g.injective h)
  have gn13 : g 1 ≠ g 3 := fun h => (by decide : (1 : Fin 7) ≠ 3) (g.injective h)
  have gn14 : g 1 ≠ g 4 := fun h => (by decide : (1 : Fin 7) ≠ 4) (g.injective h)
  have gn15 : g 1 ≠ g 5 := fun h => (by decide : (1 : Fin 7) ≠ 5) (g.injective h)
  have gn16 : g 1 ≠ g 6 := fun h => (by decide : (1 : Fin 7) ≠ 6) (g.injective h)
  have gn23 : g 2 ≠ g 3 := fun h => (by decide : (2 : Fin 7) ≠ 3) (g.injective h)
  have gn24 : g 2 ≠ g 4 := fun h => (by decide : (2 : Fin 7) ≠ 4) (g.injective h)
  have gn25 : g 2 ≠ g 5 := fun h => (by decide : (2 : Fin 7) ≠ 5) (g.injective h)
  have gn26 : g 2 ≠ g 6 := fun h => (by decide : (2 : Fin 7) ≠ 6) (g.injective h)
  have gn34 : g 3 ≠ g 4 := fun h => (by decide : (3 : Fin 7) ≠ 4) (g.injective h)
  have gn35 : g 3 ≠ g 5 := fun h => (by decide : (3 : Fin 7) ≠ 5) (g.injective h)
  have gn36 : g 3 ≠ g 6 := fun h => (by decide : (3 : Fin 7) ≠ 6) (g.injective h)
  have gn45 : g 4 ≠ g 5 := fun h => (by decide : (4 : Fin 7) ≠ 5) (g.injective h)
  have gn46 : g 4 ≠ g 6 := fun h => (by decide : (4 : Fin 7) ≠ 6) (g.injective h)
  have gn56 : g 5 ≠ g 6 := fun h => (by decide : (5 : Fin 7) ≠ 6) (g.injective h)
  have ge00 : ¬ G.Adj (g 0) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 0) hh
  have ge01 : ¬ G.Adj (g 0) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 1) hh
  have ge02 : G.Adj (g 0) (g 2) := g.map_rel_iff.mpr (by decide)
  have ge03 : ¬ G.Adj (g 0) (g 3) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 3) hh
  have ge04 : G.Adj (g 0) (g 4) := g.map_rel_iff.mpr (by decide)
  have ge05 : ¬ G.Adj (g 0) (g 5) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 5) hh
  have ge06 : ¬ G.Adj (g 0) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 6) hh
  have ge10 : ¬ G.Adj (g 1) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 0) hh
  have ge11 : ¬ G.Adj (g 1) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 1) hh
  have ge12 : ¬ G.Adj (g 1) (g 2) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 2) hh
  have ge13 : G.Adj (g 1) (g 3) := g.map_rel_iff.mpr (by decide)
  have ge14 : G.Adj (g 1) (g 4) := g.map_rel_iff.mpr (by decide)
  have ge15 : ¬ G.Adj (g 1) (g 5) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 5) hh
  have ge16 : ¬ G.Adj (g 1) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 6) hh
  have ge20 : G.Adj (g 2) (g 0) := g.map_rel_iff.mpr (by decide)
  have ge21 : ¬ G.Adj (g 2) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 1) hh
  have ge22 : ¬ G.Adj (g 2) (g 2) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 2) hh
  have ge23 : G.Adj (g 2) (g 3) := g.map_rel_iff.mpr (by decide)
  have ge24 : ¬ G.Adj (g 2) (g 4) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 4) hh
  have ge25 : G.Adj (g 2) (g 5) := g.map_rel_iff.mpr (by decide)
  have ge26 : ¬ G.Adj (g 2) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 6) hh
  have ge30 : ¬ G.Adj (g 3) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 0) hh
  have ge31 : G.Adj (g 3) (g 1) := g.map_rel_iff.mpr (by decide)
  have ge32 : G.Adj (g 3) (g 2) := g.map_rel_iff.mpr (by decide)
  have ge33 : ¬ G.Adj (g 3) (g 3) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 3) hh
  have ge34 : ¬ G.Adj (g 3) (g 4) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 4) hh
  have ge35 : G.Adj (g 3) (g 5) := g.map_rel_iff.mpr (by decide)
  have ge36 : ¬ G.Adj (g 3) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 6) hh
  have ge40 : G.Adj (g 4) (g 0) := g.map_rel_iff.mpr (by decide)
  have ge41 : G.Adj (g 4) (g 1) := g.map_rel_iff.mpr (by decide)
  have ge42 : ¬ G.Adj (g 4) (g 2) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 2) hh
  have ge43 : ¬ G.Adj (g 4) (g 3) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 3) hh
  have ge44 : ¬ G.Adj (g 4) (g 4) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 4) hh
  have ge45 : ¬ G.Adj (g 4) (g 5) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 5) hh
  have ge46 : G.Adj (g 4) (g 6) := g.map_rel_iff.mpr (by decide)
  have ge50 : ¬ G.Adj (g 5) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 0) hh
  have ge51 : ¬ G.Adj (g 5) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 1) hh
  have ge52 : G.Adj (g 5) (g 2) := g.map_rel_iff.mpr (by decide)
  have ge53 : G.Adj (g 5) (g 3) := g.map_rel_iff.mpr (by decide)
  have ge54 : ¬ G.Adj (g 5) (g 4) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 4) hh
  have ge55 : ¬ G.Adj (g 5) (g 5) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 5) hh
  have ge56 : G.Adj (g 5) (g 6) := g.map_rel_iff.mpr (by decide)
  have ge60 : ¬ G.Adj (g 6) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 0) hh
  have ge61 : ¬ G.Adj (g 6) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 1) hh
  have ge62 : ¬ G.Adj (g 6) (g 2) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 2) hh
  have ge63 : ¬ G.Adj (g 6) (g 3) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 3) hh
  have ge64 : G.Adj (g 6) (g 4) := g.map_rel_iff.mpr (by decide)
  have ge65 : G.Adj (g 6) (g 5) := g.map_rel_iff.mpr (by decide)
  have ge66 : ¬ G.Adj (g 6) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 6) hh
  have gs2 (x : V) (hx : G.Adj (g 2) x) : x = g 0 ∨ x = g 3 ∨ x = g 5 :=
    neighbor_eq_of_three hdeg (List.Nodup.map g.injective (by decide : ([0,3,5] : List (Fin 7)).Nodup)) ge20 ge23 ge25 hx
  have gs3 (x : V) (hx : G.Adj (g 3) x) : x = g 1 ∨ x = g 2 ∨ x = g 5 :=
    neighbor_eq_of_three hdeg (List.Nodup.map g.injective (by decide : ([1,2,5] : List (Fin 7)).Nodup)) ge31 ge32 ge35 hx
  have gs4 (x : V) (hx : G.Adj (g 4) x) : x = g 0 ∨ x = g 1 ∨ x = g 6 :=
    neighbor_eq_of_three hdeg (List.Nodup.map g.injective (by decide : ([0,1,6] : List (Fin 7)).Nodup)) ge40 ge41 ge46 hx
  have gs5 (x : V) (hx : G.Adj (g 5) x) : x = g 2 ∨ x = g 3 ∨ x = g 6 :=
    neighbor_eq_of_three hdeg (List.Nodup.map g.injective (by decide : ([2,3,6] : List (Fin 7)).Nodup)) ge52 ge53 ge56 hx
  grind (splits := 15)

set_option maxHeartbeats 1000000 in
/-- Every nonempty overlap reduces to a shared center or a shared triangle vertex.
The finite label cases use induced adjacency, cubic saturation, and the
four-neighbor collision bound, with no cycle-absence premise. -/
private theorem overlap_checkpoint {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) (f g : h7Symm ↪g G)
    (i j : Fin 7) (he : f i = g j) :
    f 4 = g 4 ∨
    f 2 = g 2 ∨ f 2 = g 3 ∨ f 2 = g 5 ∨
    f 3 = g 2 ∨ f 3 = g 3 ∨ f 3 = g 5 ∨
    f 5 = g 2 ∨ f 5 = g 3 ∨ f 5 = g 5 := by
  have fn01 : f 0 ≠ f 1 := fun h => (by decide : (0 : Fin 7) ≠ 1) (f.injective h)
  have fn02 : f 0 ≠ f 2 := fun h => (by decide : (0 : Fin 7) ≠ 2) (f.injective h)
  have fn03 : f 0 ≠ f 3 := fun h => (by decide : (0 : Fin 7) ≠ 3) (f.injective h)
  have fn04 : f 0 ≠ f 4 := fun h => (by decide : (0 : Fin 7) ≠ 4) (f.injective h)
  have fn05 : f 0 ≠ f 5 := fun h => (by decide : (0 : Fin 7) ≠ 5) (f.injective h)
  have fn06 : f 0 ≠ f 6 := fun h => (by decide : (0 : Fin 7) ≠ 6) (f.injective h)
  have fn12 : f 1 ≠ f 2 := fun h => (by decide : (1 : Fin 7) ≠ 2) (f.injective h)
  have fn13 : f 1 ≠ f 3 := fun h => (by decide : (1 : Fin 7) ≠ 3) (f.injective h)
  have fn14 : f 1 ≠ f 4 := fun h => (by decide : (1 : Fin 7) ≠ 4) (f.injective h)
  have fn15 : f 1 ≠ f 5 := fun h => (by decide : (1 : Fin 7) ≠ 5) (f.injective h)
  have fn16 : f 1 ≠ f 6 := fun h => (by decide : (1 : Fin 7) ≠ 6) (f.injective h)
  have fn23 : f 2 ≠ f 3 := fun h => (by decide : (2 : Fin 7) ≠ 3) (f.injective h)
  have fn24 : f 2 ≠ f 4 := fun h => (by decide : (2 : Fin 7) ≠ 4) (f.injective h)
  have fn25 : f 2 ≠ f 5 := fun h => (by decide : (2 : Fin 7) ≠ 5) (f.injective h)
  have fn26 : f 2 ≠ f 6 := fun h => (by decide : (2 : Fin 7) ≠ 6) (f.injective h)
  have fn34 : f 3 ≠ f 4 := fun h => (by decide : (3 : Fin 7) ≠ 4) (f.injective h)
  have fn35 : f 3 ≠ f 5 := fun h => (by decide : (3 : Fin 7) ≠ 5) (f.injective h)
  have fn36 : f 3 ≠ f 6 := fun h => (by decide : (3 : Fin 7) ≠ 6) (f.injective h)
  have fn45 : f 4 ≠ f 5 := fun h => (by decide : (4 : Fin 7) ≠ 5) (f.injective h)
  have fn46 : f 4 ≠ f 6 := fun h => (by decide : (4 : Fin 7) ≠ 6) (f.injective h)
  have fn56 : f 5 ≠ f 6 := fun h => (by decide : (5 : Fin 7) ≠ 6) (f.injective h)
  have fe00 : ¬ G.Adj (f 0) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 0) hh
  have fe01 : ¬ G.Adj (f 0) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 1) hh
  have fe02 : G.Adj (f 0) (f 2) := f.map_rel_iff.mpr (by decide)
  have fe03 : ¬ G.Adj (f 0) (f 3) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 3) hh
  have fe04 : G.Adj (f 0) (f 4) := f.map_rel_iff.mpr (by decide)
  have fe05 : ¬ G.Adj (f 0) (f 5) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 5) hh
  have fe06 : ¬ G.Adj (f 0) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 6) hh
  have fe10 : ¬ G.Adj (f 1) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 0) hh
  have fe11 : ¬ G.Adj (f 1) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 1) hh
  have fe12 : ¬ G.Adj (f 1) (f 2) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 2) hh
  have fe13 : G.Adj (f 1) (f 3) := f.map_rel_iff.mpr (by decide)
  have fe14 : G.Adj (f 1) (f 4) := f.map_rel_iff.mpr (by decide)
  have fe15 : ¬ G.Adj (f 1) (f 5) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 5) hh
  have fe16 : ¬ G.Adj (f 1) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 6) hh
  have fe20 : G.Adj (f 2) (f 0) := f.map_rel_iff.mpr (by decide)
  have fe21 : ¬ G.Adj (f 2) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 1) hh
  have fe22 : ¬ G.Adj (f 2) (f 2) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 2) hh
  have fe23 : G.Adj (f 2) (f 3) := f.map_rel_iff.mpr (by decide)
  have fe24 : ¬ G.Adj (f 2) (f 4) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 4) hh
  have fe25 : G.Adj (f 2) (f 5) := f.map_rel_iff.mpr (by decide)
  have fe26 : ¬ G.Adj (f 2) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 6) hh
  have fe30 : ¬ G.Adj (f 3) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 0) hh
  have fe31 : G.Adj (f 3) (f 1) := f.map_rel_iff.mpr (by decide)
  have fe32 : G.Adj (f 3) (f 2) := f.map_rel_iff.mpr (by decide)
  have fe33 : ¬ G.Adj (f 3) (f 3) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 3) hh
  have fe34 : ¬ G.Adj (f 3) (f 4) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 4) hh
  have fe35 : G.Adj (f 3) (f 5) := f.map_rel_iff.mpr (by decide)
  have fe36 : ¬ G.Adj (f 3) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 6) hh
  have fe40 : G.Adj (f 4) (f 0) := f.map_rel_iff.mpr (by decide)
  have fe41 : G.Adj (f 4) (f 1) := f.map_rel_iff.mpr (by decide)
  have fe42 : ¬ G.Adj (f 4) (f 2) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 2) hh
  have fe43 : ¬ G.Adj (f 4) (f 3) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 3) hh
  have fe44 : ¬ G.Adj (f 4) (f 4) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 4) hh
  have fe45 : ¬ G.Adj (f 4) (f 5) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 5) hh
  have fe46 : G.Adj (f 4) (f 6) := f.map_rel_iff.mpr (by decide)
  have fe50 : ¬ G.Adj (f 5) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 0) hh
  have fe51 : ¬ G.Adj (f 5) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 1) hh
  have fe52 : G.Adj (f 5) (f 2) := f.map_rel_iff.mpr (by decide)
  have fe53 : G.Adj (f 5) (f 3) := f.map_rel_iff.mpr (by decide)
  have fe54 : ¬ G.Adj (f 5) (f 4) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 4) hh
  have fe55 : ¬ G.Adj (f 5) (f 5) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 5) hh
  have fe56 : G.Adj (f 5) (f 6) := f.map_rel_iff.mpr (by decide)
  have fe60 : ¬ G.Adj (f 6) (f 0) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 0) hh
  have fe61 : ¬ G.Adj (f 6) (f 1) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 1) hh
  have fe62 : ¬ G.Adj (f 6) (f 2) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 2) hh
  have fe63 : ¬ G.Adj (f 6) (f 3) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 3) hh
  have fe64 : G.Adj (f 6) (f 4) := f.map_rel_iff.mpr (by decide)
  have fe65 : G.Adj (f 6) (f 5) := f.map_rel_iff.mpr (by decide)
  have fe66 : ¬ G.Adj (f 6) (f 6) := by
    intro h
    have hh := f.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 6) hh
  have fs2 (x : V) (hx : G.Adj (f 2) x) : x = f 0 ∨ x = f 3 ∨ x = f 5 :=
    neighbor_eq_of_three hdeg (List.Nodup.map f.injective (by decide : ([0,3,5] : List (Fin 7)).Nodup)) fe20 fe23 fe25 hx
  have fs3 (x : V) (hx : G.Adj (f 3) x) : x = f 1 ∨ x = f 2 ∨ x = f 5 :=
    neighbor_eq_of_three hdeg (List.Nodup.map f.injective (by decide : ([1,2,5] : List (Fin 7)).Nodup)) fe31 fe32 fe35 hx
  have fs4 (x : V) (hx : G.Adj (f 4) x) : x = f 0 ∨ x = f 1 ∨ x = f 6 :=
    neighbor_eq_of_three hdeg (List.Nodup.map f.injective (by decide : ([0,1,6] : List (Fin 7)).Nodup)) fe40 fe41 fe46 hx
  have fs5 (x : V) (hx : G.Adj (f 5) x) : x = f 2 ∨ x = f 3 ∨ x = f 6 :=
    neighbor_eq_of_three hdeg (List.Nodup.map f.injective (by decide : ([2,3,6] : List (Fin 7)).Nodup)) fe52 fe53 fe56 hx
  have gn01 : g 0 ≠ g 1 := fun h => (by decide : (0 : Fin 7) ≠ 1) (g.injective h)
  have gn02 : g 0 ≠ g 2 := fun h => (by decide : (0 : Fin 7) ≠ 2) (g.injective h)
  have gn03 : g 0 ≠ g 3 := fun h => (by decide : (0 : Fin 7) ≠ 3) (g.injective h)
  have gn04 : g 0 ≠ g 4 := fun h => (by decide : (0 : Fin 7) ≠ 4) (g.injective h)
  have gn05 : g 0 ≠ g 5 := fun h => (by decide : (0 : Fin 7) ≠ 5) (g.injective h)
  have gn06 : g 0 ≠ g 6 := fun h => (by decide : (0 : Fin 7) ≠ 6) (g.injective h)
  have gn12 : g 1 ≠ g 2 := fun h => (by decide : (1 : Fin 7) ≠ 2) (g.injective h)
  have gn13 : g 1 ≠ g 3 := fun h => (by decide : (1 : Fin 7) ≠ 3) (g.injective h)
  have gn14 : g 1 ≠ g 4 := fun h => (by decide : (1 : Fin 7) ≠ 4) (g.injective h)
  have gn15 : g 1 ≠ g 5 := fun h => (by decide : (1 : Fin 7) ≠ 5) (g.injective h)
  have gn16 : g 1 ≠ g 6 := fun h => (by decide : (1 : Fin 7) ≠ 6) (g.injective h)
  have gn23 : g 2 ≠ g 3 := fun h => (by decide : (2 : Fin 7) ≠ 3) (g.injective h)
  have gn24 : g 2 ≠ g 4 := fun h => (by decide : (2 : Fin 7) ≠ 4) (g.injective h)
  have gn25 : g 2 ≠ g 5 := fun h => (by decide : (2 : Fin 7) ≠ 5) (g.injective h)
  have gn26 : g 2 ≠ g 6 := fun h => (by decide : (2 : Fin 7) ≠ 6) (g.injective h)
  have gn34 : g 3 ≠ g 4 := fun h => (by decide : (3 : Fin 7) ≠ 4) (g.injective h)
  have gn35 : g 3 ≠ g 5 := fun h => (by decide : (3 : Fin 7) ≠ 5) (g.injective h)
  have gn36 : g 3 ≠ g 6 := fun h => (by decide : (3 : Fin 7) ≠ 6) (g.injective h)
  have gn45 : g 4 ≠ g 5 := fun h => (by decide : (4 : Fin 7) ≠ 5) (g.injective h)
  have gn46 : g 4 ≠ g 6 := fun h => (by decide : (4 : Fin 7) ≠ 6) (g.injective h)
  have gn56 : g 5 ≠ g 6 := fun h => (by decide : (5 : Fin 7) ≠ 6) (g.injective h)
  have ge00 : ¬ G.Adj (g 0) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 0) hh
  have ge01 : ¬ G.Adj (g 0) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 1) hh
  have ge02 : G.Adj (g 0) (g 2) := g.map_rel_iff.mpr (by decide)
  have ge03 : ¬ G.Adj (g 0) (g 3) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 3) hh
  have ge04 : G.Adj (g 0) (g 4) := g.map_rel_iff.mpr (by decide)
  have ge05 : ¬ G.Adj (g 0) (g 5) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 5) hh
  have ge06 : ¬ G.Adj (g 0) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 0 6) hh
  have ge10 : ¬ G.Adj (g 1) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 0) hh
  have ge11 : ¬ G.Adj (g 1) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 1) hh
  have ge12 : ¬ G.Adj (g 1) (g 2) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 2) hh
  have ge13 : G.Adj (g 1) (g 3) := g.map_rel_iff.mpr (by decide)
  have ge14 : G.Adj (g 1) (g 4) := g.map_rel_iff.mpr (by decide)
  have ge15 : ¬ G.Adj (g 1) (g 5) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 5) hh
  have ge16 : ¬ G.Adj (g 1) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 1 6) hh
  have ge20 : G.Adj (g 2) (g 0) := g.map_rel_iff.mpr (by decide)
  have ge21 : ¬ G.Adj (g 2) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 1) hh
  have ge22 : ¬ G.Adj (g 2) (g 2) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 2) hh
  have ge23 : G.Adj (g 2) (g 3) := g.map_rel_iff.mpr (by decide)
  have ge24 : ¬ G.Adj (g 2) (g 4) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 4) hh
  have ge25 : G.Adj (g 2) (g 5) := g.map_rel_iff.mpr (by decide)
  have ge26 : ¬ G.Adj (g 2) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 2 6) hh
  have ge30 : ¬ G.Adj (g 3) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 0) hh
  have ge31 : G.Adj (g 3) (g 1) := g.map_rel_iff.mpr (by decide)
  have ge32 : G.Adj (g 3) (g 2) := g.map_rel_iff.mpr (by decide)
  have ge33 : ¬ G.Adj (g 3) (g 3) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 3) hh
  have ge34 : ¬ G.Adj (g 3) (g 4) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 4) hh
  have ge35 : G.Adj (g 3) (g 5) := g.map_rel_iff.mpr (by decide)
  have ge36 : ¬ G.Adj (g 3) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 3 6) hh
  have ge40 : G.Adj (g 4) (g 0) := g.map_rel_iff.mpr (by decide)
  have ge41 : G.Adj (g 4) (g 1) := g.map_rel_iff.mpr (by decide)
  have ge42 : ¬ G.Adj (g 4) (g 2) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 2) hh
  have ge43 : ¬ G.Adj (g 4) (g 3) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 3) hh
  have ge44 : ¬ G.Adj (g 4) (g 4) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 4) hh
  have ge45 : ¬ G.Adj (g 4) (g 5) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 4 5) hh
  have ge46 : G.Adj (g 4) (g 6) := g.map_rel_iff.mpr (by decide)
  have ge50 : ¬ G.Adj (g 5) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 0) hh
  have ge51 : ¬ G.Adj (g 5) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 1) hh
  have ge52 : G.Adj (g 5) (g 2) := g.map_rel_iff.mpr (by decide)
  have ge53 : G.Adj (g 5) (g 3) := g.map_rel_iff.mpr (by decide)
  have ge54 : ¬ G.Adj (g 5) (g 4) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 4) hh
  have ge55 : ¬ G.Adj (g 5) (g 5) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 5 5) hh
  have ge56 : G.Adj (g 5) (g 6) := g.map_rel_iff.mpr (by decide)
  have ge60 : ¬ G.Adj (g 6) (g 0) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 0) hh
  have ge61 : ¬ G.Adj (g 6) (g 1) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 1) hh
  have ge62 : ¬ G.Adj (g 6) (g 2) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 2) hh
  have ge63 : ¬ G.Adj (g 6) (g 3) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 3) hh
  have ge64 : G.Adj (g 6) (g 4) := g.map_rel_iff.mpr (by decide)
  have ge65 : G.Adj (g 6) (g 5) := g.map_rel_iff.mpr (by decide)
  have ge66 : ¬ G.Adj (g 6) (g 6) := by
    intro h
    have hh := g.map_rel_iff.mp h
    exact (by decide : ¬ h7Symm.Adj 6 6) hh
  have gs2 (x : V) (hx : G.Adj (g 2) x) : x = g 0 ∨ x = g 3 ∨ x = g 5 :=
    neighbor_eq_of_three hdeg (List.Nodup.map g.injective (by decide : ([0,3,5] : List (Fin 7)).Nodup)) ge20 ge23 ge25 hx
  have gs3 (x : V) (hx : G.Adj (g 3) x) : x = g 1 ∨ x = g 2 ∨ x = g 5 :=
    neighbor_eq_of_three hdeg (List.Nodup.map g.injective (by decide : ([1,2,5] : List (Fin 7)).Nodup)) ge31 ge32 ge35 hx
  have gs4 (x : V) (hx : G.Adj (g 4) x) : x = g 0 ∨ x = g 1 ∨ x = g 6 :=
    neighbor_eq_of_three hdeg (List.Nodup.map g.injective (by decide : ([0,1,6] : List (Fin 7)).Nodup)) ge40 ge41 ge46 hx
  have gs5 (x : V) (hx : G.Adj (g 5) x) : x = g 2 ∨ x = g 3 ∨ x = g 6 :=
    neighbor_eq_of_three hdeg (List.Nodup.map g.injective (by decide : ([2,3,6] : List (Fin 7)).Nodup)) ge52 ge53 ge56 hx
  have collision00 (he : f 0 = g 0) : f 2 = g 2 ∨ f 2 = g 4 ∨ f 4 = g 2 ∨ f 4 = g 4 := by
    have hh := four_neighbors hdeg fe02 fe04 (he.symm ▸ ge02) (he.symm ▸ ge04)
    grind
  have collision01 (he : f 0 = g 1) : f 2 = g 3 ∨ f 2 = g 4 ∨ f 4 = g 3 ∨ f 4 = g 4 := by
    have hh := four_neighbors hdeg fe02 fe04 (he.symm ▸ ge13) (he.symm ▸ ge14)
    grind
  have collision06 (he : f 0 = g 6) : f 2 = g 4 ∨ f 2 = g 5 ∨ f 4 = g 4 ∨ f 4 = g 5 := by
    have hh := four_neighbors hdeg fe02 fe04 (he.symm ▸ ge64) (he.symm ▸ ge65)
    grind
  have collision10 (he : f 1 = g 0) : f 3 = g 2 ∨ f 3 = g 4 ∨ f 4 = g 2 ∨ f 4 = g 4 := by
    have hh := four_neighbors hdeg fe13 fe14 (he.symm ▸ ge02) (he.symm ▸ ge04)
    grind
  have collision11 (he : f 1 = g 1) : f 3 = g 3 ∨ f 3 = g 4 ∨ f 4 = g 3 ∨ f 4 = g 4 := by
    have hh := four_neighbors hdeg fe13 fe14 (he.symm ▸ ge13) (he.symm ▸ ge14)
    grind
  have collision16 (he : f 1 = g 6) : f 3 = g 4 ∨ f 3 = g 5 ∨ f 4 = g 4 ∨ f 4 = g 5 := by
    have hh := four_neighbors hdeg fe13 fe14 (he.symm ▸ ge64) (he.symm ▸ ge65)
    grind
  have collision60 (he : f 6 = g 0) : f 4 = g 2 ∨ f 4 = g 4 ∨ f 5 = g 2 ∨ f 5 = g 4 := by
    have hh := four_neighbors hdeg fe64 fe65 (he.symm ▸ ge02) (he.symm ▸ ge04)
    grind
  have collision61 (he : f 6 = g 1) : f 4 = g 3 ∨ f 4 = g 4 ∨ f 5 = g 3 ∨ f 5 = g 4 := by
    have hh := four_neighbors hdeg fe64 fe65 (he.symm ▸ ge13) (he.symm ▸ ge14)
    grind
  have collision66 (he : f 6 = g 6) : f 4 = g 4 ∨ f 4 = g 5 ∨ f 5 = g 4 ∨ f 5 = g 5 := by
    have hh := four_neighbors hdeg fe64 fe65 (he.symm ▸ ge64) (he.symm ▸ ge65)
    grind
  fin_cases i <;> fin_cases j <;> grind (splits := 15)

/-- The exact symmetric graph is subcubic. -/
theorem h7Symm_subcubic : ∀ v, h7Symm.degree v ≤ 3 := by decide

/-- The symmetric graph has no genuine simple eight-cycle: it has seven vertices. -/
theorem h7Symm_no_cycle_eight : ¬ HasSimpleCycleOfLength h7Symm 8 := by
  rintro ⟨v, w, hw, hl⟩
  have hc := cycle_length_le_card hw
  simp only [Fintype.card_fin] at hc
  omega

instance : DecidableRel (h7.sum h7Symm).Adj := fun x y => by
  cases x <;> cases y
  · exact decidable_of_iff _ SimpleGraph.sum_adj_inl.symm
  · exact isFalse (by simp)
  · exact isFalse (by simp)
  · exact decidable_of_iff _ SimpleGraph.sum_adj_inr.symm

instance : DecidableRel (h7Symm.sum h7Symm).Adj := fun x y => by
  cases x <;> cases y
  · exact decidable_of_iff _ SimpleGraph.sum_adj_inl.symm
  · exact isFalse (by simp)
  · exact isFalse (by simp)
  · exact decidable_of_iff _ SimpleGraph.sum_adj_inr.symm

/-- A mixed disjoint-union fixture jointly realizes both embeddings and the
subcubic hypothesis, independently of the packing theorem. -/
theorem h7_h7Symm_fixture :
    (∀ v, (h7.sum h7Symm).degree v ≤ 3) ∧
    ∃ (f : h7 ↪g h7.sum h7Symm) (g : h7Symm ↪g h7.sum h7Symm),
      Disjoint (Set.range f) (Set.range g) := by
  have hdeg : ∀ v, (h7.sum h7Symm).degree v ≤ 3 := by
    intro v
    unfold SimpleGraph.degree
    have he : (h7.sum h7Symm).neighborFinset v =
        Finset.univ.filter (fun w => (h7.sum h7Symm).Adj v w) := by
      ext w
      simp
    rw [he]
    clear he
    revert v
    decide
  refine ⟨hdeg, Embedding.sumInl, Embedding.sumInr, ?_⟩
  rw [Set.disjoint_left]
  rintro x ⟨i, rfl⟩ ⟨j, he⟩
  cases he

/-- A self-copy fixture jointly realizes the equal-copy case and every
subcubic/no-C8 hypothesis without invoking packing. -/
theorem h7Symm_self_fixture :
    (∀ v, h7Symm.degree v ≤ 3) ∧ ¬ HasSimpleCycleOfLength h7Symm 8 ∧
    ∃ (f g : h7Symm ↪g h7Symm), Set.range f = Set.range g := by
  exact ⟨h7Symm_subcubic, h7Symm_no_cycle_eight,
    RelEmbedding.refl _, RelEmbedding.refl _, rfl⟩

/-- Every simple cycle in the disjoint sum remains in one seven-vertex component. -/
theorem h7Symm_sum_no_cycle_eight : ¬ HasSimpleCycleOfLength (h7Symm.sum h7Symm) 8 := by
  rintro ⟨v, w, hw, hl⟩
  let collapse : Fin 7 ⊕ Fin 7 → Fin 7 := Sum.elim id id
  have hinj : ∀ x ∈ w.support.tail, ∀ y ∈ w.support.tail,
      collapse x = collapse y → x = y := by
    intro x hx y hy he
    have hrx := (w.takeUntil x (List.mem_of_mem_tail hx)).reachable
    have hry := (w.takeUntil y (List.mem_of_mem_tail hy)).reachable
    cases v <;> cases x <;> cases y
    all_goals try exact congrArg Sum.inl he
    all_goals try exact congrArg Sum.inr he
    all_goals first
      | exact False.elim (not_reachable_sum_inl_inr _ _ hrx)
      | exact False.elim (not_reachable_sum_inl_inr _ _ hry)
      | exact False.elim (not_reachable_sum_inl_inr _ _ hrx.symm)
      | exact False.elim (not_reachable_sum_inl_inr _ _ hry.symm)
  have hn := (List.Nodup.map_on hinj hw.support_nodup).length_le_card
  simp only [List.length_map, List.length_tail, Fintype.card_fin] at hn
  have hlen := w.length_support
  omega

/-- Two copies in the standard disjoint sum jointly realize subcubicity,
absence of C8, and genuinely disjoint embedding ranges. -/
theorem h7Symm_disjoint_fixture :
    (∀ v, (h7Symm.sum h7Symm).degree v ≤ 3) ∧
    ¬ HasSimpleCycleOfLength (h7Symm.sum h7Symm) 8 ∧
    ∃ (f g : h7Symm ↪g h7Symm.sum h7Symm),
      Disjoint (Set.range f) (Set.range g) := by
  have hdeg : ∀ v, (h7Symm.sum h7Symm).degree v ≤ 3 := by
    intro v
    unfold SimpleGraph.degree
    have he : (h7Symm.sum h7Symm).neighborFinset v =
        Finset.univ.filter (fun w => (h7Symm.sum h7Symm).Adj v w) := by
      ext w
      simp
    rw [he]
    clear he
    revert v
    decide
  refine ⟨hdeg, h7Symm_sum_no_cycle_eight, Embedding.sumInl, Embedding.sumInr, ?_⟩
  rw [Set.disjoint_left]
  rintro x ⟨i, rfl⟩ ⟨j, he⟩
  cases he

private theorem range_comp_symmAuto {V : Type*} {G : SimpleGraph V}
    (f : h7Symm ↪g G) (p : Fin 6) :
    Set.range (f.comp (symmAuto p).toEmbedding) = Set.range f := by
  ext x
  change (∃ i, f (symmAuto p i) = x) ↔ ∃ i, f i = x
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨symmAuto p i, hi⟩
  · rintro ⟨i, hi⟩
    obtain ⟨j, hj⟩ := (symmAuto p).surjective i
    exact ⟨j, hj ▸ hi⟩

private theorem center_ranges_eq {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v ≤ 3)
    (h8 : ¬ HasSimpleCycleOfLength G 8) (f g : h7Symm ↪g G)
    (hc : f 4 = g 4) : Set.range f = Set.range g := by
  rcases center_checkpoint hdeg f g hc with
    ⟨h0,h1,h6⟩ | ⟨h0,h1,h6⟩ | ⟨h0,h1,h6⟩ |
    ⟨h0,h1,h6⟩ | ⟨h0,h1,h6⟩ | ⟨h0,h1,h6⟩
  · have hp := center_aligned hdeg h8 f (g.comp (symmAuto 0).toEmbedding) hc h0 h1 h6
    exact (congrArg Set.range (funext hp)).trans (range_comp_symmAuto g 0)
  · have hp := center_aligned hdeg h8 f (g.comp (symmAuto 1).toEmbedding) hc h0 h1 h6
    exact (congrArg Set.range (funext hp)).trans (range_comp_symmAuto g 1)
  · have hp := center_aligned hdeg h8 f (g.comp (symmAuto 2).toEmbedding) hc h0 h1 h6
    exact (congrArg Set.range (funext hp)).trans (range_comp_symmAuto g 2)
  · have hp := center_aligned hdeg h8 f (g.comp (symmAuto 3).toEmbedding) hc h0 h1 h6
    exact (congrArg Set.range (funext hp)).trans (range_comp_symmAuto g 3)
  · have hp := center_aligned hdeg h8 f (g.comp (symmAuto 4).toEmbedding) hc h0 h1 h6
    exact (congrArg Set.range (funext hp)).trans (range_comp_symmAuto g 4)
  · have hp := center_aligned hdeg h8 f (g.comp (symmAuto 5).toEmbedding) hc h0 h1 h6
    exact (congrArg Set.range (funext hp)).trans (range_comp_symmAuto g 5)

private theorem triangle_two_ranges_eq {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v ≤ 3)
    (h8 : ¬ HasSimpleCycleOfLength G 8) (f g : h7Symm ↪g G)
    (h2 : f 2 = g 2) : Set.range f = Set.range g := by
  rcases triangle_checkpoint hdeg f g h2 with
    ⟨h0,h1,h6,h2,h3,h5⟩ | ⟨h0,h1,h6,h2,h3,h5⟩
  · have hp := triangle_aligned hdeg h8 f (g.comp (symmAuto 0).toEmbedding) h0 h1 h6 h2 h3 h5
    exact (congrArg Set.range (funext hp)).trans (range_comp_symmAuto g 0)
  · have hp := triangle_aligned hdeg h8 f (g.comp (symmAuto 1).toEmbedding) h0 h1 h6 h2 h3 h5
    exact (congrArg Set.range (funext hp)).trans (range_comp_symmAuto g 1)

private theorem triangle_ranges_eq {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v ≤ 3)
    (h8 : ¬ HasSimpleCycleOfLength G 8) (f g : h7Symm ↪g G)
    (i j : Fin 7) (hi : i = 2 ∨ i = 3 ∨ i = 5) (hj : j = 2 ∨ j = 3 ∨ j = 5)
    (he : f i = g j) : Set.range f = Set.range g := by
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
  · have hr := triangle_two_ranges_eq hdeg h8
      (f.comp (symmAuto 0).toEmbedding) (g.comp (symmAuto 0).toEmbedding) he
    simpa only [range_comp_symmAuto] using hr
  · have hr := triangle_two_ranges_eq hdeg h8
      (f.comp (symmAuto 0).toEmbedding) (g.comp (symmAuto 2).toEmbedding) he
    simpa only [range_comp_symmAuto] using hr
  · have hr := triangle_two_ranges_eq hdeg h8
      (f.comp (symmAuto 0).toEmbedding) (g.comp (symmAuto 4).toEmbedding) he
    simpa only [range_comp_symmAuto] using hr
  · have hr := triangle_two_ranges_eq hdeg h8
      (f.comp (symmAuto 2).toEmbedding) (g.comp (symmAuto 0).toEmbedding) he
    simpa only [range_comp_symmAuto] using hr
  · have hr := triangle_two_ranges_eq hdeg h8
      (f.comp (symmAuto 2).toEmbedding) (g.comp (symmAuto 2).toEmbedding) he
    simpa only [range_comp_symmAuto] using hr
  · have hr := triangle_two_ranges_eq hdeg h8
      (f.comp (symmAuto 2).toEmbedding) (g.comp (symmAuto 4).toEmbedding) he
    simpa only [range_comp_symmAuto] using hr
  · have hr := triangle_two_ranges_eq hdeg h8
      (f.comp (symmAuto 4).toEmbedding) (g.comp (symmAuto 0).toEmbedding) he
    simpa only [range_comp_symmAuto] using hr
  · have hr := triangle_two_ranges_eq hdeg h8
      (f.comp (symmAuto 4).toEmbedding) (g.comp (symmAuto 2).toEmbedding) he
    simpa only [range_comp_symmAuto] using hr
  · have hr := triangle_two_ranges_eq hdeg h8
      (f.comp (symmAuto 4).toEmbedding) (g.comp (symmAuto 4).toEmbedding) he
    simpa only [range_comp_symmAuto] using hr

/-- In a finite subcubic graph with no genuine simple eight-cycle, any two
induced symmetric subdivided-K4 copies have equal or disjoint vertex ranges.
No C4, minimum-degree, connectedness, or assumed overlap classification is used. -/
theorem h7Symm_equal_or_disjoint {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v ≤ 3)
    (h8 : ¬ HasSimpleCycleOfLength G 8) (f g : h7Symm ↪g G) :
    Set.range f = Set.range g ∨ Disjoint (Set.range f) (Set.range g) := by
  classical
  by_cases hd : Disjoint (Set.range f) (Set.range g)
  · exact Or.inr hd
  left
  rw [Set.disjoint_left] at hd
  push Not at hd
  obtain ⟨x, ⟨i, rfl⟩, ⟨j, he⟩⟩ := hd
  rcases overlap_checkpoint hdeg f g i j he.symm with
    hc | h22 | h23 | h25 | h32 | h33 | h35 | h52 | h53 | h55
  · exact center_ranges_eq hdeg h8 f g hc
  · exact triangle_ranges_eq hdeg h8 f g 2 2 (by simp) (by simp) h22
  · exact triangle_ranges_eq hdeg h8 f g 2 3 (by simp) (by simp) h23
  · exact triangle_ranges_eq hdeg h8 f g 2 5 (by simp) (by simp) h25
  · exact triangle_ranges_eq hdeg h8 f g 3 2 (by simp) (by simp) h32
  · exact triangle_ranges_eq hdeg h8 f g 3 3 (by simp) (by simp) h33
  · exact triangle_ranges_eq hdeg h8 f g 3 5 (by simp) (by simp) h35
  · exact triangle_ranges_eq hdeg h8 f g 5 2 (by simp) (by simp) h52
  · exact triangle_ranges_eq hdeg h8 f g 5 3 (by simp) (by simp) h53
  · exact triangle_ranges_eq hdeg h8 f g 5 5 (by simp) (by simp) h55

end Erdos64.SubcubicFunnel
