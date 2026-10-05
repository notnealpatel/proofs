import Erdos.Erdos64.BipartiteRegionExclusion

/-!
# Conditional cubicity of bipartite vertex-minimal counterexamples

Global vertex minimality is among all finite nonempty graphs in the same universe,
not merely bipartite graphs. No counterexample existence or global E64 closure is
asserted. Joint satisfiability of the counterexample hypotheses is unknown.
-/

set_option autoImplicit false
universe u

namespace Erdos64.BipartiteMinimalCubic

open SimpleGraph
open scoped Classical

private theorem deletion_degree {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : V)
    (x : ↥((Finset.univ.erase d : Finset V) : Set V))
    (hmin : 3 ≤ G.degree x.val) :
    (G.induce ((Finset.univ.erase d : Finset V) : Set V)).degree x +
      (if G.Adj x.val d then 1 else 0) = G.degree x.val := by
  classical
  have hcard : (G.induce ((Finset.univ.erase d : Finset V) : Set V)).degree x =
      ((G.neighborFinset x.val).erase d).card := by
    rw [← card_neighborFinset_eq_degree,
      ← Finset.card_map (Function.Embedding.subtype (fun y => y ∈
        ((Finset.univ.erase d : Finset V) : Set V)))]
    congr 1
    ext y
    simp [and_comm]
  rw [hcard, Finset.card_erase_eq_ite]
  by_cases h : G.Adj x.val d
  · simp only [mem_neighborFinset, h, if_true, card_neighborFinset_eq_degree]
    omega
  · simp [h]

private theorem deletion_excluded {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hCE : IsCounterexample G)
    (hminimal : ∀ (W : Type u) [Fintype W] [Nonempty W] (Q : SimpleGraph W),
      Fintype.card W < Fintype.card V → (∀ v, 3 ≤ Q.degree v) → HasPowerOfTwoCycle Q)
    (c : V → Bool) (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y) (d : V)
    (hlow : (Finset.univ.filter (fun x : ↥((Finset.univ.erase d : Finset V) : Set V) =>
      (G.induce ((Finset.univ.erase d : Finset V) : Set V)).degree x ≤ 2)).card ≤ 2)
    (hhigh : ∃ x : ↥((Finset.univ.erase d : Finset V) : Set V),
      3 ≤ (G.induce ((Finset.univ.erase d : Finset V) : Set V)).degree x) : False := by
  classical
  apply BipartiteRegionExclusion.proper_induced_region_excluded G hCE hminimal
    (Finset.univ.erase d) ?_ (fun x => c x.val) (fun {_ _} h => hc h) hlow hhigh
  rw [Finset.card_erase_of_mem (Finset.mem_univ d), Finset.card_univ]
  have hcard := hCE.card_verts_ge_four
  omega

/-- In a finite nonempty counterexample with global vertex minimality among all finite
nonempty graphs in `Type u`, a proper Bool coloring forces every ordinary degree to
be exactly three. This is strictly conditional; it asserts neither counterexample
existence nor a reduction of all bipartite E64 instances to cubic bipartite ones. -/
theorem degree_eq_three {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hCE : IsCounterexample G)
    (hminimal : ∀ (W : Type u) [Fintype W] [Nonempty W] (Q : SimpleGraph W),
      Fintype.card W < Fintype.card V → (∀ v, 3 ≤ Q.degree v) → HasPowerOfTwoCycle Q)
    (c : V → Bool) (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y) :
    ∀ v, G.degree v = 3 := by
  classical
  have hnoMixed : ∀ w v, G.degree w = 3 → G.Adj w v → 4 ≤ G.degree v → False := by
    intro w v hw hwv hv
    let s := Finset.univ.erase w
    let B := G.induce (s : Set V)
    let L := Finset.univ.filter (fun x : ↥(s : Set V) => B.degree x ≤ 2)
    have hlowFacts : ∀ x ∈ L, G.Adj x.val w ∧ G.degree x.val = 3 := by
      intro x hx
      have hxlow : B.degree x ≤ 2 := (Finset.mem_filter.mp hx).2
      have hxdegree : B.degree x + (if G.Adj x.val w then 1 else 0) = G.degree x.val := by
        convert deletion_degree G w x (hCE.degree_ge_three x.val) using 1
      have hxmin := hCE.degree_ge_three x.val
      by_cases h : G.Adj x.val w
      · simp only [if_pos h] at hxdegree
        exact ⟨h, by omega⟩
      · simp only [if_neg h, Nat.add_zero] at hxdegree
        omega
    have hlow : L.card ≤ 2 := by
      have hinj : L.card ≤ ((G.neighborFinset w).erase v).card := by
        apply Finset.card_le_card_of_injOn (fun x => x.val)
        · intro x hx
          obtain ⟨hxw, hxthree⟩ := hlowFacts x hx
          have hxne : x.val ≠ v := by
            intro heq
            rw [heq] at hxthree
            omega
          exact Finset.mem_erase.mpr ⟨hxne, (G.mem_neighborFinset w x.val).mpr hxw.symm⟩
        · intro x hx y hy hxy
          exact Subtype.ext hxy
      have hcard : ((G.neighborFinset w).erase v).card = 2 := by
        rw [Finset.card_erase_of_mem ((G.mem_neighborFinset w v).mpr hwv),
          card_neighborFinset_eq_degree, hw]
      omega
    have hvne : v ≠ w := hwv.ne.symm
    let x : ↥(s : Set V) := ⟨v, by simp [s, hvne]⟩
    have hxhigh : 3 ≤ B.degree x := by
      have hxdegree : B.degree x + (if G.Adj x.val w then 1 else 0) = G.degree x.val := by
        convert deletion_degree G w x (hCE.degree_ge_three x.val) using 1
      have hv' : 4 ≤ G.degree x.val := by
        convert hv using 1
      have hxw : G.Adj x.val w := hwv.symm
      simp only [if_pos hxw] at hxdegree
      omega
    exact deletion_excluded G hCE hminimal c hc w hlow ⟨x, hxhigh⟩
  intro v
  have hvmin := hCE.degree_ge_three v
  by_contra hvthree
  have hvhigh : 4 ≤ G.degree v := by omega
  let s := Finset.univ.erase v
  let B := G.induce (s : Set V)
  have hretained : ∀ x : ↥(s : Set V), 3 ≤ B.degree x := by
    intro x
    have hxdegree : B.degree x + (if G.Adj x.val v then 1 else 0) = G.degree x.val := by
      convert deletion_degree G v x (hCE.degree_ge_three x.val) using 1
    have hxmin := hCE.degree_ge_three x.val
    by_cases h : G.Adj x.val v
    · have hxhigh : 4 ≤ G.degree x.val := by
        by_contra hnot
        have hxthree : G.degree x.val = 3 := by omega
        exact hnoMixed x.val v hxthree h hvhigh
      simp only [if_pos h] at hxdegree
      omega
    · simp only [if_neg h, Nat.add_zero] at hxdegree
      omega
  have hlow : (Finset.univ.filter (fun x : ↥(s : Set V) => B.degree x ≤ 2)).card ≤ 2 := by
    have hempty : Finset.univ.filter (fun x : ↥(s : Set V) => B.degree x ≤ 2) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxlow := (Finset.mem_filter.mp hx).2
      have hxhigh := hretained x
      omega
    simp [hempty]
  obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj v).mp (by omega : 0 < G.degree v)
  let x : ↥(s : Set V) := ⟨w, by simp [s, hvw.ne.symm]⟩
  exact deletion_excluded G hCE hminimal c hc v hlow ⟨x, hretained x⟩

/-- The existing lexicographically minimal counterexample interface implies global
vertex minimality among all finite graphs, so a proper Bool coloring conditionally
forces ordinary degree three everywhere. No existence or global closure follows. -/
theorem degree_eq_three_of_minimal {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hmin : IsMinimalCounterexample G)
    (c : V → Bool) (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y) :
    ∀ v, G.degree v = 3 := by
  classical
  apply degree_eq_three G hmin.isCounterexample ?_ c hc
  intro W _ _ Q horder hdegree
  by_contra hfree
  have hQ : IsCounterexample Q := ⟨inferInstance, hdegree, hfree⟩
  exact hmin.not_size_lexLt Q hQ (Or.inl horder)

end Erdos64.BipartiteMinimalCubic
