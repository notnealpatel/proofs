import Erdos.Erdos64.UniqueCubicClawCenterCycleExpansion
import Erdos.Erdos64.UniqueCubicClawCenterCycleCount

set_option autoImplicit false

namespace Erdos64.UniqueCubicClawCenter

open SimpleGraph

universe u

/-- Used direct corridors avoiding the pole root form a matching on the
ordinary cycle nodes. This is derived from original high-degree independence. -/
theorem cycle_nonpole_direct_matching_bound {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    {v : V} [DecidableRel (completion G v).Adj]
    [DecidableRel (cliqueRoot (completion G v)).Adj]
    (hv : G.degree v = 3) (hclaw : Claw G v) (hunique : ∀ w, Claw G w → w = v)
    {z : RootNode (completion G v)} (hz : z.val = {p | G.Adj v p.val})
    {m : ℕ} (hm : 3 ≤ m + 1)
    (c : Fin (m + 1) → SuppressionNode (cliqueRoot (completion G v)))
    (hc : Function.Injective c)
    (P : ∀ i, RootCorridor (completion G v) (c i) (c (i + 1)))
    [DecidableEq (RootNode (completion G v))] [DecidableEq V] :
    2 * (Finset.univ.filter (fun i => (P i).first = (P i).last ∧
      (c i).val ≠ z ∧ (c (i + 1)).val ≠ z)).card ≤
      (Finset.univ.filter (fun i => (c i).val ≠ z)).card := by
  apply cycle_matching_endpoint_bound _ _ (fun i => i + 1) (CycleIndex.succ_injective m)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.2.1
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.2.2
  · intro i hi hnext
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hnext
    exact cycle_nonpole_direct_not_consecutive G hG hHIGH hv hclaw hunique hz hm c hc P i
      hi.2.1 hi.2.2 hi.1 ⟨hnext.2.2, hnext.1⟩

/-- The matching and incidence counts construct enough distinct ordinary
third-label representatives, with one additional representative when the
ordinary-node count is odd (the pole-hit case of an even cycle). -/
theorem exists_cycle_nonpole_candidates {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    {v : V} [DecidableRel (completion G v).Adj]
    [DecidableRel (cliqueRoot (completion G v)).Adj]
    (hv : G.degree v = 3) (hclaw : Claw G v) (hunique : ∀ w, Claw G w → w = v)
    {z : RootNode (completion G v)} (hz : z.val = {p | G.Adj v p.val})
    {m : ℕ} (hm : 3 ≤ m + 1)
    (c : Fin (m + 1) → SuppressionNode (cliqueRoot (completion G v)))
    (hc : Function.Injective c)
    (P : ∀ i, RootCorridor (completion G v) (c i) (c (i + 1)))
    (a : Fin (m + 1) → {p : V // p ≠ v}) (ha : ∀ i, a i ∈ (c i).val.val)
    [DecidableEq (RootNode (completion G v))] [DecidableEq V] :
    let r := Finset.univ.filter (fun i => (c i).val ≠ z)
    let b := (Finset.univ.filter (fun i => (P i).first = (P i).last ∧
      (c i).val ≠ z ∧ (c (i + 1)).val ≠ z)).card
    (∃ t ⊆ r, t.card = b ∧ Set.InjOn a (t : Set (Fin (m + 1)))) ∧
    (Odd r.card → ∃ t ⊆ r, t.card = b + 1 ∧ Set.InjOn a (t : Set (Fin (m + 1)))) := by
  dsimp only
  let r := Finset.univ.filter (fun i => (c i).val ≠ z)
  let b := (Finset.univ.filter (fun i => (P i).first = (P i).last ∧
    (c i).val ≠ z ∧ (c (i + 1)).val ≠ z)).card
  have hcval : Function.Injective (fun i => (c i).val) := by
    intro i j hij
    exact hc (Subtype.ext hij)
  have hcount := cycle_candidate_image_bound (completion G v)
    (completion_strongDiamondFree G hG hv) (completion_claw_free G hunique)
    (completion_min_degree G hG hv hclaw) (fun i => (c i).val) hcval a ha r
  have hbudget : 2 * b ≤ r.card :=
    cycle_nonpole_direct_matching_bound G hG hHIGH hv hclaw hunique hz hm c hc P
  constructor
  · apply cycle_lift_exists_injective_subset r a b
    omega
  · rintro ⟨k, hk⟩
    have hoddcount : r.card = 2 * k + 1 := hk
    apply cycle_lift_exists_injective_subset r a (b + 1)
    omega

/-- If a retained cycle hits the pole root at index `j`, precisely its two
incident corridors are the direct corridors omitted from the ordinary matching. -/
theorem cycle_pole_direct_count {V : Type u} [Fintype V] (G : SimpleGraph V)
    {v : V} [DecidableRel (cliqueRoot (completion G v)).Adj]
    {z : RootNode (completion G v)}
    (harms : ∀ D, (cliqueRoot (completion G v)).Adj z D →
      (cliqueRoot (completion G v)).degree D = 3)
    {m : ℕ} (hm : 3 ≤ m + 1)
    (c : Fin (m + 1) → SuppressionNode (cliqueRoot (completion G v)))
    (hc : Function.Injective c) (P : ∀ i, RootCorridor (completion G v) (c i) (c (i + 1)))
    (j : Fin (m + 1)) (hj : (c j).val = z)
    [DecidableEq (RootNode (completion G v))] [DecidableEq V] :
    (Finset.univ.filter (fun i => (P i).first = (P i).last)).card =
      (Finset.univ.filter (fun i => (P i).first = (P i).last ∧
        (c i).val ≠ z ∧ (c (i + 1)).val ≠ z)).card + 2 := by
  let s := Finset.univ.filter (fun i => (P i).first = (P i).last ∧
    (c i).val ≠ z ∧ (c (i + 1)).val ≠ z)
  have hrootiff (i : Fin (m + 1)) : (c i).val = z ↔ i = j := by
    constructor
    · intro he
      exact hc (Subtype.ext (he.trans hj.symm))
    · intro he
      exact he.symm ▸ hj
  have hnextiff (i : Fin (m + 1)) : (c (i + 1)).val = z ↔ i = j - 1 := by
    rw [hrootiff]
    constructor
    · intro he
      have hprev : i + 1 - 1 = i := add_sub_cancel_right i 1
      have hsub := congrArg (fun k : Fin (m + 1) => k - 1) he
      simpa only [hprev] using hsub
    · intro he
      have hprev : (j - 1) + 1 = j := sub_add_cancel j 1
      rw [he, hprev]
  have hjpred : j ≠ j - 1 := by
    intro he
    have hprev : (j - 1) + 1 = j := sub_add_cancel j 1
    rw [← he] at hprev
    exact CycleIndex.succ_ne m (by omega) j hprev
  have hdj : (P j).first = (P j).last := (P j).pole_direct G harms (Or.inl hj)
  have hdpred : (P (j - 1)).first = (P (j - 1)).last :=
    (P (j - 1)).pole_direct G harms (Or.inr ((hnextiff (j - 1)).mpr rfl))
  have hset : Finset.univ.filter (fun i => (P i).first = (P i).last) = s ∪ {j, j - 1} := by
    ext i
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton]
    by_cases hij : i = j
    · subst i
      simp [hdj]
    · by_cases hipred : i = j - 1
      · subst i
        simp [hdpred]
      · simp [hij, hipred, hrootiff i, hnextiff i]
  have hdisj : Disjoint s {j, j - 1} := by
    apply Finset.disjoint_left.mpr
    intro i hi hpair
    have his := (Finset.mem_filter.mp hi).2
    rcases Finset.mem_insert.mp hpair with hij | hipred
    · exact his.2.1 ((hrootiff i).mpr hij)
    · exact his.2.2 ((hnextiff i).mpr (Finset.mem_singleton.mp hipred))
  rw [hset, Finset.card_union_of_disjoint hdisj]
  simp only [Finset.card_pair hjpred]
  rfl

end Erdos64.UniqueCubicClawCenter
