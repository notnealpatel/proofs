import Erdos.Erdos64.UniqueCubicClawCenterCycleSelection
import Erdos.Erdos64.UniqueCubicClawCenterPoleRootArms

set_option autoImplicit false

namespace Erdos64.UniqueCubicClawCenter

open SimpleGraph

universe u

/-- A selected set of ordinary third labels, together with the original center
at the pole, supplies precisely the geometric splice certificates. -/
theorem selected_third_splice_certificates {V : Type u} {v : V}
    {N : Type*} (z : N) {m : ℕ} (c : Fin (m + 1) → N) (hc : Function.Injective c)
    (a : Fin (m + 1) → {p : V // p ≠ v})
    (t : Finset (Fin (m + 1)))
    (ha : Set.InjOn a (t : Set (Fin (m + 1)))) [DecidableEq N] :
    let insert := fun i => if c i = z then some v else if i ∈ t then some (a i).val else none
    (∀ i, c i = z → insert i = some v) ∧
    (∀ i x, insert i = some x →
      (x = v ∧ c i = z) ∨ (i ∈ t ∧ x = (a i).val)) ∧
    (∀ i j x, insert i = some x → insert j = some x → i = j) := by
  dsimp only
  constructor
  · intro i hi
    simp [hi]
  · constructor
    · intro i x hix
      by_cases hi : c i = z
      · left
        exact ⟨(Option.some.inj (by simpa [hi] using hix)).symm, hi⟩
      · by_cases hit : i ∈ t
        · right
          exact ⟨hit, (Option.some.inj (by simpa [hi, hit] using hix)).symm⟩
        · simp [hi, hit] at hix
    · intro i j x hix hjx
      by_cases hi : c i = z
      · have hxv : x = v := (Option.some.inj (by simpa [hi] using hix)).symm
        by_cases hj : c j = z
        · exact hc (hi.trans hj.symm)
        · by_cases hjt : j ∈ t
          · have hxj : x = (a j).val := (Option.some.inj (by simpa [hj, hjt] using hjx)).symm
            exact False.elim ((a j).property (hxj.symm.trans hxv))
          · simp [hj, hjt] at hjx
      · by_cases hit : i ∈ t
        · have hxi : x = (a i).val := (Option.some.inj (by simpa [hi, hit] using hix)).symm
          by_cases hj : c j = z
          · have hxv : x = v := (Option.some.inj (by simpa [hj] using hjx)).symm
            exact False.elim ((a i).property (hxi.symm.trans hxv))
          · by_cases hjt : j ∈ t
            · have hxj : x = (a j).val := (Option.some.inj (by simpa [hj, hjt] using hjx)).symm
              exact ha hit hjt (Subtype.ext (hxi.symm.trans hxj))
            · simp [hj, hjt] at hjx
        · simp [hi, hit] at hix

example :
    let insert := fun i : Fin 1 => if i = 0 then some (0 : Fin 2)
      else if i ∈ (∅ : Finset (Fin 1)) then some (1 : Fin 2) else none
    (∀ i, i = 0 → insert i = some 0) ∧
    (∀ i x, insert i = some x →
      (x = 0 ∧ i = 0) ∨ (i ∈ (∅ : Finset (Fin 1)) ∧ x = 1)) ∧
    (∀ i j x, insert i = some x → insert j = some x → i = j) := by
  exact selected_third_splice_certificates (v := (0 : Fin 2)) (0 : Fin 1) id
    Function.injective_id (fun _ => ⟨1, by decide⟩) ∅ (by simp)

/-- Every dyadic indexed suppression cycle lifts to an ordinary original-graph
cycle of exactly twice its length, whether or not the pole lies on the cycle. -/
theorem indexed_dyadic_cycle_lifts {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    {v : V} [DecidableRel (completion G v).Adj]
    [DecidableRel (cliqueRoot (completion G v)).Adj]
    (hv : G.degree v = 3) (hclaw : Claw G v) (hunique : ∀ w, Claw G w → w = v)
    {z : RootNode (completion G v)} (hz : z.val = {p | G.Adj v p.val})
    (hz3 : (cliqueRoot (completion G v)).degree z = 3)
    (harms : ∀ D, (cliqueRoot (completion G v)).Adj z D →
      (cliqueRoot (completion G v)).degree D = 3)
    {m k : ℕ} (hk : 2 ≤ k) (hlen : m + 1 = 2 ^ k)
    (c : Fin (m + 1) → SuppressionNode (cliqueRoot (completion G v)))
    (hc : Function.Injective c) (P : ∀ i, RootCorridor (completion G v) (c i) (c (i + 1))) :
    ∃ a, ∃ p : G.Walk a a, p.IsCycle ∧ p.length = 2 * (m + 1) := by
  classical
  let R := completion G v
  have hD := completion_strongDiamondFree G hG hv
  have hcf := completion_claw_free G hunique
  have hmin := completion_min_degree G hG hv hclaw
  have hm : 3 ≤ m + 1 := by
    have hfour := CycleIndex.four_le_of_dyadic m k hlen hk
    omega
  obtain ⟨a, ha⟩ := exists_cycle_third_labels R hD hcf hmin hm c hc P
  let r := Finset.univ.filter (fun i => (c i).val ≠ z)
  let b := (Finset.univ.filter (fun i => (P i).first = (P i).last ∧
    (c i).val ≠ z ∧ (c (i + 1)).val ≠ z)).card
  let d := (Finset.univ.filter (fun i => (P i).first = (P i).last)).card
  let base := (List.ofFn (fun i => (P i).labels)).flatten.length
  have hbase : base + d = 2 * (m + 1) := by
    have hcount := CycleCount.length_add_card_singletons (fun i => (P i).labels)
      (fun i => (P i).length_labels)
    simpa only [RootCorridor.length_labels_eq_one_iff] using hcount
  have hsel := exists_cycle_nonpole_candidates G hG hHIGH hv hclaw hunique hz hm c hc P a
    (fun i => (ha i).1)
  have build (t : Finset (Fin (m + 1)))
      (hti : Set.InjOn a (t : Set (Fin (m + 1))))
      (hcount : base + (Finset.univ.filter (fun i =>
        (if (c i).val = z then some v else if i ∈ t then some (a i).val else none).isSome)).card =
        2 * (m + 1)) :
      ∃ x, ∃ p : G.Walk x x, p.IsCycle ∧ p.length = 2 * (m + 1) := by
    let insert := fun i => if (c i).val = z then some v else if i ∈ t then some (a i).val else none
    have hcval : Function.Injective (fun i => (c i).val) :=
      fun i j hij => hc (Subtype.ext hij)
    obtain ⟨hroot, hchoice, hinj⟩ := selected_third_splice_certificates z (fun i => (c i).val)
      hcval a t hti
    have hchoice' : ∀ i x, insert i = some x →
        (x = v ∧ (c i).val = z) ∨
        ∃ p : {p : V // p ≠ v}, x = p.val ∧ p ∈ (c i).val.val ∧
          p ≠ (P i).first ∧ p ≠ (P (i - 1)).last := by
      intro i x hix
      rcases hchoice i x hix with hrootx | ⟨hit, hxa⟩
      · exact Or.inl hrootx
      · exact Or.inr ⟨a i, hxa, (ha i).1, (ha i).2.1, (ha i).2.2.1⟩
    obtain ⟨x, p, hp, hplen⟩ := cycle_expansion_of_splices G hG hv hclaw hunique hz hz3
      hm c hc P insert hroot hchoice' hinj (by change 3 ≤ base + _; rw [hcount]; omega)
    exact ⟨x, p, hp, hplen.trans hcount⟩
  by_cases hhit : ∃ j, (c j).val = z
  · obtain ⟨j, hj⟩ := hhit
    have hrootiff (i : Fin (m + 1)) : (c i).val = z ↔ i = j := by
      constructor
      · intro hij
        exact hc (Subtype.ext (hij.trans hj.symm))
      · intro hij
        exact hij.symm ▸ hj
    have hr : r = Finset.univ.erase j := by
      ext i
      simp [r, hrootiff i]
    have hodd : Odd r.card := by
      rw [hr]
      exact CycleIndex.odd_card_erase_of_dyadic m k j hlen hk
    obtain ⟨t, ht, htcard, hti⟩ := hsel.2 hodd
    have hjnot : j ∉ t := by
      intro hjt
      exact (Finset.mem_filter.mp (ht hjt)).2 hj
    have hcnt : (Finset.univ.filter (fun i =>
        (if (c i).val = z then some v else if i ∈ t then some (a i).val else none).isSome)).card =
        t.card + 1 := by
      simpa only [hrootiff] using
        CycleCount.card_isSome_root_of_notMem j t hjnot v (fun i => (a i).val)
    have hd : d = b + 2 := cycle_pole_direct_count G harms hm c hc P j hj
    apply build t hti
    rw [hcnt, htcard]
    change base + (b + 1 + 1) = 2 * (m + 1)
    omega
  · have havoid (i : Fin (m + 1)) : (c i).val ≠ z :=
      fun hi => hhit ⟨i, hi⟩
    obtain ⟨t, ht, htcard, hti⟩ := hsel.1
    have hcnt : (Finset.univ.filter (fun i =>
        (if (c i).val = z then some v else if i ∈ t then some (a i).val else none).isSome)).card =
        t.card := by
      simpa only [havoid, if_false] using
        CycleCount.card_isSome_selected t (fun i => (a i).val)
    have hd : d = b := by
      change (Finset.univ.filter (fun i => (P i).first = (P i).last)).card =
        (Finset.univ.filter (fun i => (P i).first = (P i).last ∧
          (c i).val ≠ z ∧ (c (i + 1)).val ≠ z)).card
      congr 1
      ext i
      simp [havoid i, havoid (i + 1)]
    apply build t hti
    rw [hcnt, htcard]
    change base + b = 2 * (m + 1)
    omega

open scoped Classical in
/-- Any actual dyadic cycle of the suppressed graph yields an ordinary cycle
in the original graph of exactly twice its length. All indexing and corridor
witnesses are constructed internally; no pole-hit assumption is imposed. -/
theorem suppression_cycle_lifts {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    {v : V} (hv : G.degree v = 3) (hclaw : Claw G v) (hunique : ∀ w, Claw G w → w = v)
    {x : SuppressionNode (cliqueRoot (completion G v))}
    (p : (suppression (cliqueRoot (completion G v))).Walk x x) (hp : p.IsCycle)
    {k : ℕ} (hk : 2 ≤ k) (hlen : p.length = 2 ^ k) :
    ∃ y, ∃ q : G.Walk y y, q.IsCycle ∧ q.length = 2 * p.length := by
  classical
  let R := completion G v
  have hD := completion_strongDiamondFree G hG hv
  have hcf := completion_claw_free G hunique
  have hmin := completion_min_degree G hG hv hclaw
  obtain ⟨z, hz, hz3, harms⟩ := exists_pole_root_with_cubic_arms G hG hv hclaw hunique
  let m := 2 ^ k - 1
  have hpositive : 0 < 2 ^ k := pow_pos (by decide) k
  have hm : m + 1 = 2 ^ k := by dsimp only [m]; omega
  have hthree : 3 ≤ m + 1 := by
    have hfour := CycleIndex.four_le_of_dyadic m k hm hk
    omega
  obtain ⟨c, hc, hadj⟩ := exists_indexed_cycle _ p hp m (hlen.trans hm.symm) hthree
  let P (i : Fin (m + 1)) : RootCorridor R (c i) (c (i + 1)) :=
    Classical.choice (exists_rootCorridor R hD hcf hmin (hadj i))
  obtain ⟨y, q, hq, hqlen⟩ := indexed_dyadic_cycle_lifts G hG hHIGH hv hclaw hunique
    hz hz3 harms hk hm c hc P
  exact ⟨y, q, hq, hqlen.trans (congrArg (fun n => 2 * n) (hm.trans hlen.symm))⟩

end Erdos64.UniqueCubicClawCenter
