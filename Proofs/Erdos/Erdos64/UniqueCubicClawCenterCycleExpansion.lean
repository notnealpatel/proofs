import Erdos.Erdos64.UniqueCubicClawCenterCorridor
import Erdos.Erdos64.UniqueCubicClawCenterBlockInsertion

set_option autoImplicit false

namespace Erdos64.UniqueCubicClawCenter

open SimpleGraph

universe u

/-- An expanded corridor already forms an original-graph chain. A split's
middle root node has degree two, so it cannot be the cubic pole root. -/
theorem RootCorridor.old_chain {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) {v : V}
    [DecidableRel (completion G v).Adj] [DecidableRel (cliqueRoot (completion G v)).Adj]
    (hv : G.degree v = 3) {z : RootNode (completion G v)}
    (hz : z.val = {p | G.Adj v p.val}) (hz3 : (cliqueRoot (completion G v)).degree z = 3)
    {x y : SuppressionNode (cliqueRoot (completion G v))}
    (P : RootCorridor (completion G v) x y) :
    (P.labels.map Subtype.val).IsChain G.Adj := by
  classical
  unfold RootCorridor.labels
  split_ifs with heq
  · simp
  · have hsplit : P.near = P.far ∧ (cliqueRoot (completion G v)).degree P.near = 2 := by
      rcases P.route with hdir | hsplit
      · exact False.elim (heq hdir.2.2)
      · exact ⟨hsplit.1, hsplit.2.1⟩
    have hnearz : P.near ≠ z := by
      intro he
      have hn2 := hsplit.2
      rw [he, hz3] at hn2
      omega
    have hlast : P.last ∈ P.near.val := hsplit.1.symm ▸ P.last_far
    have hadj := completion_root_angle_old G hG hv hz hnearz P.first_near hlast heq
    simpa using hadj

/-- Non-pole direct corridors on an arbitrary retained cycle cannot be
consecutive. This matching condition uses independence in the original graph. -/
theorem cycle_nonpole_direct_not_consecutive {V : Type u} [Fintype V]
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
    (i : Fin (m + 1)) (hiz : (c i).val ≠ z) (hnextz : (c (i + 1)).val ≠ z)
    (hout : (P i).first = (P i).last) :
    ¬ ((c (i + 1 + 1)).val ≠ z ∧ (P (i + 1)).first = (P (i + 1)).last) := by
  intro hnext
  have direct (j : Fin (m + 1)) (hj : (P j).first = (P j).last) :
      (cliqueRoot (completion G v)).Adj (c j).val (c (j + 1)).val := by
    have hnear : (P j).near = (c (j + 1)).val := by
      rcases (P j).route with hdir | hsplit
      · exact hdir.1
      · exact False.elim (hsplit.2.2 hj)
    exact hnear ▸ (P j).start_edge
  have hedge := direct i hout
  have hnextedge := direct (i + 1) hnext.2
  have heq := nonpole_direct_neighbors_unique G hG hHIGH hv hclaw hunique hz
    hnextz hiz hnext.1 (c (i + 1)).property (c i).property (c (i + 1 + 1)).property
    hedge.symm hnextedge
  have heqindex : i = i + 1 + 1 := hc (Subtype.ext heq)
  exact CycleIndex.succ_succ_ne m hm i heqindex.symm

/-- A cubic pole root forces every incident corridor to be direct: its arms
have degree three, excluding the degree-two middle of a split corridor. -/
theorem RootCorridor.pole_direct {V : Type u} [Fintype V] (G : SimpleGraph V)
    {v : V} [DecidableRel (cliqueRoot (completion G v)).Adj]
    {z : RootNode (completion G v)}
    (harms : ∀ D, (cliqueRoot (completion G v)).Adj z D →
      (cliqueRoot (completion G v)).degree D = 3)
    {x y : SuppressionNode (cliqueRoot (completion G v))}
    (P : RootCorridor (completion G v) x y) (hpole : x.val = z ∨ y.val = z) :
    P.first = P.last := by
  rcases P.route with hdir | hsplit
  · exact hdir.2.2
  · rcases hpole with hx | hy
    · have hnear3 := harms P.near (hx ▸ P.start_edge)
      omega
    · have hfar3 := harms P.far (hy ▸ P.finish_edge)
      have hfar2 : (cliqueRoot (completion G v)).degree P.far = 2 :=
        hsplit.1 ▸ hsplit.2.1
      omega

/-- Prepending the third label at an ordinary retained node makes an
original-graph chain; the pole node is handled instead by the original center. -/
theorem RootCorridor.old_prepend {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) {v : V}
    [DecidableRel (completion G v).Adj] [DecidableRel (cliqueRoot (completion G v)).Adj]
    (hv : G.degree v = 3) {z : RootNode (completion G v)}
    (hz : z.val = {p | G.Adj v p.val}) (hz3 : (cliqueRoot (completion G v)).degree z = 3)
    {x y : SuppressionNode (cliqueRoot (completion G v))}
    (P : RootCorridor (completion G v) x y) (hxz : x.val ≠ z)
    {a : {p : V // p ≠ v}} (ha : a ∈ x.val.val) (hane : a ≠ P.first) :
    (a.val :: P.labels.map Subtype.val).IsChain G.Adj := by
  apply List.isChain_cons.mpr
  constructor
  · intro b hb
    have heq : b = P.first.val := by
      symm
      simpa only [List.head?_map, P.head_labels, Option.map_some, Option.mem_some] using hb
    rw [heq]
    exact completion_root_angle_old G hG hv hz hxz ha P.first_start hane
  · exact P.old_chain G hG hv hz hz3

/-- Geometrically valid optional third-label splices, with the original center
at a used pole angle, yield an actual original-graph cycle. The only remaining
numerical obligation is the desired count of selected splices. -/
theorem cycle_expansion_of_splices {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) {v : V}
    [DecidableRel (completion G v).Adj] [DecidableRel (cliqueRoot (completion G v)).Adj]
    (hv : G.degree v = 3) (hclaw : Claw G v) (hunique : ∀ w, Claw G w → w = v)
    {z : RootNode (completion G v)} (hz : z.val = {p | G.Adj v p.val})
    (hz3 : (cliqueRoot (completion G v)).degree z = 3)
    {m : ℕ} (hm : 3 ≤ m + 1)
    (c : Fin (m + 1) → SuppressionNode (cliqueRoot (completion G v)))
    (hc : Function.Injective c) (P : ∀ i, RootCorridor (completion G v) (c i) (c (i + 1)))
    (insert : Fin (m + 1) → Option V)
    (hroot : ∀ i, (c i).val = z → insert i = some v)
    (hchoice : ∀ i x, insert i = some x →
      (x = v ∧ (c i).val = z) ∨
      ∃ p : {a : V // a ≠ v}, x = p.val ∧ p ∈ (c i).val.val ∧
        p ≠ (P i).first ∧ p ≠ (P (i - 1)).last)
    (hinj : ∀ i j x, insert i = some x → insert j = some x → i = j)
    (hsize : 3 ≤ (List.ofFn (fun i => (P i).labels)).flatten.length +
      (Finset.univ.filter (fun i => (insert i).isSome)).card) :
    ∃ a, ∃ p : G.Walk a a, p.IsCycle ∧ p.length =
      (List.ofFn (fun i => (P i).labels)).flatten.length +
        (Finset.univ.filter (fun i => (insert i).isSome)).card := by
  classical
  let R := completion G v
  have hD : StrongDiamondFree R := completion_strongDiamondFree G hG hv
  have hcf : ∀ p, ¬ Claw R p := completion_claw_free G hunique
  have hmin : ∀ p, 3 ≤ R.degree p := completion_min_degree G hG hv hclaw
  let blocks := fun i => (P i).labels.map Subtype.val
  have hmap : (List.ofFn blocks).flatten =
      ((List.ofFn (fun i => (P i).labels)).flatten).map Subtype.val := by
    simp [blocks, List.map_flatten, List.map_ofFn, Function.comp_def]
  have hne : ∀ i, blocks i ≠ [] := by
    intro i hi
    exact (P i).labels_ne_nil (List.map_eq_nil_iff.mp hi)
  have hbase : (List.ofFn blocks).flatten.Nodup := by
    rw [hmap]
    exact (cycle_corridor_base_nodup R hD hcf hmin hm c hc P).map Subtype.coe_injective
  have hfresh : ∀ i x, insert i = some x → x ∉ (List.ofFn blocks).flatten := by
    intro i x hi hx
    rw [hmap] at hx
    obtain ⟨q, hq, hqx⟩ := List.mem_map.mp hx
    rcases hchoice i x hi with ⟨hxv, hiz⟩ | ⟨p, hxp, hp, hpout, hpin⟩
    · exact q.property (hqx.trans hxv)
    · have hqp : q = p := Subtype.ext (hqx.trans hxp)
      rw [hqp] at hq
      exact cycle_third_label_fresh R hD hcf hmin c hc P hp hpout hpin hq
  have hhead (i : Fin (m + 1)) : (blocks i).head? = some (P i).first.val := by
    simp only [blocks, List.head?_map, (P i).head_labels, Option.map_some]
  have hlast (i : Fin (m + 1)) :
      ((insert i).toList ++ blocks i).getLast? = some (P i).last.val := by
    rw [List.getLast?_append_of_ne_nil _ (hne i)]
    simp only [blocks, List.getLast?_map, (P i).getLast_labels, Option.map_some]
  have hlocal : ∀ i, ((insert i).toList ++ blocks i).IsChain G.Adj := by
    intro i
    cases hi : insert i with
    | none => simpa only [hi, Option.toList_none, List.nil_append] using (P i).old_chain G hG hv hz hz3
    | some x =>
      rcases hchoice i x hi with ⟨hxv, hiz⟩ | ⟨p, hxp, hp, hpout, hpin⟩
      · subst x
        apply List.isChain_cons.mpr
        constructor
        · intro b hb
          change b ∈ (blocks i).head? at hb
          have hbval : b = (P i).first.val := by
            symm
            simpa only [List.nil_append, hhead i, Option.mem_some] using hb
          rw [hbval]
          have hfirst := (P i).first_start
          rw [hiz, hz] at hfirst
          exact hfirst
        · exact (P i).old_chain G hG hv hz hz3
      · have hiz : (c i).val ≠ z := by
          intro he
          have hiv := hroot i he
          have hxv : x = v := Option.some.inj (hi.symm.trans hiv)
          exact p.property (hxp.symm.trans hxv)
        simpa only [hi, Option.toList_some, List.singleton_append, hxp] using
          (P i).old_prepend G hG hv hz hz3 hiz hp hpout
  have hboundary : ∀ i a, a ∈ ((insert i).toList ++ blocks i).getLast? →
      ∀ b, b ∈ ((insert (i + 1)).toList ++ blocks (i + 1)).head? → G.Adj a b := by
    intro i a ha b hb
    have haval : a = (P i).last.val := by
      symm
      simpa only [hlast i, Option.mem_some] using ha
    rw [haval]
    cases hi : insert (i + 1) with
    | none =>
      have hiz : (c (i + 1)).val ≠ z := by
        intro he
        have hisome := hroot (i + 1) he
        rw [hi] at hisome
        contradiction
      have hbval : b = (P (i + 1)).first.val := by
        symm
        simpa only [hi, Option.toList_none, List.nil_append, hhead (i + 1), Option.mem_some] using hb
      rw [hbval]
      have hangle : (P i).last ≠ (P (i + 1)).first := by
        have hangle' := (cycle_angle_labels_ne R hD hcf hmin hm c hc P (i + 1)).symm
        have hprev : i + 1 - 1 = i := add_sub_cancel_right i 1
        rw [hprev] at hangle'
        exact hangle'
      exact completion_root_angle_old G hG hv hz hiz (P i).last_finish (P (i + 1)).first_start hangle
    | some x =>
      have hbval : b = x := by
        symm
        simpa only [hi, Option.toList_some, List.singleton_append, List.head?_cons, Option.mem_some] using hb
      rw [hbval]
      rcases hchoice (i + 1) x hi with ⟨hxv, hiz⟩ | ⟨p, hxp, hp, hpout, hpin⟩
      · rw [hxv]
        have hlastmem := (P i).last_finish
        rw [hiz, hz] at hlastmem
        exact hlastmem.symm
      · have hiz : (c (i + 1)).val ≠ z := by
          intro he
          have hiv := hroot (i + 1) he
          have hxv : x = v := Option.some.inj (hi.symm.trans hiv)
          exact p.property (hxp.symm.trans hxv)
        rw [hxp]
        have hne : (P i).last ≠ p := by
          have hprev : i + 1 - 1 = i := add_sub_cancel_right i 1
          rw [hprev] at hpin
          exact hpin.symm
        exact completion_root_angle_old G hG hv hz hiz (P i).last_finish hp hne
  obtain ⟨hfinal, hnodup, hlength, hchain⟩ :=
    BlockInsertion.certificates G blocks insert hne hbase hfresh hinj hlocal hboundary
  have hfinalsize : 3 ≤ (List.ofFn (fun i => (insert i).toList ++ blocks i)).flatten.length := by
    rw [hlength]
    simpa only [hmap, List.length_map] using hsize
  obtain ⟨a, p, hp, hplen⟩ := exists_cycle_of_nodup_list G _ hfinal hnodup hfinalsize hchain
  refine ⟨a, p, hp, ?_⟩
  rw [hplen, hlength, hmap, List.length_map]

end Erdos64.UniqueCubicClawCenter
