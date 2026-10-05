import Erdos.Erdos64.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

set_option autoImplicit false

/-!
This module proves only a conditional, non-bipartite constraint. Deleting a cubic
vertex and completing its neighborhood preserves minimum degree because a
counterexample has no C4. In a dyadic repair cycle, no new edge would give an
original dyadic cycle; a new edge followed by one further new end edge also gives
an original dyadic cycle. The remaining case lifts with length increased by one,
not with the same length.

No model of the full counterexample/minimality hypotheses is exhibited: their
joint satisfiability is not asserted. The examples below check only the retained
vertex and repair definitions, not existence of a counterexample.
-/

namespace Erdos64.MinimalCubicOddSuccessor
open SimpleGraph
open scoped Classical
universe u

private abbrev Vertex {V : Type*} (v : V) := {x : V // x ≠ v}

example : Fintype.card (Vertex (0 : Fin 2)) = 1 := by decide

/-- The induced graph off `v`, with all distinct neighbors of `v` joined. -/
private def repairGraph {V : Type*} (G : SimpleGraph V) (v : V) :
    SimpleGraph (Vertex v) where
  Adj x y := G.Adj x.val y.val ∨ (x ≠ y ∧ G.Adj v x.val ∧ G.Adj v y.val)
  symm := ⟨by
    intro x y h
    rcases h with h | ⟨hne, hx, hy⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨hne.symm, hy, hx⟩⟩
  loopless := ⟨by intro x h; rcases h with h | h; exact h.ne rfl; exact h.1 rfl⟩

example : (repairGraph (⊥ : SimpleGraph (Fin 2)) 0) = ⊥ := by
  ext x y
  simp [repairGraph]

example : (repairGraph
    (fromRel (fun x y : Fin 3 => x = 0 ∧ y ≠ 0)) 0).Adj
    ⟨1, by decide⟩ ⟨2, by decide⟩ := by
  simp [repairGraph, fromRel]

private theorem four_neighbors {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (v : V) (hd : G.degree v = 3) (a b d e : V)
    (ha : G.Adj v a) (hb : G.Adj v b) (hd' : G.Adj v d) (he : G.Adj v e)
    (hab : a ≠ b) (had : a ≠ d) (hae : a ≠ e)
    (hbd : b ≠ d) (hbe : b ≠ e) (hde : d ≠ e) : False := by
  classical
  have hs : ({a,b,d,e} : Finset V) ⊆ G.neighborFinset v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simpa
  have hn : ({a,b,d,e} : Finset V).card = 4 := by
    simp [hab, had, hae, hbd, hbe, hde]
  have hle := Finset.card_le_card hs
  rw [hn, card_neighborFinset_eq_degree, hd] at hle
  omega


private theorem lift_old {V : Type*} (G : SimpleGraph V) (v : V)
    {x y : Vertex v} (w : (repairGraph G v).Walk x y)
    (hold : ∀ i, i < w.length → G.Adj (w.getVert i).val (w.getVert (i + 1)).val) :
    ∃ r : G.Walk x.val y.val, r.length = w.length ∧
      r.support = w.support.map Subtype.val := by
  induction w with
  | nil => exact ⟨.nil, rfl, rfl⟩
  | @cons x z y h w ih =>
    have hfirst : G.Adj x.val z.val := by simpa using hold 0 (by simp)
    have hrest : ∀ i, i < w.length → G.Adj (w.getVert i).val (w.getVert (i + 1)).val := by
      intro i hi
      simpa using hold (i + 1) (by simp only [Walk.length_cons]; omega)
    obtain ⟨r, hlen, hs⟩ := ih hrest
    exact ⟨.cons hfirst r, by simp [hlen], by simp [hs]⟩

/- A new internal edge of an injective path between neighbors of `v` would
produce four distinct neighbors of `v`. Thus every new edge is an end edge. -/
private theorem path_new_edge_end {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (v : V) (hd : G.degree v = 3) {x y : Vertex v}
    (w : (repairGraph G v).Walk x y) (hw : w.IsPath)
    (hx : G.Adj v x.val) (hy : G.Adj v y.val)
    {i : ℕ} (hi : i < w.length)
    (hnew : ¬ G.Adj (w.getVert i).val (w.getVert (i + 1)).val) :
    i = 0 ∨ i + 1 = w.length := by
  have hedge := w.adj_getVert_succ hi
  obtain ⟨_, ha, hb⟩ := hedge.resolve_left hnew
  by_contra hend
  have hi0 : 0 < i := by omega
  have hil : i + 1 < w.length := by omega
  have hinj : ∀ j k, j ≤ w.length → k ≤ w.length → j ≠ k →
      (w.getVert j).val ≠ (w.getVert k).val := by
    intro j k hj hk hne heq
    exact hne (hw.getVert_injOn hj hk (Subtype.ext heq))
  apply four_neighbors G v hd (w.getVert 0).val (w.getVert i).val
    (w.getVert (i + 1)).val (w.getVert w.length).val (by simpa using hx) ha hb
    (by simpa using hy)
  all_goals apply hinj <;> omega


private theorem lift_two_first {V : Type*} (G : SimpleGraph V) (v : V)
    {a b d : Vertex v} (hab : (repairGraph G v).Adj a b)
    (hbd : (repairGraph G v).Adj b d) (r : (repairGraph G v).Walk d a)
    (hw : (Walk.cons hab (Walk.cons hbd r)).IsCycle)
    (ha : G.Adj v a.val) (hd : G.Adj v d.val)
    (hold : ∀ i, i < r.length → G.Adj (r.getVert i).val (r.getVert (i + 1)).val) :
    ∃ z, ∃ t : G.Walk z z, t.IsCycle ∧ t.length = (Walk.cons hab (Walk.cons hbd r)).length := by
  obtain ⟨s, hslen, hss⟩ := lift_old G v r hold
  have hs : s.IsPath := by
    apply (Walk.isPath_def _).mpr
    rw [hss]
    exact hw.isPath_tail.of_cons.support_nodup.map Subtype.val_injective
  have hv : v ∉ s.support := by
    rw [hss]
    intro hmem
    obtain ⟨x, _, he⟩ := List.mem_map.mp hmem
    exact x.property he
  let t : G.Walk a.val a.val := .cons ha.symm (.cons hd s)
  have htpath : (Walk.cons hd s).IsPath := by
    rw [Walk.cons_isPath_iff]
    exact ⟨hs, hv⟩
  refine ⟨a.val, t, Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨htpath, ?_⟩, ?_⟩
  · have hthree := hw.three_le_length
    simpa [t, hslen] using hthree
  · simp [t, hslen]

private theorem lift_path_first {V : Type*} (G : SimpleGraph V) (v : V)
    {x y : Vertex v} (hclose : (repairGraph G v).Adj y x)
    (w : (repairGraph G v).Walk x y) (hw : w.IsPath)
    (hlen : 3 ≤ w.length) (hy : G.Adj v y.val)
    (hnew : ¬ G.Adj (w.getVert 0).val (w.getVert 1).val)
    (hold : ∀ i, i < w.length → i ≠ 0 → G.Adj (w.getVert i).val (w.getVert (i + 1)).val) :
    ∃ z, ∃ t : G.Walk z z, t.IsCycle ∧ t.length = w.length + 1 := by
  cases w with
  | nil => simp at hlen
  | @cons x d y h r =>
    have hd : G.Adj v d.val := ((h.resolve_left (by simpa using hnew)).2.2)
    have hcycle : (Walk.cons hclose (Walk.cons h r)).IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      exact ⟨hw, by simp only [Walk.length_cons] at hlen ⊢; omega⟩
    have hr : ∀ i, i < r.length → G.Adj (r.getVert i).val (r.getVert (i + 1)).val := by
      intro i hi
      simpa using hold (i + 1) (by simp only [Walk.length_cons]; omega) (by omega)
    obtain ⟨z, t, ht, htl⟩ := lift_two_first G v hclose h r hcycle hy hd hr
    exact ⟨z, t, ht, by simpa using htl⟩


private theorem lift_cycle_old {V : Type*} (G : SimpleGraph V) (v : V)
    {a : Vertex v} (w : (repairGraph G v).Walk a a) (hw : w.IsCycle)
    (hold : ∀ i, i < w.length → G.Adj (w.getVert i).val (w.getVert (i + 1)).val) :
    ∃ z, ∃ t : G.Walk z z, t.IsCycle ∧ t.length = w.length := by
  cases w with
  | nil => exact False.elim (Walk.not_isCycle_nil hw)
  | @cons a b a h r =>
    have hab : G.Adj a.val b.val := by simpa using hold 0 (by simp)
    have hr : ∀ i, i < r.length → G.Adj (r.getVert i).val (r.getVert (i + 1)).val := by
      intro i hi
      simpa using hold (i + 1) (by simp only [Walk.length_cons]; omega)
    obtain ⟨s, hslen, hss⟩ := lift_old G v r hr
    have hs : s.IsPath := by
      apply (Walk.isPath_def _).mpr
      rw [hss]
      exact (show r.IsPath from by simpa using hw.isPath_tail).support_nodup.map Subtype.val_injective
    refine ⟨a.val, .cons hab s, Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨by simpa using hs, ?_⟩, ?_⟩
    · simpa [hslen] using hw.three_le_length
    · simp [hslen]

private theorem path_at_most_one_new {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (v : V) (hd : G.degree v = 3) {x y : Vertex v}
    (w : (repairGraph G v).Walk x y) (hw : w.IsPath)
    (hx : G.Adj v x.val) (hy : G.Adj v y.val) (hlen : 3 ≤ w.length)
    {i : ℕ} (hi : i < w.length)
    (hnew : ¬ G.Adj (w.getVert i).val (w.getVert (i + 1)).val) :
    ∀ j, j < w.length → j ≠ i → G.Adj (w.getVert j).val (w.getVert (j + 1)).val := by
  intro j hj hji
  by_contra hnewj
  have hend := path_new_edge_end G v hd w hw hx hy hi hnew
  have hendj := path_new_edge_end G v hd w hw hx hy hj hnewj
  have ha := (w.adj_getVert_succ hi).resolve_left hnew
  have hb := (w.adj_getVert_succ hj).resolve_left hnewj
  have hinj : ∀ a b, a ≤ w.length → b ≤ w.length → a ≠ b →
      (w.getVert a).val ≠ (w.getVert b).val := by
    intro a b ha hb hab he
    exact hab (hw.getVert_injOn ha hb (Subtype.ext he))
  apply four_neighbors G v hd (w.getVert i).val (w.getVert (i + 1)).val
    (w.getVert j).val (w.getVert (j + 1)).val ha.2.1 ha.2.2 hb.2.1 hb.2.2
  all_goals apply hinj <;> omega

private theorem lift_path_new {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (v : V) (hd : G.degree v = 3) {x y : Vertex v}
    (hclose : (repairGraph G v).Adj y x) (w : (repairGraph G v).Walk x y)
    (hw : w.IsPath) (hx : G.Adj v x.val) (hy : G.Adj v y.val)
    (hlen : 3 ≤ w.length) {i : ℕ} (hi : i < w.length)
    (hnew : ¬ G.Adj (w.getVert i).val (w.getVert (i + 1)).val) :
    ∃ z, ∃ t : G.Walk z z, t.IsCycle ∧ t.length = w.length + 1 := by
  have hend := path_new_edge_end G v hd w hw hx hy hi hnew
  have hold := path_at_most_one_new G v hd w hw hx hy hlen hi hnew
  rcases hend with hi0 | hil
  · subst i
    exact lift_path_first G v hclose w hw hlen hy hnew hold
  · have hnew' : ¬ G.Adj (w.reverse.getVert 0).val (w.reverse.getVert 1).val := by
      simp only [Walk.getVert_reverse, Nat.sub_zero, Walk.getVert_length]
      intro he
      apply hnew
      have heq : w.length - 1 = i := by omega
      rw [← heq]
      rw [show w.length - 1 + 1 = w.length by omega, Walk.getVert_length]
      exact he.symm
    have hold' : ∀ j, j < w.reverse.length → j ≠ 0 →
        G.Adj (w.reverse.getVert j).val (w.reverse.getVert (j + 1)).val := by
      intro j hj hj0
      simp only [Walk.length_reverse] at hj
      have hk : w.length - (j + 1) < w.length := by omega
      have hki : w.length - (j + 1) ≠ i := by omega
      have he := hold (w.length - (j + 1)) hk hki
      have heq : w.length - (j + 1) + 1 = w.length - j := by omega
      simpa only [Walk.getVert_reverse, heq] using he.symm
    obtain ⟨z,t,ht,htl⟩ := lift_path_first G v hclose.symm w.reverse hw.reverse
      (by simpa using hlen) hx hnew' hold'
    exact ⟨z,t,ht, by simpa using htl⟩

private theorem close_old_path {V : Type*} (G : SimpleGraph V) (v : V)
    {x y : Vertex v} (w : (repairGraph G v).Walk x y) (hw : w.IsPath)
    (hx : G.Adj v x.val) (hy : G.Adj v y.val) (hlen : 3 ≤ w.length)
    (hold : ∀ i, i < w.length → G.Adj (w.getVert i).val (w.getVert (i + 1)).val) :
    ∃ t : G.Walk v v, t.IsCycle ∧ t.length = w.length + 2 := by
  obtain ⟨s, hslen, hss⟩ := lift_old G v w hold
  have hs : s.IsPath := by
    apply (Walk.isPath_def _).mpr
    rw [hss]
    exact hw.support_nodup.map Subtype.val_injective
  have hv : v ∉ s.support := by
    rw [hss]
    intro hmem
    obtain ⟨x, _, he⟩ := List.mem_map.mp hmem
    exact x.property he
  let r := (Walk.cons hy s.reverse).reverse
  have hr : r.IsPath := by
    apply Walk.IsPath.reverse
    rw [Walk.cons_isPath_iff]
    exact ⟨hs.reverse, by simpa using hv⟩
  let t : G.Walk v v := .cons hx r
  refine ⟨t, Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨by simpa [t] using hr, ?_⟩, ?_⟩
  · simp only [t, r, Walk.length_cons, Walk.length_reverse, hslen]
    omega
  · simp [t, r, hslen]

private theorem successor_first {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) (v : V) (hd : G.degree v = 3)
    {a : Vertex v} (w : (repairGraph G v).Walk a a) (hw : w.IsCycle)
    {k : ℕ} (hk : 2 ≤ k) (hlen : w.length = 2^k)
    (hnew : ¬ G.Adj a.val w.snd.val) :
    ∃ t : G.Walk v v, t.IsCycle ∧ t.length = 2^k + 1 := by
  cases w with
  | nil => exact False.elim (Walk.not_isCycle_nil hw)
  | @cons a b a h r =>
    have hn : ¬ G.Adj a.val b.val := by simpa using hnew
    obtain ⟨_, ha, hb⟩ := h.resolve_left hn
    have hpow : 4 ≤ 2^k := by
      calc
        4 = 2^2 := by decide
        _ ≤ 2^k := Nat.pow_le_pow_right (by decide) hk
    have hrlen : 3 ≤ r.length := by simp only [Walk.length_cons] at hlen; omega
    have hrpath : r.IsPath := by simpa using hw.isPath_tail
    by_cases hold : ∀ i, i < r.length → G.Adj (r.getVert i).val (r.getVert (i + 1)).val
    · obtain ⟨t, ht, htl⟩ := close_old_path G v r hrpath hb ha hrlen hold
      exact ⟨t, ht, by simp only [Walk.length_cons] at hlen; omega⟩
    · push Not at hold
      obtain ⟨i, hi, hnewi⟩ := hold
      obtain ⟨z,t,ht,htl⟩ := lift_path_new G v hd h r hrpath hb ha hrlen hi hnewi
      exact False.elim (hG.not_hasPowerOfTwoCycle ⟨k,hk,z,t,ht,by simpa using htl.trans hlen⟩)

private theorem successor_cycle {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) (v : V) (hd : G.degree v = 3)
    {k : ℕ} (hk : 2 ≤ k)
    (hcycle : ∃ a, ∃ w : (repairGraph G v).Walk a a, w.IsCycle ∧ w.length = 2^k) :
    ∃ t : G.Walk v v, t.IsCycle ∧ t.length = 2^k + 1 := by
  classical
  obtain ⟨a,w,hw,hlen⟩ := hcycle
  by_cases hold : ∀ i, i < w.length → G.Adj (w.getVert i).val (w.getVert (i + 1)).val
  · obtain ⟨z,t,ht,htl⟩ := lift_cycle_old G v w hw hold
    exact False.elim (hG.not_hasPowerOfTwoCycle ⟨k,hk,z,t,ht,htl.trans hlen⟩)
  · push Not at hold
    obtain ⟨i,hi,hnew⟩ := hold
    let x := w.getVert i
    let y := w.getVert (i + 1)
    have hmem : s(x,y) ∈ w.edges := (w.mk_mem_edges_iff_exists).mpr ⟨i,hi,rfl⟩
    have hx : x ∈ w.support := w.getVert_mem_support i
    let r := w.rotate x hx
    have hr : r.IsCycle := hw.rotate hx
    have hrlen : r.length = 2^k := by simp [r, hlen]
    have hed : s(x,y) ∈ r.edges := ((w.rotate_edges x hx).perm.mem_iff).mpr hmem
    have hadj : r.toSubgraph.Adj x y := Walk.adj_toSubgraph_iff_mem_edges.mpr hed
    have hy : y = r.snd ∨ y = r.penultimate := by
      have hm : y ∈ r.toSubgraph.neighborSet x := hadj
      rw [hr.neighborSet_toSubgraph_endpoint] at hm
      exact hm
    rcases hy with hy | hy
    · exact successor_first G hG v hd r hr hk hrlen (by simpa only [← hy] using hnew)
    · exact successor_first G hG v hd r.reverse hr.reverse hk
        (by simpa only [Walk.length_reverse] using hrlen)
        (by simpa only [Walk.snd_reverse, ← hy] using hnew)


private theorem no_two_pole_neighbors {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) (v x a b : V)
    (hx : G.Adj v x) (ha : G.Adj v a) (hb : G.Adj v b)
    (hab : a ≠ b) (hxa : G.Adj x a) (hxb : G.Adj x b) : False := by
  let t : G.Walk v v := .cons ha (.cons hxa.symm (.cons hxb (.cons hb.symm .nil)))
  have ht : t.IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · simp [t, Walk.isPath_def, hab, hxa.ne.symm, hxb.ne, ha.ne.symm,
        hb.ne.symm, hx.ne.symm]
    · simp [t]
  exact hG.not_hasPowerOfTwoCycle ⟨2, by decide, v, t, ht, rfl⟩

private theorem missing_pole {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) (v : V) (hd : G.degree v = 3)
    (x : Vertex v) (hx : G.Adj v x.val) :
    ∃ y, G.Adj v y ∧ y ≠ x.val ∧ ¬ G.Adj x.val y := by
  classical
  obtain ⟨y,hy,hyx⟩ := (G.neighborFinset v).exists_mem_ne
    (by rw [card_neighborFinset_eq_degree, hd]; decide) x.val
  have hy' : G.Adj v y := by simpa using hy
  by_cases hxy : G.Adj x.val y
  · have hcard : ({x.val,y} : Finset V).card < (G.neighborFinset v).card := by
      rw [card_neighborFinset_eq_degree, hd]
      have hle : ({x.val,y} : Finset V).card ≤ 2 := by simp [hyx.symm]
      omega
    obtain ⟨z,hz,hzout⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    have hz' : G.Adj v z := by simpa using hz
    have hzx : z ≠ x.val := by intro he; exact hzout (by simp [he])
    have hzy : z ≠ y := by intro he; exact hzout (by simp [he])
    refine ⟨z,hz',hzx,?_⟩
    intro hxz
    exact no_two_pole_neighbors G hG v x.val y z hx hy' hz' hzy.symm hxy hxz
  · exact ⟨y,hy',hyx,hxy⟩

private theorem degree_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G)
    (v : V) (hd : G.degree v = 3) (x : Vertex v) :
    G.degree x.val ≤ (repairGraph G v).degree x := by
  classical
  rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
  by_cases hx : G.Adj v x.val
  · obtain ⟨y,hy',hyx,hxy⟩ := missing_pole G hG v hd x hx
    let f : G.neighborSet x.val → (repairGraph G v).neighborSet x := fun z =>
      if hz : z.val = v then
        ⟨⟨y, hy'.ne.symm⟩, Or.inr ⟨fun he => hyx (congrArg Subtype.val he).symm, hx, hy'⟩⟩
      else ⟨⟨z.val, hz⟩, Or.inl z.property⟩
    apply Fintype.card_le_of_injective f
    intro a b he
    have heval := congrArg (fun z : (repairGraph G v).neighborSet x => z.val.val) he
    by_cases ha : a.val = v <;> by_cases hb : b.val = v
    · exact Subtype.ext (ha.trans hb.symm)
    · have hyb : y = b.val := by simpa [f, ha, hb] using heval
      exact False.elim (hxy (hyb.symm ▸ b.property))
    · have hay : a.val = y := by simpa [f, ha, hb] using heval
      exact False.elim (hxy (hay ▸ a.property))
    · exact Subtype.ext (by simpa [f, ha, hb] using heval)
  · let f : G.neighborSet x.val → (repairGraph G v).neighborSet x := fun z =>
      ⟨⟨z.val, fun hz => hx (Eq.mp (congrArg (fun w : V => G.Adj w x.val) hz)
        z.property.symm)⟩, Or.inl z.property⟩
    apply Fintype.card_le_of_injective f
    intro a b he
    exact Subtype.ext (congrArg (fun z : (repairGraph G v).neighborSet x => z.val.val) he)

/-- In a vertex-minimal counterexample among all finite nonempty minimum-degree-three
ordinary graphs, every cubic vertex lies on a genuine cycle of length `2^k + 1`,
with `2 ≤ k`. No bipartiteness or existence of a counterexample is assumed or proved. -/
theorem exists_cycle_of_cubic_vertex {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hminimal : ∀ {W : Type u} [Fintype W] [Nonempty W] (Q : SimpleGraph W)
      [DecidableRel Q.Adj], Fintype.card W < Fintype.card V →
        (∀ x, 3 ≤ Q.degree x) → HasPowerOfTwoCycle Q)
    (v : V) (hd : G.degree v = 3) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ t : G.Walk v v, t.IsCycle ∧ t.length = 2^k + 1 := by
  classical
  have hcard : Fintype.card (Vertex v) = Fintype.card V - 1 := by
    simp [Fintype.card_subtype_compl (fun x : V => x = v)]
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  have hlt : Fintype.card (Vertex v) < Fintype.card V := by omega
  obtain ⟨y,hy⟩ := (G.degree_pos_iff_exists_adj v).mp (by omega)
  letI : Nonempty (Vertex v) := ⟨⟨y, hy.ne.symm⟩⟩
  obtain ⟨k,hk,hcycle⟩ := hminimal (repairGraph G v) hlt
    (fun x => (hG.degree_ge_three x.val).trans (degree_le G hG v hd x))
  exact ⟨k,hk,successor_cycle G hG v hd hk hcycle⟩

/-- Lexicographic minimality from `Basic` implies the global vertex-minimality
needed for the cubic-vertex odd-successor constraint. This is only a conditional result. -/
theorem exists_cycle_of_cubic_vertex_of_minimal {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsMinimalCounterexample G) (v : V) (hd : G.degree v = 3) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ t : G.Walk v v, t.IsCycle ∧ t.length = 2^k + 1 := by
  apply exists_cycle_of_cubic_vertex G hG.isCounterexample ?_ v hd
  intro W _ _ Q _ hlt hmin
  classical
  by_contra hcycle
  have hQ : IsCounterexample Q := ⟨inferInstance, hmin, hcycle⟩
  exact hG.false_of_size_lexLt Q hQ (Or.inl hlt)

private theorem induced_deletion_degree {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : V) (x : Vertex d) :
    (G.induce {y | y ≠ d}).degree x + (if G.Adj x.val d then 1 else 0) =
      G.degree x.val := by
  classical
  have hcard : (G.induce {y | y ≠ d}).degree x =
      ((G.neighborFinset x.val).erase d).card := by
    rw [← card_neighborFinset_eq_degree,
      ← Finset.card_map (Function.Embedding.subtype (fun y => y ≠ d))]
    congr 1
    ext y
    simp [and_comm]
  rw [hcard, Finset.card_erase_eq_ite]
  by_cases h : G.Adj x.val d
  · simp only [mem_neighborFinset, h, if_true, card_neighborFinset_eq_degree]
    have hpos : 0 < G.degree x.val := (G.degree_pos_iff_exists_adj x.val).mpr ⟨d,h⟩
    omega
  · simp [h]

private theorem exists_cubic_vertex {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hminimal : ∀ {W : Type u} [Fintype W] [Nonempty W] (Q : SimpleGraph W)
      [DecidableRel Q.Adj], Fintype.card W < Fintype.card V →
        (∀ x, 3 ≤ Q.degree x) → HasPowerOfTwoCycle Q) :
    ∃ v : V, G.degree v = 3 := by
  classical
  by_contra hnone
  have hhigh : ∀ x : V, 4 ≤ G.degree x := by
    intro x
    have hmin := hG.degree_ge_three x
    have hne : G.degree x ≠ 3 := fun he => hnone ⟨x,he⟩
    omega
  obtain ⟨d⟩ := hG.nonempty
  let Q := G.induce {y | y ≠ d}
  have hcard : Fintype.card (Vertex d) = Fintype.card V - 1 := by
    simp [Fintype.card_subtype_compl (fun x : V => x = d)]
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨d⟩
  have hlt : Fintype.card (Vertex d) < Fintype.card V := by omega
  obtain ⟨y,hy⟩ := (G.degree_pos_iff_exists_adj d).mp (by have hd := hhigh d; omega)
  letI : Nonempty ↥({y : V | y ≠ d} : Set V) := ⟨⟨y,hy.ne.symm⟩⟩
  have hminQ : ∀ x : Vertex d, 3 ≤ Q.degree x := by
    intro x
    have hdegree := induced_deletion_degree G d x
    have hxhigh := hhigh x.val
    change Q.degree x + (if G.Adj x.val d then 1 else 0) = G.degree x.val at hdegree
    split_ifs at hdegree <;> omega
  obtain ⟨k,hk,a,p,hp,hlen⟩ := hminimal Q hlt hminQ
  let f : Q →g G := { toFun := Subtype.val, map_rel' := fun h => h }
  have hf : Function.Injective f := Subtype.val_injective
  have hcycle : (p.map f).IsCycle := hp.map hf
  have hlength : (p.map f).length = 2^k := (p.length_map f).trans hlen
  exact hG.not_hasPowerOfTwoCycle ⟨k,hk,a.val,p.map f,hcycle,hlength⟩

/-- Every globally vertex-minimal counterexample among all finite nonempty ordinary
minimum-degree-three graphs contains a genuine cycle of length `2^k + 1`, with
`2 ≤ k`. No vertex needs to be selected in advance, and no existence claim follows. -/
theorem exists_cycle {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hminimal : ∀ {W : Type u} [Fintype W] [Nonempty W] (Q : SimpleGraph W)
      [DecidableRel Q.Adj], Fintype.card W < Fintype.card V →
        (∀ x, 3 ≤ Q.degree x) → HasPowerOfTwoCycle Q) :
    ∃ (v : V) (k : ℕ) (p : G.Walk v v), 2 ≤ k ∧ p.IsCycle ∧ p.length = 2^k + 1 := by
  obtain ⟨v,hd⟩ := exists_cubic_vertex G hG hminimal
  obtain ⟨k,hk,p,hp,hlen⟩ := exists_cycle_of_cubic_vertex G hG hminimal v hd
  exact ⟨v,k,p,hk,hp,hlen⟩

/-- A lexicographically minimal counterexample contains a genuine cycle of length
`2^k + 1`, with `2 ≤ k`. This is a conditional constraint, not a counterexample
existence theorem or an unconditional solution of the Erdős–Gyárfás problem. -/
theorem exists_cycle_of_minimal {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsMinimalCounterexample G) :
    ∃ (v : V) (k : ℕ) (p : G.Walk v v), 2 ≤ k ∧ p.IsCycle ∧ p.length = 2^k + 1 := by
  apply exists_cycle G hG.isCounterexample ?_
  intro W _ _ Q _ hlt hmin
  classical
  by_contra hcycle
  have hQ : IsCounterexample Q := ⟨inferInstance, hmin, hcycle⟩
  exact hG.false_of_size_lexLt Q hQ (Or.inl hlt)

end Erdos64.MinimalCubicOddSuccessor
