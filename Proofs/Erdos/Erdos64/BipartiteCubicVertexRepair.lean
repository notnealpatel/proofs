import Erdos.Erdos64.BipartiteRepairResult
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

set_option autoImplicit false

namespace Erdos64.BipartiteCubicVertexRepair
open SimpleGraph
open scoped Classical

/-- The retained vertices are exactly the vertices other than the deleted vertex. -/
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

private theorem same_color {V : Type*} (G : SimpleGraph V) (c : V → Bool)
    (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y) (v x y : V)
    (hx : G.Adj v x) (hy : G.Adj v y) : c x = c y := by
  have hx' := hc hx
  have hy' := hc hy
  cases hv : c v <;> cases hxx : c x <;> cases hyy : c y <;> simp_all

private theorem four_neighbors {V : Type*} [Fintype V] (G : SimpleGraph V)
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

private theorem parity {V : Type*} (G : SimpleGraph V) (c : V → Bool)
    (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y) {x y : V} (w : G.Walk x y) :
    w.length % 2 = if c x = c y then 0 else 1 := by
  induction w with
  | nil => simp
  | @cons x z y h w ih =>
    have hxz := hc h
    simp only [Walk.length_cons]
    cases hx : c x <;> cases hz : c z <;> cases hy : c y <;> simp_all <;> omega

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

/- An odd path between same-colored poles must use a new edge. Two new end
edges would again give four distinct neighbors, so precisely one end is new. -/
private theorem path_one_new {V : Type*} [Fintype V] (G : SimpleGraph V)
    (c : V → Bool) (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y)
    (v : V) (hd : G.degree v = 3) {x y : Vertex v}
    (w : (repairGraph G v).Walk x y) (hw : w.IsPath)
    (hx : G.Adj v x.val) (hy : G.Adj v y.val)
    (_hlen : 3 ≤ w.length) (hodd : w.length % 2 = 1) :
    ∃ i, i < w.length ∧ (i = 0 ∨ i + 1 = w.length) ∧
      ¬ G.Adj (w.getVert i).val (w.getVert (i + 1)).val ∧
      ∀ j, j < w.length → j ≠ i → G.Adj (w.getVert j).val (w.getVert (j + 1)).val := by
  classical
  have hex : ∃ i, i < w.length ∧
      ¬ G.Adj (w.getVert i).val (w.getVert (i + 1)).val := by
    by_contra! hn
    obtain ⟨r, hr, _⟩ := lift_old G v w hn
    have hp := parity G c hc r
    rw [same_color G c hc v x.val y.val hx hy, if_pos rfl, hr, hodd] at hp
    omega
  obtain ⟨i, hi, hnew⟩ := hex
  have hend := path_new_edge_end G v hd w hw hx hy hi hnew
  refine ⟨i, hi, hend, hnew, ?_⟩
  intro j hj hji
  by_contra hnewj
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

private theorem lift_odd_path {V : Type*} [Fintype V] (G : SimpleGraph V)
    (c : V → Bool) (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y)
    (v : V) (hd : G.degree v = 3) {x y : Vertex v}
    (hclose : (repairGraph G v).Adj y x) (w : (repairGraph G v).Walk x y)
    (hw : w.IsPath) (hx : G.Adj v x.val) (hy : G.Adj v y.val)
    (hlen : 3 ≤ w.length) (hodd : w.length % 2 = 1) :
    ∃ z, ∃ t : G.Walk z z, t.IsCycle ∧ t.length = w.length + 1 := by
  obtain ⟨i, hi, hend, hnew, hold⟩ := path_one_new G c hc v hd w hw hx hy hlen hodd
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

private theorem lift_cycle_first {V : Type*} [Fintype V] (G : SimpleGraph V)
    (c : V → Bool) (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y)
    (v : V) (hd : G.degree v = 3) {a : Vertex v}
    (w : (repairGraph G v).Walk a a) (hw : w.IsCycle) (heven : Even w.length)
    (hnew : ¬ G.Adj a.val w.snd.val) :
    ∃ z, ∃ t : G.Walk z z, t.IsCycle ∧ t.length = w.length := by
  cases w with
  | nil => exact False.elim (Walk.not_isCycle_nil hw)
  | @cons a b a h r =>
    have hn : ¬ G.Adj a.val b.val := by simpa using hnew
    obtain ⟨_, ha, hb⟩ := h.resolve_left hn
    obtain ⟨k, hk⟩ := heven
    have hthree := hw.three_le_length
    simp only [Walk.length_cons] at hk hthree
    have hrlen : 3 ≤ r.length := by omega
    have hodd : r.length % 2 = 1 := by omega
    obtain ⟨z,t,ht,htl⟩ := lift_odd_path G c hc v hd h r (by simpa using hw.isPath_tail) hb ha hrlen hodd
    exact ⟨z,t,ht,by simpa using htl⟩

private theorem even_cycle_transport {V : Type*} [Fintype V] (G : SimpleGraph V)
    (c : V → Bool) (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y)
    (v : V) (hd : G.degree v = 3) {n : ℕ} (hn : Even n)
    (hcycle : ∃ a, ∃ w : (repairGraph G v).Walk a a, w.IsCycle ∧ w.length = n) :
    ∃ z, ∃ t : G.Walk z z, t.IsCycle ∧ t.length = n := by
  classical
  obtain ⟨a,w,hw,hlen⟩ := hcycle
  by_cases hold : ∀ i, i < w.length → G.Adj (w.getVert i).val (w.getVert (i + 1)).val
  · obtain ⟨z,t,ht,htl⟩ := lift_cycle_old G v w hw hold
    exact ⟨z,t,ht,htl.trans hlen⟩
  · push Not at hold
    obtain ⟨i,hi,hnew⟩ := hold
    let x := w.getVert i
    let y := w.getVert (i + 1)
    have hmem : s(x,y) ∈ w.edges := (w.mk_mem_edges_iff_exists).mpr ⟨i,hi,rfl⟩
    have hx : x ∈ w.support := w.getVert_mem_support i
    let r := w.rotate x hx
    have hr : r.IsCycle := hw.rotate hx
    have hrlen : r.length = n := by simp [r, hlen]
    have hed : s(x,y) ∈ r.edges := ((w.rotate_edges x hx).perm.mem_iff).mpr hmem
    have hadj : r.toSubgraph.Adj x y := Walk.adj_toSubgraph_iff_mem_edges.mpr hed
    have hy : y = r.snd ∨ y = r.penultimate := by
      have hm : y ∈ r.toSubgraph.neighborSet x := hadj
      rw [hr.neighborSet_toSubgraph_endpoint] at hm
      exact hm
    rcases hy with hy | hy
    · have hf : ¬ G.Adj x.val r.snd.val := by simpa only [← hy] using hnew
      obtain ⟨z,t,ht,htl⟩ := lift_cycle_first G c hc v hd r hr (hrlen.symm ▸ hn) hf
      exact ⟨z,t,ht,htl.trans hrlen⟩
    · have hf : ¬ G.Adj x.val r.reverse.snd.val := by
        simpa only [Walk.snd_reverse, ← hy] using hnew
      obtain ⟨z,t,ht,htl⟩ := lift_cycle_first G c hc v hd r.reverse hr.reverse
        (by simpa only [Walk.length_reverse, hrlen] using hn) hf
      exact ⟨z,t,ht,by simpa only [Walk.length_reverse, hrlen] using htl⟩

/- It suffices to inject each original neighborhood into the repaired one.
For a neighbor of `v`, replace the lost neighbor `v` by another pole, which
cannot have been an original neighbor because the poles share their color. -/
private theorem degree_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    (c : V → Bool) (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y)
    (v : V) (hd : G.degree v = 3) (x : Vertex v) :
    G.degree x.val ≤ (repairGraph G v).degree x := by
  classical
  rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
  by_cases hx : G.Adj v x.val
  · obtain ⟨y,hy,hyx⟩ := (G.neighborFinset v).exists_mem_ne
      (by rw [card_neighborFinset_eq_degree, hd]; decide) x.val
    have hy' : G.Adj v y := by simpa using hy
    have hxy : ¬ G.Adj x.val y := by
      intro he
      exact hc he (same_color G c hc v x.val y hx hy')
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

/- The input hypotheses hold jointly on K3,3; all domains are inhabited. -/
example : ∃ (G : SimpleGraph (Fin 6)) (c : Fin 6 → Bool) (_ : DecidableRel G.Adj),
    (∀ x y, G.Adj x y → c x ≠ c y) ∧ (∀ x, 3 ≤ G.degree x) ∧ G.degree 0 = 3 := by
  let G : SimpleGraph (Fin 6) := fromRel fun x y => x.val < 3 ∧ 3 ≤ y.val
  refine ⟨G, fun x => decide (x.val < 3), (by dsimp [G]; infer_instance), ?_⟩
  decide


/-- Deleting a degree-three vertex of a properly Bool-colored graph and completing
its neighborhood to a triangle gives a finite nonempty minimum-degree-three repair.
Every even genuine cycle lifts with exactly the same length, and the output order
is strictly smaller. No C4 restriction or bipartiteness of the output is asserted. -/
theorem exists_repair {V : Type*} [Fintype V] (G : SimpleGraph V)
    (c : V → Bool) (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y)
    (hmin : ∀ x, 3 ≤ G.degree x) (v : V) (hd : G.degree v = 3) :
    ∃ R : BipartiteRepairResult G, @Fintype.card R.Vertex R.vertices < Fintype.card V := by
  classical
  have hcard : Fintype.card (Vertex v) = Fintype.card V - 1 := by
    simp [Fintype.card_subtype_compl (fun x : V => x = v)]
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  have hlt : Fintype.card (Vertex v) < Fintype.card V := by omega
  have hneighbor : ∃ y, G.Adj v y := (G.degree_pos_iff_exists_adj v).mp (by omega)
  obtain ⟨y,hy⟩ := hneighbor
  let R : BipartiteRepairResult G := {
    Vertex := Vertex v
    vertices := inferInstance
    inhabited := ⟨⟨y, hy.ne.symm⟩⟩
    graph := repairGraph G v
    order_le := hlt.le
    min_degree := fun x => (hmin x.val).trans (degree_le G c hc v hd x)
    even_cycles := fun _ hn h => even_cycle_transport G c hc v hd hn h }
  exact ⟨R, hlt⟩


end Erdos64.BipartiteCubicVertexRepair
