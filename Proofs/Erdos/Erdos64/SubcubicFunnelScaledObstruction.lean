import Erdos.Erdos64.SubcubicFunnelH7

set_option autoImplicit false

namespace Erdos64.SubcubicFunnel.ScaledObstruction
open SimpleGraph

/-- The lexicographic enumeration of the nine edges of the existing H7. -/
def h7Edge : Fin 9 → Fin 7 × Fin 7 :=
  ![(0,2), (0,3), (1,5), (1,6), (2,3), (2,4), (3,6), (4,5), (5,6)]

example : h7Edge 5 = (2,4) := rfl

/-- This enumeration lists exactly the unordered edges of the existing H7. -/
theorem h7Edge_iff : ∀ a b : Fin 7, h7.Adj a b ↔
    ∃ i : Fin 9, h7Edge i = (a,b) ∨ h7Edge i = (b,a) := by decide

/-- Original vertices retain their labels in the subdivision. -/
def old (i : Fin 7) : Fin 16 := ⟨i.val, by omega⟩

/-- Edge number i receives midpoint 7+i. -/
def mid (i : Fin 9) : Fin 16 := ⟨7 + i.val, by omega⟩

example : old 4 = 4 ∧ mid 5 = 12 := by decide

private def sEdges : List (Fin 16 × Fin 16) := [(0,7), (0,8), (1,9), (1,10), (2,11), (2,12), (3,13), (4,14), (5,15), (7,2), (8,3), (9,5), (10,6), (11,3), (12,4), (13,6), (14,5), (15,6)]

/-- The uniform two-subdivision of H7, with midpoint 7+i on edge number i. -/
def S : SimpleGraph (Fin 16) where
  Adj a b := (a,b) ∈ sEdges ∨ (b,a) ∈ sEdges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro a; fin_cases a <;> decide⟩

instance : DecidableRel S.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- All and only subdivision edges join an original endpoint to its midpoint. -/
theorem S_adj_iff : ∀ a b : Fin 16, S.Adj a b ↔ ∃ i : Fin 9,
    (a = old (h7Edge i).1 ∧ b = mid i) ∨
    (a = old (h7Edge i).2 ∧ b = mid i) ∨
    (b = old (h7Edge i).1 ∧ a = mid i) ∨
    (b = old (h7Edge i).2 ∧ a = mid i) := by decide

example : S.Adj 4 12 ∧ S.degree 4 = 2 ∧ S.degree 12 = 2 := by decide

/-- The left copy uses labels 0 through 15. -/
def leftMap (i : Fin 16) : Fin 30 := ⟨i.val, by omega⟩

/-- The right copy identifies only labels 4 and 12 with the left copy. -/
def rightMap : Fin 16 → Fin 30 :=
  ![16,17,18,19,4,20,21,22,23,24,25,26,12,27,28,29]

example : leftMap 0 = 0 ∧ rightMap 0 = 16 ∧ rightMap 4 = 4 ∧ rightMap 12 = 12 :=
  by decide

private def gEdges : List (Fin 30 × Fin 30) :=
  sEdges.map (fun e => (leftMap e.1, leftMap e.2)) ++
  sEdges.map (fun e => (rightMap e.1, rightMap e.2))

/-- The union of the two subdivided copies, glued along the edge 4--12.
Adjacency is a set predicate, so the shared edge is counted only once. -/
def G : SimpleGraph (Fin 30) where
  Adj a b := (a,b) ∈ gEdges ∨ (b,a) ∈ gEdges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro a; fin_cases a <;> decide⟩

instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

example : G.Adj 4 12 ∧ ¬ G.Adj 0 16 := by decide

/-- The left copy preserves and reflects adjacency: it is induced. -/
def left : S ↪g G where
  toFun := leftMap
  inj' := by decide
  map_rel_iff' := by decide

/-- The right copy preserves and reflects adjacency: it is induced. -/
def right : S ↪g G where
  toFun := rightMap
  inj' := by decide
  map_rel_iff' := by decide

example : left 4 = right 4 ∧ left 12 = right 12 := by decide

/-- There are thirty vertices. -/
theorem card_vertices : Fintype.card (Fin 30) = 30 := rfl

/-- The union contains exactly thirty-five undirected edges. -/
theorem card_edges : G.edgeFinset.card = 35 := by decide

/-- Exactly the displayed ten labels have degree three; all others have degree two. -/
theorem degree_eq : ∀ v : Fin 30, G.degree v =
    if v ∈ ({2,3,4,5,6,12,18,19,20,21} : Finset (Fin 30)) then 3 else 2 := by decide

/-- This finite graph is subcubic, not cubic. -/
theorem subcubic : ∀ v : Fin 30, G.degree v ≤ 3 := by decide

/-- Every vertex has degree at least two. -/
theorem two_le_degree : ∀ v : Fin 30, 2 ≤ G.degree v := by decide

/-- Vertex zero witnesses that the minimum degree is two, not three. -/
theorem degree_zero : G.degree 0 = 2 := by decide

/-- Exact membership in the left range. -/
theorem mem_range_left (v : Fin 30) : v ∈ Set.range left ↔ v.val < 16 := by
  change (∃ i : Fin 16, leftMap i = v) ↔ v.val < 16
  have h : ∀ v : Fin 30, (∃ i : Fin 16, leftMap i = v) ↔ v.val < 16 := by decide
  exact h v

/-- Exact membership in the right range. -/
theorem mem_range_right (v : Fin 30) :
    v ∈ Set.range right ↔ v = 4 ∨ v = 12 ∨ 16 ≤ v.val := by
  change (∃ i : Fin 16, rightMap i = v) ↔ _
  have h : ∀ v : Fin 30, (∃ i : Fin 16, rightMap i = v) ↔
      v = 4 ∨ v = 12 ∨ 16 ≤ v.val := by decide
  exact h v

/-- The actual ranges intersect exactly at the endpoints of the shared edge. -/
theorem range_inter : Set.range left ∩ Set.range right = ({4,12} : Set (Fin 30)) := by
  ext v
  simp only [Set.mem_inter_iff, mem_range_left, mem_range_right,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hl, hr⟩
    rcases hr with h4 | h12 | hr
    · exact Or.inl h4
    · exact Or.inr h12
    · omega
  · rintro (rfl | rfl) <;> decide

/-- Independent label witnesses: zero belongs only to the left, and four to both. -/
theorem overlap_witnesses : (0 : Fin 30) ∈ Set.range left ∧
    (0 : Fin 30) ∉ Set.range right ∧ (4 : Fin 30) ∈ Set.range left ∧
    (4 : Fin 30) ∈ Set.range right := by
  rw [mem_range_left, mem_range_right, mem_range_left, mem_range_right]
  decide

/-- The two induced ranges are unequal. -/
theorem ranges_ne : Set.range left ≠ Set.range right := by
  intro h
  exact overlap_witnesses.2.1 (h ▸ overlap_witnesses.1)

/-- The two induced ranges are not disjoint. -/
theorem ranges_not_disjoint : ¬ Disjoint (Set.range left) (Set.range right) := by
  intro h
  exact Set.disjoint_left.mp h overlap_witnesses.2.2.1 overlap_witnesses.2.2.2

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
private theorem no_closed_4 : ∀ v0 v1 : Fin 30, G.Adj v0 v1 → v1 ∉ [v0] →
    ∀ v2 : Fin 30, G.Adj v1 v2 → v2 ∉ [v0,v1] →
    ∀ v3 : Fin 30, G.Adj v2 v3 → v3 ∉ [v0,v1,v2] →
    ¬ G.Adj v3 v0 := by decide

/-- The graph has no genuine simple cycle of length 4.
The certificate prunes at each adjacency and repeated vertex, using kernel `decide`. -/
theorem no_cycle_4 : ¬ HasSimpleCycleOfLength G 4 := by
  rintro ⟨v,w,hw,hl⟩
  cases w with
  | nil => simp at hl
  | cons e0 w =>
      cases w with
      | nil => simp at hl
      | cons e1 w =>
          cases w with
          | nil => simp at hl
          | cons e2 w =>
              cases w with
              | nil => simp at hl
              | cons e3 w =>
                  cases w with
                  | cons e w =>
                    have hlen := w.length
                    simp only [Walk.length_cons] at hl
                    omega
                  | nil =>
                    have hn := hw.support_nodup
                    simp only [Walk.support_cons, Walk.support_nil, List.tail_cons, List.nodup_cons,
                      List.mem_cons, List.not_mem_nil, List.nodup_nil, not_or, and_true] at hn
                    exact no_closed_4 _ _ e0 (by simp [hn])
                      _ e1 (by simp [hn,ne_comm])
                      _ e2 (by simp [hn,ne_comm])
                      e3

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
private theorem no_closed_8 : ∀ v0 v1 : Fin 30, G.Adj v0 v1 → v1 ∉ [v0] →
    ∀ v2 : Fin 30, G.Adj v1 v2 → v2 ∉ [v0,v1] →
    ∀ v3 : Fin 30, G.Adj v2 v3 → v3 ∉ [v0,v1,v2] →
    ∀ v4 : Fin 30, G.Adj v3 v4 → v4 ∉ [v0,v1,v2,v3] →
    ∀ v5 : Fin 30, G.Adj v4 v5 → v5 ∉ [v0,v1,v2,v3,v4] →
    ∀ v6 : Fin 30, G.Adj v5 v6 → v6 ∉ [v0,v1,v2,v3,v4,v5] →
    ∀ v7 : Fin 30, G.Adj v6 v7 → v7 ∉ [v0,v1,v2,v3,v4,v5,v6] →
    ¬ G.Adj v7 v0 := by decide

/-- The graph has no genuine simple cycle of length 8.
The certificate prunes at each adjacency and repeated vertex, using kernel `decide`. -/
theorem no_cycle_8 : ¬ HasSimpleCycleOfLength G 8 := by
  rintro ⟨v,w,hw,hl⟩
  cases w with
  | nil => simp at hl
  | cons e0 w =>
      cases w with
      | nil => simp at hl
      | cons e1 w =>
          cases w with
          | nil => simp at hl
          | cons e2 w =>
              cases w with
              | nil => simp at hl
              | cons e3 w =>
                  cases w with
                  | nil => simp at hl
                  | cons e4 w =>
                      cases w with
                      | nil => simp at hl
                      | cons e5 w =>
                          cases w with
                          | nil => simp at hl
                          | cons e6 w =>
                              cases w with
                              | nil => simp at hl
                              | cons e7 w =>
                                  cases w with
                                  | cons e w =>
                                    have hlen := w.length
                                    simp only [Walk.length_cons] at hl
                                    omega
                                  | nil =>
                                    have hn := hw.support_nodup
                                    simp only [Walk.support_cons, Walk.support_nil, List.tail_cons, List.nodup_cons,
                                      List.mem_cons, List.not_mem_nil, List.nodup_nil, not_or, and_true] at hn
                                    exact no_closed_8 _ _ e0 (by simp [hn])
                                      _ e1 (by simp [hn,ne_comm])
                                      _ e2 (by simp [hn,ne_comm])
                                      _ e3 (by simp [hn,ne_comm])
                                      _ e4 (by simp [hn,ne_comm])
                                      _ e5 (by simp [hn,ne_comm])
                                      _ e6 (by simp [hn,ne_comm])
                                      e7

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
private theorem no_closed_16 : ∀ v0 v1 : Fin 30, G.Adj v0 v1 → v1 ∉ [v0] →
    ∀ v2 : Fin 30, G.Adj v1 v2 → v2 ∉ [v0,v1] →
    ∀ v3 : Fin 30, G.Adj v2 v3 → v3 ∉ [v0,v1,v2] →
    ∀ v4 : Fin 30, G.Adj v3 v4 → v4 ∉ [v0,v1,v2,v3] →
    ∀ v5 : Fin 30, G.Adj v4 v5 → v5 ∉ [v0,v1,v2,v3,v4] →
    ∀ v6 : Fin 30, G.Adj v5 v6 → v6 ∉ [v0,v1,v2,v3,v4,v5] →
    ∀ v7 : Fin 30, G.Adj v6 v7 → v7 ∉ [v0,v1,v2,v3,v4,v5,v6] →
    ∀ v8 : Fin 30, G.Adj v7 v8 → v8 ∉ [v0,v1,v2,v3,v4,v5,v6,v7] →
    ∀ v9 : Fin 30, G.Adj v8 v9 → v9 ∉ [v0,v1,v2,v3,v4,v5,v6,v7,v8] →
    ∀ v10 : Fin 30, G.Adj v9 v10 → v10 ∉ [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9] →
    ∀ v11 : Fin 30, G.Adj v10 v11 → v11 ∉ [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10] →
    ∀ v12 : Fin 30, G.Adj v11 v12 → v12 ∉ [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11] →
    ∀ v13 : Fin 30, G.Adj v12 v13 → v13 ∉ [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12] →
    ∀ v14 : Fin 30, G.Adj v13 v14 → v14 ∉ [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13] →
    ∀ v15 : Fin 30, G.Adj v14 v15 → v15 ∉ [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14] →
    ¬ G.Adj v15 v0 := by decide

/-- The graph has no genuine simple cycle of length 16.
The certificate prunes at each adjacency and repeated vertex, using kernel `decide`. -/
theorem no_cycle_16 : ¬ HasSimpleCycleOfLength G 16 := by
  rintro ⟨v,w,hw,hl⟩
  cases w with
  | nil => simp at hl
  | cons e0 w =>
      cases w with
      | nil => simp at hl
      | cons e1 w =>
          cases w with
          | nil => simp at hl
          | cons e2 w =>
              cases w with
              | nil => simp at hl
              | cons e3 w =>
                  cases w with
                  | nil => simp at hl
                  | cons e4 w =>
                      cases w with
                      | nil => simp at hl
                      | cons e5 w =>
                          cases w with
                          | nil => simp at hl
                          | cons e6 w =>
                              cases w with
                              | nil => simp at hl
                              | cons e7 w =>
                                  cases w with
                                  | nil => simp at hl
                                  | cons e8 w =>
                                      cases w with
                                      | nil => simp at hl
                                      | cons e9 w =>
                                          cases w with
                                          | nil => simp at hl
                                          | cons e10 w =>
                                              cases w with
                                              | nil => simp at hl
                                              | cons e11 w =>
                                                  cases w with
                                                  | nil => simp at hl
                                                  | cons e12 w =>
                                                      cases w with
                                                      | nil => simp at hl
                                                      | cons e13 w =>
                                                          cases w with
                                                          | nil => simp at hl
                                                          | cons e14 w =>
                                                              cases w with
                                                              | nil => simp at hl
                                                              | cons e15 w =>
                                                                  cases w with
                                                                  | cons e w =>
                                                                    have hlen := w.length
                                                                    simp only [Walk.length_cons] at hl
                                                                    omega
                                                                  | nil =>
                                                                    have hn := hw.support_nodup
                                                                    simp only [Walk.support_cons, Walk.support_nil, List.tail_cons, List.nodup_cons,
                                                                      List.mem_cons, List.not_mem_nil, List.nodup_nil, not_or, and_true] at hn
                                                                    exact no_closed_16 _ _ e0 (by simp [hn])
                                                                      _ e1 (by simp [hn,ne_comm])
                                                                      _ e2 (by simp [hn,ne_comm])
                                                                      _ e3 (by simp [hn,ne_comm])
                                                                      _ e4 (by simp [hn,ne_comm])
                                                                      _ e5 (by simp [hn,ne_comm])
                                                                      _ e6 (by simp [hn,ne_comm])
                                                                      _ e7 (by simp [hn,ne_comm])
                                                                      _ e8 (by simp [hn,ne_comm])
                                                                      _ e9 (by simp [hn,ne_comm])
                                                                      _ e10 (by simp [hn,ne_comm])
                                                                      _ e11 (by simp [hn,ne_comm])
                                                                      _ e12 (by simp [hn,ne_comm])
                                                                      _ e13 (by simp [hn,ne_comm])
                                                                      _ e14 (by simp [hn,ne_comm])
                                                                      e15

/-- Any genuine simple cycle uses at most the thirty available vertices. -/
theorem cycle_length_le_thirty {v : Fin 30} (w : G.Walk v v) (hw : w.IsCycle) :
    w.length ≤ 30 := by
  have hbound := hw.support_nodup.length_le_card
  simpa only [List.length_tail, Walk.length_support, Nat.add_sub_cancel,
    Fintype.card_fin] using hbound

/-- There are no dyadic simple cycles of length at least four in this finite graph. -/
theorem no_dyadic_cycle (k : ℕ) (hk : 2 ≤ k) :
    ¬ HasSimpleCycleOfLength G (2 ^ k) := by
  by_cases hlarge : 5 ≤ k
  · rintro ⟨v,w,hw,hl⟩
    have hbound : 2 ^ k ≤ 30 := hl ▸ cycle_length_le_thirty w hw
    have hpow : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hlarge
    norm_num at hpow
    omega
  · have hcases : k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact no_cycle_4
    · exact no_cycle_8
    · exact no_cycle_16

/-- The induced copies of this subdivision do not obey equal-or-disjoint packing,
even in this finite subcubic graph with no dyadic cycles of length at least four. -/
theorem not_equal_or_disjoint_packing :
    ¬ ∀ f g : S ↪g G, Set.range f = Set.range g ∨ Disjoint (Set.range f) (Set.range g) := by
  intro hpacking
  rcases hpacking left right with heq | hdisj
  · exact ranges_ne heq
  · exact ranges_not_disjoint hdisj

/-- The explicit finite obstruction: minimum degree two, maximum degree three,
35 edges on 30 vertices, no dyadic simple cycle of length at least four, and two
induced copies of the uniform two-subdivision of H7 with proper overlap.
This is not a minimum-degree-three counterexample to Erdős–Gyárfás. -/
theorem finite_subcubic_packing_counterexample :
    Fintype.card (Fin 30) = 30 ∧ G.edgeFinset.card = 35 ∧
    (∀ v : Fin 30, 2 ≤ G.degree v ∧ G.degree v ≤ 3) ∧ G.degree 0 = 2 ∧
    (∀ k : ℕ, 2 ≤ k → ¬ HasSimpleCycleOfLength G (2 ^ k)) ∧
    ∃ f g : S ↪g G, Set.range f ∩ Set.range g = ({4,12} : Set (Fin 30)) ∧
      Set.range f ≠ Set.range g ∧ ¬ Disjoint (Set.range f) (Set.range g) := by
  refine ⟨card_vertices, card_edges, ?_, degree_zero, no_dyadic_cycle, ?_⟩
  · intro v
    exact ⟨two_le_degree v, subcubic v⟩
  · exact ⟨left, right, range_inter, ranges_ne, ranges_not_disjoint⟩

end Erdos64.SubcubicFunnel.ScaledObstruction
