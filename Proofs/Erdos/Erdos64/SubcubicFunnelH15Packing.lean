import Erdos.Erdos64.SubcubicFunnelPacking
import Erdos.Erdos64.SubcubicFunnelSymmetricPacking

set_option autoImplicit false

namespace Erdos64.SubcubicFunnel
open SimpleGraph

/-- The exact H15 source: two H7 blocks and the three connector edges
`0–7`, `1–14`, and `14–8`. -/
def h15 : SimpleGraph (Fin 15) where
  Adj i j := (i, j) ∈ ([(0,2),(0,3),(2,3),(2,4),(4,5),(1,5),(1,6),(5,6),(3,6),
    (7,9),(7,10),(9,10),(9,11),(11,12),(8,12),(8,13),(12,13),(10,13),
    (0,7),(1,14),(14,8)] : List (Fin 15 × Fin 15)) ∨
    (j, i) ∈ ([(0,2),(0,3),(2,3),(2,4),(4,5),(1,5),(1,6),(5,6),(3,6),
    (7,9),(7,10),(9,10),(9,11),(11,12),(8,12),(8,13),(12,13),(10,13),
    (0,7),(1,14),(14,8)] : List (Fin 15 × Fin 15))
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro i; fin_cases i <;> decide⟩

instance : DecidableRel h15.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

example : h15.Adj 0 7 ∧ h15.Adj 1 14 ∧ h15.Adj 14 8 ∧ ¬ h15.Adj 4 11 := by
  decide

/-- The left induced source H7 in H15, with labels unchanged. -/
def h15Left : h7 ↪g h15 where
  toFun i := ⟨i.val, by omega⟩
  inj' := by intro i j h; apply Fin.ext; exact congrArg (fun x : Fin 15 => x.val) h
  map_rel_iff' := by intro i j; fin_cases i <;> fin_cases j <;> decide

/-- The right induced source H7 in H15, with labels shifted by seven. -/
def h15Right : h7 ↪g h15 where
  toFun i := ⟨7 + i.val, by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega
  map_rel_iff' := by intro i j; fin_cases i <;> fin_cases j <;> decide

example : h15Left 0 = 0 ∧ h15Right 0 = 7 ∧ h15Right 6 = 13 := by decide

/-- The two constituent H7 vertex sets in the exact source are disjoint. -/
theorem h15_constituents_disjoint : Disjoint (Set.range h15Left) (Set.range h15Right) := by
  rw [Set.disjoint_left]
  rintro x ⟨i,rfl⟩ ⟨j,hj⟩
  have hh := congrArg (fun x : Fin 15 => x.val) hj
  change 7 + j.val = i.val at hh
  omega

/-- Every source vertex lies in a constituent or is the connector. -/
theorem h15_vertex_cases (i : Fin 15) :
    (∃ j, h15Left j = i) ∨ (∃ j, h15Right j = i) ∨ i = 14 := by
  by_cases hi : i.val < 7
  · exact Or.inl ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
  by_cases hi' : i.val < 14
  · exact Or.inr (Or.inl ⟨⟨i.val - 7, by omega⟩, by apply Fin.ext; change 7 + (i.val - 7) = i.val; omega⟩)
  · exact Or.inr (Or.inr (Fin.ext (by omega)))

/-- H15 is subcubic; its only degree-two vertices are its three ports. -/
theorem h15_subcubic : ∀ i, h15.degree i ≤ 3 := by
  decide

/-- The exact source degrees distinguish its ports 4, 11, and 14. -/
theorem h15_degree (i : Fin 15) :
    h15.degree i = if i = 4 ∨ i = 11 ∨ i = 14 then 2 else 3 := by
  fin_cases i <;> decide

private theorem connector_excluded {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v ≤ 3)
    {K : SimpleGraph (Fin 7)} (hmin : ∀ i, ∃ a b, a ≠ b ∧ K.Adj i a ∧ K.Adj i b)
    (f : K ↪g G) (g : h15 ↪g G)
    (hl : Disjoint (Set.range f) (Set.range (g.comp h15Left)))
    (hr : Disjoint (Set.range f) (Set.range (g.comp h15Right))) :
    g 14 ∉ Set.range f := by
  rintro ⟨i,hi⟩
  obtain ⟨a,b,hab,ha,hb⟩ := hmin i
  have ha1 : f a ≠ g 1 := fun h => Set.disjoint_left.mp hl ⟨a,rfl⟩ ⟨1,h.symm⟩
  have hb1 : f b ≠ g 1 := fun h => Set.disjoint_left.mp hl ⟨b,rfl⟩ ⟨1,h.symm⟩
  have ha8 : f a ≠ g 8 := fun h => Set.disjoint_left.mp hr ⟨a,rfl⟩ ⟨1,h.symm⟩
  have hb8 : f b ≠ g 8 := fun h => Set.disjoint_left.mp hr ⟨b,rfl⟩ ⟨1,h.symm⟩
  have hab' : f a ≠ f b := fun h => hab (f.injective h)
  have h18 : g 1 ≠ g 8 := fun h => (by decide : (1 : Fin 15) ≠ 8) (g.injective h)
  have hn : [f a,f b,g 1].Nodup := by simp [hab',ha1,hb1]
  have hea : G.Adj (g 14) (f a) := by rw [← hi]; exact f.map_rel_iff.mpr ha
  have heb : G.Adj (g 14) (f b) := by rw [← hi]; exact f.map_rel_iff.mpr hb
  have he := neighbor_eq_of_three hdeg hn hea heb
    (g.map_rel_iff.mpr (by decide : h15.Adj 14 1))
    (g.map_rel_iff.mpr (by decide : h15.Adj 14 8))
  rcases he with he | he | he
  · exact ha8 he.symm
  · exact hb8 he.symm
  · exact h18 he.symm

/-- An induced H7 in a subcubic no-C8 graph is a constituent of an induced
H15 or is disjoint from its entire actual vertex range. -/
theorem h7_h15_constituent_or_disjoint {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v ≤ 3)
    (h8 : ¬ HasSimpleCycleOfLength G 8) (f : h7 ↪g G) (g : h15 ↪g G) :
    Set.range f = Set.range (g.comp h15Left) ∨
    Set.range f = Set.range (g.comp h15Right) ∨ Disjoint (Set.range f) (Set.range g) := by
  rcases h7_embedding_ranges_eq_or_disjoint hdeg h8 f (g.comp h15Left) with he | hl
  · exact Or.inl he
  rcases h7_embedding_ranges_eq_or_disjoint hdeg h8 f (g.comp h15Right) with he | hr
  · exact Or.inr (Or.inl he)
  have hz := connector_excluded hdeg (by decide : ∀ i, ∃ a b, a ≠ b ∧ h7.Adj i a ∧ h7.Adj i b) f g hl hr
  refine Or.inr (Or.inr ?_)
  rw [Set.disjoint_left]
  rintro x hx ⟨i,rfl⟩
  rcases h15_vertex_cases i with ⟨j,rfl⟩ | ⟨j,rfl⟩ | rfl
  · exact Set.disjoint_left.mp hl hx ⟨j,rfl⟩
  · exact Set.disjoint_left.mp hr hx ⟨j,rfl⟩
  · exact hz hx

/-- The symmetric subdivided-K4 source and H15 have disjoint actual ranges
in every finite subcubic graph; no cycle exclusion is needed. -/
theorem h7Symm_h15_disjoint {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v ≤ 3)
    (f : h7Symm ↪g G) (g : h15 ↪g G) : Disjoint (Set.range f) (Set.range g) := by
  have hl := (h7_h7Symm_disjoint hdeg (g.comp h15Left) f).symm
  have hr := (h7_h7Symm_disjoint hdeg (g.comp h15Right) f).symm
  have hz := connector_excluded hdeg (by decide : ∀ i, ∃ a b, a ≠ b ∧ h7Symm.Adj i a ∧ h7Symm.Adj i b) f g hl hr
  rw [Set.disjoint_left]
  rintro x hx ⟨i,rfl⟩
  rcases h15_vertex_cases i with ⟨j,rfl⟩ | ⟨j,rfl⟩ | rfl
  · exact Set.disjoint_left.mp hl hx ⟨j,rfl⟩
  · exact Set.disjoint_left.mp hr hx ⟨j,rfl⟩
  · exact hz hx

/-- The connector of an induced H15 lies in no induced H7 in a subcubic
no-C8 graph. -/
theorem h7_h15_connector_not_mem {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v ≤ 3)
    (h8 : ¬ HasSimpleCycleOfLength G 8) (f : h7 ↪g G) (g : h15 ↪g G) :
    g 14 ∉ Set.range f := by
  have hl : g 14 ∉ Set.range (g.comp h15Left) := by
    rintro ⟨i,hi⟩
    have hh := congrArg (fun x : Fin 15 => x.val) (g.injective hi)
    change i.val = 14 at hh
    omega
  have hr : g 14 ∉ Set.range (g.comp h15Right) := by
    rintro ⟨i,hi⟩
    have hh := congrArg (fun x : Fin 15 => x.val) (g.injective hi)
    change 7 + i.val = 14 at hh
    omega
  rcases h7_h15_constituent_or_disjoint hdeg h8 f g with he | he | hd
  · rw [he]; exact hl
  · rw [he]; exact hr
  · intro hx; exact Set.disjoint_left.mp hd hx ⟨14,rfl⟩

/-- Swapping the two seven-vertex blocks is an automorphism of exact H15. -/
def h15Swap : h15 ≃g h15 where
  toEquiv :=
    { toFun := fun i => (![7,8,9,10,11,12,13,0,1,2,3,4,5,6,14] : Fin 15 → Fin 15) i
      invFun := fun i => (![7,8,9,10,11,12,13,0,1,2,3,4,5,6,14] : Fin 15 → Fin 15) i
      left_inv := by intro i; fin_cases i <;> decide
      right_inv := by intro i; fin_cases i <;> decide }
  map_rel_iff' := by intro i j; fin_cases i <;> fin_cases j <;> decide

example : h15Swap 0 = 7 ∧ h15Swap 8 = 1 ∧ h15Swap 14 = 14 := by decide

private theorem swap_left : h15Swap.toEmbedding.comp h15Left = h15Right := by
  ext i; fin_cases i <;> rfl

private theorem swap_range {V : Type*} {G : SimpleGraph V} (f : h15 ↪g G) :
    Set.range (f.comp h15Swap.toEmbedding) = Set.range f := by
  ext x
  constructor
  · rintro ⟨i,rfl⟩; exact ⟨h15Swap i,rfl⟩
  · rintro ⟨i,rfl⟩; exact ⟨h15Swap.symm i, by simp⟩

private theorem external_neighbor_unique {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v ≤ 3)
    (f : h7 ↪g G) (i : Fin 7) (hi : i = 0 ∨ i = 1)
    {x y : V} (hx : G.Adj (f i) x) (hy : G.Adj (f i) y)
    (hxo : x ∉ Set.range f) (hyo : y ∉ Set.range f) : x = y := by
  have ht : ∀ i : Fin 7, (i = 0 ∨ i = 1) →
      ∃ a b, a ≠ b ∧ h7.Adj i a ∧ h7.Adj i b := by decide
  obtain ⟨a,b,hab,ha,hb⟩ := ht i hi
  have hab' : f a ≠ f b := fun h => hab (f.injective h)
  have hax : f a ≠ x := fun h => hxo ⟨a,h⟩
  have hbx : f b ≠ x := fun h => hxo ⟨b,h⟩
  have hn : [f a,f b,x].Nodup := by simp [hab',hax,hbx]
  have he := neighbor_eq_of_three hdeg hn (f.map_rel_iff.mpr ha) (f.map_rel_iff.mpr hb) hx hy
  rcases he with he | he | he
  · exact (hyo ⟨a,he.symm⟩).elim
  · exact (hyo ⟨b,he.symm⟩).elim
  · exact he.symm

private theorem outside_left {V : Type*} {G : SimpleGraph V} (f : h15 ↪g G)
    (k : Fin 15) (hk : 7 ≤ k.val) : f k ∉ Set.range (f.comp h15Left) := by
  rintro ⟨i,hi⟩
  have hh := congrArg (fun x : Fin 15 => x.val) (f.injective hi)
  change i.val = k.val at hh
  omega

private theorem same_left_range {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v ≤ 3)
    (h8 : ¬ HasSimpleCycleOfLength G 8) (f g : h15 ↪g G)
    (hl : Set.range (f.comp h15Left) = Set.range (g.comp h15Left)) :
    Set.range f = Set.range g := by
  have hports := h7_triangle_ports_of_range_eq hdeg (f.comp h15Left) (g.comp h15Left) hl
  have hf7 := outside_left f 7 (by decide)
  have hf14 := outside_left f 14 (by decide)
  have hg7 : g 7 ∉ Set.range (f.comp h15Left) := by rw [hl]; exact outside_left g 7 (by decide)
  have hg14 : g 14 ∉ Set.range (f.comp h15Left) := by rw [hl]; exact outside_left g 14 (by decide)
  rcases hports with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · change f 0 = g 0 at h0
    change f 1 = g 1 at h1
    have h7 : f 7 = g 7 := external_neighbor_unique hdeg (f.comp h15Left) 0 (Or.inl rfl)
      (f.map_rel_iff.mpr (by decide : h15.Adj 0 7))
      (by change G.Adj (f 0) (g 7); rw [h0]; exact g.map_rel_iff.mpr (by decide)) hf7 hg7
    have hz : f 14 = g 14 := external_neighbor_unique hdeg (f.comp h15Left) 1 (Or.inr rfl)
      (f.map_rel_iff.mpr (by decide : h15.Adj 1 14))
      (by change G.Adj (f 1) (g 14); rw [h1]; exact g.map_rel_iff.mpr (by decide)) hf14 hg14
    have hr := h7_embedding_ranges_eq_of_shared_vertex hdeg h8 (f.comp h15Right)
      (g.comp h15Right) (x := f 7) ⟨0,rfl⟩ ⟨0,h7.symm⟩
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      rcases h15_vertex_cases i with ⟨j,rfl⟩ | ⟨j,rfl⟩ | rfl
      · obtain ⟨k,hk⟩ := hl ▸ (Set.mem_range_self j : (f.comp h15Left) j ∈ Set.range (f.comp h15Left))
        exact ⟨h15Left k,hk⟩
      · obtain ⟨k,hk⟩ := hr ▸ (Set.mem_range_self j : (f.comp h15Right) j ∈ Set.range (f.comp h15Right))
        exact ⟨h15Right k,hk⟩
      · exact ⟨14,hz.symm⟩
    · rintro ⟨i,rfl⟩
      rcases h15_vertex_cases i with ⟨j,rfl⟩ | ⟨j,rfl⟩ | rfl
      · obtain ⟨k,hk⟩ := hl.symm ▸ (Set.mem_range_self j : (g.comp h15Left) j ∈ Set.range (g.comp h15Left))
        exact ⟨h15Left k,hk⟩
      · obtain ⟨k,hk⟩ := hr.symm ▸ (Set.mem_range_self j : (g.comp h15Right) j ∈ Set.range (g.comp h15Right))
        exact ⟨h15Right k,hk⟩
      · exact ⟨14,hz⟩
  · change f 0 = g 1 at h0
    have he : f 7 = g 14 := external_neighbor_unique hdeg (f.comp h15Left) 0 (Or.inl rfl)
      (f.map_rel_iff.mpr (by decide : h15.Adj 0 7))
      (by change G.Adj (f 0) (g 14); rw [h0]; exact g.map_rel_iff.mpr (by decide)) hf7 hg14
    exact (h7_h15_connector_not_mem hdeg h8 (f.comp h15Right) g ⟨0,he⟩).elim

private theorem swap_left_range {V : Type*} {G : SimpleGraph V} (f : h15 ↪g G) :
    Set.range ((f.comp h15Swap.toEmbedding).comp h15Left) =
      Set.range (f.comp h15Right) := by
  change Set.range (f.comp (h15Swap.toEmbedding.comp h15Left)) = _
  rw [swap_left]

/-- Any two exact induced H15 copies in a finite subcubic graph without a
genuine simple eight-cycle have equal or disjoint actual vertex ranges.
No C4, C16, minimum degree, connectedness, or cubicity is assumed. -/
theorem h15_embedding_ranges_eq_or_disjoint {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v ≤ 3)
    (h8 : ¬ HasSimpleCycleOfLength G 8) (f g : h15 ↪g G) :
    Set.range f = Set.range g ∨ Disjoint (Set.range f) (Set.range g) := by
  rcases h7_h15_constituent_or_disjoint hdeg h8 (f.comp h15Left) g with hl | hr | hdl
  · exact Or.inl (same_left_range hdeg h8 f g hl)
  · have he := same_left_range hdeg h8 f (g.comp h15Swap.toEmbedding)
      (by rw [swap_left_range]; exact hr)
    exact Or.inl (he.trans (swap_range g))
  rcases h7_h15_constituent_or_disjoint hdeg h8 (f.comp h15Right) g with hl | hr | hdr
  · have he := same_left_range hdeg h8 (f.comp h15Swap.toEmbedding) g
      (by rw [swap_left_range]; exact hl)
    exact Or.inl ((swap_range f).symm.trans he)
  · have he := same_left_range hdeg h8 (f.comp h15Swap.toEmbedding) (g.comp h15Swap.toEmbedding)
      (by rw [swap_left_range,swap_left_range]; exact hr)
    exact Or.inl ((swap_range f).symm.trans (he.trans (swap_range g)))
  right
  rw [Set.disjoint_left]
  rintro x ⟨i,rfl⟩ ⟨j,hj⟩
  rcases h15_vertex_cases i with ⟨k,rfl⟩ | ⟨k,rfl⟩ | rfl
  · exact Set.disjoint_left.mp hdl ⟨k,rfl⟩ ⟨j,hj⟩
  · exact Set.disjoint_left.mp hdr ⟨k,rfl⟩ ⟨j,hj⟩
  have hz : g 14 = f 14 := by
    rcases h15_vertex_cases j with ⟨k,rfl⟩ | ⟨k,rfl⟩ | rfl
    · exact (h7_h15_connector_not_mem hdeg h8 (g.comp h15Left) f ⟨k,hj⟩).elim
    · exact (h7_h15_connector_not_mem hdeg h8 (g.comp h15Right) f ⟨k,hj⟩).elim
    · exact hj
  have h18 : f 1 ≠ f 8 := fun h => (by decide : (1 : Fin 15) ≠ 8) (f.injective h)
  have h11 : f 1 ≠ g 1 := fun h => Set.disjoint_left.mp hdl ⟨1,rfl⟩ ⟨1,h.symm⟩
  have h81 : f 8 ≠ g 1 := fun h => Set.disjoint_left.mp hdr ⟨1,rfl⟩ ⟨1,h.symm⟩
  have h18' : f 1 ≠ g 8 := fun h => Set.disjoint_left.mp hdl ⟨1,rfl⟩ ⟨8,h.symm⟩
  have h88 : f 8 ≠ g 8 := fun h => Set.disjoint_left.mp hdr ⟨1,rfl⟩ ⟨8,h.symm⟩
  have hg18 : g 1 ≠ g 8 := fun h => (by decide : (1 : Fin 15) ≠ 8) (g.injective h)
  have hn : [f 1,f 8,g 1].Nodup := by simp [h18,h11,h81]
  have he := neighbor_eq_of_three hdeg hn
    (f.map_rel_iff.mpr (by decide : h15.Adj 14 1))
    (f.map_rel_iff.mpr (by decide : h15.Adj 14 8))
    (by rw [← hz]; exact g.map_rel_iff.mpr (by decide : h15.Adj 14 1))
    (by rw [← hz]; exact g.map_rel_iff.mpr (by decide : h15.Adj 14 8))
  rcases he with he | he | he
  · exact h18' he.symm
  · exact h88 he.symm
  · exact hg18 he.symm

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 2048 in
private theorem h15_no_closed_eight : ∀ a b : Fin 15, h15.Adj a b → b ∉ [a] →
    ∀ c : Fin 15, h15.Adj b c → c ∉ [a,b] →
    ∀ d : Fin 15, h15.Adj c d → d ∉ [a,b,c] →
    ∀ e : Fin 15, h15.Adj d e → e ∉ [a,b,c,d] →
    ∀ f : Fin 15, h15.Adj e f → f ∉ [a,b,c,d,e] →
    ∀ g : Fin 15, h15.Adj f g → g ∉ [a,b,c,d,e,f] →
    ∀ h : Fin 15, h15.Adj g h → h ∉ [a,b,c,d,e,f,g] →
    ¬ h15.Adj h a := by decide

/-- The exact fifteen-vertex source has no genuine simple eight-cycle.
The finite certificate prunes at every edge and every repeated vertex; its
Boolean reductions are checked by the Lean kernel. -/
theorem h15_no_cycle_eight : ¬ HasSimpleCycleOfLength h15 8 := by
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
                    exact h15_no_closed_eight _ _ e0 (by simp [hn,ne_comm])
                      _ e1 (by simp [hn,ne_comm])
                      _ e2 (by simp [hn,ne_comm])
                      _ e3 (by simp [hn,ne_comm])
                      _ e4 (by simp [hn,ne_comm])
                      _ e5 (by simp [hn,ne_comm])
                      _ e6 (by simp [hn,ne_comm])
                      e7

private theorem lift_left {A B : Type*} {K : SimpleGraph A} {L : SimpleGraph B}
    {x y : A ⊕ B} (w : (K ⊕g L).Walk x y) :
    ∀ a, ∀ hx : x = Sum.inl a, ∃ b, ∃ hy : y = Sum.inl b, ∃ p : K.Walk a b,
      p.map Embedding.sumInl.toHom = w.copy hx hy := by
  induction w with
  | nil =>
    intro a hx
    cases hx
    exact ⟨a,rfl,.nil,rfl⟩
  | @cons x t y e w ih =>
    intro a hx
    subst x
    cases t with
    | inr t => cases e
    | inl t =>
      obtain ⟨b,hy,p,hp⟩ := ih t rfl
      subst y
      refine ⟨b,rfl,.cons (sum_adj_inl.mp e) p,?_⟩
      simp only [Walk.copy_rfl_rfl] at hp
      simp only [Walk.map_cons, Walk.copy_rfl_rfl]
      rw [hp]
      rfl
private theorem lift_right {A B : Type*} {K : SimpleGraph A} {L : SimpleGraph B}
    {x y : A ⊕ B} (w : (K ⊕g L).Walk x y) :
    ∀ a, ∀ hx : x = Sum.inr a, ∃ b, ∃ hy : y = Sum.inr b, ∃ p : L.Walk a b,
      p.map Embedding.sumInr.toHom = w.copy hx hy := by
  induction w with
  | nil =>
    intro a hx
    cases hx
    exact ⟨a,rfl,.nil,rfl⟩
  | @cons x t y e w ih =>
    intro a hx
    subst x
    cases t with
    | inl t => cases e
    | inr t =>
      obtain ⟨b,hy,p,hp⟩ := ih t rfl
      subst y
      refine ⟨b,rfl,.cons (sum_adj_inr.mp e) p,?_⟩
      simp only [Walk.copy_rfl_rfl] at hp
      simp only [Walk.map_cons, Walk.copy_rfl_rfl]
      rw [hp]
      rfl
private theorem no_cycle_sum {A B : Type*} {K : SimpleGraph A} {L : SimpleGraph B}
    (hk : ¬ HasSimpleCycleOfLength K 8) (hl : ¬ HasSimpleCycleOfLength L 8) :
    ¬ HasSimpleCycleOfLength (K ⊕g L) 8 := by
  rintro ⟨x,w,hw,hlen⟩
  cases x with
  | inl a =>
    obtain ⟨b,hb,p,hp⟩ := lift_left w a rfl
    have hab := Sum.inl.inj hb
    subst b
    simp only [Walk.copy_rfl_rfl] at hp
    rw [← hp] at hw hlen
    exact hk ⟨a,p,(Walk.isCycle_map_iff_of_injective Sum.inl_injective).mp hw,
      (Walk.length_map (Embedding.sumInl.toHom : K →g K ⊕g L) p).symm.trans hlen⟩
  | inr a =>
    obtain ⟨b,hb,p,hp⟩ := lift_right w a rfl
    have hab := Sum.inr.inj hb
    subst b
    simp only [Walk.copy_rfl_rfl] at hp
    rw [← hp] at hw hlen
    exact hl ⟨a,p,(Walk.isCycle_map_iff_of_injective Sum.inr_injective).mp hw,
      (Walk.length_map (Embedding.sumInr.toHom : L →g K ⊕g L) p).symm.trans hlen⟩

/-- The exact source has twenty-one undirected edges. -/
theorem h15_card_edgeFinset : h15.edgeFinset.card = 21 := by decide

/-- The two nonempty source constituents have different vertex ranges. -/
theorem h15_constituents_ne : Set.range h15Left ≠ Set.range h15Right := by
  intro he
  have hx : h15Left 0 ∈ Set.range h15Right := he ▸ Set.mem_range_self 0
  exact Set.disjoint_left.mp h15_constituents_disjoint (Set.mem_range_self 0) hx

/-- The actual range of every induced H15 is exactly its two constituent
H7 ranges together with the connector singleton. -/
theorem h15_embedding_range_decomposition {V : Type*} {G : SimpleGraph V}
    (f : h15 ↪g G) : Set.range f =
      Set.range (f.comp h15Left) ∪ Set.range (f.comp h15Right) ∪ {f 14} := by
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    rcases h15_vertex_cases i with ⟨j,rfl⟩ | ⟨j,rfl⟩ | rfl
    · exact Or.inl (Or.inl ⟨j,rfl⟩)
    · exact Or.inl (Or.inr ⟨j,rfl⟩)
    · exact Or.inr rfl
  · rintro ((⟨i,rfl⟩ | ⟨i,rfl⟩) | hx)
    · exact ⟨h15Left i,rfl⟩
    · exact ⟨h15Right i,rfl⟩
    · exact ⟨14,hx.symm⟩

private theorem subcubic_sum {A B : Type*} {K : SimpleGraph A} {L : SimpleGraph B}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [LocallyFinite K] [LocallyFinite L]
    (hk : ∀ v, K.degree v ≤ 3) (hl : ∀ v, L.degree v ≤ 3) :
    ∀ v, (K ⊕g L).degree v ≤ 3 := by
  classical
  intro v
  cases v with
  | inl v =>
    let e : K.neighborSet v ≃ (K ⊕g L).neighborSet (Sum.inl v) :=
      Equiv.ofBijective (fun x => ⟨Sum.inl x.val, x.property⟩) (by
        constructor
        · intro x y h
          apply Subtype.ext
          exact Sum.inl.inj (congrArg Subtype.val h)
        · rintro ⟨x,hx⟩
          cases x with
          | inl x => exact ⟨⟨x,hx⟩,rfl⟩
          | inr x => cases hx)
    rw [← card_neighborSet_eq_degree, ← Fintype.card_congr e, card_neighborSet_eq_degree]
    exact hk v
  | inr v =>
    let e : L.neighborSet v ≃ (K ⊕g L).neighborSet (Sum.inr v) :=
      Equiv.ofBijective (fun x => ⟨Sum.inr x.val, x.property⟩) (by
        constructor
        · intro x y h
          apply Subtype.ext
          exact Sum.inr.inj (congrArg Subtype.val h)
        · rintro ⟨x,hx⟩
          cases x with
          | inr x => exact ⟨⟨x,hx⟩,rfl⟩
          | inl x => cases hx)
    rw [← card_neighborSet_eq_degree, ← Fintype.card_congr e, card_neighborSet_eq_degree]
    exact hl v

/-- The disjoint sum of two exact H15 sources is subcubic. -/
theorem h15_sum_subcubic : ∀ v, (h15 ⊕g h15).degree v ≤ 3 :=
  subcubic_sum h15_subcubic h15_subcubic

/-- Each cycle in the standard H15 disjoint sum stays inside its starting
summand, so the sum has no genuine simple eight-cycle. -/
theorem h15_sum_no_cycle_eight : ¬ HasSimpleCycleOfLength (h15 ⊕g h15) 8 :=
  no_cycle_sum h15_no_cycle_eight h15_no_cycle_eight

/-- Joint satisfiability of subcubicity, genuine no-C8, and the equal-range
branch, on H15 itself, independently of the packing theorem. -/
theorem h15_packing_equal_fixture :
    (∀ v, h15.degree v ≤ 3) ∧ ¬ HasSimpleCycleOfLength h15 8 ∧
    ∃ f g : h15 ↪g h15, Set.range f = Set.range g := by
  refine ⟨h15_subcubic,h15_no_cycle_eight,RelEmbedding.refl _,h15Swap.toEmbedding,?_⟩
  exact (swap_range (RelEmbedding.refl h15.Adj)).symm

/-- Joint satisfiability of subcubicity, genuine no-C8, and the disjoint-range
branch, on two disconnected H15 sources, independently of packing. -/
theorem h15_packing_disjoint_fixture :
    (∀ v, (h15 ⊕g h15).degree v ≤ 3) ∧ ¬ HasSimpleCycleOfLength (h15 ⊕g h15) 8 ∧
    ∃ f g : h15 ↪g (h15 ⊕g h15), Disjoint (Set.range f) (Set.range g) := by
  refine ⟨h15_sum_subcubic,h15_sum_no_cycle_eight,Embedding.sumInl,Embedding.sumInr,?_⟩
  rw [Set.disjoint_left]
  rintro x ⟨i,rfl⟩ ⟨j,hj⟩
  cases hj

/-- The exact H15 and its actual left induced H7 jointly witness the
constituent branch under all ambient hypotheses, independently of packing. -/
theorem h7_h15_constituent_fixture :
    (∀ v, h15.degree v ≤ 3) ∧ ¬ HasSimpleCycleOfLength h15 8 ∧
    ∃ f : h7 ↪g h15, ∃ g : h15 ↪g h15,
      Set.range f = Set.range (g.comp h15Left) := by
  exact ⟨h15_subcubic,h15_no_cycle_eight,h15Left,RelEmbedding.refl _,rfl⟩

/-- A disjoint H7/H15 sum jointly witnesses subcubicity, genuine no-C8,
and disjoint actual mixed ranges, without invoking mixed packing. -/
theorem h7_h15_disjoint_fixture :
    (∀ v, (h7 ⊕g h15).degree v ≤ 3) ∧ ¬ HasSimpleCycleOfLength (h7 ⊕g h15) 8 ∧
    ∃ f : h7 ↪g (h7 ⊕g h15), ∃ g : h15 ↪g (h7 ⊕g h15),
      Disjoint (Set.range f) (Set.range g) := by
  refine ⟨subcubic_sum h7_subcubic h15_subcubic,no_cycle_sum h7_no_cycle_eight h15_no_cycle_eight,
    Embedding.sumInl,Embedding.sumInr,?_⟩
  rw [Set.disjoint_left]
  rintro x ⟨i,rfl⟩ ⟨j,hj⟩
  cases hj

/-- A disjoint symmetric subdivided-K4/H15 sum jointly witnesses the
subcubic-only mixed contract, independently of its disjointness theorem. -/
theorem h7Symm_h15_disjoint_fixture :
    (∀ v, (h7Symm ⊕g h15).degree v ≤ 3) ∧
    ∃ f : h7Symm ↪g (h7Symm ⊕g h15), ∃ g : h15 ↪g (h7Symm ⊕g h15),
      Disjoint (Set.range f) (Set.range g) := by
  refine ⟨subcubic_sum h7Symm_subcubic h15_subcubic,Embedding.sumInl,Embedding.sumInr,?_⟩
  rw [Set.disjoint_left]
  rintro x ⟨i,rfl⟩ ⟨j,hj⟩
  cases hj

end Erdos64.SubcubicFunnel
