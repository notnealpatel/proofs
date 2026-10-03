import Mathlib.Combinatorics.SimpleGraph.Sum
import Erdos.Erdos64.SubcubicFunnelLocal
import Erdos.Erdos64.SubcubicFunnelFixtures
import Erdos.Erdos64.SubcubicFunnelPackingCertificate

set_option autoImplicit false
namespace Erdos64.SubcubicFunnel
open SimpleGraph
universe u
variable {V : Type u} {G : SimpleGraph V}

private theorem pairs_meet [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) {v a b c d : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c) (hd : G.Adj v d)
    (hab : a ≠ b) (hcd : c ≠ d) : a = c ∨ a = d ∨ b = c ∨ b = d := by
  classical
  by_contra hn
  have hdistinct : [a,b,c].Nodup := by simp only [List.nodup_cons,
    List.mem_cons, List.not_mem_nil, not_or, List.nodup_nil, and_true]; tauto
  have he := neighbor_eq_of_three hdeg hdistinct ha hb hc hd
  rcases he with he | he | he <;> grind

private theorem saturated_neighbors [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) (f : h7 ↪g G) (i : Fin 7)
    (hi : i = 2 ∨ i = 3 ∨ i = 5 ∨ i = 6) (x : V) (hx : G.Adj (f i) x) :
    ∃ k, h7.Adj i k ∧ f k = x := by
  have ht : ∀ i : Fin 7, (i = 2 ∨ i = 3 ∨ i = 5 ∨ i = 6) →
      ∃ a b c : Fin 7, [a,b,c].Nodup ∧ h7.Adj i a ∧ h7.Adj i b ∧ h7.Adj i c := by
    decide
  obtain ⟨a,b,c,hd,ha,hb,hc⟩ := ht i hi
  have he := neighbor_eq_of_three hdeg (List.Nodup.map f.injective hd)
    (f.map_rel_iff.mpr ha) (f.map_rel_iff.mpr hb) (f.map_rel_iff.mpr hc) hx
  rcases he with he | he | he
  · exact ⟨a,ha,he.symm⟩
  · exact ⟨b,hb,he.symm⟩
  · exact ⟨c,hc,he.symm⟩

private theorem identification_matrix (f g : Fin 7 → V) :
    ∃ m : BitVec 49, ∀ i j : Fin 7,
      m.getLsbD (7 * i.val + j.val) = true ↔ f i = g j := by
  classical
  let bits := List.ofFn (fun k : Fin 49 =>
    decide (f ⟨k.val / 7, by omega⟩ = g ⟨k.val % 7, by omega⟩))
  let m : BitVec 49 := (BitVec.ofBoolListLE bits).cast (by simp [bits])
  refine ⟨m, ?_⟩
  intro i j
  have hij : 7 * i.val + j.val < 49 := by omega
  suffices he : m.getLsbD (7 * i.val + j.val) = decide (f i = g j) by
    rw [he]; exact decide_eq_true_iff
  simp only [m, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  rw [← List.getElem_eq_getD (h := by simpa [bits] using hij) false]
  simp only [bits, List.getElem_ofFn]
  congr 3 <;> apply Fin.ext <;> dsimp only <;> omega

private theorem no_eight_vertices (h8 : ¬ HasSimpleCycleOfLength G 8)
    (x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ : V)
    (h₀ : G.Adj x₀ x₁) (h₁ : G.Adj x₁ x₂) (h₂ : G.Adj x₂ x₃)
    (h₃ : G.Adj x₃ x₄) (h₄ : G.Adj x₄ x₅) (h₅ : G.Adj x₅ x₆)
    (h₆ : G.Adj x₆ x₇) (h₇ : G.Adj x₇ x₀)
    (hn : [x₀,x₁,x₂,x₃,x₄,x₅,x₆,x₇].Nodup) : False := by
  have hd := hn
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    List.nodup_nil, and_true] at hd
  let p : Path4 G x₀ x₄ := ⟨x₁,x₂,x₃,h₀,h₁,h₂,h₃,by simp [hd]⟩
  let q : Path4 G x₀ x₄ := ⟨x₇,x₆,x₅,h₇.symm,h₆.symm,h₅.symm,h₄.symm,by simp [hd, ne_comm]⟩
  obtain ⟨z,hp,hq⟩ := p.internal_intersects h8 q
  simp only [Path4.Internal, p, q] at hp hq
  grind

private theorem valid_identification [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) (f g : h7 ↪g G) (m : BitVec 49)
    (hm : ∀ i j, PackingCertificate.bit m i j ↔ f i = g j) :
    PackingCertificate.Valid m := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro i j k hij hik
    exact g.injective ((hm i j).mp hij |>.symm.trans ((hm i k).mp hik))
  · intro i j k hij hkj
    exact f.injective (((hm i j).mp hij).trans ((hm k j).mp hkj).symm)
  · intro i k hik j l hij hkl
    have he : G.Adj (g j) (g l) := by
      rw [← (hm i j).mp hij, ← (hm k l).mp hkl]
      exact f.map_rel_iff.mpr hik
    exact g.map_rel_iff.mp he
  · intro i hi j hij l hjl
    have hx : G.Adj (f i) (g l) := by
      rw [(hm i j).mp hij]; exact g.map_rel_iff.mpr hjl
    obtain ⟨k,hik,hk⟩ := saturated_neighbors hdeg f i hi (g l) hx
    exact ⟨k,hik,(hm k l).mpr hk⟩
  · intro j hj i hij k hik
    have hx : G.Adj (g j) (f k) := by
      rw [← (hm i j).mp hij]; exact f.map_rel_iff.mpr hik
    obtain ⟨l,hjl,hl⟩ := saturated_neighbors hdeg g j hj (f k) hx
    exact ⟨l,hjl,(hm k l).mpr hl.symm⟩
  · intro i j hij
    have ht : ∀ i : Fin 7, ∃ a b : Fin 7,
        a ≠ b ∧ h7.Adj i a ∧ h7.Adj i b := by decide
    obtain ⟨a,b,hab,ha,hb⟩ := ht i
    obtain ⟨c,d,hcd,hc,hd⟩ := ht j
    have he : f i = g j := (hm i j).mp hij
    have hmeet := pairs_meet hdeg (f.map_rel_iff.mpr ha) (f.map_rel_iff.mpr hb)
      (he.symm ▸ g.map_rel_iff.mpr hc) (he.symm ▸ g.map_rel_iff.mpr hd)
      (fun h => hab (f.injective h)) (fun h => hcd (g.injective h))
    rcases hmeet with hac | had | hbc | hbd
    · exact Or.inr (Or.inr ⟨a,c,ha,hc,(hm a c).mpr hac⟩)
    · exact Or.inr (Or.inr ⟨a,d,ha,hd,(hm a d).mpr had⟩)
    · exact Or.inr (Or.inr ⟨b,c,hb,hc,(hm b c).mpr hbc⟩)
    · exact Or.inr (Or.inr ⟨b,d,hb,hd,(hm b d).mpr hbd⟩)

private theorem exclude_overlap_0 (f g : h7 ↪g G)
    (h8 : ¬ HasSimpleCycleOfLength G 8)
    (hm : ∀ i j, PackingCertificate.bit (4297129992 : BitVec 49) i j ↔ f i = g j) : False := by
  have e03 : f 0 = g 3 := (hm 0 3).mp (by unfold PackingCertificate.bit; decide)
  have e22 : f 2 = g 2 := (hm 2 2).mp (by unfold PackingCertificate.bit; decide)
  have e30 : f 3 = g 0 := (hm 3 0).mp (by unfold PackingCertificate.bit; decide)
  have e44 : f 4 = g 4 := (hm 4 4).mp (by unfold PackingCertificate.bit; decide)
  apply no_eight_vertices h8 (f 0) (f 2) (f 3) (f 6) (f 5) (f 4) (g 5) (g 6)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 0 2)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 2 3)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 3 6)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 6 5)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 5 4)
  · rw [e44]; exact g.map_rel_iff.mpr (by decide : h7.Adj 4 5)
  · exact g.map_rel_iff.mpr (by decide : h7.Adj 5 6)
  · rw [e03]; exact g.map_rel_iff.mpr (by decide : h7.Adj 6 3)
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      not_or, and_true, f.injective.eq_iff, g.injective.eq_iff, eq_comm, ← hm]
    unfold PackingCertificate.bit
    decide

private theorem exclude_overlap_1 (f g : h7 ↪g G)
    (h8 : ¬ HasSimpleCycleOfLength G 8)
    (hm : ∀ i j, PackingCertificate.bit (4299685952 : BitVec 49) i j ↔ f i = g j) : False := by
  have e06 : f 0 = g 6 := (hm 0 6).mp (by unfold PackingCertificate.bit; decide)
  have e25 : f 2 = g 5 := (hm 2 5).mp (by unfold PackingCertificate.bit; decide)
  have e31 : f 3 = g 1 := (hm 3 1).mp (by unfold PackingCertificate.bit; decide)
  have e44 : f 4 = g 4 := (hm 4 4).mp (by unfold PackingCertificate.bit; decide)
  apply no_eight_vertices h8 (f 0) (f 2) (f 3) (f 6) (f 5) (f 4) (g 2) (g 3)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 0 2)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 2 3)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 3 6)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 6 5)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 5 4)
  · rw [e44]; exact g.map_rel_iff.mpr (by decide : h7.Adj 4 2)
  · exact g.map_rel_iff.mpr (by decide : h7.Adj 2 3)
  · rw [e06]; exact g.map_rel_iff.mpr (by decide : h7.Adj 3 6)
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      not_or, and_true, f.injective.eq_iff, g.injective.eq_iff, eq_comm, ← hm]
    unfold PackingCertificate.bit
    decide

private theorem exclude_overlap_2 (f g : h7 ↪g G)
    (h8 : ¬ HasSimpleCycleOfLength G 8)
    (hm : ∀ i j, PackingCertificate.bit (4539780432896 : BitVec 49) i j ↔ f i = g j) : False := by
  have e13 : f 1 = g 3 := (hm 1 3).mp (by unfold PackingCertificate.bit; decide)
  have e44 : f 4 = g 4 := (hm 4 4).mp (by unfold PackingCertificate.bit; decide)
  have e52 : f 5 = g 2 := (hm 5 2).mp (by unfold PackingCertificate.bit; decide)
  have e60 : f 6 = g 0 := (hm 6 0).mp (by unfold PackingCertificate.bit; decide)
  apply no_eight_vertices h8 (f 0) (f 2) (f 4) (g 5) (g 6) (f 1) (f 6) (f 3)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 0 2)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 2 4)
  · rw [e44]; exact g.map_rel_iff.mpr (by decide : h7.Adj 4 5)
  · exact g.map_rel_iff.mpr (by decide : h7.Adj 5 6)
  · rw [e13]; exact g.map_rel_iff.mpr (by decide : h7.Adj 6 3)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 1 6)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 6 3)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 3 0)
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      not_or, and_true, f.injective.eq_iff, g.injective.eq_iff, eq_comm, ← hm]
    unfold PackingCertificate.bit
    decide

private theorem exclude_overlap_3 (f g : h7 ↪g G)
    (h8 : ¬ HasSimpleCycleOfLength G 8)
    (hm : ∀ i j, PackingCertificate.bit (9899899625472 : BitVec 49) i j ↔ f i = g j) : False := by
  have e16 : f 1 = g 6 := (hm 1 6).mp (by unfold PackingCertificate.bit; decide)
  have e44 : f 4 = g 4 := (hm 4 4).mp (by unfold PackingCertificate.bit; decide)
  have e55 : f 5 = g 5 := (hm 5 5).mp (by unfold PackingCertificate.bit; decide)
  have e61 : f 6 = g 1 := (hm 6 1).mp (by unfold PackingCertificate.bit; decide)
  apply no_eight_vertices h8 (f 0) (f 2) (f 4) (g 2) (g 3) (f 1) (f 6) (f 3)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 0 2)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 2 4)
  · rw [e44]; exact g.map_rel_iff.mpr (by decide : h7.Adj 4 2)
  · exact g.map_rel_iff.mpr (by decide : h7.Adj 2 3)
  · rw [e16]; exact g.map_rel_iff.mpr (by decide : h7.Adj 3 6)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 1 6)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 6 3)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 3 0)
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      not_or, and_true, f.injective.eq_iff, g.injective.eq_iff, eq_comm, ← hm]
    unfold PackingCertificate.bit
    decide

private theorem exclude_overlap_4 (f g : h7 ↪g G)
    (h8 : ¬ HasSimpleCycleOfLength G 8)
    (hm : ∀ i j, PackingCertificate.bit (281543712985092 : BitVec 49) i j ↔ f i = g j) : False := by
  have e02 : f 0 = g 2 := (hm 0 2).mp (by unfold PackingCertificate.bit; decide)
  have e15 : f 1 = g 5 := (hm 1 5).mp (by unfold PackingCertificate.bit; decide)
  have e20 : f 2 = g 0 := (hm 2 0).mp (by unfold PackingCertificate.bit; decide)
  have e33 : f 3 = g 3 := (hm 3 3).mp (by unfold PackingCertificate.bit; decide)
  have e51 : f 5 = g 1 := (hm 5 1).mp (by unfold PackingCertificate.bit; decide)
  have e66 : f 6 = g 6 := (hm 6 6).mp (by unfold PackingCertificate.bit; decide)
  apply no_eight_vertices h8 (f 0) (f 3) (f 2) (f 4) (f 5) (f 6) (f 1) (g 4)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 0 3)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 3 2)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 2 4)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 4 5)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 5 6)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 6 1)
  · rw [e15]; exact g.map_rel_iff.mpr (by decide : h7.Adj 5 4)
  · rw [e02]; exact g.map_rel_iff.mpr (by decide : h7.Adj 4 2)
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      not_or, and_true, f.injective.eq_iff, eq_comm, ← hm]
    unfold PackingCertificate.bit
    decide

private theorem exclude_overlap_5 (f g : h7 ↪g G)
    (h8 : ¬ HasSimpleCycleOfLength G 8)
    (hm : ∀ i j, PackingCertificate.bit (35218866078240 : BitVec 49) i j ↔ f i = g j) : False := by
  have e05 : f 0 = g 5 := (hm 0 5).mp (by unfold PackingCertificate.bit; decide)
  have e12 : f 1 = g 2 := (hm 1 2).mp (by unfold PackingCertificate.bit; decide)
  have e21 : f 2 = g 1 := (hm 2 1).mp (by unfold PackingCertificate.bit; decide)
  have e36 : f 3 = g 6 := (hm 3 6).mp (by unfold PackingCertificate.bit; decide)
  have e50 : f 5 = g 0 := (hm 5 0).mp (by unfold PackingCertificate.bit; decide)
  have e63 : f 6 = g 3 := (hm 6 3).mp (by unfold PackingCertificate.bit; decide)
  apply no_eight_vertices h8 (f 0) (f 3) (f 2) (f 4) (f 5) (f 6) (f 1) (g 4)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 0 3)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 3 2)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 2 4)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 4 5)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 5 6)
  · exact f.map_rel_iff.mpr (by decide : h7.Adj 6 1)
  · rw [e12]; exact g.map_rel_iff.mpr (by decide : h7.Adj 2 4)
  · rw [e05]; exact g.map_rel_iff.mpr (by decide : h7.Adj 4 5)
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      not_or, and_true, f.injective.eq_iff, eq_comm, ← hm]
    unfold PackingCertificate.bit
    decide

/-- The disjoint union of two H7 graphs has no genuine simple eight-cycle.
Each walk stays in its starting summand, which has only seven vertices. -/
theorem h7_sum_no_cycle_eight : ¬ HasSimpleCycleOfLength (h7 ⊕g h7) 8 := by
  classical
  rintro ⟨v,w,hw,hl⟩
  cases v with
  | inl v =>
    have hs : w.support.tail ⊆ (List.finRange 7).map (Sum.inl : Fin 7 → Fin 7 ⊕ Fin 7) := by
      intro z hz
      have hz' := List.mem_of_mem_tail hz
      cases z with
      | inl z => simp
      | inr z => exact (not_reachable_sum_inl_inr v z (w.takeUntil _ hz').reachable).elim
    have hn := hw.support_nodup.length_le_of_subset hs
    have hlen := w.length_support
    simp only [List.length_tail, List.length_map, List.length_finRange] at hn
    omega
  | inr v =>
    have hs : w.support.tail ⊆ (List.finRange 7).map (Sum.inr : Fin 7 → Fin 7 ⊕ Fin 7) := by
      intro z hz
      have hz' := List.mem_of_mem_tail hz
      cases z with
      | inr z => simp
      | inl z => exact (not_reachable_sum_inl_inr z v (w.takeUntil _ hz').reachable.symm).elim
    have hn := hw.support_nodup.length_le_of_subset hs
    have hlen := w.length_support
    simp only [List.length_tail, List.length_map, List.length_finRange] at hn
    omega

/-- Jointly satisfiable degree, no-C8, and equal-range hypotheses with two
actual standard induced embeddings on the seven-vertex H7 graph. -/
theorem h7_packing_equal_fixture :
    (∀ v, h7.degree v ≤ 3) ∧ ¬ HasSimpleCycleOfLength h7 8 ∧
    ∃ f g : h7 ↪g h7, Set.range f = Set.range g := by
  exact ⟨h7_subcubic, h7_no_cycle_eight, RelEmbedding.refl _, RelEmbedding.refl _, rfl⟩

/-- Both summands of the disjoint union retain their standard H7 degrees. -/
theorem h7_sum_subcubic : ∀ v, (h7 ⊕g h7).degree v ≤ 3 := by
  classical
  intro v
  cases v with
  | inl v =>
    let e : h7.neighborSet v ≃ (h7 ⊕g h7).neighborSet (Sum.inl v) :=
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
    exact h7_subcubic v
  | inr v =>
    let e : h7.neighborSet v ≃ (h7 ⊕g h7).neighborSet (Sum.inr v) :=
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
    exact h7_subcubic v

/-- Jointly satisfiable degree, no-C8, and disjoint-range hypotheses with the
two summand embeddings of a disconnected, fourteen-vertex standard graph. -/
theorem h7_packing_disjoint_fixture :
    (∀ v, (h7 ⊕g h7).degree v ≤ 3) ∧ ¬ HasSimpleCycleOfLength (h7 ⊕g h7) 8 ∧
    ∃ f g : h7 ↪g (h7 ⊕g h7), Disjoint (Set.range f) (Set.range g) := by
  refine ⟨h7_sum_subcubic, h7_sum_no_cycle_eight, Embedding.sumInl, Embedding.sumInr, ?_⟩
  rw [Set.disjoint_left]
  rintro x ⟨i,rfl⟩ ⟨j,hj⟩
  cases hj

private theorem range_eq_of_full_identification (f g : h7 ↪g G) (m : BitVec 49)
    (hm : ∀ i j, PackingCertificate.bit m i j ↔ f i = g j)
    (hr : ∀ i, ∃ j, PackingCertificate.bit m i j)
    (hc : ∀ j, ∃ i, PackingCertificate.bit m i j) :
    Set.range f = Set.range g := by
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    obtain ⟨j,hj⟩ := hr i
    exact ⟨j,((hm i j).mp hj).symm⟩
  · rintro ⟨j,rfl⟩
    obtain ⟨i,hi⟩ := hc j
    exact ⟨i,(hm i j).mp hi⟩

/-- In a finite subcubic graph with no genuine simple eight-cycle, the actual
vertex ranges of any two standard induced H7 embeddings are equal or disjoint.
No exclusion of four-cycles or connectedness assumption is required. -/
theorem h7_embedding_ranges_eq_or_disjoint [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) (h8 : ¬ HasSimpleCycleOfLength G 8)
    (f g : h7 ↪g G) : Set.range f = Set.range g ∨ Disjoint (Set.range f) (Set.range g) := by
  obtain ⟨m,hm⟩ := identification_matrix f g
  have hv := valid_identification hdeg f g m hm
  rcases PackingCertificate.classify m hv with h | h | h | h | h | h | h | h | h
  · subst m
    right
    rw [Set.disjoint_left]
    rintro x ⟨i,rfl⟩ ⟨j,hj⟩
    have hb := (hm i j).mpr hj.symm
    simp at hb
  · subst m
    exact (exclude_overlap_0 f g h8 hm).elim
  · subst m
    exact (exclude_overlap_1 f g h8 hm).elim
  · subst m
    exact (exclude_overlap_2 f g h8 hm).elim
  · subst m
    exact (exclude_overlap_3 f g h8 hm).elim
  · subst m
    exact (exclude_overlap_4 f g h8 hm).elim
  · subst m
    exact (exclude_overlap_5 f g h8 hm).elim
  · subst m
    left
    apply range_eq_of_full_identification f g _ hm
    · unfold PackingCertificate.bit; decide
    · unfold PackingCertificate.bit; decide
  · subst m
    left
    apply range_eq_of_full_identification f g _ hm
    · unfold PackingCertificate.bit; decide
    · unfold PackingCertificate.bit; decide

/-- A shared ambient vertex forces equality of the two induced H7 vertex
ranges in a finite subcubic graph without a genuine simple eight-cycle. -/
theorem h7_embedding_ranges_eq_of_shared_vertex [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) (h8 : ¬ HasSimpleCycleOfLength G 8)
    (f g : h7 ↪g G) {x : V} (hf : x ∈ Set.range f) (hg : x ∈ Set.range g) :
    Set.range f = Set.range g := by
  rcases h7_embedding_ranges_eq_or_disjoint hdeg h8 f g with he | hd
  · exact he
  · exact (Set.disjoint_left.mp hd hf hg).elim

end Erdos64.SubcubicFunnel
