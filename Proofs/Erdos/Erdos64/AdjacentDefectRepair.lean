import Erdos.Erdos64.TwoDefectCore
import Erdos.Erdos64.BipartiteRepairResult

set_option autoImplicit false
namespace Erdos64.AdjacentDefectRepair
open SimpleGraph
open scoped Classical

/-- The surviving vertex type after deleting two specified poles. -/
abbrev Remaining {V : Type*} (p q : V) := {v : V // v ≠ p ∧ v ≠ q}

example : Nonempty (Remaining (0 : Fin 3) 1) := ⟨⟨2, by decide⟩⟩

/-- Degree in a two-vertex-deleted induced graph counts exactly the old neighbors
other than the deleted poles. -/
theorem degree_remaining {V : Type*} [Fintype V] (G : SimpleGraph V)
    (p q : V) (v : Remaining p q) :
    (G.induce {x | x ≠ p ∧ x ≠ q}).degree v =
      ((G.neighborFinset v.val).filter (fun x => x ≠ p ∧ x ≠ q)).card := by
  classical
  rw [← card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun x _ => x.val)
  · intro x hx
    have hadj : G.Adj v.val x.val := by simpa using hx
    simpa using ⟨hadj, x.property⟩
  · intro x hx y hy hxy
    exact Subtype.ext hxy
  · intro x hx
    obtain ⟨hadj,hxp,hxq⟩ := by simpa using hx
    exact ⟨⟨x,hxp,hxq⟩, by simpa using hadj, rfl⟩

/-- A degree-two vertex adjacent to a specified neighbor has exactly one other neighbor. -/
theorem exists_other_neighbor {V : Type*} [Fintype V] (G : SimpleGraph V)
    (p q : V) (hpq : G.Adj p q) (hdp : G.degree p = 2) :
    ∃ a, a ≠ q ∧ G.Adj p a ∧ ∀ x, G.Adj p x ↔ x = q ∨ x = a := by
  classical
  have hcard : (G.neighborFinset p).card = 2 := by
    rw [card_neighborFinset_eq_degree]; exact hdp
  obtain ⟨x,y,hxy,hset⟩ := Finset.card_eq_two.mp hcard
  have hqmem : q ∈ G.neighborFinset p := by simpa using hpq
  have hq : q = x ∨ q = y := by simpa [hset] using hqmem
  rcases hq with rfl | rfl
  · refine ⟨y,hxy.symm,?_,?_⟩
    · rw [← mem_neighborFinset, hset]; simp
    · intro z; simp [← mem_neighborFinset, hset]
  · refine ⟨x,hxy,?_,?_⟩
    · rw [← mem_neighborFinset, hset]; simp
    · intro z; simp [← mem_neighborFinset, hset, or_comm]

/-- Four distinct vertices joined cyclically give a genuine cycle of length four. -/
theorem four_cycle {V : Type*} (G : SimpleGraph V) (p a b q : V)
    (hpa : G.Adj p a) (hab : G.Adj a b) (hbq : G.Adj b q) (hqp : G.Adj q p)
    (hpb : p ≠ b) (haq : a ≠ q) :
    ∃ x, ∃ w : G.Walk x x, w.IsCycle ∧ w.length = 4 := by
  let w : G.Walk p p := .cons hpa (.cons hab (.cons hbq (.cons hqp .nil)))
  refine ⟨p,w,?_,rfl⟩
  simp [w, Walk.cons_isCycle_iff, Walk.cons_isPath_iff, Walk.support,
    hpa.ne, hab.ne, hbq.ne, hqp.ne, hpb, haq, hpa.ne.symm, hpb.symm, hqp.ne.symm]

/-- The deleted core loses one neighbor at either surviving port and no neighbors
away from those ports, provided the two deleted degree-two neighbor lists are known. -/
theorem degrees_remaining {V : Type*} [Fintype V] (G : SimpleGraph V)
    (p q a b : V) (hp : ∀ x, G.Adj p x ↔ x = q ∨ x = a)
    (hq : ∀ x, G.Adj q x ↔ x = p ∨ x = b)
    (hap : a ≠ p) (haq : a ≠ q) (hbp : b ≠ p) (hbq : b ≠ q)
    (hab : a ≠ b) :
    (G.induce {x | x ≠ p ∧ x ≠ q}).degree ⟨a,hap,haq⟩ + 1 = G.degree a ∧
    (G.induce {x | x ≠ p ∧ x ≠ q}).degree ⟨b,hbp,hbq⟩ + 1 = G.degree b ∧
    ∀ v : Remaining p q, v.val ≠ a → v.val ≠ b →
      (G.induce {x | x ≠ p ∧ x ≠ q}).degree v = G.degree v.val := by
  classical
  have hpa : G.Adj p a := (hp a).mpr (Or.inr rfl)
  have hqb : G.Adj q b := (hq b).mpr (Or.inr rfl)
  have haq' : ¬ G.Adj a q := by
    intro h
    rcases (hq a).mp h.symm with h | h
    · exact hap h
    · exact hab h
  have hbp' : ¬ G.Adj b p := by
    intro h
    rcases (hp b).mp h.symm with h | h
    · exact hbq h
    · exact hab h.symm
  have haN : (G.neighborFinset a).filter (fun x => x ≠ p ∧ x ≠ q) =
      (G.neighborFinset a).erase p := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase, mem_neighborFinset]
    constructor
    · rintro ⟨hx,hxp,hxq⟩; exact ⟨hxp,hx⟩
    · rintro ⟨hxp,hx⟩; exact ⟨hx,hxp,fun he => haq' (he ▸ hx)⟩
  have hbN : (G.neighborFinset b).filter (fun x => x ≠ p ∧ x ≠ q) =
      (G.neighborFinset b).erase q := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase, mem_neighborFinset]
    constructor
    · rintro ⟨hx,hxp,hxq⟩; exact ⟨hxq,hx⟩
    · rintro ⟨hxq,hx⟩; exact ⟨hx,fun he => hbp' (he ▸ hx),hxq⟩
  refine ⟨?_,?_,?_⟩
  · rw [degree_remaining, haN, Finset.card_erase_of_mem (by simpa using hpa.symm),
      card_neighborFinset_eq_degree]
    have hpos := (G.degree_pos_iff_exists_adj a).mpr ⟨p,hpa.symm⟩
    omega
  · rw [degree_remaining, hbN, Finset.card_erase_of_mem (by simpa using hqb.symm),
      card_neighborFinset_eq_degree]
    have hpos := (G.degree_pos_iff_exists_adj b).mpr ⟨q,hqb.symm⟩
    omega
  · intro v hva hvb
    rw [degree_remaining]
    have hN : (G.neighborFinset v.val).filter (fun x => x ≠ p ∧ x ≠ q) =
        G.neighborFinset v.val := by
      apply Finset.filter_eq_self.mpr
      intro x hx
      have h : G.Adj v.val x := by simpa using hx
      constructor
      · intro he
        have he' := (hp v.val).mp (he ▸ h.symm)
        exact he'.elim v.property.2 hva
      · intro he
        have he' := (hq v.val).mp (he ▸ h.symm)
        exact he'.elim v.property.1 hvb
    rw [hN, card_neighborFinset_eq_degree]

/-- Adjacent degree-two defects can be removed and their other neighbors identified.
The C4 exclusion is used only to certify that the surviving opposite-colored ports
are nonadjacent. The output need not remain bipartite or connected. -/
theorem adjacent_two_defect_repair {V : Type*} [Fintype V]
    (G : SimpleGraph V) (c : V → Bool)
    (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y)
    (hC4 : ¬ ∃ x, ∃ w : G.Walk x x, w.IsCycle ∧ w.length = 4)
    (p q : V) (hpq : G.Adj p q) (hdp : G.degree p = 2) (hdq : G.degree q = 2)
    (hother : ∀ v, v ≠ p → v ≠ q → 3 ≤ G.degree v) :
    Nonempty (BipartiteRepairResult G) := by
  classical
  obtain ⟨a,haq,hpa,hp⟩ := exists_other_neighbor G p q hpq hdp
  obtain ⟨b,hbp,hqb,hq⟩ := exists_other_neighbor G q p hpq.symm hdq
  have hap : a ≠ p := hpa.ne.symm
  have hbq : b ≠ q := hqb.ne.symm
  have hab : a ≠ b := by
    intro he
    have h1 := hc hpq
    have h2 := hc hpa
    have h3 := hc hqb
    subst b
    cases cp : c p <;> cases cq : c q <;> cases ca : c a <;> simp_all
  have hcolor : c a ≠ c b := by
    have h1 := hc hpq
    have h2 := hc hpa
    have h3 := hc hqb
    cases cp : c p <;> cases cq : c q <;> cases ca : c a <;> cases cb : c b <;> simp_all
  have hnon : ¬ G.Adj a b := by
    intro h
    exact hC4 (four_cycle G p a b q hpa h hqb.symm hpq.symm hbp.symm haq)
  let L := G.induce {x | x ≠ p ∧ x ≠ q}
  let A : Remaining p q := ⟨a,hap,haq⟩
  let B : Remaining p q := ⟨b,hbp,hbq⟩
  let d : Remaining p q → Bool := fun v => c v.val
  have hAB : A ≠ B := fun he => hab (congrArg Subtype.val he)
  have hLc : ∀ ⦃x y⦄, L.Adj x y → d x ≠ d y := fun {_ _} h => hc h
  have hLn : ¬ L.Adj A B := hnon
  have hda : L.degree A + 1 = G.degree a := by
    convert (degrees_remaining G p q a b hp hq hap haq hbp hbq hab).1 using 1
  have hdb : L.degree B + 1 = G.degree b := by
    convert (degrees_remaining G p q a b hp hq hap haq hbp hbq hab).2.1 using 1
  have ha3 := hother a hap haq
  have hb3 := hother b hbp hbq
  let Q := BipartiteIdentificationRepair.identifiedGraph L A B hAB
  refine ⟨{
    Vertex := BipartiteIdentificationRepair.IdentifiedVertex B
    vertices := inferInstance
    inhabited := ⟨⟨A,hAB⟩⟩
    graph := Q
    order_le := ?_
    min_degree := ?_
    even_cycles := ?_ }⟩
  · exact (Fintype.card_subtype_le _).trans (Fintype.card_subtype_le _)
  · intro v
    by_cases hv : v.val = A
    · have he : v = ⟨A,hAB⟩ := Subtype.ext hv
      dsimp only [Q]
      rw [he]
      have hdeg : (BipartiteIdentificationRepair.identifiedGraph L A B hAB).degree ⟨A,hAB⟩ =
          L.degree A + L.degree B := by
        convert BipartiteIdentificationRepair.degree_merged L d hLc A B hAB hcolor hLn using 1 <;>
          (congr 2 <;> exact Subsingleton.elim _ _)
      have hsum : 3 ≤ L.degree A + L.degree B := by omega
      have hd : 3 ≤ (BipartiteIdentificationRepair.identifiedGraph L A B hAB).degree ⟨A,hAB⟩ := by
        rw [hdeg]
        convert hsum using 1 <;> (congr 2 <;> exact Subsingleton.elim _ _)
      convert hd using 1
    · dsimp only [Q]
      have hdeg : (BipartiteIdentificationRepair.identifiedGraph L A B hAB).degree v = L.degree v.val := by
        convert BipartiteIdentificationRepair.degree_other L d hLc A B hAB hcolor v hv using 1 <;>
          (congr 1 <;> exact Subsingleton.elim _ _)
      have hva : v.val.val ≠ a := fun he => hv (Subtype.ext he)
      have hvb : v.val.val ≠ b := fun he => v.property (Subtype.ext he)
      have hdv : L.degree v.val = G.degree v.val.val := by
        convert (degrees_remaining G p q a b hp hq hap haq hbp hbq hab).2.2 v.val hva hvb using 1
      have hthree : 3 ≤ L.degree v.val := hdv.symm ▸ hother v.val.val v.val.property.1 v.val.property.2
      have hd : 3 ≤ (BipartiteIdentificationRepair.identifiedGraph L A B hAB).degree v := by
        rw [hdeg]
        convert hthree using 1
      convert hd using 1
  · intro n hn hcycle
    exact TwoDefectCore.cycle_induce_transport G _
      (BipartiteIdentificationRepair.even_cycle_transport L d hLc A B hAB hcolor hLn hn hcycle)

end Erdos64.AdjacentDefectRepair
