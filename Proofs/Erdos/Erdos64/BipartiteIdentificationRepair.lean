/-
Opposite-class nonadjacent identification case of the internal reviewed informal
bipartite repair argument (BIPARTITE-SIDE-ELIMINATION.md and
BIPARTITE-REPAIR-REVIEW.md). No novelty or general E64 closure is claimed.
-/
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Finite

set_option autoImplicit false

namespace Erdos64.BipartiteIdentificationRepair
open SimpleGraph
open scoped Classical

/-- Vertex set after deleting the second pole; the first pole represents both poles. -/
abbrev IdentifiedVertex {V : Type*} (q : V) := {v : V // v ≠ q}

/-- Identification map, sending the second pole to the first pole. -/
noncomputable def identify {V : Type*} (p q : V) (hpq : p ≠ q) (v : V) :
    IdentifiedVertex q := if h : v = q then ⟨p, hpq⟩ else ⟨v, h⟩

example : identify (0 : Fin 2) 1 (by decide) 1 = ⟨0, by decide⟩ := by
  simp [identify]
example : identify (0 : Fin 2) 1 (by decide) 0 = ⟨0, by decide⟩ := by
  simp [identify]

/-- Simple identification graph: adjacency has original edge witnesses and excludes loops. -/
noncomputable def identifiedGraph {V : Type*} (G : SimpleGraph V)
    (p q : V) (hpq : p ≠ q) : SimpleGraph (IdentifiedVertex q) where
  Adj a b := a ≠ b ∧ ∃ x y, G.Adj x y ∧ identify p q hpq x = a ∧ identify p q hpq y = b
  symm := ⟨by
    rintro a b ⟨hne, x, y, hxy, hx, hy⟩
    exact ⟨hne.symm, y, x, hxy.symm, hy, hx⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

example : ¬ (identifiedGraph (⊥ : SimpleGraph (Fin 2)) 0 1 (by decide)).Adj
    ⟨0, by decide⟩ ⟨0, by decide⟩ := by simp [identifiedGraph]

private theorem identify_of_ne {V : Type*} (p q : V) (hpq : p ≠ q)
    (a : IdentifiedVertex q) (ha : a.val ≠ p) {x : V}
    (hx : identify p q hpq x = a) : x = a.val := by
  by_cases h : x = q
  · simp only [identify, h, ↓reduceDIte] at hx
    exact False.elim (ha (congrArg Subtype.val hx).symm)
  · simpa [identify, h] using congrArg Subtype.val hx

private theorem lift_avoiding_tail {V : Type*} (G : SimpleGraph V)
    (p q : V) (hpq : p ≠ q) {a b : IdentifiedVertex q}
    (w : (identifiedGraph G p q hpq).Walk a b)
    (havoid : ∀ z ∈ w.support.tail, z.val ≠ p) :
    ∃ x y, ∃ t : G.Walk x y,
      identify p q hpq x = a ∧ identify p q hpq y = b ∧
      t.length = w.length ∧ t.support.map (identify p q hpq) = w.support := by
  induction w with
  | @nil a =>
    refine ⟨a.val, a.val, .nil, ?_, ?_, rfl, ?_⟩ <;> simp [identify, a.property]
  | @cons a b d hab w ih =>
    obtain ⟨x, y, hxy, hx, hy⟩ := hab.2
    have hb : b.val ≠ p := havoid b (by simp)
    have hw : ∀ z ∈ w.support.tail, z.val ≠ p := by
      intro z hz
      exact havoid z (by simpa using List.mem_of_mem_tail hz)
    obtain ⟨s, t, r, hs, ht, hlen, hsupp⟩ := ih hw
    have hys : y = s := (identify_of_ne p q hpq b hb hy).trans
      (identify_of_ne p q hpq b hb hs).symm
    subst s
    refine ⟨x, t, .cons hxy r, hx, ht, ?_, ?_⟩
    · simp [hlen]
    · simp [hsupp, hx]

private theorem walk_parity {V : Type*} (G : SimpleGraph V) (c : V → Bool)
    (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y)
    {x y : V} (w : G.Walk x y) :
    w.length % 2 = if c x = c y then 0 else 1 := by
  induction w with
  | nil => simp
  | @cons x z y h w ih =>
    have hxz := hc h
    simp only [Walk.length_cons]
    cases hx : c x <;> cases hz : c z <;> cases hy : c y <;> simp_all <;> omega

private theorem fiber_merged {V : Type*} (p q : V) (hpq : p ≠ q) {x : V}
    (hx : identify p q hpq x = (⟨p, hpq⟩ : IdentifiedVertex q)) : x = p ∨ x = q := by
  by_cases h : x = q
  · exact Or.inr h
  · exact Or.inl (by simpa [identify, h] using congrArg Subtype.val hx)

private theorem cycle_at_merged {V : Type*} (G : SimpleGraph V) (c : V → Bool)
    (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y)
    (p q : V) (hpq : p ≠ q) (hcolor : c p ≠ c q)
    (w : (identifiedGraph G p q hpq).Walk ⟨p, hpq⟩ ⟨p, hpq⟩)
    (hw : w.IsCycle) (heven : Even w.length) :
    ∃ x, ∃ r : G.Walk x x, r.IsCycle ∧ r.length = w.length := by
  cases w with
  | nil => exact False.elim (Walk.not_isCycle_nil hw)
  | @cons a b d h t =>
    have htpath : t.IsPath := (Walk.cons_isCycle_iff t h).mp hw |>.1
    have hb : b.val ≠ p := by
      intro hb
      have heq : b = (⟨p, hpq⟩ : IdentifiedVertex q) := Subtype.ext hb
      exact h.ne heq.symm
    have hnodup : t.reverse.support.Nodup := htpath.reverse.support_nodup
    rw [← t.reverse.cons_tail_support] at hnodup
    have havoid : ∀ z ∈ t.reverse.support.tail, z.val ≠ p := by
      have hm : (⟨p, hpq⟩ : IdentifiedVertex q) ∉ t.reverse.support.tail :=
        (List.nodup_cons.mp hnodup).1
      intro z hz hzp
      exact hm ((Subtype.ext hzp : z = ⟨p, hpq⟩) ▸ hz)
    obtain ⟨x, y, r, hx, hy, hlen, hsupp⟩ := lift_avoiding_tail G p q hpq t.reverse havoid
    obtain ⟨s, z, hsz, hs, hz⟩ := h.2
    have hzy : z = y := (identify_of_ne p q hpq b hb hz).trans
      (identify_of_ne p q hpq b hb hy).symm
    subst z
    let W : G.Walk s x := .cons hsz r.reverse
    have hlength : W.length = (Walk.cons h t).length := by
      simp [W, hlen]
    have hpar := walk_parity G c hc W
    have hmod : W.length % 2 = 0 := by
      obtain ⟨k, hk⟩ := heven
      rw [hlength, hk]
      omega
    have hcx : c s = c x := by
      split_ifs at hpar with hh
      · exact hh
      · omega
    have hsx : s = x := by
      rcases fiber_merged p q hpq hs with hsp | hsq <;>
        rcases fiber_merged p q hpq hx with hxp | hxq
      · exact hsp.trans hxp.symm
      · exact False.elim (hcolor (hsp ▸ hxq ▸ hcx))
      · exact False.elim (hcolor (hxp ▸ hsq ▸ hcx.symm))
      · exact hsq.trans hxq.symm
    subst s
    have hrpath : r.IsPath := by
      apply (Walk.isPath_def r).mpr
      apply List.Nodup.of_map (identify p q hpq)
      rw [hsupp]
      exact htpath.reverse.support_nodup
    refine ⟨x, W, ?_, hlength⟩
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    exact ⟨by simpa [W] using hrpath.reverse, hlength ▸ hw.three_le_length⟩

/-- Every even simple cycle after identification of opposite-colored nonadjacent poles
has a genuine simple cycle of exactly the same length in the input graph. The result
is unconditional: no connectivity, finiteness, regularity, or C4 restriction is used.
This formalizes the identification case in the internal reviewed repair report. -/
theorem even_cycle_transport {V : Type*} (G : SimpleGraph V) (c : V → Bool)
    (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y)
    (p q : V) (hpq : p ≠ q) (hcolor : c p ≠ c q) (_hnadj : ¬ G.Adj p q)
    {n : ℕ} (hn : Even n)
    (h : ∃ a, ∃ w : (identifiedGraph G p q hpq).Walk a a,
      w.IsCycle ∧ w.length = n) :
    ∃ x, ∃ r : G.Walk x x, r.IsCycle ∧ r.length = n := by
  classical
  obtain ⟨a, w, hw, hlen⟩ := h
  let m : IdentifiedVertex q := ⟨p, hpq⟩
  by_cases hm : m ∈ w.support
  · obtain ⟨x, r, hr, hrl⟩ := cycle_at_merged G c hc p q hpq hcolor
      (w.rotate m hm) (hw.rotate hm) (by rw [Walk.length_rotate, hlen]; exact hn)
    exact ⟨x, r, hr, hrl.trans ((w.length_rotate m hm).trans hlen)⟩
  · have havoid : ∀ z ∈ w.support.tail, z.val ≠ p := by
      intro z hz hzp
      exact hm ((Subtype.ext hzp : z = m) ▸ List.mem_of_mem_tail hz)
    obtain ⟨x, y, r, hx, hy, hrl, hrs⟩ := lift_avoiding_tail G p q hpq w havoid
    have ha : a.val ≠ p := by
      intro hap
      exact hm ((Subtype.ext hap : a = m) ▸ w.start_mem_support)
    have hxy : x = y := (identify_of_ne p q hpq a ha hx).trans
      (identify_of_ne p q hpq a ha hy).symm
    subst y
    have hrnodup : r.support.tail.Nodup := by
      apply List.Nodup.of_map (identify p q hpq)
      have htail : r.support.tail.map (identify p q hpq) = w.support.tail := by
        cases hlist : r.support <;> simpa [hlist] using congrArg List.tail hrs
      rw [htail]
      exact hw.support_nodup
    have hrpath : r.tail.IsPath := by
      apply (Walk.isPath_def _).mpr
      rw [Walk.support_tail_of_not_nil r]
      · exact hrnodup
      · intro hz
        have hzero : r.length = 0 := Walk.length_eq_zero_iff.mpr hz
        have hthree := hw.three_le_length
        omega
    exact ⟨x, r, Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      ⟨hrpath, hrl ▸ hw.three_le_length⟩, hrl.trans hlen⟩

private theorem adj_merged {V : Type*} (G : SimpleGraph V) (p q : V)
    (hpq : p ≠ q) (hnadj : ¬ G.Adj p q) (b : IdentifiedVertex q) :
    (identifiedGraph G p q hpq).Adj ⟨p, hpq⟩ b ↔
      ∃ z, (G.Adj p z ∨ G.Adj q z) ∧ identify p q hpq z = b := by
  constructor
  · rintro ⟨_, x, y, hxy, hx, hy⟩
    rcases fiber_merged p q hpq hx with rfl | rfl
    · exact ⟨y, Or.inl hxy, hy⟩
    · exact ⟨y, Or.inr hxy, hy⟩
  · rintro ⟨z, hz, rfl⟩
    have hne : (⟨p, hpq⟩ : IdentifiedVertex q) ≠ identify p q hpq z := by
      intro heq
      rcases fiber_merged p q hpq heq.symm with rfl | rfl <;>
        rcases hz with hz | hz
      · exact hz.ne rfl
      · exact hnadj hz.symm
      · exact hnadj hz
      · exact hz.ne rfl
    refine ⟨hne, ?_⟩
    rcases hz with hz | hz
    · exact ⟨p, z, hz, by simp [identify, hpq], rfl⟩
    · exact ⟨q, z, hz, by simp [identify], rfl⟩

private theorem adj_other {V : Type*} (G : SimpleGraph V) (p q : V)
    (hpq : p ≠ q) (a b : IdentifiedVertex q) (ha : a.val ≠ p) :
    (identifiedGraph G p q hpq).Adj a b ↔
      ∃ z, G.Adj a.val z ∧ identify p q hpq z = b := by
  constructor
  · rintro ⟨_, x, y, hxy, hx, hy⟩
    have hxa := identify_of_ne p q hpq a ha hx
    exact ⟨y, hxa ▸ hxy, hy⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨?_, a.val, z, hz, by simp [identify, a.property], rfl⟩
    intro heq
    exact hz.ne (identify_of_ne p q hpq a ha heq.symm).symm

/-- The merged vertex has degree equal to the sum of the original pole degrees.
Opposite colors and nonadjacency prevent common neighbors and loss of edges. -/
theorem degree_merged {V : Type*} [Fintype V] (G : SimpleGraph V) (c : V → Bool)
    (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y)
    (p q : V) (hpq : p ≠ q) (hcolor : c p ≠ c q) (hnadj : ¬ G.Adj p q) :
    (identifiedGraph G p q hpq).degree ⟨p, hpq⟩ = G.degree p + G.degree q := by
  classical
  let S := G.neighborFinset p ∪ G.neighborFinset q
  have hS : ∀ z ∈ S, z ≠ q := by
    intro z hz
    simp only [S, Finset.mem_union, mem_neighborFinset] at hz
    rcases hz with hz | hz
    · exact fun heq => hnadj (heq ▸ hz)
    · exact hz.ne.symm
  have hinj : Set.InjOn (identify p q hpq) S := by
    intro x hx y hy hxy
    simpa [identify, hS x hx, hS y hy] using congrArg Subtype.val hxy
  have hneighbors : (identifiedGraph G p q hpq).neighborFinset ⟨p, hpq⟩ =
      S.image (identify p q hpq) := by
    ext b
    simp only [mem_neighborFinset, adj_merged G p q hpq hnadj,
      Finset.mem_image, S, Finset.mem_union, mem_neighborFinset]
  have hdis : Disjoint (G.neighborFinset p) (G.neighborFinset q) := by
    apply Finset.disjoint_left.mpr
    intro z hzp hzq
    have hpz := hc (show G.Adj p z from by simpa only [mem_neighborFinset] using hzp)
    have hqz := hc (show G.Adj q z from by simpa only [mem_neighborFinset] using hzq)
    cases cp : c p <;> cases cq : c q <;> cases cz : c z <;> simp_all
  rw [← card_neighborFinset_eq_degree, hneighbors, Finset.card_image_of_injOn hinj]
  simp only [S]
  rw [Finset.card_union_of_disjoint hdis,
    card_neighborFinset_eq_degree, card_neighborFinset_eq_degree]

/-- Every vertex other than the merged vertex retains its original degree. -/
theorem degree_other {V : Type*} [Fintype V] (G : SimpleGraph V) (c : V → Bool)
    (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y)
    (p q : V) (hpq : p ≠ q) (hcolor : c p ≠ c q)
    (a : IdentifiedVertex q) (ha : a.val ≠ p) :
    (identifiedGraph G p q hpq).degree a = G.degree a.val := by
  classical
  have hinj : Set.InjOn (identify p q hpq) (G.neighborFinset a.val) := by
    intro x hx y hy hxy
    have hax := hc (show G.Adj a.val x from by simpa only [Finset.mem_coe, mem_neighborFinset] using hx)
    have hay := hc (show G.Adj a.val y from by simpa only [Finset.mem_coe, mem_neighborFinset] using hy)
    by_cases hxq : x = q <;> by_cases hyq : y = q
    · exact hxq.trans hyq.symm
    · have hyp : y = p := by simpa [identify, hxq, hyq] using
        (congrArg Subtype.val hxy).symm
      subst x
      subst y
      cases ca : c a.val <;> cases cp : c p <;> cases cq : c q <;> simp_all
    · have hxp : x = p := by simpa [identify, hxq, hyq] using congrArg Subtype.val hxy
      subst x
      subst y
      cases ca : c a.val <;> cases cp : c p <;> cases cq : c q <;> simp_all
    · simpa [identify, hxq, hyq] using congrArg Subtype.val hxy
  have hneighbors : (identifiedGraph G p q hpq).neighborFinset a =
      (G.neighborFinset a.val).image (identify p q hpq) := by
    ext b
    simp only [mem_neighborFinset, adj_other G p q hpq a b ha,
      Finset.mem_image, mem_neighborFinset]
  rw [← card_neighborFinset_eq_degree, hneighbors, Finset.card_image_of_injOn hinj,
    card_neighborFinset_eq_degree]

/- Joint satisfiability: K3,3 minus the edge 0-3. Exactly the opposite-class,
nonadjacent poles 0 and 3 have degree two; other vertices have degree three.
The input and the quotient both contain the simple even cycle 1-4-2-5-1. -/
example : ∃ (G : SimpleGraph (Fin 6)) (c : Fin 6 → Bool)
    (_ : DecidableRel G.Adj),
    (∀ x y, G.Adj x y → c x ≠ c y) ∧ c 0 ≠ c 3 ∧
    (0 : Fin 6) ≠ 3 ∧ ¬ G.Adj 0 3 ∧ G.degree 0 = 2 ∧ G.degree 3 = 2 ∧
    (∀ v, v ≠ 0 → v ≠ 3 → 3 ≤ G.degree v) ∧
    (∃ w : (identifiedGraph G 0 3 (by decide)).Walk
        ⟨1, by decide⟩ ⟨1, by decide⟩, w.IsCycle ∧ w.length = 4) := by
  let G : SimpleGraph (Fin 6) := fromRel fun x y =>
    x.val < 3 ∧ 3 ≤ y.val ∧ ¬ (x = 0 ∧ y = 3)
  let c : Fin 6 → Bool := fun x => decide (x.val < 3)
  refine ⟨G, c, (by dsimp [G]; infer_instance), ?_⟩
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  let H := identifiedGraph G 0 3 (by decide)
  have hedge (x y : Fin 6) (hx : x ≠ 3) (hy : y ≠ 3) (hne : x ≠ y)
      (hxy : G.Adj x y) : H.Adj ⟨x, hx⟩ ⟨y, hy⟩ := by
    refine ⟨fun h => hne (congrArg Subtype.val h), x, y, hxy, ?_, ?_⟩ <;>
      simp [identify, hx, hy]
  let w : H.Walk ⟨1, by decide⟩ ⟨1, by decide⟩ :=
    .cons (hedge 1 4 (by decide) (by decide) (by decide) (by decide))
      (.cons (hedge 4 2 (by decide) (by decide) (by decide) (by decide))
        (.cons (hedge 2 5 (by decide) (by decide) (by decide) (by decide))
          (.cons (hedge 5 1 (by decide) (by decide) (by decide) (by decide)) .nil)))
  refine ⟨w, ?_, rfl⟩
  simp [w, Walk.cons_isCycle_iff, Walk.cons_isPath_iff, Walk.support]

/-- Identification removes exactly one vertex. The explicit vertex `q` witnesses
positive input order, so the natural-number subtraction does not truncate. -/
theorem card_identifiedVertex {V : Type*} [Fintype V] (q : V) :
    Fintype.card (IdentifiedVertex q) = Fintype.card V - 1 := by
  classical
  simp [Fintype.card_subtype_compl (fun v : V => v = q)]

/-- Terminal opposite-class nonadjacent two-defect repair. The quotient is nonempty,
has merged degree four and minimum degree three, has one fewer vertex, and transports
all even genuine simple cycles to same-length genuine simple input cycles. This is
Case 2b of the internal reviewed informal report, not a proof of E64 or of pruning. -/
theorem opposite_class_two_defect_repair {V : Type*} [Fintype V]
    (G : SimpleGraph V) (c : V → Bool)
    (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y)
    (p q : V) (hpq : p ≠ q) (hcolor : c p ≠ c q) (hnadj : ¬ G.Adj p q)
    (hdp : G.degree p = 2) (hdq : G.degree q = 2)
    (hother : ∀ v, v ≠ p → v ≠ q → 3 ≤ G.degree v) :
    Nonempty (IdentifiedVertex q) ∧
      (identifiedGraph G p q hpq).degree ⟨p, hpq⟩ = 4 ∧
      (∀ a, 3 ≤ (identifiedGraph G p q hpq).degree a) ∧
      Fintype.card (IdentifiedVertex q) = Fintype.card V - 1 ∧
      (∀ n : ℕ, Even n →
        (∃ a, ∃ w : (identifiedGraph G p q hpq).Walk a a,
          w.IsCycle ∧ w.length = n) →
        ∃ x, ∃ r : G.Walk x x, r.IsCycle ∧ r.length = n) := by
  classical
  have hmerged : (identifiedGraph G p q hpq).degree ⟨p, hpq⟩ = 4 := by
    rw [degree_merged G c hc p q hpq hcolor hnadj, hdp, hdq]
  refine ⟨⟨⟨p, hpq⟩⟩, hmerged, ?_, card_identifiedVertex q, ?_⟩
  · intro a
    by_cases ha : a.val = p
    · have heq : a = (⟨p, hpq⟩ : IdentifiedVertex q) := Subtype.ext ha
      rw [heq, hmerged]
      decide
    · rw [degree_other G c hc p q hpq hcolor a ha]
      exact hother a.val ha a.property
  · intro n hn hcycle
    exact even_cycle_transport G c hc p q hpq hcolor hnadj hn hcycle

/- Applying the terminal theorem to the same computable fixture explicitly reconciles
its neighbor-set Fintype instances with the classical instances in theorem statements. -/
example : ∃ G : SimpleGraph (Fin 6),
    (identifiedGraph G 0 3 (by decide)).degree ⟨0, by decide⟩ = 4 ∧
    ∀ a, 3 ≤ (identifiedGraph G 0 3 (by decide)).degree a := by
  let G : SimpleGraph (Fin 6) := fromRel fun x y =>
    x.val < 3 ∧ 3 ≤ y.val ∧ ¬ (x = 0 ∧ y = 3)
  let c : Fin 6 → Bool := fun x => decide (x.val < 3)
  letI : DecidableRel G.Adj := by dsimp [G]; infer_instance
  have hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y := by decide
  have hd0 : G.degree 0 = 2 := by decide
  have hd3 : G.degree 3 = 2 := by decide
  have hother : ∀ v, v ≠ 0 → v ≠ 3 → 3 ≤ G.degree v := by decide
  have hr := opposite_class_two_defect_repair G c hc 0 3 (by decide)
    (by decide) (by decide)
    (by convert hd0 using 1; congr 1; exact Subsingleton.elim _ _)
    (by convert hd3 using 1; congr 1; exact Subsingleton.elim _ _)
    (by
      intro v hv0 hv3
      convert hother v hv0 hv3 using 1
      congr 1
      exact Subsingleton.elim _ _)
  refine ⟨G, ?_, ?_⟩
  · convert hr.2.1 using 1
    congr 1
    exact Subsingleton.elim _ _
  · intro a
    convert hr.2.2.1 a using 1
    congr 1
    exact Subsingleton.elim _ _

end Erdos64.BipartiteIdentificationRepair
