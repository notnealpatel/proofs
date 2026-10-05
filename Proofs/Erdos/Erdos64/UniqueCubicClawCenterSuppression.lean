import Erdos.Erdos64.UniqueCubicClawCenter
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

namespace Erdos64.UniqueCubicClawCenter

open SimpleGraph

universe u

/-- The vertices retained by suppression are exactly the original degree-three vertices. -/
abbrev SuppressionNode {W : Type u} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] := {x : W // H.degree x = 3}

/-- Suppression retains direct edges and replaces a two-edge corridor through a
single degree-two vertex by an edge. Distinct endpoints are required explicitly. -/
def suppression {W : Type u} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj] :
    SimpleGraph (SuppressionNode H) where
  Adj x y := x ≠ y ∧ (H.Adj x.val y.val ∨
    ∃ m : W, H.degree m = 2 ∧ H.Adj x.val m ∧ H.Adj m y.val)
  symm := ⟨by
    rintro x y ⟨hne, hdir | ⟨m, hm, hxm, hmy⟩⟩
    · exact ⟨hne.symm, Or.inl hdir.symm⟩
    · exact ⟨hne.symm, Or.inr ⟨m, hm, hmy.symm, hxm.symm⟩⟩⟩
  loopless := ⟨by rintro x ⟨hne, _⟩; exact hne rfl⟩

/-- Suppression adjacency is precisely a direct edge or a degree-two corridor
with distinct retained endpoints, expressed using the original Mathlib adjacency. -/
theorem suppression_adj_iff {W : Type u} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (x y : SuppressionNode H) :
    (suppression H).Adj x y ↔ x ≠ y ∧ (H.Adj x.val y.val ∨
      ∃ m : W, H.degree m = 2 ∧ H.Adj x.val m ∧ H.Adj m y.val) := Iff.rfl

example : (suppression (⊤ : SimpleGraph (Fin 4))).Adj
    ⟨0, by decide⟩ ⟨1, by decide⟩ := by
  exact ⟨by decide, Or.inl (by decide)⟩

/-- The retained vertex type is finite, without leaking decidable equality into statements. -/
noncomputable instance suppressionFintype {W : Type u} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj] : Fintype (SuppressionNode H) :=
  Fintype.ofFinite _

/-- A distinguished degree-three root guarantees that the suppressed graph is nonempty. -/
theorem suppression_nonempty {W : Type u} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] {z : W} (hz : H.degree z = 3) : Nonempty (SuppressionNode H) :=
  ⟨⟨z, hz⟩⟩

/-- At a degree-two vertex, any incident edge has a unique other endpoint. -/
theorem existsUnique_degree_two_mate {W : Type u} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] {m x : W} (hm : H.degree m = 2) (hxm : H.Adj x m) :
    ∃! y : W, H.Adj m y ∧ y ≠ x := by
  classical
  have hx : x ∈ H.neighborFinset m := (H.mem_neighborFinset m x).mpr hxm.symm
  have hcard : ((H.neighborFinset m).erase x).card = 1 := by
    rw [Finset.card_erase_of_mem hx]
    change H.degree m - 1 = 1
    rw [hm]
  obtain ⟨y, herase⟩ := Finset.card_eq_one.mp hcard
  have hy : y ∈ (H.neighborFinset m).erase x := by
    rw [herase]
    exact Finset.mem_singleton_self y
  have hyne : y ≠ x := (Finset.mem_erase.mp hy).1
  have hmy : H.Adj m y := (H.mem_neighborFinset m y).mp (Finset.mem_erase.mp hy).2
  refine ⟨y, ⟨hmy, hyne⟩, ?_⟩
  intro z hz
  have hzmem : z ∈ (H.neighborFinset m).erase x :=
    Finset.mem_erase.mpr ⟨hz.2, (H.mem_neighborFinset m z).mpr hz.1⟩
  rw [herase] at hzmem
  exact Finset.mem_singleton.mp hzmem

/-- If every degree is two or three and adjacent degree-two vertices are excluded,
the other endpoint beyond a degree-two vertex has degree three. -/
theorem degree_three_of_adj_degree_two {W : Type u} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hdegrees : ∀ a, H.degree a = 2 ∨ H.degree a = 3)
    (hno22 : ∀ a b, H.Adj a b → H.degree a = 2 → H.degree b = 2 → False)
    {m y : W} (hm : H.degree m = 2) (hmy : H.Adj m y) : H.degree y = 3 := by
  rcases hdegrees y with hy | hy
  · exact False.elim (hno22 m y hmy hm hy)
  · exact hy

/-- The endpoint reached from one incident half-edge is unique: either it is a direct
retained neighbor, or it is the unique mate beyond its degree-two middle vertex. -/
theorem suppression_endpoint_unique {W : Type u} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] {x y z : SuppressionNode H} {m : W}
    (hxm : H.Adj x.val m) (hxy : (suppression H).Adj x y)
    (hxz : (suppression H).Adj x z)
    (hmy : (m = y.val ∧ H.degree m = 3) ∨ (H.degree m = 2 ∧ H.Adj m y.val))
    (hmz : (m = z.val ∧ H.degree m = 3) ∨ (H.degree m = 2 ∧ H.Adj m z.val)) :
    y = z := by
  rcases hmy with ⟨hmy, hm3⟩ | ⟨hm2, hmy⟩
  · rcases hmz with ⟨hmz, hm3'⟩ | ⟨hm2, hmz⟩
    · exact Subtype.ext (hmy.symm.trans hmz)
    · omega
  · rcases hmz with ⟨hmz, hm3⟩ | ⟨hm2', hmz⟩
    · omega
    · obtain ⟨a, ha, huniq⟩ := existsUnique_degree_two_mate H hm2 hxm
      have hyne : y.val ≠ x.val := fun heq => hxy.1 (Subtype.ext heq.symm)
      have hzne : z.val ≠ x.val := fun heq => hxz.1 (Subtype.ext heq.symm)
      have hya := huniq y.val ⟨hmy, hyne⟩
      have hza := huniq z.val ⟨hmz, hzne⟩
      exact Subtype.ext (hya.trans hza.symm)

/-- With independent degree-two vertices, no triangles, and no parallel two-edge
corridors, suppression bijects the three incident half-edges at every retained vertex
with its new neighbors. All structural hypotheses are explicit for later discharge. -/
theorem suppression_neighbor_bijection {W : Type u} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hdegrees : ∀ a, H.degree a = 2 ∨ H.degree a = 3)
    (hno22 : ∀ a b, H.Adj a b → H.degree a = 2 → H.degree b = 2 → False)
    (htri : ∀ a b c, H.Adj a b → H.Adj b c → H.Adj c a → False)
    (hparallel : ∀ a b p q, H.degree a = 3 → H.degree b = 3 → a ≠ b →
      H.degree p = 2 → H.degree q = 2 → p ≠ q →
      H.Adj a p → H.Adj p b → H.Adj a q → H.Adj q b → False)
    (x : SuppressionNode H) :
    Nonempty (H.neighborSet x.val ≃ (suppression H).neighborSet x) := by
  classical
  let r : H.neighborSet x.val → (suppression H).neighborSet x → Prop := fun m y =>
    (m.val = y.val.val ∧ H.degree m.val = 3) ∨
      (H.degree m.val = 2 ∧ H.Adj m.val y.val.val)
  have htargets (m : H.neighborSet x.val) : ∃ y : (suppression H).neighborSet x, r m y := by
    have hxm : H.Adj x.val m.val := m.property
    rcases hdegrees m.val with hm2 | hm3
    · obtain ⟨b, hb, huniq⟩ := existsUnique_degree_two_mate H hm2 hxm
      have hb3 := degree_three_of_adj_degree_two H hdegrees hno22 hm2 hb.1
      let b' : SuppressionNode H := ⟨b, hb3⟩
      have hxb : (suppression H).Adj x b' := by
        refine ⟨?_, Or.inr ⟨m.val, hm2, hxm, hb.1⟩⟩
        intro heq
        exact hb.2 (congrArg Subtype.val heq).symm
      exact ⟨⟨b', hxb⟩, Or.inr ⟨hm2, hb.1⟩⟩
    · let m' : SuppressionNode H := ⟨m.val, hm3⟩
      have hxm' : (suppression H).Adj x m' :=
        ⟨fun heq => hxm.ne (congrArg Subtype.val heq), Or.inl hxm⟩
      exact ⟨⟨m', hxm'⟩, Or.inl ⟨rfl, hm3⟩⟩
  let f : H.neighborSet x.val → (suppression H).neighborSet x :=
    fun m => Classical.choose (htargets m)
  have hspec (m : H.neighborSet x.val) : r m (f m) := Classical.choose_spec (htargets m)
  have hinj : Function.Injective f := by
    intro m n heq
    have hm := hspec m
    have hn : r n (f m) := by rw [heq]; exact hspec n
    rcases hm with ⟨hmy, hm3⟩ | ⟨hm2, hmy⟩
    · rcases hn with ⟨hny, hn3⟩ | ⟨hn2, hny⟩
      · exact Subtype.ext (hmy.trans hny.symm)
      · have hxy : H.Adj x.val (f m).val.val := by
          rw [← hmy]
          exact m.property
        exact False.elim (htri x.val (f m).val.val n.val hxy hny.symm n.property.symm)
    · rcases hn with ⟨hny, hn3⟩ | ⟨hn2, hny⟩
      · have hxy : H.Adj x.val (f m).val.val := by
          rw [← hny]
          exact n.property
        exact False.elim (htri x.val (f m).val.val m.val hxy hmy.symm m.property.symm)
      · by_cases hmn : m.val = n.val
        · exact Subtype.ext hmn
        have hxy : x.val ≠ (f m).val.val :=
          fun heq => (f m).property.1 (Subtype.ext heq)
        exact False.elim (hparallel x.val (f m).val.val m.val n.val
          x.property (f m).val.property hxy hm2 hn2 hmn m.property hmy n.property hny)
  have hsurj : Function.Surjective f := by
    intro y
    rcases y.property.2 with hdir | ⟨m, hm2, hxm, hmy⟩
    · let m : H.neighborSet x.val := ⟨y.val.val, hdir⟩
      have hr : r m y := Or.inl ⟨rfl, y.val.property⟩
      refine ⟨m, Subtype.ext ?_⟩
      exact suppression_endpoint_unique H m.property (f m).property y.property (hspec m) hr
    · let m' : H.neighborSet x.val := ⟨m, hxm⟩
      have hr : r m' y := Or.inr ⟨hm2, hmy⟩
      refine ⟨m', Subtype.ext ?_⟩
      exact suppression_endpoint_unique H m'.property (f m').property y.property (hspec m') hr
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩⟩

/-- Under the explicit no-triangle and no-parallel-corridor conditions, suppression
is cubic at every retained vertex, with no connectedness hypothesis. -/
theorem suppression_degree_three {W : Type u} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel (suppression H).Adj]
    (hdegrees : ∀ a, H.degree a = 2 ∨ H.degree a = 3)
    (hno22 : ∀ a b, H.Adj a b → H.degree a = 2 → H.degree b = 2 → False)
    (htri : ∀ a b c, H.Adj a b → H.Adj b c → H.Adj c a → False)
    (hparallel : ∀ a b p q, H.degree a = 3 → H.degree b = 3 → a ≠ b →
      H.degree p = 2 → H.degree q = 2 → p ≠ q →
      H.Adj a p → H.Adj p b → H.Adj a q → H.Adj q b → False)
    (x : SuppressionNode H) : (suppression H).degree x = 3 := by
  obtain ⟨e⟩ := suppression_neighbor_bijection H hdegrees hno22 htri hparallel x
  have hcard := Fintype.card_congr e
  rw [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree] at hcard
  exact hcard.symm.trans x.property

/-- Every angle at a root clique other than the pole clique uses an original edge,
not a triangle-completion edge. -/
theorem completion_root_angle_old {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) {v : V} (hv : G.degree v = 3)
    {z C : RootNode (completion G v)} (hz : z.val = {p | G.Adj v p.val}) (hCz : C ≠ z)
    {a b : {p : V // p ≠ v}} (ha : a ∈ C.val) (hb : b ∈ C.val) (hab : a ≠ b) :
    G.Adj a.val b.val := by
  have eab := (SimpleGraph.isMaximalClique_iff.mp C.property).1 ha hb hab
  rcases eab with hold | ⟨_, hpa, hpb⟩
  · exact hold
  · have haz : a ∈ z.val := by rw [hz]; exact hpa
    have hbz : b ∈ z.val := by rw [hz]; exact hpb
    exact False.elim (hab (root_intersection_unique (completion G v)
      (completion_strongDiamondFree G hG hv) hCz ha haz hb hbz))

/-- A four-square of distinct root nodes avoiding the pole clique gives an ordinary
four-cycle in the original graph, and therefore cannot occur. -/
theorem completion_root_square_impossible {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) {v : V}
    [DecidableRel (completion G v).Adj] (hv : G.degree v = 3) (hclaw : Claw G v)
    (hunique : ∀ w, Claw G w → w = v) {z A B P T : RootNode (completion G v)}
    (hz : z.val = {p | G.Adj v p.val}) (hAz : A ≠ z) (hBz : B ≠ z)
    (hPz : P ≠ z) (hTz : T ≠ z) (hAB : A ≠ B) (hPT : P ≠ T)
    (hAP : (cliqueRoot (completion G v)).Adj A P)
    (hPB : (cliqueRoot (completion G v)).Adj P B)
    (hBT : (cliqueRoot (completion G v)).Adj B T)
    (hTA : (cliqueRoot (completion G v)).Adj T A) : False := by
  let R := completion G v
  have hD : StrongDiamondFree R := completion_strongDiamondFree G hG hv
  have hcf : ∀ x, ¬ Claw R x := completion_claw_free G hunique
  have hmin : ∀ x, 3 ≤ R.degree x := completion_min_degree G hG hv hclaw
  obtain ⟨a, haA, haP⟩ := hAP.2
  obtain ⟨b, hbP, hbB⟩ := hPB.2
  obtain ⟨c, hcB, hcT⟩ := hBT.2
  obtain ⟨d, hdT, hdA⟩ := hTA.2
  have hab : a ≠ b := by
    intro heq
    rw [← heq] at hbB
    exact no_three_root_nodes R hD hcf hmin hAP.1 hAB hPB.1 haA haP hbB
  have hac : a ≠ c := by
    intro heq
    rw [← heq] at hcT
    exact no_three_root_nodes R hD hcf hmin hAP.1 hTA.1.symm hPT haA haP hcT
  have had : a ≠ d := by
    intro heq
    rw [← heq] at hdT
    exact no_three_root_nodes R hD hcf hmin hAP.1 hTA.1.symm hPT haA haP hdT
  have hbc : b ≠ c := by
    intro heq
    rw [← heq] at hcT
    exact no_three_root_nodes R hD hcf hmin hPB.1 hPT hBT.1 hbP hbB hcT
  have hbd : b ≠ d := by
    intro heq
    rw [← heq] at hdT
    exact no_three_root_nodes R hD hcf hmin hPB.1 hPT hBT.1 hbP hbB hdT
  have hcd : c ≠ d := by
    intro heq
    rw [← heq] at hdA
    exact no_three_root_nodes R hD hcf hmin hBT.1 hAB.symm hTA.1 hcB hcT hdA
  have eab := completion_root_angle_old G hG hv hz hPz haP hbP hab
  have ebc := completion_root_angle_old G hG hv hz hBz hbB hcB hbc
  have ecd := completion_root_angle_old G hG hv hz hTz hcT hdT hcd
  have eda := completion_root_angle_old G hG hv hz hAz hdA haA had.symm
  have ne_val : ∀ {s t : {p : V // p ≠ v}}, s ≠ t → s.val ≠ t.val :=
    fun hne heq => hne (Subtype.ext heq)
  exact not_four_cycle G hG (ne_val hab) (ne_val hac) (ne_val had)
    (ne_val hbc) (ne_val hbd) (ne_val hcd) eab ebc ecd eda

/-- Two distinct degree-two root vertices cannot form parallel corridors between
retained endpoints: the pole clique's cubic arms force such a square to avoid it. -/
theorem completion_root_parallel_impossible {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) {v : V}
    [DecidableRel (completion G v).Adj] [DecidableRel (cliqueRoot (completion G v)).Adj]
    (hv : G.degree v = 3) (hclaw : Claw G v) (hunique : ∀ w, Claw G w → w = v)
    {z A B P T : RootNode (completion G v)} (hz : z.val = {p | G.Adj v p.val})
    (hz3 : (cliqueRoot (completion G v)).degree z = 3)
    (harms : ∀ D, (cliqueRoot (completion G v)).Adj z D →
      (cliqueRoot (completion G v)).degree D = 3)
    (hAB : A ≠ B) (hPT : P ≠ T)
    (hP2 : (cliqueRoot (completion G v)).degree P = 2)
    (hT2 : (cliqueRoot (completion G v)).degree T = 2)
    (hAP : (cliqueRoot (completion G v)).Adj A P)
    (hPB : (cliqueRoot (completion G v)).Adj P B)
    (hBT : (cliqueRoot (completion G v)).Adj B T)
    (hTA : (cliqueRoot (completion G v)).Adj T A) : False := by
  have hPz : P ≠ z := by intro heq; rw [heq, hz3] at hP2; omega
  have hTz : T ≠ z := by intro heq; rw [heq, hz3] at hT2; omega
  have hAz : A ≠ z := by
    intro heq
    have hzp : (cliqueRoot (completion G v)).Adj z P := by rw [← heq]; exact hAP
    have hP3 := harms P hzp
    omega
  have hBz : B ≠ z := by
    intro heq
    have hzp : (cliqueRoot (completion G v)).Adj z P := by rw [← heq]; exact hPB.symm
    have hP3 := harms P hzp
    omega
  exact completion_root_square_impossible G hG hv hclaw hunique hz hAz hBz hPz hTz
    hAB hPT hAP hPB hBT hTA

/-- Double-counting label incidence bounds the entire root's order by the original
vertex order, without restricting to the component of the distinguished pole clique. -/
theorem cliqueRoot_card_le {W : Type u} [Fintype W] [Nonempty W]
    (R : SimpleGraph W) [DecidableRel R.Adj] [DecidableRel (cliqueRoot R).Adj]
    (hD : StrongDiamondFree R) (hclaw : ∀ x, ¬ Claw R x)
    (hdegree : ∀ x, 3 ≤ R.degree x) : Fintype.card (RootNode R) ≤ Fintype.card W := by
  classical
  have hcard (C : RootNode R) : Fintype.card C.val =
      ∑ x : W, if x ∈ C.val then (1 : ℕ) else 0 := by
    rw [Fintype.card_subtype]
    simp
  have hfiber (x : W) :
      (Finset.univ.filter (fun C : RootNode R => x ∈ C.val)).card = 2 := by
    obtain ⟨A, B, hAB, hxA, hxB, hinc⟩ := exactly_two_root_nodes R hD hclaw hdegree x
    have heq : Finset.univ.filter (fun C : RootNode R => x ∈ C.val) = {A, B} := by
      ext C
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton] using hinc C
    rw [heq]
    simp [hAB]
  have hcount : (∑ C : RootNode R, Fintype.card C.val) = 2 * Fintype.card W := by
    simp_rw [hcard]
    rw [Finset.sum_comm]
    have hinner (x : W) :
        (∑ C : RootNode R, if x ∈ C.val then (1 : ℕ) else 0) = 2 := by
      simpa using hfiber x
    simp_rw [hinner]
    simp [Nat.mul_comm]
  have hmincard (C : RootNode R) : 2 ≤ Fintype.card C.val := by
    rw [← cliqueRoot_degree_eq_card R hD hclaw hdegree C]
    rcases cliqueRoot_degree_two_or_three R hD hclaw hdegree C with htwo | hthree
    · omega
    · omega
  have hlower : 2 * Fintype.card (RootNode R) ≤ ∑ C : RootNode R, Fintype.card C.val := by
    calc
      2 * Fintype.card (RootNode R) = ∑ _C : RootNode R, (2 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ ∑ C : RootNode R, Fintype.card C.val := Finset.sum_le_sum (fun C _ => hmincard C)
  rw [hcount] at hlower
  omega

/-- The degree-three vertices of the completed graph's root have strictly smaller
order than the original graph, accounting for all root components simultaneously. -/
theorem completion_suppression_order_lt {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) {v : V}
    [DecidableRel (completion G v).Adj] [DecidableRel (cliqueRoot (completion G v)).Adj]
    (hv : G.degree v = 3) (hclaw : Claw G v) (hunique : ∀ w, Claw G w → w = v) :
    Fintype.card (SuppressionNode (cliqueRoot (completion G v))) < Fintype.card V := by
  letI := completion_nonempty G hclaw
  have hroot := cliqueRoot_card_le (completion G v) (completion_strongDiamondFree G hG hv)
    (completion_claw_free G hunique) (completion_min_degree G hG hv hclaw)
  have hsub : Fintype.card (SuppressionNode (cliqueRoot (completion G v))) ≤
      Fintype.card (RootNode (completion G v)) := Fintype.card_subtype_le _
  have hdeleted : Fintype.card {x : V // x ≠ v} < Fintype.card V :=
    Fintype.card_subtype_lt (x := v) (fun hne => hne rfl)
  exact lt_of_le_of_lt (hsub.trans hroot) hdeleted

/-- A direct root edge between two cubic non-pole-root nodes has an original label
of degree at least four: each endpoint clique supplies two disjoint original neighbors. -/
theorem old_degree_four_of_cubic_root_edge {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) {v : V}
    [DecidableRel (completion G v).Adj] [DecidableRel (cliqueRoot (completion G v)).Adj]
    (hv : G.degree v = 3) (hclaw : Claw G v) (hunique : ∀ w, Claw G w → w = v)
    {z C D : RootNode (completion G v)} (hz : z.val = {p | G.Adj v p.val})
    (hCz : C ≠ z) (hDz : D ≠ z) (hCD : C ≠ D)
    (hC3 : (cliqueRoot (completion G v)).degree C = 3)
    (hD3 : (cliqueRoot (completion G v)).degree D = 3)
    {p : {x : V // x ≠ v}} (hpC : p ∈ C.val) (hpD : p ∈ D.val) : 4 ≤ G.degree p.val := by
  classical
  let R := completion G v
  have hdiamond : StrongDiamondFree R := completion_strongDiamondFree G hG hv
  have hcf : ∀ x, ¬ Claw R x := completion_claw_free G hunique
  have hmin : ∀ x, 3 ≤ R.degree x := completion_min_degree G hG hv hclaw
  have hcardC : C.val.toFinset.card = 3 := by
    rw [Set.toFinset_card, ← cliqueRoot_degree_eq_card R hdiamond hcf hmin C]
    exact hC3
  have hcardD : D.val.toFinset.card = 3 := by
    rw [Set.toFinset_card, ← cliqueRoot_degree_eq_card R hdiamond hcf hmin D]
    exact hD3
  have hpCf : p ∈ C.val.toFinset := by simpa using hpC
  have hpDf : p ∈ D.val.toFinset := by simpa using hpD
  have hdisj : Disjoint (C.val.toFinset.erase p) (D.val.toFinset.erase p) := by
    apply Finset.disjoint_left.mpr
    intro q hqC hqD
    have hqC' := Finset.mem_erase.mp hqC
    have hqD' := Finset.mem_erase.mp hqD
    have hqCset : q ∈ C.val := by simpa using hqC'.2
    have hqDset : q ∈ D.val := by simpa using hqD'.2
    exact hqC'.1 (root_intersection_unique R hdiamond hCD hqCset hqDset hpC hpD)
  let S := C.val.toFinset.erase p ∪ D.val.toFinset.erase p
  have hsize : S.card = 4 := by
    dsimp only [S]
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hpCf,
      Finset.card_erase_of_mem hpDf, hcardC, hcardD]
  let e : {x : V // x ≠ v} ↪ V := ⟨Subtype.val, Subtype.coe_injective⟩
  have hsubset : S.map e ⊆ G.neighborFinset p.val := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := Finset.mem_map.mp hq
    apply (G.mem_neighborFinset p.val r.val).mpr
    rcases Finset.mem_union.mp hr with hrC | hrD
    · have hrC' := Finset.mem_erase.mp hrC
      have hrCset : r ∈ C.val := by simpa using hrC'.2
      exact completion_root_angle_old G hG hv hz hCz hpC hrCset hrC'.1.symm
    · have hrD' := Finset.mem_erase.mp hrD
      have hrDset : r ∈ D.val := by simpa using hrD'.2
      exact completion_root_angle_old G hG hv hz hDz hpD hrDset hrD'.1.symm
  have hle := Finset.card_le_card hsubset
  rw [Finset.card_map, hsize] at hle
  exact hle

/-- Original high-degree independence forbids two distinct high labels at an ordinary
root angle; this is the local matching condition, with original rather than completed degrees. -/
theorem old_high_labels_not_same_root_angle {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    {v : V} (hv : G.degree v = 3) {z C : RootNode (completion G v)}
    (hz : z.val = {p | G.Adj v p.val}) (hCz : C ≠ z)
    {p q : {x : V // x ≠ v}} (hp : p ∈ C.val) (hq : q ∈ C.val) (hpq : p ≠ q)
    (hp4 : 4 ≤ G.degree p.val) (hq4 : 4 ≤ G.degree q.val) : False :=
  hHIGH p.val q.val hp4 hq4 (completion_root_angle_old G hG hv hz hCz hp hq hpq)

end Erdos64.UniqueCubicClawCenter
