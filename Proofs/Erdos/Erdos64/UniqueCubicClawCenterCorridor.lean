import Erdos.Erdos64.UniqueCubicClawCenterCycleLift
import Erdos.Erdos64.UniqueCubicClawCenterCycleIndex

set_option autoImplicit false

namespace Erdos64.UniqueCubicClawCenter

open SimpleGraph

universe u

/-- The one- or two-edge root corridor representing an oriented suppressed edge,
with its endpoint labels. Direct corridors use one label; split corridors use two. -/
structure RootCorridor {W : Type u} [Fintype W] (R : SimpleGraph W)
    [DecidableRel (cliqueRoot R).Adj] (x y : SuppressionNode (cliqueRoot R)) where
  near : RootNode R
  far : RootNode R
  first : W
  last : W
  start_edge : (cliqueRoot R).Adj x.val near
  finish_edge : (cliqueRoot R).Adj y.val far
  first_start : first ∈ x.val.val
  first_near : first ∈ near.val
  last_finish : last ∈ y.val.val
  last_far : last ∈ far.val
  endpoints_ne : x ≠ y
  route : (near = y.val ∧ far = x.val ∧ first = last) ∨
    (near = far ∧ (cliqueRoot R).degree near = 2 ∧ first ≠ last)

namespace RootCorridor

variable {W : Type u} [Fintype W] {R : SimpleGraph W}
  [DecidableRel (cliqueRoot R).Adj] {x y : SuppressionNode (cliqueRoot R)}

/-- A label corridor is an actual edge of the suppression, not extra graph data. -/
theorem adj (P : RootCorridor R x y) : (suppression (cliqueRoot R)).Adj x y := by
  refine ⟨P.endpoints_ne, ?_⟩
  rcases P.route with ⟨hn, hf, he⟩ | ⟨hnf, hn2, hne⟩
  · exact Or.inl (hn ▸ P.start_edge)
  · exact Or.inr ⟨P.near, hn2, P.start_edge, hnf.symm ▸ P.finish_edge.symm⟩

/-- The first half-edge of a label corridor reaches its specified other retained endpoint. -/
theorem first_route (P : RootCorridor R x y) :
    (P.near = y.val ∧ (cliqueRoot R).degree P.near = 3) ∨
      ((cliqueRoot R).degree P.near = 2 ∧ (cliqueRoot R).Adj P.near y.val) := by
  rcases P.route with ⟨hn, hf, he⟩ | ⟨hnf, hn2, hne⟩
  · exact Or.inl ⟨hn, hn.symm ▸ y.property⟩
  · exact Or.inr ⟨hn2, hnf.symm ▸ P.finish_edge.symm⟩

/-- The last half-edge of a label corridor reaches its specified first retained endpoint. -/
theorem last_route (P : RootCorridor R x y) :
    (P.far = x.val ∧ (cliqueRoot R).degree P.far = 3) ∨
      ((cliqueRoot R).degree P.far = 2 ∧ (cliqueRoot R).Adj P.far x.val) := by
  rcases P.route with ⟨hn, hf, he⟩ | ⟨hnf, hn2, hne⟩
  · exact Or.inl ⟨hf, hf.symm ▸ x.property⟩
  · exact Or.inr ⟨hnf ▸ hn2, hnf ▸ P.start_edge.symm⟩

/-- Read the original labels along the corridor in its orientation, retaining
one copy of a direct-edge label and both labels of a split corridor. -/
noncomputable def labels (P : RootCorridor R x y) : List W := by
  classical
  exact if P.first = P.last then [P.first] else [P.first, P.last]

/-- Membership in the corridor label list means being its first or last label. -/
theorem mem_labels (P : RootCorridor R x y) (p : W) :
    p ∈ P.labels ↔ p = P.first ∨ p = P.last := by
  classical
  unfold labels
  split_ifs with heq
  · simp [heq]
  · simp

/-- Each corridor contains at least one label. -/
theorem labels_ne_nil (P : RootCorridor R x y) : P.labels ≠ [] := by
  classical
  unfold labels
  split_ifs <;> simp

/-- The labels within one corridor never repeat. -/
theorem labels_nodup (P : RootCorridor R x y) : P.labels.Nodup := by
  classical
  unfold labels
  split_ifs with heq <;> simp [heq]

/-- The first label in the corridor list is the label at its starting endpoint. -/
theorem head_labels (P : RootCorridor R x y) : P.labels.head? = some P.first := by
  classical
  unfold labels
  split_ifs <;> rfl

/-- The last label in the corridor list is the label at its terminal endpoint. -/
theorem getLast_labels (P : RootCorridor R x y) : P.labels.getLast? = some P.last := by
  classical
  unfold labels
  split_ifs with heq
  · simpa only [List.getLast?_singleton] using congrArg some heq
  · rfl

/-- A direct corridor uses one label; a split corridor uses two. -/
theorem length_labels (P : RootCorridor R x y) :
    P.labels.length = 1 ∨ P.labels.length = 2 := by
  classical
  unfold labels
  split_ifs <;> simp

/-- Singleton corridor blocks are exactly the direct corridors. -/
theorem length_labels_eq_one_iff (P : RootCorridor R x y) :
    P.labels.length = 1 ↔ P.first = P.last := by
  classical
  unfold labels
  split_ifs <;> simp_all

/-- Every used label is incident to a retained endpoint and its corresponding
corridor half-edge. -/
theorem label_slots (P : RootCorridor R x y) {p : W} (hp : p ∈ P.labels) :
    (p ∈ x.val.val ∧ p ∈ P.near.val) ∨ (p ∈ y.val.val ∧ p ∈ P.far.val) := by
  rcases (P.mem_labels p).mp hp with hpfirst | hplast
  · rw [hpfirst]
    exact Or.inl ⟨P.first_start, P.first_near⟩
  · rw [hplast]
    exact Or.inr ⟨P.last_finish, P.last_far⟩

/-- A label shared by two corridors forces equality of their unordered
retained endpoints. It cannot collide between distinct cycle corridors. -/
theorem labels_collision [DecidableRel R.Adj]
    (hD : StrongDiamondFree R) (hcf : ∀ p, ¬ Claw R p) (hmin : ∀ p, 3 ≤ R.degree p)
    {s t : SuppressionNode (cliqueRoot R)} (P : RootCorridor R x y)
    (Q : RootCorridor R s t) {p : W} (hp : p ∈ P.labels) (hq : p ∈ Q.labels) :
    (x = s ∧ y = t) ∨ (x = t ∧ y = s) := by
  rcases P.label_slots hp with ⟨hpx, hpn⟩ | ⟨hpy, hpf⟩
  · rcases Q.label_slots hq with ⟨hps, hqn⟩ | ⟨hpt, hqf⟩
    · exact suppressed_label_collision R hD hcf hmin P.adj Q.adj
        P.start_edge Q.start_edge P.first_route Q.first_route hpx hpn hps hqn
    · have hpair := suppressed_label_collision R hD hcf hmin P.adj Q.adj.symm
        P.start_edge Q.finish_edge P.first_route Q.last_route hpx hpn hpt hqf
      exact hpair.symm
  · rcases Q.label_slots hq with ⟨hps, hqn⟩ | ⟨hpt, hqf⟩
    · have hpair := suppressed_label_collision R hD hcf hmin P.adj.symm Q.adj
        P.finish_edge Q.start_edge P.last_route Q.first_route hpy hpf hps hqn
      rcases hpair with ⟨hys, hxt⟩ | ⟨hyt, hxs⟩
      · exact Or.inr ⟨hxt, hys⟩
      · exact Or.inl ⟨hxs, hyt⟩
    · have hpair := suppressed_label_collision R hD hcf hmin P.adj.symm Q.adj.symm
        P.finish_edge Q.finish_edge P.last_route Q.last_route hpy hpf hpt hqf
      rcases hpair with ⟨hyt, hxs⟩ | ⟨hys, hxt⟩
      · exact Or.inl ⟨hxs, hyt⟩
      · exact Or.inr ⟨hxt, hys⟩

end RootCorridor

/-- Every suppressed edge has a label corridor, derived directly from its
one- or two-edge geometric definition. -/
theorem exists_rootCorridor {W : Type u} [Fintype W] (R : SimpleGraph W)
    [DecidableRel R.Adj] [DecidableRel (cliqueRoot R).Adj]
    (hD : StrongDiamondFree R) (hcf : ∀ p, ¬ Claw R p) (hmin : ∀ p, 3 ≤ R.degree p)
    {x y : SuppressionNode (cliqueRoot R)}
    (hxy : (suppression (cliqueRoot R)).Adj x y) : Nonempty (RootCorridor R x y) := by
  rcases hxy.2 with hdir | ⟨m, hm2, hxm, hmy⟩
  · obtain ⟨p, hpx, hpy⟩ := hdir.2
    exact ⟨{
      near := y.val
      far := x.val
      first := p
      last := p
      start_edge := hdir
      finish_edge := hdir.symm
      first_start := hpx
      first_near := hpy
      last_finish := hpy
      last_far := hpx
      endpoints_ne := hxy.1
      route := Or.inl ⟨rfl, rfl, rfl⟩ }⟩
  · obtain ⟨p, hpx, hpm⟩ := hxm.2
    obtain ⟨q, hqm, hqy⟩ := hmy.2
    have hpq : p ≠ q := by
      intro heq
      rw [← heq] at hqy
      have hxmne := hxm.1
      have hxyne : x.val ≠ y.val := fun heq => hxy.1 (Subtype.ext heq)
      exact no_three_root_nodes R hD hcf hmin hxmne hxyne hmy.1 hpx hpm hqy
    exact ⟨{
      near := m
      far := m
      first := p
      last := q
      start_edge := hxm
      finish_edge := hmy.symm
      first_start := hpx
      first_near := hpm
      last_finish := hqy
      last_far := hqm
      endpoints_ne := hxy.1
      route := Or.inr ⟨rfl, hm2, hpq⟩ }⟩

/-- Existence of corridor data is equivalent to standard suppression adjacency
under the checked root geometry. -/
theorem nonempty_rootCorridor_iff {W : Type u} [Fintype W] (R : SimpleGraph W)
    [DecidableRel R.Adj] [DecidableRel (cliqueRoot R).Adj]
    (hD : StrongDiamondFree R) (hcf : ∀ p, ¬ Claw R p) (hmin : ∀ p, 3 ≤ R.degree p)
    (x y : SuppressionNode (cliqueRoot R)) :
    Nonempty (RootCorridor R x y) ↔ (suppression (cliqueRoot R)).Adj x y := by
  constructor
  · rintro ⟨P⟩
    exact P.adj
  · exact exists_rootCorridor R hD hcf hmin

/-- A used label identifies its unique index on an injective cyclic sequence
of retained vertices. -/
theorem cycle_corridor_label_index {W : Type u} [Fintype W] (R : SimpleGraph W)
    [DecidableRel R.Adj] [DecidableRel (cliqueRoot R).Adj]
    (hD : StrongDiamondFree R) (hcf : ∀ p, ¬ Claw R p) (hmin : ∀ p, 3 ≤ R.degree p)
    {m : ℕ} (hm : 3 ≤ m + 1)
    (c : Fin (m + 1) → SuppressionNode (cliqueRoot R)) (hc : Function.Injective c)
    (P : ∀ i, RootCorridor R (c i) (c (i + 1)))
    {i j : Fin (m + 1)} {p : W} (hi : p ∈ (P i).labels) (hj : p ∈ (P j).labels) :
    i = j := by
  classical
  apply CycleIndex.image_pair_injective m hm c hc
  rcases (P i).labels_collision hD hcf hmin (P j) hi hj with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · simp [hx, hy]
  · simp [hx, hy, Finset.pair_comm]

/-- Expanding all edges of an arbitrary retained cycle into their root-label
corridors gives a nodup base list, in every component and regardless of the pole root. -/
theorem cycle_corridor_base_nodup {W : Type u} [Fintype W] (R : SimpleGraph W)
    [DecidableRel R.Adj] [DecidableRel (cliqueRoot R).Adj]
    (hD : StrongDiamondFree R) (hcf : ∀ p, ¬ Claw R p) (hmin : ∀ p, 3 ≤ R.degree p)
    {m : ℕ} (hm : 3 ≤ m + 1)
    (c : Fin (m + 1) → SuppressionNode (cliqueRoot R)) (hc : Function.Injective c)
    (P : ∀ i, RootCorridor R (c i) (c (i + 1))) :
    (List.ofFn (fun i => (P i).labels)).flatten.Nodup := by
  rw [List.ofFn_eq_map, List.flatten_eq_flatMap, List.flatMap_map]
  apply List.nodup_flatMap.mpr
  constructor
  · intro i hi
    exact (P i).labels_nodup
  · have hindices : List.Pairwise (fun i j : Fin (m + 1) => i ≠ j)
        (List.finRange (m + 1)) := List.nodup_finRange _
    apply hindices.imp
    intro i j hij
    apply List.disjoint_left.mpr
    intro p hp hq
    exact hij (cycle_corridor_label_index R hD hcf hmin hm c hc P hp hq)

/-- A used corridor label incident to a given retained cycle node is one of
its two used angle labels: the outgoing first label or the incoming last label. -/
theorem cycle_used_label_at_node {W : Type u} [Fintype W] (R : SimpleGraph W)
    [DecidableRel R.Adj] [DecidableRel (cliqueRoot R).Adj]
    (hD : StrongDiamondFree R) (hcf : ∀ p, ¬ Claw R p) (hmin : ∀ p, 3 ≤ R.degree p)
    {m : ℕ} (c : Fin (m + 1) → SuppressionNode (cliqueRoot R)) (hc : Function.Injective c)
    (P : ∀ i, RootCorridor R (c i) (c (i + 1)))
    {i j : Fin (m + 1)} {p : W} (hpi : p ∈ (c i).val.val) (hp : p ∈ (P j).labels) :
    p = (P i).first ∨ p = (P (i - 1)).last := by
  rcases ((P j).mem_labels p).mp hp with hpfirst | hplast
  · have hpstart : p ∈ (c j).val.val := hpfirst.symm ▸ (P j).first_start
    have hpnear : p ∈ (P j).near.val := hpfirst.symm ▸ (P j).first_near
    have hnode := root_incidence_exhausted R hD hcf hmin
      (P j).start_edge.1 hpstart hpnear hpi
    rcases hnode with hij | hinear
    · have hij' : i = j := hc (Subtype.ext hij)
      subst j
      exact Or.inl hpfirst
    · have hnear3 : (cliqueRoot R).degree (P j).near = 3 := hinear ▸ (c i).property
      rcases (P j).route with ⟨hn, hf, he⟩ | ⟨hnf, hn2, hne⟩
      · have hi : i = j + 1 := hc (Subtype.ext (hinear.trans hn))
        have hj : i - 1 = j := by rw [hi]; simp
        rw [hj]
        exact Or.inr (hpfirst.trans he)
      · omega
  · have hpfinish : p ∈ (c (j + 1)).val.val := hplast.symm ▸ (P j).last_finish
    have hpfar : p ∈ (P j).far.val := hplast.symm ▸ (P j).last_far
    have hnode := root_incidence_exhausted R hD hcf hmin
      (P j).finish_edge.1 hpfinish hpfar hpi
    rcases hnode with hij | hifar
    · have hi : i = j + 1 := hc (Subtype.ext hij)
      have hj : i - 1 = j := by rw [hi]; simp
      rw [hj]
      exact Or.inr hplast
    · have hfar3 : (cliqueRoot R).degree (P j).far = 3 := hifar ▸ (c i).property
      rcases (P j).route with ⟨hn, hf, he⟩ | ⟨hnf, hn2, hne⟩
      · have hi : i = j := hc (Subtype.ext (hifar.trans hf))
        subst j
        exact Or.inl (hplast.trans he.symm)
      · have hfar2 : (cliqueRoot R).degree (P j).far = 2 := hnf ▸ hn2
        omega

/-- A third incident label distinct from both used angle labels lies outside
all corridor labels of the cycle, not just outside its two adjacent corridors. -/
theorem cycle_third_label_fresh {W : Type u} [Fintype W] (R : SimpleGraph W)
    [DecidableRel R.Adj] [DecidableRel (cliqueRoot R).Adj]
    (hD : StrongDiamondFree R) (hcf : ∀ p, ¬ Claw R p) (hmin : ∀ p, 3 ≤ R.degree p)
    {m : ℕ} (c : Fin (m + 1) → SuppressionNode (cliqueRoot R)) (hc : Function.Injective c)
    (P : ∀ i, RootCorridor R (c i) (c (i + 1)))
    {i : Fin (m + 1)} {p : W} (hpi : p ∈ (c i).val.val)
    (hpout : p ≠ (P i).first) (hpin : p ≠ (P (i - 1)).last) :
    p ∉ (List.ofFn (fun j => (P j).labels)).flatten := by
  intro hp
  obtain ⟨xs, hxs, hpxs⟩ := List.mem_flatten.mp hp
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hxs
  rcases cycle_used_label_at_node R hD hcf hmin c hc P hpi hpxs with hout | hin
  · exact hpout hout
  · exact hpin hin

/-- The two used angle labels at every retained cycle node are distinct. -/
theorem cycle_angle_labels_ne {W : Type u} [Fintype W] (R : SimpleGraph W)
    [DecidableRel R.Adj] [DecidableRel (cliqueRoot R).Adj]
    (hD : StrongDiamondFree R) (hcf : ∀ p, ¬ Claw R p) (hmin : ∀ p, 3 ≤ R.degree p)
    {m : ℕ} (hm : 3 ≤ m + 1)
    (c : Fin (m + 1) → SuppressionNode (cliqueRoot R)) (hc : Function.Injective c)
    (P : ∀ i, RootCorridor R (c i) (c (i + 1))) (i : Fin (m + 1)) :
    (P i).first ≠ (P (i - 1)).last := by
  intro heq
  have hp : (P i).first ∈ (P i).labels := ((P i).mem_labels _).mpr (Or.inl rfl)
  have hq : (P i).first ∈ (P (i - 1)).labels :=
    ((P (i - 1)).mem_labels _).mpr (Or.inr heq)
  have hi : i = i - 1 := cycle_corridor_label_index R hD hcf hmin hm c hc P hp hq
  have hnext : i + 1 = i := by
    have hadd := congrArg (fun j : Fin (m + 1) => j + 1) hi
    simpa using hadd
  exact CycleIndex.succ_ne m (by omega) i hnext

/-- At each retained cycle node, the third edge supplies a candidate label
outside the entire expanded cycle. No component or root-hit restriction is imposed. -/
theorem exists_cycle_third_labels {W : Type u} [Fintype W] (R : SimpleGraph W)
    [DecidableRel R.Adj] [DecidableRel (cliqueRoot R).Adj]
    (hD : StrongDiamondFree R) (hcf : ∀ p, ¬ Claw R p) (hmin : ∀ p, 3 ≤ R.degree p)
    {m : ℕ} (hm : 3 ≤ m + 1)
    (c : Fin (m + 1) → SuppressionNode (cliqueRoot R)) (hc : Function.Injective c)
    (P : ∀ i, RootCorridor R (c i) (c (i + 1))) :
    ∃ a : Fin (m + 1) → W, ∀ i, a i ∈ (c i).val.val ∧
      a i ≠ (P i).first ∧ a i ≠ (P (i - 1)).last ∧
      a i ∉ (List.ofFn (fun j => (P j).labels)).flatten := by
  have hthird (i : Fin (m + 1)) : ∃ a : W, a ∈ (c i).val.val ∧
      a ≠ (P i).first ∧ a ≠ (P (i - 1)).last := by
    have hin : (P (i - 1)).last ∈ (c i).val.val := by
      simpa using (P (i - 1)).last_finish
    obtain ⟨a, ha, huniq⟩ := existsUnique_third_root_label R hD hcf hmin (c i).property
      (P i).first_start hin (cycle_angle_labels_ne R hD hcf hmin hm c hc P i)
    exact ⟨a, ha⟩
  choose a ha using hthird
  refine ⟨a, ?_⟩
  intro i
  exact ⟨(ha i).1, (ha i).2.1, (ha i).2.2,
    cycle_third_label_fresh R hD hcf hmin c hc P (ha i).1 (ha i).2.1 (ha i).2.2⟩

/-- Incidence-two bounds the candidate image on any indexed subset of retained
cycle nodes. Injectivity of the indexing prevents repeated source nodes. -/
theorem cycle_candidate_image_bound {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W)
    [DecidableRel R.Adj] (hD : StrongDiamondFree R) (hcf : ∀ p, ¬ Claw R p)
    (hmin : ∀ p, 3 ≤ R.degree p) {m : ℕ}
    (c : Fin (m + 1) → RootNode R) (hc : Function.Injective c)
    (a : Fin (m + 1) → W) (ha : ∀ i, a i ∈ (c i).val)
    (s : Finset (Fin (m + 1))) : s.card ≤ 2 * (s.image a).card := by
  classical
  apply Finset.card_le_mul_card_image s 2
  intro p hp
  obtain ⟨A, B, hAB, hpA, hpB, hinc⟩ := exactly_two_root_nodes R hD hcf hmin p
  let fiber := s.filter (fun i => a i = p)
  have hsub : fiber.image c ⊆ {A, B} := by
    intro C hC
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hC
    have hai : a i = p := (Finset.mem_filter.mp hi).2
    have hpi : p ∈ (c i).val := hai ▸ ha i
    simpa only [Finset.mem_insert, Finset.mem_singleton] using (hinc (c i)).mp hpi
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective fiber hc] at hcard
  simpa [fiber, hAB] using hcard

end Erdos64.UniqueCubicClawCenter
