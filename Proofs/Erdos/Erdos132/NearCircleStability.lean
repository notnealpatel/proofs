import Erdos.Erdos132.TwoInteriorCircle
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.ProperSpace.Real

set_option autoImplicit false

open scoped BigOperators
open Erdos132.TwoInteriorCircle

namespace Erdos132.NearCircleStability

/-- The actual finite set of points of a finite labelled configuration. -/
noncomputable def points {α : Type*} [Fintype α] (x : α → Plane) : Finset Plane :=
  Finset.univ.image x

/-- The labelled class counts loop-free unordered label pairs at an ordinary distance. -/
noncomputable def labelMultiplicity {α : Type*} [Fintype α]
    (x : α → Plane) (d : ℝ) : ℕ := by
  classical
  exact ((pairs (Finset.univ : Finset α)).filter
    (fun e => pairDist (Sym2.map x e) = d)).card

/-- Injective labels give the expected number of actual points. -/
theorem card_points {α : Type*} [Fintype α] (x : α → Plane)
    (hx : Function.Injective x) : (points x).card = Fintype.card α := by
  classical
  exact Finset.card_image_of_injective Finset.univ hx

/-- For collision-free labels, labelled multiplicity is exactly actual unordered-pair
multiplicity, not an oriented-pair count. -/
theorem multiplicity_points {α : Type*} [Fintype α] (x : α → Plane)
    (hx : Function.Injective x) (d : ℝ) :
    multiplicity (points x) d = labelMultiplicity x d := by
  classical
  symm
  unfold TwoInteriorCircle.multiplicity labelMultiplicity
  apply Finset.card_bij (fun e _ => Sym2.map x e)
  · intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hp := (mk_mem_pairs _ a b).mp (Finset.mem_filter.mp he).1
      exact Finset.mem_filter.mpr ⟨(mk_mem_pairs _ _ _).mpr
        ⟨Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩,
        Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩,
        fun h => hp.2.2 (hx h)⟩, (Finset.mem_filter.mp he).2⟩
  · intro a ha b hb hab
    exact Sym2.map.injective hx hab
  · intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hp := (mk_mem_pairs _ a b).mp (Finset.mem_filter.mp he).1
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp.1
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp.2.1
      exact ⟨s(i,j), Finset.mem_filter.mpr ⟨(mk_mem_pairs _ _ _).mpr
        ⟨hi, hj, fun h => hp.2.2 (congrArg x h)⟩,
        (Finset.mem_filter.mp he).2⟩, rfl⟩

example : points (fun i : Fin 2 => (WithLp.toLp 2 ![(i.val : ℝ), 0] : Plane)) =
    {WithLp.toLp 2 ![0,0], WithLp.toLp 2 ![1,0]} := by
  classical
  simp [points, Fin.univ_succ, Finset.image_insert, Finset.image_singleton]

example : labelMultiplicity (fun i : Fin 2 => (WithLp.toLp 2 ![(i.val : ℝ), 0] : Plane)) 1 = 1 := by
  classical
  have hp : pairs (Finset.univ : Finset (Fin 2)) = {s((0 : Fin 2), 1)} := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [mk_mem_pairs, Finset.mem_univ, true_and, Finset.mem_singleton, Sym2.eq_iff]
      fin_cases a <;> fin_cases b <;> simp
  rw [labelMultiplicity, hp]
  have hd : dist (WithLp.toLp 2 ![(0 : ℝ),0] : Plane)
      (WithLp.toLp 2 ![(1 : ℝ),0] : Plane) = 1 := by
    have hs : ‖(WithLp.toLp 2 ![(0 : ℝ),0] : Plane) -
        (WithLp.toLp 2 ![(1 : ℝ),0] : Plane)‖ ^ 2 = 1 := by
      norm_num [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    rw [dist_eq_norm]
    nlinarith [norm_nonneg ((WithLp.toLp 2 ![(0 : ℝ),0] : Plane) -
      (WithLp.toLp 2 ![(1 : ℝ),0] : Plane))]
  simp only [Finset.filter_singleton, Sym2.map_mk, pairDist_mk]
  norm_num [hd]

/-- A fixed unordered label-pair distance is continuous under pointwise convergence. -/
theorem tendsto_pairDist {α β : Type*} [Fintype α] {l : Filter β}
    {f : β → α → Plane} {x : α → Plane}
    (hf : ∀ i, Filter.Tendsto (fun t => f t i) l (nhds (x i))) (e : Sym2 α) :
    Filter.Tendsto (fun t => pairDist (Sym2.map (f t) e)) l
      (nhds (pairDist (Sym2.map x e))) := by
  induction e using Sym2.ind with
  | _ a b => exact (hf a).dist (hf b)

/-- Finite distance classes can split under convergence, but no pair outside the entire
limiting class can join the class of a selected pair eventually. -/
theorem eventually_class_subset {α β : Type*} [Fintype α] {l : Filter β}
    {f : β → α → Plane} {x : α → Plane}
    (hf : ∀ i, Filter.Tendsto (fun t => f t i) l (nhds (x i))) (p : Sym2 α) :
    ∀ᶠ t in l, ∀ e : Sym2 α,
      pairDist (Sym2.map (f t) e) = pairDist (Sym2.map (f t) p) →
      pairDist (Sym2.map x e) = pairDist (Sym2.map x p) := by
  classical
  apply Filter.eventually_all.mpr
  intro e
  by_cases he : pairDist (Sym2.map x e) = pairDist (Sym2.map x p)
  · exact Filter.Eventually.of_forall (fun _ _ => he)
  · have ht := ((tendsto_pairDist hf e).sub (tendsto_pairDist hf p)).eventually_ne
      (sub_ne_zero.mpr he)
    exact ht.mono (fun _ h hEq => False.elim (h (sub_eq_zero.mpr hEq)))

/-- The selected nearby class has at most the cardinality of its entire limiting class. -/
theorem eventually_labelMultiplicity_le {α β : Type*} [Fintype α] {l : Filter β}
    {f : β → α → Plane} {x : α → Plane}
    (hf : ∀ i, Filter.Tendsto (fun t => f t i) l (nhds (x i))) (p : Sym2 α) :
    ∀ᶠ t in l, labelMultiplicity (f t) (pairDist (Sym2.map (f t) p)) ≤
      labelMultiplicity x (pairDist (Sym2.map x p)) := by
  classical
  apply (eventually_class_subset hf p).mono
  intro t ht
  apply Finset.card_le_card
  intro e he
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).1,
    ht e (Finset.mem_filter.mp he).2⟩

/-- A collision-free finite limit makes all nearby labelled configurations collision-free. -/
theorem eventually_injective {α β : Type*} [Fintype α] {l : Filter β}
    {f : β → α → Plane} {x : α → Plane}
    (hf : ∀ i, Filter.Tendsto (fun t => f t i) l (nhds (x i)))
    (hx : Function.Injective x) : ∀ᶠ t in l, Function.Injective (f t) := by
  apply Filter.eventually_all.mpr
  intro a
  apply Filter.eventually_all.mpr
  intro b
  by_cases hab : a = b
  · exact Filter.Eventually.of_forall (fun _ _ => hab)
  · have ht := ((hf a).dist (hf b)).eventually_ne (dist_ne_zero.mpr (hx.ne hab))
    exact ht.mono (fun _ h he => False.elim (h (dist_eq_zero.mpr he)))

/-- Any positive nondiameter low-multiplicity class in a collision-free finite limit
produces an actual occurring positive nondiameter class of no greater multiplicity nearby.
No equality within the limiting class is required to persist. -/
theorem eventually_witness {α β : Type*} [Fintype α] {l : Filter β}
    {f : β → α → Plane} {x : α → Plane}
    (hf : ∀ i, Filter.Tendsto (fun t => f t i) l (nhds (x i)))
    (hx : Function.Injective x) {d : ℝ} {N : ℕ}
    (hd : 0 < d) (hdiam : d < Metric.diam (points x : Set Plane))
    (hm : 1 ≤ multiplicity (points x) d) (hN : multiplicity (points x) d ≤ N) :
    ∀ᶠ t in l, ∃ d' : ℝ, 0 < d' ∧ d' < Metric.diam (points (f t) : Set Plane) ∧
      1 ≤ multiplicity (points (f t)) d' ∧ multiplicity (points (f t)) d' ≤ N := by
  classical
  rw [multiplicity_points x hx] at hm hN
  obtain ⟨p, hp⟩ := Finset.one_le_card.mp hm
  have hpairs := (Finset.mem_filter.mp hp).1
  have hpd := (Finset.mem_filter.mp hp).2
  obtain ⟨a, b, hab⟩ : ∃ a b, d < dist (x a) (x b) := by
    by_contra h
    have hb : ∀ a b, dist (x a) (x b) ≤ d := by
      intro a b
      exact le_of_not_gt (fun ht => h ⟨a,b,ht⟩)
    have hle : Metric.diam (points x : Set Plane) ≤ d := by
      apply Metric.diam_le_of_forall_dist_le hd.le
      intro u hu v hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
      exact hb i j
    exact (not_le_of_gt hdiam) hle
  have hpos : ∀ᶠ t in l, 0 < pairDist (Sym2.map (f t) p) :=
    (tendsto_const_nhds : Filter.Tendsto (fun _ : β => (0 : ℝ)) l (nhds 0)).eventually_lt
      (tendsto_pairDist hf p) (by rwa [hpd])
  have hlt : ∀ᶠ t in l, pairDist (Sym2.map (f t) p) < dist (f t a) (f t b) :=
    (tendsto_pairDist hf p).eventually_lt ((hf a).dist (hf b)) (by rwa [hpd])
  filter_upwards [eventually_injective hf hx, eventually_labelMultiplicity_le hf p,
    hpos, hlt] with t htinj htcard htpos htlt
  let d' := pairDist (Sym2.map (f t) p)
  refine ⟨d', htpos, htlt.trans_le ?_, ?_, ?_⟩
  · apply Metric.dist_le_diam_of_mem (points (f t)).finite_toSet.isBounded
    · exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
    · exact Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩
  · rw [multiplicity_points _ htinj]
    exact Finset.one_le_card.mpr ⟨p, Finset.mem_filter.mpr ⟨hpairs, rfl⟩⟩
  · rw [multiplicity_points _ htinj]
    exact htcard.trans (by rwa [hpd])

/-- A finite labelled hull is the image of the standard simplex by its barycentre map. -/
theorem convexHull_range {ι : Type*} [Fintype ι] (x : ι → Plane) :
    convexHull ℝ (Set.range x) =
      (fun t : ι → ℝ => ∑ i, t i • x i) '' stdSimplex ℝ ι := by
  classical
  let L : (ι → ℝ) →ₗ[ℝ] Plane := ∑ i, (LinearMap.proj i).smulRight (x i)
  have he : ∀ t, L t = ∑ i, t i • x i := by
    intro t
    simp [L]
  have hr : Set.range x = L '' (Set.range (fun i : ι => Pi.single i (1 : ℝ))) := by
    rw [← Set.range_comp]
    congr 1
    funext i
    simp [he]
  rw [hr, ← LinearMap.image_convexHull, convexHull_rangle_single_eq_stdSimplex]
  simp only [he]

/-- Membership in the convex hull of finitely many continuously moving labelled points
is a closed relation, including at collisions. -/
theorem isClosed_hull_relation {ι : Type*} [Fintype ι] :
    IsClosed {p : (ι → Plane) × Plane | p.2 ∈ convexHull ℝ (Set.range p.1)} := by
  classical
  let S := stdSimplex ℝ ι
  letI : CompactSpace S := by dsimp [S]; infer_instance
  have hc : IsClosed {q : ((ι → Plane) × Plane) × S |
      (∑ i, q.2.val i • q.1.1 i) = q.1.2} := by
    apply isClosed_eq _ continuous_fst.snd
    exact continuous_finsetSum _ (fun i _ =>
      ((continuous_apply i).comp continuous_snd.subtype_val).smul
        ((continuous_apply i).comp continuous_fst.fst))
  have hp := isClosedMap_fst_of_compactSpace _ hc
  convert hp using 1
  ext p
  change p.2 ∈ convexHull ℝ (Set.range p.1) ↔
    p ∈ Prod.fst '' {q : ((ι → Plane) × Plane) × S |
      (∑ i, q.2.val i • q.1.1 i) = q.1.2}
  rw [convexHull_range]
  constructor
  · rintro ⟨t, ht, he⟩
    exact ⟨(p, ⟨t, ht⟩), he, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.2.val, q.2.property, hq⟩

/-- Closed-ball depth in a finite hull survives pointwise limits. This is true ambient
Euclidean depth, not relative interior or membership in a collapsed hull. -/
theorem closedBall_subset_hull_limit {ι β : Type*} [Fintype ι] {l : Filter β}
    [l.NeBot] {h : β → ι → Plane} {z : β → Plane} {h₀ : ι → Plane} {z₀ : Plane}
    {Θ : ℝ} (hh : ∀ i, Filter.Tendsto (fun t => h t i) l (nhds (h₀ i)))
    (hz : Filter.Tendsto z l (nhds z₀))
    (hdepth : ∀ᶠ t in l, Metric.closedBall (z t) Θ ⊆ convexHull ℝ (Set.range (h t))) :
    Metric.closedBall z₀ Θ ⊆ convexHull ℝ (Set.range h₀) := by
  intro p hp
  let v := p - z₀
  have hv : ‖v‖ ≤ Θ := by simpa only [v, Metric.mem_closedBall, dist_eq_norm] using hp
  have hmem : ∀ᶠ t in l, (h t, z t + v) ∈
      {q : (ι → Plane) × Plane | q.2 ∈ convexHull ℝ (Set.range q.1)} := by
    apply hdepth.mono
    intro t ht
    apply ht
    simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left] using hv
  have ht := (tendsto_pi_nhds.mpr hh).prodMk_nhds (hz.add_const v)
  have hm := isClosed_hull_relation.mem_of_tendsto ht hmem
  change z₀ + v ∈ convexHull ℝ (Set.range h₀) at hm
  simpa only [v, add_sub_cancel] using hm

/-- The actual point set is exactly the range of the labels. -/
theorem coe_points {α : Type*} [Fintype α] (x : α → Plane) :
    (points x : Set Plane) = Set.range x := by
  classical
  ext p
  simp [points]

/-- Hull labels and the two interior labels are disjoint indexing domains. -/
abbrev Labels (m : ℕ) := Fin m ⊕ Fin 2

/-- Splitting the label domain yields precisely the hull and the two interior points. -/
theorem points_sum (m : ℕ) (x : Labels m → Plane) :
    points x = insert (x (Sum.inr 0)) (insert (x (Sum.inr 1))
      (points (fun i : Fin m => x (Sum.inl i)))) := by
  classical
  ext p
  simp only [points, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_insert]
  constructor
  · rintro ⟨i, rfl⟩
    rcases i with i | i
    · exact Or.inr (Or.inr ⟨i, rfl⟩)
    · fin_cases i <;> simp
  · rintro (rfl | rfl | ⟨i, rfl⟩)
    · exact ⟨Sum.inr 0, rfl⟩
    · exact ⟨Sum.inr 1, rfl⟩
    · exact ⟨Sum.inl i, rfl⟩

/-- Positive closed-ball depth implies genuine ambient interior. -/
theorem interior_of_closedBall_subset {K : Set Plane} {z : Plane} {Θ : ℝ}
    (hΘ : 0 < Θ) (h : Metric.closedBall z Θ ⊆ K) : z ∈ interior K := by
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (Metric.closedBall_mem_nhds z hΘ) h)

/-- The checked exact-circle producer supplies a witness at a collision-free labelled
limit; finite-class stability transports it to every sufficiently late configuration. -/
theorem circle_limit_eventually_witness {m : ℕ} {β : Type*} {l : Filter β}
    {f : β → Labels m → Plane} {x : Labels m → Plane} {O : Plane} {R Θ : ℝ}
    (hm : 6 ≤ m) (hR : 0 < R) (hΘ : 0 < Θ)
    (hf : ∀ i, Filter.Tendsto (fun t => f t i) l (nhds (x i)))
    (hx : Function.Injective x)
    (hcircle : ∀ i : Fin m, dist (x (Sum.inl i)) O = R)
    (hz : Metric.closedBall (x (Sum.inr 0)) Θ ⊆
      convexHull ℝ (Set.range (fun i : Fin m => x (Sum.inl i))))
    (hw : Metric.closedBall (x (Sum.inr 1)) Θ ⊆
      convexHull ℝ (Set.range (fun i : Fin m => x (Sum.inl i)))) :
    ∀ᶠ t in l, ∃ d : ℝ, 0 < d ∧ d < Metric.diam (points (f t) : Set Plane) ∧
      1 ≤ multiplicity (points (f t)) d ∧ multiplicity (points (f t)) d ≤ m + 2 := by
  classical
  let H := points (fun i : Fin m => x (Sum.inl i))
  have hH : H.card = m := by
    change (points (fun i : Fin m => x (Sum.inl i))).card = m
    simpa only [Fintype.card_fin] using
      card_points (fun i : Fin m => x (Sum.inl i)) (fun _ _ h => Sum.inl_injective (hx h))
  have hc : ∀ p ∈ H, dist p O = R := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact hcircle i
  have hz' : x (Sum.inr 0) ∈ interior (convexHull ℝ (H : Set Plane)) := by
    rw [coe_points]
    exact interior_of_closedBall_subset hΘ hz
  have hw' : x (Sum.inr 1) ∈ interior (convexHull ℝ (H : Set Plane)) := by
    rw [coe_points]
    exact interior_of_closedBall_subset hΘ hw
  have hzw : x (Sum.inr 0) ≠ x (Sum.inr 1) := hx.ne (by simp)
  obtain ⟨d, hd, hdiam, hmul, hbound⟩ := circle_witness H O _ _ R
    (by rw [hH]; exact hm) hR hc hz' hw' hzw
  have hset : insert (x (Sum.inr 0)) (insert (x (Sum.inr 1)) H) = points x :=
    (points_sum m x).symm
  rw [hset] at hdiam hmul hbound
  have hcard : (points x).card = m + 2 := by
    rw [card_points x hx, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  rw [hcard] at hbound
  exact eventually_witness hf hx hd hdiam hmul hbound

/-- Uniform qualitative near-circle stability for `m` hull labels and two interior
labels. The modulus depends only on the fixed parameters, not on a configuration or a
chosen limiting distance class. An anchored label and actual diameter one bound all points. -/
theorem uniform_near_circle (m : ℕ) (Δ Θ rminus rplus C : ℝ)
    (hm : 6 ≤ m) (hΔ : 0 < Δ) (hΘ : 0 < Θ) (hrminus : 0 < rminus)
    (_hrplus : 0 < rplus) (_hC : 0 < C) (_hrange : rminus < rplus) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (x : Labels m → Plane) (O : Plane) (R ε : ℝ),
      0 ≤ ε → ε < ε₀ → (∃ i : Fin m, x (Sum.inl i) = 0) →
      Metric.diam (points x : Set Plane) = 1 →
      (∀ i j, i ≠ j → Δ ≤ dist (x i) (x j)) →
      Metric.closedBall (x (Sum.inr 0)) Θ ⊆
        convexHull ℝ (Set.range (fun i : Fin m => x (Sum.inl i))) →
      Metric.closedBall (x (Sum.inr 1)) Θ ⊆
        convexHull ℝ (Set.range (fun i : Fin m => x (Sum.inl i))) →
      ‖O‖ ≤ C → rminus ≤ R → R ≤ rplus →
      (∀ i : Fin m, |dist (x (Sum.inl i)) O - R| ≤ ε) →
      ∃ d : ℝ, 0 < d ∧ d < Metric.diam (points x : Set Plane) ∧
        1 ≤ multiplicity (points x) d ∧ multiplicity (points x) d ≤ m + 2 := by
  classical
  by_contra hfail
  push Not at hfail
  have hseq : ∀ j : ℕ, ∃ (x : Labels m → Plane) (O : Plane) (R : ℝ),
      (∀ i, ‖x i‖ ≤ 1) ∧
      (∀ i k, i ≠ k → Δ ≤ dist (x i) (x k)) ∧
      Metric.closedBall (x (Sum.inr 0)) Θ ⊆
        convexHull ℝ (Set.range (fun i : Fin m => x (Sum.inl i))) ∧
      Metric.closedBall (x (Sum.inr 1)) Θ ⊆
        convexHull ℝ (Set.range (fun i : Fin m => x (Sum.inl i))) ∧
      ‖O‖ ≤ C ∧ rminus ≤ R ∧ R ≤ rplus ∧
      (∀ i : Fin m, |dist (x (Sum.inl i)) O - R| ≤ 1 / ((j : ℝ) + 1)) ∧
      ¬ (∃ d : ℝ, 0 < d ∧ d < Metric.diam (points x : Set Plane) ∧
        1 ≤ multiplicity (points x) d ∧ multiplicity (points x) d ≤ m + 2) := by
    intro j
    obtain ⟨x, O, R, ε, hε, hεlt, ha, hdiam, hsep, hz, hw, hO, hRlo, hRhi,
      herr, hbad⟩ := hfail (1 / ((j : ℝ) + 1)) (by positivity)
    refine ⟨x, O, R, ?_, hsep, hz, hw, hO, hRlo, hRhi,
      fun i => (herr i).trans hεlt.le, ?_⟩
    · obtain ⟨a, ha⟩ := ha
      intro i
      have hd := Metric.dist_le_diam_of_mem (points x).finite_toSet.isBounded
        (show x i ∈ (points x : Set Plane) from Finset.mem_image.mpr
          ⟨i, Finset.mem_univ i, rfl⟩)
        (show x (Sum.inl a) ∈ (points x : Set Plane) from Finset.mem_image.mpr
          ⟨Sum.inl a, Finset.mem_univ _, rfl⟩)
      simpa only [ha, dist_zero_right, hdiam] using hd
    · simpa only [not_exists, not_and, not_le] using hbad
  choose x O R hs using hseq
  let K : Set ((Labels m → Plane) × Plane × ℝ) :=
    {y | ∀ i, y i ∈ Metric.closedBall (0 : Plane) 1} ×ˢ
      (Metric.closedBall (0 : Plane) C ×ˢ Set.Icc rminus rplus)
  have hK : IsCompact K :=
    (isCompact_pi_infinite (fun _ => isCompact_closedBall (0 : Plane) 1)).prod
      ((isCompact_closedBall (0 : Plane) C).prod isCompact_Icc)
  have hmem : ∀ j, (x j, O j, R j) ∈ K := by
    intro j
    exact ⟨fun i => by simpa only [Metric.mem_closedBall, dist_zero_right] using (hs j).1 i,
      by simpa only [Metric.mem_closedBall, dist_zero_right] using (hs j).2.2.2.2.1,
      (hs j).2.2.2.2.2.1, (hs j).2.2.2.2.2.2.1⟩
  obtain ⟨q, hq, φ, hφ, ht⟩ := hK.tendsto_subseq hmem
  let x₀ := q.1
  let O₀ := q.2.1
  let R₀ := q.2.2
  have hxall : Filter.Tendsto (fun j => x (φ j)) Filter.atTop (nhds x₀) :=
    (continuous_fst.tendsto q).comp ht
  have hx : ∀ i, Filter.Tendsto (fun j => x (φ j) i) Filter.atTop (nhds (x₀ i)) :=
    tendsto_pi_nhds.mp hxall
  have hO : Filter.Tendsto (O ∘ φ) Filter.atTop (nhds O₀) :=
    (continuous_snd.fst.tendsto q).comp ht
  have hR : Filter.Tendsto (R ∘ φ) Filter.atTop (nhds R₀) :=
    (continuous_snd.snd.tendsto q).comp ht
  have hsep : ∀ i k, i ≠ k → Δ ≤ dist (x₀ i) (x₀ k) := by
    intro i k hik
    exact le_of_tendsto_of_tendsto tendsto_const_nhds ((hx i).dist (hx k))
      (Filter.Eventually.of_forall (fun j => (hs (φ j)).2.1 i k hik))
  have hinj : Function.Injective x₀ := by
    intro i k he
    by_contra hik
    have hh := hsep i k hik
    rw [he, dist_self] at hh
    exact (not_le_of_gt hΔ) hh
  have hz : Metric.closedBall (x₀ (Sum.inr 0)) Θ ⊆
      convexHull ℝ (Set.range (fun i : Fin m => x₀ (Sum.inl i))) :=
    closedBall_subset_hull_limit (fun i => hx (Sum.inl i)) (hx (Sum.inr 0))
      (Filter.Eventually.of_forall (fun j => (hs (φ j)).2.2.1))
  have hw : Metric.closedBall (x₀ (Sum.inr 1)) Θ ⊆
      convexHull ℝ (Set.range (fun i : Fin m => x₀ (Sum.inl i))) :=
    closedBall_subset_hull_limit (fun i => hx (Sum.inl i)) (hx (Sum.inr 1))
      (Filter.Eventually.of_forall (fun j => (hs (φ j)).2.2.2.1))
  have hcircle : ∀ i : Fin m, dist (x₀ (Sum.inl i)) O₀ = R₀ := by
    intro i
    have hlim := (((hx (Sum.inl i)).dist hO).sub hR).abs
    have hzero : |dist (x₀ (Sum.inl i)) O₀ - R₀| ≤ 0 :=
      le_of_tendsto_of_tendsto hlim
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
        (Filter.Eventually.of_forall (fun j => (hs (φ j)).2.2.2.2.2.2.2.1 i))
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _)))
  have hRpos : 0 < R₀ := hrminus.trans_le hq.2.2.1
  have hgood := circle_limit_eventually_witness hm hRpos hΘ hx hinj hcircle hz hw
  obtain ⟨j, hj⟩ := hgood.exists
  exact (hs (φ j)).2.2.2.2.2.2.2.2 hj

/-- For fixed `n ≥ 8` and positive nondegeneracy parameters there is a uniform positive
radial tolerance. Every diameter-one labelled configuration with first hull label zero,
separation at least `Δ`, two closed-ball interior margins, bounded centre and radius, and
hull radial errors below that tolerance has an actual occurring nondiameter distance of
unordered loop-free multiplicity between one and `n`. Its actual point set has cardinal `n`. -/
theorem near_circle_stability (n : ℕ) (hn : 8 ≤ n) (Δ Θ rminus rplus C : ℝ)
    (hΔ : 0 < Δ) (hΘ : 0 < Θ) (hrminus : 0 < rminus)
    (hrplus : 0 < rplus) (hC : 0 < C) (hrange : rminus < rplus) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (x : Labels (n - 2) → Plane) (O : Plane) (R ε : ℝ),
      0 ≤ ε → ε < ε₀ → x (Sum.inl ⟨0, by omega⟩) = 0 →
      Metric.diam (points x : Set Plane) = 1 →
      (∀ i j, i ≠ j → Δ ≤ dist (x i) (x j)) →
      Metric.closedBall (x (Sum.inr 0)) Θ ⊆
        convexHull ℝ (Set.range (fun i : Fin (n - 2) => x (Sum.inl i))) →
      Metric.closedBall (x (Sum.inr 1)) Θ ⊆
        convexHull ℝ (Set.range (fun i : Fin (n - 2) => x (Sum.inl i))) →
      ‖O‖ ≤ C → rminus ≤ R → R ≤ rplus →
      (∀ i : Fin (n - 2), |dist (x (Sum.inl i)) O - R| ≤ ε) →
      (points x).card = n ∧ ∃ d : ℝ, 0 < d ∧ d < Metric.diam (points x : Set Plane) ∧
        1 ≤ multiplicity (points x) d ∧ multiplicity (points x) d ≤ n := by
  obtain ⟨ε₀, hε₀, hu⟩ := uniform_near_circle (n - 2) Δ Θ rminus rplus C
    (by omega) hΔ hΘ hrminus hrplus hC hrange
  refine ⟨ε₀, hε₀, ?_⟩
  intro x O R ε hε hεlt ha hdiam hsep hz hw hO hRlo hRhi herr
  have hx : Function.Injective x := by
    intro i j he
    by_contra hij
    have hh := hsep i j hij
    rw [he, dist_self] at hh
    exact (not_le_of_gt hΔ) hh
  have hcard : (points x).card = n := by
    rw [card_points x hx, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    omega
  refine ⟨hcard, ?_⟩
  have hsum : n - 2 + 2 = n := by omega
  simpa only [hsum] using hu x O R ε hε hεlt ⟨⟨0, by omega⟩, ha⟩
    hdiam hsep hz hw hO hRlo hRhi herr

example : Fintype.card (Labels 6) = 8 := by decide

example : Nonempty (Labels 0) := ⟨Sum.inr 0⟩

example (n : ℕ) (hn : 8 ≤ n) : Nonempty (Fin (n - 2)) := ⟨⟨0, by omega⟩⟩

/-- A simultaneous non-vacuity model: the checked rational six-vertex circle with two
ambient-interior points is translated and scaled to first-label zero and actual diameter
one. Its eight labels are separated by a positive margin, both interior labels have a
common positive closed-ball depth, and the centre and radius have compatible positive
bounds. All six hull radial errors are exactly zero. -/
theorem normalized_exact_circle_fixture : ∃ (x : Labels 6 → Plane) (O : Plane) (R Δ Θ rminus rplus C : ℝ),
    0 < Δ ∧ 0 < Θ ∧ 0 < rminus ∧ 0 < rplus ∧ 0 < C ∧ rminus < rplus ∧
    x (Sum.inl 0) = 0 ∧ Metric.diam (points x : Set Plane) = 1 ∧
    (∀ i j, i ≠ j → Δ ≤ dist (x i) (x j)) ∧
    Metric.closedBall (x (Sum.inr 0)) Θ ⊆ convexHull ℝ (Set.range (fun i : Fin 6 => x (Sum.inl i))) ∧
    Metric.closedBall (x (Sum.inr 1)) Θ ⊆ convexHull ℝ (Set.range (fun i : Fin 6 => x (Sum.inl i))) ∧
    ‖O‖ ≤ C ∧ rminus ≤ R ∧ R ≤ rplus ∧
    (∀ i : Fin 6, dist (x (Sum.inl i)) O = R) ∧ (points x).card = 8 ∧
    (∀ i : Fin 6, x (Sum.inl i) ∈
      (convexHull ℝ (Set.range (fun j : Fin 6 => x (Sum.inl j)))).extremePoints ℝ) := by
  classical
  obtain ⟨H,z,w,hcard,hcircle,_hext,hz,hw,hzw⟩ := rational_circle_fixture
  let e := (H.equivFinOfCardEq hcard).symm
  let h : Fin 6 → Plane := fun i => (e i).val
  have hH : points h = H := by
    ext p
    simp only [points, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i,rfl⟩; exact (e i).property
    · intro hp
      exact ⟨e.symm ⟨p,hp⟩, congrArg Subtype.val (e.apply_symm_apply ⟨p,hp⟩)⟩
  let y : Labels 6 → Plane := Sum.elim h (fun j => if j = 0 then z else w)
  have hyset : points y = insert z (insert w H) := by
    rw [points_sum]
    simp only [y, Sum.elim_inr, Sum.elim_inl, hH]
    norm_num
  have hycard : (points y).card = Fintype.card (Labels 6) := by
    rw [hyset, card_insert_interiors H 0 z w (by norm_num) hcircle hz hw hzw, hcard]
    simp [Labels]
  have hyinj : Function.Injective y := by
    have hinj : Set.InjOn y (Finset.univ : Finset (Labels 6)) := by
      apply Finset.card_image_iff.mp
      change (points y).card = _
      simpa only [Finset.card_univ] using hycard
    exact fun i j he => hinj (Finset.mem_univ i) (Finset.mem_univ j) he
  let D := Metric.diam (points y : Set Plane)
  have hD : 0 < D := diam_pos (points y) (by rw [hycard]; simp [Labels])
  let r := D⁻¹
  have hr : 0 < r := inv_pos.mpr hD
  let a := y (Sum.inl 0)
  let T : Plane → Plane := fun p => r • (p - a)
  let t : Plane ≃ₜ Plane := (Homeomorph.addRight (-a)).trans (Homeomorph.smulOfNeZero r hr.ne')
  have ht : ∀ p, t p = T p := by intro p; rfl
  let A : Plane →ᵃ[ℝ] Plane := (r • (LinearMap.id : Plane →ₗ[ℝ] Plane)).toAffineMap.comp
    (AffineEquiv.constVAdd ℝ Plane (-a)).toAffineMap
  have hA : ∀ p, A p = T p := by
    intro p
    change r • (-a + p) = r • (p - a)
    congr 1
    abel
  have hdist : ∀ p q, dist (T p) (T q) = r * dist p q := by
    intro p q
    simp only [T, dist_smul₀, Real.norm_eq_abs, abs_of_pos hr, dist_sub_right]
  let x : Labels 6 → Plane := T ∘ y
  have hxinj : Function.Injective x := by
    intro i j he
    exact hyinj (t.injective (by simpa only [ht, x, Function.comp_apply] using he))
  have hxdiam : Metric.diam (points x : Set Plane) = 1 := by
    apply le_antisymm
    · apply Metric.diam_le_of_forall_dist_le (by norm_num)
      intro p hp q hq
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hq
      have hd := Metric.dist_le_diam_of_mem (points y).finite_toSet.isBounded
        (show y i ∈ (points y : Set Plane) from Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
        (show y j ∈ (points y : Set Plane) from Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
      change dist (T (y i)) (T (y j)) ≤ 1
      rw [hdist]
      calc r * dist (y i) (y j) ≤ r * D := mul_le_mul_of_nonneg_left hd hr.le
           _ = 1 := inv_mul_cancel₀ hD.ne'
    · have hb : D ≤ D * Metric.diam (points x : Set Plane) := by
        apply Metric.diam_le_of_forall_dist_le (mul_nonneg hD.le Metric.diam_nonneg)
        intro p hp q hq
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hq
        have hd := Metric.dist_le_diam_of_mem (points x).finite_toSet.isBounded
          (show x i ∈ (points x : Set Plane) from Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
          (show x j ∈ (points x : Set Plane) from Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
        change dist (T (y i)) (T (y j)) ≤ _ at hd
        rw [hdist] at hd
        have hh := mul_le_mul_of_nonneg_left hd hD.le
        simpa only [r, ← mul_assoc, mul_inv_cancel₀ hD.ne', one_mul] using hh
      nlinarith
  have hhull : T '' convexHull ℝ (H : Set Plane) =
      convexHull ℝ (Set.range (fun i : Fin 6 => x (Sum.inl i))) := by
    have himage : A '' (H : Set Plane) = Set.range (fun i : Fin 6 => x (Sum.inl i)) := by
      rw [← hH, coe_points]
      ext p
      simp only [Set.mem_image, Set.mem_range, hA, x, y, Sum.elim_inl, Function.comp_apply]
      constructor
      · rintro ⟨q,⟨i,rfl⟩,rfl⟩; exact ⟨i,rfl⟩
      · rintro ⟨i,rfl⟩; exact ⟨h i,⟨i,rfl⟩,rfl⟩
    have hAT : (A : Plane → Plane) = T := funext hA
    calc T '' convexHull ℝ (H : Set Plane) = A '' convexHull ℝ (H : Set Plane) := by rw [hAT]
         _ = convexHull ℝ (A '' (H : Set Plane)) := A.image_convexHull (H : Set Plane)
         _ = _ := by rw [himage]
  have hzi : x (Sum.inr 0) ∈ interior (convexHull ℝ (Set.range (fun i : Fin 6 => x (Sum.inl i)))) := by
    rw [← hhull, ← show t '' convexHull ℝ (H : Set Plane) = T '' convexHull ℝ (H : Set Plane) from by simp only [ht], ← t.image_interior]
    exact ⟨z,hz,by simp [ht,x,y]⟩
  have hwi : x (Sum.inr 1) ∈ interior (convexHull ℝ (Set.range (fun i : Fin 6 => x (Sum.inl i)))) := by
    rw [← hhull, ← show t '' convexHull ℝ (H : Set Plane) = T '' convexHull ℝ (H : Set Plane) from by simp only [ht], ← t.image_interior]
    exact ⟨w,hw,by simp [ht,x,y]⟩
  obtain ⟨θz,hθz,hballz⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzi)
  obtain ⟨θw,hθw,hballw⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hwi)
  let Θ := min θz θw / 2
  have hΘ : 0 < Θ := by dsimp [Θ]; positivity
  let S := (pairs (Finset.univ : Finset (Labels 6))).image (fun p => pairDist (Sym2.map x p))
  have hS : S.Nonempty := by
    refine ⟨dist (x (Sum.inr 0)) (x (Sum.inr 1)), Finset.mem_image.mpr ⟨s(Sum.inr 0,Sum.inr 1), ?_, rfl⟩⟩
    exact (mk_mem_pairs _ _ _).mpr ⟨Finset.mem_univ _,Finset.mem_univ _,by simp⟩
  let Δ := S.min' hS
  have hΔ : 0 < Δ := by
    change 0 < S.min' hS
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp (S.min'_mem hS)
    induction p using Sym2.ind with
    | _ i j =>
      have hij := ((mk_mem_pairs _ _ _).mp hp).2.2
      rw [← he, Sym2.map_mk, pairDist_mk]
      exact dist_pos.mpr (hxinj.ne hij)
  have hsep : ∀ i j, i ≠ j → Δ ≤ dist (x i) (x j) := by
    intro i j hij
    exact S.min'_le _ (Finset.mem_image.mpr ⟨s(i,j),
      (mk_mem_pairs _ _ _).mpr ⟨Finset.mem_univ _,Finset.mem_univ _,hij⟩,rfl⟩)
  have hcirclex : ∀ i : Fin 6, dist (x (Sum.inl i)) (T 0) = r := by
    intro i
    change dist (T (h i)) (T 0) = r
    rw [hdist,hcircle (h i) (by rw [← hH]; exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩),mul_one]
  have hcardx : (points x).card = 8 := by
    rw [card_points x hxinj]
    decide
  have hextx : ∀ i : Fin 6, x (Sum.inl i) ∈
      (convexHull ℝ (Set.range (fun j : Fin 6 => x (Sum.inl j)))).extremePoints ℝ := by
    have hsub : convexHull ℝ (Set.range (fun j : Fin 6 => x (Sum.inl j))) ⊆
        Metric.closedBall (T 0) r := by
      apply convexHull_min _ (convex_closedBall (T 0) r)
      rintro p ⟨i,rfl⟩
      exact (hcirclex i).le
    intro i
    apply inter_extremePoints_subset_extremePoints_of_subset hsub
    exact ⟨subset_convexHull ℝ _ ⟨i,rfl⟩,
      StrictConvexSpace.sphere_subset_extremePoints_closedBall (T 0) hr.ne'
        (by simpa only [Metric.mem_sphere] using hcirclex i)⟩
  refine ⟨x,T 0,r,Δ,Θ,r/2,2*r,‖T 0‖+1,hΔ,hΘ,by positivity,by positivity,
    by positivity,by linarith,?_,hxdiam,hsep,?_,?_,by linarith [norm_nonneg (T 0)],
    by linarith,by linarith,hcirclex,hcardx,hextx⟩
  · simp [x,T,a]
  · exact (Metric.closedBall_subset_ball (by dsimp [Θ]; linarith [min_le_left θz θw])).trans hballz
  · exact (Metric.closedBall_subset_ball (by dsimp [Θ]; linarith [min_le_right θz θw])).trans hballw

end Erdos132.NearCircleStability
