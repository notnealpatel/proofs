import Erdos.Erdos132.NearCircleStability
import Erdos.Erdos132.EvenThreeInteriorCircle
import Erdos.Erdos132.ThreeInteriorCenter
import Erdos.Erdos132.ThreeInteriorOffCenter

set_option autoImplicit false

open Erdos132.TwoInteriorCircle Erdos132.NearCircleStability

namespace Erdos132.NearCircleThree

/-- Disjoint labels for the hull and all three interior points. -/
abbrev Labels (m : ℕ) := Fin m ⊕ Fin 3

example : Fintype.card (Labels 6) = 9 := by decide
example : Nonempty (Labels 0) := ⟨Sum.inr 0⟩
example (n : ℕ) (hn : 9 ≤ n) : Nonempty (Fin (n - 3)) := ⟨⟨0, by omega⟩⟩

/-- The actual range splits into the hull and the three interior labels. -/
theorem points_sum (m : ℕ) (x : Labels m → Plane) :
    points x = insert (x (Sum.inr 0)) (insert (x (Sum.inr 1))
      (insert (x (Sum.inr 2)) (points (fun i : Fin m => x (Sum.inl i))))) := by
  classical
  ext p
  simp only [points, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨i, rfl⟩
    rcases i with i | i
    · exact Or.inr (Or.inr (Or.inr ⟨i, rfl⟩))
    · fin_cases i <;> simp
  · rintro (rfl | rfl | rfl | ⟨i, rfl⟩)
    · exact ⟨Sum.inr 0, rfl⟩
    · exact ⟨Sum.inr 1, rfl⟩
    · exact ⟨Sum.inr 2, rfl⟩
    · exact ⟨Sum.inl i, rfl⟩

/-- The adopted even, odd-center and odd-off-center producers jointly supply an
occurring positive nondiameter class for every injective three-interior circle. -/
theorem exact_circle_witness (m : ℕ) (x : Labels m → Plane) (O : Plane) (R Θ : ℝ)
    (hm : 6 ≤ m) (hR : 0 < R) (hΘ : 0 < Θ) (hx : Function.Injective x)
    (hcircle : ∀ i : Fin m, dist (x (Sum.inl i)) O = R)
    (hdepth : ∀ j : Fin 3, Metric.closedBall (x (Sum.inr j)) Θ ⊆
      convexHull ℝ (Set.range (fun i : Fin m => x (Sum.inl i)))) :
    ∃ d : ℝ, 0 < d ∧ d < Metric.diam (points x : Set Plane) ∧
      1 ≤ multiplicity (points x) d ∧ multiplicity (points x) d ≤ m + 3 := by
  classical
  let H := points (fun i : Fin m => x (Sum.inl i))
  let z := x (Sum.inr 0)
  let w := x (Sum.inr 1)
  let v := x (Sum.inr 2)
  have hH : H.card = m := by
    simpa only [Fintype.card_fin] using
      card_points (fun i : Fin m => x (Sum.inl i)) (fun _ _ h => Sum.inl_injective (hx h))
  have hc : ∀ p ∈ H, dist p O = R := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact hcircle i
  have hi : ∀ j : Fin 3, x (Sum.inr j) ∈ interior (convexHull ℝ (H : Set Plane)) := by
    intro j
    rw [coe_points]
    exact interior_of_closedBall_subset hΘ (hdepth j)
  have hzw : z ≠ w := hx.ne (by simp)
  have hzv : z ≠ v := hx.ne (by simp)
  have hwv : w ≠ v := hx.ne (by simp)
  have hset : insert z (insert w (insert v H)) = points x := (points_sum m x).symm
  have hcard : (points x).card = m + 3 := by
    rw [card_points x hx, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  by_cases he : Even (m + 3)
  · have hm7 : 7 ≤ H.card := by
      rw [hH]
      obtain ⟨k, hk⟩ := he
      omega
    have he' : Even (insert z (insert w (insert v H))).card := by rwa [hset, hcard]
    obtain ⟨d, hd, hlt, hmul, hb⟩ := EvenThreeInteriorCircle.circle_witness H O z w v R
      hm7 hR hc (hi 0) (hi 1) (hi 2) hzw hzv hwv he'
    rw [hset] at hlt hmul hb
    rw [hcard] at hb
    exact ⟨d, hd, hlt, hmul, hb⟩
  · have ho : Odd (m + 3) := Nat.not_even_iff_odd.mp he
    have hn : 9 ≤ m + 3 := by omega
    have hH' : H.card = m + 3 - 3 := by omega
    by_cases hzO : z = O
    · obtain ⟨_, d, hd, hlt, hmul, hb⟩ := ThreeInteriorCenter.one_center_circle
        (m + 3) H O w v R hn ho hH' hR hc (by rw [← hzO]; exact hzw.symm)
        (by rw [← hzO]; exact hzv.symm) hwv (by rw [← hzO]; exact hi 0) (hi 1) (hi 2)
      rw [← hzO, hset] at hlt hmul hb
      exact ⟨d, hd, hlt, hmul, hb⟩
    · by_cases hwO : w = O
      · obtain ⟨_, d, hd, hlt, hmul, hb⟩ := ThreeInteriorCenter.one_center_circle
          (m + 3) H O z v R hn ho hH' hR hc hzO
          (by rw [← hwO]; exact hwv.symm) hzv (by rw [← hwO]; exact hi 1) (hi 0) (hi 2)
        have hs : insert O (insert z (insert v H)) = points x := by
          rw [← hwO, Finset.insert_comm, hset]
        rw [hs] at hlt hmul hb
        exact ⟨d, hd, hlt, hmul, hb⟩
      · by_cases hvO : v = O
        · obtain ⟨_, d, hd, hlt, hmul, hb⟩ := ThreeInteriorCenter.one_center_circle
            (m + 3) H O z w R hn ho hH' hR hc hzO hwO hzw
            (by rw [← hvO]; exact hi 2) (hi 0) (hi 1)
          have hs : insert O (insert z (insert w H)) = points x := by
            rw [← hvO, Finset.insert_comm v z, Finset.insert_comm v w, hset]
          rw [hs] at hlt hmul hb
          exact ⟨d, hd, hlt, hmul, hb⟩
        · obtain ⟨_, d, hd, hlt, _hocc, hmul, hb⟩ := ThreeInteriorOffCenter.circle_witness
            (m + 3) H O R z w v hn ho hH' hR hc hzO hwO hvO hzw hzv hwv
            (hi 0) (hi 1) (hi 2)
          rw [hset] at hlt hmul hb
          exact ⟨d, hd, hlt, hmul, hb⟩

/-- Uniform qualitative near-circle stability for `m` hull labels and three interior
labels. The modulus depends only on the fixed parameters, not on a configuration or a
chosen limiting distance class. An anchored label and actual diameter one bound all points. -/
theorem uniform_near_circle (m : ℕ) (Δ Θ rminus rplus C : ℝ)
    (hm : 6 ≤ m) (hΔ : 0 < Δ) (hΘ : 0 < Θ) (hrminus : 0 < rminus)
    (_hrplus : 0 < rplus) (_hC : 0 < C) (_hrange : rminus < rplus) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (x : Labels m → Plane) (O : Plane) (R ε : ℝ),
      0 ≤ ε → ε < ε₀ → (∃ i : Fin m, x (Sum.inl i) = 0) →
      Metric.diam (points x : Set Plane) = 1 →
      (∀ i j, i ≠ j → Δ ≤ dist (x i) (x j)) →
      (∀ j : Fin 3, Metric.closedBall (x (Sum.inr j)) Θ ⊆
        convexHull ℝ (Set.range (fun i : Fin m => x (Sum.inl i)))) →
      ‖O‖ ≤ C → rminus ≤ R → R ≤ rplus →
      (∀ i : Fin m, |dist (x (Sum.inl i)) O - R| ≤ ε) →
      ∃ d : ℝ, 0 < d ∧ d < Metric.diam (points x : Set Plane) ∧
        1 ≤ multiplicity (points x) d ∧ multiplicity (points x) d ≤ m + 3 := by
  classical
  by_contra hfail
  push Not at hfail
  have hseq : ∀ j : ℕ, ∃ (x : Labels m → Plane) (O : Plane) (R : ℝ),
      (∀ i, ‖x i‖ ≤ 1) ∧
      (∀ i k, i ≠ k → Δ ≤ dist (x i) (x k)) ∧
      (∀ j : Fin 3, Metric.closedBall (x (Sum.inr j)) Θ ⊆
        convexHull ℝ (Set.range (fun i : Fin m => x (Sum.inl i)))) ∧
      ‖O‖ ≤ C ∧ rminus ≤ R ∧ R ≤ rplus ∧
      (∀ i : Fin m, |dist (x (Sum.inl i)) O - R| ≤ 1 / ((j : ℝ) + 1)) ∧
      ¬ (∃ d : ℝ, 0 < d ∧ d < Metric.diam (points x : Set Plane) ∧
        1 ≤ multiplicity (points x) d ∧ multiplicity (points x) d ≤ m + 3) := by
    intro j
    obtain ⟨x, O, R, ε, hε, hεlt, ha, hdiam, hsep, hdepth, hO, hRlo, hRhi,
      herr, hbad⟩ := hfail (1 / ((j : ℝ) + 1)) (by positivity)
    refine ⟨x, O, R, ?_, hsep, hdepth, hO, hRlo, hRhi,
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
      by simpa only [Metric.mem_closedBall, dist_zero_right] using (hs j).2.2.2.1,
      (hs j).2.2.2.2.1, (hs j).2.2.2.2.2.1⟩
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
  have hdepth : ∀ j : Fin 3, Metric.closedBall (x₀ (Sum.inr j)) Θ ⊆
      convexHull ℝ (Set.range (fun i : Fin m => x₀ (Sum.inl i))) := by
    intro j
    exact closedBall_subset_hull_limit (fun i => hx (Sum.inl i)) (hx (Sum.inr j))
      (Filter.Eventually.of_forall (fun k => (hs (φ k)).2.2.1 j))
  have hcircle : ∀ i : Fin m, dist (x₀ (Sum.inl i)) O₀ = R₀ := by
    intro i
    have hlim := (((hx (Sum.inl i)).dist hO).sub hR).abs
    have hzero : |dist (x₀ (Sum.inl i)) O₀ - R₀| ≤ 0 :=
      le_of_tendsto_of_tendsto hlim
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
        (Filter.Eventually.of_forall (fun j => (hs (φ j)).2.2.2.2.2.2.1 i))
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _)))
  have hRpos : 0 < R₀ := hrminus.trans_le hq.2.2.1
  obtain ⟨d, hd, hdiam, hmul, hb⟩ := exact_circle_witness m x₀ O₀ R₀ Θ
    hm hRpos hΘ hinj hcircle hdepth
  have hgood := eventually_witness hx hinj hd hdiam hmul hb
  obtain ⟨j, hj⟩ := hgood.exists
  exact (hs (φ j)).2.2.2.2.2.2.2 hj

/-- For fixed `n ≥ 9` and positive nondegeneracy parameters there is a uniform positive
radial tolerance. Every diameter-one labelled configuration with first hull label zero,
separation at least `Δ`, three closed-ball interior margins, bounded centre and radius, and
hull radial errors below that tolerance has an actual occurring nondiameter distance of
unordered loop-free multiplicity between one and `n`. Its actual point set has cardinal `n`. -/
theorem near_circle_stability (n : ℕ) (hn : 9 ≤ n) (Δ Θ rminus rplus C : ℝ)
    (hΔ : 0 < Δ) (hΘ : 0 < Θ) (hrminus : 0 < rminus)
    (hrplus : 0 < rplus) (hC : 0 < C) (hrange : rminus < rplus) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (x : Labels (n - 3) → Plane) (O : Plane) (R ε : ℝ),
      0 ≤ ε → ε < ε₀ → x (Sum.inl ⟨0, by omega⟩) = 0 →
      Metric.diam (points x : Set Plane) = 1 →
      (∀ i j, i ≠ j → Δ ≤ dist (x i) (x j)) →
      (∀ j : Fin 3, Metric.closedBall (x (Sum.inr j)) Θ ⊆
        convexHull ℝ (Set.range (fun i : Fin (n - 3) => x (Sum.inl i)))) →
      ‖O‖ ≤ C → rminus ≤ R → R ≤ rplus →
      (∀ i : Fin (n - 3), |dist (x (Sum.inl i)) O - R| ≤ ε) →
      (points x).card = n ∧ ∃ d : ℝ, 0 < d ∧ d < Metric.diam (points x : Set Plane) ∧
        1 ≤ multiplicity (points x) d ∧ multiplicity (points x) d ≤ n := by
  obtain ⟨ε₀, hε₀, hu⟩ := uniform_near_circle (n - 3) Δ Θ rminus rplus C
    (by omega) hΔ hΘ hrminus hrplus hC hrange
  refine ⟨ε₀, hε₀, ?_⟩
  intro x O R ε hε hεlt ha hdiam hsep hdepth hO hRlo hRhi herr
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
  have hsum : n - 3 + 3 = n := by omega
  simpa only [hsum] using hu x O R ε hε hεlt ⟨⟨0, by omega⟩, ha⟩
    hdiam hsep hdepth hO hRlo hRhi herr


/-- The concrete six-vertex centered construction from the adopted center fixture,
with its cardinality exposed rather than hidden behind an existential size. -/
private theorem six_vertex_center_fixture : ∃ (H : Finset Plane) (u v : Plane),
    H.card = 6 ∧ (∀ h ∈ H, ‖h‖ = 1) ∧ u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v ∧
    (0 : Plane) ∈ interior (convexHull ℝ (H : Set Plane)) ∧
    u ∈ interior (convexHull ℝ (H : Set Plane)) ∧
    v ∈ interior (convexHull ℝ (H : Set Plane)) := by
  classical
  let A : Plane := WithLp.toLp 2 ![1,0]
  let B : Plane := WithLp.toLp 2 ![0,1]
  let C : Plane := WithLp.toLp 2 ![-1,0]
  let D : Plane := WithLp.toLp 2 ![0,-1]
  let E : Plane := WithLp.toLp 2 ![3/5,4/5]
  let F : Plane := WithLp.toLp 2 ![-3/5,-4/5]
  let H : Finset Plane := {A,B,C,D,E,F}
  have hcard : H.card = 6 := by
    norm_num [H,A,B,C,D,E,F,Finset.card_insert_of_notMem,WithLp.ext_iff,
      funext_iff,Fin.forall_fin_two]
  have hcircle : ∀ h ∈ H, ‖h‖ = 1 := by
    intro h hh
    have hs : ‖h‖ ^ 2 = 1 := by
      simp only [H,Finset.mem_insert,Finset.mem_singleton] at hh
      rcases hh with rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num [EuclideanSpace.norm_sq_eq,Fin.sum_univ_two,A,B,C,D,E,F]
    nlinarith [norm_nonneg h]
  have hanti : ∀ h ∈ H, -h ∈ H := by
    intro h hh
    simp only [H,Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [H,A,B,C,D,E,F,WithLp.ext_iff,funext_iff,Fin.forall_fin_two]
  have hA : A ∈ affineSpan ℝ (H : Set Plane) := subset_affineSpan ℝ _ (by simp [H])
  have hB : B ∈ affineSpan ℝ (H : Set Plane) := subset_affineSpan ℝ _ (by simp [H])
  have hC : C ∈ affineSpan ℝ (H : Set Plane) := subset_affineSpan ℝ _ (by simp [H])
  have htop : affineSpan ℝ (H : Set Plane) = ⊤ := by
    apply top_unique
    intro p _hp
    have hv := (affineSpan ℝ (H : Set Plane)).direction.add_mem
      ((affineSpan ℝ (H : Set Plane)).direction.smul_mem (p 1)
        (AffineSubspace.vsub_mem_direction hB hA))
      ((affineSpan ℝ (H : Set Plane)).direction.smul_mem ((1-p 0-p 1)/2)
        (AffineSubspace.vsub_mem_direction hC hA))
    have hm := AffineSubspace.vadd_mem_of_mem_direction hv hA
    have he : (p 1 • (B -ᵥ A) + ((1-p 0-p 1)/2) • (C -ᵥ A)) +ᵥ A = p := by
      ext i
      fin_cases i
      · simp only [Fin.isValue, vsub_eq_sub, vadd_eq_add, Fin.zero_eta, PiLp.add_apply,
          PiLp.smul_apply, PiLp.sub_apply, Matrix.cons_val_zero, zero_sub,
          smul_eq_mul, mul_neg, mul_one, B, A, C]
        ring
      · simp only [Fin.isValue, vsub_eq_sub, vadd_eq_add, Fin.mk_one, PiLp.add_apply,
          PiLp.smul_apply, PiLp.sub_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one,
          sub_zero, smul_eq_mul, mul_one, sub_self, mul_zero, add_zero, B, A, C]
    rwa [he] at hm
  obtain ⟨z, hz⟩ := interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr htop
  have hnegset : -(H : Set Plane) = (H : Set Plane) := by
    ext x
    simp only [Set.mem_neg, Finset.mem_coe]
    exact ⟨fun hx => by simpa only [neg_neg] using hanti (-x) hx, hanti x⟩
  have hneghull : -(convexHull ℝ (H : Set Plane)) = convexHull ℝ (H : Set Plane) := by
    rw [← convexHull_neg, hnegset]
  have hnz : -z ∈ interior (convexHull ℝ (H : Set Plane)) := by
    have himage := (Homeomorph.neg Plane).image_interior (convexHull ℝ (H : Set Plane))
    have hmem : -z ∈ (Homeomorph.neg Plane) '' interior (convexHull ℝ (H : Set Plane)) :=
      ⟨z, hz, rfl⟩
    rw [himage] at hmem
    change -z ∈ interior ((fun x : Plane => -x) '' convexHull ℝ (H : Set Plane)) at hmem
    rwa [Set.image_neg_eq_neg, hneghull] at hmem
  have h0 : (0 : Plane) ∈ interior (convexHull ℝ (H : Set Plane)) := by
    have hm := (convex_convexHull ℝ (H : Set Plane)).interior.midpoint_mem hz hnz
    simpa only [midpoint_self_neg] using hm
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior 0 h0
  let u := (ε / 2) • A
  let v := -u
  have hnA : ‖A‖ = 1 := hcircle A (by simp [H])
  have hnu : ‖u‖ = ε / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < ε / 2), hnA, mul_one]
  have hnv : ‖v‖ = ε / 2 := by rw [norm_neg, hnu]
  have hu0 : u ≠ 0 := norm_pos_iff.mp (by rw [hnu]; linarith)
  have hv0 : v ≠ 0 := norm_pos_iff.mp (by rw [hnv]; linarith)
  have huv : u ≠ v := by
    intro he
    have hz2 : u + u = 0 := by
      calc
        u + u = u + v := congrArg (fun w : Plane => u + w) he
        _ = 0 := by simp [v]
    have hucoord : ∀ i : Fin 2, u i = 0 := by
      intro i
      have hc := congrArg (fun x : Plane => x i) hz2
      simp only [PiLp.add_apply, PiLp.zero_apply] at hc
      linarith
    exact hu0 (by ext i; exact hucoord i)
  have hu : u ∈ interior (convexHull ℝ (H : Set Plane)) :=
    hball (by rw [Metric.mem_ball, dist_zero_right, hnu]; linarith)
  have hv : v ∈ interior (convexHull ℝ (H : Set Plane)) :=
    hball (by rw [Metric.mem_ball, dist_zero_right, hnv]; linarith)
  exact ⟨H, u, v, hcard, hcircle, hu0, hv0, huv, h0, hu, hv⟩

set_option maxHeartbeats 800000 in
/-- A simultaneous non-vacuity model: the checked rational six-vertex circle with three
ambient-interior points is translated and scaled to first-label zero and actual diameter
one. Its nine labels are separated by a positive margin, all three interior labels have a
common positive closed-ball depth, and the centre and radius have compatible positive
bounds. All six hull radial errors are exactly zero. -/
theorem normalized_exact_circle_fixture : ∃ (x : Labels 6 → Plane) (O : Plane) (R Δ Θ rminus rplus C : ℝ),
    0 < Δ ∧ 0 < Θ ∧ 0 < rminus ∧ 0 < rplus ∧ 0 < C ∧ rminus < rplus ∧
    x (Sum.inl 0) = 0 ∧ Metric.diam (points x : Set Plane) = 1 ∧
    (∀ i j, i ≠ j → Δ ≤ dist (x i) (x j)) ∧
    (∀ j : Fin 3, Metric.closedBall (x (Sum.inr j)) Θ ⊆
      convexHull ℝ (Set.range (fun i : Fin 6 => x (Sum.inl i)))) ∧
    ‖O‖ ≤ C ∧ rminus ≤ R ∧ R ≤ rplus ∧
    (∀ i : Fin 6, dist (x (Sum.inl i)) O = R) ∧ (points x).card = 9 ∧
    (∀ i : Fin 6, x (Sum.inl i) ∈
      (convexHull ℝ (Set.range (fun j : Fin 6 => x (Sum.inl j)))).extremePoints ℝ) := by
  classical
  obtain ⟨H,w,v,hcard,hcircle,hw0,hv0,hwv,hz,hw,hv⟩ := six_vertex_center_fixture
  let z : Plane := 0
  have hzw : z ≠ w := hw0.symm
  have hzv : z ≠ v := hv0.symm
  have hc : ∀ h ∈ H, dist h (0 : Plane) = 1 := by simpa only [dist_zero_right] using hcircle
  let e := (H.equivFinOfCardEq hcard).symm
  let h : Fin 6 → Plane := fun i => (e i).val
  have hH : points h = H := by
    ext p
    simp only [points, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i,rfl⟩; exact (e i).property
    · intro hp
      exact ⟨e.symm ⟨p,hp⟩, congrArg Subtype.val (e.apply_symm_apply ⟨p,hp⟩)⟩
  let y : Labels 6 → Plane := Sum.elim h (fun j => if j = 0 then z else if j = 1 then w else v)
  have hyset : points y = insert z (insert w (insert v H)) := by
    rw [points_sum]
    simp only [y, Sum.elim_inr, Sum.elim_inl, hH]
    simp only [if_true,
      show (1 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 0 from by decide,
      show (2 : Fin 3) ≠ 1 from by decide, if_false]
  have hycard : (points y).card = Fintype.card (Labels 6) := by
    rw [hyset, EvenThreeInteriorCircle.card_insert_three H (by norm_num) hcircle hz hw hv hzw hzv hwv, hcard]
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
  have hvi : x (Sum.inr 2) ∈ interior (convexHull ℝ (Set.range (fun i : Fin 6 => x (Sum.inl i)))) := by
    rw [← hhull, ← show t '' convexHull ℝ (H : Set Plane) = T '' convexHull ℝ (H : Set Plane) from by simp only [ht], ← t.image_interior]
    exact ⟨v,hv,by simp [ht,x,y]⟩
  obtain ⟨θz,hθz,hballz⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzi)
  obtain ⟨θw,hθw,hballw⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hwi)
  obtain ⟨θv,hθv,hballv⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hvi)
  let Θ := min (min θz θw) θv / 2
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
    rw [hdist,hc (h i) (by rw [← hH]; exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩),mul_one]
  have hcardx : (points x).card = 9 := by
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
    by positivity,by linarith,?_,hxdiam,hsep,?_,by linarith [norm_nonneg (T 0)],
    by linarith,by linarith,hcirclex,hcardx,hextx⟩
  · simp [x,T,a]
  · intro j
    have hΘz : Θ < θz := by
      dsimp [Θ]
      linarith [min_le_left (min θz θw) θv, min_le_left θz θw]
    have hΘw : Θ < θw := by
      dsimp [Θ]
      linarith [min_le_left (min θz θw) θv, min_le_right θz θw]
    have hΘv : Θ < θv := by
      dsimp [Θ]
      linarith [min_le_right (min θz θw) θv]
    fin_cases j
    · exact (Metric.closedBall_subset_ball hΘz).trans hballz
    · exact (Metric.closedBall_subset_ball hΘw).trans hballw
    · exact (Metric.closedBall_subset_ball hΘv).trans hballv

end Erdos132.NearCircleThree
