import Erdos.Erdos132.TwoInteriorCircle
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false

open Erdos132.TwoInteriorCircle

namespace Erdos132.AxialEllipse

/-- Two strictly increasing maps on a finite ordered set with the same image agree there. -/
theorem eq_on_of_strictMonoOn_image_eq (A : Finset ℝ) (f g : ℝ → ℝ)
    (hf : StrictMonoOn f (A : Set ℝ)) (hg : StrictMonoOn g (A : Set ℝ))
    (he : A.image f = A.image g) : ∀ x ∈ A, f x = g x := by
  classical
  have hex : ∀ x : A, ∃ y : A, f x = g y := by
    intro x
    have hm : f x ∈ A.image g := he ▸ Finset.mem_image.mpr ⟨x, x.property, rfl⟩
    obtain ⟨y, hy, hgy⟩ := Finset.mem_image.mp hm
    exact ⟨⟨y, hy⟩, hgy.symm⟩
  let T : A → A := fun x => Classical.choose (hex x)
  have hT : ∀ x : A, f x = g (T x) := fun x => Classical.choose_spec (hex x)
  have hmono : StrictMono T := by
    intro x y hxy
    have hfg : g (T x) < g (T y) := by rw [← hT x, ← hT y]; exact hf x.property y.property hxy
    by_contra h
    have hle : (T y : ℝ) ≤ T x := le_of_not_gt h
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hrev := hg (T y).property (T x).property hlt
      exact (not_lt_of_ge hrev.le) hfg
    · exact (ne_of_lt hfg) (congrArg g heq.symm)
  have hid : T = id := hmono.eq_id
  intro x hx
  have hh := hT ⟨x, hx⟩
  simpa only [hid, id_eq] using hh

/-- The squared Euclidean radial function on an ellipse in canonical axes. -/
noncomputable def radialSquare (a b c x : ℝ) : ℝ := (1 - b^2 / a^2) * x^2 - 2*c*x + b^2 + c^2

example : radialSquare 2 1 (8/5) 0 = 89/25 := by norm_num [radialSquare]

/-- At the inclusive positive axial threshold the squared radial function strictly decreases. -/
theorem radialSquare_strictAntiOn (a b c : ℝ) (hb : 0 < b) (hab : b < a)
    (hc : (a^2-b^2)/a ≤ c) : StrictAntiOn (radialSquare a b c) (Set.Icc (-a) a) := by
  have ha : 0 < a := hb.trans hab
  have ha2 : 0 < a^2 := sq_pos_of_pos ha
  have halpha : 0 < 1 - b^2/a^2 := by
    apply sub_pos.mpr
    apply (div_lt_one ha2).mpr
    nlinarith
  have hthreshold : (1-b^2/a^2)*a ≤ c := by
    have he : (1-b^2/a^2)*a = (a^2-b^2)/a := by field_simp
    rwa [he]
  intro x hx y hy hxy
  have hsum : x+y < 2*a := by linarith [hx.2, hy.2]
  have hfactor : (1-b^2/a^2)*(x+y)-2*c < 0 := by
    have hm := mul_lt_mul_of_pos_left hsum halpha
    nlinarith
  have hdiff : radialSquare a b c y - radialSquare a b c x =
      (y-x)*((1-b^2/a^2)*(x+y)-2*c) := by unfold radialSquare; ring
  have hprod : (y-x)*((1-b^2/a^2)*(x+y)-2*c) < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr hxy) hfactor
  linarith

/-- At the inclusive negative axial threshold the squared radial function strictly increases. -/
theorem radialSquare_strictMonoOn (a b c : ℝ) (hb : 0 < b) (hab : b < a)
    (hc : c ≤ -((a^2-b^2)/a)) : StrictMonoOn (radialSquare a b c) (Set.Icc (-a) a) := by
  have ha : 0 < a := hb.trans hab
  have ha2 : 0 < a^2 := sq_pos_of_pos ha
  have halpha : 0 < 1 - b^2/a^2 := by
    apply sub_pos.mpr
    apply (div_lt_one ha2).mpr
    nlinarith
  have hthreshold : c ≤ -(1-b^2/a^2)*a := by
    have he : -(1-b^2/a^2)*a = -((a^2-b^2)/a) := by field_simp
    rwa [he]
  intro x hx y hy hxy
  have hsum : -2*a < x+y := by linarith [hx.1, hy.1]
  have hfactor : 0 < (1-b^2/a^2)*(x+y)-2*c := by
    have hm := mul_lt_mul_of_pos_left hsum halpha
    nlinarith
  have hdiff : radialSquare a b c y - radialSquare a b c x =
      (y-x)*((1-b^2/a^2)*(x+y)-2*c) := by unfold radialSquare; ring
  have hprod : 0 < (y-x)*((1-b^2/a^2)*(x+y)-2*c) :=
    mul_pos (sub_pos.mpr hxy) hfactor
  linarith

/-- Canonical Cartesian point in the ordinary Euclidean plane. -/
def point (x y : ℝ) : Plane := WithLp.toLp 2 ![x,y]

example (x y : ℝ) : point x y 0 = x ∧ point x y 1 = y := by simp [point]

/-- The Cartesian ellipse equation; geometric consumers explicitly require `0 < b < a`. -/
def OnEllipse (a b : ℝ) (p : Plane) : Prop := p 0 ^ 2 / a^2 + p 1 ^ 2 / b^2 = 1

example : OnEllipse 2 1 (point 0 1) := by norm_num [OnEllipse, point]

/-- Ellipse coordinates lie in the closed major-axis interval. -/
theorem coordinate_mem_Icc (a b : ℝ) (hb : 0 < b) (hab : b < a)
    {p : Plane} (hp : OnEllipse a b p) : p 0 ∈ Set.Icc (-a) a := by
  have ha : 0 < a := hb.trans hab
  have ha2 : 0 < a^2 := sq_pos_of_pos ha
  have hb2 : 0 < b^2 := sq_pos_of_pos hb
  have hnon : 0 ≤ p 1 ^ 2 / b^2 := div_nonneg (sq_nonneg _) hb2.le
  have hle : p 0 ^ 2 ≤ a^2 := (div_le_one ha2).mp (by unfold OnEllipse at hp; linarith)
  constructor <;> nlinarith [sq_nonneg (p 0 + a), sq_nonneg (p 0 - a)]

/-- Squared ordinary Euclidean distance on the ellipse is the radial quadratic. -/
theorem dist_sq_eq_radialSquare (a b c : ℝ) (hb : 0 < b) (hab : b < a)
    {p : Plane} (hp : OnEllipse a b p) :
    dist p (point c 0)^2 = radialSquare a b c (p 0) := by
  have ha : 0 < a := hb.trans hab
  have he : p 1 ^ 2 = b^2 - b^2/a^2 * p 0 ^ 2 := by
    unfold OnEllipse at hp
    have hh := (div_eq_iff (ne_of_gt (sq_pos_of_pos hb))).mp
      (show p 1 ^ 2 / b^2 = 1 - p 0 ^ 2 / a^2 by linarith)
    rw [hh]
    ring
  rw [dist_eq_norm, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
  change (p 0 - c)^2 + (p 1 - 0)^2 = _
  rw [sub_zero]
  rw [he]
  unfold radialSquare
  ring

/-- A vertical line has at most two actual ellipse points. -/
theorem vertical_card_le_two (H : Finset Plane) (a b x : ℝ) (hb : 0 < b) (_hab : b < a)
    (hE : ∀ p ∈ H, OnEllipse a b p) : (H.filter fun p => p 0 = x).card ≤ 2 := by
  classical
  let F := H.filter fun p => p 0 = x
  by_cases hc : 1 < F.card
  · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hc
    have hu' := Finset.mem_filter.mp hu
    have hv' := Finset.mem_filter.mp hv
    have heq : ∀ p ∈ F, p 1 ^ 2 = u 1 ^ 2 := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpE := hE p hp'.1
      have huE := hE u hu'.1
      unfold OnEllipse at hpE huE
      rw [hp'.2] at hpE
      rw [hu'.2] at huE
      have hh : p 1 ^ 2 / b^2 = u 1 ^ 2 / b^2 := by linarith
      exact (div_left_inj' (ne_of_gt (sq_pos_of_pos hb))).mp hh
    have hsub : F ⊆ {u,v} := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hsq := heq p hp
      have hvsq := heq v hv
      have hneq : u 1 ≠ v 1 := by
        intro he
        apply huv
        ext i
        fin_cases i
        · exact hu'.2.trans hv'.2.symm
        · exact he
      have hy : p 1 = u 1 ∨ p 1 = v 1 := by
        rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with he | he
        · exact Or.inl he
        · have hvneg : v 1 = -u 1 := (sq_eq_sq_iff_eq_or_eq_neg.mp hvsq).resolve_left hneq.symm
          exact Or.inr (he.trans hvneg.symm)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hy with hy | hy
      · left; ext i; fin_cases i
        · exact hp'.2.trans hu'.2.symm
        · exact hy
      · right; ext i; fin_cases i
        · exact hp'.2.trans hv'.2.symm
        · exact hy
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · dsimp [F] at hc
    omega

/-- An actual ellipse point cannot belong to the ambient interior of its finite hull. -/
theorem ellipse_not_mem_interior (H : Finset Plane) (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (hE : ∀ p ∈ H, OnEllipse a b p) {p : Plane} (hpE : OnEllipse a b p) :
    p ∉ interior (convexHull ℝ (H : Set Plane)) := by
  have ha : 0 < a := hb.trans hab
  have ha2 : 0 < a^2 := sq_pos_of_pos ha
  have hb2 : 0 < b^2 := sq_pos_of_pos hb
  let L : Plane →ₗ[ℝ] ℝ := (p 0 / a^2) • (EuclideanSpace.proj 0).toLinearMap +
    (p 1 / b^2) • (EuclideanSpace.proj 1).toLinearMap
  have hLp : L p = 1 := by
    change p 0 / a^2 * p 0 + p 1 / b^2 * p 1 = 1
    unfold OnEllipse at hpE
    convert hpE using 1; ring
  have hsub : convexHull ℝ (H : Set Plane) ⊆ {q | L q ≤ 1} := by
    apply convexHull_min _ (convex_halfSpace_le (show IsLinearMap ℝ L from ⟨L.map_add, L.map_smul⟩) 1)
    intro q hq
    have hqE := hE q hq
    have hpE' := hpE
    unfold OnEllipse at hpE' hqE
    field_simp [ne_of_gt ha, ne_of_gt hb] at hpE' hqE
    have hs : 0 ≤ b^2 * (q 0 - p 0)^2 + a^2 * (q 1 - p 1)^2 := by positivity
    have hident : a^2*b^2*(L q) = b^2*p 0*q 0 + a^2*p 1*q 1 := by
      change a^2*b^2*(p 0/a^2*q 0+p 1/b^2*q 1) = _
      field_simp
    have hh : a^2*b^2*(L q) ≤ a^2*b^2*1 := by rw [hident]; nlinarith
    exact (mul_le_mul_iff_right₀ (mul_pos ha2 hb2)).mp hh
  intro hp
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
  let t : ℝ := ε / (2*(‖p‖+1))
  have ht : 0 < t := div_pos hε (by positivity)
  have hdist : dist ((1+t) • p) p < ε := by
    have he : (1+t) • p - p = t • p := by module
    rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2*(‖p‖+1))).mpr
    nlinarith [norm_nonneg p]
  have hq := hsub (hball (by simpa only [Metric.mem_ball] using hdist))
  change L ((1+t) • p) ≤ 1 at hq
  rw [L.map_smul, hLp, smul_eq_mul, mul_one] at hq
  linarith

/-- Either axial threshold gives an injective squared radial function on the major-axis interval. -/
theorem radialSquare_injOn (a b c : ℝ) (hb : 0 < b) (hab : b < a)
    (hc : (a^2-b^2)/a ≤ |c|) : Set.InjOn (radialSquare a b c) (Set.Icc (-a) a) := by
  rcases le_or_gt 0 c with hpos | hneg
  · rw [abs_of_nonneg hpos] at hc
    exact (radialSquare_strictAntiOn a b c hb hab hc).injOn
  · rw [abs_of_neg hneg] at hc
    exact (radialSquare_strictMonoOn a b c hb hab (by linarith)).injOn

/-- Every ordinary radial distance fiber at an axial threshold contains at most two ellipse points. -/
theorem radial_card_le_two (H : Finset Plane) (a b c d : ℝ) (hb : 0 < b) (hab : b < a)
    (hE : ∀ p ∈ H, OnEllipse a b p) (hc : (a^2-b^2)/a ≤ |c|) :
    (H.filter fun p => dist p (point c 0) = d).card ≤ 2 := by
  classical
  by_cases hn : (H.filter fun p => dist p (point c 0) = d).Nonempty
  · obtain ⟨u, hu⟩ := hn
    have hu' := Finset.mem_filter.mp hu
    have hsub : (H.filter fun p => dist p (point c 0) = d) ⊆ (H.filter fun p => p 0 = u 0) := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      refine Finset.mem_filter.mpr ⟨hp'.1, ?_⟩
      apply radialSquare_injOn a b c hb hab hc
        (coordinate_mem_Icc a b hb hab (hE p hp'.1))
        (coordinate_mem_Icc a b hb hab (hE u hu'.1))
      rw [← dist_sq_eq_radialSquare a b c hb hab (hE p hp'.1),
        ← dist_sq_eq_radialSquare a b c hb hab (hE u hu'.1), hp'.2, hu'.2]
    exact (Finset.card_le_card hsub).trans (vertical_card_le_two H a b (u 0) hb hab hE)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
    simp

/-- Equal radial-square supports for distinct same-side threshold centers force at most two actual ellipse points. -/
theorem common_support_card_le_two (H : Finset Plane) (a b c₁ c₂ : ℝ)
    (hb : 0 < b) (hab : b < a) (hE : ∀ p ∈ H, OnEllipse a b p)
    (hne : c₁ ≠ c₂) (hsign : 0 < c₁*c₂)
    (hc₁ : (a^2-b^2)/a ≤ |c₁|) (hc₂ : (a^2-b^2)/a ≤ |c₂|)
    (he : H.image (fun p => radialSquare a b c₁ (p 0)) =
      H.image (fun p => radialSquare a b c₂ (p 0))) : H.card ≤ 2 := by
  classical
  let A := H.image fun p => p 0
  have hA : (A : Set ℝ) ⊆ Set.Icc (-a) a := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    exact coordinate_mem_Icc a b hb hab (hE p hp)
  have heA : A.image (radialSquare a b c₁) = A.image (radialSquare a b c₂) := by
    simpa only [A, Finset.image_image, Function.comp_def] using he
  have heq : ∀ x ∈ A, radialSquare a b c₁ x = radialSquare a b c₂ x := by
    rcases lt_trichotomy c₁ 0 with hneg | hz | hpos
    · have hneg₂ : c₂ < 0 := by nlinarith
      rw [abs_of_neg hneg] at hc₁
      rw [abs_of_neg hneg₂] at hc₂
      exact eq_on_of_strictMonoOn_image_eq A _ _
        ((radialSquare_strictMonoOn a b c₁ hb hab (by linarith)).mono hA)
        ((radialSquare_strictMonoOn a b c₂ hb hab (by linarith)).mono hA) heA
    · rw [hz, zero_mul] at hsign
      exact False.elim ((lt_irrefl 0) hsign)
    · have hpos₂ : 0 < c₂ := by nlinarith
      rw [abs_of_pos hpos] at hc₁
      rw [abs_of_pos hpos₂] at hc₂
      have hf : StrictMonoOn (fun x => -radialSquare a b c₁ x) (A : Set ℝ) := by
        intro x hx y hy hxy
        exact neg_lt_neg ((radialSquare_strictAntiOn a b c₁ hb hab hc₁) (hA hx) (hA hy) hxy)
      have hg : StrictMonoOn (fun x => -radialSquare a b c₂ x) (A : Set ℝ) := by
        intro x hx y hy hxy
        exact neg_lt_neg ((radialSquare_strictAntiOn a b c₂ hb hab hc₂) (hA hx) (hA hy) hxy)
      have himg := congrArg (fun S : Finset ℝ => S.image fun x => -x) heA
      have heNeg : A.image (fun x => -radialSquare a b c₁ x) =
          A.image (fun x => -radialSquare a b c₂ x) := by simpa only [Finset.image_image, Function.comp_def] using himg
      intro x hx
      exact neg_injective (eq_on_of_strictMonoOn_image_eq A _ _ hf hg heNeg x hx)
  have hx : ∀ p ∈ H, p 0 = (c₁+c₂)/2 := by
    intro p hp
    have hh := heq (p 0) (Finset.mem_image.mpr ⟨p,hp,rfl⟩)
    have hfactor : (c₁-c₂)*(c₁+c₂-2*p 0) = 0 := by
      calc
        _ = radialSquare a b c₁ (p 0) - radialSquare a b c₂ (p 0) := by unfold radialSquare; ring
        _ = 0 := sub_eq_zero.mpr hh
    have hh' := (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne)
    linarith
  have hfilter : H.filter (fun p => p 0 = (c₁+c₂)/2) = H := Finset.filter_true_of_mem hx
  rw [← hfilter]
  exact vertical_card_le_two H a b ((c₁+c₂)/2) hb hab hE

private theorem radial_mem_actual (H : Finset Plane) (z w p : Plane)
    (hcard : 2 ≤ H.card) (hz : z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hw : w ∈ interior (convexHull ℝ (H : Set Plane)))
    (hp : p ∈ interior (convexHull ℝ (H : Set Plane)))
    (hpX : p ∈ insert z (insert w H)) (hpH : p ∉ H) :
    ∀ h ∈ H, dist h p ∈ nonDiameterDistances (insert z (insert w H)) := by
  classical
  intro h hh
  apply (mem_nonDiameterDistances _ _).mpr
  refine ⟨⟨h, by simp [hh], p, hpX, ?_, rfl⟩, ?_⟩
  · intro he
    exact hpH (he ▸ hh)
  · rw [diam_insert_interiors H z w hz hw, dist_comm]
    exact dist_lt_diam_hull H hcard hp (subset_convexHull ℝ (H : Set Plane) hh)

private theorem image_eq_of_saturated {α β : Type*} [DecidableEq β] (H : Finset α) (T : Finset β)
    (f : α → β) (hmap : ∀ h ∈ H, f h ∈ T)
    (hcap : ∀ d ∈ T, (H.filter fun h => f h = d).card ≤ 2)
    (heq : H.card = 2*T.card) : H.image f = T := by
  classical
  have hs := saturated_fibers H T f hmap hcap heq
  ext d
  constructor
  · intro hd
    obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp hd
    exact hmap h hh
  · intro hd
    have hpos : 0 < (H.filter fun h => f h = d).card := by rw [hs d hd]; decide
    obtain ⟨h,hh⟩ := Finset.card_pos.mp hpos
    exact Finset.mem_image.mpr ⟨h, (Finset.mem_filter.mp hh).1, (Finset.mem_filter.mp hh).2⟩

/-- The same-side axial ellipse theorem uses actual points, ambient interiors, ordinary
Euclidean distance, and loop-free unordered-pair multiplicity. The threshold is inclusive. -/
theorem same_side_axial_ellipse (n : ℕ) (H : Finset Plane) (a b c₁ c₂ : ℝ)
    (hn : 8 ≤ n) (hb : 0 < b) (hab : b < a) (hH : H.card = n-2)
    (hE : ∀ p ∈ H, OnEllipse a b p)
    (h₁ : point c₁ 0 ∈ interior (convexHull ℝ (H : Set Plane)))
    (h₂ : point c₂ 0 ∈ interior (convexHull ℝ (H : Set Plane)))
    (hne : c₁ ≠ c₂) (hsign : 0 < c₁*c₂)
    (hc₁ : (a^2-b^2)/a ≤ |c₁|) (hc₂ : (a^2-b^2)/a ≤ |c₂|) :
    (insert (point c₁ 0) (insert (point c₂ 0) H)).card = n ∧
    ∃ d : ℝ, 0 < d ∧
      d < Metric.diam ((insert (point c₁ 0) (insert (point c₂ 0) H) : Finset Plane) : Set Plane) ∧
      1 ≤ multiplicity (insert (point c₁ 0) (insert (point c₂ 0) H)) d ∧
      multiplicity (insert (point c₁ 0) (insert (point c₂ 0) H)) d ≤ n := by
  classical
  let z := point c₁ 0
  let w := point c₂ 0
  let X := insert z (insert w H)
  let T := nonDiameterDistances X
  have hH6 : 6 ≤ H.card := by omega
  have hzH : z ∉ H := fun hh => ellipse_not_mem_interior H a b hb hab hE (hE z hh) h₁
  have hwH : w ∉ H := fun hh => ellipse_not_mem_interior H a b hb hab hE (hE w hh) h₂
  have hzw : z ≠ w := by
    intro he
    have he0 := congrArg (fun p : Plane => p 0) he
    exact hne he0
  have hX : X.card = n := by
    dsimp [X]
    rw [Finset.card_insert_of_notMem (by simp [hzw, hzH]), Finset.card_insert_of_notMem hwH]
    omega
  refine ⟨hX, ?_⟩
  by_contra hnone
  have hlarge : ∀ d ∈ T, X.card + 1 ≤ multiplicity X d := by
    intro d hd
    obtain ⟨⟨u,hu,v,hv,huv,huvd⟩,hdD⟩ := (mem_nonDiameterDistances X d).mp hd
    have hdpos : 0 < d := huvd ▸ dist_pos.mpr huv
    have hmpos : 1 ≤ multiplicity X d := by
      apply Finset.card_pos.mpr
      exact ⟨s(u,v), Finset.mem_filter.mpr ⟨(mk_mem_pairs X u v).mpr ⟨hu,hv,huv⟩, huvd⟩⟩
    have hnot : ¬ multiplicity X d ≤ n := by
      intro hle
      exact hnone ⟨d,hdpos,hdD,hmpos,hle⟩
    omega
  have hmap₁ : ∀ p ∈ H, dist p z ∈ T :=
    radial_mem_actual H z w z (by omega) h₁ h₂ h₁ (by simp) hzH
  have hmap₂ : ∀ p ∈ H, dist p w ∈ T :=
    radial_mem_actual H z w w (by omega) h₁ h₂ h₂ (by simp) hwH
  have hcap₁ : ∀ d ∈ T, (H.filter fun p => dist p z = d).card ≤ 2 :=
    fun d _ => radial_card_le_two H a b c₁ d hb hab hE hc₁
  have hcap₂ : ∀ d ∈ T, (H.filter fun p => dist p w = d).card ≤ 2 :=
    fun d _ => radial_card_le_two H a b c₂ d hb hab hE hc₂
  have hlower : n-2 ≤ 2*T.card := by
    rw [← hH]
    exact Finset.card_le_mul_card_image_of_maps_to hmap₁ 2 hcap₁
  have hbudget := nonDiameter_pair_budget X (by omega) hlarge
  rw [hX] at hbudget
  have heven := (even_size_of_pair_budget n T.card hn hlower hbudget).1
  have heq : H.card = 2*T.card := by omega
  have hs₁ := image_eq_of_saturated H T (fun p => dist p z) hmap₁ hcap₁ heq
  have hs₂ := image_eq_of_saturated H T (fun p => dist p w) hmap₂ hcap₂ heq
  have hsquare := congrArg (fun S : Finset ℝ => S.image fun d => d^2) (hs₁.trans hs₂.symm)
  simp only [Finset.image_image, Function.comp_def] at hsquare
  have he₁ : H.image (fun p => dist p z ^ 2) = H.image (fun p => radialSquare a b c₁ (p 0)) :=
    Finset.image_congr (fun p hp => dist_sq_eq_radialSquare a b c₁ hb hab (hE p hp))
  have he₂ : H.image (fun p => dist p w ^ 2) = H.image (fun p => radialSquare a b c₂ (p 0)) :=
    Finset.image_congr (fun p hp => dist_sq_eq_radialSquare a b c₂ hb hab (hE p hp))
  have hsmall := common_support_card_le_two H a b c₁ c₂ hb hab hE hne hsign hc₁ hc₂
    (he₁.symm.trans (hsquare.trans he₂))
  omega

private theorem rectangle_subset_hull (H : Finset Plane) (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (hcorner : ∀ x ∈ ({-r,r} : Finset ℝ), ∀ y ∈ ({-s,s} : Finset ℝ), point x y ∈ H) :
    {q : Plane | -r ≤ q 0 ∧ q 0 ≤ r ∧ -s ≤ q 1 ∧ q 1 ≤ s} ⊆ convexHull ℝ (H : Set Plane) := by
  classical
  intro q hq
  let t : ℝ := (q 0+r)/(2*r)
  let u : ℝ := (q 1+s)/(2*s)
  have ht0 : 0 ≤ t := div_nonneg (by linarith [hq.1]) (by positivity)
  have ht1 : t ≤ 1 := (div_le_one (by positivity : 0 < 2*r)).mpr (by linarith [hq.2.1])
  have hu0 : 0 ≤ u := div_nonneg (by linarith [hq.2.2.1]) (by positivity)
  have hu1 : u ≤ 1 := (div_le_one (by positivity : 0 < 2*s)).mpr (by linarith [hq.2.2.2])
  have hleft : point (-r) (q 1) ∈ convexHull ℝ (H : Set Plane) := by
    have hh := convex_convexHull ℝ (H : Set Plane)
      (subset_convexHull ℝ _ (hcorner (-r) (by simp) (-s) (by simp)))
      (subset_convexHull ℝ _ (hcorner (-r) (by simp) s (by simp)))
      (sub_nonneg.mpr hu1) hu0 (by ring : (1-u)+u=1)
    have he : (1-u) • point (-r) (-s) + u • point (-r) s = point (-r) (q 1) := by
      ext i
      fin_cases i <;> simp [point, u] <;> field_simp <;> ring
    rwa [he] at hh
  have hright : point r (q 1) ∈ convexHull ℝ (H : Set Plane) := by
    have hh := convex_convexHull ℝ (H : Set Plane)
      (subset_convexHull ℝ _ (hcorner r (by simp) (-s) (by simp)))
      (subset_convexHull ℝ _ (hcorner r (by simp) s (by simp)))
      (sub_nonneg.mpr hu1) hu0 (by ring : (1-u)+u=1)
    have he : (1-u) • point r (-s) + u • point r s = point r (q 1) := by
      ext i
      fin_cases i <;> simp [point, u] <;> field_simp <;> ring
    rwa [he] at hh
  have hh := convex_convexHull ℝ (H : Set Plane) hleft hright
    (sub_nonneg.mpr ht1) ht0 (by ring : (1-t)+t=1)
  have he : (1-t) • point (-r) (q 1) + t • point r (q 1) = q := by
    ext i
    fin_cases i <;> simp [point, t] <;> field_simp <;> ring
  rwa [he] at hh

private theorem axial_mem_interior_rectangle (H : Finset Plane) (r s c : ℝ)
    (hr : 0 < r) (hs : 0 < s)
    (hcorner : ∀ x ∈ ({-r,r} : Finset ℝ), ∀ y ∈ ({-s,s} : Finset ℝ), point x y ∈ H)
    (hc : -r < c ∧ c < r) : point c 0 ∈ interior (convexHull ℝ (H : Set Plane)) := by
  let U : Set Plane := {q | -r < q 0 ∧ q 0 < r ∧ -s < q 1 ∧ q 1 < s}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      ((isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const).inter
        ((isOpen_lt continuous_const (EuclideanSpace.proj 1).continuous).inter
          (isOpen_lt (EuclideanSpace.proj 1).continuous continuous_const)))
  have hsub : U ⊆ convexHull ℝ (H : Set Plane) := by
    intro q hq
    exact rectangle_subset_hull H r s hr hs hcorner ⟨hq.1.le,hq.2.1.le,hq.2.2.1.le,hq.2.2.2.le⟩
  apply interior_maximal hsub hU
  change -r < c ∧ c < r ∧ -s < 0 ∧ (0 : ℝ) < s
  exact ⟨hc.1,hc.2,by linarith,hs⟩

/-- The six original ellipse points: all four signed rectangle corners and both minor-axis endpoints. -/
noncomputable def fixtureHull : Finset Plane := by
  classical
  exact {point (Real.sqrt 3) (1/2), point (Real.sqrt 3) (-1/2),
    point (-Real.sqrt 3) (1/2), point (-Real.sqrt 3) (-1/2), point 0 1, point 0 (-1)}

/-- The prescribed sqrt(3) configuration simultaneously satisfies every geometric and
numeric hypothesis of the original theorem, at n=8, a=2, b=1, c₁=8/5, c₂=17/10. -/
theorem ellipse_fixture : fixtureHull.card = 6 ∧
    (∀ p ∈ fixtureHull, OnEllipse 2 1 p) ∧
    point (8/5) 0 ∈ interior (convexHull ℝ (fixtureHull : Set Plane)) ∧
    point (17/10) 0 ∈ interior (convexHull ℝ (fixtureHull : Set Plane)) ∧
    8 ≤ (8 : ℕ) ∧ (0 : ℝ) < 1 ∧ (1 : ℝ) < 2 ∧
    (8/5 : ℝ) ≠ 17/10 ∧ (0 : ℝ) < (8/5)*(17/10) ∧
    ((2 : ℝ)^2-1^2)/2 ≤ |(8/5 : ℝ)| ∧ ((2 : ℝ)^2-1^2)/2 ≤ |(17/10 : ℝ)| := by
  classical
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hsn : Real.sqrt 3 ≠ 0 := ne_of_gt hs
  have hcard : fixtureHull.card = 6 := by
    norm_num [fixtureHull, Finset.card_insert_of_notMem, point, WithLp.ext_iff,
      funext_iff, Fin.forall_fin_two, hsn, (by linarith : Real.sqrt 3 ≠ -Real.sqrt 3)]
  have hE : ∀ p ∈ fixtureHull, OnEllipse 2 1 p := by
    intro p hp
    simp only [fixtureHull, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [OnEllipse, point, neg_sq, hsq]
  have hcorner : ∀ x ∈ ({-Real.sqrt 3, Real.sqrt 3} : Finset ℝ),
      ∀ y ∈ ({-(1/2),1/2} : Finset ℝ), point x y ∈ fixtureHull := by
    intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num [fixtureHull]
  have h₁ : point (8/5) 0 ∈ interior (convexHull ℝ (fixtureHull : Set Plane)) := by
    apply axial_mem_interior_rectangle fixtureHull (Real.sqrt 3) (1/2) (8/5) hs (by norm_num) hcorner
    constructor <;> nlinarith
  have h₂ : point (17/10) 0 ∈ interior (convexHull ℝ (fixtureHull : Set Plane)) := by
    apply axial_mem_interior_rectangle fixtureHull (Real.sqrt 3) (1/2) (17/10) hs (by norm_num) hcorner
    constructor <;> nlinarith
  exact ⟨hcard,hE,h₁,h₂,by norm_num,by norm_num,by norm_num,by norm_num,
    by norm_num,by norm_num,by norm_num⟩

example :
    (insert (point (8/5) 0) (insert (point (17/10) 0) fixtureHull)).card = 8 ∧
    ∃ d : ℝ, 0 < d ∧
      d < Metric.diam ((insert (point (8/5) 0) (insert (point (17/10) 0) fixtureHull) : Finset Plane) : Set Plane) ∧
      1 ≤ multiplicity (insert (point (8/5) 0) (insert (point (17/10) 0) fixtureHull)) d ∧
      multiplicity (insert (point (8/5) 0) (insert (point (17/10) 0) fixtureHull)) d ≤ 8 := by
  rcases ellipse_fixture with ⟨hcard,hE,h₁,h₂,hn,hb,hab,hne,hsign,hc₁,hc₂⟩
  exact same_side_axial_ellipse 8 fixtureHull 2 1 (8/5) (17/10) hn hb hab
    (by norm_num [hcard]) hE h₁ h₂ hne hsign hc₁ hc₂

end Erdos132.AxialEllipse
