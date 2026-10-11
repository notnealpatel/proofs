import Erdos.Erdos132.HullOutlierOutside

set_option autoImplicit false

namespace Erdos132.HullOutlierInside

open Erdos132.TwoInteriorCircle

private theorem reflected_chord_sq (z c : Plane) (hz : z ≠ 0) :
    dist c ((ℝ ∙ z).reflection c) ^ 2 * ‖z‖ ^ 2 =
      4 * (‖c‖ ^ 2 * ‖z‖ ^ 2 - (inner ℝ z c)^2) := by
  have hn : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  rw [dist_eq_norm,Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  have he : c - (2 • (inner ℝ z c / ‖z‖ ^ 2) • z - c) =
      (2 : ℝ) • c - (2 * (inner ℝ z c / ‖z‖ ^ 2)) • z := by module
  rw [he,norm_sub_sq_real]
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,inner_smul_left,inner_smul_right,
    real_inner_comm c z]
  norm_num only [map_ofNat]
  field_simp [hn]
  ring

private theorem gram (z a b : Plane) :
    ‖z‖^2 * (inner ℝ a b)^2 + ‖a‖^2 * (inner ℝ z b)^2 +
    ‖b‖^2 * (inner ℝ z a)^2 =
    ‖z‖^2 * ‖a‖^2 * ‖b‖^2 +
      2 * inner ℝ z a * inner ℝ z b * inner ℝ a b := by
  simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two,
    Real.norm_eq_abs, sq_abs, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_two, Pi.star_apply, star_trivial]
  ring

private theorem cross_pair (z a b : Plane) (s t : ℝ) (ht : 0 < t)
    (hz : ‖z‖^2 = t) (ha : ‖a‖^2 = s) (hb : ‖b‖^2 = s)
    (hrb : ‖(ℝ ∙ z).reflection b‖^2 = s) :
    (dist a b^2 + dist a ((ℝ ∙ z).reflection b)^2)*t =
      4*s*t-4*inner ℝ z a*inner ℝ z b ∧
    (dist a b^2 * dist a ((ℝ ∙ z).reflection b)^2)*t =
      4*s*(inner ℝ z a-inner ℝ z b)^2 := by
  let rb := (ℝ ∙ z).reflection b
  have hir : inner ℝ a rb = 2*inner ℝ z b/t*inner ℝ z a-inner ℝ a b := by
    dsimp [rb]
    rw [Submodule.reflection_singleton_apply]
    simp only [RCLike.ofReal_real_eq_id,id_eq,inner_sub_right,two_smul,inner_add_right,inner_smul_right,
      real_inner_comm a z,hz]
    ring
  have h1 : dist a b^2 = 2*s-2*inner ℝ a b := by
    rw [dist_eq_norm,norm_sub_sq_real,ha,hb]; ring
  have h2 : dist a rb^2 = 2*s-2*inner ℝ a rb := by
    rw [dist_eq_norm,norm_sub_sq_real,ha,hrb]; ring
  have hg := gram z a b
  rw [hz,ha,hb] at hg
  change (dist a b^2 + dist a rb^2)*t = _ ∧ (dist a b^2 * dist a rb^2)*t = _
  rw [h1,h2,hir]
  constructor
  · field_simp
    ring
  · field_simp
    nlinarith only [hg]

private theorem reflection_inner (z b : Plane) (hz : 0 < ‖z‖^2) :
    inner ℝ z ((ℝ ∙ z).reflection b) = inner ℝ z b := by
  rw [Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id,id_eq,inner_sub_right,two_smul,inner_add_right,
    inner_smul_right,real_inner_self_eq_norm_sq]
  have hn0 : ‖z‖ ≠ 0 := by intro he; simp [he] at hz
  field_simp [hn0]
  ring


private theorem cross_distinct (s t A B H K : ℝ)
    (hA : A^2 < s*t) (hB : B^2 < s*t)
    (hsum : (H+K)*t = 4*s*t-4*A*B)
    (hprod : H*K*t = 4*s*(A-B)^2) : H ≠ K := by
  intro he
  have hpos : 0 < (s*t-A^2)*(s*t-B^2) := mul_pos (sub_pos.mpr hA) (sub_pos.mpr hB)
  have hid : (H-K)^2*t^2 = 16*((s*t-A^2)*(s*t-B^2)) := by
    have hh : ((H+K)*t)^2 = (4*s*t-4*A*B)^2 := congrArg (fun x : ℝ => x^2) hsum
    have hp := congrArg (fun x : ℝ => x*(4*t)) hprod
    nlinarith only [hh,hp]
  simp only [he,sub_self,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_mul] at hid
  linarith

set_option maxHeartbeats 1000000

private theorem inside_obstruction_false (C : Finset Plane) (z : Plane) (R δ : ℝ)
    (T : Finset ℝ) (hR : 0 < R) (hzpos : 0 < ‖z‖) (hin : ‖z‖ < R)
    (hc : ∀ c ∈ C, ‖c‖ = R) (hcard : T.card = 3)
    (hT : ∀ w ∈ T, 0 < w ∧ w < δ ∧ ∃ c ∈ C, dist c z ^ 2 = w)
    (hs : R^2 ∈ T) (ht : ‖z‖^2 ∈ T)
    (href : ∀ c ∈ C, (ℝ ∙ z).reflection c ∈ C ∧ (ℝ ∙ z).reflection c ≠ c ∧
      dist c z ^ 2 = R ^ 2 + ‖z‖ ^ 2 - 2 * inner ℝ z c ∧
      dist c ((ℝ ∙ z).reflection c) ^ 2 * ‖z‖ ^ 2 =
        4 * (R ^ 2 * ‖z‖ ^ 2 - (inner ℝ z c) ^ 2))
    (hch : ∀ a ∈ C, ∀ b ∈ C, a ≠ b → dist a b ^ 2 ∈ T ∨ dist a b ^ 2 = δ) : False := by
  classical
  let s := R^2
  let t := ‖z‖^2
  have hspos : 0 < s := sq_pos_of_pos hR
  have htpos : 0 < t := sq_pos_of_pos hzpos
  have hts : t < s := by dsimp [s,t]; nlinarith
  obtain ⟨v,hv,hvs,hvt⟩ : ∃ v ∈ T, v ≠ s ∧ v ≠ t := by
    by_contra hn
    have hsub : T ⊆ {s,t} := by
      intro x hx
      by_cases hxs : x = s
      · simp [hxs]
      by_cases hxt : x = t
      · simp [hxt]
      exact False.elim (hn ⟨x,hx,hxs,hxt⟩)
    have hh := Finset.card_le_card hsub
    have hstne : s ≠ t := ne_of_gt hts
    simp [hcard,hstne] at hh
  have hset : T = {s,t,v} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hs
      · exact ht
      · exact hv
    · simp [hcard,ne_of_gt hts,Ne.symm hvs,Ne.symm hvt]
  have chord_cases : ∀ a ∈ C, ∀ b ∈ C, a ≠ b →
      dist a b^2 = s ∨ dist a b^2 = t ∨ dist a b^2 = v ∨ dist a b^2 = δ := by
    intro a ha b hb hab
    rcases hch a ha b hb hab with hm | hd
    · have hh : dist a b^2 = s ∨ dist a b^2 = t ∨ dist a b^2 = v := by
        simpa only [hset,Finset.mem_insert,Finset.mem_singleton] using hm
      rcases hh with hh | hh | hh
      · exact Or.inl hh
      · exact Or.inr (Or.inl hh)
      · exact Or.inr (Or.inr (Or.inl hh))
    · exact Or.inr (Or.inr (Or.inr hd))
  have chord_le : ∀ a ∈ C, ∀ b ∈ C, a ≠ b → dist a b^2 ≤ δ := by
    intro a ha b hb hab
    rcases hch a ha b hb hab with hm | hd
    · exact (hT _ hm).2.1.le
    · exact hd.le
  have normsq : ∀ a ∈ C, ‖a‖^2 = s := by intro a ha; rw [hc a ha]
  have dot_bound : ∀ a ∈ C, (inner ℝ z a)^2 < s*t := by
    intro a ha
    have hh := (href a ha).2.2.2
    have hp := mul_pos (sq_pos_of_pos (dist_pos.mpr (href a ha).2.1.symm)) htpos
    change dist a ((ℝ ∙ z).reflection a)^2*t = 4*(s*t-(inner ℝ z a)^2) at hh
    nlinarith only [hh,hp]
  obtain ⟨a,ha,has⟩ := (hT s hs).2.2
  obtain ⟨b,hb,hbt⟩ := (hT t ht).2.2
  obtain ⟨e,he,hev⟩ := (hT v hv).2.2
  have hza : inner ℝ z a = t/2 := by
    have hh := (href a ha).2.2.1
    change dist a z^2 = s+t-2*inner ℝ z a at hh
    linarith
  have hzb : inner ℝ z b = s/2 := by
    have hh := (href b hb).2.2.1
    change dist b z^2 = s+t-2*inner ℝ z b at hh
    linarith
  have hze : inner ℝ z e = (s+t-v)/2 := by
    have hh := (href e he).2.2.1
    change dist e z^2 = s+t-2*inner ℝ z e at hh
    linarith
  have hL : dist a ((ℝ ∙ z).reflection a)^2 = 4*s-t := by
    have hh := (href a ha).2.2.2
    rw [hza] at hh
    change dist a ((ℝ ∙ z).reflection a)^2*t = 4*(s*t-(t/2)^2) at hh
    nlinarith only [hh,htpos]
  have hδ : 3*s < δ := by
    have hh := chord_le a ha _ (href a ha).1 (href a ha).2.1.symm
    rw [hL] at hh
    linarith
  have hab : a ≠ b := by intro hab; rw [hab] at hza; linarith
  have harb : a ≠ (ℝ ∙ z).reflection b := by
    intro hab
    rw [hab,reflection_inner z b (by exact htpos)] at hza
    linarith
  let H := dist a b^2
  let K := dist a ((ℝ ∙ z).reflection b)^2
  obtain ⟨hsum0,hprod0⟩ := cross_pair z a b s t htpos rfl (normsq a ha)
    (normsq b hb) (normsq _ (href b hb).1)
  rw [hza,hzb] at hsum0 hprod0
  have hsum : H+K = 3*s := by dsimp [H,K]; nlinarith only [hsum0,htpos]
  have hprod : H*K*t = s*(s-t)^2 := by dsimp [H,K]; nlinarith only [hprod0]
  have hHpos : 0 < H := sq_pos_of_pos (dist_pos.mpr hab)
  have hKpos : 0 < K := sq_pos_of_pos (dist_pos.mpr harb)
  have hHK : H ≠ K := cross_distinct s t (inner ℝ z a) (inner ℝ z b) H K
    (dot_bound a ha) (dot_bound b hb)
    (by simpa only [H,K,hza,hzb] using hsum0)
    (by simpa only [H,K,hza,hzb] using hprod0)
  have hHcases : H = s ∨ H = t ∨ H = v := by
    have hh := chord_cases a ha b hb hab
    change H = s ∨ H = t ∨ H = v ∨ H = δ at hh
    rcases hh with hh | hh | hh | hh
    · exact Or.inl hh
    · exact Or.inr (Or.inl hh)
    · exact Or.inr (Or.inr hh)
    · exfalso; linarith
  have hKcases : K = s ∨ K = t ∨ K = v := by
    have hh := chord_cases a ha _ (href b hb).1 harb
    change K = s ∨ K = t ∨ K = v ∨ K = δ at hh
    rcases hh with hh | hh | hh | hh
    · exact Or.inl hh
    · exact Or.inr (Or.inl hh)
    · exact Or.inr (Or.inr hh)
    · exfalso; linarith
  have hcases : (v = 2*s ∧ 2*s^2*t = s*(s-t)^2) ∨
      (v = 3*s-t ∧ t*(3*s-t)*t = s*(s-t)^2) := by
    rcases hHcases with hH | hH | hH <;> rcases hKcases with hK | hK | hK
    · exact False.elim (hHK (hH.trans hK.symm))
    · exfalso; linarith
    · left
      have hv2 : v = 2*s := by linarith
      rw [hH,hK,hv2] at hprod
      exact ⟨hv2,by nlinarith only [hprod]⟩
    · exfalso; linarith
    · exact False.elim (hHK (hH.trans hK.symm))
    · right
      have hv3 : v = 3*s-t := by linarith
      rw [hH,hK,hv3] at hprod
      exact ⟨hv3,hprod⟩
    · left
      have hv2 : v = 2*s := by linarith
      rw [hH,hK,hv2] at hprod
      exact ⟨hv2,by nlinarith only [hprod]⟩
    · right
      have hv3 : v = 3*s-t := by linarith
      rw [hH,hK,hv3] at hprod
      exact ⟨hv3,by nlinarith only [hprod]⟩
    · exact False.elim (hHK (hH.trans hK.symm))
  rcases hcases with ⟨hv2,hpoly⟩ | ⟨hv3,hpoly⟩
  · have hquad : s^2+t^2 = 4*s*t := by nlinarith only [hpoly,hspos]
    have hδeq : δ = 4*s-t := by
      have hh := chord_cases a ha _ (href a ha).1 (href a ha).2.1.symm
      rw [hL] at hh
      rcases hh with hh | hh | hh | hh <;> linarith
    have hbe : b ≠ e := by intro hh; rw [hh] at hbt; linarith
    have hbre : b ≠ (ℝ ∙ z).reflection e := by
      intro hh
      rw [hh,reflection_inner z e (by exact htpos)] at hzb
      linarith
    let U := dist b e^2
    let V := dist b ((ℝ ∙ z).reflection e)^2
    obtain ⟨hu0,hv0⟩ := cross_pair z b e s t htpos rfl (normsq b hb)
      (normsq e he) (normsq _ (href e he).1)
    rw [hzb,hze,hv2] at hu0 hv0
    have hu : U+V = 3*s+δ := by
      dsimp [U,V]
      rw [hδeq]
      nlinarith only [hu0,hquad,htpos]
    have hvp : U*V = 3*s*δ := by
      dsimp [U,V]
      rw [hδeq]
      have hh := congrArg (fun x : ℝ => x*s) hquad
      nlinarith only [hv0,hh,htpos]
    have hroot : U = 3*s ∨ U = δ := by
      have hh : (U-3*s)*(U-δ) = 0 := by
        have huU := congrArg (fun x : ℝ => U*x) hu
        nlinarith only [huU,hvp]
      rcases mul_eq_zero.mp hh with hh | hh
      · exact Or.inl (sub_eq_zero.mp hh)
      · exact Or.inr (sub_eq_zero.mp hh)
    have h3 : dist b e^2 = 3*s ∨ dist b ((ℝ ∙ z).reflection e)^2 = 3*s := by
      rcases hroot with hh | hh
      · exact Or.inl hh
      · right; change V = 3*s; linarith
    rcases h3 with hh | hh
    · have hcc := chord_cases b hb e he hbe
      rw [hh] at hcc
      rcases hcc with hcc | hcc | hcc | hcc <;> linarith
    · have hcc := chord_cases b hb _ (href e he).1 hbre
      rw [hh] at hcc
      rcases hcc with hcc | hcc | hcc | hcc <;> linarith
  · have hfactor : (s+t)*(t^2-3*s*t+s^2) = 0 := by nlinarith only [hpoly]
    have hquad : t^2-3*s*t+s^2 = 0 :=
      (mul_eq_zero.mp hfactor).resolve_left (ne_of_gt (add_pos hspos htpos))
    have hbound := dot_bound e he
    rw [hze,hv3] at hbound
    nlinarith only [hbound,hquad]

/-- In the zero-centered inside branch, six circle vertices and an off-circle
vertex, all extreme in their augmented hull, together with the center and a
nonzero interior point strictly inside the circle, give nine actual points and
an ordinary positive strict non-diameter distance of unordered multiplicity 1–9.
Neither interior point is required to lie in the hull of the six circle points. -/
theorem original_zero_centered_inside (C : Finset Plane) (u z : Plane) (R : ℝ)
    (hC : C.card = 6) (hR : 0 < R) (hcircle : ∀ c ∈ C, dist c (0 : Plane) = R)
    (hu : dist u (0 : Plane) ≠ R)
    (hext : ∀ a ∈ insert u C,
      a ∈ (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)).extremePoints ℝ)
    (hO : (0 : Plane) ∈ interior (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)))
    (hz : z ∈ interior (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)))
    (hzpos : 0 < dist z (0 : Plane)) (hin : dist z (0 : Plane) < R) :
    let X := insert (0 : Plane) (insert z (insert u C))
    X.card = 9 ∧ ∃ d : ℝ, 0 < d ∧ d < Metric.diam (X : Set Plane) ∧
      1 ≤ multiplicity X d ∧ multiplicity X d ≤ 9 := by
  classical
  let A := insert u C
  let X := insert (0 : Plane) (insert z A)
  let S := nonDiameterDistances X
  let δ := Metric.diam (X : Set Plane)^2
  have hzN : 0 < ‖z‖ := by simpa only [dist_zero_right] using hzpos
  have hinN : ‖z‖ < R := by simpa only [dist_zero_right] using hin
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzN
  have hcircleN : ∀ c ∈ C, ‖c‖ = R := by simpa only [dist_zero_right] using hcircle
  obtain ⟨hcard,hcase⟩ := HullOutlierOutside.original_target_or_saturation
    C 0 u z R hC hcircle hu hext hO hz hz0.symm
  change X.card = 9 at hcard
  change X.card = 9 ∧ _
  refine ⟨hcard,?_⟩
  rcases hcase with htarget | ⟨hS,hsupport,_hfibers,hsat,_hlarge⟩
  · exact htarget
  · exfalso
    let T := S.image (fun d => d^2)
    have hSpos : ∀ d ∈ S, 0 < d ∧ d < Metric.diam (X : Set Plane) := by
      intro d hd
      obtain ⟨hp,hl,_⟩ :=
        (Erdos132.ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive X d).mp hd
      exact ⟨hp,hl⟩
    have hTcard : T.card = 3 := by
      have hi : Set.InjOn (fun d : ℝ => d^2) (S : Set ℝ) := by
        intro a ha b hb he
        have hapos := (hSpos a ha).1
        have hbpos := (hSpos b hb).1
        nlinarith
      exact (Finset.card_image_iff.mpr hi).trans hS
    have hT : ∀ t ∈ T, 0 < t ∧ t < δ ∧ ∃ c ∈ C, dist c z^2 = t := by
      intro t ht
      obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨hdpos,hdlt⟩ := hSpos d hd
      have hdimage : d ∈ C.image (fun c => dist c z) := hsupport.symm ▸ hd
      obtain ⟨c,hc,hcd⟩ := Finset.mem_image.mp hdimage
      refine ⟨sq_pos_of_pos hdpos,?_,c,hc,?_⟩
      · dsimp [δ]
        nlinarith [Metric.diam_nonneg (s := (X : Set Plane))]
      · rw [hcd]
    have hXhull : (X : Set Plane) ⊆ convexHull ℝ (A : Set Plane) := by
      intro a ha
      simp only [X,Finset.mem_coe,Finset.mem_insert] at ha
      rcases ha with rfl | rfl | ha
      · exact interior_subset hO
      · exact interior_subset hz
      · exact subset_convexHull ℝ (A : Set Plane) ha
    obtain ⟨_hc,hdiam,_hdiampos⟩ := HullOutlierOutside.original_geometry_card_and_diameter
      C 0 u z R hC hcircle hu hext hO hz hz0.symm
    change Metric.diam (X : Set Plane) = Metric.diam (A : Set Plane) at hdiam
    have hcenter : ∀ a ∈ X, a ≠ 0 → ‖a‖ ∈ S := by
      intro a ha ha0
      apply (mem_nonDiameterDistances X ‖a‖).mpr
      refine ⟨⟨a,ha,0,by simp [X],ha0,dist_zero_right a⟩,?_⟩
      rw [← dist_zero_right,dist_comm,hdiam]
      have hAcard : 2 ≤ A.card := (Finset.card_le_card (Finset.subset_insert u C)).trans' (by omega)
      exact dist_lt_diam_hull A hAcard hO (hXhull ha)
    have hRmem : R^2 ∈ T := by
      obtain ⟨c,hc⟩ := Finset.card_pos.mp (show 0 < C.card by omega)
      have hc0 : c ≠ 0 := norm_pos_iff.mp ((hcircleN c hc).symm ▸ hR)
      have hcS := hcenter c (by simp [X,A,hc]) hc0
      rw [hcircleN c hc] at hcS
      exact Finset.mem_image.mpr ⟨R,hcS,rfl⟩
    have hzmem : ‖z‖^2 ∈ T := Finset.mem_image.mpr ⟨‖z‖,hcenter z (by simp [X]) hz0,rfl⟩
    apply inside_obstruction_false C z R δ T hR hzN hinN hcircleN hTcard hT hRmem hzmem
    · intro c hc
      obtain ⟨hr,hrne⟩ := reflection_preserves_saturated_hull C z R hz0 hcircleN hsat c hc
      refine ⟨hr,hrne,?_,?_⟩
      · rw [dist_eq_norm,norm_sub_sq_real,hcircleN c hc,real_inner_comm c z]
        ring
      · simpa only [hcircleN c hc] using reflected_chord_sq z c hz0
    · intro a ha b hb hab
      have haX : a ∈ X := by simp [X,A,ha]
      have hbX : b ∈ X := by simp [X,A,hb]
      have hle := Metric.dist_le_diam_of_mem X.finite_toSet.isBounded haX hbX
      by_cases hlt : dist a b < Metric.diam (X : Set Plane)
      · apply Or.inl
        have hdS := (mem_nonDiameterDistances X (dist a b)).mpr ⟨⟨a,haX,b,hbX,hab,rfl⟩,hlt⟩
        exact Finset.mem_image.mpr ⟨dist a b,hdS,rfl⟩
      · apply Or.inr
        exact congrArg (fun d : ℝ => d^2) (le_antisymm hle (le_of_not_gt hlt))

/-- A simultaneous original inside geometry exists: scale the adopted genuine
outside interior toward the center to norm one half, without changing any of
the six circle vertices, the outlier, or the augmented hull. -/
theorem original_inside_geometry_fixture : ∃ (C : Finset Plane) (u z : Plane),
    C.card = 6 ∧ (∀ c ∈ C, dist c (0 : Plane) = 1) ∧ dist u (0 : Plane) ≠ 1 ∧
    (∀ a ∈ insert u C,
      a ∈ (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)).extremePoints ℝ) ∧
    (0 : Plane) ∈ interior (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)) ∧
    z ∈ interior (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)) ∧
    0 < dist z (0 : Plane) ∧ dist z (0 : Plane) < 1 := by
  obtain ⟨C,u,z0,hC,hcircle,hu,hext,hO,hz0,_hne,houtside⟩ :=
    HullOutlierOutside.original_outside_geometry_fixture
  have hnorm : 1 < ‖z0‖ := by simpa only [dist_zero_right] using houtside
  let b : ℝ := 1/(2*‖z0‖)
  let z : Plane := b • z0
  have hb : 0 < b := by dsimp [b]; positivity
  have hb1 : b < 1 := by dsimp [b]; apply (div_lt_one (by positivity)).mpr; linarith
  have hz : z ∈ interior (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)) := by
    have hh := (convex_convexHull ℝ ((insert u C : Finset Plane) : Set Plane)).combo_interior_self_mem_interior
      hO (interior_subset hz0) (show 0 < 1-b by linarith) hb.le (by ring : (1-b)+b=1)
    simpa only [smul_zero,zero_add] using hh
  have hzd : dist z (0 : Plane) = 1/2 := by
    rw [dist_zero_right]
    dsimp [z]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hb]
    dsimp [b]
    field_simp
  exact ⟨C,u,z,hC,hcircle,hu,hext,hO,hz,by rw [hzd]; norm_num,by rw [hzd]; norm_num⟩

/-- The simultaneous original inside geometry satisfies this module's actual
nine-point ordinary-distance consumer; this is an application of the consumer,
not a witness to the impossible saturation branch. -/
theorem original_inside_fixture_with_conclusion : ∃ (C : Finset Plane) (u z : Plane),
    C.card = 6 ∧ (∀ c ∈ C, dist c (0 : Plane) = 1) ∧ dist u (0 : Plane) ≠ 1 ∧
    (∀ a ∈ insert u C,
      a ∈ (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)).extremePoints ℝ) ∧
    (0 : Plane) ∈ interior (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)) ∧
    z ∈ interior (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)) ∧
    0 < dist z (0 : Plane) ∧ dist z (0 : Plane) < 1 ∧
    (insert (0 : Plane) (insert z (insert u C))).card = 9 ∧
    ∃ d : ℝ, 0 < d ∧
      d < Metric.diam ((insert (0 : Plane) (insert z (insert u C)) : Finset Plane) : Set Plane) ∧
      1 ≤ multiplicity (insert (0 : Plane) (insert z (insert u C))) d ∧
      multiplicity (insert (0 : Plane) (insert z (insert u C))) d ≤ 9 := by
  obtain ⟨C,u,z,hC,hcircle,hu,hext,hO,hz,hzpos,hin⟩ := original_inside_geometry_fixture
  obtain ⟨hcard,htarget⟩ := original_zero_centered_inside C u z 1 hC (by norm_num)
    hcircle hu hext hO hz hzpos hin
  exact ⟨C,u,z,hC,hcircle,hu,hext,hO,hz,hzpos,hin,hcard,htarget⟩

/-- With the same zero-centered augmented-hull geometry and any nonzero second
ambient interior, the inside theorem and the adopted outside/boundary theorem
exhaust the radial cases. No inside/outside condition is a premise. -/
theorem original_zero_centered (C : Finset Plane) (u z : Plane) (R : ℝ)
    (hC : C.card = 6) (hR : 0 < R) (hcircle : ∀ c ∈ C, dist c (0 : Plane) = R)
    (hu : dist u (0 : Plane) ≠ R)
    (hext : ∀ a ∈ insert u C,
      a ∈ (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)).extremePoints ℝ)
    (hO : (0 : Plane) ∈ interior (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)))
    (hz : z ∈ interior (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)))
    (hz0 : z ≠ 0) :
    let X := insert (0 : Plane) (insert z (insert u C))
    X.card = 9 ∧ ∃ d : ℝ, 0 < d ∧ d < Metric.diam (X : Set Plane) ∧
      1 ≤ multiplicity X d ∧ multiplicity X d ≤ 9 := by
  by_cases hin : dist z (0 : Plane) < R
  · exact original_zero_centered_inside C u z R hC hR hcircle hu hext hO hz
      (dist_pos.mpr hz0) hin
  · exact HullOutlierOutside.original_zero_centered_outside C u z R hC hR hcircle hu
      hext hO hz (le_of_not_gt hin)

end Erdos132.HullOutlierInside
