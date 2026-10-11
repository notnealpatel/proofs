import Erdos.Erdos132.TwoInteriorCircle

set_option autoImplicit false
open scoped BigOperators
open Erdos132.TwoInteriorCircle

namespace Erdos132.KnownSixPointGeometry

private theorem inner_coords (u v : Plane) :
    inner ℝ u v = u 0 * v 0 + u 1 * v 1 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
  ring

private theorem gram_three (u v w : Plane) :
    ‖u‖ ^ 2 * ‖v‖ ^ 2 * ‖w‖ ^ 2 +
      2 * inner ℝ u v * inner ℝ u w * inner ℝ v w -
      ‖u‖ ^ 2 * (inner ℝ v w) ^ 2 -
      ‖v‖ ^ 2 * (inner ℝ u w) ^ 2 -
      ‖w‖ ^ 2 * (inner ℝ u v) ^ 2 = 0 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, inner_coords]
  ring

private theorem orthogonal_gram (z u v : Plane)
    (hzu : inner ℝ z u = 0) (hzv : inner ℝ z v = 0) :
    ‖z‖ ^ 2 * (‖u‖ ^ 2 * ‖v‖ ^ 2 - (inner ℝ u v) ^ 2) = 0 := by
  have h := gram_three z u v
  rw [hzu, hzv] at h
  nlinarith only [h]

private theorem parallel_inner (z u v : Plane) (hv : v ≠ 0)
    (hzv : inner ℝ z v = 0) (huv : inner ℝ u v = 0) :
    (inner ℝ z u) ^ 2 = ‖z‖ ^ 2 * ‖u‖ ^ 2 := by
  have h := orthogonal_gram v z u (by simpa [real_inner_comm] using hzv)
    (by simpa [real_inner_comm] using huv)
  have hvn : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
  have hh := (mul_eq_zero.mp h).resolve_left hvn
  linarith

private theorem centered_norms (q : Fin 5 → Plane) (A B : ℝ)
    (hsum : ∑ i, q i = 0)
    (hd : ∀ i j, ‖q i - q j‖ ^ 2 =
      if i = j then 0 else if j = i + 1 ∨ i = j + 1 then A else B) :
    ∀ i, ‖q i‖ ^ 2 = (A + B) / 5 := by
  have hrow (i : Fin 5) : ∑ j, ‖q i - q j‖ ^ 2 = 2 * A + 2 * B := by
    simp_rw [hd]
    simp only [Fin.sum_univ_five]
    fin_cases i <;> norm_num [Fin.ext_iff, Fin.val_add] <;> ring
  have hexpand (i : Fin 5) :
      5 * ‖q i‖ ^ 2 + ∑ j, ‖q j‖ ^ 2 = 2 * A + 2 * B := by
    have hh := hrow i
    simp_rw [norm_sub_sq_real] at hh
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum, ← inner_sum, hsum, inner_zero_right, mul_zero, sub_zero] at hh
    exact hh
  have hequal (i : Fin 5) : ‖q i‖ ^ 2 = ‖q 0‖ ^ 2 := by
    linarith only [hexpand i, hexpand 0]
  have htotal : (∑ j, ‖q j‖ ^ 2) = 5 * ‖q 0‖ ^ 2 := by
    simp_rw [hequal]
    simp
  intro i
  rw [hequal]
  linarith only [hexpand 0, htotal]


private theorem perpendicular_product (z u v w : Plane) (hw : w ≠ 0)
    (hzw : inner ℝ z w = 0) (huw : inner ℝ u w = 0)
    (hvw : inner ℝ v w = 0) :
    ‖v‖ ^ 2 * inner ℝ z u = inner ℝ z v * inner ℝ u v := by
  have hz := parallel_inner z v w hw hzw hvw
  have hu := parallel_inner u v w hw huw hvw
  have hzu := parallel_inner (z + u) v w hw
    (by rw [inner_add_left, hzw, huw]; ring) hvw
  rw [inner_add_left, norm_add_sq_real] at hzu
  nlinarith only [hz, hu, hzu]

private theorem metric_inner (q : Fin 5 → Plane) (A B r : ℝ)
    (hc : ∀ i, ‖q i‖ ^ 2 = r)
    (hd : ∀ i j, ‖q i - q j‖ ^ 2 =
      if i = j then 0 else if j = i + 1 ∨ i = j + 1 then A else B) :
    ∀ i j, inner ℝ (q i) (q j) =
      r - (if i = j then 0 else if j = i + 1 ∨ i = j + 1 then A else B) / 2 := by
  intro i j
  have h := hd i j
  rw [norm_sub_sq_real, hc i, hc j] at h
  linarith only [h]

private theorem metric_relation (q : Fin 5 → Plane) (A B r : ℝ)
    (hB : 0 < B) (hr : 5 * r = A + B)
    (hc : ∀ i, ‖q i‖ ^ 2 = r)
    (hi : ∀ i j, inner ℝ (q i) (q j) =
      r - (if i = j then 0 else if j = i + 1 ∨ i = j + 1 then A else B) / 2) :
    A ^ 2 - 3 * A * B + B ^ 2 = 0 := by
  have h := gram_three (q 0) (q 1) (q 2)
  simp only [hc, hi] at h
  norm_num [Fin.add_def, Fin.ext_iff] at h
  have hf : B * (A ^ 2 - 4 * A * r + B * r) = 0 := by
    nlinarith only [h]
  have hh := (mul_eq_zero.mp hf).resolve_left (ne_of_gt hB)
  linear_combination 5 * hh + (4 * A - B) * hr

private theorem center_not_length (A B r : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hr : 5 * r = A + B) (hrel : A ^ 2 - 3 * A * B + B ^ 2 = 0) :
    r ≠ A ∧ r ≠ B := by
  constructor
  · intro he
    rw [he] at hr
    have hb : B = 4 * A := by linarith only [hr]
    rw [hb] at hrel
    nlinarith only [hrel, sq_pos_of_pos hA]
  · intro he
    rw [he] at hr
    have ha : A = 4 * B := by linarith only [hr]
    rw [ha] at hrel
    nlinarith only [hrel, sq_pos_of_pos hB]

private theorem axis_exclusion (q : Fin 5 → Plane) (y : Plane) (A B r L M : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hAB : A ≠ B) (hr : 5 * r = A + B)
    (hc : ∀ i, ‖q i‖ ^ 2 = r)
    (hi : ∀ i j, inner ℝ (q i) (q j) =
      r - (if i = j then 0 else if j = i + 1 ∨ i = j + 1 then A else B) / 2)
    (hsum : ∑ i, q i = 0) (hy : y ≠ q 0)
    (hLM : (L = A ∧ M = B) ∨ (L = B ∧ M = A))
    (h1 : ‖y - q 1‖ ^ 2 = L) (h4 : ‖y - q 4‖ ^ 2 = L)
    (h2 : ‖y - q 2‖ ^ 2 = M) (h3 : ‖y - q 3‖ ^ 2 = M) : False := by
  have hrpos : 0 < r := by linarith only [hr, hA, hB]
  have hw : q 1 - q 4 ≠ 0 := by
    intro he
    have hn : ‖q 1 - q 4‖ ^ 2 = 0 := by rw [he, norm_zero]; ring
    rw [norm_sub_sq_real, hc, hc, hi] at hn
    norm_num [Fin.add_def, Fin.ext_iff] at hn
    linarith only [hn, hB]
  have hzw : inner ℝ y (q 1 - q 4) = 0 := by
    rw [inner_sub_right]
    rw [norm_sub_sq_real, hc] at h1 h4
    linarith only [h1, h4]
  have h0w : inner ℝ (q 0) (q 1 - q 4) = 0 := by
    rw [inner_sub_right, hi, hi]
    norm_num [Fin.add_def, Fin.ext_iff]
  have huw : inner ℝ (q 1 + q 4) (q 1 - q 4) = 0 := by
    rw [inner_add_left, inner_sub_right, inner_sub_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hc, hc,
      real_inner_comm (q 4) (q 1)]
    ring
  have hp := perpendicular_product y (q 1 + q 4) (q 0) (q 1 - q 4)
    hw hzw huw h0w
  rw [hc, inner_add_left, hi, hi] at hp
  norm_num [Fin.add_def, Fin.ext_iff] at hp
  have hparallel := parallel_inner y (q 0) (q 1 - q 4) hw hzw h0w
  rw [hc] at hparallel
  have hsum' : q 1 + q 4 + (q 2 + q 3) = -q 0 := by
    rw [Fin.sum_univ_five] at hsum
    calc
      _ = (q 0 + q 1 + q 2 + q 3 + q 4) - q 0 := by abel
      _ = -q 0 := by rw [hsum]; simp
  have ht : inner ℝ y (q 0) = L + M - 2 * (‖y‖ ^ 2 + r) := by
    have hh := congrArg (fun v : Plane => inner ℝ y v) hsum'
    simp only [inner_add_right, inner_neg_right] at hh
    rw [norm_sub_sq_real, hc] at h1 h2 h3 h4
    linarith only [hh, h1, h2, h3, h4]
  have hu : inner ℝ y (q 1 + q 4) = ‖y‖ ^ 2 + r - L := by
    rw [inner_add_right]
    rw [norm_sub_sq_real, hc] at h1 h4
    linarith only [h1, h4]
  rw [hu] at hp
  rcases hLM with ⟨hL, hM⟩ | ⟨hL, hM⟩
  · rw [hL] at hp
    rw [hL, hM] at ht
    have ht0 : inner ℝ y (q 0) = r := by
      have hf : (A - B) * (inner ℝ y (q 0) - r) = 0 := by
        linear_combination 2 * hp - r * ht + inner ℝ y (q 0) * hr
      exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr hAB))
    have hs : ‖y‖ ^ 2 = r := by linarith only [ht, ht0, hr]
    have hz : ‖y - q 0‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, hc, hs, ht0]; ring
    exact hy (sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (y - q 0)])))
  · rw [hL] at hp
    rw [hL, hM] at ht
    have ht0 : inner ℝ y (q 0) = -r := by
      have hf : (A - B) * (inner ℝ y (q 0) + r) = 0 := by
        linear_combination 2 * hp - r * ht + inner ℝ y (q 0) * hr
      have hh := (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr hAB)
      linarith only [hh]
    have hs : ‖y‖ ^ 2 = 2 * r := by linarith only [ht, ht0, hr]
    rw [ht0, hs] at hparallel
    nlinarith only [hparallel, sq_pos_of_pos hrpos]


private theorem nonaxis_exclusion (q : Fin 5 → Plane) (y : Plane) (A B r L M : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hr : 5 * r = A + B)
    (hc : ∀ i, ‖q i‖ ^ 2 = r)
    (hi : ∀ i j, inner ℝ (q i) (q j) =
      r - (if i = j then 0 else if j = i + 1 ∨ i = j + 1 then A else B) / 2)
    (hLM : (L = A ∧ M = B) ∨ (L = B ∧ M = A))
    (h1 : ‖y - q 1‖ ^ 2 = L)
    (hcase : (‖y - q 2‖ ^ 2 = L ∧ ‖y - q 3‖ ^ 2 = M ∧ ‖y - q 4‖ ^ 2 = M) ∨
      (‖y - q 3‖ ^ 2 = L ∧ ‖y - q 2‖ ^ 2 = M ∧ ‖y - q 4‖ ^ 2 = M)) : False := by
  have hrel := metric_relation q A B r hB hr hc hi
  have hcenter := center_not_length A B r hA hB hr hrel
  have h3A : 3 * A - B ≠ 0 := by
    intro he
    have hb : B = 3 * A := by linarith only [he]
    rw [hb] at hrel
    nlinarith only [hrel, sq_pos_of_pos hA]
  have h3B : 3 * B - A ≠ 0 := by
    intro he
    have ha : A = 3 * B := by linarith only [he]
    rw [ha] at hrel
    nlinarith only [hrel, sq_pos_of_pos hB]
  have horth (i j : Fin 5) (N : ℝ)
      (hiN : ‖y - q i‖ ^ 2 = N) (hjN : ‖y - q j‖ ^ 2 = N) :
      inner ℝ y (q i - q j) = 0 := by
    rw [inner_sub_right]
    rw [norm_sub_sq_real, hc] at hiN hjN
    linarith only [hiN, hjN]
  have hkill (u v : Plane) (hu : inner ℝ y u = 0) (hv : inner ℝ y v = 0)
      (hdet : ‖u‖ ^ 2 * ‖v‖ ^ 2 - (inner ℝ u v) ^ 2 ≠ 0) : False := by
    have hn := orthogonal_gram y u v hu hv
    have hy0 : y = 0 := norm_eq_zero.mp (by
      have hh := (mul_eq_zero.mp hn).resolve_right hdet
      nlinarith only [hh, norm_nonneg y])
    rw [hy0, zero_sub, norm_neg, hc] at h1
    rcases hLM with ⟨hL, hM⟩ | ⟨hL, hM⟩
    · exact hcenter.1 (h1.trans hL)
    · exact hcenter.2 (h1.trans hL)
  rcases hcase with ⟨h2, h3, h4⟩ | ⟨h3, h2, h4⟩
  · apply hkill (q 1 - q 2) (q 3 - q 4) (horth 1 2 L h1 h2) (horth 3 4 M h3 h4)
    have he : ‖q 1 - q 2‖ ^ 2 * ‖q 3 - q 4‖ ^ 2 -
        (inner ℝ (q 1 - q 2) (q 3 - q 4)) ^ 2 = (A + B) * (3 * A - B) / 4 := by
      simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right, hc, hi]
      norm_num [Fin.ext_iff, Fin.val_add]
      ring
    rw [he]
    exact div_ne_zero (mul_ne_zero (ne_of_gt (add_pos hA hB)) h3A) (by norm_num)
  · apply hkill (q 1 - q 3) (q 2 - q 4) (horth 1 3 L h1 h3) (horth 2 4 M h2 h4)
    have he : ‖q 1 - q 3‖ ^ 2 * ‖q 2 - q 4‖ ^ 2 -
        (inner ℝ (q 1 - q 3) (q 2 - q 4)) ^ 2 = (A + B) * (3 * B - A) / 4 := by
      simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right, hc, hi]
      norm_num [Fin.ext_iff, Fin.val_add]
      ring
    rw [he]
    exact div_ne_zero (mul_ne_zero (ne_of_gt (add_pos hA hB)) h3B) (by norm_num)

private theorem pairing_inventory : ∀ (s t : Finset (Fin 5)),
    s.card = 2 → t.card = 2 → Disjoint s t →
    ∃ h : Fin 5,
      (s = {h + 1, h + 2} ∧ t = {h + 3, h + 4}) ∨
      (t = {h + 1, h + 2} ∧ s = {h + 3, h + 4}) ∨
      (s = {h + 1, h + 3} ∧ t = {h + 2, h + 4}) ∨
      (t = {h + 1, h + 3} ∧ s = {h + 2, h + 4}) ∨
      (s = {h + 1, h + 4} ∧ t = {h + 2, h + 3}) ∨
      (t = {h + 1, h + 4} ∧ s = {h + 2, h + 3}) := by
  decide


/-- An injective five-cycle in the ordinary Euclidean plane with two distinct positive
cyclic distance classes admits no outside point with two radial neighbors in each class.
Addition on `Fin 5` is exactly addition modulo five; no geometric ordering is assumed. -/
theorem no_two_two_extension_of_five_cycle_metric
    (p : Fin 5 → Plane) (hp : Function.Injective p) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (hside : ∀ i, dist (p i) (p (i + 1)) = a)
    (hstar : ∀ i, dist (p i) (p (i + 2)) = b)
    (x : Plane) (hx : x ∉ Set.range p) :
    ¬((Finset.univ.filter fun i => dist x (p i) = a).card = 2 ∧
      (Finset.univ.filter fun i => dist x (p i) = b).card = 2) := by
  classical
  intro hcounts
  let s := Finset.univ.filter fun i => dist x (p i) = a
  let t := Finset.univ.filter fun i => dist x (p i) = b
  have hdis : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro i his hit
    have hs := (Finset.mem_filter.mp his).2
    have ht := (Finset.mem_filter.mp hit).2
    exact hab (hs.symm.trans ht)
  obtain ⟨h, hpair⟩ := pairing_inventory s t hcounts.1 hcounts.2 hdis
  let o : Plane := (5 : ℝ)⁻¹ • ∑ i : Fin 5, p (h + i)
  let q : Fin 5 → Plane := fun i => p (h + i) - o
  let y : Plane := x - o
  let A : ℝ := a ^ 2
  let B : ℝ := b ^ 2
  let r : ℝ := (A + B) / 5
  have hA : 0 < A := sq_pos_of_pos ha
  have hB : 0 < B := sq_pos_of_pos hb
  have hAB : A ≠ B := by
    intro he
    exact hab ((sq_eq_sq₀ ha.le hb.le).mp he)
  have hr : 5 * r = A + B := by dsimp [r]; ring
  have hpd : ∀ i j : Fin 5, ‖p i - p j‖ ^ 2 =
      if i = j then 0 else if j = i + 1 ∨ i = j + 1 then A else B := by
    have hs (i : Fin 5) : ‖p i - p (i + 1)‖ ^ 2 = A := by
      rw [← dist_eq_norm, hside]
    have ht (i : Fin 5) : ‖p i - p (i + 2)‖ ^ 2 = B := by
      rw [← dist_eq_norm, hstar]
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff, Fin.val_add]
    · exact hs 0
    · exact ht 0
    · rw [norm_sub_rev]
      exact ht 3
    · rw [norm_sub_rev]
      exact hs 4
    · rw [norm_sub_rev]
      exact hs 0
    · exact hs 1
    · exact ht 1
    · rw [norm_sub_rev]
      exact ht 4
    · rw [norm_sub_rev]
      exact ht 0
    · rw [norm_sub_rev]
      exact hs 1
    · exact hs 2
    · exact ht 2
    · exact ht 3
    · rw [norm_sub_rev]
      exact ht 1
    · rw [norm_sub_rev]
      exact hs 2
    · exact hs 3
    · exact hs 4
    · exact ht 4
    · rw [norm_sub_rev]
      exact ht 2
    · rw [norm_sub_rev]
      exact hs 3
  have hd : ∀ i j, ‖q i - q j‖ ^ 2 =
      if i = j then 0 else if j = i + 1 ∨ i = j + 1 then A else B := by
    intro i j
    have he : q i - q j = p (h + i) - p (h + j) := by dsimp [q]; abel
    rw [he, hpd]
    simp only [add_assoc, add_left_cancel_iff]
  have hsum : ∑ i, q i = 0 := by
    dsimp [q]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    dsimp [o]
    module
  have hc : ∀ i, ‖q i‖ ^ 2 = r := centered_norms q A B hsum hd
  have hi := metric_inner q A B r hc hd
  have hy : y ≠ q 0 := by
    intro he
    apply hx
    refine ⟨h, ?_⟩
    dsimp [y, q] at he
    simpa only [add_zero] using (sub_left_inj.mp he).symm
  have hradA (i : Fin 5) (his : h + i ∈ s) : ‖y - q i‖ ^ 2 = A := by
    have he : y - q i = x - p (h + i) := by dsimp [y, q]; abel
    rw [he, ← dist_eq_norm, (Finset.mem_filter.mp his).2]
  have hradB (i : Fin 5) (hit : h + i ∈ t) : ‖y - q i‖ ^ 2 = B := by
    have he : y - q i = x - p (h + i) := by dsimp [y, q]; abel
    rw [he, ← dist_eq_norm, (Finset.mem_filter.mp hit).2]
  rcases hpair with ⟨hs, ht⟩ | ⟨ht, hs⟩ | ⟨hs, ht⟩ | ⟨ht, hs⟩ | ⟨hs, ht⟩ | ⟨ht, hs⟩
  · apply nonaxis_exclusion q y A B r A B hA hB hr hc hi
    · exact Or.inl ⟨rfl, rfl⟩
    · exact hradA 1 (by rw [hs]; simp)
    · left
      refine ⟨?_, ?_, ?_⟩
      · exact hradA 2 (by rw [hs]; simp)
      · exact hradB 3 (by rw [ht]; simp)
      · exact hradB 4 (by rw [ht]; simp)
  · apply nonaxis_exclusion q y A B r B A hA hB hr hc hi
    · exact Or.inr ⟨rfl, rfl⟩
    · exact hradB 1 (by rw [ht]; simp)
    · left
      refine ⟨?_, ?_, ?_⟩
      · exact hradB 2 (by rw [ht]; simp)
      · exact hradA 3 (by rw [hs]; simp)
      · exact hradA 4 (by rw [hs]; simp)
  · apply nonaxis_exclusion q y A B r A B hA hB hr hc hi
    · exact Or.inl ⟨rfl, rfl⟩
    · exact hradA 1 (by rw [hs]; simp)
    · right
      refine ⟨?_, ?_, ?_⟩
      · exact hradA 3 (by rw [hs]; simp)
      · exact hradB 2 (by rw [ht]; simp)
      · exact hradB 4 (by rw [ht]; simp)
  · apply nonaxis_exclusion q y A B r B A hA hB hr hc hi
    · exact Or.inr ⟨rfl, rfl⟩
    · exact hradB 1 (by rw [ht]; simp)
    · right
      refine ⟨?_, ?_, ?_⟩
      · exact hradB 3 (by rw [ht]; simp)
      · exact hradA 2 (by rw [hs]; simp)
      · exact hradA 4 (by rw [hs]; simp)
  · apply axis_exclusion q y A B r A B hA hB hAB hr hc hi hsum hy
    · exact Or.inl ⟨rfl, rfl⟩
    · exact hradA 1 (by rw [hs]; simp)
    · exact hradA 4 (by rw [hs]; simp)
    · exact hradB 2 (by rw [ht]; simp)
    · exact hradB 3 (by rw [ht]; simp)
  · apply axis_exclusion q y A B r B A hA hB hAB hr hc hi hsum hy
    · exact Or.inr ⟨rfl, rfl⟩
    · exact hradB 1 (by rw [ht]; simp)
    · exact hradB 4 (by rw [ht]; simp)
    · exact hradA 2 (by rw [hs]; simp)
    · exact hradA 3 (by rw [hs]; simp)

end Erdos132.KnownSixPointGeometry
