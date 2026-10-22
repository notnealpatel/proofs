import Mathlib

set_option autoImplicit false

namespace AnningErdos

open EuclideanGeometry

/-- The Euclidean plane, with its standard real inner product. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- All distances between points of the set are integer casts. -/
def IntegralDistances (A : Set Plane) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∃ z : ℤ, dist x y = (z : ℝ)

example : IntegralDistances ({0} : Set Plane) := by
  intro x hx y hy
  simp only [Set.mem_singleton_iff] at hx hy
  subst x; subst y
  exact ⟨0, by simp⟩

private lemma norm_sq (p : Plane) : ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 := by
  simpa [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_sq_eq p

private lemma dist_sq (p q : Plane) :
    dist p q ^ 2 = (p 0 - q 0)^2 + (p 1 - q 1)^2 := by
  simpa [dist_eq_norm, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] using
    EuclideanSpace.norm_sq_eq (p-q)

private lemma quadratic_nonzero
    (a₀ a₁ b₀ b₁ k l : ℝ)
    (hD : a₀*b₁-a₁*b₀ ≠ 0) :
    let D := a₀*b₁-a₁*b₀
    let c := (a₀^2+a₁^2-k^2)/2
    let d := (b₀^2+b₁^2-l^2)/2
    let u₀ := l*a₁-k*b₁
    let u₁ := k*b₀-l*a₀
    let v₀ := c*b₁-d*a₁
    let v₁ := d*a₀-c*b₀
    u₀^2+u₁^2-D^2 ≠ 0 ∨ v₀^2+v₁^2 ≠ 0 := by
  dsimp only
  let D := a₀*b₁-a₁*b₀
  let c := (a₀^2+a₁^2-k^2)/2
  let d := (b₀^2+b₁^2-l^2)/2
  let u₀ := l*a₁-k*b₁
  let u₁ := k*b₀-l*a₀
  let v₀ := c*b₁-d*a₁
  let v₁ := d*a₀-c*b₀
  change u₀^2+u₁^2-D^2 ≠ 0 ∨ v₀^2+v₁^2 ≠ 0
  by_contra h
  push Not at h
  obtain ⟨hu, hv⟩ := h
  have hv₀ : v₀ = 0 := by nlinarith only [hv, sq_nonneg v₁]
  have hv₁ : v₁ = 0 := by nlinarith only [hv, sq_nonneg v₀]
  have hcD : c*D = 0 := by
    calc
      _ = a₀*v₀+a₁*v₁ := by dsimp [D, v₀, v₁]; ring
      _ = 0 := by rw [hv₀, hv₁]; ring
  have hdD : d*D = 0 := by
    calc
      _ = b₀*v₀+b₁*v₁ := by dsimp [D, v₀, v₁]; ring
      _ = 0 := by rw [hv₀, hv₁]; ring
  have hc : a₀^2+a₁^2-k^2 = 0 := by
    have hc0 : c = 0 := (mul_eq_zero.mp hcD).resolve_right hD
    dsimp [c] at hc0
    linarith only [hc0]
  have hd : b₀^2+b₁^2-l^2 = 0 := by
    have hd0 : d = 0 := (mul_eq_zero.mp hdD).resolve_right hD
    dsimp [d] at hd0
    linarith only [hd0]
  have ha : (a₀*D+k*u₀)^2 + (a₁*D+k*u₁)^2 = 0 := by
    calc
      _ = D^2*(a₀^2+a₁^2-k^2)+k^2*(u₀^2+u₁^2-D^2) := by
        dsimp [D, u₀, u₁]; ring
      _ = 0 := by rw [hc, hu]; ring
  have hb : (b₀*D+l*u₀)^2 + (b₁*D+l*u₁)^2 = 0 := by
    calc
      _ = D^2*(b₀^2+b₁^2-l^2)+l^2*(u₀^2+u₁^2-D^2) := by
        dsimp [D, u₀, u₁]; ring
      _ = 0 := by rw [hd, hu]; ring
  have ha₀ : a₀*D = -k*u₀ := by nlinarith only [ha, sq_nonneg (a₁*D+k*u₁)]
  have ha₁ : a₁*D = -k*u₁ := by nlinarith only [ha, sq_nonneg (a₀*D+k*u₀)]
  have hb₀ : b₀*D = -l*u₀ := by nlinarith only [hb, sq_nonneg (b₁*D+l*u₁)]
  have hb₁ : b₁*D = -l*u₁ := by nlinarith only [hb, sq_nonneg (b₀*D+l*u₀)]
  have he : D^3 = 0 := by
    calc
      _ = (a₀*D)*(b₁*D)-(a₁*D)*(b₀*D) := by dsimp [D]; ring
      _ = 0 := by rw [ha₀, ha₁, hb₀, hb₁]; ring
  exact pow_ne_zero 3 hD he

private lemma finite_locus (o a b : Plane)
    (hD : (a 0-o 0)*(b 1-o 1)-(a 1-o 1)*(b 0-o 0) ≠ 0) (k l : ℝ) :
    {p : Plane | dist p a-dist p o = k ∧ dist p b-dist p o = l}.Finite := by
  let a₀ := a 0-o 0
  let a₁ := a 1-o 1
  let b₀ := b 0-o 0
  let b₁ := b 1-o 1
  let D := a₀*b₁-a₁*b₀
  let c := (a₀^2+a₁^2-k^2)/2
  let d := (b₀^2+b₁^2-l^2)/2
  let u₀ := l*a₁-k*b₁
  let u₁ := k*b₀-l*a₀
  let v₀ := c*b₁-d*a₁
  let v₁ := d*a₀-c*b₀
  let S := {p : Plane | dist p a-dist p o = k ∧ dist p b-dist p o = l}
  have hcoord (p : Plane) (hp : p ∈ S) :
      D*(p 0-o 0) = u₀*dist p o+v₀ ∧
      D*(p 1-o 1) = u₁*dist p o+v₁ := by
    have hpa : dist p a = dist p o+k := by linarith only [hp.1]
    have hpb : dist p b = dist p o+l := by linarith only [hp.2]
    have hea : a₀*(p 0-o 0)+a₁*(p 1-o 1) = c-k*dist p o := by
      have ha := dist_sq p a
      have ho := dist_sq p o
      rw [hpa] at ha
      dsimp [a₀, a₁, c]
      nlinarith only [ha, ho]
    have heb : b₀*(p 0-o 0)+b₁*(p 1-o 1) = d-l*dist p o := by
      have hb := dist_sq p b
      have ho := dist_sq p o
      rw [hpb] at hb
      dsimp [b₀, b₁, d]
      nlinarith only [hb, ho]
    constructor
    · calc
        _ = b₁*(a₀*(p 0-o 0)+a₁*(p 1-o 1)) -
            a₁*(b₀*(p 0-o 0)+b₁*(p 1-o 1)) := by dsimp [D]; ring
        _ = _ := by rw [hea, heb]; dsimp [u₀, v₀]; ring
    · calc
        _ = a₀*(b₀*(p 0-o 0)+b₁*(p 1-o 1)) -
            b₀*(a₀*(p 0-o 0)+a₁*(p 1-o 1)) := by dsimp [D]; ring
        _ = _ := by rw [hea, heb]; dsimp [u₁, v₁]; ring
  let F : Polynomial ℝ := Polynomial.C (u₀^2+u₁^2-D^2)*Polynomial.X^2 +
    Polynomial.C (2*(u₀*v₀+u₁*v₁))*Polynomial.X^1 + Polynomial.C (v₀^2+v₁^2)
  have hF : F ≠ 0 := by
    intro hzero
    have htwo := congrArg (fun f : Polynomial ℝ => f.coeff 2) hzero
    have hzero' := congrArg (fun f : Polynomial ℝ => f.coeff 0) hzero
    have ht : u₀^2+u₁^2-D^2 = 0 := by simpa only [F, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_zero, if_pos, if_neg, ite_false, OfNat.ofNat_ne_zero,
      (show (2 : ℕ) ≠ 1 from by decide), add_zero] using htwo
    have hz : v₀^2+v₁^2 = 0 := by simpa only [F, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_zero, if_pos, if_neg, ite_false,
      (show (0 : ℕ) ≠ 2 from by decide), (show (0 : ℕ) ≠ 1 from by decide), zero_add] using hzero'
    exact (quadratic_nonzero a₀ a₁ b₀ b₁ k l hD).elim (fun h => h ht) (fun h => h hz)
  have hroot (p : Plane) (hp : p ∈ S) : F.IsRoot (dist p o) := by
    obtain ⟨hx, hy⟩ := hcoord p hp
    have hnorm := dist_sq p o
    have he : (u₀*dist p o+v₀)^2+(u₁*dist p o+v₁)^2 = D^2*dist p o^2 := by
      rw [← hx, ← hy]
      calc
        _ = D^2*((p 0-o 0)^2+(p 1-o 1)^2) := by ring
        _ = _ := by rw [← hnorm]
    change F.eval (dist p o) = 0
    simp only [F, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    nlinarith only [he]
  have himage : ((fun p : Plane => dist p o) '' S).Finite :=
    (Polynomial.finite_setOfPred_isRoot hF).subset (by
      rintro r ⟨p, hp, rfl⟩
      exact hroot p hp)
  apply himage.of_finite_image
  intro p hp q hq he
  obtain ⟨hp₀, hp₁⟩ := hcoord p hp
  obtain ⟨hq₀, hq₁⟩ := hcoord q hq
  change dist p o = dist q o at he
  rw [he] at hp₀ hp₁
  have hx : p 0-o 0 = q 0-o 0 := mul_left_cancel₀ hD (hp₀.trans hq₀.symm)
  have hy : p 1-o 1 = q 1-o 1 := mul_left_cancel₀ hD (hp₁.trans hq₁.symm)
  apply PiLp.ext
  intro i
  fin_cases i
  · change p 0 = q 0
    linarith only [hx]
  · change p 1 = q 1
    linarith only [hy]

private lemma collinear_of_det (A : Set Plane) (o a : Plane) (ho : o ∈ A) (ha : a ≠ o)
    (hd : ∀ p ∈ A, (a 0-o 0)*(p 1-o 1)-(a 1-o 1)*(p 0-o 0) = 0) :
    Collinear ℝ A := by
  apply (collinear_iff_of_mem ho).2
  refine ⟨a-o, ?_⟩
  intro p hp
  have hd' := hd p hp
  by_cases h₀ : a 0-o 0 = 0
  · have h₁ : a 1-o 1 ≠ 0 := by
      intro h₁
      apply ha
      apply PiLp.ext
      intro i
      fin_cases i
      · change a 0 = o 0
        linarith only [h₀]
      · change a 1 = o 1
        linarith only [h₁]
    refine ⟨(p 1-o 1)/(a 1-o 1), ?_⟩
    apply PiLp.ext
    intro i
    fin_cases i
    · change p 0 = (p 1-o 1)/(a 1-o 1)*(a 0-o 0)+o 0
      rw [h₀, mul_zero, zero_add]
      have hp₀ : p 0-o 0 = 0 := by
        have hmul : (a 1-o 1)*(p 0-o 0) = 0 := by rw [h₀] at hd'; linarith only [hd']
        exact (mul_eq_zero.mp hmul).resolve_left h₁
      linarith only [hp₀]
    · change p 1 = (p 1-o 1)/(a 1-o 1)*(a 1-o 1)+o 1
      rw [div_mul_cancel₀ _ h₁]
      ring
  · refine ⟨(p 0-o 0)/(a 0-o 0), ?_⟩
    apply PiLp.ext
    intro i
    fin_cases i
    · change p 0 = (p 0-o 0)/(a 0-o 0)*(a 0-o 0)+o 0
      rw [div_mul_cancel₀ _ h₀]
      ring
    · change p 1 = (p 0-o 0)/(a 0-o 0)*(a 1-o 1)+o 1
      apply (mul_right_cancel₀ h₀)
      field_simp
      nlinarith only [hd']

private lemma finite_of_integral (A : Set Plane) (hd : IntegralDistances A)
    (o a b : Plane) (ho : o ∈ A) (ha : a ∈ A) (hb : b ∈ A)
    (hD : (a 0-o 0)*(b 1-o 1)-(a 1-o 1)*(b 0-o 0) ≠ 0) : A.Finite := by
  obtain ⟨ma, hma⟩ := hd a ha o ho
  obtain ⟨mb, hmb⟩ := hd b hb o ho
  let f : Plane → ℝ × ℝ := fun p => (dist p a-dist p o, dist p b-dist p o)
  let T : Set (ℝ × ℝ) :=
    ((fun z : ℤ => (z : ℝ)) '' Set.Icc (-ma) ma) ×ˢ
    ((fun z : ℤ => (z : ℝ)) '' Set.Icc (-mb) mb)
  have hT : T.Finite := ((Set.finite_Icc (-ma) ma).image _).prod
    ((Set.finite_Icc (-mb) mb).image _)
  have himage : (f '' A).Finite := hT.subset (by
    rintro x ⟨p, hp, rfl⟩
    obtain ⟨zpa, hzpa⟩ := hd p hp a ha
    obtain ⟨zpb, hzpb⟩ := hd p hp b hb
    obtain ⟨zpo, hzpo⟩ := hd p hp o ho
    have hea : dist p a-dist p o = ((zpa-zpo : ℤ) : ℝ) := by
      rw [hzpa, hzpo, Int.cast_sub]
    have heb : dist p b-dist p o = ((zpb-zpo : ℤ) : ℝ) := by
      rw [hzpb, hzpo, Int.cast_sub]
    have hba : |((zpa-zpo : ℤ) : ℝ)| ≤ (ma : ℝ) := by
      have h := abs_dist_sub_le a o p
      simpa only [dist_comm a p, dist_comm o p, hea, hma] using h
    have hbb : |((zpb-zpo : ℤ) : ℝ)| ≤ (mb : ℝ) := by
      have h := abs_dist_sub_le b o p
      simpa only [dist_comm b p, dist_comm o p, heb, hmb] using h
    have hza : zpa-zpo ∈ Set.Icc (-ma) ma := by
      obtain ⟨hlo, hhi⟩ := abs_le.mp hba
      constructor
      · exact_mod_cast hlo
      · exact_mod_cast hhi
    have hzb : zpb-zpo ∈ Set.Icc (-mb) mb := by
      obtain ⟨hlo, hhi⟩ := abs_le.mp hbb
      constructor
      · exact_mod_cast hlo
      · exact_mod_cast hhi
    exact ⟨⟨zpa-zpo, hza, hea.symm⟩, ⟨zpb-zpo, hzb, heb.symm⟩⟩)
  apply Set.Finite.of_finite_fibers f himage
  intro x hx
  apply (finite_locus o a b hD x.1 x.2).subset
  intro p hp
  have he : f p = x := hp.2
  exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩

/-- An infinite planar set whose pairwise distances are integral is collinear.
This is an independent coordinate-quadratic proof of the Anning–Erdős theorem;
it is not a formalization of the angular proof in the original 1945 paper. -/
theorem anning_erdos (A : Set Plane) (hA : A.Infinite)
    (hd : IntegralDistances A) : Collinear ℝ A := by
  obtain ⟨o, ho⟩ := hA.nonempty
  obtain ⟨a, ha, hao⟩ := hA.exists_notMem_finite (Set.finite_singleton o)
  have hao' : a ≠ o := hao
  by_contra hn
  have hb : ∃ b ∈ A, (a 0-o 0)*(b 1-o 1)-(a 1-o 1)*(b 0-o 0) ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (collinear_of_det A o a ho hao' h)
  obtain ⟨b, hb, hD⟩ := hb
  exact hA (finite_of_integral A hd o a b ho ha hb hD)

/-- Two integer-axis points have distance equal to the absolute integer difference. -/
theorem integer_axis_dist (n m : ℤ) : dist
    (WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then (n : ℝ) else 0) : Plane)
    (WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then (m : ℝ) else 0) : Plane) =
    ((|n-m| : ℤ) : ℝ) := by
  simp [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Int.cast_abs,
    Int.cast_sub, Real.sqrt_sq_eq_abs]

/-- The entire integer axis has pairwise integral distances. -/
theorem integer_axis_integral : IntegralDistances (Set.range (fun n : ℤ =>
    (WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then (n : ℝ) else 0) : Plane))) := by
  rintro x ⟨n, rfl⟩ y ⟨m, rfl⟩
  exact ⟨|n-m|, integer_axis_dist n m⟩

/-- The integer axis is infinite, witnessing the joint hypotheses of Anning–Erdős. -/
theorem integer_axis_infinite : (Set.range (fun n : ℤ =>
    (WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then (n : ℝ) else 0) : Plane))).Infinite := by
  apply Set.infinite_range_of_injective
  intro n m he
  have h₀ := congrArg (fun p : Plane => p 0) he
  simpa using h₀

example : ∃ A : Set Plane, A.Infinite ∧ IntegralDistances A :=
  ⟨_, integer_axis_infinite, integer_axis_integral⟩

/-- Edges join distinct points exactly when their distance is an integer cast. -/
def intDistGraph (A : Set Plane) : SimpleGraph A where
  Adj x y := x ≠ y ∧ ∃ z : ℤ, dist x.1 y.1 = (z : ℝ)
  symm := ⟨by
    intro x y h
    exact ⟨h.1.symm, by obtain ⟨z, hz⟩ := h.2; exact ⟨z, by rwa [dist_comm]⟩⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

/-- The adjacency predicate includes both distinctness and exact integrality. -/
theorem intDistGraph_adj (A : Set Plane) (x y : A) :
    (intDistGraph A).Adj x y ↔ x ≠ y ∧ ∃ z : ℤ, dist x.1 y.1 = (z : ℝ) := Iff.rfl

/-- If no three points of a planar set are collinear, its integer-distance graph
has no infinite clique. No concyclicity assumption is required. -/
theorem no_infinite_clique (A : Set Plane)
    (h3 : ∀ s ⊆ A, s.ncard = 3 → ¬ Collinear ℝ s)
    (B : Set A) (hB : B.Infinite)
    (hclique : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → (intDistGraph A).Adj x y) :
    False := by
  let C : Set Plane := Subtype.val '' B
  have hC : C.Infinite := hB.image Subtype.val_injective.injOn
  have hd : IntegralDistances C := by
    rintro p ⟨x, hx, rfl⟩ q ⟨y, hy, rfl⟩
    by_cases he : x = y
    · subst y
      exact ⟨0, by simp⟩
    · exact (hclique x hx y hy he).2
  have hc : Collinear ℝ C := anning_erdos C hC hd
  obtain ⟨s, hsC, _hsfin, hcard⟩ := hC.exists_subset_ncard_eq 3
  have hsA : s ⊆ A := by
    intro p hp
    obtain ⟨x, _hx, he⟩ := hsC hp
    exact he ▸ x.property
  exact (h3 s hsA hcard) (Collinear.subset hsC hc)

end AnningErdos
