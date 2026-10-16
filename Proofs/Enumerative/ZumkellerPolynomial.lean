import Enumerative.IsZumkeller

/-!
# Signed polynomial propagation of Zumkeller values

This is the positive-degree version of the polynomial propagation result in
Section 2 of arXiv:2310.14149 (`prop:Zum_poly_infinite`). Positive degree is
necessary for infinitely many distinct values: the constant polynomial 6
has positive leading coefficient but only one value.
-/

set_option autoImplicit false

open Filter Polynomial

private theorem zumkeller_of_square_dvd {z y : ℕ} (hz : IsZumkeller z)
    (hy : 0 < y) (hd : (z : ℤ) ^ 2 ∣ (y : ℤ) - z) : IsZumkeller y := by
  obtain ⟨q, hq⟩ := hd
  have heq : (y : ℤ) = (z : ℤ) * (1 + (z : ℤ) * q) := by
    nlinarith [hq]
  have hz' : (0 : ℤ) < z := by exact_mod_cast hz.pos
  have hy' : (0 : ℤ) < y := by exact_mod_cast hy
  have hm : 0 < 1 + (z : ℤ) * q := by nlinarith [heq]
  let m : ℕ := (1 + (z : ℤ) * q).toNat
  have hmcast : (m : ℤ) = 1 + (z : ℤ) * q := Int.toNat_of_nonneg (le_of_lt hm)
  have heq' : (y : ℤ) = (z : ℤ) * (m : ℤ) := by
    rw [hmcast]
    exact heq
  have hyzm : y = z * m := by exact_mod_cast heq'
  have hc : IsCoprime (z : ℤ) (m : ℤ) := by
    refine ⟨-q, 1, ?_⟩
    rw [hmcast]
    ring
  have hcop : z.Coprime m := by
    have hg := Int.isCoprime_iff_gcd_eq_one.mp hc
    simpa only [Int.gcd_natCast_natCast] using hg
  rw [hyzm]
  exact hz.mul_of_coprime hcop

/-- A positive-leading integer polynomial of positive degree that takes one
Zumkeller value at a natural argument takes infinitely many distinct natural
Zumkeller values. Coefficients other than the leading coefficient may be signed. -/
theorem IsZumkeller.infinite_polynomial_values (P : Polynomial ℤ)
    (hdeg : 0 < P.natDegree) (hlc : 0 < P.leadingCoeff)
    (l z : ℕ) (hz : IsZumkeller z) (hval : P.eval (l : ℤ) = (z : ℤ)) :
    {y : ℕ | IsZumkeller y ∧ ∃ n : ℕ, P.eval (n : ℤ) = (y : ℤ)}.Infinite := by
  let Q : Polynomial ℝ := P.map (Int.castRingHom ℝ)
  have hQdeg : 0 < Q.degree := by
    apply Polynomial.natDegree_pos_iff_degree_pos.mp
    simpa only [Q, Polynomial.natDegree_map_eq_of_injective
      (f := Int.castRingHom ℝ) Int.cast_injective] using hdeg
  have hQlc : 0 ≤ Q.leadingCoeff := by
    rw [Polynomial.leadingCoeff_map_of_injective Int.cast_injective]
    change (0 : ℝ) ≤ (P.leadingCoeff : ℝ)
    exact_mod_cast le_of_lt hlc
  have hgrowth := Q.tendsto_atTop_of_leadingCoeff_nonneg hQdeg hQlc
  have hz' : (0 : ℝ) < z := by exact_mod_cast hz.pos
  have hmul : Tendsto (fun x : ℝ => (z : ℝ)^2 * x) atTop atTop := by
    simpa only [pow_one] using
      (tendsto_const_mul_pow_atTop (n := 1) (by decide) (sq_pos_of_pos hz'))
  have harg : Tendsto (fun t : ℕ => (l : ℝ) + (z : ℝ)^2 * (t : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (hmul.comp tendsto_natCast_atTop_atTop)
  have hg : Tendsto (fun t : ℕ => Q.eval ((l : ℝ) + (z : ℝ)^2 * (t : ℝ)))
      atTop atTop := hgrowth.comp harg
  apply Set.infinite_of_not_bddAbove
  intro hb
  obtain ⟨b, hb⟩ := hb
  obtain ⟨t, ht⟩ := (hg.eventually (eventually_gt_atTop ((b : ℝ) + 1))).exists
  let n : ℕ := l + z^2 * t
  have heval : (Int.cast (P.eval (n : ℤ)) : ℝ) =
      Q.eval ((l : ℝ) + (z : ℝ)^2 * (t : ℝ)) := by
    simpa [Q, n] using
      (Polynomial.eval_map_apply (f := Int.castRingHom ℝ) (p := P) (n : ℤ)).symm
  have hbig : (b : ℤ) + 1 < P.eval (n : ℤ) := by
    exact_mod_cast (heval ▸ ht)
  have hpos : 0 < P.eval (n : ℤ) := by omega
  let y : ℕ := (P.eval (n : ℤ)).toNat
  have hycast : (y : ℤ) = P.eval (n : ℤ) := Int.toNat_of_nonneg (le_of_lt hpos)
  have hypos : 0 < y := by exact_mod_cast (hycast ▸ hpos)
  have hdarg : (z : ℤ)^2 ∣ (n : ℤ) - l := by
    refine ⟨(t : ℤ), ?_⟩
    simp [n]
  have hd : (z : ℤ)^2 ∣ (y : ℤ) - z := by
    have hdpoly := dvd_trans hdarg (Polynomial.sub_dvd_eval_sub (n : ℤ) (l : ℤ) P)
    rwa [hval, ← hycast] at hdpoly
  have hymem : y ∈ {y : ℕ | IsZumkeller y ∧ ∃ n : ℕ, P.eval (n : ℤ) = (y : ℤ)} :=
    ⟨zumkeller_of_square_dvd hz hypos hd, n, hycast.symm⟩
  have hle := hb hymem
  have hlt : b < y := by exact_mod_cast (show (b : ℤ) < (y : ℤ) by omega)
  omega

example : 0 < (X + C 6 : Polynomial ℤ).natDegree ∧
    0 < (X + C 6 : Polynomial ℤ).leadingCoeff ∧
    IsZumkeller 6 ∧ (X + C 6 : Polynomial ℤ).eval (0 : ℤ) = (6 : ℤ) := by
  simp only [Polynomial.natDegree_X_add_C, Polynomial.leadingCoeff_X_add_C,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  norm_num
  decide
