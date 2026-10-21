/-
# Filaseta–Martirosyan–Swan: the non-reciprocal part of `x^{d_r} + ⋯ + x^{d_1} + p`

## Source

arXiv:2610.05568, M. Filaseta, L. Martirosyan, L. C. Swan, "On the factorization of
`x^{d_r} + x^{d_{r-1}} + ⋯ + x^{d_2} + x^{d_1} + p` and a conjecture of C. Nicol".
Statement: Section 1, Theorem 1.1 (label `factorizationthm`); proof in Section 2
(Lemma 2.1 `f=uvlem` after Filaseta–Solan, Lemma 2.2 `Winfo`, Borisov's argument).
Recorded 2026-10-21.

Verbatim (Section 1):

> The *reciprocal* of a polynomial `w(x) ∈ ℝ[x]` is the polynomial `w̃(x) = x^{deg w} w(1/x)`.
> A `w(x) ∈ ℝ[x]` is a *reciprocal polynomial* if `w̃(x) = ±w(x)`. [...] The non-reciprocal
> part of `w(x) ∈ ℤ[x]` is `w(x)` removed of all of its irreducible reciprocal factors in
> `ℤ[x]` having positive leading coefficient. [...]
> Let `F(x) = x^{d_r} + x^{d_{r-1}} + ⋯ + x^{d_2} + x^{d_1} + p`, with `r, d_j ∈ ℤ^+`,
> `d_r > ⋯ > d_1`, and `p` prime.
> **Theorem 1.1.** The non-reciprocal part of the polynomial `F(x)` given in (1.1) is
> irreducible.

Status: proved in the paper (known result).

## Formalization

* `filasetaPoly p D = ∑_{d ∈ D} X^d + C p`, with `D = {d_1 < ⋯ < d_r}` a `Finset ℕ`,
  `0 ∉ D` (all `d_j ≥ 1`) and `D.Nonempty` (`r ≥ 1`).
* The paper's reciprocal `w̃` is `Polynomial.reverse`; it agrees with `Polynomial.mirror` for
  `w(0) ≠ 0` (`mirror_eq_reverse_of_coeff_zero_ne_zero`).
* The non-reciprocal part `N` is characterized by `F = R * N` with every irreducible factor of
  `R` reciprocal and no irreducible factor of `N` reciprocal; by unique factorization this
  determines `N` up to sign, and `exists_reciprocal_mul_nonreciprocal` shows such `R, N`
  always exist. `thm_1_1` is Theorem 1.1 in this form.
* `reverse_eq_or_reverse_eq_of_eq_mul` is the core (stronger than the "no non-reciprocal
  splitting" form): in any factorization `F = u v`, the factor whose constant term is prime to
  `p` satisfies `w̃ = w`. This bypasses Lemma 2.1 of the paper: an irreducible factor of a
  reducible non-reciprocal part with constant term prime to `p` would be reciprocal.
* The proof of the core follows Lemma 2.2 and Borisov's argument with `W = u ṽ`, replacing the
  paper's positivity/monic normalization by the inequality `c^2 - c ≥ p^2 - p` for nonzero
  multiples `c` of `p`.
-/
import Mathlib

set_option autoImplicit false

open Polynomial

namespace Candidates.FilasetaNonreciprocal

/-- The polynomial `F(x) = ∑_{d ∈ D} x^d + p` of the paper, display (1.1), with the exponent
set `D = {d_1 < ⋯ < d_r}` given as a `Finset ℕ`. -/
noncomputable def filasetaPoly (p : ℕ) (D : Finset ℕ) : ℤ[X] :=
  ∑ d ∈ D, (X : ℤ[X]) ^ d + C (p : ℤ)

/-- A polynomial has *0/1-shape with constant `p`* if its constant coefficient is `p` and every
other coefficient is `0` or `1`. This is the shape of `F(x)` and, by Lemma 2.2 of the paper, of
the auxiliary polynomial `W(x)`. -/
def ZeroOneShape (p : ℤ) (G : ℤ[X]) : Prop :=
  G.coeff 0 = p ∧ ∀ j, j ≠ 0 → G.coeff j = 0 ∨ G.coeff j = 1

/-- Coefficients of `filasetaPoly`. -/
theorem coeff_filasetaPoly (p : ℕ) (D : Finset ℕ) (j : ℕ) :
    (filasetaPoly p D).coeff j = (if j ∈ D then 1 else 0) + (if j = 0 then (p : ℤ) else 0) := by
  simp only [filasetaPoly, coeff_add, finsetSum_coeff, coeff_X_pow, coeff_C]
  rw [Finset.sum_ite_eq]

/-- `F(x)` has 0/1-shape with constant `p` whenever `0 ∉ D`. -/
theorem zeroOneShape_filasetaPoly (p : ℕ) (D : Finset ℕ) (hD0 : 0 ∉ D) :
    ZeroOneShape (p : ℤ) (filasetaPoly p D) := by
  refine ⟨?_, fun j hj => ?_⟩
  · rw [coeff_filasetaPoly]; simp [hD0]
  · rw [coeff_filasetaPoly]
    by_cases hjD : j ∈ D <;> simp [hjD, hj]

example : filasetaPoly 2 {1, 3} = X ^ 3 + X + C 2 := by
  simp only [filasetaPoly, Finset.mem_singleton, OfNat.one_ne_ofNat, not_false_eq_true,
    Finset.sum_insert, pow_one, Finset.sum_singleton, Nat.cast_ofNat, eq_intCast, Int.cast_ofNat,
    add_left_inj]
  ring

/-- The paper's first example (Section 1): `x^10 + x^7 + x^6 + x^5 + x^3 + x + 2` factors as
`(x + 1)^2 (x^2 + 1) (x^6 - 2x^5 + 2x^4 - x^3 + 2x^2 - 3x + 2)`. -/
example : filasetaPoly 2 {1, 3, 5, 6, 7, 10} =
    (X + 1) ^ 2 * (X ^ 2 + 1) *
      (X ^ 6 - 2 * X ^ 5 + 2 * X ^ 4 - X ^ 3 + 2 * X ^ 2 - 3 * X + C 2) := by
  simp only [filasetaPoly, Finset.mem_insert, OfNat.one_ne_ofNat, Finset.mem_singleton, or_self,
    not_false_eq_true, Finset.sum_insert, pow_one, Nat.reduceEqDiff, Finset.sum_singleton,
    Nat.cast_ofNat, eq_intCast, Int.cast_ofNat]
  ring

example : ZeroOneShape 2 (X ^ 3 + X + C 2 : ℤ[X]) := by
  refine ⟨by simp, fun j hj => ?_⟩
  simp only [coeff_add, coeff_X_pow, coeff_X, coeff_C, hj, if_false, add_zero]
  by_cases h3 : j = 3 <;> by_cases h1 : j = 1 <;> simp_all [eq_comm]

/-- Evaluation at `1` is invariant under `Polynomial.mirror`. -/
theorem eval_one_mirror (q : ℤ[X]) : q.mirror.eval 1 = q.eval 1 := by
  letI : Invertible (1 : ℤ) := invertibleOne
  have h := eval₂_reverse_mul_pow (RingHom.id ℤ) (1 : ℤ) q
  simp only [invOf_one, one_pow, mul_one] at h
  rw [mirror, eval_mul, eval_pow, eval_X, one_pow, mul_one]
  exact h

/-- For a 0/1-shape polynomial with constant `p`, `∑ (c_j^2 - c_j) = p^2 - p`. -/
theorem sum_sq_sub_of_shape (p : ℤ) (G : ℤ[X]) (hG : ZeroOneShape p G) (N : ℕ)
    (hN : G.natDegree < N) :
    ∑ j ∈ Finset.range N, (G.coeff j ^ 2 - G.coeff j) = p ^ 2 - p := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [Finset.sum_range_succ', hG.1]
  have hzero : ∑ i ∈ Finset.range M, (G.coeff (i + 1) ^ 2 - G.coeff (i + 1)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rcases hG.2 (i + 1) (Nat.succ_ne_zero i) with h | h <;> rw [h] <;> norm_num
  rw [hzero, zero_add]

/-- A nonzero integer polynomial whose coefficients all lie in `{-1, 0, 1}` has trailing
coefficient of absolute value `1`. -/
theorem natAbs_trailingCoeff_eq_one (A : ℤ[X]) (hA : A ≠ 0)
    (hc : ∀ j, (A.coeff j).natAbs ≤ 1) : A.trailingCoeff.natAbs = 1 := by
  have hne : A.trailingCoeff ≠ 0 := trailingCoeff_nonzero_iff_nonzero.mpr hA
  have hle := hc A.natTrailingDegree
  have hpos : 0 < A.trailingCoeff.natAbs := Int.natAbs_pos.mpr hne
  unfold trailingCoeff at hpos ⊢
  omega

/-- If an integer `c` is a nonzero multiple of `p > 1`, then `c^2 - c ≥ p^2 - p`, with equality
only for `c = p`. -/
theorem sq_sub_ge_of_dvd (p c : ℤ) (hp : 1 < p) (hc : c ≠ 0) (hpc : p ∣ c) :
    p ^ 2 - p ≤ c ^ 2 - c ∧ (c ^ 2 - c = p ^ 2 - p → c = p) := by
  have habs : p ≤ |c| := Int.le_of_dvd (abs_pos.mpr hc) ((dvd_abs p c).mpr hpc)
  rcases le_or_gt 0 c with h0 | h0
  · rw [abs_of_nonneg h0] at habs
    refine ⟨by nlinarith, fun h => ?_⟩
    have hfac : (c - p) * (c + p - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hfac with h1 | h1 <;> [linarith; linarith]
  · rw [abs_of_neg h0] at habs
    refine ⟨by nlinarith, fun h => ?_⟩
    nlinarith

/-- **Lemma 2.2 (shape of `W`).** Let `F` have 0/1-shape with constant `p > 1`, and let `W` have
the same degree, a nonzero constant term divisible by `p`, `W · W̃ = F · F̃` and `W(1) = F(1)`.
Then `W` also has 0/1-shape with constant `p`. -/
theorem zeroOneShape_of_mul_mirror (p : ℤ) (hp : 1 < p) (F W : ℤ[X]) (hF : ZeroOneShape p F)
    (hdeg : W.natDegree = F.natDegree) (hW0 : W.coeff 0 ≠ 0) (hpW : p ∣ W.coeff 0)
    (hsq : W * W.mirror = F * F.mirror) (h1 : W.eval 1 = F.eval 1) : ZeroOneShape p W := by
  set N := F.natDegree + 1 with hNdef
  have hF0 : F.coeff 0 ≠ 0 := by rw [hF.1]; omega
  have hWt : W.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (.inr hW0)
  have hFt : F.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (.inr hF0)
  have hWN : W.natDegree < N := by omega
  have hFN : F.natDegree < N := by omega
  -- sum of squares of the coefficients agree (middle coefficient of `W W̃ = F F̃`)
  have hsumsq : ∑ j ∈ Finset.range N, W.coeff j ^ 2 = ∑ j ∈ Finset.range N, F.coeff j ^ 2 := by
    have hW := coeff_mul_mirror W
    have hF' := coeff_mul_mirror F
    rw [hWt, hdeg, hsq, ← hFt, hF', sum_over_range' W (f := fun _ a => a ^ 2) (fun _ => zero_pow two_ne_zero) N hWN,
      sum_over_range' F (f := fun _ a => a ^ 2) (fun _ => zero_pow two_ne_zero) N hFN] at hW
    exact hW.symm
  -- sums of the coefficients agree (`W(1) = F(1)`)
  have hsum : ∑ j ∈ Finset.range N, W.coeff j = ∑ j ∈ Finset.range N, F.coeff j := by
    rw [eval_eq_sum_range' hWN, eval_eq_sum_range' hFN] at h1
    simpa only [one_pow, mul_one] using h1
  have htot : ∑ j ∈ Finset.range N, (W.coeff j ^ 2 - W.coeff j) = p ^ 2 - p := by
    rw [Finset.sum_sub_distrib, hsumsq, hsum, ← Finset.sum_sub_distrib]
    exact sum_sq_sub_of_shape p F hF N hFN
  rw [hNdef, Finset.sum_range_succ'] at htot
  have hnonneg : ∀ i ∈ Finset.range F.natDegree,
      0 ≤ W.coeff (i + 1) ^ 2 - W.coeff (i + 1) := fun i _ => by
    nlinarith [sq_nonneg (2 * W.coeff (i + 1) - 1)]
  have hrest := Finset.sum_nonneg hnonneg
  obtain ⟨hge, heq⟩ := sq_sub_ge_of_dvd p (W.coeff 0) hp hW0 hpW
  have hrest0 : ∑ i ∈ Finset.range F.natDegree, (W.coeff (i + 1) ^ 2 - W.coeff (i + 1)) = 0 := by
    linarith
  refine ⟨heq (by linarith), fun j hj => ?_⟩
  rcases le_or_gt j F.natDegree with hjle | hjgt
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hi : i ∈ Finset.range F.natDegree := Finset.mem_range.mpr (by omega)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hrest0 i hi
    have hfac : W.coeff (i + 1) * (W.coeff (i + 1) - 1) = 0 := by linear_combination hz
    rcases mul_eq_zero.mp hfac with h | h
    · exact .inl h
    · exact .inr (by linarith)
  · exact .inl (coeff_eq_zero_of_natDegree_lt (by omega))

/-- Two 0/1-shape polynomials with the same constant `p` differ coefficientwise by at most `1`. -/
theorem natAbs_coeff_sub_le_one (p : ℤ) (F W : ℤ[X]) (hF : ZeroOneShape p F)
    (hW : ZeroOneShape p W) (j : ℕ) : ((W - F).coeff j).natAbs ≤ 1 := by
  rw [coeff_sub]
  rcases eq_or_ne j 0 with rfl | hj
  · rw [hW.1, hF.1, sub_self]; simp
  · rcases hW.2 j hj with h | h <;> rcases hF.2 j hj with h' | h' <;> rw [h, h'] <;> decide

/-- **Borisov's argument (proof of Theorem 1.1).** Two 0/1-shape polynomials `F`, `W` with the
same constant `p > 1`, the same degree and `W · W̃ = F · F̃` are equal: otherwise the lowest
coefficients of the two sides of `F (W̃ - F̃) = (F - W) W̃` are `±p` and `±1`. -/
theorem eq_of_zeroOneShape_of_mul_mirror (p : ℤ) (hp : 1 < p) (F W : ℤ[X])
    (hF : ZeroOneShape p F) (hW : ZeroOneShape p W) (hdeg : W.natDegree = F.natDegree)
    (hsq : W * W.mirror = F * F.mirror) : W = F := by
  by_contra hne
  have hF0 : F.coeff 0 ≠ 0 := by rw [hF.1]; omega
  have hW0 : W.coeff 0 ≠ 0 := by rw [hW.1]; omega
  have hWt : W.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (.inr hW0)
  have hFt : F.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (.inr hF0)
  -- the degree is positive, since a degree-zero `W` would equal `F`
  have hn : F.natDegree ≠ 0 := by
    intro hn0
    apply hne
    ext j
    rcases eq_or_ne j 0 with rfl | hj
    · rw [hW.1, hF.1]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]
  have hkey : F * (W.mirror - F.mirror) = (F - W) * W.mirror := by linear_combination hsq
  set A := W.mirror - F.mirror with hA
  have hAne : A ≠ 0 := by
    intro h0
    apply hne
    rw [← W.mirror_mirror, ← F.mirror_mirror, sub_eq_zero.mp h0]
  have hBne : F - W ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hAc : ∀ j, (A.coeff j).natAbs ≤ 1 := fun j => by
    rw [hA, coeff_sub, coeff_mirror, coeff_mirror, hWt, hFt, hdeg, ← coeff_sub]
    exact natAbs_coeff_sub_le_one p F W hF hW _
  have hBc : ∀ j, ((F - W).coeff j).natAbs ≤ 1 := fun j => by
    rw [← neg_sub, coeff_neg, Int.natAbs_neg]
    exact natAbs_coeff_sub_le_one p F W hF hW j
  have htr := congrArg (fun G => G.trailingCoeff.natAbs) hkey
  simp only [trailingCoeff_mul, mirror_trailingCoeff, Int.natAbs_mul,
    natAbs_trailingCoeff_eq_one A hAne hAc,
    natAbs_trailingCoeff_eq_one (F - W) hBne hBc, trailingCoeff_eq_coeff_zero hF0, hF.1,
    mul_one, one_mul] at htr
  -- the leading coefficient of `W` is `0` or `1`, but has absolute value `p > 1`
  have hlead : W.leadingCoeff = 0 ∨ W.leadingCoeff = 1 := hW.2 _ (by rw [hdeg]; exact hn)
  rcases hlead with h | h <;> rw [h] at htr <;> omega

/-- **Core of Theorem 1.1.** If a 0/1-shape polynomial `F` with constant `p > 1` factors as
`F = u * v` with `p ∣ u(0)`, then `v` is self-reciprocal: `ṽ = v`. -/
theorem mirror_eq_of_mul_eq (p : ℤ) (hp : 1 < p) (F u v : ℤ[X]) (hF : ZeroOneShape p F)
    (h : F = u * v) (hu : p ∣ u.coeff 0) : v.mirror = v := by
  have hF0 : F.coeff 0 ≠ 0 := by rw [hF.1]; omega
  have hmul0 : F.coeff 0 = u.coeff 0 * v.coeff 0 := by rw [h, mul_coeff_zero]
  have hu0 : u.coeff 0 ≠ 0 := fun h0 => hF0 (by rw [hmul0, h0, zero_mul])
  have hv0 : v.coeff 0 ≠ 0 := fun h0 => hF0 (by rw [hmul0, h0, mul_zero])
  have hune : u ≠ 0 := fun h0 => hu0 (by rw [h0, coeff_zero])
  have hvne : v ≠ 0 := fun h0 => hv0 (by rw [h0, coeff_zero])
  have hvt : v.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (.inr hv0)
  -- the auxiliary polynomial `W = u ṽ` of (2.1)
  set W := u * v.mirror with hWdef
  have hmv0 : v.mirror.coeff 0 = v.leadingCoeff := by
    rw [← mirror_trailingCoeff, trailingCoeff, mirror_natTrailingDegree, hvt]
  have hW0 : W.coeff 0 = u.coeff 0 * v.leadingCoeff := by rw [hWdef, mul_coeff_zero, hmv0]
  have hW0ne : W.coeff 0 ≠ 0 := by
    rw [hW0]; exact mul_ne_zero hu0 (leadingCoeff_ne_zero.mpr hvne)
  have hpW : p ∣ W.coeff 0 := by rw [hW0]; exact Dvd.dvd.mul_right hu _
  have hdeg : W.natDegree = F.natDegree := by
    rw [hWdef, h, natDegree_mul hune (mirror_eq_zero.not.mpr hvne), mirror_natDegree,
      natDegree_mul hune hvne]
  have hsq : W * W.mirror = F * F.mirror := by
    rw [hWdef, h, mirror_mul_of_domain, mirror_mul_of_domain, mirror_mirror]
    ring
  have h1 : W.eval 1 = F.eval 1 := by
    rw [hWdef, h, eval_mul, eval_mul, eval_one_mirror]
  have hWshape := zeroOneShape_of_mul_mirror p hp F W hF hdeg hW0ne hpW hsq h1
  have hWF := eq_of_zeroOneShape_of_mul_mirror p hp F W hF hWshape hdeg hsq
  rw [hWdef, h] at hWF
  exact mul_left_cancel₀ hune hWF

/-- For a polynomial with nonzero constant term, `Polynomial.mirror` agrees with
`Polynomial.reverse` (the paper's reciprocal `w̃(x) = x^{deg w} w(1/x)`). -/
theorem mirror_eq_reverse_of_coeff_zero_ne_zero (q : ℤ[X]) (hq : q.coeff 0 ≠ 0) :
    q.mirror = q.reverse := by
  rw [mirror, natTrailingDegree_eq_zero.mpr (.inr hq), pow_zero, mul_one]

/-- The constant term of `F(x)` is `p`. -/
theorem coeff_zero_filasetaPoly (p : ℕ) (D : Finset ℕ) (hD0 : 0 ∉ D) :
    (filasetaPoly p D).coeff 0 = p :=
  (zeroOneShape_filasetaPoly p D hD0).1

/-- In any factorization `F = u * v`, exactly the factor with constant term not divisible by `p`
is self-reciprocal: if `p ∤ w(0)` and `w ∣ F`, then `w̃ = w`. -/
theorem reverse_eq_of_dvd (p : ℕ) (hp : p.Prime) (D : Finset ℕ) (hD0 : 0 ∉ D) (w : ℤ[X])
    (hw : w ∣ filasetaPoly p D) (hpw : ¬ (p : ℤ) ∣ w.coeff 0) : w.reverse = w := by
  obtain ⟨c, hc⟩ := hw
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp1 : (1 : ℤ) < p := by exact_mod_cast hp.one_lt
  have hshape := zeroOneShape_filasetaPoly p D hD0
  have h0 : w.coeff 0 * c.coeff 0 = p := by rw [← mul_coeff_zero, ← hc, hshape.1]
  have hw0 : w.coeff 0 ≠ 0 := by
    intro hz; rw [hz, zero_mul] at h0; omega
  have hpc : (p : ℤ) ∣ c.coeff 0 :=
    (hpZ.dvd_or_dvd (dvd_of_eq h0.symm)).resolve_left hpw
  have hm := mirror_eq_of_mul_eq (p : ℤ) hp1 _ c w hshape (by rw [hc, mul_comm]) hpc
  rw [← mirror_eq_reverse_of_coeff_zero_ne_zero w hw0, hm]

/-- **Core form of Theorem 1.1.** If `F(x) = x^{d_r} + ⋯ + x^{d_1} + p` (`p` prime, all
`d_j ≥ 1`) factors as `F = u v` in `ℤ[x]`, then `u` or `v` is self-reciprocal (`w̃ = w`, with
`w̃(x) = x^{deg w} w(1/x)` the paper's reciprocal). -/
theorem reverse_eq_or_reverse_eq_of_eq_mul (p : ℕ) (hp : p.Prime) (D : Finset ℕ) (hD0 : 0 ∉ D)
    (u v : ℤ[X]) (h : filasetaPoly p D = u * v) : u.reverse = u ∨ v.reverse = v := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h0 : u.coeff 0 * v.coeff 0 = p := by
    rw [← mul_coeff_zero, ← h, coeff_zero_filasetaPoly p D hD0]
  by_cases hpu : (p : ℤ) ∣ u.coeff 0
  · have hpv : ¬ (p : ℤ) ∣ v.coeff 0 := by
      rintro ⟨b, hb⟩
      obtain ⟨a, ha⟩ := hpu
      have hab : (p : ℤ) * (p * (a * b)) = p * 1 := by
        linear_combination h0 - v.coeff 0 * ha - (p : ℤ) * a * hb
      have hab' := mul_left_cancel₀ hpZ.ne_zero hab
      exact hpZ.not_unit (isUnit_iff_exists_inv.mpr ⟨_, hab'⟩)
    exact .inr (reverse_eq_of_dvd p hp D hD0 v ⟨u, by rw [h, mul_comm]⟩ hpv)
  · exact .inl (reverse_eq_of_dvd p hp D hD0 u ⟨v, h⟩ hpu)

/-- **No non-reciprocal splitting (paper's notion).** `F(x) = x^{d_r} + ⋯ + x^{d_1} + p` has no
factorization `F = u v` in `ℤ[x]` with both `u` and `v` non-reciprocal, i.e. `ũ ≠ ±u` and
`ṽ ≠ ±v`. This is the statement that, combined with Lemma 2.1 (Filaseta–Solan), gives
Theorem 1.1 of arXiv:2610.05568. -/
theorem not_nonreciprocal_split (p : ℕ) (hp : p.Prime) (D : Finset ℕ) (hD0 : 0 ∉ D)
    (u v : ℤ[X]) (hF : filasetaPoly p D = u * v)
    (hu : u.reverse ≠ u ∧ u.reverse ≠ -u) (hv : v.reverse ≠ v ∧ v.reverse ≠ -v) : False := by
  rcases reverse_eq_or_reverse_eq_of_eq_mul p hp D hD0 u v hF with h | h
  · exact hu.1 h
  · exact hv.1 h

/-- **No non-reciprocal splitting (`Polynomial.mirror` form).** The triage's formal sketch:
`F` has no factorization `F = u v` with `ũ ≠ ±u` and `ṽ ≠ ±v`, reciprocals taken via
`Polynomial.mirror`. -/
theorem no_nonreciprocal_split (p : ℕ) (hp : p.Prime) (D : Finset ℕ) (hD0 : 0 ∉ D)
    (u v : ℤ[X]) (hF : (∑ d ∈ D, (X : ℤ[X]) ^ d) + C (p : ℤ) = u * v)
    (hu : u.mirror ≠ u ∧ u.mirror ≠ -u) (hv : v.mirror ≠ v ∧ v.mirror ≠ -v) : False := by
  have h0 : u.coeff 0 * v.coeff 0 = p := by
    rw [← mul_coeff_zero, ← hF]
    exact coeff_zero_filasetaPoly p D hD0
  have hu0 : u.coeff 0 ≠ 0 := by
    intro hz; rw [hz, zero_mul] at h0; have := hp.pos; omega
  have hv0 : v.coeff 0 ≠ 0 := by
    intro hz; rw [hz, mul_zero] at h0; have := hp.pos; omega
  rw [mirror_eq_reverse_of_coeff_zero_ne_zero u hu0] at hu
  rw [mirror_eq_reverse_of_coeff_zero_ne_zero v hv0] at hv
  exact not_nonreciprocal_split p hp D hD0 u v hF hu hv

/-- If `p` is prime and `p ∣ G(0)`, then some irreducible factor `w` of `G` in `ℤ[x]` has
`p ∣ w(0)`. -/
theorem exists_irreducible_dvd_coeff_zero (p : ℤ) (hp : Prime p) (G : ℤ[X])
    (hG : p ∣ G.coeff 0) : ∃ w : ℤ[X], Irreducible w ∧ w ∣ G ∧ p ∣ w.coeff 0 := by
  induction G using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact ⟨X, irreducible_X, dvd_zero X, by rw [coeff_X_zero]; exact dvd_zero p⟩
  | h₂ x hx =>
    exfalso
    obtain ⟨r, hr, rfl⟩ := Polynomial.isUnit_iff.mp hx
    rw [coeff_C_zero] at hG
    exact hp.not_unit (isUnit_of_dvd_unit hG hr)
  | h₃ a q _ hq ih =>
    rw [mul_coeff_zero] at hG
    rcases hp.dvd_or_dvd hG with hq0 | ha0
    · exact ⟨q, hq.irreducible, dvd_mul_right q a, hq0⟩
    · obtain ⟨w, hw, hwa, hw0⟩ := ih ha0
      exact ⟨w, hw, hwa.trans (dvd_mul_left a q), hw0⟩

/-- For nonempty `D` (i.e. `r ≥ 1`) with `0 ∉ D`, `F(x)` has leading coefficient `1`. -/
theorem leadingCoeff_filasetaPoly (p : ℕ) (D : Finset ℕ) (hD0 : 0 ∉ D) (hD : D.Nonempty) :
    (filasetaPoly p D).leadingCoeff = 1 := by
  have hshape := zeroOneShape_filasetaPoly p D hD0
  obtain ⟨d, hd⟩ := hD
  have hd0 : d ≠ 0 := fun h => hD0 (h ▸ hd)
  have hcd : (filasetaPoly p D).coeff d ≠ 0 := by
    rw [coeff_filasetaPoly]; simp [hd, hd0]
  have hdeg : (filasetaPoly p D).natDegree ≠ 0 := by
    have := le_natDegree_of_ne_zero hcd; omega
  have hne : (filasetaPoly p D) ≠ 0 := fun h => hcd (by rw [h, coeff_zero])
  rcases hshape.2 _ hdeg with h | h
  · exact absurd h (leadingCoeff_ne_zero.mpr hne)
  · exact h

/-- **Theorem 1.1 of arXiv:2610.05568 (Filaseta–Martirosyan–Swan).** Let `p` be prime and
`F(x) = x^{d_r} + ⋯ + x^{d_1} + p` with `r ≥ 1` and all `d_j ≥ 1`. Then the non-reciprocal part
of `F` is irreducible.

The non-reciprocal part is `F` with all its irreducible reciprocal factors removed; by unique
factorization in `ℤ[x]` it is characterized (up to sign) as the cofactor `N` in a
factorization `F = R * N` in which every irreducible factor of `R` is reciprocal (`q̃ = ±q`)
and no irreducible factor of `N` is reciprocal. Here `q̃ = q.reverse = x^{deg q} q(1/x)`. -/
theorem thm_1_1 (p : ℕ) (hp : p.Prime) (D : Finset ℕ) (hD0 : 0 ∉ D) (hD : D.Nonempty)
    (R N : ℤ[X]) (hRN : filasetaPoly p D = R * N)
    (hR : ∀ q : ℤ[X], Irreducible q → q ∣ R → q.reverse = q ∨ q.reverse = -q)
    (hN : ∀ q : ℤ[X], Irreducible q → q ∣ N → q.reverse ≠ q ∧ q.reverse ≠ -q) :
    Irreducible N := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp1 : (1 : ℤ) < p := by exact_mod_cast hp.one_lt
  have hF0 := coeff_zero_filasetaPoly p D hD0
  have hFne : filasetaPoly p D ≠ 0 := fun h => by rw [h, coeff_zero] at hF0; omega
  have hNne : N ≠ 0 := fun h => hFne (by rw [hRN, h, mul_zero])
  refine ⟨fun hNu => ?_, fun a b hab => ?_⟩
  · -- `N` is not a unit: an irreducible factor `w` with `p ∣ w(0)` would be reciprocal and
    -- divide the monic `F`, forcing `p ∣ lc(w) ∣ 1`.
    obtain ⟨w, hw, hwF, hw0⟩ :=
      exists_irreducible_dvd_coeff_zero (p : ℤ) hpZ _ (by rw [hF0])
    have hwR : w ∣ R := by
      rw [hRN] at hwF
      exact (IsUnit.dvd_mul_right hNu).mp hwF
    have hlead : (p : ℤ) ∣ w.leadingCoeff := by
      rw [← coeff_zero_reverse]
      rcases hR w hw hwR with h | h <;> rw [h]
      · exact hw0
      · rw [coeff_neg]; exact (dvd_neg).mpr hw0
    obtain ⟨c, hc⟩ := hwF
    have hlc : w.leadingCoeff * c.leadingCoeff = 1 := by
      rw [← leadingCoeff_mul, ← hc, leadingCoeff_filasetaPoly p D hD0 hD]
    exact hpZ.not_unit (isUnit_of_dvd_unit hlead (isUnit_iff_exists_inv.mpr ⟨_, hlc⟩))
  · -- a splitting `N = a b` into non-units yields a self-reciprocal irreducible factor of `N`
    by_contra hnot
    push Not at hnot
    obtain ⟨hau, hbu⟩ := hnot
    have h0 : R.coeff 0 * (a.coeff 0 * b.coeff 0) = p := by
      rw [← mul_coeff_zero, ← mul_coeff_zero, ← hab, ← hRN, hF0]
    -- one of `a(0)`, `b(0)` is prime to `p`
    have hex : ∃ x : ℤ[X], x ∣ N ∧ ¬ IsUnit x ∧ ¬ (p : ℤ) ∣ x.coeff 0 := by
      by_cases hpa : (p : ℤ) ∣ a.coeff 0
      · refine ⟨b, ⟨a, by rw [hab, mul_comm]⟩, hbu, fun hpb => ?_⟩
        obtain ⟨s, hs⟩ := hpa
        obtain ⟨t, ht⟩ := hpb
        have hst : (p : ℤ) * (p * (R.coeff 0 * s * t)) = p * 1 := by
          linear_combination h0 - R.coeff 0 * b.coeff 0 * hs - R.coeff 0 * (p : ℤ) * s * ht
        exact hpZ.not_unit
          (isUnit_iff_exists_inv.mpr ⟨_, mul_left_cancel₀ hpZ.ne_zero hst⟩)
      · exact ⟨a, ⟨b, hab⟩, hau, hpa⟩
    obtain ⟨x, hxN, hxu, hpx⟩ := hex
    have hxne : x ≠ 0 := fun h => hNne (zero_dvd_iff.mp (h ▸ hxN))
    obtain ⟨w, hw, hwx⟩ := WfDvdMonoid.exists_irreducible_factor hxu hxne
    have hpw : ¬ (p : ℤ) ∣ w.coeff 0 := by
      obtain ⟨e, he⟩ := hwx
      intro hdiv
      apply hpx
      rw [he, mul_coeff_zero]
      exact Dvd.dvd.mul_right hdiv _
    have hwN : w ∣ N := hwx.trans hxN
    have hwF : w ∣ filasetaPoly p D := by rw [hRN]; exact hwN.trans (dvd_mul_left N R)
    exact (hN w hw hwN).1 (reverse_eq_of_dvd p hp D hD0 w hwF hpw)

/-- Associated polynomials in `ℤ[x]` differ by a sign. -/
theorem eq_or_eq_neg_of_associated (q r : ℤ[X]) (h : Associated q r) : r = q ∨ r = -q := by
  obtain ⟨e, rfl⟩ := h
  obtain ⟨c, hc, hce⟩ := Polynomial.isUnit_iff.mp e.isUnit
  rw [← hce]
  rcases Int.isUnit_iff.mp hc with rfl | rfl
  · exact .inl (by rw [C_1, mul_one])
  · exact .inr (by rw [C_neg, C_1, mul_neg_one])

/-- Being reciprocal (`q̃ = ±q`) is invariant under association in `ℤ[x]`. -/
theorem reciprocal_iff_of_associated (q r : ℤ[X]) (h : Associated q r) :
    (q.reverse = q ∨ q.reverse = -q) ↔ (r.reverse = r ∨ r.reverse = -r) := by
  rcases eq_or_eq_neg_of_associated q r h with rfl | rfl
  · exact Iff.rfl
  · rw [reverse_neg, neg_inj, neg_eq_iff_eq_neg, neg_neg, or_comm]

/-- **Existence of the non-reciprocal part.** Every nonzero `f ∈ ℤ[x]` factors as `f = R * N`
where every irreducible factor of `R` is reciprocal and no irreducible factor of `N` is
reciprocal. This shows the hypotheses of `thm_1_1` are satisfiable for every `F`. -/
theorem exists_reciprocal_mul_nonreciprocal (f : ℤ[X]) (hf : f ≠ 0) :
    ∃ R N : ℤ[X], f = R * N ∧
      (∀ q : ℤ[X], Irreducible q → q ∣ R → q.reverse = q ∨ q.reverse = -q) ∧
      (∀ q : ℤ[X], Irreducible q → q ∣ N → q.reverse ≠ q ∧ q.reverse ≠ -q) := by
  classical
  let P : ℤ[X] → Prop := fun q => q.reverse = q ∨ q.reverse = -q
  let S := UniqueFactorizationMonoid.normalizedFactors f
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.prod_normalizedFactors hf
  refine ⟨(S.filter P).prod, (S.filter fun a => ¬ P a).prod * u, ?_, ?_, ?_⟩
  · rw [← mul_assoc, Multiset.prod_filter_mul_prod_filter_not, hu]
  · intro q hq hqR
    obtain ⟨r, hrS, hqr⟩ :=
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hq).exists_mem_multiset_dvd hqR
    obtain ⟨hrS', hPr⟩ := Multiset.mem_filter.mp hrS
    have hr := UniqueFactorizationMonoid.irreducible_of_normalized_factor r hrS'
    exact (reciprocal_iff_of_associated q r (hq.associated_of_dvd hr hqr)).mpr hPr
  · intro q hq hqN
    have hqN' : q ∣ (S.filter fun a => ¬ P a).prod := (Units.dvd_mul_right).mp hqN
    obtain ⟨r, hrS, hqr⟩ :=
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hq).exists_mem_multiset_dvd hqN'
    obtain ⟨hrS', hPr⟩ := Multiset.mem_filter.mp hrS
    have hr := UniqueFactorizationMonoid.irreducible_of_normalized_factor r hrS'
    have hnq : ¬ P q := fun hPq =>
      hPr ((reciprocal_iff_of_associated q r (hq.associated_of_dvd hr hqr)).mp hPq)
    exact not_or.mp hnq

/-- Non-vacuity of `thm_1_1`: for `F = x + 2` the hypotheses are jointly satisfiable, so the
theorem yields an irreducible non-reciprocal part. -/
example : ∃ R N : ℤ[X], filasetaPoly 2 {1} = R * N ∧ Irreducible N := by
  have hne : filasetaPoly 2 {1} ≠ 0 := by
    intro h
    have := congrArg (fun G => G.coeff 0) h
    simp only [coeff_zero] at this
    rw [coeff_zero_filasetaPoly 2 {1} (by decide)] at this
    norm_num at this
  obtain ⟨R, N, hRN, hR, hN⟩ := exists_reciprocal_mul_nonreciprocal _ hne
  exact ⟨R, N, hRN, thm_1_1 2 Nat.prime_two {1} (by decide) ⟨1, by simp⟩ R N hRN hR hN⟩

end Candidates.FilasetaNonreciprocal
