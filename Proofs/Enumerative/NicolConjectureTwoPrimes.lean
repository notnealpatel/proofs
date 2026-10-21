/-
# Nicol's conjecture for `n = l p`, `m = l q` (primes `l < q < p`)

## Source

* M. Filaseta, L. Martirosyan, L. C. Swan, *On the factorization of
  `x^{d_r} + ⋯ + x^{d_1} + p` and a conjecture of C. Nicol*, arXiv:2610.05568.
* Where: Section 1, Conjecture 1.2 (Nicol), equation (1.2) (`introeq:ellpqeq`),
  the `t = 1` instance of the first assertion of Theorem 1.3 (`kpq:mainthm`), with
  the ingredients Theorem 1.1 (`factorizationthm`, Borisov's argument, Section 2)
  and Lemma 3.1 (`recipfactf(x)`).
* Status: proved in the paper (special case of the open Nicol conjecture).
* Date: 2026-10-21.

## Informal claim (verbatim from the source)

Conjecture 1.2 (Nicol): "If `n` and `m` are integers exceeding `1`, then the
non-cyclotomic part of the polynomial `Φ_n(x) + Φ_m(x)` is either `2` or
irreducible in `ℚ[x]`."

Section 1: "For primes `p`, `q` and `ℓ` satisfying `p > q > ℓ`, one can show that
`(Φ_{ℓp}(x) + Φ_{ℓq}(x)) Φ_ℓ(x) = Φ_ℓ(x^p) + Φ_ℓ(x^q) = Σ_{i=1}^{ℓ-1} x^{pi} +
Σ_{j=1}^{ℓ-1} x^{qj} + 2` ... Hence, in the case that `n = ℓp` and `m = ℓq` with
primes `p > q > ℓ`, the conclusion of Conjecture 1.2 follows."

## Formal reading

The non-cyclotomic part of the monic `f = Φ_{lp} + Φ_{lq} ∈ ℤ[X]` is irreducible
exactly when every factorisation `f = u * v` in `ℤ[X]` has a factor all of whose
complex roots are roots of unity (Gauss's lemma moves `ℚ[X]` factorisations to
`ℤ[X]`, and a factor containing a non-cyclotomic irreducible piece has a root that
is not a root of unity).  `nicol_lp_lq` states this `ℤ[X]` form;
`nicol_lp_lq_rat` states the same for factorisations in `ℚ[X]`.

## Proof route (self-contained; no appeal to Lemma 2.1 of the paper)

1. `cyclotomic_add_mul_eq_expand_add`: the identity (1.2), from Mathlib's
   `cyclotomic_expand_eq_cyclotomic_mul`.
2. `monic_coeff_expand_add`: `F = Φ_l(X^p) + Φ_l(X^q)` is monic with constant
   coefficient `2` and all other coefficients in `{0, 1}` (uses `l < q < p`).
3. `mirror_eq_of_mul_eq` (Ljunggren / Borisov, Section 2): if such an `F` factors
   as `F = U * V` with `V(0) = ±1`, then `V` is reciprocal (`V.mirror = V`).  The
   paper's `W = U Ṽ` comparison is carried out with Mathlib's `Polynomial.mirror`.
4. `exists_pow_eq_one_of_mirror_eq` (Lemma 3.1 analogue): every complex root of a
   reciprocal factor `V` of `F` with `V(0) ≠ 0` is a root of unity.
5. Since `f(0) = 2`, one of `u(0)`, `v(0)` is `±1`; apply 3 and 4 to that factor
   times `Φ_l`.

The proof shows slightly more than the claim: the factor with constant term `±1`
is the one whose roots are all roots of unity.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.NicolConjectureTwoPrimes

open Polynomial

/-! ## Ljunggren–Borisov step (Theorem 1.1, Section 2) -/

/-- **Borisov's argument (paper, Section 2).** Let `F ∈ ℤ[X]` be monic with constant
coefficient `2` and every other coefficient in `{0, 1}`.  If `F = U * V` with `V(0)`
a unit, then `V` is reciprocal: `V.mirror = V`.  The proof compares `F` with
`W = U * V.mirror`, which satisfies `W * W.mirror = F * F.mirror`. -/
theorem mirror_eq_of_mul_eq {F U V : ℤ[X]} (hF : F.Monic) (hF0 : F.coeff 0 = 2)
    (hF1 : ∀ k, k ≠ 0 → F.coeff k = 0 ∨ F.coeff k = 1) (hUV : F = U * V)
    (hV0 : IsUnit (V.coeff 0)) : V.mirror = V := by
  have hU : U ≠ 0 := by rintro rfl; rw [zero_mul] at hUV; exact hF.ne_zero hUV
  have hV : V ≠ 0 := by rintro rfl; rw [mul_zero] at hUV; exact hF.ne_zero hUV
  set W := U * V.mirror with hWdef
  have hmir : W * W.mirror = F * F.mirror := by
    rw [hWdef, hUV, mirror_mul_of_domain, mirror_mul_of_domain, mirror_mirror]
    ring
  have hV0' : V.coeff 0 = 1 ∨ V.coeff 0 = -1 := Int.isUnit_iff.mp hV0
  have hVntd : V.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (Or.inr hV0.ne_zero)
  have hVmc0 : V.mirror.coeff 0 = V.leadingCoeff := by
    rw [mirror, hVntd, pow_zero, mul_one, coeff_zero_reverse]
  have hlead : U.leadingCoeff * V.leadingCoeff = 1 := by
    rw [← leadingCoeff_mul, ← hUV]; exact hF
  have hVlead : V.leadingCoeff = 1 ∨ V.leadingCoeff = -1 :=
    Int.isUnit_iff.mp (IsUnit.of_mul_eq_one_right _ hlead)
  have hUlead : U.leadingCoeff = 1 ∨ U.leadingCoeff = -1 :=
    Int.isUnit_iff.mp (IsUnit.of_mul_eq_one _ hlead)
  have hUV0 : U.coeff 0 * V.coeff 0 = 2 := by rw [← mul_coeff_zero, ← hUV, hF0]
  have hW0 : W.coeff 0 = 2 ∨ W.coeff 0 = -2 := by
    rw [hWdef, mul_coeff_zero, hVmc0]
    rcases hV0' with h | h <;> rcases hVlead with h' | h' <;> rw [h] at hUV0 <;> rw [h'] <;>
      omega
  have hWlead : W.leadingCoeff = 1 ∨ W.leadingCoeff = -1 := by
    have htc : V.trailingCoeff = V.coeff 0 := by rw [trailingCoeff, hVntd]
    rw [hWdef, leadingCoeff_mul, mirror_leadingCoeff, htc]
    rcases hV0' with h | h <;> rcases hUlead with h' | h' <;> rw [h, h'] <;> norm_num
  have hW_ne : W ≠ 0 := by intro h; rw [h, coeff_zero] at hW0; omega
  have hWntd : W.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (Or.inr (by omega))
  have hFntd : F.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (Or.inr (by omega))
  have hdeg : W.natDegree = F.natDegree := by
    have h := congrArg natDegree hmir
    rw [natDegree_mul_mirror, natDegree_mul_mirror] at h
    omega
  have hsq : (W.sum fun _ a => a ^ 2) = F.sum fun _ a => a ^ 2 := by
    rw [← coeff_mul_mirror, ← coeff_mul_mirror, hmir, hdeg, hWntd, hFntd]
  have hone : W.eval 1 = F.eval 1 := by
    rw [hWdef, hUV, eval_mul, eval_mul, mirror_eval_one]
  have hrange : ∑ i ∈ Finset.range (F.natDegree + 1), (W.coeff i ^ 2 - W.coeff i) =
      ∑ i ∈ Finset.range (F.natDegree + 1), (F.coeff i ^ 2 - F.coeff i) := by
    have h1 := hsq
    rw [sum_over_range W (fun _ => by ring), sum_over_range F (fun _ => by ring)] at h1
    have h2 := hone
    rw [eval_eq_sum_range, eval_eq_sum_range] at h2
    simp only [one_pow, mul_one] at h2
    rw [hdeg] at h1 h2
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, h1, h2]
  have hFsum : ∑ i ∈ Finset.range (F.natDegree + 1), (F.coeff i ^ 2 - F.coeff i) = 2 := by
    rw [Finset.sum_range_succ', hF0, Finset.sum_eq_zero]
    · norm_num
    intro i _
    rcases hF1 (i + 1) (Nat.succ_ne_zero i) with h | h <;> rw [h] <;> norm_num
  have hnonneg : ∀ i, 0 ≤ W.coeff i ^ 2 - W.coeff i := fun i => by
    rcases le_or_gt (W.coeff i) 0 with h | h <;> nlinarith
  rw [hFsum, Finset.sum_range_succ'] at hrange
  have hg0 : 2 ≤ W.coeff 0 ^ 2 - W.coeff 0 := by
    rcases hW0 with h | h <;> rw [h] <;> norm_num
  have hrest0 := Finset.sum_nonneg (fun i (_ : i ∈ Finset.range F.natDegree) => hnonneg (i + 1))
  have hW02 : W.coeff 0 = 2 := by
    rcases hW0 with h | h
    · exact h
    · rw [h] at hrange; omega
  have hrest : ∑ i ∈ Finset.range F.natDegree, (W.coeff (i + 1) ^ 2 - W.coeff (i + 1)) = 0 := by
    linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg (i + 1))] at hrest
  have hW1 : ∀ k, k ≠ 0 → W.coeff k = 0 ∨ W.coeff k = 1 := by
    intro k hk
    by_cases hkD : k ≤ F.natDegree
    · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := Nat.exists_eq_succ_of_ne_zero hk
      have hi := hrest i (Finset.mem_range.mpr (by omega))
      have h' : W.coeff (i + 1) * (W.coeff (i + 1) - 1) = 0 := by linear_combination hi
      rcases mul_eq_zero.mp h' with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · exact Or.inl (coeff_eq_zero_of_natDegree_lt (by omega))
  have hFW : F = W := by
    by_contra hne
    have hsub : F - W ≠ 0 := sub_ne_zero.mpr hne
    have key : F * (W.mirror - F.mirror) = (F - W) * W.mirror := by linear_combination hmir
    have h1 := congrArg trailingCoeff key
    rw [trailingCoeff_mul, trailingCoeff_mul, mirror_trailingCoeff] at h1
    have hFtc : F.trailingCoeff = 2 := by rw [trailingCoeff, hFntd, hF0]
    have hsubtc : (F - W).trailingCoeff = 1 ∨ (F - W).trailingCoeff = -1 := by
      have hne0 : (F - W).trailingCoeff ≠ 0 := mt trailingCoeff_eq_zero.mp hsub
      rw [trailingCoeff, coeff_sub] at hne0 ⊢
      set k := (F - W).natTrailingDegree
      by_cases hk : k = 0
      · rw [hk, hF0, hW02] at hne0; omega
      · rcases hF1 k hk with h | h <;> rcases hW1 k hk with h' | h' <;> rw [h, h'] at hne0 ⊢ <;>
          omega
    rw [hFtc] at h1
    rcases hsubtc with h | h <;> rcases hWlead with h' | h' <;> rw [h, h'] at h1 <;> omega
  rw [hWdef] at hFW
  rw [hUV] at hFW
  exact (mul_left_cancel₀ hU hFW).symm


/-! ## The polynomial `F = Φ_l(X^p) + Φ_l(X^q)` -/

/-- Coefficients of `Φ_l` for a prime `l`: `1` below degree `l`, `0` from `l` on. -/
theorem coeff_cyclotomic_prime {l : ℕ} (hl : l.Prime) (k : ℕ) :
    (cyclotomic l ℤ).coeff k = if k < l then 1 else 0 := by
  haveI := Fact.mk hl
  rw [cyclotomic_prime, finsetSum_coeff]
  simp [coeff_X_pow]

/-- **Shape of `F` (paper, equation (1.2)).** For primes `l < q < p`, the polynomial
`F = Φ_l(X^p) + Φ_l(X^q)` is monic, has constant coefficient `2`, and every other
coefficient is `0` or `1` (the exponents `p i`, `q j`, `1 ≤ i, j < l`, are distinct). -/
theorem monic_coeff_expand_add {l q p : ℕ} (hl : l.Prime) (hq : q.Prime) (hp : p.Prime)
    (hlq : l < q) (hqp : q < p) :
    (expand ℤ p (cyclotomic l ℤ) + expand ℤ q (cyclotomic l ℤ)).Monic ∧
      (expand ℤ p (cyclotomic l ℤ) + expand ℤ q (cyclotomic l ℤ)).coeff 0 = 2 ∧
      ∀ k, k ≠ 0 → (expand ℤ p (cyclotomic l ℤ) + expand ℤ q (cyclotomic l ℤ)).coeff k = 0 ∨
        (expand ℤ p (cyclotomic l ℤ) + expand ℤ q (cyclotomic l ℤ)).coeff k = 1 := by
  have hc : ∀ (r : ℕ), 0 < r → ∀ k, (expand ℤ r (cyclotomic l ℤ)).coeff k =
      if r ∣ k ∧ k / r < l then 1 else 0 := by
    intro r hr k
    rw [coeff_expand hr, coeff_cyclotomic_prime hl]
    by_cases h1 : r ∣ k <;> by_cases h2 : k / r < l <;> simp [h1, h2]
  refine ⟨?_, ?_, ?_⟩
  · apply Monic.add_of_left (Monic.expand hp.pos (cyclotomic.monic l ℤ))
    apply degree_lt_degree
    rw [natDegree_expand, natDegree_expand, natDegree_cyclotomic, Nat.totient_prime hl]
    have hl2 := hl.two_le
    exact Nat.mul_lt_mul_of_pos_left hqp (by omega)
  · rw [coeff_add, hc p hp.pos, hc q hq.pos]
    simp [Nat.zero_div, hl.pos]
  · intro k hk
    rw [coeff_add, hc p hp.pos, hc q hq.pos]
    by_cases h1 : p ∣ k ∧ k / p < l
    · have h2 : ¬ (q ∣ k ∧ k / q < l) := by
        rintro ⟨hqk, -⟩
        obtain ⟨a, rfl⟩ := h1.1
        have hcop : Nat.Coprime q p := (Nat.coprime_primes hq hp).mpr (by omega)
        have hqa : q ∣ a := hcop.dvd_of_dvd_mul_left hqk
        have ha : a ≠ 0 := by rintro rfl; simp at hk
        have hqa' := Nat.le_of_dvd (Nat.pos_of_ne_zero ha) hqa
        have hal := h1.2
        rw [Nat.mul_div_cancel_left a hp.pos] at hal
        omega
      simp [h1, h2]
    · by_cases h2 : q ∣ k ∧ k / q < l <;> simp [h1, h2]

/-- **Identity (1.2) of the paper.** For a prime `l` and primes `p, q` different from
`l`, `(Φ_{lp} + Φ_{lq}) · Φ_l = Φ_l(X^p) + Φ_l(X^q)`. -/
theorem cyclotomic_add_mul_eq_expand_add {l q p : ℕ} (hl : l.Prime) (hq : q.Prime)
    (hp : p.Prime) (hlq : l ≠ q) (hlp : l ≠ p) :
    (cyclotomic (l * p) ℤ + cyclotomic (l * q) ℤ) * cyclotomic l ℤ =
      expand ℤ p (cyclotomic l ℤ) + expand ℤ q (cyclotomic l ℤ) := by
  have hpl : ¬ p ∣ l := fun h => hlp ((Nat.prime_dvd_prime_iff_eq hp hl).mp h).symm
  have hql : ¬ q ∣ l := fun h => hlq ((Nat.prime_dvd_prime_iff_eq hq hl).mp h).symm
  rw [cyclotomic_expand_eq_cyclotomic_mul hp hpl, cyclotomic_expand_eq_cyclotomic_mul hq hql,
    add_mul]

/-- Ground truth for (1.2) at `(l, q, p) = (3, 5, 7)`:
`Φ_3(X^7) + Φ_3(X^5) = X^14 + X^10 + X^7 + X^5 + 2`. -/
example : expand ℤ 7 (cyclotomic 3 ℤ) + expand ℤ 5 (cyclotomic 3 ℤ) =
    X ^ 14 + X ^ 10 + X ^ 7 + X ^ 5 + 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [cyclotomic_prime]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, map_add, map_zero, map_pow,
    expand_X, pow_zero, map_one, pow_one]
  ring

/-! ## Reciprocal factors of `F` (Lemma 3.1 analogue) -/

/-- Reversal of a geometric sum: `(Σ_{i<l} y⁻ⁱ) · y^(l-1) = Σ_{i<l} yⁱ` for `y ≠ 0`. -/
theorem geom_sum_inv_mul_pow (l : ℕ) {y : ℂ} (hy : y ≠ 0) :
    (∑ i ∈ Finset.range l, y⁻¹ ^ i) * y ^ (l - 1) = ∑ i ∈ Finset.range l, y ^ i := by
  rw [Finset.sum_mul, ← Finset.sum_range_reflect (fun i => y ^ i) l]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have hsplit : y ^ (l - 1) = y ^ (l - 1 - i) * y ^ i := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit, inv_pow]
  field_simp

/-- Evaluation of `F = Φ_l(X^p) + Φ_l(X^q)` at `z ∈ ℂ` for a prime `l`. -/
theorem aeval_expand_add (l p q : ℕ) (hl : l.Prime) (z : ℂ) :
    aeval z (expand ℤ p (cyclotomic l ℤ) + expand ℤ q (cyclotomic l ℤ)) =
      (∑ i ∈ Finset.range l, (z ^ p) ^ i) + ∑ i ∈ Finset.range l, (z ^ q) ^ i := by
  haveI := Fact.mk hl
  rw [map_add, expand_aeval, expand_aeval, cyclotomic_prime]
  simp

/-- **Lemma 3.1 analogue.** Let `l` be prime, `q < p`, and `F = Φ_l(X^p) + Φ_l(X^q)
= U * V` in `ℤ[X]` with `V(0) ≠ 0` and `V` reciprocal (`V.mirror = V`).  Then every
complex root `z` of `V` is a root of unity: `z ^ k = 1` for some `0 < k`.  (Both `z`
and `z⁻¹` are roots of `F`, which forces `Φ_l(z^p) = 0` or `z^((p-q)(l-1)) = 1`.) -/
theorem exists_pow_eq_one_of_mirror_eq {l q p : ℕ} (hl : l.Prime) (hqp : q < p) {U V : ℤ[X]}
    (hUV : expand ℤ p (cyclotomic l ℤ) + expand ℤ q (cyclotomic l ℤ) = U * V)
    (hV0 : V.coeff 0 ≠ 0) (hmir : V.mirror = V) {z : ℂ} (hz : aeval z V = 0) :
    ∃ k : ℕ, 0 < k ∧ z ^ k = 1 := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp only [aeval_def, eval₂_at_zero, eq_intCast, Int.cast_eq_zero] at hz
    exact hV0 hz
  have hrev : V.reverse = V := by
    have hntd : V.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (Or.inr hV0)
    have h := hmir
    rwa [mirror, hntd, pow_zero, mul_one] at h
  have hzinv : aeval z⁻¹ V = 0 := by
    letI := invertibleOfNonzero hz0
    have h := (eval₂_reverse_eq_zero_iff (algebraMap ℤ ℂ) z V).mpr (by rwa [aeval_def] at hz)
    rwa [hrev, invOf_eq_inv, ← aeval_def] at h
  have hA := aeval_expand_add l p q hl z
  have hB := aeval_expand_add l p q hl z⁻¹
  rw [hUV, map_mul, hz, mul_zero] at hA
  rw [hUV, map_mul, hzinv, mul_zero] at hB
  set a := z ^ p with ha
  set b := z ^ q with hb
  have ha0 : a ≠ 0 := pow_ne_zero _ hz0
  have hb0 : b ≠ 0 := pow_ne_zero _ hz0
  rw [inv_pow, inv_pow, ← ha, ← hb] at hB
  have hGa := geom_sum_inv_mul_pow l ha0
  have hGb := geom_sum_inv_mul_pow l hb0
  have hkey : (∑ i ∈ Finset.range l, a ^ i) * (b ^ (l - 1) - a ^ (l - 1)) = 0 := by
    linear_combination -(b ^ (l - 1)) * hGa - a ^ (l - 1) * hGb
      - (a ^ (l - 1) * b ^ (l - 1)) * hB + a ^ (l - 1) * hA
  have hl2 := hl.two_le
  rcases mul_eq_zero.mp hkey with hGz | hab
  · refine ⟨p * l, Nat.mul_pos (by omega) hl.pos, ?_⟩
    have hgeom := geom_sum_mul a l
    rw [hGz, zero_mul] at hgeom
    rw [pow_mul, ← ha]
    linear_combination -hgeom
  · refine ⟨(p - q) * (l - 1), Nat.mul_pos (by omega) (by omega), ?_⟩
    have hsplit : a ^ (l - 1) = z ^ ((p - q) * (l - 1)) * b ^ (l - 1) := by
      rw [ha, hb, ← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      rw [← Nat.add_mul, Nat.sub_add_cancel hqp.le, Nat.mul_comm]
    have hb' : b ^ (l - 1) ≠ 0 := pow_ne_zero _ hb0
    have h2 : (z ^ ((p - q) * (l - 1)) - 1) * b ^ (l - 1) = 0 := by
      linear_combination -hsplit - hab
    rcases mul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hb'

/-! ## Nicol's conjecture for `n = l p`, `m = l q` -/

/-- If `a * b = 2` in `ℤ`, then `a` or `b` is a unit. -/
theorem isUnit_or_isUnit_of_mul_eq_two {a b : ℤ} (h : a * b = 2) : IsUnit a ∨ IsUnit b := by
  have hab : a.natAbs * b.natAbs = 2 := by rw [← Int.natAbs_mul, h]; rfl
  rcases Nat.prime_two.eq_one_or_self_of_dvd _ (Dvd.intro _ hab) with ha | ha
  · exact Or.inl (Int.isUnit_iff_natAbs_eq.mpr ha)
  · right
    rw [ha] at hab
    exact Int.isUnit_iff_natAbs_eq.mpr (by omega)

/-- **Key step.** For primes `l < q < p`, if `Φ_{lp} + Φ_{lq} = U * V` in `ℤ[X]` and
`V(0)` is a unit, then every complex root of `V` is a root of unity. -/
theorem exists_pow_eq_one_of_isUnit_coeff_zero {l q p : ℕ} (hl : l.Prime) (hq : q.Prime)
    (hp : p.Prime) (hlq : l < q) (hqp : q < p) {U V : ℤ[X]}
    (h : cyclotomic (l * p) ℤ + cyclotomic (l * q) ℤ = U * V) (hV0 : IsUnit (V.coeff 0))
    {z : ℂ} (hz : aeval z V = 0) : ∃ k : ℕ, 0 < k ∧ z ^ k = 1 := by
  obtain ⟨hFm, hF0, hF1⟩ := monic_coeff_expand_add hl hq hp hlq hqp
  have hid := cyclotomic_add_mul_eq_expand_add hl hq hp (by omega) (by omega)
  have hUV : expand ℤ p (cyclotomic l ℤ) + expand ℤ q (cyclotomic l ℤ) =
      U * (V * cyclotomic l ℤ) := by
    rw [← hid, h, mul_assoc]
  have hV'0 : IsUnit ((V * cyclotomic l ℤ).coeff 0) := by
    rw [mul_coeff_zero, cyclotomic_coeff_zero ℤ hl.one_lt, mul_one]
    exact hV0
  have hmir := mirror_eq_of_mul_eq hFm hF0 hF1 hUV hV'0
  refine exists_pow_eq_one_of_mirror_eq hl hqp hUV hV'0.ne_zero hmir ?_
  rw [map_mul, hz, zero_mul]

/-- **Nicol's conjecture for `n = l p`, `m = l q` (arXiv:2610.05568, Section 1,
consequence of Theorem 1.1 and Lemma 3.1; the `t = 1` case of Theorem 1.3).**
Let `l < q < p` be primes.  Whenever `Φ_{lp} + Φ_{lq} = u * v` in `ℤ[X]`, one of
`u`, `v` has only roots of unity as complex roots.  Equivalently, the non-cyclotomic
part of `Φ_{lp}(x) + Φ_{lq}(x)` is irreducible. -/
theorem nicol_lp_lq {l q p : ℕ} (hl : l.Prime) (hq : q.Prime) (hp : p.Prime) (hlq : l < q)
    (hqp : q < p) (u v : ℤ[X]) (h : cyclotomic (l * p) ℤ + cyclotomic (l * q) ℤ = u * v) :
    (∀ z : ℂ, aeval z u = 0 → ∃ k : ℕ, 0 < k ∧ z ^ k = 1) ∨
      ∀ z : ℂ, aeval z v = 0 → ∃ k : ℕ, 0 < k ∧ z ^ k = 1 := by
  have hf0 : u.coeff 0 * v.coeff 0 = 2 := by
    rw [← mul_coeff_zero, ← h, coeff_add,
      cyclotomic_coeff_zero ℤ (Nat.one_lt_mul_iff.mpr ⟨hl.pos, hp.pos, Or.inl hl.one_lt⟩),
      cyclotomic_coeff_zero ℤ (Nat.one_lt_mul_iff.mpr ⟨hl.pos, hq.pos, Or.inl hl.one_lt⟩)]
    rfl
  rcases isUnit_or_isUnit_of_mul_eq_two hf0 with hu | hv
  · left
    intro z hz
    exact exists_pow_eq_one_of_isUnit_coeff_zero hl hq hp hlq hqp
      (by rw [h, mul_comm]) hu hz
  · right
    intro z hz
    exact exists_pow_eq_one_of_isUnit_coeff_zero hl hq hp hlq hqp h hv hz

/-- Non-vacuity: the hypotheses of `nicol_lp_lq` are jointly satisfiable, at
`(l, q, p) = (2, 3, 5)` with the trivial factorisation `u = Φ_{10} + Φ_6`, `v = 1`. -/
example :
    (∀ z : ℂ, aeval z (cyclotomic (2 * 5) ℤ + cyclotomic (2 * 3) ℤ) = 0 →
        ∃ k : ℕ, 0 < k ∧ z ^ k = 1) ∨
      ∀ z : ℂ, aeval z (1 : ℤ[X]) = 0 → ∃ k : ℕ, 0 < k ∧ z ^ k = 1 :=
  nicol_lp_lq (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ _
    (mul_one _).symm

/-- **Nicol's conjecture for `n = l p`, `m = l q`, over `ℚ[X]` (arXiv:2610.05568,
Section 1, as stated: irreducibility in `ℚ[x]`).**  Let `l < q < p` be primes.
Whenever `Φ_{lp} + Φ_{lq} = u * v` in `ℚ[X]`, one of `u`, `v` has only roots of unity
as complex roots; i.e. the non-cyclotomic part of `Φ_{lp} + Φ_{lq}` is irreducible
in `ℚ[x]`.  Reduced to `nicol_lp_lq` by Gauss's lemma
(`IsIntegrallyClosed.eq_map_mul_C_of_dvd`). -/
theorem nicol_lp_lq_rat {l q p : ℕ} (hl : l.Prime) (hq : q.Prime) (hp : p.Prime)
    (hlq : l < q) (hqp : q < p) (u v : ℚ[X])
    (h : cyclotomic (l * p) ℚ + cyclotomic (l * q) ℚ = u * v) :
    (∀ z : ℂ, aeval z u = 0 → ∃ k : ℕ, 0 < k ∧ z ^ k = 1) ∨
      ∀ z : ℂ, aeval z v = 0 → ∃ k : ℕ, 0 < k ∧ z ^ k = 1 := by
  set f : ℤ[X] := cyclotomic (l * p) ℤ + cyclotomic (l * q) ℤ with hfdef
  have hfm : f.Monic := by
    apply Monic.add_of_left (cyclotomic.monic _ ℤ)
    apply degree_lt_degree
    rw [natDegree_cyclotomic, natDegree_cyclotomic, Nat.totient_mul
      ((Nat.coprime_primes hl hq).mpr (by omega)), Nat.totient_mul
      ((Nat.coprime_primes hl hp).mpr (by omega)), Nat.totient_prime hl,
      Nat.totient_prime hq, Nat.totient_prime hp]
    have hl2 := hl.two_le
    exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  have hmap : map (algebraMap ℤ ℚ) f = u * v := by
    rw [hfdef, Polynomial.map_add, map_cyclotomic, map_cyclotomic, h]
  obtain ⟨u', hu'⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ hfm (Dvd.intro v hmap.symm)
  obtain ⟨v', hv'⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ hfm (Dvd.intro_left u hmap.symm)
  have hlead : u.leadingCoeff * v.leadingCoeff = 1 := by
    rw [← leadingCoeff_mul, ← hmap, (hfm.map (algebraMap ℤ ℚ)).leadingCoeff]
  have hu0 : u.leadingCoeff ≠ 0 := left_ne_zero_of_mul_eq_one hlead
  have hv0 : v.leadingCoeff ≠ 0 := right_ne_zero_of_mul_eq_one hlead
  have hf' : f = u' * v' := by
    apply map_injective (algebraMap ℤ ℚ) (RingHom.injective_int (algebraMap ℤ ℚ))
    rw [hmap, Polynomial.map_mul, ← hu', ← hv']
    calc map (algebraMap ℤ ℚ) u' * C u.leadingCoeff * (map (algebraMap ℤ ℚ) v' * C v.leadingCoeff)
        = map (algebraMap ℤ ℚ) u' * map (algebraMap ℤ ℚ) v' *
            C (u.leadingCoeff * v.leadingCoeff) := by rw [C_mul]; ring
      _ = map (algebraMap ℤ ℚ) u' * map (algebraMap ℤ ℚ) v' := by rw [hlead, C_1, mul_one]
  have hroot : ∀ (w : ℚ[X]) (w' : ℤ[X]), map (algebraMap ℤ ℚ) w' * C w.leadingCoeff = w →
      w.leadingCoeff ≠ 0 → ∀ z : ℂ, aeval z w = 0 → aeval z w' = 0 := by
    intro w w' hw hw0 z hz
    rw [← hw, map_mul, aeval_map_algebraMap, aeval_C] at hz
    exact (mul_eq_zero.mp hz).resolve_right (by simpa using hw0)
  rcases nicol_lp_lq hl hq hp hlq hqp u' v' hf' with hu | hv
  · exact Or.inl fun z hz => hu z (hroot u u' hu' hu0 z hz)
  · exact Or.inr fun z hz => hv z (hroot v v' hv' hv0 z hz)

end Candidates.NicolConjectureTwoPrimes
