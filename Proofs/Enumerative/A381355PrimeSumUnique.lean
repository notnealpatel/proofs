/-
# A381355: prime divisibility of logarithmic-derivative coefficients

OEIS A381355 and A381353, Paul D. Hanna; the conjecture comment is unsigned.
The normalized rational series `F`, with constant and linear coefficients
`1`, is uniquely determined by `[X^n] F^prime(n) = 0` for `n ≥ 2`.
Its coefficients and those of `A = XF'/F` are integral. For every `n ≥ 2`,
`prime(n)` divides the integer coefficient `a(n)`.
The proof uses prime-power coefficient divisibility and `X(F^p)' = pAF^p`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A381355PrimeSumUnique

open PowerSeries
open scoped Polynomial

/-- Frobenius congruence: for a prime `p` and `P ∈ ℤ[X]`, the coefficient of `x^j`
in `P^p` is divisible by `p` whenever `p ∤ j`. -/
theorem prime_dvd_coeff_pow_of_not_dvd (p : ℕ) [hp : Fact p.Prime] (P : ℤ[X]) (j : ℕ)
    (hj : ¬ p ∣ j) : (p : ℤ) ∣ (P ^ p).coeff j := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hmap : (((P ^ p).coeff j : ℤ) : ZMod p) =
      ((P.map (Int.castRingHom (ZMod p))) ^ p).coeff j := by
    rw [← Polynomial.map_pow, Polynomial.coeff_map]
    rfl
  rw [hmap, ← ZMod.expand_card, Polynomial.coeff_expand hp.out.pos, if_neg hj]

/-- If `φ` has constant term `1` and `1 ≤ m`, then
`[x^m] φ^q = [x^m] (trunc_m φ)^q + q * [x^m] φ`. -/
theorem coeff_pow_eq_coeff_trunc_pow_add {R : Type*} [CommRing R] (φ : R⟦X⟧)
    (hφ : constantCoeff φ = 1) (m q : ℕ) (hm : 1 ≤ m) :
    coeff m (φ ^ q) = ((trunc m φ) ^ q).coeff m + q * coeff m φ := by
  set T : R⟦X⟧ := (trunc m φ : R⟦X⟧) with hT
  have hdvd : (X : R⟦X⟧) ^ m ∣ φ - T := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro k hk
    rw [map_sub, hT, Polynomial.coeff_coe, coeff_trunc, if_pos hk, sub_self]
  obtain ⟨ψ, hψ⟩ := hdvd
  have hT0 : constantCoeff T = 1 := by
    rw [hT, ← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, coeff_trunc,
      if_pos (by omega), coeff_zero_eq_constantCoeff_apply, hφ]
  have hψ0 : constantCoeff ψ = coeff m φ := by
    have h := congrArg (coeff m) hψ
    rw [map_sub, hT, Polynomial.coeff_coe, coeff_trunc, if_neg (lt_irrefl m), sub_zero,
      PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      coeff_zero_eq_constantCoeff_apply] at h
    exact h.symm
  have hgeom := Commute.geom_sum₂_mul (Commute.all φ T) q
  have hdiff : φ ^ q = T ^ q + X ^ m * (ψ * ∑ i ∈ Finset.range q, φ ^ i * T ^ (q - 1 - i)) := by
    rw [← mul_assoc, ← hψ, mul_comm, hgeom]
    ring
  have hQ : constantCoeff (∑ i ∈ Finset.range q, φ ^ i * T ^ (q - 1 - i)) = q := by
    simp [map_sum, hφ, hT0]
  rw [hdiff, map_add, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    coeff_zero_eq_constantCoeff_apply, map_mul, hQ, hψ0, hT, ← Polynomial.coe_pow,
    Polynomial.coeff_coe, mul_comm]


/-! ## Definitions -/

/-- `prime n` is the `n`-th prime `p_n`, one-indexed: `prime 1 = 2`, `prime 2 = 3`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The coefficient chosen at step `m` of the construction (PARI program of A381353):
`f_0 = f_1 = 1` and, for `m ≥ 2`, `f_m = -[x^m] G^{p_m} / p_m`, where `G` is the
polynomial `∑_{k<m} f_k x^k` already constructed. -/
noncomputable def nextCoeff (m : ℕ) (G : ℚ[X]) : ℚ :=
  if m < 2 then 1 else -((G ^ prime m).coeff m) / (prime m : ℚ)

/-- `partialF n = ∑_{k<n} f_k x^k`, the truncation of `F` built step by step. -/
noncomputable def partialF : ℕ → ℚ[X]
  | 0 => 0
  | m + 1 => partialF m + Polynomial.C (nextCoeff m (partialF m)) * Polynomial.X ^ m

/-- `f m = [x^m] F(x)`, the coefficients of A381353. -/
noncomputable def f (m : ℕ) : ℚ := (partialF (m + 1)).coeff m

/-- `F(x) = ∑ f_m x^m`, the g.f. of A381353 (over `ℚ`; integrality is proved below). -/
noncomputable def F : ℚ⟦X⟧ := PowerSeries.mk f

/-- `A(x) = x F'(x) / F(x)`, the g.f. of A381355. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.X * d⁄dX ℚ F * F⁻¹

/-- `a n = [x^n] A(x)`, the terms of A381355. -/
noncomputable def a (n : ℕ) : ℚ := coeff n A

/-! ## Basic facts -/

/-- `n < prime n` for all `n` (since `p_n ≥ n + 1`). -/
theorem lt_prime (n : ℕ) : n < prime n := by
  have hmono : StrictMono (Nat.nth Nat.Prime) :=
    Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have h : n - 1 + Nat.nth Nat.Prime 0 ≤ Nat.nth Nat.Prime (n - 1 + 0) :=
    hmono.add_le_nat (n - 1) 0
  rw [Nat.add_zero, Nat.nth_prime_zero_eq_two] at h
  unfold prime
  omega

/-- `prime n` is prime. -/
theorem prime_prime (n : ℕ) : (prime n).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _

/-- Coefficients of the partial sums. -/
theorem coeff_partialF (n k : ℕ) :
    (partialF n).coeff k = if k < n then f k else 0 := by
  induction n with
  | zero => simp [partialF]
  | succ m ih =>
    rw [partialF, Polynomial.coeff_add, ih, Polynomial.coeff_C_mul_X_pow]
    rcases lt_trichotomy k m with hk | hk | hk
    · rw [if_pos hk, if_neg hk.ne, if_pos (by omega), add_zero]
    · subst hk
      rw [if_neg (lt_irrefl k), if_pos rfl, if_pos (by omega), zero_add, f, partialF,
        Polynomial.coeff_add, ih, if_neg (lt_irrefl k), Polynomial.coeff_C_mul_X_pow,
        if_pos rfl, zero_add]
    · rw [if_neg (by omega), if_neg hk.ne', if_neg (by omega), add_zero]

/-- `trunc n F = partialF n`. -/
theorem trunc_F (n : ℕ) : trunc n F = partialF n := by
  ext k
  rw [coeff_trunc, coeff_partialF, F, coeff_mk]

/-- `f m = nextCoeff m (partialF m)`. -/
theorem f_eq_nextCoeff (m : ℕ) : f m = nextCoeff m (partialF m) := by
  rw [f, partialF, Polynomial.coeff_add, coeff_partialF, if_neg (lt_irrefl m),
    Polynomial.coeff_C_mul_X_pow, if_pos rfl, zero_add]

/-- `F` has constant term `1`. -/
theorem constantCoeff_F : constantCoeff F = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, F, coeff_mk, f_eq_nextCoeff, nextCoeff,
    if_pos (by norm_num)]

/-- `[x^1] F = 1`. -/
theorem coeff_one_F : coeff 1 F = 1 := by
  rw [F, coeff_mk, f_eq_nextCoeff, nextCoeff, if_pos (by norm_num)]

/-- The defining property of A381353: `[x^n] F(x)^{p_n} = 0` for `n ≥ 2`. -/
theorem coeff_F_pow_prime (n : ℕ) (hn : 2 ≤ n) : coeff n (F ^ prime n) = 0 := by
  have hp : (prime n : ℚ) ≠ 0 := by exact_mod_cast (prime_prime n).ne_zero
  rw [coeff_pow_eq_coeff_trunc_pow_add F constantCoeff_F n (prime n) (by omega), trunc_F, F,
    coeff_mk, f_eq_nextCoeff, nextCoeff, if_neg (by omega)]
  field_simp
  ring


/-! ## Integrality of `F` -/

/-- Every partial sum `partialF n` has integer coefficients. -/
theorem exists_int_partialF (n : ℕ) :
    ∃ P : ℤ[X], partialF n = P.map (Int.castRingHom ℚ) := by
  induction n with
  | zero => exact ⟨0, by simp [partialF]⟩
  | succ m ih =>
    obtain ⟨P, hP⟩ := ih
    have hc : ∃ z : ℤ, nextCoeff m (partialF m) = z := by
      by_cases hm : m < 2
      · exact ⟨1, by rw [nextCoeff, if_pos hm, Int.cast_one]⟩
      · have hpp : Fact (prime m).Prime := ⟨prime_prime m⟩
        have hndvd : ¬ prime m ∣ m := fun h =>
          absurd (Nat.le_of_dvd (by omega) h) (not_le.mpr (lt_prime m))
        obtain ⟨z, hz⟩ := prime_dvd_coeff_pow_of_not_dvd (prime m) P m hndvd
        have hp : (prime m : ℚ) ≠ 0 := by exact_mod_cast (prime_prime m).ne_zero
        refine ⟨-z, ?_⟩
        rw [nextCoeff, if_neg hm, hP, ← Polynomial.map_pow, Polynomial.coeff_map, hz,
          eq_intCast]
        push_cast
        field_simp
    obtain ⟨z, hz⟩ := hc
    refine ⟨P + Polynomial.C z * Polynomial.X ^ m, ?_⟩
    rw [partialF, hz, hP]
    simp

/-- Every coefficient `f m` of `F` is an integer. -/
theorem exists_int_f (m : ℕ) : ∃ z : ℤ, f m = z := by
  obtain ⟨P, hP⟩ := exists_int_partialF (m + 1)
  exact ⟨P.coeff m, by rw [f, hP, Polynomial.coeff_map, eq_intCast]⟩


/-! ## Integer lifts of `F` and `A` -/

/-- The integer power series whose image in `ℚ⟦X⟧` is `F`. -/
noncomputable def FZ : ℤ⟦X⟧ := PowerSeries.mk fun k => Classical.choose (exists_int_f k)

/-- `FZ` maps to `F`. -/
theorem map_FZ : PowerSeries.map (Int.castRingHom ℚ) FZ = F := by
  ext k
  rw [coeff_map, FZ, coeff_mk, F, coeff_mk, eq_intCast]
  exact (Classical.choose_spec (exists_int_f k)).symm

/-- `FZ` has constant term `1`. -/
theorem constantCoeff_FZ : constantCoeff FZ = 1 := by
  have h := congrArg constantCoeff map_FZ
  rw [constantCoeff_F, ← coeff_zero_eq_constantCoeff_apply, coeff_map, eq_intCast,
    coeff_zero_eq_constantCoeff_apply] at h
  exact_mod_cast h

/-- The derivative commutes with the coefficient map `ℤ → ℚ`. -/
theorem map_derivative (φ : ℤ⟦X⟧) :
    PowerSeries.map (Int.castRingHom ℚ) (d⁄dX ℤ φ) =
      d⁄dX ℚ (PowerSeries.map (Int.castRingHom ℚ) φ) := by
  ext k
  rw [coeff_map, coeff_derivative, coeff_derivative, coeff_map, map_mul]
  simp

/-- The integer series `A_ℤ = x F_ℤ' F_ℤ⁻¹`. -/
noncomputable def AZ : ℤ⟦X⟧ := PowerSeries.X * d⁄dX ℤ FZ * invOfUnit FZ 1

/-- `A_ℤ F_ℤ = x F_ℤ'`. -/
theorem AZ_mul_FZ : AZ * FZ = PowerSeries.X * d⁄dX ℤ FZ := by
  rw [AZ, mul_assoc, mul_comm (invOfUnit FZ 1) FZ,
    mul_invOfUnit FZ 1 (by rw [constantCoeff_FZ, Units.val_one]), mul_one]

/-- `A_ℤ` maps to `A`. -/
theorem map_AZ : PowerSeries.map (Int.castRingHom ℚ) AZ = A := by
  have hF0 : constantCoeff F ≠ 0 := by rw [constantCoeff_F]; exact one_ne_zero
  have hinv : PowerSeries.map (Int.castRingHom ℚ) (invOfUnit FZ 1) = F⁻¹ := by
    rw [PowerSeries.eq_inv_iff_mul_eq_one hF0, ← map_FZ, ← map_mul, mul_comm,
      mul_invOfUnit FZ 1 (by rw [constantCoeff_FZ, Units.val_one]), map_one]
  rw [AZ, map_mul, map_mul, hinv, map_derivative, map_FZ, map_X, A]

/-- Every term `a n` of A381355 is an integer, namely `[x^n] A_ℤ`. -/
theorem a_eq_coeff_AZ (n : ℕ) : a n = ((coeff n AZ : ℤ) : ℚ) := by
  rw [a, ← map_AZ, coeff_map, eq_intCast]

/-! ## The divisibility -/

/-- Logarithmic-derivative identity for the power: `x (F_ℤ^q)' = q A_ℤ F_ℤ^q`. -/
theorem X_mul_derivative_FZ_pow (q : ℕ) (hq : 1 ≤ q) :
    PowerSeries.X * d⁄dX ℤ (FZ ^ q) = (q : ℤ⟦X⟧) * (AZ * FZ ^ q) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  rw [derivative_pow, Nat.add_sub_cancel, pow_succ]
  linear_combination (-((r + 1 : ℕ) : ℤ⟦X⟧) * FZ ^ r) * AZ_mul_FZ

/-- Core lemma: if `[x^n] F_ℤ^p = 0` for a prime `p` with `1 ≤ n < p`, then
`p ∣ [x^n] A_ℤ`. -/
theorem prime_dvd_coeff_AZ (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : 1 ≤ n) (hnp : n < p)
    (hz : coeff n (FZ ^ p) = 0) : (p : ℤ) ∣ coeff n AZ := by
  have hsum : coeff n (AZ * FZ ^ p) = 0 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h := congrArg (coeff (m + 1)) (X_mul_derivative_FZ_pow p hp.out.one_le)
    rw [coeff_succ_X_mul, coeff_derivative, hz, zero_mul, ← map_natCast (C (R := ℤ)),
      coeff_C_mul] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (by exact_mod_cast hp.out.ne_zero)
  have hH0 : coeff 0 (FZ ^ p) = 1 := by
    rw [coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_FZ, one_pow]
  -- every term other than `(n, 0)` of the Cauchy product is divisible by `p`
  have hterm : ∀ ij ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (n, 0),
      (p : ℤ) ∣ coeff ij.1 AZ * coeff ij.2 (FZ ^ p) := by
    rintro ⟨i, j⟩ hij
    simp only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal, ne_eq,
      Prod.mk.injEq] at hij ⊢
    obtain ⟨hne, hsum⟩ := hij
    rcases Nat.eq_zero_or_pos i with hi | hi
    · have h0 : coeff 0 AZ = 0 := by
        rw [AZ, mul_assoc, coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_X,
          zero_mul]
      rw [hi, h0, zero_mul]
      exact dvd_zero _
    · have hj : j ≠ 0 := fun hj => hne ⟨by omega, hj⟩
      have hpj : ¬ p ∣ j := fun h => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hj) h)
        (by omega)
      obtain ⟨P, hP⟩ : ∃ P : ℤ[X], P = trunc (j + 1) FZ := ⟨_, rfl⟩
      have hcoeff : coeff j (FZ ^ p) = (P ^ p).coeff j := by
        rw [hP, ← Polynomial.coeff_coe, Polynomial.coe_pow, ← coeff_coe_trunc_of_lt
          (lt_add_one j), ← trunc_trunc_pow, coeff_coe_trunc_of_lt (lt_add_one j)]
      exact Dvd.dvd.mul_left (hcoeff ▸ prime_dvd_coeff_pow_of_not_dvd p P j hpj) _
  rw [coeff_mul, ← Finset.add_sum_erase _ _ ((show (n, 0) ∈ Finset.HasAntidiagonal.antidiagonal n from
      Finset.HasAntidiagonal.mem_antidiagonal.mpr (add_zero n))),
    hH0, mul_one] at hsum
  have hrest := Finset.dvd_sum hterm
  rw [eq_neg_of_add_eq_zero_left hsum]
  exact hrest.neg_right


/-- `F` is the unique series with `[x^0] F = [x^1] F = 1` and `[x^n] F^{p_n} = 0` for
all `n ≥ 2`, as the definitions of A381353/A381355 presuppose. -/
theorem eq_F_of_coeff_pow_prime (G : ℚ⟦X⟧) (h0 : constantCoeff G = 1) (h1 : coeff 1 G = 1)
    (h : ∀ n, 2 ≤ n → coeff n (G ^ prime n) = 0) : G = F := by
  have key : ∀ m, trunc m G = trunc m F := by
    intro m
    induction m with
    | zero => ext k; simp
    | succ m ih =>
      have hm : coeff m G = coeff m F := by
        rcases Nat.lt_or_ge m 2 with hm | hm
        · interval_cases m
          · rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, h0,
              constantCoeff_F]
          · rw [h1, coeff_one_F]
        · have hp : (prime m : ℚ) ≠ 0 := by exact_mod_cast (prime_prime m).ne_zero
          have hG := h m hm
          have hF := coeff_F_pow_prime m hm
          rw [coeff_pow_eq_coeff_trunc_pow_add G h0 m (prime m) (by omega)] at hG
          rw [coeff_pow_eq_coeff_trunc_pow_add F constantCoeff_F m (prime m) (by omega),
            ← ih] at hF
          exact mul_left_cancel₀ hp (by linear_combination hG - hF)
      ext k
      rw [coeff_trunc, coeff_trunc]
      split_ifs with hk
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
        · have := congrArg (fun P : ℚ[X] => P.coeff k) ih
          simpa only [coeff_trunc, if_pos hk] using this
        · rw [hk, hm]
      · rfl
  ext k
  have := congrArg (fun P : ℚ[X] => P.coeff k) (key (k + 1))
  simpa only [coeff_trunc, if_pos (lt_add_one k)] using this

/-! ## The conjecture -/

/-- **A381355 conjecture (Paul D. Hanna).** For every `n ≥ 2`, the term
`a(n) = [x^n] x F'(x)/F(x)` is an integer divisible by `p_n = prime(n)`.
The integer witness is `[x^n] A_ℤ`. -/
theorem prime_dvd_a (n : ℕ) (hn : 2 ≤ n) : ∃ z : ℤ, a n = z ∧ (prime n : ℤ) ∣ z := by
  have hpp : Fact (prime n).Prime := ⟨prime_prime n⟩
  refine ⟨coeff n AZ, a_eq_coeff_AZ n, prime_dvd_coeff_AZ (prime n) n (by omega)
    (lt_prime n) ?_⟩
  have h := coeff_F_pow_prime n hn
  rw [← map_FZ, ← map_pow, coeff_map, eq_intCast] at h
  exact_mod_cast h


/-! ## Examples -/

/-- `A F = x F'`, the defining identity of `A = x F'/F`. -/
theorem A_mul_F : A * F = PowerSeries.X * d⁄dX ℚ F := by
  rw [A, mul_assoc, PowerSeries.inv_mul_cancel F (by rw [constantCoeff_F]; exact one_ne_zero),
    mul_one]

/-- `prime 2 = 3`. -/
example : prime 2 = 3 := Nat.nth_prime_one_eq_three

/-- First terms of A381353: `1, 1, -1`. -/
theorem f_first_terms : f 0 = 1 ∧ f 1 = 1 ∧ f 2 = -1 := by
  refine ⟨by rw [f_eq_nextCoeff, nextCoeff, if_pos (by norm_num)],
    by rw [f_eq_nextCoeff, nextCoeff, if_pos (by norm_num)], ?_⟩
  have h2 : partialF 2 = 1 + Polynomial.X := by
    simp [partialF, nextCoeff]
  have hp2 : prime 2 = 3 := Nat.nth_prime_one_eq_three
  rw [f_eq_nextCoeff, nextCoeff, if_neg (by norm_num), h2, hp2,
    Polynomial.coeff_one_add_X_pow]
  norm_num [Nat.choose]

/-- First terms of A381355: `a(0) = 0` (no constant term), `a(1) = 1`, `a(2) = -3`. -/
example : a 0 = 0 ∧ a 1 = 1 ∧ a 2 = -3 := by
  have hrec : ∀ n, coeff (n + 1) (A * F) = f (n + 1) * (n + 1) := by
    intro n
    rw [A_mul_F, coeff_succ_X_mul, coeff_derivative, F, coeff_mk]
  have h0 : a 0 = 0 := by
    rw [a, A, mul_assoc, coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_X, zero_mul]
  obtain ⟨hf0, hf1, hf2⟩ := f_first_terms
  have e1 := hrec 0
  have e2 := hrec 1
  simp only [coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
    Finset.sum_singleton, F, coeff_mk] at e1 e2
  simp only [a] at h0 ⊢
  rw [h0, hf0, hf1] at e1
  rw [h0, hf0, hf1, hf2] at e2
  refine ⟨h0, by linear_combination e1, by linear_combination e2 - e1⟩

/-- Non-vacuity: the conjecture at `n = 2` says `3 ∣ a(2) = -3`. -/
example : ∃ z : ℤ, a 2 = z ∧ (3 : ℤ) ∣ z := by
  have h := prime_dvd_a 2 le_rfl
  rwa [show prime 2 = 3 from Nat.nth_prime_one_eq_three] at h

/-- Non-vacuity of the uniqueness theorem: `F` itself satisfies its hypotheses. -/
example : F = F :=
  eq_F_of_coeff_pow_prime F constantCoeff_F coeff_one_F coeff_F_pow_prime

end Candidates.A381355PrimeSumUnique
