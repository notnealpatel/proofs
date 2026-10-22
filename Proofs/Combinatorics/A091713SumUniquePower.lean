/-
# A091713 — odd coefficients of `A = X + X * A(A(A(X)))`

Paul D. Hanna (OEIS A091713, Dec 01 2024) conjectured that every
positive-degree coefficient is odd.

## Formalization

`A(x)` is the unique `A : ℤ⟦X⟧` with `constantCoeff A = 0` and
`A = X + X * A(A(A(X)))`, where composition is `PowerSeries.subst`:
`subst (subst A A) A` is `A ∘ (A ∘ A)`.  Existence and uniqueness are proved
(`existsUnique_solution`), so the conjecture `hanna_coeff_odd`, quantified over
all solutions, is about exactly the OEIS series.

## Proof

Two solutions agreeing modulo `X ^ n` agree modulo `X ^ (n + 1)`
(`X_pow_succ_dvd_rhs_sub`), which gives uniqueness over any commutative ring
and existence by Picard iteration.  Over `ZMod 2`, `B = X / (1 - X)` satisfies
`B ∘ B = X / (1 - 2X) = X`, hence `B ∘ (B ∘ B) = B = X + X * B`; reduction mod 2
commutes with substitution (`PowerSeries.map_subst`), so the reduction of `A` is
`B` by uniqueness, and every coefficient `a(n)`, `n ≥ 1`, is `1` mod 2.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A091713SumUniquePower

open PowerSeries

/-! ## Definitions -/

section General

variable {R : Type*} [CommRing R]

/-- The right-hand side `X + X * A(A(A(X)))` of the functional equation of A091713,
with composition given by `PowerSeries.subst`. -/
noncomputable def rhs (A : R⟦X⟧) : R⟦X⟧ :=
  X + X * subst (subst A A : R⟦X⟧) A

/-! ## Congruences modulo powers of `X` under substitution -/

/-- If `a` has zero constant term and `X ∣ f`, then `X ∣ f(a)`. -/
theorem X_dvd_subst {a f : R⟦X⟧} (ha : constantCoeff a = 0) (hf : X ∣ f) :
    X ∣ (subst a f : R⟦X⟧) := by
  obtain ⟨q, rfl⟩ := hf
  have hs := HasSubst.of_constantCoeff_zero' ha
  rw [subst_mul hs, subst_X hs]
  exact Dvd.dvd.mul_right (X_dvd_iff.mpr ha) _

/-- A composite `f(a)` of series with zero constant terms has zero constant term. -/
theorem constantCoeff_subst_eq_zero {a f : R⟦X⟧} (ha : constantCoeff a = 0)
    (hf : constantCoeff f = 0) : constantCoeff (subst a f : R⟦X⟧) = 0 :=
  X_dvd_iff.mp (X_dvd_subst ha (X_dvd_iff.mpr hf))

/-- If `f ≡ g (mod X ^ n)` (both with zero constant term), then
`h(f) ≡ h(g) (mod X ^ n)` for every `h`. -/
theorem X_pow_dvd_subst_sub_subst {f g : R⟦X⟧} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) (h : R⟦X⟧) {n : ℕ} (hfg : X ^ n ∣ f - g) :
    X ^ n ∣ (subst f h : R⟦X⟧) - subst g h := by
  rw [X_pow_dvd_iff]
  intro m hm
  rw [map_sub, coeff_subst' (HasSubst.of_constantCoeff_zero' hf),
    coeff_subst' (HasSubst.of_constantCoeff_zero' hg), sub_eq_zero]
  congr 1
  funext d
  have hpow : X ^ n ∣ f ^ d - g ^ d := hfg.trans (sub_dvd_pow_sub_pow f g d)
  have hcoeff := (X_pow_dvd_iff.mp hpow) m hm
  rw [map_sub, sub_eq_zero] at hcoeff
  rw [hcoeff]

/-- If `h ≡ k (mod X ^ n)` and `a` has zero constant term, then
`h(a) ≡ k(a) (mod X ^ n)`. -/
theorem X_pow_dvd_subst_sub_subst_left {a : R⟦X⟧} (ha : constantCoeff a = 0)
    {h k : R⟦X⟧} {n : ℕ} (hhk : X ^ n ∣ h - k) :
    X ^ n ∣ (subst a h : R⟦X⟧) - subst a k := by
  have hs := HasSubst.of_constantCoeff_zero' ha
  obtain ⟨q, hq⟩ := hhk
  rw [← subst_sub hs, hq, subst_mul hs, subst_pow hs, subst_X hs]
  exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd (X_dvd_iff.mpr ha) n) _

/-- If `A ≡ B (mod X ^ n)` (both with zero constant term), then
`A(A(A)) ≡ B(B(B)) (mod X ^ n)`. -/
theorem X_pow_dvd_comp3_sub {A B : R⟦X⟧} (hA : constantCoeff A = 0)
    (hB : constantCoeff B = 0) {n : ℕ} (hAB : X ^ n ∣ A - B) :
    X ^ n ∣ (subst (subst A A : R⟦X⟧) A : R⟦X⟧) - subst (subst B B : R⟦X⟧) B := by
  have huv : X ^ n ∣ (subst A A : R⟦X⟧) - subst B B := by
    have h1 := X_pow_dvd_subst_sub_subst hA hB A hAB
    have h2 := X_pow_dvd_subst_sub_subst_left hB hAB
    have h12 := dvd_add h1 h2
    rwa [sub_add_sub_cancel] at h12
  have hu := constantCoeff_subst_eq_zero hA hA
  have hv := constantCoeff_subst_eq_zero hB hB
  have h1 := X_pow_dvd_subst_sub_subst hu hv A huv
  have h2 := X_pow_dvd_subst_sub_subst_left hv hAB
  have h12 := dvd_add h1 h2
  rwa [sub_add_sub_cancel] at h12

/-- The contraction step: `A ≡ B (mod X ^ n)` implies
`rhs A ≡ rhs B (mod X ^ (n + 1))`. -/
theorem X_pow_succ_dvd_rhs_sub {A B : R⟦X⟧} (hA : constantCoeff A = 0)
    (hB : constantCoeff B = 0) {n : ℕ} (hAB : X ^ n ∣ A - B) :
    X ^ (n + 1) ∣ rhs A - rhs B := by
  have h := X_pow_dvd_comp3_sub hA hB hAB
  have heq : rhs A - rhs B =
      X * ((subst (subst A A : R⟦X⟧) A : R⟦X⟧) - subst (subst B B : R⟦X⟧) B) := by
    unfold rhs; ring
  rw [heq, pow_succ']
  exact mul_dvd_mul_left X h

/-- A power series divisible by every power of `X` is zero. -/
theorem eq_zero_of_forall_X_pow_dvd {φ : R⟦X⟧} (h : ∀ n, X ^ n ∣ φ) : φ = 0 := by
  ext m
  exact (X_pow_dvd_iff.mp (h (m + 1))) m (Nat.lt_succ_self m)

/-- The right-hand side always has zero constant term. -/
theorem constantCoeff_rhs (A : R⟦X⟧) : constantCoeff (rhs A) = 0 := by
  simp [rhs]

/-! ## Uniqueness and existence -/

/-- Uniqueness: two series with zero constant term solving `A = rhs A` coincide. -/
theorem eq_of_eq_rhs {A B : R⟦X⟧} (hA0 : constantCoeff A = 0) (hB0 : constantCoeff B = 0)
    (hA : A = rhs A) (hB : B = rhs B) : A = B := by
  have key : ∀ n, X ^ n ∣ A - B := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h := X_pow_succ_dvd_rhs_sub hA0 hB0 ih
      rwa [← hA, ← hB] at h
  exact sub_eq_zero.mp (eq_zero_of_forall_X_pow_dvd key)

/-- Picard iterates `A₀ = 0`, `A_{k+1} = X + X * A_k(A_k(A_k(X)))`. -/
noncomputable def approx : ℕ → R⟦X⟧
  | 0 => 0
  | k + 1 => rhs (approx k)

/-- Every Picard iterate has zero constant term. -/
theorem constantCoeff_approx (k : ℕ) : constantCoeff (approx (R := R) k) = 0 := by
  cases k with
  | zero => simp [approx]
  | succ k => exact constantCoeff_rhs _

/-- Consecutive Picard iterates agree modulo `X ^ k`. -/
theorem X_pow_dvd_approx_succ_sub (k : ℕ) :
    X ^ k ∣ approx (R := R) (k + 1) - approx k := by
  induction k with
  | zero => simp
  | succ k ih =>
    exact X_pow_succ_dvd_rhs_sub (constantCoeff_approx _) (constantCoeff_approx _) ih

/-- Picard iterates `A_m` and `A_k` with `k ≤ m` agree modulo `X ^ k`. -/
theorem X_pow_dvd_approx_sub {k m : ℕ} (hkm : k ≤ m) :
    X ^ k ∣ approx (R := R) m - approx k := by
  induction m, hkm using Nat.le_induction with
  | base => simp
  | succ m hkm ih =>
    have h := (pow_dvd_pow (X : R⟦X⟧) hkm).trans (X_pow_dvd_approx_succ_sub (R := R) m)
    have h12 := dvd_add h ih
    rwa [sub_add_sub_cancel] at h12

/-- The limit of the Picard iterates: its `n`-th coefficient is that of `A_{n+1}`. -/
noncomputable def solution : R⟦X⟧ := mk fun n => coeff n (approx (R := R) (n + 1))

/-- The limit agrees with the `k`-th Picard iterate modulo `X ^ k`. -/
theorem X_pow_dvd_solution_sub (k : ℕ) : X ^ k ∣ solution (R := R) - approx k := by
  rw [X_pow_dvd_iff]
  intro m hm
  have h := (X_pow_dvd_iff.mp (X_pow_dvd_approx_sub (R := R) (Nat.succ_le_of_lt hm))) m
    (Nat.lt_succ_self m)
  rw [map_sub, sub_eq_zero] at h
  rw [map_sub, sub_eq_zero, solution, coeff_mk, h]

/-- The limit has zero constant term. -/
theorem constantCoeff_solution : constantCoeff (solution (R := R)) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, solution, coeff_mk,
    coeff_zero_eq_constantCoeff_apply, constantCoeff_approx]

/-- The limit solves the functional equation `A = X + X * A(A(A(X)))`. -/
theorem solution_eq_rhs : solution (R := R) = rhs solution := by
  have key : ∀ n, X ^ n ∣ rhs (solution (R := R)) - solution := by
    intro n
    have h1 := X_pow_succ_dvd_rhs_sub constantCoeff_solution (constantCoeff_approx n)
      (X_pow_dvd_solution_sub (R := R) n)
    have h2 := X_pow_dvd_solution_sub (R := R) (n + 1)
    have h3 := dvd_sub h1 h2
    rw [show rhs (solution (R := R)) - rhs (approx n) - (solution - approx (n + 1)) =
      rhs solution - solution by rw [approx]; ring] at h3
    exact (pow_dvd_pow X (Nat.le_succ n)).trans h3
  exact (sub_eq_zero.mp (eq_zero_of_forall_X_pow_dvd key)).symm

/-- Reduction along a ring hom commutes with the right-hand side. -/
theorem map_rhs {S : Type*} [CommRing S] (φ : R →+* S) {A : R⟦X⟧}
    (hA : constantCoeff A = 0) : map φ (rhs A) = rhs (map φ A) := by
  have hs := HasSubst.of_constantCoeff_zero' hA
  have hu := HasSubst.of_constantCoeff_zero' (constantCoeff_subst_eq_zero hA hA)
  have h1 : map φ (subst A A : R⟦X⟧) = subst (map φ A) (map φ A) := map_subst hs A
  have h2 : map φ (subst (subst A A : R⟦X⟧) A : R⟦X⟧) =
      subst (map φ (subst A A : R⟦X⟧)) (map φ A) := map_subst hu A
  unfold rhs
  rw [map_add, map_mul, map_X, h2, h1]

end General

/-- **A091713 is well defined.** There is exactly one `A : ℤ⟦X⟧` with
`A(0) = 0` and `A(x) = x + x * A(A(A(x)))` (OEIS A091713, NAME line). -/
theorem existsUnique_solution :
    ∃! A : ℤ⟦X⟧, constantCoeff A = 0 ∧ A = X + X * subst (subst A A : ℤ⟦X⟧) A :=
  ⟨solution, ⟨constantCoeff_solution, solution_eq_rhs⟩,
    fun _ hB => eq_of_eq_rhs hB.1 constantCoeff_solution hB.2 solution_eq_rhs⟩

/-! ## The explicit solution modulo 2 -/

/-- The geometric series `1 + X + X ^ 2 + ⋯` over `ZMod 2`. -/
noncomputable def geom : (ZMod 2)⟦X⟧ := mk fun _ => 1

/-- `X / (1 - X) = X + X ^ 2 + ⋯` over `ZMod 2`. -/
noncomputable def B2 : (ZMod 2)⟦X⟧ := X * geom

/-- The geometric series satisfies `G = 1 + X * G`. -/
theorem geom_eq : geom = 1 + X * geom := by
  ext n
  cases n with
  | zero => simp [geom]
  | succ n => simp [geom, coeff_succ_X_mul]

/-- `B2` has zero constant term. -/
theorem constantCoeff_B2 : constantCoeff B2 = 0 := by
  simp [B2]

/-- In characteristic 2, `B2 ∘ B2 = X` (`X / (1 - 2X) = X`). -/
theorem subst_B2_self : (subst B2 B2 : (ZMod 2)⟦X⟧) = X := by
  have hs := HasSubst.of_constantCoeff_zero' constantCoeff_B2
  set y : (ZMod 2)⟦X⟧ := subst B2 geom with hy_def
  have hy : y = 1 + B2 * y := by
    have h := congrArg (subst B2) geom_eq
    rw [subst_add hs, subst_mul hs, subst_X hs] at h
    rw [hy_def]
    convert h using 2
    rw [← coe_substAlgHom hs, map_one]
  have h2 : (2 : (ZMod 2)⟦X⟧) = 0 := by
    have h2' : (2 : ZMod 2) = 0 := rfl
    calc (2 : (ZMod 2)⟦X⟧) = C (2 : ZMod 2) := (map_ofNat C 2).symm
      _ = 0 := by rw [h2', map_zero]
  have hGy : geom * y = 1 := by
    unfold B2 at hy
    linear_combination (-1 : (ZMod 2)⟦X⟧) * hy + y * geom_eq + (y - 1) * h2
  have hBB : (subst B2 B2 : (ZMod 2)⟦X⟧) = B2 * y := by
    rw [show (subst B2 B2 : (ZMod 2)⟦X⟧) = subst B2 (X * geom) from rfl,
      subst_mul hs, subst_X hs]
  rw [hBB, B2, mul_assoc, hGy, mul_one]

/-- `B2 = X / (1 - X)` solves the functional equation over `ZMod 2`. -/
theorem B2_eq_rhs : B2 = rhs B2 := by
  unfold rhs
  rw [subst_B2_self, X_subst]
  conv_lhs => rw [B2, geom_eq]
  rw [B2]
  ring

/-- Every coefficient of `B2` in positive degree is `1`. -/
theorem coeff_B2 {n : ℕ} (hn : 1 ≤ n) : coeff n B2 = 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp [B2, geom, coeff_succ_X_mul]

/-- The reduction mod 2 of the A091713 series is `X / (1 - X)`. -/
theorem map_zmod_two_eq {A : ℤ⟦X⟧} (h0 : constantCoeff A = 0)
    (hA : A = X + X * subst (subst A A : ℤ⟦X⟧) A) :
    map (Int.castRingHom (ZMod 2)) A = X * mk fun _ => 1 := by
  have hA' : A = rhs A := hA
  have hm0 : constantCoeff (map (Int.castRingHom (ZMod 2)) A) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h0,
      map_zero]
  have hm : map (Int.castRingHom (ZMod 2)) A = rhs (map (Int.castRingHom (ZMod 2)) A) := by
    rw [← map_rhs (Int.castRingHom (ZMod 2)) h0, ← hA']
  exact eq_of_eq_rhs hm0 constantCoeff_B2 hm B2_eq_rhs

/-! ## The conjecture -/

/-- **Hanna's conjecture (A091713, Paul D. Hanna, Dec 01 2024).**

Every positive-degree coefficient is odd. These are the coefficients
`a(n)`, `n ≥ 1`, of the power series `A(x)` with `A(0) = 0` and
`A(x) = x + x * A(A(A(x)))`; by `existsUnique_solution` there is exactly one
such `A`.  The guard `1 ≤ n` is load-bearing: `a(0) = 0` is even. -/
theorem hanna_coeff_odd {A : ℤ⟦X⟧} (h0 : constantCoeff A = 0)
    (hA : A = X + X * subst (subst A A : ℤ⟦X⟧) A) {n : ℕ} (hn : 1 ≤ n) :
    Odd (coeff n A) := by
  have hc := congrArg (coeff n) (map_zmod_two_eq h0 hA)
  rw [coeff_map, show (X * mk fun _ => (1 : ZMod 2)) = B2 from rfl, coeff_B2 hn] at hc
  exact ZMod.intCast_eq_one_iff_odd.mp hc

/-! ## Examples from the listed terms -/

/-- The truncation `X + X² + 3X³ + 15X⁴ + 99X⁵` of the listed terms. -/
noncomputable def p5 : ℤ⟦X⟧ := X + X ^ 2 + 3 * X ^ 3 + 15 * X ^ 4 + 99 * X ^ 5

/-- Substituting into `p5` evaluates the polynomial. -/
theorem subst_p5 {a : ℤ⟦X⟧} (ha : constantCoeff a = 0) :
    (subst a p5 : ℤ⟦X⟧) = a + a ^ 2 + 3 * a ^ 3 + 15 * a ^ 4 + 99 * a ^ 5 := by
  have hs := HasSubst.of_constantCoeff_zero' ha
  rw [p5, ← coe_substAlgHom hs]
  simp only [map_add, map_mul, map_pow, map_ofNat, coe_substAlgHom, subst_X hs]

/-- `p5` has zero constant term. -/
theorem constantCoeff_p5 : constantCoeff p5 = 0 := by simp [p5]

/-- `p5` solves the functional equation modulo `X ^ 6`. -/
theorem X_pow_six_dvd_rhs_p5_sub : X ^ 6 ∣ rhs p5 - p5 := by
  set q : ℤ⟦X⟧ := X + 2 * X ^ 2 + 8 * X ^ 3 + 46 * X ^ 4 + 330 * X ^ 5 with hq
  have hq0 : constantCoeff q = 0 := by simp [hq]
  have hu : X ^ 6 ∣ (subst p5 p5 : ℤ⟦X⟧) - q := by
    rw [subst_p5 constantCoeff_p5]
    refine ⟨941480149401*X^19 + 713242537425*X^18 + 358782609735*X^17 + 166750734645*X^16 +
      107142179760*X^15 + 48561460200*X^14 + 18360903825*X^13 + 6805765395*X^12 +
      2938402170*X^11 + 999859950*X^10 + 303613434*X^9 + 92745810*X^8 + 31223232*X^7 +
      8283114*X^6 + 2040498*X^5 + 518616*X^4 + 139563*X^3 + 27987*X^2 + 5532*X + 1194, ?_⟩
    rw [p5, hq]
    ring
  have h1 := X_pow_dvd_subst_sub_subst (constantCoeff_subst_eq_zero constantCoeff_p5
    constantCoeff_p5) hq0 p5 hu
  have h2 : X ^ 6 ∣ X + X * (subst q p5 : ℤ⟦X⟧) - p5 := by
    rw [subst_p5 hq0]
    refine ⟨387440390700000*X^20 + 270034211700000*X^19 + 122244736680000*X^18 +
      48419645076000*X^17 + 20900027451600*X^16 + 7439654551824*X^15 + 2304074028960*X^14 +
      675209620800*X^13 + 199653173280*X^12 + 52195643520*X^11 + 12547784712*X^10 +
      2909746200*X^9 + 665416800*X^8 + 135403128*X^7 + 25952172*X^6 + 4877772*X^5 +
      880458*X^4 + 139198*X^3 + 21586*X^2 + 3464*X + 781, ?_⟩
    rw [p5, hq]
    ring
  have h3 := dvd_add (dvd_mul_of_dvd_right h1 X) h2
  rw [show X * ((subst (subst p5 p5 : ℤ⟦X⟧) p5 : ℤ⟦X⟧) - subst q p5) +
    (X + X * (subst q p5 : ℤ⟦X⟧) - p5) = rhs p5 - p5 by rw [rhs]; ring] at h3
  exact h3

/-- Any solution agrees with `p5` modulo `X ^ n` for `n ≤ 6`. -/
theorem X_pow_dvd_sub_p5 {A : ℤ⟦X⟧} (h0 : constantCoeff A = 0) (hA : A = rhs A) :
    ∀ n ≤ 6, X ^ n ∣ A - p5 := by
  intro n hn
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := X_pow_succ_dvd_rhs_sub h0 constantCoeff_p5 (ih (Nat.le_of_succ_le hn))
    have h2 := (pow_dvd_pow X hn).trans X_pow_six_dvd_rhs_p5_sub
    have h3 := dvd_add h1 h2
    rwa [sub_add_sub_cancel, ← hA] at h3

-- The solution's first coefficients are the listed terms
-- `1, 1, 3, 15, 99`.
example {A : ℤ⟦X⟧} (h0 : constantCoeff A = 0)
    (hA : A = X + X * subst (subst A A : ℤ⟦X⟧) A) :
    coeff 1 A = 1 ∧ coeff 2 A = 1 ∧ coeff 3 A = 3 ∧ coeff 4 A = 15 ∧ coeff 5 A = 99 := by
  have h := X_pow_dvd_iff.mp (X_pow_dvd_sub_p5 h0 hA 6 le_rfl)
  simp only [map_sub, sub_eq_zero] at h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [h _ (by norm_num), p5, ← map_ofNat (C (R := ℤ)) 3, ← map_ofNat (C (R := ℤ)) 15,
      ← map_ofNat (C (R := ℤ)) 99]
    simp only [map_add, coeff_C_mul_X_pow, coeff_X_pow, coeff_X]
    norm_num

-- Non-vacuity of the conjecture's hypotheses: a solution exists.
example : ∃ A : ℤ⟦X⟧, constantCoeff A = 0 ∧ A = X + X * subst (subst A A : ℤ⟦X⟧) A :=
  existsUnique_solution.exists

end Candidates.A091713SumUniquePower
