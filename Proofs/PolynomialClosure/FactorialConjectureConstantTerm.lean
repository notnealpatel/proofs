/-
# Factorial Conjecture: nonzero constant term and one variable (van den Essen-Wright-Zhao)

## Source

arXiv 1008.3962, Arno van den Essen, David Wright and Wenhua Zhao,
"On the Image Conjecture", Section 4 "The Factorial Conjecture".
Retrieved 2026-10-21 (`fetch 1008.3962`, LaTeX source).

Definition 1.2 (label `Ldef`): for any ring `A`, `𝓛 : A[z_1, …, z_n] → A` is
the `A`-linear map with `𝓛(z_1^{l_1} ⋯ z_n^{l_n}) = l_1! ⋯ l_n!`.

Conjecture 4.2 (label `numbers`, Factorial Conjecture), verbatim:

> Let `f ∈ ℂ[U_1,…,U_n]` be such that `𝓛(f^m) = 0` for all `m ≥ 1`.
> Then `f = 0`.

The paper says "the Factorial Conjecture holds for `f`" when this
implication holds for that `f`.  The proved cases formalized here, verbatim:

* Proposition 4.7 (label `monomtimes`): "The Factorial Conjecture holds for
  `f ∈ ℂ[U_1,…,U_n]` having the form `f = Mh` where `M` is a monomial and `h`
  has nonzero constant term."
* Proposition 4.8 (label `const`): "The Factorial Conjecture holds for
  `f ∈ ℂ[U_1,…,U_n]` having nonzero constant term."
* Theorem 4.9 (label `n=1`): "The Factorial Conjecture holds for `n = 1`."

Numbering: every environment in the source shares the per-section `rema`
counter, so the labels above sit at 4.7, 4.8 and 4.9 in source order.  The
dispatcher's target text called them Prop 4.5, Prop/Cor 4.6 and Theorem 4.6/4.7;
the labels are the stable identifiers.

## Status

Proved in the paper (2010).  The general Factorial Conjecture is open.

## Route taken here

The paper uses Nullstellensatz reduction to algebraic coefficients and
valuations on Dedekind overrings.  This file follows a shorter route.

1. The coefficients of `h` generate a finite type `ℤ`-subalgebra `A`.
2. `ℤ` is a Jacobson ring, so a residue field `A ⧸ m` is a finite `ℤ`-module
   (Zariski's lemma), hence has prime characteristic `p`
   (`exists_prime_not_isUnit_of_finiteType`).
3. In `(A ⧸ m)[U]`, `h^p = ∑ c_d^p U^{p d}`.  The shifted factorial weights
   `(pα + pd)! / (pα)!` vanish mod `p` for `d ≠ 0`.  So the shifted functional
   of `h^p` reduces to `c_0^p = 1`.
4. Then `𝓛((U^α h)^p) = (pα)! · c^p · (nonzero) ≠ 0`.

The coefficient field is generalised to any field of characteristic zero.
The `ℂ` statements in the paper are special cases.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.FactorialConjectureConstantTerm

open MvPolynomial

/-! ## Weighted linear functionals on polynomial rings -/

/-- The `R`-linear functional on `R[U]` sending the monomial `U^d` to the
natural-number weight `w d`. -/
noncomputable def weightL {σ R : Type*} [CommSemiring R] (w : (σ →₀ ℕ) → ℕ) :
    MvPolynomial σ R →ₗ[R] R :=
  (basisMonomials σ R).constr R (fun d => (w d : R))

/-- `weightL w (c U^d) = c · w d`. -/
theorem weightL_monomial {σ R : Type*} [CommSemiring R] (w : (σ →₀ ℕ) → ℕ)
    (d : σ →₀ ℕ) (c : R) : weightL w (monomial d c) = c * w d := by
  have hmon : monomial d c = c • (monomial d (1 : R) : MvPolynomial σ R) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hmon, map_smul, smul_eq_mul]
  have hb : (monomial d (1 : R) : MvPolynomial σ R) = basisMonomials σ R d := by
    rw [coe_basisMonomials]
  rw [hb, weightL, Module.Basis.constr_basis]

/-- Coefficient formula: `weightL w f = ∑_d coeff d f · w d`. -/
theorem weightL_eq_sum {σ R : Type*} [CommSemiring R] (w : (σ →₀ ℕ) → ℕ)
    (f : MvPolynomial σ R) : weightL w f = ∑ d ∈ f.support, coeff d f * w d := by
  conv_lhs => rw [f.as_sum]
  rw [map_sum]
  exact Finset.sum_congr rfl fun d _ => weightL_monomial w d (coeff d f)

/-- A weighted functional commutes with any change of coefficient ring. -/
theorem map_weightL {σ R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (w : (σ →₀ ℕ) → ℕ) (f : MvPolynomial σ R) :
    φ (weightL w f) = weightL w (map φ f) := by
  conv_rhs => rw [f.as_sum]
  rw [weightL_eq_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_monomial, weightL_monomial, map_mul, map_natCast]

/-! ## The factorial functional `𝓛` -/

/-- The factorial weight `d! = d_1! ⋯ d_n!` of an exponent vector. -/
def factWeight {σ : Type*} [Fintype σ] (d : σ →₀ ℕ) : ℕ :=
  ∏ i, (d i).factorial

/-- The paper's map `𝓛 : R[U_1,…,U_n] → R` (Definition 1.2): the `R`-linear map
with `𝓛(U_1^{l_1} ⋯ U_n^{l_n}) = l_1! ⋯ l_n!`. -/
noncomputable def factL {σ R : Type*} [Fintype σ] [CommSemiring R] :
    MvPolynomial σ R →ₗ[R] R :=
  weightL factWeight

/-- `𝓛(c U^d) = c · d_1! ⋯ d_n!`. -/
theorem factL_monomial {σ R : Type*} [Fintype σ] [CommSemiring R] (d : σ →₀ ℕ) (c : R) :
    factL (monomial d c) = c * ∏ i, ((d i).factorial : R) := by
  rw [factL, weightL_monomial, factWeight, Nat.cast_prod]

/-- `𝓛(X_i^k) = k!`. -/
theorem factL_X_pow {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R] (i : σ)
    (k : ℕ) : factL (X i ^ k : MvPolynomial σ R) = k.factorial := by
  rw [X_pow_eq_monomial, factL_monomial, one_mul]
  rw [Finset.prod_eq_single i]
  · rw [Finsupp.single_eq_same]
  · intro j _ hj
    rw [Finsupp.single_eq_of_ne hj, Nat.factorial_zero, Nat.cast_one]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- Ground truth: `𝓛(U_1^2 U_2^3) = 2! · 3! = 12`. -/
example : factL (monomial (Finsupp.single 0 2 + Finsupp.single 1 3) 1 :
    MvPolynomial (Fin 2) ℚ) = 12 := by
  rw [factL_monomial, Fin.prod_univ_two]
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  norm_num [Nat.factorial]

/-- Ground truth: `𝓛(U^3) = 6` in one variable. -/
example : factL (X 0 ^ 3 : MvPolynomial (Fin 1) ℚ) = 6 := by
  rw [factL_X_pow]
  norm_num [Nat.factorial]

/-- Ground truth: `f = U - 1` has `𝓛(f) = 1! - 0! = 0`. -/
example : factL (X 0 - 1 : MvPolynomial (Fin 1) ℚ) = 0 := by
  rw [map_sub, ← pow_one (X 0), factL_X_pow, ← C_1, ← monomial_zero', factL_monomial]
  simp

/-- Ground truth: for `f = U - 1`, `𝓛(f^2) = 2! - 2·1! + 0! = 1 ≠ 0`, so the
hypothesis `𝓛(f^m) = 0` for all `m ≥ 1` really constrains `f` beyond `m = 1`. -/
example : factL ((X 0 - 1) ^ 2 : MvPolynomial (Fin 1) ℚ) = 1 := by
  have hexp : ((X 0 - 1) ^ 2 : MvPolynomial (Fin 1) ℚ) =
      X 0 ^ 2 - C 2 * X 0 ^ 1 + monomial 0 1 := by
    rw [monomial_zero', C_1, pow_one, map_ofNat]
    ring
  rw [hexp, map_add, map_sub, C_mul', map_smul, factL_X_pow, factL_X_pow,
    factL_monomial]
  norm_num [Nat.factorial]

/-- The paper's phrase "the Factorial Conjecture holds for `f`": if `𝓛(f^m) = 0`
for every `m ≥ 1`, then `f = 0`. -/
def FactorialConjectureHolds {σ R : Type*} [Fintype σ] [CommSemiring R]
    (f : MvPolynomial σ R) : Prop :=
  (∀ m : ℕ, 1 ≤ m → factL (f ^ m) = 0) → f = 0

/-- The Factorial Conjecture (Conjecture 4.2 of arXiv 1008.3962) in `n` variables:
every `f ∈ ℂ[U_1,…,U_n]` with `𝓛(f^m) = 0` for all `m ≥ 1` is zero. -/
def FactorialConjecture (n : ℕ) : Prop :=
  ∀ f : MvPolynomial (Fin n) ℂ, FactorialConjectureHolds f

/-! ## Shifted factorial weights -/

/-- The shifted weight `(β + γ)! / β! = ∏_i (β_i + 1)(β_i + 2) ⋯ (β_i + γ_i)`. -/
def shiftWeight {σ : Type*} [Fintype σ] (β γ : σ →₀ ℕ) : ℕ :=
  ∏ i, (β i + 1).ascFactorial (γ i)

/-- `(β + γ)! = β! · shiftWeight β γ`. -/
theorem factWeight_add {σ : Type*} [Fintype σ] (β γ : σ →₀ ℕ) :
    factWeight (β + γ) = factWeight β * shiftWeight β γ := by
  rw [factWeight, factWeight, shiftWeight, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finsupp.add_apply, Nat.factorial_mul_ascFactorial]

/-- `shiftWeight β 0 = 1`. -/
theorem shiftWeight_zero {σ : Type*} [Fintype σ] (β : σ →₀ ℕ) : shiftWeight β 0 = 1 := by
  simp [shiftWeight]

/-- For `d ≠ 0` and `0 < p`, `p` divides `shiftWeight β (p • d)`: some factor is a
rising factorial of length `p d_i ≥ p`, which `(p d_i)!` and hence `p` divide. -/
theorem dvd_shiftWeight_smul {σ : Type*} [Fintype σ] {p : ℕ} (hp : 0 < p) (β d : σ →₀ ℕ)
    (hd : d ≠ 0) : p ∣ shiftWeight β (p • d) := by
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := Finsupp.ne_iff.mp hd
  have hpi : p ∣ (β i + 1).ascFactorial ((p • d) i) := by
    have h1 : p ∣ ((p • d) i).factorial := by
      apply Nat.dvd_factorial hp
      rw [Finsupp.smul_apply, smul_eq_mul]
      exact Nat.le_mul_of_pos_right p (Nat.pos_of_ne_zero hi)
    exact h1.trans (Nat.factorial_dvd_ascFactorial _ _)
  exact hpi.trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))

/-- Factor the monomial out of `𝓛`: `𝓛(U^β G) = β! · weightL (shiftWeight β) G`. -/
theorem factL_monomial_one_mul {σ R : Type*} [Fintype σ] [CommSemiring R] (β : σ →₀ ℕ)
    (G : MvPolynomial σ R) :
    factL (monomial β 1 * G) = (factWeight β : R) * weightL (shiftWeight β) G := by
  have hG : monomial β 1 * G = ∑ γ ∈ G.support, monomial (β + γ) (coeff γ G) := by
    conv_lhs => rw [G.as_sum]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun γ _ => by rw [monomial_mul, one_mul]
  rw [hG, map_sum, weightL_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [factL, weightL_monomial, factWeight_add, Nat.cast_mul]
  ring

/-! ## Frobenius step in prime characteristic -/

/-- In characteristic `p`, if `g` has constant term `1`, then the shifted functional
of `g^p` is `1`: `g^p = ∑ c_d^p U^{p d}`, every term with `d ≠ 0` has weight
divisible by `p`, and the `d = 0` term is `1`. -/
theorem weightL_shiftWeight_pow_char {σ k : Type*} [Fintype σ] [CommRing k] (p : ℕ)
    [Fact p.Prime] [CharP k p] (β : σ →₀ ℕ) (g : MvPolynomial σ k) (hg : coeff 0 g = 1) :
    weightL (shiftWeight β) (g ^ p) = 1 := by
  have hpow : g ^ p = ∑ d ∈ g.support, monomial (p • d) (coeff d g ^ p) := by
    conv_lhs => rw [g.as_sum]
    rw [sum_pow_char]
    exact Finset.sum_congr rfl fun d _ => monomial_pow
  rw [hpow, map_sum]
  simp_rw [weightL_monomial]
  rw [Finset.sum_eq_single 0]
  · rw [smul_zero, shiftWeight_zero, hg, one_pow, Nat.cast_one, mul_one]
  · intro d _ hd
    obtain ⟨m, hm⟩ := dvd_shiftWeight_smul (Fact.out : p.Prime).pos β d hd
    rw [hm, Nat.cast_mul, CharP.cast_eq_zero, zero_mul, mul_zero]
  · intro h0
    haveI : Nontrivial k := CharP.nontrivial_of_char_ne_one (Fact.out : p.Prime).one_lt.ne'
    rw [mem_support_iff, not_not, hg] at h0
    exact absurd h0 one_ne_zero

/-! ## Bridge: finite type `ℤ`-algebras have non-invertible primes -/

open Ideal in
/-- `ℤ` is a Jacobson ring: every nonzero prime is maximal, and the Jacobson radical
of `0` is `0` because `x * x + 1` is a unit only for `x = 0`. -/
instance isJacobsonRing_int : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases hbot : P = ⊥
  · subst hbot
    refine le_antisymm (fun x hx => ?_) le_jacobson
    rw [mem_jacobson_bot] at hx
    have hu := hx x
    rw [Int.isUnit_iff] at hu
    rw [Ideal.mem_bot]
    rcases hu with h | h <;> nlinarith [sq_nonneg x]
  · haveI : P.IsMaximal := hP.isMaximal hbot
    exact jacobson_eq_self_of_isMaximal

/-- A nontrivial commutative ring of finite type over `ℤ` has a rational prime that
is not a unit.  A residue field is a finite `ℤ`-module (Zariski's lemma over the
Jacobson ring `ℤ`), so it has prime characteristic `p`, and `p` lies in the
maximal ideal. -/
theorem exists_prime_not_isUnit_of_finiteType (A : Type*) [CommRing A] [Nontrivial A]
    [Algebra.FiniteType ℤ A] : ∃ p : ℕ, p.Prime ∧ ¬ IsUnit (p : A) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite ℤ (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℤ (A ⧸ m)
  have hmax : (RingHom.ker (algebraMap ℤ (A ⧸ m))).IsMaximal := by
    rw [RingHom.ker_eq_comap_bot]
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (⊥ : Ideal (A ⧸ m))
  have hne : RingHom.ker (algebraMap ℤ (A ⧸ m)) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hmax
    have h2top : Ideal.span {(2 : ℤ)} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top, Int.isUnit_iff]
      decide
    have h2 := hmax.eq_of_le h2top bot_le
    have hmem : (2 : ℤ) ∈ (⊥ : Ideal ℤ) := h2 ▸ Ideal.mem_span_singleton_self 2
    rw [Ideal.mem_bot] at hmem
    exact absurd hmem (by decide)
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [RingHom.mem_ker, eq_intCast] at hn
  set q := ringChar (A ⧸ m) with hq
  haveI : CharP (A ⧸ m) q := ringChar.charP (A ⧸ m)
  have hq0 : q ≠ 0 := by
    intro h0
    rw [CharP.intCast_eq_zero_iff (A ⧸ m) q, h0, Nat.cast_zero, zero_dvd_iff] at hn
    exact hn0 hn
  have hqprime : q.Prime := (CharP.char_is_prime_or_zero (A ⧸ m) q).resolve_right hq0
  refine ⟨q, hqprime, fun hu => ?_⟩
  have hzero : ((q : A) : A ⧸ m) = 0 := by
    rw [map_natCast]
    exact CharP.cast_eq_zero (A ⧸ m) q
  have hmem : (q : A) ∈ m := Ideal.Quotient.eq_zero_iff_mem.mp hzero
  exact hm.ne_top (Ideal.eq_top_of_isUnit_mem m hmem hu)

/-- If the prime `p` is not a unit of `A`, then some residue field of `A` has
characteristic `p`. -/
theorem exists_charP_quotient_of_not_isUnit {A : Type*} [CommRing A] {p : ℕ}
    (hp : p.Prime) (hu : ¬ IsUnit (p : A)) :
    ∃ m : Ideal A, m.IsMaximal ∧ CharP (A ⧸ m) p := by
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits (show (p : A) ∈ nonunits A from hu)
  refine ⟨m, hm, ?_⟩
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  rw [CharP.charP_iff_prime_eq_zero hp, ← map_natCast (Ideal.Quotient.mk m)]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem

/-! ## The core nonvanishing statement -/

/-- If `h` has constant term `1` (over any nontrivial commutative ring), then there
is a prime `p` such that every shifted functional `weightL (shiftWeight β)`
is nonzero on `h^p`. -/
theorem exists_prime_forall_weightL_shiftWeight_pow_ne_zero {σ K : Type*} [Fintype σ]
    [CommRing K] [Nontrivial K] (h : MvPolynomial σ K) (h0 : coeff 0 h = 1) :
    ∃ p : ℕ, p.Prime ∧ ∀ β : σ →₀ ℕ, weightL (shiftWeight β) (h ^ p) ≠ 0 := by
  let A : Subalgebra ℤ K := Algebra.adjoin ℤ (h.coeffs : Set K)
  haveI : Algebra.FiniteType ℤ A := Algebra.FiniteType.adjoin_of_finite (Finset.finite_toSet _)
  have hrange : h ∈ Set.range (map (A.val : A →+* K)) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro c hc
    exact ⟨⟨c, Algebra.subset_adjoin hc⟩, rfl⟩
  obtain ⟨hA, hmap⟩ := hrange
  have hinj : Function.Injective (A.val : A →+* K) := Subtype.val_injective
  have hA0 : coeff 0 hA = 1 := by
    apply hinj
    rw [← coeff_map, hmap, h0, map_one]
  obtain ⟨p, hp, hpu⟩ := exists_prime_not_isUnit_of_finiteType A
  obtain ⟨m, hm, hchar⟩ := exists_charP_quotient_of_not_isUnit hp hpu
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨p, hp, fun β hne => ?_⟩
  have hk0 : coeff 0 (map (Ideal.Quotient.mk m) hA) = 1 := by
    rw [coeff_map, hA0, map_one]
  have hone := weightL_shiftWeight_pow_char p β (map (Ideal.Quotient.mk m) hA) hk0
  rw [← map_pow, ← map_weightL] at hone
  have hzeroA : weightL (shiftWeight β) (hA ^ p) = 0 := by
    apply hinj
    rw [map_weightL, map_pow, hmap, hne, map_zero]
  rw [hzeroA, map_zero] at hone
  haveI : Nontrivial (A ⧸ m) := Ideal.Quotient.nontrivial_iff.mpr hm.ne_top
  exact zero_ne_one hone

/-- Positive form of Proposition 4.7 over any field of characteristic zero: if `h`
has nonzero constant term, then for some prime `p`, `𝓛((U^α h)^p) ≠ 0`. -/
theorem exists_prime_factL_pow_ne_zero {σ K : Type*} [Fintype σ] [Field K] [CharZero K]
    (α : σ →₀ ℕ) (h : MvPolynomial σ K) (h0 : coeff 0 h ≠ 0) :
    ∃ p : ℕ, p.Prime ∧ factL ((monomial α 1 * h) ^ p) ≠ 0 := by
  set c := coeff 0 h with hc
  set h' : MvPolynomial σ K := c⁻¹ • h with hh'
  have hh'0 : coeff 0 h' = 1 := by
    rw [hh', coeff_smul, smul_eq_mul, ← hc, inv_mul_cancel₀ h0]
  have hh : h = c • h' := by
    rw [hh', smul_smul, mul_inv_cancel₀ h0, one_smul]
  obtain ⟨p, hp, hne⟩ := exists_prime_forall_weightL_shiftWeight_pow_ne_zero h' hh'0
  refine ⟨p, hp, ?_⟩
  have hexp : (monomial α 1 * h) ^ p = c ^ p • (monomial (p • α) 1 * h' ^ p) := by
    rw [hh, mul_smul_comm, smul_pow, mul_pow, monomial_pow, one_pow]
  rw [hexp, map_smul, factL_monomial_one_mul, smul_eq_mul]
  have hfact : (factWeight (p • α) : K) ≠ 0 := by
    rw [Nat.cast_ne_zero, factWeight]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _
  exact mul_ne_zero (pow_ne_zero p h0) (mul_ne_zero hfact (hne (p • α)))

/-- Proposition 4.7 (arXiv 1008.3962, label `monomtimes`), over any field of
characteristic zero: the Factorial Conjecture holds for `f = U^α h` whenever `h`
has nonzero constant term. -/
theorem factorialConjectureHolds_monomial_mul {σ K : Type*} [Fintype σ] [Field K]
    [CharZero K] (α : σ →₀ ℕ) (h : MvPolynomial σ K) (h0 : coeff 0 h ≠ 0) :
    FactorialConjectureHolds (monomial α 1 * h) := by
  intro hL
  obtain ⟨p, hp, hne⟩ := exists_prime_factL_pow_ne_zero α h h0
  exact absurd (hL p hp.one_lt.le) hne

/-- Proposition 4.7 (arXiv 1008.3962, label `monomtimes`): the Factorial Conjecture
holds for `f ∈ ℂ[U_1,…,U_n]` of the form `f = M h`, `M` a monomial and `h` with
nonzero constant term. -/
theorem prop_4_7 {n : ℕ} (α : Fin n →₀ ℕ) (h : MvPolynomial (Fin n) ℂ)
    (h0 : coeff 0 h ≠ 0) : FactorialConjectureHolds (monomial α 1 * h) :=
  factorialConjectureHolds_monomial_mul α h h0

/-- Proposition 4.8 over any field of characteristic zero: the Factorial
Conjecture holds for every `f` with nonzero constant term. -/
theorem factorialConjectureHolds_of_coeff_zero_ne_zero {σ K : Type*} [Fintype σ]
    [Field K] [CharZero K] (f : MvPolynomial σ K) (h0 : coeff 0 f ≠ 0) :
    FactorialConjectureHolds f := by
  have hf : f = monomial 0 1 * f := by
    rw [monomial_zero', C_1, one_mul]
  rw [hf]
  exact factorialConjectureHolds_monomial_mul 0 f h0

/-- Proposition 4.8 (arXiv 1008.3962, label `const`): the Factorial Conjecture
holds for `f ∈ ℂ[U_1,…,U_n]` having nonzero constant term. -/
theorem prop_4_8 {n : ℕ} (f : MvPolynomial (Fin n) ℂ) (h0 : coeff 0 f ≠ 0) :
    FactorialConjectureHolds f :=
  factorialConjectureHolds_of_coeff_zero_ne_zero f h0

/-! ## One variable -/

/-- If every exponent in the support of `f` dominates `α`, and `α` is in the
support, then `f = U^α h` with `h` having constant term `coeff α f`. -/
theorem eq_monomial_mul_divMonomial {σ R : Type*} [CommSemiring R] (f : MvPolynomial σ R)
    (α : σ →₀ ℕ) (hle : ∀ d ∈ f.support, α ≤ d) :
    f = monomial α 1 * f.divMonomial α ∧ coeff 0 (f.divMonomial α) = coeff α f := by
  refine ⟨?_, ?_⟩
  · have hmod : f.modMonomial α = 0 := by
      ext s
      by_cases hs : α ≤ s
      · rw [coeff_modMonomial_of_le f hs, coeff_zero]
      · rw [coeff_modMonomial_of_not_le f hs, coeff_zero]
        by_contra hne
        exact hs (hle s (mem_support_iff.mpr hne))
    conv_lhs => rw [← divMonomial_add_modMonomial f α]
    rw [hmod, add_zero]
  · rw [coeff_divMonomial, add_zero]

/-- In one variable, every nonzero `f` has the form `U^α h` with `h(0) ≠ 0`. -/
theorem exists_eq_monomial_mul_of_ne_zero {R : Type*} [CommSemiring R]
    (f : MvPolynomial (Fin 1) R) (hf : f ≠ 0) :
    ∃ (α : Fin 1 →₀ ℕ) (h : MvPolynomial (Fin 1) R), coeff 0 h ≠ 0 ∧
      f = monomial α 1 * h := by
  have hne : f.support.Nonempty := support_nonempty.mpr hf
  obtain ⟨α, hα, hmin⟩ := f.support.exists_min_image (fun d => d 0) hne
  have hle : ∀ d ∈ f.support, α ≤ d := by
    intro d hd
    rw [Finsupp.le_def]
    intro i
    rw [Fin.fin_one_eq_zero i]
    exact hmin d hd
  obtain ⟨hfac, hcoeff⟩ := eq_monomial_mul_divMonomial f α hle
  refine ⟨α, f.divMonomial α, ?_, hfac⟩
  rw [hcoeff]
  exact mem_support_iff.mp hα

/-- Theorem 4.9 over any field of characteristic zero: the Factorial Conjecture
holds for every polynomial in one variable. -/
theorem factorialConjectureHolds_fin_one {K : Type*} [Field K] [CharZero K]
    (f : MvPolynomial (Fin 1) K) : FactorialConjectureHolds f := by
  intro hL
  by_contra hf
  obtain ⟨α, h, h0, rfl⟩ := exists_eq_monomial_mul_of_ne_zero f hf
  exact hf (factorialConjectureHolds_monomial_mul α h h0 hL)

/-- Theorem 4.9 (arXiv 1008.3962, label `n=1`): the Factorial Conjecture holds for
`n = 1`, i.e. every `f ∈ ℂ[U]` with `𝓛(f^m) = 0` for all `m ≥ 1` is zero. -/
theorem thm_4_9 : FactorialConjecture 1 :=
  fun f => factorialConjectureHolds_fin_one f

/-! ## Non-vacuity checks -/

/-- The hypothesis of Proposition 4.8 is satisfiable: `1 - U` has constant term `1`,
and the positive form yields a prime `p` with `𝓛((1 - U)^p) ≠ 0`. -/
example : ∃ p : ℕ, p.Prime ∧ factL ((monomial 0 1 * (1 - X 0)) ^ p :
    MvPolynomial (Fin 1) ℂ) ≠ 0 := by
  apply exists_prime_factL_pow_ne_zero
  rw [coeff_sub, coeff_one, coeff_X, if_pos rfl, if_neg]
  · norm_num
  · intro h
    have := congrArg (fun d : Fin 1 →₀ ℕ => d 0) h
    simp at this

/-- `FactorialConjecture 1` is not vacuous: its hypothesis holds for `f = 0`. -/
example : (∀ m : ℕ, 1 ≤ m → factL ((0 : MvPolynomial (Fin 1) ℂ) ^ m) = 0) := by
  intro m hm
  rw [zero_pow (by omega), map_zero]

end Candidates.FactorialConjectureConstantTerm
