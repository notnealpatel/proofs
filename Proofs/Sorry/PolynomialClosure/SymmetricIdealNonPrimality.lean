/-
# On the non-primality of certain symmetric ideals — Jun's "more variables" conjecture

## Source

H. K. Jun, *On the non primality of certain symmetric ideals*, arXiv:2112.10207,
J. Commut. Algebra 16 (2024) 37–47. Section 5 "Open Problems", subsection
"More variables", Conjecture `Conj:more variables`. (Theorem `theorem:generalization`
of Section 4 is the `r = 2` case.)

Verbatim (LaTeX source):

  Fix $r, n \in \N$, and for a subset $S$ of $[r] := \{1,2, \cdots, r\}$, define
  $t_S = \sum_{i \in S} t_i$, and $t_{S,0} = t_0 + t_S$. [...] We then define
  $I_r^{(d)} \subset R := K[t_0, \cdots, t_r]$ to be
  $I_r^{(d)} := \langle (t_{S,0})^d: S \subset [r]\rangle.$
  Conjecture. For any $r\geq 2$ and $n\geq 1$, we have
  $\left( t_1\cdots t_r\right)^{2n-1} \in I_{r}^{(nr)}$.

(`K` is a field of characteristic zero throughout the paper.)

Date: 2026-10-21. Status in the source: OPEN (proved there only for `r = 2`; checked by
computer for some small `r ≥ 3`).

## This module

Proves the conjecture (`conj_more_variables`) and the free generalization
`∏ tᵢ^(2aᵢ+1) ∈ I_r^{(∑ aᵢ + r)}` (`prod_X_pow_mem_symIdeal`), in fact over any commutative
`ℚ`-algebra (`prod_pow_mem_span_pow_add_sum`).

Proof (exponential generating functions):
1. One variable: from `1 = ((Y+1) - Y)^(2a+1)` and the binomial theorem, obtain rational
   power series `P, Q` of degree `≤ a` with `P + Q eˣ = X^(2a+1) + O(X^(2a+2))`
   (`exists_oneVar`).
2. Tensor step: `H = exp(xX) ∏ᵢ gᵢ(tᵢX)` with `gᵢ = Pᵢ + Qᵢ eˣ`. Its `D`-th coefficient
   (`D = ∑ (2aᵢ+1)`) is `∏ tᵢ^(2aᵢ+1)`; expanding the product gives
   `∑_S W_S(X) exp((x + t_S)X)` with `deg W_S ≤ ∑ aᵢ`, so the same coefficient is a
   combination of powers `(x + t_S)^l` with `l ≥ ∑ aᵢ + r`.
-/
import Mathlib

set_option autoImplicit false
open PowerSeries

namespace SymmetricIdealNonPrimality

/-- `DegLE d φ`: the power series `φ` has no coefficient beyond degree `d`, i.e. it is a
polynomial of degree at most `d`. -/
def DegLE {R : Type*} [CommRing R] (d : ℕ) (φ : R⟦X⟧) : Prop := ∀ j, d < j → coeff j φ = 0

/-- Degree bounds add under multiplication. -/
theorem degLE_mul {R : Type*} [CommRing R] {d e : ℕ} {φ ψ : R⟦X⟧}
    (hφ : DegLE d φ) (hψ : DegLE e ψ) :
    DegLE (d + e) (φ * ψ) := by
  intro j hj
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  by_cases h1 : d < p.1
  · rw [hφ _ h1, zero_mul]
  · rw [hψ p.2 (by omega), mul_zero]

/-- The power series `1` has degree at most `0`. -/
theorem degLE_one {R : Type*} [CommRing R] : DegLE 0 (1 : R⟦X⟧) := by
  intro j hj
  rw [coeff_one, if_neg (by omega)]

/-- Degree bounds add over finite products. -/
theorem degLE_prod {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι) (d : ι → ℕ) (f : ι → R⟦X⟧)
    (h : ∀ i ∈ s, DegLE (d i) (f i)) : DegLE (∑ i ∈ s, d i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using degLE_one
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact degLE_mul (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- Rescaling the image of a rational power series preserves its degree bound. -/
theorem degLE_rescale_map {A : Type*} [CommRing A] [Algebra ℚ A] {d : ℕ} {P : ℚ⟦X⟧}
    (hP : DegLE d P) (y : A) : DegLE d (rescale y (map (algebraMap ℚ A) P)) := by
  intro j hj
  rw [coeff_rescale, coeff_map, hP j hj, map_zero, mul_zero]

/-- `expScale y = exp (y X) = ∑ yⁿ Xⁿ / n!` as a power series over a `ℚ`-algebra. -/
noncomputable def expScale {A : Type*} [CommRing A] [Algebra ℚ A] (y : A) : A⟦X⟧ :=
  rescale y (exp A)

/-- The `n`-th coefficient of `exp (y X)` is `yⁿ / n!`. -/
theorem coeff_expScale {A : Type*} [CommRing A] [Algebra ℚ A] (y : A) (n : ℕ) :
    coeff n (expScale y) = algebraMap ℚ A (1 / n.factorial) * y ^ n := by
  rw [expScale, coeff_rescale, coeff_exp, mul_comm]

/-- `exp (y X) * exp (z X) = exp ((y + z) X)`. -/
theorem expScale_add {A : Type*} [CommRing A] [Algebra ℚ A] (y z : A) :
    expScale y * expScale z = expScale (y + z) :=
  exp_mul_exp_eq_exp_add y z

/-- `exp (0 X) = 1`. -/
theorem expScale_zero {A : Type*} [CommRing A] [Algebra ℚ A] : expScale (0 : A) = 1 := by
  rw [expScale, rescale_zero_apply, constantCoeff_exp, map_one]

/-- `∏ exp (tᵢ X) = exp ((∑ tᵢ) X)`. -/
theorem prod_expScale {A : Type*} [CommRing A] [Algebra ℚ A] {ι : Type*}
    (s : Finset ι) (t : ι → A) :
    ∏ i ∈ s, expScale (t i) = expScale (∑ i ∈ s, t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expScale_zero]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, expScale_add]

/-- If `W` has degree at most `d ≤ N`, then the `N`-th coefficient of `W * exp (ℓ X)` is a
multiple of `ℓ ^ (N - d)`. -/
theorem coeff_mul_expScale_mem {A : Type*} [CommRing A] [Algebra ℚ A] {d N : ℕ} {W : A⟦X⟧}
    (hW : DegLE d W) (hdN : d ≤ N) (ℓ : A) :
    coeff N (W * expScale ℓ) ∈ Ideal.span {ℓ ^ (N - d)} := by
  rw [coeff_mul]
  refine Ideal.sum_mem _ fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  by_cases h1 : d < p.1
  · rw [hW _ h1, zero_mul]
    exact Ideal.zero_mem _
  · rw [coeff_expScale]
    have hp2 : p.2 = (N - d) + (p.2 - (N - d)) := by omega
    rw [hp2, pow_add]
    refine Ideal.mul_mem_left _ _ ?_
    rw [mul_comm, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)


/-- Constant coefficient of a rescaled image of a rational power series. -/
theorem constantCoeff_rescale_map {A : Type*} [CommRing A] [Algebra ℚ A] (y : A) (u : ℚ⟦X⟧) :
    constantCoeff (rescale y (map (algebraMap ℚ A) u)) = algebraMap ℚ A (constantCoeff u) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul, coeff_map,
    coeff_zero_eq_constantCoeff_apply]

/-- Tensor step: given, for each `i`, one-variable data `gᵢ = Pᵢ + Qᵢ eˣ` with `Pᵢ, Qᵢ` of
degree `≤ aᵢ` and `gᵢ = X^(2aᵢ+1) + O(X^(2aᵢ+2))`, the product `∏ tᵢ^(2aᵢ+1)` lies in the
ideal generated by `(x + ∑_{i∈S} tᵢ)^(∑ aᵢ + #ι)` for `S ⊆ ι`. -/
theorem prod_pow_mem_span_of_oneVar {A : Type*} [CommRing A] [Algebra ℚ A] {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) (P Q : ι → ℚ⟦X⟧) (hP : ∀ i, DegLE (a i) (P i)) (hQ : ∀ i, DegLE (a i) (Q i))
    (hdvd : ∀ i, X ^ (2 * a i + 1) ∣ P i + Q i * exp ℚ)
    (hlead : ∀ i, coeff (2 * a i + 1) (P i + Q i * exp ℚ) = 1) (x : A) (t : ι → A) :
    ∏ i, t i ^ (2 * a i + 1) ∈ Ideal.span (Set.range fun S : Finset ι =>
      (x + ∑ i ∈ S, t i) ^ (∑ i, a i + Fintype.card ι)) := by
  let φ : ι → ℚ⟦X⟧ →+* A⟦X⟧ := fun i => (rescale (t i)).comp (map (algebraMap ℚ A))
  let g : ι → ℚ⟦X⟧ := fun i => P i + Q i * exp ℚ
  let D : ℕ := ∑ i, (2 * a i + 1)
  let H : A⟦X⟧ := expScale x * ∏ i, φ i (g i)
  -- Claim 1: the `D`-th coefficient of `H` is the target monomial.
  have hclaim1 : coeff D H = ∏ i, t i ^ (2 * a i + 1) := by
    choose u hu using hdvd
    have hu0 : ∀ i, constantCoeff (u i) = 1 := by
      intro i
      have h := hlead i
      rw [hu i, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        coeff_zero_eq_constantCoeff_apply] at h
      exact h
    have hφg : ∀ i, φ i (g i) = C (t i ^ (2 * a i + 1)) * X ^ (2 * a i + 1) * φ i (u i) := by
      intro i
      change φ i (P i + Q i * exp ℚ) = _
      rw [hu i, map_mul, map_pow]
      simp only [φ, RingHom.comp_apply, map_X, rescale_X, mul_pow, map_pow]
    have hprod : ∏ i, φ i (g i) =
        X ^ D * (C (∏ i, t i ^ (2 * a i + 1)) * ∏ i, φ i (u i)) := by
      simp only [hφg, Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum, D]
      ring
    have hconst : constantCoeff (expScale x * ∏ i, φ i (u i)) = 1 := by
      have hφu : ∀ i, constantCoeff (φ i (u i)) = 1 := by
        intro i
        change constantCoeff (rescale (t i) (map (algebraMap ℚ A) (u i))) = 1
        rw [constantCoeff_rescale_map, hu0, map_one]
      have hE : constantCoeff (expScale x) = 1 := by
        rw [← coeff_zero_eq_constantCoeff_apply, coeff_expScale, Nat.factorial_zero,
          Nat.cast_one, div_one, map_one, pow_zero, mul_one]
      rw [map_mul, map_prod, hE, one_mul]
      exact Finset.prod_eq_one fun i _ => hφu i
    have hH : H = X ^ D * (C (∏ i, t i ^ (2 * a i + 1)) * (expScale x * ∏ i, φ i (u i))) := by
      simp only [H, hprod]
      ring
    rw [hH, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_C_mul,
      coeff_zero_eq_constantCoeff_apply, hconst, mul_one]
  -- Claim 2: the `D`-th coefficient of `H` lies in the ideal.
  have hφexp : ∀ i, φ i (exp ℚ) = expScale (t i) := by
    intro i
    change rescale (t i) (map (algebraMap ℚ A) (exp ℚ)) = _
    rw [map_exp]
    rfl
  have hexpand : H = ∑ S ∈ (Finset.univ : Finset ι).powerset,
      ((∏ i ∈ S, φ i (Q i)) * ∏ i ∈ Finset.univ \ S, φ i (P i)) *
        expScale (x + ∑ i ∈ S, t i) := by
    have hφg : ∀ i, φ i (g i) = φ i (Q i) * expScale (t i) + φ i (P i) := by
      intro i
      change φ i (P i + Q i * exp ℚ) = _
      rw [map_add, map_mul, hφexp, add_comm]
    simp only [H, hφg, Finset.prod_add, Finset.mul_sum, Finset.prod_mul_distrib,
      prod_expScale, ← expScale_add]
    refine Finset.sum_congr rfl fun S _ => ?_
    ring
  have hclaim2 : coeff D H ∈ Ideal.span (Set.range fun S : Finset ι =>
      (x + ∑ i ∈ S, t i) ^ (∑ i, a i + Fintype.card ι)) := by
    rw [hexpand, map_sum]
    refine Ideal.sum_mem _ fun S _ => ?_
    have hdeg : DegLE (∑ i, a i)
        ((∏ i ∈ S, φ i (Q i)) * ∏ i ∈ Finset.univ \ S, φ i (P i)) := by
      have h := degLE_mul
        (degLE_prod S a (fun i => φ i (Q i)) fun i _ => degLE_rescale_map (hQ i) (t i))
        (degLE_prod (Finset.univ \ S) a (fun i => φ i (P i))
          fun i _ => degLE_rescale_map (hP i) (t i))
      rwa [add_comm, Finset.sum_sdiff (Finset.subset_univ S)] at h
    have hle : ∑ i, a i ≤ D := by
      simp only [D]
      exact Finset.sum_le_sum fun i _ => by omega
    have hD : D - ∑ i, a i = ∑ i, a i + Fintype.card ι := by
      simp only [D, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
        mul_one, ← Finset.mul_sum]
      omega
    have hmem := coeff_mul_expScale_mem hdeg hle (x + ∑ i ∈ S, t i)
    rw [hD] at hmem
    refine Ideal.span_mono ?_ hmem
    rw [Set.singleton_subset_iff]
    exact ⟨S, rfl⟩
  rw [← hclaim1]
  exact hclaim2


/-- Degree bounds are preserved by addition. -/
theorem degLE_add {R : Type*} [CommRing R] {d : ℕ} {φ ψ : R⟦X⟧} (hφ : DegLE d φ) (hψ : DegLE d ψ) :
    DegLE d (φ + ψ) := by
  intro j hj
  rw [map_add, hφ j hj, hψ j hj, add_zero]

/-- Degree bounds are preserved by scalar multiplication. -/
theorem degLE_smul {R : Type*} [CommRing R] {d : ℕ} {φ : R⟦X⟧} (hφ : DegLE d φ) (c : R) :
    DegLE d (c • φ) := by
  intro j hj
  rw [map_smul, hφ j hj, smul_zero]

/-- The zero power series has every degree bound. -/
theorem degLE_zero_series {R : Type*} [CommRing R] (d : ℕ) : DegLE d (0 : R⟦X⟧) := by
  intro j _
  rw [map_zero]

/-- `c Xᵏ` has degree at most `d` when `k ≤ d`. -/
theorem degLE_C_mul_X_pow {R : Type*} [CommRing R] {d k : ℕ} (hk : k ≤ d) (c : R) :
    DegLE d (C c * X ^ k) := by
  intro j hj
  rw [coeff_C_mul_X_pow, if_neg (by omega)]

-- Ground truth for `DegLE`: `X²` has degree at most `2` but not at most `1`.
example : DegLE 2 (X ^ 2 : ℚ⟦X⟧) := by
  simpa using degLE_C_mul_X_pow (d := 2) le_rfl (1 : ℚ)

example : ¬ DegLE 1 (X ^ 2 : ℚ⟦X⟧) := fun h => by
  simpa using h 2 (by norm_num)

/-- The `n`-th coefficient of `exp (y X) * c Xᵏ` (with `k ≤ n`) is `c yⁿ⁻ᵏ / (n-k)!`. -/
theorem coeff_expScale_mul_C_mul_X_pow {A : Type*} [CommRing A] [Algebra ℚ A] (y c : A)
    {k n : ℕ} (hk : k ≤ n) :
    coeff n (expScale y * (C c * X ^ k)) =
      c * (algebraMap ℚ A (1 / (n - k).factorial) * y ^ (n - k)) := by
  rw [show expScale y * (C c * X ^ k) = X ^ k * (C c * expScale y) by ring, coeff_X_pow_mul',
    if_pos hk, coeff_C_mul, coeff_expScale]

/-- Mapping `q Xᵏ` from `ℚ⟦X⟧` to `A⟦X⟧`. -/
theorem map_C_mul_X_pow {A : Type*} [CommRing A] [Algebra ℚ A] (q : ℚ) (k : ℕ) :
    map (algebraMap ℚ A) (C q * X ^ k) = C (algebraMap ℚ A q) * X ^ k := by
  simp only [_root_.map_mul, _root_.map_pow, map_C, map_X]

/-- `exp = exp (1 X)`. -/
theorem exp_eq_expScale_one (A : Type*) [CommRing A] [Algebra ℚ A] : exp A = expScale (1 : A) := by
  rw [expScale, rescale_one, RingHom.id_apply]

/-- `m! * (1 / m!) = 1` in any `ℚ`-algebra. -/
theorem factorial_mul_inv_factorial {A : Type*} [CommRing A] [Algebra ℚ A] (m : ℕ) :
    algebraMap ℚ A (m.factorial : ℚ) * algebraMap ℚ A (1 / m.factorial) = 1 := by
  rw [← _root_.map_mul, mul_one_div_cancel (by exact_mod_cast m.factorial_ne_zero), _root_.map_one]

/-- The one-variable generators `Y^(2a+1-k)` and `(Y+1)^(2a+1-k)`, `k ≤ a`, in `ℚ[Y]`
(dehomogenized `t^k t_0^(2a+1-k)` and `t^k (t_0+t)^(2a+1-k)` at `t_0 = Y`, `t = 1`). -/
def oneVarGens (a : ℕ) : Set (Polynomial ℚ) :=
  {f | ∃ k ≤ a, f = Polynomial.X ^ (2 * a + 1 - k) ∨ f = (Polynomial.X + 1) ^ (2 * a + 1 - k)}

-- Ground truth for `oneVarGens`: for `a = 1` (`2a+1 = 3`) it contains `Y³` and `(Y+1)²`.
example : (Polynomial.X ^ 3 : Polynomial ℚ) ∈ oneVarGens 1 := ⟨0, Nat.zero_le 1, Or.inl rfl⟩

example : ((Polynomial.X + 1) ^ 2 : Polynomial ℚ) ∈ oneVarGens 1 := ⟨1, le_rfl, Or.inr rfl⟩

/-- Every `f` in the `ℚ`-span of `oneVarGens a` is the `(2a+1)`-th coefficient of
`exp (Y X) * (P + Q eˣ)` for rational power series `P, Q` of degree `≤ a`. -/
theorem realizable_of_mem_span (a : ℕ) {f : Polynomial ℚ}
    (hf : f ∈ Submodule.span ℚ (oneVarGens a)) :
    ∃ P Q : ℚ⟦X⟧, DegLE a P ∧ DegLE a Q ∧
      f = coeff (2 * a + 1)
        (expScale (Polynomial.X : Polynomial ℚ) *
          map (algebraMap ℚ (Polynomial ℚ)) (P + Q * exp ℚ)) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k, hk, hf | hf⟩ := hf
    · refine ⟨C ((2 * a + 1 - k).factorial : ℚ) * X ^ k, 0, degLE_C_mul_X_pow hk _,
        degLE_zero_series a, ?_⟩
      rw [zero_mul, add_zero, map_C_mul_X_pow, coeff_expScale_mul_C_mul_X_pow _ _ (by omega),
        ← mul_assoc, factorial_mul_inv_factorial, one_mul, hf]
    · refine ⟨0, C ((2 * a + 1 - k).factorial : ℚ) * X ^ k, degLE_zero_series a,
        degLE_C_mul_X_pow hk _, ?_⟩
      rw [zero_add, _root_.map_mul (map (algebraMap ℚ (Polynomial ℚ))), map_C_mul_X_pow, map_exp,
        exp_eq_expScale_one,
        show ∀ u v w : (Polynomial ℚ)⟦X⟧, u * (v * w) = (u * w) * v from fun u v w => by ring,
        expScale_add, coeff_expScale_mul_C_mul_X_pow _ _ (by omega),
        ← mul_assoc, factorial_mul_inv_factorial, one_mul, hf]
  | zero => exact ⟨0, 0, degLE_zero_series a, degLE_zero_series a, by simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨P₁, Q₁, hP₁, hQ₁, rfl⟩ := hf
    obtain ⟨P₂, Q₂, hP₂, hQ₂, rfl⟩ := hg
    refine ⟨P₁ + P₂, Q₁ + Q₂, degLE_add hP₁ hP₂, degLE_add hQ₁ hQ₂, ?_⟩
    rw [← map_add]
    congr 1
    rw [← mul_add, ← map_add]
    ring_nf
  | smul c f _ hf =>
    obtain ⟨P, Q, hP, hQ, rfl⟩ := hf
    refine ⟨c • P, c • Q, degLE_smul hP c, degLE_smul hQ c, ?_⟩
    rw [smul_mul_assoc, ← smul_add, smul_eq_C_mul,
      _root_.map_mul (map (algebraMap ℚ (Polynomial ℚ))),
      map_C, mul_left_comm, coeff_C_mul, Algebra.smul_def]


/-- For `j ≤ 2a+1`, `(Y+1)^j Y^(2a+1-j)` lies in the `ℚ`-span of `oneVarGens a`. -/
theorem pow_mem_span_oneVarGens (a j : ℕ) (hj : j ≤ 2 * a + 1) :
    (Polynomial.X + 1) ^ j * Polynomial.X ^ (2 * a + 1 - j) ∈
      Submodule.span ℚ (oneVarGens a) := by
  set Y : Polynomial ℚ := Polynomial.X with hY
  by_cases hja : j ≤ a
  · rw [add_pow, Finset.sum_mul]
    refine Submodule.sum_mem _ fun i hi => ?_
    have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hterm : Y ^ i * 1 ^ (j - i) * ((j.choose i : ℕ) : Polynomial ℚ) * Y ^ (2 * a + 1 - j) =
        (j.choose i : ℤ) • Y ^ (2 * a + 1 - (j - i)) := by
      rw [zsmul_eq_mul, show 2 * a + 1 - (j - i) = i + (2 * a + 1 - j) by omega, pow_add]
      push_cast
      ring
    rw [hterm]
    exact zsmul_mem (Submodule.subset_span
      (show _ ∈ oneVarGens a from ⟨j - i, by omega, Or.inl rfl⟩)) _
  · have hY1 : Y ^ (2 * a + 1 - j) = ((Y + 1) + (-1)) ^ (2 * a + 1 - j) := by ring
    rw [hY1, add_pow (Y + 1) (-1), Finset.mul_sum]
    refine Submodule.sum_mem _ fun i hi => ?_
    have hi' : i ≤ 2 * a + 1 - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hterm : (Y + 1) ^ j * ((Y + 1) ^ i * (-1) ^ (2 * a + 1 - j - i) *
        (((2 * a + 1 - j).choose i : ℕ) : Polynomial ℚ)) =
        ((-1) ^ (2 * a + 1 - j - i) * ((2 * a + 1 - j).choose i : ℤ)) •
          (Y + 1) ^ (2 * a + 1 - (2 * a + 1 - j - i)) := by
      rw [zsmul_eq_mul, show 2 * a + 1 - (2 * a + 1 - j - i) = j + i by omega, pow_add]
      push_cast
      ring
    rw [hterm]
    exact zsmul_mem (Submodule.subset_span
      (show _ ∈ oneVarGens a from ⟨2 * a + 1 - j - i, by omega, Or.inr rfl⟩)) _

/-- One-variable binomial step: `1 = ((Y+1) - Y)^(2a+1)` lies in the span of `oneVarGens a`;
the homogeneous form is `t^(2a+1) ∈ ⟨t₀^(a+1), (t₀+t)^(a+1)⟩` (the `r = 1` case in the paper). -/
theorem one_mem_span_oneVarGens (a : ℕ) : (1 : Polynomial ℚ) ∈ Submodule.span ℚ (oneVarGens a) := by
  set Y : Polynomial ℚ := Polynomial.X with hY
  have h1 : (1 : Polynomial ℚ) = ((Y + 1) + (-Y)) ^ (2 * a + 1) := by ring
  rw [h1, add_pow]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hm' : m ≤ 2 * a + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hterm : (Y + 1) ^ m * (-Y) ^ (2 * a + 1 - m) * (((2 * a + 1).choose m : ℕ) : Polynomial ℚ) =
      ((-1) ^ (2 * a + 1 - m) * ((2 * a + 1).choose m : ℤ)) •
        ((Y + 1) ^ m * Y ^ (2 * a + 1 - m)) := by
    rw [zsmul_eq_mul, neg_pow]
    push_cast
    ring
  rw [hterm]
  exact zsmul_mem (pow_mem_span_oneVarGens a m hm') _


/-- Coefficient extraction: the `Y^(n-b)` coefficient of the `n`-th coefficient of
`exp (Y X) * g` equals `g_b / (n-b)!`. -/
theorem polyCoeff_coeff_expScale_X_mul (g : ℚ⟦X⟧) {n b : ℕ} (hb : b ≤ n) :
    Polynomial.coeff (coeff n (expScale (Polynomial.X : Polynomial ℚ) *
      map (algebraMap ℚ (Polynomial ℚ)) g)) (n - b) = 1 / (n - b).factorial * coeff b g := by
  have hterm : ∀ p : ℕ × ℕ, coeff p.1 (expScale (Polynomial.X : Polynomial ℚ)) *
      coeff p.2 (map (algebraMap ℚ (Polynomial ℚ)) g) =
      Polynomial.C (1 / p.1.factorial * coeff p.2 g) * Polynomial.X ^ p.1 := by
    intro p
    rw [coeff_expScale, coeff_map, Polynomial.algebraMap_eq, _root_.map_mul]
    ring
  rw [coeff_mul, Polynomial.finsetSum_coeff]
  simp only [hterm, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single (n - b, b)]
  · rw [if_pos rfl]
  · intro p hp hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [if_neg]
    intro h
    exact hne (Prod.ext h.symm (by omega))
  · intro h
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega)) h

/-- One-variable Hermite–Padé data: there are rational power series `P, Q` of degree `≤ a`
with `P + Q eˣ = X^(2a+1) + O(X^(2a+2))`. -/
theorem exists_oneVar (a : ℕ) : ∃ P Q : ℚ⟦X⟧, DegLE a P ∧ DegLE a Q ∧
    X ^ (2 * a + 1) ∣ P + Q * exp ℚ ∧ coeff (2 * a + 1) (P + Q * exp ℚ) = 1 := by
  obtain ⟨P, Q, hP, hQ, h⟩ := realizable_of_mem_span a (one_mem_span_oneVarGens a)
  have hc : ∀ b ≤ 2 * a + 1, coeff b (P + Q * exp ℚ) =
      if b = 2 * a + 1 then 1 else 0 := by
    intro b hb
    have h' := congrArg (fun f : Polynomial ℚ => f.coeff (2 * a + 1 - b)) h
    simp only [polyCoeff_coeff_expScale_X_mul _ hb, Polynomial.coeff_one] at h'
    by_cases hbn : b = 2 * a + 1
    · subst hbn
      rw [Nat.sub_self, if_pos rfl, Nat.factorial_zero, Nat.cast_one, div_one, one_mul] at h'
      rw [if_pos rfl, ← h']
    · rw [if_neg (by omega)] at h'
      rw [if_neg hbn]
      have hfac : (1 / ((2 * a + 1 - b).factorial : ℚ)) ≠ 0 := by
        have := Nat.factorial_ne_zero (2 * a + 1 - b)
        positivity
      exact (mul_eq_zero.mp h'.symm).resolve_left hfac
  refine ⟨P, Q, hP, hQ, ?_, ?_⟩
  · rw [X_pow_dvd_iff]
    intro m hm
    rw [hc m hm.le, if_neg hm.ne]
  · rw [hc _ le_rfl, if_pos rfl]



/-- Generalized conjecture over any commutative `ℚ`-algebra: for `a : ι → ℕ`, elements `x`
and `t : ι → A`, `∏ tᵢ^(2aᵢ+1) ∈ ⟨(x + ∑_{i∈S} tᵢ)^(∑ aᵢ + #ι) : S ⊆ ι⟩`. -/
theorem prod_pow_mem_span_pow_add_sum {A : Type*} [CommRing A] [Algebra ℚ A] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (a : ι → ℕ) (x : A) (t : ι → A) :
    ∏ i, t i ^ (2 * a i + 1) ∈ Ideal.span (Set.range fun S : Finset ι =>
      (x + ∑ i ∈ S, t i) ^ (∑ i, a i + Fintype.card ι)) := by
  choose P Q hP hQ hdvd hlead using fun i => exists_oneVar (a i)
  exact prod_pow_mem_span_of_oneVar a P Q hP hQ hdvd hlead x t

open MvPolynomial in
/-- Jun's ideal `I_r^{(d)} = ⟨(t_0 + t_S)^d : S ⊆ [r]⟩ ⊆ K[t_0, …, t_r]`, with `t_0 = X none`
and `t_{i+1} = X (some i)` (all `2^r` subsets, `S = ∅` giving `t_0^d`). -/
noncomputable def symIdeal (K : Type*) [Field K] (r d : ℕ) :
    Ideal (MvPolynomial (Option (Fin r)) K) :=
  Ideal.span (Set.range fun S : Finset (Fin r) => (X none + ∑ i ∈ S, X (some i)) ^ d)

open MvPolynomial in
-- Ground truth for `symIdeal`: `S = ∅` gives `t₀^d`, `S = [2]` gives `(t₀ + t₁ + t₂)^d`.
example (d : ℕ) : (X none ^ d : MvPolynomial (Option (Fin 2)) ℚ) ∈ symIdeal ℚ 2 d :=
  Ideal.subset_span ⟨∅, by simp⟩

open MvPolynomial in
example (d : ℕ) :
    ((X none + X (some 0) + X (some 1)) ^ d : MvPolynomial (Option (Fin 2)) ℚ) ∈ symIdeal ℚ 2 d :=
  Ideal.subset_span ⟨Finset.univ, by simp [Fin.sum_univ_two, add_assoc]⟩

open MvPolynomial in
/-- Non-vacuity: for `d ≥ 1` the ideal `I_r^{(d)}` is proper (all generators have zero
constant term), so membership in it is a genuine constraint. -/
theorem symIdeal_ne_top (K : Type*) [Field K] (r d : ℕ) (hd : 1 ≤ d) : symIdeal K r d ≠ ⊤ := by
  intro htop
  have hle : symIdeal K r d ≤
      RingHom.ker (constantCoeff : MvPolynomial (Option (Fin r)) K →+* K) := by
    rw [symIdeal, Ideal.span_le]
    rintro _ ⟨S, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, map_pow, map_add, map_sum, constantCoeff_X]
    simp only [constantCoeff_X, Finset.sum_const_zero, add_zero]
    exact zero_pow (by omega)
  have h1 := hle (htop ▸ Submodule.mem_top : (1 : MvPolynomial (Option (Fin r)) K) ∈ symIdeal K r d)
  rw [RingHom.mem_ker, map_one] at h1
  exact one_ne_zero h1

open MvPolynomial in
/-- Generalization of Jun's conjecture (free unequal exponents): over a field of characteristic
zero, for every `r` and `a : Fin r → ℕ`, `∏ tᵢ^(2aᵢ+1) ∈ I_r^{(∑ aᵢ + r)}`. -/
theorem prod_X_pow_mem_symIdeal (K : Type*) [Field K] [CharZero K] (r : ℕ) (a : Fin r → ℕ) :
    (∏ i : Fin r, X (some i) ^ (2 * a i + 1) : MvPolynomial (Option (Fin r)) K) ∈
      symIdeal K r (∑ i, a i + r) := by
  have h := prod_pow_mem_span_pow_add_sum a (X none : MvPolynomial (Option (Fin r)) K)
    (fun i => X (some i))
  rwa [Fintype.card_fin] at h

open MvPolynomial in
/-- Jun, arXiv:2112.10207, Conjecture `Conj:more variables` (Sec. 5): over a field `K` of
characteristic zero, for `r ≥ 2` and `n ≥ 1`, `(t_1 ⋯ t_r)^(2n-1) ∈ I_r^{(nr)}`.
The hypothesis `r ≥ 2` is kept to mirror the source; the proof does not use it. -/
theorem conj_more_variables (K : Type*) [Field K] [CharZero K] (r n : ℕ) (_hr : 2 ≤ r)
    (hn : 1 ≤ n) :
    (∏ i : Fin r, X (some i) : MvPolynomial (Option (Fin r)) K) ^ (2 * n - 1) ∈
      symIdeal K r (n * r) := by
  have h := prod_X_pow_mem_symIdeal K r (fun _ => n - 1)
  rw [Finset.prod_pow, show 2 * (n - 1) + 1 = 2 * n - 1 by omega, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, show r * (n - 1) + r = n * r by
      cases n with
      | zero => omega
      | succ m => simp only [Nat.add_sub_cancel]; ring] at h
  exact h

open MvPolynomial in
-- Satisfiability of the hypotheses at the paper's worked example `r = 2`, `n = 2`:
-- `(t₁ t₂)³ ∈ I_2^{(4)}` (the paper's identity `aδ⁴ + b(δ+x)⁴ + c(δ+y)⁴ + d(δ+x+y)⁴ = (xy)³`).
example : ((X (some 0) * X (some 1)) ^ 3 : MvPolynomial (Option (Fin 2)) ℚ) ∈ symIdeal ℚ 2 4 := by
  simpa [Fin.prod_univ_two] using conj_more_variables ℚ 2 2 le_rfl (by norm_num)

end SymmetricIdealNonPrimality
