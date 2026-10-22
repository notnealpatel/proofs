/-
# A finite copartition nonnegativity case

Haijun Li, "Further results on non-negativity conjectures for copartition
products", arXiv:2609.16913, Conjecture 1.2 (Burson-Eichhorn, Ann. Comb. 29
(2025), Conjecture 5.3) and diagonal reduction Theorem 1.3.
The formal power-series quotients use unit inverses. An explicit polynomial
with nonnegative coefficients gives
`D_{2,2}(x) = P(x)/((1-x^4)(1-x^10))`.
The certificate extends to `G_{2,2,M}` for every `M ≥ 2`; substitution
`x = q^b` gives coefficientwise nonnegativity of `g_{2b,b,3b}(2,M;q)`
for every `b ≥ 1`, `M ≥ 2`. This is a special case, not the full conjecture;
nonnegativity, rather than strict positivity, is asserted.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.BursonEichhornCopartitionSmallest

open PowerSeries

/-! ## Definitions mirroring the source -/

/-- The finite `q`-Pochhammer symbol `(a; q)_n = ∏_{i=0}^{n-1} (1 - a q^i)` in
`ℤ⟦X⟧`. -/
noncomputable def qPoch (a q : ℤ⟦X⟧) (n : ℕ) : ℤ⟦X⟧ :=
  ∏ i ∈ Finset.range n, (1 - a * q ^ i)

/-- The numerator `(-x^{k+1}; x^{k+1})_{N+M-1}` of `G_{k,N,M}(x)`.
(The source has `N, M ≥ 1`, so the natural subtraction is exact there.) -/
noncomputable def numer (k N M : ℕ) : ℤ⟦X⟧ :=
  qPoch (-X ^ (k + 1)) (X ^ (k + 1)) (N + M - 1)

/-- The denominator `(-x^k; x^{k+1})_N (x; x^{k+1})_M` of `G_{k,N,M}(x)`. -/
noncomputable def denom (k N M : ℕ) : ℤ⟦X⟧ :=
  qPoch (-X ^ k) (X ^ (k + 1)) N * qPoch X (X ^ (k + 1)) M

/-- `G_{k,N,M}(x) = (-x^{k+1};x^{k+1})_{N+M-1} / ((-x^k;x^{k+1})_N (x;x^{k+1})_M)`
(arXiv:2609.16913, eq. (1.4)), as a formal power series over `ℤ`.  The
denominator has constant coefficient `1` whenever `1 ≤ k` (the source's
`k ∈ ℕ`), see `constantCoeff_denom`, so `invOfUnit _ 1` is its genuine
inverse there. -/
noncomputable def G (k N M : ℕ) : ℤ⟦X⟧ :=
  numer k N M * invOfUnit (denom k N M) 1

/-- The diagonal specialization `D_{k,N}(x) := G_{k,N,N}(x)`. -/
noncomputable def D (k N : ℕ) : ℤ⟦X⟧ := G k N N

/-! ## Basic facts about the definitions -/

/-- The constant coefficient of `(a; q)_n` is `1` when `a` has zero constant
coefficient. -/
theorem constantCoeff_qPoch (a q : ℤ⟦X⟧) (n : ℕ) (ha : constantCoeff a = 0) :
    constantCoeff (qPoch a q n) = 1 := by
  unfold qPoch
  rw [map_prod]
  exact Finset.prod_eq_one fun i _ => by simp [ha]

/-- For `1 ≤ k` the denominator of `G_{k,N,M}` has constant coefficient `1`. -/
theorem constantCoeff_denom (k N M : ℕ) (hk : 1 ≤ k) :
    constantCoeff (denom k N M) = 1 := by
  have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
  unfold denom
  rw [map_mul, constantCoeff_qPoch _ _ _ (by simp [hk0]),
    constantCoeff_qPoch _ _ _ (by simp)]
  rfl

/-- The defining relation `G_{k,N,M} · denominator = numerator` (for `1 ≤ k`). -/
theorem G_mul_denom (k N M : ℕ) (hk : 1 ≤ k) :
    G k N M * denom k N M = numer k N M := by
  have hinv : denom k N M * invOfUnit (denom k N M) 1 = 1 :=
    mul_invOfUnit _ _ (by rw [constantCoeff_denom k N M hk]; rfl)
  rw [G, mul_assoc, mul_comm (invOfUnit _ _), hinv, mul_one]

/-- `G_{k,N,M}` is the unique series `f` with `f · denominator = numerator`
(for `1 ≤ k`). -/
theorem eq_G_of_mul_denom (k N M : ℕ) (hk : 1 ≤ k) (f : ℤ⟦X⟧)
    (hf : f * denom k N M = numer k N M) : f = G k N M := by
  have hinv : denom k N M * invOfUnit (denom k N M) 1 = 1 :=
    mul_invOfUnit _ _ (by rw [constantCoeff_denom k N M hk]; rfl)
  calc f = f * (denom k N M * invOfUnit (denom k N M) 1) := by rw [hinv, mul_one]
    _ = G k N M := by rw [← mul_assoc, hf, G]

/-! ### Example: the case `(k, N, M) = (2, 2, 2)` unfolds to the displayed
quotient. -/

/-- The numerator of `D_{2,2}` is `(1+x^3)(1+x^6)(1+x^9)`. -/
theorem numer_two_two_two :
    numer 2 2 2 = (1 + X ^ 3) * (1 + X ^ 6) * (1 + X ^ 9) := by
  simp only [numer, qPoch, Finset.prod_range_succ, Finset.prod_range_zero]
  ring

/-- The denominator of `D_{2,2}` is `(1+x^2)(1+x^5)(1-x)(1-x^4)`. -/
theorem denom_two_two_two :
    denom 2 2 2 = (1 + X ^ 2) * (1 + X ^ 5) * (1 - X) * (1 - X ^ 4) := by
  simp only [denom, qPoch, Finset.prod_range_succ, Finset.prod_range_zero]
  ring

/-! ## Non-negativity toolkit -/

/-- A series over `ℤ` has non-negative coefficients. -/
def Nonneg (f : ℤ⟦X⟧) : Prop := ∀ n, 0 ≤ coeff n f

/-- `1` has non-negative coefficients. -/
theorem Nonneg.one : Nonneg 1 := fun n => by
  rw [coeff_one]; split_ifs <;> norm_num

/-- `x^d` has non-negative coefficients. -/
theorem Nonneg.X_pow (d : ℕ) : Nonneg (X ^ d) := fun n => by
  rw [coeff_X_pow]; split_ifs <;> norm_num

/-- `x` has non-negative coefficients. -/
theorem Nonneg.X : Nonneg X := fun n => by
  rw [coeff_X]; split_ifs <;> norm_num

/-- Non-negativity is closed under addition. -/
theorem Nonneg.add {f g : ℤ⟦X⟧} (hf : Nonneg f) (hg : Nonneg g) : Nonneg (f + g) :=
  fun n => by rw [map_add]; exact add_nonneg (hf n) (hg n)

/-- Non-negativity is closed under multiplication (Cauchy product). -/
theorem Nonneg.mul {f g : ℤ⟦X⟧} (hf : Nonneg f) (hg : Nonneg g) : Nonneg (f * g) :=
  fun n => by
    rw [coeff_mul]
    exact Finset.sum_nonneg fun p _ => mul_nonneg (hf p.1) (hg p.2)

/-- Non-negativity is preserved by doubling. -/
theorem Nonneg.two_mul {f : ℤ⟦X⟧} (hf : Nonneg f) : Nonneg (2 * f) := by
  rw [_root_.two_mul]; exact hf.add hf

/-- The geometric series `1/(1 - x^a) = ∑_{a ∣ n} x^n`. -/
noncomputable def geom (a : ℕ) : ℤ⟦X⟧ := mk fun n => if a ∣ n then 1 else 0

/-- The geometric series `∑_{a ∣ n} x^n` has non-negative coefficients. -/
theorem Nonneg.geom (a : ℕ) : Nonneg (geom a) := fun n => by
  rw [Candidates.BursonEichhornCopartitionSmallest.geom, coeff_mk]
  split_ifs <;> norm_num

/-- `geom a` inverts `1 - x^a` for `0 < a`. -/
theorem geom_mul_one_sub (a : ℕ) (ha : 0 < a) : geom a * (1 - X ^ a) = 1 := by
  ext n
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', geom, coeff_mk, coeff_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.not_le.mpr ha]
  · have hn0 : n ≠ 0 := hn.ne'
    by_cases hdvd : a ∣ n
    · have hle : a ≤ n := Nat.le_of_dvd hn hdvd
      have hdvd' : a ∣ n - a := Nat.dvd_sub hdvd dvd_rfl
      simp [hdvd, hle, hdvd', coeff_mk, hn0]
    · by_cases hle : a ≤ n
      · have hdvd' : ¬ a ∣ n - a := fun h => hdvd (by
          have hsum := Nat.dvd_add h (dvd_refl a)
          rwa [Nat.sub_add_cancel hle] at hsum)
        simp [hdvd, hle, hdvd', coeff_mk, hn0]
      · simp [hdvd, hle, hn0]

/-! ## The certificate for `D_{2,2}` -/

/-- The certificate numerator
`P(x) = 1+x+x^3+2x^4+2x^7+x^8+x^9+2x^10+x^11+x^12+2x^13+2x^16+x^17+x^19+x^20`
with `D_{2,2}(x) = P(x)/((1-x^4)(1-x^10))`. -/
noncomputable def certP : ℤ⟦X⟧ :=
  1 + X + X ^ 3 + 2 * X ^ 4 + 2 * X ^ 7 + X ^ 8 + X ^ 9 + 2 * X ^ 10 + X ^ 11 + X ^ 12
    + 2 * X ^ 13 + 2 * X ^ 16 + X ^ 17 + X ^ 19 + X ^ 20

/-- The certificate numerator `P(x)` has non-negative coefficients. -/
theorem Nonneg.certP : Nonneg certP := by
  unfold Candidates.BursonEichhornCopartitionSmallest.certP
  refine (((((((((((((Nonneg.one.add Nonneg.X).add (Nonneg.X_pow _)).add
    (Nonneg.X_pow _).two_mul).add (Nonneg.X_pow _).two_mul).add (Nonneg.X_pow _)).add
    (Nonneg.X_pow _)).add (Nonneg.X_pow _).two_mul).add (Nonneg.X_pow _)).add
    (Nonneg.X_pow _)).add (Nonneg.X_pow _).two_mul).add (Nonneg.X_pow _).two_mul).add
    (Nonneg.X_pow _)).add (Nonneg.X_pow _)).add (Nonneg.X_pow _)

/-- The polynomial certificate identity
`P(x)(1+x^2)(1+x^5)(1-x)(1-x^4) = (1+x^3)(1+x^6)(1+x^9)(1-x^4)(1-x^10)`. -/
theorem certP_identity :
    certP * ((1 + X ^ 2) * (1 + X ^ 5) * (1 - X) * (1 - X ^ 4))
      = (1 + X ^ 3) * (1 + X ^ 6) * (1 + X ^ 9) * (1 - X ^ 4) * (1 - X ^ 10) := by
  unfold certP
  ring

/-- `D_{2,2}(x) = P(x) · 1/(1-x^4) · 1/(1-x^10)`. -/
theorem D_two_two_eq : D 2 2 = certP * geom 4 * geom 10 := by
  symm
  apply eq_G_of_mul_denom 2 2 2 (by norm_num)
  rw [numer_two_two_two, denom_two_two_two]
  calc certP * geom 4 * geom 10 * ((1 + X ^ 2) * (1 + X ^ 5) * (1 - X) * (1 - X ^ 4))
      = (certP * ((1 + X ^ 2) * (1 + X ^ 5) * (1 - X) * (1 - X ^ 4))) * geom 4 * geom 10 := by
        ring
    _ = (1 + X ^ 3) * (1 + X ^ 6) * (1 + X ^ 9)
          * (geom 4 * (1 - X ^ 4)) * (geom 10 * (1 - X ^ 10)) := by
        rw [certP_identity]; ring
    _ = (1 + X ^ 3) * (1 + X ^ 6) * (1 + X ^ 9) := by
        rw [geom_mul_one_sub 4 (by norm_num), geom_mul_one_sub 10 (by norm_num)]; ring

/-! Example: the first coefficients of `D_{2,2}` are
`1, 1, 0, 1, 3, 1, 0, 3, 4, 2, 3, …`; the zero at degree `2` shows that
non-negativity, not strict positivity, is the right claim. -/

example : coeff 2 (D 2 2) = 0 := by
  rw [D_two_two_eq]
  simp [certP, coeff_mul, Finset.Nat.antidiagonal_succ, geom, coeff_X_pow, coeff_one, coeff_X]

example : coeff 4 (D 2 2) = 3 := by
  rw [D_two_two_eq]
  simp [certP, coeff_mul, Finset.Nat.antidiagonal_succ, geom, coeff_X_pow, coeff_one, coeff_X,
    map_ofNat]

/-- **Smallest open case of the Burson–Eichhorn finite conjecture.**
`D_{2,2}(x) = (1+x^3)(1+x^6)(1+x^9) / ((1+x^2)(1+x^5)(1-x)(1-x^4))` has
non-negative coefficients, i.e. `D_{2,2}(x) ∈ ℕ₀[[x]]`
(arXiv:2609.16913, Conjecture 1.2 via Theorem 1.3, case `k = 2`, `N = 2`,
listed there as open). -/
theorem D_two_two_nonneg (n : ℕ) : 0 ≤ coeff n (D 2 2) := by
  rw [D_two_two_eq]
  exact ((Nonneg.certP.mul (Nonneg.geom 4)).mul (Nonneg.geom 10)) n

/-! ## Extension along Theorem 1.3: `G_{2,2,M}(x) ∈ ℕ₀[[x]]` for all `M ≥ 2` -/

/-- The non-negative certificate for `G_{2,2,M}`:
`P(x)/((1-x^4)(1-x^10)) · ∏_{j=2}^{M-1} (1+x^{3(2+j)})/(1-x^{3j+1})`, the
second factor being the manifestly non-negative factor of Theorem 1.3. -/
noncomputable def certG (M : ℕ) : ℤ⟦X⟧ :=
  certP * geom 4 * geom 10 *
    ∏ j ∈ Finset.Ico 2 M, ((1 + X ^ (3 * (2 + j))) * geom (3 * j + 1))

/-- The certificate for `G_{2,2,M}` has non-negative coefficients. -/
theorem Nonneg.certG (M : ℕ) : Nonneg (certG M) := by
  unfold Candidates.BursonEichhornCopartitionSmallest.certG
  refine ((Nonneg.certP.mul (Nonneg.geom 4)).mul (Nonneg.geom 10)).mul ?_
  induction M with
  | zero => simpa using Nonneg.one
  | succ M ih =>
    rcases Nat.lt_or_ge M 2 with hM | hM
    · rw [Finset.Ico_eq_empty (by omega)]; simpa using Nonneg.one
    · rw [Finset.prod_Ico_succ_top hM]
      exact ih.mul ((Nonneg.one.add (Nonneg.X_pow _)).mul (Nonneg.geom _))

/-- The certificate satisfies the defining relation of `G_{2,2,M}` for `M ≥ 2`. -/
theorem certG_mul_denom (M : ℕ) (hM : 2 ≤ M) :
    certG M * denom 2 2 M = numer 2 2 M := by
  induction M, hM using Nat.le_induction with
  | base =>
    have hD : certP * geom 4 * geom 10 * denom 2 2 2 = numer 2 2 2 := by
      rw [← D_two_two_eq]; exact G_mul_denom 2 2 2 (by norm_num)
    simpa [certG] using hD
  | succ M hM ih =>
    have hnum : numer 2 2 (M + 1) = numer 2 2 M * (1 + X ^ (3 * (2 + M))) := by
      have hidx : 2 + (M + 1) - 1 = (2 + M - 1) + 1 := by omega
      simp only [numer, qPoch]
      rw [hidx, Finset.prod_range_succ]
      have hexp : 2 + M - 1 = M + 1 := by omega
      rw [hexp]; ring
    have hden : denom 2 2 (M + 1) = denom 2 2 M * (1 - X ^ (3 * M + 1)) := by
      simp only [denom, qPoch, Finset.prod_range_succ]
      ring
    have hcert : certG (M + 1) =
        certG M * ((1 + X ^ (3 * (2 + M))) * geom (3 * M + 1)) := by
      simp only [certG]
      rw [Finset.prod_Ico_succ_top hM]
      ring
    calc certG (M + 1) * denom 2 2 (M + 1)
        = (certG M * denom 2 2 M) * (1 + X ^ (3 * (2 + M)))
            * (geom (3 * M + 1) * (1 - X ^ (3 * M + 1))) := by
          rw [hcert, hden]; ring
      _ = numer 2 2 (M + 1) := by
          rw [ih, geom_mul_one_sub _ (by omega), hnum, mul_one]

/-- `G_{2,2,M}(x) = certG M` for every `M ≥ 2`. -/
theorem G_two_two_eq (M : ℕ) (hM : 2 ≤ M) : G 2 2 M = certG M :=
  (eq_G_of_mul_denom 2 2 M (by norm_num) _ (certG_mul_denom M hM)).symm

/-- **Burson–Eichhorn finite conjecture for `k = 2`, `N = 2`, all `M ≥ 2`.**
`G_{2,2,M}(x) = (-x^3;x^3)_{M+1} / ((-x^2;x^3)_2 (x;x^3)_M)` has non-negative
coefficients for every `M ≥ 2`; with `x = q^b` this is the case
`(a, b, m, N, M) = (2b, b, 3b, 2, M)` of arXiv:2609.16913, Conjecture 1.2. -/
theorem G_two_two_nonneg (M : ℕ) (hM : 2 ≤ M) (n : ℕ) : 0 ≤ coeff n (G 2 2 M) := by
  rw [G_two_two_eq M hM]
  exact Nonneg.certG M n

/-! ## The original `q`-form: `g_{2b,b,3b}(2, M; q) ∈ ℕ₀[[q]]` for all `b ≥ 1`, `M ≥ 2` -/

/-- The source's finite copartition product
`g_{a,b,m}(N,M;q) = (-q^m;q^m)_{N+M-1} / ((-q^a;q^m)_N (q^b;q^m)_M)`
(arXiv:2609.16913, eq. (1.3)) as a series over `ℤ`.  For `1 ≤ a` and `1 ≤ b`
the denominator has constant coefficient `1` (`constantCoeff_gDenom`), so
`invOfUnit _ 1` is its genuine inverse. -/
noncomputable def g (a b m N M : ℕ) : ℤ⟦X⟧ :=
  qPoch (-X ^ m) (X ^ m) (N + M - 1) *
    invOfUnit (qPoch (-X ^ a) (X ^ m) N * qPoch (X ^ b) (X ^ m) M) 1

/-- The denominator of `g_{a,b,m}(N,M;q)` has constant coefficient `1` when
`1 ≤ a` and `1 ≤ b`. -/
theorem constantCoeff_gDenom (a b m N M : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    constantCoeff (qPoch (-X ^ a) (X ^ m) N * qPoch (X ^ b) (X ^ m) M) = 1 := by
  have ha0 : a ≠ 0 := Nat.one_le_iff_ne_zero.mp ha
  have hb0 : b ≠ 0 := Nat.one_le_iff_ne_zero.mp hb
  rw [map_mul, constantCoeff_qPoch _ _ _ (by simp [ha0]),
    constantCoeff_qPoch _ _ _ (by simp [hb0])]
  rfl

/-- `g_{a,b,m}(N,M)` is the unique series `f` with `f · denominator = numerator`
(for `1 ≤ a`, `1 ≤ b`). -/
theorem eq_g_of_mul_denom (a b m N M : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (f : ℤ⟦X⟧)
    (hf : f * (qPoch (-X ^ a) (X ^ m) N * qPoch (X ^ b) (X ^ m) M)
      = qPoch (-X ^ m) (X ^ m) (N + M - 1)) : f = g a b m N M := by
  set d := qPoch (-X ^ a) (X ^ m) N * qPoch (X ^ b) (X ^ m) M with hd
  have hinv : d * invOfUnit d 1 = 1 :=
    mul_invOfUnit _ _ (by rw [hd, constantCoeff_gDenom a b m N M ha hb]; rfl)
  calc f = f * (d * invOfUnit d 1) := by rw [hinv, mul_one]
    _ = g a b m N M := by rw [← mul_assoc, hf, g]

/-- Example: `G_{k,N,M}(x) = g_{k,1,k+1}(N,M;x)` (the substitution
`a = kb`, `x = q^b` at `b = 1`). -/
theorem G_eq_g (k N M : ℕ) : G k N M = g k 1 (k + 1) N M := by
  simp only [G, g, numer, denom, pow_one]

/-- The certificate polynomial `P(y)` in an arbitrary series `y`. -/
noncomputable def certPoly (Y : ℤ⟦X⟧) : ℤ⟦X⟧ :=
  1 + Y + Y ^ 3 + 2 * Y ^ 4 + 2 * Y ^ 7 + Y ^ 8 + Y ^ 9 + 2 * Y ^ 10 + Y ^ 11 + Y ^ 12
    + 2 * Y ^ 13 + 2 * Y ^ 16 + Y ^ 17 + Y ^ 19 + Y ^ 20

/-- `P(y)` has non-negative coefficients whenever `y` does. -/
theorem Nonneg.certPoly {Y : ℤ⟦X⟧} (hY : Nonneg Y) :
    Nonneg (Candidates.BursonEichhornCopartitionSmallest.certPoly Y) := by
  unfold Candidates.BursonEichhornCopartitionSmallest.certPoly
  have hp : ∀ e : ℕ, Nonneg (Y ^ e) := fun e => by
    induction e with
    | zero => simpa using Nonneg.one
    | succ e ih => rw [pow_succ]; exact ih.mul hY
  refine (((((((((((((Nonneg.one.add hY).add (hp _)).add
    (hp _).two_mul).add (hp _).two_mul).add (hp _)).add
    (hp _)).add (hp _).two_mul).add (hp _)).add
    (hp _)).add (hp _).two_mul).add (hp _).two_mul).add
    (hp _)).add (hp _)).add (hp _)

/-- The certificate identity in an arbitrary series `y`:
`P(y)(1+y^2)(1+y^5)(1-y)(1-y^4) = (1+y^3)(1+y^6)(1+y^9)(1-y^4)(1-y^10)`. -/
theorem certPoly_identity_aux (Y : ℤ⟦X⟧) :
    certPoly Y * ((1 + Y ^ 2) * (1 + Y ^ 5) * (1 - Y) * (1 - Y ^ 4))
      = (1 + Y ^ 3) * (1 + Y ^ 6) * (1 + Y ^ 9) * (1 - Y ^ 4) * (1 - Y ^ 10) := by
  unfold certPoly
  ring

/-- The non-negative certificate for `g_{2b,b,3b}(2,M;q)`. -/
noncomputable def certg (b M : ℕ) : ℤ⟦X⟧ :=
  certPoly (X ^ b) * geom (4 * b) * geom (10 * b) *
    ∏ j ∈ Finset.Ico 2 M, ((1 + X ^ (3 * b * (2 + j))) * geom (b * (3 * j + 1)))

/-- The certificate for `g_{2b,b,3b}(2,M)` has non-negative coefficients. -/
theorem Nonneg.certg (b M : ℕ) : Nonneg (certg b M) := by
  unfold Candidates.BursonEichhornCopartitionSmallest.certg
  refine (((Nonneg.certPoly (Nonneg.X_pow b)).mul (Nonneg.geom _)).mul
    (Nonneg.geom _)).mul ?_
  induction M with
  | zero => simpa using Nonneg.one
  | succ M ih =>
    rcases Nat.lt_or_ge M 2 with hM | hM
    · rw [Finset.Ico_eq_empty (by omega)]; simpa using Nonneg.one
    · rw [Finset.prod_Ico_succ_top hM]
      exact ih.mul ((Nonneg.one.add (Nonneg.X_pow _)).mul (Nonneg.geom _))

/-- The certificate satisfies the defining relation of `g_{2b,b,3b}(2,M)`. -/
theorem certg_mul_denom (b M : ℕ) (hb : 1 ≤ b) (hM : 2 ≤ M) :
    certg b M * (qPoch (-X ^ (2 * b)) (X ^ (3 * b)) 2 * qPoch (X ^ b) (X ^ (3 * b)) M)
      = qPoch (-X ^ (3 * b)) (X ^ (3 * b)) (2 + M - 1) := by
  induction M, hM using Nat.le_induction with
  | base =>
    have h4 : geom (4 * b) * (1 - X ^ (4 * b)) = 1 := geom_mul_one_sub _ (by omega)
    have h10 : geom (10 * b) * (1 - X ^ (10 * b)) = 1 := geom_mul_one_sub _ (by omega)
    have hid := certPoly_identity_aux (X ^ b)
    simp only [certg, qPoch, Finset.prod_range_succ, Finset.prod_range_zero,
      Finset.Ico_self, Finset.prod_empty]
    calc certPoly (X ^ b) * geom (4 * b) * geom (10 * b) * 1 *
          (1 * (1 - -X ^ (2 * b) * (X ^ (3 * b)) ^ 0) * (1 - -X ^ (2 * b) * (X ^ (3 * b)) ^ 1) *
            (1 * (1 - X ^ b * (X ^ (3 * b)) ^ 0) * (1 - X ^ b * (X ^ (3 * b)) ^ 1)))
        = (certPoly (X ^ b) * ((1 + (X ^ b) ^ 2) * (1 + (X ^ b) ^ 5) * (1 - X ^ b)
            * (1 - (X ^ b) ^ 4))) * geom (4 * b) * geom (10 * b) := by ring
      _ = (1 + (X ^ b) ^ 3) * (1 + (X ^ b) ^ 6) * (1 + (X ^ b) ^ 9)
            * (geom (4 * b) * (1 - X ^ (4 * b))) * (geom (10 * b) * (1 - X ^ (10 * b))) := by
          rw [hid]; ring
      _ = _ := by rw [h4, h10]; ring
  | succ M hM ih =>
    have hnum : qPoch (-X ^ (3 * b)) (X ^ (3 * b)) (2 + (M + 1) - 1)
        = qPoch (-X ^ (3 * b)) (X ^ (3 * b)) (2 + M - 1) * (1 + X ^ (3 * b * (2 + M))) := by
      have hidx : 2 + (M + 1) - 1 = (2 + M - 1) + 1 := by omega
      simp only [qPoch]
      rw [hidx, Finset.prod_range_succ]
      have hexp : 2 + M - 1 = M + 1 := by omega
      rw [hexp]; ring
    have hden : qPoch (X ^ b) (X ^ (3 * b)) (M + 1)
        = qPoch (X ^ b) (X ^ (3 * b)) M * (1 - X ^ (b * (3 * M + 1))) := by
      simp only [qPoch, Finset.prod_range_succ]
      ring
    have hcert : certg b (M + 1) =
        certg b M * ((1 + X ^ (3 * b * (2 + M))) * geom (b * (3 * M + 1))) := by
      simp only [certg]
      rw [Finset.prod_Ico_succ_top hM]
      ring
    have hpos : 0 < b * (3 * M + 1) := Nat.mul_pos (by omega) (by omega)
    calc certg b (M + 1) *
          (qPoch (-X ^ (2 * b)) (X ^ (3 * b)) 2 * qPoch (X ^ b) (X ^ (3 * b)) (M + 1))
        = (certg b M * (qPoch (-X ^ (2 * b)) (X ^ (3 * b)) 2 * qPoch (X ^ b) (X ^ (3 * b)) M))
            * (1 + X ^ (3 * b * (2 + M)))
            * (geom (b * (3 * M + 1)) * (1 - X ^ (b * (3 * M + 1)))) := by
          rw [hcert, hden]; ring
      _ = _ := by
          rw [ih, geom_mul_one_sub _ hpos, hnum, mul_one]

/-- **Burson–Eichhorn finite conjecture, case `(a, b, m, N) = (2b, b, 3b, 2)`.**
For every `b ≥ 1` and every `M ≥ 2`,
`g_{2b,b,3b}(2,M;q) = (-q^{3b};q^{3b})_{M+1} / ((-q^{2b};q^{3b})_2 (q^b;q^{3b})_M)`
has non-negative coefficients (arXiv:2609.16913, Conjecture 1.2 =
Burson–Eichhorn Conjecture 5.3, at `k = a/b = 2`, `N = 2`; open in the source). -/
theorem g_two_nonneg (b M : ℕ) (hb : 1 ≤ b) (hM : 2 ≤ M) (n : ℕ) :
    0 ≤ coeff n (g (2 * b) b (3 * b) 2 M) := by
  have heq : certg b M = g (2 * b) b (3 * b) 2 M :=
    eq_g_of_mul_denom _ _ _ _ _ (by omega) hb _ (certg_mul_denom b M hb hM)
  rw [← heq]
  exact Nonneg.certg b M n

end Candidates.BursonEichhornCopartitionSmallest
