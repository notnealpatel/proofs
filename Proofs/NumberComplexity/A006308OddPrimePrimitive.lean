/-
# A006308 — Somos: the coefficients of period polynomials are `p(p-1)/2`

Michael Somos's conjecture in OEIS A006308 (2020), using Sean A. Irvine's
period-polynomial definition (2017). The listed terms start at the odd prime
`p = 3` (offset 2).

For every odd prime `p`, the coefficient identity holds for every
primitive root `g` modulo `p²` (so the value is independent of `g`), and in
the more general form `neg_coeff_periodPoly` for every primitive `p²`-th root
of unity `ζ ∈ ℂ`.  The second equality of the comment,
`p(p-1)/2 = Σ_{k<p} (k³ mod p)`, is `sum_cube_mod_eq` below.

Proof outline.  `[x^(p-2)] f = e₂(h) = ((Σ h)² - Σ h²)/2`.  Writing
`S(M) = Σ_{k<p} ζ^((q+kp)M)`, orthogonality gives `S(M) = 0` if `p ∤ M` and
`S(M) = p` if `p² ∣ M`.  Then `Σ_k h_k = Σ_j S(q^j) = 0` and
`Σ_k h_k² = Σ_{j,j'} S(q^j + q^j')`.  Since `q` has order `p-1` modulo `p²`
and every `x ≡ 1 (mod p)` satisfies `x^p ≡ 1 (mod p²)`, the condition
`p ∣ q^j + q^j'` forces `p² ∣ q^j + q^j'` and holds for exactly one `j'`
(namely `q^j' = q^(j+(p-1)/2) = -q^j`).  So `Σ h_k² = p(p-1)`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A006308OddPrimePrimitive

open Polynomial Finset

/-! ## Definitions -/

/-- `ζ = exp(2πi/p²)`, the primitive `p²`-th root of unity of the entry. -/
noncomputable def zeta (p : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / ((p ^ 2 : ℕ) : ℂ))

/-- The Gauss period `h(p,k) = Σ_{j=0}^{p-2} ζ^((q + k p) q^j)` with `q = g^p`,
the exponent computed in `ℕ` exactly as written in the entry. -/
noncomputable def periodSum (p g : ℕ) (ζ : ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ range (p - 1), ζ ^ ((g ^ p + k * p) * (g ^ p) ^ j)

/-- The period polynomial `f(p,x) = Π_{k=0}^{p-1} (x - h(p,k))`. -/
noncomputable def periodPoly (p g : ℕ) (ζ : ℂ) : ℂ[X] :=
  ∏ k ∈ range p, (X - C (periodSum p g ζ k))

/-! ## Examples -/

/-- The listed terms are `p(p-1)/2` for the odd primes `p = 3, …, 101`. -/
example : [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73,
      79, 83, 89, 97, 101].map (fun p => p * (p - 1) / 2) =
    [3, 10, 21, 55, 78, 136, 171, 253, 406, 465, 666, 820, 903, 1081, 1378, 1711, 1830,
      2211, 2485, 2628, 3081, 3403, 3916, 4656, 5050] := by decide

/-- The A008837 form `Σ_{k<p} (k³ mod p)` of the same terms, for `p = 3, …, 101`. -/
example : [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73,
      79, 83, 89, 97, 101].map (fun p => ∑ k ∈ range p, k ^ 3 % p) =
    [3, 10, 21, 55, 78, 136, 171, 253, 406, 465, 666, 820, 903, 1081, 1378, 1711, 1830,
      2211, 2485, 2628, 3081, 3403, 3916, 4656, 5050] := by decide

/-- The hypotheses are satisfiable: `2` is a primitive root modulo `3² = 9`. -/
example : orderOf ((2 : ℕ) : ZMod (3 ^ 2)) = 3 * (3 - 1) := by
  rw [orderOf_eq_iff (by norm_num)]
  decide

/-- `ζ = exp(2πi/p²)` is a primitive `p²`-th root of unity. -/
theorem zeta_isPrimitiveRoot (p : ℕ) (hp : p ≠ 0) : IsPrimitiveRoot (zeta p) (p ^ 2) :=
  Complex.isPrimitiveRoot_exp (p ^ 2) (pow_ne_zero 2 hp)

/-! ## The polynomial identity `2 e₂ = (Σ a)² - Σ a²` -/

/-- The subleading coefficient of `Π_{k ≤ n} (X - a_k)` is `-Σ a_k`. -/
theorem coeff_prod_X_sub_C_succ_self {R : Type*} [CommRing R] [Nontrivial R] (a : ℕ → R)
    (n : ℕ) : (∏ k ∈ range (n + 1), (X - C (a k))).coeff n = -∑ k ∈ range (n + 1), a k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmon : (∏ k ∈ range (n + 1), (X - C (a k))).coeff (n + 1) = 1 := by
      have hm := (monic_prod_of_monic (range (n+1)) (fun k => X - C (a k))
        (fun k _ => monic_X_sub_C (a k)))
      have hdeg : (∏ k ∈ range (n + 1), (X - C (a k))).natDegree = n + 1 := by
        rw [natDegree_prod_of_monic _ _ (fun k _ => monic_X_sub_C (a k))]
        simp
      have hc := hm.coeff_natDegree
      rwa [hdeg] at hc
    rw [prod_range_succ, coeff_mul_X_sub_C, ih, hmon, sum_range_succ _ (n + 1)]
    ring

/-- Twice the coefficient of `X^n` in `Π_{k < n+2} (X - a_k)` is `(Σ a_k)² - Σ a_k²`. -/
theorem two_mul_coeff_prod_X_sub_C {R : Type*} [CommRing R] [Nontrivial R] (a : ℕ → R)
    (n : ℕ) : 2 * (∏ k ∈ range (n + 2), (X - C (a k))).coeff n =
      (∑ k ∈ range (n + 2), a k) ^ 2 - ∑ k ∈ range (n + 2), a k ^ 2 := by
  induction n with
  | zero =>
    simp only [zero_add, prod_range_succ, range_one, prod_singleton, mul_coeff_zero, coeff_sub,
      coeff_X_zero, coeff_C_zero, zero_sub, mul_neg, neg_mul, neg_neg, sum_range_succ,
      sum_singleton]
    ring
  | succ n ih =>
    rw [prod_range_succ, coeff_mul_X_sub_C, mul_sub, ih, coeff_prod_X_sub_C_succ_self,
      sum_range_succ _ (n + 2), sum_range_succ _ (n + 2)]
    ring

/-- In `ZMod (p^2)`, an element congruent to `1` modulo `p` has `p`-th power `1`. -/
theorem pow_prime_eq_one_of_dvd_sub_one (p : ℕ) {y : ZMod (p ^ 2)}
    (hy : (p : ZMod (p ^ 2)) ∣ y - 1) : y ^ p = 1 := by
  have h := dvd_sub_pow_of_dvd_sub hy 1
  have hp2 : ((p : ZMod (p ^ 2))) ^ (1 + 1) = 0 := by
    rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  rw [hp2, zero_dvd_iff, pow_one, one_pow, sub_eq_zero] at h
  exact h

/-- Kernel of reduction `ZMod (p^2) → ZMod p` is generated by `p`. -/
theorem dvd_of_castHom_eq_zero (p : ℕ) [Fact p.Prime] {z : ZMod (p ^ 2)}
    (hz : ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) z = 0) :
    (p : ZMod (p ^ 2)) ∣ z := by
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (Fact.out : p.Prime).ne_zero⟩
  rw [← ZMod.natCast_zmod_val z, map_natCast, ZMod.natCast_eq_zero_iff] at hz
  obtain ⟨c, hc⟩ := hz
  refine ⟨c, ?_⟩
  rw [← ZMod.natCast_zmod_val z, hc, Nat.cast_mul]

/-- If `y^(p-1) = 1` and `y ≡ 1 (mod p)` then `y = 1`. -/
theorem eq_one_of_pow_pred_eq_one (p : ℕ) [Fact p.Prime] {y : ZMod (p ^ 2)}
    (hy : (p : ZMod (p ^ 2)) ∣ y - 1) (hpred : y ^ (p - 1) = 1) : y = 1 := by
  have hpow := pow_prime_eq_one_of_dvd_sub_one p hy
  have hsplit : y ^ p = y ^ (p - 1) * y := by
    rw [← pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
  rw [hsplit, hpred, one_mul] at hpow
  exact hpow

/-- For an odd prime `p`, `p - 1` is even. -/
theorem even_pred_of_odd_prime (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) : Even (p - 1) :=
  Nat.Odd.sub_odd ((Fact.out : p.Prime).odd_of_ne_two hp2) odd_one

/-- For an odd prime `p`, `y² = 1` implies `y^(p-1) = 1`. -/
theorem pow_pred_eq_one_of_sq_eq_one (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {y : ZMod (p ^ 2)}
    (hy : y ^ 2 = 1) : y ^ (p - 1) = 1 := by
  obtain ⟨m, hm⟩ := even_pred_of_odd_prime p hp2
  rw [hm, ← two_mul, pow_mul, hy, one_pow]

/-- If `u^(p-1) = v^(p-1) = 1` in `ZMod (p²)` and `p ∣ u + v`, then `u + v = 0`. -/
theorem add_eq_zero_of_dvd_add (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {u v : ZMod (p ^ 2)}
    (hu : u ^ (p - 1) = 1) (hv : v ^ (p - 1) = 1) (hdvd : (p : ZMod (p ^ 2)) ∣ u + v) :
    u + v = 0 := by
  have hp := (Fact.out : p.Prime)
  have hsplit : u ^ (p - 2) * u = 1 := by
    rw [← pow_succ, ← hu]
    congr 1
    have := hp.two_le
    omega
  set y : ZMod (p ^ 2) := -(v * u ^ (p - 2)) with hy_def
  have hy1 : y - 1 = -(u ^ (p - 2)) * (u + v) := by
    rw [hy_def]; linear_combination hsplit
  have hdvd' : (p : ZMod (p ^ 2)) ∣ y - 1 := by
    rw [hy1]; exact Dvd.dvd.mul_left hdvd _
  have hev := even_pred_of_odd_prime p hp2
  have hypow : y ^ (p - 1) = 1 := by
    rw [hy_def, neg_pow, hev.neg_one_pow, one_mul, mul_pow, hv, one_mul, ← pow_mul,
      mul_comm, pow_mul, hu, one_pow]
  have hy : y = 1 := eq_one_of_pow_pred_eq_one p hdvd' hypow
  rw [hy_def] at hy
  linear_combination (-u) * hy - v * hsplit

/-- The square roots of `1` in `ZMod (p²)`, `p` an odd prime, are `±1`. -/
theorem eq_neg_one_of_sq_eq_one (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {y : ZMod (p ^ 2)}
    (hy : y ^ 2 = 1) (hne : y ≠ 1) : y = -1 := by
  set φ := ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) with hφ
  have hφy : φ y * φ y = 1 := by rw [← map_mul, ← sq, hy, map_one]
  rcases mul_self_eq_one_iff.mp hφy with h1 | h1
  · exfalso
    apply hne
    refine eq_one_of_pow_pred_eq_one p (dvd_of_castHom_eq_zero p ?_)
      (pow_pred_eq_one_of_sq_eq_one p hp2 hy)
    rw [map_sub, h1, map_one, sub_self]
  · have hneg : -y = 1 := by
      refine eq_one_of_pow_pred_eq_one p (dvd_of_castHom_eq_zero p ?_)
        (pow_pred_eq_one_of_sq_eq_one p hp2 (by rw [neg_sq, hy]))
      rw [map_sub, map_neg, h1, map_one, neg_neg, sub_self]
    linear_combination -hneg

/-- Orthogonality: `Σ_{k<p} ζ^((Q + k p) M) = 0` when `p ∤ M`. -/
theorem sum_pow_eq_zero_of_not_dvd (p : ℕ) [Fact p.Prime] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (p ^ 2))
    (Q M : ℕ) (hM : ¬ p ∣ M) : ∑ k ∈ range p, ζ ^ ((Q + k * p) * M) = 0 := by
  have hp := (Fact.out : p.Prime)
  set ω := ζ ^ (p * M) with hω
  have hterm : ∀ k ∈ range p, ζ ^ ((Q + k * p) * M) = ζ ^ (Q * M) * ω ^ k := by
    intro k _
    rw [hω, ← pow_mul, ← pow_add]
    congr 1
    ring
  rw [sum_congr rfl hterm, ← mul_sum]
  have hω1 : ω ≠ 1 := by
    rw [hω, Ne, hζ.pow_eq_one_iff_dvd, sq]
    exact fun h => hM (Nat.dvd_of_mul_dvd_mul_left hp.pos h)
  have hωp : ω ^ p = 1 := by
    rw [hω, ← pow_mul, hζ.pow_eq_one_iff_dvd]
    exact ⟨M, by ring⟩
  rw [geom_sum_eq hω1, hωp, sub_self, zero_div, mul_zero]

/-- `Σ_{k<p} ζ^((Q + k p) M) = p` when `p² ∣ M`. -/
theorem sum_pow_eq_of_sq_dvd (p : ℕ) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (p ^ 2))
    (Q M : ℕ) (hM : p ^ 2 ∣ M) : ∑ k ∈ range p, ζ ^ ((Q + k * p) * M) = p := by
  have hterm : ∀ k ∈ range p, ζ ^ ((Q + k * p) * M) = 1 := by
    intro k _
    rw [hζ.pow_eq_one_iff_dvd]
    exact Dvd.dvd.mul_left hM _
  rw [sum_congr rfl hterm]
  simp

/-! ## The primitive root `q = g^p` -/

/-- If `g` is a primitive root modulo `p²` then `q = g^p` has order `p - 1` modulo `p²`. -/
theorem orderOf_pow_prime (p g : ℕ) [Fact p.Prime]
    (hg : orderOf (g : ZMod (p ^ 2)) = p * (p - 1)) :
    orderOf ((g : ZMod (p ^ 2)) ^ p) = p - 1 := by
  have hp := (Fact.out : p.Prime)
  rw [orderOf_pow_of_dvd hp.ne_zero (hg ▸ dvd_mul_right p (p - 1)), hg,
    Nat.mul_div_cancel_left _ hp.pos]

/-- A primitive root `g` modulo `p²` is not divisible by `p`, nor is any `(g^p)^j`. -/
theorem not_dvd_pow (p g : ℕ) [Fact p.Prime] (hg : orderOf (g : ZMod (p ^ 2)) = p * (p - 1))
    (j : ℕ) : ¬ p ∣ (g ^ p) ^ j := by
  have hp := (Fact.out : p.Prime)
  have hpos : 0 < orderOf (g : ZMod (p ^ 2)) := by
    rw [hg]; exact Nat.mul_pos hp.pos (Nat.sub_pos_of_lt hp.one_lt)
  have hunit : IsUnit (g : ZMod (p ^ 2)) := (orderOf_pos_iff.mp hpos).isUnit
  rw [ZMod.isUnit_iff_coprime] at hunit
  have hcop : Nat.Coprime p g := (hunit.coprime_dvd_right (dvd_pow_self p two_ne_zero)).symm
  intro hdvd
  exact (hp.coprime_iff_not_dvd.mp hcop) (hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow hdvd))

/-- `q^((p-1)/2) = -1` modulo `p²` for `q = g^p`. -/
theorem pow_half_eq_neg_one (p g : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hg : orderOf (g : ZMod (p ^ 2)) = p * (p - 1)) :
    ((g : ZMod (p ^ 2)) ^ p) ^ ((p - 1) / 2) = -1 := by
  have hp := (Fact.out : p.Prime)
  have hord := orderOf_pow_prime p g hg
  have h3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hev := even_pred_of_odd_prime p hp2
  apply eq_neg_one_of_sq_eq_one p hp2
  · rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.mp hev), ← hord, pow_orderOf_eq_one]
  · apply pow_ne_one_of_lt_orderOf (by omega)
    rw [hord]
    omega

/-- For `j, j' < p - 1` and `Q = g^p`: `p ∣ Q^j + Q^j'` iff `j' = (j + (p-1)/2) mod (p-1)`;
in that case even `p² ∣ Q^j + Q^j'`. -/
theorem dvd_add_pow_iff (p g : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hg : orderOf (g : ZMod (p ^ 2)) = p * (p - 1)) (j j' : ℕ) (hj' : j' < p - 1) :
    (p ∣ (g ^ p) ^ j + (g ^ p) ^ j' ↔ j' = (j + (p - 1) / 2) % (p - 1)) ∧
      (p ∣ (g ^ p) ^ j + (g ^ p) ^ j' → p ^ 2 ∣ (g ^ p) ^ j + (g ^ p) ^ j') := by
  set q : ZMod (p ^ 2) := (g : ZMod (p ^ 2)) ^ p with hq
  have hord : orderOf q = p - 1 := orderOf_pow_prime p g hg
  have hq1 : q ^ (p - 1) = 1 := by rw [← hord]; exact pow_orderOf_eq_one q
  have hfin : IsOfFinOrder q := by
    apply orderOf_pos_iff.mp
    rw [hord]
    exact Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  have hcast : (((g ^ p) ^ j + (g ^ p) ^ j' : ℕ) : ZMod (p ^ 2)) = q ^ j + q ^ j' := by
    rw [hq]; push_cast; rfl
  have hhalf : q ^ (j + (p - 1) / 2) = -q ^ j := by
    rw [pow_add, hq, pow_half_eq_neg_one p g hp2 hg, mul_neg_one]
  -- `p ∣ M` forces `M ≡ 0 (mod p²)`
  have hlift : p ∣ (g ^ p) ^ j + (g ^ p) ^ j' → p ^ 2 ∣ (g ^ p) ^ j + (g ^ p) ^ j' := by
    intro hdvd
    have hdvd' : (p : ZMod (p ^ 2)) ∣ q ^ j + q ^ j' := by
      rw [← hcast]; exact Nat.cast_dvd_cast hdvd
    have hzero := add_eq_zero_of_dvd_add p hp2
      (by rw [← pow_mul, mul_comm, pow_mul, hq1, one_pow])
      (by rw [← pow_mul, mul_comm, pow_mul, hq1, one_pow]) hdvd'
    rw [← hcast, ZMod.natCast_eq_zero_iff] at hzero
    exact hzero
  refine ⟨⟨fun hdvd => ?_, fun hj => ?_⟩, hlift⟩
  · have hzero : q ^ j + q ^ j' = 0 := by
      rw [← hcast, ZMod.natCast_eq_zero_iff]; exact hlift hdvd
    have heq : q ^ j' = q ^ (j + (p - 1) / 2) := by
      rw [hhalf]; linear_combination hzero
    rw [hfin.pow_eq_pow_iff_modEq, hord] at heq
    rw [← heq, Nat.mod_eq_of_lt hj']
  · have heq : q ^ j' = q ^ (j + (p - 1) / 2) := by
      rw [hfin.pow_eq_pow_iff_modEq, hord, hj]
      exact Nat.mod_modEq _ _
    have hzero : (((g ^ p) ^ j + (g ^ p) ^ j' : ℕ) : ZMod (p ^ 2)) = 0 := by
      rw [hcast, heq, hhalf, add_neg_cancel]
    rw [ZMod.natCast_eq_zero_iff] at hzero
    exact (dvd_pow_self p two_ne_zero).trans hzero

/-! ## The power sums of the periods -/

/-- `Σ_k h(p,k) = 0`. -/
theorem sum_periodSum (p g : ℕ) [Fact p.Prime] (hg : orderOf (g : ZMod (p ^ 2)) = p * (p - 1))
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (p ^ 2)) :
    ∑ k ∈ range p, periodSum p g ζ k = 0 := by
  unfold periodSum
  rw [sum_comm]
  exact sum_eq_zero fun j _ => sum_pow_eq_zero_of_not_dvd p hζ _ _ (not_dvd_pow p g hg j)

/-- `Σ_k h(p,k)² = p (p - 1)`. -/
theorem sum_periodSum_sq (p g : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hg : orderOf (g : ZMod (p ^ 2)) = p * (p - 1)) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (p ^ 2)) :
    ∑ k ∈ range p, periodSum p g ζ k ^ 2 = (p : ℂ) * ((p : ℂ) - 1) := by
  have hp := (Fact.out : p.Prime)
  have hexpand : ∀ k ∈ range p, periodSum p g ζ k ^ 2 = ∑ j ∈ range (p - 1),
      ∑ j' ∈ range (p - 1), ζ ^ ((g ^ p + k * p) * ((g ^ p) ^ j + (g ^ p) ^ j')) := by
    intro k _
    rw [periodSum, sq, sum_mul_sum]
    refine sum_congr rfl fun j _ => sum_congr rfl fun j' _ => ?_
    rw [← pow_add, mul_add]
  have hinner : ∀ j ∈ range (p - 1), ∀ j' ∈ range (p - 1),
      ∑ k ∈ range p, ζ ^ ((g ^ p + k * p) * ((g ^ p) ^ j + (g ^ p) ^ j')) =
        if j' = (j + (p - 1) / 2) % (p - 1) then (p : ℂ) else 0 := by
    intro j _ j' hj'
    have hiff := dvd_add_pow_iff p g hp2 hg j j' (mem_range.mp hj')
    by_cases hdvd : p ∣ (g ^ p) ^ j + (g ^ p) ^ j'
    · rw [if_pos (hiff.1.mp hdvd)]
      exact sum_pow_eq_of_sq_dvd p hζ _ _ (hiff.2 hdvd)
    · rw [if_neg (fun h => hdvd (hiff.1.mpr h))]
      exact sum_pow_eq_zero_of_not_dvd p hζ _ _ hdvd
  have hpos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  calc ∑ k ∈ range p, periodSum p g ζ k ^ 2
      = ∑ k ∈ range p, ∑ j ∈ range (p - 1), ∑ j' ∈ range (p - 1),
          ζ ^ ((g ^ p + k * p) * ((g ^ p) ^ j + (g ^ p) ^ j')) := sum_congr rfl hexpand
    _ = ∑ j ∈ range (p - 1), ∑ j' ∈ range (p - 1), ∑ k ∈ range p,
          ζ ^ ((g ^ p + k * p) * ((g ^ p) ^ j + (g ^ p) ^ j')) := by
        rw [sum_comm]
        exact sum_congr rfl fun j _ => sum_comm
    _ = ∑ j ∈ range (p - 1), ∑ j' ∈ range (p - 1),
          (if j' = (j + (p - 1) / 2) % (p - 1) then (p : ℂ) else 0) :=
        sum_congr rfl fun j hj => sum_congr rfl fun j' hj' => hinner j hj j' hj'
    _ = ∑ j ∈ range (p - 1), (p : ℂ) := by
        refine sum_congr rfl fun j _ => ?_
        rw [sum_ite_eq' (range (p - 1)), if_pos (mem_range.mpr (Nat.mod_lt _ hpos))]
    _ = (p : ℂ) * ((p : ℂ) - 1) := by
        rw [sum_const, card_range, nsmul_eq_mul, Nat.cast_sub hp.one_le, Nat.cast_one,
          mul_comm]

/-! ## The conjecture -/

/-- **General form.** For an odd prime `p`, a primitive root `g` modulo `p²`, and any
primitive `p²`-th root of unity `ζ ∈ ℂ`, minus the coefficient of `x^(p-2)` in the period
polynomial `f(p,x) = Π_{k<p} (x - h(p,k))` equals `p(p-1)/2`. -/
theorem neg_coeff_periodPoly (p g : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hg : orderOf (g : ZMod (p ^ 2)) = p * (p - 1)) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (p ^ 2)) :
    -(periodPoly p g ζ).coeff (p - 2) = (p : ℂ) * ((p : ℂ) - 1) / 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hkey := two_mul_coeff_prod_X_sub_C (periodSum p g ζ) (p - 2)
  rw [Nat.sub_add_cancel hp.two_le, sum_periodSum p g hg hζ,
    sum_periodSum_sq p g hp2 hg hζ] at hkey
  rw [periodPoly]
  linear_combination (-1 / 2 : ℂ) * hkey

/-- Somos's conjecture (OEIS A006308, 2020), using Irvine's period polynomial:
for every odd prime `p` and every primitive root `g` modulo `p²`,
`-[x^(p-2)] f(p,x) = p(p-1)/2`, with `ζ = exp(2πi/p²)` and `q = g^p`.
The second equality, with `Σ_{k<p} (k³ mod p)`, is `sum_cube_mod_eq`. -/
theorem a006308_conjecture (p g : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hg : orderOf (g : ZMod (p ^ 2)) = p * (p - 1)) :
    -(periodPoly p g (zeta p)).coeff (p - 2) = (p : ℂ) * ((p : ℂ) - 1) / 2 :=
  neg_coeff_periodPoly p g hp hp2 hg (zeta_isPrimitiveRoot p hp.ne_zero)

/-! ## The A008837 form `Σ_{k<p} (k³ mod p)` -/

/-- For a prime `p` and `0 < m < p`, `(m³ mod p) + ((p - m)³ mod p) = p`. -/
theorem cube_mod_add_cube_mod (p m : ℕ) (hp : p.Prime) (hm0 : 0 < m) (hmp : m < p) :
    m ^ 3 % p + (p - m) ^ 3 % p = p := by
  have hndvd : ∀ n, 0 < n → n < p → 0 < n ^ 3 % p := by
    intro n hn0 hnp
    apply Nat.pos_of_ne_zero
    intro h
    have h' := hp.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero h)
    exact absurd (Nat.le_of_dvd hn0 h') (not_le.mpr hnp)
  have ha := hndvd m hm0 hmp
  have hb := hndvd (p - m) (Nat.sub_pos_of_lt hmp) (Nat.sub_lt hp.pos hm0)
  have hlt1 := Nat.mod_lt (m ^ 3) hp.pos
  have hlt2 := Nat.mod_lt ((p - m) ^ 3) hp.pos
  have hdvd : p ∣ m ^ 3 % p + (p - m) ^ 3 % p := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast [ZMod.natCast_mod, Nat.cast_sub hmp.le, ZMod.natCast_self]
    ring
  obtain ⟨c, hc⟩ := hdvd
  have hc1 : c = 1 := by
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · rw [h, mul_zero] at hc; omega
      · exact h
    have hc2 : p * c < p * 2 := by rw [← hc]; omega
    have := Nat.lt_of_mul_lt_mul_left hc2
    omega
  rw [hc, hc1, mul_one]

/-- A008837: for a prime `p`, `2 Σ_{k<p} (k³ mod p) = p (p - 1)`. -/
theorem two_mul_sum_cube_mod (p : ℕ) (hp : p.Prime) :
    2 * ∑ k ∈ range p, k ^ 3 % p = p * (p - 1) := by
  obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.one_le).symm⟩
  have hshift : ∑ k ∈ range p, k ^ 3 % p = ∑ k ∈ range n, (k + 1) ^ 3 % p := by
    rw [hn, sum_range_succ']
    simp
  have hrefl : ∑ k ∈ range n, (k + 1) ^ 3 % p = ∑ k ∈ range n, (p - (k + 1)) ^ 3 % p := by
    rw [← sum_range_reflect]
    refine sum_congr rfl fun k hk => ?_
    have hk' := mem_range.mp hk
    congr 3
    omega
  have hpair : ∀ k ∈ range n, (k + 1) ^ 3 % p + (p - (k + 1)) ^ 3 % p = p := by
    intro k hk
    have hk' := mem_range.mp hk
    exact cube_mod_add_cube_mod p (k + 1) hp (Nat.succ_pos k) (by omega)
  calc 2 * ∑ k ∈ range p, k ^ 3 % p
      = ∑ k ∈ range n, (k + 1) ^ 3 % p + ∑ k ∈ range n, (p - (k + 1)) ^ 3 % p := by
        rw [two_mul]
        nth_rewrite 1 [hshift]
        rw [hshift, hrefl]
    _ = ∑ k ∈ range n, p := by rw [← sum_add_distrib]; exact sum_congr rfl hpair
    _ = p * (p - 1) := by rw [sum_const, card_range, smul_eq_mul, hn, Nat.add_sub_cancel, mul_comm]

/-- A008837: for a prime `p`, `Σ_{k<p} (k³ mod p) = p (p - 1) / 2` (as a complex number). -/
theorem sum_cube_mod_eq (p : ℕ) (hp : p.Prime) :
    ((∑ k ∈ range p, k ^ 3 % p : ℕ) : ℂ) = (p : ℂ) * ((p : ℂ) - 1) / 2 := by
  have h := congrArg (fun n : ℕ => (n : ℂ)) (two_mul_sum_cube_mod p hp)
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hp.one_le, Nat.cast_one] at h
  linear_combination (1 / 2 : ℂ) * h

/-- **Both equalities of the conjecture.** For an odd prime `p` and a primitive root `g`
modulo `p²`, `-[x^(p-2)] f(p,x) = Σ_{k<p} (k³ mod p)`, i.e. A006308 agrees with A008837. -/
theorem a006308_eq_sum_cube_mod (p g : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hg : orderOf (g : ZMod (p ^ 2)) = p * (p - 1)) :
    -(periodPoly p g (zeta p)).coeff (p - 2) = ((∑ k ∈ range p, k ^ 3 % p : ℕ) : ℂ) := by
  rw [a006308_conjecture p g hp hp2 hg, sum_cube_mod_eq p hp]

end Candidates.A006308OddPrimePrimitive
