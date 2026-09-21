/-
  Erdős Problem #142 — the immediate finite census/transfer composition.

  Two accepted kernels are combined here:

  * `Erdos.Erdos142.TorusGridCensus` supplies the reciprocal census lower bound
    `torusGrid_card_lower_inv`, i.e. `q^2 * rho(e) - 3*q ≤ #(torusGrid e⁻¹ q)`
    for `e ≥ 6`, with `rho(e) = 7/24 - 1/(2*e) + 1/(2*e^2)`;
  * `Erdos.Erdos142.FiniteTorusTransfer` supplies `finiteTorusTransfer`,
    `(N:ℝ) * R^2 * #(torusGrid e⁻¹ q)^k ≤ q^(2*k) * (41*k*e^2*q^2 + R^2) * rothNumberNat N`.

  Writing `b(e,q) = rho(e) - 3/q`, the census gives `#(torusGrid e⁻¹ q) ≥ q^2 * b(e,q)`,
  so when `b(e,q) ≥ 0` the `k`-th power comparison `(q^2 * b)^k ≤ #(torusGrid e⁻¹ q)^k`
  turns the transfer into the multiplication-form lower bound

    `N * R^2 * b(e,q)^k ≤ (41*k*e^2*q^2 + R^2) * rothNumberNat N`.

  The equivalent divided corollary
  `N * R^2 * b(e,q)^k / (41*k*e^2*q^2 + R^2) ≤ rothNumberNat N` follows by
  division with the (strictly positive) coefficient denominator.

  No sorry, no new axioms.  The only imported census/transfer statements are
  reused verbatim; `finiteTorusTransfer` and every existing statement are
  preserved.
-/

import Erdos.Erdos142.TorusGridCensus
import Erdos.Erdos142.FiniteTorusTransfer

set_option autoImplicit false

namespace Erdos142

/-- The census density `rho(e) = 7/24 - 1/(2*e) + 1/(2*e^2)` appearing in the
torus-grid lower bound, written in the same `e⁻¹` shape as
`torusGrid_card_lower_inv`. -/
noncomputable def rho (e : ℝ) : ℝ := 7 / 24 - e⁻¹ / 2 + e⁻¹ ^ 2 / 2

/-- The census slack `b(e,q) = rho(e) - 3/q`: the density that survives the
`3*q` ledger loss after the `q^2` normalization of `torusGrid_card_lower_inv`. -/
noncomputable def b (e : ℝ) (q : ℕ) : ℝ := rho e - 3 / (q : ℝ)

/-- **Census slack in transfer form.**  For `e ≥ 6` the reciprocal census lower
bound of `TorusGridCensus` reads `q^2 * b(e,q) ≤ #(torusGrid e⁻¹ q)`: the
`-3*q` ledger loss is exactly the `q^2 * (3/q)` absorbed into `b`. -/
theorem q_sq_mul_b_le_torusGrid_card {e : ℝ} (he : 6 ≤ e) (q : ℕ) [NeZero q] :
    (q : ℝ) ^ 2 * b e q ≤ ((torusGrid e⁻¹ q).card : ℝ) := by
  have he0 : 0 < e := by linarith
  have hq : 0 < q := NeZero.pos q
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqR
  have hene : e ≠ 0 := ne_of_gt he0
  have hcard := torusGrid_card_lower_inv (e := e) he q
  have hbq : (q : ℝ) ^ 2 * b e q =
      (q : ℝ) ^ 2 * (7 / 24 - e⁻¹ / 2 + e⁻¹ ^ 2 / 2) - 3 * (q : ℝ) := by
    rw [b, rho]
    field_simp [hqne, hene]
  rw [hbq]
  exact hcard

/-- **Primary multiplication-form lower bound.**  For prime `q`, `6 ≤ e`,
`1 ≤ N ≤ q`, `1 ≤ R`, the scale hypothesis `N * (2*R - 1)^(2*k) < q^(2*k)`, and
nonnegative census slack `0 ≤ b(e,q)`:

  `(N:ℝ) * (R:ℝ)^2 * b(e,q)^k ≤
     (41*(k:ℝ)*e^2*(q:ℝ)^2 + (R:ℝ)^2) * (rothNumberNat N : ℝ)`.

The census gives `q^2 * b(e,q) ≤ #(torusGrid e⁻¹ q)`; raising to the `k`-th
power (using `b ≥ 0`) and multiplying the finite transfer by `N * R^2` lets the
common factor `q^(2*k)` cancel. -/
theorem finiteTorusCensusTransfer {e : ℝ} {q k R N : ℕ} [Fact q.Prime]
    (he : 6 ≤ e) (hN1 : 1 ≤ N) (hNq : N ≤ q) (hR : 1 ≤ R)
    (hscale : N * (2 * R - 1) ^ (2 * k) < q ^ (2 * k))
    (hb : 0 ≤ b e q) :
    (N : ℝ) * (R : ℝ) ^ 2 * b e q ^ k ≤
      (41 * (k : ℝ) * e ^ 2 * (q : ℝ) ^ 2 + (R : ℝ) ^ 2) * (rothNumberNat N : ℝ) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hq : 0 < q := (Fact.out : q.Prime).pos
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hcard' : (q : ℝ) ^ 2 * b e q ≤ ((torusGrid e⁻¹ q).card : ℝ) :=
    q_sq_mul_b_le_torusGrid_card he q
  have hq2b : (0 : ℝ) ≤ (q : ℝ) ^ 2 * b e q := mul_nonneg (sq_nonneg _) hb
  have hpow : ((q : ℝ) ^ 2 * b e q) ^ k ≤ (((torusGrid e⁻¹ q).card : ℝ)) ^ k :=
    pow_le_pow_left₀ hq2b hcard' k
  have hcardpow : ((((torusGrid e⁻¹ q).card ^ k : ℕ)) : ℝ) =
      ((torusGrid e⁻¹ q).card : ℝ) ^ k := by
    rw [Nat.cast_pow]
  have hpow' : (q : ℝ) ^ (2 * k) * b e q ^ k ≤
      ((((torusGrid e⁻¹ q).card ^ k : ℕ)) : ℝ) := by
    rw [hcardpow]
    calc (q : ℝ) ^ (2 * k) * b e q ^ k = ((q : ℝ) ^ 2 * b e q) ^ k := by
          rw [mul_pow, ← pow_mul]
      _ ≤ ((torusGrid e⁻¹ q).card : ℝ) ^ k := hpow
  have htrans := finiteTorusTransfer (e := e) (q := q) (k := k) (R := R) (N := N)
    he hN1 hNq hR hscale
  have hNR : (0 : ℝ) ≤ (N : ℝ) * (R : ℝ) ^ 2 :=
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hstep : (N : ℝ) * (R : ℝ) ^ 2 * ((q : ℝ) ^ (2 * k) * b e q ^ k) ≤
      (N : ℝ) * (R : ℝ) ^ 2 * ((((torusGrid e⁻¹ q).card ^ k : ℕ)) : ℝ) :=
    mul_le_mul_of_nonneg_left hpow' hNR
  have hqpow : (0 : ℝ) < (q : ℝ) ^ (2 * k) := pow_pos hqR _
  have hkey : (q : ℝ) ^ (2 * k) * ((N : ℝ) * (R : ℝ) ^ 2 * b e q ^ k) ≤
      (q : ℝ) ^ (2 * k) *
        ((41 * (k : ℝ) * e ^ 2 * (q : ℝ) ^ 2 + (R : ℝ) ^ 2) *
          (rothNumberNat N : ℝ)) := by
    calc (q : ℝ) ^ (2 * k) * ((N : ℝ) * (R : ℝ) ^ 2 * b e q ^ k)
        = (N : ℝ) * (R : ℝ) ^ 2 * ((q : ℝ) ^ (2 * k) * b e q ^ k) := by ring
      _ ≤ (N : ℝ) * (R : ℝ) ^ 2 * ((((torusGrid e⁻¹ q).card ^ k : ℕ)) : ℝ) := hstep
      _ ≤ (q : ℝ) ^ (2 * k) *
            (41 * (k : ℝ) * e ^ 2 * (q : ℝ) ^ 2 + (R : ℝ) ^ 2) *
              (rothNumberNat N : ℝ) := htrans
      _ = (q : ℝ) ^ (2 * k) *
            ((41 * (k : ℝ) * e ^ 2 * (q : ℝ) ^ 2 + (R : ℝ) ^ 2) *
              (rothNumberNat N : ℝ)) := by ring
  exact le_of_mul_le_mul_left hkey hqpow

/-- **Divided explicit lower bound.**  Under the same hypotheses as
`finiteTorusCensusTransfer`, the coefficient
`41*(k:ℝ)*e^2*(q:ℝ)^2 + (R:ℝ)^2` is strictly positive (it dominates `R^2 ≥ 1`),
so dividing gives

  `(N:ℝ) * (R:ℝ)^2 * b(e,q)^k / (41*(k:ℝ)*e^2*(q:ℝ)^2 + (R:ℝ)^2) ≤
     (rothNumberNat N : ℝ)`. -/
theorem rothNumberNat_lower_bound_of_finiteTorusCensus {e : ℝ} {q k R N : ℕ}
    [Fact q.Prime] (he : 6 ≤ e) (hN1 : 1 ≤ N) (hNq : N ≤ q) (hR : 1 ≤ R)
    (hscale : N * (2 * R - 1) ^ (2 * k) < q ^ (2 * k))
    (hb : 0 ≤ b e q) :
    (N : ℝ) * (R : ℝ) ^ 2 * b e q ^ k /
        (41 * (k : ℝ) * e ^ 2 * (q : ℝ) ^ 2 + (R : ℝ) ^ 2) ≤
      (rothNumberNat N : ℝ) := by
  have hden : 0 < 41 * (k : ℝ) * e ^ 2 * (q : ℝ) ^ 2 + (R : ℝ) ^ 2 := by
    have hRpos : (0 : ℝ) < (R : ℝ) := by
      exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num : 0 < 1) hR)
    have hterm : (0 : ℝ) ≤ 41 * (k : ℝ) * e ^ 2 * (q : ℝ) ^ 2 := by positivity
    have hR2 : (0 : ℝ) < (R : ℝ) ^ 2 := pow_pos hRpos 2
    linarith
  rw [div_le_iff₀ hden]
  have hfirst := finiteTorusCensusTransfer he hN1 hNq hR hscale hb
  nlinarith [hfirst]

/-- **Nonnegative census slack from explicit thresholds.**  For `6 ≤ e` and
`14 ≤ q` the census slack is nonnegative: `rho(e) ≥ rho(6) = 2/9` and
`3/q ≤ 3/14`, whence `b(e,q) ≥ 2/9 - 3/14 = 1/126 > 0`.  This discharges the
`0 ≤ b(e,q)` hypothesis of the two transfer theorems from explicit parameter
bounds. -/
theorem b_nonneg_of_six_le_and_fourteen_le {e : ℝ} {q : ℕ} (he : 6 ≤ e)
    (hq : 14 ≤ q) : 0 ≤ b e q := by
  have he0 : 0 < e := by linarith
  have hene : e ≠ 0 := ne_of_gt he0
  have hqpos : 0 < q := by omega
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have hq14 : (14 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hrho : (2 : ℝ) / 9 ≤ 7 / 24 - e⁻¹ / 2 + e⁻¹ ^ 2 / 2 := by
    have hkey : 7 / 24 - e⁻¹ / 2 + e⁻¹ ^ 2 / 2 - 2 / 9 =
        (e - 6) * (5 * e - 6) / (72 * e ^ 2) := by
      field_simp [hene]
      ring
    have hnonneg : (0 : ℝ) ≤ (e - 6) * (5 * e - 6) / (72 * e ^ 2) := by
      apply div_nonneg
      · exact mul_nonneg (by linarith) (by linarith)
      · positivity
    have hsub : (0 : ℝ) ≤ 7 / 24 - e⁻¹ / 2 + e⁻¹ ^ 2 / 2 - 2 / 9 := by
      rw [hkey]
      exact hnonneg
    linarith
  have h3 : 3 / (q : ℝ) ≤ 3 / 14 := by
    rw [div_le_iff₀ hqR]
    nlinarith [hq14]
  rw [b, rho]
  linarith

-- Ground-truth checks.

/-- At `e = 6` the census density is `2/9`, matching `rho(6)` directly. -/
example : rho 6 = 2 / 9 := by
  rw [rho]
  norm_num

/-- At the threshold `(e, q) = (6, 14)` the census slack is `b 6 14 = 1/126`. -/
example : b 6 14 = 1 / 126 := by
  rw [b, rho]
  norm_num

/-- The slack is negative at `q = 2`, so the `0 ≤ b(e,q)` hypothesis is a
genuine side condition and is not implied by the other transfer hypotheses. -/
example : b 6 2 = 2 / 9 - 3 / 2 := by
  rw [b, rho]
  norm_num

/-- Positive-slack witness: at `e = 6`, `q = 14` the census slack is `1/126 > 0`,
so `b_nonneg_of_six_le_and_fourteen_le` is not vacuous. -/
example : 0 < b 6 14 := by
  have h := b_nonneg_of_six_le_and_fourteen_le (e := 6) (q := 14) (by norm_num) (by norm_num)
  rw [b, rho] at h ⊢
  norm_num at h ⊢

#print axioms q_sq_mul_b_le_torusGrid_card
#print axioms finiteTorusCensusTransfer
#print axioms rothNumberNat_lower_bound_of_finiteTorusCensus
#print axioms b_nonneg_of_six_le_and_fourteen_le

end Erdos142