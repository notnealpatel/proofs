/-
  Erdős Problem #142 — asymptotic assembly of the torus lower bound.

  This module is the *abstract bridge* from the finite torus construction plus
  the real radius ratio to an exponential Roth lower bound.  It deliberately
  does **not** choose `δ`, `e`, `q`, or `k`: those are inputs, and the module
  exposes the two compositions that an eventual parameter choice consumes.

  * `torusLowerBoundRaw` is the multiplicative form of the finite census.  With
    `R = torusRadius N q k` it instantiates
    `rothNumberNat_lower_bound_of_finiteTorusCensus` (giving
    `N·R²·b(e,q)^k / (41·k·e²·q² + R²) ≤ r₃(N)`) and multiplies the ratio lower
    bound `torusRadius_ratio_lower` (giving
    `exp(-log N/k)/(660·k·e²) ≤ R²/(41·k·e²·q² + R²)`) by the nonnegative factor
    `N·b(e,q)^k`, so the `R²/(…)` ratios cancel and the explicit product
    `N·b(e,q)^k·exp(-log N/k)/(660·k·e²)` remains bounded by `r₃(N)`.

  * `rothNumberNat_lower_bound_of_budget` converts the raw product into an
    exponential lower bound.  Writing
    `L = k·log(1/b) + log N/k + log(660·k·e²)`, positivity of `b` and of the
    denominator turn the product into `N·exp(-L)`, and the *budget hypothesis*
    `L ≤ C·√(log N)` plus monotonicity of `exp` yields
    `N·exp(-C·√(log N)) ≤ r₃(N)`.

  No `sorry`, no `unsafe`, no new axioms; every imported statement is reused
  verbatim and no existing declaration is edited.
-/

import Erdos.Erdos142.TorusAsymptoticParameters

set_option autoImplicit false

namespace Erdos142

/-- **Raw multiplicative torus lower bound.**  For prime `q`, `64 ≤ N ≤ q`,
`1 ≤ k`, `6 ≤ e`, and positive census slack `0 < b(e,q)`,

`N · b(e,q)^k · exp(-log N/k) / (660·k·e²) ≤ r₃(N)`.

`torusRadius_spec` supplies `R = torusRadius N q k` with `1 ≤ R` and the strict
scale inequality `N·(2R-1)^(2k) < q^(2k)`, so
`rothNumberNat_lower_bound_of_finiteTorusCensus` gives
`N·R²·b^k / (41·k·e²·q² + R²) ≤ r₃(N)`.  Multiplying `torusRadius_ratio_lower`
by the nonnegative factor `N·b^k` matches the same coefficient denominator, and
the two `R²/(41·k·e²·q² + R²)` expressions cancel. -/
theorem torusLowerBoundRaw {e : ℝ} {N q k : ℕ} [Fact q.Prime]
    (hN : 64 ≤ N) (hNq : N ≤ q) (hk : 1 ≤ k) (he : 6 ≤ e) (hb : 0 < b e q) :
    (N : ℝ) * b e q ^ k * Real.exp (-(Real.log N) / (k : ℝ)) / (660 * (k : ℝ) * e ^ 2) ≤
      (rothNumberNat N : ℝ) := by
  have hN1 : 1 ≤ N := by omega
  have hspec := torusRadius_spec (N := N) (q := q) (k := k) hN hNq hk
  have hR1 : 1 ≤ torusRadius N q k := hspec.1
  have hscale : N * (2 * torusRadius N q k - 1) ^ (2 * k) < q ^ (2 * k) := hspec.2.2.2
  have htrans := rothNumberNat_lower_bound_of_finiteTorusCensus (e := e) (q := q) (k := k)
    (R := torusRadius N q k) (N := N) he hN1 hNq hR1 hscale hb.le
  have hratio := torusRadius_ratio_lower (N := N) (q := q) (k := k) (e := e) hN hNq hk he
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hbk : (0 : ℝ) ≤ b e q ^ k := pow_nonneg hb.le k
  have hmul := mul_le_mul_of_nonneg_left hratio (mul_nonneg hNnn hbk)
  have hleft : ((N : ℝ) * b e q ^ k) *
      (Real.exp (-(Real.log N) / (k : ℝ)) / (660 * (k : ℝ) * e ^ 2)) =
      (N : ℝ) * b e q ^ k * Real.exp (-(Real.log N) / (k : ℝ)) /
        (660 * (k : ℝ) * e ^ 2) := by
    ring
  have hright : ((N : ℝ) * b e q ^ k) *
      ((torusRadius N q k : ℝ) ^ 2 /
        (41 * (k : ℝ) * e ^ 2 * (q : ℝ) ^ 2 + (torusRadius N q k : ℝ) ^ 2)) =
      (N : ℝ) * (torusRadius N q k : ℝ) ^ 2 * b e q ^ k /
        (41 * (k : ℝ) * e ^ 2 * (q : ℝ) ^ 2 + (torusRadius N q k : ℝ) ^ 2) := by
    ring
  rw [hleft, hright] at hmul
  exact le_trans hmul htrans

/-- **Exponential Roth lower bound from a logarithmic budget.**  For prime `q`,
`64 ≤ N ≤ q`, `1 ≤ k`, `6 ≤ e`, positive census slack `0 < b(e,q)`, and a real
`C` satisfying the *budget*

`k·log(1/b(e,q)) + log N/k + log(660·k·e²) ≤ C·√(log N)`,

the Roth number satisfies `N·exp(-C·√(log N)) ≤ r₃(N)`.

The raw bound `torusLowerBoundRaw` gives `N·b^k·exp(-log N/k)/(660·k·e²) ≤ r₃(N)`.
Positivity of `b(e,q)` and of `660·k·e²` rewrite `b^k = exp(-k·log(1/b))` and
`1/(660·k·e²) = exp(-log(660·k·e²))`, so the left side is `N·exp(-L)` with
`L` the budget expression.  The budget gives `-C·√(log N) ≤ -L`, and
`Real.exp_le_exp` plus multiplication by `N ≥ 0` yields the claim. -/
theorem rothNumberNat_lower_bound_of_budget {e C : ℝ} {N q k : ℕ} [Fact q.Prime]
    (hN : 64 ≤ N) (hNq : N ≤ q) (hk : 1 ≤ k) (he : 6 ≤ e) (hb : 0 < b e q)
    (hbudget : (k : ℝ) * Real.log (1 / b e q) + Real.log N / (k : ℝ) +
        Real.log (660 * (k : ℝ) * e ^ 2) ≤ C * Real.sqrt (Real.log N)) :
    (N : ℝ) * Real.exp (-(C * Real.sqrt (Real.log N))) ≤ (rothNumberNat N : ℝ) := by
  have hraw := torusLowerBoundRaw (e := e) (N := N) (q := q) (k := k) hN hNq hk he hb
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hepos : (0 : ℝ) < e := by linarith
  have hDpos : (0 : ℝ) < 660 * (k : ℝ) * e ^ 2 := by positivity
  set L := (k : ℝ) * Real.log (1 / b e q) + Real.log N / (k : ℝ) +
      Real.log (660 * (k : ℝ) * e ^ 2) with hLdef
  have hBpow : b e q ^ k = Real.exp (-((k : ℝ) * Real.log (1 / b e q))) := by
    rw [one_div, Real.log_inv]
    rw [show -((k : ℝ) * -Real.log (b e q)) = (k : ℝ) * Real.log (b e q) by ring]
    rw [Real.exp_nat_mul, Real.exp_log hb]
  have hDinv : (660 * (k : ℝ) * e ^ 2)⁻¹ =
      Real.exp (-(Real.log (660 * (k : ℝ) * e ^ 2))) := by
    rw [eq_comm, Real.exp_neg, Real.exp_log hDpos]
  have hNexp : Real.exp (-(Real.log N) / (k : ℝ)) = Real.exp (-(Real.log N / (k : ℝ))) := by
    congr 1
    ring
  have hLHS : (N : ℝ) * b e q ^ k * Real.exp (-(Real.log N) / (k : ℝ)) /
        (660 * (k : ℝ) * e ^ 2) =
      (N : ℝ) * (Real.exp (-((k : ℝ) * Real.log (1 / b e q))) *
        Real.exp (-(Real.log N / (k : ℝ))) *
        Real.exp (-(Real.log (660 * (k : ℝ) * e ^ 2)))) := by
    rw [hBpow, hNexp, div_eq_mul_inv, hDinv]
    ring
  have hexp_prod : Real.exp (-((k : ℝ) * Real.log (1 / b e q))) *
      Real.exp (-(Real.log N / (k : ℝ))) *
      Real.exp (-(Real.log (660 * (k : ℝ) * e ^ 2))) = Real.exp (-L) := by
    rw [hLdef]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hraw' : (N : ℝ) * Real.exp (-L) ≤ (rothNumberNat N : ℝ) := by
    rw [← hexp_prod, ← hLHS]
    exact hraw
  have hbudget' : L ≤ C * Real.sqrt (Real.log N) := by
    rw [hLdef]
    exact hbudget
  have hmono : Real.exp (-(C * Real.sqrt (Real.log N))) ≤ Real.exp (-L) := by
    apply Real.exp_le_exp.mpr
    linarith [hbudget']
  calc (N : ℝ) * Real.exp (-(C * Real.sqrt (Real.log N)))
      ≤ (N : ℝ) * Real.exp (-L) := mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg N)
    _ ≤ (rothNumberNat N : ℝ) := hraw'

-- Ground-truth checks.

/-- The budget theorem is satisfiable at `N = 64`, `q = 67`, `k = 1`, `e = 6`
with the (deliberately generous) constant `C = 1000000`.  Every hypothesis holds
and the logarithmic budget is discharged by coarse bounds
`log(1/b) ≤ 1/b - 1`, `log x ≤ x - 1`, and `1 ≤ √(log 64)`. -/
example : (64 : ℝ) * Real.exp (-(1000000 * Real.sqrt (Real.log 64))) ≤
    (rothNumberNat 64 : ℝ) := by
  haveI : Fact (Nat.Prime 67) := ⟨by norm_num⟩
  refine rothNumberNat_lower_bound_of_budget (e := 6) (C := 1000000)
    (N := 64) (q := 67) (k := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_ ?_
  · rw [b, rho]
    norm_num
  · have hlog1b : Real.log (1 / b 6 67) ≤ 496 / 107 := by
      have hpos : (0 : ℝ) < 1 / b 6 67 := by
        rw [b, rho]
        norm_num
      have h := Real.log_le_sub_one_of_pos hpos
      have hval : (1 : ℝ) / b 6 67 = 603 / 107 := by
        rw [b, rho]
        norm_num
      rw [hval] at h ⊢
      norm_num at h ⊢
      exact h
    have hlog64 : Real.log (64 : ℝ) ≤ 63 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 64 by norm_num)
      norm_num at h
      exact h
    have hlog23760 : Real.log (23760 : ℝ) ≤ 23759 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 23760 by norm_num)
      norm_num at h
      exact h
    have hsqrt : (1 : ℝ) ≤ Real.sqrt (Real.log 64) := by
      rw [Real.one_le_sqrt, Real.le_log_iff_exp_le (show (0 : ℝ) < 64 by norm_num)]
      linarith [Real.exp_one_lt_three]
    have hRHS : (1000000 : ℝ) ≤ 1000000 * Real.sqrt (Real.log 64) := by
      nlinarith [hsqrt]
    have h660 : 660 * ((1 : ℕ) : ℝ) * (6 : ℝ) ^ 2 = (23760 : ℝ) := by norm_num
    rw [h660]
    simp only [Nat.cast_one, one_mul, div_one]
    linarith [hlog1b, hlog64, hlog23760, hRHS]

#print axioms torusLowerBoundRaw
#print axioms rothNumberNat_lower_bound_of_budget

end Erdos142