import Sorry.Erdos.Erdos142.SquareScaleNegativeDensity
import Sorry.Erdos.Erdos142.CriticalContractionTransfer
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

open Filter Asymptotics MeasureTheory Set
open scoped Topology

namespace Erdos142

noncomputable section

/-- Natural-log square growth, normalized by the shift `log 2`. -/
def squareLogGrowth (n : ℕ) : ℝ :=
  Real.log (rothLogDeficit (n ^ 2) / rothLogDeficit n) / Real.log 2

/-- The positive loglog cell length, used only for indices at least three. -/
def loglogWeight (n : ℕ) : ℝ :=
  Real.log (Real.log (n + 1 : ℝ)) - Real.log (Real.log (n : ℝ))

/-- The actual Roth weighted square-growth prefix (not a telescope theorem). -/
def weightedSquareSum (M : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 3 M, loglogWeight n * squareLogGrowth n

/-- The logarithm of the actual deficit shifted by twice the log-two window loss. -/
def shiftedLogDeficit (n : ℕ) : ℝ :=
  Real.log (rothLogDeficit n + 2 * Real.log 2)

/-- Integer scale selected by the double-exponential coordinate. -/
def loglogScale (x : ℝ) : ℕ := ⌊Real.exp (Real.exp x)⌋₊

example (n : ℕ) : squareLogGrowth n =
    Real.log (rothLogDeficit (n ^ 2) / rothLogDeficit n) / Real.log 2 := rfl
example (n : ℕ) : loglogWeight n =
    Real.log (Real.log (n + 1 : ℝ)) - Real.log (Real.log (n : ℝ)) := rfl
example : weightedSquareSum 3 = loglogWeight 3 * squareLogGrowth 3 := by
  simp [weightedSquareSum]
example (n : ℕ) : shiftedLogDeficit n =
    Real.log (rothLogDeficit n + 2 * Real.log 2) := rfl
example (x : ℝ) : loglogScale x = ⌊Real.exp (Real.exp x)⌋₊ := rfl

private theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- The loglog weights are strictly positive on the intended nonempty tail. -/
theorem loglogWeight_pos {n : ℕ} (hn : 3 ≤ n) : 0 < loglogWeight n := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn'
  apply sub_pos.mpr
  apply Real.log_lt_log hlog
  exact Real.log_lt_log (by positivity) (by norm_cast; omega)

/-- Square deficits lie between the original deficit and twice it plus `log 2`.
This is square-only monotonicity, not monotonicity on arbitrary integer scales. -/
theorem rothLogDeficit_square_bounds {n : ℕ} (hn : 3 ≤ n) :
    rothLogDeficit n ≤ rothLogDeficit (n ^ 2) ∧
      rothLogDeficit (n ^ 2) ≤ 2 * rothLogDeficit n + Real.log 2 := by
  have heq := squareScaleDefect_eq_rothLogDeficit_sub n (by omega)
  have hlo := neg_rothLogDeficit_le_squareScaleDefect n (by omega)
  have hhi := log_squareScaleDefect_le_log_two n (by omega)
  constructor <;> linarith

/-- Within a factor-two integer window the deficit can rise by at most `log 2`.
The proof uses monotonicity of the Roth count, not of its deficit. -/
theorem rothLogDeficit_le_of_le_two_mul {L M : ℕ} (hL : 1 ≤ L)
    (hLM : L ≤ M) (hM : M ≤ 2 * L) :
    rothLogDeficit M ≤ rothLogDeficit L + Real.log 2 := by
  have hM1 : 1 ≤ M := hL.trans hLM
  have hrL := rothNumberNat_pos_real hL
  have hrM := rothNumberNat_pos_real hM1
  have hcount : (rothNumberNat L : ℝ) ≤ (rothNumberNat M : ℝ) := by
    exact_mod_cast rothNumberNat.monotone hLM
  have hnum : (M : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast hM
  have hlognum : Real.log (M : ℝ) ≤ Real.log (L : ℝ) + Real.log 2 := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < M) hnum
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)] at hh
    linarith
  have hlogcount := Real.log_le_log hrL hcount
  rw [rothLogDeficit_eq hM1, rothLogDeficit_eq hL]
  linarith

/-- The rounded square-window comparison has absolute error at most `log 2`. -/
theorem abs_rothLogDeficit_sub_square_le {n m : ℕ} (hn : 3 ≤ n)
    (hlo : n ^ 2 ≤ m) (hhi : m ≤ 2 * n ^ 2) :
    |rothLogDeficit m - rothLogDeficit (n ^ 2)| ≤ Real.log 2 := by
  have hn2 : 1 ≤ n ^ 2 := one_le_pow₀ (by omega : 1 ≤ n)
  have hleft := rothLogDeficit_le_add_log_two hn2 hlo
  have hright := rothLogDeficit_le_of_le_two_mul hn2 hlo hhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem log_add_error {a d : ℝ} (ha : 0 < a) (hd : 0 ≤ d) :
    0 ≤ Real.log (a + d) - Real.log a ∧
      Real.log (a + d) - Real.log a ≤ d / a := by
  have had : 0 < a + d := by positivity
  have hlo := Real.log_le_log ha (by linarith : a ≤ a + d)
  have hhi := Real.log_le_sub_one_of_pos (div_pos had ha)
  rw [Real.log_div (ne_of_gt had) (ne_of_gt ha)] at hhi
  constructor
  · linarith
  · have heq : (a + d) / a - 1 = d / a := by field_simp; ring
    linarith

/-- A finite tail-uniform surrogate bound: every rounded square window gives
square growth within `5 / λ(n)` of the shifted logarithmic difference.
The `log 2` normalization cancels exactly in this bound. -/
theorem abs_squareLogGrowth_sub_shifted_le {n m : ℕ} (hn : 3 ≤ n)
    (hlo : n ^ 2 ≤ m) (hhi : m ≤ 2 * n ^ 2) :
    |squareLogGrowth n -
      (shiftedLogDeficit m - shiftedLogDeficit n) / Real.log 2| ≤
      5 / rothLogDeficit n := by
  let a := rothLogDeficit n
  let s := rothLogDeficit (n ^ 2)
  let h := Real.log 2
  have ha : 0 < a := rothLogDeficit_pos_of_three_le hn
  have hs : a ≤ s := (rothLogDeficit_square_bounds hn).1
  have hspos : 0 < s := ha.trans_le hs
  have hh : 0 < h := log_two_pos
  have hwindow := abs_rothLogDeficit_sub_square_le hn hlo hhi
  have hwindow' : -h ≤ rothLogDeficit m - s ∧
      rothLogDeficit m - s ≤ h := abs_le.mp hwindow
  have hmlo : s ≤ rothLogDeficit m + 2 * h := by linarith
  have hmhi : rothLogDeficit m + 2 * h ≤ s + 3 * h := by linarith
  have hmloglo := Real.log_le_log hspos hmlo
  have hmloghi := Real.log_le_log (hspos.trans_le hmlo) hmhi
  have es := log_add_error hspos (by positivity : 0 ≤ 3 * h)
  have ea := log_add_error ha (by positivity : 0 ≤ 2 * h)
  have hdiv : 3 * h / s ≤ 3 * h / a :=
    div_le_div_of_nonneg_left (by positivity) ha hs
  have hsplit : 5 * h / a = 2 * h / a + 3 * h / a := by ring
  have htwo : 0 ≤ 2 * h / a := by positivity
  have hthree : 0 ≤ 3 * h / a := by positivity
  have herr : |(Real.log s - Real.log a) -
      (Real.log (rothLogDeficit m + 2 * h) - Real.log (a + 2 * h))| ≤
      5 * h / a := by
    apply abs_le.mpr
    constructor <;> linarith [es.1, es.2, ea.1, ea.2]
  have hlog : Real.log (s / a) = Real.log s - Real.log a :=
    Real.log_div (ne_of_gt hspos) (ne_of_gt ha)
  change |Real.log (s / a) / h -
    (Real.log (rothLogDeficit m + 2 * h) - Real.log (a + 2 * h)) / h| ≤ 5 / a
  rw [hlog, ← sub_div, abs_div, abs_of_pos hh]
  apply (div_le_iff₀ hh).2
  calc
    _ ≤ 5 * h / a := herr
    _ = 5 / a * h := by ring

/-- Qualitative Roth makes the local comparison uniformly small over *all*
integer points in each square window, without a quantitative Roth assumption. -/
theorem eventually_squareLogGrowth_shifted_close {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, n ^ 2 ≤ m → m ≤ 2 * n ^ 2 →
      |squareLogGrowth n -
        (shiftedLogDeficit m - shiftedLogDeficit n) / Real.log 2| < ε := by
  have htail := tendsto_rothLogDeficit_atTop.eventually
    (eventually_gt_atTop (5 / ε))
  filter_upwards [eventually_ge_atTop 3, htail] with n hn hlarge
  intro m hlo hhi
  have ha := rothLogDeficit_pos_of_three_le hn
  have hsmall : 5 / rothLogDeficit n < ε := by
    apply (div_lt_iff₀ ha).2
    have hmul := (div_lt_iff₀ hε).1 hlarge
    nlinarith
  exact (abs_squareLogGrowth_sub_shifted_le hn hlo hhi).trans_lt hsmall

/-- The shifted deficit doubles at most across every rounded square window. -/
theorem shifted_deficit_square_window_le {n m : ℕ} (hn : 3 ≤ n)
    (hlo : n ^ 2 ≤ m) (hhi : m ≤ 2 * n ^ 2) :
    rothLogDeficit m + 2 * Real.log 2 ≤
      2 * (rothLogDeficit n + 2 * Real.log 2) := by
  have hwindow := rothLogDeficit_le_of_le_two_mul
    (one_le_pow₀ (by omega : 1 ≤ n) : 1 ≤ n ^ 2) hlo hhi
  have hsquare := (rothLogDeficit_square_bounds hn).2
  linarith

/-- On the endpoint integer window `[N,N²]`, the shifted logarithm differs
from `log λ(N)` by a nonnegative error at most `log 2 + 2 log 2 / λ(N)`.
This endpoint control does not require monotonicity of the deficit. -/
theorem shiftedLogDeficit_endpoint_bounds {N m : ℕ} (hN : 3 ≤ N)
    (hlo : N ≤ m) (hhi : m ≤ N ^ 2) :
    0 ≤ shiftedLogDeficit m - Real.log (rothLogDeficit N) ∧
      shiftedLogDeficit m - Real.log (rothLogDeficit N) ≤
        Real.log 2 + 2 * Real.log 2 / rothLogDeficit N := by
  let a := rothLogDeficit N
  let h := Real.log 2
  have ha : 0 < a := rothLogDeficit_pos_of_three_le hN
  have hh : 0 < h := log_two_pos
  have hlower := rothLogDeficit_le_add_log_two (by omega : 1 ≤ N) hlo
  have hm1 : 1 ≤ m := by omega
  have hupper := rothLogDeficit_le_add_log_two hm1 hhi
  have hsquare := (rothLogDeficit_square_bounds hN).2
  have hbLo : a ≤ rothLogDeficit m + 2 * h := by dsimp [a, h]; linarith
  have hbHi : rothLogDeficit m + 2 * h ≤ 2 * (a + 2 * h) := by
    dsimp [a, h]; linarith
  have hloglo := Real.log_le_log ha hbLo
  have hloghi := Real.log_le_log (ha.trans_le hbLo) hbHi
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (ne_of_gt (by positivity : 0 < a + 2 * h))] at hloghi
  have herror := log_add_error ha (by positivity : 0 ≤ 2 * h)
  change 0 ≤ Real.log (rothLogDeficit m + 2 * h) - Real.log a ∧
    Real.log (rothLogDeficit m + 2 * h) - Real.log a ≤ h + 2 * h / a
  constructor <;> linarith

/-- The endpoint comparison is uniformly bounded on a positive actual-Roth tail. -/
theorem eventually_shiftedLogDeficit_endpoint_close :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, N ≤ m → m ≤ N ^ 2 →
      |shiftedLogDeficit m - Real.log (rothLogDeficit N)| ≤ Real.log 2 + 1 := by
  have htail := tendsto_rothLogDeficit_atTop.eventually
    (eventually_ge_atTop (2 * Real.log 2))
  filter_upwards [eventually_ge_atTop 3, htail] with N hN hlarge
  intro m hlo hhi
  have ha := rothLogDeficit_pos_of_three_le hN
  have hh := shiftedLogDeficit_endpoint_bounds hN hlo hhi
  rw [abs_of_nonneg hh.1]
  have hfrac : 2 * Real.log 2 / rothLogDeficit N ≤ 1 := by
    exact (div_le_one ha).2 hlarge
  linarith [hh.2]

/-- The double-exponential coordinate converts a log-two translation into squaring. -/
theorem exp_exp_add_log_two (x : ℝ) :
    Real.exp (Real.exp (x + Real.log 2)) = Real.exp (Real.exp x) ^ 2 := by
  rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [mul_comm, ← Nat.cast_ofNat, Real.exp_nat_mul]

private theorem floor_square_window {t : ℝ} (ht : 0 ≤ t)
    (hn : 3 ≤ ⌊t⌋₊) :
    ⌊t⌋₊ ^ 2 ≤ ⌊t ^ 2⌋₊ ∧ ⌊t ^ 2⌋₊ < 2 * ⌊t⌋₊ ^ 2 := by
  let n : ℕ := ⌊t⌋₊
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlo : (n : ℝ) ≤ t := Nat.floor_le ht
  have hhi : t < (n : ℝ) + 1 := Nat.lt_floor_add_one t
  constructor
  · apply Nat.le_floor
    push_cast
    nlinarith
  · apply (Nat.floor_lt (sq_nonneg t)).2
    push_cast
    nlinarith

private theorem exp_exp_loglog {n : ℕ} (hn : 3 ≤ n) :
    Real.exp (Real.exp (Real.log (Real.log (n : ℝ)))) = n := by
  have hnreal : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  rw [Real.exp_log (Real.log_pos hnreal), Real.exp_log (by positivity)]

/-- The floor scale is exactly the integer `n` on its half-open loglog cell. -/
theorem loglogScale_eq_of_cell {n : ℕ} (hn : 3 ≤ n) {x : ℝ}
    (hlo : Real.log (Real.log (n : ℝ)) ≤ x)
    (hhi : x < Real.log (Real.log (n + 1 : ℝ))) :
    loglogScale x = n := by
  have heq := exp_exp_loglog hn
  have heq' : Real.exp (Real.exp (Real.log (Real.log (n + 1 : ℝ)))) = (n : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      exp_exp_loglog (show 3 ≤ n + 1 by omega)
  apply (Nat.floor_eq_iff (le_of_lt (Real.exp_pos _))).2
  constructor
  · calc
      (n : ℝ) = Real.exp (Real.exp (Real.log (Real.log (n : ℝ)))) := heq.symm
      _ ≤ Real.exp (Real.exp x) := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hlo)
  · have hh := Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr hhi)
    exact hh.trans_eq heq'

/-- At each positive loglog cell boundary the floor scale returns its integer. -/
theorem loglogScale_loglog {n : ℕ} (hn : 3 ≤ n) :
    loglogScale (Real.log (Real.log (n : ℝ))) = n := by
  dsimp [loglogScale]
  rw [exp_exp_loglog hn, Nat.floor_natCast]

/-- The actual loglog floor scale tends to infinity over all real coordinates. -/
theorem tendsto_loglogScale_atTop : Tendsto loglogScale atTop atTop := by
  apply tendsto_atTop.mpr
  intro n
  have hexp := Real.tendsto_exp_atTop.comp Real.tendsto_exp_atTop
  filter_upwards [hexp.eventually (eventually_ge_atTop (n : ℝ))] with x hx
  exact Nat.le_floor hx

/-- The rounded shift lies in the intended square window as soon as the
floor scale is at least three; the upper endpoint is strictly excluded. -/
theorem loglogScale_shift_window {x : ℝ} (hx : 3 ≤ loglogScale x) :
    loglogScale x ^ 2 ≤ loglogScale (x + Real.log 2) ∧
      loglogScale (x + Real.log 2) < 2 * loglogScale x ^ 2 := by
  have hwindow := floor_square_window (le_of_lt (Real.exp_pos (Real.exp x))) hx
  simpa only [loglogScale, exp_exp_add_log_two] using hwindow

/-- The actual rounded local surrogate error tends to zero over *all* real
coordinates, not just a subsequence of integer loglog boundaries. -/
theorem tendsto_squareLogGrowth_sub_shifted_loglogScale :
    Tendsto (fun x : ℝ => squareLogGrowth (loglogScale x) -
      (shiftedLogDeficit (loglogScale (x + Real.log 2)) -
        shiftedLogDeficit (loglogScale x)) / Real.log 2) atTop (𝓝 0) := by
  have hsmall : Tendsto (fun x : ℝ => 5 / rothLogDeficit (loglogScale x))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rothLogDeficit_atTop.comp tendsto_loglogScale_atTop)
  apply squeeze_zero_norm' _ hsmall
  filter_upwards [tendsto_loglogScale_atTop.eventually (eventually_ge_atTop 3)] with x hx
  have hw := loglogScale_shift_window hx
  simpa only [Real.norm_eq_abs] using abs_squareLogGrowth_sub_shifted_le hx hw.1 hw.2.le

/-- Every point of the final real window `[loglog N, loglog N + log 2]`
has floor scale in the endpoint integer window `[N,N²]`. -/
theorem loglogScale_endpoint_window {N : ℕ} (hN : 3 ≤ N) {y : ℝ}
    (hlo : Real.log (Real.log (N : ℝ)) ≤ y)
    (hhi : y ≤ Real.log (Real.log (N : ℝ)) + Real.log 2) :
    N ≤ loglogScale y ∧ loglogScale y ≤ N ^ 2 := by
  have heq := exp_exp_loglog hN
  constructor
  · apply Nat.le_floor
    calc
      (N : ℝ) = Real.exp (Real.exp (Real.log (Real.log (N : ℝ)))) := heq.symm
      _ ≤ Real.exp (Real.exp y) := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hlo)
  · have hle := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hhi)
    rw [exp_exp_add_log_two, heq] at hle
    have hfloor := (Nat.floor_le (le_of_lt (Real.exp_pos (Real.exp y)))).trans hle
    exact_mod_cast hfloor

/-- The endpoint real-window error is uniformly bounded on an actual-Roth tail.
Together with the local surrogate this is the analytic telescope's endpoint input. -/
theorem eventually_shiftedLogDeficit_real_endpoint_close :
    ∀ᶠ N : ℕ in atTop, ∀ y : ℝ,
      Real.log (Real.log (N : ℝ)) ≤ y →
      y ≤ Real.log (Real.log (N : ℝ)) + Real.log 2 →
      |shiftedLogDeficit (loglogScale y) - Real.log (rothLogDeficit N)| ≤ Real.log 2 + 1 := by
  filter_upwards [eventually_ge_atTop 3, eventually_shiftedLogDeficit_endpoint_close]
    with N hN hclose
  intro y hlo hhi
  have hwindow := loglogScale_endpoint_window hN hlo hhi
  exact hclose (loglogScale y) hwindow.1 hwindow.2

private theorem weight_sum_shifted (M : ℕ) : ∑ k ∈ Finset.range M, loglogWeight (k + 3) =
    Real.log (Real.log (M + 3 : ℝ)) - Real.log (Real.log (3 : ℝ)) := by
  let F : ℕ → ℝ := fun k => Real.log (Real.log (k + 3 : ℝ))
  have heq (k : ℕ) : loglogWeight (k + 3) = F (k + 1) - F k := by
    simp only [loglogWeight, F, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    congr 3; ring
  simp_rw [heq]
  simpa only [F, Nat.cast_zero, zero_add] using Finset.sum_range_sub F M

private theorem loglog_shifted_atTop : Tendsto (fun M : ℕ => Real.log (Real.log (M + 3 : ℝ))) atTop atTop := by
  have hcast : Tendsto (fun M : ℕ => (M + 3 : ℝ)) atTop atTop := by
    exact_mod_cast (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 3)
  exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hcast)

private theorem accumulation_range (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0)) :
    (fun M => ∑ k ∈ Finset.range M, loglogWeight (k + 3) * e (k + 3)) =o[atTop]
      (fun M => ∑ k ∈ Finset.range M, loglogWeight (k + 3)) := by
  have he' : Tendsto (fun k => e (k + 3)) atTop (𝓝 0) := he.comp (tendsto_add_atTop_nat 3)
  have hlittle : (fun k => e (k + 3)) =o[atTop] (fun _ : ℕ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).mpr he'
  have hweighted : (fun k => loglogWeight (k + 3) * e (k + 3)) =o[atTop]
      (fun k => loglogWeight (k + 3)) := by
    simpa only [one_mul, mul_one, mul_comm] using
      hlittle.mul_isBigO (isBigO_refl (fun k => loglogWeight (k + 3)) atTop)
  apply hweighted.sum_range
  · intro k
    exact (loglogWeight_pos (by omega : 3 ≤ k + 3)).le
  · have hsum (M : ℕ) : ∑ k ∈ Finset.range M, loglogWeight (k + 3) =
        Real.log (Real.log (M + 3 : ℝ)) - Real.log (Real.log (3 : ℝ)) := by
      let F : ℕ → ℝ := fun k => Real.log (Real.log (k + 3 : ℝ))
      have heq (k : ℕ) : loglogWeight (k + 3) = F (k + 1) - F k := by
        simp only [loglogWeight, F, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
        congr 3; ring
      simp_rw [heq]
      simpa only [F, Nat.cast_zero, zero_add] using Finset.sum_range_sub F M
    have hcast : Tendsto (fun M : ℕ => (M + 3 : ℝ)) atTop atTop := by
      exact_mod_cast (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 3)
    have hlog := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hcast)
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hlog.eventually (eventually_ge_atTop
      (b + Real.log (Real.log (3 : ℝ))))] with M hM
    rw [hsum]
    dsimp only [Function.comp_def] at hM
    linarith

/-- Any scalar sequence tending to zero has loglog-weighted prefix error little-o of loglog.
The interval is exactly `Icc 3 M`, and no accumulated error estimate is assumed. -/
theorem loglog_weighted_error_isLittleO (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0)) :
    (fun M => ∑ n ∈ Finset.Icc 3 M, loglogWeight n * e n) =o[atTop]
      (fun M => Real.log (Real.log (M : ℝ))) := by
  have hB : (fun M => ∑ k ∈ Finset.range M, loglogWeight (k + 3)) =O[atTop]
      (fun M => Real.log (Real.log (M + 3 : ℝ))) := by
    apply isBigO_iff.mpr
    refine ⟨2, ?_⟩
    filter_upwards [loglog_shifted_atTop.eventually
      (eventually_ge_atTop |Real.log (Real.log (3 : ℝ))|)] with M hM
    rw [weight_sum_shifted]
    have hp : 0 ≤ Real.log (Real.log (M + 3 : ℝ)) := (abs_nonneg _).trans hM
    simp only [Real.norm_eq_abs, abs_of_nonneg hp]
    calc
      _ ≤ |Real.log (Real.log (M + 3 : ℝ))| + |Real.log (Real.log (3 : ℝ))| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le
          (Real.log (Real.log (M + 3 : ℝ))) (Real.log (Real.log (3 : ℝ)))
      _ ≤ 2 * Real.log (Real.log (M + 3 : ℝ)) := by rw [abs_of_nonneg hp]; linarith
  have hR := (accumulation_range e he).trans_isBigO hB
  have hsub : Tendsto (fun M : ℕ => M - 2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b + 2)] with M hM
    omega
  have hC := hR.comp_tendsto hsub
  have hP : (fun M => ∑ k ∈ Finset.range (M - 2), loglogWeight (k + 3) * e (k + 3))
      =o[atTop] (fun M => Real.log (Real.log (M + 1 : ℝ))) := by
    apply hC.congr' (Eventually.of_forall (fun _ => rfl))
    filter_upwards [eventually_ge_atTop 3] with M hM
    dsimp only [Function.comp_def]
    have hnat : M - 2 + 3 = M + 1 := by omega
    have hcast : ((M - 2 : ℕ) : ℝ) + 3 = (M : ℝ) + 1 := by exact_mod_cast hnat
    rw [hcast]
  have hQ : (fun M => ∑ n ∈ Finset.Icc 3 M, loglogWeight n * e n)
      =o[atTop] (fun M => Real.log (Real.log (M + 1 : ℝ))) := by
    apply hP.congr' _ (Eventually.of_forall (fun _ => rfl))
    filter_upwards [eventually_ge_atTop 3] with M hM
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    have hlen : M + 1 - 3 = M - 2 := by omega
    simp only [hlen, Nat.add_comm]
  have hlog : Tendsto (fun M : ℕ => Real.log (Real.log (M : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hcomp : (fun M : ℕ => Real.log (Real.log (M + 1 : ℝ))) =O[atTop]
      (fun M => Real.log (Real.log (M : ℝ))) := by
    apply isBigO_iff.mpr
    refine ⟨2, ?_⟩
    filter_upwards [eventually_ge_atTop 3, hlog.eventually
      (eventually_ge_atTop (Real.log 2))] with M hM hlarge
    have hMp : (1 : ℝ) < M := by exact_mod_cast (by omega : 1 < M)
    have hlp : 0 < Real.log (M : ℝ) := Real.log_pos hMp
    have houter : 0 ≤ Real.log (Real.log (M : ℝ)) := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hlarge
    have hmono : Real.log (Real.log (M : ℝ)) ≤ Real.log (Real.log (M + 1 : ℝ)) :=
      Real.log_le_log hlp (Real.log_le_log (by positivity) (by linarith))
    have hsq : (M : ℝ) + 1 ≤ (M : ℝ) ^ 2 := by
      have hMreal : (3 : ℝ) ≤ M := by exact_mod_cast hM
      nlinarith
    have hi := Real.log_le_log (by positivity : 0 < (M : ℝ) + 1) hsq
    rw [Real.log_pow] at hi
    norm_num only at hi
    have ho := Real.log_le_log (Real.log_pos (by linarith : (1 : ℝ) < (M : ℝ) + 1)) hi
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hlp)] at ho
    simp only [Real.norm_eq_abs, abs_of_nonneg houter, abs_of_nonneg (houter.trans hmono)]
    linarith
  exact hQ.trans_isBigO hcomp

/-- The actual Roth weighted prefix is within little-o of loglog of every
shifted-deficit prefix sampled inside the rounded square windows. -/
theorem weightedSquareSum_sub_window_surrogate_isLittleO (m : ℕ → ℕ) (hm : ∀ n : ℕ, 3 ≤ n → n ^ 2 ≤ m n ∧ m n ≤ 2 * n ^ 2) :
    (fun M => weightedSquareSum M - ∑ n ∈ Finset.Icc 3 M,
      loglogWeight n * ((shiftedLogDeficit (m n) - shiftedLogDeficit n) / Real.log 2))
      =o[atTop] (fun M => Real.log (Real.log (M : ℝ))) := by
  let e : ℕ → ℝ := fun n => squareLogGrowth n -
    (shiftedLogDeficit (m n) - shiftedLogDeficit n) / Real.log 2
  have he : Tendsto e atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_const_nhds.div_atTop tendsto_rothLogDeficit_atTop :
      Tendsto (fun n : ℕ => 5 / rothLogDeficit n) atTop (𝓝 0))
    filter_upwards [eventually_ge_atTop 3] with n hn
    simpa only [e, Real.norm_eq_abs] using
      abs_squareLogGrowth_sub_shifted_le hn (hm n hn).1 (hm n hn).2
  have h := loglog_weighted_error_isLittleO e he
  apply h.congr_left
  intro M
  simp only [e, weightedSquareSum, mul_sub, Finset.sum_sub_distrib]

/-- In particular the actual square sample gives a fully discrete surrogate
with accumulated error little-o of loglog. This does not assert telescope cancellation. -/
theorem weightedSquareSum_sub_square_surrogate_isLittleO :
    (fun M => weightedSquareSum M - ∑ n ∈ Finset.Icc 3 M,
      loglogWeight n * ((shiftedLogDeficit (n ^ 2) - shiftedLogDeficit n) / Real.log 2))
      =o[atTop] (fun M => Real.log (Real.log (M : ℝ))) := by
  exact weightedSquareSum_sub_window_surrogate_isLittleO (fun n => n ^ 2) (fun n _ => ⟨le_rfl, by omega⟩)

/-- Any real-valued sequence composed with the loglog floor scale is measurable. -/
theorem measurable_loglogScale_comp (f : ℕ → ℝ) : Measurable (fun x : ℝ => f (loglogScale x)) := by
  exact (measurable_of_countable f).comp
    (Nat.measurable_floor.comp (Real.measurable_exp.comp Real.measurable_exp))

/-- Every real-valued sequence on the integer loglog scale is integrable on
any finite real interval: its image there is finite and bounded. -/
theorem intervalIntegrable_loglogScale_comp (f : ℕ → ℝ) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => f (loglogScale x)) volume a b := by
  have hm : Measurable (fun x : ℝ => f (loglogScale x)) :=
    (measurable_of_countable f).comp
      (Nat.measurable_floor.comp (Real.measurable_exp.comp Real.measurable_exp))
  let B : ℕ := loglogScale (max a b)
  let C : ℝ := ∑ i ∈ Finset.range (B + 1), ‖f i‖
  apply IntegrableOn.intervalIntegrable
  apply Measure.integrableOn_of_bounded
    (isCompact_uIcc.measure_ne_top) hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIcc] with x hx
  have hscale : loglogScale x ≤ B :=
    Nat.floor_mono (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hx.2))
  exact Finset.single_le_sum (fun i _ => norm_nonneg (f i))
    (Finset.mem_range.mpr (show loglogScale x < B + 1 by omega))


/-- The exact integral over one positive loglog cell is its length times
the sequence value. The upper boundary, where the floor changes, has measure zero. -/
theorem integral_loglogScale_cell (f : ℕ → ℝ) {n : ℕ} (hn : 3 ≤ n) :
    (∫ x in Real.log (Real.log (n : ℝ))..Real.log (Real.log (n + 1 : ℝ)),
      f (loglogScale x)) = loglogWeight n * f n := by
  have hab : Real.log (Real.log (n : ℝ)) < Real.log (Real.log (n + 1 : ℝ)) :=
    sub_pos.mp (loglogWeight_pos hn)
  have hne : ∀ᵐ x : ℝ, x ≠ Real.log (Real.log (n + 1 : ℝ)) := by
    rw [ae_iff]
    simp
  have heq : (∫ x in Real.log (Real.log (n : ℝ))..Real.log (Real.log (n + 1 : ℝ)),
      f (loglogScale x)) = ∫ _x in Real.log (Real.log (n : ℝ))..Real.log (Real.log (n + 1 : ℝ)), f n := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hne] with x hx
    intro hmem
    rw [Set.uIoc_of_le hab.le] at hmem
    exact congrArg f (loglogScale_eq_of_cell hn hmem.1.le (lt_of_le_of_ne hmem.2 hx))
  rw [heq, intervalIntegral.integral_const]
  rfl

/-- The exact finite loglog cell partition identifies the weighted prefix
with its real-coordinate integral; the index interval is nonempty. -/
theorem integral_loglogScale_prefix (f : ℕ → ℝ) {M : ℕ} (hM : 3 ≤ M) :
    (∫ x in Real.log (Real.log (3 : ℝ))..Real.log (Real.log (M + 1 : ℝ)),
      f (loglogScale x)) = ∑ n ∈ Finset.Icc 3 M, loglogWeight n * f n := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  have hp := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (a := fun n : ℕ => Real.log (Real.log (n : ℝ))) (show 3 ≤ M + 1 by omega)
    (fun k _ => intervalIntegrable_loglogScale_comp f _ _)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hp
  rw [← hp]
  apply Finset.sum_congr rfl
  intro n hn
  exact integral_loglogScale_cell f (Finset.mem_Ico.mp hn).1

/-- The integral of a translated difference cancels exactly to the two
endpoint windows. Integrability is derived, not supplied as a premise. -/
theorem integral_loglogScale_translation (f : ℕ → ℝ) (a b h : ℝ) :
    (∫ x in a..b, (f (loglogScale (x + h)) - f (loglogScale x))) =
      (∫ x in b..b + h, f (loglogScale x)) -
        (∫ x in a..a + h, f (loglogScale x)) := by
  have hshift : IntervalIntegrable (fun x => f (loglogScale (x + h))) volume a b :=
    (IntervalIntegrable.comp_add_right_iff (f := fun x : ℝ => f (loglogScale x))).mpr (intervalIntegrable_loglogScale_comp f _ _)
  rw [intervalIntegral.integral_sub hshift (intervalIntegrable_loglogScale_comp f a b),
    intervalIntegral.integral_comp_add_right (f := fun x : ℝ => f (loglogScale x)) h]
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_loglogScale_comp f a (a + h))
    (intervalIntegrable_loglogScale_comp f (a + h) (b + h))
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_loglogScale_comp f a b)
    (intervalIntegrable_loglogScale_comp f b (b + h))
  linarith


/-- The actual Roth weighted square prefix differs from the integrated
shifted-deficit difference by little-o of loglog. Each cell error is bounded by
its length times 5/λ(n); the accumulated bound uses qualitative Roth divergence. -/
theorem weightedSquareSum_sub_integral_isLittleO :
    (fun M : ℕ => weightedSquareSum M -
      ∫ x in Real.log (Real.log (3 : ℝ))..Real.log (Real.log (M + 1 : ℝ)),
        (shiftedLogDeficit (loglogScale (x + Real.log 2)) -
          shiftedLogDeficit (loglogScale x)) / Real.log 2)
      =o[atTop] (fun M => Real.log (Real.log (M : ℝ))) := by
  let E : ℝ → ℝ := fun x => squareLogGrowth (loglogScale x) -
    (shiftedLogDeficit (loglogScale (x + Real.log 2)) -
      shiftedLogDeficit (loglogScale x)) / Real.log 2
  have hshift (a b : ℝ) : IntervalIntegrable
      (fun x => shiftedLogDeficit (loglogScale (x + Real.log 2))) volume a b :=
    (IntervalIntegrable.comp_add_right_iff
      (f := fun x : ℝ => shiftedLogDeficit (loglogScale x))).mpr
      (intervalIntegrable_loglogScale_comp shiftedLogDeficit _ _)
  have hi (a b : ℝ) : IntervalIntegrable E volume a b :=
    (intervalIntegrable_loglogScale_comp squareLogGrowth a b).sub
      (((hshift a b).sub (intervalIntegrable_loglogScale_comp shiftedLogDeficit a b)).div_const (Real.log 2))
  have hcell (n : ℕ) (hn : 3 ≤ n) :
      ‖∫ x in Real.log (Real.log (n : ℝ))..Real.log (Real.log (n + 1 : ℝ)), E x‖ ≤
        loglogWeight n * (5 / rothLogDeficit n) := by
    have hab : Real.log (Real.log (n : ℝ)) < Real.log (Real.log (n + 1 : ℝ)) :=
      sub_pos.mp (loglogWeight_pos hn)
    have hne : ∀ᵐ x : ℝ, x ≠ Real.log (Real.log (n + 1 : ℝ)) := by
      rw [ae_iff]
      simp
    have hb : ∀ᵐ x : ℝ, x ∈ Set.uIoc (Real.log (Real.log (n : ℝ)))
        (Real.log (Real.log (n + 1 : ℝ))) → ‖E x‖ ≤ 5 / rothLogDeficit n := by
      filter_upwards [hne] with x hx
      intro hmem
      rw [Set.uIoc_of_le hab.le] at hmem
      have heq := loglogScale_eq_of_cell hn hmem.1.le (lt_of_le_of_ne hmem.2 hx)
      have hn' : 3 ≤ loglogScale x := by rw [heq]; exact hn
      have hw := loglogScale_shift_window hn'
      have hb := abs_squareLogGrowth_sub_shifted_le hn' hw.1 hw.2.le
      simpa only [E, Real.norm_eq_abs, heq] using hb
    have hb' := intervalIntegral.norm_integral_le_of_norm_le_const_ae hb
    simpa only [show Real.log (Real.log (n + 1 : ℝ)) - Real.log (Real.log (n : ℝ)) = loglogWeight n from rfl, abs_of_pos (loglogWeight_pos hn), mul_comm] using hb'
  have hbound : (fun M : ℕ => weightedSquareSum M -
      ∫ x in Real.log (Real.log (3 : ℝ))..Real.log (Real.log (M + 1 : ℝ)),
        (shiftedLogDeficit (loglogScale (x + Real.log 2)) -
          shiftedLogDeficit (loglogScale x)) / Real.log 2)
      =O[atTop] (fun M => ∑ n ∈ Finset.Icc 3 M, loglogWeight n * (5 / rothLogDeficit n)) := by
    apply isBigO_iff.mpr
    refine ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop 3] with M hM
    have hrep : weightedSquareSum M -
        (∫ x in Real.log (Real.log (3 : ℝ))..Real.log (Real.log (M + 1 : ℝ)),
          (shiftedLogDeficit (loglogScale (x + Real.log 2)) -
            shiftedLogDeficit (loglogScale x)) / Real.log 2) =
        ∫ x in Real.log (Real.log (3 : ℝ))..Real.log (Real.log (M + 1 : ℝ)), E x := by
      rw [show weightedSquareSum M = ∫ x in Real.log (Real.log (3 : ℝ))..
        Real.log (Real.log (M + 1 : ℝ)), squareLogGrowth (loglogScale x) from
        (integral_loglogScale_prefix squareLogGrowth hM).symm]
      exact (intervalIntegral.integral_sub
        (intervalIntegrable_loglogScale_comp squareLogGrowth _ _)
        (((hshift _ _).sub (intervalIntegrable_loglogScale_comp shiftedLogDeficit _ _)).div_const _)).symm
    rw [hrep, one_mul]
    have hp := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun n : ℕ => Real.log (Real.log (n : ℝ))) (show 3 ≤ M + 1 by omega)
      (fun k _ => hi _ _)
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hp
    rw [← hp, Finset.Ico_add_one_right_eq_Icc]
    calc
      _ ≤ ∑ n ∈ Finset.Icc 3 M, ‖∫ x in Real.log (Real.log (n : ℝ))..
          Real.log (Real.log (n + 1 : ℝ)), E x‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 3 M, loglogWeight n * (5 / rothLogDeficit n) := by
        apply Finset.sum_le_sum
        intro n hn
        exact hcell n (Finset.mem_Icc.mp hn).1
      _ ≤ ‖∑ n ∈ Finset.Icc 3 M, loglogWeight n * (5 / rothLogDeficit n)‖ := le_abs_self _
  exact hbound.trans_isLittleO (loglog_weighted_error_isLittleO (fun n => 5 / rothLogDeficit n)
    (tendsto_const_nhds.div_atTop tendsto_rothLogDeficit_atTop))

/-- The actual Roth weighted square telescope: S(M) − log λ(M+1) is
little-o of loglog M as natural M tends to infinity. Translation by log 2
cancels exactly; there is no extra 1/log 2 factor in the endpoint term.
This establishes the weighted-telescope input, not its density or critical-scale corollaries. -/
theorem weightedSquareSum_sub_logDeficit_isLittleO :
    (fun M : ℕ => weightedSquareSum M - Real.log (rothLogDeficit (M + 1)))
      =o[atTop] (fun M => Real.log (Real.log (M : ℝ))) := by
  let h : ℝ := Real.log 2
  let L : ℝ → ℝ := fun x => shiftedLogDeficit (loglogScale x)
  let A : ℕ → ℝ := fun N => Real.log (Real.log (N : ℝ))
  let B : ℕ → ℝ := fun N => (∫ x in A N..A N + h, L x) / h - Real.log (rothLogDeficit N)
  let K : ℝ := (∫ x in A 3..A 3 + h, L x) / h
  have hh : 0 < h := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hB : B =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    apply isBigO_iff.mpr
    refine ⟨h + 1, ?_⟩
    filter_upwards [eventually_shiftedLogDeficit_real_endpoint_close] with N hN
    have hb : ∀ x ∈ Set.uIoc (A N) (A N + h),
        ‖L x - Real.log (rothLogDeficit N)‖ ≤ h + 1 := by
      intro x hx
      rw [Set.uIoc_of_le (by linarith : A N ≤ A N + h)] at hx
      simpa only [L, h, Real.norm_eq_abs] using hN x hx.1.le hx.2
    have hb' := intervalIntegral.norm_integral_le_of_norm_le_const hb
    have hrep : B N = (∫ x in A N..A N + h, L x - Real.log (rothLogDeficit N)) / h := by
      rw [intervalIntegral.integral_sub (intervalIntegrable_loglogScale_comp shiftedLogDeficit _ _)
        (intervalIntegrable_const), intervalIntegral.integral_const]
      simp only [smul_eq_mul, add_sub_cancel_left]
      dsimp only [B, L]
      field_simp
    rw [hrep, norm_div]
    simp only [Real.norm_eq_abs, abs_of_pos hh, norm_one, mul_one]
    simp only [add_sub_cancel_left, abs_of_pos hh] at hb'
    simpa only [Real.norm_eq_abs, norm_one, mul_one] using
      (div_le_iff₀ hh).mpr hb'
  have hlog : Tendsto (fun M : ℕ => Real.log (Real.log (M : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hnorm : Tendsto (fun M : ℕ => ‖Real.log (Real.log (M : ℝ))‖) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hlog.eventually (eventually_ge_atTop b)] with M hM
    exact hM.trans (le_abs_self _)
  have hconst (c : ℝ) : (fun _ : ℕ => c) =o[atTop]
      (fun M => Real.log (Real.log (M : ℝ))) :=
    isLittleO_const_left.mpr (Or.inr hnorm)
  have hB' : (fun M : ℕ => B (M + 1)) =o[atTop]
      (fun M => Real.log (Real.log (M : ℝ))) :=
    (hB.comp_tendsto (tendsto_add_atTop_nat 1)).trans_isLittleO (hconst 1)
  have htotal := weightedSquareSum_sub_integral_isLittleO.add (hB'.sub (hconst K))
  apply htotal.congr_left
  intro M
  have ht := integral_loglogScale_translation shiftedLogDeficit (A 3) (A (M + 1)) h
  have hd : (∫ x in A 3..A (M + 1), (L (x + h) - L x) / h) =
      ((∫ x in A (M + 1)..A (M + 1) + h, L x) - (∫ x in A 3..A 3 + h, L x)) / h := by
    rw [intervalIntegral.integral_div]
    exact congrArg (fun z : ℝ => z / h) ht
  dsimp only [B, K, A, L, h] at hd ⊢
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hd ⊢
  rw [hd]
  ring

end
end Erdos142
