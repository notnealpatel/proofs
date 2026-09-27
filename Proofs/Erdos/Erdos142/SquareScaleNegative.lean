import Erdos.Erdos142.PowerLawObstruction
import Erdos.Erdos142.SquareScaleCriterion
import Erdos.Erdos142.SquareScaleProduct

set_option autoImplicit false

open Filter
open scoped Topology

namespace Erdos142

noncomputable section

/-- A positive sequence bounded by a geometric progression cannot grow eventually at a
strictly larger geometric rate. -/
theorem frequently_le_geometric_of_eventually_upper
    (a : ℕ → ℝ) (s q C : ℝ) (hs : 0 < s) (hsq : s < q)
    (hpos : ∀ᶠ k : ℕ in atTop, 0 < a k)
    (hupper : ∀ᶠ k : ℕ in atTop, a k ≤ C * s ^ k) :
    ∃ᶠ k : ℕ in atTop, a (k + 1) ≤ q * a k := by
  rw [Filter.Frequently]
  intro hnever
  have hbad : ∀ᶠ k : ℕ in atTop, q * a k < a (k + 1) := by
    filter_upwards [hnever] with k hk
    exact lt_of_not_ge hk
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hbad.and (hpos.and hupper))
  have hstart : 0 < a K := (hK K le_rfl).2.1
  have hq : 0 < q := lt_trans hs hsq
  have hgeom : ∀ n : ℕ, q ^ n * a K ≤ a (K + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hn := (hK (K + n) (by omega)).1
      have hh := mul_le_mul_of_nonneg_left ih hq.le
      rw [pow_succ, Nat.add_succ]
      nlinarith [hh]
  have hr : 1 < q / s := (one_lt_div hs).2 hsq
  have hpow : Tendsto (fun n : ℕ => (q / s) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hr
  obtain ⟨n, hn⟩ := (hpow.eventually (eventually_gt_atTop (C * s ^ K / a K))).exists
  have hu := (hK (K + n) (by omega)).2.2
  have hg := hgeom n
  have hsp : 0 < s ^ n := pow_pos hs _
  have hsk : 0 < s ^ K := pow_pos hs _
  have hqn : 0 < q ^ n := pow_pos hq _
  rw [pow_add] at hu
  have hratio : (q / s) ^ n * a K ≤ C * s ^ K := by
    rw [div_pow, div_mul_eq_mul_div]
    apply (div_le_iff₀ hsp).2
    calc
      q ^ n * a K ≤ a (K + n) := hg
      _ ≤ C * (s ^ K * s ^ n) := hu
      _ = (C * s ^ K) * s ^ n := by ring
  have hcontra : (q / s) ^ n ≤ C * s ^ K / a K :=
    (le_div_iff₀ hstart).2 hratio
  exact (not_lt_of_ge hcontra) hn

/-- For a base `M ≥ 1`, the square-root logarithmic scale grows geometrically along
iterated squares.  The hypothesis is not vacuous decoration: at `M = 0` the statement
would only hold because `Real.log` is totalized by `Real.log 0 = 0`, i.e. it would be
about the junk value rather than about a logarithmic scale.  It is used in the proof to
guarantee that the logarithmic factor under the square root is nonnegative. -/
theorem sqrt_log_iterated_square (M k : ℕ) (hM : 1 ≤ M) :
    Real.sqrt (Real.log ((M ^ (2 ^ k) : ℕ) : ℝ)) =
      Real.sqrt (Real.log (M : ℝ)) * (Real.sqrt 2) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsq : M ^ (2 ^ (k + 1)) = (M ^ (2 ^ k)) ^ 2 := by
      rw [pow_succ, pow_mul]
    have hlog : 0 ≤ Real.log ((M ^ (2 ^ k) : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast one_le_pow₀ hM)
    rw [hsq, Nat.cast_pow, Real.log_pow]
    norm_cast
    rw [show (2 : ℝ) * Real.log ((M ^ (2 ^ k) : ℕ) : ℝ) =
      Real.log ((M ^ (2 ^ k) : ℕ) : ℝ) * 2 by ring,
      Real.sqrt_mul hlog, ih, pow_succ]
    ring

/-- Roth's theorem makes the logarithmic deficit positive eventually, also on any
iterated-square sequence with base at least three. -/
theorem eventually_pos_rothLogDeficit_iterated_square (M : ℕ) (hM : 3 ≤ M) :
    ∀ᶠ k : ℕ in atTop, 0 < rothLogDeficit (M ^ (2 ^ k)) := by
  have htower : Tendsto (fun k : ℕ => M ^ (2 ^ k)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by omega : 1 < M)).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by omega : 1 < (2 : ℕ)))
  have hsmall : ∀ᶠ N : ℕ in atTop,
      (rothNumberNat N : ℝ) / (N : ℝ) < 1 :=
    tendsto_rothNumberNat_div_nat_zero.eventually_lt_const (by norm_num)
  filter_upwards [htower.eventually hsmall] with k hk
  have hNk : 1 ≤ M ^ (2 ^ k) := one_le_pow₀ (by omega : 1 ≤ M)
  have hr : (0 : ℝ) < (rothNumberNat (M ^ (2 ^ k)) : ℝ) :=
    rothNumberNat_pos_real hNk
  have hN : (0 : ℝ) < ((M ^ (2 ^ k) : ℕ) : ℝ) := by positivity
  have hlt : (rothNumberNat (M ^ (2 ^ k)) : ℝ) < (M ^ (2 ^ k) : ℕ) := by
    have := (div_lt_iff₀ hN).1 hk
    nlinarith
  rw [rothLogDeficit]
  exact Real.log_pos ((one_lt_div hr).2 hlt)

/-- EHPS bounds the logarithmic Roth deficit along iterated squares by the
square-root geometric progression. -/
theorem eventually_rothLogDeficit_iterated_square_le (M : ℕ) (hM : 3 ≤ M) :
    ∀ᶠ k : ℕ in atTop,
      rothLogDeficit (M ^ (2 ^ k)) ≤
        ((torusLeadingConstant + 1) * Real.sqrt (Real.log (M : ℝ))) *
          (Real.sqrt 2) ^ k := by
  have htower : Tendsto (fun k : ℕ => M ^ (2 ^ k)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by omega : 1 < M)).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by omega : 1 < (2 : ℕ)))
  filter_upwards [htower.eventually eventually_le_normalizedDeficit_rothNumberNat]
    with k hk
  have hN : 1 < (M ^ (2 ^ k) : ℕ) := by
    have he : 0 < 2 ^ k := pow_pos (by omega : 0 < (2 : ℕ)) _
    exact one_lt_pow₀ (by omega : 1 < M) (by omega)
  have hlog : 0 < Real.log ((M ^ (2 ^ k) : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hsqrt : 0 < Real.sqrt (Real.log ((M ^ (2 ^ k) : ℕ) : ℝ)) :=
    Real.sqrt_pos.2 hlog
  have hbound : rothLogDeficit (M ^ (2 ^ k)) ≤
      (torusLeadingConstant + 1) * Real.sqrt (Real.log ((M ^ (2 ^ k) : ℕ) : ℝ)) := by
    exact (div_le_iff₀ hsqrt).1 (show
      rothLogDeficit (M ^ (2 ^ k)) /
        Real.sqrt (Real.log ((M ^ (2 ^ k) : ℕ) : ℝ)) ≤ torusLeadingConstant + 1 by
      simpa only [normalizedDeficit, logDeficit, rothLogDeficit] using hk)
  rw [sqrt_log_iterated_square M k (by omega)] at hbound
  convert hbound using 1; ring

/-- Roth's density theorem forces the logarithmic deficit to diverge. -/
theorem tendsto_rothLogDeficit_atTop : Tendsto rothLogDeficit atTop atTop := by
  let q : ℕ → ℝ := fun N => (rothNumberNat N : ℝ) / (N : ℝ)
  have hq0 : Tendsto q atTop (𝓝 0) := tendsto_rothNumberNat_div_nat_zero
  have hqpos : ∀ᶠ N : ℕ in atTop, 0 < q N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact div_pos (rothNumberNat_pos_real hN) (by exact_mod_cast hN)
  have hq : Tendsto q atTop (𝓝[Set.Ioi (0 : ℝ)] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hq0, hqpos⟩
  have hlog : Tendsto (fun N => Real.log (q N)) atTop atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hq
  have hneg : Tendsto (fun N => -Real.log (q N)) atTop atTop := by
    simpa only [Function.comp_def] using tendsto_neg_atBot_atTop.comp hlog
  apply hneg.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  dsimp [rothLogDeficit, q]
  rw [show (N : ℝ) / (rothNumberNat N : ℝ) =
      ((rothNumberNat N : ℝ) / (N : ℝ))⁻¹ by rw [inv_div], Real.log_inv]

/-- For every fixed base and every rate strictly above `√2`, infinitely many
iterated squares have logarithmic Roth deficit growth at most that rate. -/
theorem frequently_rothLogDeficit_iterated_square_le
    (M : ℕ) (hM : 3 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ k : ℕ in atTop,
      rothLogDeficit (M ^ (2 ^ (k + 1))) ≤
        (Real.sqrt 2 + ε) * rothLogDeficit (M ^ (2 ^ k)) := by
  exact frequently_le_geometric_of_eventually_upper
    (fun k => rothLogDeficit (M ^ (2 ^ k))) (Real.sqrt 2)
    (Real.sqrt 2 + ε)
    ((torusLeadingConstant + 1) * Real.sqrt (Real.log (M : ℝ)))
    (Real.sqrt_pos.2 (by norm_num)) (by linarith)
    (eventually_pos_rothLogDeficit_iterated_square M hM)
    (eventually_rothLogDeficit_iterated_square_le M hM)

/-- The precise negative square-scale deficit inequality holds infinitely often
for every `0 < ε < 2 - √2`. -/
theorem frequently_rothLogDeficit_square_le_negative_fraction
    (M : ℕ) (hM : 3 ≤ M) (ε : ℝ)
    (hε : 0 < ε) (hεmax : ε < 2 - Real.sqrt 2) :
    ∃ᶠ k : ℕ in atTop,
      rothLogDeficit (M ^ (2 ^ (k + 1))) -
        2 * rothLogDeficit (M ^ (2 ^ k)) ≤
          -(2 - Real.sqrt 2 - ε) * rothLogDeficit (M ^ (2 ^ k)) := by
  apply (frequently_rothLogDeficit_iterated_square_le M hM ε hε).mono
  intro k hk
  have hrate : Real.sqrt 2 + ε < 2 := by linarith
  nlinarith [hrate]

/-- The square-scale defect equals the difference between successive log deficits. -/
theorem squareScaleDefect_eq_rothLogDeficit_sub (N : ℕ) (hN : 1 ≤ N) :
    squareScaleDefect N = rothLogDeficit (N ^ 2) - 2 * rothLogDeficit N := by
  have hN2 : 1 ≤ N ^ 2 := one_le_pow₀ hN
  have hr : (rothNumberNat N : ℝ) ≠ 0 :=
    ne_of_gt (rothNumberNat_pos_real hN)
  have hr2 : (rothNumberNat (N ^ 2) : ℝ) ≠ 0 :=
    ne_of_gt (rothNumberNat_pos_real hN2)
  rw [squareScaleDefect, Real.log_div (pow_ne_zero 2 hr) hr2,
    Real.log_pow, rothLogDeficit_eq hN2, rothLogDeficit_eq hN,
    Nat.cast_pow, Real.log_pow]
  push_cast
  ring

/-- The square-scale multiplicativity defect of the iterated-square Roth number is
bounded above by the negative `(2 - √2 - ε)` multiple of its logarithmic deficit,
infinitely often, for every `0 < ε < 2 - √2`. -/
theorem frequently_squareScaleDefect_iterated_square_le_negative_fraction
    (M : ℕ) (hM : 3 ≤ M) (ε : ℝ)
    (hε : 0 < ε) (hεmax : ε < 2 - Real.sqrt 2) :
    ∃ᶠ k : ℕ in atTop,
      squareScaleDefect (M ^ (2 ^ k)) ≤
        -(2 - Real.sqrt 2 - ε) * rothLogDeficit (M ^ (2 ^ k)) := by
  apply (frequently_rothLogDeficit_square_le_negative_fraction M hM ε hε hεmax).mono
  intro k hk
  have hN : 1 ≤ M ^ (2 ^ k) := one_le_pow₀ (by omega : 1 ≤ M)
  have hsq : (M ^ (2 ^ k)) ^ 2 = M ^ (2 ^ (k + 1)) := by
    symm
    rw [pow_succ, pow_mul]
  rw [squareScaleDefect_eq_rothLogDeficit_sub _ hN, hsq]
  exact hk

/-- The square-scale log-deficit difference is arbitrarily negative infinitely often.
This uses only Roth's density limit and the accepted EHPS upper envelope. -/
theorem frequently_rothLogDeficit_square_sub_two_lt
    (M : ℕ) (hM : 3 ≤ M) (ε : ℝ)
    (hε : 0 < ε) (hεmax : ε < 2 - Real.sqrt 2) (B : ℝ) :
    ∃ᶠ k : ℕ in atTop,
      rothLogDeficit (M ^ (2 ^ (k + 1))) -
        2 * rothLogDeficit (M ^ (2 ^ k)) < -B := by
  let c : ℝ := 2 - (Real.sqrt 2 + ε)
  have hc : 0 < c := by dsimp [c]; linarith
  have htower : Tendsto (fun k : ℕ => M ^ (2 ^ k)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by omega : 1 < M)).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by omega : 1 < (2 : ℕ)))
  have hlarge : ∀ᶠ k : ℕ in atTop,
      B / c < rothLogDeficit (M ^ (2 ^ k)) :=
    (tendsto_rothLogDeficit_atTop.comp htower).eventually
      (eventually_gt_atTop (B / c))
  have hfreq := (frequently_rothLogDeficit_iterated_square_le M hM ε hε).and_eventually hlarge
  apply hfreq.mono
  intro k hk
  have hB : B < c * rothLogDeficit (M ^ (2 ^ k)) :=
    by simpa only [mul_comm] using (div_lt_iff₀ hc).1 hk.2
  dsimp [c] at hB
  nlinarith [hk.1]

/-- At a fixed iterated-square base, the actual square-scale multiplicativity
logarithm is less than every negative threshold infinitely often. -/
theorem frequently_squareScaleDefect_lt_neg
    (M : ℕ) (hM : 3 ≤ M) (B : ℝ) :
    ∃ᶠ k : ℕ in atTop, squareScaleDefect (M ^ (2 ^ k)) < -B := by
  have hε : (0 : ℝ) < 1 / 2 := by norm_num
  have hεmax : (1 / 2 : ℝ) < 2 - Real.sqrt 2 := by
    have hsq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hnonneg := Real.sqrt_nonneg 2
    nlinarith
  apply (frequently_rothLogDeficit_square_sub_two_lt M hM (1 / 2) hε hεmax B).mono
  intro k hk
  have hN : 1 ≤ M ^ (2 ^ k) := one_le_pow₀ (by omega : 1 ≤ M)
  have hsq : (M ^ (2 ^ k)) ^ 2 = M ^ (2 ^ (k + 1)) := by
    symm
    rw [pow_succ, pow_mul]
  rw [squareScaleDefect_eq_rothLogDeficit_sub _ hN, hsq]
  exact hk

/-- Square-scale Roth ratios are not eventually bounded, even on each
iterated-square sequence starting from a base at least three. -/
theorem frequently_rothNumberNat_square_ratio_gt
    (M : ℕ) (hM : 3 ≤ M) (C : ℝ) (hC : 0 < C) :
    ∃ᶠ k : ℕ in atTop,
      C < (rothNumberNat ((M ^ (2 ^ k)) ^ 2) : ℝ) /
        (rothNumberNat (M ^ (2 ^ k)) : ℝ) ^ 2 := by
  apply (frequently_squareScaleDefect_lt_neg M hM (Real.log C)).mono
  intro k hk
  let N : ℕ := M ^ (2 ^ k)
  have hN : 1 ≤ N := one_le_pow₀ (by omega : 1 ≤ M)
  have hN2 : 1 ≤ N ^ 2 := one_le_pow₀ hN
  have hr : (0 : ℝ) < (rothNumberNat N : ℝ) := rothNumberNat_pos_real hN
  have hr2 : (0 : ℝ) < (rothNumberNat (N ^ 2) : ℝ) :=
    rothNumberNat_pos_real hN2
  have hden : (0 : ℝ) < (rothNumberNat N : ℝ) ^ 2 := pow_pos hr _
  have hsmall : (rothNumberNat N : ℝ) ^ 2 /
      (rothNumberNat (N ^ 2) : ℝ) < C⁻¹ := by
    apply (Real.log_lt_log_iff (div_pos hden hr2) (inv_pos.2 hC)).1
    rw [Real.log_inv]
    exact hk
  exact (lt_div_iff₀ hden).2 (by
    have hh := (div_lt_iff₀ hr2).1 hsmall
    have hprod := mul_lt_mul_of_pos_left hh hC
    have hcne : C ≠ 0 := ne_of_gt hC
    field_simp at hprod ⊢
    nlinarith)

/-- Eventual boundedness of `r₃(N²)/r₃(N)²` is false. -/
theorem not_eventually_bounded_rothNumberNat_square_ratio :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      (rothNumberNat (N ^ 2) : ℝ) / (rothNumberNat N : ℝ) ^ 2 ≤ C := by
  rintro ⟨C, hC, hbound⟩
  have htower : Tendsto (fun k : ℕ => 3 ^ (2 ^ k)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by omega : 1 < (3 : ℕ))).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by omega : 1 < (2 : ℕ)))
  have hratio := frequently_rothNumberNat_square_ratio_gt 3 (by omega) C hC
  exact hratio (htower.eventually hbound |>.mono (fun k hk => not_lt_of_ge hk))

/-- The positivity and admissible-rate hypotheses are simultaneously realized
by the concrete base `3` and rate `1/2`. -/
example : (3 : ℕ) ≤ 3 ∧ (0 : ℝ) < 1 / 2 ∧
    (1 / 2 : ℝ) < 2 - Real.sqrt 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hnonneg := Real.sqrt_nonneg 2
  constructor
  · omega
  constructor
  · norm_num
  · nlinarith

#check @Erdos142.frequently_rothLogDeficit_iterated_square_le
#check @Erdos142.frequently_squareScaleDefect_lt_neg

end
end Erdos142
