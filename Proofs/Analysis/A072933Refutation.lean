/-
# A072933: refutation of Cloitre's limit conjecture

OEIS A072933 (Benoit Cloitre, 2002-08-13) consists of positive integers `m`
for which the least positive `k` satisfying
`⌊(1+1/k)^m⌋ = ⌊(1+1/m)^k⌋` differs from `round(91m/100)`.
The entry conjectures `a(n)/n → 10`.

For every `m ≥ 18000`, the rounded candidate is not a solution: its two
floors are respectively at least `3` and at most `2`. Thus every such `m`
is a member, the enumeration is eventually affine, and `a(n)/n → 1`.
The threshold is a sufficient bound, not a sharpness claim.

The floor equality is computed in `ℚ`, with positive `k` to exclude the
value of `1/0`; membership explicitly requires `m ≥ 1`. Mathlib's rational
`round` rounds ties up (ties occur at `m ≡ 50 mod 100`). The refutation is
insensitive to tie-breaking. The OEIS offset is 1: `a 1 = 39`; `a 0` is
irrelevant to the limit.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A072933Refutation

open Filter Topology

/-! ## Definition layer -/

/-- `Matches m k` holds when `floor((1+1/k)^m) = floor((1+1/m)^k)`, computed
exactly in `ℚ`. -/
def Matches (m k : ℕ) : Prop := ⌊(1 + 1 / (k : ℚ)) ^ m⌋ = ⌊(1 + 1 / (m : ℚ)) ^ k⌋

instance (m k : ℕ) : Decidable (Matches m k) := by unfold Matches; infer_instance

/-- A positive solution `k` always exists: `k = m` for `m ≥ 1`, and `k = 1`
for `m = 0`. -/
theorem exists_matches (m : ℕ) : ∃ k, 1 ≤ k ∧ Matches m k := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨1, le_rfl, by simp [Matches]⟩
  · exact ⟨m, hm, rfl⟩

/-- The least positive `k` with `floor((1+1/k)^m) = floor((1+1/m)^k)`. -/
def leastK (m : ℕ) : ℕ := Nat.find (exists_matches m)

/-- Membership in A072933: `m ≥ 1` and the least `k` differs from
`round(91m/100)`. -/
def InS (m : ℕ) : Prop := 1 ≤ m ∧ (leastK m : ℤ) ≠ round ((91 * m : ℚ) / 100)

/-- `a n` is the `n`-th term of A072933 (OEIS offset 1, so `a 1 = 39`). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth InS (n - 1)

/-! ## Integer bridge (used for decidability and the analytic estimate) -/

/-- `Matches` in integer arithmetic: `(k+1)^m / k^m = (m+1)^k / m^k`
(natural-number floor division). -/
def MatchesN (m k : ℕ) : Prop := (k + 1) ^ m / k ^ m = (m + 1) ^ k / m ^ k

instance (m k : ℕ) : Decidable (MatchesN m k) := by unfold MatchesN; infer_instance

/-- `floor((1+1/a)^b) = (a+1)^b / a^b` for `a ≥ 1`. -/
theorem floor_one_add_inv_pow (a b : ℕ) (ha : 1 ≤ a) :
    ⌊(1 + 1 / (a : ℚ)) ^ b⌋ = (((a + 1) ^ b / a ^ b : ℕ) : ℤ) := by
  have ha' : (a : ℚ) ≠ 0 := by positivity
  have h : (1 + 1 / (a : ℚ)) ^ b = (((a + 1) ^ b : ℕ) : ℤ) / ((a ^ b : ℕ) : ℚ) := by
    push_cast
    rw [← div_pow]
    congr 1
    field_simp
  rw [h, Rat.floor_intCast_div_natCast]
  push_cast
  rfl

/-- For `m, k ≥ 1`, `Matches m k` is equivalent to its integer form. -/
theorem matches_iff (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) : Matches m k ↔ MatchesN m k := by
  unfold Matches MatchesN
  rw [floor_one_add_inv_pow k m hk, floor_one_add_inv_pow m k hm]
  exact Nat.cast_inj

/-- `round(91m/100) = (91m + 50) / 100` (half-up rounding). -/
theorem round_mul_91_div_100 (m : ℕ) :
    round ((91 * m : ℚ) / 100) = (((91 * m + 50) / 100 : ℕ) : ℤ) := by
  rw [_root_.round_eq]
  have h : (91 * m : ℚ) / 100 + 1 / 2 = (((91 * m + 50 : ℕ) : ℤ) : ℚ) / ((100 : ℕ) : ℚ) := by
    push_cast
    ring
  rw [h, Rat.floor_intCast_div_natCast]
  push_cast
  rfl

/-- Decidable integer form of `InS`: `m ≥ 1` and `r = round(91m/100)` is not
the least positive solution. -/
def InSN (m : ℕ) : Prop :=
  1 ≤ m ∧ ¬ ((1 ≤ (91 * m + 50) / 100 ∧ MatchesN m ((91 * m + 50) / 100)) ∧
    ∀ j < (91 * m + 50) / 100, ¬ (1 ≤ j ∧ MatchesN m j))

/-- `InS` agrees with its integer form `InSN`. -/
theorem inS_iff_inSN (m : ℕ) : InS m ↔ InSN m := by
  unfold InS InSN
  rw [round_mul_91_div_100, Ne, Nat.cast_inj, leastK, Nat.find_eq_iff]
  constructor
  · rintro ⟨hm, h⟩
    refine ⟨hm, fun ⟨⟨h1, h2⟩, h3⟩ => h ⟨⟨h1, (matches_iff m _ hm h1).2 h2⟩,
      fun j hj ⟨hj1, hj2⟩ => h3 j hj ⟨hj1, (matches_iff m j hm hj1).1 hj2⟩⟩⟩
  · rintro ⟨hm, h⟩
    refine ⟨hm, fun ⟨⟨h1, h2⟩, h3⟩ => h ⟨⟨h1, (matches_iff m _ hm h1).1 h2⟩,
      fun j hj ⟨hj1, hj2⟩ => h3 j hj ⟨hj1, (matches_iff m j hm hj1).2 hj2⟩⟩⟩

instance : DecidablePred InSN := by unfold InSN; infer_instance

instance : DecidablePred InS := fun m => decidable_of_iff _ (inS_iff_inSN m).symm

/-! ## Examples from the listed terms -/

example : round ((91 * ((50 : ℕ) : ℚ)) / 100) = 46 :=
  (round_mul_91_div_100 50).trans (by norm_num)

-- For `m = 39` the least solution is `k = 36`, while `round(91·39/100) = 35`.
example : leastK 39 = 36 := by
  rw [leastK, Nat.find_eq_iff]
  refine ⟨⟨by norm_num, (matches_iff 39 36 (by norm_num) (by norm_num)).2 (by decide)⟩, ?_⟩
  have hN : ∀ j < 36, 1 ≤ j → ¬ MatchesN 39 j := by decide
  rintro j hj ⟨hj1, hjm⟩
  exact hN j hj hj1 ((matches_iff 39 j (by norm_num) hj1).1 hjm)

example : ¬ InS 38 := by decide

example : InS 39 := by decide

example : ¬ InS 40 := by decide

example : a 1 = 39 := by
  have h0 : Nat.count InS 39 = 0 := by decide
  have h := Nat.nth_count (p := InS) (n := 39) (by decide)
  rw [h0] at h
  exact h

example : a 2 = 128 := by
  have h0 : Nat.count InS 128 = 1 := by decide +kernel
  have h := Nat.nth_count (p := InS) (n := 128) (by decide)
  rw [h0] at h
  exact h

example : a 3 = 139 := by
  have h0 : Nat.count InS 139 = 2 := by decide +kernel
  have h := Nat.nth_count (p := InS) (n := 139) (by decide)
  rw [h0] at h
  exact h

/-! ## The conjecture -/

/-- **Cloitre's conjecture (A072933, Benoit Cloitre, Aug 13 2002).**

Verbatim: "Conjecture: lim n -> infinity a(n)/n = 10". -/
def Conjecture : Prop := Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 10)

/-! ## Analytic estimates -/

/-- If `r ≥ 1` and `2747 (r+1) ≤ 2500 m`, then `(1+1/r)^m ≥ 3`.  Uses
`log(1+1/r) ≥ 1/(r+1)` and `exp(1.0988) ≥ e·(1 + 0.0988 + 0.0988²/2) ≥ 3`. -/
theorem three_le_one_add_inv_pow (m r : ℕ) (hr : 1 ≤ r) (h : 2747 * (r + 1) ≤ 2500 * m) :
    (3 : ℝ) ≤ (1 + 1 / (r : ℝ)) ^ m := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hx : (0 : ℝ) < 1 + 1 / (r : ℝ) := by positivity
  have hsub : 1 - (1 + 1 / (r : ℝ))⁻¹ = 1 / ((r : ℝ) + 1) := by
    field_simp
    ring
  have hlog : 1 / ((r : ℝ) + 1) ≤ Real.log (1 + 1 / (r : ℝ)) :=
    hsub ▸ Real.one_sub_inv_le_log_of_pos hx
  have hcast : (2747 : ℝ) * ((r : ℝ) + 1) ≤ 2500 * (m : ℝ) := by exact_mod_cast h
  have hc : (2747 / 2500 : ℝ) ≤ m * Real.log (1 + 1 / (r : ℝ)) := by
    calc (2747 / 2500 : ℝ) ≤ m * (1 / ((r : ℝ) + 1)) := by
          rw [mul_one_div, le_div_iff₀ (by positivity)]
          linarith
      _ ≤ m * Real.log (1 + 1 / (r : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg m)
  have he : (3 : ℝ) ≤ Real.exp (2747 / 2500) := by
    have hsplit : Real.exp (2747 / 2500) = Real.exp 1 * Real.exp (247 / 2500) := by
      rw [← Real.exp_add]
      norm_num
    rw [hsplit]
    calc (3 : ℝ) ≤ 2.7182818283 * (1 + 247 / 2500 + (247 / 2500) ^ 2 / 2) := by norm_num
      _ ≤ Real.exp 1 * Real.exp (247 / 2500) :=
          mul_le_mul Real.exp_one_gt_d9.le (Real.quadratic_le_exp_of_nonneg (by norm_num))
            (by norm_num) (Real.exp_pos 1).le
  calc (3 : ℝ) ≤ Real.exp (2747 / 2500) := he
    _ ≤ Real.exp (m * Real.log (1 + 1 / (r : ℝ))) := Real.exp_le_exp.2 hc
    _ = (1 + 1 / (r : ℝ)) ^ m := by rw [Real.exp_nat_mul, Real.exp_log hx]

/-- If `1 ≤ m` and `r ≤ m`, then `(1+1/m)^r ≤ (1+1/m)^m ≤ e < 3`. -/
theorem one_add_inv_pow_lt_three (m r : ℕ) (hm : 1 ≤ m) (hr : r ≤ m) :
    (1 + 1 / (m : ℝ)) ^ r < 3 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  calc (1 + 1 / (m : ℝ)) ^ r ≤ (1 + 1 / (m : ℝ)) ^ m :=
        pow_le_pow_right₀ (by simp) hr
    _ ≤ Real.exp (1 / (m : ℝ)) ^ m := by
        apply pow_le_pow_left₀ (by positivity)
        rw [add_comm]
        exact Real.add_one_le_exp _
    _ = Real.exp 1 := by
        rw [← Real.exp_nat_mul]
        congr 1
        field_simp
    _ < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)

/-- For `m ≥ 18000`, `k = round(91m/100)` is not a solution:
`floor((1+1/k)^m) ≥ 3 > 2 ≥ floor((1+1/m)^k)`. -/
theorem not_matchesN_of_le (m : ℕ) (hm : 18000 ≤ m) : ¬ MatchesN m ((91 * m + 50) / 100) := by
  set r := (91 * m + 50) / 100 with hr_def
  have hr100 : 100 * r ≤ 91 * m + 50 := Nat.mul_div_le (91 * m + 50) 100
  have hr100' : 91 * m + 50 < 100 * (r + 1) := by omega
  have hr1 : 1 ≤ r := by omega
  have hrm : r ≤ m := by omega
  have hm1 : 1 ≤ m := by omega
  have hlhs : 3 ≤ (r + 1) ^ m / r ^ m := by
    rw [Nat.le_div_iff_mul_le (by positivity)]
    have h := three_le_one_add_inv_pow m r hr1 (by omega)
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr1
    have heq : (1 + 1 / (r : ℝ)) ^ m = ((r : ℝ) + 1) ^ m / (r : ℝ) ^ m := by
      rw [← div_pow]
      congr 1
      field_simp
    rw [heq, le_div_iff₀ (by positivity)] at h
    exact_mod_cast h
  have hrhs : (m + 1) ^ r / m ^ r < 3 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    have h := one_add_inv_pow_lt_three m r hm1 hrm
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm1
    have heq : (1 + 1 / (m : ℝ)) ^ r = ((m : ℝ) + 1) ^ r / (m : ℝ) ^ r := by
      rw [← div_pow]
      congr 1
      field_simp
    rw [heq, div_lt_iff₀ (by positivity)] at h
    exact_mod_cast h
  intro hmatch
  unfold MatchesN at hmatch
  omega

/-- Every `m ≥ 18000` belongs to A072933. -/
theorem inS_of_le (m : ℕ) (hm : 18000 ≤ m) : InS m := by
  rw [inS_iff_inSN]
  exact ⟨by omega, fun ⟨⟨_, h⟩, _⟩ => not_matchesN_of_le m hm h⟩

/-! ## Counting and the limit -/

/-- If every `m ≥ M` is a member, the count up to `M + j` grows by `j`. -/
theorem count_add_of_forall_le (M j : ℕ) (h : ∀ m, M ≤ m → InS m) :
    Nat.count InS (M + j) = Nat.count InS M + j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← add_assoc, Nat.count_succ, ih, if_pos (h _ (by omega))]
    omega

/-- If every `m ≥ M` is a member, the `(count M + j)`-th member (0-indexed)
is `M + j`. -/
theorem nth_count_add_of_forall_le (M j : ℕ) (h : ∀ m, M ≤ m → InS m) :
    Nat.nth InS (Nat.count InS M + j) = M + j := by
  rw [← count_add_of_forall_le M j h]
  exact Nat.nth_count (h _ (by omega))

/-- **Corrected form.** `a(n)/n → 1`: A072933 contains every `m ≥ 18000`,
so its terms are eventually `n + C` for a constant `C`. -/
theorem tendsto_a_div : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 1) := by
  set c := Nat.count InS 18000 with hc
  have key : ∀ n, c + 1 ≤ n → (a n : ℝ) / n = 1 + ((18000 : ℝ) - c - 1) / n := by
    intro n hn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    have ha : a (c + 1 + j) = 18000 + j := by
      unfold a
      rw [show c + 1 + j - 1 = c + j by omega]
      exact nth_count_add_of_forall_le 18000 j inS_of_le
    rw [ha]
    push_cast
    field_simp
    ring
  have hlim : Tendsto (fun n : ℕ => 1 + ((18000 : ℝ) - c - 1) / n) atTop (𝓝 1) := by
    have h0 := (tendsto_const_div_atTop_nhds_zero_nat ((18000 : ℝ) - c - 1)).const_add 1
    rw [add_zero] at h0
    exact h0
  exact hlim.congr' (eventually_atTop.2 ⟨c + 1, fun n hn => (key n hn).symm⟩)

/-- Cloitre's conjecture (A072933) is false: every `m ≥ 18000` is a term,
so `a(n)/n → 1`, not `10`. -/
theorem conjecture_false : ¬ Conjecture := fun h => by
  have h10 := tendsto_nhds_unique h tendsto_a_div
  norm_num at h10

end Candidates.A072933Refutation
