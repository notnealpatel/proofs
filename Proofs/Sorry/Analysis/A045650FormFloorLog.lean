/-
# A045650 — King: the n-th number not of the form k + floor(log k) is asymptotic to e^n

## OEIS source (retrieved with `oeis show A045650`, 2026-10-21)

```
NAME:     Numbers that cannot be expressed as k + floor(log(k)) where k is an integer.
TERMS:    3,9,23,58,153,409,1103,2988,8112,22036,59885,162766,442426,1202618,
          3269032,8886126,24154969,65659987,178482319,485165215,1318815755,...
KEYWORDS: nonn,easy
COMMENT:  Complement of A212445. - _Michel Marcus_, Jun 30 2015
FORMULA (the conjecture):
  Conjecture: lim n->infinity a(n) = e^n. - _Ron R. King_, Nov 10 2006
FORMULA:  a(n) = floor(e^n) + n. - Nurdin N. Takenov, Mar 10 2007
PROGRAM:  (PARI) a(n)=floor(exp(n))+n \\ _Charles R Greathouse IV_, Jul 02 2015
```

## Reading of the conjecture

Read literally, "lim a(n) = e^n" is ill-posed (the right side depends on `n`).
The intended content is the asymptotic `a(n) / e^n → 1`, proved here as
`tendsto_a_div_exp`.  The difference reading `a(n) - e^n → 0` is false: we
prove `a(n) - e^n → ∞` as `tendsto_a_sub_exp_atTop`.

## Status

Triage status: unclear (no proof located in the entry or the literature).
The entry's Takenov formula already implies the ratio limit, but it is stated
without proof.  Here the exact closed form `a(n+1) = ⌈e^(n+1)⌉ + n`
(`a_succ`) is proved from the definition; it agrees with Takenov's
`⌊e^n⌋ + n` because `e^n` is irrational for `n ≥ 1` (not needed here).

## Definitions

`log` is the natural logarithm; `k` ranges over positive integers (for
`k ≥ 1` the integer floor and `Nat.floor` of `log k` coincide).  The sequence
is indexed with the OEIS offset 1 via `Nat.nth` of the complement.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A045650FormFloorLog

open Filter Topology

/-- The value `k + ⌊log k⌋` of the form in the A045650 name. -/
noncomputable def formVal (k : ℕ) : ℕ := k + ⌊Real.log k⌋₊

/-- `m` is a term of A045650: a positive integer not equal to `k + ⌊log k⌋` for any
positive integer `k`. -/
def IsTerm (m : ℕ) : Prop := 0 < m ∧ ∀ k : ℕ, 0 < k → formVal k ≠ m

/-- A045650 with the OEIS offset 1: `a n` is the `n`-th term (`a 0` is junk, equal to `a 1`). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- The thresholds `c j = ⌈e^j⌉`. -/
noncomputable def c (j : ℕ) : ℕ := ⌈Real.exp j⌉₊

/-- `c 0 = 1`. -/
lemma c_zero : c 0 = 1 := by simp [c]

/-- `c j + 1 ≤ c (j + 1)`, since `e^j + 1 ≤ e^(j+1)`. -/
lemma c_add_one_le (j : ℕ) : c j + 1 ≤ c (j + 1) := by
  have hpos : 0 ≤ Real.exp j := (Real.exp_pos _).le
  have h1 : 1 ≤ Real.exp j := Real.one_le_exp (by positivity)
  have he : 2 ≤ Real.exp 1 := by
    have hexp := Real.add_one_le_exp 1; linarith
  have hle : Real.exp j + 1 ≤ Real.exp ((j + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one, Real.exp_add]; nlinarith
  unfold c
  rw [← Nat.ceil_add_one hpos]
  exact Nat.ceil_mono hle

/-- `c` is strictly monotone. -/
lemma c_strictMono : StrictMono c := strictMono_nat_of_lt_succ fun j => c_add_one_le j

/-- For `k ≥ 1`, `⌊log k⌋ = i` iff `c i ≤ k < c (i+1)`. -/
lemma floor_log_eq_iff {k : ℕ} (hk : 0 < k) (i : ℕ) :
    ⌊Real.log k⌋₊ = i ↔ c i ≤ k ∧ k < c (i + 1) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
  rw [Nat.floor_eq_iff hlog, Real.le_log_iff_exp_le hk', Real.log_lt_iff_lt_exp hk', c, c,
    Nat.ceil_le, Nat.lt_ceil]
  push_cast
  rfl

/-- `j + 1 ≤ c j`. -/
lemma le_c (j : ℕ) : j + 1 ≤ c j := by
  induction j with
  | zero => simp [c_zero]
  | succ j ih => have hstep := c_add_one_le j; omega

/-- Exact description of the gaps: `m` is a term of A045650 iff `m = ⌈e^(j+1)⌉ + j`
for some `j`. -/
lemma isTerm_iff (m : ℕ) : IsTerm m ↔ ∃ j : ℕ, m = c (j + 1) + j := by
  constructor
  · rintro ⟨hm, hform⟩
    have hex : ∃ j, m < c (j + 1) + j + 1 := ⟨m, by have hc := le_c (m + 1); omega⟩
    classical
    set j := Nat.find hex with hjdef
    have hj : m < c (j + 1) + j + 1 := Nat.find_spec hex
    have hlow : c j + j ≤ m := by
      rcases Nat.eq_zero_or_eq_succ_pred j with h0 | hsucc
      · rw [h0, c_zero]; omega
      · have hmin := Nat.find_min hex (show j - 1 < j by omega)
        have hj1 : j - 1 + 1 = j := by omega
        rw [hj1] at hmin
        omega
    by_contra hne
    push Not at hne
    have hk : 0 < m - j := by have hc := le_c j; omega
    have hfl : ⌊Real.log ((m - j : ℕ) : ℝ)⌋₊ = j :=
      (floor_log_eq_iff hk j).2 ⟨by omega, by
        have : m ≠ c (j + 1) + j := fun h => hne j h
        omega⟩
    apply hform (m - j) hk
    rw [formVal, hfl]
    omega
  · rintro ⟨j, rfl⟩
    refine ⟨by have hc := le_c (j + 1); omega, fun k hk hkm => ?_⟩
    set i := ⌊Real.log (k : ℝ)⌋₊ with hi
    have hbounds := (floor_log_eq_iff hk i).1 rfl
    rw [formVal, ← hi] at hkm
    rcases le_or_gt i j with hij | hij
    · have hmono := c_strictMono.monotone (show i + 1 ≤ j + 1 by omega)
      omega
    · have hmono := c_strictMono.monotone (show j + 1 ≤ i by omega)
      omega

/-- The gap function `g j = ⌈e^(j+1)⌉ + j` is strictly monotone. -/
lemma gap_strictMono : StrictMono (fun j : ℕ => c (j + 1) + j) :=
  fun _ _ hij => Nat.add_lt_add (c_strictMono (by omega)) hij

/-- The set of terms of A045650 is the range of the gap function. -/
lemma ofPred_isTerm_eq : Set.ofPred IsTerm = Set.range (fun j : ℕ => c (j + 1) + j) := by
  ext m
  simp only [Set.mem_range]
  rw [show m ∈ Set.ofPred IsTerm ↔ IsTerm m from Iff.rfl, isTerm_iff]
  exact exists_congr fun j => eq_comm

/-- The `j`-th term (0-indexed) of A045650 is `⌈e^(j+1)⌉ + j`. -/
lemma nth_isTerm (j : ℕ) : Nat.nth IsTerm j = c (j + 1) + j := by
  have hinf : (Set.ofPred IsTerm).Infinite := by
    rw [ofPred_isTerm_eq]
    exact Set.infinite_range_of_injective gap_strictMono.injective
  have hall : ∀ n : ℕ, n ∈ {n : ℕ | ∀ hf : Set.Finite (Set.ofPred IsTerm),
      n < hf.toFinset.card} := fun n hf => absurd hf hinf
  refine (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (fun j : ℕ => c (j + 1) + j)
    ?_ ?_ ?_ (hall j)).symm
  · intro m hm
    rw [ofPred_isTerm_eq] at hm
    obtain ⟨i, rfl⟩ := hm
    exact ⟨i, hall i, rfl⟩
  · intro i _
    rw [ofPred_isTerm_eq]
    exact ⟨i, rfl⟩
  · exact gap_strictMono.strictMonoOn _

/-- Closed form with the OEIS offset: `a (n + 1) = ⌈e^(n+1)⌉ + n`. -/
theorem a_succ (n : ℕ) : a (n + 1) = ⌈Real.exp ((n + 1 : ℕ) : ℝ)⌉₊ + n := by
  rw [a, Nat.add_sub_cancel, nth_isTerm, c]

/-- `e^(n+1) ≤ a (n + 1) < e^(n+1) + n + 1`. -/
lemma a_succ_bounds (n : ℕ) :
    Real.exp ((n + 1 : ℕ) : ℝ) + n ≤ a (n + 1) ∧
      (a (n + 1) : ℝ) < Real.exp ((n + 1 : ℕ) : ℝ) + n + 1 := by
  rw [a_succ]
  set x := Real.exp ((n + 1 : ℕ) : ℝ) with hxdef
  have hx : 0 ≤ x := (Real.exp_pos _).le
  have hle := Nat.le_ceil x
  have hlt := Nat.ceil_lt_add_one hx
  rw [Nat.cast_add]
  constructor <;> linarith

/-- `e^k = (e^1)^k` for natural `k`. -/
lemma exp_natCast_eq_pow (k : ℕ) : Real.exp (k : ℝ) = Real.exp 1 ^ k := by
  rw [← Real.exp_nat_mul, mul_one]

/-- Ground truth: `a 1 = 3` (first listed term), from `2 < e^1 ≤ 3`. -/
example : a 1 = 3 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ, exp_natCast_eq_pow]
  suffices h : ⌈Real.exp 1 ^ (0 + 1)⌉₊ = 3 by rw [h]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.exp_one_lt_d9
  generalize Real.exp 1 = e at h1 h2 ⊢
  have hlo : (2.7182818283 : ℝ) ^ (0 + 1) < e ^ (0 + 1) :=
    pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have hhi : e ^ (0 + 1) ≤ (2.7182818286 : ℝ) ^ (0 + 1) :=
    pow_le_pow_left₀ (by linarith) h2.le _
  rw [Nat.ceil_eq_iff (by norm_num)]
  constructor <;> norm_num at hlo hhi ⊢ <;> linarith

/-- Ground truth: `a 2 = 9` (second listed term), from `7 < e^2 ≤ 8`. -/
example : a 2 = 9 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ, exp_natCast_eq_pow]
  suffices h : ⌈Real.exp 1 ^ (1 + 1)⌉₊ = 8 by rw [h]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.exp_one_lt_d9
  generalize Real.exp 1 = e at h1 h2 ⊢
  have hlo : (2.7182818283 : ℝ) ^ (1 + 1) < e ^ (1 + 1) :=
    pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have hhi : e ^ (1 + 1) ≤ (2.7182818286 : ℝ) ^ (1 + 1) :=
    pow_le_pow_left₀ (by linarith) h2.le _
  rw [Nat.ceil_eq_iff (by norm_num)]
  constructor <;> norm_num at hlo hhi ⊢ <;> linarith

/-- Ground truth: `a 3 = 23` (third listed term), from `20 < e^3 ≤ 21`. -/
example : a 3 = 23 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_succ, exp_natCast_eq_pow]
  suffices h : ⌈Real.exp 1 ^ (2 + 1)⌉₊ = 21 by rw [h]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.exp_one_lt_d9
  generalize Real.exp 1 = e at h1 h2 ⊢
  have hlo : (2.7182818283 : ℝ) ^ (2 + 1) < e ^ (2 + 1) :=
    pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have hhi : e ^ (2 + 1) ≤ (2.7182818286 : ℝ) ^ (2 + 1) :=
    pow_le_pow_left₀ (by linarith) h2.le _
  rw [Nat.ceil_eq_iff (by norm_num)]
  constructor <;> norm_num at hlo hhi ⊢ <;> linarith

/-- Ground truth: `a 4 = 58` (fourth listed term), from `54 < e^4 ≤ 55`. -/
example : a 4 = 58 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, a_succ, exp_natCast_eq_pow]
  suffices h : ⌈Real.exp 1 ^ (3 + 1)⌉₊ = 55 by rw [h]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.exp_one_lt_d9
  generalize Real.exp 1 = e at h1 h2 ⊢
  have hlo : (2.7182818283 : ℝ) ^ (3 + 1) < e ^ (3 + 1) :=
    pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have hhi : e ^ (3 + 1) ≤ (2.7182818286 : ℝ) ^ (3 + 1) :=
    pow_le_pow_left₀ (by linarith) h2.le _
  rw [Nat.ceil_eq_iff (by norm_num)]
  constructor <;> norm_num at hlo hhi ⊢ <;> linarith

/-- `(n + 1) / e^(n+1) → 0`. -/
lemma tendsto_succ_div_exp :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / Real.exp ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, pow_one, Real.exp_neg, div_eq_mul_inv]

/-- **King's conjecture for A045650 (Ron R. King, Nov 10 2006), ratio form.**

Verbatim: "Conjecture: lim n->infinity a(n) = e^n."  Since the literal statement
is ill-posed, it is formalized as the intended asymptotic `a(n) / e^n → 1`
as `n → ∞`, where `a(n)` is the `n`-th positive integer not of the form
`k + ⌊log k⌋` (`k ≥ 1`). -/
theorem tendsto_a_div_exp :
    Tendsto (fun n : ℕ => (a n : ℝ) / Real.exp n) atTop (𝓝 1) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have hupper : Tendsto (fun n : ℕ => 1 + ((n + 1 : ℕ) : ℝ) / Real.exp ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 1) := by
    simpa using tendsto_succ_div_exp.const_add 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n => ?_) (fun n => ?_)
  · obtain ⟨hlo, -⟩ := a_succ_bounds n
    have hx := Real.exp_pos ((n + 1 : ℕ) : ℝ)
    simp only
    rw [le_div_iff₀ hx]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · obtain ⟨-, hhi⟩ := a_succ_bounds n
    have hx := Real.exp_pos ((n + 1 : ℕ) : ℝ)
    simp only
    rw [div_le_iff₀ hx, add_mul, one_mul, div_mul_cancel₀ _ hx.ne']
    push_cast at hhi ⊢
    linarith

/-- The difference reading of King's statement, `a(n) - e^n → 0`, fails: in fact
`a(n) - e^n → ∞` as `n → ∞`. -/
theorem tendsto_a_sub_exp_atTop :
    Tendsto (fun n : ℕ => (a n : ℝ) - Real.exp n) atTop atTop := by
  rw [← tendsto_add_atTop_iff_nat 1]
  refine tendsto_atTop_mono (fun n => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨hlo, -⟩ := a_succ_bounds n
  linarith

end Candidates.A045650FormFloorLog
