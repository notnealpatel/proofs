/-
# A094603 — the rightmost black run of Rule 30 depends only on `v₂(n)`

OEIS A094603, Alan Michael Gómez Calderón (2023):
`a(n) = A094604(A007814(n)) = a(2^{v₂(n)})` for `1 ≤ n`, where `a(n)` is
the length of the rightmost black run in row `n` of Rule 30 begun from one
black cell. Row `n` is generation `n - 1`.
The mechanism is Rowland's Theorem 1, *Local nested structure in Rule 30*,
Complex Systems 16 (2006), §3.

## Proof outline

Reflect the row at its right edge: bit `j` of the reflected row at time `t`
is the cell `t - j`.  Then bit `j` evolves as
`x_j ← x_j xor (x_{j-1} || x_{j-2})`, so the low bits `0..m` evolve
autonomously and the low block returns to itself after `2^m` steps.  The
predecessor of the initial low block is the all-black block, so
"run ≥ m+1 in row n" iff the low block at time `n` equals the initial one,
iff the minimal period (a power of two) of the low block divides `n`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A094603LengthRightmostRun

/-! ## Definition layer (mirrors the entry) -/

/-- Wolfram's elementary rule 30: the new state of a cell with left neighbour
`l`, own state `c` and right neighbour `r` is bit `4l + 2c + r` of `30`. -/
def rule30 (l c r : Bool) : Bool :=
  Nat.testBit 30 (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Rule 30 in closed form: `l xor (c || r)`. -/
theorem rule30_eq (l c r : Bool) : rule30 l c r = xor l (c || r) := by
  cases l <;> cases c <;> cases r <;> decide

/-- Generation `t` of Rule 30 on `ℤ` begun from a single black cell at `0`
(`true` = black). -/
def gen : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule30 (gen t (i - 1)) (gen t i) (gen t (i + 1))

/-- `a(n)` (A094603): row `n ≥ 1` is generation `n - 1`, occupying cells
`-(n-1), …, n-1`; `a(n)` is the largest `k ≤ 2n - 1` (the row width) such that
the `k` rightmost cells `n-1, n-2, …, n-k` of the row are all black. -/
def rightRun (n : ℕ) : ℕ :=
  Nat.findGreatest (fun k => ∀ i < k, gen (n - 1) ((n : ℤ) - 1 - i) = true) (2 * n - 1)

example : rightRun 1 = 1 := by decide
example : rightRun 2 = 3 := by decide
example : rightRun 3 = 1 := by decide
example : rightRun 4 = 4 := by decide
example : rightRun 5 = 1 := by decide
example : rightRun 6 = 3 := by decide
example : rightRun 7 = 1 := by decide
example : rightRun 8 = 6 := by decide

/-! ## The reflected automaton -/

/-- The contribution of the two cells to the right of bit `j` in the
reflected row (missing cells are white). -/
def hpart (b : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | 1 => b 0
  | j + 2 => b (j + 1) || b j

/-- One step of Rule 30 seen from the right edge: bit `j` becomes
`b j xor (b (j-1) || b (j-2))`. -/
def step (b : ℕ → Bool) (j : ℕ) : Bool := xor (b j) (hpart b j)

/-- The reflected initial row: only bit `0` is black. -/
def init : ℕ → Bool := fun j => decide (j = 0)

/-- Cells strictly right of `t` are white at generation `t`. -/
theorem gen_eq_false_of_lt (t : ℕ) (i : ℤ) (h : (t : ℤ) < i) : gen t i = false := by
  induction t generalizing i with
  | zero =>
    simp only [gen, decide_eq_false_iff_not]
    omega
  | succ t ih =>
    rw [gen, ih (i - 1) (by push_cast at h; omega), ih i (by push_cast at h; omega),
      ih (i + 1) (by push_cast at h; omega)]
    decide

/-- Cells strictly left of `-t` are white at generation `t`. -/
theorem gen_eq_false_of_lt_neg (t : ℕ) (i : ℤ) (h : i < -(t : ℤ)) : gen t i = false := by
  induction t generalizing i with
  | zero =>
    simp only [gen, decide_eq_false_iff_not]
    omega
  | succ t ih =>
    rw [gen, ih (i - 1) (by push_cast at h; omega), ih i (by push_cast at h; omega),
      ih (i + 1) (by push_cast at h; omega)]
    decide

/-- Bridge: cell `t - j` of generation `t` is bit `j` of the reflected row
`step^[t] init`. -/
theorem gen_sub_eq (t j : ℕ) : gen t ((t : ℤ) - j) = (step^[t] init) j := by
  induction t generalizing j with
  | zero =>
    simp [gen, init]
  | succ t ih =>
    rw [Function.iterate_succ_apply', gen, rule30_eq]
    set c := step^[t] init with hc
    rcases j with _ | _ | j
    · have h1 : ((t + 1 : ℕ) : ℤ) - (0 : ℕ) - 1 = (t : ℤ) - (0 : ℕ) := by push_cast; ring
      rw [h1, ih 0, gen_eq_false_of_lt t _ (by push_cast; omega),
        gen_eq_false_of_lt t _ (by push_cast; omega)]
      simp [step, hpart]
    · have h1 : ((t + 1 : ℕ) : ℤ) - (1 : ℕ) - 1 = (t : ℤ) - (1 : ℕ) := by push_cast; ring
      have h2 : ((t + 1 : ℕ) : ℤ) - (1 : ℕ) = (t : ℤ) - (0 : ℕ) := by push_cast; ring
      rw [h1, h2, ih 1, ih 0, gen_eq_false_of_lt t _ (by push_cast; omega)]
      simp [step, hpart]
    · have h1 : ((t + 1 : ℕ) : ℤ) - (j + 2 : ℕ) - 1 = (t : ℤ) - (j + 2 : ℕ) := by
        push_cast; ring
      have h2 : ((t + 1 : ℕ) : ℤ) - (j + 2 : ℕ) = (t : ℤ) - (j + 1 : ℕ) := by push_cast; ring
      have h3 : ((t + 1 : ℕ) : ℤ) - (j + 2 : ℕ) + 1 = (t : ℤ) - (j : ℕ) := by push_cast; ring
      rw [h1, h3, h2, ih, ih, ih]
      simp [step, hpart]

/-! ## Locality and the `2^m` return of the low block -/

/-- `hpart b j` only reads bits of `b` below `j`. -/
theorem hpart_congr {b b' : ℕ → Bool} {j : ℕ} (h : ∀ i < j, b i = b' i) :
    hpart b j = hpart b' j := by
  rcases j with _ | _ | j
  · rfl
  · simp only [hpart]
    exact h 0 (by omega)
  · simp only [hpart]
    rw [h (j + 1) (by omega), h j (by omega)]

/-- If `b` and `b'` agree below `N`, so do `step b` and `step b'`. -/
theorem step_congr {b b' : ℕ → Bool} {N : ℕ} (h : ∀ i < N, b i = b' i) :
    ∀ i < N, step b i = step b' i := by
  intro i hi
  simp only [step]
  rw [h i hi, hpart_congr (fun k hk => h k (by omega))]

/-- If `b` and `b'` agree below `N`, so do all their iterates. -/
theorem iterate_step_congr {b b' : ℕ → Bool} {N : ℕ} (h : ∀ i < N, b i = b' i) (n : ℕ) :
    ∀ i < N, (step^[n] b) i = (step^[n] b') i := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    exact step_congr ih

/-- The total flip `step^[n] b j xor b j` of bit `j` only depends on the bits
of `b` below `j`. -/
theorem iterate_step_xor_congr {b b' : ℕ → Bool} {j : ℕ} (h : ∀ i < j, b i = b' i)
    (n : ℕ) : xor ((step^[n] b) j) (b j) = xor ((step^[n] b') j) (b' j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply', step]
    have hh : hpart (step^[n] b) j = hpart (step^[n] b') j :=
      hpart_congr (iterate_step_congr h n)
    rw [hh, Bool.xor_right_comm, ih, Bool.xor_right_comm]

/-- The low block `0..k` returns to itself after `2^k` steps, for every row. -/
theorem iterate_step_two_pow (k : ℕ) (b : ℕ → Bool) :
    ∀ j ≤ k, (step^[2 ^ k] b) j = b j := by
  induction k generalizing b with
  | zero =>
    intro j hj
    obtain rfl : j = 0 := by omega
    simp [step, hpart]
  | succ k ih =>
    intro j hj
    have hsplit : step^[2 ^ (k + 1)] b = step^[2 ^ k] (step^[2 ^ k] b) := by
      rw [pow_succ, mul_two, Function.iterate_add_apply]
    rw [hsplit]
    set b' := step^[2 ^ k] b with hb'
    have hagree : ∀ i < k + 1, b' i = b i := fun i hi => ih b i (by omega)
    rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
    · rw [ih b' j (by omega), hagree j hjk]
    · obtain rfl : j = k + 1 := by omega
      have hx := iterate_step_xor_congr hagree (2 ^ k)
      rw [← hb'] at hx
      have : (step^[2 ^ k] b') (k + 1) = xor (xor (b' (k + 1)) (b (k + 1))) (b' (k + 1)) := by
        rw [← hx, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
      rw [this, Bool.xor_right_comm, Bool.xor_self, Bool.false_xor]

/-! ## The low block as a periodic point -/

/-- Truncation of a reflected row to its low block `0..m`. -/
def trunc (m : ℕ) (b : ℕ → Bool) : ℕ → Bool := fun j => if j ≤ m then b j else false

/-- The step acting on low blocks `0..m`. -/
def stepTrunc (m : ℕ) (b : ℕ → Bool) : ℕ → Bool := trunc m (step b)

/-- Iterating the truncated step on a truncated row truncates the iterate. -/
theorem iterate_stepTrunc (m : ℕ) (b : ℕ → Bool) (n : ℕ) :
    (stepTrunc m)^[n] (trunc m b) = trunc m (step^[n] b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    funext j
    simp only [stepTrunc, trunc]
    split_ifs with hj
    · refine step_congr (N := m + 1) (fun i hi => ?_) j (by omega)
      simp [trunc, show i ≤ m by omega]
    · rfl

/-- The low block `0..m` at time `n` equals the initial one iff `n` is a
periodic time of the truncated dynamics. -/
theorem lowBlock_eq_iff_isPeriodicPt (m n : ℕ) :
    (∀ j ≤ m, (step^[n] init) j = init j) ↔
      Function.IsPeriodicPt (stepTrunc m) n (trunc m init) := by
  rw [Function.IsPeriodicPt, Function.IsFixedPt, iterate_stepTrunc]
  constructor
  · intro h
    funext j
    simp only [trunc]
    split_ifs with hj
    · exact h j hj
    · rfl
  · intro h j hj
    have := congrFun h j
    simpa only [trunc, hj, if_true] using this

/-- The minimal period of the low block `0..m` is a power of two. -/
theorem exists_minimalPeriod_eq_two_pow (m : ℕ) :
    ∃ e, Function.minimalPeriod (stepTrunc m) (trunc m init) = 2 ^ e := by
  have hper : Function.IsPeriodicPt (stepTrunc m) (2 ^ m) (trunc m init) :=
    (lowBlock_eq_iff_isPeriodicPt m (2 ^ m)).mp (iterate_step_two_pow m init)
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hper.minimalPeriod_dvd
  exact ⟨e, he⟩

/-- The predecessor of the initial low block is the all-black block. -/
theorem step_lowBlock_eq_init_iff (b : ℕ → Bool) (m : ℕ) :
    (∀ j ≤ m, step b j = init j) ↔ ∀ j ≤ m, b j = true := by
  constructor
  · intro h j
    induction j using Nat.strong_induction_on with
    | _ j ihj =>
      intro hj
      have hs := h j hj
      rcases j with _ | _ | j
      · simpa [step, hpart, init] using hs
      · have h0 := ihj 0 (by omega) (by omega)
        simp only [step, hpart, init, h0] at hs
        simpa using hs
      · have h1 := ihj (j + 1) (by omega) (by omega)
        have h0 := ihj j (by omega) (by omega)
        simp only [step, hpart, init, h0, h1] at hs
        simpa using hs
  · intro h j hj
    rcases j with _ | _ | j
    · simp [step, hpart, init, h 0 hj]
    · simp [step, hpart, init, h 0 (by omega), h 1 hj]
    · simp [step, hpart, init, h (j + 2) hj, h (j + 1) (by omega)]

/-! ## The run length in terms of the reflected row -/

/-- `k ≤ a(n)` iff the `k` low bits of the reflected row at time `n - 1` are
all black. -/
theorem le_rightRun_iff (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    k ≤ rightRun n ↔ ∀ i < k, (step^[n - 1] init) i = true := by
  have hcell : ∀ i : ℕ, gen (n - 1) ((n : ℤ) - 1 - i) = (step^[n - 1] init) i := by
    intro i
    rw [← gen_sub_eq]
    congr 1
    push_cast [Nat.cast_sub hn]
    ring
  simp only [rightRun, hcell]
  constructor
  · intro hk i hi
    have hspec := Nat.findGreatest_spec (P := fun k => ∀ i < k, (step^[n - 1] init) i = true)
      (Nat.zero_le (2 * n - 1)) (fun i hi => absurd hi (Nat.not_lt_zero i))
    exact hspec i (by omega)
  · intro hk
    refine Nat.le_findGreatest ?_ hk
    by_contra hlt
    have hwhite := gen_eq_false_of_lt_neg (n - 1) ((n : ℤ) - 1 - ((2 * n - 1 : ℕ) : ℤ))
      (by push_cast [Nat.cast_sub hn, Nat.cast_sub (show 1 ≤ 2 * n by omega)]; omega)
    rw [hcell, hk (2 * n - 1) (by omega)] at hwhite
    exact absurd hwhite (by decide)

/-- `m + 1 ≤ a(n)` iff the minimal period of the low block `0..m` divides `n`. -/
theorem succ_le_rightRun_iff (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    m + 1 ≤ rightRun n ↔
      Function.minimalPeriod (stepTrunc m) (trunc m init) ∣ n := by
  rw [le_rightRun_iff n hn, ← Function.isPeriodicPt_iff_minimalPeriod_dvd,
    ← lowBlock_eq_iff_isPeriodicPt]
  have hsucc : step^[n] init = step (step^[n - 1] init) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, Function.iterate_succ_apply']
  rw [hsucc, step_lowBlock_eq_init_iff]
  exact ⟨fun h j hj => h j (by omega), fun h j hj => h j (by omega)⟩

/-! ## The conjecture -/

/-- **Gómez Calderón's conjecture (A094603, Feb 17 2023), proved.**

Since A094604(k) is by
definition `a(2^k)` and A007814 is the 2-adic valuation, this says: for every
`n ≥ 1`, the length `a(n)` of the rightmost run of black cells in row `n` of
Rule 30 (begun from one black cell) equals `a(2^{v₂(n)})`, i.e. it depends
only on `v₂(n)`.  (Mechanism of Rowland, Complex Systems 16 (2006), Thm 1.) -/
theorem rightRun_eq_rightRun_two_pow_padicValNat (n : ℕ) (hn : 1 ≤ n) :
    rightRun n = rightRun (2 ^ padicValNat 2 n) := by
  have hpos : 1 ≤ 2 ^ padicValNat 2 n := Nat.one_le_two_pow
  have hiff : ∀ k, k ≤ rightRun n ↔ k ≤ rightRun (2 ^ padicValNat 2 n) := by
    intro k
    rcases k with _ | m
    · simp
    · rw [succ_le_rightRun_iff n hn, succ_le_rightRun_iff _ hpos]
      obtain ⟨e, he⟩ := exists_minimalPeriod_eq_two_pow m
      rw [he, padicValNat_dvd_iff_le (by omega),
        Nat.pow_dvd_pow_iff_le_right (by norm_num)]
  exact le_antisymm ((hiff _).mp le_rfl) ((hiff _).mpr le_rfl)

/-- Equivalent form: `a(n)` depends only on `v₂(n)`. -/
theorem rightRun_eq_of_padicValNat_eq (n n' : ℕ) (hn : 1 ≤ n) (hn' : 1 ≤ n')
    (h : padicValNat 2 n = padicValNat 2 n') : rightRun n = rightRun n' := by
  rw [rightRun_eq_rightRun_two_pow_padicValNat n hn,
    rightRun_eq_rightRun_two_pow_padicValNat n' hn', h]

end Candidates.A094603LengthRightmostRun
