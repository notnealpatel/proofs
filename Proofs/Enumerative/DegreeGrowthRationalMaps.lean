/-
# Degree growth of three-term Gale-Robinson recurrences

Melih Emin Can, "Degree Growth of Rational Maps with Laurent Property",
arXiv:2610.21627, Section 3, Conjecture 1 and Theorem 2.
For the specified initial-value tropical recurrence, the periodic quadratic
correction conjecture is equivalent to `m = p+q+r` shift identities
`2(k_(n+N)-k_n) = 2n+N` for `1 ≤ n ≤ m`.
This reduction holds for all positive triples. Finite certificates prove
every ordered coprime triple with `1 ≤ p < q < r ≤ 6`; `(2,4,6)` shows that
the gcd condition cannot simply be omitted. The general conjecture is not
proved here. The source's theorem covers the family `(1,2,r)`, `r ≥ 3`.
-/
import Mathlib.Data.List.GetD
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace DegreeGrowthRationalMaps

/-! ## Definitions

Indices follow the source: the sequence lives on `n ≥ 1`; index `0` is an
unused padding value (equal to `0`).  The source offsets `n + m - p`,
`n + m - q`, `n + m - r` are written `n + (q + r)`, `n + (p + r)`,
`n + (p + q)`, which avoids natural-number subtraction.  -/

/-- One step of the table evaluator: the value at index `j` of the growth rate
sequence, given the list `t` of the values at indices `0, …, j - 1`.  It is `0`
below `m = p + q + r`, `1` at `m`, and otherwise the max-plus recurrence with
`j = n + m`. -/
def grNext (p q r : ℕ) (t : List ℤ) (j : ℕ) : ℤ :=
  if j < p + q + r then 0
  else if j = p + q + r then 1
  else
    let n := j - (p + q + r)
    max (max (t.getD (n + p) 0 + t.getD (n + (q + r)) 0)
        (t.getD (n + q) 0 + t.getD (n + (p + r)) 0))
        (t.getD (n + r) 0 + t.getD (n + (p + q)) 0) - t.getD n 0

/-- The list `[k_0, k_1, …, k_{L-1}]` of the first `L` values (index `0` padding). -/
def grTable (p q r : ℕ) : ℕ → List ℤ
  | 0 => []
  | L + 1 => grTable p q r L ++ [grNext p q r (grTable p q r L) L]

/-- The growth rate sequence `k_n` of the three-term Gale-Robinson recurrence
with shifts `p, q, r` (source, Sec. 3); `grK p q r 0 = 0` is padding. -/
def grK (p q r n : ℕ) : ℤ := (grTable p q r (n + 1)).getD n 0

/-- `k` satisfies the three-term Gale-Robinson max-plus recurrence
`k_{n+m} = max(k_{n+p}+k_{n+m-p}, k_{n+q}+k_{n+m-q}, k_{n+r}+k_{n+m-r}) - k_n`
for all `n ≥ 1`, where `m = p + q + r`. -/
def IsGRSolution (p q r : ℕ) (k : ℕ → ℤ) : Prop :=
  ∀ n, 1 ≤ n → k (n + (p + q + r)) =
    max (max (k (n + p) + k (n + (q + r))) (k (n + q) + k (n + (p + r))))
      (k (n + r) + k (n + (p + q))) - k n

/-- The table of length `L` has length `L`. -/
theorem length_grTable (p q r L : ℕ) : (grTable p q r L).length = L := by
  induction L with
  | zero => rfl
  | succ L ih => simp [grTable, ih]

/-- Every table entry is the corresponding value of `grK`. -/
theorem getD_grTable (p q r : ℕ) {i L : ℕ} (hi : i < L) :
    (grTable p q r L).getD i 0 = grK p q r i := by
  induction L with
  | zero => omega
  | succ L ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
    · rw [grTable, List.getD_append _ _ _ _ (by rw [length_grTable]; exact h), ih h]
    · subst h; rfl

/-- Unfolding equation: `k_n` is one evaluator step on the first `n` values. -/
theorem grK_eq_grNext (p q r n : ℕ) : grK p q r n = grNext p q r (grTable p q r n) n := by
  rw [grK, grTable, List.getD_append_right _ _ _ _ (by rw [length_grTable]),
    length_grTable, Nat.sub_self]
  rfl

/-- Initial values: `k_n = 0` for `n < m` (in particular `k_1 = … = k_{m-1} = 0`). -/
theorem grK_of_lt (p q r : ℕ) {n : ℕ} (hn : n < p + q + r) : grK p q r n = 0 := by
  rw [grK_eq_grNext, grNext, if_pos hn]

/-- Initial value `k_m = 1`. -/
theorem grK_order (p q r : ℕ) : grK p q r (p + q + r) = 1 := by
  rw [grK_eq_grNext, grNext, if_neg (lt_irrefl _), if_pos rfl]

/-- The growth rate sequence satisfies the Gale-Robinson max-plus recurrence. -/
theorem isGRSolution_grK {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    IsGRSolution p q r (grK p q r) := by
  intro n hn
  rw [grK_eq_grNext, grNext, if_neg (by omega), if_neg (by omega)]
  simp only [Nat.add_sub_cancel]
  have hL : ∀ i, i < n + (p + q + r) → (grTable p q r (n + (p + q + r))).getD i 0 = grK p q r i :=
    fun i hi => getD_grTable p q r hi
  rw [hL (n + p) (by omega), hL (n + (q + r)) (by omega), hL (n + q) (by omega),
    hL (n + (p + r)) (by omega), hL (n + r) (by omega), hL (n + (p + q)) (by omega),
    hL n (by omega)]

/-- Shift and arithmetic-progression invariance: if `k` solves the recurrence,
so does `n ↦ k_{n+N} + a + b n`. -/
theorem isGRSolution_shift_add_linear {p q r : ℕ} {k : ℕ → ℤ} (hk : IsGRSolution p q r k)
    (N : ℕ) (a b : ℤ) : IsGRSolution p q r (fun n => k (n + N) + a + b * n) := by
  intro n hn
  have h := hk (n + N) (by omega)
  have e : ∀ s : ℕ, n + s + N = n + N + s := fun s => by omega
  simp only [e]
  rw [h]
  have C : ∀ x y z w : ℤ, max (max (x + w) (y + w)) (z + w) = max (max x y) z + w :=
    fun x y z w => by rw [max_add_add_right, max_add_add_right]
  have key := C (k (n + N + p) + k (n + N + (q + r))) (k (n + N + q) + k (n + N + (p + r)))
    (k (n + N + r) + k (n + N + (p + q))) (2 * a + b * (2 * n + (p + q + r)))
  push_cast
  have e1 : k (n + N + p) + a + b * (↑n + ↑p) + (k (n + N + (q + r)) + a + b * (↑n + (↑q + ↑r)))
      = k (n + N + p) + k (n + N + (q + r)) + (2 * a + b * (2 * n + (p + q + r))) := by ring
  have e2 : k (n + N + q) + a + b * (↑n + ↑q) + (k (n + N + (p + r)) + a + b * (↑n + (↑p + ↑r)))
      = k (n + N + q) + k (n + N + (p + r)) + (2 * a + b * (2 * n + (p + q + r))) := by ring
  have e3 : k (n + N + r) + a + b * (↑n + ↑r) + (k (n + N + (p + q)) + a + b * (↑n + (↑p + ↑q)))
      = k (n + N + r) + k (n + N + (p + q)) + (2 * a + b * (2 * n + (p + q + r))) := by ring
  rw [e1, e2, e3, key]
  ring

/-- Determinacy: two solutions of the recurrence that agree on `1 ≤ n ≤ m`
agree for all `n ≥ 1`. -/
theorem eq_of_isGRSolution {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    {k l : ℕ → ℤ} (hk : IsGRSolution p q r k) (hl : IsGRSolution p q r l)
    (hw : ∀ n, 1 ≤ n → n ≤ p + q + r → k n = l n) : ∀ n, 1 ≤ n → k n = l n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hm : n ≤ p + q + r
    · exact hw n hn hm
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + (p + q + r) := ⟨n - (p + q + r), by omega⟩
      have hj : 1 ≤ j := by omega
      rw [hk j hj, hl j hj, ih (j + p) (by omega) (by omega), ih (j + (q + r)) (by omega) (by omega),
        ih (j + q) (by omega) (by omega), ih (j + (p + r)) (by omega) (by omega),
        ih (j + r) (by omega) (by omega), ih (j + (p + q)) (by omega) (by omega),
        ih j (by omega) hj]

/-- Window propagation: if a solution satisfies `2 (k_{n+N} - k_n) = 2n + N`
for `1 ≤ n ≤ m`, it satisfies it for all `n ≥ 1`. -/
theorem shift_of_window {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    {k : ℕ → ℤ} (hk : IsGRSolution p q r k) (N : ℕ)
    (hw : ∀ n, 1 ≤ n → n ≤ p + q + r → 2 * (k (n + N) - k n) = 2 * (n : ℤ) + N) :
    ∀ n, 1 ≤ n → 2 * (k (n + N) - k n) = 2 * (n : ℤ) + N := by
  obtain ⟨h, hh⟩ : ∃ h : ℕ, N = 2 * h := by
    have h1 := hw 1 le_rfl (by omega)
    push_cast at h1
    exact ⟨N / 2, by omega⟩
  subst hh
  have hl := isGRSolution_shift_add_linear hk (2 * h) (-(h : ℤ)) (-1)
  have heq := eq_of_isGRSolution hp hq hr hl hk (fun n h1 h2 => by
    have := hw n h1 h2
    push_cast at this
    linarith)
  intro n hn
  have := heq n hn
  push_cast
  linarith

/-- Characterization: `grK` is the source's growth rate sequence, i.e. every
`k` with `k_1 = … = k_{m-1} = 0`, `k_m = 1` satisfying the recurrence agrees
with `grK` on all `n ≥ 1`. -/
theorem eq_grK_of_isGRSolution {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    {k : ℕ → ℤ} (hk : IsGRSolution p q r k) (h0 : ∀ n, 1 ≤ n → n < p + q + r → k n = 0)
    (h1 : k (p + q + r) = 1) : ∀ n, 1 ≤ n → k n = grK p q r n := by
  refine eq_of_isGRSolution hp hq hr hk (isGRSolution_grK hp hq hr) fun n hn hm => ?_
  rcases Nat.lt_or_eq_of_le hm with hlt | rfl
  · rw [h0 n hn hlt, grK_of_lt p q r hlt]
  · rw [h1, grK_order]

/-- The conjectured period `N = gcd(p,q) r² + gcd(p,r) q² + gcd(q,r) p² + pqr`. -/
def grN (p q r : ℕ) : ℕ :=
  Nat.gcd p q * r ^ 2 + Nat.gcd p r * q ^ 2 + Nat.gcd q r * p ^ 2 + p * q * r

/-- Conjecture 1 of arXiv 2610.21627 for the triple `(p, q, r)` (without its
gcd hypothesis): there is an integer sequence `c` with `c_{n+N} = c_n` for all
`n ≥ 1` and `k_n = (n² + c_n) / (2N)` for all `n ≥ 1`. -/
def GRConjecture (p q r : ℕ) : Prop :=
  ∃ c : ℕ → ℤ, (∀ n, 1 ≤ n → c (n + grN p q r) = c n) ∧
    ∀ n, 1 ≤ n → (grK p q r n : ℚ) = ((n : ℚ) ^ 2 + c n) / (2 * grN p q r)

/-- Boolean window checker: evaluates the first `N + m + 1` values once and
tests `2 (k_{n+N} - k_n) = 2n + N` for `1 ≤ n ≤ m`. -/
def windowCheck (p q r N : ℕ) : Bool :=
  let t := grTable p q r (N + (p + q + r) + 1)
  (List.range' 1 (p + q + r)).all fun n =>
    2 * (t.getD (n + N) 0 - t.getD n 0) == 2 * (n : ℤ) + N

/-! ### Examples -/

-- Somos-6, `(p, q, r) = (1, 2, 3)`: `k_0, …, k_19` (`k_0 = 0` is padding).
example : (List.range 20).map (grK 1 2 3) =
    [0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 3, 3, 4, 5, 5, 6, 7, 8, 9] := by decide
-- The triple `(1, 3, 4)`.
example : (List.range 20).map (grK 1 3 4) =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 5] := by decide
-- The paper's periods for Somos-6 and Somos-7 (`N = 20, 30`).
example : grN 1 2 3 = 20 := rfl
example : grN 1 2 4 = 30 := rfl
example : grN 1 3 4 = 38 := rfl
example : grN 2 3 5 = 68 := rfl

/-! ## Reduction lemma -/

/-- `windowCheck` decides the window condition. -/
theorem windowCheck_eq_true_iff (p q r N : ℕ) :
    windowCheck p q r N = true ↔
      ∀ n, 1 ≤ n → n ≤ p + q + r → 2 * (grK p q r (n + N) - grK p q r n) = 2 * (n : ℤ) + N := by
  unfold windowCheck
  simp only [List.all_eq_true, List.mem_range'_1, beq_iff_eq]
  constructor
  · intro h n h1 h2
    have hn := h n ⟨h1, by omega⟩
    rwa [getD_grTable p q r (by omega), getD_grTable p q r (by omega)] at hn
  · rintro h n ⟨h1, h2⟩
    rw [getD_grTable p q r (by omega), getD_grTable p q r (by omega)]
    exact h n h1 (by omega)

/-- **Reduction lemma.** For every triple of positive integers `p, q, r`
(coprime or not), Conjecture 1 of arXiv 2610.21627 for `(p, q, r)` holds iff
the finite window condition `2 (k_{n+N} - k_n) = 2n + N` (that is,
`k_{N+n} = k_n + n + N/2`) holds for `1 ≤ n ≤ m = p + q + r`. -/
theorem grConjecture_iff_window {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    GRConjecture p q r ↔
      ∀ n, 1 ≤ n → n ≤ p + q + r →
        2 * (grK p q r (n + grN p q r) - grK p q r n) = 2 * (n : ℤ) + grN p q r := by
  set N := grN p q r with hNdef
  have hN : 0 < N := by
    have : 0 < p * q * r := Nat.mul_pos (Nat.mul_pos hp hq) hr
    simp only [hNdef, grN]
    omega
  have hNq : (2 * N : ℚ) ≠ 0 := by positivity
  constructor
  · rintro ⟨c, hc, hk⟩ n h1 _
    -- `2N k_j = j² + c_j` in `ℤ`, for `j ≥ 1`.
    have hz : ∀ j, 1 ≤ j → 2 * (N : ℤ) * grK p q r j = (j : ℤ) ^ 2 + c j := by
      intro j hj
      have hq := hk j hj
      rw [eq_div_iff hNq] at hq
      exact_mod_cast (by linarith : (2 * (N : ℚ)) * grK p q r j = (j : ℚ) ^ 2 + c j)
    have hA := hz (n + N) (by omega)
    have hB := hz n h1
    rw [hc n h1] at hA
    push_cast at hA
    have hmul : (N : ℤ) * (2 * (grK p q r (n + N) - grK p q r n)) = (N : ℤ) * (2 * n + N) := by
      linear_combination hA - hB
    exact mul_left_cancel₀ (by exact_mod_cast hN.ne') hmul
  · intro hw
    have hall := shift_of_window hp hq hr (isGRSolution_grK hp hq hr) N hw
    refine ⟨fun n => 2 * N * grK p q r n - (n : ℤ) ^ 2, fun n hn => ?_, fun n _ => ?_⟩
    · have h := hall n hn
      push_cast
      linear_combination (N : ℤ) * h
    · rw [← hNdef]
      push_cast
      field_simp
      ring

/-- Instances follow from a successful window check. -/
theorem grConjecture_of_windowCheck {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (h : windowCheck p q r (grN p q r) = true) : GRConjecture p q r :=
  (grConjecture_iff_window hp hq hr).2 ((windowCheck_eq_true_iff p q r _).1 h)

/-! ## Instances

Each check evaluates `N + m + 1` terms in the kernel (`decide +kernel`, no
`native_decide`).  The instances are elaborated sequentially
(`Elab.async false`): run concurrently, the kernel checks exceed the
memory cap of the bounded build environment. -/

set_option Elab.async false

/-- Conjecture 1 of arXiv 2610.21627 holds for `(p, q, r) = (1, 2, 3)` (paper, Theorem 2: the `(1, 2, r)` family). -/
theorem grConjecture_1_2_3 : GRConjecture 1 2 3 :=
  grConjecture_of_windowCheck (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

/-- Conjecture 1 of arXiv 2610.21627 holds for `(p, q, r) = (1, 2, 4)` (paper, Theorem 2: the `(1, 2, r)` family). -/
theorem grConjecture_1_2_4 : GRConjecture 1 2 4 :=
  grConjecture_of_windowCheck (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

/-- Conjecture 1 of arXiv 2610.21627 holds for `(p, q, r) = (1, 3, 4)` (outside the paper's `(1, 2, r)` family). -/
theorem grConjecture_1_3_4 : GRConjecture 1 3 4 :=
  grConjecture_of_windowCheck (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

/-- Conjecture 1 of arXiv 2610.21627 holds for `(p, q, r) = (2, 3, 4)` (outside the paper's `(1, 2, r)` family). -/
theorem grConjecture_2_3_4 : GRConjecture 2 3 4 :=
  grConjecture_of_windowCheck (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

/-- Conjecture 1 of arXiv 2610.21627 holds for `(p, q, r) = (1, 2, 5)` (paper, Theorem 2: the `(1, 2, r)` family). -/
theorem grConjecture_1_2_5 : GRConjecture 1 2 5 :=
  grConjecture_of_windowCheck (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

/-- Conjecture 1 of arXiv 2610.21627 holds for `(p, q, r) = (1, 3, 5)` (outside the paper's `(1, 2, r)` family). -/
theorem grConjecture_1_3_5 : GRConjecture 1 3 5 :=
  grConjecture_of_windowCheck (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

/-- Conjecture 1 of arXiv 2610.21627 holds for `(p, q, r) = (2, 3, 5)` (outside the paper's `(1, 2, r)` family). -/
theorem grConjecture_2_3_5 : GRConjecture 2 3 5 :=
  grConjecture_of_windowCheck (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

/-- Conjecture 1 of arXiv 2610.21627 holds for `(p, q, r) = (1, 4, 5)` (outside the paper's `(1, 2, r)` family). -/
theorem grConjecture_1_4_5 : GRConjecture 1 4 5 :=
  grConjecture_of_windowCheck (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

/-- Conjecture 1 of arXiv 2610.21627 holds for `(p, q, r) = (2, 4, 5)` (outside the paper's `(1, 2, r)` family). -/
theorem grConjecture_2_4_5 : GRConjecture 2 4 5 :=
  grConjecture_of_windowCheck (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

/-- Conjecture 1 of arXiv 2610.21627 holds for `(p, q, r) = (3, 4, 5)` (outside the paper's `(1, 2, r)` family). -/
theorem grConjecture_3_4_5 : GRConjecture 3 4 5 :=
  grConjecture_of_windowCheck (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

/-- Conjecture 1 of arXiv 2610.21627 holds for `(p, q, r) = (1, 2, 6)` (paper, Theorem 2: the `(1, 2, r)` family). -/
theorem grConjecture_1_2_6 : GRConjecture 1 2 6 :=
  grConjecture_of_windowCheck (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

/-- Conjecture 1 of arXiv 2610.21627 holds for `(p, q, r) = (1, 3, 6)` (outside the paper's `(1, 2, r)` family). -/
theorem grConjecture_1_3_6 : GRConjecture 1 3 6 :=
  grConjecture_of_windowCheck (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

/-- Conjecture 1 of arXiv 2610.21627 holds for `(p, q, r) = (2, 3, 6)` (outside the paper's `(1, 2, r)` family). -/
theorem grConjecture_2_3_6 : GRConjecture 2 3 6 :=
  grConjecture_of_windowCheck (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

/-- Conjecture 1 of arXiv 2610.21627 holds for `(p, q, r) = (1, 4, 6)` (outside the paper's `(1, 2, r)` family). -/
theorem grConjecture_1_4_6 : GRConjecture 1 4 6 :=
  grConjecture_of_windowCheck (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

/-- Conjecture 1 of arXiv 2610.21627 holds for `(p, q, r) = (3, 4, 6)` (outside the paper's `(1, 2, r)` family). -/
theorem grConjecture_3_4_6 : GRConjecture 3 4 6 :=
  grConjecture_of_windowCheck (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

/-- Conjecture 1 of arXiv 2610.21627 holds for `(p, q, r) = (1, 5, 6)` (outside the paper's `(1, 2, r)` family). -/
theorem grConjecture_1_5_6 : GRConjecture 1 5 6 :=
  grConjecture_of_windowCheck (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

/-- Conjecture 1 of arXiv 2610.21627 holds for `(p, q, r) = (2, 5, 6)` (outside the paper's `(1, 2, r)` family). -/
theorem grConjecture_2_5_6 : GRConjecture 2 5 6 :=
  grConjecture_of_windowCheck (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

/-- Conjecture 1 of arXiv 2610.21627 holds for `(p, q, r) = (3, 5, 6)` (outside the paper's `(1, 2, r)` family). -/
theorem grConjecture_3_5_6 : GRConjecture 3 5 6 :=
  grConjecture_of_windowCheck (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

/-- Conjecture 1 of arXiv 2610.21627 holds for `(p, q, r) = (4, 5, 6)` (outside the paper's `(1, 2, r)` family). -/
theorem grConjecture_4_5_6 : GRConjecture 4 5 6 :=
  grConjecture_of_windowCheck (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

/-- The gcd hypothesis of Conjecture 1 is needed: for `(2, 4, 6)`, where
`gcd = 2`, the conclusion fails. -/
theorem not_grConjecture_2_4_6 : ¬ GRConjecture 2 4 6 := by
  rw [grConjecture_iff_window (by norm_num) (by norm_num) (by norm_num),
    ← windowCheck_eq_true_iff]
  decide +kernel

end DegreeGrowthRationalMaps
