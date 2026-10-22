/-
# A128391 — Adamson: only `k = 24` gives a sequence `A054523^k * A000594` with a zero

Gary W. Adamson's conjecture in OEIS A128391 says that only `k = 24`
produces a zero in `A054523^k * A000594`. The source's `A018391` is read as
A128391, the `k = 24` sequence. As Andrew Howroyd notes, applying A054523 is
Dirichlet convolution with Euler's totient.

This module **refutes** the conjecture.  Applying A054523 is Dirichlet
convolution with Euler's totient, so at a prime `p` the `k`-th sequence takes
the value `tau(p) + k * (p - 1)`.  Since
`tau(59) = -5189203740 = -58 * 89469030`, the sequence for `k = 89469030`
vanishes at `n = 59`.
-/
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Candidates.A128391Refutation

/-! ## Ramanujan's tau function (A000594)

`tau n` is the coefficient of `x^n` in `x * ∏_{j ≥ 1} (1 - x^j)^24`, i.e. the
coefficient of `x^(n-1)` in `∏_{j ≥ 1} (1 - x^j)^24`.  It is computed with truncated power series represented as coefficient lists. -/

/-- Multiply the truncated power series with coefficient list `c` (coefficient
of `x^i` at index `i`) by `1 - x^m`, keeping the same truncation length: the
new coefficient of `x^i` is `c_i - c_(i - m)` (with `c_(i - m) = 0` for
`i < m`).  `List.zipWith` stops at the shorter list, which is `c`. -/
def mulOneSubX (m : ℕ) (c : List ℤ) : List ℤ :=
  List.zipWith (· - ·) c (List.replicate m 0 ++ c)

/-- `(1 - x) * (1 + 2x + 3x^2 + 4x^3) ≡ 1 + x + x^2 + x^3 (mod x^4)`
and `(1 - x^2) * (1 + 2x + 3x^2 + 4x^3) ≡ 1 + 2x + 2x^2 + 2x^3 (mod x^4)`. -/
example : mulOneSubX 1 [1, 2, 3, 4] = [1, 1, 1, 1] ∧
    mulOneSubX 2 [1, 2, 3, 4] = [1, 2, 2, 2] := by
  decide +kernel

/-- `etaPow24TruncAux N K` is the list of coefficients of `x^0, …, x^(N-1)` of
the polynomial `∏_{j=1}^{K} (1 - x^j)^24`, i.e. that product modulo `x^N`;
the factor `(1 - x^j)^24` is applied as 24 multiplications by `1 - x^j`. -/
def etaPow24TruncAux (N : ℕ) : ℕ → List ℤ
  | 0 => (List.range N).map fun i => if i = 0 then 1 else 0
  | K + 1 => (mulOneSubX (K + 1))^[24] (etaPow24TruncAux N K)

/-- modulo `x^25`, `(1 - x)^24` has the coefficients
`(-1)^j * C(24, j)`. -/
example : etaPow24TruncAux 25 1 =
    (List.range 25).map fun j => (-1) ^ j * (Nat.choose 24 j : ℤ) := by
  decide +kernel

/-- The coefficients of `x^0, …, x^(N-1)` of `∏_{j=1}^{N} (1 - x^j)^24`; factors
with `j ≥ N` do not affect these coefficients, so this is the truncation of
the infinite product `∏_{j ≥ 1} (1 - x^j)^24` modulo `x^N`. -/
def etaPow24Trunc (N : ℕ) : List ℤ :=
  etaPow24TruncAux N N

/-- Ramanujan's tau function (A000594): `tau n` is the coefficient of `x^n` in
`x * ∏_{j ≥ 1} (1 - x^j)^24`, i.e. the coefficient of `x^(n-1)` of the
product.  The constant coefficient of `x * ∏ …` is `0`, so `tau 0 = 0`. -/
def tau (n : ℕ) : ℤ :=
  if n = 0 then 0 else (etaPow24Trunc n).getD (n - 1) 0

/-- the first 20 terms of A000594. -/
example : (List.range 20).map (fun i => tau (i + 1)) =
    [1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920, 534612,
      -370944, -577738, 401856, 1217160, 987136, -6905934, 2727432, 10661420,
      -7109760] := by
  decide +kernel

/-- Ramanujan's `tau(59) = -5189203740 = -58 * 89469030` (kernel evaluation of
the truncated product). -/
theorem tau_fiftyNine : tau 59 = -5189203740 := by
  decide +kernel

/-! ## The triangle A054523 and its action -/

/-- The triangle A054523: `T(n, m) = phi(n / m)` if `m ∣ n`, and `0` otherwise
(read for `1 ≤ m ≤ n`). -/
def A054523 (n m : ℕ) : ℤ :=
  if m ∣ n then ((n / m).totient : ℤ) else 0

/-- rows `1, …, 12` of A054523. -/
example : (List.range 12).flatMap (fun i => (List.range (i + 1)).map
      fun j => A054523 (i + 1) (j + 1)) =
    [1, 1, 1, 2, 0, 1, 2, 1, 0, 1, 4, 0, 0, 0, 1, 2, 2, 1, 0, 0, 1, 6, 0, 0, 0, 0, 0,
      1, 4, 2, 0, 1, 0, 0, 0, 1, 6, 0, 2, 0, 0, 0, 0, 0, 1, 4, 4, 0, 0, 1, 0, 0, 0,
      0, 1, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 2, 2, 2, 0, 1, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

/-- The lower-triangular matrix A054523 applied to a column vector
`v = (v 1, v 2, …)`: the `n`-th entry is `∑_{m=1}^{n} T(n, m) * v m`. -/
def applyA054523 (v : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ m ∈ Finset.Icc 1 n, A054523 n m * v m

/-- `A054523^k * A000594`: the matrix A054523 applied `k` times to the column
vector of Ramanujan's tau function.  (`seq 24` is A128391.) -/
def seq : ℕ → ℕ → ℤ
  | 0 => tau
  | k + 1 => applyA054523 (seq k)

/-- Applying A054523 is Dirichlet convolution with Euler's totient:
`(A054523 v)(n) = ∑_{m ∣ n} phi(n / m) * v m`. -/
theorem applyA054523_eq_sum_divisors (v : ℕ → ℤ) (n : ℕ) :
    applyA054523 v n = ∑ m ∈ n.divisors, ((n / m).totient : ℤ) * v m := by
  have hIcc : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := rfl
  rw [applyA054523, Nat.divisors, hIcc, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : m ∣ n
  · simp only [A054523, hm, if_true]
  · simp only [A054523, hm, if_false, zero_mul]

/-- The divisor-sum form of `seq`, used for evaluation. -/
def seqDiv : ℕ → ℕ → ℤ
  | 0 => tau
  | k + 1 => fun n => ∑ m ∈ n.divisors, ((n / m).totient : ℤ) * seqDiv k m

/-- `seq` agrees with its divisor-sum form `seqDiv`. -/
theorem seq_eq_seqDiv (k : ℕ) : seq k = seqDiv k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext n
    rw [seq, seqDiv, applyA054523_eq_sum_divisors, ih]

/-- the first 12 terms of A128391 (`k = 24`). -/
example : (List.range 12).map (fun i => seq 24 (i + 1)) =
    [1, 0, 300, -1724, 4926, 0, -16600, 44600, -100299, 0, 534852, -517200] := by
  rw [seq_eq_seqDiv]
  decide +kernel

/-! ## The conjecture -/

/-- **Adamson's conjecture (A128391, Gary W. Adamson).**

"Conjecture: Given A054523^k, k = any positive integer, "zero"
appears only in the sequence A018391 (k=24)."  ("A018391" is a typo for
A128391, the `k = 24` sequence.)

Formalized: for every positive `k`, if the sequence `A054523^k * A000594`
(indexed by `n ≥ 1`) has a zero term, then `k = 24`.  This is the "only"
direction; the converse (`k = 24` has a zero) holds, see `seq_24_two`. -/
def Conjecture : Prop :=
  ∀ k : ℕ, 0 < k → (∃ n : ℕ, 0 < n ∧ seq k n = 0) → k = 24

/-! ## The refutation -/

/-- Every sequence `A054523^k * A000594` starts with `1`. -/
theorem seq_one (k : ℕ) : seq k 1 = 1 := by
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    rw [seq, applyA054523_eq_sum_divisors, Nat.divisors_one, Finset.sum_singleton, ih]
    norm_num

/-- At a prime `p`, `(A054523^k * A000594)(p) = tau(p) + k * (p - 1)`. -/
theorem seq_prime (k : ℕ) {p : ℕ} (hp : p.Prime) :
    seq k p = tau p + k * ((p : ℤ) - 1) := by
  induction k with
  | zero => simp [seq]
  | succ k ih =>
    have hp1 : p ≠ 1 := hp.ne_one
    have htot : ((p.totient : ℕ) : ℤ) = (p : ℤ) - 1 := by
      rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
    rw [seq, applyA054523_eq_sum_divisors, hp.divisors, Finset.sum_pair hp1.symm,
      ih, seq_one, Nat.div_one, Nat.div_self hp.pos, htot, Nat.totient_one]
    push_cast
    ring

/-- Consistency with the entry: A128391 (`k = 24`) does have a zero, at
`n = 2`, since `tau(2) + 24 * (2 - 1) = -24 + 24 = 0`. -/
theorem seq_24_two : seq 24 2 = 0 := by
  rw [seq_prime 24 Nat.prime_two]
  decide +kernel

/-- The sequence `A054523^89469030 * A000594` vanishes at `n = 59`:
`tau(59) + 89469030 * 58 = -5189203740 + 5189203740 = 0`. -/
theorem seq_89469030_fiftyNine : seq 89469030 59 = 0 := by
  rw [seq_prime 89469030 (by norm_num), tau_fiftyNine]
  norm_num

/-- **Adamson's conjecture is false.**  Counterexample: `k = 89469030`,
`n = 59`.  At a prime `p` the `k`-th sequence equals `tau(p) + k (p - 1)`, and
`tau(59) = -5189203740 = -58 * 89469030`, so `A054523^89469030 * A000594` has
`a(59) = 0` (and hence, by multiplicativity, `a(n) = 0` whenever `59 ∥ n`).
A zero at a prime `p` occurs exactly when `(p - 1) ∣ tau(p)` with
`tau(p) < 0`; `p = 2` gives `k = 24`. -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  have hk := h 89469030 (by norm_num) ⟨59, by norm_num, seq_89469030_fiftyNine⟩
  exact absurd hk (by decide)

end Candidates.A128391Refutation
