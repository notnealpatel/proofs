/-
# A128382 — Adamson: only `k = 24` gives a sequence `A051731^k * A000594` with a zero

## OEIS source (retrieved 2026-10-21 with `oeis show A128382` and the live entry)

```
NAME:     Inverse Moebius transform operation performed 24 times on A000594:
          A051731^24 * A000594.
TERMS:    1,0,276,-1748,4854,0,-16720,44552,-107295,0,534636,-482448,-577714,0,
          1339704,2528206,-6905910,0,10661444,-8484792,-4614720,0,18643296,
          12296352,-25383005,0,-75928312,29226560,128406654,0,-52843144,
          -151821160,147559536,0,-81158880
KEYWORDS: sign,mult
COMMENT (the conjecture, unsigned in the entry; AUTHOR line of the entry is
  Gary W. Adamson, Feb 28 2007):
  Conjecture: given the inverse Moebius transform operation performed any k
  times (k=1,2,3,...); k=24 is the only such sequence with zeros. A weaker
  conjecture: "zero" occurs an infinite number of times in A128382.
COMMENT:
  Multiplicative because A000594 is. Each application of A051731 corresponds
  to an inverse Moebius transform. - _Andrew Howroyd_, Aug 03 2018
EXTENSIONS:
  Terms a(11) and beyond from Andrew Howroyd, Aug 03 2018
PROGRAM (PARI):
  seq(n, k=24)={my(u=vector(n,n,1), v=vector(n,n,ramanujantau(n)));
  for(i=1, k, v=dirmul(u,v)); v} \\ _Andrew Howroyd_, Aug 03 2018
```

No later comment in the entry retracts or amends the conjecture.

A051731: "Triangle read by rows: T(n,k) = 1 if k divides n, T(n,k) = 0
otherwise (for n >= 1 and 1 <= k <= n)."
A000594: "Ramanujan's tau function", G.f. `x * Product_{k>=1} (1 - x^k)^24`.

## Status

This module **refutes** the (strong) conjecture.  Applying A051731 is the
inverse Moebius transform (Dirichlet convolution with the constant function
`1`), so at a prime `p` the `k`-th sequence takes the value `tau(p) + k`.
Since `tau(7) = -16744`, the sequence for `k = 16744` vanishes at `n = 7`.

The weaker conjecture (infinitely many zeros for `k = 24`) is true: `a(2) = 0`
and the sequence is multiplicative, so `a(n) = 0` for all `n ≡ 2 (mod 4)`.
Its proof needs the multiplicativity of `tau` (Mordell), which is not in
Mathlib; it is stated below as `WeakConjecture` but not proved here.
-/
import Mathlib

set_option autoImplicit false
set_option Elab.async false

namespace Candidates.A128382Refutation

/-! ## Ramanujan's tau function (A000594)

`tau n` is the coefficient of `x^n` in `x * ∏_{j ≥ 1} (1 - x^j)^24`, i.e. the
coefficient of `x^(n-1)` in `∏_{j ≥ 1} (1 - x^j)^24`.  We compute it with
truncated power series represented as coefficient lists. -/

/-- The coefficient list of the polynomial `(1 - x)^24` (coefficient of `x^j` at
index `j`), written out; by the binomial theorem the coefficient of `x^j` is
`(-1)^j * C(24, j)`, which the ground-truth check below confirms. -/
def oneSubXPow24 : List ℤ :=
  [1, -24, 276, -2024, 10626, -42504, 134596, -346104, 735471, -1307504, 1961256,
    -2496144, 2704156, -2496144, 1961256, -1307504, 735471, -346104, 134596, -42504,
    10626, -2024, 276, -24, 1]

/-- Ground truth: the coefficient of `x^j` in `(1 - x)^24` is `(-1)^j * C(24, j)`. -/
example : oneSubXPow24 = (List.range 25).map fun j => (-1) ^ j * (Nat.choose 24 j : ℤ) := by
  decide +kernel

/-- Multiply the truncated power series with coefficient list `c` (coefficient
of `x^i` at index `i`) by `(1 - x^m)^24 = ∑_{j=0}^{24} e_j * x^(m j)`, where
`e = oneSubXPow24` is the coefficient list of `(1 - x)^24`, keeping the same
truncation length: the new coefficient of `x^i` is
`∑_{j ≤ 24, m j ≤ i} e_j * c_(i - m j)`. -/
def mulOneSubXPow24 (m : ℕ) (c : List ℤ) : List ℤ :=
  (List.range c.length).map fun i =>
    ((List.range 25).map fun j =>
      if m * j ≤ i then oneSubXPow24.getD j 0 * c.getD (i - m * j) 0 else 0).sum

/-- The coefficients of `x^0, …, x^(N-1)` of `∏_{j=1}^{N} (1 - x^j)^24`; factors
with `j ≥ N` do not affect these coefficients, so this is the truncation of
the infinite product `∏_{j ≥ 1} (1 - x^j)^24` modulo `x^N`. -/
def etaPow24Trunc (N : ℕ) : List ℤ :=
  (List.range N).foldl (fun acc j => mulOneSubXPow24 (j + 1) acc)
    ((List.range N).map fun i => if i = 0 then 1 else 0)

/-- Ramanujan's tau function (A000594): `tau n` is the coefficient of `x^n` in
`x * ∏_{j ≥ 1} (1 - x^j)^24`, i.e. the coefficient of `x^(n-1)` of the
product.  The constant coefficient of `x * ∏ …` is `0`, so `tau 0 = 0`. -/
def tau (n : ℕ) : ℤ :=
  if n = 0 then 0 else (etaPow24Trunc n).getD (n - 1) 0

/-- Ground truth: the first 15 terms of A000594. -/
example : (List.range 15).map (fun i => tau (i + 1)) =
    [1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920, 534612,
      -370944, -577738, 401856, 1217160] := by
  decide +kernel

/-! ## The triangle A051731 and its action -/

/-- The triangle A051731: `T(n, m) = 1` if `m ∣ n`, and `0` otherwise
(read for `1 ≤ m ≤ n`). -/
def A051731 (n m : ℕ) : ℤ :=
  if m ∣ n then 1 else 0

/-- Ground truth: rows `1, …, 10` of A051731. -/
example : (List.range 10).flatMap (fun i => (List.range (i + 1)).map
      fun j => A051731 (i + 1) (j + 1)) =
    [1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0,
      1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0,
      0, 1] := by
  decide +kernel

/-- The lower-triangular matrix A051731 applied to a column vector
`v = (v 1, v 2, …)`: the `n`-th entry is `∑_{m=1}^{n} T(n, m) * v m`
(the inverse Moebius transform of `v`). -/
def applyA051731 (v : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ m ∈ Finset.Icc 1 n, A051731 n m * v m

/-- `A051731^k * A000594`: the matrix A051731 applied `k` times to the column
vector of Ramanujan's tau function.  (`seq 24` is A128382.) -/
def seq : ℕ → ℕ → ℤ
  | 0 => tau
  | k + 1 => applyA051731 (seq k)

/-- Applying A051731 is the inverse Moebius transform:
`(A051731 v)(n) = ∑_{m ∣ n} v m`. -/
theorem applyA051731_eq_sum_divisors (v : ℕ → ℤ) (n : ℕ) :
    applyA051731 v n = ∑ m ∈ n.divisors, v m := by
  have hIcc : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := rfl
  rw [applyA051731, Nat.divisors, hIcc, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : m ∣ n
  · simp only [A051731, hm, if_true, one_mul]
  · simp only [A051731, hm, if_false, zero_mul]

/-- The divisor-sum form of `seq`, used for evaluation. -/
def seqDiv : ℕ → ℕ → ℤ
  | 0 => tau
  | k + 1 => fun n => ∑ m ∈ n.divisors, seqDiv k m

/-- `seq` agrees with its divisor-sum form `seqDiv`. -/
theorem seq_eq_seqDiv (k : ℕ) : seq k = seqDiv k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext n
    rw [seq, seqDiv, applyA051731_eq_sum_divisors, ih]

/-- Ground truth: the first 15 terms of A128382 (`k = 24`). -/
example : (List.range 15).map (fun i => seq 24 (i + 1)) =
    [1, 0, 276, -1748, 4854, 0, -16720, 44552, -107295, 0, 534636, -482448, -577714,
      0, 1339704] := by
  rw [seq_eq_seqDiv]
  decide +kernel

/-! ## The conjectures -/

/-- **Adamson's conjecture (A128382, Gary W. Adamson, Feb 28 2007).**

Verbatim: "Conjecture: given the inverse Moebius transform operation performed
any k times (k=1,2,3,...); k=24 is the only such sequence with zeros."

Formalized: for every positive `k`, the sequence `A051731^k * A000594`
(indexed by `n ≥ 1`) has a zero term if and only if `k = 24`. -/
def Conjecture : Prop :=
  ∀ k : ℕ, 0 < k → ((∃ n : ℕ, 0 < n ∧ seq k n = 0) ↔ k = 24)

/-- **Adamson's weaker conjecture (A128382, same comment).**

Verbatim: "A weaker conjecture: "zero" occurs an infinite number of times in
A128382."

Formalized: the set of indices `n ≥ 1` with `A128382(n) = 0` is infinite.
This is true (zeros at all `n ≡ 2 (mod 4)` by multiplicativity of `tau`), but
it is not proved in this module. -/
def WeakConjecture : Prop :=
  {n : ℕ | 0 < n ∧ seq 24 n = 0}.Infinite

/-! ## The refutation -/

/-- Every sequence `A051731^k * A000594` starts with `1`. -/
theorem seq_one (k : ℕ) : seq k 1 = 1 := by
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    rw [seq, applyA051731_eq_sum_divisors, Nat.divisors_one, Finset.sum_singleton, ih]

/-- At a prime `p`, `(A051731^k * A000594)(p) = tau(p) + k`. -/
theorem seq_prime (k : ℕ) {p : ℕ} (hp : p.Prime) : seq k p = tau p + k := by
  induction k with
  | zero => simp [seq]
  | succ k ih =>
    have hp1 : p ≠ 1 := hp.ne_one
    rw [seq, applyA051731_eq_sum_divisors, hp.divisors, Finset.sum_pair hp1.symm,
      ih, seq_one]
    push_cast
    ring

/-- Ramanujan's `tau(7) = -16744`. -/
theorem tau_seven : tau 7 = -16744 := by
  decide +kernel

/-- The sequence `A051731^16744 * A000594` vanishes at `n = 7`:
`tau(7) + 16744 = 0`. -/
theorem seq_16744_seven : seq 16744 7 = 0 := by
  rw [seq_prime 16744 (by norm_num), tau_seven]
  norm_num

/-- **Adamson's conjecture is false.**  Counterexample: `k = 16744`, `n = 7`.
At a prime `p` the `k`-th sequence equals `tau(p) + k`, and
`tau(7) = -16744`, so `A051731^16744 * A000594` has `a(7) = 0`
(and hence, by multiplicativity, `a(n) = 0` whenever `7 ∥ n`).  By
`seq_prime`, a zero at a prime `p` occurs exactly when `tau(p) < 0`, with
`k = -tau(p)`; `k = 24` is the case `p = 2`.  The author presumably intended
the claim only for small `k`: the triage brute-force search (`k ≤ 3000`,
`n ≤ 64`; evidence, not proved here) finds zeros only for `k = 24`. -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  have h16744 := (h 16744 (by norm_num)).mp ⟨7, by norm_num, seq_16744_seven⟩
  norm_num at h16744

end Candidates.A128382Refutation
