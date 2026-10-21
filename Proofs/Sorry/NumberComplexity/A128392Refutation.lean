/-
# A128392 — Adamson: only `k = 12` gives a sequence `A126988^k * A000594` with a zero

## OEIS source (retrieved 2026-10-21 with `oeis show A128392` and the live entry)

```
NAME:     A126988^12 * A000594.
TERMS:    1,0,288,-1736,4890,0,-16660,44576,-103869,0,534744,-499968,-577582,0,
          1408320,2507344,-6905730,0,10661648,-8489040,-4798080,0,18643548,
          12837888,-25207475,0,-77183496,28921760,128406978,0,-52842796,
          -151328128,154006272,0,-81467400
KEYWORDS: sign,mult
COMMENT (the conjecture, unsigned in the entry; AUTHOR line of the entry is
  Gary W. Adamson, Feb 28 2007):
  Conjecture: Given A126988^k, k any positive integer, A128392 is the only
  sequence in the infinite set with zeros.
COMMENT:
  Each application of A126988 corresponds to the Dirichlet convolution of the
  natural numbers with the sequence on the right. Since both Ramanujan's tau
  function A000594 and the natural numbers are multiplicative, the resulting
  sequence will also be multiplicative. - _Andrew Howroyd_, Aug 03 2018
PROGRAM (PARI):
  seq(n, k=12)={my(u=vector(n,n,n), v=vector(n,n,ramanujantau(n)));
  for(i=1, k, v=dirmul(u,v)); v} \\ _Andrew Howroyd_, Aug 03 2018
```

No later comment in the entry retracts or amends the conjecture.

A126988: "Triangle read by rows: T(n,k) = n/k if k is a divisor of n;
T(n,k) = 0 if k is not a divisor of n (1 <= k <= n)."
A000594: "Ramanujan's tau function", G.f. `x * Product_{k>=1} (1 - x^k)^24`.

## Status

This module **refutes** the conjecture.  Applying A126988 is Dirichlet
convolution with `N(n) = n`, so at a prime `p` the `k`-th sequence takes the
value `tau(p) + k * p`.  Since `tau(7) = -16744 = -7 * 2392`, the sequence for
`k = 2392` vanishes at `n = 7`.
-/
import Mathlib

set_option autoImplicit false
set_option Elab.async false

namespace Candidates.A128392Refutation

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

/-! ## The triangle A126988 and its action -/

/-- The triangle A126988: `T(n, m) = n / m` if `m ∣ n`, and `0` otherwise
(read for `1 ≤ m ≤ n`). -/
def A126988 (n m : ℕ) : ℤ :=
  if m ∣ n then ((n / m : ℕ) : ℤ) else 0

/-- Ground truth: rows `1, …, 12` of A126988. -/
example : (List.range 12).flatMap (fun i => (List.range (i + 1)).map
      fun j => A126988 (i + 1) (j + 1)) =
    [1, 2, 1, 3, 0, 1, 4, 2, 0, 1, 5, 0, 0, 0, 1, 6, 3, 2, 0, 0, 1, 7, 0, 0, 0, 0, 0,
      1, 8, 4, 0, 2, 0, 0, 0, 1, 9, 0, 3, 0, 0, 0, 0, 0, 1, 10, 5, 0, 0, 2, 0, 0, 0,
      0, 1, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 12, 6, 4, 3, 0, 2, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

/-- The lower-triangular matrix A126988 applied to a column vector
`v = (v 1, v 2, …)`: the `n`-th entry is `∑_{m=1}^{n} T(n, m) * v m`. -/
def applyA126988 (v : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ m ∈ Finset.Icc 1 n, A126988 n m * v m

/-- `A126988^k * A000594`: the matrix A126988 applied `k` times to the column
vector of Ramanujan's tau function.  (`seq 12` is A128392.) -/
def seq : ℕ → ℕ → ℤ
  | 0 => tau
  | k + 1 => applyA126988 (seq k)

/-- Applying A126988 is Dirichlet convolution with `N(n) = n`:
`(A126988 v)(n) = ∑_{m ∣ n} (n / m) * v m`. -/
theorem applyA126988_eq_sum_divisors (v : ℕ → ℤ) (n : ℕ) :
    applyA126988 v n = ∑ m ∈ n.divisors, ((n / m : ℕ) : ℤ) * v m := by
  have hIcc : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := rfl
  rw [applyA126988, Nat.divisors, hIcc, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : m ∣ n
  · simp only [A126988, hm, if_true]
  · simp only [A126988, hm, if_false, zero_mul]

/-- The divisor-sum form of `seq`, used for evaluation. -/
def seqDiv : ℕ → ℕ → ℤ
  | 0 => tau
  | k + 1 => fun n => ∑ m ∈ n.divisors, ((n / m : ℕ) : ℤ) * seqDiv k m

/-- `seq` agrees with its divisor-sum form `seqDiv`. -/
theorem seq_eq_seqDiv (k : ℕ) : seq k = seqDiv k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext n
    rw [seq, seqDiv, applyA126988_eq_sum_divisors, ih]

/-- Ground truth: the first 15 terms of A128392 (`k = 12`). -/
example : (List.range 15).map (fun i => seq 12 (i + 1)) =
    [1, 0, 288, -1736, 4890, 0, -16660, 44576, -103869, 0, 534744, -499968, -577582,
      0, 1408320] := by
  rw [seq_eq_seqDiv]
  decide +kernel

/-! ## The conjecture -/

/-- **Adamson's conjecture (A128392, Gary W. Adamson, Feb 28 2007).**

Verbatim: "Conjecture: Given A126988^k, k any positive integer, A128392 is the
only sequence in the infinite set with zeros."

Formalized: for every positive `k`, the sequence `A126988^k * A000594`
(indexed by `n ≥ 1`) has a zero term if and only if `k = 12`. -/
def Conjecture : Prop :=
  ∀ k : ℕ, 0 < k → ((∃ n : ℕ, 0 < n ∧ seq k n = 0) ↔ k = 12)

/-! ## The refutation -/

/-- Every sequence `A126988^k * A000594` starts with `1`. -/
theorem seq_one (k : ℕ) : seq k 1 = 1 := by
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    rw [seq, applyA126988_eq_sum_divisors, Nat.divisors_one, Finset.sum_singleton, ih]
    norm_num

/-- At a prime `p`, `(A126988^k * A000594)(p) = tau(p) + k * p`. -/
theorem seq_prime (k : ℕ) {p : ℕ} (hp : p.Prime) : seq k p = tau p + k * p := by
  induction k with
  | zero => simp [seq]
  | succ k ih =>
    have hp1 : p ≠ 1 := hp.ne_one
    rw [seq, applyA126988_eq_sum_divisors, hp.divisors, Finset.sum_pair hp1.symm,
      ih, seq_one, Nat.div_one, Nat.div_self hp.pos]
    push_cast
    ring

/-- Ramanujan's `tau(7) = -16744 = -7 * 2392`. -/
theorem tau_seven : tau 7 = -16744 := by
  decide +kernel

/-- The sequence `A126988^2392 * A000594` vanishes at `n = 7`:
`tau(7) + 2392 * 7 = -16744 + 16744 = 0`. -/
theorem seq_2392_seven : seq 2392 7 = 0 := by
  rw [seq_prime 2392 (by norm_num), tau_seven]
  norm_num

/-- **Adamson's conjecture is false.**  Counterexample: `k = 2392`, `n = 7`.
At a prime `p` the `k`-th sequence equals `tau(p) + k p`, and
`tau(7) = -16744 = -7 * 2392`, so `A126988^2392 * A000594` has `a(7) = 0`
(and hence, by multiplicativity, `a(n) = 0` whenever `7 ∥ n`).  By
`seq_prime`, a zero at a prime `p` occurs exactly when `p ∣ tau(p)` and
`tau(p) < 0`, with `k = -tau(p) / p`.  The author presumably intended the
claim only for small `k`: the triage brute-force search (`k ≤ 3000`, `n ≤ 64`;
evidence, not proved here) finds zeros only for `k = 12` and `k = 2392`. -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  have h2392 := (h 2392 (by norm_num)).mp ⟨7, by norm_num, seq_2392_seven⟩
  norm_num at h2392

end Candidates.A128392Refutation
