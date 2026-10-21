/-
# A128381 — Adamson's "only k = 6 and k = 24" conjecture is false

## OEIS source (retrieved 2026-10-21 with `oeis show A128381`; author line
## from the live entry https://oeis.org/A128381/internal)

```
NAME:     A007318^24 * A000594.
TERMS:    1,0,-324,-10976,-260898,-4919184,-67536616,-212659776,28757879829,...
FORMULA:  Binomial transform operation performed 24 times on A000594, assuming
          A000594 has offset zero.
COMMENT:  Conjecture: given the bto performed any k times on A000594
          (k = 1, 2, 3, ...); k = 6 and k = 24 are the only members of the set
          with zeros. k = 6 generates (1, -18, 0, 688, 4494, 5508, ...).
AUTHOR:   Gary W. Adamson, Feb 28 2007
MATHEMATICA: Nest[Table[Sum[Binomial[n-1, k-1] * #[[k]], {k, 1, n}],
          {n, 1, Length[#]}] &, RamanujanTau[Range[19]], 24]
          (* _Amiram Eldar_, Jan 08 2025 *)
```

No later comment in the entry retracts or amends the conjecture.

## Status

This module **refutes** the conjecture.  With `b j = τ (j + 1)` (A000594 taken
with offset zero), `k` binomial transforms give
`B_k(n) = ∑_{j ≤ n} C(n, j) k^(n - j) τ(j + 1)`, so
`B_k(1) = k - 24` and `B_k(2) = k² - 48k + 252 = (k - 6)(k - 42)`.
The printed `k = 6` zero is one root of this quadratic; the other root
`k = 42` also produces a zero, `B_42(2) = 0`.

`Elab.async false` keeps the kernel checks sequential; under a virtual-memory
cap the default asynchronous elaboration fails to create its worker threads.
-/
import Mathlib

set_option autoImplicit false
set_option Elab.async false

namespace Candidates.A128381Refutation

/-! ## The Ramanujan tau function (A000594)

`τ(n)` is the coefficient of `q^n` in `q ∏_{i ≥ 1} (1 - q^i)^24`, i.e. the
coefficient of `X^(n-1)` in `∏_{i ≥ 1} (1 - X^i)^24`.  Factors with `i ≥ n`
are `≡ 1 mod X^n` and the series is truncated at length `n`, so the finite
list computation below is exact for that coefficient. -/

/-- Multiply a power series truncated to its first `N` coefficients (given as a
list of length `N`) by `1 - X^i`, keeping the first `N` coefficients:
the new coefficient of `X^m` is `f m - f (m - i)` (the second term only when
`i ≤ m`). -/
def mulOneSubXPow (N i : ℕ) (f : List ℤ) : List ℤ :=
  List.zipWith (· - ·) f ((List.replicate i 0 ++ f).take N)

/-- The first `N` coefficients of `∏_{i = 1}^{N} (1 - X^i)^24`, which agree with
those of the infinite product `∏_{i ≥ 1} (1 - X^i)^24`. -/
def deltaCoeffs (N : ℕ) : List ℤ :=
  (List.range' 1 N).foldl (fun f i => (mulOneSubXPow N i)^[24] f)
    (1 :: List.replicate (N - 1) 0)

/-- Ramanujan's tau function (A000594): `τ(n)` is the coefficient of `q^n` in
`q ∏_{i ≥ 1} (1 - q^i)^24`, with the convention `τ(0) = 0`. -/
def tau (n : ℕ) : ℤ :=
  if n = 0 then 0 else (deltaCoeffs n).getD (n - 1) 0

/-- Ground truth: the first twelve terms of A000594. -/
example : (List.range' 1 12).map tau =
    [1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920, 534612,
      -370944] := by
  decide +kernel

/-- `τ(1) = 1`. -/
theorem tau_one : tau 1 = 1 := by decide +kernel

/-- `τ(2) = -24`. -/
theorem tau_two : tau 2 = -24 := by decide +kernel

/-- `τ(3) = 252`. -/
theorem tau_three : tau 3 = 252 := by decide +kernel

/-- A000594 taken with offset zero, as in the entry: `b j = τ (j + 1)`. -/
def b (j : ℕ) : ℤ := tau (j + 1)

/-! ## The binomial transform and its iterates -/

/-- The binomial transform ("bto"): `(bt a) n = ∑_{j = 0}^{n} C(n, j) a j`
(the Mathematica `Table[Sum[Binomial[n-1, k-1] * #[[k]], ...]]` step in
0-based indexing). -/
def bt (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1), (n.choose j : ℤ) * a j

/-- The sequence obtained from A000594 (offset zero) by applying the binomial
transform `k` times; `k = 24` is A128381. -/
def iterBT (k : ℕ) : ℕ → ℤ := bt^[k] b

/-- Vandermonde-type inner sum:
`∑_{m = j}^{n} C(n, m) C(m, j) c^(m - j) = C(n, j) (c + 1)^(n - j)`. -/
theorem sum_Icc_choose_mul_choose_mul_pow (n j : ℕ) (hj : j ≤ n) (c : ℤ) :
    ∑ m ∈ Finset.Icc j n, (n.choose m : ℤ) * ((m.choose j : ℤ) * c ^ (m - j)) =
      (n.choose j : ℤ) * (c + 1) ^ (n - j) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, add_pow,
    Finset.mul_sum]
  have hlen : n + 1 - j = n - j + 1 := by omega
  rw [hlen]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hchoose : (n.choose (j + i) : ℤ) * ((j + i).choose j : ℤ) =
      (n.choose j : ℤ) * ((n - j).choose i : ℤ) := by
    have h := Nat.choose_mul (n := n) (k := j + i) (s := j) (by omega)
    rw [Nat.add_sub_cancel_left] at h
    exact_mod_cast h
  rw [Nat.add_sub_cancel_left, one_pow, mul_one, ← mul_assoc, hchoose]
  ring

/-- Closed form of the `k`-fold binomial transform:
`(bt^[k] a) n = ∑_{j = 0}^{n} C(n, j) k^(n - j) a j`. -/
theorem iterate_bt (a : ℕ → ℤ) (k n : ℕ) :
    (bt^[k] a) n =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℤ) * (k : ℤ) ^ (n - j) * a j := by
  induction k generalizing n with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Nat.cast_zero]
    rw [Finset.sum_eq_single n]
    · simp
    · intro j hj hjn
      have hjlt : j < n := by
        have hj' := Finset.mem_range.mp hj
        omega
      simp [Nat.sub_ne_zero_of_lt hjlt]
    · simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    simp only [bt, ih, Finset.mul_sum]
    rw [Finset.sum_comm' (t' := Finset.range (n + 1)) (s' := fun j => Finset.Icc j n)]
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have h := sum_Icc_choose_mul_choose_mul_pow n j hjn (k : ℤ)
      push_cast
      calc ∑ m ∈ Finset.Icc j n,
            (n.choose m : ℤ) * ((m.choose j : ℤ) * (k : ℤ) ^ (m - j) * a j)
          = (∑ m ∈ Finset.Icc j n,
              (n.choose m : ℤ) * ((m.choose j : ℤ) * (k : ℤ) ^ (m - j))) * a j := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun m _ => ?_
            ring
        _ = (n.choose j : ℤ) * ((k : ℤ) + 1) ^ (n - j) * a j := by rw [h]
    · intro m j
      simp only [Finset.mem_range, Finset.mem_Icc]
      omega

/-- Closed form of the `k`-th iterate on A000594 (offset zero). -/
theorem iterBT_eq (k n : ℕ) :
    iterBT k n =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℤ) * (k : ℤ) ^ (n - j) * tau (j + 1) :=
  iterate_bt b k n

/-- Ground truth: the first terms of A128381 (`k = 24`). -/
example : (List.range 6).map (fun n => iterBT 24 n) =
    [1, 0, -324, -10976, -260898, -4919184] := by
  simp only [iterBT_eq]
  decide +kernel

/-- Ground truth: the `k = 6` terms printed in the conjecture comment. -/
example : (List.range 6).map (fun n => iterBT 6 n) =
    [1, -18, 0, 688, 4494, 5508] := by
  simp only [iterBT_eq]
  decide +kernel

/-! ## The conjecture -/

/-- **Adamson's conjecture (A128381, Gary W. Adamson, Feb 28 2007).**
Verbatim: "Conjecture: given the bto performed any k times on A000594
(k = 1, 2, 3, ...); k = 6 and k = 24 are the only members of the set with
zeros."

Formally: for every `k ≥ 1`, the `k`-fold binomial transform of A000594 (offset
zero) has a zero term if and only if `k = 6` or `k = 24`. -/
def AdamsonConjecture : Prop :=
  ∀ k : ℕ, 1 ≤ k → ((∃ n : ℕ, iterBT k n = 0) ↔ (k = 6 ∨ k = 24))

/-- `B_k(1) = k - 24`. -/
theorem iterBT_one (k : ℕ) : iterBT k 1 = (k : ℤ) - 24 := by
  rw [iterBT_eq]
  simp only [Nat.reduceAdd, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
    Nat.choose_succ_self_right, zero_add, Nat.cast_one, tsub_zero, pow_one, one_mul, tau_one,
    mul_one, Nat.choose_self, tsub_self, pow_zero, tau_two, Int.reduceNeg, mul_neg]
  ring

/-- `B_k(2) = k² - 48k + 252 = (k - 6)(k - 42)`. -/
theorem iterBT_two (k : ℕ) : iterBT k 2 = ((k : ℤ) - 6) * ((k : ℤ) - 42) := by
  rw [iterBT_eq]
  simp only [Nat.reduceAdd, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
    Nat.choose_zero_right, Nat.cast_one, tsub_zero, one_mul, zero_add, tau_one, mul_one,
    Nat.choose_succ_self_right, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, tau_two,
    Int.reduceNeg, mul_neg, Nat.choose_self, tsub_self, pow_zero, tau_three]
  ring

/-- Non-vacuity of the "if" direction: `k = 6` and `k = 24` do produce zeros
(`B_6(2) = 0`, `B_24(1) = 0`), exactly as the entry says. -/
example : (∃ n : ℕ, iterBT 6 n = 0) ∧ (∃ n : ℕ, iterBT 24 n = 0) :=
  ⟨⟨2, by rw [iterBT_two]; norm_num⟩, ⟨1, by rw [iterBT_one]; norm_num⟩⟩

/-- `B_42(2) = 0`: the 42-fold binomial transform of A000594 (offset zero) has
a zero term. -/
theorem iterBT_fortyTwo_two : iterBT 42 2 = 0 := by
  rw [iterBT_two]
  norm_num

/-- **Refutation of Adamson's conjecture (A128381).**  Counterexample `k = 42`,
`n = 2`: `B_42(2) = 42² - 48·42 + 252 = 0`, the second root of
`B_k(2) = (k - 6)(k - 42)`, whose first root is the printed `k = 6`.  The author
evidently found the root `k = 6` of this quadratic but missed `k = 42`; the
corrected statement for `n ≤ 2` is `zero_iff_of_le_two`. -/
theorem adamsonConjecture_false : ¬ AdamsonConjecture := by
  intro h
  have hk : (42 : ℕ) = 6 ∨ (42 : ℕ) = 24 := (h 42 (by norm_num)).mp ⟨2, iterBT_fortyTwo_two⟩
  omega

/-- Corrected statement over the first three terms: for `n ≤ 2`, `B_k(n) = 0`
exactly when `(k, n) = (24, 1)`, `(6, 2)` or `(42, 2)`. -/
theorem zero_iff_of_le_two (k n : ℕ) (hn : n ≤ 2) :
    iterBT k n = 0 ↔ (n = 1 ∧ k = 24) ∨ (n = 2 ∧ (k = 6 ∨ k = 42)) := by
  interval_cases n
  · have h0 : iterBT k 0 = 1 := by
      rw [iterBT_eq]
      simp [tau_one]
    simp [h0]
  · rw [iterBT_one, sub_eq_zero]
    constructor
    · intro hk
      left
      exact ⟨rfl, by exact_mod_cast hk⟩
    · rintro (⟨-, hk⟩ | ⟨h, -⟩)
      · subst hk
        norm_num
      · omega
  · rw [iterBT_two, mul_eq_zero, sub_eq_zero, sub_eq_zero]
    constructor
    · rintro (hk | hk)
      · exact Or.inr ⟨rfl, Or.inl (by exact_mod_cast hk)⟩
      · exact Or.inr ⟨rfl, Or.inr (by exact_mod_cast hk)⟩
    · rintro (⟨h, -⟩ | ⟨-, hk | hk⟩)
      · omega
      · subst hk
        norm_num
      · subst hk
        norm_num

end Candidates.A128381Refutation
