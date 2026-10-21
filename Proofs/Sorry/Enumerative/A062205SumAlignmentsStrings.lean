/-
# A062205 — Bala: alignments of n strings of length 4 are 1 mod 80 and eventually periodic mod k

## OEIS source (pulled with `oeis show A062205`, retrieved 2026-10-21)

```
NAME:     Number of alignments of n strings of length 4.
TERMS:    1,1,321,699121,5552351121,117029959485121,5402040231378569121,
          480086443888959812703121,74896283763383392805211587121,...
KEYWORDS: nonn
XREFS:    See A062204 for references, formulas and comments.
          Row n=4 of A262809.
COMMENT (the conjecture):
  Conjectures: a(n) == 1 (mod 80); for fixed k, the sequence a(n) (mod k)
  eventually becomes periodic. - _Peter Bala_, Dec 19 2019
```

Defining formula (A062204, the referenced entry, and A262809):

```
A(n, y) = sum(k=0,n*y, sum(t=0,k, (-1)^t * binomial(k,t) * binomial(k-t,y)^n )).
```

A062205 is `A(n, 4)`; the offset is 0 and `a(0) = 1`, so the first part of the
conjecture is read for `n ≥ 1` (for `n = 0` it holds as well, since `a(0) = 1`).

## Literature status (triage)

Open: no proof in the entry; a web search found only the OEIS statements of
the same conjecture family (A055203 mod 12, A062208 mod 60, A062205 mod 80).
No matches is not novelty.

## Proof outline (formalized below)

Write `P_n(i) = C(i,4)^n`.  The inner sum `∑_t (-1)^t C(k,t) P_n(k-t)` is the
`k`-th forward difference of `P_n` at `0`; it vanishes for `k > 4n` because
`P_n` is a rational polynomial of degree `4n`.  So the outer cut-off `4n` can be
replaced by any `K ≥ 4n`, and the whole sum is an integer combination of the
values `P_n(i)`.  Hence pointwise congruences `P_m(i) ≡ P_n(i) (mod M)` give
`a(m) ≡ a(n) (mod M)`.

* mod 5: by Lucas, `C(i,4) ≡ C(i mod 5, 4) ∈ {0,1}`, so `P_n ≡ P_1`.
* mod 16: `x^8 = x^4` in `ZMod 16`, so `a(n+4) ≡ a(n)` for `n ≥ 4`; the base
  cases `a(1..7) ≡ 1` are kernel computations.
* periodicity mod `k`: in the finite monoid `ZMod k` the power maps `x ↦ x^n`
  repeat, so `x^(n+T) = x^n` for all `x` and all `n ≥ N`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A062205SumAlignmentsStrings

open Finset Polynomial

/-! ## Definition layer -/

/-- The OEIS double sum with a general integer-valued summand `f` and outer
cut-off `K`: `∑_{k=0}^{K} ∑_{t=0}^{k} (-1)^t C(k,t) f(k-t)`.  The `k - t` is a
natural subtraction guarded by `t ≤ k` (the inner range). -/
def alignSum (f : ℕ → ℤ) (K : ℕ) : ℤ :=
  ∑ k ∈ range (K + 1), ∑ t ∈ range (k + 1), (-1) ^ t * (k.choose t : ℤ) * f (k - t)

/-- A062205: the number of alignments of `n` strings of length 4,
`a(n) = ∑_{k=0}^{4n} ∑_{t=0}^{k} (-1)^t C(k,t) C(k-t,4)^n` (formula of A062204
with `y = 4`). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ range (4 * n + 1), ∑ t ∈ range (k + 1),
    (-1) ^ t * (k.choose t : ℤ) * ((k - t).choose 4 : ℤ) ^ n

/-! ### Ground truth against the listed terms -/

example : a 0 = 1 := by decide
example : a 1 = 1 := by decide
example : a 2 = 321 := by decide
example : a 3 = 699121 := by decide
example : a 4 = 5552351121 := by decide
example : a 5 = 117029959485121 := by decide

/-- `a n` is the general double sum at the summand `i ↦ C(i,4)^n` and cut-off `4n`. -/
theorem a_eq_alignSum (n : ℕ) : a n = alignSum (fun i => (i.choose 4 : ℤ) ^ n) (4 * n) := rfl

/-! ## The finite-difference bridge -/

/-- **Load-bearing step.** If `f` takes the values of a rational polynomial `P` at
the naturals, then the inner sum `∑_{t ≤ k} (-1)^t C(k,t) f(k-t)` (the `k`-th
forward difference of `f` at `0`) vanishes for `k > deg P`. -/
theorem inner_sum_eq_zero (P : ℚ[X]) (f : ℕ → ℤ) (hf : ∀ i : ℕ, (f i : ℚ) = P.eval (i : ℚ))
    (k : ℕ) (hk : P.natDegree < k) :
    ∑ t ∈ range (k + 1), (-1) ^ t * (k.choose t : ℤ) * f (k - t) = 0 := by
  have hzero := congr_fun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (P := P) hk) 0
  rw [fwdDiff_iter_eq_sum_shift, Pi.zero_apply] at hzero
  have hcast :
      ((∑ j ∈ range (k + 1), (-1) ^ (k - j) * (k.choose j : ℤ) * f j : ℤ) : ℚ) = 0 := by
    rw [← hzero]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [zsmul_eq_mul, hf j]
    simp
  have hint : ∑ j ∈ range (k + 1), (-1) ^ (k - j) * (k.choose j : ℤ) * f j = 0 := by
    exact_mod_cast hcast
  rw [← hint, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun t ht => ?_
  have htk : t ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
  have h1 : k + 1 - 1 - t = k - t := by omega
  have h2 : k - (k - t) = t := by omega
  rw [h1, h2, Nat.choose_symm htk]

/-- For a polynomial summand, the outer cut-off can be raised freely past the
degree: `alignSum f K = alignSum f D` whenever `deg P ≤ D ≤ K`. -/
theorem alignSum_eq_of_le (P : ℚ[X]) (f : ℕ → ℤ) (hf : ∀ i : ℕ, (f i : ℚ) = P.eval (i : ℚ))
    {D K : ℕ} (hD : P.natDegree ≤ D) (hK : D ≤ K) : alignSum f K = alignSum f D := by
  induction K, hK using Nat.le_induction with
  | base => rfl
  | succ K hDK ih =>
    have hzero := inner_sum_eq_zero P f hf (K + 1) (by omega)
    rw [alignSum, Finset.sum_range_succ, hzero, add_zero]
    exact ih

/-- `alignSum` respects pointwise congruences of the summand. -/
theorem alignSum_modEq {f g : ℕ → ℤ} {M : ℤ} (h : ∀ i, f i ≡ g i [ZMOD M]) (K : ℕ) :
    alignSum f K ≡ alignSum g K [ZMOD M] :=
  Int.ModEq.sum fun k _ => Int.ModEq.sum fun t _ => (h (k - t)).mul_left _

/-- The rational polynomial `(X(X-1)(X-2)(X-3)/24)^n`, whose value at a natural
`i` is `C(i,4)^n`. -/
noncomputable def choosePoly (n : ℕ) : ℚ[X] := (C (1 / 24 : ℚ) * descPochhammer ℚ 4) ^ n

/-- `choosePoly n` has degree at most `4n`. -/
theorem choosePoly_natDegree_le (n : ℕ) : (choosePoly n).natDegree ≤ 4 * n := by
  unfold choosePoly
  calc ((C (1 / 24 : ℚ) * descPochhammer ℚ 4) ^ n).natDegree
      ≤ n * (C (1 / 24 : ℚ) * descPochhammer ℚ 4).natDegree := natDegree_pow_le
    _ ≤ n * 4 := by
        gcongr
        exact (natDegree_C_mul_le _ _).trans (descPochhammer_natDegree ℚ 4).le
    _ = 4 * n := by ring

/-- `choosePoly n` evaluates to `C(i,4)^n` at every natural `i`. -/
theorem choosePoly_eval (n i : ℕ) : (((i.choose 4 : ℤ) ^ n : ℤ) : ℚ) = (choosePoly n).eval (i : ℚ) := by
  rw [choosePoly, eval_pow, eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  push_cast [Nat.factorial]
  ring

/-- **Transfer.** Pointwise congruences `C(i,4)^m ≡ C(i,4)^n (mod M)` give
`a(m) ≡ a(n) (mod M)`. -/
theorem a_modEq_of_forall {M : ℤ} {m n : ℕ}
    (h : ∀ i : ℕ, (i.choose 4 : ℤ) ^ m ≡ (i.choose 4 : ℤ) ^ n [ZMOD M]) :
    a m ≡ a n [ZMOD M] := by
  have hm : a m = alignSum (fun i => (i.choose 4 : ℤ) ^ m) (4 * m + 4 * n) := by
    rw [a_eq_alignSum]
    exact (alignSum_eq_of_le (choosePoly m) _ (choosePoly_eval m) (choosePoly_natDegree_le m)
      (by omega)).symm
  have hn : a n = alignSum (fun i => (i.choose 4 : ℤ) ^ n) (4 * m + 4 * n) := by
    rw [a_eq_alignSum]
    exact (alignSum_eq_of_le (choosePoly n) _ (choosePoly_eval n) (choosePoly_natDegree_le n)
      (by omega)).symm
  rw [hm, hn]
  exact alignSum_modEq h _

/-- A power identity in `ZMod M` gives the corresponding integer congruence. -/
theorem pow_modEq_of_zmod {M m n : ℕ} (h : ∀ x : ZMod M, x ^ m = x ^ n) (c : ℤ) :
    c ^ m ≡ c ^ n [ZMOD (M : ℤ)] := by
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  exact h _

/-! ## Part (i): `a(n) ≡ 1 (mod 80)` -/

/-- Mod 5, by Lucas: `C(i,4)^n ≡ C(i,4) (mod 5)` for `n ≥ 1`. -/
theorem choose_four_pow_modEq_five (i : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (i.choose 4 : ℤ) ^ n ≡ (i.choose 4 : ℤ) ^ 1 [ZMOD 5] := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hlucas : i.choose 4 ≡ (i % 5).choose 4 [MOD 5] := by
    have := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := i) (k := 4) (p := 5)
    simpa using this
  have hz : (i.choose 4 : ℤ) ≡ ((i % 5).choose 4 : ℤ) [ZMOD 5] := by
    exact_mod_cast Int.natCast_modEq_iff.mpr hlucas
  have hidem : ((i % 5).choose 4 : ℤ) ^ n = ((i % 5).choose 4 : ℤ) := by
    have hr : i % 5 < 5 := Nat.mod_lt _ (by norm_num)
    have hn0 : n ≠ 0 := by omega
    generalize i % 5 = r at hr ⊢
    interval_cases r <;> simp [Nat.choose, hn0]
  calc (i.choose 4 : ℤ) ^ n ≡ ((i % 5).choose 4 : ℤ) ^ n [ZMOD 5] := hz.pow n
    _ = ((i % 5).choose 4 : ℤ) := hidem
    _ ≡ (i.choose 4 : ℤ) [ZMOD 5] := hz.symm
    _ = (i.choose 4 : ℤ) ^ 1 := (pow_one _).symm

/-- `a(n) ≡ 1 (mod 5)` for `n ≥ 1`. -/
theorem a_modEq_one_five {n : ℕ} (hn : 1 ≤ n) : a n ≡ 1 [ZMOD 5] := by
  have h1 : a 1 = 1 := by decide
  rw [← h1]
  exact a_modEq_of_forall fun i => choose_four_pow_modEq_five i hn

/-- In `ZMod 16`, `x^(n+4) = x^n` for every `n ≥ 4`. -/
theorem zmod16_pow_add_four {n : ℕ} (hn : 4 ≤ n) (x : ZMod 16) : x ^ (n + 4) = x ^ n := by
  have h84 : ∀ y : ZMod 16, y ^ 8 = y ^ 4 := by decide
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  calc x ^ (4 + j + 4) = x ^ j * x ^ 8 := by ring
    _ = x ^ j * x ^ 4 := by rw [h84 x]
    _ = x ^ (4 + j) := by ring

/-- `a(n) ≡ 1 (mod 16)` for `n ≥ 1`. -/
theorem a_modEq_one_sixteen {n : ℕ} (hn : 1 ≤ n) : a n ≡ 1 [ZMOD 16] := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hsmall : n ≤ 7
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have hstep : a (m + 4) ≡ a m [ZMOD 16] :=
        a_modEq_of_forall fun i =>
          pow_modEq_of_zmod (M := 16) (m := m + 4) (n := m)
            (zmod16_pow_add_four (n := m) (by omega)) _
      exact hstep.trans (ih m (by omega) (by omega))

/-- **Bala's conjecture (i) (A062205, Peter Bala, Dec 19 2019).**
Verbatim: "Conjectures: a(n) == 1 (mod 80)".  For every `n ≥ 1`, the number
`a(n)` of alignments of `n` strings of length 4 satisfies `a(n) ≡ 1 (mod 80)`. -/
theorem a_modEq_one_eighty {n : ℕ} (hn : 1 ≤ n) : a n ≡ 1 [ZMOD 80] := by
  have hcop : (5 : ℤ).natAbs.Coprime (16 : ℤ).natAbs := by decide
  have hboth := (Int.modEq_and_modEq_iff_modEq_mul hcop).mp
    ⟨a_modEq_one_five hn, a_modEq_one_sixteen hn⟩
  norm_num at hboth
  exact hboth

/-! ## Part (ii): eventual periodicity mod every `k ≥ 1` -/

/-- In `ZMod M` with `M ≠ 0` the power maps are eventually periodic, uniformly in
the base: `x^(n+T) = x^n` for all `x` and all `n ≥ N`, with `T > 0`. -/
theorem zmod_pow_eventually_periodic (M : ℕ) [NeZero M] :
    ∃ N T : ℕ, 0 < T ∧ ∀ n, N ≤ n → ∀ x : ZMod M, x ^ (n + T) = x ^ n := by
  obtain ⟨i, j, hij, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun e : ℕ => fun x : ZMod M => x ^ e)
  have key : ∀ p q : ℕ, p < q → (fun x : ZMod M => x ^ p) = (fun x => x ^ q) →
      ∃ N T : ℕ, 0 < T ∧ ∀ n, N ≤ n → ∀ x : ZMod M, x ^ (n + T) = x ^ n := by
    intro p q hpq hfun
    refine ⟨p, q - p, by omega, fun n hn x => ?_⟩
    have hx : x ^ p = x ^ q := congr_fun hfun x
    calc x ^ (n + (q - p)) = x ^ (n - p) * x ^ q := by
          rw [← pow_add]; congr 1; omega
      _ = x ^ (n - p) * x ^ p := by rw [hx]
      _ = x ^ n := by rw [← pow_add]; congr 1; omega
  rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
  · exact key i j hlt heq
  · exact key j i hgt heq.symm

/-- **Bala's conjecture (ii) (A062205, Peter Bala, Dec 19 2019).**
Verbatim: "for fixed k, the sequence a(n) (mod k) eventually becomes periodic".
For every `k ≥ 1` there are a threshold `N` and a period `T > 0` with
`a(n+T) ≡ a(n) (mod k)` for all `n ≥ N`. -/
theorem a_eventually_periodic (k : ℕ) (hk : 0 < k) :
    ∃ N T : ℕ, 0 < T ∧ ∀ n, N ≤ n → a (n + T) ≡ a n [ZMOD (k : ℤ)] := by
  haveI : NeZero k := ⟨hk.ne'⟩
  obtain ⟨N, T, hT, hper⟩ := zmod_pow_eventually_periodic k
  exact ⟨N, T, hT, fun n hn =>
    a_modEq_of_forall fun i => pow_modEq_of_zmod (hper n hn) _⟩

end Candidates.A062205SumAlignmentsStrings
