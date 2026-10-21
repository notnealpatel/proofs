/-
# A092674 — Perry: the constant term of a floor-sum recursion is never negative

## OEIS source (retrieved with `oeis show A092674` and https://oeis.org/A092674, 2026-10-21)

```
NAME:     Derived from a(n)=binomial(n+1,2) - sum{i=1,n-1,a(i)*floor(n/i)}
          (see A000010) - this is the value of the constant term.
OFFSET:   1,2
TERMS:    0,3,3,1,5,0,7,4,6,2,11,5,13,4,7,8,17,6,19,9,11,8,23,8,20,10,18,13,29,
          10,31,16,19,14,23,12,37,16,23,16,41,14,43,21,24,20,47,16,42,20,31,25,...
KEYWORDS: nonn
COMMENT (the conjecture):
  It is conjectured that a(n) is never less than 0 (tested to n=2000)
PROGRAM:
  (PARI) s=vector(200); t(n)=binomial(n+1,2); s[1]=x; for(i=2,200,
  s[i]=t(i)-sum(j=1,i-1, s[j]*floor(i/j))); for(i=1,200,print1(","polcoeff(s[i],0)))
AUTHOR:   _Jon Perry_, Mar 02 2004 (the conjecture comment is unsigned; it is
          part of the original submission)
```

The PARI program fixes the meaning: `a(1) = x` is an indeterminate, every
later `a(n)` is a polynomial (in fact linear) in `x`, and the sequence lists
the coefficient of `x^0`.

## Status

Triage: open (no proof in the entry or the literature as far as the triage
could tell; numerically checked to `n = 3000` by the triage and to `n = 6000`
for this card).  This module proves it: Möbius inversion of the floor-sum
recursion gives the closed form
`c(n) = φ(n) - μ(n) + [2 ∣ n] μ(n/2)`, and `φ(n) ≥ 2` for `n ≥ 3`.
The minimum value `0` is attained at `n = 1` and `n = 6`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A092674DefineSumFloor

open ArithmeticFunction

/-! ## Definition layer -/

/-- Perry's recursion with free initial value `x` in a commutative ring `R`:
`a(1) = x` and, for `n ≥ 2`,
`a(n) = binomial(n+1, 2) - ∑_{i=1}^{n-1} a(i) * floor(n/i)`.
The value at `0` is a junk value `0` (the entry has offset 1). Taking
`R = ℤ[X]` and `x = X` gives exactly the polynomials `s[n]` of the PARI program. -/
def seq {R : Type*} [CommRing R] (x : R) : ℕ → R
  | 0 => 0
  | 1 => x
  | n + 2 => ((n + 3).choose 2 : R) -
      ∑ i ∈ (Finset.Ioo 0 (n + 2)).attach, seq x i * (((n + 2) / (i : ℕ) : ℕ) : R)
  decreasing_by exact (Finset.mem_Ioo.1 i.2).2

/-- The constant term `c(n)` of `a(n)` (A092674), computed by specializing `x = 0`;
`coeff_zero_seq_X` identifies it with the coefficient of `X^0` of `seq X n`. -/
def constTerm (n : ℕ) : ℤ := seq (0 : ℤ) n

/-- The coefficient of `x` in `a(n)`; `seq_X_eq` shows `a(n) = constTerm n + xCoeff n * x`. -/
def xCoeff (n : ℕ) : ℤ := seq (1 : ℤ) n - seq (0 : ℤ) n

/-- The closed form `φ(n) - μ(n) + [2 ∣ n] μ(n/2)` of the constant term. -/
def closedForm (n : ℕ) : ℤ :=
  (n.totient : ℤ) - moebius n + (if 2 ∣ n then moebius (n / 2) else 0)

/-! ## Unfolding and the polynomial bridge -/

/-- The defining recursion of `seq` for `n ≥ 2`, with the sum over `0 < i < n`. -/
theorem seq_of_two_le {R : Type*} [CommRing R] (x : R) {n : ℕ} (hn : 2 ≤ n) :
    seq x n = ((n + 1).choose 2 : R) - ∑ i ∈ Finset.Ioo 0 n, seq x i * ((n / i : ℕ) : R) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [seq, Finset.sum_attach (Finset.Ioo 0 (m + 2)) (fun i => seq x i * (((m + 2) / i : ℕ) : R))]

/-- Ring homomorphisms commute with `seq`: `f (a_x(n)) = a_{f x}(n)`. -/
theorem map_seq {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : R) (n : ℕ) :
    f (seq x n) = seq (f x) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [seq]
    | 1, _ => simp [seq]
    | m + 2, ih =>
      rw [seq_of_two_le x (by omega), seq_of_two_le (f x) (by omega), map_sub, map_sum]
      simp only [map_mul, map_natCast]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [ih i (Finset.mem_Ioo.1 hi).2]

/-- The coefficient of `X^0` of the polynomial `a(n) ∈ ℤ[X]` (with `a(1) = X`)
is `constTerm n`. -/
theorem coeff_zero_seq_X (n : ℕ) :
    (seq (Polynomial.X : Polynomial ℤ) n).coeff 0 = constTerm n := by
  rw [Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coe_evalRingHom, map_seq]
  simp [constTerm]

/-! ## Ground truth

Kernel evaluation of the well-founded recursion `seq` is expensive (it is
unmemoized and unfolds accessibility proofs), so the listed terms are checked
on a structurally recursive table proved equal to `constTerm`. -/

/-- `constTerm 0 = 0` (junk value at the unused index). -/
theorem constTerm_zero : constTerm 0 = 0 := by simp [constTerm, seq]

/-- `c(1) = 0`: the constant term of `a(1) = x`. -/
theorem constTerm_one : constTerm 1 = 0 := by simp [constTerm, seq]

/-- A structurally recursive table of constant terms: `constTermTable n i = c(i)`
for `i ≤ n` (`constTermTable_eq`). -/
def constTermTable : ℕ → ℕ → ℤ
  | 0 => fun _ => 0
  | n + 1 =>
    let f := constTermTable n
    let v : ℤ := if n = 0 then 0 else
      ((n + 2).choose 2 : ℤ) - ∑ i ∈ Finset.Ioo 0 (n + 1), f i * (((n + 1) / i : ℕ) : ℤ)
    fun j => if j = n + 1 then v else f j

/-- The table agrees with the recursion: `constTermTable n i = c(i)` for `i ≤ n`. -/
theorem constTermTable_eq {n i : ℕ} (hi : i ≤ n) : constTermTable n i = constTerm i := by
  induction n generalizing i with
  | zero =>
    obtain rfl : i = 0 := by omega
    simp [constTermTable, constTerm, seq]
  | succ n ih =>
    simp only [constTermTable]
    split_ifs with hin hn0
    · subst hin hn0
      exact constTerm_one.symm
    · subst hin
      rw [constTerm, seq_of_two_le (0 : ℤ) (by omega)]
      push_cast
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [ih (by have hj' := (Finset.mem_Ioo.1 hj).2; omega)]
      rfl
    · exact ih (by omega)

/-- `constTerm` is the diagonal of the table. -/
theorem constTerm_eq_table : constTerm = fun n => constTermTable n n :=
  funext fun _ => (constTermTable_eq le_rfl).symm

/-- The first twenty listed terms of A092674 (offset 1); the zero at `n = 6`
shows that the nonnegativity bound is attained. -/
example : (List.range' 1 20).map constTerm =
    [0, 3, 3, 1, 5, 0, 7, 4, 6, 2, 11, 5, 13, 4, 7, 8, 17, 6, 19, 9] := by
  rw [constTerm_eq_table]
  decide +kernel

/-- `c(2) = 3`. -/
theorem constTerm_two : constTerm 2 = 3 := by
  rw [← constTermTable_eq le_rfl]
  decide +kernel

/-- The coefficient of `x` starts `1, -2, -1` (`a(2) = 3 - 2x`, `a(3) = 3 - x`). -/
example : xCoeff 1 = 1 ∧ xCoeff 2 = -2 ∧ xCoeff 3 = -1 := by
  have hI2 : Finset.Ioo 0 2 = {1} := by decide
  have hI3 : Finset.Ioo 0 3 = {1, 2} := by decide
  refine ⟨by simp [xCoeff, seq], ?_, ?_⟩
  · simp [xCoeff, seq_of_two_le, seq, hI2]
  · simp [xCoeff, seq_of_two_le, seq, hI2, hI3]

/-- `a(n)` is affine-linear in `x` over every commutative ring:
`a_x(n) = constTerm n + x * xCoeff n`. -/
theorem seq_eq_linear {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    seq x n = (constTerm n : R) + x * (xCoeff n : R) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [seq, constTerm, xCoeff]
    | 1, _ => simp [seq, constTerm, xCoeff]
    | m + 2, ih =>
      simp only [constTerm, xCoeff] at ih ⊢
      rw [seq_of_two_le x (by omega), seq_of_two_le (0 : ℤ) (by omega),
        seq_of_two_le (1 : ℤ) (by omega)]
      rw [Finset.sum_congr rfl fun i hi => by rw [ih i (Finset.mem_Ioo.1 hi).2]]
      simp only [Int.cast_sub, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
      simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, mul_sub,
        sub_mul, Finset.sum_sub_distrib]
      ring

/-- In `ℤ[X]` with `a(1) = X`: `a(n) = C (constTerm n) + C (xCoeff n) * X`
("which is linear in x"). -/
theorem seq_X_eq (n : ℕ) :
    seq (Polynomial.X : Polynomial ℤ) n =
      Polynomial.C (constTerm n) + Polynomial.C (xCoeff n) * Polynomial.X := by
  rw [seq_eq_linear, ← Polynomial.C_eq_intCast, ← Polynomial.C_eq_intCast, mul_comm, Int.cast_id,
    Int.cast_id]

/-! ## Möbius bookkeeping -/

/-- `∑_{d ∣ n} μ(d) = [n = 1]`. -/
theorem sum_divisors_moebius (n : ℕ) :
    ∑ d ∈ n.divisors, moebius d = if n = 1 then 1 else 0 := by
  rw [← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply]

/-- `∑_{d ∣ n} [2 ∣ d] μ(d/2) = [n = 2]` for `n ≠ 0`. -/
theorem sum_divisors_shift_moebius {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (if 2 ∣ d then moebius (d / 2) else 0) = if n = 2 then 1 else 0 := by
  rw [← Finset.sum_filter]
  by_cases h2 : 2 ∣ n
  · obtain ⟨m, rfl⟩ := h2
    have hm : m ≠ 0 := by omega
    have hbij : ∑ d ∈ (2 * m).divisors with 2 ∣ d, moebius (d / 2) =
        ∑ e ∈ m.divisors, moebius e := by
      refine Finset.sum_nbij' (· / 2) (2 * ·) ?_ ?_ ?_ ?_ ?_
      · intro d hd
        simp only [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
        obtain ⟨⟨hdn, -⟩, k, rfl⟩ := hd
        refine ⟨?_, hm⟩
        rw [Nat.mul_div_cancel_left k (by norm_num)]
        exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).1 hdn
      · intro e he
        simp only [Finset.mem_filter, Nat.mem_divisors] at he ⊢
        exact ⟨⟨Nat.mul_dvd_mul_left 2 he.1, by omega⟩, dvd_mul_right 2 e⟩
      · intro d hd
        simp only [Finset.mem_filter] at hd
        exact Nat.mul_div_cancel' hd.2
      · intro e _
        exact Nat.mul_div_cancel_left e (by norm_num)
      · intro d _
        rfl
    rw [hbij, sum_divisors_moebius]
    by_cases hm1 : m = 1
    · simp [hm1]
    · rw [if_neg hm1, if_neg (by omega)]
  · have hempty : (n.divisors.filter (2 ∣ ·)) = ∅ := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.notMem_empty, iff_false, not_and]
      intro hd h2d
      exact h2 (h2d.trans hd.1)
    rw [hempty, Finset.sum_empty, if_neg]
    rintro rfl
    exact h2 (dvd_refl 2)

/-! ## The floor-sum recursion as a divisor-sum identity -/

/-- For `n ≥ 2`: `∑_{i=1}^{n} c(i) floor(n/i) = binomial(n+1, 2)`. -/
theorem sum_Ioc_constTerm_mul_div {n : ℕ} (hn : 2 ≤ n) :
    ∑ i ∈ Finset.Ioc 0 n, constTerm i * ((n / i : ℕ) : ℤ) = ((n + 1).choose 2 : ℤ) := by
  rw [← Finset.Ioo_insert_right (by omega), Finset.sum_insert (by simp), Nat.div_self (by omega)]
  have hrec := seq_of_two_le (0 : ℤ) hn
  simp only [constTerm] at hrec ⊢
  rw [hrec]
  push_cast
  ring

/-- The floor sums `∑_{i=1}^{N} c(i) floor(N/i)` for every `N`. -/
theorem sum_Ioc_constTerm_mul_div_eq (N : ℕ) :
    ∑ i ∈ Finset.Ioc 0 N, constTerm i * ((N / i : ℕ) : ℤ) =
      if N ≤ 1 then 0 else ((N + 1).choose 2 : ℤ) := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · rw [if_pos (by omega)]
    interval_cases N
    · simp
    · simp [constTerm_one]
  · rw [if_neg (by omega), sum_Ioc_constTerm_mul_div hN]

/-- Swapping the floor sum: `∑_{m ≤ N} ∑_{d ∣ m} c(d) = ∑_{i ≤ N} c(i) floor(N/i)`. -/
theorem sum_Ioc_sum_divisors_constTerm (N : ℕ) :
    ∑ m ∈ Finset.Ioc 0 N, ∑ d ∈ m.divisors, constTerm d =
      ∑ i ∈ Finset.Ioc 0 N, constTerm i * ((N / i : ℕ) : ℤ) := by
  let F : ArithmeticFunction ℤ := ⟨constTerm, constTerm_zero⟩
  have hF : ∀ m, F m = constTerm m := fun _ => rfl
  have hsum := sum_Ioc_mul_zeta_eq_sum F N
  simp only [coe_mul_zeta_apply, hF] at hsum
  exact hsum

/-- For `n ≠ 0`: `∑_{d ∣ n} c(d) = n - [n = 1] + [n = 2]`. -/
theorem sum_divisors_constTerm {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, constTerm d =
      (n : ℤ) - (if n = 1 then 1 else 0) + (if n = 2 then 1 else 0) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hstep := Finset.sum_Ioc_succ_top (Nat.zero_le N)
    (fun m => ∑ d ∈ m.divisors, constTerm d)
  simp only [sum_Ioc_sum_divisors_constTerm, sum_Ioc_constTerm_mul_div_eq] at hstep
  rcases Nat.lt_or_ge N 2 with hN | hN
  · interval_cases N
    · simp only [zero_add, Std.le_refl, ↓reduceIte, zero_le, Nat.divisors_one,
        Finset.sum_singleton, Nat.cast_one, sub_self, OfNat.one_ne_ofNat, add_zero] at hstep ⊢
      linarith
    · simp only [Nat.reduceAdd, Nat.not_ofNat_le_one, ↓reduceIte, Nat.choose_succ_self_right,
        Nat.cast_ofNat, Std.le_refl, zero_add, OfNat.ofNat_ne_one, sub_zero, Int.reduceAdd] at hstep ⊢
      linarith
  · rw [if_neg (by omega), if_neg (by omega)] at hstep
    rw [if_neg (by omega), if_neg (by omega)]
    have hch : (N + 1 + 1).choose 2 = N + 1 + (N + 1).choose 2 := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
    rw [hch] at hstep
    push_cast at hstep ⊢
    linarith

/-- For `n ≠ 0`: `∑_{d ∣ n} (φ(d) - μ(d) + [2 ∣ d] μ(d/2)) = n - [n = 1] + [n = 2]`. -/
theorem sum_divisors_closedForm {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, closedForm d =
      (n : ℤ) - (if n = 1 then 1 else 0) + (if n = 2 then 1 else 0) := by
  simp only [closedForm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_divisors_moebius, sum_divisors_shift_moebius hn, ← Nat.cast_sum, Nat.sum_totient]

/-- Closed form of A092674: `c(n) = φ(n) - μ(n) + [2 ∣ n] μ(n/2)` (Möbius inversion). -/
theorem constTerm_eq_closedForm (n : ℕ) : constTerm n = closedForm n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [constTerm_zero, closedForm]
    · have hn : n ≠ 0 := hpos.ne'
      have hc := sum_divisors_constTerm hn
      have hg := sum_divisors_closedForm hn
      rw [← Nat.cons_self_properDivisors hn, Finset.sum_cons] at hc hg
      have hprop : ∑ d ∈ n.properDivisors, constTerm d =
          ∑ d ∈ n.properDivisors, closedForm d :=
        Finset.sum_congr rfl fun d hd => ih d (Nat.mem_properDivisors.1 hd).2
      linarith

/-- For `n ≥ 3`, `φ(n) - μ(n) + [2 ∣ n] μ(n/2) ≥ 0`, since `φ(n)` is even and positive. -/
theorem closedForm_nonneg_of_two_lt {n : ℕ} (hn : 2 < n) : 0 ≤ closedForm n := by
  have htot : 2 ≤ n.totient := by
    obtain ⟨k, hk⟩ := Nat.totient_even hn
    have hpos := Nat.totient_pos.2 (by omega : 0 < n)
    omega
  have hmu : moebius n ≤ 1 := (abs_le.1 abs_moebius_le_one).2
  have hshift : -1 ≤ (if 2 ∣ n then moebius (n / 2) else 0) := by
    split_ifs
    · exact (abs_le.1 abs_moebius_le_one).1
    · norm_num
  have htot' : (2 : ℤ) ≤ n.totient := by exact_mod_cast htot
  unfold closedForm
  linarith

/-- The constant term `c(n)` is nonnegative for every `n ≥ 1`. -/
theorem constTerm_nonneg {n : ℕ} (hn : 1 ≤ n) : 0 ≤ constTerm n := by
  rcases Nat.lt_or_ge 2 n with h | h
  · rw [constTerm_eq_closedForm]
    exact closedForm_nonneg_of_two_lt h
  · interval_cases n
    · rw [constTerm_one]
    · rw [constTerm_two]
      norm_num

/-! ## The conjecture -/

/-- **Perry's conjecture (A092674, Jon Perry, Mar 02 2004).**

Verbatim: "It is conjectured that a(n) is never less than 0 (tested to n=2000)",
where `a(n)` is the constant term of the polynomial `s[n] ∈ ℤ[x]` defined by
`s[1] = x`, `s[n] = binomial(n+1, 2) - ∑_{j=1}^{n-1} s[j] * floor(n/j)`.

Formalized: for every `n ≥ 1` (the entry's offset), the coefficient of `X^0` in
`seq X n ∈ ℤ[X]` is nonnegative. Proved via the closed form
`c(n) = φ(n) - μ(n) + [2 ∣ n] μ(n/2)`. -/
theorem conjecture {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ (seq (Polynomial.X : Polynomial ℤ) n).coeff 0 := by
  rw [coeff_zero_seq_X]
  exact constTerm_nonneg hn

end Candidates.A092674DefineSumFloor
