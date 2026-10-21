/-
# A262959 — refutation of Sun's residue conjecture (part (i))

## OEIS source (retrieved with `oeis show A262959` and checked against the
## live entry https://oeis.org/A262959, 2026-10-21)

```
NAME:     Positive integers that cannot be written as the sum of a fourth
          power, a square and a positive triangular number.
TERMS:    9,34,63,89,99,139,164,174,193,204,245,314,324,399,424,454,464,489,
          504,524,549,714,1049,1089,1149,1174,1439,1504,1539,1639,1714,1799,...
COMMENT:  Conjecture: (i) Each term is congruent to one of 3, 4, 5, 9 modulo 10.
COMMENT:  (ii) a(n+1) - a(n) > 4 for all n > 0.
COMMENT:  Part (ii) of this conjecture is stronger than the conjecture in
          A262956. Note that a(139) - a(138) = 18089 - 18084 = 5.
AUTHOR:   Zhi-Wei Sun, Oct 05 2015
```

The conjecture comments carry no separate signature; they are by the entry's
author, Zhi-Wei Sun (Oct 05 2015).  No later comment in the live entry
retracts or qualifies part (i) (checked 2026-10-21).

## Status of this module

This module **refutes** the conjecture: part (i) fails at `n = 9052`
(`9052 ≡ 2 (mod 10)`), the 99th term of the sequence.  A second
counterexample is `11808 ≡ 8 (mod 10)` (the 117th term).  The original
program in the entry searched only `m ≤ 5000`, which explains why the
pattern looked exceptionless.  A bounded computation (Python, all
`n ≤ 30000`) finds exactly these two exceptions to part (i) and minimum gap
`5` between consecutive terms, so part (ii) survives that range; part (ii)
is not addressed here.

`Elab.async false` keeps the kernel checks sequential; under a virtual-memory
cap the default asynchronous elaboration fails to create its worker threads.
-/
import Mathlib

set_option autoImplicit false
set_option Elab.async false

namespace Candidates.A262959Refutation

/-! ## Definitions -/

/-- `n` is the sum of a fourth power, a square and a *positive* triangular
number: `n = x^4 + y^2 + z(z+1)/2` with `x, y ≥ 0` and `z ≥ 1`.  The division
is exact because `z * (z + 1)` is even. -/
def Representable (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < z ∧ n = x ^ 4 + y ^ 2 + z * (z + 1) / 2

/-- Membership in A262959: `n` is positive and not `Representable`. -/
def InS (n : ℕ) : Prop :=
  0 < n ∧ ¬ Representable n

/-- **Sun's conjecture (A262959, Zhi-Wei Sun, Oct 05 2015).**

(i) "Each term is congruent to one of 3, 4, 5, 9 modulo 10."
(ii) "a(n+1) - a(n) > 4 for all n > 0": whenever `m < n` are consecutive
elements of the sequence (no element strictly between them), `m + 4 < n`. -/
def Conjecture : Prop :=
  (∀ n : ℕ, InS n → n % 10 ∈ ({3, 4, 5, 9} : Finset ℕ)) ∧
  (∀ m n : ℕ, InS m → InS n → m < n → (∀ k : ℕ, m < k → k < n → ¬ InS k) → m + 4 < n)

/-! ## A Boolean decision procedure with explicit bounds -/

/-- The residual `n - x^4 - z(z+1)/2` left for the square term.  It is only
used under the guard `x^4 + z(z+1)/2 ≤ n`, so the truncated subtraction never
reaches its junk value where it matters. -/
def residual (n x z : ℕ) : ℕ :=
  n - x ^ 4 - z * (z + 1) / 2

/-- Boolean search for a representation of `n` with `x < a` and `0 < z < c`:
for each such pair it tests whether the residual is a perfect square using
`Nat.sqrt`. -/
def repB (n a c : ℕ) : Bool :=
  Nat.any a fun x _ => Nat.any c fun z _ =>
    decide (0 < z) && decide (x ^ 4 + z * (z + 1) / 2 ≤ n) &&
      Nat.sqrt (residual n x z) ^ 2 == residual n x z

/-- `Nat.any n f` is true exactly when some `i < n` satisfies `f`. -/
theorem nat_any_eq_true_iff {n : ℕ} (f : (i : ℕ) → i < n → Bool) :
    Nat.any n f = true ↔ ∃ i, ∃ h : i < n, f i h = true := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.any_succ, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨i, hi, hf⟩ | hf)
      · exact ⟨i, by omega, hf⟩
      · exact ⟨n, by omega, hf⟩
    · rintro ⟨i, hi, hf⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · exact Or.inl ⟨i, hlt, hf⟩
      · exact Or.inr hf

/-- `repB` decides `Representable n` once the bounds exceed `n`:
`n < a^4` and `n < c(c+1)/2`. -/
theorem representable_iff_repB {n a c : ℕ} (ha : n < a ^ 4) (hc : n < c * (c + 1) / 2) :
    Representable n ↔ repB n a c = true := by
  simp only [repB, nat_any_eq_true_iff, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨x, y, z, hz, hn⟩
    have hx : x < a := by
      by_contra hxa
      have hpow : a ^ 4 ≤ x ^ 4 := Nat.pow_le_pow_left (Nat.le_of_not_lt hxa) 4
      omega
    have hz' : z < c := by
      by_contra hzc
      have hcz : c ≤ z := Nat.le_of_not_lt hzc
      have htri : c * (c + 1) / 2 ≤ z * (z + 1) / 2 :=
        Nat.div_le_div_right (Nat.mul_le_mul hcz (Nat.add_le_add_right hcz 1))
      omega
    have hres : residual n x z = y ^ 2 := by
      unfold residual
      omega
    refine ⟨x, hx, z, hz', ⟨⟨hz, by omega⟩, ?_⟩⟩
    rw [hres, Nat.sqrt_eq']
  · rintro ⟨x, _, z, _, ⟨hz, hle⟩, hsq⟩
    refine ⟨x, Nat.sqrt (residual n x z), z, hz, ?_⟩
    rw [hsq]
    unfold residual
    omega

/-! ## Ground truth: the listed terms below `250` -/

/-- The elements of A262959 below `250` are exactly
`9, 34, 63, 89, 99, 139, 164, 174, 193, 204, 245`, matching the first eleven
listed terms. -/
theorem inS_iff_of_lt_250 {n : ℕ} (hn : n < 250) :
    InS n ↔ n ∈ ([9, 34, 63, 89, 99, 139, 164, 174, 193, 204, 245] : List ℕ) := by
  have hcheck : ∀ m < 250, ((decide (0 < m) && !repB m 4 22) =
      decide (m ∈ ([9, 34, 63, 89, 99, 139, 164, 174, 193, 204, 245] : List ℕ))) := by
    decide +kernel
  have hm := hcheck n hn
  rw [InS, representable_iff_repB (a := 4) (c := 22) (by omega) (by omega),
    Bool.not_eq_true, ← decide_eq_true_iff (p := n ∈ _), ← hm]
  cases repB n 4 22 <;> simp

example : InS 9 := (inS_iff_of_lt_250 (by norm_num)).mpr (by simp)
example : ¬ InS 8 := fun h => by simpa using (inS_iff_of_lt_250 (by norm_num)).mp h
example : Representable 1 := ⟨0, 0, 1, by norm_num, by norm_num⟩

/-! ## The counterexample `9052` -/

/-- `9052` has no representation: for every `x < 10` and `0 < z < 135` with
`x^4 + z(z+1)/2 ≤ 9052`, the residual `9052 - x^4 - z(z+1)/2` is not a perfect
square.  Checked by kernel evaluation (`decide +kernel`, not `native_decide`). -/
theorem repB_9052 : repB 9052 10 135 = false := by
  decide +kernel

/-- `9052` belongs to A262959 (it is the 99th term). -/
theorem inS_9052 : InS 9052 := by
  refine ⟨by norm_num, ?_⟩
  rw [representable_iff_repB (a := 10) (c := 135) (by norm_num) (by norm_num), repB_9052]
  exact Bool.false_ne_true

/-- `11808` belongs to A262959 (it is the 117th term), a second
counterexample to part (i). -/
theorem inS_11808 : InS 11808 := by
  refine ⟨by norm_num, ?_⟩
  have hrep : repB 11808 11 154 = false := by decide +kernel
  rw [representable_iff_repB (a := 11) (c := 154) (by norm_num) (by norm_num), hrep]
  exact Bool.false_ne_true

/-- **Refutation of Sun's conjecture on A262959.**  Part (i) fails: `9052`
is in the sequence (it is not a fourth power plus a square plus a positive
triangular number) but `9052 ≡ 2 (mod 10)`.  Sun's original search stopped at
`5000`; the statement he probably intended is the empirical residue pattern of
the terms in that range, which first breaks at `9052` (and again at
`11808 ≡ 8 (mod 10)`, see `inS_11808`). -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  have hmem := hconj.1 9052 inS_9052
  norm_num at hmem

/-- Part (i) of the conjecture fails at a second residue class as well:
`11808 ≡ 8 (mod 10)` is in the sequence. -/
theorem part_i_fails_at_11808 :
    InS 11808 ∧ 11808 % 10 ∉ ({3, 4, 5, 9} : Finset ℕ) :=
  ⟨inS_11808, by decide⟩

end Candidates.A262959Refutation
