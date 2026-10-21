/-
# A227781 — the level of `ZMod n`: Greathouse's conjecture

## OEIS source (re-pulled verbatim from `https://oeis.org/search?q=id:A227781&fmt=text`, 2026-10-21)

```
%N A227781 Least number of squares which add to -1 mod n.
%S A227781 0,1,2,3,1,2,2,4,2,1,2,3,1,2,2,4,1,2,2,3,2,2,2,4,1,1,2,3,1,2,2,4,2,1,
%C A227781 Pfister proved that a(p) <= 2 for all primes p; then a(p) is called the
          stufe of the field Z/pZ.
%C A227781 Conjecture: a(n) = 4 if and only if n is divisible by 8 and a(n) = 3 if
          and only if n is 4 mod 8. Together with A008784 this would completely
          define the sequence.
%F A227781 a(n) <= A002828(n-1) <= 4.
%F A227781 a(n) = 1 if and only if n > 1 is in A008784. a(4n) >= 3 for all n.
%O A227781 1,3
%A A227781 _Charles R Greathouse IV_, Jul 31 2013
```

The conjecture line carries no separate signature; it belongs to the entry's
author, Charles R Greathouse IV (entry dated Jul 31 2013, last edited
May 15 2017).

## Status

Triage status: "unclear".  The triage found no printed proof (the
levels-of-rings survey in Banach Center Publ. 108 and arXiv:2608.22435 were
consulted); the statement is very likely folklore.  Brute force over
`n = 1..3000` (triage) and `n = 3001..3400` (this session) found no exception.

## Proof outline (all proved below)

* Upper bound 4 for every `n ≥ 1`: Lagrange's four-square theorem on `n - 1`.
* Upper bound 2 when `4 ∤ n`, and 3 when `n ≡ 4 (mod 8)`: for odd `m`, Dirichlet
  gives a prime `p ≡ 2m - 1 (mod 4m)`; then `p ≡ 1 (mod 4)` is a sum of two
  squares `x² + y²`, so `x² + y² = 2m - 1` in `ZMod (4m)`.  Push to `ZMod m`
  (`n = m` odd) or `ZMod (2m)` (`n = 2m`) to get `-1`; for `n = 4m` use
  `1 + (x + y)² + (x - y)² = 1 + 2(2m - 1) = -1`.
* Lower bounds: push forward to `ZMod 8` (resp. `ZMod 4`) and decide that `7`
  (resp. `3`) is not a sum of three (resp. two) squares there.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A227781LeastSumSquares

/-! ## Definition layer -/

/-- The set of `k : ℕ` such that `-1` is a sum of `k` squares in `ZMod n`. -/
def sqSumSet (n : ℕ) : Set ℕ :=
  {k | ∃ f : Fin k → ZMod n, ∑ i, f i ^ 2 = -1}

/-- OEIS A227781: the least number of squares which add to `-1` modulo `n`,
i.e. the least `k ≥ 0` such that `-1` is a sum of `k` squares in `ZMod n`
(the level of `ZMod n`).  For `n ≥ 1` the set is nonempty (Lagrange), so the
`sInf` is a genuine minimum; at `n = 0` (`ZMod 0 = ℤ`) the set is empty and the
value is the junk `0`, which is why the theorems below assume `0 < n` where it
matters. -/
noncomputable def A227781 (n : ℕ) : ℕ :=
  sInf (sqSumSet n)

/-! ## Basic structure of `sqSumSet` -/

/-- Padding with a zero square: a representation with `k` squares gives one
with `k + 1` squares. -/
theorem succ_mem_sqSumSet {n k : ℕ} (h : k ∈ sqSumSet n) : k + 1 ∈ sqSumSet n := by
  obtain ⟨f, hf⟩ := h
  refine ⟨Fin.cons 0 f, ?_⟩
  rw [Fin.sum_univ_succ]
  simpa using hf

/-- `sqSumSet n` is upward closed. -/
theorem sqSumSet_upward_closed (n : ℕ) :
    ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ sqSumSet n → k₂ ∈ sqSumSet n := by
  intro k₁ k₂ hle hk₁
  induction k₂, hle using Nat.le_induction with
  | base => exact hk₁
  | succ k _ ih => exact succ_mem_sqSumSet ih

/-- `A227781 n = k + 1` exactly when `k + 1` squares suffice and `k` do not. -/
theorem A227781_eq_succ_iff (n k : ℕ) :
    A227781 n = k + 1 ↔ k + 1 ∈ sqSumSet n ∧ k ∉ sqSumSet n :=
  Nat.sInf_upward_closed_eq_succ_iff (sqSumSet_upward_closed n) k

/-- If `-1` is a sum of `k` squares in `ZMod n`, then `A227781 n ≤ k`. -/
theorem A227781_le_of_mem {n k : ℕ} (h : k ∈ sqSumSet n) : A227781 n ≤ k :=
  Nat.sInf_le h

/-! ## Upper bounds -/

/-- Lagrange: for `n ≥ 1`, `-1 = n - 1` is a sum of four squares in `ZMod n`. -/
theorem four_mem_sqSumSet {n : ℕ} (hn : 0 < n) : 4 ∈ sqSumSet n := by
  obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares (n - 1)
  refine ⟨![a, b, c, d], ?_⟩
  have hcast : ((n - 1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one, zero_sub]
  rw [Fin.sum_univ_four, ← hcast, ← habcd]
  push_cast
  rfl

/-- **Load-bearing step (Dirichlet + Fermat).** For odd `m`, `2m - 1` is a sum
of two squares in `ZMod (4m)`: pick a prime `p ≡ 2m - 1 (mod 4m)`; then
`p ≡ 1 (mod 4)`, so `p = x² + y²`. -/
theorem exists_sq_add_sq_eq (m : ℕ) (hm : Odd m) :
    ∃ x y : ZMod (4 * m), x ^ 2 + y ^ 2 = 2 * (m : ZMod (4 * m)) - 1 := by
  have hq : 4 * m ≠ 0 := by have := hm.pos; omega
  have hcop : IsCoprime (2 * (m : ℤ) - 1) ((4 * m : ℕ) : ℤ) :=
    ⟨2 * m - 1, 1 - m, by push_cast; ring⟩
  obtain ⟨p, -, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_zmodEq 0 hq hcop
  have h4 : (p : ℤ) ≡ 2 * m - 1 [ZMOD 4] :=
    Int.ModEq.of_mul_right (m : ℤ) (by simpa using hpa)
  have hp4 : p % 4 ≠ 3 := by
    obtain ⟨k, hk⟩ := hm
    unfold Int.ModEq at h4
    omega
  haveI := Fact.mk hp
  obtain ⟨x, y, hxy⟩ := Nat.Prime.sq_add_sq hp4
  refine ⟨x, y, ?_⟩
  have hcast : ((p : ℤ) : ZMod (4 * m)) = ((2 * m - 1 : ℤ) : ZMod (4 * m)) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).2 hpa
  push_cast at hcast
  rw [← hcast, ← hxy]
  push_cast
  ring

/-- Two squares in `ZMod n` summing to `-1` give a witness that `2 ∈ sqSumSet n`. -/
theorem two_mem_sqSumSet_of {n : ℕ} {x y : ZMod n} (h : x ^ 2 + y ^ 2 = -1) :
    2 ∈ sqSumSet n :=
  ⟨![x, y], by rw [Fin.sum_univ_two]; exact h⟩

/-- For odd `n`, `-1` is a sum of two squares in `ZMod n`. -/
theorem two_mem_sqSumSet_of_odd {n : ℕ} (hn : Odd n) : 2 ∈ sqSumSet n := by
  obtain ⟨x, y, hxy⟩ := exists_sq_add_sq_eq n hn
  let φ : ZMod (4 * n) →+* ZMod n := ZMod.castHom (Dvd.intro_left 4 rfl) (ZMod n)
  refine two_mem_sqSumSet_of (x := φ x) (y := φ y) ?_
  rw [← map_pow, ← map_pow, ← map_add, hxy]
  simp

/-- For `n = 2m` with `m` odd, `-1` is a sum of two squares in `ZMod n`. -/
theorem two_mem_sqSumSet_of_two_mul_odd {m : ℕ} (hm : Odd m) :
    2 ∈ sqSumSet (2 * m) := by
  obtain ⟨x, y, hxy⟩ := exists_sq_add_sq_eq m hm
  have hdvd : 2 * m ∣ 4 * m := ⟨2, by ring⟩
  let φ : ZMod (4 * m) →+* ZMod (2 * m) := ZMod.castHom hdvd (ZMod (2 * m))
  refine two_mem_sqSumSet_of (x := φ x) (y := φ y) ?_
  rw [← map_pow, ← map_pow, ← map_add, hxy]
  have h2m : ((2 * m : ℕ) : ZMod (2 * m)) = 0 := ZMod.natCast_self _
  push_cast at h2m
  rw [map_sub, map_mul, map_natCast, map_ofNat, map_one, h2m, zero_sub]

/-- For `n = 4m` with `m` odd, `-1 = 1² + (x + y)² + (x - y)²` in `ZMod n`. -/
theorem three_mem_sqSumSet_of_four_mul_odd {m : ℕ} (hm : Odd m) :
    3 ∈ sqSumSet (4 * m) := by
  obtain ⟨x, y, hxy⟩ := exists_sq_add_sq_eq m hm
  refine ⟨![1, x + y, x - y], ?_⟩
  have h4m : ((4 * m : ℕ) : ZMod (4 * m)) = 0 := ZMod.natCast_self _
  push_cast at h4m
  rw [Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  linear_combination 2 * hxy + h4m

/-- If `4 ∤ n`, then `-1` is a sum of two squares in `ZMod n`. -/
theorem two_mem_sqSumSet {n : ℕ} (h4 : ¬ 4 ∣ n) : 2 ∈ sqSumSet n := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | hn
  · have hmo : Odd m := by
      rcases Nat.even_or_odd m with ⟨k, hk⟩ | hmo
      · exact absurd ⟨k, by omega⟩ h4
      · exact hmo
    have hn : n = 2 * m := by omega
    subst hn
    exact two_mem_sqSumSet_of_two_mul_odd hmo
  · exact two_mem_sqSumSet_of_odd hn

/-- If `n ≡ 4 (mod 8)`, then `-1` is a sum of three squares in `ZMod n`. -/
theorem three_mem_sqSumSet {n : ℕ} (h : n % 8 = 4) : 3 ∈ sqSumSet n := by
  have hmo : Odd (n / 4) := ⟨n / 8, by omega⟩
  have hn : n = 4 * (n / 4) := by omega
  rw [hn]
  exact three_mem_sqSumSet_of_four_mul_odd hmo

/-! ## Lower bounds -/

/-- In `ZMod 8`, `-1` is not a sum of three squares (squares lie in `{0, 1, 4}`). -/
theorem zmod8_sq_add_sq_add_sq_ne (x y z : ZMod 8) : x ^ 2 + y ^ 2 + z ^ 2 ≠ -1 := by
  revert x y z
  decide

/-- In `ZMod 4`, `-1` is not a sum of two squares (squares lie in `{0, 1}`). -/
theorem zmod4_sq_add_sq_ne (x y : ZMod 4) : x ^ 2 + y ^ 2 ≠ -1 := by
  revert x y
  decide

/-- If `8 ∣ n`, then `-1` is not a sum of three squares in `ZMod n`. -/
theorem three_not_mem_sqSumSet {n : ℕ} (h8 : 8 ∣ n) : 3 ∉ sqSumSet n := by
  rintro ⟨f, hf⟩
  let φ : ZMod n →+* ZMod 8 := ZMod.castHom h8 (ZMod 8)
  have hφ := congrArg φ hf
  rw [Fin.sum_univ_three] at hφ
  simp only [map_add, map_pow, map_neg, map_one] at hφ
  exact zmod8_sq_add_sq_add_sq_ne _ _ _ hφ

/-- If `4 ∣ n`, then `-1` is not a sum of two squares in `ZMod n`. -/
theorem two_not_mem_sqSumSet {n : ℕ} (h4 : 4 ∣ n) : 2 ∉ sqSumSet n := by
  rintro ⟨f, hf⟩
  let φ : ZMod n →+* ZMod 4 := ZMod.castHom h4 (ZMod 4)
  have hφ := congrArg φ hf
  rw [Fin.sum_univ_two] at hφ
  simp only [map_add, map_pow, map_neg, map_one] at hφ
  exact zmod4_sq_add_sq_ne _ _ hφ

/-! ## The junk value at `n = 0` -/

/-- In `ZMod 0 = ℤ`, `-1` is never a sum of squares. -/
theorem sqSumSet_zero : sqSumSet 0 = ∅ := by
  ext k
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨f, hf⟩
  let g : Fin k → ℤ := f
  have hnn : (0 : ℤ) ≤ ∑ i, g i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (g i))
  have hg : ∑ i, g i ^ 2 = -1 := hf
  omega

/-- The junk value `A227781 0 = 0` (outside the entry's offset). -/
theorem A227781_zero : A227781 0 = 0 := by
  rw [A227781, sqSumSet_zero, Nat.sInf_empty]

/-! ## The conjecture -/

/-- **Implicit bound in Greathouse's conjecture (A227781).** If `4 ∤ n`, then
`-1` is a sum of at most two squares modulo `n`: `A227781 n ≤ 2`.  (No `0 < n`
guard is needed: `4 ∣ 0`.) -/
theorem A227781_le_two {n : ℕ} (h4 : ¬ 4 ∣ n) : A227781 n ≤ 2 :=
  A227781_le_of_mem (two_mem_sqSumSet h4)

/-- **Greathouse's conjecture, part 1 (A227781, Charles R Greathouse IV,
Jul 31 2013).** Verbatim: "a(n) = 4 if and only if n is divisible by 8".
For every `n ≥ 1`, the least number of squares adding to `-1` modulo `n` is `4`
iff `8 ∣ n`.  The guard `0 < n` is the entry's offset and is load-bearing: at
`n = 0` the junk value `A227781 0 = 0` while `8 ∣ 0`. -/
theorem A227781_eq_four_iff {n : ℕ} (hn : 0 < n) : A227781 n = 4 ↔ 8 ∣ n := by
  constructor
  · intro h
    by_contra h8
    by_cases h4 : 4 ∣ n
    · have hmod : n % 8 = 4 := by omega
      have hle := A227781_le_of_mem (three_mem_sqSumSet hmod)
      omega
    · have hle := A227781_le_two h4
      omega
  · intro h8
    exact (A227781_eq_succ_iff n 3).2 ⟨four_mem_sqSumSet hn, three_not_mem_sqSumSet h8⟩

/-- **Greathouse's conjecture, part 2 (A227781, Charles R Greathouse IV,
Jul 31 2013).** Verbatim: "a(n) = 3 if and only if n is 4 mod 8".
The least number of squares adding to `-1` modulo `n` is `3` iff
`n ≡ 4 (mod 8)`.  This holds for every `n : ℕ`, including the junk case
`n = 0` (both sides false), so no `0 < n` guard is needed. -/
theorem A227781_eq_three_iff {n : ℕ} : A227781 n = 3 ↔ n % 8 = 4 := by
  constructor
  · intro h
    by_cases h4 : 4 ∣ n
    · by_contra hmod
      have h8 : 8 ∣ n := by omega
      have hn : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0
          rw [A227781_zero] at h
          omega
        · exact hpos
      have h4eq := (A227781_eq_four_iff hn).2 h8
      omega
    · have hle := A227781_le_two h4
      omega
  · intro hmod
    exact (A227781_eq_succ_iff n 2).2
      ⟨three_mem_sqSumSet hmod, two_not_mem_sqSumSet (by omega)⟩

/-! ## Ground truth against the listed terms `0, 1, 2, 3, 1, 2, 2, 4, …` -/

/-- `A227781 1 = 0`: in `ZMod 1`, `-1 = 0` is the empty sum. -/
example : A227781 1 = 0 :=
  Nat.sInf_eq_zero.2 (Or.inl ⟨Fin.elim0, Subsingleton.elim _ _⟩)

/-- `A227781 2 = 1`: `1² = -1` in `ZMod 2`. -/
example : A227781 2 = 1 :=
  (A227781_eq_succ_iff 2 0).2
    ⟨⟨![1], by decide⟩, by
      rintro ⟨f, hf⟩
      rw [Finset.univ_eq_empty, Finset.sum_empty] at hf
      exact absurd hf (by decide)⟩

/-- `A227781 3 = 2`: `1² + 1² = -1` in `ZMod 3`, and `-1` is not a square. -/
example : A227781 3 = 2 :=
  (A227781_eq_succ_iff 3 1).2
    ⟨⟨![1, 1], by decide⟩, by
      rintro ⟨f, hf⟩
      rw [Fin.sum_univ_one] at hf
      revert hf
      generalize f 0 = x
      revert x
      decide⟩

/-- `A227781 4 = 3`, `A227781 8 = 4`, `A227781 7 ≤ 2`, `A227781 12 = 3`,
`A227781 16 = 4` from the theorems above. -/
example : A227781 4 = 3 ∧ A227781 8 = 4 ∧ A227781 7 ≤ 2 ∧ A227781 12 = 3 ∧
    A227781 16 = 4 :=
  ⟨A227781_eq_three_iff.2 (by decide), (A227781_eq_four_iff (by decide)).2 (by decide),
    A227781_le_two (by decide), A227781_eq_three_iff.2 (by decide),
    (A227781_eq_four_iff (by decide)).2 (by decide)⟩

end Candidates.A227781LeastSumSquares
