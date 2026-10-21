/-
# A399755 — Chai Wah Wu: `A399491(n) < 4n^3+3n` iff a small Pell solution exists

## OEIS source (retrieved with `oeis show A399755` / `oeis show A399491`, 2026-10-21)

```
A399755 NAME: Numbers k such that the generalized Pell equation
              x^2-(k^2+1)*(y^2+1) = 0 has more than one fundamental solution
              in (x, y).
TERMS:  7,38,41,117,239,268,515,682,882,1393,2072,2943,4030,4443,5357,...
COMMENT: The generalized Pell equation x^2-(k^2+1)*(y^2+1) = 0 has at least
         one solution (k^2+1, k).
COMMENT: If k is not a term of this sequence, then A399491(k) = 4*k^3+3*k.
COMMENT: Conjecture: A399491(k) < 4*k^3+3*k if and only if k is a term of
         this sequence.

A399491 NAME: The smallest integer m > n such that (n^2+1)*(m^2+1) is a
              perfect square.
TERMS:  7,38,117,268,515,882,41,2072,2943,4030,5357,6948,8827,11018,...
COMMENT: a(n) <= 4*n^3+3*n.
COMMENT: If the generalized Pell equation x^2-(n^2+1)*(y^2+1) = 0 has one
         fundamental solution in (x, y), then a(n) = 4*n^3+3*n.
         Conjecture: the converse of this statement is true.
         - _Chai Wah Wu_, Sep 10 2026
```

## Status (triage)

Open: no proof in the entry or the literature as far as the triage could
tell.  The entry gives the converse direction only as a comment.

## Formalization choice

"More than one fundamental solution" is Nagell's class-theoretic notion for
`x^2 - D*y^2 = D`, `D = n^2+1`.  With the unit `n + sqrt D` of norm `-1`,
the fundamental solutions are those with `|y| ≤ n` (Nagell bound
`y1*sqrt N / sqrt(2(x1+1)) = n`), and the main class is `(D, n)`.  So
"more than one fundamental solution" is "some `1 ≤ m0 < n` with
`D*(m0^2+1)` a square" (`y = 0` is impossible because `D` is not a square).
That identification is a remark and is *not* formalized here: the Lean
target is the self-contained equivalent recorded by the triage,

  `A399491(n) < 4n^3+3n  ↔  ∃ m0, 1 ≤ m0 < n, (n^2+1)*(m0^2+1) is a square`.

## Proof

`ε = n + sqrt D` has `ε^2 = (2n^2+1) + 2n sqrt D`, of norm `1`.
(⇐) from `x0^2 = D(m0^2+1)` take `m = (2n^2+1)m0 + 2n x0`; then
`n < m < 4n^3+3n` because `x0 < D`.
(⇒) from `x^2 = D(m^2+1)` with `n < m < 4n^3+3n` take
`y = (2n^2+1)m - 2n x`; the identities
`((2n^2+1)m ∓ n)^2 - (2nx)^2 = (m ± n)(m ∓ (4n^3+3n))`
give `-n < y < n`, and `y ≠ 0` since `D` is not a square.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A399755ChaiWahLeast

/-! ## Definition layer -/

/-- The conjectured threshold `4n^3+3n` of A399491. -/
def bound (n : ℕ) : ℕ := 4 * n ^ 3 + 3 * n

/-- `PellSq n m`: the number `(n^2+1)*(m^2+1)` is a perfect square, i.e. the
generalized Pell equation `x^2 - (n^2+1)*(y^2+1) = 0` has a solution with
`y = m`. -/
def PellSq (n m : ℕ) : Prop := IsSquare ((n ^ 2 + 1) * (m ^ 2 + 1))

instance (n : ℕ) : DecidablePred (PellSq n) := fun m =>
  Nat.instDecidablePredIsSquare ((n ^ 2 + 1) * (m ^ 2 + 1))

/-- The identity `(n^2+1)*((4n^3+3n)^2+1) = ((n^2+1)*(4n^2+1))^2`: the bound
`4n^3+3n` always gives a solution (the entry's comment `a(n) ≤ 4n^3+3n`). -/
theorem pellSq_bound (n : ℕ) : PellSq n (bound n) :=
  ⟨(n ^ 2 + 1) * (4 * n ^ 2 + 1), by unfold bound; ring⟩

/-- For `n ≥ 1`, `n < 4n^3+3n`. -/
theorem lt_bound {n : ℕ} (hn : 0 < n) : n < bound n := by
  unfold bound
  exact Nat.lt_of_lt_of_le (by omega) (Nat.le_add_left _ _)

/-- For `n ≥ 1` some `m > n` has `(n^2+1)*(m^2+1)` a square, namely
`m = 4n^3+3n`. -/
theorem exists_pellSq (n : ℕ) (hn : 0 < n) : ∃ m, n < m ∧ PellSq n m :=
  ⟨bound n, lt_bound hn, pellSq_bound n⟩

/-- **A399491**: for `n ≥ 1`, the smallest integer `m > n` such that
`(n^2+1)*(m^2+1)` is a perfect square. -/
def a399491 (n : ℕ) (hn : 0 < n) : ℕ := Nat.find (exists_pellSq n hn)

/-- Self-contained form of membership in A399755: some `1 ≤ m0 < n` has
`(n^2+1)*(m0^2+1)` a perfect square, i.e. the norm-`(n^2+1)` equation has a
solution besides the main class `(n^2+1, n)`. -/
def SmallSol (n : ℕ) : Prop := ∃ m, 1 ≤ m ∧ m < n ∧ PellSq n m

/-! ## Ground truth -/

/-- Bounded witness search for squares, used to check terms by `decide`. -/
theorem isSquare_iff_exists_lt {N B : ℕ} (hB : N < B * B) :
    IsSquare N ↔ ∃ r < B, r * r = N := by
  constructor
  · rintro ⟨r, rfl⟩
    refine ⟨r, ?_, rfl⟩
    by_contra hc
    exact absurd (Nat.mul_le_mul (not_lt.mp hc) (not_lt.mp hc)) (not_le.mpr hB)
  · rintro ⟨r, -, hr⟩
    exact ⟨r, hr.symm⟩

/-- `PellSq n m` with a uniform witness bound `B` valid for all `m < M`. -/
theorem pellSq_iff_bounded {n m B : ℕ} (hB : (n ^ 2 + 1) * (m ^ 2 + 1) < B * B) :
    PellSq n m ↔ ∃ r < B, r * r = (n ^ 2 + 1) * (m ^ 2 + 1) :=
  isSquare_iff_exists_lt hB

/-- Certificate form of `a399491 n = m`, with all square tests bounded by a
single witness bound `B`. -/
theorem a399491_eq_of_bounded {n : ℕ} (hn : 0 < n) {m B : ℕ}
    (hB : (n ^ 2 + 1) * (m ^ 2 + 1) < B * B) (hm : n < m)
    (hsq : ∃ r < B, r * r = (n ^ 2 + 1) * (m ^ 2 + 1))
    (hmin : ∀ k < m, n < k → ¬ ∃ r < B, r * r = (n ^ 2 + 1) * (k ^ 2 + 1)) :
    a399491 n hn = m := by
  rw [a399491, Nat.find_eq_iff]
  refine ⟨⟨hm, (pellSq_iff_bounded hB).mpr hsq⟩, ?_⟩
  rintro k hk ⟨hnk, hks⟩
  have hkB : (n ^ 2 + 1) * (k ^ 2 + 1) < B * B :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (by gcongr)) hB
  exact hmin k hk hnk ((pellSq_iff_bounded hkB).mp hks)

/-- For `m < n` the square root of `(n^2+1)*(m^2+1)` lies below `n^2+1`. -/
theorem pellSq_iff_bounded_of_lt {n m : ℕ} (hmn : m < n) :
    PellSq n m ↔ ∃ r < n ^ 2 + 1, r * r = (n ^ 2 + 1) * (m ^ 2 + 1) := by
  refine pellSq_iff_bounded (Nat.mul_lt_mul_of_pos_left ?_ (by positivity))
  have hsq : m ^ 2 < n ^ 2 := by gcongr
  omega

/-- Bounded form of `SmallSol`, decidable by `decide`. -/
theorem smallSol_iff_bounded (n : ℕ) :
    SmallSol n ↔ ∃ m < n, 1 ≤ m ∧ ∃ r < n ^ 2 + 1, r * r = (n ^ 2 + 1) * (m ^ 2 + 1) := by
  unfold SmallSol
  refine exists_congr fun m => ?_
  constructor
  · rintro ⟨h1, hmn, hsq⟩
    exact ⟨hmn, h1, (pellSq_iff_bounded_of_lt hmn).mp hsq⟩
  · rintro ⟨hmn, h1, hsq⟩
    exact ⟨h1, hmn, (pellSq_iff_bounded_of_lt hmn).mpr hsq⟩

/-- `A399491(1) = 7`. -/
example : a399491 1 Nat.one_pos = 7 :=
  a399491_eq_of_bounded _ (B := 11) (by norm_num) (by norm_num) ⟨10, by norm_num, by norm_num⟩
    (by decide)

/-- `A399491(2) = 38`. -/
example : a399491 2 two_pos = 38 :=
  a399491_eq_of_bounded _ (B := 86) (by norm_num) (by norm_num) ⟨85, by norm_num, by norm_num⟩
    (by decide +kernel)

/-- `A399491(7) = 41`, the first value below `4n^3+3n = 1393`. -/
example : a399491 7 (by norm_num) = 41 :=
  a399491_eq_of_bounded _ (B := 291) (by norm_num) (by norm_num) ⟨290, by norm_num, by norm_num⟩
    (by decide +kernel)

/-- `7` is the first term of A399755 (self-contained form). -/
example : SmallSol 7 := ⟨1, le_rfl, by norm_num, 10, by norm_num⟩

/-- No `n < 7` lies in A399755 (self-contained form). -/
example : ∀ n < 7, ¬ SmallSol n := by
  simp only [smallSol_iff_bounded]
  decide

/-! ## The descent and ascent steps -/

/-- **Descent by `ε^{-2}`.** If `x^2 = (n^2+1)(m^2+1)` with `x ≥ 0` and
`n < m < 4n^3+3n`, then `y = (2n^2+1)m - 2nx` satisfies `-n < y < n` and
`((2n^2+1)x - 2n(n^2+1)m)^2 = (n^2+1)(y^2+1)`.  The bounds come from the
identities `((2n^2+1)m ∓ n)^2 - (2nx)^2 = (m ± n)(m ∓ (4n^3+3n))`. -/
theorem descend (n m x : ℤ) (hn : 1 ≤ n) (hm : n < m) (hmB : m < 4 * n ^ 3 + 3 * n)
    (hx : 0 ≤ x) (hxe : x ^ 2 = (n ^ 2 + 1) * (m ^ 2 + 1)) :
    -n < (2 * n ^ 2 + 1) * m - 2 * n * x ∧ (2 * n ^ 2 + 1) * m - 2 * n * x < n ∧
    ((2 * n ^ 2 + 1) * x - 2 * n * (n ^ 2 + 1) * m) ^ 2 =
      (n ^ 2 + 1) * (((2 * n ^ 2 + 1) * m - 2 * n * x) ^ 2 + 1) := by
  have hid1 : ((2 * n ^ 2 + 1) * m - n) ^ 2 - (2 * n * x) ^ 2 =
      (m + n) * (m - (4 * n ^ 3 + 3 * n)) := by
    linear_combination (-4 * n ^ 2) * hxe
  have hid2 : ((2 * n ^ 2 + 1) * m + n) ^ 2 - (2 * n * x) ^ 2 =
      (m - n) * (m + (4 * n ^ 3 + 3 * n)) := by
    linear_combination (-4 * n ^ 2) * hxe
  have hneg : (m + n) * (m - (4 * n ^ 3 + 3 * n)) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) (by linarith)
  have hpos : 0 < (m - n) * (m + (4 * n ^ 3 + 3 * n)) :=
    mul_pos (by linarith) (by nlinarith)
  refine ⟨?_, ?_, ?_⟩
  · by_contra hc
    have hge : (2 * n ^ 2 + 1) * m + n ≤ 2 * n * x := by linarith
    have h0 : 0 ≤ (2 * n ^ 2 + 1) * m + n := by nlinarith
    have hsq := pow_le_pow_left₀ h0 hge 2
    linarith
  · by_contra hc
    have hge : 2 * n * x ≤ (2 * n ^ 2 + 1) * m - n := by linarith
    have h0 : 0 ≤ 2 * n * x := by positivity
    have hsq := pow_le_pow_left₀ h0 hge 2
    linarith
  · linear_combination hxe

/-- `n^2+1` is not a perfect square for `n ≥ 1` (it lies strictly between
`n^2` and `(n+1)^2`). -/
theorem not_sq_succ_sq (n t : ℕ) (hn : 1 ≤ n) : t ^ 2 ≠ n ^ 2 + 1 := by
  intro ht
  rcases le_or_gt t n with htn | htn
  · have hle : t ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left htn 2
    omega
  · have hle : (n + 1) ^ 2 ≤ t ^ 2 := Nat.pow_le_pow_left htn 2
    nlinarith

/-- (⇒) A solution `n < m < 4n^3+3n` descends to a small solution
`1 ≤ m0 < n`. -/
theorem smallSol_of_between {n m : ℕ} (hn : 0 < n) (hm : n < m) (hmB : m < bound n)
    (hsq : PellSq n m) : SmallSol n := by
  obtain ⟨x, hx⟩ := hsq
  unfold bound at hmB
  have hxe : (x : ℤ) ^ 2 = ((n : ℤ) ^ 2 + 1) * ((m : ℤ) ^ 2 + 1) := by
    rw [sq]; exact_mod_cast hx.symm
  obtain ⟨hlo, hhi, hX⟩ := descend n m x (by exact_mod_cast hn) (by exact_mod_cast hm)
    (by exact_mod_cast hmB) (by positivity) hxe
  set y : ℤ := (2 * (n : ℤ) ^ 2 + 1) * m - 2 * n * x with hy
  set X : ℤ := (2 * (n : ℤ) ^ 2 + 1) * x - 2 * n * ((n : ℤ) ^ 2 + 1) * m with hXdef
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0] at hX
    have hnat : X.natAbs ^ 2 = n ^ 2 + 1 := by
      have hc : ((X.natAbs ^ 2 : ℕ) : ℤ) = ((n ^ 2 + 1 : ℕ) : ℤ) := by
        push_cast
        rw [sq_abs, hX]
        ring
      exact_mod_cast hc
    exact not_sq_succ_sq n X.natAbs hn hnat
  refine ⟨y.natAbs, ?_, ?_, X.natAbs, ?_⟩
  · exact Int.natAbs_pos.mpr hy0
  · omega
  · have hc : (((n ^ 2 + 1) * (y.natAbs ^ 2 + 1) : ℕ) : ℤ) =
        ((X.natAbs * X.natAbs : ℕ) : ℤ) := by
      push_cast
      rw [sq_abs, abs_mul_abs_self, ← sq, hX]
    exact_mod_cast hc

/-- (⇐) **Ascent by `ε^2`.** A small solution `1 ≤ m0 < n` with
`x0^2 = (n^2+1)(m0^2+1)` gives the solution `m = (2n^2+1)m0 + 2n x0`, and
`n < m < 4n^3+3n` because `x0 < n^2+1`. -/
theorem exists_between_of_smallSol {n : ℕ} (h : SmallSol n) :
    ∃ m, n < m ∧ m < bound n ∧ PellSq n m := by
  obtain ⟨m0, h1, hm0, x0, hx0⟩ := h
  have hxD : x0 < n ^ 2 + 1 := by
    by_contra hc
    have hle : (n ^ 2 + 1) * (n ^ 2 + 1) ≤ x0 * x0 := Nat.mul_le_mul (not_lt.mp hc) (not_lt.mp hc)
    have hm2 : m0 ^ 2 + 1 < n ^ 2 + 1 := by
      have hsq : m0 ^ 2 < n ^ 2 := by gcongr
      omega
    have hlt : (n ^ 2 + 1) * (m0 ^ 2 + 1) < (n ^ 2 + 1) * (n ^ 2 + 1) :=
      Nat.mul_lt_mul_of_pos_left hm2 (by positivity)
    omega
  refine ⟨(2 * n ^ 2 + 1) * m0 + 2 * n * x0, ?_, ?_,
    (2 * n ^ 2 + 1) * x0 + 2 * n * (n ^ 2 + 1) * m0, ?_⟩
  · nlinarith
  · unfold bound
    have hm0' : m0 + 1 ≤ n := hm0
    have hx0' : x0 + 1 ≤ n ^ 2 + 1 := hxD
    nlinarith
  · have hc : (((n ^ 2 + 1) * (((2 * n ^ 2 + 1) * m0 + 2 * n * x0) ^ 2 + 1) : ℕ) : ℤ) =
        ((((2 * n ^ 2 + 1) * x0 + 2 * n * (n ^ 2 + 1) * m0) *
          ((2 * n ^ 2 + 1) * x0 + 2 * n * (n ^ 2 + 1) * m0) : ℕ) : ℤ) := by
      have hx0z : ((n : ℤ) ^ 2 + 1) * ((m0 : ℤ) ^ 2 + 1) = (x0 : ℤ) * x0 := by
        exact_mod_cast hx0
      push_cast
      linear_combination hx0z
    exact_mod_cast hc

/-- **Self-contained equivalence.** For `n ≥ 1`, some `m` with
`n < m < 4n^3+3n` has `(n^2+1)(m^2+1)` a square iff some `1 ≤ m0 < n` does. -/
theorem exists_between_iff_smallSol (n : ℕ) (hn : 0 < n) :
    (∃ m, n < m ∧ m < bound n ∧ PellSq n m) ↔ SmallSol n :=
  ⟨fun ⟨_, hm, hmB, hsq⟩ => smallSol_of_between hn hm hmB hsq, exists_between_of_smallSol⟩

/-! ## The conjecture -/

/-- Entry comment of A399491: `a(n) ≤ 4n^3+3n`. -/
theorem a399491_le_bound (n : ℕ) (hn : 0 < n) : a399491 n hn ≤ bound n :=
  Nat.find_min' (exists_pellSq n hn) ⟨lt_bound hn, pellSq_bound n⟩

/-- **Chai Wah Wu's conjecture (A399755 / A399491, Sep 10 2026), self-contained
form.** For every `n ≥ 1`, `A399491(n) < 4n^3+3n` iff some `1 ≤ m0 < n` makes
`(n^2+1)*(m0^2+1)` a perfect square (the self-contained form of
"`x^2 - (n^2+1)(y^2+1) = 0` has more than one fundamental solution", i.e. of
`n ∈ A399755`; the link to Nagell's fundamental solutions is not formalized). -/
theorem a399491_lt_bound_iff (n : ℕ) (hn : 0 < n) :
    a399491 n hn < bound n ↔ SmallSol n := by
  rw [← exists_between_iff_smallSol n hn]
  constructor
  · intro hlt
    obtain ⟨hgt, hsq⟩ := Nat.find_spec (exists_pellSq n hn)
    exact ⟨a399491 n hn, hgt, hlt, hsq⟩
  · rintro ⟨m, hm, hmB, hsq⟩
    exact lt_of_le_of_lt (Nat.find_min' (exists_pellSq n hn) ⟨hm, hsq⟩) hmB

/-- Entry comment direction, together with its converse: `A399491(n) = 4n^3+3n`
iff no `1 ≤ m0 < n` makes `(n^2+1)*(m0^2+1)` a perfect square. -/
theorem a399491_eq_bound_iff (n : ℕ) (hn : 0 < n) :
    a399491 n hn = bound n ↔ ¬ SmallSol n := by
  rw [← a399491_lt_bound_iff n hn]
  have hle := a399491_le_bound n hn
  omega

/-- Non-vacuity: the conjecture's left side holds at `n = 7`
(`A399491(7) = 41 < 1393`). -/
example : a399491 7 (by norm_num) < bound 7 :=
  (a399491_lt_bound_iff 7 (by norm_num)).mpr ⟨1, le_rfl, by norm_num, 10, by norm_num⟩

end Candidates.A399755ChaiWahLeast
