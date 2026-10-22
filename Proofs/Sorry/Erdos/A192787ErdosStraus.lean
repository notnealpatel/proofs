/- WARNING: the strict denominator predicate is distinct from the non-strict
Erdős–Straus conjecture. Strict-predicate results must not be presented as
a resolution of Erdős–Straus; existing load-bearing admissions remain. -/
/-
# A192787 / A073101 — the Erdős–Straus conjecture (4/n = 1/x + 1/y + 1/z)

## OEIS source (re-pulled verbatim 2026-08-05)

`goof oeis show A073101`:
```
NAME:     Number of integer solutions (x,y,z) to 4/n = 1/x + 1/y + 1/z
          satisfying 0 < x < y < z.
TERMS:    0,0,1,1,2,5,5,6,4,9,7,15,4,14,33,22,4,21,9,30,25,22,19,45,10,17,25,36,
          7,72,17,62,27,22,59,69,9,29,67,84,7,77,12,56,87,39,32,142,16,48,46,53,
          13,82,92,124,37,30,25,178,11,34,147,118,49,94,15,67,51,176,38,191,7
KEYWORDS: nonn
COMMENTS:
  In 1948 Erdős and Straus conjectured that for any positive integer n >= 2 the
  equation 4/n = 1/x + 1/y + 1/z has a solution with positive integers x, y and
  z (without the additional requirement 0 < x < y < z). All of the solutions can
  be printed by removing the comment symbols from the Mathematica program. For
  the solution (x,y,z) having the largest z value, see (A075245, A075246,
  A075247). See A075248 for Sierpiński's conjecture for 5/n.
  See (A257839, A257840, A257841) for the lexicographically smallest solutions,
  and A257843 for the differences between these and those with largest z-value.
  - _M. F. Hasler_, May 16 2015
```

`goof oeis show A192787`:
```
NAME:     Number of distinct solutions of 4/n = 1/a + 1/b + 1/c in positive
          integers satisfying 1 <= a <= b <= c.
TERMS:    0,1,3,3,2,8,7,10,6,12,9,21,4,17,39,28,4,26,11,36,29,25,21,57,10,20,29,
          42,7,81,19,70,31,25,65,79,9,32,73,96,7,86,14,62,93,42,34,160,18,53,52,
          59,13,89,98,136,41,33,27,196,11,37,155,128,49,103,17,73,55,185,40,211,
          7,32,129,80,97,160,37,292
KEYWORDS: nonn
COMMENTS:
  The Erdős-Straus conjecture is that a(n) > 0 for n > 1. Swett verified the
  conjecture for n < 10^14.
  Vaughan shows that the number of n < x with a(n) = 0 is at most
  x exp(-c * (log x)^(2/3)) for some c > 0.
  See A073101 for the 4/n conjecture due to Erdős and Straus.
```

**Indexing note the two entries disagree on.**  A073101 counts solutions with
`0 < x < y < z` (*strict*, so `n = 2` has `a(2) = 0` even though `4/2 = 2` does
decompose as `1/1 + 1/2 + 1/2`), while A192787 counts `1 ≤ a ≤ b ≤ c`
(*non-strict*, so `a(2) = 1`).  The **conjecture** — as spelled out in the
A073101 comment, "without the additional requirement `0 < x < y < z`" — is the
non-strict one.  This card states the non-strict form; the strict form is
recorded separately and is *false* at `n = 2`, which is exactly why the source
is careful.  Getting this backwards would be a silent statement error, so the
distinction is carried in the theorem names.

## Status

Open, famous.  Erdős and Straus 1948.  The verification bound in the dated OEIS
quotation above is historical source text, not a claim about current status.
Vaughan's density bound is quoted above.

## Repo adjacency

Organizationally fits the Erdős arc (`Proofs/Erdos`); no definition reuse.  The
cleared-denominator form uses only `ℕ` arithmetic — no subtraction, no division,
so STYLE.md-clean by construction.
-/
import Sorry.Erdos.ErdosStrausResidues

set_option autoImplicit false

namespace Candidates.A192787

/-! ## Definition layer

`leandoc` findings: nothing sequence-specific exists.  What is used:

* `Nat.Prime`, `Nat.Coprime`, `Nat.gcd` — for the standard reduction to prime
  `n` (`erdosStraus_of_prime` below).
* `ℚ` with `Rat.num`, `Rat.den`, `div_add_div`, `field_simp` — for the literal
  rational form.
* `ZMod` and `Nat.ModEq` — for the residue-class case analysis that is the whole
  known theory here.

Two encodings are given.  `HasEgyptian4 n` is the **literal** conjecture over
`ℚ`; `HasEgyptian4Cleared n` is the cleared-denominator `ℕ` form.  Their
proved equivalence for positive `n` is in the PROVABLE layer.  Both predicates
are false at `n = 0`: positive cleared witnesses give `0 < 4xyz`, whereas the
right-hand side is zero; in the rational form `4/0 = 0` cannot equal a sum of
three positive reciprocals.  Thus zero does not create a representation drift.
The conjecture carries the guard `2 ≤ n` explicitly. -/

/-- The literal Erdős–Straus predicate over `ℚ`: `4/n = 1/x + 1/y + 1/z` with
`x, y, z` positive integers.  Division is guarded by the positivity hypotheses
plus the `2 ≤ n` guard at the use sites, per STYLE.md. -/
abbrev HasEgyptian4 := ErdosStraus.HasEgyptian4

/-- Cleared-denominator form: `4 x y z = n (y z + x z + x y)`.  No division, no
subtraction — decidable once the search range is bounded. -/
abbrev HasEgyptian4Cleared := ErdosStraus.HasEgyptian4Cleared

/-- The A073101 (strict) predicate, recorded only to keep the two OEIS indexings
distinguishable.  **This is not the conjecture** — see the header note. -/
abbrev HasEgyptian4Strict := ErdosStraus.HasEgyptian4Strict

/-! ## The conjecture -/

/-- **The Erdős–Straus conjecture (A073101 / A192787, Erdős and Straus 1948).**

Verbatim (A073101): "In 1948 Erdős and Straus conjectured that for any positive
integer n >= 2 the equation 4/n = 1/x + 1/y + 1/z has a solution with positive
integers x, y and z (without the additional requirement 0 < x < y < z)."

Verbatim (A192787): "The Erdős-Straus conjecture is that a(n) > 0 for n > 1.
Swett verified the conjecture for n < 10^14."

**Mathlib primitives available.** `ZMod`, `Nat.ModEq`, `Nat.chineseRemainder`,
`Nat.Prime`, `Nat.exists_prime_and_dvd`, `Nat.minFac`;
`Nat.sq_mul_squarefree` and quadratic-residue API (`legendreSym`,
`ZMod.euler_criterion`, `ZMod.exists_sq_eq_neg_one_iff`) for the `n ≡ 1 (mod 24)`
residue analysis; `field_simp`, `div_add_div`, `one_div` for the ℚ ↔ ℕ bridge.

**Sketch of the known theory** (this is real and largely formalizable, unlike
the conjecture itself):
1. *Scaling.*  If `HasEgyptian4 n`, `n ∣ m`, and `0 < m`, then
   `HasEgyptian4 m` (scale each of `x, y, z` by the positive multiplier `m / n`;
   solvability forces `0 < n`).  A zero multiplier or zero target is invalid.
   Hence it suffices to prove the conjecture for **primes** —
   `erdosStraus_of_prime` below, proved in the production foundation.
2. *Residue classes.*  Explicit identities settle some residue classes.  Each
   identity below has a concrete numerical check; the general identity table
   is proved in the imported production residue module.
   * `n = 4k + 3`:  `4/n = 1/(k+1) + 1/(n(k+1))` — a **two**-term identity,
     since `4/n − 1/(k+1) = (4(k+1) − n)/(n(k+1)) = 1/(n(k+1))`.  Split the last
     term by `1/m = 1/(m+1) + 1/(m(m+1))` to reach three:
     `x = k+1`, `y = n(k+1) + 1`, `z = n(k+1)(n(k+1) + 1)`.
     Check `n = 7` (`k = 1`): `(2, 15, 210)`, and `1/2 + 1/15 + 1/210 = 4/7`. ✓
   * `n + 1 = 3m`, with `1 ≤ m`:  `x = m`, `y = n`, `z = n m`, since
     `1/m + 1/n + 1/(nm) = (n + m + 1)/(nm) = 4m/(nm) = 4/n`.
     Check `n = 5` (`m = 2`): `(2, 5, 10)`, and `1/2 + 1/5 + 1/10 = 4/5`. ✓
   * `n = 2m`, with `1 ≤ m`: `4/n = 2/m = 1/m + 1/(m+1) + 1/(m(m+1))`.
     Check `n = 6` (`m = 3`): `(3, 4, 12)`, and `1/3 + 1/4 + 1/12 = 2/3 = 4/6`. ✓
   These branches alone do not reduce the prime cases to `p ≡ 1 (mod 24)`:
   the `p ≡ 13 (mod 24)` case needs a separate `p ≡ 5 (mod 8)` identity branch.
   The conclusion of `erdosStraus_residual` is the residual reduction; its only
   premise is solvability for primes `p ≡ 1 (mod 24)`.  Its proof is supplied by
   the production residue module; the reduction itself is not assumed as a premise.

**Tactic families.** `ring`/`field_simp` to verify each identity in the case table;
`omega` for the residue bookkeeping; `Nat.ModEq` and `interval_cases` on
`n % 24` for the case split; `decide` on `ZMod 24` for the residue enumeration.

**Related work in this repo.**  None directly; organizationally this belongs
with `Proofs/Erdos/`.  Adjacent card in this directory:
`A000041SunAntichain.lean` (another additive-representation archive card). -/
theorem erdosStraus (n : ℕ) (hn : 2 ≤ n) : HasEgyptian4 n := by
  sorry

/-- The prime reduction: it suffices to prove the conjecture for primes.
**Provable today** (scale a solution for `p` up by `n / p`), and the single most
useful lemma here. -/
theorem erdosStraus_of_prime
    (h : ∀ p : ℕ, p.Prime → 2 ≤ p → HasEgyptian4Cleared p) :
    ∀ n : ℕ, 2 ≤ n → HasEgyptian4Cleared n := by
  exact ErdosStraus.erdosStraus_of_prime h

/-- The residual reduction: solvability for primes `p ≡ 1 (mod 24)` implies
solvability for every `n ≥ 2`.  The only premise is that prime-case solvability;
the reduction is the conclusion, proved in the production residue module.  The
listed identities include a separate `p ≡ 5 (mod 8)` branch covering `13 (mod 24)`. -/
theorem erdosStraus_residual
    (h : ∀ p : ℕ, p.Prime → p % 24 = 1 → HasEgyptian4Cleared p) :
    ∀ n : ℕ, 2 ≤ n → HasEgyptian4Cleared n := by
  exact ErdosStraus.erdosStraus_residual h

/-! ## Sanity layer -/

-- PROVABLE: the two encodings agree for `n ≥ 1`.  This is the translation audit.
theorem hasEgyptian4_iff_cleared (n : ℕ) (hn : 1 ≤ n) :
    HasEgyptian4 n ↔ HasEgyptian4Cleared n := by
  exact ErdosStraus.hasEgyptian4_iff_cleared n hn

-- PROVABLE: the guard `2 ≤ n` is load-bearing.  At `n = 1` the equation
-- `4 = 1/x + 1/y + 1/z` has no positive-integer solution (the max of the RHS is
-- `3` at `x = y = z = 1`), so `HasEgyptian4 1` is false.
example : ¬ HasEgyptian4Cleared 1 := by
  rintro ⟨x, y, z, hx, hy, hz, h⟩
  have hx1 : 1 ≤ x := hx
  have hy1 : 1 ≤ y := hy
  have hz1 : 1 ≤ z := hz
  have hyz : y * z ≤ x * y * z := by
    calc
      y * z = 1 * (y * z) := by ring
      _ ≤ x * (y * z) := Nat.mul_le_mul_right _ hx1
      _ = x * y * z := by ring
  have hxz : x * z ≤ x * y * z := by
    calc
      x * z = 1 * (x * z) := by ring
      _ ≤ y * (x * z) := Nat.mul_le_mul_right _ hy1
      _ = x * y * z := by ring
  have hxy : x * y ≤ x * y * z := by
    calc
      x * y = 1 * (x * y) := by ring
      _ ≤ z * (x * y) := Nat.mul_le_mul_right _ hz1
      _ = x * y * z := by ring
  have hpos : 0 < x * y * z := Nat.mul_pos (Nat.mul_pos hx hy) hz
  nlinarith only [h, hyz, hxz, hxy, hpos]

-- PROVABLE: satisfiability at `n = 2`:  `4/2 = 1/1 + 1/2 + 1/2`.
--   cleared: `4 * 1 * 2 * 2 = 16 = 2 * (2*2 + 1*2 + 1*2) = 2 * 8`.
example : HasEgyptian4Cleared 2 := ⟨1, 2, 2, by norm_num, by norm_num, by norm_num, by norm_num⟩

-- PROVABLE: `n = 3`:  `4/3 = 1/1 + 1/4 + 1/12`.
--   cleared: `4 * 1 * 4 * 12 = 192 = 3 * (48 + 12 + 4) = 3 * 64`.
example : HasEgyptian4Cleared 3 := ⟨1, 4, 12, by norm_num, by norm_num, by norm_num, by norm_num⟩

-- PROVABLE: `n = 5`:  `4/5 = 1/2 + 1/4 + 1/20`.
--   cleared: `4 * 2 * 4 * 20 = 640 = 5 * (80 + 40 + 8) = 5 * 128`.
example : HasEgyptian4Cleared 5 := ⟨2, 4, 20, by norm_num, by norm_num, by norm_num, by norm_num⟩

-- PROVABLE: A073101's strict count really is `0` at `n = 2` while A192787's
-- non-strict count is `1` — i.e. the two OEIS indexings genuinely differ, and
-- the conjecture is about the non-strict one.
example : ¬ HasEgyptian4Strict 2 := by
  rintro ⟨x, y, z, hx, hxy, hyz, h⟩
  have hx1 : 1 ≤ x := hx
  have hy2 : 2 ≤ y := by omega
  have hz3 : 3 ≤ z := by omega
  have hy : 0 < y := by omega
  have hz : 0 < z := by omega
  have hyz_bound : y * z ≤ x * y * z := by
    calc
      y * z = 1 * (y * z) := by ring
      _ ≤ x * (y * z) := Nat.mul_le_mul_right _ hx1
      _ = x * y * z := by ring
  have hxz_bound : 2 * (x * z) ≤ x * y * z := by
    calc
      2 * (x * z) ≤ y * (x * z) := Nat.mul_le_mul_right _ hy2
      _ = x * y * z := by ring
  have hxy_bound : 3 * (x * y) ≤ x * y * z := by
    calc
      3 * (x * y) ≤ z * (x * y) := Nat.mul_le_mul_right _ hz3
      _ = x * y * z := by ring
  have hpos : 0 < x * y * z := Nat.mul_pos (Nat.mul_pos hx hy) hz
  nlinarith only [h, hyz_bound, hxz_bound, hxy_bound, hpos]

/-- The search bound: `4/n = 1/x + 1/y + 1/z ≤ 3/x` forces `4x ≤ 3n`. -/
theorem erdosStraus_bound_x {n x y z : ℕ} (hx : 0 < x) (hxy : x ≤ y) (hyz : y ≤ z)
    (h : 4 * x * y * z = n * (y * z + x * z + x * y)) : 4 * x ≤ 3 * n := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hz : 0 < z := lt_of_lt_of_le hy hyz
  have hxz : x ≤ z := le_trans hxy hyz
  have hterm_z : x * z ≤ y * z := Nat.mul_le_mul_right z hxy
  have hterm_y : x * y ≤ y * z := by
    calc
      x * y ≤ z * y := Nat.mul_le_mul_right y hxz
      _ = y * z := Nat.mul_comm z y
  have hsum : y * z + x * z + x * y ≤ 3 * (y * z) := by
    calc
      y * z + x * z + x * y ≤ y * z + y * z + y * z :=
        Nat.add_le_add (Nat.add_le_add_left hterm_z (y * z)) hterm_y
      _ = 3 * (y * z) := by ring
  have hmul : (4 * x) * (y * z) ≤ (3 * n) * (y * z) := by
    calc
      (4 * x) * (y * z) = 4 * x * y * z := by ring
      _ = n * (y * z + x * z + x * y) := h
      _ ≤ n * (3 * (y * z)) := Nat.mul_le_mul_left n hsum
      _ = (3 * n) * (y * z) := by ring
  exact Nat.le_of_mul_le_mul_right hmul (Nat.mul_pos hy hz)

/-! ## Notes for a follow-up card

The prime reduction is proved in the imported production foundation.  The
production residue module proves the complementary residue classes with positive
explicit denominators and cleared equations, including the `p ≡ 5 (mod 8)` branch
covering `13 (mod 24)`.  The archive residual wrapper therefore derives its
conclusion from the unchanged prime-case premise.  That premise itself remains open.

Reference: Elsholtz & Tao, *Counting the number of solutions to the Erdős–Straus
equation on unit fractions*, J. Aust. Math. Soc. 94 (2013) 50–105. -/

end Candidates.A192787
