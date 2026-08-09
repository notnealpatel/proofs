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

Open, famous.  Erdős and Straus 1948.  Verified for `n < 10^14` (Swett).
Vaughan's density bound is quoted above.

## Repo adjacency

Organizationally fits the Erdős arc (`Proofs/Erdos`); no definition reuse.  The
cleared-denominator form uses only `ℕ` arithmetic — no subtraction, no division,
so STYLE.md-clean by construction.
-/
import Mathlib

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
equivalence is in the PROVABLE layer.  Stating only the cleared form would be a
definitional-drift risk (the `n = 0` case of the cleared equation is solvable by
`x = y = z` arbitrary, which the rational form forbids), so both are kept and
the guard `2 ≤ n` is carried explicitly. -/

/-- The literal Erdős–Straus predicate over `ℚ`: `4/n = 1/x + 1/y + 1/z` with
`x, y, z` positive integers.  Division is guarded by the positivity hypotheses
plus the `2 ≤ n` guard at the use sites, per STYLE.md. -/
def HasEgyptian4 (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

/-- Cleared-denominator form: `4 x y z = n (y z + x z + x y)`.  No division, no
subtraction — decidable once the search range is bounded. -/
def HasEgyptian4Cleared (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    4 * x * y * z = n * (y * z + x * z + x * y)

/-- The A073101 (strict) predicate, recorded only to keep the two OEIS indexings
distinguishable.  **This is not the conjecture** — see the header note. -/
def HasEgyptian4Strict (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ x < y ∧ y < z ∧
    4 * x * y * z = n * (y * z + x * z + x * y)

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
1. *Multiplicativity.*  If `HasEgyptian4 n` and `n ∣ m` then `HasEgyptian4 m`
   (scale each of `x, y, z` by `m / n`).  Hence it suffices to prove the
   conjecture for **primes** — `erdosStraus_of_prime` below.  This reduction is
   provable today and is the single most valuable lemma in the file.
2. *Residue classes.*  Explicit identities settle many residue classes.  Each
   identity below has been checked numerically at the indicated prime (an
   earlier draft of this file carried a *wrong* `p ≡ 3 (mod 4)` identity that
   summed to `3/p`; it was caught by the adversarial reviewer, which is why each
   line now records its check).
   * `n = 4k + 3`:  `4/n = 1/(k+1) + 1/(n(k+1))` — a **two**-term identity,
     since `4/n − 1/(k+1) = (4(k+1) − n)/(n(k+1)) = 1/(n(k+1))`.  Split the last
     term by `1/m = 1/(m+1) + 1/(m(m+1))` to reach three:
     `x = k+1`, `y = n(k+1) + 1`, `z = n(k+1)(n(k+1) + 1)`.
     Check `n = 7` (`k = 1`): `(2, 15, 210)`, and `1/2 + 1/15 + 1/210 = 4/7`. ✓
   * `n = 3m − 1`:  `x = m`, `y = n`, `z = n m`, since
     `1/m + 1/n + 1/(nm) = (n + m + 1)/(nm) = 4(n+1)/(n(n+1)) = 4/n`.
     Check `n = 5` (`m = 2`): `(2, 5, 10)`, and `1/2 + 1/5 + 1/10 = 4/5`. ✓
   * `n = 2m` even: `4/n = 2/m = 1/m + 1/(m+1) + 1/(m(m+1))`.
     Check `n = 6` (`m = 3`): `(3, 4, 12)`, and `1/3 + 1/4 + 1/12 = 2/3 = 4/6`. ✓
   Formalizing the case table is bounded, mechanical work and would be a genuine
   contribution.  Mordell's refinement narrows the residual set to
   `n ≡ 1, 11², 13², 17², 19², 23² (mod 840)`; the `p ≡ 1 (mod 24)` phrasing used
   in `erdosStraus_residual` below is the coarser standard reduction and is
   implied by it.  **Neither reduction is asserted here** — `erdosStraus_residual`
   takes the reduction as a hypothesis, so nothing unproved is smuggled in.
3. *What is actually open.*  No residue class of the form `p ≡ r (mod M)` with
   `r` a quadratic residue mod `M` has ever been settled by an identity, and
   Elsholtz–Tao showed the number of solutions is `n^{o(1)}` on average, which
   is consistent with but does not imply positivity.

**Tactic families.**  `decide`/`native_decide` for the bounded sweep (the bound
`x ≤ ⌈3n/4⌉` comes from `4/n ≤ 3/x`, see `erdosStraus_bound_x`);
`ring`/`field_simp` to verify each identity in the case table;
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
  sorry

/-- The residual open case after the classical identities: `p ≡ 1 (mod 24)`.
Recorded separately because a card that formalizes the identity table would
reduce `erdosStraus` to exactly this. -/
theorem erdosStraus_residual
    (h : ∀ p : ℕ, p.Prime → p % 24 = 1 → HasEgyptian4Cleared p) :
    ∀ n : ℕ, 2 ≤ n → HasEgyptian4Cleared n := by
  sorry

/-! ## Sanity layer -/

-- PROVABLE: the two encodings agree for `n ≥ 1`.  This is the translation audit.
theorem hasEgyptian4_iff_cleared (n : ℕ) (hn : 1 ≤ n) :
    HasEgyptian4 n ↔ HasEgyptian4Cleared n := by
  sorry

-- PROVABLE: the guard `2 ≤ n` is load-bearing.  At `n = 1` the equation
-- `4 = 1/x + 1/y + 1/z` has no positive-integer solution (the max of the RHS is
-- `3` at `x = y = z = 1`), so `HasEgyptian4 1` is false.
example : ¬ HasEgyptian4Cleared 1 := by
  rintro ⟨x, y, z, hx, hy, hz, h⟩
  -- 4xyz = yz + xz + xy ≤ 3xyz for positive x,y,z
  nlinarith [Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff.mp hx).ne',
             Nat.mul_le_mul_right (y * z) hx]

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
  -- x ≥ 1, y ≥ 2, z ≥ 3 forces 1/x + 1/y + 1/z < 2 = 4/2
  sorry  -- PROVABLE, but needs the bound argument spelled out; not open content

-- PROVABLE: the search bound.  `4/n = 1/x + 1/y + 1/z ≤ 3/x` forces `4x ≤ 3n`,
-- so the sweep may quantify `x` over `Finset.range (3 * n / 4 + 1)`.  Stated as
-- a lemma so the bounded sweep below is not smuggling in an assumption.
theorem erdosStraus_bound_x {n x y z : ℕ} (hx : 0 < x) (hxy : x ≤ y) (hyz : y ≤ z)
    (h : 4 * x * y * z = n * (y * z + x * z + x * y)) : 4 * x ≤ 3 * n := by
  sorry

-- PROVABLE (window check): a solution exists for every `2 ≤ n ≤ 200`.
-- The bounds `x ≤ n`, `y ≤ 2*n*n`, `z ≤ 4*n*n*n` are generous but finite; tune
-- downward with `erdosStraus_bound_x` before running.
example : ∀ n ∈ Finset.Icc 2 200,
    ∃ x ∈ Finset.Icc 1 n, ∃ y ∈ Finset.Icc 1 (2 * n * n), ∃ z ∈ Finset.Icc 1 (4 * n * n * n),
      4 * x * y * z = n * (y * z + x * z + x * y) := by
  native_decide

/-! ## Notes for a follow-up card

Two separable deliverables, both genuine formalization content:

1. `erdosStraus_of_prime` — the multiplicative reduction.  Provable today,
   ~30 lines, and it is the reduction every paper on the subject opens with.
2. The **identity table**: for each residue class `r ∈ {2, 3 (mod 4)}`,
   `{2 (mod 3)}`, `{3 (mod 4)}`, … an explicit `(x, y, z)` as a function of `n`,
   each verified by `ring` after clearing.  Landing the table proves
   `erdosStraus_residual`'s hypothesis suffices, i.e. reduces the famous
   conjecture to `p ≡ 1 (mod 24)`.  That is a publishable-shaped Lean artifact
   and does not require settling anything.

Reference: Elsholtz & Tao, *Counting the number of solutions to the Erdős–Straus
equation on unit fractions*, J. Aust. Math. Soc. 94 (2013) 50–105. -/

/-!
## Adversarial review verdict — **FLAG, one substantive defect, now FIXED**

Independent re-pull of A073101 and A192787 by a source-fidelity reviewer,
2026-08-05.

**Defect (substantive).**  The docstring's `p ≡ 3 (mod 4)` identity
`x = p, y = (p+1)/2, z = p(p+1)/2` sums to `3/p`, not `4/p` — checked at `p = 7`,
where it gives `1/7 + 1/4 + 1/28 = 3/7`.  **FIXED**: replaced with the correct
two-term identity `4/n = 1/(k+1) + 1/(n(k+1))` for `n = 4k+3`, split to three
terms, and every identity in the table now carries its own numeric check.

Everything else confirmed:
* Both `%O` lines are `1`; A073101 `a(2) = 0` (strict) vs A192787 `a(2) = 1`
  (non-strict), so the strict/non-strict distinction the card draws is real and
  the conjecture is the non-strict one.
* The cleared form `4xyz = n(yz + xz + xy)` is the correct clearing.
* All three numeric witnesses `(2;1,2,2)`, `(3;1,4,12)`, `(5;2,4,20)` check out.
* `HasEgyptian4Cleared 0` **is** satisfiable (so the cleared and rational forms
  genuinely differ at `n = 0`, as the card says), and `HasEgyptian4Cleared 1` is
  false by exhaustive search and by the `≤ 3xyz < 4xyz` bound.
* `erdosStraus_bound_x` (`4x ≤ 3n`) derives correctly from `x ≤ y ≤ z`.
* The `p ≡ 2 (mod 3)` identity is correct (verified at `p = 5`).
* `ZMod.euler_criterion`, `legendreSym`, `Nat.chineseRemainder`,
  `Nat.sq_mul_squarefree`, `ZMod.exists_sq_eq_neg_one_iff` all exist.
-/

end Candidates.A192787
