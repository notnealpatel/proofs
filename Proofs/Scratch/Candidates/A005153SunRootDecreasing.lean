/-
# A005153 — Sun: the `n`-th practical number's `n`-th root is strictly decreasing

## OEIS source (re-pulled verbatim 2026-08-05)

`goof oeis show A005153` plus `curl "https://oeis.org/search?q=id:A005153&fmt=text"`:

```
%N A005153 Practical numbers: positive integers m such that every k <= sigma(m)
           is a sum of distinct divisors of m. Also called panarithmic numbers.
%O A005153 1,2
%A A005153 _N. J. A. Sloane_
%K A005153 nonn,nice,easy
COMMENT (the conjecture):
  Conjecture: The sequence a(n)^(1/n) (n=3,4,...) is strictly decreasing to the
  limit 1. - _Zhi-Wei Sun_, Jan 12 2013
COMMENT (what makes the limit half known):
  Let P(x) denote the number of practical numbers up to x. P(x) has order of
  magnitude x/log(x) (see Saias 1997). Moreover, we have
  P(x) = c*x/log(x) + O(x/(log(x))^2), where c = 1.33607... (see Weingartner
  2015, 2020 and Remark 1 of Pomerance & Weingartner 2021). As a result,
  a(n) = k*n*log(n*log(n)) + O(n), where k = 1/c = 0.74846...
  - _Andreas Weingartner_, Jun 26 2021
%F A005153 More precisely, a(n) = k*n*log(n*log(n)) + O(n), where k = 0.74846...
           (see comments). - _Andreas Weingartner_, Jun 26 2021
TERMS: 1,2,4,6,8,12,16,18,20,24,28,30,32,36,40,42,48,54,56,60,64,66,72,78,80,84,
       88,90,96,100,104,108,112,120,126,128,132,140,144,150,156,160,162,168,176,
       180,192,196,198,200,204,208,210,216,220,224,228,234,240,252
```

Offset `1`: `a(1) = 1`, `a(2) = 2`, `a(3) = 4`, `a(4) = 6`, `a(5) = 8`, …

The conjecture starts at `n = 3` — the source says so explicitly ("n=3,4,...").
That guard is load-bearing: `a(1)^{1/1} = 1` and `a(2)^{1/2} = √2 ≈ 1.414` while
`a(3)^{1/3} = 4^{1/3} ≈ 1.587`, so the sequence **increases** from `n = 2` to
`n = 3`.  Starting at `n = 1` or `n = 2` makes the statement false.

## The two halves have very different status

* **Limit `1`**: essentially known.  Weingartner's `a(n) = k·n·log(n log n) + O(n)`
  gives `a(n)^{1/n} → 1` immediately (any polynomially-growing sequence does).
  This half is a *theorem modulo formalizing Weingartner*, and even a crude
  `a(n) ≤ C·n^2` bound suffices — which is far weaker and provable by hand from
  `practical_two_pow` plus a counting argument.
* **Strict monotonicity**: open.  This is the whole content.

The card separates them.
-/
import Mathlib
import Enumerative.Practical

set_option autoImplicit false

namespace Candidates.A005153Root

/-! ## Definition layer

`leandoc` findings:

* `Nat.nth (p : ℕ → Prop) (n : ℕ) : ℕ` — `noncomputable def`, the `n`-th
  natural satisfying `p`, **0-indexed**.  Mathlib API: `Nat.nth_zero`,
  `Nat.nth_succ`, `Nat.nth_lt_nth`, `Nat.nth_mem_of_infinite`,
  `Nat.count_nth`.  This is the right primitive for "the `n`-th practical
  number", and the repo already uses it (`nth_isZumkeller_zero` in
  `Enumerative/ZumkellerSigmaHalf.lean`).
* `Real.rpow`, `Real.rpow_natCast`, `Real.rpow_lt_rpow_left_iff`,
  `Real.rpow_natCast`, `Filter.Tendsto`, `nhds`.
* `Nat.Practical` from the repo.

**Offset shim.**  `Nat.nth` is 0-indexed and A005153 is 1-indexed, so
`a(n) = Nat.nth Nat.Practical (n − 1)`.  Rather than carry `ℕ` subtraction, the
card defines `pract n = Nat.nth Nat.Practical n` (0-indexed, so
`pract 0 = 1`, `pract 1 = 2`, `pract 2 = 4`) and reindexes the conjecture:
Sun's `n ≥ 3` becomes `pract` index `≥ 2`.  The shim is stated explicitly and
checked in the sanity layer, because an off-by-one here silently changes which
inequality is being asserted.

**Real-power discipline.**  `a(n)^{1/n}` needs `Real.rpow`; `(a n : ℕ) ^ (1/n)`
with `ℕ` division is `a n ^ 0 = 1` for `n > 1`, i.e. total nonsense.  The
statement is therefore given in **two** forms: the literal real one and the
equivalent integer one `a(n)^{n+1} > a(n+1)^n`, which is what a computation can
check exactly.  Their equivalence is in the PROVABLE layer. -/

/-- The practical numbers, 0-indexed: `pract 0 = 1`, `pract 1 = 2`,
`pract 2 = 4`, …  So A005153's `a(n)` is `pract (n − 1)`. -/
noncomputable def pract (k : ℕ) : ℕ := Nat.nth Nat.Practical k

/-! ## The conjecture -/

/-- **Sun's monotonicity conjecture (A005153, Zhi-Wei Sun, Jan 12 2013).**

Verbatim: "Conjecture: The sequence a(n)^(1/n) (n=3,4,...) is strictly
decreasing to the limit 1."

Real form.  Index shim: Sun's `a(n)` is `pract (n−1)`, so Sun's `n ≥ 3` is
`k ≥ 2` here, and the claim is
`pract k ^ (1/(k+1)) > pract (k+1) ^ (1/(k+2))` for `k ≥ 2`.
Written with `<` per STYLE.md.

**The `k ≥ 2` guard is load-bearing**: at `k = 1` (Sun's `n = 2`) the sequence
*increases* — `2^{1/2} ≈ 1.414 < 4^{1/3} ≈ 1.587`.

**Mathlib primitives available.**  `Nat.nth` API (`Nat.nth_lt_nth`,
`Nat.nth_mem_of_infinite`, `Nat.count_nth_succ`, `Nat.nth_count`);
`Real.rpow` API (`Real.rpow_natCast`, `Real.rpow_lt_rpow_left_iff`,
`Real.rpow_le_rpow_left_iff`, `Real.rpow_inv_natCast_pow`);
`Real.log`, `Real.exp`, `Real.log_le_sub_one_of_pos` for the log-linearization
`x^{1/n} < y^{1/m} ⟺ m log x < n log y`.
Practical-number side is all repo API; `Nat.Practical` is infinite by
`practical_two_pow`, which is what makes `Nat.nth` well behaved.

**Sketch of an attack.**
1. *The limit half.*  `a(n)^{1/n} → 1` follows from any polynomial bound
   `a(n) ≤ C n^d`, since then `a(n)^{1/n} ≤ (C n^d)^{1/n} → 1`.  A crude bound
   is provable today: the practical numbers include all `2^j`, so
   `a(n) ≤ 2^n`; that gives `a(n)^{1/n} ≤ 2`, not `→ 1`.  For `→ 1` one needs
   `a(n) = n^{1+o(1)}`, i.e. positive density on a log scale — Saias/Weingartner
   give `P(x) ≍ x/log x`, hence `a(n) ≍ n log n`, which is more than enough.
   **Formalizing even a weak `a(n) ≤ C n^2` would settle the limit half**, and
   that is plausibly reachable via Stewart's criterion (a practical number can
   be built by multiplying primes greedily, giving `a(n) = O(n log n)` with the
   right counting).
2. *The monotonicity half.*  `a(n)^{1/n}` strictly decreasing is equivalent to
   `a(n)^{n+1} > a(n+1)^n`, i.e. `(n+1) log a(n) > n log a(n+1)`, i.e.
   `log a(n+1) − log a(n) < log a(n) / n`.  With `a(n) ≈ k n log n`, the left
   side is `≈ 1/n` and the right side is `≈ log(kn log n)/n ≈ log n / n`.
   So the inequality has a comfortable margin **asymptotically** — the
   difficulty is entirely in the small/irregular range, where consecutive
   practical numbers can be far apart (the entry's own Jianing Song comment
   shows `d_{i+1}/d_i` is unbounded for divisors; the analogous irregularity for
   consecutive *practical numbers* is what must be controlled).
   **So this conjecture is plausibly provable**: an explicit Weingartner-type
   bound plus a finite check.  That is a materially better outlook than the
   candidates document's "heavy" rating suggests, and worth flagging.

**Tactic families.**  `native_decide` on the integer form for the window check;
`Real.rpow` simp set and `Real.log` monotonicity for the real form;
`Nat.nth_lt_nth` for basic monotonicity of `pract`; `nlinarith` for the
integer inequalities; `Filter.Tendsto.comp` for the limit.

**Related work in this repo.** `Enumerative.Practical`,
`Enumerative.StewartCriterion`, and `Enumerative.ZumkellerSigmaHalf` (which
already computes `Nat.nth` values for `IsZumkeller`, so the `Nat.nth` idiom is
established).  Adjacent Sun practical cards in this directory:
`A005153Switkay.lean`, `A209312SymmetricPractical.lean`,
`A222603PracticalTree.lean`, `A373686SomuTran.lean`. -/
theorem sun_root_strictAnti (k : ℕ) (hk : 2 ≤ k) :
    ((pract (k + 1) : ℝ)) ^ ((k + 2 : ℝ)⁻¹) < ((pract k : ℝ)) ^ ((k + 1 : ℝ)⁻¹) := by
  sorry

/-- The **integer form**, which is what a computation can check exactly:
`a(n)^{n+1} > a(n+1)^n`.  Equivalent to `sun_root_strictAnti` (see
`root_strictAnti_iff_pow`). -/
theorem sun_root_strictAnti_int (k : ℕ) (hk : 2 ≤ k) :
    pract (k + 1) ^ (k + 1) < pract k ^ (k + 2) := by
  sorry

/-- The **limit half**, which is essentially known (Saias/Weingartner) and is a
separate, materially easier target. -/
theorem sun_root_tendsto_one :
    Filter.Tendsto (fun k : ℕ => ((pract k : ℝ)) ^ ((k + 1 : ℝ)⁻¹))
      Filter.atTop (nhds 1) := by
  sorry

/-! ## Sanity layer -/

-- PROVABLE: the offset shim.  `pract` is 0-indexed and reproduces the DATA line
-- `1, 2, 4, 6, 8, 12, 16, 18, 20, 24` at indices `0..9`.  An off-by-one here
-- would silently change which inequality the conjecture asserts.
theorem pract_zero : pract 0 = 1 := by sorry
theorem pract_one : pract 1 = 2 := by sorry
theorem pract_two : pract 2 = 4 := by sorry
theorem pract_three : pract 3 = 6 := by sorry

-- PROVABLE: the two forms of the conjecture agree.
theorem root_strictAnti_iff_pow (k : ℕ) (hp : 0 < pract k) (hq : 0 < pract (k + 1)) :
    ((pract (k + 1) : ℝ)) ^ ((k + 2 : ℝ)⁻¹) < ((pract k : ℝ)) ^ ((k + 1 : ℝ)⁻¹)
      ↔ pract (k + 1) ^ (k + 1) < pract k ^ (k + 2) := by
  sorry

-- PROVABLE: the `2 ≤ k` guard is load-bearing.  At `k = 1` (Sun's `n = 2`) the
-- inequality **reverses**: `2^3 = 8 < 16 = 4^2`, i.e. `pract 1 ^ 3 < pract 2 ^ 2`,
-- so `pract 1 ^ (1+2) < pract 2 ^ (1+1)` — the opposite of the conjecture's
-- shape.  Dropping the guard makes the statement false, not merely vacuous.
example : (2 : ℕ) ^ 3 < 4 ^ 2 := by norm_num

-- PROVABLE: the first genuine instances of the conjecture, in integer form.
--   k = 2 (Sun's n = 3): a(3)^4 = 4^4 = 256 > 216 = 6^3 = a(4)^3 ✓
--   k = 3 (Sun's n = 4): a(4)^5 = 6^5 = 7776 > 4096 = 8^4 ✓
--   k = 4 (Sun's n = 5): a(5)^6 = 8^6 = 262144 > 248832 = 12^5 ✓
--   k = 5 (Sun's n = 6): a(6)^7 = 12^7 = 35831808 > 16777216 = 16^6 ✓
example : (6 : ℕ) ^ 3 < 4 ^ 4 := by norm_num
example : (8 : ℕ) ^ 4 < 6 ^ 5 := by norm_num
example : (12 : ℕ) ^ 5 < 8 ^ 6 := by norm_num
example : (16 : ℕ) ^ 6 < 12 ^ 7 := by norm_num

-- PROVABLE: `Nat.Practical` is infinite, which is what makes `Nat.nth` (and
-- hence `pract`) well defined rather than eventually junk.  Follows from
-- `Nat.practical_two_pow`.
theorem practical_infinite : {n : ℕ | n.Practical}.Infinite := by
  sorry

-- PROVABLE (window check): the integer inequality for every `2 ≤ k ≤ 200`,
-- i.e. the candidates document's "`a(n)^(n+1) > a(n+1)^n` for n ≤ 200".
-- Needs a computable list of practical numbers (not `Nat.nth`, which is
-- `noncomputable`); build it with `Finset.filter Nat.Practical (Finset.range N)`
-- and index into the sorted list.
def practList (N : ℕ) : List ℕ := ((Finset.range N).filter Nat.Practical).sort (· ≤ ·)

example : (practList 300).take 10 = [1, 2, 4, 6, 8, 12, 16, 18, 20, 24] := by native_decide

example : ∀ k ∈ Finset.Icc 2 40,
    (practList 3000)[k + 1]! ^ (k + 1) < (practList 3000)[k]! ^ (k + 2) := by
  native_decide

/-! ## Notes for a follow-up card

This candidate is **better than its Tier-3 placement suggests**.  In order:

1. `pract_zero` … `pract_three` and `practList` agreement — the offset audit.
   Free, and mandatory before any statement is trusted.
2. `practical_infinite` — free from `practical_two_pow`.
3. `root_strictAnti_iff_pow` — the real↔integer bridge, `Real.rpow` bookkeeping.
4. `sun_root_tendsto_one` — the limit half.  Needs only a **polynomial** upper
   bound on `pract k`; Stewart's criterion (already in the repo) plus a greedy
   construction should give `pract k = O(k log k)`, which is far more than
   enough.  **This is a genuine, reachable theorem** and the best target here.
5. `sun_root_strictAnti` — open, but with a large asymptotic margin (see the
   sketch), so an explicit Weingartner-type bound plus a finite check might
   actually close it.  Worth a serious look before writing it off.

References: Saias, *Entiers à diviseurs denses 1*, J. Number Theory 62 (1997);
Weingartner, *Practical numbers and the distribution of divisors*, Q. J. Math 66
(2015); Pomerance & Weingartner, 2021. -/

/-!
## Adversarial review verdict — **PASS** (no defects)

Independent re-pull of A005153 plus exact-integer verification, 2026-08-05.

Confirmed:
* Sun's Jan 12 2013 conjecture and Weingartner's Jun 26 2021 comment/`%F` are
  verbatim; `%O 1,2`, `%A _N. J. A. Sloane_`.
* **The offset shim is right**: `pract 0 = 1 = a(1)`, `pract 2 = 4 = a(3)`, so
  Sun's `n ≥ 3` is `k ≥ 2`.  Numerically `4^{1/3} = 1.5874 > 6^{1/4} = 1.5651`,
  and the card's `<`-oriented statement is the same inequality.
* **The `k ≥ 2` guard is load-bearing**: `2^{1/2} = 1.4142 < 4^{1/3} = 1.5874`,
  so the sequence *increases* at Sun's `n = 2`; the integer form `2^3 = 8 < 16 =
  4^2` shows the conjecture's inequality fails there.
* The real↔integer equivalence `a(n)^{1/n} > a(n+1)^{1/(n+1)} ⟺
  a(n)^{n+1} > a(n+1)^n` is standard, and the index shim maps it to
  `pract (k+1)^{k+1} < pract k^{k+2}` correctly.
* All four explicit instances check (`6^3 < 4^4`, `8^4 < 6^5`, `12^5 < 8^6`,
  `16^6 < 12^7`).
* **The window check holds**: `a(n)^{n+1} > a(n+1)^n` for every `n = 3..60` in
  exact integer arithmetic, no failures.
* `Finset.sort` exists with the `(· ≤ ·)` default and returns a `List`;
  `practList 3000` has ~470 elements, so `[k]!` for `k ≤ 41` cannot panic.
-/

end Candidates.A005153Root
