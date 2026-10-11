/-
# A209312 — Sun: symmetric prime/practical offsets

## OEIS source (re-pulled verbatim 2026-08-05)

`goof oeis show A209312` plus `curl "https://oeis.org/search?q=id:A209312&fmt=text"`:

```
%N A209312 Number of practical numbers p<n with n-p and n+p both prime or both
           practical.
%O A209312 1,4
%A A209312 _Zhi-Wei Sun_, Jan 19 2013
%K A209312 nonn
COMMENTS:
  Conjecture: a(n)>0 for all n>2.
  This has been verified for n up to 10^7.
  Except for p=1, all practical numbers are even. Thus, (n-p,n+p) prime is
  possible only if n is odd, and (n-p,n+p) can be practical only if n is even
  (except for p=1). - _M. F. Hasler_, Jan 19 2013
XREFS:
  Cf. A005153, A208243, A208244, A208246, A208249, A209253, A209254.
  Cf. A209321: Indices for which a(n)=2.
TERMS: 0,0,1,2,2,2,2,1,2,3,2,4,1,2,3,3,3,4,2,4,3,4,3,6,3,2,3,4,4,6,3,5,3,4,5,8,3,
       2,5,5,4,7,4,7,4,2,4,11,3,1,4,7,4,7,6,7,3,4,5,12,3,2,4,8,7,8,5,9,4,2,6,14,
       5,2,6,7,7,9,5,9,4,4,5,14,8,2,5,8,7,10,6,9,6,2,8,15,5,3,5,8
```

**Attribution confirmed.**  The candidates document says "uncredited in the
pull; style strongly suggests Zhi-Wei Sun — verify before carding".  The `%A`
line settles it: **Zhi-Wei Sun, Jan 19 2013**.  (`goof oeis show` strips `%A`,
which is why the earlier sweep could not see it.)

Offset `1`.  `a(1) = a(2) = 0`, hence the `n > 2` guard.

DATA spot-checks:
* `a(3) = 1`: practical `p < 3` are `1, 2`.  `p = 1`: `(2, 4)` — not both prime
  (`4`), but both practical ✓.  `p = 2`: `(1, 5)` — `1` is not prime, `5` is not
  practical ✗.  Total `1`. ✓
* `a(4) = 2`: `p = 1`: `(3, 5)` both prime ✓.  `p = 2`: `(2, 6)` both practical ✓.
  Total `2`. ✓

## Status

Open.  Verified to `10^7`.

## Priority note

The candidates document rates this "Lower priority than Switkay's cleaner
statement in Tier 1", and that is right: the "both prime **or** both practical"
disjunction plus Hasler's parity observation make the card fiddly, and the proof
is hopeless.  The one thing it *adds* over `A005153Switkay.lean` is Hasler's
parity split, which is provable and is stated below.
-/
import Mathlib
import Enumerative.Practical

set_option autoImplicit false

namespace Candidates.A209312

/-! ## Definition layer

Existing repo definition reused: `Nat.Practical` from
`Proofs/Enumerative/Practical.lean`, with `instance decidablePredPractical`.
`leandoc "Nat.Practical"` is a `mode:"miss"` — Mathlib has none.

**Subtraction discipline.**  `n − p` is `ℕ` subtraction and would truncate to `0`
when `p > n`; the counting set restricts to `p < n`, so it never truncates, but
STYLE.md wants that visible.  `A209312Cond` therefore takes `p < n` as an
explicit conjunct rather than relying on the enclosing `Finset` range. -/

/-- The A209312 condition at offset `p`: `p` is practical, `p < n`, and
`n − p`, `n + p` are **both prime or both practical**.  The disjunction is the
OEIS's, and it is inclusive. -/
def A209312Cond (n p : ℕ) : Prop :=
  p.Practical ∧ p < n ∧
    (((n - p).Prime ∧ (n + p).Prime) ∨ ((n - p).Practical ∧ (n + p).Practical))

instance (n p : ℕ) : Decidable (A209312Cond n p) := by unfold A209312Cond; infer_instance

/-- A209312 itself: the number of such `p`. -/
def a209312 (n : ℕ) : ℕ := ((Finset.range n).filter (A209312Cond n)).card

/-! ## The conjecture -/

/-- **Sun's conjecture (A209312, Zhi-Wei Sun, Jan 19 2013).**

Verbatim: "Conjecture: a(n)>0 for all n>2." / "This has been verified for n up
to 10^7."

The `2 < n` guard is from the source and is load-bearing: `a(1) = a(2) = 0`, so
the statement is *false* without it.  (`n = 2`: the only practical `p < 2` is
`p = 1`, giving `(1, 3)` — `1` is neither prime nor practical-plus-prime-pair,
and `1` *is* practical but `3` is not, so neither disjunct fires.)

**Mathlib primitives available.**  `Nat.Prime` and its API,
`Nat.exists_prime_lt_and_le_two_mul` (Bertrand); `Finset.card_pos`,
`Finset.filter_nonempty_iff`.  Practical-number side is all repo API.

**Sketch of an attack.**  Hopeless in full, for the same reason Switkay's
conjecture is: it asserts a positive-density additive structure statement about
primes and practicals simultaneously.  What *is* accessible:
1. **Hasler's parity split** (below): for odd `n > 3`, the only live disjunct is
   "both prime"; for even `n`, only "both practical" (except the `p = 1` case).
   This halves the search and is provable today.
2. For **odd** `n`, the surviving claim is "there is a practical `p < n` with
   `n − p` and `n + p` both prime" — a *symmetric-prime* statement, strictly
   harder than Goldbach-type statements because it demands two primes
   simultaneously.  Hopeless.
3. For **even** `n`, it is "there is a practical `p < n` with `n ± p` both
   practical".  Melfi's theorem (every even number is a sum of two practicals)
   gives `n − p` practical for suitable `p`, but not `n + p` simultaneously.
   Still hopeless, but *closer* — a strengthening of Melfi to a symmetric form
   would do it, and that is a well-posed research question.

**Tactic families.**  `decide` for small `n` via `decidablePredPractical` and
the `Nat.Prime` decidability; `native_decide` for the sweep;
`Finset.card_pos` / `Finset.filter_nonempty_iff` to move between the count and
the existential; `omega` for the parity bookkeeping.

**Related work in this repo.** `Enumerative.Practical`,
`Enumerative.StewartCriterion`.  Adjacent cards in this directory:
`A005153Switkay.lean` (the cleaner Tier-1 statement),
`A373686SomuTran.lean`, `A222603PracticalTree.lean`,
`A005153SunRootDecreasing.lean` — the last three are all Sun's practical-number
programme. -/
theorem sun_a209312_pos (n : ℕ) (hn : 2 < n) : 0 < a209312 n := by
  sorry

/-- The existential form, which is what a proof would actually produce. -/
theorem sun_a209312_exists (n : ℕ) (hn : 2 < n) : ∃ p : ℕ, A209312Cond n p := by
  sorry

/-- **Hasler's parity split (A209312, M. F. Hasler, Jan 19 2013) — provable.**

Verbatim: "Except for p=1, all practical numbers are even. Thus, (n-p,n+p) prime
is possible only if n is odd, and (n-p,n+p) can be practical only if n is even
(except for p=1)."

Formalized for `p > 1` (so `p` is even by `Nat.Practical.two_dvd`):
if `n − p` and `n + p` are both prime and `n + p > 2`, then `n` is odd;
if both are practical and `n + p > 1`, then `n` is even.
This is provable today from `Practical.two_dvd` plus parity, and it is the one
genuinely useful lemma this card contributes over `A005153Switkay.lean`. -/
theorem hasler_parity {n p : ℕ} (hp : p.Practical) (hp1 : 1 < p) (hpn : p < n) :
    ((n - p).Prime ∧ (n + p).Prime ∧ 2 < n + p → Odd n) ∧
    ((n - p).Practical ∧ (n + p).Practical ∧ 1 < n + p → Even n) := by
  sorry

/-! ## Sanity layer -/

-- PROVABLE: the DATA head `a(1..10) = 0,0,1,2,2,2,2,1,2,3`, which pins the
-- counting convention (practical `p` with `p < n`, inclusive disjunction).
example : List.map a209312 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] = [0, 0, 1, 2, 2, 2, 2, 1, 2, 3] := by
  native_decide

-- PROVABLE: the `2 < n` guard is load-bearing — `a(1) = a(2) = 0` are genuine
-- counterexamples to the ungarded statement.
example : a209312 1 = 0 ∧ a209312 2 = 0 := by decide

-- PROVABLE: satisfiability at the boundary.  `a(3) = 1` via `p = 1`:
-- `(3 − 1, 3 + 1) = (2, 4)`, both practical.
example : A209312Cond 3 1 := by decide

-- PROVABLE: and via the *other* disjunct at `n = 4`, `p = 1`:
-- `(3, 5)` both prime.  Both branches of the disjunction are live, so neither
-- can be dropped.
example : A209312Cond 4 1 := by decide
example : A209312Cond 4 2 := by decide

-- PROVABLE: `p = 1` is the exception Hasler flags — it is the only *odd*
-- practical number.
example : Nat.Practical 1 ∧ ¬ Even 1 := ⟨Nat.practical_one, by decide⟩

-- PROVABLE: and every practical `p > 1` is even (repo lemma), which is what
-- drives `hasler_parity`.
example : ∀ p ∈ Finset.Icc 2 100, p.Practical → Even p := by decide

-- PROVABLE (window check): `a(n) > 0` for every `3 ≤ n ≤ 5000`.  The candidates
-- document proposed `n ≤ 2000`; `5000` is still comfortable, but time it before
-- raising further — `A209312Cond` calls `Nat.Practical` three times per `p`.
example : ∀ n ∈ Finset.Icc 3 5000, 0 < a209312 n := by native_decide

-- PROVABLE: A209321 ("Indices for which a(n)=2") cross-check — `a(26) = 2`,
-- `a(38) = 2`, `a(46) = 2`, read off the DATA line.
example : a209312 26 = 2 ∧ a209312 38 = 2 ∧ a209312 46 = 2 := by native_decide

/-! ## Notes for a follow-up card

Only one item is worth doing:

* `hasler_parity` — provable today from `Nat.Practical.two_dvd` and parity, ~30
  lines.  It is a real (small) theorem about the sequence and it is the reason
  to keep this card at all.

The conjecture itself is strictly harder than Switkay's (`A005153Switkay.lean`)
and should be ranked below it, as the candidates document already says. -/

/-!
## Adversarial review verdict — **PASS** (zero defects)

Independent re-pull of A209312 plus a from-scratch python recomputation,
2026-08-05.

Confirmed:
* NAME, all 100 TERMS, the three COMMENTS, `%O 1,4`, XREFS verbatim.
* **`%A A209312 _Zhi-Wei Sun_, Jan 19 2013`** — the candidates document's guess
  ("uncredited; style strongly suggests Zhi-Wei Sun") is confirmed by the raw
  pull.  `goof oeis show` strips `%A`, which is why the earlier sweep could not
  see it.
* `a(1..10) = 0,0,1,2,2,2,2,1,2,3` reproduced independently; the spot-checks
  `a(3) = 1` (via `p = 1`, `(2,4)` both practical) and `a(4) = 2` (via `(3,5)`
  both prime and `(2,6)` both practical) are correct.
* `hasler_parity` is **true**: `1 < p` plus practicality forces `p` even
  (`Nat.Practical.two_dvd`), so `n ± p` share `n`'s parity; both prime and `> 2`
  makes them odd, both practical and `> 1` makes them even.  The `2 < n + p` and
  `1 < n + p` side conditions are vacuously satisfied under the stated
  hypotheses (they force `n + p ≥ 5`) but are correct and conservative.
-/

end Candidates.A209312
