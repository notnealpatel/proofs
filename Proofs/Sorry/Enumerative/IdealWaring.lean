import Enumerative.IdealWaring

/-!
# A002804: explicit admission archive

This archive imports the proved production infrastructure and adds only the
uniform positive-exponent upper admission and its dependent identity. The
source/status ledger below is retained in full; references to production
declarations describe the imported module, not new proofs in this archive.
Both declarations below depend on `sorryAx`.

## The presumed value of `g(n)` in Waring's problem

## Source, pinned verbatim

Re-pulled with `goof oeis show A002804` on **2026-08-05**.  The `offset`, `author`
and `%I` fields are not exposed by `goof oeis show`; they were read from the OEIS
internal text format (`https://oeis.org/search?q=id:A002804&fmt=text`, header
`%I A002804 M3361 N1353 #122 Jul 11 2026 13:08:59`) on the same day.

`id` (verbatim): `A002804`

`name` (verbatim):

> (Presumed) solution to Waring's problem: g(n) = 2^n + floor((3/2)^n) - 2.

`keywords` (verbatim): `nonn,easy`

`offset` (verbatim, from `%O`): `1,2`

`author` (verbatim, from `%A`): `_N. J. A. Sloane_`

`terms` (verbatim, the whole field — 34 terms; line-wrapped here only, the field
itself is one line):

> 1,4,9,19,37,73,143,279,548,1079,2132,4223,8384,16673,33203,66190,132055,263619,
> 526502,1051899,2102137,4201783,8399828,16794048,33579681,67146738,134274541,
> 268520676,536998744,1073933573,2147771272,4295398733,8590581749,17180839921

`comments` (verbatim, all four entries of the field, in order):

> g(n) is the smallest number s such that every natural number is the sum of at
> most s n-th powers of natural numbers.

> It is known (Kubina and Wunderlich, 1990) that g(n) = 2^n + floor((3/2)^n) - 2
> for all n <= 471600000. This formula is conjectured to be correct for all n (see
> A174420).

> Mahler showed that there are only finitely many n's for which this formula
> fails. - _Tomohiro Yamada_, Sep 23 2017

> This sequence (which corresponds to Waring's original conjecture) is much easier
> to compute than A079611, the problem of finding the minimal s = G(n) for almost
> all (= sufficienly large) integers. See Wikipedia for a one-line proof that this
> value for g(n), conjectured by J. A. Euler in 1772, is indeed a lower bound; it
> is known to be tight if 2^n*frac((3/2)^n) + floor((3/2)^n) <= 2^n, and no
> counterexample to this inequality is known. - _M. F. Hasler_, Jun 29 2014

`xrefs` (verbatim): `Cf. A002376, A002377, A079611, A174406, A174420, A297446 (for
info on Mathematica functions).`

`programs` (verbatim, the PARI and Python entries — they are the ones that fix the
floor convention as a `ℕ`-division; the bare `(Python)` line is its own element of
the `programs` array, reproduced here in place):

> (PARI) a(n)=2^n+(3^n>>n)-2 \\ _Charles R Greathouse IV_, Feb 01 2013

> (Python)
> def A002804(n): return (1<<n)+(3**n>>n)-2 # _Chai Wah Wu_, Jun 25 2024

Both compute `floor((3/2)^n)` as `3^n >> n`, i.e. as the `ℕ`-division
`3 ^ n / 2 ^ n`.  That is the reading taken here, and
`three_pow_div_two_pow_eq_floor` proves it agrees with `⌊((3 : ℚ) / 2) ^ n⌋₊`.

## Wikipedia's one-line proof, pinned verbatim

Hasler's comment says "See Wikipedia for a one-line proof".  Fetched with
`goof wiki article "Waring's problem"` on 2026-08-05; the relevant two paragraphs,
verbatim (LaTeX as it appears in the source):

> Let $q$ and $r$ be defined by the Euclidean division$3^k = 2^k q + r, \quad 0 \le
> r < 2^k,$or explicitly by $q = \lfloor(3/2)^k\rfloor $ and $r = 2^k \{(3/2)^k\} $,
> where $\lfloor x\rfloor$ and $\{x\}$ respectively denote the integral and
> fractional part of a real number $x$.

> Since the number $2^k q - 1 $ is less than $3^k$, as a sum of integer powers, it
> can only be expressed using $1^k$ and $2^k$. Using modular arithmetic, one shows
> that the fewest number of terms is achieved by the formula$2^k q - 1 =
> \underbrace{1^k + \dots + 1^k}_{2^k-1 \text{ times}} + \underbrace{2^k + \dots +
> 2^k}_{q - 1 \text{ times}},$and it follows that$g(k) \ge 2^k + q - 2,$which was
> noted by J. A. Euler in about 1772.

and, on the status of the conjecture:

> No value of $k$ is known for which the hypothesis $q + r > 2^k$ in the last two
> cases holds. Mahler proved that there can only be a finite number of such $k$.
> Kubina and Wunderlich, extending work of Stemmler, have shown that any such $k$
> must satisfy $k > 471\,600\,000$. It is conjectured that there are no such $k$; in
> that case, $g(k) = 2^k + q - 2$ for *every* positive integer $k$.

The same article fixes the definition of `g` used below:

> For every $k$, let $g(k)$ denote the minimum number $s$ of $k$th powers of
> naturals needed to represent all positive integers.

## What this file establishes

* `idealWaring n = 2 ^ n + 3 ^ n / 2 ^ n - 2` is the entry's formula, checked
  against the first twelve `terms` and against `⌊((3 : ℚ) / 2) ^ n⌋₊`;
* `idealWaring_le_of_waringAdmissible` — **J. A. Euler's lower bound, sorry-free**:
  every `s` that works for exponent `n ≠ 0` satisfies `idealWaring n ≤ s`, hence
  `idealWaring n ≤ waringG n`.  This is the "one-line proof" above, formalized;
* The upper half `waringAdmissible_idealWaring` and its consequence
  `waringG_eq_idealWaring` are admissions archived in
  `Sorry.Enumerative.IdealWaring`, not declarations of this production module.
  Their exact domain remains `n ≠ 0`, including `n = 1`.

Sorry-free consequences that pin the statements to reality:

* `waringG_one : waringG 1 = 1` and `waringG_two : waringG 2 = 4` — the entry's
  `a(1)` and `a(2)`, proved outright (the second from Mathlib's
  `Nat.sum_four_squares`, i.e. Lagrange).  `waringG_two` in particular shows the
  set `{s | WaringAdmissible 2 s}` is nonempty, so `waringG` is not reading its
  `sInf` junk value there;
* `not_isSumOfNthPowers_seven`, `not_isSumOfNthPowers_twentyThree`,
  `not_isSumOfNthPowers_seventyNine` — the Wikipedia sentence "7 requires 4
  squares, 23 requires 9 cubes, and 79 requires 19 fourth powers", each with its
  matching positive certificate.  All three are instances of the same Euler
  argument at `q = 2, 3, 5`.

## Deviation from the Wikipedia argument

Wikipedia says "Using modular arithmetic, one shows that the fewest number of terms
is achieved by ...".  No modular arithmetic is used here.  Writing `a` for the
number of `2 ^ n` summands and `b` for the number of `1 ^ n` summands, `a * 2 ^ n +
b = 2 ^ n q - 1` forces `a < q`; putting `u = q - a ≥ 1` gives `b + 1 = 2 ^ n u`, so
the term count is `a + b = q - 1 + u (2 ^ n - 1)`, minimized at `u = 1`.  That is a
counting argument, and it is what `two_pow_add_le_of_isSumOfNthPowers` proves — in
that proof `u` appears shifted, as `q = a + t + 1` with `t = u - 1`, so that all the
arithmetic stays inside `ℕ` and `omega` can finish.

## Conventions and guards

*"At most `s` powers".*  `IsSumOfNthPowers n s N` is `∃ m : Multiset ℕ,
Multiset.card m ≤ s ∧ (m.map (· ^ n)).sum = N`.  The multiset (not a list, not a
tuple) is the right carrier: a sum of powers has no order, and the `≤` makes the
comment's "at most" explicit rather than relying on `0 ^ n = 0` for padding.

*"Of natural numbers".*  The entry's comment says "n-th powers of natural numbers";
Wikipedia says "$k$th powers of naturals".  Whether `0` counts as an allowed base is
immaterial: `isSumOfNthPowers_iff_isSumOfPosNthPowers` proves that for `n ≠ 0` the
restriction to strictly positive bases defines the same predicate (drop the zeros;
`0 ^ n = 0` and the count only goes down).

*"Every natural number" vs "all positive integers".*  `WaringAdmissible n s`
quantifies over all of `ℕ`, including `0`, matching the entry's comment; Wikipedia's
"all positive integers" gives the same notion, because `0` is the empty sum
(`Multiset.card 0 = 0 ≤ s`) and so is representable for every `n` and `s`.

*`n = 0` is excluded everywhere.*  `not_waringAdmissible_zero` shows no `s` works
for exponent `0` (every `x ^ 0 = 1`, so only `N ≤ s` are representable), hence
`waringG 0 = sInf ∅ = 0` (`waringG_zero`) is a junk value.  The entry's `offset` is
`1`, so this is outside A002804 anyway.  Note that `idealWaring 0 = 1 + 1 - 2 = 0`
*also* holds, so the unguarded `∀ n, waringG n = idealWaring n` would be true at
`n = 0` for entirely spurious reasons; every statement below carries `n ≠ 0`.

*The two totalized operators.*  `3 ^ n / 2 ^ n` is `ℕ`-division, which is the
intended floor (`three_pow_div_two_pow_eq_floor`, and the PARI/Python programs
above).  The `- 2` is `ℕ`-subtraction, which does not truncate for `n ≠ 0`
(`idealWaring_add_two`).  `waringG` is an `sInf` over `ℕ`, whose junk value on the
empty set is discussed above and isolated in `waringG_zero`.

*What `waringAdmissible_idealWaring` really contains.*  Its `≤` half needs the
Hilbert–Waring theorem (1909), which is not in Mathlib and is not proved here; the
sorry therefore covers a proved theorem together with the open conjecture.  That is
unavoidable if the archived claim is to be stated as the entry states it: A002804
presupposes that `g(n)` exists.  The known partial results — Kubina and Wunderlich's
`n <= 471600000` and Mahler's finiteness — are recorded in the docstring of
`waringAdmissible_idealWaring` and are *not* formalized.


## Admission boundary and source interpretation

The source quotes above are retained verbatim. The published conditional
Dickson/Pillai/Rubugunday/Niven engine linking `WaringTight` to admissibility
is not locally proved. Mahler's finite-exception result and the external
471600000 search do not establish a uniform formal result here; merely making
a finite-exception bound effective would not by itself exclude all exceptions.
No Hilbert–Waring proof is supplied. The upper admission and its dependent
identity are in `Sorry.Enumerative.IdealWaring` only. In particular,
`idealWaring 1 = 2 + 1 - 2 = 1`, not 0, and exponent 1 remains in the contract.

## Library wiring

`Proofs/Enumerative.lean` is not edited by this lane; the import line
(`import Enumerative.IdealWaring`) is the orchestrator's to add.

## Computational orientation (not proofs)

`command -v sage` is empty on this machine, so no `sage` was used, none is claimed,
and no sympy or other fallback was substituted for it.  No `python` was run either:
every numeric claim below is discharged by the Lean kernel (`decide` / `norm_num`),
including the twelve-term comparison against the `terms` field and the range check
`waringTight_of_mem_range`.

## Axiom audit

Every production declaration reports a subset of `{propext, Classical.choice, Quot.sound}`.
Only the separate archive's `waringAdmissible_idealWaring` and
`waringG_eq_idealWaring` additionally report `sorryAx`.
There is no `native_decide`.
-/

set_option autoImplicit false

namespace A002804

/-! ## The archived claim -/

/-- **A002804's `name` field, upper half — the single intended `sorry`.**

Verbatim from the entry, pulled 2026-08-05:

> (Presumed) solution to Waring's problem: g(n) = 2^n + floor((3/2)^n) - 2.

with the comment fixing what `g` means:

> g(n) is the smallest number s such that every natural number is the sum of at
> most s n-th powers of natural numbers.

The lower half, `idealWaring n ≤ s` for every admissible `s`, is
`idealWaring_le_of_waringAdmissible` and is proved.  What remains — and what this
declaration asserts — is that `idealWaring n` many `n`-th powers actually suffice.

**Status: open.**  Verbatim from the entry:

> It is known (Kubina and Wunderlich, 1990) that g(n) = 2^n + floor((3/2)^n) - 2
> for all n <= 471600000. This formula is conjectured to be correct for all n (see
> A174420).

> Mahler showed that there are only finitely many n's for which this formula
> fails. - _Tomohiro Yamada_, Sep 23 2017

So the statement is known for `n ≤ 471600000` (Kubina–Wunderlich, *Extending
Waring's conjecture to 471,600,000*, Math. Comp. 55 (1990), 815–820) and can fail
for at most finitely many `n` (Mahler, *On the fractional parts of the powers of a
rational number (II)*, Mathematika 4 (1957), 122–124).  Neither result is formalized
here; both would themselves be substantial developments.

**What this `sorry` also swallows.**  Even for a *single* `n`, the assertion
contains the Hilbert–Waring theorem (1909) — that some finite `s` works at all —
which Mathlib does not have.  Hilbert–Waring is a theorem, so this does not make the
statement weaker than the entry's; but a future discharge of the `sorry` has to
supply it.  The `n = 2` case is discharged unconditionally in the imported production module
(`waringAdmissible_two_four`, from `Nat.sum_four_squares`), and `n = 1` trivially
(`waringAdmissible_one_one`); the exact values `waringG_one` and `waringG_two`
therefore stand free of this `sorry`.

**Why the remaining direction is hard.**  Reducing to `idealWaring n` summands means
handling *every* natural number with a fixed budget, and the extremal numbers are
exactly the ones the lower bound exhibits: `2 ^ n q - 1` and its relatives, which use
only `1 ^ n` and `2 ^ n`.  Dickson, Pillai, Rubugunday and Niven reduced the general
`g(n)` formula to the single arithmetic inequality `q + r ≤ 2 ^ n` recorded as
`WaringTight`, so the open part is really a Diophantine question about the fractional
parts of `(3/2) ^ n`; Mahler's finiteness result is an ineffective bound on that
question, but an effective bound alone would still leave exceptions to exclude. The
published conditional engine is not locally proved; neither cited external
result supplies this uniform admission. -/
theorem waringAdmissible_idealWaring {n : ℕ} (hn : n ≠ 0) :
    WaringAdmissible n (idealWaring n) := by
  -- intended sorry: A002804 `name`, "(Presumed) solution to Waring's problem"
  sorry

/-- **The archived A002804 identity**, `g(n) = 2 ^ n + floor((3/2) ^ n) - 2` for
`n ≠ 0`, assembled from the two halves.  The `≤` direction is
`waringAdmissible_idealWaring` (the `sorry`), the `≥` direction is
`idealWaring_le_waringG` (J. A. Euler, proved).  Depends on `sorryAx`. -/
theorem waringG_eq_idealWaring {n : ℕ} (hn : n ≠ 0) : waringG n = idealWaring n :=
  le_antisymm (waringG_le (waringAdmissible_idealWaring hn))
    (idealWaring_le_waringG hn ⟨_, waringAdmissible_idealWaring hn⟩)

end A002804

/-!
# Historical/source card: A002804

This documentation migration preserves the complete remaining source card,
including its historical status and estimates, without changing any executable
archive bytes. The source is OEIS A002804 and the Mahler/Yamada comment cited
below. The objects are natural numbers represented by multisets of natural
n-th powers, with at most s summands; the exponent domain is n != 0, including
n = 1 and idealWaring 1 = 1. This is integer Waring theory, not ranks of forms.
The imported production module proves the independent lower bounds, guarded
infimum facts and exponent-one/two cases. The two existing archive declarations
are explicitly admitted, not proved. No duplicate declaration is added here.
The uniform upper bound and its conditional arithmetic engine remain unpaid;
finite external verification is not a proof for all positive exponents.

## Formalize/A002804-euler-ideal-waring.md (verbatim)

```text
seq:     A002804
claim:   euler-ideal-waring
status:  open mathematics; faithful admission boundary implemented
stmt:    S (original estimate; genuine integer Waring definitions now exist)
proof:   hard-open
module:  Proofs/Enumerative/IdealWaring.lean;
         archive Proofs/Sorry/Enumerative/IdealWaring.lean
source:  OEIS A002804 comments; Mahler finiteness noted by
         Tomohiro Yamada, 2017-09-23; cf. A174420

EXACT CLAIM
  For every positive exponent n, the genuine integer Waring number is
    g(n) = 2^n + floor((3/2)^n) - 2.
  WaringAdmissible n s means every natural number is a sum of at most
  s n-th powers; the production module uses actual multisets and defines
  waringG by Nat.sInf with attainment/nonemptiness guards on its lemmas.
  The exact archived domain is n != 0. In particular idealWaring(1)=1,
  not 0; the independent exponent-one and exponent-two cases are proved.
  Integer Waring numbers are not Waring ranks of homogeneous forms.
  Proofs/CHILO/ConnerWaring.lean does not supply an inference between them.

ARITHMETIC ROUTE AND LIMITS
  Write 3^n=q*2^n+r with 0 <= r < 2^n. The ideal-Waring inequality is
  q+r <= 2^n. For n>0 its exact fractional-part threshold is
    frac((3/2)^n) <= (1-(3/4)^n)/(1-2^(-n)).
  The smaller bound 1-(3/4)^n is only sufficient. The former card's
  ellipsis was not an exact formula. The published conditional Waring
  engine relating this arithmetic to the upper bound is not locally proved.
  Mahler's finite-exception result and the external Kubina-Wunderlich
  computation through n=471600000 do not prove the uniform conjecture;
  the computation has not been replayed as a local Lean certificate.

IMPLEMENTATION STATUS
  Production defines the genuine objects and proves independent lower
  bounds, existence-guarded sInf facts, and the n=1,2 cases. The accepted
  admission split moves exactly waringAdmissible_idealWaring and its
  dependent waringG_eq_idealWaring to the matching Sorry module. The build,
  fresh all-owned production axiom audit, and separate archive signature
  audit and independent review passed; the boundary was adopted at
  3935f8aa7ad524d66da0c83342120e9ac62f779a. This card remains for
  metadata reconciliation before retirement. Acceptance is implementation, not a
  proof of the open formula or of the locally unformalized conditional engine.
```
-/
