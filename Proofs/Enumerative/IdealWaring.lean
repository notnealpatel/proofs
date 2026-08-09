import Mathlib

/-!
# A002804: the presumed value of `g(n)` in Waring's problem

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
* `waringAdmissible_idealWaring` — the *upper* half, `WaringAdmissible n
  (idealWaring n)`.  **This is the single intended `sorry` of the file**;
* `waringG_eq_idealWaring` — the entry's `name` field, obtained from those two.
  It is not itself a `sorry`, but it depends on one.

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

Every declaration below reports a subset of `{propext, Classical.choice, Quot.sound}`
except `waringAdmissible_idealWaring` — the single intended `sorry` — and
`waringG_eq_idealWaring`, which depends on it; both additionally report `sorryAx`.
The sweep is at the end of the file.  There is no `native_decide`.
-/

set_option autoImplicit false

namespace A002804

/-! ## Representations as sums of `n`-th powers -/

/-- `IsSumOfNthPowers n s N` says that `N` is a sum of **at most** `s` `n`-th powers
of natural numbers.

This is the A002804 comment "`N` is the sum of at most `s` `n`-th powers of natural
numbers" read literally.  The summands are carried by a `Multiset ℕ` because a sum
has no order, and "at most" is the explicit `Multiset.card m ≤ s`. -/
def IsSumOfNthPowers (n s N : ℕ) : Prop :=
  ∃ m : Multiset ℕ, Multiset.card m ≤ s ∧ (m.map (· ^ n)).sum = N

/-- The same predicate with the summand bases restricted to be strictly positive.
`isSumOfNthPowers_iff_isSumOfPosNthPowers` shows the two agree for `n ≠ 0`, so the
ambiguity in "natural numbers" costs nothing. -/
def IsSumOfPosNthPowers (n s N : ℕ) : Prop :=
  ∃ m : Multiset ℕ, Multiset.card m ≤ s ∧ (∀ x ∈ m, 0 < x) ∧ (m.map (· ^ n)).sum = N

-- ground truth: `7 = 2 ^ 2 + 1 ^ 2 + 1 ^ 2 + 1 ^ 2`
example : IsSumOfNthPowers 2 4 7 := ⟨{2, 1, 1, 1}, by decide, by decide⟩

-- ground truth: `23 = 2 ^ 3 + 2 ^ 3 + 7 * 1 ^ 3`
example : IsSumOfNthPowers 3 9 23 := ⟨{2, 2, 1, 1, 1, 1, 1, 1, 1}, by decide, by decide⟩

-- ground truth for the positive form, at the same witness
example : IsSumOfPosNthPowers 2 4 7 := ⟨{2, 1, 1, 1}, by decide, by decide, by decide⟩

-- "at most" is really `≤`, not `=`: a shorter multiset is allowed
example : IsSumOfNthPowers 2 4 4 := ⟨{2}, by decide, by decide⟩

/-- A representation with at most `s` summands is a representation with at most `s'`
summands whenever `s ≤ s'`.  No padding is needed — "at most" is built into the
definition — so this holds even at `n = 0`. -/
theorem IsSumOfNthPowers.mono {n s s' N : ℕ} (h : IsSumOfNthPowers n s N) (hss : s ≤ s') :
    IsSumOfNthPowers n s' N :=
  let ⟨m, hcard, hsum⟩ := h; ⟨m, hcard.trans hss, hsum⟩

/-- **Zero bases may be discarded.**  For `n ≠ 0`, allowing `0` among the summand
bases does not enlarge the set of representable numbers: `0 ^ n = 0` contributes
nothing to the sum, and deleting it only shortens the multiset.

This settles the reading of "n-th powers of natural numbers" in the A002804 comment
against Wikipedia's "$k$th powers of naturals": the two are the same predicate. -/
theorem isSumOfNthPowers_iff_isSumOfPosNthPowers {n s N : ℕ} (hn : n ≠ 0) :
    IsSumOfNthPowers n s N ↔ IsSumOfPosNthPowers n s N := by
  constructor
  · rintro ⟨m, hcard, hsum⟩
    refine ⟨m.filter (0 < ·), (Multiset.card_le_card (Multiset.filter_le _ _)).trans hcard,
      fun x hx => (Multiset.mem_filter.mp hx).2, ?_⟩
    have hzero : ((m.filter fun x : ℕ => ¬ 0 < x).map (· ^ n)).sum = 0 := by
      refine Multiset.sum_eq_zero ?_
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
      have hx0 : x = 0 := by have hlt := (Multiset.mem_filter.mp hx).2; omega
      rw [hx0, zero_pow hn]
    calc ((m.filter fun x : ℕ => 0 < x).map (· ^ n)).sum
        = ((m.filter fun x : ℕ => 0 < x).map (· ^ n)).sum
          + ((m.filter fun x : ℕ => ¬ 0 < x).map (· ^ n)).sum := by rw [hzero, add_zero]
      _ = (((m.filter fun x : ℕ => 0 < x) + m.filter fun x : ℕ => ¬ 0 < x).map (· ^ n)).sum := by
          rw [Multiset.map_add, Multiset.sum_add]
      _ = (m.map (· ^ n)).sum := by rw [Multiset.filter_add_not]
      _ = N := hsum
  · rintro ⟨m, hcard, -, hsum⟩
    exact ⟨m, hcard, hsum⟩

/-! ## `g(n)` -/

/-- `WaringAdmissible n s` says that `s` many `n`-th powers suffice for **every**
natural number.  A002804's comment: "`g(n)` is the smallest number `s` such that
every natural number is the sum of at most `s` `n`-th powers of natural numbers." -/
def WaringAdmissible (n s : ℕ) : Prop := ∀ N : ℕ, IsSumOfNthPowers n s N

/-- Admissibility is upward closed. -/
theorem WaringAdmissible.mono {n s s' : ℕ} (hs : WaringAdmissible n s) (hss : s ≤ s') :
    WaringAdmissible n s' := fun N => (hs N).mono hss

/-- **`g(1) = 1` is available for free**: every `N` is `N ^ 1`. -/
theorem waringAdmissible_one_one : WaringAdmissible 1 1 := fun N => ⟨{N}, by simp, by simp⟩

/-- **Lagrange's four-square theorem** in the present notation: four squares always
suffice.  This is `Nat.sum_four_squares` repackaged, and it is what makes
`waringG_two` — the entry's `a(2) = 4` — provable outright. -/
theorem waringAdmissible_two_four : WaringAdmissible 2 4 := by
  intro N
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares N
  refine ⟨{a, b, c, d}, by simp only [Multiset.insert_eq_cons, Multiset.card_cons,
    Multiset.card_singleton]; omega, ?_⟩
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
    Multiset.map_singleton, Multiset.sum_singleton]
  omega

/-- **Exponent `0` admits no `s` at all.**  Every `x ^ 0` is `1`, so a multiset of
size at most `s` sums to at most `s`, and `s + 1` is unreachable.  Consequently
`waringG 0` is the `sInf ∅` junk value; see `waringG_zero`. -/
theorem not_waringAdmissible_zero (s : ℕ) : ¬ WaringAdmissible 0 s := by
  intro h
  obtain ⟨m, hcard, hsum⟩ := h (s + 1)
  have hone : (m.map (· ^ 0)).sum = Multiset.card m := by simp
  omega

/-- `g(n)`: the least `s` that works for exponent `n`.  Junk (`= 0`) when no `s`
works, which by `not_waringAdmissible_zero` happens exactly at `n = 0`; for `n ≠ 0`
non-junkness is the Hilbert–Waring theorem, which Mathlib does not have and which
this file assumes only inside `waringAdmissible_idealWaring`. -/
noncomputable def waringG (n : ℕ) : ℕ := sInf {s | WaringAdmissible n s}

/-- `g(n)` is a lower bound for every admissible `s`. -/
theorem waringG_le {n s : ℕ} (hs : WaringAdmissible n s) : waringG n ≤ s := Nat.sInf_le hs

/-- `g(n)` is itself admissible, provided some `s` is. -/
theorem waringAdmissible_waringG {n : ℕ} (hne : ∃ s, WaringAdmissible n s) :
    WaringAdmissible n (waringG n) := by
  have h : sInf {s | WaringAdmissible n s} ∈ {s | WaringAdmissible n s} := Nat.sInf_mem hne
  exact h

/-- `g(n)` characterizes admissibility: `s` works iff `g(n) ≤ s`. -/
theorem waringAdmissible_iff_waringG_le {n s : ℕ} (hne : ∃ s, WaringAdmissible n s) :
    WaringAdmissible n s ↔ waringG n ≤ s :=
  ⟨waringG_le, fun h => (waringAdmissible_waringG hne).mono h⟩

/-- **`waringG 0 = 0` is junk.**  The guard for every `n ≠ 0` hypothesis below. -/
theorem waringG_zero : waringG 0 = 0 := by
  refine Nat.sInf_eq_zero.mpr (Or.inr ?_)
  refine Set.eq_empty_iff_forall_notMem.mpr fun s hs => ?_
  exact not_waringAdmissible_zero s hs

/-! ## The A002804 formula -/

/-- `2 ^ n + floor((3/2) ^ n) - 2`, the entry's `name` field, with `floor((3/2) ^ n)`
spelled as the `ℕ`-division `3 ^ n / 2 ^ n` exactly as the entry's PARI
(`3^n>>n`) and Python (`3**n>>n`) programs do. -/
def idealWaring (n : ℕ) : ℕ := 2 ^ n + 3 ^ n / 2 ^ n - 2

/-- Ground truth against the entry's `terms` field: the first twelve values are
`1, 4, 9, 19, 37, 73, 143, 279, 548, 1079, 2132, 4223`.  The entry's `offset` is
`1,2`, whose first component says the sequence is indexed from `n = 1`; hence the
`i + 1`. -/
theorem idealWaring_terms :
    (List.range 12).map (fun i => idealWaring (i + 1)) =
      [1, 4, 9, 19, 37, 73, 143, 279, 548, 1079, 2132, 4223] := by decide

/-- The `ℕ`-division really is the floor: `3 ^ n / 2 ^ n = ⌊(3/2) ^ n⌋`. -/
theorem three_pow_div_two_pow_eq_floor (n : ℕ) : 3 ^ n / 2 ^ n = ⌊((3 : ℚ) / 2) ^ n⌋₊ := by
  rw [div_pow, show ((3 : ℚ) ^ n) = ((3 ^ n : ℕ) : ℚ) by push_cast; ring,
    show ((2 : ℚ) ^ n) = ((2 ^ n : ℕ) : ℚ) by push_cast; ring, Nat.floor_div_eq_div]

/-- The entry's formula, with the floor written as a `Nat.floor` over `ℚ`. -/
theorem idealWaring_eq_floor (n : ℕ) : idealWaring n = 2 ^ n + ⌊((3 : ℚ) / 2) ^ n⌋₊ - 2 := by
  rw [idealWaring, three_pow_div_two_pow_eq_floor]

/-- **The `ℕ`-subtraction in `idealWaring` does not truncate for `n ≠ 0`**: there
`2 ^ n + ⌊(3/2) ^ n⌋ ≥ 2 + 1 = 3`.  (At `n = 0` the value is `1 + 1 - 2 = 0`, and
the subtraction is exact there too — but `waringG 0 = 0` is junk, so `n = 0` is
excluded everywhere regardless.) -/
theorem idealWaring_add_two {n : ℕ} (hn : n ≠ 0) :
    idealWaring n + 2 = 2 ^ n + 3 ^ n / 2 ^ n := by
  have h2pos : 0 < 2 ^ n := Nat.two_pow_pos n
  have hq1 : 1 ≤ 3 ^ n / 2 ^ n :=
    (Nat.one_le_div_iff h2pos).mpr (Nat.pow_le_pow_left (by norm_num) n)
  have h2 : 2 ≤ 2 ^ n := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold idealWaring
  omega

/-! ## J. A. Euler's lower bound

The Wikipedia "one-line proof", formalized.  `two_pow_add_le_of_isSumOfNthPowers` is
the whole content: it applies verbatim to `2 ^ n q - 1` for *any* `q` with
`2 ^ n q ≤ 3 ^ n`, which is what makes the three small certificates below instances
of one lemma. -/

/-- Bookkeeping for a multiset of bases all bounded by `2`: the sum of `n`-th powers
splits as `(#2's) * 2 ^ n + (#1's)`, and those two counts together do not exceed the
size.  The `0`'s contribute `0 ^ n = 0`, which is where `n ≠ 0` is used. -/
private theorem count_two_mul_add_count_one {n : ℕ} (hn : n ≠ 0) :
    ∀ m : Multiset ℕ, (∀ x ∈ m, x ≤ 2) →
      (m.map (· ^ n)).sum = m.count 2 * 2 ^ n + m.count 1 ∧
        m.count 2 + m.count 1 ≤ Multiset.card m := by
  intro m
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x t ih =>
    intro h
    have hx : x ≤ 2 := h x (Multiset.mem_cons_self x t)
    have ht : ∀ y ∈ t, y ≤ 2 := fun y hy => h y (Multiset.mem_cons_of_mem hy)
    obtain ⟨hsum, hcnt⟩ := ih ht
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    interval_cases x
    · rw [Multiset.count_cons_of_ne (by norm_num : (2 : ℕ) ≠ 0),
        Multiset.count_cons_of_ne (by norm_num : (1 : ℕ) ≠ 0), zero_pow hn]
      omega
    · rw [Multiset.count_cons_of_ne (by norm_num : (2 : ℕ) ≠ 1),
        Multiset.count_cons_self, one_pow]
      omega
    · rw [Multiset.count_cons_self,
        Multiset.count_cons_of_ne (by norm_num : (1 : ℕ) ≠ 2), add_mul, one_mul]
      omega

/-- **J. A. Euler's counting argument (1772).**

Let `q` satisfy `2 ^ n q ≤ 3 ^ n` and let `N + 1 = 2 ^ n q`, i.e. `N = 2 ^ n q - 1`.
Then any representation of `N` as a sum of at most `s` `n`-th powers forces
`2 ^ n + q ≤ s + 2`.

Proof, following Wikipedia but with the "modular arithmetic" replaced by counting.
`N < 3 ^ n`, so no summand base exceeds `2` and the representation is
`a` copies of `2 ^ n` plus `b` copies of `1 ^ n`, with `a + b ≤ s`.  From
`a * 2 ^ n + b = N < 2 ^ n q` we get `a < q`; writing `q = a + t + 1` gives
`b + 1 = 2 ^ n (t + 1)`, whence
`s + 2 ≥ a + b + 2 = a + 2 ^ n t + 2 ^ n + 1 ≥ a + t + 1 + 2 ^ n = q + 2 ^ n`,
using `t ≤ 2 ^ n t`.  Equality needs `t = 0`, which is Wikipedia's
"`q - 1` copies of `2 ^ k` and `2 ^ k - 1` copies of `1 ^ k`". -/
theorem two_pow_add_le_of_isSumOfNthPowers {n s q N : ℕ} (hn : n ≠ 0)
    (hq3 : 2 ^ n * q ≤ 3 ^ n) (hN : N + 1 = 2 ^ n * q)
    (h : IsSumOfNthPowers n s N) : 2 ^ n + q ≤ s + 2 := by
  obtain ⟨m, hcard, hsum⟩ := h
  have h2pos : 0 < 2 ^ n := Nat.two_pow_pos n
  have hNlt : N < 3 ^ n := by omega
  have hle : ∀ x ∈ m, x ≤ 2 := by
    intro x hx
    rcases Nat.lt_or_ge 2 x with hx2 | hx2
    · exfalso
      have hpow : 3 ^ n ≤ x ^ n := Nat.pow_le_pow_left hx2 n
      have hmem : x ^ n ≤ (m.map (· ^ n)).sum :=
        Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (f := fun y => y ^ n) hx)
      omega
    · exact hx2
  obtain ⟨hsplit, hcnt⟩ := count_two_mul_add_count_one hn m hle
  set a := m.count 2
  set b := m.count 1
  have hab : a * 2 ^ n + b = N := by rw [← hsum, hsplit]
  have haq : a < q := by
    refine Nat.lt_of_mul_lt_mul_right (a := 2 ^ n) ?_
    have hcomm : q * 2 ^ n = 2 ^ n * q := Nat.mul_comm _ _
    omega
  obtain ⟨t, ht⟩ : ∃ t, q = a + t + 1 := ⟨q - a - 1, by omega⟩
  have hexp : 2 ^ n * q = 2 ^ n * a + (2 ^ n * t + 2 ^ n) := by rw [ht]; ring
  have hcomm : a * 2 ^ n = 2 ^ n * a := Nat.mul_comm _ _
  have htle : t ≤ 2 ^ n * t := Nat.le_mul_of_pos_left t h2pos
  omega

/-- **The Euler lower bound: `idealWaring n ≤ s` for every admissible `s`.**

Instantiate `two_pow_add_le_of_isSumOfNthPowers` at `q = ⌊(3/2) ^ n⌋ = 3 ^ n / 2 ^ n`,
whose defining property `2 ^ n q ≤ 3 ^ n` is `Nat.div_mul_le_self`.  This is the half
of A002804's `name` field that is a theorem, not a conjecture — the "one-line proof"
Hasler's comment points at. -/
theorem idealWaring_le_of_waringAdmissible {n s : ℕ} (hn : n ≠ 0)
    (hs : WaringAdmissible n s) : idealWaring n ≤ s := by
  have h2pos : 0 < 2 ^ n := Nat.two_pow_pos n
  have hq1 : 1 ≤ 3 ^ n / 2 ^ n :=
    (Nat.one_le_div_iff h2pos).mpr (Nat.pow_le_pow_left (by norm_num) n)
  have hq3 : 2 ^ n * (3 ^ n / 2 ^ n) ≤ 3 ^ n := by
    rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  have hpos : 0 < 2 ^ n * (3 ^ n / 2 ^ n) := Nat.mul_pos h2pos hq1
  have hkey := two_pow_add_le_of_isSumOfNthPowers hn hq3
    (N := 2 ^ n * (3 ^ n / 2 ^ n) - 1) (by omega) (hs _)
  have hshift := idealWaring_add_two hn
  omega

/-- The Euler bound at `g(n)` itself.  Needs some `s` to be admissible, i.e. the
Hilbert–Waring theorem at `n`; without it `waringG n` is the `sInf ∅` junk value. -/
theorem idealWaring_le_waringG {n : ℕ} (hn : n ≠ 0) (hne : ∃ s, WaringAdmissible n s) :
    idealWaring n ≤ waringG n :=
  idealWaring_le_of_waringAdmissible hn (waringAdmissible_waringG hne)

/-! ## Small cases, proved outright

Wikipedia (same fetch, verbatim including its LaTeX):

> Some simple computations show that 7 requires 4 squares, 23 requires 9 cubes, and
> 79 requires 19 fourth powers; these examples show that $g(2) \ge 4$, $g(3) \ge 9$,
> and $g(4) \ge 19$. Waring conjectured that these lower bounds were in fact exact
> values.

All three lower bounds are `two_pow_add_le_of_isSumOfNthPowers` at `q = 2, 3, 5`
(giving `N = 7, 23, 79`), and each comes with its positive certificate. -/

/-- `7 = 2 ^ 2 * 2 - 1` is not a sum of three squares. -/
theorem not_isSumOfNthPowers_seven : ¬ IsSumOfNthPowers 2 3 7 := fun h => by
  have hkey := two_pow_add_le_of_isSumOfNthPowers (n := 2) (q := 2) (N := 7)
    (by norm_num) (by norm_num) (by norm_num) h
  norm_num at hkey

/-- `7 = 2 ^ 2 + 1 ^ 2 + 1 ^ 2 + 1 ^ 2` is a sum of four squares. -/
theorem isSumOfNthPowers_seven : IsSumOfNthPowers 2 4 7 :=
  ⟨{2, 1, 1, 1}, by decide, by decide⟩

/-- `23 = 2 ^ 3 * 3 - 1` is not a sum of eight cubes. -/
theorem not_isSumOfNthPowers_twentyThree : ¬ IsSumOfNthPowers 3 8 23 := fun h => by
  have hkey := two_pow_add_le_of_isSumOfNthPowers (n := 3) (q := 3) (N := 23)
    (by norm_num) (by norm_num) (by norm_num) h
  norm_num at hkey

/-- `23 = 2 ^ 3 + 2 ^ 3 + 7 * 1 ^ 3` is a sum of nine cubes. -/
theorem isSumOfNthPowers_twentyThree : IsSumOfNthPowers 3 9 23 :=
  ⟨{2, 2, 1, 1, 1, 1, 1, 1, 1}, by decide, by decide⟩

/-- `79 = 2 ^ 4 * 5 - 1` is not a sum of eighteen fourth powers. -/
theorem not_isSumOfNthPowers_seventyNine : ¬ IsSumOfNthPowers 4 18 79 := fun h => by
  have hkey := two_pow_add_le_of_isSumOfNthPowers (n := 4) (q := 5) (N := 79)
    (by norm_num) (by norm_num) (by norm_num) h
  norm_num at hkey

/-- `79 = 4 * 2 ^ 4 + 15 * 1 ^ 4` is a sum of nineteen fourth powers. -/
theorem isSumOfNthPowers_seventyNine : IsSumOfNthPowers 4 19 79 :=
  ⟨{2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1}, by decide, by decide⟩

/-- Three squares do not suffice for every natural number — `7` is the obstruction.
This is the sharpness half of `waringG_two`. -/
theorem not_waringAdmissible_two_three : ¬ WaringAdmissible 2 3 :=
  fun h => not_isSumOfNthPowers_seven (h 7)

/-- **`g(1) = 1`**, the entry's `a(1)`. -/
theorem waringG_one : waringG 1 = 1 := by
  have hub : waringG 1 ≤ 1 := waringG_le waringAdmissible_one_one
  have hlb := idealWaring_le_waringG (n := 1) (by norm_num) ⟨1, waringAdmissible_one_one⟩
  rw [show idealWaring 1 = 1 by decide] at hlb
  omega

/-- **`g(2) = 4`**, the entry's `a(2)`: Lagrange's four-square theorem for the upper
bound, Euler's counting argument at `7` for the lower.  Together with `waringG_one`
these are the only two values of A002804 this file certifies free of the archived
`sorry`, and this one doubles as the witness that `{s | WaringAdmissible 2 s}` is
nonempty, so `waringG 2` is not an `sInf ∅`. -/
theorem waringG_two : waringG 2 = 4 := by
  have hub : waringG 2 ≤ 4 := waringG_le waringAdmissible_two_four
  have hlb := idealWaring_le_waringG (n := 2) (by norm_num) ⟨4, waringAdmissible_two_four⟩
  rw [show idealWaring 2 = 4 by decide] at hlb
  omega

/-! ## Hasler's tightness criterion

Hasler's comment: the value is "known to be tight if `2^n*frac((3/2)^n) +
floor((3/2)^n) <= 2^n`, and no counterexample to this inequality is known".  Since
`2 ^ n * frac((3/2) ^ n) = 3 ^ n mod 2 ^ n`, that is Wikipedia's `q + r ≤ 2^k` with
`3 ^ k = 2 ^ k q + r`.  The implication itself (Dickson, Pillai, Rubugunday, Niven)
is *not* formalized here; what is recorded is the criterion as a decidable predicate
and its verification on an initial range. -/

/-- `WaringTight n` is Hasler's `2 ^ n * frac((3/2) ^ n) + floor((3/2) ^ n) ≤ 2 ^ n`,
i.e. Wikipedia's `q + r ≤ 2 ^ k` for `3 ^ k = 2 ^ k q + r`. -/
def WaringTight (n : ℕ) : Prop := 3 ^ n % 2 ^ n + 3 ^ n / 2 ^ n ≤ 2 ^ n

instance (n : ℕ) : Decidable (WaringTight n) :=
  inferInstanceAs (Decidable (3 ^ n % 2 ^ n + 3 ^ n / 2 ^ n ≤ 2 ^ n))

/-- The Euclidean division behind `q` and `r`: `3 ^ n = 2 ^ n q + r`. -/
theorem two_pow_mul_div_add_mod (n : ℕ) :
    2 ^ n * (3 ^ n / 2 ^ n) + 3 ^ n % 2 ^ n = 3 ^ n :=
  Nat.div_add_mod (3 ^ n) (2 ^ n)

/-- Hasler's inequality holds for every `n < 41`, checked in the kernel.  ("No
counterexample to this inequality is known" — this is not evidence for the
conjecture, only a guard that `WaringTight` is not vacuously false.) -/
theorem waringTight_of_mem_range : ∀ n ∈ List.range 41, WaringTight n := by decide

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
supply it.  The `n = 2` case is discharged unconditionally elsewhere in this file
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
question, and effectivizing it is what would close A002804. -/
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

/-! ## Satisfiability and non-degeneracy

Every predicate above is instantiated at a concrete value in both polarities, so no
statement is about an empty domain, and the hypotheses of every conditional
statement are jointly inhabited. -/

-- `IsSumOfNthPowers` holds somewhere and fails somewhere, at the same `n`
example : IsSumOfNthPowers 2 4 7 ∧ ¬ IsSumOfNthPowers 2 3 7 :=
  ⟨isSumOfNthPowers_seven, not_isSumOfNthPowers_seven⟩

-- `IsSumOfPosNthPowers` likewise, via the equivalence
example : IsSumOfPosNthPowers 2 4 7 ∧ ¬ IsSumOfPosNthPowers 2 3 7 :=
  ⟨(isSumOfNthPowers_iff_isSumOfPosNthPowers (by norm_num)).mp isSumOfNthPowers_seven,
   fun h => not_isSumOfNthPowers_seven
     ((isSumOfNthPowers_iff_isSumOfPosNthPowers (by norm_num)).mpr h)⟩

-- the equivalence is not `True ↔ True`: both sides fail at `s = 3`
example : ¬ IsSumOfNthPowers 2 3 7 ∧ ¬ IsSumOfPosNthPowers 2 3 7 :=
  ⟨not_isSumOfNthPowers_seven, fun h => not_isSumOfNthPowers_seven
    ((isSumOfNthPowers_iff_isSumOfPosNthPowers (by norm_num)).mpr h)⟩

-- `WaringAdmissible` holds somewhere and fails somewhere, at the same `n`
example : WaringAdmissible 2 4 ∧ ¬ WaringAdmissible 2 3 :=
  ⟨waringAdmissible_two_four, not_waringAdmissible_two_three⟩

-- the `∃ s, WaringAdmissible n s` hypothesis of `idealWaring_le_waringG` and of
-- `waringAdmissible_iff_waringG_le` is inhabited at `n = 2`, jointly with `n ≠ 0`
example : (2 : ℕ) ≠ 0 ∧ ∃ s, WaringAdmissible 2 s := ⟨by norm_num, 4, waringAdmissible_two_four⟩

-- and it fails at `n = 0`, which is exactly the guard
example : ¬ ∃ s, WaringAdmissible 0 s := fun ⟨s, hs⟩ => not_waringAdmissible_zero s hs

-- `waringAdmissible_iff_waringG_le` is a genuine `↔`: true at `s = 4`, false at `s = 3`
example : WaringAdmissible 2 4 ↔ waringG 2 ≤ 4 :=
  waringAdmissible_iff_waringG_le ⟨4, waringAdmissible_two_four⟩
example : ¬ (waringG 2 ≤ 3) := by rw [waringG_two]; norm_num

-- `idealWaring_le_of_waringAdmissible` is sharp at `n = 2`: `idealWaring 2 = 4 = g(2)`
example : idealWaring 2 = 4 := by decide
example : idealWaring 2 = waringG 2 := by rw [waringG_two]; decide

-- `WaringTight` is inhabited and its statement is not trivially true: at `n = 3`
-- the inequality `3 + 3 ≤ 8` has genuine slack, while `n = 1` is the tight case `2 ≤ 2`
example : WaringTight 1 ∧ WaringTight 3 := ⟨by decide, by decide⟩

-- the archived identity is consistent with the two values proved outright
example : idealWaring 1 = 1 ∧ idealWaring 2 = 4 := ⟨by decide, by decide⟩

-- the hypotheses of `two_pow_add_le_of_isSumOfNthPowers` are jointly inhabited, and
-- there the bound `2 ^ n + q ≤ s + 2` is an equality — the lemma is sharp, not slack
example : (2 : ℕ) ≠ 0 ∧ 2 ^ 2 * 2 ≤ 3 ^ 2 ∧ 7 + 1 = 2 ^ 2 * 2 ∧ IsSumOfNthPowers 2 4 7 :=
  ⟨by norm_num, by norm_num, by norm_num, isSumOfNthPowers_seven⟩
example : 2 ^ 2 + 2 = 4 + 2 := by norm_num

-- the hypotheses of `idealWaring_le_of_waringAdmissible` are jointly inhabited, and
-- there too the conclusion `idealWaring n ≤ s` is an equality
example : (2 : ℕ) ≠ 0 ∧ WaringAdmissible 2 4 := ⟨by norm_num, waringAdmissible_two_four⟩
example : idealWaring 2 ≤ 4 :=
  idealWaring_le_of_waringAdmissible (by norm_num) waringAdmissible_two_four

-- **the archived `sorry`'s conclusion is discharged outright at `n = 1` and `n = 2`**,
-- so `waringAdmissible_idealWaring` is not asserting something already known false
example : WaringAdmissible 1 (idealWaring 1) := by
  rw [show idealWaring 1 = 1 by decide]; exact waringAdmissible_one_one
example : WaringAdmissible 2 (idealWaring 2) := by
  rw [show idealWaring 2 = 4 by decide]; exact waringAdmissible_two_four

-- **the `n ≠ 0` guard on the archived `sorry` is load-bearing**: without it the
-- statement would be false, since `idealWaring 0 = 0` and no `s` works at exponent `0`
example : ¬ WaringAdmissible 0 (idealWaring 0) := not_waringAdmissible_zero (idealWaring 0)
example : idealWaring 0 = 0 ∧ waringG 0 = 0 := ⟨by decide, waringG_zero⟩

/-! ## Signature audit -/

#check @IsSumOfNthPowers
#check @IsSumOfPosNthPowers
#check @IsSumOfNthPowers.mono
#check @isSumOfNthPowers_iff_isSumOfPosNthPowers
#check @WaringAdmissible
#check @WaringAdmissible.mono
#check @waringAdmissible_one_one
#check @waringAdmissible_two_four
#check @not_waringAdmissible_zero
#check @waringG
#check @waringG_le
#check @waringAdmissible_waringG
#check @waringAdmissible_iff_waringG_le
#check @waringG_zero
#check @idealWaring
#check @idealWaring_terms
#check @three_pow_div_two_pow_eq_floor
#check @idealWaring_eq_floor
#check @idealWaring_add_two
#check @two_pow_add_le_of_isSumOfNthPowers
#check @idealWaring_le_of_waringAdmissible
#check @idealWaring_le_waringG
#check @not_isSumOfNthPowers_seven
#check @isSumOfNthPowers_seven
#check @not_isSumOfNthPowers_twentyThree
#check @isSumOfNthPowers_twentyThree
#check @not_isSumOfNthPowers_seventyNine
#check @isSumOfNthPowers_seventyNine
#check @not_waringAdmissible_two_three
#check @waringG_one
#check @waringG_two
#check @WaringTight
#check @two_pow_mul_div_add_mod
#check @waringTight_of_mem_range
#check @waringAdmissible_idealWaring
#check @waringG_eq_idealWaring

/-! ## Axiom audit

Everything is `{propext, Classical.choice, Quot.sound}` or a subset of it, except
`waringAdmissible_idealWaring` — the single intended `sorry` — and
`waringG_eq_idealWaring`, which is assembled from it. -/

#print axioms IsSumOfNthPowers.mono
#print axioms isSumOfNthPowers_iff_isSumOfPosNthPowers
#print axioms WaringAdmissible.mono
#print axioms waringAdmissible_one_one
#print axioms waringAdmissible_two_four
#print axioms not_waringAdmissible_zero
#print axioms waringG_le
#print axioms waringAdmissible_waringG
#print axioms waringAdmissible_iff_waringG_le
#print axioms waringG_zero
#print axioms idealWaring_terms
#print axioms three_pow_div_two_pow_eq_floor
#print axioms idealWaring_eq_floor
#print axioms idealWaring_add_two
#print axioms count_two_mul_add_count_one
#print axioms two_pow_add_le_of_isSumOfNthPowers
#print axioms idealWaring_le_of_waringAdmissible
#print axioms idealWaring_le_waringG
#print axioms not_isSumOfNthPowers_seven
#print axioms isSumOfNthPowers_seven
#print axioms not_isSumOfNthPowers_twentyThree
#print axioms isSumOfNthPowers_twentyThree
#print axioms not_isSumOfNthPowers_seventyNine
#print axioms isSumOfNthPowers_seventyNine
#print axioms not_waringAdmissible_two_three
#print axioms waringG_one
#print axioms waringG_two
#print axioms two_pow_mul_div_add_mod
#print axioms waringTight_of_mem_range
#print axioms waringAdmissible_idealWaring
#print axioms waringG_eq_idealWaring

end A002804
