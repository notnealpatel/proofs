import Enumerative.Brocard

/-!
# Quarantined admissions

The original source and disclosure documentation is retained below as historical context.
Descriptions of the original file refer to its pre-quarantine layout: independent proven
infrastructure now lives in the imported production module; the admissions and their
admission-dependent consequences live only here. No proof closure is claimed.
-/


/-!
# OEIS A146968 / A085692 / A216071 — Brocard's problem, `n! + 1 = m²`

**Status.**  Archive file.  Every declaration is proved and kernel-checked except one
intended `sorry`, `A146968.brocard`, which carries the open problem itself.  No
`native_decide` is used anywhere in this file; every `decide` is kernel reduction.

## Primary sources, pinned verbatim

### OEIS A146968, raw record

Pulled 2026-08-05 from `https://oeis.org/search?q=id:A146968&fmt=text`; the `%N`, `%C`, `%Y`,
`%K` and program fields agree line-for-line with `goof oeis show A146968`.

```
%I A146968 #45 Sep 10 2025 21:02:34
%S A146968 4,5,7
%N A146968 Brocard's problem: positive integers n such that n!+1 = m^2.
%C A146968 No other terms below 10^9.
%C A146968 See A085692 for more comments and references. - _M. F. Hasler_, Nov 20 2018
%H A146968 Bruce C. Berndt and William F. Galway, <a href="https://web.archive.org/web/20110605041402/http://www.math.uiuc.edu/~berndt/articles/galway.pdf">On the Brocard-Ramanujan Diophantine Equation n!+1=m^2</a>, Ramanujan J. (March 2000) Vol. 4, Issue 1, 41-42.
%H A146968 Thomas Bloom, <a href="https://www.erdosproblems.com/398">Problem 398</a>, Erdős Problems.
%H A146968 Erdős problems database contributors, <a href="https://github.com/teorth/erdosproblems/blob/main/README.md#table">Erdős problem database</a>, see no. 398.
%H A146968 Apoloniusz Tyszka, <a href="https://philarchive.org/rec/TYSDAS">On sets X subset of N for which we know an algorithm that computes a threshold number t(X) in N such that X is infinite if and only if X contains an element greater than t(X)</a>, 2019.
%H A146968 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/BrocardsProblem.html">Brocard's Problem</a>.
%e A146968 7! + 1 = 5041 = 71^2, hence 7 is in the sequence. - _Klaus Brockhaus_, Nov 05 2008
%t A146968 Select[Range[10],IntegerQ[Sqrt[#!+1]]&] (* _Harvey P. Dale_, Jan 31 2015 *)
%Y A146968 A085692, A146968, A216071 are all essentially the same sequence. - _N. J. A. Sloane_, Sep 01 2012
%K A146968 bref,nonn,hard
%O A146968 1,1
%A A146968 Marco Bellaccini (marcomurk(AT)tele2.it), Nov 03 2008
%E A146968 Edited by _Max Alekseyev_, Feb 06 2010
```

### OEIS A085692, raw record (same pull)

```
%S A085692 25,121,5041
%N A085692 Brocard's problem: squares which can be written as n!+1 for some n.
%C A085692 Next term, if it exists, is greater than 10^850. - _Sascha Kurz_, Sep 22 2003
%C A085692 No more terms < 10^20000. - _David Wasserman_, Feb 08 2005
%C A085692 The problem of whether there are any other terms in this sequence, Brocard's problem, has been unsolved since 1876. The known calculations give a(4) > (10^9)! = factorial(10^9). - _Stefan Steinerberger_, Mar 19 2006
%C A085692 I wrote a similar program sieving against the 40 smallest primes larger than 4*10^9 and can report that a(4) > factorial(4*10^9+1). In other words, it's now known that the only n <= 4*10^9 for which n!+1 is a square are 4, 5 and 7. C source code available on request. - Tim Peters (tim.one(AT)comcast.net), Jul 02 2006
%C A085692 Robert Matson claims to have verified that 4, 5, and 7 are the only values of n <= 10^12 for which n!+1 is a square. This implies that the next term, if it exists, is greater than (10^12+1)! ~ 1.4*10^11565705518115. - _David Radcliffe_, Oct 28 2019
%D A085692 R. Guy, "Unsolved Problems in Number Theory", 3rd edition, D25
%F A085692 a(n) = A216071(n)^2 = A146968(n)!+1 = A038507(A146968(n)). - _M. F. Hasler_, Nov 20 2018
%e A085692    5^2 =   25 = 4! + 1;
%e A085692   11^2 =  121 = 5! + 1;
%e A085692   71^2 = 5041 = 7! + 1.
%K A085692 nonn,bref
%O A085692 1,1
```

### OEIS A216071, raw record (same pull)

```
%S A216071 5,11,71
%N A216071 Brocard's problem: positive integers m such that m^2 = n! + 1 for some n.
%F A216071 a(n) = A000196(A085692(n)) = A000196(A038507(A146968(n))) where A000196 = sqrt and A038507(n) = n! + 1. - _M. F. Hasler_, Nov 20 2018
%K A216071 nonn,hard,bref
%O A216071 1,1
```

### Erdős Problem 398, from `goof erdos fetch 398` (pulled 2026-08-05)

*Statement* (LaTeX exactly as the database serves it):

> Are the only solutions to \\[n!=x^2-1\\] when $n=4,5,7$?

*Body*, verbatim:

> The Brocard-Ramanujan conjecture. Erd\\H{o}s and Graham describe this as an old conjecture,
> and write it 'is almost certainly true but it is intractable at present'.
>
> Overholt \\cite{Ov93} has shown that this has only finitely many solutions assuming a weak
> form of the ABC conjecture.
>
> There are no other solutions below $10^9$ (see the OEIS page).
>
> Naciri \\cite{Na25} has proved that there are only finitely many solutions if $x\\pm 1$ is
> either $k$-free (for some $k\\geq 2$) or a prime power (and Cambie explains both facts in
> the comments), and that if $x\\pm 1$ is $7$-free then $n=4,5,7$ give the only solutions.

*References*, verbatim:

> [Na25] A. M. Naciri, *On the Brocard-Ramanujan equation with $7$-free integers and prime
> powers*. Integers (2025), A71.
>
> [Ov93] Overholt, Marius, *The Diophantine equation $n!+1=m^2$*. Bull. London Math. Soc.
> (1993), 104.

*Comment* by "Dogmachine", 23:32 on 28 Mar 2026, verbatim (site marked "The site has been
updated to address this comment."):

> Each solution corresponds to a number $n$ such that the radical of $n(n+1)$ is equal to a
> primorial. From the known ones, we get the values $n=2,5,35$. Numbers $n$ with this
> property are tracked by OEIS sequence A141399. Note that any proof that this sequence is
> finite would settle the Brocard- Ramanujan equation. One might want to link this OEIS
> sequence here aswell.

*Comment* by "mysticflounder", 20:28 on 18 Apr 2026, verbatim (HTML entities resolved):

> quick note: the computational bound in the current note says $10^9$; the actual range
> checked is now $10^{15}$.
>
> Matson (2017) pushed it to $n \\leq 4 \\cdot 10^{11}$ using quadratic residues and Legendre
> symbols against large test primes. Epstein and Glickman (2020) extended that to
> $n \\leq 10^{15}$ with an optimized C++ implementation, code at
> https://github.com/jhg023/brocard
>
> Wikipedia (https://en.wikipedia.org/wiki/Brocard%27s_problem) reflects the $10^{15}$ figure

### Wikipedia, "Brocard's problem", from `goof wiki article "Brocard's problem"`

> **Brocard's problem** is a problem in mathematics that seeks integer values of $n$ such
> that $n!+1$ is a perfect square, where $n!$ is the factorial. Only three values of $n$ are
> known — 4, 5, 7 — and it is not known whether there are any more.
>
> More formally, it seeks pairs of integers $n$ and $m$ such that $n!+1 = m^2.$ The problem
> was posed by Henri Brocard in a pair of articles in 1876 and 1885, and independently in
> 1913 by Srinivasa Ramanujan.
>
> Pairs of the numbers $(n,m)$ that solve Brocard's problem were named **Brown numbers** by
> Clifford A. Pickover in his 1995 book *Keys to Infinity*, after learning of the problem
> from Kevin S. Brown. As of October 2022, there are only three known pairs of Brown
> numbers  [...]  Paul Erdős conjectured that no other solutions exist. Computational
> searches have found no further solutions with $n \\leq 10^{15}$.
>
> It would follow from the abc conjecture that there are only finitely many Brown numbers.

## Note on the computational bounds

The three sources give three different verified ranges — A146968 says `10^9`, A085692's 2006
and 2019 comments say `4·10^9` and `10^12`, and the Erdős-398 comment and Wikipedia say
`10^15`.  These are consistent (each is a weaker statement than the next); none of them is
formalized here.  The range this file verifies by kernel reduction is `n ≤ 30`, some thirteen
orders of magnitude short of the published `n ≤ 10^15`: at `n = 30` the numbers involved are
already `30! + 1 ≈ 2.7 · 10^32`, and `n!` grows super-exponentially, so kernel `decide` cannot
be pushed anywhere near `10^9`.  The verified range is a sanity anchor, not a contribution.

## What this file proves, and what it does not

Proved, `sorry`-free and kernel-checked:

* `isBrown_four`, `isBrown_five`, `isBrown_seven` — the three known Brown pairs `(4,5)`,
  `(5,11)`, `(7,71)`, by `decide`; and `factorial_add_one_eq`, the A085692 terms
  `25, 121, 5041`, and the A216071 terms `5, 11, 71`.
* `eq_of_isSquare_factorial_add_one_of_le` — for `n ≤ 30`, `n! + 1` is a perfect square only
  at `n = 4, 5, 7`.  Each of the 28 non-solutions is discharged by exhibiting the two
  consecutive squares that straddle `n! + 1` (`not_isSquare_of_lt_of_lt`), so no integer
  square root is ever computed; `Nat.sqrt` is defined by well-founded recursion and does not
  kernel-reduce.
* `isBrown_unique` — `m` is determined by `n`, which is why A146968, A085692 and A216071 are
  "essentially the same sequence" (`%Y`).
* `isBrown_succ_iff` — the factorisation form `n! = k(k+2)`, i.e. `n! = (m-1)(m+1)` written
  without truncated `ℕ` subtraction.
* `isBrown_iff_pronic` — for `2 ≤ n`, `n! + 1` is a square iff `n!` is four times a pronic
  number, `n! = 4·j·(j+1)`; the solution then has `m = 2j+1`.  At `n = 4, 5, 7` this gives
  `j = 2, 5, 35`, which are exactly the three values in the Erdős-398 comment of
  "Dogmachine" quoted above.
* `primeFactors_pronic_eq` — the other half of that comment: if `n! = 4·j·(j+1)` then the
  primes dividing `j(j+1)` are exactly the primes `≤ n`, i.e. the radical of `j(j+1)` is the
  primorial of `n`.
* `prime_dvd_or_dvd_of_isBrown`, `prime_dvd_xor_dvd_of_isBrown` — every prime `p ≤ n`
  divides `m-1` or `m+1`, and for odd `p` exactly one of the two.
* `brocardConjecture_iff_solutions`, `finite_solutions_of_brocardConjecture`,
  `indices_eq_of_brocardConjecture`, `values_eq_of_brocardConjecture`,
  `squares_eq_of_brocardConjecture` — the consequences of the conjecture, each proved from
  it *as a hypothesis* and therefore `sorry`-free: the conjecture is equivalent to
  `solutions = {(4,5), (5,11), (7,71)}`, it implies finiteness of the solution set, and it
  pins A146968 `= {4,5,7}`, A216071 `= {5,11,71}` and A085692 `= {25,121,5041}`.

The single intended `sorry`:

* `brocard : BrocardConjecture` — Brocard's problem itself, open since 1876.

**Deviations.**  Three results named by the sources are *not* formalized, and none of them is
archived as a second `sorry`, because each is a published theorem rather than a conjecture
and archiving a theorem as a `sorry` would misrepresent it:

* Overholt's `[Ov93]` finiteness under a weak abc conjecture;
* Naciri's `[Na25]` finiteness for `k`-free / prime-power `x ± 1`, and the unconditional
  `n = 4, 5, 7` for `7`-free `x ± 1`;
* the Berndt–Galway `n ≤ 10^9` verification and its successors.

They are listed as open items in the lane report.

## Structure

`IsBrown n m` is the equation `n! + 1 = m²` (Pickover's *Brown numbers*), with a `Decidable`
instance so that the OEIS terms are certified by `decide`.  `BrocardConjecture` is the
`Prop`-valued statement of the problem; `solutions` is the set of solution pairs.
-/

set_option autoImplicit false

open scoped Nat

namespace A146968

/-- **Brocard's problem** — the Brocard–Ramanujan conjecture, Erdős Problem 398:
`n! + 1 = m²` has only the solutions `(n, m) = (4,5), (5,11), (7,71)`.

**Status: open**, since Brocard posed it in 1876.  This is the single intended `sorry` of
the file, and the only declaration here that reports `sorryAx`.  Erdős and Graham write that
it "is almost certainly true but it is intractable at present"; Overholt `[Ov93]` derives
finiteness of the solution set from a weak form of the abc conjecture, and the equation has
been checked to `n ≤ 10^15`.

It is not vacuous: `known_subset_solutions` shows the three asserted pairs really are
solutions, `pair_eq_of_isBrown_of_le` proves the conjecture unconditionally for `n ≤ 30`,
and `brocardConjecture_iff_solutions` shows the statement is equivalent to a set equality
whose right-hand side has exactly three elements. -/
theorem brocard : BrocardConjecture := by
  -- Intended `sorry`: Brocard's problem, open since 1876 (Brocard 1876/1885; Ramanujan 1913;
  -- Erdős Problem 398; OEIS A146968, keyword `hard`).
  sorry

end A146968
