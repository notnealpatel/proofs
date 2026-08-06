import Mathlib

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

/-! ## The equation -/

/-- **Brocard's equation.**  `IsBrown n m` says that the pair `(n, m)` solves `n! + 1 = m²`.
Pickover calls such a pair a pair of *Brown numbers*; `A146968` lists the `n`, `A216071` the
`m`, and `A085692` the common value `n! + 1 = m²`. -/
def IsBrown (n m : ℕ) : Prop := n ! + 1 = m ^ 2

instance instDecidableIsBrown (n m : ℕ) : Decidable (IsBrown n m) :=
  inferInstanceAs (Decidable (n ! + 1 = m ^ 2))

/-- Unfolding lemma for `IsBrown`; the definition is the equation itself. -/
theorem isBrown_def (n m : ℕ) : IsBrown n m ↔ n ! + 1 = m ^ 2 := Iff.rfl

/-! ## The three known solutions (`decide`)

These certify the `%S` fields of all three cross-referenced sequences: A146968 `4,5,7`,
A216071 `5,11,71`, A085692 `25,121,5041`. -/

/-- Ground check, A146968 `a(1) = 4` and A216071 `a(1) = 5`: `4! + 1 = 25 = 5²`. -/
theorem isBrown_four : IsBrown 4 5 := by decide

/-- Ground check, A146968 `a(2) = 5` and A216071 `a(2) = 11`: `5! + 1 = 121 = 11²`. -/
theorem isBrown_five : IsBrown 5 11 := by decide

/-- Ground check, A146968 `a(3) = 7` and A216071 `a(3) = 71`: `7! + 1 = 5041 = 71²`.  This is
the OEIS `%e` line "7! + 1 = 5041 = 71^2, hence 7 is in the sequence". -/
theorem isBrown_seven : IsBrown 7 71 := by decide

/-- Ground check against the `%S` and `%e` fields of A085692: the three squares are
`25, 121, 5041`. -/
theorem factorial_add_one_eq : 4 ! + 1 = 25 ∧ 5 ! + 1 = 121 ∧ 7 ! + 1 = 5041 := by decide

/-- Negative ground checks: `IsBrown` is not satisfied by near misses. -/
theorem not_isBrown_six : ¬ IsBrown 6 27 ∧ ¬ IsBrown 6 26 ∧ ¬ IsBrown 4 6 := by decide

/-! ## Elementary structure of the equation -/

/-- Brocard's equation forces `m ≠ 0`, since `n! + 1 ≥ 2 > 0 = 0²`. -/
theorem ne_zero_of_isBrown {n m : ℕ} (h : IsBrown n m) : m ≠ 0 := by
  rintro rfl
  rw [isBrown_def] at h
  have hz : (0 : ℕ) ^ 2 = 0 := by norm_num
  rw [hz] at h
  omega

/-- For a fixed `n` at most one `m` solves Brocard's equation.  This is the content of the
A146968 `%Y` line "A085692, A146968, A216071 are all essentially the same sequence". -/
theorem isBrown_unique {n m m' : ℕ} (h : IsBrown n m) (h' : IsBrown n m') : m = m' :=
  Nat.pow_left_injective (by norm_num) (((isBrown_def n m).mp h).symm.trans ((isBrown_def n m').mp h'))

/-- A solution of Brocard's equation exhibits `n! + 1` as a perfect square. -/
theorem isSquare_of_isBrown {n m : ℕ} (h : IsBrown n m) : IsSquare (n ! + 1) :=
  (isSquare_iff_exists_sq _).mpr ⟨m, (isBrown_def n m).mp h⟩

/-- Conversely, if `n! + 1` is a perfect square then `n` is a Brocard index. -/
theorem exists_isBrown_of_isSquare {n : ℕ} (h : IsSquare (n ! + 1)) : ∃ m, IsBrown n m :=
  (isSquare_iff_exists_sq _).mp h

/-- **Factorisation form.**  Writing `m = k + 1`, Brocard's equation `n! + 1 = m²` becomes
`n! = k(k+2)`, which is `n! = (m-1)(m+1)` with no truncated `ℕ` subtraction.  This is also
the shape in which Erdős Problem 398 states it, `n! = x² - 1`. -/
theorem isBrown_succ_iff (n k : ℕ) : IsBrown n (k + 1) ↔ n ! = k * (k + 2) := by
  rw [isBrown_def]
  have e : (k + 1) ^ 2 = k * (k + 2) + 1 := by ring
  constructor
  · intro h
    exact Nat.add_right_cancel (h.trans e)
  · intro h
    rw [e, h]

/-- Every solution has `m = k + 1` for some `k` with `n! = k(k+2)`. -/
theorem exists_succ_of_isBrown {n m : ℕ} (h : IsBrown n m) :
    ∃ k, m = k + 1 ∧ n ! = k * (k + 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by have hm := ne_zero_of_isBrown h; omega⟩
  exact ⟨k, rfl, (isBrown_succ_iff n k).mp h⟩

/-- **Pronic form.**  For `2 ≤ n` the number `n! + 1` is a perfect square exactly when `n!`
is four times a pronic number, `n! = 4·j·(j+1)`; the corresponding solution is `m = 2j + 1`.
The hypothesis `2 ≤ n` is what makes `n!` even, hence `m` odd.  At `n = 4, 5, 7` the
witnesses are `j = 2, 5, 35`, the three values in the Erdős-398 comment quoted in the file
header. -/
theorem isBrown_iff_pronic {n : ℕ} (hn : 2 ≤ n) :
    (∃ m, IsBrown n m) ↔ ∃ j, n ! = 4 * (j * (j + 1)) := by
  constructor
  · rintro ⟨m, hm⟩
    rw [isBrown_def] at hm
    obtain ⟨t, ht⟩ : 2 ∣ n ! := Nat.dvd_factorial (by norm_num) hn
    have hsq : m ^ 2 = 2 * t + 1 := by rw [← hm, ht]
    have hoddm : Odd m := by
      have hmm : Odd (m * m) := by rw [← pow_two]; exact ⟨t, hsq⟩
      exact (Nat.odd_mul.mp hmm).1
    obtain ⟨j, hj⟩ := hoddm
    refine ⟨j, ?_⟩
    have e : (2 * j + 1) ^ 2 = 4 * (j * (j + 1)) + 1 := by ring
    rw [hj, e] at hm
    exact Nat.add_right_cancel hm
  · rintro ⟨j, hj⟩
    refine ⟨2 * j + 1, ?_⟩
    rw [isBrown_def]
    have e : (2 * j + 1) ^ 2 = 4 * (j * (j + 1)) + 1 := by ring
    rw [e, hj]

/-- Ground check for `isBrown_iff_pronic`: the three known solutions in pronic form, with
`j = 2, 5, 35` and `m = 2j + 1 = 5, 11, 71`. -/
theorem pronic_known :
    4 ! = 4 * (2 * (2 + 1)) ∧ 5 ! = 4 * (5 * (5 + 1)) ∧ 7 ! = 4 * (35 * (35 + 1)) := by decide

/-! ## Divisibility constraints -/

/-- **Every prime `p ≤ n` divides `m - 1` or `m + 1`.**  In the `m = k + 1` parametrisation
of `isBrown_succ_iff`: `p ∣ k` or `p ∣ k + 2`. -/
theorem prime_dvd_or_dvd_of_isBrown {n k p : ℕ} (hp : Nat.Prime p) (hpn : p ≤ n)
    (h : IsBrown n (k + 1)) : p ∣ k ∨ p ∣ k + 2 := by
  have hfac : n ! = k * (k + 2) := (isBrown_succ_iff n k).mp h
  have hdvd : p ∣ k * (k + 2) := by
    rw [← hfac]
    exact Nat.dvd_factorial hp.pos hpn
  exact (Nat.Prime.dvd_mul hp).mp hdvd

/-- For an *odd* prime `p ≤ n` exactly one of `k`, `k + 2` is divisible by `p`: the two
differ by `2`, so a common odd prime factor would divide `2`. -/
theorem prime_dvd_xor_dvd_of_isBrown {n k p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (hpn : p ≤ n) (h : IsBrown n (k + 1)) :
    (p ∣ k ∧ ¬ p ∣ k + 2) ∨ (¬ p ∣ k ∧ p ∣ k + 2) := by
  have hne : ¬ (p ∣ k ∧ p ∣ k + 2) := by
    rintro ⟨h1, h2⟩
    have hsub : k + 2 - k = 2 := by omega
    have h3 : p ∣ 2 := by
      rw [← hsub]
      exact Nat.dvd_sub h2 h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
  rcases prime_dvd_or_dvd_of_isBrown hp hpn h with h1 | h2
  · exact Or.inl ⟨h1, fun h2 => hne ⟨h1, h2⟩⟩
  · exact Or.inr ⟨fun h1 => hne ⟨h1, h2⟩, h2⟩

/-- **Radical of the pronic factor is the primorial.**  If `n! = 4·j·(j+1)` then the primes
dividing `j(j+1)` are exactly the primes `≤ n`.  This is the first half of the Erdős-398
comment of "Dogmachine" quoted in the file header ("the radical of `n(n+1)` is equal to a
primorial").  The hypothesis already forces `4 ≤ n`, so no lower bound on `n` is assumed. -/
theorem primeFactors_pronic_eq {n j : ℕ} (h : n ! = 4 * (j * (j + 1))) :
    (j * (j + 1)).primeFactors = Nat.primesBelow (n + 1) := by
  have hfpos : 0 < 4 * (j * (j + 1)) := by rw [← h]; exact Nat.factorial_pos n
  have hpos : 0 < j * (j + 1) := by omega
  ext p
  rw [Nat.mem_primeFactors, Nat.mem_primesBelow]
  constructor
  · rintro ⟨hp, hdvd, -⟩
    refine ⟨?_, hp⟩
    have hfac : p ∣ n ! := by
      rw [h]
      exact dvd_mul_of_dvd_right hdvd 4
    exact Nat.lt_succ_of_le ((Nat.Prime.dvd_factorial hp).mp hfac)
  · rintro ⟨hlt, hp⟩
    refine ⟨hp, ?_, hpos.ne'⟩
    have hpn : p ≤ n := Nat.lt_succ_iff.mp hlt
    have hdvd : p ∣ 4 * (j * (j + 1)) := by
      rw [← h]
      exact Nat.dvd_factorial hp.pos hpn
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h4 | hX
    · have hfour : (4 : ℕ) = 2 * 2 := by norm_num
      rw [hfour] at h4
      have h2 : p ∣ 2 := by
        rcases (Nat.Prime.dvd_mul hp).mp h4 with hl | hr
        · exact hl
        · exact hr
      have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
      subst hp2
      exact (Nat.even_mul_succ_self j).two_dvd
    · exact hX

/-! ## The verified range `n ≤ 30` (`decide`)

`Nat.sqrt` is defined by well-founded recursion and therefore does not reduce in the kernel,
so no integer square root is computed anywhere below.  Instead each non-solution `n` is
discharged by naming the integer `a = ⌊√(n!+1)⌋` and checking the two strict inequalities
`a² < n! + 1 < (a+1)²` by kernel reduction; `not_isSquare_of_lt_of_lt` turns that pair into
non-squareness.  The witnesses were computed with `python3` (`math.isqrt`); no `sage` is
installed in this environment.  They are *not* trusted: both inequalities are re-checked by
`decide` at each use site. -/

/-- If `N` lies strictly between two consecutive squares then `N` is not a perfect square. -/
theorem not_isSquare_of_lt_of_lt {N a : ℕ} (h₁ : a * a < N) (h₂ : N < (a + 1) * (a + 1)) :
    ¬ IsSquare N := by
  rintro ⟨m, rfl⟩
  have hlt : a < m := Nat.mul_self_lt_mul_self_iff.mp h₁
  have hgt : m < a + 1 := Nat.mul_self_lt_mul_self_iff.mp h₂
  omega

/-- **Verified range.**  For `n ≤ 30` the number `n! + 1` is a perfect square only at
`n = 4, 5, 7`.  Kernel reduction throughout; no number appearing in the proof exceeds
`(⌊√(30!+1)⌋ + 1)² ≈ 2.7 · 10^32`. -/
theorem eq_of_isSquare_factorial_add_one_of_le {n : ℕ} (hn : n ≤ 30)
    (h : IsSquare (n ! + 1)) : n = 4 ∨ n = 5 ∨ n = 7 := by
  interval_cases n
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 1) (by decide) (by decide))
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 1) (by decide) (by decide))
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 1) (by decide) (by decide))
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 2) (by decide) (by decide))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 26) (by decide) (by decide))
  · exact Or.inr (Or.inr rfl)
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 200) (by decide) (by decide))
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 602) (by decide) (by decide))
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 1904) (by decide) (by decide))
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 6317) (by decide) (by decide))
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 21886) (by decide) (by decide))
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 78911) (by decide) (by decide))
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 295259) (by decide) (by decide))
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 1143535) (by decide) (by decide))
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 4574143) (by decide) (by decide))
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 18859677) (by decide) (by decide))
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 80014834) (by decide) (by decide))
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 348776576) (by decide) (by decide))
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 1559776268) (by decide) (by decide))
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 7147792818) (by decide) (by decide))
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 33526120082) (by decide) (by decide))
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 160785623545) (by decide) (by decide))
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 787685471322) (by decide) (by decide))
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 3938427356614) (by decide) (by decide))
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 20082117944245) (by decide) (by decide))
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 104349745809073) (by decide) (by decide))
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 552166953567228) (by decide) (by decide))
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 2973510046012910) (by decide) (by decide))
  · exact absurd h (not_isSquare_of_lt_of_lt (a := 16286585271694955) (by decide) (by decide))

/-- **Verified range, pair form.**  For `n ≤ 30` the only Brown pairs are the three known
ones. -/
theorem pair_eq_of_isBrown_of_le {n m : ℕ} (hn : n ≤ 30) (h : IsBrown n m) :
    (n, m) = (4, 5) ∨ (n, m) = (5, 11) ∨ (n, m) = (7, 71) := by
  rcases eq_of_isSquare_factorial_add_one_of_le hn (isSquare_of_isBrown h) with rfl | rfl | rfl
  · exact Or.inl (by rw [isBrown_unique h isBrown_four])
  · exact Or.inr (Or.inl (by rw [isBrown_unique h isBrown_five]))
  · exact Or.inr (Or.inr (by rw [isBrown_unique h isBrown_seven]))

/-! ## The archived conjecture -/

/-- The set of all solution pairs of Brocard's equation `n! + 1 = m²`. -/
def solutions : Set (ℕ × ℕ) := {p | IsBrown p.1 p.2}

/-- Membership in `solutions` is the equation itself. -/
theorem mem_solutions {p : ℕ × ℕ} : p ∈ solutions ↔ IsBrown p.1 p.2 := Iff.rfl

/-- **Brocard's problem**, in the form conjectured by Erdős: `(4,5)`, `(5,11)` and `(7,71)`
are the only solutions of `n! + 1 = m²`.  Stated as a `Prop`-valued definition so that its
consequences below can be derived from it as a hypothesis, `sorry`-free. -/
def BrocardConjecture : Prop :=
  ∀ n m : ℕ, IsBrown n m → (n, m) = (4, 5) ∨ (n, m) = (5, 11) ∨ (n, m) = (7, 71)

/-- The three known Brown pairs really are solutions.  In particular `solutions` is nonempty
and `BrocardConjecture` is not the assertion that some empty set is empty. -/
theorem known_subset_solutions : ({(4, 5), (5, 11), (7, 71)} : Set (ℕ × ℕ)) ⊆ solutions := by
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact isBrown_four
  · exact isBrown_five
  · exact isBrown_seven

/-- `BrocardConjecture` says exactly that `solutions` is the three-element set of known Brown
pairs.  `sorry`-free: the `⊇` half is `known_subset_solutions`, the `⊆` half is the
conjecture. -/
theorem brocardConjecture_iff_solutions :
    BrocardConjecture ↔ solutions = {(4, 5), (5, 11), (7, 71)} := by
  constructor
  · intro H
    refine Set.Subset.antisymm (fun p hp => ?_) known_subset_solutions
    obtain ⟨n, m⟩ := p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact H n m hp
  · intro H n m hnm
    have hmem : (n, m) ∈ solutions := hnm
    rw [H] at hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem

/-- The conjecture implies that Brocard's equation has only finitely many solutions —
the conclusion Overholt derives from a weak form of the abc conjecture.  `sorry`-free: the
conjecture is a hypothesis. -/
theorem finite_solutions_of_brocardConjecture (H : BrocardConjecture) : solutions.Finite := by
  rw [brocardConjecture_iff_solutions.mp H]
  exact ((Set.finite_singleton ((7 : ℕ), (71 : ℕ))).insert ((5 : ℕ), (11 : ℕ))).insert
    ((4 : ℕ), (5 : ℕ))

/-- Under the conjecture, **A146968** is exactly `{4, 5, 7}`. -/
theorem indices_eq_of_brocardConjecture (H : BrocardConjecture) :
    {n : ℕ | ∃ m, IsBrown n m} = {4, 5, 7} := by
  ext n
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨m, hm⟩
    rcases H n m hm with hp | hp | hp
    · exact Or.inl (congrArg Prod.fst hp)
    · exact Or.inr (Or.inl (congrArg Prod.fst hp))
    · exact Or.inr (Or.inr (congrArg Prod.fst hp))
  · rintro (rfl | rfl | rfl)
    · exact ⟨5, isBrown_four⟩
    · exact ⟨11, isBrown_five⟩
    · exact ⟨71, isBrown_seven⟩

/-- Under the conjecture, **A216071** is exactly `{5, 11, 71}`. -/
theorem values_eq_of_brocardConjecture (H : BrocardConjecture) :
    {m : ℕ | ∃ n, IsBrown n m} = {5, 11, 71} := by
  ext m
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨n, hm⟩
    rcases H n m hm with hp | hp | hp
    · exact Or.inl (congrArg Prod.snd hp)
    · exact Or.inr (Or.inl (congrArg Prod.snd hp))
    · exact Or.inr (Or.inr (congrArg Prod.snd hp))
  · rintro (rfl | rfl | rfl)
    · exact ⟨4, isBrown_four⟩
    · exact ⟨5, isBrown_five⟩
    · exact ⟨7, isBrown_seven⟩

/-- Under the conjecture, **A085692** is exactly `{25, 121, 5041}`: the perfect squares of
the form `n! + 1`. -/
theorem squares_eq_of_brocardConjecture (H : BrocardConjecture) :
    {s : ℕ | IsSquare s ∧ ∃ n, s = n ! + 1} = {25, 121, 5041} := by
  ext s
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hsq, n, rfl⟩
    obtain ⟨m, hm⟩ := exists_isBrown_of_isSquare hsq
    rcases H n m hm with hp | hp | hp
    · have hn : n = 4 := congrArg Prod.fst hp
      subst hn
      exact Or.inl (by decide)
    · have hn : n = 5 := congrArg Prod.fst hp
      subst hn
      exact Or.inr (Or.inl (by decide))
    · have hn : n = 7 := congrArg Prod.fst hp
      subst hn
      exact Or.inr (Or.inr (by decide))
  · rintro (rfl | rfl | rfl)
    · exact ⟨⟨5, by decide⟩, 4, by decide⟩
    · exact ⟨⟨11, by decide⟩, 5, by decide⟩
    · exact ⟨⟨71, by decide⟩, 7, by decide⟩

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

/-! ## Satisfiability of every hypothesis, and non-vacuity

Each theorem above with hypotheses is instantiated below at a single concrete model in which
all of its hypotheses hold simultaneously, so that none of them is proved from a contradiction.
-/

/-- `IsBrown` is satisfiable and refutable: `decide` separates solutions from near misses. -/
example : IsBrown 4 5 ∧ IsBrown 5 11 ∧ IsBrown 7 71 ∧ ¬ IsBrown 6 26 ∧ ¬ IsBrown 8 200 := by
  decide

/-- `solutions` is inhabited, and does not contain everything. -/
example : ((4 : ℕ), (5 : ℕ)) ∈ solutions ∧ ((6 : ℕ), (26 : ℕ)) ∉ solutions := by
  refine ⟨isBrown_four, fun h => ?_⟩
  have h' : IsBrown 6 26 := h
  exact absurd h' (by decide)

/-- `ne_zero_of_isBrown` fires on a genuine solution. -/
example : (5 : ℕ) ≠ 0 := ne_zero_of_isBrown isBrown_four

/-- `isBrown_unique`'s two hypotheses are jointly satisfiable, at `n = 7`. -/
example : (71 : ℕ) = 71 := isBrown_unique isBrown_seven isBrown_seven

/-- `isSquare_of_isBrown` at a genuine solution. -/
example : IsSquare (7 ! + 1) := isSquare_of_isBrown isBrown_seven

/-- `exists_isBrown_of_isSquare` at the same point, closing the round trip. -/
example : ∃ m, IsBrown 7 m := exists_isBrown_of_isSquare (isSquare_of_isBrown isBrown_seven)

/-- `isBrown_succ_iff` at `n = 7`, `k = 70`: both sides hold. -/
example : (7 : ℕ)! = 70 * (70 + 2) := (isBrown_succ_iff 7 70).mp isBrown_seven

/-- `exists_succ_of_isBrown` at `n = 5`. -/
example : ∃ k, (11 : ℕ) = k + 1 ∧ 5 ! = k * (k + 2) := exists_succ_of_isBrown isBrown_five

/-- `isBrown_iff_pronic`'s hypothesis `2 ≤ n` and both sides of its conclusion hold jointly
at `n = 7`, with `j = 35`. -/
example : ∃ j, (7 : ℕ)! = 4 * (j * (j + 1)) :=
  (isBrown_iff_pronic (by norm_num)).mp ⟨71, isBrown_seven⟩

/-- The other direction of `isBrown_iff_pronic`, recovering `m = 2·35 + 1 = 71` from the
pronic witness `j = 35`. -/
example : ∃ m, IsBrown 7 m := (isBrown_iff_pronic (by norm_num)).mpr ⟨35, by decide⟩

/-- `prime_dvd_or_dvd_of_isBrown` at `n = 7`, `k = 70`, `p = 7`: all three hypotheses hold. -/
example : (7 : ℕ) ∣ 70 ∨ (7 : ℕ) ∣ 70 + 2 :=
  prime_dvd_or_dvd_of_isBrown (by norm_num) (le_refl 7) isBrown_seven

/-- `prime_dvd_xor_dvd_of_isBrown` at `n = 7`, `k = 70`, `p = 3`: the odd prime `3` divides
`72` and not `70`, so the disjunction lands on its right branch. -/
example : ((3 : ℕ) ∣ 70 ∧ ¬ (3 : ℕ) ∣ 70 + 2) ∨ (¬ (3 : ℕ) ∣ 70 ∧ (3 : ℕ) ∣ 70 + 2) :=
  prime_dvd_xor_dvd_of_isBrown (by norm_num) (by norm_num) (by norm_num) isBrown_seven

/-- `primeFactors_pronic_eq` at `n = 4`, `j = 2`: the radical of `2 · 3` is the primorial
`2 · 3`, i.e. the primes below `5`. -/
example : ((2 : ℕ) * (2 + 1)).primeFactors = Nat.primesBelow 5 :=
  primeFactors_pronic_eq (n := 4) (j := 2) (by decide)

/-- `primeFactors_pronic_eq` at `n = 7`, `j = 35`: the radical of `35 · 36 = 1260` is
`2 · 3 · 5 · 7 = 210`, the primorial of `7`. -/
example : ((35 : ℕ) * (35 + 1)).primeFactors = Nat.primesBelow 8 :=
  primeFactors_pronic_eq (n := 7) (j := 35) (by decide)

/-- The three primorials appearing above, as explicit finite sets. -/
example : Nat.primesBelow 5 = {2, 3} ∧ Nat.primesBelow 6 = {2, 3, 5} ∧
    Nat.primesBelow 8 = {2, 3, 5, 7} := by decide

/-- `not_isSquare_of_lt_of_lt` fires on a concrete non-square, `4 < 8 < 9`. -/
example : ¬ IsSquare 8 := not_isSquare_of_lt_of_lt (a := 2) (by decide) (by decide)

/-- `eq_of_isSquare_factorial_add_one_of_le`'s two hypotheses hold jointly at `n = 5`. -/
example : (5 : ℕ) = 4 ∨ (5 : ℕ) = 5 ∨ (5 : ℕ) = 7 :=
  eq_of_isSquare_factorial_add_one_of_le (n := 5) (by norm_num) (isSquare_of_isBrown isBrown_five)

/-- `pair_eq_of_isBrown_of_le`'s two hypotheses hold jointly at `(n, m) = (7, 71)`. -/
example : ((7 : ℕ), (71 : ℕ)) = (4, 5) ∨ ((7 : ℕ), (71 : ℕ)) = (5, 11) ∨
    ((7 : ℕ), (71 : ℕ)) = (7, 71) := pair_eq_of_isBrown_of_le (by norm_num) isBrown_seven

/-- The conjecture's conclusion set is genuinely three distinct pairs, so
`brocardConjecture_iff_solutions` is not an equality between two descriptions of `∅`. -/
example : ((4 : ℕ), (5 : ℕ)) ≠ (5, 11) ∧ ((5 : ℕ), (11 : ℕ)) ≠ (7, 71) ∧
    ((4 : ℕ), (5 : ℕ)) ≠ (7, 71) := by decide

/-- The five consequence theorems take `H : BrocardConjecture` as a hypothesis, so each of
them is `sorry`-free; the only way to discharge `H` in this file is `brocard`, and applying
one of them to `brocard` would produce a `sorryAx`-dependent term.  No such application is
made here, which is why `brocard` is the sole declaration below reporting `sorryAx`.  That
`H` is not a self-contradictory hypothesis is witnessed instead by
`brocardConjecture_iff_solutions`, whose right-hand side is a concrete three-element set
containing the three verified solutions. -/
example : ({(4, 5), (5, 11), (7, 71)} : Set (ℕ × ℕ)).Finite :=
  ((Set.finite_singleton ((7 : ℕ), (71 : ℕ))).insert ((5 : ℕ), (11 : ℕ))).insert
    ((4 : ℕ), (5 : ℕ))

end A146968

/-! ## Axiom audit

`A146968.brocard` carries the file's single intended `sorry` and reports `sorryAx` by
construction.  Every other declaration in the file — the full public surface is swept
below — must report a subset of `{propext, Classical.choice, Quot.sound}`. -/

#print axioms A146968.IsBrown
#print axioms A146968.instDecidableIsBrown
#print axioms A146968.isBrown_def
#print axioms A146968.isBrown_four
#print axioms A146968.isBrown_five
#print axioms A146968.isBrown_seven
#print axioms A146968.factorial_add_one_eq
#print axioms A146968.not_isBrown_six
#print axioms A146968.ne_zero_of_isBrown
#print axioms A146968.isBrown_unique
#print axioms A146968.isSquare_of_isBrown
#print axioms A146968.exists_isBrown_of_isSquare
#print axioms A146968.isBrown_succ_iff
#print axioms A146968.exists_succ_of_isBrown
#print axioms A146968.isBrown_iff_pronic
#print axioms A146968.pronic_known
#print axioms A146968.prime_dvd_or_dvd_of_isBrown
#print axioms A146968.prime_dvd_xor_dvd_of_isBrown
#print axioms A146968.primeFactors_pronic_eq
#print axioms A146968.not_isSquare_of_lt_of_lt
#print axioms A146968.eq_of_isSquare_factorial_add_one_of_le
#print axioms A146968.pair_eq_of_isBrown_of_le
#print axioms A146968.solutions
#print axioms A146968.mem_solutions
#print axioms A146968.BrocardConjecture
#print axioms A146968.known_subset_solutions
#print axioms A146968.brocardConjecture_iff_solutions
#print axioms A146968.finite_solutions_of_brocardConjecture
#print axioms A146968.indices_eq_of_brocardConjecture
#print axioms A146968.values_eq_of_brocardConjecture
#print axioms A146968.squares_eq_of_brocardConjecture
#print axioms A146968.brocard
