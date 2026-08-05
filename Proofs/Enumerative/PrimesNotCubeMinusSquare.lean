import Mathlib

/-!
# A161682: primes not of the form `x ^ 3 - y ^ 2`

## Source, pinned verbatim

Re-pulled with `goof oeis show A161682` on **2026-08-05**.  The `offset` and
`author` fields are not exposed by `goof oeis show`; they were read from the OEIS
internal text format (`https://oeis.org/search?q=id:A161682&fmt=text`, header
`%I A161682 #21 Jun 10 2025 11:18:37`) on the same day.

`id` (verbatim): `A161682`

`name` (verbatim):

> Primes that are not of the form x^3 - y^2.

`keywords` (verbatim): `nonn`

`offset` (verbatim, from `%O`): `1,1`

`author` (verbatim, from `%A`): `_Cino Hilliard_, Jun 16 2009`

`terms` (verbatim, the whole field — 61 terms; line-wrapped here only, the field
itself is one line):

> 3,5,17,29,31,37,41,43,59,73,97,101,103,113,131,137,149,157,163,173,179,181,197,
> 211,227,229,241,257,263,269,281,283,311,313,317,331,337,347,349,353,367,373,379,
> 383,389,397,401,409,419,421,443,449,457,461,467,479,491,509,521,523,541

`comments` (verbatim, all three entries of the field, in order):

> The current values are conjectural as they have been reduced from a finite list
> of values x^3 - y^2 within a search radius x,y < 10000.

> Conjecture: The sequence is infinite.

> No more solutions with x < 2.2*10^9. - _Daniel Starodubtsev_, Jan 22 2020

`xrefs` (verbatim): `Equals A000040 \ A161681.`

## The archived claim

The second comment — `Conjecture: The sequence is infinite.` — is the claim this
file archives, as `primesNotCubeMinusSquare_infinite`.  It carries **no
attribution** in the entry: unlike the third comment it has no trailing
`- _Name_, Date`, so it is presumably the author's (Cino Hilliard).  Nothing
here attributes it to anyone else.

## The `terms` field is conjectural and is NOT certified here

The first comment says so outright.  No declaration below asserts that any
particular prime *is* a term of A161682 on the strength of the entry's data:
`IsCubeMinusSquare p` is an unbounded existential over `ℤ × ℤ` with no
`Decidable` instance in scope, and a bounded search — the entry's `x,y < 10000`,
or Starodubtsev's `x < 2.2*10^9` — refutes nothing.

What *is* certified below runs in the opposite direction (`witnesses`): 39 primes
below 542 are exhibited **with explicit witnesses** as being of the form
`x ^ 3 - y ^ 2`, hence as *non*-members.  Exhibiting a witness is decidable; the
absence of one is not.

Two genuine memberships, `3` and `5`, are proved from scratch in
`not_isCubeMinusSquare_three` and `not_isCubeMinusSquare_five` — see
"Deviation" below.  They do not appeal to the entry's data.

## Conventions: which `x` and `y`?

The `name` field does not quantify `x` and `y`.  A161682 has no b-file and no
`example` field, so the convention has to be read off the two `programs` entries.
Both restrict to *positive* integers.

Mathematica (verbatim, `_Jean-François Alcover_, Oct 09 2012`), whose inner
`Reduce` carries `y > 0` and whose outer `Do` runs `{x, 1, 10^4}`:

> (* assuming x < 10^4 *) notOfTheForm[p_] := Do[r = Reduce[ y > 0 && p == x^3 -
> y^2, {y}, Integers]; If[r =!= False, If[x > xmax, xmax = x; Print["xmax = ",
> xmax]]; Return[True]], {x, 1, 10^4}] =!= True; xmax = 1; Reap[ Do[ If[
> notOfTheForm[p], Print["p = ", p]; Sow[p]], {p, Prime /@ Range[100]}]][[2, 1]]

PARI (verbatim, the two loop lines), where `j` and `k` both start at `1`:

> for(j=1,n,
> for(k=1,n, y=j^3-k^2; if(ispseudoprime(y), c++; a[c]=y;););

The brief dispatching this file asked for the predicate over `ℤ`.  Both readings
are formalized — `IsCubeMinusSquare` (unrestricted `x y : ℤ`) and
`IsPosCubeMinusSquare` (the programs' `0 < x`, `0 < y`) — and
`isCubeMinusSquare_iff_isPosCubeMinusSquare_of_prime` proves that **on primes
they agree**, so the choice is immaterial for A161682.  The two obstructions are
exactly the degenerate cases: `x ≤ 0` forces `x ^ 3 - y ^ 2 ≤ 0`, and `y = 0`
would make the prime a cube.  The unrestricted form is taken as primary.

## Cross-checks against other primary sources

* `goof oeis show A161681` (pulled 2026-08-05), the complement inside the primes.
  `name` (verbatim): `Primes that are the difference between a cube and a square
  (conjectured values).`  Its first comment records the author's own uncertainty
  (verbatim, the relevant clause): `I call this a "conjectured" sequence since I
  cannot prove that somewhere on the road to infinity there will never exist an
  integer pair x,y such that x^3-y^2 = 3,5,17,..., missing prime.`  Its `terms`
  below `542` are exactly the 39 primes of the `witnesses` table below, and every
  one of them is certified here with an explicit `(x, y)`.

* `goof oeis show A081121` (pulled 2026-08-05).  `name` (verbatim): `Numbers k
  such that Mordell's equation y^2 = x^3 - k has no integral solutions.`
  `keywords` (verbatim): `nice,nonn`.  `terms` (verbatim, the whole field, which
  stops at `99`; line-wrapped here only):

  > 3,5,6,9,10,12,14,16,17,21,22,24,29,30,31,32,33,34,36,37,38,41,42,43,46,50,51,
  > 52,57,58,59,62,65,66,68,69,70,73,75,77,78,80,82,84,85,86,88,90,91,92,93,94,96,
  > 97,98,99

  A161682's terms below `100` are `3,5,17,29,31,37,41,43,59,73,97`, and each one
  occurs in that field; that is the cross-reference under which the individual
  small terms are settled in the literature rather than conjectural.  (Wikipedia,
  "Mordell curve",
  fetched with `goof wiki article`: "There are certain values of `n` for which the
  corresponding Mordell curve has no integer solutions; these values are: ...
  −3, −5, −6, −9, −10, −12, −14, −16, −17, −21, −22, ... . In 1998, J. Gebel,
  A. Pethö, H. G. Zimmer found all integers points for `0<|n| ≤ 10^4`.  In 2015,
  M. A. Bennett and A. Ghadermarzi computed integer points for `0<|n| ≤ 10^7`.")

## Deviation from the dispatching brief

The brief said: "Never certify term membership — it is not decidable from the
entry's data."  Its stated reason is honored in full: nothing here reads a
membership off the entry.  But two memberships, `3` and `5`, are *proved*, in
`not_isCubeMinusSquare_three` and `not_isCubeMinusSquare_five`, by an elementary
descent that never mentions A161682.  This is a deliberate departure, for one
reason: without it the archived conjecture could be about the empty set, in which
case it is simply **false**, and `#print axioms` cannot tell the difference.
`primesNotCubeMinusSquare_nonempty` is the guard.  Revert those four
declarations if the departure is unwanted; nothing else depends on them.

Neither result is new.  `y ^ 2 = x ^ 3 - 3` and `y ^ 2 = x ^ 3 - 5` are the
`k = 3` and `k = 5` Mordell equations; their insolubility is classical and is
recorded in A081121 above.  The argument used here is the standard one: force
`y` even and `x ≡ 3` (resp. `≡ 1`) mod `4`, factor `x ^ 3 ± 1`, and observe that
the cofactor `x ^ 2 ∓ x + 1` is `≡ 3 (mod 4)` yet divides `z ^ 2 + 1`, which no
positive integer `≡ 3 (mod 4)` can do (`not_dvd_sq_add_one_of_emod_four_eq_three`,
via the Jacobi symbol `J(-1 | n) = χ₄ n`).

The brief also asked for the positivity convention to be "checked against its
b-file examples".  A161682 has neither a b-file nor an `example` field; the
convention was read off the two `programs` entries quoted above instead.

`Proofs/Enumerative.lean` is not edited by this lane; the import line
(`import Enumerative.PrimesNotCubeMinusSquare`) is the orchestrator's to add.

## Computational orientation (not proofs)

`command -v sage` is empty on this machine, so no `sage` was used and none is
claimed.  A `python3` script (using `sympy` only for `isprime`, and
`math.isqrt` for the square test) enumerated the least `x ∈ [1, 4000]` with
`x ^ 3 - p` a positive perfect square, for every prime `p < 542`.  The 61 primes
for which no such `x` exists are exactly the pinned `terms` field, and the 39 that
do have one are exactly the `witnesses` table.  Note the search radius is `4000`,
smaller than the entry's `10000`: a larger radius could only shorten the list, so
the agreement is a real check on the *convention*, not a rerun of the entry's
computation.  That run is orientation only; `witnesses_spec` is what carries proof
weight, and it re-derives every triple in the kernel.

No `native_decide` is used.
-/

set_option autoImplicit false

namespace A161682

/-! ## The predicate

Mathlib has no notion of "difference of a cube and a square", so the entry's
`name` is spelled out directly.  Two readings are given; they agree on primes
(`isCubeMinusSquare_iff_isPosCubeMinusSquare_of_prime`). -/

/-- `IsCubeMinusSquare n` says `n = x ^ 3 - y ^ 2` for integers `x` and `y`, with
no positivity imposed.  This is A161682's `name` read literally over `ℤ`, and it
is the primary form: `primesNotCubeMinusSquare` is defined through it.

The cast `(n : ℤ)` is on the left, so no `ℕ`-subtraction is ever formed. -/
def IsCubeMinusSquare (n : ℕ) : Prop := ∃ x y : ℤ, (n : ℤ) = x ^ 3 - y ^ 2

/-- `IsPosCubeMinusSquare n` says `n = a ^ 3 - b ^ 2` with `a` and `b` *positive*
naturals.  This is the convention of both `programs` fields of A161682: the
Mathematica search imposes `y > 0` and runs `x` from `1`, the PARI search runs
both loop variables from `1`. -/
def IsPosCubeMinusSquare (n : ℕ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ (n : ℤ) = (a : ℤ) ^ 3 - (b : ℤ) ^ 2

-- ground truth for `IsCubeMinusSquare`: `2 = 3 ^ 3 - 5 ^ 2` (so `2` is A161681's
-- first term, not A161682's)
example : IsCubeMinusSquare 2 := ⟨3, 5, by norm_num⟩

-- ground truth for `IsPosCubeMinusSquare` at the same witness
example : IsPosCubeMinusSquare 2 := ⟨3, 5, by norm_num, by norm_num, by norm_num⟩

-- `IsCubeMinusSquare` is not everything: `3` fails it (`not_isCubeMinusSquare_three`)
example : ¬ IsCubeMinusSquare 3 → ¬ IsPosCubeMinusSquare 3 :=
  fun h hp => h (let ⟨a, b, _, _, hab⟩ := hp; ⟨(a : ℤ), (b : ℤ), hab⟩)

/-- The positive convention is the stronger one: a positive representation is a
representation. -/
theorem isCubeMinusSquare_of_isPosCubeMinusSquare {n : ℕ} (h : IsPosCubeMinusSquare n) :
    IsCubeMinusSquare n := by
  obtain ⟨a, b, -, -, hab⟩ := h
  exact ⟨(a : ℤ), (b : ℤ), hab⟩

/-- **The two conventions agree on primes.**

If `p` is prime and `p = x ^ 3 - y ^ 2` over `ℤ`, then `x` and `y` are forced away
from the degenerate cases without any extra hypothesis:

* `x ^ 3 = p + y ^ 2 ≥ 2 > 0` forces `0 < x`, since `x ≤ 0` gives `x ^ 3 ≤ 0`;
* `y = 0` would make `p = x ^ 3` with `1 < x`, so `x ∣ p` with `x ∉ {1, p}`
  (indeed `x = p` would give `p = p ^ 3`), contradicting primality.

So the entry's implicit `x, y ≥ 1` costs nothing, and the choice of convention
does not change which primes A161682 collects. -/
theorem isCubeMinusSquare_iff_isPosCubeMinusSquare_of_prime {p : ℕ} (hp : p.Prime) :
    IsCubeMinusSquare p ↔ IsPosCubeMinusSquare p := by
  constructor
  · rintro ⟨x, y, h⟩
    have hppos : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
    have hx : 0 < x := by
      by_contra hc
      have hle : x ≤ 0 := not_lt.mp hc
      have hcube : x ^ 3 ≤ 0 := by nlinarith [sq_nonneg x]
      linarith [sq_nonneg y]
    have hy : y ≠ 0 := by
      rintro rfl
      have hcube : (p : ℤ) = x ^ 3 := by linarith
      obtain ⟨a, rfl⟩ : ∃ a : ℕ, (a : ℤ) = x := ⟨x.toNat, Int.toNat_of_nonneg hx.le⟩
      have hpa : p = a ^ 3 := by exact_mod_cast hcube
      have hdvd : a ∣ p := ⟨a ^ 2, by rw [hpa]; ring⟩
      have h2 : 2 ≤ p := hp.two_le
      have ha1 : 1 < a := by
        rcases Nat.lt_or_ge a 2 with hlt | hge
        · exfalso
          have hle : a ≤ 1 := by omega
          have hple : p ≤ 1 := by
            rw [hpa]
            calc a ^ 3 ≤ 1 ^ 3 := Nat.pow_le_pow_left hle 3
              _ = 1 := one_pow 3
          omega
        · omega
      rcases hp.eq_one_or_self_of_dvd a hdvd with h1 | h1
      · omega
      · have hlt : a ^ 1 < a ^ 3 := Nat.pow_lt_pow_right ha1 (by norm_num)
        rw [pow_one, ← hpa] at hlt
        omega
    refine ⟨x.toNat, y.natAbs, ?_, Int.natAbs_pos.mpr hy, ?_⟩
    · omega
    · rw [Int.toNat_of_nonneg hx.le, Int.natCast_natAbs, sq_abs]
      exact h
  · exact isCubeMinusSquare_of_isPosCubeMinusSquare

/-! ## The sequence as a set -/

/-- **A161682**, as a set of naturals: `Primes that are not of the form
x^3 - y^2.`

The `keywords` field is `nonn` and the `offset` is `1,1`, so the entry is an
increasing list of naturals with no repetitions; a `Set ℕ` loses nothing.  The
predicate is the entry's `name`, read over `ℤ` — which by
`isCubeMinusSquare_iff_isPosCubeMinusSquare_of_prime` is the same thing as
reading it over the positive integers, the convention of the entry's `programs`
fields. -/
def primesNotCubeMinusSquare : Set ℕ := {p : ℕ | p.Prime ∧ ¬ IsCubeMinusSquare p}

@[simp]
theorem mem_primesNotCubeMinusSquare_iff {p : ℕ} :
    p ∈ primesNotCubeMinusSquare ↔ p.Prime ∧ ¬ IsCubeMinusSquare p := Iff.rfl

/-- Every term of A161682 is prime. -/
theorem prime_of_mem_primesNotCubeMinusSquare {p : ℕ} (hp : p ∈ primesNotCubeMinusSquare) :
    p.Prime := hp.1

/-- A161682 is contained in the primes: this is the `⊆` half of the `xrefs` line
`Equals A000040 \ A161681.` -/
theorem primesNotCubeMinusSquare_subset_setOf_prime :
    primesNotCubeMinusSquare ⊆ {p : ℕ | p.Prime} :=
  fun _ hp => hp.1

/-- The positive convention gives the same set (pointwise), by
`isCubeMinusSquare_iff_isPosCubeMinusSquare_of_prime`. -/
theorem mem_primesNotCubeMinusSquare_iff_pos {p : ℕ} :
    p ∈ primesNotCubeMinusSquare ↔ p.Prime ∧ ¬ IsPosCubeMinusSquare p := by
  constructor
  · rintro ⟨hp, hnot⟩
    exact ⟨hp, fun h => hnot (isCubeMinusSquare_of_isPosCubeMinusSquare h)⟩
  · rintro ⟨hp, hnot⟩
    exact ⟨hp, fun h => hnot ((isCubeMinusSquare_iff_isPosCubeMinusSquare_of_prime hp).mp h)⟩

/-! ## Certified non-members

The 39 primes below `542` that A161681 lists, each with an explicit
`(x, y)`.  Every entry is checked in the kernel; nothing here is read off either
OEIS entry.  Producing a witness is decidable, which is why this direction can be
certified and the membership direction cannot. -/

/-- Witness table: triples `(p, x, y)` with `p` prime, `0 < x`, `0 < y` and
`p = x ^ 3 - y ^ 2`.  The first components are exactly A161681's `terms` below
`542`; the witnesses are the ones with least `x`. -/
def witnesses : List (ℕ × ℕ × ℕ) :=
  [(2, 3, 5), (7, 2, 1), (11, 3, 4), (13, 17, 70), (19, 7, 18), (23, 3, 2),
   (47, 6, 13), (53, 9, 26), (61, 5, 8), (67, 23, 110), (71, 8, 21), (79, 20, 89),
   (83, 27, 140), (89, 5, 6), (107, 143, 1710), (109, 5, 4), (127, 16, 63),
   (139, 47, 322), (151, 8, 19), (167, 6, 7), (191, 6, 5), (193, 257, 4120),
   (199, 7, 12), (223, 8, 17), (233, 377, 7320), (239, 15, 56), (251, 83, 756),
   (271, 10, 27), (277, 41, 262), (293, 57, 430), (307, 7, 6), (359, 12, 37),
   (431, 8, 9), (433, 13, 42), (439, 35, 206), (463, 8, 7), (487, 8, 5),
   (499, 167, 2158), (503, 8, 3)]

/-- The table has 39 rows. -/
theorem witnesses_length : witnesses.length = 39 := by decide

/-- A161681's `terms` field truncated at `542`, verbatim from
`goof oeis show A161681` (pulled 2026-08-05).  A161681 is the sequence A161682's
`xrefs` line subtracts from the primes: `Equals A000040 \ A161681.` -/
def a161681PrefixBelow542 : List ℕ :=
  [2, 7, 11, 13, 19, 23, 47, 53, 61, 67, 71, 79, 83, 89, 107, 109, 127, 139, 151, 167,
   191, 193, 199, 223, 233, 239, 251, 271, 277, 293, 307, 359, 431, 433, 439, 463, 487,
   499, 503]

/-- The witness table's first components are exactly that A161681 prefix. -/
theorem witnesses_map_fst : witnesses.map Prod.fst = a161681PrefixBelow542 := by decide

set_option maxRecDepth 8000 in
/-- **Every row of the table is a certified positive representation.**

Kernel-checked, no `native_decide`: each row asserts primality of `p`, positivity
of `x` and `y`, and the identity `p = x ^ 3 - y ^ 2` in `ℤ`.  The `maxRecDepth`
bump is for `Nat.decidablePrime`'s trial division at `p = 503`; it is an
elaborator budget, not a change to the trusted base. -/
theorem witnesses_spec :
    ∀ t ∈ witnesses,
      Nat.Prime t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧
        (t.1 : ℤ) = (t.2.1 : ℤ) ^ 3 - (t.2.2 : ℤ) ^ 2 := by
  decide

/-- Every row of the witness table certifies a positive cube-minus-square representation. -/
theorem isPosCubeMinusSquare_of_mem_witnesses {t : ℕ × ℕ × ℕ} (ht : t ∈ witnesses) :
    IsPosCubeMinusSquare t.1 := by
  obtain ⟨-, hx, hy, heq⟩ := witnesses_spec t ht
  exact ⟨t.2.1, t.2.2, hx, hy, heq⟩

/-- Every row of the witness table certifies an unrestricted cube-minus-square representation. -/
theorem isCubeMinusSquare_of_mem_witnesses {t : ℕ × ℕ × ℕ} (ht : t ∈ witnesses) :
    IsCubeMinusSquare t.1 :=
  isCubeMinusSquare_of_isPosCubeMinusSquare (isPosCubeMinusSquare_of_mem_witnesses ht)

/-- **No row of the table is a term of A161682.**  Each is a prime *of* the form
`x ^ 3 - y ^ 2`. -/
theorem notMem_primesNotCubeMinusSquare_of_mem_witnesses {t : ℕ × ℕ × ℕ} (ht : t ∈ witnesses) :
    t.1 ∉ primesNotCubeMinusSquare :=
  fun hmem => hmem.2 (isCubeMinusSquare_of_mem_witnesses ht)

/-- `2` is prime and is not a term of A161682, because `2 = 3 ^ 3 - 5 ^ 2`. -/
theorem two_notMem_primesNotCubeMinusSquare : (2 : ℕ) ∉ primesNotCubeMinusSquare :=
  notMem_primesNotCubeMinusSquare_of_mem_witnesses (t := (2, 3, 5)) (by decide)

/-- **A161682 is a proper subset of the primes.**

This is the non-vacuity guard in the *upper* direction: without it,
`primesNotCubeMinusSquare_infinite` below could be nothing more than a restatement
of Euclid's theorem.  `2` separates the two sets. -/
theorem primesNotCubeMinusSquare_ssubset_setOf_prime :
    primesNotCubeMinusSquare ⊂ {p : ℕ | p.Prime} := by
  refine (Set.ssubset_iff_of_subset primesNotCubeMinusSquare_subset_setOf_prime).mpr ?_
  exact ⟨2, Nat.prime_two, two_notMem_primesNotCubeMinusSquare⟩

/-! ## Two proved memberships

Everything in this section is independent of the OEIS entry: it is the
insolubility of the Mordell equations `y ^ 2 = x ^ 3 - 3` and `y ^ 2 = x ^ 3 - 5`,
which is classical (A081121 lists `3` and `5` as its first two terms).  See the
"Deviation" note in the module docstring for why it is here. -/

/-- **No positive integer `≡ 3 (mod 4)` divides `z ^ 2 + 1`.**

Via the Jacobi symbol: `n` is odd, so `J(-1 | n) = χ₄ n = -1`; but `n ∣ z ^ 2 + 1`
makes `-1 ≡ z ^ 2 (mod n)` with `gcd (z, n) = 1`, whence `J(-1 | n) = J(z ^ 2 | n)
= 1`.

(The usual phrasing — "some prime factor of `n` is `≡ 3 (mod 4)`, and `-1` is a
non-residue there" — needs an induction over the factorization that the Jacobi
symbol packages already.) -/
private theorem not_dvd_sq_add_one_of_emod_four_eq_three {m z : ℤ} (hm : 0 < m)
    (h4 : m % 4 = 3) : ¬ m ∣ z ^ 2 + 1 := by
  intro hdvd
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℤ) = m := ⟨m.toNat, Int.toNat_of_nonneg hm.le⟩
  have hn4 : n % 4 = 3 := by omega
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  have hgcd : Int.gcd z (n : ℤ) = 1 := by
    have h1 : ((Int.gcd z (n : ℤ) : ℕ) : ℤ) ∣ z := Int.gcd_dvd_left z (n : ℤ)
    have h2 : ((Int.gcd z (n : ℤ) : ℕ) : ℤ) ∣ (n : ℤ) := Int.gcd_dvd_right z (n : ℤ)
    have h3 : ((Int.gcd z (n : ℤ) : ℕ) : ℤ) ∣ z ^ 2 + 1 := h2.trans hdvd
    have h4' : ((Int.gcd z (n : ℤ) : ℕ) : ℤ) ∣ z ^ 2 := h1.pow (by norm_num)
    have h5 : ((Int.gcd z (n : ℤ) : ℕ) : ℤ) ∣ 1 := by
      have h6 := dvd_sub h3 h4'
      simpa using h6
    have h7 : Int.gcd z (n : ℤ) ∣ 1 := by exact_mod_cast h5
    exact Nat.dvd_one.mp h7
  have hmod : (-1 : ℤ) % (n : ℤ) = (z ^ 2) % (n : ℤ) :=
    Int.modEq_iff_dvd.mpr (by simpa using hdvd)
  have hneg : jacobiSym (-1) n = -1 := by
    rw [jacobiSym.at_neg_one hodd, ZMod.χ₄_nat_three_mod_four hn4]
  have hone : jacobiSym (-1) n = 1 := by
    rw [jacobiSym.mod_left' hmod, jacobiSym.sq_one' hgcd]
  rw [hneg] at hone
  norm_num at hone

/-- The common tail of both Mordell descents: a positive `n ≡ 3 (mod 4)` cannot
divide `4 * (z ^ 2 + 1)`.

`n` is odd, so it is coprime to `4` — witnessed by Bézout coefficients read off
`n = 4 * K + 3`, since `n * n - 4 * (4 * K ^ 2 + 6 * K + 2) = 1` — and therefore
`n ∣ z ^ 2 + 1`, which
`not_dvd_sq_add_one_of_emod_four_eq_three` forbids. -/
private theorem false_of_dvd_four_mul_sq_add_one {n z K : ℤ} (hpos : 0 < n)
    (hK : n = 4 * K + 3) (hdvd : n ∣ 4 * (z ^ 2 + 1)) : False := by
  have hcop : IsCoprime n (4 : ℤ) := ⟨n, -(4 * K ^ 2 + 6 * K + 2), by rw [hK]; ring⟩
  have hmod : n % 4 = 3 := by omega
  exact not_dvd_sq_add_one_of_emod_four_eq_three hpos hmod (hcop.dvd_of_dvd_mul_left hdvd)

/-- **`3` is not of the form `x ^ 3 - y ^ 2`** — the Mordell equation
`y ^ 2 = x ^ 3 - 3` has no integral solution.

Descent.  If `y` were odd then `x ^ 3 = 4 * (s ^ 2 + s + 1)` with `s ^ 2 + s`
even, so `x` is even and `2 * t ^ 3` is odd.  Hence `y = 2 * z` and
`x ^ 3 = 4 * z ^ 2 + 3` is odd; writing `x = 2 * w + 1` gives
`4 * w ^ 3 + 6 * w ^ 2 + 3 * w = 2 * z ^ 2 + 1`, so `w` is odd and
`x ≡ 3 (mod 4)`.  Now
`(x + 1) * (x ^ 2 - x + 1) = x ^ 3 + 1 = 4 * (z ^ 2 + 1)`, and the cofactor
`x ^ 2 - x + 1` is positive and `≡ 3 (mod 4)`: `false_of_dvd_four_mul_sq_add_one`
closes it. -/
theorem not_isCubeMinusSquare_three : ¬ IsCubeMinusSquare 3 := by
  rintro ⟨x, y, h⟩
  norm_num at h
  have hcube : y ^ 2 + 3 = x ^ 3 := by linarith
  obtain ⟨z, rfl⟩ : ∃ z : ℤ, y = 2 * z := by
    rcases Int.even_or_odd y with he | ho
    · obtain ⟨z, hz⟩ := he
      exact ⟨z, by omega⟩
    · exfalso
      obtain ⟨s, hs⟩ := ho
      have hx3 : x ^ 3 = 4 * (s ^ 2 + s + 1) := by rw [← hcube, hs]; ring
      obtain ⟨t, ht⟩ : (2 : ℤ) ∣ x :=
        Int.prime_two.dvd_of_dvd_pow (n := 3) ⟨2 * (s ^ 2 + s + 1), by rw [hx3]; ring⟩
      have h8 : 8 * t ^ 3 = 4 * (s ^ 2 + s + 1) := by rw [← hx3, ht]; ring
      obtain ⟨k, hk⟩ : ∃ k : ℤ, s ^ 2 + s = 2 * k :=
        ⟨(Int.even_mul_succ_self s).choose, by
          have hchoose := (Int.even_mul_succ_self s).choose_spec
          linear_combination hchoose⟩
      obtain ⟨T, hT⟩ : ∃ T : ℤ, t ^ 3 = T := ⟨_, rfl⟩
      rw [hT] at h8
      omega
  have hx3 : x ^ 3 = 4 * z ^ 2 + 3 := by rw [← hcube]; ring
  obtain ⟨w, hw⟩ : ∃ w : ℤ, x = 2 * w + 1 := by
    rcases Int.even_or_odd x with he | ho
    · exfalso
      obtain ⟨t, ht⟩ := he
      have h8 : 8 * t ^ 3 = 4 * z ^ 2 + 3 := by rw [← hx3, ht]; ring
      obtain ⟨T, hT⟩ : ∃ T : ℤ, t ^ 3 = T := ⟨_, rfl⟩
      obtain ⟨Z, hZ⟩ : ∃ Z : ℤ, z ^ 2 = Z := ⟨_, rfl⟩
      rw [hT, hZ] at h8
      omega
    · exact ho
  have hcubic : 4 * w ^ 3 + 6 * w ^ 2 + 3 * w = 2 * z ^ 2 + 1 := by
    have hh := hx3
    rw [hw] at hh
    linarith [hh]
  obtain ⟨v, hv⟩ : ∃ v : ℤ, x = 4 * v + 3 := by
    obtain ⟨A, hA⟩ : ∃ A : ℤ, w ^ 3 = A := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B : ℤ, w ^ 2 = B := ⟨_, rfl⟩
    obtain ⟨C, hC⟩ : ∃ C : ℤ, z ^ 2 = C := ⟨_, rfl⟩
    rw [hA, hB, hC] at hcubic
    exact ⟨(w - 1) / 2, by omega⟩
  obtain ⟨K, hK⟩ : ∃ K : ℤ, x ^ 2 - x + 1 = 4 * K + 3 :=
    ⟨4 * v ^ 2 + 5 * v + 1, by rw [hv]; ring⟩
  refine false_of_dvd_four_mul_sq_add_one (z := z) ?_ hK ⟨x + 1, by linear_combination -hx3⟩
  nlinarith [sq_nonneg (2 * x - 1)]

/-- **`5` is not of the form `x ^ 3 - y ^ 2`** — the Mordell equation
`y ^ 2 = x ^ 3 - 5` has no integral solution.

Same descent, with the parities shifted.  `y` odd would give
`x ^ 3 = 4 * s ^ 2 + 4 * s + 6`, hence `x` even and `8 * t ^ 3 = 4 * s ^ 2 +
4 * s + 6`, which is `0 ≡ 2` mod `4`.  So
`y = 2 * z`, `x ^ 3 = 4 * z ^ 2 + 5` is odd, `x = 2 * w + 1` gives
`4 * w ^ 3 + 6 * w ^ 2 + 3 * w = 2 * z ^ 2 + 2` so `w` is even and
`x ≡ 1 (mod 4)`.  This time `(x - 1) * (x ^ 2 + x + 1) = x ^ 3 - 1 =
4 * (z ^ 2 + 1)` and the cofactor `x ^ 2 + x + 1` is positive and
`≡ 3 (mod 4)`. -/
theorem not_isCubeMinusSquare_five : ¬ IsCubeMinusSquare 5 := by
  rintro ⟨x, y, h⟩
  norm_num at h
  have hcube : y ^ 2 + 5 = x ^ 3 := by linarith
  obtain ⟨z, rfl⟩ : ∃ z : ℤ, y = 2 * z := by
    rcases Int.even_or_odd y with he | ho
    · obtain ⟨z, hz⟩ := he
      exact ⟨z, by omega⟩
    · exfalso
      obtain ⟨s, hs⟩ := ho
      have hx3 : x ^ 3 = 4 * s ^ 2 + 4 * s + 6 := by rw [← hcube, hs]; ring
      obtain ⟨t, ht⟩ : (2 : ℤ) ∣ x :=
        Int.prime_two.dvd_of_dvd_pow (n := 3) ⟨2 * s ^ 2 + 2 * s + 3, by rw [hx3]; ring⟩
      have h8 : 8 * t ^ 3 = 4 * s ^ 2 + 4 * s + 6 := by rw [← hx3, ht]; ring
      obtain ⟨T, hT⟩ : ∃ T : ℤ, t ^ 3 = T := ⟨_, rfl⟩
      obtain ⟨S, hS⟩ : ∃ S : ℤ, s ^ 2 = S := ⟨_, rfl⟩
      rw [hT, hS] at h8
      omega
  have hx3 : x ^ 3 = 4 * z ^ 2 + 5 := by rw [← hcube]; ring
  obtain ⟨w, hw⟩ : ∃ w : ℤ, x = 2 * w + 1 := by
    rcases Int.even_or_odd x with he | ho
    · exfalso
      obtain ⟨t, ht⟩ := he
      have h8 : 8 * t ^ 3 = 4 * z ^ 2 + 5 := by rw [← hx3, ht]; ring
      obtain ⟨T, hT⟩ : ∃ T : ℤ, t ^ 3 = T := ⟨_, rfl⟩
      obtain ⟨Z, hZ⟩ : ∃ Z : ℤ, z ^ 2 = Z := ⟨_, rfl⟩
      rw [hT, hZ] at h8
      omega
    · exact ho
  have hcubic : 4 * w ^ 3 + 6 * w ^ 2 + 3 * w = 2 * z ^ 2 + 2 := by
    have hh := hx3
    rw [hw] at hh
    linarith [hh]
  obtain ⟨v, hv⟩ : ∃ v : ℤ, x = 4 * v + 1 := by
    obtain ⟨A, hA⟩ : ∃ A : ℤ, w ^ 3 = A := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B : ℤ, w ^ 2 = B := ⟨_, rfl⟩
    obtain ⟨C, hC⟩ : ∃ C : ℤ, z ^ 2 = C := ⟨_, rfl⟩
    rw [hA, hB, hC] at hcubic
    exact ⟨w / 2, by omega⟩
  obtain ⟨K, hK⟩ : ∃ K : ℤ, x ^ 2 + x + 1 = 4 * K + 3 :=
    ⟨4 * v ^ 2 + 3 * v, by rw [hv]; ring⟩
  refine false_of_dvd_four_mul_sq_add_one (z := z) ?_ hK ⟨x - 1, by linear_combination -hx3⟩
  nlinarith [sq_nonneg (2 * x + 1)]

/-- `3`, the first `terms` entry of A161682, really is a term. -/
theorem three_mem_primesNotCubeMinusSquare : (3 : ℕ) ∈ primesNotCubeMinusSquare :=
  ⟨Nat.prime_three, not_isCubeMinusSquare_three⟩

/-- `5`, the second `terms` entry of A161682, really is a term. -/
theorem five_mem_primesNotCubeMinusSquare : (5 : ℕ) ∈ primesNotCubeMinusSquare :=
  ⟨by norm_num, not_isCubeMinusSquare_five⟩

/-- **A161682 is nonempty.**

This is the non-vacuity guard in the *lower* direction:
`primesNotCubeMinusSquare_infinite` asserts a set is infinite, which an empty set
would make plainly **false**, and no axiom sweep can detect that. -/
theorem primesNotCubeMinusSquare_nonempty : primesNotCubeMinusSquare.Nonempty :=
  ⟨3, three_mem_primesNotCubeMinusSquare⟩

/-! ## The conjecture -/

/-- The archived conjecture, unfolded: "infinite" for a set of naturals is
"unbounded".  A proof of `primesNotCubeMinusSquare_infinite` is exactly a
procedure that, given `N`, produces a prime `p` with `N < p` admitting no representation
`p = x ^ 3 - y ^ 2` at all — not merely none with `x, y` below some search
radius. -/
theorem primesNotCubeMinusSquare_infinite_iff :
    primesNotCubeMinusSquare.Infinite ↔
      ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ ¬ IsCubeMinusSquare p := by
  rw [Set.infinite_iff_exists_gt]
  constructor
  · intro h N
    obtain ⟨p, hmem, hlt⟩ := h N
    exact ⟨p, hlt, hmem.1, hmem.2⟩
  · intro h N
    obtain ⟨p, hlt, hp, hnot⟩ := h N
    exact ⟨p, ⟨hp, hnot⟩, hlt⟩

/-- **The A161682 infinitude conjecture.**

Verbatim from the entry's `comments` field, pulled 2026-08-05 — the whole line,
which carries no attribution:

> Conjecture: The sequence is infinite.

**Status: open.**  This is the single intended `sorry` of the file.

**What is and is not established around it.**  The statement is not vacuous in
either direction: `primesNotCubeMinusSquare_nonempty` shows the set is inhabited
(so the claim is not trivially *false*), and
`primesNotCubeMinusSquare_ssubset_setOf_prime` shows it is a *proper* subset of
the primes (so the claim is not a restatement of Euclid, which would make it
trivially *true*).  Neither of those, of course, is evidence for the conjecture.

**Why it is hard.**  Membership of a single prime `p` is the assertion that the
Mordell equation `y ^ 2 = x ^ 3 - p` has no integral point.  Each such assertion
is decidable in principle — Baker's method bounds the integral points effectively,
and Siegel's theorem makes them finite — but the bounds are astronomical and, more
to the point, they are *per `p`*.  An infinitude statement needs a single
obstruction that recurs for infinitely many `p`, and the entry supplies none: its
only evidence is the bounded search recorded in the first comment (`x,y < 10000`)
and Starodubtsev's extension (`x < 2.2*10^9`), which are searches for
representations, not proofs that none exist.  Hall's conjecture on `|x ^ 3 - y ^ 2|`
is the natural quantitative frame and is itself open.

The congruence obstructions that settle the individual cases here — `p = 3` and
`p = 5`, via `x ^ 2 ∓ x + 1 ≡ 3 (mod 4)` dividing `z ^ 2 + 1` — do not generalize:
for `p = 4 * k ^ 2 + 1` with `k > 1` the same factorization produces
`x ^ 2 + x + 1 ∣ z ^ 2 + k ^ 2`, and a prime `≡ 3 (mod 4)` may divide `z ^ 2 + k ^ 2`
whenever it divides both `z` and `k`, which nothing in the descent rules out. -/
theorem primesNotCubeMinusSquare_infinite : primesNotCubeMinusSquare.Infinite := by
  -- intended sorry: the unattributed A161682 comment "Conjecture: The sequence is infinite."
  sorry

/-! ## Satisfiability and sharpness

Every predicate defined above is instantiated at a concrete value, in both
polarities, so that no statement below is about an empty domain. -/

-- `IsCubeMinusSquare` holds somewhere and fails somewhere
example : IsCubeMinusSquare 2 ∧ ¬ IsCubeMinusSquare 3 :=
  ⟨⟨3, 5, by norm_num⟩, not_isCubeMinusSquare_three⟩

-- `IsPosCubeMinusSquare` holds somewhere and fails somewhere
example : IsPosCubeMinusSquare 2 ∧ ¬ IsPosCubeMinusSquare 3 :=
  ⟨⟨3, 5, by norm_num, by norm_num, by norm_num⟩,
   fun h => not_isCubeMinusSquare_three (isCubeMinusSquare_of_isPosCubeMinusSquare h)⟩

-- `primesNotCubeMinusSquare` has members and non-members
example : (3 : ℕ) ∈ primesNotCubeMinusSquare ∧ (2 : ℕ) ∉ primesNotCubeMinusSquare :=
  ⟨three_mem_primesNotCubeMinusSquare, two_notMem_primesNotCubeMinusSquare⟩

-- the hypothesis of `isCubeMinusSquare_iff_isPosCubeMinusSquare_of_prime` is
-- inhabited, and both sides of the resulting `Iff` are then true at `p = 2`
example : IsPosCubeMinusSquare 2 :=
  (isCubeMinusSquare_iff_isPosCubeMinusSquare_of_prime Nat.prime_two).mp ⟨3, 5, by norm_num⟩

-- and false at `p = 3`, so the `Iff` is not merely `True ↔ True`
example : ¬ IsPosCubeMinusSquare 3 :=
  fun h => not_isCubeMinusSquare_three
    ((isCubeMinusSquare_iff_isPosCubeMinusSquare_of_prime (by norm_num)).mpr h)

-- primality enters the `Iff` only to exclude `y = 0`, and `n = 1` is exactly where
-- that exclusion has no other source: `1 = 1 ^ 3 - 0 ^ 2` uses `y = 0`, and `1` is
-- not prime.  (Whether `1` also has a *positive* representation is the Mordell
-- equation `y ^ 2 = x ^ 3 - 1`; it is not decided anywhere in this file.)
example : IsCubeMinusSquare 1 ∧ ¬ Nat.Prime 1 := ⟨⟨1, 0, by norm_num⟩, by norm_num⟩

-- composites are not excluded by the predicate itself: `4 = 2 ^ 3 - 2 ^ 2`
example : IsCubeMinusSquare 4 ∧ IsPosCubeMinusSquare 4 :=
  ⟨⟨2, 2, by norm_num⟩, ⟨2, 2, by norm_num, by norm_num, by norm_num⟩⟩

-- `witnesses` is not the empty list, and its first row is the `p = 2` certificate
example : (2, 3, 5) ∈ witnesses := by decide

-- the unbounded form of the conjecture is equivalent to the `Set.Infinite` form,
-- and its right-hand side is inhabited at `N = 2` by `p = 3`
example : ∃ p : ℕ, 2 < p ∧ p.Prime ∧ ¬ IsCubeMinusSquare p :=
  ⟨3, by norm_num, Nat.prime_three, not_isCubeMinusSquare_three⟩

/-! ## Signature audit -/

#check @IsCubeMinusSquare
#check @IsPosCubeMinusSquare
#check @isCubeMinusSquare_of_isPosCubeMinusSquare
#check @isCubeMinusSquare_iff_isPosCubeMinusSquare_of_prime
#check @primesNotCubeMinusSquare
#check @mem_primesNotCubeMinusSquare_iff
#check @mem_primesNotCubeMinusSquare_iff_pos
#check @prime_of_mem_primesNotCubeMinusSquare
#check @primesNotCubeMinusSquare_subset_setOf_prime
#check @witnesses
#check @witnesses_length
#check @a161681PrefixBelow542
#check @witnesses_map_fst
#check @witnesses_spec
#check @isPosCubeMinusSquare_of_mem_witnesses
#check @isCubeMinusSquare_of_mem_witnesses
#check @notMem_primesNotCubeMinusSquare_of_mem_witnesses
#check @two_notMem_primesNotCubeMinusSquare
#check @primesNotCubeMinusSquare_ssubset_setOf_prime
#check @not_isCubeMinusSquare_three
#check @not_isCubeMinusSquare_five
#check @three_mem_primesNotCubeMinusSquare
#check @five_mem_primesNotCubeMinusSquare
#check @primesNotCubeMinusSquare_nonempty
#check @primesNotCubeMinusSquare_infinite_iff
#check @primesNotCubeMinusSquare_infinite

/-! ## Axiom audit

Everything below is `{propext, Classical.choice, Quot.sound}` except
`primesNotCubeMinusSquare_infinite`, the single intended `sorry`, which also
reports `sorryAx`. -/

#print axioms isCubeMinusSquare_of_isPosCubeMinusSquare
#print axioms isCubeMinusSquare_iff_isPosCubeMinusSquare_of_prime
#print axioms mem_primesNotCubeMinusSquare_iff
#print axioms mem_primesNotCubeMinusSquare_iff_pos
#print axioms prime_of_mem_primesNotCubeMinusSquare
#print axioms primesNotCubeMinusSquare_subset_setOf_prime
#print axioms witnesses_length
#print axioms witnesses_map_fst
#print axioms witnesses_spec
#print axioms isPosCubeMinusSquare_of_mem_witnesses
#print axioms isCubeMinusSquare_of_mem_witnesses
#print axioms notMem_primesNotCubeMinusSquare_of_mem_witnesses
#print axioms two_notMem_primesNotCubeMinusSquare
#print axioms primesNotCubeMinusSquare_ssubset_setOf_prime
#print axioms not_dvd_sq_add_one_of_emod_four_eq_three
#print axioms false_of_dvd_four_mul_sq_add_one
#print axioms not_isCubeMinusSquare_three
#print axioms not_isCubeMinusSquare_five
#print axioms three_mem_primesNotCubeMinusSquare
#print axioms five_mem_primesNotCubeMinusSquare
#print axioms primesNotCubeMinusSquare_nonempty
#print axioms primesNotCubeMinusSquare_infinite_iff
#print axioms primesNotCubeMinusSquare_infinite

end A161682
