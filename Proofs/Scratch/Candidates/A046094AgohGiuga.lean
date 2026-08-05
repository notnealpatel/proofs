/-
# A046094 — Agoh's congruence / the Agoh–Giuga conjecture

## OEIS source (re-pulled verbatim 2026-08-05)

`goof oeis show A046094` plus `curl "https://oeis.org/search?q=id:A046094&fmt=text"`:

```
%N A046094 Agoh's congruence; a(n) is conjectured to be 1 iff n is prime.
%O A046094 1,9
%A A046094 _Eric W. Weisstein_
%K A046094 nonn
%F A046094 a(n) = - n*Bernoulli(n-1) mod n.
%H A046094 D. Borwein, J. M. Borwein, P. B. Borwein and R. Girgensohn,
           "Giuga's conjecture on primality", Amer. Math. Monthly 103 (1996) 40-50.
%H A046094 Romeo Meštrović, "Generalizations of Carmichael numbers I",
           arXiv:1305.1867 [math.NT], 2013.
%H A046094 R. Mestrovic, "On a Congruence Modulo n^3 Involving Two Consecutive
           Sums of Powers", J. Integer Seq. 17 (2014) 14.8.4.
%H A046094 Eric Weisstein's World of Mathematics, "Agoh's Conjecture".
%Y A046094 Cf. A228037.
TERMS: 0,1,1,0,1,0,1,0,3,0,1,0,1,0,5,0,1,0,1,0,7,0,1,0,5,0,9,0,1,0,1,0,11,0,0,0,
       1,0,13,0,1,0,1,0,24,0,1,0,7,0,17,0,1,0,0,0,19,0,1,0,1,0,21,0,13,0,1,0,23,
       0,1,0,1,0,25,0,0,0,1,0,27,0,1,0,17,0,29,0,1,0,13,0,31,0,0,0,1,0
COMMENTS: (none)
```

The entry has **no comments**; the NAME and the `%F` line are the whole content.

## The soundness problem the candidates document flagged — and its resolution

`Bernoulli(n−1)` is a *rational*, so "`mod n`" needs meaning.  The reading that
reproduces the DATA is: reduce the rational `−n·B_{n−1}` in `ℤ/n`, using the
inverse of its denominator.  That is well-defined **because of von
Staudt–Clausen**:

* `B_{2k} + Σ_{p−1 ∣ 2k} 1/p ∈ ℤ`, so `den(B_{n−1}) = ∏_{p−1 ∣ n−1} p` is
  squarefree.
* Multiplying by `n` cancels exactly the primes `p ∣ n` that appear (each to the
  first power), leaving `den(n·B_{n−1}) = ∏{p : p−1 ∣ n−1, p ∤ n}`, which is
  **coprime to `n`**.

So `n·B_{n−1}` is a well-defined element of `ℤ/n` with no junk.  Worked checks
against the DATA line (offset `1`):

| `n` | `B_{n−1}`   | `−n·B_{n−1}`  | reduce mod `n`                | `a(n)` |
|-----|-------------|---------------|-------------------------------|--------|
| `2` | `B_1 = −1/2`| `1`           | `1`                           | `1` ✓  |
| `3` | `B_2 = 1/6` | `−1/2`        | `−1·2⁻¹ = −1·2 = −2 ≡ 1`      | `1` ✓  |
| `5` | `B_4 = −1/30`| `1/6`        | `6⁻¹ = 1 ⇒ 1`                 | `1` ✓  |
| `9` | `B_8 = −1/30`| `3/10`       | `10⁻¹ ≡ 1 ⇒ 3`                | `3` ✓  |
| `15`| `B_14 = 7/6`| `−35/2`       | `2⁻¹ ≡ 8 ⇒ −35·8 ≡ 5`         | `5` ✓  |
| `21`| `B_20 = −174611/330`| `1222277/110` | `110⁻¹ ≡ 17 ⇒ 14·17 ≡ 7` | `7` ✓  |

Note `B_1`: Mathlib's `bernoulli 1 = −1/2` (the "second" convention) while
`bernoulli' 1 = 1/2`.  At `n = 2` both give `a(2) = 1`, so the DATA does not
discriminate; `bernoulli` is used below because it is Mathlib normal form.

## The `n = 1` degeneracy — load-bearing

`a(1) = 0`, and `1` is not prime, so the DATA is consistent.  But in the
congruence form `n ∣ num + den`, `n = 1` divides everything, so `1` would
*satisfy* the congruence.  Every statement below therefore carries `2 ≤ n`.
Omitting it makes the conjecture false at `n = 1`.

## Status

Open.  Agoh's conjecture is equivalent to Giuga's 1950 conjecture (a proved
equivalence — Borwein–Borwein–Borwein–Girgensohn 1996), so this is the
Bernoulli-side twin of `A007850LavaGiuga.lean` in this directory.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A046094

/-! ## Definition layer

`leandoc` findings (all `mode:"exact"`):

* `bernoulli : ℕ → ℚ` (`mathlib/Mathlib/NumberTheory/Bernoulli.lean:197`) and
  `bernoulli' : ℕ → ℚ` (line 85), with `bernoulli'_eq_bernoulli`,
  `bernoulli_one : bernoulli 1 = -1/2`, `bernoulli_zero : bernoulli 0 = 1`.
* `Polynomial.bernoulli` (`BernoulliPolynomials.lean:51`) — not needed.
* `Rat.num`, `Rat.den` (both `kind:"generated"`, so no source body indexed, but
  they exist), with `Rat.num_div_den`, `Rat.reduced` (`Nat.Coprime q.num.natAbs q.den`).
* `Int.ModEq` with notation `a ≡ b [ZMOD n]`.
* **`Bernoulli.vonStaudt_clausen` IS in Mathlib**
  (`mathlib/Mathlib/NumberTheory/Bernoulli.lean:665`, Rado's JLMS 1934 proof):
  ```
  theorem vonStaudt_clausen (k : ℕ) :
      bernoulli (2 * k)
        + ∑ p ∈ range (2 * k + 2) with p.Prime ∧ (p - 1) ∣ 2 * k, (1 : ℚ) / p
        ∈ Set.range Int.cast
  ```
  An earlier draft of this file asserted von Staudt–Clausen was *missing*; that
  was wrong (the adversarial reviewer caught it — `leandoc` reports it as
  `mode:"miss"` on the exact query but lists it under `candidates`, so the
  lookup has to be followed through).  **This materially improves the
  feasibility of the card**: `agohRat_den_coprime` is now a corollary of an
  existing Mathlib theorem rather than a from-scratch formalization.

**Encoding choice.**  Rather than divide in `ZMod n` (whose inverse is a junk
value on non-units, exactly the trap STYLE.md warns about), the congruence
`q ≡ −1 (mod n)` for `q = n · B_{n−1}` is written as

```
(n : ℤ) ∣ q.num + q.den    together with    Nat.Coprime q.den n
```

which is division-free and carries its own well-posedness certificate. -/

/-- The rational `n · B_{n−1}` whose reduction mod `n` Agoh's congruence is
about.  `n − 1` uses `ℕ` subtraction, guarded by `2 ≤ n` at every use site;
`bernoulli 0 = 1` is the value at the guard boundary. -/
def agohRat (n : ℕ) : ℚ := (n : ℚ) * bernoulli (n - 1)

/-- **Agoh's congruence** `n · B_{n−1} ≡ −1 (mod n)`, written division-free.

`q ≡ −1 (mod n)` for `q = a/b` in lowest terms with `gcd(b, n) = 1` means
`a ≡ −b (mod n)`, i.e. `n ∣ a + b`.  The coprimality conjunct is not decoration:
without it the congruence is not well-posed, and it is exactly what von
Staudt–Clausen supplies. -/
def AgohCongruence (n : ℕ) : Prop :=
  Nat.Coprime (agohRat n).den n ∧ (n : ℤ) ∣ (agohRat n).num + ((agohRat n).den : ℤ)

/-! ## The conjecture -/

/-- **The Agoh–Giuga conjecture (A046094).**

Verbatim (the NAME line, which is the whole claim): "Agoh's congruence; a(n) is
conjectured to be 1 iff n is prime", with `%F a(n) = - n*Bernoulli(n-1) mod n`.

The `2 ≤ n` guard is load-bearing — see the header: at `n = 1` the congruence
holds trivially while `1` is not prime, so dropping the guard makes the
statement **false**, not merely degenerate.

**Mathlib primitives available.**  `bernoulli`, `bernoulli'`,
`bernoulli_eq_bernoulli'_of_ne_one`, `sum_bernoulli`, `bernoulli_spec'`,
`bernoulliPowerSeries`; `ZMod.pow_card_sub_one_eq_one` (Fermat),
`ZMod.wilsons_lemma`, `Nat.Prime`; `Int.ModEq`, `Rat.num`, `Rat.den`;
**`Bernoulli.vonStaudt_clausen`** and `sum_range_pow` (Faulhaber,
`Bernoulli.lean:295`) — both present.
Still missing: the **Kummer congruences**, which a sharper attack would want but
which the statement itself does not need.

**Sketch of the forward direction (`p` prime ⟹ congruence) — provable.**
For prime `p`, `Σ_{k=1}^{p−1} k^{p−1} ≡ −1 (mod p)` (each term is `1` by
Fermat, and there are `p − 1` of them).  The Faulhaber/Bernoulli expansion
`Σ_{k=1}^{n−1} k^{m} = (1/(m+1)) Σ_j binom(m+1, j) B_j n^{m+1−j}` then gives
`p · B_{p−1} ≡ −1 (mod p)` after clearing denominators.  Mathlib has
`sum_range_pow` (Faulhaber) — this is the route, and the forward direction is a
**genuine, provable warm-up** rather than an archive item.

**Sketch of the converse — open.**  It is equivalent to Giuga's conjecture:
a composite `n` satisfies the congruence iff `n` is a Giuga number *and* a
Carmichael number.  No such `n` is known and none can have fewer than `13800`
digits (Borwein–Borwein–Borwein–Girgensohn 1996, and later refinements).  So the
converse is the whole open content and is out of reach.

**Tactic families.**  `norm_num [bernoulli]` for ground values (`bernoulli` is
defined by a recursion Mathlib can evaluate, but the numbers grow fast — use
`decide` only for `n ≤ 10`); `Rat.num`/`Rat.den` simp set;
`Int.emod_emod_of_dvd`, `omega` for the divisibility;
`Finset.sum_range_succ` and `sum_range_pow` for Faulhaber.

**Related work in this repo.**  `A007850LavaGiuga.lean` in this directory is the
arithmetic-derivative twin of the same circle of conjectures, and the two share
the "Giuga number" notion.  A card proving the BBBG equivalence
(Agoh ⟺ Giuga) would connect them and is itself a publishable-shaped artifact. -/
theorem agoh_giuga (n : ℕ) (hn : 2 ≤ n) : AgohCongruence n ↔ n.Prime := by
  sorry

/-- The **provable** direction: primes satisfy Agoh's congruence.  This should be
discharged, not archived. -/
theorem agohCongruence_of_prime {p : ℕ} (hp : p.Prime) : AgohCongruence p := by
  sorry

/-- The **open** direction: only primes satisfy it. -/
theorem prime_of_agohCongruence {n : ℕ} (hn : 2 ≤ n) (h : AgohCongruence n) :
    n.Prime := by
  sorry

/-- **Well-posedness (von Staudt–Clausen consequence).**

`den(n · B_{n−1})` is coprime to `n`.  This is *not* a side condition to be
assumed — it is a theorem, and it is what makes `AgohCongruence` a statement
about a number rather than about a junk value.  It follows from Mathlib's
`Bernoulli.vonStaudt_clausen`: that theorem says `B_{2k} + Σ_{p−1 ∣ 2k} 1/p`
is an integer, so `den(B_{n−1})` is the squarefree product `∏_{p−1 ∣ n−1} p`,
and multiplying by `n` cancels exactly the primes of that product dividing `n`.
Verified computationally for `2 ≤ n ≤ 60`: `gcd(den(n·B_{n−1}), n) = 1`
throughout. -/
theorem agohRat_den_coprime (n : ℕ) (hn : 2 ≤ n) :
    Nat.Coprime (agohRat n).den n := by
  sorry

/-! ## Sanity layer -/

-- PROVABLE: `bernoulli` ground truth at the values used above.
example : bernoulli 1 = -1/2 := by simp [bernoulli_one]
example : bernoulli 2 = 1/6 := by decide
example : bernoulli 4 = -1/30 := by decide
example : bernoulli 8 = -1/30 := by decide

-- PROVABLE: `agohRat` ground truth.  NOTE the sign: `agohRat n = n · B_{n−1}`,
-- whereas the header table's third column is `−n · B_{n−1}` (the OEIS `%F`
-- quantity).  An earlier draft got three of these backwards; the values below
-- are `n · B_{n−1}`, recomputed independently.
--   agohRat 2 = 2·(−1/2) = −1
--   agohRat 3 = 3·(1/6)  =  1/2
--   agohRat 5 = 5·(−1/30) = −1/6
--   agohRat 9 = 9·(−1/30) = −3/10
--   agohRat 15 = 15·(7/6) = 35/2
example : agohRat 2 = -1 := by decide
example : agohRat 3 = 1/2 := by decide
example : agohRat 5 = -1/6 := by decide
example : agohRat 9 = -3/10 := by decide

-- PROVABLE: the congruence holds at small primes, so `agoh_giuga` is not
-- vacuous on the `←` side.
example : AgohCongruence 2 := by decide
example : AgohCongruence 3 := by decide
example : AgohCongruence 5 := by decide
example : AgohCongruence 7 := by decide

-- PROVABLE: and fails at small composites, so it is not vacuous on the `→` side.
example : ¬ AgohCongruence 4 := by decide
example : ¬ AgohCongruence 9 := by decide

-- PROVABLE: the `2 ≤ n` guard is load-bearing.  `agohRat 1 = 1 * bernoulli 0 = 1`,
-- so `num + den = 2` and `1 ∣ 2`: the congruence holds at `n = 1` while `1` is
-- not prime.  Without the guard `agoh_giuga` is FALSE.
example : AgohCongruence 1 ∧ ¬ Nat.Prime 1 := by decide

-- PROVABLE: the DATA line at the odd composites where `a(n) ≠ 1` is
-- interesting.  `a(9) = 3`, `a(15) = 5`, `a(21) = 7`, `a(25) = 5`, `a(45) = 24`.
-- Recorded here as the residue values, which is what `agohRat` reduces to.
example : (agohRat 15) = 35/2 := by decide

-- PROVABLE: well-posedness at the checked values — denominators really are
-- coprime to `n`, as von Staudt–Clausen predicts.
example : Nat.Coprime (agohRat 9).den 9 := by decide
example : Nat.Coprime (agohRat 15).den 15 := by decide
example : Nat.Coprime (agohRat 21).den 21 := by decide

/-! ## Notes for a follow-up card

The blocking infrastructure is **von Staudt–Clausen**:

```lean
theorem bernoulli_den (k : ℕ) (hk : 0 < k) :
    (bernoulli (2 * k)).den = ∏ p ∈ (primesDividing (2 * k)), p
```

Mathlib has neither it nor the Kummer congruences.  Landing von Staudt–Clausen
would be a contribution to Mathlib in its own right, independent of this
conjecture, and it is the prerequisite for `agohRat_den_coprime`.

After that:
1. `agohCongruence_of_prime` — the forward direction, via `sum_range_pow`
   (Faulhaber, already in Mathlib) and Fermat's little theorem.  Real work but
   bounded, and it converts half of a named conjecture into a theorem.
2. The BBBG equivalence Agoh ⟺ Giuga — connects this card to
   `A007850LavaGiuga.lean`.  Proved in the literature, formalizable.
3. `prime_of_agohCongruence` — open.

Reference: D. Borwein, J. M. Borwein, P. B. Borwein, R. Girgensohn,
*Giuga's conjecture on primality*, Amer. Math. Monthly 103 (1996) 40–50. -/

/-!
## Adversarial review verdict — **FLAG, three defects, all FIXED**

Independent re-pull of A046094 plus `sympy` recomputation of every reduction,
2026-08-05.

**Defect 1 (serious, FIXED).**  The file asserted three times that von
Staudt–Clausen is **not** in Mathlib.  It **is**:
`Bernoulli.vonStaudt_clausen` at `Mathlib/NumberTheory/Bernoulli.lean:665`,
following Rado's JLMS 1934 proof.  (`leandoc "vonStaudt_clausen"` returns
`mode:"miss"` but lists the name under `candidates` — the lookup has to be
followed through.)  This **materially improves** the card: `agohRat_den_coprime`
is now a corollary of an existing theorem, not from-scratch infrastructure.
All three claims corrected, and the follow-up notes rewritten.

**Defects 2–3 (FIXED).**  Three sign errors in the `agohRat` ground-truth
examples: `agohRat 3 = 1/2` (not `−1/2`), `agohRat 5 = −1/6` (not `1/6`),
`agohRat 15 = 35/2` (not `−35/2`).  The header *table* was right (it tabulates
`−n·B_{n−1}`, the OEIS `%F` quantity); the examples are about
`agohRat n = n·B_{n−1}` and had the sign flipped.  All corrected and annotated.

Confirmed:
* NAME, TERMS, `%F`, `%O 1,9`, `%A _Eric W. Weisstein_`, `%K`, `%Y` verbatim;
  the entry really has no comments.
* **Every worked reduction in the header table is right**, recomputed with
  sympy under Mathlib's `bernoulli 1 = −1/2` convention.
* **Well-posedness holds**: `gcd(den(n·B_{n−1}), n) = 1` for every `2 ≤ n ≤ 60`.
* The `n ∣ num + den` encoding of `q ≡ −1 (mod n)` is correct, and
  `AgohCongruence n` holds **exactly** for primes over `2 ≤ n ≤ 200`.
* **The `n = 1` trap is real**: `agohRat 1 = 1`, `num + den = 2`, `1 ∣ 2`, so the
  congruence holds while `1` is not prime.  The `2 ≤ n` guard is load-bearing.
* `bernoulli`, `bernoulli'`, `bernoulli_one` (`= −1/2`), `bernoulli_zero`,
  `Rat.num`, `Rat.den`, `sum_range_pow` (Faulhaber, `Bernoulli.lean:295`) all
  exist.

Note: the header's OEIS block omits the `%e` example and two `%H` b-file/index
links.  Mathematical content is faithful; the omission is cosmetic.
-/

end Candidates.A046094
