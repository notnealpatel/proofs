# Erdős #376 / OEIS A030979: the finite digit-equivalence layer

## Scope

This development proves the pointwise coprimality/digit equivalence and finite
sanity certificates. It does **not** assert infinitude, give an asymptotic count,
or claim progress on the open infinitude question. The exploratory
`Proofs/Scratch/ErdosCandidates/E376.lean` is not imported; its unfinished
statements remain outside this development's proof dependencies.

## Live-source reconciliation (2026-09-12 UTC)

The first two commands of this lane were `erdos fetch 376` and
`oeis show A030979`, before inspecting repository prose.

- [Erdős #376](https://www.erdosproblems.com/376) asks: “Are there infinitely
  many $n$ such that $\binom{2n}{n}$ is coprime to $105$?” It gives the equivalent
  base-3/base-5/base-7 digit restrictions. This matches the scratch header and
  `Erdos175/KummerDigits.lean`; it is not a theorem proved here.
- [OEIS A030979](https://oeis.org/A030979) is “Numbers k such that
  binomial(2k,k) is not divisible by 3, 5 or 7.” Its first comment states the
  single-prime digit criterion and attributes it to Lucas's theorem. The Erdős
  record attributes the equivalence to Kummer's theorem. These are compatible
  proof routes; the repository uses Kummer.
- The first thirteen live terms are
  `0, 1, 10, 756, 757, 3160, 3186, 3187, 3250, 7560, 7561, 7651, 20007`.
  They agree with the scratch list. Each is certified here, without asserting
  that these are all solutions up to `20007`.

Three incorrect or unsupported comments in the scratch file were corrected,
without changing any of its Lean statements or proofs:

1. The ternary expansion is `756 = 3^6 + 3^3 = (1001000)_3`.
   Neither the old `(1000000)_3` nor the old leading term `2*3^5` is correct.
   `digits_three_756` checks the low-endian list `[0,0,0,1,0,0,1]` in Lean.
2. The inequality `2*d < p` does **not** imply `2*d + 1 < p` for odd primes:
   `p = 3, d = 1` is a kernel-checked counterexample in `Sanity.lean`.
   The valid no-carry induction starts with incoming carry zero and propagates
   incoming carry zero. It never needs the false inequality.
3. The assertion “doubly-exponentially sparse” has no support in either live
   record and was removed. The OEIS record reports only a heuristic count
   (approximately `x^0.02595...` terms up to `x`), not a proved growth law.

The scratch API inventory was also stale: the precise Kummer theorem is
Mathlib's `padicValNat_choose'`, and the full list-digit bridge already exists
as `Erdos175.prime_not_dvd_centralBinom_iff_digits`. The old scratch restriction
to odd primes is unnecessary, as already documented in `KummerDigits.lean`.
The current development reuses that stronger theorem rather than reproving it.
`leandoc` was used for exact API inspection, followed by Lean `#check`.

## Library interface and proof route

Import `Erdos.Erdos376.DigitCriterion` for the equivalences, or
`Erdos.Erdos376.Sanity` for those plus the finite certificates.
`Proofs/Erdos.lean` imports the latter.

The inherited single-prime theorem is:

```lean
Erdos175.prime_not_dvd_centralBinom_iff_digits
  {p n : ℕ} (hp : p.Prime) :
  ¬ p ∣ Nat.centralBinom n ↔ ∀ d ∈ Nat.digits p n, 2 * d < p
```

Thus it applies in particular to every odd prime. The new public theorems are:

- `Erdos376.coprime_centralBinom_prime_iff_digits`: the same criterion with
  `Nat.Coprime (Nat.centralBinom n) p` on the left.
- `Erdos376.coprime_105_iff_digits`: for every natural `n`,

  ```lean
  Nat.Coprime (Nat.centralBinom n) 105 ↔
    (∀ d ∈ Nat.digits 3 n, d < 2) ∧
    (∀ d ∈ Nat.digits 5 n, d < 3) ∧
    (∀ d ∈ Nat.digits 7 n, d < 4)
  ```

  The proof factors `105 = 3 * (5 * 7)`, uses the prime criterion for each
  factor, then converts the three inequalities by elementary arithmetic.
- `Erdos376.small_a030979_digit_certificates` and
  `Erdos376.small_a030979_coprime_certificates`: the displayed thirteen inputs
  satisfy the digit conditions and hence the coprimality condition.
- `Erdos376.digits_three_756`: the checked ternary expansion above.
- `Erdos376.not_digits_three_two` and `Erdos376.not_coprime_105_two`: a negative
  sanity instance.

No replacement definition of digits or coprimality is introduced. All natural
numbers, including zero, are allowed. At zero the digit lists are empty and
`Nat.centralBinom 0 = 1`, so the vacuous digit condition is intentionally
correct. Positive examples at `10`, `756`, and `757` ensure the statements are
not validated only by an empty digit domain. The inherited prime theorem also
works at `p = 2`; zero passes while one fails. Prime hypotheses rule out the
invalid bases zero and one. Statements use `2 * d < p`, never truncated `p / 2`.

## Validation and trust

Successful targeted builds:

```sh
flock .lake/agent.lock lake build Erdos.Erdos175.KummerDigits
flock .lake/agent.lock lake build Erdos.Erdos376.DigitCriterion
flock .lake/agent.lock lake build Erdos.Erdos376.DigitCertificates
flock .lake/agent.lock lake build Erdos.Erdos376.Sanity
```

All three new Lean modules set `autoImplicit false` and compile without errors
or proof placeholders. Every named theorem above has a `#print axioms` audit;
the exact reported set for each is
`[propext, Classical.choice, Quot.sound]`, including the inherited single-prime
bridge. There is no custom axiom or `native_decide` in their trusted closure.
The finite checks use kernel-checked `decide` on digits rather than evaluating
large binomial coefficients.

`DigitCertificates.lean` is the frozen computation module: downstream semantic
proofs belong in `Sanity.lean`. Its first build took 1.3 seconds, with Mathlib
dependencies already available; the subsequent downstream build replayed the
certificate rather than recomputing it. The criterion and sanity modules took
1.4 and 1.3 seconds respectively. These are module elaboration times, not a
from-source rebuild of all Mathlib dependencies.

The integration check `flock .lake/agent.lock lake build Erdos` also succeeded
(8741 jobs). That umbrella target reports pre-existing proof-placeholder
warnings in unrelated developments, including `Covering/ErdosRows.lean` and
`Covering/OddCovering.lean`; none is in the dependency closure of these E376
results. The three targeted E376 builds have no such warnings.

## Completed-lane checkpoint

The source reconciliation, equivalence, finite certificates, signature/axiom
audits, and umbrella import check are complete. No proof obligation or
computation remains in this lane. The next action is dispatcher review and
adoption of the three new Lean modules, this source/audit note, the single
umbrella import, and the three comment-only scratch corrections. Do not import
the scratch candidate or treat its unfinished headline as part of the result.
