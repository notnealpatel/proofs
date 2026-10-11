# Bounded even whole-square f2 composition

## Objects and exact scope

`InfinitarySquareCycleF2.lean` uses the existing canonical infinitary divisor sum
`sigma`, occupied-bit set `binarySupport`, ordinary `Nat.factorization`, and
actual `Nat.primeFactors`. It introduces no definitions or alternate arithmetic
interfaces. Its namespace is `InfinitarySuperperfect`; its only two public named
exports are the following.

1. `exists_prime_dvd_reverse_not_dvd_sigma_of_budget_two`: for natural `n,m`,
   assume `0 < n`, `2 ∣ n`, `IsSquare n`, `0 < m`,
   `m.factorization 2 = 2`, `sigma m = 2 * n`,
   `∀ q ∈ m.primeFactors, q ≠ 2 → q % 4 = 1`, and the literal canonical budget
   `(∑ p ∈ n.primeFactors, if p = 2 then 0 else
   (binarySupport (n.factorization p)).card) = 2`.
   Then there exists a natural prime `q` with `q ≠ 2`, `q ∣ m`, and
   `¬ q ∣ sigma n`. There is no forward equation, supplied support, mixed-shape
   witness, residue witness, or square assumption on `m` in this contract.
2. `factorization_sigma_two_ne_two_of_even_square`: for natural `n,m`, assume
   `0 < n`, `2 ∣ n`, `IsSquare n`, `m = sigma n`, and
   `sigma m = 2 * n`. Then `m.factorization 2 ≠ 2`.
   Residue and budget conditions are discharged internally, not premises.

The square premise concerns the whole input `n`, not only its odd part.
The domains are natural numbers, which are nonempty; positivity excludes the
zero-input empty-support convention in both exports. The actual strict model
below has nonempty prime supports. No totalized division, natural subtraction,
or bounded extremum is introduced in these statements.

## Composition and consumer

For the strict export, adopted A–B
`three_and_five_dvd_of_reverse` supplies actual `3 ∣ n` and `5 ∣ n`.
Adopted C `mixed_shape_of_budget_two` produces guarded heights `1 ≤ j,k`,
valuations at three and five, and the mixed factorization shape; C
`support_two_three_five_of_budget_two` supplies actual support inclusion.
Adopted E `exists_reverse_prime_residues` gives an actual prime divisor of `m`
with residues one modulo four, two modulo three, four modulo five, and nine or
thirteen modulo sixteen. Whole-square factorization supplies even valuations.
The canonical-support consumer
`not_dvd_sigma_of_support_two_three_five` then excludes this prime from
`sigma n`. Pairing that exclusion with actual `q ∣ m` closes the strict export.

For the cycle export, assume valuation two for contradiction. `sigma_pos`
and `m = sigma n` give positivity of `m`. Actual prime-factor membership gives
primality and divisibility; rewriting that divisibility with the forward
equation and applying `prime_mod_four_of_dvd_sigma_of_even` proves the required
modulo-four condition for every actual odd reverse prime. The adopted
`factorization_sigma_two_of_isSquare`, the forward equation, and the assumed
valuation give exactly the canonical budget two. The strict export now yields
`q ∣ m` but `¬ q ∣ sigma n`; rewriting the former with `m = sigma n` is the
contradiction. Thus the named cycle consumer has no unpaid internal bridge.

A–B, C, D, E, square-input arithmetic, and successor/canonical support exclusions
are existing adopted results, **not proved by this module**. This module proves
only their bounded final composition and its model certificates. There is no
novelty claim. It proves neither the cases with valuation at least three nor a
global classification or a general successor theorem. Those larger obligations
remain outside this unit.

## Independent joint model and boundaries

Private certificates reconstruct support and valuations from
`8100 = 2^2 * 3^4 * 5^2 = 90^2` and
`9860 = 2^2 * 5 * 17 * 29` using standard factorization APIs.
The supports are respectively `{2,3,5}` and `{2,5,17,29}`. Independent canonical
product calculations prove `sigma 8100 = 10660` and `sigma 9860 = 16200`.
The private joint certificate proves **all** strict premises together:
positivity, evenness, whole-square input, positive reverse member, its valuation
two, the reverse equation, all actual odd support residues, and exact budget two.
An anonymous example invokes the strict export on that certificate.

Separate anonymous examples establish directly that 29 is prime, is not two,
divides 9860, and does not divide `sigma 8100`, and that
`sigma 8100 ≠ 9860`. These do not use either export. This is a nonvacuous model
of the entire strict antecedent, deliberately not a full cycle. There is no
invented model for the inconsistent cycle branch with valuation two.
Boundary examples certify that two is not square and that nine is square but
not even. Thus the known nonsquare cycle at two and odd-square cycle at nine
are outside the stated input conditions; the theorem does not silently
strengthen its hypotheses to exclude them.

## Producer checks and remaining gates

At the assigned accepted baseline, the producer ran:

- `timeout --kill-after=2s 60s lake -q build +Erdos.InfinitarySquareCycleF2`
  via bounded `tool_task` (70-second task limit), first for the two-export
  composition and then with the independent joint model: both succeeded with
  exit status zero and no diagnostics. Logs are
  `/tmp/infinitary-strict-f2-producer-01a1290f/first-build.log` and
  `/tmp/infinitary-strict-f2-producer-01a1290f/model-build.log`.
- `timeout --kill-after=2s 60s lake env lean -j 1 -M 4000
  /tmp/infinitary-strict-f2-producer-01a1290f/Audit.lean` via bounded `tool_task`
  (70-second task limit) succeeded with exit status zero. This disposable
  import-only audit checked both full export signatures, confirming precisely
  the contracts above, and reported only `[propext, Classical.choice,
  Quot.sound]` for each export. Its source and output are `Audit.lean` and
  `audit.log` in the same evidence directory. This is a producer audit only.

There are no `sorry`s, new axioms, native computations, production informational
commands, or temporary Scratch leaves in this unit. Arithmetic certificates
use kernel-checked `decide` and standard factorization rewrites. The production
scope is exactly this companion and its Lean module; evidence resides outside
tracked production. The implementation required composition and representation
certificates, not additional mathematics or a dependency change. Initial
source inspection had one filename mismatch (`InfinitarySquareInput.lean`);
inspection immediately used the actual `InfinitarySuperperfectSquareInput.lean`.
No build timeout or proof error occurred.

Tools exposed during production: file read/write/edit through the filesystem
and supplied tools, bounded shell/Lake checks through `tool_task`, and
read-only `jj --ignore-working-copy` inspection. No peer contact, isolated
`tool_think` review, external research, integration, adoption, or revision
management was performed. In particular the producer has **not** performed
or substituted for the future independent strict complete-final-pair literal
review or the coordinator's fresh imported all-public signature/axiom audit.
Those are separate release gates. Working-copy changes alone are handed off.
