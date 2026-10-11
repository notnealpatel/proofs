# Actual-cycle five-exponent-four anchor at 313

## Exact scope and contract

The companion Lean module is `Erdos.InfinitarySquareCycleF3Anchor313`, in namespace
`InfinitarySuperperfect`. It imports the existing canonical square-input and
successor-order modules. It introduces no definitions, alternate divisor sum,
or axioms. All objects are the existing `sigma`, `localSigma`, `binarySupport`,
ordinary `Nat.factorization`, actual `Nat.primeFactors`, and standard `ZMod`.

The principal public theorem is `anchor313_of_actual_cycle_shape`. Its entire
contract is:

```lean
(n m a j ell p : ℕ)
(ha : 2 ≤ a) (_haeven : Even a) (_hj : 1 ≤ j) (_hell : 1 ≤ ell)
(hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5)
(hn : n = 2 ^ a * 3 ^ (2 ^ j) * 5 ^ 4 * p ^ (2 ^ ell))
(hforward : m = sigma n) (hreverse : sigma m = 2 * n)
:
m.factorization 313 = 1 ∧ p = 157
```

The permitted omission of `m.factorization 2 = 3` is used: this proof needs only
the explicit shape and both actual equations. The parity and lower bounds on
`j` and `ell` remain literal hypotheses, although this proof does not use them.
The lower bound on `a` supplies its positivity. No normalized-support or
reverse-product certificate is a premise of the principal theorem.

Two additional public helpers are:

* `pow_eight_eq_one_of_313_dvd (b h : ℕ)` assumes
  `313 ∣ b ^ (2 ^ h) + 1` and concludes `(b : ZMod 313) ^ 8 = 1`.
* `not_dvd_313_two_three (h : ℕ)` concludes
  `¬313 ∣ 2 ^ (2 ^ h) + 1 ∧ ¬313 ∣ 3 ^ (2 ^ h) + 1`.

The helpers quantify over every natural height, including zero; there is no
arbitrary bounded-height computation.

## Actual mathematics and forward bridge

1. The existing successor-order theorem gives exact order `2^(h+1)` modulo
   313 for any 313-divisible binary successor. That order divides
   `313 - 1 = 312`. Since 16 does not divide 312, it divides eight. Thus the
   base's eighth power is one. Kernel-checked finite residue certificates
   exclude bases two and three, whose eighth powers are not one modulo 313.
2. The private `sigma_shape` lemma reconstructs the actual prime factors and
   their valuations from the explicit input product. It proves, using the
   canonical definitions rather than an assumed product formula,
   
   `sigma n = localSigma 2 a * (1 + 3^(2^j)) * 626 * (1 + p^(2^ell))`.
   
   A private single-bit lemma establishes
   `localSigma b (2^j) = 1 + b^(2^j)`. The actual forward equation then identifies
   this product with `m`.
3. Neither the base-two local product nor the three successor contains 313.
   Since `626 = 2 * 313`, the forward valuation formula is
   
   `m.factorization 313 = 1 + (1 + p^(2^ell)).factorization 313`.
   
   In particular, 313 is an actual member of `m.primeFactors`. If its valuation
   exceeds one, the remaining forward successor is 313-divisible and hence
   `p^8 = 1` modulo 313.
4. A valuation greater than one has an occupied positive binary bit, proved
   using the existing sum-of-binary-support identity. Its 313 successor divides
   `sigma m` by the existing `slot_dvd_sigma`. Independently, the reverse equation
   and the explicit input shape imply that every prime divisor of `sigma m`
   belongs to `{2,3,5,p}`; this is derived by prime divisibility of products and
   powers, not assumed as a final support hypothesis.
5. A positive reverse height at 313 is impossible. At height one, its successor
   is divisible by both 97 and 101; the derived support would force each of
   these distinct primes to equal `p`. At every height at least two, put
   `s = 313^(2^h) + 1` and `r = s / 2`. The proof first establishes
   `s % 4 = 2`, `s % 3 = 2`, `s % 5 = 2`, `2*r = s`, and `0 < r`.
   Consequently `r` has no prime divisor 2, 3, or 5, and every prime divisor of
   `r` equals `p`. The standard unique-prime-divisor theorem expresses `r` as a
   power of `p`. Therefore `r^8 = 1` modulo 313. But `2*r = s` implies
   `r = 157` modulo 313, and `157^8` is not one (its residue is 302).
6. The valuation is therefore exactly one. Its occupied zero bit supplies
   `314 = 1 + 313` as an actual reverse divisor. Hence prime 157 divides
   `sigma m = 2*n`; the already derived support and its distinction from
   2, 3, and 5 force `p = 157`.

This is implementation of the supplied argument, not a novelty claim. The
finite certificates use `norm_num` and kernel `decide`, not `native_decide`.
The only division introduced in this module is the private natural halving;
its denominator is the nonzero constant two, and exact divisibility and
positivity are proved before using the quotient.

## Models, boundaries, and semantic limits

An anonymous example jointly verifies the explicit shape and actual forward
bridge with

* `a = 2`, `j = ell = 1`, `p = 7`;
* `n = 1102500 = 2^2 * 3^2 * 5^4 * 7^2`;
* `m = 1565000 = sigma 1102500`;
* the stated evenness, lower bounds, primality, and prime exclusions.

The two equal height parameters instantiate both height lower bounds. Separate
examples certify `313 ∣ 5^(2^2)+1` and `(5 : ZMod 313)^8 = 1`, giving a concrete
model of the divisibility/order helper's antecedent.

**No full-cycle model is claimed.** The shape-and-forward example does not
certify `sigma m = 2*n` and is not a joint model of the principal theorem's
whole antecedent. Full antecedent satisfiability has not been established.
The principal result is a conditional branch restriction, not a witness of an
actual cycle. No hypothetical witness is used to evade a contradiction.

All quantified domains are naturals and are nonempty. The input shape forces
positive `n`, and the forward equation and `sigma_pos` give positive `m`.
The actual 313 prime support is explicitly established. The reverse quotient
is positive; the proof does not exploit a zero quotient or an empty support
convention. There are no section-variable declarations, overloaded local
arithmetic conventions, concrete-type instance parameters, or new definitions.

## Consumer and unpaid upstream work

The named consumer is the actual f3 k2 branch analysis: **under this explicit
shape and both cycle equations**, it now reduces to prime 157 and valuation
one at 313. This file does not derive the shape from the general f3 hypothesis,
formalize the reviewed general-shape support reduction, restrict `ell`, prove
an abundance bridge, or close the remaining cycle obstruction. Those upstream
and downstream steps remain with the parent. In particular this is not a full
f3 contradiction or a general classification.

## Verification and finalization status

During implementation, bounded one-file `lake env lean -j 1 -M 4000` checks
successfully elaborated first the modular kernel and then the actual-cycle
wrapper. Initial failures were an absent local dependency cache, an incorrect
order API name, numeral reduction in `ZMod`, simplifier rewrite ordering, a
nonexistent valuation API name, and recursion in positivity proof synthesis.
They were repaired locally. The valuation-product side conditions now use
explicit nonzero proofs, avoiding the problematic positivity synthesis.

The final production module includes the concrete shape-and-forward example
and a restricted nonterminal `simp only`. Its narrow cached build is run as
`timeout --kill-after=2s 60s lake -q build +Erdos.InfinitarySquareCycleF3Anchor313`
through `tool_task` with a 70-second task bound. This final build completed
successfully with exit status zero and no reported diagnostics, including the
actual-cycle theorem, the modular helpers, and the concrete model examples.
The pair is frozen for the parent's independent checks.

No `sorry`, declared axiom, native proof computation, or production informational
command occurs in the module. **Standard-axiom status has not yet been audited.**
No independent imported signature/axiom audit or independent literal both-file
review was performed by this producer; the parent explicitly owns those fresh
checks once the pair is frozen. Compilation is not represented as a completed
axiom, semantic, or full-antecedent non-vacuity audit.

Only this Lean file and companion are production changes. No integration,
adoption, commit, issue, ledger, References, or global target change was made.
