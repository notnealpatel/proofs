# Fubini numbers modulo `k`: periodicity

## Status and scope

This is a recovered Palomar candidate for human review. It records one
Fubini-specific formalization only. Human review is pending; this README does
not claim Palomar acceptance, publication, human approval, fresh verification,
or global priority. No agent review is claimed or required for this recovery.

The mathematical object is the project’s `A051293.fubini`, the Fubini (ordered
Bell) numbers, with initial values `1, 1, 3, 13, 75, 541, 4683, 47293`.
`Proofs/Enumerative/FubiniMod.lean` restates their binomial recurrence and
works modulo `k` in `ZMod k`.

## Exact formal result

In namespace `A000670`, the principal declaration is
`fubini_mod_eventuallyPeriodic_conjecture (k : ℕ) (hk : 1 ≤ k)`. Its exact
shape is

```text
∃ N P : ℕ, P ∣ Nat.totient k ∧ 0 < P ∧
  ∀ n, N ≤ n → fubini (n + P) ≡ fubini n [MOD k]
```

Thus some positive period dividing `φ(k)` works eventually for every positive
modulus. Supporting declarations include the explicit mod-2, mod-4, and
mod-16 instances (`fubini_odd`,
`fubini_add_two_modEq_four`, and `fubini_add_two_modEq_sixteen`), the private
truncated-sum congruence `poonen_congr`, the private prime-power result
`fubini_modEq_prime_pow`, and the private Chinese-remainder induction
`fubini_eventuallyPeriodic`. The mod-16 closed form is
`(fubini n : ZMod 16) = 12 - (-1)^n` for `3 ≤ n`, giving residues `13,11,13,11,…`.

The general proof introduces the finite sum
`c(k,n) = ∑ j < k, 2^(k-1-j) j^n` and proves
`(2^k - 1) fubini(n) = c(k,n)` in `ZMod k`. At `p^m`, powers with `p ∣ j`
eventually vanish and Euler periodicity handles `p ∤ j`; an invertibility
argument cancels `2^(p^m)-1`. Prime-power periods are then glued by the
Chinese remainder argument. This is a formalized Fubini instance, not a
formalization of every sequence with an integral e.g.f. `G(exp(x)-1)`.

## Attribution and contribution

Peter Bala’s 8 July 2022 OEIS A000670 comment presented this Fubini statement
as a conjecture. The recovered source and correction drafts identify the
underlying theorem as B. Poonen, “Periodicity of a Combinatorial Sequence,”
*The Fibonacci Quarterly* 26 (1988), 70–76. Poonen’s Theorem 2 gives the
prime-power periodicity (for `n ≥ m`), and Theorem 6 combines the components
to obtain the general modulus conclusion. The mathematics is therefore not a
new theorem or a priority claim. The contribution here is a self-contained
Lean formalization of the Fubini-specific result, rederiving the elementary
recurrence argument rather than importing an analytic series identity.

## Recovered evidence and limitations

I recovered the source file, draft 12 (“the conjecture that was a 1988
theorem”), draft 14 (the scope correction), and the prior parent journal’s
saved source/policy report. Those materials consistently support the Poonen
attribution and the boundary above. They also caution that no exact checked
Barsky citation was recovered, so no Barsky attribution is made. The result
does not settle the broader `G(exp(x)-1)` assertion or transfer automatically
to OEIS A354242 or A002050.

This recovery performed no Lean elaboration, build, test, dependency setup, or
proof audit. The old journal records an earlier environment failure involving
an unknown `Enumerative` module prefix; it is not fresh verification. The
source’s declarations and comments are recorded here as recovered evidence,
not as an independent audit.

## Concrete next obligations

Before packaging, a prover must check the declarations at a fixed public
commit in the pinned project, inspect the permitted axiom footprint, and
resolve whether private helpers need public bridges. A package maintainer must
then prepare a small allowlisted Challenge matching the exact existential
statement, a sorry-free Solution, a Comparator naming every compared
principal declaration, and complete provenance/author/license/source/review
metadata. Import closure, theorem alignment with `A051293.fubini`, degenerate
`k = 1` behavior, the stated source deviation, AI involvement, and pending
human review must all be documented. None of those package artifacts or
verification steps is claimed here.
