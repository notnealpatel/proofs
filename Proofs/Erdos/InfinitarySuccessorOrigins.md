# Infinitary successor origins: the f=2 congruence core

## Exact completed contract

`Erdos.InfinitarySuccessorOrigins.not_dvd_successors` proves, for every natural prime `q`,

- `q % 4 = 1`,
- `q % 3 = 2`,
- `q % 5 = 4`,
- `q % 16 = 9 ∨ q % 16 = 13`,

that **for every natural bit position `h` with `1 ≤ h`**, none of

```text
2^(2^h) + 1, 3^(2^h) + 1, 5^(2^h) + 1
```

is divisible by `q`. The positions are unbounded and the actual exponents are `2^h`; there is no selected-exponent-divisor surrogate, assumed order certificate, or additional bounded-order hypothesis.

The objects, quantifiers, all assigned hypotheses, and conclusion survive unchanged. The mod-4 and mod-3 hypotheses are retained in the exported theorem but unnecessary for this proof. No cycle, support inclusion, valuation budget, or extraction hypothesis is added.

## Smaller proof route

This unit uses a shorter argument than the source's base-specific quadratic-reciprocity route:

1. Divisibility gives `b^(2^h) = -1` in `ZMod q`. The residue hypotheses give `2 < q`, so `-1 ≠ 1`.
2. `orderOf_eq_prime_pow` gives **exactly** `orderOf b = 2^(h+1)`: its `2^h`-th power is not one and its `2^(h+1)`-th power is one. The modulus is prime and `b` is nonzero; the latter follows directly from the successor divisibility.
3. Finite-field Lagrange gives `2^(h+1) ∣ q - 1`. If `3 ≤ h`, then `16 ∣ q - 1`, contrary to either permitted residue modulo 16. Thus `h ≤ 2`. The subtraction occurs only inside the proof, with `2 < q` already established, not as an unguarded theorem hypothesis.
4. Positive `h` is therefore one or two. The six factors are

   | base | h = 1 | h = 2 |
   |---|---:|---:|
   | 2 | 5 | 17 |
   | 3 | 2 · 5 | 2 · 41 |
   | 5 | 2 · 13 | 2 · 313 |

   The listed factors are prime, and none is `4` modulo 5. Prime divisibility of a product reduces to divisibility of one of its factors. All numerical primality and residue checks are kernel-checked `norm_num` proofs.

In particular, handling `5^4 + 1 = 626 = 2 · 313` explicitly eliminates the need for Euler's criterion or quadratic reciprocity. This is an alternative proof of the same contract, not a hidden QR premise or a weakened statement. The unbounded step is the exact-order and Lagrange argument, not finite enumeration.

## Nonvacuity and translation checks

The production file includes a joint interface example at **q = 29**, proving primality and every assigned congruence. It also specializes the completed universal theorem at q = 29. These examples make no assertion about an actual cycle.

The order and position helper hypotheses are jointly realized by `q = 29`, `b = 12`, `h = 1`, since `12² + 1 = 145` is divisible by 29. These checks are also retained in production. An external disposable audit additionally checked that the positive-position domain is inhabited by `h = 1`, and jointly instantiated the finite-factor helper hypotheses at q = 29. There are no new definitions requiring representation equivalences, and no concrete-type instance overrides or empty quantified finite domains.

## Evidence and imports

Read in full:

- `/tmp/erdos-program-infinitary-argument3-01a127d7.md`, SHA256 `e72de9881c020ea2ed6c3f8538ac88385d4063145ef72f9504764c9f23392ac4` (locally verified).
- `/tmp/coordinator-infinitary-square-f2-prose-review-01a127d7.md`, local SHA256 `f88f98989a1c70f80f3c461d1034227ff59b026c796d36043f107d3af49a310a`.
- `/tmp/coordinator-infinitary-f2-review-literal-input-verification-01a127d7.json`, reporting full literal-byte review at seq 5, call `call_sG1jLHn36uFKOsEXBUXavq7J`.

The Lean module directly imports only `Mathlib.FieldTheory.Finite.Basic`, `Mathlib.GroupTheory.OrderOfElement`, and `Mathlib.Tactic`. It does **not** import any project f=1, square-input, or unreviewed partial f=2 module. API discovery used `leandoc`, followed by actual elaboration; a disposable external audit checked the full signatures of the order, cast-zero, and finite-field APIs and all four exported theorems.

Observed checks, each bounded by a 60-second command timeout with 2-second kill grace and launched through a 70-second `tool_task`:

1. `lake env lean -j 1 -M 4000 Proofs/Erdos/InfinitarySuccessorOrigins.lean` at the two-checkpoint stage: **exit 0**, no diagnostics.
2. `lake -q build +Erdos.InfinitarySuccessorOrigins` for the completed module: **exit 0**, no diagnostics; its `.olean` was produced.
3. `lake env lean -j 1 -M 4000 /tmp/infinitary-successor-audit.lean`: **exit 0**. Full exported signatures match the displayed contract. Each of `orderOf_eq_two_pow_succ`, `position_le_two`, `not_dvd_small_successor`, and `not_dvd_successors` reports exactly `[propext, Classical.choice, Quot.sound]`.

The external audit is not imported into production. No `sorry`, custom axioms, `native_decide`, external proof implementation, or production `#check`/`#print`/`#eval` remains. This is a producer-side signature and axiom check; independent final review and adoption remain coordinator-owned.

Effort receipt: dispatch baseline `2026-10-11T01:52:32.280792577Z`; the complete build and separate audit were already successful by the `2026-10-11T01:55:45Z` inspection. There were three inspected successful compiler checks and an earlier initial checkpoint invocation whose completion notification did not retain diagnostics; it was repeated with explicit output/status logging. No compiler error, mathematical enumeration, Sage run, or QR infrastructure implementation was needed.

## Named consumer and unpaid bridges

This theorem supplies the **forward-origin exclusion** needed by the strict-support witness under the reverse-cycle bit budget two: once extraction supplies a prime with these congruences, it divides none of the positive-position successor factors with bases 2, 3, or 5.

The extraction of `(q+1)/2 = 3^v * 5^u` with positive `v` and positive odd `u`, derivation of the congruences from that extraction, the exact reverse-cycle bit budget, and closure of the canonical `S(N)` support through those factors **remain unformalized here**. No formal strict-support witness or actual-cycle f=2 exclusion is claimed. This completed implication is ready for that named consumer, not a substitute for its unpaid upstream and support bridges.

Only `Proofs/Erdos/InfinitarySuccessorOrigins.lean` and this companion are added. No references, ledger, existing f=1/square-input files, or revision graph are modified.
