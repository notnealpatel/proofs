import Enumerative.PartitionPerfectPower

/-!
# Open obligation for A000041

This quarantine module retains the existing unproved source statement under its original
namespace and header. The production module supplies the definitions and unconditional
proofs; importing production alone does not admit this conjecture. Source quotations,
limitations, and evidence for the statement are retained below and in the production
module's pinned source documentation. No mathematical proof closure is claimed.
## Archived implementation-card crosswalk

Former card `A000041-sun-perfect-power.md`: A000041, claim `sun-no-perfect-power`,
statement size S, proof difficulty hard, mathematical status open; source is
Zhi-Wei Sun's OEIS comment of 2013-12-02. Production remains at
`Proofs/Enumerative/PartitionPerfectPower.lean`; this `Proofs/Sorry/` module is the
unproved statement archive. `partitionNumber` is the cardinality of `Nat.Partition`;
`IsPerfectPower` means `x^m` with both `x` and `m` at least 2, not `IsPrimePow`.
The former card asked for `n ≥ 1`; the archived all-`n` formulation also includes
the separately proved harmless `n = 0` case. Uniform partition arithmetic is unpaid.
The card's unspecified “large computed ranges” claim is not supported by the
pinned source's verification bound: that source gives none. The exact finite
certificates and their identification range are stated below, not an unbounded proof.
-/

set_option autoImplicit false

namespace A000041

/-- **Sun's perfect-power conjecture for the partition numbers (OEIS A000041).**

Verbatim from the entry's `comments` field, pulled 2026-08-05:

> Conjecture: No a(n) has the form x^m with m > 1 and x > 1. - _Zhi-Wei Sun_,
> Dec 02 2013

No guard on `n` is needed: `a(0) = a(1) = 1` and no perfect power in Sun's sense is
below `4` (`four_le_of_isPerfectPower`), so the two degenerate indices are covered by
the same statement — see `sun_partitionNumber_zero` and `sun_partitionNumber_one`,
which are proved.

**Status: open.**  This is the single intended `sorry` of the file.  The entry publishes
no verification bound for this comment; what is verified here is
`not_isPerfectPower_of_mem_a000041Prefix`, which rules out every term of the pinned
50-term prefix `a(0), …, a(49)`, together with the compiler-checked identification
`partitionNumber n = a(n)` for `n ≤ 16`.

**Why it is hard.**  A proof must control the arithmetic of `p(n)` uniformly in `n`, and
the two handles the A000041 entry itself supplies are the wrong shape for that.

*Congruential.*  In a bracketed note on Forberg's comment about primes dividing
partition numbers, the entry cites Ono (verbatim): "The existence of such partition
numbers follows from Ono's proof (see his paper "Distribution of the partition function
modulo m"). - _Ralf Stephan_, Jan 28 2026" — "such partition numbers" refers to
partition numbers divisible by a given prime, not to perfect powers.  A congruence rules
out a residue class of *values*, but `m`-th
powers occupy every residue class that contains an `m`-th power residue, so no fixed
modulus can exclude them all.

*Analytic.*  The entry's `formulas` field records (verbatim) "a(n) ~
1/(4*n*sqrt(3)) * e^(Pi * sqrt(2n/3)) as n -> infinity (Hardy and Ramanujan). See
A050811."  Even the exact Rademacher refinement of that expansion only locates `p(n)` as
the nearest integer to a transcendental sum, which says nothing about whether that
integer is an `m`-th power.

The same obstruction blocks the sibling conjecture on A000166 (derangements,
`Proofs/Enumerative/DerangementPerfectPower.lean`) and Brocard's problem
(`Proofs/Enumerative/Brocard.lean`). -/
theorem sun_partitionNumber_not_isPerfectPower (n : ℕ) :
    ¬ IsPerfectPower (partitionNumber n) := by
  sorry

end A000041
