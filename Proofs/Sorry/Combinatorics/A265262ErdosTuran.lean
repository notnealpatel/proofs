import Sorry.Combinatorics.ErdosTuranProfiles

/-!
# A265262 — Erdős–Turán profiles (open conjecture archive)

The unordered profile, basis/Sidon/hemitropic definitions, locality, the
compactness equivalence, and sanity checks are proved in
`Combinatorics.ErdosTuranProfiles`. They retain the `Candidates.A265262` API.
Only the open Erdős–Turán conjecture below remains admitted here.

## OEIS source

A fresh `oeis show A265262` read confirms the unordered `x ≤ y` convention,
the inclusion of zero in the basis condition, and the entry's description of
the conjecture as undecided. This fresh OEIS check is not an independent audit
of the primary literature. The orchestrator's primary-source audit identifies
Haddad, arXiv:1507.05849, pp. 8 and 28, for this all-natural-number unordered
profile and tree convention; Nathanson, arXiv:math/0302155, discusses the
finite-prefix/König equivalence. These references do not identify the fixed-set
all-natural and asymptotic basis predicates, and no such equivalence is asserted
here. The previously recorded entry excerpt follows.

```
%N A265262 The tree of hemitropic sequences read by rows, arising from an
           Erdős-Turán conjecture.
%O A265262 0,3
%A A265262 _Labib Haddad_ and _Michel Marcus_, Dec 06 2015
%K A265262 nonn,tabf
%F A265262 For each k>=0, let u(k)=1 if k is in A, u(k)=0 is k is not in A. Then
           pA(n) = Sum_{k=0..floor(n/2)} u(k)*u(n-k). See formula (5) on p. 8
           and p. 28 in Haddad link.
%H A265262 P. Erdős and P. Turán, "On a problem of Sidon in additive number
           theory, and on some related problems", J. Lond. Math. Soc. 16 (1941),
           212-215.
%H A265262 Labib Haddad, "Some peculiarities of order 2 bases of N and the
           Erdos-Turan conjecture", arXiv:1507.05849 [math.NT], 2015
           (see The binary tree of hemitropic sequences chapter).
%H A265262 Wikipedia, "Erdős-Turán conjecture on additive bases".
TERMS: 1,1,2,0,1,1,2,0,1,1,2,1,2,2,3,0,1,1,2,0,1,1,2,0,1,1,2,1,2,2,3,0,1,1,2,0,
       1,1,2,1,2,2,3,1,2,2,3,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,0,1,1,2,0,
       1,1,2,0,1,1,2,0,1,1,2,0,1,1,2
COMMENTS:
  Let A be a subset of the set N of nonnegative integers. Let pA(n) be the
  number of pairs (x, y) of elements of A such that n = x + y and x <= y. The
  sequence pA = [pA(0), pA(1), ... , pA(n), ... ] is called the profile of A. A
  Sidon set is a subset A whose profile has only 0's and 1's.
  An [order 2 additive] basis of N is a subset A whose profile has no 0's.
  Erdős and Turán conjectured that the profile of a basis is always unbounded
  (see the Erdős and Turán link). The conjecture is, up till now, still
  undecided.
  The tree below displays the infinite sequences [1, pA(2), ... ], associated to
  the profiles pA = [1, 1, pA(2), ... ] of all the subsets A of N to which 0 and
  1 belong. Those are the so-called hemitropic sequences. The Erdős-Turán
  conjecture would not hold if (and only if) the tree contained an infinite
  bounded branch with no 0's.
  The length of the n-th row is 2^n. The right leaf of a node is equal to the
  left leaf + 1.
XREFS:
  Cf. A004137, A066062, A217793.
```

Row structure, read off the TERMS with `2^n` per row (offset `0`):
row 0 `[1]`; row 1 `[1, 2]`; row 2 `[0, 1, 1, 2]`;
row 3 `[0, 1, 1, 2, 1, 2, 2, 3]`;
row 4 `[0, 1, 1, 2, 0, 1, 1, 2, 0, 1, 1, 2, 1, 2, 2, 3]`.

The compactness proof reuses Mathlib's `Finset.rado_selection` with Boolean
membership decisions. It yields a global bounded zero-free profile from
prefixes satisfying a fixed bound at every horizon; it does not rule out such
prefixes and cannot discharge the conjecture. No novelty claim is made.

Row `n` stores `pA(n + 1)`, not `pA(n)`: the entry displays
`[1, pA(2), ...]`. The four choices for membership of `2, 3` extending `{0, 1}`
give profiles at `3` equal to `0, 1, 1, 2`, checked in production. Inserting a
new positive `m` into a set containing zero adds precisely the pair `(0, m)`
at `m`, as proved by `profile_insert_self`.
-/

set_option autoImplicit false

namespace Candidates.A265262

/-- The open Erdős–Turán conjecture: every order-two basis of the nonnegative
integers has an unbounded unordered representation profile. This admission is
not a consequence of the proved compactness equivalence. -/
theorem erdosTuran_basis_profile_unbounded (A : Set ℕ) [DecidablePred (· ∈ A)]
    (hA : IsBasis2 A) : ¬ BddAbove (Set.range (profile A)) := by
  sorry

example : IsBasis2 (Set.univ : Set ℕ) := isBasis2_univ
example : ¬ BddAbove (Set.range (profile (Set.univ : Set ℕ))) := profile_univ_unbounded

end Candidates.A265262
