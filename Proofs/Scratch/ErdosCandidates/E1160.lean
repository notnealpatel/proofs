/-
  Erdős Problem #1160 — group counts below powers of two.
  Status: open (attribution uncertain per the source itself).
  Tier UB archive target on the repo's GroupCount layer.

  Verbatim statement (`goof erdos fetch 1160`, pulled 2026-08-05):

    "Let $g(n)$ denote the number of groups of order $n$. If
    $n\leq 2^m$ then $g(n)\leq g(2^m)$."

  DB remarks: listed as Question 22.16 in Blackburn–Neumann–
  Venkataraman [BNV07], "a quite natural conjecture, whose origin we
  have been unable to trace satisfactorily... attributed at various
  times to... Paul Erdős and Graham Higman."  Question 22.18 suggests
  the stronger `∑_{n<2^m} g(n) ≤ g(2^m)` for large m (perhaps m ≥ 7).
  Pantelidakis [Pa03, DPhil thesis]: true for odd n when m ≥ 3619.
  Comment (BorisAlexeev): numerology — 14 groups of order 16 and 14 of
  order in (8,16); 51 of order 32 and 51 in (16,32); suggests
  `∑_{2^{m-1}<n<2^m} g(n) ≤ g(2^m)`.

  Repo adjacency: `Proofs/GroupCount/Gnu.lean` — `GroupCount.gnu n`
  (A000001, groups of order n up to isomorphism, defined via decidable
  quotient of `GroupStructure n`), with `gnu_prime`, `gnu_four`
  landed.  Honest-confidence caveat from the candidates doc: certified
  gnu values beyond small orders are the bottleneck (gnu 64 = 267 is
  already serious); only the m ≤ 2 instance is near-term provable.

  OEIS anchor: A000001 (1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 5, 1, 2, 1,
  14, …).
-/
import Mathlib
import GroupCount.Gnu

set_option autoImplicit false

namespace ErdosCandidates.E1160

open GroupCount

/-- **Erdős #1160 (OPEN)**: for `1 ≤ n ≤ 2^m`, the number of groups of
    order `n` is at most the number of groups of order `2^m`.

    Source text: "If $n\leq 2^m$ then $g(n)\leq g(2^m)$."

    Uses the repo's `GroupCount.gnu` (junk pinned: gnu 0 = 0, so the
    `1 ≤ n` guard keeps the statement about actual group orders).
    Believed true — "almost all groups are 2-groups" folklore; fully
    open in general. -/
theorem erdos_1160 (m n : ℕ) (hn : 1 ≤ n) (h : n ≤ 2 ^ m) :
    gnu n ≤ gnu (2 ^ m) := by
  sorry

/-- The `m = 2` instance — provable NOW from the repo's landed lemmas:
    `gnu 4 = 2` (`GroupCount.gnu_four`) and `gnu 1 = gnu 2 = gnu 3 = 1`
    (`gnu_prime` + the trivial order-1 count).
    -- PROVABLE (case split on n ∈ {1,2,3,4}). -/
theorem erdos_1160_m2 (n : ℕ) (hn : 1 ≤ n) (h : n ≤ 2 ^ 2) :
    gnu n ≤ gnu (2 ^ 2) := by
  sorry

/-- The `m = 3` instance: needs `gnu 8 = 5` (certified classification
    of order-8 groups — C₈, C₄×C₂, C₂³, D₄, Q₈) and `gnu n ≤ 5` for
    n ≤ 8; gnu 8 = 5 is the natural next GroupCount target (the
    `card_eq_gnu_of_classification` machinery is built for exactly
    this).  -- PROVABLE-with-work (effort M, per the repo's gnu
    range caveat). -/
theorem erdos_1160_m3 (n : ℕ) (hn : 1 ≤ n) (h : n ≤ 2 ^ 3) :
    gnu n ≤ gnu (2 ^ 3) := by
  sorry

/-- **Pantelidakis** ([Pa03], archived; thesis reported via [BNV07] —
    the original is not independently verified, flagged in the DB
    remarks): the conjecture holds for odd `n` when `m ≥ 3619`. -/
theorem pantelidakis_odd (m n : ℕ) (hm : 3619 ≤ m) (hn : 1 ≤ n)
    (hodd : Odd n) (h : n ≤ 2 ^ m) :
    gnu n ≤ gnu (2 ^ m) := by
  sorry

/-- **BNV Question 22.18** (the stronger sum form), archived: for all
    sufficiently large `m` (perhaps m ≥ 7),
    `∑_{1 ≤ n < 2^m} g(n) ≤ g(2^m)`. -/
theorem bnv_22_18 :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      ∑ n ∈ Finset.Ico 1 (2 ^ m), gnu n ≤ gnu (2 ^ m) := by
  sorry

/-- Sanity against A000001 (pulled 2026-08-05): gnu values 1, 1, 1, 2,
    1, 2, 1, 5 for n = 1..8 — the m ≤ 3 ground truth.  gnu 1 through
    gnu 4 follow from landed lemmas; gnu 5, 7 from `gnu_prime`;
    gnu 6 = 2 and gnu 8 = 5 are the open certified-count targets.
    -- PROVABLE-with-work. -/
example : gnu 1 = 1 ∧ gnu 2 = 1 ∧ gnu 3 = 1 ∧ gnu 4 = 2 ∧ gnu 5 = 1 ∧
    gnu 6 = 2 ∧ gnu 7 = 1 ∧ gnu 8 = 5 := by
  sorry

end ErdosCandidates.E1160

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Statement matches DB verbatim (re-pulled 2026-08-05).
   - Pantelidakis [Pa03] via BNV07: DB confirms "Pantelidakis proved
     true if n is odd and m >= 3619". Thomas Bloom notes thesis not
     independently found. File flags this correctly.
   - BNV Question 22.18 (sum form, perhaps m >= 7): matches DB.
   - BorisAlexeev numerology (14 groups order 16, 14 in (8,16); 51 of
     order 32, 51 in (16,32)): matches DB comment post-3796.
   - OEIS A000001 prefix: DB terms "0,1,1,1,2,1,2,1,5,..."; file claims
     gnu 1..8 = 1,1,1,2,1,2,1,5. Matches (offset by 1 for n=0 junk).
   - Repo import: GroupCount.Gnu exists at Proofs/GroupCount/Gnu.lean;
     exports gnu_prime (line 44), gnu_four (line 45),
     gnu_eq_zero_iff (line 38: gnu n = 0 <-> n = 0). The file's
     "gnu 0 = 0 junk" claim is confirmed by gnu_eq_zero_iff.
-/
