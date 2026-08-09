/-
  Erdős Problem #21 / OEIS A391599 — the Erdős–Lovász cover number g(r).

  STATUS: STATEMENT ARCHIVE (USER directive) for the large-n and n ≥ 4
  literature, PROVED for n ≤ 3. The §6 theorems carry INTENDED, DISCLOSED
  sorries; everything else in this file is proved. See "SORRY LEDGER" at the
  end of this header for the exact list.

  The first three OEIS A391599 terms are now sorry-free: g(1) = 1, g(2) = 3,
  and — as of 2026-08-05 — g(3) = 6, whose lower half `6 ≤ g(3)` used to be
  archived and is now the §4 counting argument.

  THE QUANTITY. Following Erdős–Lovász [EL75] (and Sivashankar [Si26], who
  writes g(r); Kahn [Ka94] writes n(r); erdosproblems.com/21 writes f(r);
  OEIS A391599 writes a(n)):

    g(r) = the minimum number of edges of an r-uniform intersecting
           hypergraph H with cover (transversal) number τ(H) = r.

  OEIS A391599 states the same thing in the equivalent "no small cover"
  form, which is the form formalized here as `IsErdosLovaszFamily`
  (`oeis show A391599`, name field, offset 1):

    "Minimum size of an intersecting family of n-sets such that every set of
     size at most n-1 is disjoint from at least one member of the family."

  τ(H) = r is the largest possible cover number of an r-uniform intersecting
  hypergraph, since any single edge is already a cover [Si26, §1]. The
  equivalence of the two phrasings is PROVED here, both directions, in §2:
  `IsErdosLovaszFamily.coveringNumber_eq` (OEIS form → τ = n) and
  `isErdosLovaszFamily_of_coveringNumber_eq` (τ = n → OEIS form), against the
  τ of `Erdos/CoveringNumber.lean`.

  NOT the same as Meyer's M(r), the minimum size of a *maximal* r-uniform
  intersecting family: every maximal family has τ = r but not conversely, so
  M(r) ≥ g(r) and the two can differ [Si26, §1]. The card's phrase "maximal
  intersecting family" is therefore avoided in all names here.

  GROUND TRUTH (pinned live; OEIS/erdosproblems 2026-07-30, re-pulled and the
  arXiv sources re-fetched 2026-08-05).
  * OEIS A391599 (live pull via the `oeis` CLI): DATA 1, 3, 6, 9, 13;
    keywords nonn,hard,more. The `oeis show` JSON has no offset field, so the
    offset was confirmed separately against https://oeis.org/A391599/internal,
    whose `%O` line reads verbatim "%O 1,2" — offset 1.
    So g(1)=1, g(2)=3, g(3)=6, g(4)=9, g(5)=13.
  * erdosproblems.com problem 21 (live pull via the `erdos` CLI): the
    linearity question is recorded as answered; $500 prize noted on the
    site. Verbatim: "The values $f(3)=6$ and $f(4)=9$ were established by
    Tripathi \cite{Tr14}. Bar\'{a}t and Wanless \cite{BaWa21} proved that
    $f(5)=13$, and that $13\leq f(6)\leq 18$."  The f(3)=6 half of that
    sentence is an over-attribution; see [FOT96]/[Tr14] below.
  * References/Erdos/arXiv-2606-24878/erdos_lovasz.tex (re-fetched 2026-08-05
    after the earlier copy went missing), abstract and Theorem 1, read
    directly — see [Si26] below.
  * References/Erdos/arXiv-1409-4610/paper.tex (fetched 2026-08-05), read
    directly — see [Tr14] below.

  LITERATURE, verbatim where it matters.
  [EL75] P. Erdős, L. Lovász, "Problems and results on 3-chromatic
    hypergraphs and some related questions", Infinite and Finite Sets
    (Colloq. Keszthely 1973), Colloq. Math. Soc. János Bolyai 10,
    North-Holland 1975, 609–627: g(r) ≥ 8r/3 − 3, and g(r) ≪ r^{3/2} log r.
  [Ka92] J. Kahn, "On a problem of Erdős and Lovász: random lines in a
    projective plane", Combinatorica 12 (1992), 417–423: g(r) ≪ r log r.
  [Ka94] J. Kahn, "On a problem of Erdős and Lovász. II. n(r) = O(r)",
    J. Amer. Math. Soc. 7 (1994), 125–143: g(r) = O(r). This settled Erdős'
    $500 question; the constant is not explicit.
  [FOT96] P. Frankl, K. Ota, N. Tokushige, "Covers in uniform intersecting
    families and a counterexample to a conjecture of Lovász", J. Combin.
    Theory Ser. A 74 (1996), 33–42: THE ORIGINAL SOURCE OF g(3) = 6. Not
    fetched here (paywalled, 1996); the attribution is taken from [Tr14]'s
    own text, quoted next, and is corroborated by [Si26].
  [Tr14] A. Tripathi, "A result on intersecting families with maximum
    transversal size", arXiv:1409.4610 (2014): g(4) = 9, plus a second proof
    of g(3) = 6. Verbatim from References/Erdos/arXiv-1409-4610/paper.tex:
      "It is easy to see that $q(2) = 3$. In \cite{Frankl}, it was proved
       (among other things) that $q(3) = 6$."
    and, introducing the corollary in his §2,
      "As another application, we give a different proof of the following
       result from \cite{Frankl}," / "\begin{corollary} $q(3) = 6$."
    where \cite{Frankl} is [FOT96] above. [Si26] concurs, verbatim:
      "For small values, Tripathi proved $g(4)=9$ and gave a short proof
       that $g(3)=6$~\cite{Tripathi}".
    So erdosproblems.com/21 over-credits g(3) = 6 to [Tr14] (OEIS does not
    attribute it specifically); the priority is [FOT96]. The `tripathi_` name prefix is kept on
    the g(3) declarations for stability, with the correction in each
    docstring. (Neither proof is the one formalized here — see §4.)
  [Ba21] J. Barát, "Intersecting and 2-intersecting hypergraphs with
    maximal covering number: the Erdős–Lovász theme revisited",
    J. Combin. Des. 29 (2021), 193–209: g(5) = 13, 13 ≤ g(6) ≤ 18.
    AUTHORSHIP DISPUTED, UNRESOLVED HERE: the arXiv source
    (arXiv:2011.04444, fetched to References/Erdos/arXiv-2011-04444) has the
    single \author{J\'anos Bar\'at}, with no Wanless anywhere in the file
    and no journal metadata; but OEIS A391599's %H line and
    erdosproblems.com/21 both cite it as "J. Barát and I. M. Wanless" with
    the same title but different page ranges (OEIS: 193–209; erdosproblems:
    260–286). The likely reading is
    that the published version gained a coauthor the 2020 preprint lacks.
    Nothing in this file depends on the resolution — [Ba21] appears only in
    the two archived §6 statements, which are sorried.
  [Si26] V. Sivashankar, "An Improved Lower Bound for the Erdős–Lovász Cover
    Number Problem", arXiv:2606.24878 (2026), Theorem 1, verbatim:
      (i)  For every positive integer r, g(r) ≥ 3r − 4.
      (ii) For every ε > 0, there is r₀ such that, for every r ≥ r₀,
           g(r) ≥ ((41 − √19)/12 − ε) r.
    with (41 − √19)/12 = 3.05342…, and the remark: "Since (41−√19)/12 > 3,
    part (ii) implies g(r) > 3r for all sufficiently large r".

  THE "3r + O(1)" QUESTION IS REFUTED, NOT OPEN. Both OEIS A391599 and
  erdosproblems.com/21 record the folklore speculation (see [Ka94]) that the
  truth is g(r) = 3r + O(1). [Si26, Thm 1(ii)] contradicts it: g(r) ≥
  (3.0534… − ε)r eventually forces g(r) − 3r → ∞. This file therefore does
  NOT state 3r + O(1) as a theorem; it records the speculation as a `Prop`
  (`ThreeMulAddBigO`) and PROVES its incompatibility with Theorem 1(ii)
  (`not_threeMulAddBigO_of_asymptotic_lower_bound`, sorry-free). What remains
  open is the value of the optimal linear constant, which Frankl–Tokushige
  call "hopelessly difficult" [Si26, §1]; the erdosproblems.com/21 comment
  thread (Jun 2026) quotes [Si26] as g(r) ≥ (61/20 − o(1))r, a rounding of
  (41 − √19)/12 — derived here as `sivashankar_lower_bound_61_20`.

  ∅ ∉ F GUARD (auditor mandate for this lane). `coveringNumber F = 0`
  conflates the honest F = ∅ case with the junk ∅ ∈ F case
  (`Erdos/CoveringNumber.lean`, `coveringNumber_eq_zero_iff`). Here the guard
  is not assumed but PROVED: `IsErdosLovaszFamily.empty_notMem` derives
  ∅ ∉ F from the intersecting clause alone (¬Disjoint A A ↔ A ≠ ∅), and every
  theorem in this file that mentions `coveringNumber` discharges its guard
  from that lemma or carries `∅ ∉ F` explicitly
  (`coveringNumber_le_card_family`). `not_isErdosLovaszFamily_of_empty_mem`
  pins the junk case out. Do NOT `open Metric` in this file: it would clash
  with Mathlib's `Metric.coveringNumber`.

  JUNK VALUES PINNED. `erdosLovaszNum` is a `Nat.sInf`, hence 0 on an empty
  index set. `erdosLovaszCards_nonempty` (0 < n) rules that out, so
  `erdosLovaszNum_mem` gives attainment by an actual family, and
  `zero_lt_erdosLovaszNum` shows 0 is never the value for n ≥ 1.
  `erdosLovaszNum_zero : erdosLovaszNum 0 = 0` is the honest — not junk —
  value at n = 0 (the empty family is 0-uniform, vacuously intersecting, and
  no S has card < 0), which is why the OEIS offset is 1 and every substantive
  theorem here carries `0 < n`.

  TIER 1 — PROVED HERE (sorry-free; axioms exactly
  {propext, Classical.choice, Quot.sound}, verified declaration by
  declaration, 2026-07-30):
    isErdosLovaszFamily_iff             — Mathlib normal form (Set.Sized/Set.Intersecting)
    IsErdosLovaszFamily.empty_notMem    — the ∅ ∉ F guard, derived
    not_isErdosLovaszFamily_of_empty_mem — junk case excluded
    IsErdosLovaszFamily.nonempty        — F ≠ ∅ for n ≥ 1
    coveringNumber_le_card_family       — τ(F) ≤ |F|            (∅ ∉ F)
    coveringNumber_add_one_le_card      — τ(F) + 1 ≤ |F|        (intersecting)
    IsErdosLovaszFamily.le_coveringNumber, .coveringNumber_le
    IsErdosLovaszFamily.coveringNumber_eq — OEIS form → τ(F) = n  (n ≥ 1)
    isErdosLovaszFamily_of_coveringNumber_eq — τ(F) = n → OEIS form
    IsErdosLovaszFamily.le_card, .succ_le_card — n ≤ |F|; n+1 ≤ |F| (n ≥ 2)
    IsErdosLovaszFamily.map             — ground-set independence (embeddings)
    isErdosLovaszFamily_powersetCard    — all (m+1)-subsets of a (2m+1)-set
    erdosLovaszCards_nonempty, erdosLovaszNum_mem — attainment (n ≥ 1)
    erdosLovaszNum_zero/one/two         — g(0)=0, g(1)=1, g(2)=3
    le_erdosLovaszNum                   — n ≤ g(n)          (n ≥ 1)
    zero_lt_erdosLovaszNum              — 0 < g(n)          (n ≥ 1)
    succ_le_erdosLovaszNum              — n + 1 ≤ g(n)      (n ≥ 2)
    erdosLovaszNum_le_choose            — g(m+1) ≤ C(2m+1, m+1)
    isErdosLovaszFamily_witnessThree, erdosLovaszNum_three_le
                                        — g(3) ≤ 6 via the explicit 6-edge
                                          `witnessThree` on 6 vertices
    sum_card_filter_notMem_eq_sum_card_sdiff — the §4 double count
    IsErdosLovaszFamily.three_le_card_filter_notMem
                                        — ≥ 3 members avoid each vertex (n ≥ 3)
    IsErdosLovaszFamily.six_le_card     — 6 ≤ |F| for every EL family of
                                          triples, over every ground type
    tripathi_six_le_erdosLovaszNum_three — 6 ≤ g(3)
    tripathi_erdosLovaszNum_three       — g(3) = 6   [FOT96]; see §4
    sivashankarConst_bounds             — 61/20 < (41−√19)/12 < 3.054
    isBigO_of_forall_le_linear          — explicit constant → IsBigO
    lower_bound_61_20_of_asymptotic     — Thm 1(ii) → the 61/20 rounding
    one_le_of_forall_le_linear          — any Kahn constant satisfies 1 ≤ C
    thirteen_le_erdosLovaszNum_six_of_erdos_lovasz — [EL75] at n=6 gives 13
    not_threeMulAddBigO_of_asymptotic_lower_bound — Thm 1(ii) refutes 3r+O(1)

  TIER 2 — ARCHIVED LITERATURE (intended, disclosed sorries; no Tier 1
  declaration uses any of them):
    erdos_lovasz_lower_bound            [EL75]      8n/3 − 3 ≤ g(n)
    kahn_erdosLovaszNum_le_linear       [Ka94]      ∃C, g(n) ≤ Cn
    sivashankar_three_mul_sub_four      [Si26](i)   3n − 4 ≤ g(n)
    sivashankar_asymptotic_lower_bound  [Si26](ii)  ((41−√19)/12 − ε)n ≤ g(n) ev.
    tripathi_erdosLovaszNum_four        [Tr14]      g(4) = 9
    barat_erdosLovaszNum_five    [Ba21]    g(5) = 13
    barat_erdosLovaszNum_six_le  [Ba21]    g(6) ≤ 18

  TIER 3 — DERIVED FROM TIER 2 (each is a Tier 1 implication applied to a
  Tier 2 statement, so it reports `sorryAx` too — by design, not by
  oversight):
    kahn_erdosLovaszNum_isBigO          [Ka94] in IsBigO form
    sivashankar_lower_bound_61_20       the 61/20 rounding

  SORRY LEDGER (2026-08-05): exactly the seven Tier 2 statements, one
  `declaration uses sorry` warning each. `6 ≤ g(3)` LEFT THE LEDGER on
  2026-08-05 — it is now proved outright in §4, which also promotes
  `tripathi_erdosLovaszNum_three : g(3) = 6` out of Tier 3 into Tier 1. The
  remaining sorries are the four asymptotic/large-n bounds ([EL75], [Ka94],
  [Si26](i), [Si26](ii)) and the three finite values beyond n = 3 ([Tr14]'s
  g(4) = 9, [Ba21]'s g(5) = 13 and g(6) ≤ 18), for which no witness family is
  transcribed here.

  Axiom audit (2026-08-05, §9 of this file runs `#print axioms` on every one
  of the 51 named declarations, in source order): the 42 Tier 1 declarations
  report exactly {propext, Classical.choice, Quot.sound}; the 7 Tier 2 and
  2 Tier 3 declarations report those plus `sorryAx`; nothing reports anything
  else. The build emits exactly 7 `declaration uses sorry` warnings, one per
  Tier 2 statement. No `native_decide`, no custom axioms; all ground checks
  are kernel `decide`. Signatures of the §1–§4 theorems (stated inside
  `variable` sections) were confirmed with `#check @…` per STYLE.md.
-/
import Erdos.CoveringNumber

set_option autoImplicit false

-- ════════════════════════════════════════════════════════════════════
-- §1 THE FAMILY PREDICATE
-- ════════════════════════════════════════════════════════════════════

section Family

variable {α : Type*} {n : ℕ} {F : Finset (Finset α)}

/-- `IsErdosLovaszFamily n F`: the finite family `F` of finite subsets of `α`
is (1) `n`-uniform, (2) intersecting — no two members are disjoint, the
diagonal case `A = B` included, which is Mathlib's `Set.Intersecting`
convention and forces `∅ ∉ F` — and (3) *cover-maximal* in the sense of OEIS
A391599: every set of fewer than `n` vertices is disjoint from at least one
member. Clause (3) says exactly that `F` has no cover of size `< n`, i.e.
`n ≤ τ(F)`; with (1) and (2) it gives `τ(F) = n`
(`IsErdosLovaszFamily.coveringNumber_eq`), the defining condition of
[Si26]'s g(r). No typeclass assumptions: `Disjoint` on `Finset α` needs only
the order structure.

Two deliberate wording choices, both value-preserving:
* OEIS says "size at most n − 1"; clause (3) says `S.card < n` instead, which
  is the same condition for `n ≥ 1` and avoids truncated `ℕ` subtraction
  (STYLE.md). At `n = 0` the two differ, and `< n` is the honest reading —
  no set has fewer than 0 elements — giving `erdosLovaszNum_zero`.
* Clause (2) includes the diagonal `A = B`, following Mathlib's
  `Set.Intersecting`. This is what makes `∅ ∉ F` derivable
  (`IsErdosLovaszFamily.empty_notMem`) rather than an extra hypothesis, and
  it does not change g(n): for `n ≥ 1` clause (1) already forces `∅ ∉ F`,
  and for `n = 0` clause (1) forces `F ⊆ {∅}`, where the empty family
  attains the minimum either way. -/
def IsErdosLovaszFamily (n : ℕ) (F : Finset (Finset α)) : Prop :=
  (∀ A ∈ F, A.card = n) ∧ (∀ A ∈ F, ∀ B ∈ F, ¬ Disjoint A B) ∧
    ∀ S : Finset α, S.card < n → ∃ A ∈ F, Disjoint A S

/-- Over a finite decidable ground type the predicate is decidable, so
concrete witnesses can be checked by kernel `decide`. -/
instance instDecidableIsErdosLovaszFamily [DecidableEq α] [Fintype α] (n : ℕ) :
    DecidablePred (IsErdosLovaszFamily (α := α) n) := fun F =>
  decidable_of_iff ((∀ A ∈ F, A.card = n) ∧ (∀ A ∈ F, ∀ B ∈ F, ¬ Disjoint A B) ∧
    ∀ S : Finset α, S.card < n → ∃ A ∈ F, Disjoint A S) Iff.rfl

/-- The same predicate in Mathlib normal form: `Set.Sized` for uniformity and
`Set.Intersecting` for the intersecting clause. `DecidableEq α` appears only
because Mathlib's `Set.Intersecting` is stated over a `SemilatticeInf`, and
`Finset α` is one only for decidable equality; `IsErdosLovaszFamily` itself
needs no instance. -/
theorem isErdosLovaszFamily_iff [DecidableEq α] :
    IsErdosLovaszFamily n F ↔
      (↑F : Set (Finset α)).Sized n ∧ (↑F : Set (Finset α)).Intersecting ∧
        ∀ S : Finset α, S.card < n → ∃ A ∈ F, Disjoint A S := by
  constructor
  · rintro ⟨hsize, hint, hcov⟩
    exact ⟨fun A hA => hsize A (Finset.mem_coe.mp hA),
      fun A hA B hB => hint A (Finset.mem_coe.mp hA) B (Finset.mem_coe.mp hB), hcov⟩
  · rintro ⟨hsize, hint, hcov⟩
    exact ⟨fun A hA => hsize (Finset.mem_coe.mpr hA),
      fun A hA B hB => hint (Finset.mem_coe.mpr hA) (Finset.mem_coe.mpr hB), hcov⟩

/-- THE GUARD (auditor mandate): no member of an Erdős–Lovász family is
empty. Derived from the intersecting clause alone at `A = B`, since
`Disjoint A A ↔ A = ∅`. Every use of `coveringNumber` below discharges its
`∅ ∉ F` guard through this lemma. -/
theorem IsErdosLovaszFamily.empty_notMem (h : IsErdosLovaszFamily n F) : ∅ ∉ F := by
  intro hmem
  exact h.2.1 ∅ hmem ∅ hmem (Finset.disjoint_empty_left ∅)

/-- JUNK PIN: a family containing `∅` is never an Erdős–Lovász family, so the
junk branch of `coveringNumber` (`∅ ∈ F → coveringNumber F = 0`) is
unreachable from `IsErdosLovaszFamily`. -/
theorem not_isErdosLovaszFamily_of_empty_mem (h : ∅ ∈ F) :
    ¬ IsErdosLovaszFamily n F := fun hF => hF.empty_notMem h

/-- For `n ≥ 1` an Erdős–Lovász family is nonempty: clause (3) at `S = ∅`
demands a member. (At `n = 0` the empty family qualifies — see
`erdosLovaszNum_zero`.) -/
theorem IsErdosLovaszFamily.nonempty (h : IsErdosLovaszFamily n F) (hn : 0 < n) :
    F.Nonempty := by
  obtain ⟨A, hA, -⟩ := h.2.2 ∅ (by simpa using hn)
  exact ⟨A, hA⟩

end Family

-- ════════════════════════════════════════════════════════════════════
-- §2 BRIDGE TO THE COVERING NUMBER τ
-- ════════════════════════════════════════════════════════════════════

section Covering

variable {α : Type*} [DecidableEq α] [Fintype α] {n : ℕ} {F : Finset (Finset α)}

/-- Picking one vertex from each member covers the family, so
`τ(F) ≤ |F|`. The guard `∅ ∉ F` is explicit: with `∅ ∈ F` the left side is
the junk 0 and the statement, while still true, is about the junk. -/
theorem coveringNumber_le_card_family (h : ∅ ∉ F) : coveringNumber F ≤ F.card := by
  revert h
  induction F using Finset.induction_on with
  | empty => intro _; simp
  | insert A G hAG ih =>
      intro h
      have hA : A ≠ ∅ := fun hAe => h (hAe ▸ Finset.mem_insert_self A G)
      have hG : ∅ ∉ G := fun hmem => h (Finset.mem_insert_of_mem hmem)
      obtain ⟨T, hT, hTcard⟩ := exists_isTransversal_card_eq hG
      obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hA
      have hins : IsTransversal (insert A G) (insert a T) := by
        intro B hB
        rcases Finset.mem_insert.mp hB with rfl | hBG
        · exact ⟨a, ha, Finset.mem_insert_self a T⟩
        · obtain ⟨x, hxB, hxT⟩ := hT B hBG
          exact ⟨x, hxB, Finset.mem_insert_of_mem hxT⟩
      calc coveringNumber (insert A G) ≤ (insert a T).card := coveringNumber_le_card hins
        _ ≤ T.card + 1 := Finset.card_insert_le a T
        _ = coveringNumber G + 1 := by rw [hTcard]
        _ ≤ G.card + 1 := Nat.succ_le_succ (ih hG)
        _ = (insert A G).card := (Finset.card_insert_of_notMem hAG).symm

/-- Clause (3) of `IsErdosLovaszFamily` says `F` has no cover of size `< n`:
`n ≤ τ(F)`. -/
theorem IsErdosLovaszFamily.le_coveringNumber (h : IsErdosLovaszFamily n F) :
    n ≤ coveringNumber F := by
  by_contra hlt
  push Not at hlt
  obtain ⟨T, hT, hTcard⟩ := exists_isTransversal_card_eq h.empty_notMem
  obtain ⟨A, hA, hdisj⟩ := h.2.2 T (by omega)
  obtain ⟨x, hxA, hxT⟩ := hT A hA
  exact (Finset.disjoint_left.mp hdisj hxA) hxT

/-- Any single member of an intersecting family is a cover, so
`τ(F) ≤ n` for a nonempty `n`-uniform intersecting family. -/
theorem IsErdosLovaszFamily.coveringNumber_le (h : IsErdosLovaszFamily n F)
    (hF : F.Nonempty) : coveringNumber F ≤ n := by
  obtain ⟨A, hA⟩ := hF
  have hAtrans : IsTransversal F A := fun B hB =>
    Finset.not_disjoint_iff.mp (h.2.1 B hB A hA)
  calc coveringNumber F ≤ A.card := coveringNumber_le_card hAtrans
    _ = n := h.1 A hA

/-- BRIDGE (OEIS form → [Si26] form): an Erdős–Lovász family of `n`-sets with
`n ≥ 1` has covering number exactly `n`, the maximum possible for an
`n`-uniform intersecting family. -/
theorem IsErdosLovaszFamily.coveringNumber_eq (h : IsErdosLovaszFamily n F)
    (hn : 0 < n) : coveringNumber F = n :=
  le_antisymm (h.coveringNumber_le (h.nonempty hn)) h.le_coveringNumber

/-- BRIDGE ([Si26] form → OEIS form): an `n`-uniform intersecting family with
`τ(F) = n` satisfies clause (3), i.e. every set of fewer than `n` vertices
misses some member. Together with `IsErdosLovaszFamily.coveringNumber_eq`
this shows the two definitions of g(n) agree. -/
theorem isErdosLovaszFamily_of_coveringNumber_eq (hsize : ∀ A ∈ F, A.card = n)
    (hint : ∀ A ∈ F, ∀ B ∈ F, ¬ Disjoint A B) (hτ : coveringNumber F = n) :
    IsErdosLovaszFamily n F := by
  refine ⟨hsize, hint, fun S hS => ?_⟩
  by_contra hno
  push Not at hno
  have hStrans : IsTransversal F S := fun A hA => Finset.not_disjoint_iff.mp (hno A hA)
  have hle : coveringNumber F ≤ S.card := coveringNumber_le_card hStrans
  omega

/-- `τ(F) ≤ |F|` sharpens to `τ(F) ≤ |F| - 1` once `F` is intersecting with
two distinct members: a shared vertex of those two members covers both. -/
theorem coveringNumber_add_one_le_card (h : ∅ ∉ F)
    (hint : ∀ A ∈ F, ∀ B ∈ F, ¬ Disjoint A B) (hcard : 2 ≤ F.card) :
    coveringNumber F + 1 ≤ F.card := by
  obtain ⟨A, hA, B, hB, hAB⟩ := Finset.one_lt_card.mp hcard
  obtain ⟨x, hxA, hxB⟩ := Finset.not_disjoint_iff.mp (hint A hA B hB)
  have hBerase : B ∈ F.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  set G := (F.erase A).erase B with hGdef
  have hGempty : ∅ ∉ G :=
    fun hmem => h (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hmem))
  obtain ⟨T, hT, hTcard⟩ := exists_isTransversal_card_eq hGempty
  have hins : IsTransversal F (insert x T) := by
    intro C hC
    by_cases hCA : C = A
    · exact ⟨x, by rw [hCA]; exact hxA, Finset.mem_insert_self x T⟩
    by_cases hCB : C = B
    · exact ⟨x, by rw [hCB]; exact hxB, Finset.mem_insert_self x T⟩
    · obtain ⟨y, hyC, hyT⟩ :=
        hT C (Finset.mem_erase.mpr ⟨hCB, Finset.mem_erase.mpr ⟨hCA, hC⟩⟩)
      exact ⟨y, hyC, Finset.mem_insert_of_mem hyT⟩
  have h1 : coveringNumber F ≤ (insert x T).card := coveringNumber_le_card hins
  have h2 : (insert x T).card ≤ T.card + 1 := Finset.card_insert_le x T
  have h3 : coveringNumber G ≤ G.card := coveringNumber_le_card_family hGempty
  have hc1 : (F.erase A).card = F.card - 1 := Finset.card_erase_of_mem hA
  have hc2 : G.card = (F.erase A).card - 1 := Finset.card_erase_of_mem hBerase
  omega

/-- `n ≤ |F|` for every Erdős–Lovász family of `n`-sets: one vertex per member
would otherwise be a cover of size `< n`. -/
theorem IsErdosLovaszFamily.le_card (h : IsErdosLovaszFamily n F) : n ≤ F.card :=
  h.le_coveringNumber.trans (coveringNumber_le_card_family h.empty_notMem)

/-- For `n ≥ 2` the bound improves to `n + 1 ≤ |F|`, which is sharp at
`n = 2` (`erdosLovaszNum_two`). -/
theorem IsErdosLovaszFamily.succ_le_card (h : IsErdosLovaszFamily n F) (hn : 2 ≤ n) :
    n + 1 ≤ F.card := by
  have hcard : 2 ≤ F.card := le_trans hn h.le_card
  have h1 : coveringNumber F + 1 ≤ F.card :=
    coveringNumber_add_one_le_card h.empty_notMem h.2.1 hcard
  have h2 : n ≤ coveringNumber F := h.le_coveringNumber
  omega

end Covering

-- ════════════════════════════════════════════════════════════════════
-- §3 GROUND-SET INDEPENDENCE AND THE EXISTENCE WITNESS
-- ════════════════════════════════════════════════════════════════════

section Transfer

/-- Being an Erdős–Lovász family is intrinsic to the family, not to the
ambient ground type: pushing `F` forward along an embedding `α ↪ β` preserves
all three clauses. This is what makes the `∃ N` in `erdosLovaszCards` (below)
harmless — a witness on a small ground type is a witness on every larger one,
so no choice of ambient type can make g(n) spuriously small. -/
theorem IsErdosLovaszFamily.map {α β : Type*} {n : ℕ} {F : Finset (Finset α)}
    (e : α ↪ β) (h : IsErdosLovaszFamily n F) :
    IsErdosLovaszFamily n (F.map (Finset.mapEmbedding e).toEmbedding) := by
  obtain ⟨hsize, hint, hcov⟩ := h
  have hmem : ∀ A : Finset β,
      A ∈ F.map (Finset.mapEmbedding e).toEmbedding ↔ ∃ A' ∈ F, A'.map e = A := by
    intro A
    simp [Finset.mem_map, Finset.mapEmbedding_apply]
  refine ⟨?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨A', hA', rfl⟩ := (hmem A).mp hA
    rw [Finset.card_map]
    exact hsize A' hA'
  · intro A hA B hB
    obtain ⟨A', hA', rfl⟩ := (hmem A).mp hA
    obtain ⟨B', hB', rfl⟩ := (hmem B).mp hB
    obtain ⟨x, hxA, hxB⟩ := Finset.not_disjoint_iff.mp (hint A' hA' B' hB')
    exact Finset.not_disjoint_iff.mpr
      ⟨e x, Finset.mem_map_of_mem e hxA, Finset.mem_map_of_mem e hxB⟩
  · intro S hS
    have hinj : Set.InjOn e (⇑e ⁻¹' ↑S) := e.injective.injOn
    have hcard : (S.preimage e hinj).card ≤ S.card :=
      Finset.card_le_card_of_injOn e (fun a ha => Finset.mem_preimage.mp ha) e.injective.injOn
    obtain ⟨A', hA', hdisj⟩ := hcov (S.preimage e hinj) (by omega)
    refine ⟨A'.map e, (hmem _).mpr ⟨A', hA', rfl⟩, ?_⟩
    rw [Finset.disjoint_left]
    intro b hb hbS
    obtain ⟨a, haA', rfl⟩ := Finset.mem_map.mp hb
    exact (Finset.disjoint_left.mp hdisj haA') (Finset.mem_preimage.mpr hbS)

/-- THE EXISTENCE WITNESS: all `(m+1)`-subsets of a `(2m+1)`-set form an
Erdős–Lovász family. Uniform by construction; intersecting because two
`(m+1)`-subsets of a `(2m+1)`-set cannot be disjoint; and any `S` with
`|S| ≤ m` leaves `≥ m+1` vertices free, which contain a member disjoint from
`S`. This is what makes `erdosLovaszCards n` nonempty for `n ≥ 1`. -/
theorem isErdosLovaszFamily_powersetCard (m : ℕ) :
    IsErdosLovaszFamily (m + 1)
      (Finset.powersetCard (m + 1) (Finset.univ : Finset (Fin (2 * m + 1)))) := by
  refine ⟨fun A hA => (Finset.mem_powersetCard.mp hA).2, ?_, ?_⟩
  · intro A hA B hB
    have hAc : A.card = m + 1 := (Finset.mem_powersetCard.mp hA).2
    have hBc : B.card = m + 1 := (Finset.mem_powersetCard.mp hB).2
    have hunion : (A ∪ B).card ≤ 2 * m + 1 := by simpa using Finset.card_le_univ (A ∪ B)
    have hsum : (A ∪ B).card + (A ∩ B).card = A.card + B.card :=
      Finset.card_union_add_card_inter A B
    have hpos : 0 < (A ∩ B).card := by omega
    exact Finset.not_disjoint_iff_nonempty_inter.mpr (Finset.card_pos.mp hpos)
  · intro S hS
    have hcomplcard : Sᶜ.card = 2 * m + 1 - S.card := by simpa using Finset.card_compl S
    obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq (s := Sᶜ) (n := m + 1) (by omega)
    refine ⟨A, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ A, hAcard⟩, ?_⟩
    rw [Finset.disjoint_left]
    intro a haA haS
    exact (Finset.mem_compl.mp (hAsub haA)) haS

end Transfer

-- ════════════════════════════════════════════════════════════════════
-- §4 THE COUNTING LOWER BOUND: SIX EDGES WHEN n = 3
-- ════════════════════════════════════════════════════════════════════

section LowerBound

variable {α : Type*} [DecidableEq α] {n : ℕ} {F : Finset (Finset α)}

/-- DOUBLE COUNTING (a hypothesis-free `Finset` identity): summing over the
vertices `x` of `A` the number of members of `G` that avoid `x` gives the same
total as summing over the members `B` of `G` the number of vertices of `A`
outside `B`. Both sides count the pairs `(x, B) ∈ A × G` with `x ∉ B`, so the
proof is `Finset.sum_comm` after unfolding both cards into indicator sums. -/
theorem sum_card_filter_notMem_eq_sum_card_sdiff
    (A : Finset α) (G : Finset (Finset α)) :
    ∑ x ∈ A, (G.filter (fun B => x ∉ B)).card = ∑ B ∈ G, (A \ B).card := by
  simp only [Finset.card_filter, Finset.sdiff_eq_filter]
  exact Finset.sum_comm

/-- THE LOCAL LEMMA behind `IsErdosLovaszFamily.six_le_card`: for `n ≥ 3` and
*every* vertex `x` of the ground type — not merely every vertex used by the
family — at least three members of an Erdős–Lovász family avoid `x`.

The three witnesses come from three applications of clause (3), each to a set
of at most two vertices (hence of card `< n`, which is exactly what `3 ≤ n`
buys):
* `S = {x}` gives `B₁` with `x ∉ B₁`;
* `S = {x, y}` for some `y ∈ B₁` (nonempty since `|B₁| = n ≥ 3`) gives `B₂`
  with `x, y ∉ B₂`, so `B₂ ≠ B₁`;
* `S = {x, z}` for some `z ∈ B₁ ∩ B₂` (nonempty by the intersecting clause)
  gives `B₃` with `x, z ∉ B₃`, so `B₃ ∉ {B₁, B₂}`.

Transversal reading: `{x}` together with any cover of `{B ∈ F | x ∉ B}` covers
all of `F`, so that subfamily has covering number `≥ n - 1 ≥ 2`, and an
intersecting family with covering number `≥ 2` needs at least three members
(two intersecting members share a vertex, which alone would cover them). -/
theorem IsErdosLovaszFamily.three_le_card_filter_notMem
    (h : IsErdosLovaszFamily n F) (hn : 3 ≤ n) (x : α) :
    3 ≤ (F.filter (fun B => x ∉ B)).card := by
  obtain ⟨hsize, hint, hcov⟩ := h
  -- Every one- or two-element `S` is admissible in clause (3) because `3 ≤ n`.
  have hfst : ∀ u v : α, u ∈ ({u, v} : Finset α) := fun u v => Finset.mem_insert_self u {v}
  have hsnd : ∀ u v : α, v ∈ ({u, v} : Finset α) := fun u v =>
    Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
  have hpair : ∀ u v : α, ({u, v} : Finset α).card < n := by
    intro u v
    have hle := Finset.card_insert_le u ({v} : Finset α)
    rw [Finset.card_singleton] at hle
    omega
  -- B₁ avoids x.
  obtain ⟨B₁, hB₁, hd₁⟩ := hcov {x} (by rw [Finset.card_singleton]; omega)
  have hxB₁ : x ∉ B₁ := Finset.disjoint_singleton_right.mp hd₁
  have hB₁card : B₁.card = n := hsize B₁ hB₁
  obtain ⟨y, hy⟩ : B₁.Nonempty := Finset.card_pos.mp (by omega)
  -- B₂ avoids x and a vertex y of B₁, so B₂ ≠ B₁.
  obtain ⟨B₂, hB₂, hd₂⟩ := hcov {x, y} (hpair x y)
  have hxB₂ : x ∉ B₂ := fun hc => Finset.disjoint_left.mp hd₂ hc (hfst x y)
  have hyB₂ : y ∉ B₂ := fun hc => Finset.disjoint_left.mp hd₂ hc (hsnd x y)
  -- B₃ avoids x and a common vertex z of B₁, B₂, so B₃ ∉ {B₁, B₂}.
  obtain ⟨z, hzB₁, hzB₂⟩ := Finset.not_disjoint_iff.mp (hint B₁ hB₁ B₂ hB₂)
  obtain ⟨B₃, hB₃, hd₃⟩ := hcov {x, z} (hpair x z)
  have hxB₃ : x ∉ B₃ := fun hc => Finset.disjoint_left.mp hd₃ hc (hfst x z)
  have hzB₃ : z ∉ B₃ := fun hc => Finset.disjoint_left.mp hd₃ hc (hsnd x z)
  have h12 : B₁ ≠ B₂ := fun hc => hyB₂ (hc ▸ hy)
  have h13 : B₁ ≠ B₃ := fun hc => hzB₃ (hc ▸ hzB₁)
  have h23 : B₂ ≠ B₃ := fun hc => hzB₃ (hc ▸ hzB₂)
  -- Three distinct members inside the subfamily avoiding x.
  have hsub : ({B₁, B₂, B₃} : Finset (Finset α)) ⊆ F.filter (fun B => x ∉ B) := by
    intro B hB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hB
    rcases hB with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hB₁, hxB₁⟩
    · exact Finset.mem_filter.mpr ⟨hB₂, hxB₂⟩
    · exact Finset.mem_filter.mpr ⟨hB₃, hxB₃⟩
  have hne23 : B₂ ∉ ({B₃} : Finset (Finset α)) := Finset.notMem_singleton.mpr h23
  have hne123 : B₁ ∉ ({B₂, B₃} : Finset (Finset α)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact fun hmem => hmem.elim h12 h13
  have hcard3 : ({B₁, B₂, B₃} : Finset (Finset α)).card = 3 := by
    rw [Finset.card_insert_of_notMem hne123, Finset.card_insert_of_notMem hne23,
      Finset.card_singleton]
  calc 3 = ({B₁, B₂, B₃} : Finset (Finset α)).card := hcard3.symm
    _ ≤ (F.filter (fun B => x ∉ B)).card := Finset.card_le_card hsub

omit [DecidableEq α] in
/-- **THE LOWER BOUND `6 ≤ |F|`** for every Erdős–Lovász family of triples,
over every ground type. This is the whole content of `6 ≤ g(3)`; no ground-set
normalization and no finite search is involved, so it holds verbatim for the
`Fin N` families indexing `erdosLovaszCards 3`.

Fix a member `A` (`IsErdosLovaszFamily.nonempty`), so `|A| = 3`. Then

* each of the three vertices `x ∈ A` is avoided by at least three members
  (`three_le_card_filter_notMem`), so
  `∑ x ∈ A, |{B ∈ F | x ∉ B}| ≥ 3 · 3 = 9`;
* that sum equals `∑ B ∈ F, |A \ B|`
  (`sum_card_filter_notMem_eq_sum_card_sdiff`);
* every `B ∈ F` meets `A` by the intersecting clause, so
  `|A \ B| ≤ |A| - 1 = 2`, while the term at `B = A` is `|A \ A| = 0`;
  hence `∑ B ∈ F, |A \ B| ≤ 2 · |F.erase A| = 2 (|F| - 1)`.

Chaining, `9 ≤ 2(|F| - 1)`, i.e. `|F| - 1 ≥ 5` over `ℕ`, i.e. `6 ≤ |F|`.

SHARP: `witnessThree` has `|F| = 6` and meets both estimates almost exactly —
each vertex of its member `{0,1,2}` is avoided by exactly three members and
`∑ B, |A \ B| = 9 ≤ 10`. The same counting for general `n` reads
`3n ≤ (n-1)(|F|-1)`, which is sharp only at `n = 3` and gives nothing
asymptotically; the growing lower bounds are [EL75] and [Si26]. -/
theorem IsErdosLovaszFamily.six_le_card (h : IsErdosLovaszFamily 3 F) : 6 ≤ F.card := by
  classical
  obtain ⟨A, hA⟩ := h.nonempty (by norm_num)
  have hAcard : A.card = 3 := h.1 A hA
  have hlow : 9 ≤ ∑ x ∈ A, (F.filter (fun B => x ∉ B)).card := by
    calc 9 = ∑ _x ∈ A, 3 := by rw [Finset.sum_const, smul_eq_mul, hAcard]
      _ ≤ ∑ x ∈ A, (F.filter (fun B => x ∉ B)).card :=
          Finset.sum_le_sum fun x _ => h.three_le_card_filter_notMem le_rfl x
  have hsdiff : ∀ B ∈ F, (A \ B).card ≤ 2 := by
    intro B hB
    have hsplit := Finset.card_sdiff_add_card_inter A B
    have hpos : 0 < (A ∩ B).card :=
      Finset.card_pos.mpr (Finset.not_disjoint_iff_nonempty_inter.mp (h.2.1 A hA B hB))
    omega
  have hdiag : (A \ A).card = 0 := by rw [Finset.sdiff_self, Finset.card_empty]
  have hup : ∑ B ∈ F, (A \ B).card ≤ 2 * (F.erase A).card := by
    rw [← Finset.sum_erase F (a := A) (f := fun B => (A \ B).card) hdiag]
    calc ∑ B ∈ F.erase A, (A \ B).card ≤ ∑ _B ∈ F.erase A, 2 :=
          Finset.sum_le_sum fun B hB => hsdiff B (Finset.mem_of_mem_erase hB)
      _ = 2 * (F.erase A).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hkey : 9 ≤ 2 * (F.erase A).card := by
    rw [sum_card_filter_notMem_eq_sum_card_sdiff] at hlow
    omega
  have herase : (F.erase A).card = F.card - 1 := Finset.card_erase_of_mem hA
  omega

end LowerBound

-- ════════════════════════════════════════════════════════════════════
-- §5 THE COVER NUMBER g(n) AND ITS PROVED VALUES
-- ════════════════════════════════════════════════════════════════════

/-- The set of family sizes realized by Erdős–Lovász families of `n`-sets,
over all finite ground types (`Fin N`, all `N`). Ground-type independence is
`IsErdosLovaszFamily.map`. -/
def erdosLovaszCards (n : ℕ) : Set ℕ :=
  {k | ∃ (N : ℕ) (F : Finset (Finset (Fin N))), IsErdosLovaszFamily n F ∧ F.card = k}

/-- **The Erdős–Lovász cover number** g(n) (= n(n) of [Ka94] = f(n) of
erdosproblems.com/21 = a(n) of OEIS A391599 at offset 1): the least number of
edges of an `n`-uniform intersecting family whose covering number is `n`.

Junk value: `Nat.sInf ∅ = 0`, so this is 0 whenever no such family exists.
That never happens for `n ≥ 1` (`erdosLovaszCards_nonempty`), and
`zero_lt_erdosLovaszNum` shows the value is then positive;
`erdosLovaszNum_zero = 0` is the honest value at `n = 0`. -/
noncomputable def erdosLovaszNum (n : ℕ) : ℕ := sInf (erdosLovaszCards n)

/-- For `n ≥ 1` some Erdős–Lovász family of `n`-sets exists, so the index set
of the `sInf` is nonempty and `erdosLovaszNum n` is not the junk 0. -/
theorem erdosLovaszCards_nonempty {n : ℕ} (hn : 0 < n) : (erdosLovaszCards n).Nonempty := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact ⟨_, 2 * m + 1, Finset.powersetCard (m + 1) Finset.univ,
    isErdosLovaszFamily_powersetCard m, rfl⟩

/-- ATTAINMENT: for `n ≥ 1` the minimum is realized by an actual family. -/
theorem erdosLovaszNum_mem {n : ℕ} (hn : 0 < n) : erdosLovaszNum n ∈ erdosLovaszCards n :=
  Nat.sInf_mem (erdosLovaszCards_nonempty hn)

/-- DEGENERATE PIN (honest, not junk): at `n = 0` the empty family is
0-uniform, vacuously intersecting, and no set has card `< 0`, so `g(0) = 0`.
This is why OEIS A391599 has offset 1 and every substantive statement here
assumes `0 < n`. -/
theorem erdosLovaszNum_zero : erdosLovaszNum 0 = 0 := by
  have hmem : (0 : ℕ) ∈ erdosLovaszCards 0 :=
    ⟨0, ∅, ⟨fun A hA => absurd hA (Finset.notMem_empty A),
      fun A hA => absurd hA (Finset.notMem_empty A),
      fun S hS => absurd hS (Nat.not_lt_zero _)⟩, rfl⟩
  exact Nat.le_zero.mp (Nat.sInf_le hmem)

/-- `n ≤ g(n)`: one vertex per member of a smaller family would be a cover of
size `< n`. -/
theorem le_erdosLovaszNum {n : ℕ} (hn : 0 < n) : n ≤ erdosLovaszNum n := by
  obtain ⟨N, F, hF, hcard⟩ := erdosLovaszNum_mem hn
  exact hcard ▸ hF.le_card

/-- The value is positive for `n ≥ 1` — in particular the junk 0 of the
`sInf` is not attained there. -/
theorem zero_lt_erdosLovaszNum {n : ℕ} (hn : 0 < n) : 0 < erdosLovaszNum n :=
  lt_of_lt_of_le hn (le_erdosLovaszNum hn)

/-- `n + 1 ≤ g(n)` for `n ≥ 2`, sharp at `n = 2`. -/
theorem succ_le_erdosLovaszNum {n : ℕ} (hn : 2 ≤ n) : n + 1 ≤ erdosLovaszNum n := by
  obtain ⟨N, F, hF, hcard⟩ := erdosLovaszNum_mem (n := n) (by omega)
  exact hcard ▸ hF.succ_le_card hn

/-- `g(m+1) ≤ C(2m+1, m+1)`, from the all-`(m+1)`-subsets-of-a-`(2m+1)`-set
witness. Tight at `m = 0` (g(1) = 1) and `m = 1` (g(2) = 3); far from tight
afterwards (C(5,3) = 10 versus g(3) = 6). -/
theorem erdosLovaszNum_le_choose (m : ℕ) :
    erdosLovaszNum (m + 1) ≤ (2 * m + 1).choose (m + 1) := by
  refine Nat.sInf_le ⟨2 * m + 1, Finset.powersetCard (m + 1) Finset.univ,
    isErdosLovaszFamily_powersetCard m, ?_⟩
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- `g(1) = 1` (OEIS A391599, a(1) = 1): a single singleton family. -/
theorem erdosLovaszNum_one : erdosLovaszNum 1 = 1 := by
  have hchoose : Nat.choose (2 * 0 + 1) (0 + 1) = 1 := by decide
  have hle : erdosLovaszNum 1 ≤ 1 := by
    have h0 := erdosLovaszNum_le_choose 0
    rwa [hchoose] at h0
  have hge : 1 ≤ erdosLovaszNum 1 := le_erdosLovaszNum one_pos
  omega

/-- `g(2) = 3` (OEIS A391599, a(2) = 3): the triangle. Upper bound from the
`C(3,2) = 3` witness, lower bound from `succ_le_erdosLovaszNum`. -/
theorem erdosLovaszNum_two : erdosLovaszNum 2 = 3 := by
  have hchoose : Nat.choose (2 * 1 + 1) (1 + 1) = 3 := by decide
  have hle : erdosLovaszNum 2 ≤ 3 := by
    have h0 := erdosLovaszNum_le_choose 1
    rwa [hchoose] at h0
  have hge : 3 ≤ erdosLovaszNum 2 := succ_le_erdosLovaszNum le_rfl
  omega

/-- A 6-edge Erdős–Lovász family of triples on 6 vertices, found by exhaustive
search (6 vertices is the least possible: there is no 6-edge witness on ≤ 5
vertices). It witnesses `g(3) ≤ 6`, the upper half of `g(3) = 6`.

The search also reported no 4- or 5-edge witness on ≤ 11 vertices, exhaustive
for ≤ 5 edges by the span bound `3 + 2·4`. That search is now SUPERSEDED and
no longer load-bearing: `IsErdosLovaszFamily.six_le_card` proves the same
non-existence for every ground type, by counting rather than by enumeration. -/
def witnessThree : Finset (Finset (Fin 6)) :=
  {{0, 1, 2}, {0, 1, 3}, {0, 4, 5}, {1, 4, 5}, {2, 3, 4}, {2, 3, 5}}

set_option maxRecDepth 2000 in
/-- `witnessThree` is an Erdős–Lovász family of triples. Routed through the τ
bridge `isErdosLovaszFamily_of_coveringNumber_eq` rather than a direct
`decide` on `IsErdosLovaszFamily`: the bridge turns the `∀ S : Finset (Fin 6)`
clause into a `coveringNumber` evaluation, which is the kernel-`decide` shape
already exercised over `Fin 6` in `Erdos/CoveringNumber.lean`. -/
theorem isErdosLovaszFamily_witnessThree : IsErdosLovaszFamily 3 witnessThree :=
  isErdosLovaszFamily_of_coveringNumber_eq (by decide) (by decide) (by decide)

/-- `g(3) ≤ 6`, by `witnessThree`. -/
theorem erdosLovaszNum_three_le : erdosLovaszNum 3 ≤ 6 :=
  Nat.sInf_le ⟨6, witnessThree, isErdosLovaszFamily_witnessThree, by decide⟩

/-- **`6 ≤ g(3)`** — PROVED HERE, not archived. The minimum is attained by an
actual family (`erdosLovaszNum_mem` at `n = 3`), and every Erdős–Lovász family
of triples over every ground type has at least six members
(`IsErdosLovaszFamily.six_le_card`). No ground-set normalization and no finite
search enter: the counting argument of §4 is uniform in the ground type, so
the unbounded `∃ N` of `erdosLovaszCards` is handled directly.

ATTRIBUTION. The `tripathi_` prefix is kept for name stability, but priority
for `g(3) = 6` is [FOT96], not [Tr14] — Tripathi's own text says the result
was proved in [FOT96] and that his §2 gives "a different proof" of it (both
quoted verbatim in the file header); [Tr14]'s own new value is `g(4) = 9`.
The proof formalized here is a third one: a double count, which unlike
[Tr14]'s route needs neither his minimal-length/degree dichotomy lemma nor
the notion of minimal length, and therefore disposes of every `|F| ≤ 5` in
one step rather than of `|F| = 5` alone. -/
theorem tripathi_six_le_erdosLovaszNum_three : 6 ≤ erdosLovaszNum 3 := by
  obtain ⟨N, F, hF, hcard⟩ := erdosLovaszNum_mem (n := 3) (by norm_num)
  exact hcard ▸ hF.six_le_card

/-- **`g(3) = 6`** (OEIS A391599, a(3) = 6; [FOT96], reproved in [Tr14]).
SORRY-FREE: the upper bound is `witnessThree`, the lower bound is the §4
counting argument. -/
theorem tripathi_erdosLovaszNum_three : erdosLovaszNum 3 = 6 :=
  le_antisymm erdosLovaszNum_three_le tripathi_six_le_erdosLovaszNum_three

-- ════════════════════════════════════════════════════════════════════
-- §6 LITERATURE STATEMENTS (INTENDED SORRIES)
-- ════════════════════════════════════════════════════════════════════

/-- **[EL75] lower bound** (literature, INTENDED SORRY): `8n/3 − 3 ≤ g(n)`
for every `n ≥ 1`. Cast to `ℝ` before subtracting. Erdős and Lovász also
proved `g(r) ≪ r^{3/2} log r`, superseded by [Ka92], [Ka94]. -/
theorem erdos_lovasz_lower_bound (n : ℕ) (hn : 0 < n) :
    (8 : ℝ) / 3 * n - 3 ≤ erdosLovaszNum n := by
  -- INTENDED SORRY: statement-archive lane. [EL75]'s argument is a genuine
  -- (and sizeable) piece of extremal set theory, out of scope here.
  sorry

/-- **[Ka94]** (literature, INTENDED SORRY): `g(r) = O(r)`, the solution of
Erdős' $500 problem, in explicit-constant form. The constant is not explicit
in [Ka94] (a random-lines-in-a-projective-plane argument via [Ka92]). -/
theorem kahn_erdosLovaszNum_le_linear :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → (erdosLovaszNum n : ℝ) ≤ C * n := by
  -- INTENDED SORRY: statement-archive lane. [Ka94] is a full research paper.
  sorry

/-- **[Si26] Theorem 1(i)** (literature, INTENDED SORRY): `3n − 4 ≤ g(n)` for
every `n ≥ 1`, by an elementary degree-peeling argument. Stated in `ℤ` so the
subtraction is honest. -/
theorem sivashankar_three_mul_sub_four (n : ℕ) (hn : 0 < n) :
    3 * (n : ℤ) - 4 ≤ erdosLovaszNum n := by
  -- INTENDED SORRY: statement-archive lane. [Si26, §2–§3].
  sorry

/-- **[Si26] Theorem 1(ii)** (literature, INTENDED SORRY): for every `ε > 0`,
eventually `((41 − √19)/12 − ε) n ≤ g(n)`. The constant `(41 − √19)/12 =
3.05342…` exceeds 3, so this settles Erdős' question whether `g(r) < 3r`
(`not_threeMulAddBigO_of_asymptotic_lower_bound`). `Real.sqrt` is applied to
the nonnegative numeral 19, so it is off its junk branch;
`sivashankarConst_bounds` pins the value numerically. -/
theorem sivashankar_asymptotic_lower_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ((41 - Real.sqrt 19) / 12 - ε) * n ≤ erdosLovaszNum n := by
  -- INTENDED SORRY: statement-archive lane. [Si26, §4] uses Kahn's
  -- small-codegree hypergraph edge-colouring theorem.
  sorry

/-- **[Tr14]** (literature, INTENDED SORRY): `g(4) = 9` (OEIS A391599,
a(4) = 9). [Ba21] showed the extremal example is unique and "notably
asymmetric" (erdosproblems.com/21, comment of 03 Dec 2025). A 9-edge witness
on 11 vertices was checked computationally while preparing this file, but is
not transcribed here: a kernel `decide` over `Finset (Fin 11)` enumerates
2^11 subsets, so `g(4) ≤ 9` is archived rather than proved. -/
theorem tripathi_erdosLovaszNum_four : erdosLovaszNum 4 = 9 := by
  -- INTENDED SORRY: statement-archive lane; no witness family transcribed
  -- here, so both inequalities are archived.
  sorry

/-- **[Ba21]** (literature, INTENDED SORRY): `g(5) = 13` (OEIS A391599,
a(5) = 13), with exactly three non-isomorphic extremal examples
(erdosproblems.com/21, comment of 03 Dec 2025). -/
theorem barat_erdosLovaszNum_five : erdosLovaszNum 5 = 13 := by
  -- INTENDED SORRY: statement-archive lane; computer search in [Ba21].
  sorry

/-- **[Ba21]** (literature, INTENDED SORRY): `g(6) ≤ 18`. [Ba21] determine
`m(6) = 18`, where `m(r)` is the minimum number of lines of a projective plane
with covering number `r`; such a configuration is a 6-uniform intersecting
family with τ = 6, whence `g(6) ≤ 18`. The exact value of g(6) is unknown,
which is why OEIS A391599 stops at a(5) and carries the `more` keyword.

The companion `13 ≤ g(6)` quoted on erdosproblems.com/21 is NOT independent
literature — it is [EL75] evaluated at n = 6, where `8·6/3 − 3 = 13` exactly;
see `thirteen_le_erdosLovaszNum_six_of_erdos_lovasz`, which is sorry-free. -/
theorem barat_erdosLovaszNum_six_le : erdosLovaszNum 6 ≤ 18 := by
  -- INTENDED SORRY: statement-archive lane.
  sorry

-- ════════════════════════════════════════════════════════════════════
-- §7 CONSEQUENCES OF THE LITERATURE STATEMENTS (SORRY-FREE)
-- ════════════════════════════════════════════════════════════════════

/-- Numeric pin for [Si26]'s constant: `61/20 < (41 − √19)/12 < 3.054`. In
particular the constant exceeds 3, which is the whole point of Theorem 1(ii),
and it is not the junk branch of `Real.sqrt`. -/
theorem sivashankarConst_bounds :
    (61 : ℝ) / 20 < (41 - Real.sqrt 19) / 12 ∧ (41 - Real.sqrt 19) / 12 < 3.054 := by
  have hsq : Real.sqrt 19 ^ 2 = 19 := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 19 := Real.sqrt_nonneg 19
  constructor
  · nlinarith [hsq, hnn]
  · nlinarith [hsq, hnn]

/-- SORRY-FREE DERIVATION behind `sivashankar_lower_bound_61_20`: the
`61/20 = 3.05` rounding quoted in the erdosproblems.com/21 comment thread
(Jun 2026) follows from Theorem 1(ii), taken here as a hypothesis, because
`61/20 < (41 − √19)/12` (`sivashankarConst_bounds`). -/
theorem lower_bound_61_20_of_asymptotic
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
      ((41 - Real.sqrt 19) / 12 - ε) * n ≤ erdosLovaszNum n)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ((61 : ℝ) / 20 - ε) * n ≤ erdosLovaszNum n := by
  filter_upwards [h ε hε] with n hn
  refine le_trans ?_ hn
  have hconst : (61 : ℝ) / 20 < (41 - Real.sqrt 19) / 12 := sivashankarConst_bounds.1
  exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)

/-- The `61/20` form of [Si26]'s bound. DERIVED from the archived
`sivashankar_asymptotic_lower_bound`, hence inheriting its `sorryAx`; the
derivation itself is the sorry-free `lower_bound_61_20_of_asymptotic`. -/
theorem sivashankar_lower_bound_61_20 (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ((61 : ℝ) / 20 - ε) * n ≤ erdosLovaszNum n :=
  lower_bound_61_20_of_asymptotic sivashankar_asymptotic_lower_bound ε hε

/-- SORRY-FREE DERIVATION behind `kahn_erdosLovaszNum_isBigO`: an explicit
linear bound gives Mathlib's `IsBigO` form. -/
theorem isBigO_of_forall_le_linear {C : ℝ}
    (h : ∀ n : ℕ, 1 ≤ n → (erdosLovaszNum n : ℝ) ≤ C * n) :
    (fun n : ℕ => (erdosLovaszNum n : ℝ)) =O[Filter.atTop] (fun n : ℕ => (n : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound |C| ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have h1 : (erdosLovaszNum n : ℝ) ≤ C * n := h n hn
  have h2 : C * (n : ℝ) ≤ |C| * n :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (Nat.cast_nonneg n)
  rw [Real.norm_natCast, Real.norm_natCast]
  linarith

/-- [Ka94]'s bound in Mathlib's asymptotic normal form. DERIVED from the
archived `kahn_erdosLovaszNum_le_linear`, hence inheriting its `sorryAx`; the
derivation itself is the sorry-free `isBigO_of_forall_le_linear`. -/
theorem kahn_erdosLovaszNum_isBigO :
    (fun n : ℕ => (erdosLovaszNum n : ℝ)) =O[Filter.atTop] (fun n : ℕ => (n : ℝ)) := by
  obtain ⟨C, hC⟩ := kahn_erdosLovaszNum_le_linear
  exact isBigO_of_forall_le_linear hC

/-- CONTENT CHECK on `kahn_erdosLovaszNum_le_linear`: every admissible
constant satisfies `1 ≤ C`, so the statement is not satisfiable by a trivial
`C ≤ 0`. Uses only the proved `erdosLovaszNum_one`. -/
theorem one_le_of_forall_le_linear {C : ℝ}
    (h : ∀ n : ℕ, 1 ≤ n → (erdosLovaszNum n : ℝ) ≤ C * n) : 1 ≤ C := by
  have h1 := h 1 le_rfl
  rw [erdosLovaszNum_one] at h1
  simpa using h1

/-- The `13 ≤ g(6)` half of the erdosproblems.com/21 bound `13 ≤ f(6) ≤ 18`,
derived from [EL75] taken as a hypothesis (this file's
`erdos_lovasz_lower_bound 6 (by norm_num)` instantiates it): at n = 6 the
Erdős–Lovász bound reads `8·6/3 − 3 = 13`, so the quoted lower bound is that
theorem and nothing more. Sorry-free as stated.

NOTE (vacuity audit): the hypothesis and conclusion here are interderivable
numeral facts — this declaration is a provenance record pinning where the
erdosproblems bound comes from, not independent mathematical content. -/
theorem thirteen_le_erdosLovaszNum_six_of_erdos_lovasz
    (h : (8 : ℝ) / 3 * ((6 : ℕ) : ℝ) - 3 ≤ erdosLovaszNum 6) : 13 ≤ erdosLovaszNum 6 := by
  norm_num at h
  exact_mod_cast h

/-- The folklore speculation that `g(r) = 3r + O(1)`, recorded in OEIS
A391599 ("it has been speculated that a(n) = 3*n + O(1)") and on
erdosproblems.com/21 (attributed there to [Ka94]). Stated as a `Prop`, NOT as
a theorem: [Si26, Thm 1(ii)] refutes it
(`not_threeMulAddBigO_of_asymptotic_lower_bound`). -/
def ThreeMulAddBigO : Prop :=
  ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → |(erdosLovaszNum n : ℝ) - 3 * n| ≤ c

-- Ground checks for the predicate SHAPE (vacuity audit): the `∃ c, ∀ n, …`
-- pattern is neither unsatisfiable nor tautological — it holds for `3n` and
-- fails for `4n`.
example : ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → |((3 * n : ℕ) : ℝ) - 3 * n| ≤ c := by
  refine ⟨0, fun n _ => ?_⟩
  push_cast
  simp

example : ¬ ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → |((4 * n : ℕ) : ℝ) - 3 * n| ≤ c := by
  rintro ⟨c, hc⟩
  have key : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ c := by
    intro n hn
    have habs := (abs_le.mp (hc n hn)).2
    push_cast at habs
    linarith
  have hle : ((⌈c⌉₊ + 1 : ℕ) : ℝ) ≤ c := key (⌈c⌉₊ + 1) (Nat.le_add_left 1 _)
  have hceil : c ≤ (⌈c⌉₊ : ℝ) := Nat.le_ceil c
  push_cast at hle
  linarith

/-- REFUTATION (sorry-free, hypothesis = [Si26, Thm 1(ii)]): the asymptotic
lower bound with constant `(41 − √19)/12 > 3` is incompatible with
`g(r) = 3r + O(1)`. Instantiating the hypothesis with
`sivashankar_asymptotic_lower_bound` gives `¬ ThreeMulAddBigO` outright,
conditional only on that literature statement. -/
theorem not_threeMulAddBigO_of_asymptotic_lower_bound
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
      ((41 - Real.sqrt 19) / 12 - ε) * n ≤ erdosLovaszNum n) :
    ¬ ThreeMulAddBigO := by
  rintro ⟨c, hc⟩
  set c₀ : ℝ := (41 - Real.sqrt 19) / 12 with hc₀def
  have hlow : (61 : ℝ) / 20 < c₀ := by rw [hc₀def]; exact sivashankarConst_bounds.1
  have hc₀ : 3 < c₀ := by linarith
  set ε : ℝ := (c₀ - 3) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨n, ⟨hbound, hn1⟩, hnbig⟩ :=
    (((h ε hε).and (Filter.eventually_ge_atTop 1)).and
      (Filter.eventually_gt_atTop ⌈c / ε⌉₊)).exists
  have hce : c₀ - ε = 3 + ε := by rw [hεdef]; ring
  rw [hce] at hbound
  have hcabs : (erdosLovaszNum n : ℝ) - 3 * n ≤ c := (abs_le.mp (hc n hn1)).2
  have hceil : c / ε < (n : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hnbig)
  have hcn : c < (n : ℝ) * ε := (div_lt_iff₀ hε).mp hceil
  nlinarith [hbound, hcabs, hcn]

-- ════════════════════════════════════════════════════════════════════
-- §8 GROUND CHECKS AND SATISFIABILITY
-- ════════════════════════════════════════════════════════════════════

section GroundChecks

/-! ### `IsErdosLovaszFamily`: positive instances -/

-- g(1): the one-edge family; g(2): the triangle (`= powersetCard 2 univ`,
-- i.e. the `m = 1` case of `isErdosLovaszFamily_powersetCard`).
example : IsErdosLovaszFamily 1 ({{0}} : Finset (Finset (Fin 1))) := by decide
example : IsErdosLovaszFamily 2 ({{0, 1}, {1, 2}, {0, 2}} : Finset (Finset (Fin 3))) := by
  decide
example :
    Finset.powersetCard 2 (Finset.univ : Finset (Fin 3)) = {{0, 1}, {0, 2}, {1, 2}} := by
  decide
-- g(3): `isErdosLovaszFamily_witnessThree`, with the edge count.
example : witnessThree.card = 6 := by decide

/-! ### Negative instances: each of the three clauses is load-bearing -/

-- (1) uniformity fails.
example : ¬ IsErdosLovaszFamily 2 ({{0, 1}, {0, 1, 2}} : Finset (Finset (Fin 3))) := by
  decide
-- (2) intersecting fails.
example : ¬ IsErdosLovaszFamily 1 ({{0}, {1}} : Finset (Finset (Fin 2))) := by decide
-- (3) fails: the common vertex 0 covers both edges, so τ = 1 < 2.
example : ¬ IsErdosLovaszFamily 2 ({{0, 1}, {0, 2}} : Finset (Finset (Fin 3))) := by decide
-- (3) fails for the empty family whenever n ≥ 1 (S = ∅ has no disjoint
-- member) — this is why 0 < g(n) for n ≥ 1 — but holds at n = 0, which is
-- the honest `erdosLovaszNum_zero = 0`.
example : ¬ IsErdosLovaszFamily 1 (∅ : Finset (Finset (Fin 1))) := by decide
example : IsErdosLovaszFamily 0 (∅ : Finset (Finset (Fin 1))) := by decide

/-! ### The `∅ ∉ F` guard and the `coveringNumber` junk branch -/

-- JUNK PIN: a family containing ∅ is never an Erdős–Lovász family, so the
-- junk branch of `coveringNumber` is unreachable from `IsErdosLovaszFamily`.
example : ¬ IsErdosLovaszFamily 1 ({∅, {0}} : Finset (Finset (Fin 1))) := by decide
-- ...and this is the junk value that would otherwise be in play.
example : coveringNumber ({∅, {0}} : Finset (Finset (Fin 1))) = 0 := by decide
-- The guard as proved for the witness.
example : ∅ ∉ witnessThree := isErdosLovaszFamily_witnessThree.empty_notMem

/-! ### The τ bridge, both directions, on the `n = 3` witness -/

-- Forward (OEIS form → τ = n); the reverse direction is what proves
-- `isErdosLovaszFamily_witnessThree` in the first place.
example : coveringNumber witnessThree = 3 :=
  isErdosLovaszFamily_witnessThree.coveringNumber_eq (by norm_num)

/-! ### Satisfiability of hypothesis bundles

Every theorem of §1–§5 with hypotheses is instantiated jointly at a concrete
model (`witnessThree`, `n = 3`), together with its conclusion. -/

-- `IsErdosLovaszFamily.*`: the bundle (h, 0 < n) and (h, 2 ≤ n) at n = 3.
example : IsErdosLovaszFamily 3 witnessThree ∧ 0 < 3 ∧ 2 ≤ 3 :=
  ⟨isErdosLovaszFamily_witnessThree, by norm_num, by norm_num⟩
example : witnessThree.Nonempty := isErdosLovaszFamily_witnessThree.nonempty (by norm_num)
example : 3 ≤ witnessThree.card := isErdosLovaszFamily_witnessThree.le_card
example : 3 + 1 ≤ witnessThree.card :=
  isErdosLovaszFamily_witnessThree.succ_le_card (by norm_num)
example : coveringNumber witnessThree ≤ 3 :=
  isErdosLovaszFamily_witnessThree.coveringNumber_le
    (isErdosLovaszFamily_witnessThree.nonempty (by norm_num))
example : 3 ≤ coveringNumber witnessThree := isErdosLovaszFamily_witnessThree.le_coveringNumber

-- `coveringNumber_le_card_family` (∅ ∉ F) and `coveringNumber_add_one_le_card`
-- (∅ ∉ F, intersecting, 2 ≤ |F|) — jointly satisfied, conclusions nontrivial
-- (3 ≤ 6 and 3 + 1 ≤ 6).
example : coveringNumber witnessThree ≤ witnessThree.card :=
  coveringNumber_le_card_family isErdosLovaszFamily_witnessThree.empty_notMem
example : coveringNumber witnessThree + 1 ≤ witnessThree.card :=
  coveringNumber_add_one_le_card isErdosLovaszFamily_witnessThree.empty_notMem
    isErdosLovaszFamily_witnessThree.2.1 (by decide)

-- `IsErdosLovaszFamily.map`: pushing the witness along `Fin 6 ↪ Fin 7`
-- preserves the property AND the edge count — the ground-set independence
-- that makes the `∃ N` in `erdosLovaszCards` harmless.
example :
    IsErdosLovaszFamily 3 (witnessThree.map
      (Finset.mapEmbedding ⟨Fin.castSucc, Fin.castSucc_injective 6⟩).toEmbedding) :=
  isErdosLovaszFamily_witnessThree.map _
example :
    (witnessThree.map
      (Finset.mapEmbedding ⟨Fin.castSucc, Fin.castSucc_injective 6⟩).toEmbedding).card = 6 := by
  rw [Finset.card_map]
  decide

/-! ### §4, the counting lower bound, evaluated at the extremal family

Both estimates behind `IsErdosLovaszFamily.six_le_card` are (nearly) attained
by `witnessThree`, so neither is slack enough to be uninformative. -/

-- `three_le_card_filter_notMem`: EXACTLY three members of `witnessThree` avoid
-- each of the six vertices, so the bound `3 ≤ …` is attained, not slack.
example : ∀ x : Fin 6, (witnessThree.filter (fun B => x ∉ B)).card = 3 := by decide
-- The lemma itself, instantiated (its hypothesis `3 ≤ n` holds at `n = 3`).
example : 3 ≤ (witnessThree.filter (fun B => (0 : Fin 6) ∉ B)).card :=
  isErdosLovaszFamily_witnessThree.three_le_card_filter_notMem le_rfl 0
-- The `x` of `three_le_card_filter_notMem` ranges over the whole ground type,
-- not just the vertices used by `F`: here `6 : Fin 7` lies outside the image
-- of `Fin.castSucc`, i.e. outside the support of the transported witness.
example :
    3 ≤ ((witnessThree.map
        (Finset.mapEmbedding ⟨Fin.castSucc, Fin.castSucc_injective 6⟩).toEmbedding).filter
      (fun B => (6 : Fin 7) ∉ B)).card :=
  (isErdosLovaszFamily_witnessThree.map _).three_le_card_filter_notMem le_rfl 6

-- The double count at `A = {0,1,2} ∈ witnessThree`: `3 · 3 = 9` on the left,
-- `0 + 1 + 2 + 2 + 2 + 2 = 9` on the right — the identity
-- `sum_card_filter_notMem_eq_sum_card_sdiff` at a concrete instance.
example :
    ∑ x ∈ ({0, 1, 2} : Finset (Fin 6)),
      (witnessThree.filter (fun B => x ∉ B)).card = 9 := by decide
example : ∑ B ∈ witnessThree, (({0, 1, 2} : Finset (Fin 6)) \ B).card = 9 := by decide
example :
    ∑ x ∈ ({0, 1, 2} : Finset (Fin 6)),
        (witnessThree.filter (fun B => x ∉ B)).card
      = ∑ B ∈ witnessThree, (({0, 1, 2} : Finset (Fin 6)) \ B).card :=
  sum_card_filter_notMem_eq_sum_card_sdiff _ _
-- The ceiling the count is compared against, `2 · (|F| − 1) = 10`: the gap
-- `9 ≤ 10` is exactly why 6 edges are possible and 5 are not (`2 · 4 = 8 < 9`).
example : 2 * (witnessThree.erase {0, 1, 2}).card = 10 := by decide

-- The conclusion at the extremal family: `6 ≤ 6`, so the bound is sharp.
example : 6 ≤ witnessThree.card := isErdosLovaszFamily_witnessThree.six_le_card

-- THE LOWER BOUND IN NEGATIVE FORM, which is what `6 ≤ g(3)` really asserts:
-- no family of at most five triples is an Erdős–Lovász family, over ANY
-- ground type. `decide` cannot reach this — the ground type is unbounded —
-- and no normalization to a fixed `Fin N` is used to get there.
example : ∀ k < 6, k ∉ erdosLovaszCards 3 := by
  rintro k hk ⟨N, F, hF, rfl⟩
  have h6 : 6 ≤ F.card := hF.six_le_card
  omega
-- ...and 6 itself IS realized, so the bound is exactly the truth.
example : (6 : ℕ) ∈ erdosLovaszCards 3 ∧ ∀ k < 6, k ∉ erdosLovaszCards 3 := by
  refine ⟨⟨6, witnessThree, isErdosLovaszFamily_witnessThree, by decide⟩, ?_⟩
  rintro k hk ⟨N, F, hF, rfl⟩
  have h6 : 6 ≤ F.card := hF.six_le_card
  omega

-- `erdosLovaszCards` is inhabited at n = 1, 2, 3 by the three witnesses, so
-- the `sInf` defining `erdosLovaszNum` is never taken over an empty set there.
example : (1 : ℕ) ∈ erdosLovaszCards 1 := ⟨1, {{0}}, by decide, by decide⟩
example : (3 : ℕ) ∈ erdosLovaszCards 2 :=
  ⟨3, {{0, 1}, {1, 2}, {0, 2}}, by decide, by decide⟩
example : (6 : ℕ) ∈ erdosLovaszCards 3 :=
  ⟨6, witnessThree, isErdosLovaszFamily_witnessThree, by decide⟩

-- The `∀ᶠ … in atTop` statements of §6–§7 quantify over a proper filter, so
-- they are not vacuously true.
example : (Filter.atTop : Filter ℕ).NeBot := inferInstance

/-! ### The archived literature statements, checked at the proved values

Each sorried bound of §6 is evaluated at every `n` whose value this file
proves, so the archived statements are consistent with the proved ones. -/

-- [EL75] `8n/3 − 3 ≤ g(n)`: at n = 1, −1/3 ≤ 1; at n = 2, 7/3 ≤ 3.
example : (8 : ℝ) / 3 * ((1 : ℕ) : ℝ) - 3 ≤ erdosLovaszNum 1 := by
  rw [erdosLovaszNum_one]
  norm_num
example : (8 : ℝ) / 3 * ((2 : ℕ) : ℝ) - 3 ≤ erdosLovaszNum 2 := by
  rw [erdosLovaszNum_two]
  norm_num

-- [Si26](i) `3n − 4 ≤ g(n)`: at n = 1, −1 ≤ 1; at n = 2, 2 ≤ 3.
example : 3 * ((1 : ℕ) : ℤ) - 4 ≤ (erdosLovaszNum 1 : ℤ) := by
  rw [erdosLovaszNum_one]
  norm_num
example : 3 * ((2 : ℕ) : ℤ) - 4 ≤ (erdosLovaszNum 2 : ℤ) := by
  rw [erdosLovaszNum_two]
  norm_num

-- [Ka94] `g(n) ≤ Cn` is consistent with every value proved here at C = 3:
-- g(1) = 1 ≤ 3, g(2) = 3 ≤ 6, g(3) ≤ 6 ≤ 9. (`one_le_of_forall_le_linear`
-- shows no C < 1 can work, so the archived ∃C is not satisfiable trivially.)
example : (erdosLovaszNum 1 : ℝ) ≤ 3 * 1 ∧ (erdosLovaszNum 2 : ℝ) ≤ 3 * 2 ∧
    (erdosLovaszNum 3 : ℝ) ≤ 3 * 3 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [erdosLovaszNum_one]; norm_num
  · rw [erdosLovaszNum_two]; norm_num
  · have h6 : (erdosLovaszNum 3 : ℝ) ≤ 6 := by exact_mod_cast erdosLovaszNum_three_le
    linarith

-- The OEIS A391599 data row, as far as this file proves it: a(1) = 1,
-- a(2) = 3, a(3) = 6 — the first three terms of `1, 3, 6, 9, 13`, all three
-- now sorry-free. (a(4) = 9 and a(5) = 13 remain archived.)
example : erdosLovaszNum 1 = 1 ∧ erdosLovaszNum 2 = 3 ∧ erdosLovaszNum 3 = 6 :=
  ⟨erdosLovaszNum_one, erdosLovaszNum_two, tripathi_erdosLovaszNum_three⟩

end GroundChecks

-- ════════════════════════════════════════════════════════════════════
-- §9 AXIOM AUDIT
-- ════════════════════════════════════════════════════════════════════

/-! Every named declaration of this file, in source order. The 42 Tier 1
declarations must report exactly `[propext, Classical.choice, Quot.sound]`;
the 7 Tier 2 statements and the 2 Tier 3 consequences must additionally
report `sorryAx`, and nothing must report anything else. No `native_decide`,
no `@[implemented_by]`/`@[extern]`/`@[csimp]`, no declared `axiom`. -/

section AxiomAudit

-- §1 the family predicate.
#print axioms IsErdosLovaszFamily
#print axioms instDecidableIsErdosLovaszFamily
#print axioms isErdosLovaszFamily_iff
#print axioms IsErdosLovaszFamily.empty_notMem
#print axioms not_isErdosLovaszFamily_of_empty_mem
#print axioms IsErdosLovaszFamily.nonempty

-- §2 the τ bridge.
#print axioms coveringNumber_le_card_family
#print axioms IsErdosLovaszFamily.le_coveringNumber
#print axioms IsErdosLovaszFamily.coveringNumber_le
#print axioms IsErdosLovaszFamily.coveringNumber_eq
#print axioms isErdosLovaszFamily_of_coveringNumber_eq
#print axioms coveringNumber_add_one_le_card
#print axioms IsErdosLovaszFamily.le_card
#print axioms IsErdosLovaszFamily.succ_le_card

-- §3 transfer and the existence witness.
#print axioms IsErdosLovaszFamily.map
#print axioms isErdosLovaszFamily_powersetCard

-- §4 the counting lower bound.
#print axioms sum_card_filter_notMem_eq_sum_card_sdiff
#print axioms IsErdosLovaszFamily.three_le_card_filter_notMem
#print axioms IsErdosLovaszFamily.six_le_card

-- §5 g(n) and its proved values.
#print axioms erdosLovaszCards
#print axioms erdosLovaszNum
#print axioms erdosLovaszCards_nonempty
#print axioms erdosLovaszNum_mem
#print axioms erdosLovaszNum_zero
#print axioms le_erdosLovaszNum
#print axioms zero_lt_erdosLovaszNum
#print axioms succ_le_erdosLovaszNum
#print axioms erdosLovaszNum_le_choose
#print axioms erdosLovaszNum_one
#print axioms erdosLovaszNum_two
#print axioms witnessThree
#print axioms isErdosLovaszFamily_witnessThree
#print axioms erdosLovaszNum_three_le
#print axioms tripathi_six_le_erdosLovaszNum_three
#print axioms tripathi_erdosLovaszNum_three

-- §6 TIER 2 — the archived literature statements; these must and do report
-- `sorryAx`.
#print axioms erdos_lovasz_lower_bound
#print axioms kahn_erdosLovaszNum_le_linear
#print axioms sivashankar_three_mul_sub_four
#print axioms sivashankar_asymptotic_lower_bound
#print axioms tripathi_erdosLovaszNum_four
#print axioms barat_erdosLovaszNum_five
#print axioms barat_erdosLovaszNum_six_le

-- §7 consequences. The two TIER 3 entries (`sivashankar_lower_bound_61_20`,
-- `kahn_erdosLovaszNum_isBigO`) inherit `sorryAx` from §6 by design; the
-- hypothesis-form derivations beside them do not.
#print axioms sivashankarConst_bounds
#print axioms lower_bound_61_20_of_asymptotic
#print axioms sivashankar_lower_bound_61_20
#print axioms isBigO_of_forall_le_linear
#print axioms kahn_erdosLovaszNum_isBigO
#print axioms one_le_of_forall_le_linear
#print axioms thirteen_le_erdosLovaszNum_six_of_erdos_lovasz
#print axioms ThreeMulAddBigO
#print axioms not_threeMulAddBigO_of_asymptotic_lower_bound

end AxiomAudit
