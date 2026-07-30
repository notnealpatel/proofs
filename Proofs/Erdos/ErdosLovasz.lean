/-
  Erdős Problem #21 / OEIS A391599 — the Erdős–Lovász cover number g(r).

  STATUS: STATEMENT ARCHIVE (USER directive). The literature theorems below
  carry INTENDED, DISCLOSED sorries; everything else in this file is proved.
  See "SORRY LEDGER" at the end of this header for the exact list.

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

  GROUND TRUTH (pinned live, 2026-07-30).
  * OEIS A391599 (live pull via the `oeis` CLI): DATA 1, 3, 6, 9, 13 with
    offset 1 per the entry; keywords nonn,hard,more.
    So g(1)=1, g(2)=3, g(3)=6, g(4)=9, g(5)=13.
  * erdosproblems.com problem 21 (live pull via the `erdos` CLI): the
    linearity question is recorded as answered; $500 prize noted on the
    site. Small values g(3)=6, g(4)=9 [Tr14]; g(5)=13 and
    13 ≤ g(6) ≤ 18 [Ba21].
  * References/arXiv-2606-24878/erdos_lovasz.tex (fetched here), abstract and
    Theorem 1, read directly — see [Si26] below.

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
  [Tr14] A. Tripathi, "A result on intersecting families with maximum
    transversal size", arXiv:1409.4610 (2014): g(3) = 6, g(4) = 9.
  [Ba21] J. Barát, "Intersecting and 2-intersecting hypergraphs with
    maximal covering number: the Erdős–Lovász theme revisited",
    J. Combin. Des. 29 (2021), no. 3, 193–209: g(5) = 13,
    13 ≤ g(6) ≤ 18.  (Single-author; a prior draft of this file
    misattributed it to Barát–Wanless following erdosproblems.com —
    corrected per the vacuity audit against the paper's own tex.)
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
    tripathi_six_le_erdosLovaszNum_three [Tr14]     6 ≤ g(3)  (≤ is proved)
    tripathi_erdosLovaszNum_four        [Tr14]      g(4) = 9
    barat_erdosLovaszNum_five    [Ba21]    g(5) = 13
    barat_erdosLovaszNum_six_le  [Ba21]    g(6) ≤ 18

  TIER 3 — DERIVED FROM TIER 2 (each is a Tier 1 implication applied to a
  Tier 2 statement, so it reports `sorryAx` too — by design, not by
  oversight):
    tripathi_erdosLovaszNum_three       g(3) = 6      (= proved ≤ 6, archived ≥ 6)
    kahn_erdosLovaszNum_isBigO          [Ka94] in IsBigO form
    sivashankar_lower_bound_61_20       the 61/20 rounding

  Axiom audit (2026-07-30, `#print axioms` on every named declaration): all
  37 Tier 1 declarations report exactly {propext, Classical.choice,
  Quot.sound}; the 8 Tier 2 and 3 Tier 3 declarations report those plus
  `sorryAx`; nothing reports anything else. The build emits exactly 8
  `declaration uses sorry` warnings, one per Tier 2 statement. No
  `native_decide`, no custom axioms; all ground checks are kernel `decide`.
  Signatures of the §1–§3 theorems (stated inside `variable` sections) were
  confirmed with `#check @…` per STYLE.md.
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
-- §4 THE COVER NUMBER g(n) AND ITS PROVED VALUES
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
search (6 vertices is the least possible; there is no 6-edge witness on ≤ 5
vertices, and no 4- or 5-edge witness on ≤ 11 vertices, which is exhaustive
for ≤ 5 edges by the span bound `3 + 2·4`). It witnesses `g(3) ≤ 6`, the
upper half of [Tr14]'s `g(3) = 6`. -/
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

-- ════════════════════════════════════════════════════════════════════
-- §5 LITERATURE STATEMENTS (INTENDED SORRIES)
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

/-- **[Tr14]** (literature, INTENDED SORRY): `6 ≤ g(3)`. The matching upper
bound `g(3) ≤ 6` is PROVED above (`erdosLovaszNum_three_le`), so this
inequality is the entire sorried content of `g(3) = 6`. -/
theorem tripathi_six_le_erdosLovaszNum_three : 6 ≤ erdosLovaszNum 3 := by
  -- INTENDED SORRY: statement-archive lane. [Tr14]'s case analysis.
  sorry

/-- **[Tr14]**: `g(3) = 6` (OEIS A391599, a(3) = 6). -/
theorem tripathi_erdosLovaszNum_three : erdosLovaszNum 3 = 6 :=
  le_antisymm erdosLovaszNum_three_le tripathi_six_le_erdosLovaszNum_three

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
-- §6 CONSEQUENCES OF THE LITERATURE STATEMENTS (SORRY-FREE)
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
-- §7 GROUND CHECKS AND SATISFIABILITY
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

Every theorem of §1–§4 with hypotheses is instantiated jointly at a concrete
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

-- `erdosLovaszCards` is inhabited at n = 1, 2, 3 by the three witnesses, so
-- the `sInf` defining `erdosLovaszNum` is never taken over an empty set there.
example : (1 : ℕ) ∈ erdosLovaszCards 1 := ⟨1, {{0}}, by decide, by decide⟩
example : (3 : ℕ) ∈ erdosLovaszCards 2 :=
  ⟨3, {{0, 1}, {1, 2}, {0, 2}}, by decide, by decide⟩
example : (6 : ℕ) ∈ erdosLovaszCards 3 :=
  ⟨6, witnessThree, isErdosLovaszFamily_witnessThree, by decide⟩

-- The `∀ᶠ … in atTop` statements of §5–§6 quantify over a proper filter, so
-- they are not vacuously true.
example : (Filter.atTop : Filter ℕ).NeBot := inferInstance

/-! ### The archived literature statements, checked at the proved values

Each sorried bound of §5 is evaluated at every `n` whose value this file
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
-- a(2) = 3, a(3) ≤ 6 (with a(3) = 6 archived as [Tr14]).
example : erdosLovaszNum 1 = 1 ∧ erdosLovaszNum 2 = 3 ∧ erdosLovaszNum 3 ≤ 6 :=
  ⟨erdosLovaszNum_one, erdosLovaszNum_two, erdosLovaszNum_three_le⟩

end GroundChecks
