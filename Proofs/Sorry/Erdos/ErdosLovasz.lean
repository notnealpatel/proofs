import Erdos.ErdosLovasz

/-!
Quarantined admissions and their dependent consequences. Production supplies the
independent infrastructure; the declarations below retain their original statements
and proofs. The original source and disclosure documentation is retained below.
No mathematical proof closure is claimed.
-/

/-
  Erdős Problem #21 / OEIS A391599 — the Erdős–Lovász cover number g(r).

  STATUS: PROVED for n ≤ 4, including the exact equality g(4) = 9.
  The classical universal lower bound g(n) ≥ 8n/3 − 3 is also proved.
  The upper bound g(6) ≤ 18 is proved by an explicit 18-line witness.
  The remaining large-n and g(5) literature statements in §6 are a
  STATEMENT ARCHIVE (USER directive) with INTENDED, DISCLOSED sorries;
  everything else in this file is proved. See "SORRY LEDGER" below.

  The first four OEIS A391599 terms are sorry-free: g(1) = 1, g(2) = 3,
  g(3) = 6, and g(4) = 9. The lower half `6 ≤ g(3)` is the §4 counting
  argument; `9 ≤ g(4)` is the universal incidence argument in
  Erdos/ErdosLovaszFourLower.lean, bridged to the attained minimum in §5.

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
  * Tripathi's canonical source https://arxiv.org/abs/1409.4610, retrieved
    with `tool_arxiv` for the g(4) lower-bound proof and read directly.
    The historical References/Erdos/arXiv-1409-4610/paper.tex pointer is
    absent from this checkout; the new download is outside the repository.
    The quotations below were checked against its paper.tex.

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
    of g(3) = 6. Verbatim from the canonical paper.tex (see the source
    pointer above):
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
    the archived g(5) statement, which is sorried, and as the source of the
    g(6) ≤ 18 bound, which is proved here by an explicit witness.
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
    witnessFour_isTransversal          — explicit four-vertex cover
    witnessFour_no_small_transversal   — no cover of size < 4
    coveringNumber_witnessFour         — τ(witnessFour) = 4
    isErdosLovaszFamily_witnessFour     — Tripathi's nine-edge 4-uniform family
    erdosLovaszNum_four_le             — g(4) ≤ 9, independently of §6
    IsErdosLovaszFamily.nine_le_card    — 9 ≤ |F| for every EL family of
                                          four-sets, over every ground type
    tripathi_nine_le_erdosLovaszNum_four — 9 ≤ g(4)
    tripathi_erdosLovaszNum_four        — g(4) = 9   [Tr14], now proved
    erdos_lovasz_lower_bound            [EL75]      8n/3 − 3 ≤ g(n)
    sivashankarConst_bounds             — 61/20 < (41−√19)/12 < 3.054
    isBigO_of_forall_le_linear          — explicit constant → IsBigO
    lower_bound_61_20_of_asymptotic     — Thm 1(ii) → the 61/20 rounding
    one_le_of_forall_le_linear          — any Kahn constant satisfies 1 ≤ C
    thirteen_le_erdosLovaszNum_six_of_erdos_lovasz — [EL75] at n=6 gives 13
    not_threeMulAddBigO_of_asymptotic_lower_bound — Thm 1(ii) refutes 3r+O(1)
    noCoverSearch_sound                 — the branching no-cover search is sound
    barat_erdosLovaszNum_six_le  [Ba21] — g(6) ≤ 18 via the explicit 18-line
                                          `witnessSix` ⊆ PG(2,5) on Fin 31

  TIER 2 — ARCHIVED LITERATURE (intended, disclosed sorries; no Tier 1
  declaration uses any of them):
    kahn_erdosLovaszNum_le_linear       [Ka94]      ∃C, g(n) ≤ Cn
    sivashankar_three_mul_sub_four      [Si26](i)   3n − 4 ≤ g(n)
    sivashankar_asymptotic_lower_bound  [Si26](ii)  ((41−√19)/12 − ε)n ≤ g(n) ev.
    barat_erdosLovaszNum_five    [Ba21]    g(5) = 13

  TIER 3 — DERIVED FROM TIER 2 (each is a Tier 1 implication applied to a
  Tier 2 statement, so it reports `sorryAx` too — by design, not by
  oversight):
    kahn_erdosLovaszNum_isBigO          [Ka94] in IsBigO form
    sivashankar_lower_bound_61_20       the 61/20 rounding

  SORRY LEDGER: exactly the four Tier 2 statements, one
  `declaration uses sorry` warning each. `6 ≤ g(3)` left the ledger on
  2026-08-05; `tripathi_erdosLovaszNum_four : g(4) = 9` has now also left
  the ledger. The classical `erdos_lovasz_lower_bound` is now proved by
  finite incidence counting, pairing, and peeling in Erdos/ErdosLovaszLower.
  `barat_erdosLovaszNum_six_le : g(6) ≤ 18` has also left the ledger: it is
  proved by the explicit 18-line subfamily `witnessSix` of PG(2,5) on
  Fin 31, with uniformity and pairwise intersection checked by `decide` and
  the no-5-cover clause by the kernel `decide +kernel` branching
  certificate `noCoverSearch`, made sound by `noCoverSearch_sound`.
  The remaining sorries are exactly kahn_erdosLovaszNum_le_linear,
  sivashankar_three_mul_sub_four, sivashankar_asymptotic_lower_bound, and
  barat_erdosLovaszNum_five. These archived statements are unchanged.

  The exact g(4) proof combines Tripathi's explicit witness in
  Erdos/ErdosLovaszFourWitness.lean with the universal lower bound in
  Erdos/ErdosLovaszFourLower.lean. Its selected dependency closure, both
  bounds, and the family-level lower-bound bridge report exactly
  {propext, Classical.choice, Quot.sound}; no archived theorem is used.
  The build emits exactly 4 `declaration uses sorry` warnings, one per
  Tier 2 statement. The two Tier 3 consequences still inherit `sorryAx`.
  No `native_decide` or custom axioms are used; all finite ground checks are
  kernel `decide` (including the `decide +kernel` g(6) certificate).  The recorded signatures of the §1–§4 theorems (stated
  inside `variable` sections) and of the new g(4) bridges have the intended
  explicit parameters.
-/


set_option autoImplicit false

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

/-- **[Ba21]** (literature, INTENDED SORRY): `g(5) = 13` (OEIS A391599,
a(5) = 13), with exactly three non-isomorphic extremal examples
(erdosproblems.com/21, comment of 03 Dec 2025). -/
theorem barat_erdosLovaszNum_five : erdosLovaszNum 5 = 13 := by
  -- INTENDED SORRY: statement-archive lane; computer search in [Ba21].
  sorry

/-! ### A verified branching search for `g(6) ≤ 18`

The witness is an 18-line subfamily of the projective plane `PG(2,5)` on 31
points (labelled `0, …, 30`). Its no-small-cover clause is certified by a
branching search: any cover must contain a point of the first uncovered line,
so `noCoverSearch` branches over that line's six points, giving at most
`6 ^ 5` leaves. `noCoverSearch_sound` proves the search sound for every
finite candidate set, and the run itself is a kernel `decide +kernel` check. -/

/-- `noCoverSearch lines k S = true` certifies that no set `T` of at most `k`
points, added to the already chosen points `S`, meets every line of `lines`.
With no fuel left some line must avoid `S`; otherwise the search picks the
first line avoiding `S` and branches over its points. -/
private def noCoverSearch {α : Type} [DecidableEq α] (lines : List (List α)) :
    ℕ → List α → Bool
  | 0, S => lines.any (fun L => L.all (fun x => x ∉ S))
  | k + 1, S =>
    match lines.find? (fun L => L.all (fun x => x ∉ S)) with
    | none => false
    | some L => L.all (fun x => noCoverSearch lines k (x :: S))

example : noCoverSearch [[0, 1], [2, 3]] 1 [] = true := by decide
example : noCoverSearch [[0, 1], [1, 2]] 1 [] = false := by decide

/-- Soundness of the branching search: a successful run with fuel `k` from
chosen points `S` yields, for every finite set `T` of at most `k` points, a
line avoiding both `S` and `T`. -/
private theorem noCoverSearch_sound {α : Type} [DecidableEq α] (lines : List (List α)) :
    ∀ (k : ℕ) (S : List α), noCoverSearch lines k S = true →
      ∀ T : Finset α, T.card ≤ k → ∃ L ∈ lines, ∀ x ∈ L, x ∉ S ∧ x ∉ T := by
  intro k
  induction k with
  | zero =>
    intro S hS T hT
    have hT0 : T = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hT)
    subst hT0
    simp only [noCoverSearch, List.any_eq_true, List.all_eq_true, decide_eq_true_eq] at hS
    obtain ⟨L, hL, hLS⟩ := hS
    exact ⟨L, hL, fun x hx => ⟨hLS x hx, Finset.notMem_empty x⟩⟩
  | succ k ih =>
    intro S hS T hT
    simp only [noCoverSearch] at hS
    split at hS
    · exact absurd hS Bool.false_ne_true
    · rename_i L hfind
      have hL : L ∈ lines := List.mem_of_find?_eq_some hfind
      have hLS : ∀ x ∈ L, x ∉ S := by
        have hpred := List.find?_some hfind
        simpa only [List.all_eq_true, decide_eq_true_eq] using hpred
      rw [List.all_eq_true] at hS
      by_cases hmeet : ∃ x ∈ L, x ∈ T
      · obtain ⟨x, hxL, hxT⟩ := hmeet
        have hcard : (T.erase x).card ≤ k := by
          rw [Finset.card_erase_of_mem hxT]; omega
        obtain ⟨L', hL', hL'S⟩ := ih (x :: S) (hS x hxL) (T.erase x) hcard
        refine ⟨L', hL', fun y hy => ?_⟩
        obtain ⟨hyS, hyT⟩ := hL'S y hy
        have hyx : y ≠ x := fun h => hyS (h ▸ List.mem_cons_self)
        exact ⟨fun h => hyS (List.mem_cons_of_mem x h),
          fun h => hyT (Finset.mem_erase.mpr ⟨hyx, h⟩)⟩
      · simp only [not_exists, not_and] at hmeet
        exact ⟨L, hL, fun x hx => ⟨hLS x hx, hmeet x hx⟩⟩

/-- The eighteen lines of the `g(6)` witness, as lists of points of `PG(2,5)`
labelled `0, …, 30`, in the form consumed by `noCoverSearch`. -/
private def linesSix : List (List (Fin 31)) :=
  [[0, 6, 7, 8, 9, 10], [0, 21, 22, 23, 24, 25], [1, 6, 11, 16, 21, 26],
   [1, 7, 12, 17, 22, 27], [1, 8, 13, 18, 23, 28], [2, 6, 12, 18, 24, 30],
   [2, 7, 13, 19, 25, 26], [2, 9, 15, 16, 22, 28], [2, 10, 11, 17, 23, 29],
   [3, 7, 14, 16, 23, 30], [3, 8, 15, 17, 24, 26], [3, 10, 12, 19, 21, 28],
   [4, 8, 11, 19, 22, 30], [4, 9, 12, 20, 23, 26], [4, 10, 13, 16, 24, 27],
   [5, 7, 11, 20, 24, 28], [5, 8, 12, 16, 25, 29], [5, 10, 14, 18, 22, 26]]

/-- The `g(6)` witness: eighteen lines of `PG(2,5)`, a 6-uniform
intersecting family on 31 points with no cover of fewer than six points. -/
private def witnessSix : Finset (Finset (Fin 31)) :=
  (linesSix.map List.toFinset).toFinset

/-- The witness has exactly eighteen distinct edges. -/
private theorem witnessSix_card : witnessSix.card = 18 := by decide

/-- Each witness line lists six distinct points. -/
private theorem linesSix_nodup_length : ∀ L ∈ linesSix, L.Nodup ∧ L.length = 6 := by
  decide

/-- Any two witness lines share a point, including a line with itself. -/
private theorem linesSix_meet : ∀ L ∈ linesSix, ∀ M ∈ linesSix, ∃ x ∈ L, x ∈ M := by
  decide

/-- Every edge of the witness has exactly six points. -/
private theorem witnessSix_uniform : ∀ A ∈ witnessSix, A.card = 6 := by
  intro A hA
  obtain ⟨L, hL, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hA)
  obtain ⟨hnodup, hlen⟩ := linesSix_nodup_length L hL
  rw [List.toFinset_card_of_nodup hnodup, hlen]

/-- Every two edges of the witness meet, including an edge with itself. -/
private theorem witnessSix_intersecting :
    ∀ A ∈ witnessSix, ∀ B ∈ witnessSix, ¬ Disjoint A B := by
  intro A hA B hB
  obtain ⟨L, hL, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hA)
  obtain ⟨M, hM, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hB)
  obtain ⟨x, hxL, hxM⟩ := linesSix_meet L hL M hM
  exact Finset.not_disjoint_iff.mpr ⟨x, List.mem_toFinset.mpr hxL, List.mem_toFinset.mpr hxM⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel certificate: the branching search with fuel five succeeds on the
witness lines, i.e. no five points meet all eighteen lines. -/
private theorem linesSix_search : noCoverSearch linesSix 5 [] = true := by
  decide +kernel

/-- No set of fewer than six points meets every edge of the witness. -/
private theorem witnessSix_no_small_cover (S : Finset (Fin 31)) (hS : S.card < 6) :
    ∃ A ∈ witnessSix, Disjoint A S := by
  obtain ⟨L, hL, hLS⟩ :=
    noCoverSearch_sound linesSix 5 [] linesSix_search S (by omega)
  refine ⟨L.toFinset, ?_, ?_⟩
  · exact List.mem_toFinset.mpr (List.mem_map_of_mem hL)
  · rw [Finset.disjoint_left]
    intro x hx
    exact (hLS x (List.mem_toFinset.mp hx)).2

/-- The eighteen-line witness is an Erdős–Lovász family of 6-sets. -/
private theorem isErdosLovaszFamily_witnessSix : IsErdosLovaszFamily 6 witnessSix :=
  ⟨witnessSix_uniform, witnessSix_intersecting, witnessSix_no_small_cover⟩

/-- **[Ba21]** (PROVED here): `g(6) ≤ 18`. [Ba21] determine
`m(6) = 18`, where `m(r)` is the minimum number of lines of a projective plane
with covering number `r`; such a configuration is a 6-uniform intersecting
family with τ = 6, whence `g(6) ≤ 18`. The proof exhibits such a
configuration: the explicit 18-line subfamily `witnessSix` of `PG(2,5)` on
`Fin 31`, whose uniformity and pairwise intersection are checked by `decide`
and whose no-5-cover clause is the kernel `decide +kernel` branching
certificate `noCoverSearch`, made sound by `noCoverSearch_sound`. The exact
value of g(6) is unknown, which is why OEIS A391599 stops at a(5) and carries
the `more` keyword.

The companion `13 ≤ g(6)` quoted on erdosproblems.com/21 is NOT independent
literature — it is [EL75] evaluated at n = 6, where `8·6/3 − 3 = 13` exactly;
see `thirteen_le_erdosLovaszNum_six_of_erdos_lovasz`, which is sorry-free. -/
theorem barat_erdosLovaszNum_six_le : erdosLovaszNum 6 ≤ 18 :=
  Nat.sInf_le ⟨31, witnessSix, isErdosLovaszFamily_witnessSix, witnessSix_card⟩

/-- The `61/20` form of [Si26]'s bound. DERIVED from the archived
`sivashankar_asymptotic_lower_bound`, hence inheriting its `sorryAx`; the
derivation itself is the sorry-free `lower_bound_61_20_of_asymptotic`. -/
theorem sivashankar_lower_bound_61_20 (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ((61 : ℝ) / 20 - ε) * n ≤ erdosLovaszNum n :=
  lower_bound_61_20_of_asymptotic sivashankar_asymptotic_lower_bound ε hε

/-- [Ka94]'s bound in Mathlib's asymptotic normal form. DERIVED from the
archived `kahn_erdosLovaszNum_le_linear`, hence inheriting its `sorryAx`; the
derivation itself is the sorry-free `isBigO_of_forall_le_linear`. -/
theorem kahn_erdosLovaszNum_isBigO :
    (fun n : ℕ => (erdosLovaszNum n : ℝ)) =O[Filter.atTop] (fun n : ℕ => (n : ℝ)) := by
  obtain ⟨C, hC⟩ := kahn_erdosLovaszNum_le_linear
  exact isBigO_of_forall_le_linear hC

