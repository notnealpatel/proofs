/-
  BilinearComplexity/BooleanRankGeneric — almost every square Boolean
  matrix has full Boolean row rank: the fraction of n × n matrices over
  the Boolean semiring ({0,1}, ∨, ∧) whose row rank is n tends to 1 as
  n → ∞. This proves the conjectured limit stated (unattributed, "it
  appears from some empirical computations") in OEIS A354741.

    · `RowLE u v`          — row domination: wherever `u` has a 1 so
                             does `v`.
    · `rowsSum A T`        — the Boolean sum (entrywise or) of the rows
                             of `A` indexed by `T`.
    · `rowSpan A S`        — the Boolean row span of the rows indexed by
                             `S`, as a `Finset` of vectors: all sums of
                             subsets of those rows (empty sum `0`
                             included).
    · `boolRowRank A`      — the least cardinality of a set of rows of
                             `A` whose span is the span of all rows
                             (`Nat.find` over the decidable predicate
                             `BoolRowRankLE A ·`, witnessed at `r = m`).
    · `boolRank_le_boolRowRank`
                           — bridge to the committed rectangle-cover
                             rank of `BooleanRank.lean`: a spanning row
                             basis of size `r` yields a factorization
                             through `r`.
    · `boolRowRank_eq_of_antichain`
                           — matrices whose rows are nonzero and
                             pairwise incomparable under `RowLE` have
                             full row rank; hence a dominated-pair
                             union bound (`card_dominatedRowLE_le`,
                             at most `n·n·3ⁿ·2^(n(n−2))` bad matrices)
                             forces almost all matrices to full rank.
    · `fullRowRankFraction_tendsto_one`
                           — the A354741 limit: the fraction of n × n
                             Boolean matrices of full row rank tends
                             to 1 (squeeze between `1 − n²(3/4)ⁿ`
                             and `1`).

  Novelty status (literature sweep 2026-07-30,
  `.tasks/main/docs/novelty-BooleanRankGeneric.md`): NO-REFERENCE-FOUND —
  first recorded proof of the A354741 comment (unattributed, "it appears
  from some empirical computations"). The ingredients (union bound, the
  `(3/4)ⁿ` dominated-pair probability, antichain ⟹ full row rank) are
  individually standard; the contribution is the combination and the
  machine-checked proof. Related but DISTINCT results: Komlós 1967 /
  Kahn–Komlós–Szemerédi 1995 (real rank → 1); Pourmoradnasseri–Theis 2017
  (Schein rank, `(1−o(1))n` a.a.s.); Izhakian–Janson–Rhodes 2015
  (triangular rank `O(log n)`); over `GF(2)` the full-rank fraction tends
  to `∏(1 − 2⁻ⁱ) ≈ 0.2888` (A048651), not 1. Not a novel discovery.

  Semantics guardrails. A354741 counts matrices by Boolean ROW rank
  (minimal spanning subset of the rows), which is NOT the rectangle-
  cover (Schein) rank `boolRank` of `BooleanRank.lean`: the two
  triangles agree for n ≤ 3 and split at n = 4 (A354741 row 4 ends
  37488, 19272; the Schein triangle A355333 ends 40656, 16104), where
  `boolRank A ≤ boolRowRank A` always (`boolRank_le_boolRowRank`).
  The limit proved here is the row-rank statement of the A354741
  comment; empirically (A355333) the full-Schein-rank fraction is
  decreasing in n, so the two statistics genuinely diverge. Likewise
  Boolean arithmetic here is (∨, ∧) on `BoolSemiring`, not Mathlib's
  xor-based 𝔽₂ structure on `Bool`: over 𝔽₂ the full-rank fraction
  tends to ∏ (1 − 2⁻ⁱ) ≈ 0.2888 (A048651, A286331), not 1, and the
  in-file 𝔽₂ contrast block exhibits the divergence at n = 3.

  Empirical ground (2026-07-30, exhaustive n ≤ 4 + Monte Carlo):
  row-rank triangle rows 0–4 reproduce A354741 exactly; full-rank
  fraction 0.5, 0.375, 0.3047, 0.2941, 0.3277 for n = 1..5, then
  ≈ 0.99 at n = 20 and → 1.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.ZMod.Basic
import BilinearComplexity.BooleanRank

set_option autoImplicit false

namespace BilinearComplexity

open Finset Filter

/-! ## 1. Row domination -/

/-- `RowLE u v` : the Boolean vector `u` is dominated by `v` — wherever
`u` has a `1`, so does `v`. This is the pointwise order of the Boolean
semiring on rows, kept as a bespoke decidable predicate (no order
instances on the `BoolSemiring` synonym are introduced). -/
def RowLE {n : ℕ} (u v : Fin n → BoolSemiring) : Prop :=
  ∀ c, u c = 1 → v c = 1

/-- Row domination is decidable (a finite check over columns). -/
instance {n : ℕ} (u v : Fin n → BoolSemiring) : Decidable (RowLE u v) :=
  inferInstanceAs (Decidable (∀ c, u c = 1 → v c = 1))

-- Ground checks: domination is the pointwise (∨, ∧)-order, not equality.
example : RowLE (fun _ => 0 : Fin 2 → BoolSemiring) (fun _ => 1) := by decide
example : ¬ RowLE (fun _ => 1 : Fin 2 → BoolSemiring) (fun _ => 0) := by decide
example : RowLE (boolId 2 0) (fun _ => 1) := by decide
example : ¬ RowLE (boolId 2 0) (boolId 2 1) := by decide

/-! ## 2. Boolean row spans -/

/-- The Boolean sum (entrywise or) of the rows of `A` indexed by `T`. -/
def rowsSum {m n : ℕ} (A : BoolMatrix m n) (T : Finset (Fin m)) :
    Fin n → BoolSemiring :=
  fun j => ∑ i ∈ T, A i j

/-- The sum of a single row is that row. -/
theorem rowsSum_singleton {m n : ℕ} (A : BoolMatrix m n) (i : Fin m) :
    rowsSum A {i} = A i := by
  funext j
  exact Finset.sum_singleton _ _

/-- Every row indexed by `T` is dominated by the Boolean sum of the
rows indexed by `T` (`+` is or). -/
theorem rowLE_rowsSum {m n : ℕ} {A : BoolMatrix m n} {T : Finset (Fin m)}
    {i : Fin m} (hi : i ∈ T) : RowLE (A i) (rowsSum A T) := by
  intro c hc
  exact (BoolSemiring.sum_eq_one_iff T fun i' => A i' c).mpr ⟨i, hi, hc⟩

/-- The Boolean row span of the rows of `A` indexed by `S`: the
`Finset` of all Boolean sums of subsets of those rows. The empty sum
`0` is a member, so spans of different index sets are compared on
equal footing. -/
def rowSpan {m n : ℕ} (A : BoolMatrix m n) (S : Finset (Fin m)) :
    Finset (Fin n → BoolSemiring) :=
  S.powerset.image (rowsSum A)

/-- Each spanned row is in the span. -/
theorem mem_rowSpan_self {m n : ℕ} (A : BoolMatrix m n) {S : Finset (Fin m)}
    {i : Fin m} (hi : i ∈ S) : A i ∈ rowSpan A S :=
  Finset.mem_image.mpr
    ⟨{i}, Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hi),
      rowsSum_singleton A i⟩

-- Ground checks: the span of both identity rows contains all four
-- Boolean vectors of length 2; the or of the two identity rows is the
-- all-ones vector.
example : rowsSum (boolId 2) {0, 1} = fun _ => 1 := by decide
example : rowSpan (boolId 2) Finset.univ = Finset.univ := by decide
example : rowSpan (boolId 2) {0} = {0, boolId 2 0} := by decide

/-! ## 3. Boolean row rank -/

/-- `BoolRowRankLE A r` : some set of at most `r` rows of `A` spans the
Boolean row space of `A`. This is the "row rank ≤ r" predicate of
A354741 (minimal spanning subset of the rows, or-combinations only). -/
def BoolRowRankLE {m n : ℕ} (A : BoolMatrix m n) (r : ℕ) : Prop :=
  ∃ S : Finset (Fin m), S.card ≤ r ∧ rowSpan A S = rowSpan A Finset.univ

/-- Boolean row rank-≤ is decidable: a finite search over row subsets. -/
instance {m n : ℕ} (A : BoolMatrix m n) (r : ℕ) : Decidable (BoolRowRankLE A r) :=
  inferInstanceAs (Decidable
    (∃ S : Finset (Fin m), S.card ≤ r ∧ rowSpan A S = rowSpan A Finset.univ))

/-- Row rank-≤ is monotone in `r` (the same spanning set witnesses). -/
theorem BoolRowRankLE.mono {m n : ℕ} {A : BoolMatrix m n} {r r' : ℕ}
    (h : BoolRowRankLE A r) (hrr' : r ≤ r') : BoolRowRankLE A r' := by
  obtain ⟨S, hcard, hspan⟩ := h
  exact ⟨S, hcard.trans hrr', hspan⟩

/-- All `m` rows span, so the row rank search is witnessed at `r = m`. -/
theorem boolRowRankLE_rows {m n : ℕ} (A : BoolMatrix m n) : BoolRowRankLE A m :=
  ⟨Finset.univ, by simp, rfl⟩

/-- Spanning witnesses exist, so `Nat.find` below is never vacuous. -/
theorem exists_boolRowRankLE {m n : ℕ} (A : BoolMatrix m n) :
    ∃ r, BoolRowRankLE A r :=
  ⟨m, boolRowRankLE_rows A⟩

/-- The Boolean row rank of `A`: the least cardinality of a set of rows
whose Boolean span is the span of all rows — the row-rank statistic of
A354741. (Unlike field rank there is no column-count bound: an m × n
matrix whose rows form a Sperner antichain has row rank `m`, which can
exceed `n`.) -/
def boolRowRank {m n : ℕ} (A : BoolMatrix m n) : ℕ :=
  Nat.find (exists_boolRowRankLE A)

/-- The Boolean row rank is attained. -/
theorem boolRowRankLE_boolRowRank {m n : ℕ} (A : BoolMatrix m n) :
    BoolRowRankLE A (boolRowRank A) :=
  Nat.find_spec (exists_boolRowRankLE A)

/-- Minimality: any spanning bound dominates the Boolean row rank. -/
theorem boolRowRank_le_of_boolRowRankLE {m n : ℕ} {A : BoolMatrix m n} {r : ℕ}
    (h : BoolRowRankLE A r) : boolRowRank A ≤ r :=
  Nat.find_min' (exists_boolRowRankLE A) h

/-- Order interface: `boolRowRank A ≤ r` iff `r` rows suffice to span. -/
theorem boolRowRank_le_iff {m n : ℕ} {A : BoolMatrix m n} {r : ℕ} :
    boolRowRank A ≤ r ↔ BoolRowRankLE A r :=
  ⟨fun h => (boolRowRankLE_boolRowRank A).mono h, boolRowRank_le_of_boolRowRankLE⟩

/-- Ground-check driver: `boolRowRank A = r` iff `r` rows span but no
`s < r` rows do. Both sides are decidable, so small concrete instances
close by `decide`. -/
theorem boolRowRank_eq_iff {m n : ℕ} {A : BoolMatrix m n} {r : ℕ} :
    boolRowRank A = r ↔ BoolRowRankLE A r ∧ ∀ s < r, ¬BoolRowRankLE A s :=
  Nat.find_eq_iff (exists_boolRowRankLE A)

/-- The trivial row-count bound: `boolRowRank A ≤ m`. -/
theorem boolRowRank_le_rows {m n : ℕ} (A : BoolMatrix m n) : boolRowRank A ≤ m :=
  boolRowRank_le_of_boolRowRankLE (boolRowRankLE_rows A)

-- Ground checks at 2 × 2: rank 0 (zero matrix), 1 (all ones), 2 (identity).
example : boolRowRank (0 : BoolMatrix 2 2) = 0 := by
  rw [boolRowRank_eq_iff]; decide
example : boolRowRank (fun _ _ => 1 : BoolMatrix 2 2) = 1 := by
  rw [boolRowRank_eq_iff]; decide
example : boolRowRank (boolId 2) = 2 := by
  rw [boolRowRank_eq_iff]; decide
-- A dominated pair need not kill full rank: rows (1,0), (1,1).
example : boolRowRank (fun i j => if i = 0 ∨ j = 1 then 1 else 0 : BoolMatrix 2 2) = 2 := by
  rw [boolRowRank_eq_iff]; decide

/-! ## 4. Bridge: rectangle-cover rank ≤ row rank -/

/-- A spanning row set `S` yields a Boolean factorization of `A` through
`S.card`: writing each row `A i` as the Boolean sum of a subset `T i ⊆ S`,
take `B i s = [sᵗʰ row of S ∈ T i]` and let `C` list the rows of `S`.
Verified pointwise via the rectangle-cover characterization
`boolRankLE_iff_pointwise`: `A i j = 1` iff some row of `T i` has a `1`
in column `j`. -/
theorem boolRankLE_card_of_rowSpan_eq {m n : ℕ} {A : BoolMatrix m n}
    {S : Finset (Fin m)} (hspan : rowSpan A S = rowSpan A Finset.univ) :
    BoolRankLE A S.card := by
  classical
  have hrow : ∀ i : Fin m, ∃ T ∈ S.powerset, rowsSum A T = A i := by
    intro i
    have hmem : A i ∈ rowSpan A S := by
      rw [hspan]
      exact mem_rowSpan_self A (Finset.mem_univ i)
    exact Finset.mem_image.mp hmem
  choose T hTsub hTsum using hrow
  set e := S.equivFin with he
  rw [boolRankLE_iff_pointwise]
  refine ⟨fun i s => if (↑(e.symm s) : Fin m) ∈ T i then 1 else 0,
          fun s j => A (↑(e.symm s)) j, fun i j => ?_⟩
  simp only
  constructor
  · intro hA1
    have hsum : (∑ x ∈ T i, A x j) = 1 := by
      calc (∑ x ∈ T i, A x j) = rowsSum A (T i) j := rfl
        _ = A i j := by rw [hTsum i]
        _ = 1 := hA1
    obtain ⟨x, hxT, hx1⟩ :=
      (BoolSemiring.sum_eq_one_iff (T i) fun x => A x j).mp hsum
    have hxS : x ∈ S := Finset.mem_powerset.mp (hTsub i) hxT
    refine ⟨e ⟨x, hxS⟩, ?_, ?_⟩
    · rw [Equiv.symm_apply_apply]
      exact if_pos hxT
    · rw [Equiv.symm_apply_apply]
      exact hx1
  · rintro ⟨s, hBs, hCs⟩
    by_cases hmem : (↑(e.symm s) : Fin m) ∈ T i
    · have hsum : (∑ x ∈ T i, A x j) = 1 :=
        (BoolSemiring.sum_eq_one_iff (T i) fun x => A x j).mpr ⟨_, hmem, hCs⟩
      calc A i j = rowsSum A (T i) j := by rw [hTsum i]
        _ = 1 := hsum
    · rw [if_neg hmem] at hBs
      exact absurd hBs (by decide)

/-- The committed rectangle-cover (Schein) rank `boolRank` of
`BooleanRank.lean` is bounded by the row rank: expressing every row as
the Boolean sum of a subset of a spanning row set `S` yields a
factorization `A = B · C` through `S.card`. The inequality is strict in
general (A355333 vs A354741 diverge at n = 4). -/
theorem boolRank_le_boolRowRank {m n : ℕ} (A : BoolMatrix m n) :
    boolRank A ≤ boolRowRank A := by
  obtain ⟨S, hcard, hspan⟩ := boolRowRankLE_boolRowRank A
  exact boolRank_le_of_boolRankLE
    ((boolRankLE_card_of_rowSpan_eq hspan).mono hcard)

/-! ## 5. Antichains of rows have full row rank -/

/-- If the rows of `A` are nonzero and pairwise incomparable under
`RowLE`, no proper subset of the rows spans: a missing row `A i` would
be a Boolean sum of rows `A j` with `j ≠ i`, each dominated by `A i` —
impossible for a nonempty sum by incomparability and for the empty sum
by nonzeroness. Hence the row rank is the full row count `m`. -/
theorem boolRowRank_eq_of_antichain {m n : ℕ} {A : BoolMatrix m n}
    (hdom : ∀ i j : Fin m, i ≠ j → ¬ RowLE (A i) (A j))
    (hone : ∀ i : Fin m, ∃ c, A i c = 1) :
    boolRowRank A = m := by
  rw [boolRowRank_eq_iff]
  refine ⟨boolRowRankLE_rows A, fun s hs hLE => ?_⟩
  obtain ⟨S, hcard, hspan⟩ := hLE
  have hmiss : ∃ i, i ∉ S := by
    by_contra hall
    push Not at hall
    have huniv : S = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    rw [huniv, Finset.card_univ, Fintype.card_fin] at hcard
    omega
  obtain ⟨i, hiS⟩ := hmiss
  have hmem : A i ∈ rowSpan A S := by
    rw [hspan]
    exact mem_rowSpan_self A (Finset.mem_univ i)
  obtain ⟨T, hTmem, hTsum⟩ := Finset.mem_image.mp hmem
  have hTS : T ⊆ S := Finset.mem_powerset.mp hTmem
  rcases Finset.eq_empty_or_nonempty T with rfl | ⟨j, hjT⟩
  · obtain ⟨c, hc⟩ := hone i
    have h0 : rowsSum A (∅ : Finset (Fin m)) c = 1 := by rw [hTsum]; exact hc
    rw [rowsSum, Finset.sum_empty] at h0
    exact (by decide : (0 : BoolSemiring) ≠ 1) h0
  · have hji : j ≠ i := fun hji => hiS (hji ▸ hTS hjT)
    exact hdom j i hji (hTsum ▸ rowLE_rowsSum hjT)

/-- The `n × n` identity has full Boolean row rank: its rows are
nonzero and pairwise incomparable. -/
theorem boolRowRank_boolId (n : ℕ) : boolRowRank (boolId n) = n := by
  refine boolRowRank_eq_of_antichain (fun i j hij hle => ?_) (fun i => ?_)
  · have h1 : boolId n i i = 1 := by rw [boolId, if_pos rfl]
    have h2 := hle i h1
    rw [boolId, if_neg (Ne.symm hij)] at h2
    exact (by decide : (0 : BoolSemiring) ≠ 1) h2
  · exact ⟨i, by rw [boolId, if_pos rfl]⟩

-- Cross-check: the generic antichain theorem agrees with kernel `decide`.
example : boolRowRank (boolId 2) = 2 := boolRowRank_boolId 2

/-! ## 6. The dominated-pair union bound -/

/-- Counting matrices with a fixed dominated row pair: for `i ≠ j`, at
most `3ⁿ · 2^(n(n−2))` of the `2^(n²)` matrices satisfy
`RowLE (A i) (A j)` — the pair `(A i c, A j c)` avoids `(1, 0)` in each
of `n` columns (3 choices), the remaining `n − 2` rows are free. -/
theorem card_filter_rowLE_le {n : ℕ} {i j : Fin n} (hij : i ≠ j) (_hn : 2 ≤ n) :
    (Finset.univ.filter fun A : BoolMatrix n n => RowLE (A i) (A j)).card
      ≤ 3 ^ n * 2 ^ (n * (n - 2)) := by
  classical
  -- Inject a matrix into (its (i, j)-row pair, its remaining rows): the
  -- pair function lands in the 3-choices-per-column set, the rest is free.
  have key : (Finset.univ.filter fun A : BoolMatrix n n => RowLE (A i) (A j)).card
      ≤ ((Finset.univ.filter fun p : Fin n → BoolSemiring × BoolSemiring =>
            ∀ c, ¬((p c).1 = 1 ∧ (p c).2 = 0)) ×ˢ
          (Finset.univ :
            Finset ({k : Fin n // k ≠ i ∧ k ≠ j} → Fin n → BoolSemiring))).card := by
    refine Finset.card_le_card_of_injOn
      (fun A => (fun c => (A i c, A j c), fun k c => A k.1 c)) ?_ ?_
    · intro A hA
      obtain ⟨-, hle⟩ := Finset.mem_filter.mp hA
      refine Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Finset.mem_univ _⟩
      rintro c ⟨h1, h0⟩
      simp only at h1 h0
      have h1' : A j c = 1 := hle c h1
      rw [h0] at h1'
      exact (by decide : (0 : BoolSemiring) ≠ 1) h1'
    · intro A _ B _ hAB
      have hfst : (fun c => (A i c, A j c)) = fun c => (B i c, B j c) :=
        congrArg Prod.fst hAB
      have hsnd : (fun (k : {k : Fin n // k ≠ i ∧ k ≠ j}) (c : Fin n) => A k.1 c) =
          fun k c => B k.1 c := congrArg Prod.snd hAB
      funext k c
      by_cases hki : k = i
      · subst hki
        exact congrArg Prod.fst (congrFun hfst c)
      · by_cases hkj : k = j
        · subst hkj
          exact congrArg Prod.snd (congrFun hfst c)
        · exact congrFun (congrFun hsnd ⟨k, hki, hkj⟩) c
  refine key.trans (le_of_eq ?_)
  rw [Finset.card_product]
  -- The pair-function count: 3 admissible values per column.
  have hpair : (Finset.univ.filter fun p : Fin n → BoolSemiring × BoolSemiring =>
      ∀ c, ¬((p c).1 = 1 ∧ (p c).2 = 0)).card = 3 ^ n := by
    have hpi : (Finset.univ.filter fun p : Fin n → BoolSemiring × BoolSemiring =>
        ∀ c, ¬((p c).1 = 1 ∧ (p c).2 = 0)) =
        Fintype.piFinset fun _ : Fin n =>
          Finset.univ.filter fun q : BoolSemiring × BoolSemiring =>
            ¬(q.1 = 1 ∧ q.2 = 0) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Fintype.mem_piFinset]
    have h3 : (Finset.univ.filter fun q : BoolSemiring × BoolSemiring =>
        ¬(q.1 = 1 ∧ q.2 = 0)).card = 3 := by decide
    rw [hpi, Fintype.card_piFinset_const, h3]
  -- The remaining-rows count: `n − 2` free rows of `n` free entries.
  have hsub : Fintype.card {k : Fin n // k ≠ i ∧ k ≠ j} = n - 2 := by
    rw [Fintype.card_subtype]
    have hcompl : (Finset.univ.filter fun k : Fin n => k ≠ i ∧ k ≠ j) =
        ({i, j} : Finset (Fin n))ᶜ := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
        Finset.mem_insert, Finset.mem_singleton, not_or]
    rw [hcompl, Finset.card_compl, Finset.card_pair_eq_two_iff.mpr hij,
      Fintype.card_fin]
  have hBS : Fintype.card BoolSemiring = 2 := rfl
  rw [hpair, Finset.card_univ, Fintype.card_fun, Fintype.card_fun, hBS,
    Fintype.card_fin, hsub, ← pow_mul]

/-- Union bound over the at most `n·n` ordered row pairs (`n(n−1) ≤ n·n`): at most
`n·n·3ⁿ·2^(n(n−2))` matrices contain a dominated row pair. -/
theorem card_dominatedRowLE_le (n : ℕ) (hn : 2 ≤ n) :
    (Finset.univ.filter fun A : BoolMatrix n n =>
        ∃ i j : Fin n, i ≠ j ∧ RowLE (A i) (A j)).card
      ≤ n * n * (3 ^ n * 2 ^ (n * (n - 2))) := by
  have hsub : (Finset.univ.filter fun A : BoolMatrix n n =>
      ∃ i j : Fin n, i ≠ j ∧ RowLE (A i) (A j))
      ⊆ (Finset.univ.offDiag).biUnion
          (fun p => Finset.univ.filter fun A : BoolMatrix n n =>
            RowLE (A p.1) (A p.2)) := by
    intro A hA
    obtain ⟨-, i, j, hij, hle⟩ := Finset.mem_filter.mp hA
    exact Finset.mem_biUnion.mpr
      ⟨(i, j),
        Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hij⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_biUnion_le_card_mul _ _ (3 ^ n * 2 ^ (n * (n - 2))) ?_).trans ?_
  · rintro ⟨i, j⟩ hp
    exact card_filter_rowLE_le (Finset.mem_offDiag.mp hp).2.2 hn
  · refine Nat.mul_le_mul_right _ ?_
    rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
    exact Nat.sub_le _ _

/-- A matrix with no dominated row pair has full row rank (for
`2 ≤ n`): incomparability is the antichain hypothesis, and an all-zero
row would be dominated by any other row. -/
theorem boolRowRank_eq_of_not_exists_rowLE {n : ℕ} (h2 : 2 ≤ n)
    {A : BoolMatrix n n}
    (h : ¬ ∃ i j : Fin n, i ≠ j ∧ RowLE (A i) (A j)) : boolRowRank A = n := by
  push Not at h
  refine boolRowRank_eq_of_antichain h (fun i => ?_)
  by_contra hc
  push Not at hc
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [Fintype.card_fin]; omega) i
  exact h i j (Ne.symm hj) (fun c hcone => absurd hcone (hc c))

/-- There are `2^(m·n)` Boolean matrices of shape `m × n`. -/
theorem card_boolMatrix (m n : ℕ) :
    Fintype.card (BoolMatrix m n) = 2 ^ (m * n) := by
  have hcard : Fintype.card BoolSemiring = 2 := rfl
  rw [Fintype.card_fun, Fintype.card_fun, hcard, Fintype.card_fin,
    Fintype.card_fin, ← pow_mul, mul_comm]

/-- The number of `n × n` Boolean matrices of full Boolean row rank —
the diagonal entry `T(n, n)` of A354741. -/
def fullRowRankCount (n : ℕ) : ℕ :=
  (Finset.univ.filter fun A : BoolMatrix n n => boolRowRank A = n).card

/-- Full row rank as a directly decidable filter: for `1 ≤ n`, a square
matrix has row rank `n` iff no `n − 1` rows span. Ground-check driver —
the `Nat.find` inside `boolRowRank` does not kernel-reduce, while the
right-hand filter closes by `decide` at small `n`. -/
theorem fullRowRankCount_eq_card_filter_not {n : ℕ} (hn : 1 ≤ n) :
    fullRowRankCount n =
      (Finset.univ.filter fun A : BoolMatrix n n =>
        ¬ BoolRowRankLE A (n - 1)).card := by
  unfold fullRowRankCount
  refine congrArg Finset.card (Finset.filter_congr fun A _ => ?_)
  constructor
  · intro hrk hLE
    have hle := boolRowRank_le_of_boolRowRankLE hLE
    omega
  · intro hnot
    have hub : boolRowRank A ≤ n := boolRowRank_le_rows A
    have hlb : ¬ boolRowRank A ≤ n - 1 :=
      fun hle => hnot (boolRowRank_le_iff.mp hle)
    omega

-- A354741 diagonal ground checks: T(1,1) = 1 and T(2,2) = 6 (of the
-- 2 and 16 matrices respectively) have full Boolean row rank.
example : fullRowRankCount 1 = 1 := by
  rw [fullRowRankCount_eq_card_filter_not le_rfl]
  decide
example : fullRowRankCount 2 = 6 := by
  rw [fullRowRankCount_eq_card_filter_not (by omega)]
  decide

-- Tightness of the per-pair count at n = 2: exactly 3² · 2⁰ = 9 of the
-- 16 matrices have row 0 dominated by row 1, meeting the bound of
-- `card_filter_rowLE_le`.
example : (Finset.univ.filter
    fun A : BoolMatrix 2 2 => RowLE (A 0) (A 1)).card = 9 := by decide
example : (Finset.univ.filter
      fun A : BoolMatrix 2 2 => RowLE (A 0) (A 1)).card
    ≤ 3 ^ 2 * 2 ^ (2 * (2 - 2)) :=
  card_filter_rowLE_le (by decide) (by norm_num)

/-- Every matrix either has a dominated row pair or has full row rank,
so the two counts cover `2^(n·n)` (for `2 ≤ n`). -/
theorem two_pow_le_fullRowRankCount_add {n : ℕ} (h2 : 2 ≤ n) :
    2 ^ (n * n) ≤ fullRowRankCount n + n * n * (3 ^ n * 2 ^ (n * (n - 2))) := by
  have hcover : (Finset.univ : Finset (BoolMatrix n n)) ⊆
      (Finset.univ.filter fun A : BoolMatrix n n => boolRowRank A = n) ∪
        (Finset.univ.filter fun A : BoolMatrix n n =>
          ∃ i j : Fin n, i ≠ j ∧ RowLE (A i) (A j)) := by
    rintro A -
    by_cases hbad : ∃ i j : Fin n, i ≠ j ∧ RowLE (A i) (A j)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩)
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, boolRowRank_eq_of_not_exists_rowLE h2 hbad⟩)
  calc 2 ^ (n * n) = (Finset.univ : Finset (BoolMatrix n n)).card := by
        rw [Finset.card_univ, card_boolMatrix]
    _ ≤ _ := Finset.card_le_card hcover
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ fullRowRankCount n + n * n * (3 ^ n * 2 ^ (n * (n - 2))) :=
        Nat.add_le_add_left (card_dominatedRowLE_le n h2) _

/-! ## 7. The limit theorem (A354741 comment) -/

/-- The fraction of `n × n` Boolean matrices of full Boolean row rank,
among all `2^(n·n)` matrices. The denominator is positive for every
`n`, so the division never takes its junk value. -/
noncomputable def fullRowRankFraction (n : ℕ) : ℝ :=
  (fullRowRankCount n : ℝ) / 2 ^ (n * n)

/-- The full-row-rank fraction is at most `1`. -/
theorem fullRowRankFraction_le_one (n : ℕ) : fullRowRankFraction n ≤ 1 := by
  refine div_le_one_of_le₀ ?_ (by positivity)
  have hle : fullRowRankCount n ≤ 2 ^ (n * n) := by
    calc fullRowRankCount n
        ≤ (Finset.univ : Finset (BoolMatrix n n)).card :=
          Finset.card_filter_le _ _
      _ = 2 ^ (n * n) := by rw [Finset.card_univ, card_boolMatrix]
  exact_mod_cast hle

/-- The union-bound lower envelope: for `2 ≤ n` the full-row-rank
fraction is at least `1 − n²(3/4)ⁿ`. -/
theorem one_sub_le_fullRowRankFraction {n : ℕ} (h2 : 2 ≤ n) :
    1 - (n : ℝ) ^ 2 * (3 / 4) ^ n ≤ fullRowRankFraction n := by
  have hR : (2 : ℝ) ^ (n * n) ≤ (fullRowRankCount n : ℝ) +
      (n : ℝ) * n * (3 ^ n * 2 ^ (n * (n - 2))) := by
    exact_mod_cast two_pow_le_fullRowRankCount_add h2
  have hpow : (0 : ℝ) < 2 ^ (n * n) := by positivity
  -- exponent bookkeeping: n·(n−2) + 2·n = n·n for 2 ≤ n
  have hnn : n * (n - 2) + 2 * n = n * n := by
    have hsub2 : n - 2 + 2 = n := Nat.sub_add_cancel h2
    calc n * (n - 2) + 2 * n = n * ((n - 2) + 2) := by ring
      _ = n * n := by rw [hsub2]
  have hsplit : (2 : ℝ) ^ (n * n) = 2 ^ (n * (n - 2)) * 2 ^ (2 * n) := by
    rw [← pow_add, hnn]
  have h42 : ((4 : ℝ)) ^ n = 2 ^ (2 * n) := by
    rw [pow_mul]
    norm_num
  -- the bad-event mass is exactly n²(3/4)ⁿ
  have hfrac : ((n : ℝ) * n * (3 ^ n * 2 ^ (n * (n - 2)))) / 2 ^ (n * n)
      = (n : ℝ) ^ 2 * (3 / 4) ^ n := by
    rw [hsplit, div_pow, h42]
    have hne : (2 : ℝ) ^ (n * (n - 2)) ≠ 0 := by positivity
    have hne' : (2 : ℝ) ^ (2 * n) ≠ 0 := by positivity
    field_simp
  have hgoal : fullRowRankFraction n = (fullRowRankCount n : ℝ) / 2 ^ (n * n) := rfl
  rw [hgoal, sub_le_iff_le_add]
  calc (1 : ℝ) = 2 ^ (n * n) / 2 ^ (n * n) := (div_self (ne_of_gt hpow)).symm
    _ ≤ ((fullRowRankCount n : ℝ) + (n : ℝ) * n * (3 ^ n * 2 ^ (n * (n - 2)))) /
          2 ^ (n * n) :=
        div_le_div_of_nonneg_right hR (le_of_lt hpow)
    _ = (fullRowRankCount n : ℝ) / 2 ^ (n * n) +
          ((n : ℝ) * n * (3 ^ n * 2 ^ (n * (n - 2)))) / 2 ^ (n * n) := add_div _ _ _
    _ = (fullRowRankCount n : ℝ) / 2 ^ (n * n) + (n : ℝ) ^ 2 * (3 / 4) ^ n := by
        rw [hfrac]

/-- **The A354741 limit.** The fraction of `n × n` Boolean matrices
with full Boolean row rank `n` tends to `1` as `n → ∞` — the
conjectured limit stated in the comment of OEIS A354741, in contrast
with the 𝔽₂ limit `∏ (1 − 2⁻ⁱ) ≈ 0.2888` (A048651). Squeeze between
`1 − n²(3/4)ⁿ` and `1`. -/
theorem fullRowRankFraction_tendsto_one :
    Tendsto fullRowRankFraction atTop (nhds 1) := by
  have h0 : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * (3 / 4) ^ n) atTop (nhds 0) :=
    tendsto_pow_const_mul_const_pow_of_lt_one 2 (by norm_num) (by norm_num)
  have hlow : Tendsto (fun n : ℕ => 1 - (n : ℝ) ^ 2 * (3 / 4) ^ n)
      atTop (nhds 1) := by
    simpa using h0.const_sub 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · exact eventually_atTop.mpr ⟨2, fun n hn => one_sub_le_fullRowRankFraction hn⟩
  · exact Eventually.of_forall fullRowRankFraction_le_one

/-! ## 8. 𝔽₂ contrast (A354741 vs A286331 at n = 3)

Boolean (∨, ∧) row rank is NOT 𝔽₂ (xor) rank, and the two counting
problems genuinely diverge: A354741 row 3 is `1, 49, 306, 156` while
the GF(2)-rank triangle A286331 row 3 is `1, 49, 294, 168`. Below both
diagonal entries are computed in-kernel over the same 512 matrices:
exactly 156 have full Boolean row rank, while exactly
168 = (2³−1)(2³−2)(2³−4) are nonsingular over `ZMod 2` (full 𝔽₂ rank
iff no nonempty set of rows xor-sums to zero — over 𝔽₂ every linear
combination is a subset sum). Had xor arithmetic leaked into
`BoolSemiring`, the first count would come out 168, not 156. The limit
of the full-rank fraction differs accordingly: `∏ (1 − 2⁻ⁱ) ≈ 0.2888`
(A048651) over 𝔽₂, versus `1` here
(`fullRowRankFraction_tendsto_one`). -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
example : fullRowRankCount 3 = 156 := by
  rw [fullRowRankCount_eq_card_filter_not (by omega)]
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
example : (Finset.univ.filter fun A : Fin 3 → Fin 3 → ZMod 2 =>
    ∀ T : Finset (Fin 3), (∀ j, (∑ x ∈ T, A x j) = 0) → T = ∅).card = 168 := by
  decide

-- Satisfiability: every hypothesis above is jointly instantiable.
example : BoolRankLE (boolId 2) (Finset.univ : Finset (Fin 2)).card :=
  boolRankLE_card_of_rowSpan_eq rfl
example : boolRowRank (boolId 2) = 2 :=
  boolRowRank_eq_of_not_exists_rowLE (le_refl 2) (by decide)
example : 1 - (2 : ℝ) ^ 2 * (3 / 4) ^ 2 ≤ fullRowRankFraction 2 :=
  one_sub_le_fullRowRankFraction (le_refl 2)

-- The fraction is not junk: at n = 1 it is exactly 1/2 (T(1,1) = 1 of
-- the 2 one-entry matrices, A354741 row 1).
example : fullRowRankFraction 1 = 1 / 2 := by
  have h1 : fullRowRankCount 1 = 1 := by
    rw [fullRowRankCount_eq_card_filter_not le_rfl]
    decide
  show (fullRowRankCount 1 : ℝ) / 2 ^ (1 * 1) = 1 / 2
  rw [h1]
  norm_num

/-! ## Axiom audit (every named declaration; all are sorry-free) -/

#print axioms RowLE
#print axioms instDecidableRowLE
#print axioms instDecidableBoolRowRankLE
#print axioms rowsSum
#print axioms rowsSum_singleton
#print axioms rowLE_rowsSum
#print axioms rowSpan
#print axioms mem_rowSpan_self
#print axioms BoolRowRankLE
#print axioms BoolRowRankLE.mono
#print axioms boolRowRankLE_rows
#print axioms exists_boolRowRankLE
#print axioms boolRowRank
#print axioms boolRowRankLE_boolRowRank
#print axioms boolRowRank_le_of_boolRowRankLE
#print axioms boolRowRank_le_iff
#print axioms boolRowRank_eq_iff
#print axioms boolRowRank_le_rows
#print axioms boolRankLE_card_of_rowSpan_eq
#print axioms boolRank_le_boolRowRank
#print axioms boolRowRank_eq_of_antichain
#print axioms boolRowRank_boolId
#print axioms card_filter_rowLE_le
#print axioms card_dominatedRowLE_le
#print axioms boolRowRank_eq_of_not_exists_rowLE
#print axioms card_boolMatrix
#print axioms fullRowRankCount
#print axioms fullRowRankCount_eq_card_filter_not
#print axioms two_pow_le_fullRowRankCount_add
#print axioms fullRowRankFraction
#print axioms fullRowRankFraction_le_one
#print axioms one_sub_le_fullRowRankFraction
#print axioms fullRowRankFraction_tendsto_one

end BilinearComplexity
