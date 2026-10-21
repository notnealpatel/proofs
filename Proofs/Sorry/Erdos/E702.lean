/-
  Erdős Problem #702 — Frankl's forbidden singleton intersection.
  Status: proved (Frankl 1977; Katona unpublished for k = 4).
  Tier C infrastructure target (a shifting lemma for the extremal
  set-theory lane).

  Verbatim statement (`goof erdos fetch 702`, pulled 2026-08-05):

    "Let $k\geq 4$. If $\mathcal{F}$ is a family of subsets of
    $\{1,\ldots,n\}$ with $\lvert A\rvert=k$ for all
    $A\in \mathcal{F}$ and
    $\lvert \mathcal{F}\rvert >\binom{n-2}{k-2}$ then there are
    $A,B\in\mathcal{F}$ such that $\lvert A\cap B\rvert=1$."

  DB remarks: conjecture of Erdős–Sós; Katona proved k = 4
  (unpublished), Frankl [Fr77] all k ≥ 4.  Also in [Er76b, p. 186].
  See #703.

  Note k ≥ 4 is necessary as a uniform threshold: for k = 3 the
  Steiner-ish constructions beat C(n−2, k−2); Frankl's proof uses a
  bespoke shifting ("compression") argument for the forbidden
  1-intersection.

  Repo adjacency: compression operators in
  `Proofs/Erdos/Erdos20` (sunflower lane); the shifting lemma here is
  NEW infrastructure (partial reuse only), which is the point of the
  candidate — it deepens the extremal set-theory lane beyond
  sunflowers.

  Mathlib inventory: `Finset (Finset (Fin n))`, `Finset.powersetCard`;
  `Finset.memberSubfamily`-style compressions exist in Mathlib's
  `Combinatorics/SetFamily/Compression/` (UV-compressions, Down
  compressions) — evaluate reuse before writing a bespoke shift.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E702

/- ORIGINAL STATEMENT (removed: false as written; see
   `frankl_singleton_intersection_false` below).  Verbatim text
   (Lean block comments nest, so the inner docstring is kept as is):

/-- **Erdős #702, Frankl's theorem** (Fr77): a `k`-uniform family on
    `{1, …, n}` with more than `C(n−2, k−2)` members contains two sets
    meeting in exactly one point (`k ≥ 4`).

    Source text as in the header.  ℕ-subtractions `n − 2`, `k − 2` are
    exact under `4 ≤ k ≤ n` (the `k ≤ n` guard also keeps the family
    nonempty-able).

    Proof sketch (attack plan): Frankl's shifting — replace F by a
    compressed family preserving cardinality and the absence of
    1-intersections, until the family is an up-set under the shift
    order supported on {1, 2}; then count: a shifted family with no
    two members meeting in one point must have every member contain
    both 1 and 2 (or a similar pinned pair), giving |F| ≤ C(n−2, k−2).
    The compression preserving ¬(|A∩B|=1) is the new lemma — Mathlib's
    UV-compression (`Finset.compression`) is the candidate engine.
    Effort M–L per candidates audit. -/
theorem frankl_singleton_intersection (n k : ℕ) (hk : 4 ≤ k) (hkn : k ≤ n)
    (F : Finset (Finset (Fin n)))
    (huniform : ∀ A ∈ F, A.card = k)
    (hcard : (n - 2).choose (k - 2) < F.card) :
    ∃ A ∈ F, ∃ B ∈ F, (A ∩ B).card = 1 := by
  sorry
-/

/-- The concrete family refuting the uniform-in-`n` reading: all
    `4`-subsets of `Fin 5`. -/
def allFourSubsetsFin5 : Finset (Finset (Fin 5)) :=
  (Finset.univ : Finset (Fin 5)).powersetCard 4

/-- Ground truth: `allFourSubsetsFin5` has `C(5,4) = 5` members. -/
example : allFourSubsetsFin5.card = 5 := by decide

/-- **Refutation of the original `frankl_singleton_intersection`.**

    Original claim (quoted): "for all `n k` with `4 ≤ k ≤ n`, every
    `F : Finset (Finset (Fin n))` with `∀ A ∈ F, A.card = k` and
    `(n - 2).choose (k - 2) < F.card` has `A, B ∈ F` with
    `(A ∩ B).card = 1`."

    Counterexample: `n = 5`, `k = 4`, `F` = all `4`-subsets of
    `Fin 5`.  Any two members meet in at least `3` points, so no two
    meet in exactly one, yet `F.card = 5 > 3 = C(3, 2)`.  The same
    works for every `k ≥ 4` at `n = k + 1` (indeed any `n ≤ 2k − 2`
    forces pairwise intersections of size `≥ 2`).

    Source of the discrepancy: erdosproblems.com #702 states the
    Erdős–Sós conjecture without a range for `n`, but Frankl [Fr77]
    proves `|F| ≤ C(n−2, k−2)` only for `k ≥ 4` and `n ≥ n₀(k)`
    (`n` sufficiently large), as restated by Keevash–Mubayi–Wilson
    (SIAM J. Discrete Math. 20 (2007)) and Linz (arXiv:2604.00418,
    which gets the exact range `3k − 3 ≤ n ≤ k² − k + 1`).  The
    intended hypothesis is therefore `n` large relative to `k`; see
    `frankl_singleton_intersection_eventually`. -/
theorem frankl_singleton_intersection_false :
    ¬ ∀ (n k : ℕ), 4 ≤ k → k ≤ n →
      ∀ F : Finset (Finset (Fin n)),
        (∀ A ∈ F, A.card = k) →
        (n - 2).choose (k - 2) < F.card →
        ∃ A ∈ F, ∃ B ∈ F, (A ∩ B).card = 1 := by
  intro h
  have huniform : ∀ A ∈ allFourSubsetsFin5, A.card = 4 := by decide
  have hcard : (5 - 2).choose (4 - 2) < allFourSubsetsFin5.card := by decide
  have hnone : ¬ ∃ A ∈ allFourSubsetsFin5, ∃ B ∈ allFourSubsetsFin5,
      (A ∩ B).card = 1 := by decide
  exact hnone (h 5 4 le_rfl (by norm_num) allFourSubsetsFin5 huniform hcard)

/-- **Erdős #702, Frankl's theorem (corrected form, [Fr77])**: for
    every `k ≥ 4` there is `n₀` such that for all `n ≥ n₀`, a
    `k`-uniform family on `Fin n` with more than `C(n−2, k−2)`
    members contains two sets meeting in exactly one point.

    This is the statement Frankl actually proves (`n` sufficiently
    large); the uniform version without a lower bound on `n` is false
    (`frankl_singleton_intersection_false`).  `n₀ ≥ 4` is not
    required explicitly: for `n ≥ n₀ ≥ k ≥ 4` the subtractions are
    exact, and since `n₀` is existential the prover may choose it as
    large as needed.  OPEN in this repository (known theorem, not yet
    formalized): Frankl's shifting argument, with Mathlib's
    UV-compression (`Finset.compression`) as the candidate engine. -/
theorem frankl_singleton_intersection_eventually (k : ℕ) (hk : 4 ≤ k) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ F : Finset (Finset (Fin n)),
        (∀ A ∈ F, A.card = k) →
        (n - 2).choose (k - 2) < F.card →
        ∃ A ∈ F, ∃ B ∈ F, (A ∩ B).card = 1 := by
  sorry

/-- Sharpness witness: the family of all `k`-sets containing `{0, 1}`
    has exactly `C(n−2, k−2)` members and all pairwise intersections
    of size ≥ 2 — so the threshold is tight.
    -- PROVABLE (bijection with (k−2)-subsets of the remaining n−2
    points; `Finset.card_powersetCard` + image counting).  Effort S;
    the natural first sorry-free landing. -/
theorem sharpness_pinned_pair (n k : ℕ) (hk : 4 ≤ k) (hkn : k ≤ n) :
    ∃ F : Finset (Finset (Fin n)),
      (∀ A ∈ F, A.card = k) ∧
      F.card = (n - 2).choose (k - 2) ∧
      ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card := by
  have hn : 4 ≤ n := hk.trans hkn
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let P : Finset (Fin n) := {a, b}
  have hab : a ≠ b := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = 1 at hv
    omega
  have hP : P.card = 2 := by simp [P, hab]
  let C : Finset (Fin n) := Finset.univ \ P
  have hC : C.card = n - 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ P)]
    simp [hP]
  let S := C.powersetCard (k - 2)
  have hdis : ∀ X ∈ S, Disjoint P X := by
    intro X hX
    have hsub : X ⊆ C := (Finset.mem_powersetCard.mp hX).1
    apply Finset.disjoint_left.mpr
    intro x hxP hxX
    exact (Finset.mem_sdiff.mp (hsub hxX)).2 hxP
  have hinj : Set.InjOn (fun X => P ∪ X) S := by
    intro X hX Y hY hXY
    have hdiff := congrArg (fun T => T \ P) hXY
    simpa only [Finset.union_sdiff_cancel_left (hdis X hX),
      Finset.union_sdiff_cancel_left (hdis Y hY)] using hdiff
  refine ⟨S.image (fun X => P ∪ X), ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hA
    have hXcard : X.card = k - 2 := (Finset.mem_powersetCard.mp hX).2
    rw [Finset.card_union_of_disjoint (hdis X hX), hP, hXcard]
    omega
  · rw [Finset.card_image_of_injOn hinj, Finset.card_powersetCard, hC]
  · intro A hA B hB
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hB
    have hsub : P ⊆ (P ∪ X) ∩ (P ∪ Y) := by
      intro x hx
      exact Finset.mem_inter.mpr ⟨Finset.mem_union_left X hx,
        Finset.mem_union_left Y hx⟩
    simpa only [hP] using Finset.card_le_card hsub

/-- The explicit four-element sets `{0,1,2,3}` and `{3,4,5,6}`
    in `Fin 7` belong to their two-member family and meet in one point. -/
theorem fin7_singleton_certificate :
    ∃ A ∈ ({{0,1,2,3}, {3,4,5,6}} : Finset (Finset (Fin 7))),
    ∃ B ∈ ({{0,1,2,3}, {3,4,5,6}} : Finset (Finset (Fin 7))),
      (A ∩ B).card = 1 := by
  refine ⟨{0, 1, 2, 3}, ?_, {3, 4, 5, 6}, ?_, ?_⟩ <;> decide

/-- Satisfiability of the conclusion at a small model: in the family
    `{{0,1,2,3}, {3,4,5,6}}` (k = 4, n = 7) the two members meet
    exactly in `{3}`.  -- PROVABLE (decide). -/
example :
    ∃ A ∈ ({{0,1,2,3}, {3,4,5,6}} : Finset (Finset (Fin 7))),
    ∃ B ∈ ({{0,1,2,3}, {3,4,5,6}} : Finset (Finset (Fin 7))),
      (A ∩ B).card = 1 := by
  exact fin7_singleton_certificate

/-- The `k = 3` boundary is genuinely different (why the problem says
    k ≥ 4): for k = 3 one can beat `C(n−2, 1) = n − 2` without a
    1-intersection — e.g. partition-style triple families with all
    pairwise intersections in {0, 2}.  Recorded as an existence
    statement at a concrete n to keep the k ≥ 4 hypothesis honest.
    Probe (sage) for the smallest witness before proving.
    -- PROVABLE-in-principle (decide once the witness family is
    pinned). -/
theorem k3_boundary :
    ∃ (n : ℕ) (F : Finset (Finset (Fin n))),
      (∀ A ∈ F, A.card = 3) ∧
      (n - 2).choose 1 < F.card ∧
      ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).card ≠ 1 := by
  refine ⟨4, (Finset.univ : Finset (Fin 4)).powersetCard 3, ?_⟩
  decide

end ErdosCandidates.E702

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches `goof erdos fetch 702` exactly.
   - Attributions correct: Erdos-Sos conjecture, Katona k=4 unpublished, Frankl [Fr77], [Er76b p.186].
   - N-subtractions n-2, k-2 guarded by 4 <= k <= n; exact under those hypotheses.
   - k3_boundary arithmetic verified: C(4,3)=4 triples of a 4-set, C(2,1)=2, 4>2, all pairwise
     intersections have size 2 (=3+3-4). Correct.
   - Sharpness witness (pinned-pair family of size C(n-2,k-2)) is standard and correctly stated.
   - No Mathlib `Ramsey` or `Frankl` overlap found.
-/
