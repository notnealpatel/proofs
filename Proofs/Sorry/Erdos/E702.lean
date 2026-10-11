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
  sorry

/-- Satisfiability of the conclusion at a small model: in the family
    `{{0,1,2,3}, {3,4,5,6}}` (k = 4, n = 7) the two members meet
    exactly in `{3}`.  -- PROVABLE (decide). -/
example :
    ∃ A ∈ ({{0,1,2,3}, {3,4,5,6}} : Finset (Finset (Fin 7))),
    ∃ B ∈ ({{0,1,2,3}, {3,4,5,6}} : Finset (Finset (Fin 7))),
      (A ∩ B).card = 1 := by
  sorry

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
  sorry

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
