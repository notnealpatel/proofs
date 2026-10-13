/-
  Erdős Problem #58 — chromatic number versus number of odd cycle lengths.
  Status: proved (Gyárfás 1992).  Tier A proof target.

  Verbatim statement (`goof erdos fetch 58`, pulled 2026-08-05):

    "If $G$ is a graph which contains odd cycles of $\leq k$ different
    lengths then $\chi(G)\leq 2k+2$, with equality if and only if $G$
    contains $K_{2k+2}$."

  DB remarks: conjectured by Bollobás–Erdős; k = 1 confirmed by
  Bollobás–Shelah; proved by Gyárfás [Gy92], who proved the stronger
  result that a 2-connected such G is either K_{2k+2} or has a vertex of
  degree ≤ 2k.  Strengthening by Gao–Huo–Ma [GaHuMa21]: χ(G) ≥ 2k+3
  forces cycles of k+1 consecutive odd lengths.

  Mathlib inventory (leandoc 2026-08-05):
  * `SimpleGraph.chromaticNumber : ℕ∞` (Coloring/Vertex.lean);
  * `SimpleGraph.Walk.IsCycle`, `Walk.length` for cycle lengths;
  * `SimpleGraph.CliqueFree` / `IsNClique` for the K_{2k+2} condition;
  * `Set.Finite`, `Set.ncard` for "≤ k different lengths".
  No off-the-shelf odd-cycle-spectrum machinery; the definition layer
  below is fresh.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E58

open SimpleGraph

variable {V : Type*}

/-- The set of lengths of odd cycles of `G` — the "odd cycle spectrum".
    A length `ℓ` is in the spectrum iff some cycle of `G` has odd length
    `ℓ`. -/
def oddCycleLengths (G : SimpleGraph V) : Set ℕ :=
  {ℓ : ℕ | Odd ℓ ∧ ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = ℓ}

/-- Every cycle in a finite graph has length between three and the vertex count. -/
theorem cycle_length_bounds [Fintype V] {G : SimpleGraph V} {v : V}
    {c : G.Walk v v} (hc : c.IsCycle) :
    3 ≤ c.length ∧ c.length ≤ Fintype.card V := by
  refine ⟨hc.three_le_length, ?_⟩
  have hcard := hc.support_nodup.length_le_card
  simpa [List.length_tail, Walk.length_support] using hcard

/-- A complete graph on at least three vertices contains a triangle. -/
theorem triangle_in_top (n : ℕ) :
    ∃ (v : Fin (n + 3)) (c : (⊤ : SimpleGraph (Fin (n + 3))).Walk v v),
      c.IsCycle ∧ c.length = 3 := by
  let a : Fin (n + 3) := ⟨0, by omega⟩
  let b : Fin (n + 3) := ⟨1, by omega⟩
  let d : Fin (n + 3) := ⟨2, by omega⟩
  have hab : (⊤ : SimpleGraph (Fin (n + 3))).Adj a b := by simp [a, b]
  have hbd : (⊤ : SimpleGraph (Fin (n + 3))).Adj b d := by simp [b, d]
  have hda : (⊤ : SimpleGraph (Fin (n + 3))).Adj d a := by simp [d, a]
  let c := Walk.cons hab (Walk.cons hbd (Walk.cons hda Walk.nil))
  refine ⟨a, c, ?_, rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply Walk.IsPath.mk'
    change ([b, d, a] : List (Fin (n + 3))).Nodup
    simp [a, b, d]
  · simp [c]

/-- Ground truth: the odd cycle spectrum of a triangle is `{3}`.
    -- PROVABLE (the only cycles of `K₃` have length 3). -/
theorem oddCycleLengths_top_fin_three : oddCycleLengths (⊤ : SimpleGraph (Fin 3)) = {3} := by
  ext ℓ
  constructor
  · rintro ⟨hodd, v, c, hc, hlen⟩
    have hb := cycle_length_bounds hc
    simp only [Fintype.card_fin] at hb
    simp only [Set.mem_singleton_iff]
    omega
  · intro hℓ
    have hlen : ℓ = 3 := Set.mem_singleton_iff.mp hℓ
    subst ℓ
    obtain ⟨v, c, hc, hlength⟩ := triangle_in_top 0
    exact ⟨by decide, v, c, hc, hlength⟩

example : oddCycleLengths (⊤ : SimpleGraph (Fin 3)) = {3} :=
  oddCycleLengths_top_fin_three

/-- Ground truth: bipartite graphs have empty odd cycle spectrum —
    e.g. `K₂`.  Guards the k = 0 edge of the statement: with no odd
    cycles the bound reads χ ≤ 2, which is the bipartite case.
    -- PROVABLE. -/
theorem oddCycleLengths_top_fin_two : oddCycleLengths (⊤ : SimpleGraph (Fin 2)) = ∅ := by
  ext ℓ
  constructor
  · rintro ⟨hodd, v, c, hc, hlen⟩
    have hb := cycle_length_bounds hc
    simp only [Fintype.card_fin] at hb
    omega
  · simp

example : oddCycleLengths (⊤ : SimpleGraph (Fin 2)) = ∅ :=
  oddCycleLengths_top_fin_two

/-- **Erdős #58, Gyárfás's theorem, headline bound** (Gy92): if a finite
    graph has at most `k` different odd cycle lengths, then
    `χ(G) ≤ 2k + 2`.

    Source text: "If $G$ is a graph which contains odd cycles of $\leq k$
    different lengths then $\chi(G)\leq 2k+2$..."

    Formalization notes: `chromaticNumber : ℕ∞`, so the bound is stated
    in `ℕ∞`; `V` finite keeps χ finite.  "≤ k different lengths" =
    `(oddCycleLengths G).Finite ∧ ncard ≤ k` — for finite `V` the
    spectrum is automatically finite, so we state just the `ncard`
    bound with `Set.ncard` (which is 0 for infinite sets; harmless here
    since the set is finite, but the `Finite` conjunct is kept to guard
    the degenerate reading per STYLE.md).

    Proof sketch (attack plan): Gyárfás's induction: reduce to a
    2-connected block (χ is the max over blocks; block decomposition is
    the missing Mathlib piece — expect to prove a weak form: induction
    on vertices, deleting a vertex of degree ≤ 2k+1).  Core lemma: a
    2-connected graph with min degree ≥ 2k+1 that is not K_{2k+2} has
    odd cycles of > k lengths, proved via a DFS/longest-path argument
    producing cycles of many different parities.  First slice to
    attempt: `k = 1` (Bollobás–Shelah): one odd cycle length forces
    χ ≤ 4.  Mathlib tools: `chromaticNumber_le_iff_colorable`,
    `Colorable` monotonicity, strong induction on `Fintype.card V`.
    Effort M (headline) per candidates audit. -/
theorem gyarfas_chromatic_bound [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hfin : (oddCycleLengths G).Finite)
    (hk : (oddCycleLengths G).ncard ≤ k) :
    G.chromaticNumber ≤ (2 * k + 2 : ℕ) := by
  sorry

/-- **Erdős #58, equality case** (Gy92): equality `χ(G) = 2k + 2` holds
    iff `G` contains `K_{2k+2}` (as a subgraph, i.e. `G` is not
    `(2k+2)`-clique-free).  The forward direction is the hard one; the
    backward direction is the trivial `χ ≥ clique number` plus the
    headline bound.  Effort L per candidates audit — sorry'd separately
    from the headline so the lane can land the bound first. -/
theorem gyarfas_equality_iff [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hfin : (oddCycleLengths G).Finite)
    (hk : (oddCycleLengths G).ncard ≤ k) :
    G.chromaticNumber = (2 * k + 2 : ℕ) ↔ ¬ G.CliqueFree (2 * k + 2) := by
  sorry

/-- The odd cycle spectrum of the complete graph on four vertices is `{3}`. -/
theorem oddCycleLengths_top_fin_four : oddCycleLengths (⊤ : SimpleGraph (Fin 4)) = {3} := by
  ext ℓ
  constructor
  · rintro ⟨hodd, v, c, hc, hlen⟩
    have hb := cycle_length_bounds hc
    simp only [Fintype.card_fin] at hb
    obtain ⟨k, hk⟩ := hodd
    simp only [Set.mem_singleton_iff]
    omega
  · intro hℓ
    have hlen : ℓ = 3 := Set.mem_singleton_iff.mp hℓ
    subst ℓ
    obtain ⟨v, c, hc, hlength⟩ := triangle_in_top 1
    exact ⟨by decide, v, c, hc, hlength⟩

/-- The complete graph on four vertices jointly realizes one odd cycle length and chromatic number four. -/
theorem top_fin_four_spectrum_chromatic :
    (oddCycleLengths (⊤ : SimpleGraph (Fin 4))).ncard = 1 ∧
    (⊤ : SimpleGraph (Fin 4)).chromaticNumber = (4 : ℕ) := by
  constructor
  · rw [oddCycleLengths_top_fin_four]
    exact Set.ncard_singleton 3
  · simp [SimpleGraph.chromaticNumber_top]

/-- Satisfiability of the equality case at `k = 1`: `K₄` has odd cycle
    spectrum `{3}` (one length) and `χ(K₄) = 4 = 2·1 + 2`.
    -- PROVABLE (decide-scale + `chromaticNumber_top`). -/
example :
    (oddCycleLengths (⊤ : SimpleGraph (Fin 4))).ncard = 1 ∧
    (⊤ : SimpleGraph (Fin 4)).chromaticNumber = (4 : ℕ) :=
  top_fin_four_spectrum_chromatic

/-- Sanity for the `k = 1` slice (Bollobás–Shelah): a 5-cycle has one
    odd cycle length and χ(C₅) = 3 ≤ 4.
    -- PROVABLE (`chromaticNumber_cycleGraph_of_odd` exists in Mathlib,
    leandoc hit in Coloring/Constructions.lean). -/
theorem cycleGraph_five_chromaticNumber_le_four :
    (cycleGraph 5).chromaticNumber ≤ (4 : ℕ) := by
  rw [SimpleGraph.chromaticNumber_cycleGraph_of_odd 5 (by decide) (by decide)]
  norm_num

example : (cycleGraph 5).chromaticNumber ≤ (4 : ℕ) :=
  cycleGraph_five_chromaticNumber_le_four

end ErdosCandidates.E58

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - DB statement matches file header verbatim.
   - Solver attribution Gyarfas [Gy92] matches DB.
   - `oddCycleLengths` definition is faithful: set of lengths l such that l is odd and some cycle of G has length l.
   - `chromaticNumber : ℕ∞` correctly handled via cast `(2 * k + 2 : ℕ)` to `ℕ∞`.
   - Equality case `χ = 2k+2 ↔ ¬CliqueFree (2k+2)` faithfully translates "iff G contains K_{2k+2}": ¬CliqueFree n = "has an n-clique" = "contains K_n as subgraph".
   - k=0 edge: no odd cycles means χ ≤ 2, the bipartite bound. Correct (bipartite ↔ no odd cycles).
   - K₄ satisfiability: odd cycle spectrum = {3} (only triangles), χ(K₄) = 4 = 2*1+2. Correct.
   - C₅ sanity: one odd cycle length (5), χ(C₅) = 3 ≤ 4. Correct.
   - `Set.ncard` for "≤ k different lengths" is appropriate; finite guard `hfin` included.
   - No Mathlib definition for odd-cycle-spectrum exists; fresh `oddCycleLengths` is justified.
-/
