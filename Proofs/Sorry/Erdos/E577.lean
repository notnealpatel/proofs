/-
  Erdős Problem #577 — vertex-disjoint 4-cycles (Erdős–Faudree).
  Status: proved (Wang 2010).  Tier D statement archive (the ~45-page
  case analysis is a campaign, not a lane).

  Verbatim statement (`goof erdos fetch 577`, pulled 2026-08-05):

    "If $G$ is a graph with $4k$ vertices and minimum degree at least
    $2k$ then $G$ contains $k$ vertex-disjoint $4$-cycles."

  DB remarks: conjecture of Erdős–Faudree; proved by Wang [Wa10]
  ("Proof of the Erdős-Faudree conjecture on quadrilaterals",
  Graphs Combin. 2010, 833–877).

  Mathlib inventory: `SimpleGraph.minDegree`, `SimpleGraph.cycleGraph`
  and copies (`⊑` via Copy.lean); vertex-disjoint packing has no
  Mathlib API — encoded below via a family of disjoint 4-sets each
  spanning a C₄ copy.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E577

open SimpleGraph

/-- `HasDisjointC4s G k`: `G` contains `k` vertex-disjoint 4-cycles —
    a family of pairwise-disjoint 4-element vertex sets, each carrying
    a 4-cycle of `G` (as a cyclic ordering with the four cycle edges
    present; chords allowed — a C₄ copy need not be induced). -/
def HasDisjointC4s {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (k : ℕ) : Prop :=
  ∃ f : Fin k → (Fin 4 → V),
    (∀ i, Function.Injective (f i)) ∧
    (∀ i j, i ≠ j → ∀ a b, f i a ≠ f j b) ∧
    ∀ i, G.Adj (f i 0) (f i 1) ∧ G.Adj (f i 1) (f i 2) ∧
      G.Adj (f i 2) (f i 3) ∧ G.Adj (f i 3) (f i 0)

/-- The complete graph on four vertices contains the identity-ordered C₄. -/
theorem completeGraph_four_hasC4 : HasDisjointC4s (⊤ : SimpleGraph (Fin 4)) 1 := by
  refine ⟨fun _ a => a, ?_, ?_, ?_⟩
  · intro i
    exact Function.injective_id
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  · intro i
    dsimp only
    decide

example : 1 ≤ (1 : ℕ) ∧ 2 * 1 ≤ (⊤ : SimpleGraph (Fin (4 * 1))).minDegree ∧
    HasDisjointC4s (⊤ : SimpleGraph (Fin (4 * 1))) 1 := by
  refine ⟨by decide, ?_, completeGraph_four_hasC4⟩
  simp [SimpleGraph.minDegree_top]

/-- **Erdős #577, Wang's theorem** ([Wa10]): a graph on `4k` vertices
    with minimum degree at least `2k` contains `k` vertex-disjoint
    4-cycles.

    Source text as in the header.  Guards: `1 ≤ k` (k = 0 is
    trivially true and the min-degree hypothesis at k = 0 is empty).

    Archive rationale: Wang's full extremal case analysis remains admitted.
    The elementary four-vertex slice below exhausts the six independent
    edge choices and does not depend on this headline theorem. -/
theorem wang_erdos_faudree (k : ℕ) (hk : 1 ≤ k)
    (G : SimpleGraph (Fin (4 * k))) [DecidableRel G.Adj]
    (hdeg : 2 * k ≤ G.minDegree) :
    HasDisjointC4s G k := by
  sorry

private theorem cycle_singleton (G : SimpleGraph (Fin 4)) (f : Fin 4 → Fin 4)
    (hf : Function.Injective f)
    (he : G.Adj (f 0) (f 1) ∧ G.Adj (f 1) (f 2) ∧
      G.Adj (f 2) (f 3) ∧ G.Adj (f 3) (f 0)) : HasDisjointC4s G 1 := by
  refine ⟨fun _ => f, fun _ => hf, ?_, fun _ => he⟩
  intro i j hij
  exact (hij (Subsingleton.elim i j)).elim

/-- Every graph on four vertices with minimum degree at least two contains
    a C₄, by exhaustion of its six independent undirected edge choices. -/
theorem wang_k1 (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj]
    (hdeg : 2 ≤ G.minDegree) :
    HasDisjointC4s G 1 := by
  have hd (v : Fin 4) : 2 ≤ ∑ j : Fin 4, if G.Adj v j then (1 : ℕ) else 0 := by
    rw [← G.degree_eq_sum_if_adj (R := ℕ)]
    exact hdeg.trans (G.minDegree_le_degree v)
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  have h3 := hd 3
  clear hd hdeg
  simp only [Fin.sum_univ_four] at h0 h1 h2 h3
  have hc : (G.Adj 0 1 ∧ G.Adj 1 2 ∧ G.Adj 2 3 ∧ G.Adj 3 0) ∨
      (G.Adj 0 1 ∧ G.Adj 1 3 ∧ G.Adj 3 2 ∧ G.Adj 2 0) ∨
      (G.Adj 0 2 ∧ G.Adj 2 1 ∧ G.Adj 1 3 ∧ G.Adj 3 0) := by
    by_cases h01 : G.Adj 0 1 <;> by_cases h02 : G.Adj 0 2 <;>
      by_cases h03 : G.Adj 0 3 <;> by_cases h12 : G.Adj 1 2 <;>
      by_cases h13 : G.Adj 1 3 <;> by_cases h23 : G.Adj 2 3 <;>
      simp only [G.adj_comm, SimpleGraph.irrefl, h01, h02, h03, h12, h13, h23,
        ↓reduceIte, and_true, and_false, or_true, or_false] at h0 h1 h2 h3 ⊢ <;> omega
  rcases hc with hc | hc | hc
  · exact cycle_singleton G id Function.injective_id hc
  · apply cycle_singleton G ![0, 1, 3, 2]
    · decide
    · simpa using hc
  · apply cycle_singleton G ![0, 2, 1, 3]
    · decide
    · simpa using hc

/-- The complete bipartite graph with parts `{0,1,2}` and `{3,4,5,6,7}`. -/
private def bipartiteGraph : SimpleGraph (Fin 8) where
  Adj u v := (u.val < 3 ∧ 3 ≤ v.val) ∨ (v.val < 3 ∧ 3 ≤ u.val)
  symm := ⟨fun u v h => h.symm⟩
  loopless := ⟨by intro u h; omega⟩

example : bipartiteGraph.Adj 0 3 := by
  change (0 < 3 ∧ 3 ≤ 3) ∨ (3 < 3 ∧ 3 ≤ 0)
  decide
example : ¬ bipartiteGraph.Adj 0 2 := by
  change ¬ ((0 < 3 ∧ 3 ≤ 2) ∨ (2 < 3 ∧ 3 ≤ 0))
  decide
example : ¬ bipartiteGraph.Adj 3 7 := by
  change ¬ ((3 < 3 ∧ 3 ≤ 7) ∨ (7 < 3 ∧ 3 ≤ 3))
  decide

/-- Sharpness sanity: min degree `2k − 1` does not suffice —
    K_{2k-1, 2k+1} has min degree 2k−1 and its C₄-packing is limited
    by the smaller side: at most ⌊(2k−1)/2⌋ = k−1 disjoint C₄s (each
    C₄ uses 2 vertices per side).  Recorded at k = 2: K_{3,5} on 8
    vertices, min degree 3, no 2 disjoint C₄s.
    The obstruction is an injection of four chosen left-side vertices
    into a side containing only three vertices. -/
theorem sharpness_k2 :
    ∃ (G : SimpleGraph (Fin 8)) (_ : DecidableRel G.Adj),
      3 ≤ G.minDegree ∧ ¬ HasDisjointC4s G 2 := by
  letI : DecidableRel bipartiteGraph.Adj := fun u v =>
    inferInstanceAs (Decidable ((u.val < 3 ∧ 3 ≤ v.val) ∨
      (v.val < 3 ∧ 3 ≤ u.val)))
  refine ⟨bipartiteGraph, inferInstance, ?_, ?_⟩
  · apply bipartiteGraph.le_minDegree_of_forall_le_degree
    intro v
    have hd : bipartiteGraph.degree v = ∑ j : Fin 8,
        if bipartiteGraph.Adj v j then (1 : ℕ) else 0 :=
      bipartiteGraph.degree_eq_sum_if_adj (R := ℕ) v
    rw [hd]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    fin_cases v <;> norm_num [bipartiteGraph]
  · rintro ⟨f, hf, hdisj, he⟩
    let pos : Fin 2 → Fin 2 → Fin 4 := fun i b =>
      if (f i 0).val < 3 then (if b = 0 then 0 else 2)
      else (if b = 0 then 1 else 3)
    have hleft (i : Fin 2) (b : Fin 2) : (f i (pos i b)).val < 3 := by
      have hedges := he i
      change (((f i 0).val < 3 ∧ 3 ≤ (f i 1).val) ∨
        ((f i 1).val < 3 ∧ 3 ≤ (f i 0).val)) ∧
        (((f i 1).val < 3 ∧ 3 ≤ (f i 2).val) ∨
        ((f i 2).val < 3 ∧ 3 ≤ (f i 1).val)) ∧
        (((f i 2).val < 3 ∧ 3 ≤ (f i 3).val) ∨
        ((f i 3).val < 3 ∧ 3 ≤ (f i 2).val)) ∧
        (((f i 3).val < 3 ∧ 3 ≤ (f i 0).val) ∨
        ((f i 0).val < 3 ∧ 3 ≤ (f i 3).val)) at hedges
      fin_cases b <;> dsimp [pos] <;> split <;> omega
    have hpos (i : Fin 2) : Function.Injective (pos i) := by
      intro a b hab
      by_cases hl : (f i 0).val < 3 <;>
        fin_cases a <;> fin_cases b <;> simp [pos, hl] at hab ⊢
    let g : Fin 2 × Fin 2 → Fin 3 := fun x =>
      ⟨(f x.1 (pos x.1 x.2)).val, hleft x.1 x.2⟩
    have hg : Function.Injective g := by
      intro x y hxy
      have hv : f x.1 (pos x.1 x.2) = f y.1 (pos y.1 y.2) := by
        apply Fin.ext
        exact congrArg (fun z : Fin 3 => z.val) hxy
      have hi : x.1 = y.1 := by
        by_contra hne
        exact hdisj x.1 y.1 hne (pos x.1 x.2) (pos y.1 y.2) hv
      have hb : x.2 = y.2 := by
        apply hpos x.1
        apply hf x.1
        simpa only [hi] using hv
      exact Prod.ext hi hb
    have hcard := Fintype.card_le_of_injective g hg
    norm_num at hcard

end ErdosCandidates.E577

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches `goof erdos fetch 577` exactly.
   - Wang [Wa10] attribution and Erdos-Faudree conjecture provenance confirmed.
   - HasDisjointC4s encoding is faithful: Fin k -> Fin 4 -> V with per-cycle
     injectivity, pairwise vertex-disjointness, and the four cycle edges
     0-1, 1-2, 2-3, 3-0 correctly capture vertex-disjoint C4 copies
     (chords allowed, as intended).
   - Sharpness K_{3,5} arithmetic verified: 8 vertices, min degree 3 (5-side
     has degree 3), each C4 uses 2 per side, two disjoint C4s need 4 from the
     3-side -- impossible.  Claim is correct.
   - k=1 sanity rationale in docstring is sound.
-/
