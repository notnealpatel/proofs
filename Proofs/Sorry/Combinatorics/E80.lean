/-
  Erdős Problem #80 — edges in many triangles (books).
  Status: open.  Tier C archive target.

  Verbatim statement (`goof erdos fetch 80`, pulled 2026-08-05):

    "Let $c>0$ and let $f_c(n)$ be the maximal $m$ such that every
    graph $G$ with $n$ vertices and at least $cn^2$ edges, where each
    edge is contained in at least one triangle, must contain a book of
    size $m$, that is, an edge shared by at least $m$ different
    triangles.

    Estimate $f_c(n)$. In particular, is it true that
    $f_c(n)>n^{\epsilon}$ for some $\epsilon>0$? Or
    $f_c(n)\gg \log n$?"

  DB remarks (Erdős–Rothschild): Alon–Trotter: f_c(n) ≪_c √n for
  c < 1/4.  Szemerédi (regularity): f_c(n) → ∞.  Edwards (unpub.) and
  Khadzhiivanov–Nikiforov [KhNi79] independently: f_c(n) ≥ n/6 for
  c > 1/4.  Fox–Loh [FoLo12]: f_c(n) ≤ n^{O(1/log log n)} for all
  c < 1/4 — disproving the n^ε conjecture.  Potechin [Po18] further
  partial improvements (comment).

  The c > 1/4 slice below uses the classical finite counting route,
  as presented in Bollobás–Nikiforov, Books in graphs (2005),
  Theorem 1, arXiv:math/0405080. The proof counts triangle/vertex
  equal-adjacency incidences and uses Cauchy's degree-square bound;
  it does not use a Kruskal–Katona or Turán supersaturation claim.

  Mathlib inventory: `SimpleGraph.cliqueFinset 3` for triangles;
  book size of an edge = number of common neighbours of its ends.
-/
import Combinatorics.Books.Edwards

set_option autoImplicit false

namespace ErdosCandidates.E80

open SimpleGraph Finset

variable {n : ℕ}

/-- `bookSize G u v`: the number of triangles sharing the edge
    `{u, v}` — i.e. common neighbours of `u` and `v`. -/
abbrev bookSize (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    ℕ :=
  ErdosCandidates.Books.bookSize G u v

/-- `EveryEdgeInTriangle G`: each edge lies in at least one triangle. -/
abbrev EveryEdgeInTriangle (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Prop :=
  ErdosCandidates.Books.EveryEdgeInTriangle G

/-- In `K₄`, the edge joining vertices `0` and `1` has two common neighbours. -/
theorem k4_bookSize_zero_one : bookSize (⊤ : SimpleGraph (Fin 4)) 0 1 = 2 := by
  decide

/-- Ground truth: in `K₄` every edge is in exactly 2 triangles.
    -- PROVABLE (decide). -/
example : bookSize (⊤ : SimpleGraph (Fin 4)) 0 1 = 2 := by
  exact k4_bookSize_zero_one

/-- **Edwards / Khadzhiivanov–Nikiforov** (the c > 1/4 slice):
    more than `n²/4` edges force a book of size at least `n/6`.
    The unchanged archive conclusion `n ≤ 6·bookSize + 5` is a
    division-free weakening of the classical bound, not a replacement
    for its constant. The `EveryEdgeInTriangle` premise is retained.

    The production proof follows the equal-adjacency incidence count
    and degree-square inequality in Bollobás–Nikiforov, *Books in
    graphs*, European J. Combin. 26 (2005), 259–270, Theorem 1
    (arXiv:math/0405080); ordered counts avoid induced four-vertex
    infrastructure. Edwards' unpublished result and the independent
    Khadzhiivanov–Nikiforov (1979) result are classical, not new here. -/
theorem edwards_kn_book (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hn : 6 ≤ n)
    (he : n ^ 2 < 4 * G.edgeFinset.card)
    (ht : EveryEdgeInTriangle G) :
    ∃ u v : Fin n, G.Adj u v ∧ n ≤ 6 * bookSize G u v + 5 := by
  exact ErdosCandidates.Books.edwards_kn_book G hn he ht

/-- **Erdős #80, first conjecture — REFUTED by Fox–Loh** ([FoLo12]):
    it is NOT true that for `c < 1/4` one has `f_c(n) > n^ε`; there
    are graphs with `cn²` edges, every edge in a triangle, and max
    book size `≤ n^{C/log log n}`.  Archived as the negated form:
    for every `ε > 0` and `c < 1/4`, witnesses exist infinitely often.
    (Fox–Loh's construction is a pentagon-blowup with modifications —
    explicit but analytically sized.) -/
theorem fox_loh_refutation (c ε : ℝ) (hc : 0 < c) (hc4 : c < 1 / 4)
    (hε : 0 < ε) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
        c * n ^ 2 ≤ (G.edgeFinset.card : ℝ) ∧
        EveryEdgeInTriangle G ∧
        ∀ u v : Fin n, G.Adj u v → (bookSize G u v : ℝ) < (n : ℝ) ^ ε := by
  sorry

/-- The number of ordered adjacent pairs of `G` is twice its edge count. -/
private lemma card_adjPairs {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj] :
    #(univ.filter fun p : α × α => G.Adj p.1 p.2) = 2 * #G.edgeFinset := by
  rw [← G.sum_degrees_eq_twice_card_edges, card_filter, ← univ_product_univ, sum_product]
  refine sum_congr rfl fun v _ => ?_
  rw [← card_filter, ← card_neighborFinset_eq_degree, neighborFinset_eq_filter]

/-- If every edge of `G` lies in fewer than `m` triangles, then `G` has at most
    `n² · m` triangles: each triangle is the image of an ordered adjacent pair
    together with a common neighbour. -/
private lemma card_cliqueFinset_three_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (m : ℕ) (hsmall : ∀ u v, G.Adj u v → ErdosCandidates.Books.bookSize G u v < m) :
    #(G.cliqueFinset 3) ≤ n ^ 2 * m := by
  set P := univ.filter fun p : Fin n × Fin n => G.Adj p.1 p.2 with hP
  set NB : Fin n → Fin n → Finset (Fin n) :=
    fun a b => univ.filter fun w => G.Adj a w ∧ G.Adj b w with hNB
  have hsub : G.cliqueFinset 3 ⊆
      P.biUnion fun p => (NB p.1 p.2).image fun c => ({p.1, p.2, c} : Finset (Fin n)) := by
    intro t ht
    rw [mem_cliqueFinset_iff, is3Clique_iff] at ht
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht
    rw [mem_biUnion]
    refine ⟨(a, b), by simp [hP, hab], mem_image.2 ⟨c, by simp [hNB, hac, hbc], rfl⟩⟩
  have hfib : ∀ p ∈ P, #((NB p.1 p.2).image fun c => ({p.1, p.2, c} : Finset (Fin n))) ≤ m := by
    intro p hp
    have hadj : G.Adj p.1 p.2 := (mem_filter.1 hp).2
    exact (card_image_le).trans (hsmall _ _ hadj).le
  have hPcard : #P ≤ n ^ 2 := by
    calc #P ≤ #(univ : Finset (Fin n × Fin n)) := card_le_card (filter_subset _ _)
      _ = n ^ 2 := by simp [sq]
  calc #(G.cliqueFinset 3) ≤ #(P.biUnion fun p => (NB p.1 p.2).image
          fun c => ({p.1, p.2, c} : Finset (Fin n))) := card_le_card hsub
    _ ≤ ∑ p ∈ P, #((NB p.1 p.2).image fun c => ({p.1, p.2, c} : Finset (Fin n))) :=
        card_biUnion_le
    _ ≤ ∑ _p ∈ P, m := sum_le_sum hfib
    _ = #P * m := by rw [sum_const, smul_eq_mul]
    _ ≤ n ^ 2 * m := Nat.mul_le_mul_right m hPcard

/-- Charging bound: if `G' ≤ G` is triangle-free, every edge of `G` lies in a
    triangle, and every edge of `G` lies in fewer than `m` triangles, then
    `|E(G)| ≤ (|E(G)| - |E(G')|) · (2m + 1)`. Each edge of `G` shares a triangle
    with a deleted edge, and each deleted edge is charged at most `2m + 1` times. -/
private lemma card_edgeFinset_le_deleted {n : ℕ} (G G' : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel G'.Adj] (hle : G' ≤ G) (hfree : G'.CliqueFree 3)
    (ht : ErdosCandidates.Books.EveryEdgeInTriangle G) (m : ℕ)
    (hsmall : ∀ u v, G.Adj u v → ErdosCandidates.Books.bookSize G u v < m) :
    (#G.edgeFinset : ℝ) ≤ ((#G.edgeFinset : ℝ) - #G'.edgeFinset) * (2 * m + 1) := by
  set P := univ.filter fun p : Fin n × Fin n => G.Adj p.1 p.2 with hP
  set S := P.filter fun p => ¬ G'.Adj p.1 p.2 with hS
  set NB : Fin n → Fin n → Finset (Fin n) :=
    fun a b => univ.filter fun w => G.Adj a w ∧ G.Adj b w with hNB
  set F : Fin n × Fin n → Finset (Fin n × Fin n) := fun p =>
    insert p ((NB p.1 p.2).image (fun x => (p.1, x)) ∪ (NB p.1 p.2).image (fun x => (x, p.1)))
    with hF
  have hPcard : #P = 2 * #G.edgeFinset := card_adjPairs G
  have hP'card : #(P.filter fun p => G'.Adj p.1 p.2) = 2 * #G'.edgeFinset := by
    rw [← card_adjPairs G', hP, filter_filter]
    congr 1
    refine filter_congr fun p _ => ?_
    exact ⟨fun h => h.2, fun h => ⟨hle h, h⟩⟩
  have hSP : #S + 2 * #G'.edgeFinset = 2 * #G.edgeFinset := by
    rw [← hP'card, ← hPcard, hS, add_comm]
    exact card_filter_add_card_filter_not _
  have hsub : P ⊆ S.biUnion F := by
    intro p hp
    obtain ⟨u, v⟩ := p
    have huv : G.Adj u v := (mem_filter.1 hp).2
    obtain ⟨w, hw⟩ := card_pos.1 (ht u v huv)
    obtain ⟨huw, hvw⟩ := (mem_filter.1 hw).2
    have hnot : ¬ (G'.Adj u v ∧ G'.Adj u w ∧ G'.Adj v w) := fun h =>
      hfree {u, v, w} (is3Clique_triple_iff.2 h)
    rw [mem_biUnion]
    by_cases h1 : G'.Adj u v
    · by_cases h2 : G'.Adj u w
      · have h3 : ¬ G'.Adj v w := fun h3 => hnot ⟨h1, h2, h3⟩
        refine ⟨(v, w), by simp [hS, hP, hvw, h3], ?_⟩
        simp [hF, hNB, huv.symm, huw.symm]
      · refine ⟨(u, w), by simp [hS, hP, huw, h2], ?_⟩
        simp [hF, hNB, huv, hvw.symm]
    · exact ⟨(u, v), by simp [hS, hP, huv, h1], by simp [hF]⟩
  have hFcard : ∀ p ∈ S, #(F p) ≤ 2 * m + 1 := by
    intro p hp
    have hadj : G.Adj p.1 p.2 := (mem_filter.1 (mem_filter.1 hp).1).2
    have hb : #(NB p.1 p.2) < m := hsmall _ _ hadj
    calc #(F p) ≤ #((NB p.1 p.2).image (fun x => (p.1, x)) ∪
            (NB p.1 p.2).image (fun x => (x, p.1))) + 1 := card_insert_le _ _
      _ ≤ #((NB p.1 p.2).image (fun x => (p.1, x))) +
            #((NB p.1 p.2).image (fun x => (x, p.1))) + 1 :=
          Nat.add_le_add_right (card_union_le _ _) 1
      _ ≤ #(NB p.1 p.2) + #(NB p.1 p.2) + 1 :=
          Nat.add_le_add_right (Nat.add_le_add card_image_le card_image_le) 1
      _ ≤ 2 * m + 1 := by omega
  have hcharge : 2 * #G.edgeFinset ≤ #S * (2 * m + 1) := by
    calc 2 * #G.edgeFinset = #P := hPcard.symm
      _ ≤ #(S.biUnion F) := card_le_card hsub
      _ ≤ ∑ p ∈ S, #(F p) := card_biUnion_le
      _ ≤ ∑ _p ∈ S, (2 * m + 1) := sum_le_sum hFcard
      _ = #S * (2 * m + 1) := by rw [sum_const, smul_eq_mul]
  have hSR : (#S : ℝ) = 2 * ((#G.edgeFinset : ℝ) - #G'.edgeFinset) := by
    have := congrArg (fun k : ℕ => (k : ℝ)) hSP
    push_cast at this
    linarith
  have hchargeR : (2 * #G.edgeFinset : ℝ) ≤ (#S : ℝ) * (2 * m + 1) := by
    exact_mod_cast hcharge
  rw [hSR] at hchargeR
  linarith

/-- **Szemerédi's regularity consequence**, archived: for every fixed
    `c > 0`, `f_c(n) → ∞` — every bound `m` is eventually forced.
    The only known lower bounds at c < 1/4; regularity is in Mathlib
    (`SzemerediRegularity`), making this a heavy-but-conceivable
    target. -/
theorem szemeredi_book_unbounded (c : ℝ) (hc : 0 < c) (m : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
        c * n ^ 2 ≤ (G.edgeFinset.card : ℝ) →
        EveryEdgeInTriangle G →
        ∃ u v : Fin n, G.Adj u v ∧ m ≤ bookSize G u v := by
  set ε : ℝ := c / (2 * m + 1) with hεdef
  have hK : (0 : ℝ) < 2 * m + 1 := by positivity
  have hε : 0 < ε := div_pos hc hK
  have hδ : 0 < triangleRemovalBound ε := triangleRemovalBound_pos hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((m : ℝ) / triangleRemovalBound ε)
  refine ⟨N + 1, fun n hn G _ hE ht => ?_⟩
  by_contra! hsmall
  have hnpos : (0 : ℝ) < n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.le_add_left 1 N).trans hn
    linarith
  have hmn : (m : ℝ) < triangleRemovalBound ε * n := by
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast (Nat.le_succ N).trans hn
    rw [← div_lt_iff₀' hδ]
    linarith
  have htri : (#(G.cliqueFinset 3) : ℝ) < triangleRemovalBound ε * n ^ 3 := by
    have hcount : (#(G.cliqueFinset 3) : ℝ) ≤ (n : ℝ) ^ 2 * m := by
      exact_mod_cast card_cliqueFinset_three_le G m hsmall
    have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    calc (#(G.cliqueFinset 3) : ℝ) ≤ (n : ℝ) ^ 2 * m := hcount
      _ < (n : ℝ) ^ 2 * (triangleRemovalBound ε * n) := mul_lt_mul_of_pos_left hmn hn2
      _ = triangleRemovalBound ε * n ^ 3 := by ring
  obtain ⟨G', hle, _, hdiff, hfree⟩ := triangle_removal (ε := ε) (G := G) (by simpa using htri)
  have hcharge := card_edgeFinset_le_deleted G G' hle hfree ht m hsmall
  have hdiff' : (#G.edgeFinset : ℝ) - #G'.edgeFinset < ε * n ^ 2 := by simpa using hdiff
  have hprod : ((#G.edgeFinset : ℝ) - #G'.edgeFinset) * (2 * m + 1) < c * n ^ 2 := by
    calc ((#G.edgeFinset : ℝ) - #G'.edgeFinset) * (2 * m + 1)
        < ε * n ^ 2 * (2 * m + 1) := mul_lt_mul_of_pos_right hdiff' hK
      _ = c * n ^ 2 := by rw [hεdef]; field_simp
  linarith

/-- `K₄` satisfies the density and triangle hypotheses jointly. -/
theorem k4_dense_everyEdgeInTriangle :
    (4 : ℕ) ^ 2 < 4 * (⊤ : SimpleGraph (Fin 4)).edgeFinset.card ∧
      EveryEdgeInTriangle (⊤ : SimpleGraph (Fin 4)) := by
  unfold EveryEdgeInTriangle
  decide

/-- Sanity: the hypothesis pair is jointly satisfiable at a nontrivial
    model — `K₄` has 6 > 4²/4 = 4 edges, every edge in a triangle.
    -- PROVABLE (decide). -/
example : (4 : ℕ) ^ 2 < 4 * (⊤ : SimpleGraph (Fin 4)).edgeFinset.card ∧
    EveryEdgeInTriangle (⊤ : SimpleGraph (Fin 4)) := by
  exact k4_dense_everyEdgeInTriangle

end ErdosCandidates.E80

/- Formalization scope: only the classical dense-graph slice is discharged.
   The definitions above are transparent aliases of the production counts.
   The adopted K₄ checks are unchanged. Fox–Loh and Szemerédi remain
   OPEN formalization obligations, with their original sorry contracts.
   The weaker +5 conclusion is intentional; it is not the exact classical
   constant and this file makes no historical source-review PASS claim.
-/

