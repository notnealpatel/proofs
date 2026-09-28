/-
Erdős–Gyárfás problem 64 — the converse `C₆` translation for incidence configurations.

PROVENANCE.  arXiv:2608.02675, Julius Tranquilli, "A 60-Vertex Lower Bound for Cubic
Bipartite Counterexamples to the Erdős–Gyárfás Conjecture" (2 August 2026), Section 2
("Incidence configurations and cycle translations"), the `C₆` / Berge-cycle translation.

SOURCE CLAIM BOUNDARY.  Section 2 records that a Berge cycle of length `k ≥ 3` — a cyclic
sequence of distinct blocks `B₀, …, B_{k-1}` and distinct points `p₀, …, p_{k-1}` with
`pᵢ ∈ Bᵢ ∩ B_{i+1}` (indices modulo `k`) — is equivalently a simple `C_{2k}` in the Levi
graph; in particular a simple Levi `C₆` is a Berge triangle.
`Erdos.Erdos64.Incidence` formalized the configuration→Levi construction and the forward
translation "Berge triangle → simple Levi `C₆`", but left the converse open.

WHAT IS FORMALIZED HERE.  Exactly the missing local translation of that section: every simple
`6`-cycle of the Levi graph of an incidence configuration determines a Berge triangle, so
that

  `HasSimpleCycleOfLength C.leviGraph 6 ↔ Nonempty (BergeTriangle C)`

for every incidence configuration `C`.  The extraction reads off the three points and the
three block indices carried by the cycle's vertices, uses the Levi adjacency lemmas to force
the alternation between the two sides, and uses `SimpleGraph.Walk.IsCycle.getVert_injOn'` to
prove the cyclically indexed vertices distinct (so the three points, and separately the three
block indices, are pairwise distinct).  Both possible starting sides — a point vertex
`Sum.inl p` and a block-index vertex `Sum.inr b` — are handled, the second by the cyclic
reindexing of the same incidence pattern.  Together with the forward direction already in
`Erdos.Erdos64.Incidence`, this completes the `C₆ ↔ Berge triangle` translation of §2.

NOT FORMALIZED HERE.  Nothing beyond that local translation.  This module does not formalize
the graph→configuration reading of the graph/configuration correspondence; it assumes no
`3`-uniformity, `3`-regularity or linearity hypothesis; and the source's exhaustive
restricted-growth search, static witness certificates, triangle-rooted orbit analysis and the
`60`-vertex lower bound (`thm:main`, `cor:bound`) are **not** claimed or used below.  In
particular there is no enumeration of incidence configurations and no `60`-vertex theorem
here; this file supplies only the local short-cycle translation such a search consumes.
-/

import Erdos.Erdos64.Incidence

set_option autoImplicit false

namespace Erdos64

open SimpleGraph

universe u

variable {P B : Type u}

section Incidence

variable [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]

namespace IncidenceConfig

/-! ### The Berge triangle of six incidence data -/

omit [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B] in
/-- Six incidence data with pairwise distinct points and pairwise distinct block indices give a
Berge triangle: the points `p₀, p₁, p₂` indexed by `Fin 3` and the blocks `b₀, b₁, b₂` indexed
by `Fin 3`, with the consecutive incidences `p₀ ∈ b₀ ∩ b₁`, `p₁ ∈ b₁ ∩ b₂`, `p₂ ∈ b₂ ∩ b₀`.
This is the converse bookkeeping of `hasSimpleCycleOfLength_six_of_berge_data`: it assembles
the `BergeTriangle` structure out of the raw incidence data extracted from a cycle, so that
both possible starting sides of a Levi `C₆` reduce to the same pattern. -/
theorem nonempty_bergeTriangle_of_incidence_six (C : IncidenceConfig P B)
    {p₀ p₁ p₂ : P} {b₀ b₁ b₂ : B}
    (hp₀₁ : p₀ ≠ p₁) (hp₁₂ : p₁ ≠ p₂) (hp₀₂ : p₀ ≠ p₂)
    (hb₀₁ : b₀ ≠ b₁) (hb₁₂ : b₁ ≠ b₂) (hb₀₂ : b₀ ≠ b₂)
    (h₀ : p₀ ∈ C.blocks b₀) (h₁ : p₀ ∈ C.blocks b₁)
    (h₂ : p₁ ∈ C.blocks b₁) (h₃ : p₁ ∈ C.blocks b₂)
    (h₄ : p₂ ∈ C.blocks b₂) (h₅ : p₂ ∈ C.blocks b₀) :
    Nonempty (BergeTriangle C) := by
  have hcyc0 : cyc3 (0 : Fin 3) = 1 := by decide
  have hcyc1 : cyc3 (1 : Fin 3) = 2 := by decide
  have hcyc2 : cyc3 (2 : Fin 3) = 0 := by decide
  refine ⟨⟨![p₀, p₁, p₂], ![b₀, b₁, b₂], ?_, ?_, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i
    · exact ⟨by simpa using h₀, by simpa [hcyc0] using h₁⟩
    · exact ⟨by simpa using h₂, by simpa [hcyc1] using h₃⟩
    · exact ⟨by simpa using h₄, by simpa [hcyc2] using h₅⟩

/-! ### The converse `C₆` translation -/

/-- A simple six-cycle in the Levi graph determines a Berge triangle.  Reading the six vertices
`getVert 0, …, getVert 5` off the cycle, the Levi adjacency lemmas force the sides to alternate,
so the cycle is `p₀ – b₁ – p₂ – b₃ – p₄ – b₅ – p₀` (when it starts at a point) or the cyclic
shift `b₀ – p₁ – b₂ – p₃ – b₄ – p₅ – b₀` (when it starts at a block index).  Simplicity of the
cycle (`Walk.IsCycle.getVert_injOn'`) makes the three points and the three block indices
pairwise distinct, and the six incidences `p₀ ∈ b₅ ∩ b₁`, `p₂ ∈ b₁ ∩ b₃`, `p₄ ∈ b₃ ∩ b₅` (and
their shift) are exactly the consecutive incidences of a Berge triangle. -/
theorem bergeTriangle_of_hasSimpleCycleOfLength_six (C : IncidenceConfig P B)
    (h : HasSimpleCycleOfLength C.leviGraph 6) : Nonempty (BergeTriangle C) := by
  classical
  obtain ⟨v, c, hc, hlen⟩ := h
  have hv0 : c.getVert 0 = v := c.getVert_zero
  have hv6 : c.getVert 6 = v := by
    have h' := c.getVert_length
    rw [hlen] at h'
    exact h'
  have hinj := hc.getVert_injOn'
  have hne : ∀ i j : ℕ, i ≤ 5 → j ≤ 5 → i ≠ j → c.getVert i ≠ c.getVert j := by
    intro i j hi hj hij hh
    exact hij (hinj (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) hh)
  have e01 := c.adj_getVert_succ (i := 0) (by omega)
  have e12 := c.adj_getVert_succ (i := 1) (by omega)
  have e23 := c.adj_getVert_succ (i := 2) (by omega)
  have e34 := c.adj_getVert_succ (i := 3) (by omega)
  have e45 := c.adj_getVert_succ (i := 4) (by omega)
  have e56 := c.adj_getVert_succ (i := 5) (by omega)
  rcases v with p | b₀
  · -- the cycle starts at a point
    rw [hv0] at e01
    obtain ⟨b₁, h1, hp₀b₁⟩ := (leviGraph_adj_inl_iff C p (c.getVert 1)).mp e01
    rw [h1] at e12
    obtain ⟨p₂, h2, hp₂b₁⟩ := (leviGraph_adj_inr_iff C b₁ (c.getVert 2)).mp e12
    rw [h2] at e23
    obtain ⟨b₃, h3, hp₂b₃⟩ := (leviGraph_adj_inl_iff C p₂ (c.getVert 3)).mp e23
    rw [h3] at e34
    obtain ⟨p₄, h4, hp₄b₃⟩ := (leviGraph_adj_inr_iff C b₃ (c.getVert 4)).mp e34
    rw [h4] at e45
    obtain ⟨b₅, h5, hp₄b₅⟩ := (leviGraph_adj_inl_iff C p₄ (c.getVert 5)).mp e45
    rw [h5] at e56
    rw [hv6] at e56
    have hp₀b₅ : p ∈ C.blocks b₅ := e56
    have h02 : c.getVert 0 ≠ c.getVert 2 := hne 0 2 (by omega) (by omega) (by omega)
    have h04 : c.getVert 0 ≠ c.getVert 4 := hne 0 4 (by omega) (by omega) (by omega)
    have h24 : c.getVert 2 ≠ c.getVert 4 := hne 2 4 (by omega) (by omega) (by omega)
    have h13 : c.getVert 1 ≠ c.getVert 3 := hne 1 3 (by omega) (by omega) (by omega)
    have h15 : c.getVert 1 ≠ c.getVert 5 := hne 1 5 (by omega) (by omega) (by omega)
    have h35 : c.getVert 3 ≠ c.getVert 5 := hne 3 5 (by omega) (by omega) (by omega)
    refine nonempty_bergeTriangle_of_incidence_six C
      (fun hh => h02 (by rw [hv0, h2, hh]))
      (fun hh => h24 (by rw [h2, h4, hh]))
      (fun hh => h04 (by rw [hv0, h4, hh]))
      (fun hh => h15 (by rw [h1, h5, hh]))
      (fun hh => h13 (by rw [h1, h3, hh]))
      (fun hh => h35 (by rw [h3, h5, hh]))
      hp₀b₅ hp₀b₁ hp₂b₁ hp₂b₃ hp₄b₃ hp₄b₅
  · -- the cycle starts at a block index
    rw [hv0] at e01
    obtain ⟨p₁, h1, hp₁b₀⟩ := (leviGraph_adj_inr_iff C b₀ (c.getVert 1)).mp e01
    rw [h1] at e12
    obtain ⟨b₂, h2, hp₁b₂⟩ := (leviGraph_adj_inl_iff C p₁ (c.getVert 2)).mp e12
    rw [h2] at e23
    obtain ⟨p₃, h3, hp₃b₂⟩ := (leviGraph_adj_inr_iff C b₂ (c.getVert 3)).mp e23
    rw [h3] at e34
    obtain ⟨b₄, h4, hp₃b₄⟩ := (leviGraph_adj_inl_iff C p₃ (c.getVert 4)).mp e34
    rw [h4] at e45
    obtain ⟨p₅, h5, hp₅b₄⟩ := (leviGraph_adj_inr_iff C b₄ (c.getVert 5)).mp e45
    rw [h5] at e56
    rw [hv6] at e56
    have hp₅b₀ : p₅ ∈ C.blocks b₀ := e56
    have h02 : c.getVert 0 ≠ c.getVert 2 := hne 0 2 (by omega) (by omega) (by omega)
    have h04 : c.getVert 0 ≠ c.getVert 4 := hne 0 4 (by omega) (by omega) (by omega)
    have h24 : c.getVert 2 ≠ c.getVert 4 := hne 2 4 (by omega) (by omega) (by omega)
    have h13 : c.getVert 1 ≠ c.getVert 3 := hne 1 3 (by omega) (by omega) (by omega)
    have h15 : c.getVert 1 ≠ c.getVert 5 := hne 1 5 (by omega) (by omega) (by omega)
    have h35 : c.getVert 3 ≠ c.getVert 5 := hne 3 5 (by omega) (by omega) (by omega)
    refine nonempty_bergeTriangle_of_incidence_six C
      (fun hh => h13 (by rw [h1, h3, hh]))
      (fun hh => h35 (by rw [h3, h5, hh]))
      (fun hh => h15 (by rw [h1, h5, hh]))
      (fun hh => h02 (by rw [hv0, h2, hh]))
      (fun hh => h24 (by rw [h2, h4, hh]))
      (fun hh => h04 (by rw [hv0, h4, hh]))
      hp₁b₀ hp₁b₂ hp₃b₂ hp₃b₄ hp₅b₄ hp₅b₀

/-- The `C₆` translation of §2: for an incidence configuration, the Levi graph contains a simple
`6`-cycle if and only if the configuration admits a Berge triangle.  The forward direction is
`bergeTriangle_of_hasSimpleCycleOfLength_six`; the backward direction is
`BergeTriangle.hasSimpleCycleOfLength_six` from `Erdos.Erdos64.Incidence`. -/
theorem hasSimpleCycleOfLength_six_iff_nonempty_bergeTriangle (C : IncidenceConfig P B) :
    HasSimpleCycleOfLength C.leviGraph 6 ↔ Nonempty (BergeTriangle C) :=
  ⟨C.bergeTriangle_of_hasSimpleCycleOfLength_six,
   fun h => h.elim fun T => BergeTriangle.hasSimpleCycleOfLength_six T⟩

end IncidenceConfig

end Incidence

end Erdos64