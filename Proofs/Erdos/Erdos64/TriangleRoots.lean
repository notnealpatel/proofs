/-
Erdős–Gyárfás problem 64 — the intrinsic triangle-root orbit extension.

PROVENANCE.  arXiv:2608.02675, Julius Tranquilli, "A 60-Vertex Lower Bound for Cubic Bipartite
Counterexamples to the Erdős–Gyárfás Conjecture" (2 August 2026), Section 3.1, Lemma
`lem:triangle-orbits` — the triangle-rooted orbit analysis that precedes the restricted-growth
search of Section 3.2.  Graphs here are finite, undirected and simple.

SOURCE CLAIM BOUNDARY.  The source roots a linear `3`-uniform `3`-regular incidence configuration
at a Berge triangle and inspects the local incidence around one of its root points.  Its
`lem:triangle-orbits` records that, up to the stabiliser of the rooted triangle, only two labelled
root patterns occur, written informally as `{0,4,6}` and `{0,6,7}`.  That statement is *labelled*
and is phrased "up to stabiliser"; the stabiliser action, the global relabelling of the point set
and the resulting orbit classification are **not** part of what is formalised here.  What is
formalised is the intrinsic, label-free local combinatorics that the orbit analysis consumes.

WHAT IS FORMALIZED HERE.  The witness structure `TriangleRootExtension C T i` and the existence
theorem `exists_triangleRootExtension`, both stated about an arbitrary `IncidenceConfig` with no
finiteness assumption on the point type.  For a linear `3`-uniform `3`-regular configuration `C`, a
Berge triangle `T` and a chosen root index `i : Fin 3`, the structure packages:

* `aux` — the unique third point of each triangle block, with the exact block equation
  `C.blocks (T.block j) = {T.point j, T.point (cyc3 (cyc3 j)), aux j}` for every `j`;
* six-way distinctness of the six root points: `T.point` is injective (already a field of
  `BergeTriangle`), `aux` is injective, and `aux j ≠ T.point k` for all `j k`;
* `thirdBlock` — the unique indexed block through `T.point i` other than the two known triangle
  blocks, with the exact equation
  `C.incidentBlocks (T.point i) = {T.block i, T.block (cyc3 i), thirdBlock}` together with
  uniqueness among the incident blocks outside those two.  Block *indices* are never identified
  with one another, so two equal-neighbourhood block indices remain two distinct witnesses;
* `q q'` — the two remaining points of `thirdBlock`, with `C.blocks thirdBlock = {T.point i, q, q'}`
  and pairwise distinctness of the three;
* the four linearity exclusions: `thirdBlock` contains none of `T.point (cyc3 i)`,
  `T.point (cyc3 (cyc3 i))`, `aux i`, `aux (cyc3 i)` — exactly the four root points already paired
  with `T.point i` through its two triangle blocks;
* the intrinsic dichotomy for the only remaining root point, `aux (cyc3 (cyc3 i))`: it is `q`, it
  is `q'`, or it is neither.  The split itself is a classical propositional tautology; its content
  is the proved exclusions and distinctness around it.  Equivalently — and this is stated as the
  public theorem `TriangleRootExtension.mem_thirdBlock_iff` — the first two branches say that the
  third block through the root point also contains the auxiliary point of the opposite triangle
  block.  Under the source's local first-occurrence naming, the disjunctive reuse case
  `aux (cyc3 (cyc3 i)) = q ∨ aux (cyc3 (cyc3 i)) = q'` — the third block through the root point
  reuses the auxiliary point of the opposite triangle block together with one fresh point — is the
  labelled root pattern written `{0,4,6}`, while the case in which the point is neither,
  `aux (cyc3 (cyc3 i)) ≠ q ∧ aux (cyc3 (cyc3 i)) ≠ q'` — two fresh points — is the pattern written
  `{0,6,7}`.  The individual disjuncts `aux (cyc3 (cyc3 i)) = q` and `aux (cyc3 (cyc3 i)) = q'`
  are **not** separately matched to the two labelled patterns: the extraction orders `q` and `q'`
  arbitrarily, so only the disjunction and its negation carry source meaning.  That correspondence
  is documentation of the intended reading of the source, not a formal statement: the
  identification of the two disjunctive cases with the labelled patterns relies on the paper's
  naming convention and is not proved here.

NOT FORMALIZED HERE.  Root naming, the global relabelling `P ≃ Fin n`, the stabiliser action and
its orbit classification, the restricted-growth coverage of Section 3.2, the static witness
certificates, any enumeration or emptiness check of the search, the `60`-vertex lower bound
(`thm:main`, `cor:bound`) and the Erdős–Gyárfás conjecture are all **not** formalised here.  This
module proves only the local intrinsic combinatorics listed above; in particular it makes no claim
about which of the two branches of the dichotomy can occur.
-/

import Erdos.Erdos64.CertificateReduction
import Mathlib.Tactic

set_option autoImplicit false

namespace Erdos64

universe u

variable {P B : Type u}

/-! ### Cyclic identities on `Fin 3` -/

/-- Three applications of the cyclic successor `cyc3` return to the starting index. -/
theorem cyc3_cyc3_cyc3 (j : Fin 3) : cyc3 (cyc3 (cyc3 j)) = j := by
  fin_cases j <;> decide

/-- The cyclic successor moves every index of `Fin 3`. -/
theorem cyc3_ne_self (j : Fin 3) : j ≠ cyc3 j := by
  fin_cases j <;> decide

/-- Two applications of the cyclic successor move every index of `Fin 3`. -/
theorem cyc3_cyc3_ne_self (j : Fin 3) : j ≠ cyc3 (cyc3 j) := by
  fin_cases j <;> decide

/-- Every index of `Fin 3` is the starting index, its successor, or the successor of its
successor. -/
theorem eq_self_or_eq_cyc3_or_eq_cyc3_cyc3 (j k : Fin 3) :
    k = j ∨ k = cyc3 j ∨ k = cyc3 (cyc3 j) := by
  fin_cases j <;> fin_cases k <;> decide

/-- A *different* index of `Fin 3` is the successor of the starting index or the successor of that
successor.  This is the case split behind the linearity arguments: two distinct triangle blocks
share exactly one triangle point. -/
theorem eq_cyc3_or_eq_cyc3_cyc3_of_ne (j k : Fin 3) (h : j ≠ k) :
    k = cyc3 j ∨ k = cyc3 (cyc3 j) := by
  rcases eq_self_or_eq_cyc3_or_eq_cyc3_cyc3 j k with h' | h' | h'
  · exact (h h'.symm).elim
  · exact Or.inl h'
  · exact Or.inr h'

/-! ### Reordering and extraction lemmas for three-element finsets -/

section FinsetHelpers

variable [DecidableEq P]

/-- A three-element literal may be written with its last element first. -/
theorem insert_pair_eq_three {a b c : P} :
    (insert c {a, b} : Finset P) = {a, b, c} := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- A finset of cardinality three that contains two distinct points `a`, `b` has a third point `c`,
with `c` distinct from both and with the exact presentation `s = {a, b, c}`.  This is the
extraction used for the auxiliary points of the triangle blocks and for the third incident block
through a root point. -/
theorem exists_eq_three_of_card_eq_three {s : Finset P} {a b : P} (hab : a ≠ b) (ha : a ∈ s)
    (hb : b ∈ s) (hcard : s.card = 3) :
    ∃ c : P, c ≠ a ∧ c ≠ b ∧ s = {a, b, c} := by
  have hsub : ({a, b} : Finset P) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have hcard_pair : ({a, b} : Finset P).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hab), Finset.card_singleton]
  have hne : ({a, b} : Finset P) ≠ s := by
    intro heq
    rw [← heq, hcard_pair] at hcard
    omega
  obtain ⟨c, hcs, hcnot⟩ :=
    Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  have hca : c ≠ a := by
    intro h
    exact hcnot (by simp [h])
  have hcb : c ≠ b := by
    intro h
    exact hcnot (by simp [h])
  have hins : insert c ({a, b} : Finset P) ⊆ s := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hcs
    · exact hsub hx
  have hcard_ins : (insert c ({a, b} : Finset P)).card = 3 := by
    rw [Finset.card_insert_of_notMem hcnot, hcard_pair]
  have heq : insert c ({a, b} : Finset P) = s :=
    Finset.eq_of_subset_of_card_le hins (by rw [hcard_ins, hcard])
  exact ⟨c, hca, hcb, by rw [← heq, insert_pair_eq_three]⟩

/-- A finset of cardinality three containing a point `a` has two further points `b`, `c`, both
distinct from `a` and from each other, with the exact presentation `s = {a, b, c}`.  This is the
extraction used for the two new points of the third incident block through a root point. -/
theorem exists_pair_of_mem_card_eq_three {s : Finset P} {a : P} (ha : a ∈ s)
    (hcard : s.card = 3) :
    ∃ b c : P, b ≠ a ∧ c ≠ a ∧ b ≠ c ∧ s = {a, b, c} := by
  have hcard_erase : (s.erase a).card = 2 := by
    rw [Finset.card_erase_of_mem ha, hcard]
  obtain ⟨b, c, hbc, heq⟩ := Finset.card_eq_two.mp hcard_erase
  have hb : b ∈ s.erase a := by rw [heq]; simp
  have hc : c ∈ s.erase a := by rw [heq]; simp
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  have hca : c ≠ a := (Finset.mem_erase.mp hc).1
  exact ⟨b, c, hba, hca, hbc, by rw [← Finset.insert_erase ha, heq]⟩

end FinsetHelpers

/-! ### Membership in the incident-block finset -/

/-- A block index lies in the incident-block finset of a point exactly when the point lies in that
block.  This is the unfolding of `IncidenceConfig.incidentBlocks` used throughout. -/
theorem mem_incidentBlocks {C : IncidenceConfig P B} [Fintype B] [DecidableEq P] {p : P} {b : B} :
    b ∈ C.incidentBlocks p ↔ p ∈ C.blocks b := by
  rw [IncidenceConfig.incidentBlocks, Finset.mem_filter]
  simp

/-! ### Triangle-block incidence and injectivity helpers -/

/-- The triangle blocks of a Berge triangle are distinct at distinct indices. -/
theorem BergeTriangle.block_ne {C : IncidenceConfig P B} (T : BergeTriangle C) {j k : Fin 3}
    (h : j ≠ k) : T.block j ≠ T.block k :=
  fun hh => h (T.block_injective hh)

/-- The triangle points of a Berge triangle are distinct at distinct indices. -/
theorem BergeTriangle.point_ne {C : IncidenceConfig P B} (T : BergeTriangle C) {j k : Fin 3}
    (h : j ≠ k) : T.point j ≠ T.point k :=
  fun hh => h (T.point_injective hh)

/-! ### The triangle-root extension -/

/-- **The intrinsic triangle-root extension.**  For an incidence configuration `C`, a Berge triangle
`T` of `C` and a chosen root index `i`, this witness packages the label-free local combinatorics of
the source's `lem:triangle-orbits` (arXiv:2608.02675, Section 3.1): the auxiliary point of every
triangle block, six-way distinctness of the root points, the unique third indexed block through the
root point `T.point i`, its two remaining points, the four linearity exclusions that pair the root
point with its two triangle blocks, and the intrinsic two-case split for the last remaining root
point.

The source's statement is *labelled* and phrased "up to stabiliser"; nothing here identifies block
indices with equal blocks, and no global relabelling or stabiliser classification is asserted.  The
dichotomy field is a classical case split; its mathematical content lies in the exact block
equations, the six-way distinctness and the four exclusions. -/
structure TriangleRootExtension (C : IncidenceConfig P B) [Fintype B] [DecidableEq P]
    [DecidableEq B] (T : BergeTriangle C) (i : Fin 3) where
  /-- The auxiliary (third) point of each triangle block. -/
  aux : Fin 3 → P
  /-- Exact block equation: the triangle block at `j` is the two triangle points at `j` and at the
  preceding index together with the auxiliary point at `j`. -/
  block_eq : ∀ j : Fin 3, C.blocks (T.block j) = {T.point j, T.point (cyc3 (cyc3 j)), aux j}
  /-- The auxiliary points are pairwise distinct. -/
  aux_injective : Function.Injective aux
  /-- No auxiliary point is a triangle point. -/
  aux_ne_point : ∀ j k : Fin 3, aux j ≠ T.point k
  /-- The unique third indexed block through the root point `T.point i`. -/
  thirdBlock : B
  /-- The root point lies in the third block. -/
  thirdBlock_mem : T.point i ∈ C.blocks thirdBlock
  /-- The third block is not the first known triangle block. -/
  thirdBlock_ne_block_i : thirdBlock ≠ T.block i
  /-- The third block is not the second known triangle block. -/
  thirdBlock_ne_block_cyc : thirdBlock ≠ T.block (cyc3 i)
  /-- Exact incident-block equation: the blocks through the root point are precisely the two known
  triangle blocks and the third block.  Block indices are not identified. -/
  incidentBlocks_eq : C.incidentBlocks (T.point i) = {T.block i, T.block (cyc3 i), thirdBlock}
  /-- Uniqueness: any incident block through the root point other than the two known triangle
  blocks is the third block. -/
  thirdBlock_unique : ∀ b : B, T.point i ∈ C.blocks b → b ≠ T.block i → b ≠ T.block (cyc3 i) →
    b = thirdBlock
  /-- The first of the two remaining points of the third block. -/
  q : P
  /-- The second of the two remaining points of the third block. -/
  q' : P
  /-- The first remaining point is not the root point. -/
  q_ne_point_i : q ≠ T.point i
  /-- The second remaining point is not the root point. -/
  q'_ne_point_i : q' ≠ T.point i
  /-- The two remaining points are distinct. -/
  q_ne_q' : q ≠ q'
  /-- Exact block equation for the third block: it is the root point together with `q` and `q'`. -/
  thirdBlock_eq : C.blocks thirdBlock = {T.point i, q, q'}
  /-- Linearity exclusion: the third block does not contain the other triangle point of the second
  known triangle block. -/
  not_mem_point_cyc : T.point (cyc3 i) ∉ C.blocks thirdBlock
  /-- Linearity exclusion: the third block does not contain the other triangle point of the first
  known triangle block. -/
  not_mem_point_cyc_cyc : T.point (cyc3 (cyc3 i)) ∉ C.blocks thirdBlock
  /-- Linearity exclusion: the third block does not contain the auxiliary point of the first known
  triangle block. -/
  not_mem_aux_i : aux i ∉ C.blocks thirdBlock
  /-- Linearity exclusion: the third block does not contain the auxiliary point of the second known
  triangle block. -/
  not_mem_aux_cyc : aux (cyc3 i) ∉ C.blocks thirdBlock
  /-- The intrinsic two-case split for the only remaining root point `aux (cyc3 (cyc3 i))`: it is
  one of the two remaining points of the third block, or it is neither. -/
  dichotomy : (aux (cyc3 (cyc3 i)) = q ∨ aux (cyc3 (cyc3 i)) = q') ∨
    (aux (cyc3 (cyc3 i)) ≠ q ∧ aux (cyc3 (cyc3 i)) ≠ q')

/-- The dichotomy of a triangle-root extension is exactly the question whether the third block
through the root point contains the auxiliary point of the opposite triangle block.  The
equivalence uses the exact block equation for the third block and the distinctness of that
auxiliary point from the root point; it is the intrinsic content that the source's labelled forms
`{0,4,6}` (the reuse case, in which the third block takes up the opposite block's auxiliary point
together with one fresh point) and `{0,6,7}` (the two-fresh-point case) record. -/
theorem TriangleRootExtension.mem_thirdBlock_iff {C : IncidenceConfig P B} [Fintype B]
    [DecidableEq P] [DecidableEq B] {T : BergeTriangle C} {i : Fin 3}
    (E : TriangleRootExtension C T i) :
    E.aux (cyc3 (cyc3 i)) ∈ C.blocks E.thirdBlock ↔
      (E.aux (cyc3 (cyc3 i)) = E.q ∨ E.aux (cyc3 (cyc3 i)) = E.q') := by
  rw [E.thirdBlock_eq]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h)
    · exact absurd h (E.aux_ne_point (cyc3 (cyc3 i)) i)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

/-- **Existence of the triangle-root extension.**  Every Berge triangle of a linear `3`-uniform
`3`-regular incidence configuration admits a triangle-root extension at every root index.

The auxiliary points come from `3`-uniformity of the two triangle blocks through each root point;
their six-way distinctness, and the four linearity exclusions around the root point, come from
linearity applied to pairs of distinct triangle blocks; the third incident block comes from
`3`-regularity of the root point; its two remaining points come from `3`-uniformity of the third
block.  Only the point type's decidability and the block index type's finiteness and decidability
are needed. -/
theorem exists_triangleRootExtension {C : IncidenceConfig P B} [Fintype B] [DecidableEq P]
    [DecidableEq B] (hU : C.IsThreeUniform) (hR : C.IsThreeRegular) (hLin : C.IsLinear)
    (T : BergeTriangle C) (i : Fin 3) : Nonempty (TriangleRootExtension C T i) := by
  classical
  -- Auxiliary points of the three triangle blocks.
  have haux_exists : ∀ j : Fin 3, ∃ u : P, u ≠ T.point j ∧ u ≠ T.point (cyc3 (cyc3 j)) ∧
      C.blocks (T.block j) = {T.point j, T.point (cyc3 (cyc3 j)), u} := by
    intro j
    have h1 : T.point j ∈ C.blocks (T.block j) := (T.incident j).1
    have h2 : T.point (cyc3 (cyc3 j)) ∈ C.blocks (T.block j) := by
      have h := (T.incident (cyc3 (cyc3 j))).2
      simpa [cyc3_cyc3_cyc3] using h
    have hne : T.point j ≠ T.point (cyc3 (cyc3 j)) := T.point_ne (cyc3_cyc3_ne_self j)
    exact exists_eq_three_of_card_eq_three hne h1 h2 (hU (T.block j))
  choose aux haux_ne_self haux_ne_cyc haux_eq using haux_exists
  -- Six-way distinctness.
  have haux_ne_point : ∀ j k : Fin 3, aux j ≠ T.point k := by
    intro j k
    rcases eq_self_or_eq_cyc3_or_eq_cyc3_cyc3 j k with hk | hk | hk
    · rw [hk]; exact haux_ne_self j
    · rw [hk]
      intro h
      have h1 : T.point j ∈ C.blocks (T.block j) := (T.incident j).1
      have h2 : T.point j ∈ C.blocks (T.block (cyc3 j)) := (T.incident j).2
      have h3 : aux j ∈ C.blocks (T.block j) := by rw [haux_eq j]; simp
      have h4 : aux j ∈ C.blocks (T.block (cyc3 j)) := by
        rw [h]; exact (T.incident (cyc3 j)).1
      have heq : T.point j = aux j :=
        hLin (b₁ := T.block j) (b₂ := T.block (cyc3 j)) (T.block_ne (cyc3_ne_self j))
          h1 h2 h3 h4
      exact haux_ne_self j heq.symm
    · rw [hk]; exact haux_ne_cyc j
  have haux_injective : Function.Injective aux := by
    intro j k hjk
    by_contra hne
    rcases eq_cyc3_or_eq_cyc3_cyc3_of_ne j k hne with hk | hk
    · have h1 : T.point j ∈ C.blocks (T.block j) := (T.incident j).1
      have h2 : T.point j ∈ C.blocks (T.block (cyc3 j)) := (T.incident j).2
      have h3 : aux j ∈ C.blocks (T.block j) := by rw [haux_eq j]; simp
      have h4 : aux j ∈ C.blocks (T.block (cyc3 j)) := by
        rw [← hk, haux_eq k]; simp [hjk]
      have heq : T.point j = aux j :=
        hLin (b₁ := T.block j) (b₂ := T.block (cyc3 j)) (T.block_ne (cyc3_ne_self j))
          h1 h2 h3 h4
      exact haux_ne_self j heq.symm
    · have h1 : T.point (cyc3 (cyc3 j)) ∈ C.blocks (T.block j) := by rw [haux_eq j]; simp
      have h2 : T.point (cyc3 (cyc3 j)) ∈ C.blocks (T.block (cyc3 (cyc3 j))) :=
        (T.incident (cyc3 (cyc3 j))).1
      have h3 : aux j ∈ C.blocks (T.block j) := by rw [haux_eq j]; simp
      have h4 : aux j ∈ C.blocks (T.block (cyc3 (cyc3 j))) := by
        rw [← hk, haux_eq k]; simp [hjk]
      have heq : T.point (cyc3 (cyc3 j)) = aux j :=
        hLin (b₁ := T.block j) (b₂ := T.block (cyc3 (cyc3 j)))
          (T.block_ne (cyc3_cyc3_ne_self j)) h1 h2 h3 h4
      exact haux_ne_point j (cyc3 (cyc3 j)) heq.symm
  -- The third indexed block through the root point.
  obtain ⟨thirdBlock, htb_ne_i, htb_ne_cyc, htb_inc⟩ :=
    exists_eq_three_of_card_eq_three (T.block_ne (cyc3_ne_self i))
      (by rw [mem_incidentBlocks]; exact (T.incident i).1)
      (by rw [mem_incidentBlocks]; exact (T.incident i).2)
      (hR (T.point i))
  have htb_mem : T.point i ∈ C.blocks thirdBlock := by
    have h : thirdBlock ∈ C.incidentBlocks (T.point i) := by rw [htb_inc]; simp
    rwa [mem_incidentBlocks] at h
  have htb_unique : ∀ b : B, T.point i ∈ C.blocks b → b ≠ T.block i →
      b ≠ T.block (cyc3 i) → b = thirdBlock := by
    intro b hb hbi hbcyc
    have h : b ∈ C.incidentBlocks (T.point i) := by rwa [mem_incidentBlocks]
    rw [htb_inc] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · exact absurd h hbi
    · exact absurd h hbcyc
    · exact h
  -- The two remaining points of the third block.
  obtain ⟨q, q', hq_ne_i, hq'_ne_i, hq_ne_q', htb_eq⟩ :=
    exists_pair_of_mem_card_eq_three htb_mem (hU thirdBlock)
  -- The four linearity exclusions.
  have hnot_cyc : T.point (cyc3 i) ∉ C.blocks thirdBlock := by
    intro hmem
    have heq : T.point i = T.point (cyc3 i) :=
      hLin (b₁ := thirdBlock) (b₂ := T.block (cyc3 i)) htb_ne_cyc htb_mem (T.incident i).2
        hmem (T.incident (cyc3 i)).1
    exact cyc3_ne_self i (T.point_injective heq)
  have hnot_cyccyc : T.point (cyc3 (cyc3 i)) ∉ C.blocks thirdBlock := by
    intro hmem
    have hmem_i : T.point (cyc3 (cyc3 i)) ∈ C.blocks (T.block i) := by rw [haux_eq i]; simp
    have heq : T.point i = T.point (cyc3 (cyc3 i)) :=
      hLin (b₁ := thirdBlock) (b₂ := T.block i) htb_ne_i htb_mem (T.incident i).1 hmem hmem_i
    exact cyc3_cyc3_ne_self i (T.point_injective heq)
  have hnot_aux : aux i ∉ C.blocks thirdBlock := by
    intro hmem
    have hmem_i : aux i ∈ C.blocks (T.block i) := by rw [haux_eq i]; simp
    have heq : T.point i = aux i :=
      hLin (b₁ := thirdBlock) (b₂ := T.block i) htb_ne_i htb_mem (T.incident i).1 hmem hmem_i
    exact haux_ne_self i heq.symm
  have hnot_aux_cyc : aux (cyc3 i) ∉ C.blocks thirdBlock := by
    intro hmem
    have hmem_i : aux (cyc3 i) ∈ C.blocks (T.block (cyc3 i)) := by rw [haux_eq (cyc3 i)]; simp
    have heq : T.point i = aux (cyc3 i) :=
      hLin (b₁ := thirdBlock) (b₂ := T.block (cyc3 i)) htb_ne_cyc htb_mem (T.incident i).2 hmem
        hmem_i
    exact haux_ne_point (cyc3 i) i heq.symm
  have hdich : (aux (cyc3 (cyc3 i)) = q ∨ aux (cyc3 (cyc3 i)) = q') ∨
      (aux (cyc3 (cyc3 i)) ≠ q ∧ aux (cyc3 (cyc3 i)) ≠ q') := by
    by_cases h : aux (cyc3 (cyc3 i)) = q
    · exact Or.inl (Or.inl h)
    · by_cases h' : aux (cyc3 (cyc3 i)) = q'
      · exact Or.inl (Or.inr h')
      · exact Or.inr ⟨h, h'⟩
  exact ⟨{
    aux := aux
    block_eq := haux_eq
    aux_injective := haux_injective
    aux_ne_point := haux_ne_point
    thirdBlock := thirdBlock
    thirdBlock_mem := htb_mem
    thirdBlock_ne_block_i := htb_ne_i
    thirdBlock_ne_block_cyc := htb_ne_cyc
    incidentBlocks_eq := htb_inc
    thirdBlock_unique := htb_unique
    q := q
    q' := q'
    q_ne_point_i := hq_ne_i
    q'_ne_point_i := hq'_ne_i
    q_ne_q' := hq_ne_q'
    thirdBlock_eq := htb_eq
    not_mem_point_cyc := hnot_cyc
    not_mem_point_cyc_cyc := hnot_cyccyc
    not_mem_aux_i := hnot_aux
    not_mem_aux_cyc := hnot_aux_cyc
    dichotomy := hdich }⟩

/-! ### A concrete model: the Fano configuration -/

/-- The Fano plane read as an incidence configuration on seven points and seven blocks, with block
`b` the translate `{b, b + 1, b + 3}` of the difference set `{0, 1, 3}`.  It is the reference model
used below to witness that the hypotheses of `exists_triangleRootExtension` are jointly
satisfiable; it is not used by any theorem of this module. -/
def fanoConfig : IncidenceConfig (Fin 7) (Fin 7) where
  blocks b := {b, b + 1, b + 3}

/-- A Berge triangle of `fanoConfig`: the three blocks `{0,1,3}`, `{1,2,4}`, `{2,3,5}` with the
three intersection points `1`, `2`, `3`. -/
def fanoTriangle : BergeTriangle fanoConfig where
  point := ![1, 2, 3]
  block := ![0, 1, 2]
  point_injective := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all
  block_injective := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all
  incident := by intro i; fin_cases i <;> decide

/-- The Fano configuration is `3`-uniform, `3`-regular and linear, so it carries a triangle-root
extension: the hypotheses of `exists_triangleRootExtension` are jointly satisfiable. -/
example : Nonempty (TriangleRootExtension fanoConfig fanoTriangle 0) := by
  have hU : fanoConfig.IsThreeUniform := by
    intro b
    fin_cases b <;> decide
  have hR : fanoConfig.IsThreeRegular := by
    intro p
    fin_cases p <;> decide
  have hLin : fanoConfig.IsLinear := by
    intro b₁ b₂ hb p q hp₁ hp₂ hq₁ hq₂
    fin_cases b₁ <;> fin_cases b₂ <;> simp_all only [fanoConfig, Finset.mem_insert, Finset.mem_singleton] <;> (rcases hp₁ with rfl | rfl | rfl) <;> (rcases hq₁ with rfl | rfl | rfl) <;> simp_all
  exact exists_triangleRootExtension hU hR hLin fanoTriangle 0

/-! ### The adapter for the triangle-rooted search input -/

section SearchInput

variable {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- **Root extension for a triangle-rooted search input.**  Any `TriangleSearchInput` carries a
Berge triangle of its extracted configuration together with a triangle-root extension of that
triangle at any chosen root index.  The structural hypotheses are the ones already retained by
`model`; the choice of triangle is existential, so no representative is singled out. -/
theorem TriangleSearchInput.exists_triangleRootExtension (S : TriangleSearchInput G) (i : Fin 3) :
    ∃ T : BergeTriangle S.model.config, Nonempty (TriangleRootExtension S.model.config T i) := by
  obtain ⟨T⟩ := S.model.triangle
  exact ⟨T, Erdos64.exists_triangleRootExtension S.model.threeUniform S.model.threeRegular
    S.model.linear T i⟩

end SearchInput

end Erdos64