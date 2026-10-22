/-
# Lyudogovskiy: triangular threshold and staircase first occurrence in the partition graph

## Source

arXiv:2603.23228, G. Lyudogovskiy, "Simplex Stratification and Phase Boundaries in the
Partition Graph", Section "Thresholds and computational evidence":
Conjecture `conj:triangular-threshold` and Conjecture `conj:first-family`, restated in the
conclusion as Problems `prob:threshold-formula` and `prob:first-occurrence-family`.
The later revision arXiv:2603.29988 (Theorem `thm:firstocc_initial`) settles only
`r = 0, …, 3` by finite check.  Recorded 2026-10-21.

Verbatim (source definitions):

  "We write $G_n$ for the partition graph of $n$: its vertices are the integer partitions of
  $n$, and two vertices are adjacent if one can be obtained from the other by an elementary
  transfer of one unit between two parts, followed by reordering."

  "For a vertex $\lambda\in V(G_n)$, define $\dimloc(\lambda) := \max\{\dim \sigma:\sigma$ is a
  simplex of $K_n$ and $\lambda\in \sigma\}$.  Equivalently, $\dimloc(\lambda)=d$ if and only if
  the largest clique of $G_n$ containing $\lambda$ has cardinality $d+1$."

  "$L_r(n):=\{\lambda\in V(G_n):\dimloc(\lambda)=r\}$", "$\Delta(n):=\max_{\lambda\vdash n}
  \dimloc(\lambda)$", "$\tau(r):=\min\{n:L_r(n)\neq\varnothing\}$".

Verbatim (conjectures):

  Conjecture (conj:triangular-threshold).  "For every $r\ge 0$, $\tau(r)=1+\frac{r(r+1)}{2}$.
  Equivalently, $\Delta(n)=\max\{r:\ 1+\frac{r(r+1)}{2}\le n\}$."

  Conjecture (conj:first-family).  "For every $r\ge 2$, the first-occurrence layer
  $L_r(\tau(r))$ consists exactly of the partitions obtained from the staircase partition
  $\delta_r$ by adding one cell at an addable corner."

Status in the source: open (computational evidence for `n ≤ 30`).  Re-validated here by
exhaustive Bron–Kerbosch clique computation for `n ≤ 28` (`Δ(n) = max {r : T_r ≤ n - 1}`,
`τ(r) = 1 + T_r` for `r ≤ 6`, first family for `r = 2, …, 6`).

## Formal model

A partition of `n` is modelled by a Mathlib `YoungDiagram` with `n` cells.  An elementary
transfer of one unit from one part to another (possibly new) part removes one cell of the
Ferrers diagram and adds another, so two partitions of the same size are adjacent exactly when
their diagrams differ by one cell: `(μ.cells \ ν.cells).card = 1`.  The clique statement
`∃ s, (partitionGraph n).IsNClique (r + 1) s ↔ r * (r + 1) / 2 + 1 ≤ n` (for `1 ≤ r`) is the
threshold conjecture: it says `Δ(n) = max {r : 1 + T_r ≤ n}` and `τ_≥(r) = 1 + T_r`.  The
first-family statement characterises the vertices of `G_{T_r + 1}` lying in an
`(r + 1)`-clique, i.e. `L_r(1 + T_r)` (no larger clique exists at that size).

## Proof outline

* Johnson-type lemma: `n`-sets with pairwise differences of one element either all contain
  `A ∩ B` (a sunflower) or all lie in `A ∪ B` (a co-sunflower).
* A sunflower of `k + 1` diagrams over the core `I` gives `k + 1` pairwise incomparable
  addable cells of `I`; a co-sunflower of `k + 1` diagrams gives `k + 1` pairwise
  incomparable removable corners of `A ∪ B`.  A pigeonhole on rows and columns places the
  staircase `δ_k` (resp. `δ_{k+1}`) inside `I` (resp. `A ∪ B`).
* Conversely the staircase `δ_r` with a row-`0` extension has `r + 1` addable cells.
-/
import Mathlib

set_option autoImplicit false

open Finset

namespace LyudogovskiySimplexStratificationPhase

/-! ### The staircase -/

/-- The staircase Young diagram `δ_r = (r, r - 1, …, 1)` as its set of cells
`{(i, j) : i + j < r}`. -/
def staircase (r : ℕ) : Finset (ℕ × ℕ) :=
  (range r ×ˢ range r).filter (fun p => p.1 + p.2 < r)

/-- Membership in the staircase: `(i, j) ∈ δ_r ↔ i + j < r`. -/
theorem mem_staircase {r : ℕ} {p : ℕ × ℕ} : p ∈ staircase r ↔ p.1 + p.2 < r := by
  unfold staircase
  simp only [mem_filter, mem_product, mem_range]
  omega

/-- `δ_{r+1}` is `δ_r` together with the anti-diagonal `i + j = r`. -/
theorem card_staircase_succ (r : ℕ) :
    (staircase (r + 1)).card = (staircase r).card + (r + 1) := by
  have hsplit : staircase (r + 1) = staircase r ∪ antidiagonal r := by
    ext p
    simp only [mem_union, mem_staircase, HasAntidiagonal.mem_antidiagonal]
    omega
  have hdisj : Disjoint (staircase r) (antidiagonal r) := by
    rw [disjoint_left]
    intro p hp hq
    rw [mem_staircase] at hp
    rw [HasAntidiagonal.mem_antidiagonal] at hq
    omega
  rw [hsplit, card_union_of_disjoint hdisj, Nat.card_antidiagonal]

/-- `|δ_r| · 2 = r (r + 1)`. -/
theorem card_staircase_mul_two (r : ℕ) : (staircase r).card * 2 = r * (r + 1) := by
  induction r with
  | zero => simp [staircase]
  | succ r ih =>
    rw [card_staircase_succ, add_mul, ih]
    ring

/-- `|δ_r| = T_r = r (r + 1) / 2`. -/
theorem card_staircase (r : ℕ) : (staircase r).card = r * (r + 1) / 2 := by
  have h := card_staircase_mul_two r
  omega

example : staircase 3 = {(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0)} := by decide

example : (staircase 4).card = 10 := by decide

/-! ### Incomparable cells force a staircase -/

/-- Cells with pairwise distinct rows: fewer than `t` of them lie in rows `< t`. -/
theorem card_filter_fst_lt_le (P : Finset (ℕ × ℕ)) (h : Set.InjOn Prod.fst (P : Set (ℕ × ℕ)))
    (t : ℕ) : (P.filter (fun p => p.1 < t)).card ≤ t := by
  have hinj : Set.InjOn Prod.fst ((P.filter (fun p => p.1 < t) : Finset _) : Set (ℕ × ℕ)) :=
    h.mono (by intro x hx; exact (mem_filter.mp hx).1)
  calc (P.filter (fun p => p.1 < t)).card
      = ((P.filter (fun p => p.1 < t)).image Prod.fst).card := (card_image_of_injOn hinj).symm
    _ ≤ (range t).card := by
        apply card_le_card
        intro x hx
        obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
        exact mem_range.mpr (mem_filter.mp hp).2
    _ = t := card_range t

/-- Cells with pairwise distinct columns: at most `t` of them lie in columns `< t`. -/
theorem card_filter_snd_lt_le (P : Finset (ℕ × ℕ)) (h : Set.InjOn Prod.snd (P : Set (ℕ × ℕ)))
    (t : ℕ) : (P.filter (fun p => p.2 < t)).card ≤ t := by
  have hinj : Set.InjOn Prod.snd ((P.filter (fun p => p.2 < t) : Finset _) : Set (ℕ × ℕ)) :=
    h.mono (by intro x hx; exact (mem_filter.mp hx).1)
  calc (P.filter (fun p => p.2 < t)).card
      = ((P.filter (fun p => p.2 < t)).image Prod.snd).card := (card_image_of_injOn hinj).symm
    _ ≤ (range t).card := by
        apply card_le_card
        intro x hx
        obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
        exact mem_range.mpr (mem_filter.mp hp).2
    _ = t := card_range t

/-- Pigeonhole: among `m` cells with distinct rows and distinct columns, for every `t < m`
some cell has row `≥ t` and column `≥ m - 1 - t`. -/
theorem exists_mem_fst_snd_large (P : Finset (ℕ × ℕ))
    (h1 : Set.InjOn Prod.fst (P : Set (ℕ × ℕ))) (h2 : Set.InjOn Prod.snd (P : Set (ℕ × ℕ)))
    (t : ℕ) (ht : t < P.card) : ∃ p ∈ P, t ≤ p.1 ∧ P.card ≤ p.2 + t + 1 := by
  by_contra hcon
  push Not at hcon
  have hsub : P ⊆ P.filter (fun p => p.1 < t) ∪ P.filter (fun p => p.2 < P.card - 1 - t) := by
    intro p hp
    rw [mem_union, mem_filter, mem_filter]
    by_cases hpt : t ≤ p.1
    · have hlt := hcon p hp hpt
      right
      exact ⟨hp, by omega⟩
    · left
      exact ⟨hp, by omega⟩
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  have hA := card_filter_fst_lt_le P h1 t
  have hB := card_filter_snd_lt_le P h2 (P.card - 1 - t)
  omega

/-- Pairwise incomparable cells have distinct rows. -/
theorem injOn_fst_of_antichain (P : Finset (ℕ × ℕ))
    (hP : ∀ p ∈ P, ∀ q ∈ P, p ≤ q → p = q) : Set.InjOn Prod.fst (P : Set (ℕ × ℕ)) := by
  intro p hp q hq hpq
  rcases le_total p.2 q.2 with h | h
  · exact hP p hp q hq (by rw [Prod.le_def]; exact ⟨hpq.le, h⟩)
  · exact (hP q hq p hp (by rw [Prod.le_def]; exact ⟨hpq.ge, h⟩)).symm

/-- Pairwise incomparable cells have distinct columns. -/
theorem injOn_snd_of_antichain (P : Finset (ℕ × ℕ))
    (hP : ∀ p ∈ P, ∀ q ∈ P, p ≤ q → p = q) : Set.InjOn Prod.snd (P : Set (ℕ × ℕ)) := by
  intro p hp q hq hpq
  rcases le_total p.1 q.1 with h | h
  · exact hP p hp q hq (by rw [Prod.le_def]; exact ⟨h, hpq.le⟩)
  · exact (hP q hq p hp (by rw [Prod.le_def]; exact ⟨h, hpq.ge⟩)).symm

/-- If `D` contains, for each cell `p` of an antichain `P`, the box of cells `x` with
`x.1 ≤ p.1` and `x.2 + e ≤ p.2`, then `D` contains the staircase `δ_k` whenever
`k + e ≤ |P|`. -/
theorem staircase_subset_of_antichain (D : Set (ℕ × ℕ)) (P : Finset (ℕ × ℕ))
    (hP : ∀ p ∈ P, ∀ q ∈ P, p ≤ q → p = q) (e k : ℕ) (hk : k + e ≤ P.card)
    (hbox : ∀ p ∈ P, ∀ x : ℕ × ℕ, x.1 ≤ p.1 → x.2 + e ≤ p.2 → x ∈ D) :
    ∀ x ∈ staircase k, x ∈ D := by
  intro x hx
  rw [mem_staircase] at hx
  obtain ⟨p, hp, h1, h2⟩ := exists_mem_fst_snd_large P (injOn_fst_of_antichain P hP)
    (injOn_snd_of_antichain P hP) x.1 (by omega)
  exact hbox p hp x h1 (by omega)

/-! ### Johnson-type clique lemma -/

/-- Pointwise Johnson lemma: if `A, B, C` are `n`-sets with `|A \ B| = |A \ C| = |B \ C| = 1`,
then either `A ∩ B ⊆ C`, or `C = (A ∪ B) \ {x}` for some `x ∈ A ∩ B` missing from `C`. -/
theorem subset_or_subset_of_sdiff {α : Type*} [DecidableEq α] (n : ℕ) (A B C : Finset α)
    (hA : A.card = n) (hB : B.card = n) (hC : C.card = n) (hAB : (A \ B).card = 1)
    (hAC : (A \ C).card = 1) (hBC : (B \ C).card = 1) :
    A ∩ B ⊆ C ∨ ∃ x ∈ A ∩ B, x ∉ C ∧ C = (A ∪ B).erase x := by
  by_cases hsub : A ∩ B ⊆ C
  · exact Or.inl hsub
  right
  obtain ⟨x, hxAB, hxC⟩ := not_subset.mp hsub
  refine ⟨x, hxAB, hxC, ?_⟩
  have hxA : x ∈ A \ C := mem_sdiff.mpr ⟨(mem_inter.mp hxAB).1, hxC⟩
  have hxB : x ∈ B \ C := mem_sdiff.mpr ⟨(mem_inter.mp hxAB).2, hxC⟩
  have hsubC : (A ∪ B).erase x ⊆ C := by
    intro y hy
    obtain ⟨hyx, hyAB⟩ := mem_erase.mp hy
    by_contra hyC
    rcases mem_union.mp hyAB with hyA | hyB
    · exact hyx (card_le_one.mp hAC.le y (mem_sdiff.mpr ⟨hyA, hyC⟩) x hxA)
    · exact hyx (card_le_one.mp hBC.le y (mem_sdiff.mpr ⟨hyB, hyC⟩) x hxB)
  have hinter : (A ∩ B).card + 1 = n := by
    have hsplit := card_sdiff_add_card_inter A B
    omega
  have hunion : (A ∪ B).card = n + 1 := by
    have hui := card_union_add_card_inter A B
    omega
  have hxU : x ∈ A ∪ B := mem_union.mpr (Or.inl (mem_inter.mp hxAB).1)
  have hcardE : ((A ∪ B).erase x).card = n := by
    rw [card_erase_of_mem hxU, hunion]
    rfl
  exact (eq_of_subset_of_card_le hsubC (by rw [hC, hcardE])).symm

/-- Johnson-type clique lemma: in a family of `n`-sets whose distinct members differ in exactly
one element, for any two distinct members `A, B`, either every member contains `A ∩ B` or every
member lies inside `A ∪ B`. -/
theorem sunflower_or_cosunflower {α : Type*} [DecidableEq α] (n : ℕ) (F : Finset (Finset α))
    (hcard : ∀ C ∈ F, C.card = n) (hadj : ∀ C ∈ F, ∀ D ∈ F, C ≠ D → (C \ D).card = 1)
    (A B : Finset α) (hA : A ∈ F) (hB : B ∈ F) (hAB : A ≠ B) :
    (∀ C ∈ F, A ∩ B ⊆ C) ∨ (∀ C ∈ F, C ⊆ A ∪ B) := by
  have key : ∀ C ∈ F, A ∩ B ⊆ C ∨ ∃ x ∈ A ∩ B, x ∉ C ∧ C = (A ∪ B).erase x := by
    intro C hC
    by_cases hCA : C = A
    · subst hCA
      exact Or.inl inter_subset_left
    by_cases hCB : C = B
    · subst hCB
      exact Or.inl inter_subset_right
    exact subset_or_subset_of_sdiff n A B C (hcard A hA) (hcard B hB) (hcard C hC)
      (hadj A hA B hB hAB) (hadj A hA C hC (Ne.symm hCA)) (hadj B hB C hC (Ne.symm hCB))
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨C, hC, hCsub⟩, ⟨D, hD, hDsub⟩⟩ := hcon
  obtain ⟨x, hxAB, hxC, hCeq⟩ := (key C hC).resolve_left hCsub
  have hDI : A ∩ B ⊆ D := by
    rcases key D hD with h | ⟨y, -, -, hDeq⟩
    · exact h
    · exact absurd (hDeq ▸ erase_subset y (A ∪ B)) hDsub
  obtain ⟨y, hyD, hyU⟩ := not_subset.mp hDsub
  have hCD : C ≠ D := by
    rintro rfl
    exact hxC (hDI hxAB)
  have h2 : ({x, y} : Finset α) ⊆ D \ C := by
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact mem_sdiff.mpr ⟨hDI hxAB, hxC⟩
    · rw [mem_singleton.mp hz]
      refine mem_sdiff.mpr ⟨hyD, fun hyC => hyU ?_⟩
      rw [hCeq] at hyC
      exact (mem_erase.mp hyC).2
  have hxy : x ≠ y := by
    rintro rfl
    exact hyU (mem_union.mpr (Or.inl (mem_inter.mp hxAB).1))
  have hle := card_le_card h2
  rw [card_pair hxy, hadj D hD C hC (Ne.symm hCD)] at hle
  omega

/-! ### Sunflower and co-sunflower bounds -/

/-- Sunflower bound: if `k + 1` lower sets each consist of a common core `I` plus one cell,
then the core contains the staircase `δ_k`. -/
theorem staircase_subset_of_sunflower (I : Finset (ℕ × ℕ)) (F : Finset (Finset (ℕ × ℕ)))
    (hF : ∀ C ∈ F, I ⊆ C ∧ (C \ I).card = 1 ∧ IsLowerSet (C : Set (ℕ × ℕ)))
    (k : ℕ) (hk : k + 1 ≤ F.card) : staircase k ⊆ I := by
  set P := F.biUnion (fun C => C \ I) with hPdef
  have hdisj : ∀ C ∈ F, ∀ D ∈ F, C ≠ D → Disjoint (C \ I) (D \ I) := by
    intro C hC D hD hCD
    rw [disjoint_left]
    intro a haC haD
    apply hCD
    obtain ⟨a', ha'⟩ := card_eq_one.mp (hF C hC).2.1
    obtain ⟨a'', ha''⟩ := card_eq_one.mp (hF D hD).2.1
    rw [ha'] at haC
    rw [ha''] at haD
    rw [mem_singleton] at haC haD
    rw [← union_sdiff_of_subset (hF C hC).1, ← union_sdiff_of_subset (hF D hD).1, ha', ha'',
      ← haC, ← haD]
  have hPcard : P.card = F.card := by
    rw [hPdef, card_biUnion hdisj]
    rw [sum_congr rfl (fun C hC => (hF C hC).2.1), sum_const, smul_eq_mul, mul_one]
  have hanti : ∀ p ∈ P, ∀ q ∈ P, p ≤ q → p = q := by
    intro p hp q hq hpq
    obtain ⟨C, hC, hpC⟩ := mem_biUnion.mp hp
    obtain ⟨D, hD, hqD⟩ := mem_biUnion.mp hq
    have hpD : p ∈ D := (hF D hD).2.2 hpq (mem_sdiff.mp hqD).1
    exact card_le_one.mp (hF D hD).2.1.le p (mem_sdiff.mpr ⟨hpD, (mem_sdiff.mp hpC).2⟩) q hqD
  have hbox : ∀ p ∈ P, ∀ x : ℕ × ℕ, x.1 ≤ p.1 → x.2 + 1 ≤ p.2 →
      x ∈ (I : Set (ℕ × ℕ)) := by
    intro p hp x hx1 hx2
    obtain ⟨C, hC, hpC⟩ := mem_biUnion.mp hp
    have hxp : x ≤ p := by
      rw [Prod.le_def]
      exact ⟨hx1, by omega⟩
    have hxC : x ∈ C := (hF C hC).2.2 hxp (mem_sdiff.mp hpC).1
    by_contra hxI
    have hxeq := card_le_one.mp (hF C hC).2.1.le x (mem_sdiff.mpr ⟨hxC, hxI⟩) p hpC
    rw [hxeq] at hx2
    omega
  intro x hx
  exact staircase_subset_of_antichain (I : Set (ℕ × ℕ)) P hanti 1 k (by omega) hbox x hx

/-- Co-sunflower bound: if `k` lower sets each arise from a common lower set `U` by deleting one
cell, then `U` contains the staircase `δ_k`. -/
theorem staircase_subset_of_cosunflower (U : Finset (ℕ × ℕ))
    (hU : IsLowerSet (U : Set (ℕ × ℕ))) (F : Finset (Finset (ℕ × ℕ)))
    (hF : ∀ C ∈ F, C ⊆ U ∧ (U \ C).card = 1 ∧ IsLowerSet (C : Set (ℕ × ℕ)))
    (k : ℕ) (hk : k ≤ F.card) : staircase k ⊆ U := by
  set P := F.biUnion (fun C => U \ C) with hPdef
  have hdisj : ∀ C ∈ F, ∀ D ∈ F, C ≠ D → Disjoint (U \ C) (U \ D) := by
    intro C hC D hD hCD
    rw [disjoint_left]
    intro a haC haD
    apply hCD
    obtain ⟨a', ha'⟩ := card_eq_one.mp (hF C hC).2.1
    obtain ⟨a'', ha''⟩ := card_eq_one.mp (hF D hD).2.1
    rw [ha'] at haC
    rw [ha''] at haD
    rw [mem_singleton] at haC haD
    rw [← Finset.sdiff_sdiff_eq_self (hF C hC).1, ← Finset.sdiff_sdiff_eq_self (hF D hD).1,
      ha', ha'', ← haC, ← haD]
  have hPcard : P.card = F.card := by
    rw [hPdef, card_biUnion hdisj]
    rw [sum_congr rfl (fun C hC => (hF C hC).2.1), sum_const, smul_eq_mul, mul_one]
  have hanti : ∀ p ∈ P, ∀ q ∈ P, p ≤ q → p = q := by
    intro p hp q hq hpq
    obtain ⟨C, hC, hpC⟩ := mem_biUnion.mp hp
    obtain ⟨D, hD, hqD⟩ := mem_biUnion.mp hq
    by_contra hne
    have hqC : q ∈ C := by
      by_contra hqC
      exact hne (card_le_one.mp (hF C hC).2.1.le p hpC q
        (mem_sdiff.mpr ⟨(mem_sdiff.mp hqD).1, hqC⟩))
    exact (mem_sdiff.mp hpC).2 ((hF C hC).2.2 hpq hqC)
  have hbox : ∀ p ∈ P, ∀ x : ℕ × ℕ, x.1 ≤ p.1 → x.2 + 0 ≤ p.2 →
      x ∈ (U : Set (ℕ × ℕ)) := by
    intro p hp x hx1 hx2
    obtain ⟨C, hC, hpC⟩ := mem_biUnion.mp hp
    have hxp : x ≤ p := by
      rw [Prod.le_def]
      exact ⟨hx1, by omega⟩
    exact hU hxp (mem_sdiff.mp hpC).1
  intro x hx
  exact staircase_subset_of_antichain (U : Set (ℕ × ℕ)) P hanti 0 k (by omega) hbox x hx

/-! ### The partition graph -/

/-- The partition graph `G_n` in the Young-diagram model: vertices are Young diagrams with `n`
cells (partitions of `n`), and two of them are adjacent iff they differ by moving a single cell,
i.e. `|μ \ ν| = 1`.  This is the source's "elementary transfer of one unit between two parts,
followed by reordering" (a new part of size one may be created). -/
def partitionGraph (n : ℕ) : SimpleGraph {μ : YoungDiagram // μ.cells.card = n} where
  Adj μ ν := (μ.1.cells \ ν.1.cells).card = 1
  symm := by
    constructor
    intro μ ν h
    rw [card_sdiff_comm (ν.2.trans μ.2.symm)]
    exact h
  loopless := by
    constructor
    intro μ h
    change (μ.1.cells \ μ.1.cells).card = 1 at h
    simp at h

/-- Adjacency in `G_n` unfolds to `|μ \ ν| = 1`. -/
theorem partitionGraph_adj {n : ℕ} {μ ν : {μ : YoungDiagram // μ.cells.card = n}} :
    (partitionGraph n).Adj μ ν ↔ (μ.1.cells \ ν.1.cells).card = 1 := Iff.rfl

/-- Vertices of `G_n` are determined by their cells. -/
theorem vertex_ext {n : ℕ} {μ ν : {μ : YoungDiagram // μ.cells.card = n}}
    (h : μ.1.cells = ν.1.cells) : μ = ν :=
  Subtype.ext (YoungDiagram.ext h)

/-- Structure of a clique of `G_n` with `k + 1 ≥ 2` vertices: either it is a sunflower over a
core `I` with `n - 1` cells containing `δ_k`, or the union of two of its members is a diagram
with `n + 1` cells containing `δ_{k+1}`. -/
theorem isNClique_structure {n k : ℕ} {s : Finset {μ : YoungDiagram // μ.cells.card = n}}
    (hs : (partitionGraph n).IsNClique (k + 1) s) (hk : 1 ≤ k) :
    (∃ I : Finset (ℕ × ℕ), I.card + 1 = n ∧
        (∀ v ∈ s, I ⊆ v.1.cells ∧ (v.1.cells \ I).card = 1) ∧ staircase k ⊆ I) ∨
      (∃ U : Finset (ℕ × ℕ), U.card = n + 1 ∧ staircase (k + 1) ⊆ U) := by
  classical
  set F := s.image (fun v => v.1.cells) with hFdef
  have hinj : Set.InjOn (fun v : {μ : YoungDiagram // μ.cells.card = n} => v.1.cells) s :=
    fun v _ w _ hvw => vertex_ext hvw
  have hFcard : F.card = k + 1 := by rw [hFdef, card_image_of_injOn hinj, hs.2]
  have hmemF : ∀ C ∈ F, ∃ v ∈ s, v.1.cells = C := fun C hC => mem_image.mp hC
  have hcard : ∀ C ∈ F, C.card = n := by
    intro C hC
    obtain ⟨v, -, rfl⟩ := hmemF C hC
    exact v.2
  have hlower : ∀ C ∈ F, IsLowerSet (C : Set (ℕ × ℕ)) := by
    intro C hC
    obtain ⟨v, -, rfl⟩ := hmemF C hC
    exact v.1.isLowerSet
  have hadj : ∀ C ∈ F, ∀ D ∈ F, C ≠ D → (C \ D).card = 1 := by
    intro C hC D hD hCD
    obtain ⟨v, hv, rfl⟩ := hmemF C hC
    obtain ⟨w, hw, rfl⟩ := hmemF D hD
    have hvw : v ≠ w := by
      rintro rfl
      exact hCD rfl
    exact partitionGraph_adj.mp (hs.1 hv hw hvw)
  obtain ⟨A, hA, B, hB, hAB⟩ := one_lt_card.mp (by rw [hFcard]; omega : 1 < F.card)
  have hAB1 := hadj A hA B hB hAB
  have hinter : (A ∩ B).card + 1 = n := by
    have hsplit := card_sdiff_add_card_inter A B
    have hAn := hcard A hA
    omega
  rcases sunflower_or_cosunflower n F hcard hadj A B hA hB hAB with hsun | hco
  · left
    have hF : ∀ C ∈ F, A ∩ B ⊆ C ∧ (C \ (A ∩ B)).card = 1 ∧
        IsLowerSet (C : Set (ℕ × ℕ)) := by
      intro C hC
      refine ⟨hsun C hC, ?_, hlower C hC⟩
      have h1 := card_sdiff_add_card_inter C (A ∩ B)
      rw [inter_eq_right.mpr (hsun C hC), hcard C hC] at h1
      omega
    refine ⟨A ∩ B, hinter, ?_, staircase_subset_of_sunflower (A ∩ B) F hF k (by omega)⟩
    intro v hv
    have hC : v.1.cells ∈ F := mem_image_of_mem _ hv
    exact ⟨(hF _ hC).1, (hF _ hC).2.1⟩
  · right
    have hunion : (A ∪ B).card = n + 1 := by
      have hui := card_union_add_card_inter A B
      have hAn := hcard A hA
      have hBn := hcard B hB
      omega
    have hU : IsLowerSet ((A ∪ B : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
      rw [coe_union]
      exact (hlower A hA).union (hlower B hB)
    have hF : ∀ C ∈ F, C ⊆ A ∪ B ∧ ((A ∪ B) \ C).card = 1 ∧
        IsLowerSet (C : Set (ℕ × ℕ)) := by
      intro C hC
      refine ⟨hco C hC, ?_, hlower C hC⟩
      have h1 := card_sdiff_add_card_inter (A ∪ B) C
      rw [inter_eq_right.mpr (hco C hC), hcard C hC, hunion] at h1
      omega
    exact ⟨A ∪ B, hunion, staircase_subset_of_cosunflower (A ∪ B) hU F hF (k + 1) (by omega)⟩

/-- A lower set `I` with `n - 1` cells and a set `A` of addable cells yields an `|A|`-clique of
`G_n`, namely the diagrams `I ∪ {a}` for `a ∈ A`. -/
theorem exists_isNClique_of_addable (n : ℕ) (I : Finset (ℕ × ℕ)) (hIn : I.card + 1 = n)
    (A : Finset (ℕ × ℕ))
    (hA : ∀ a ∈ A, a ∉ I ∧ IsLowerSet ((insert a I : Finset (ℕ × ℕ)) : Set (ℕ × ℕ))) :
    ∃ s : Finset {μ : YoungDiagram // μ.cells.card = n},
      (partitionGraph n).IsNClique A.card s ∧
        ∀ a ∈ A, ∃ v ∈ s, v.1.cells = insert a I := by
  classical
  let f : A → {μ : YoungDiagram // μ.cells.card = n} := fun a =>
    ⟨⟨insert a.1 I, (hA a.1 a.2).2⟩, by
      change (insert a.1 I).card = n
      rw [card_insert_of_notMem (hA a.1 a.2).1, hIn]⟩
  have hf : ∀ a, (f a).1.cells = insert a.1 I := fun a => rfl
  have hinsert : ∀ a b : A, a ≠ b → (insert a.1 I \ insert b.1 I) = {a.1} := by
    intro a b hab
    ext x
    simp only [mem_sdiff, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hx | hx, hx'⟩
      · exact hx
      · exact absurd (Or.inr hx) hx'
    · rintro rfl
      refine ⟨Or.inl rfl, ?_⟩
      rintro (h | h)
      · exact hab (Subtype.ext h)
      · exact (hA a.1 a.2).1 h
  have hfinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    have h1 := congrArg
      (fun v : {μ : YoungDiagram // μ.cells.card = n} => v.1.cells \ insert b.1 I) hab
    simp only [hf, sdiff_self] at h1
    rw [hinsert a b hne] at h1
    exact singleton_ne_empty _ h1
  refine ⟨univ.map ⟨f, hfinj⟩, ⟨?_, ?_⟩, ?_⟩
  · intro v hv w hw hvw
    simp only [coe_map, Function.Embedding.coeFn_mk, coe_univ, Set.image_univ,
      Set.mem_range] at hv hw
    obtain ⟨a, rfl⟩ := hv
    obtain ⟨b, rfl⟩ := hw
    have hab : a ≠ b := fun h => hvw (congrArg f h)
    rw [partitionGraph_adj, hf, hf, hinsert a b hab, card_singleton]
  · rw [card_map, card_univ, Fintype.card_coe]
  · intro a ha
    exact ⟨f ⟨a, ha⟩, mem_map_of_mem _ (mem_univ _), rfl⟩

/-! ### Lower bound: an explicit `(r + 1)`-clique -/

/-- The staircase `δ_r` with its first row extended by `e` cells. -/
def extendedStaircase (r e : ℕ) : Finset (ℕ × ℕ) :=
  staircase r ∪ (Ico r (r + e)).map ⟨fun j => (0, j), fun _ _ h => (Prod.ext_iff.mp h).2⟩

/-- Membership in the extended staircase. -/
theorem mem_extendedStaircase {r e : ℕ} {p : ℕ × ℕ} :
    p ∈ extendedStaircase r e ↔ p.1 + p.2 < r ∨ (p.1 = 0 ∧ r ≤ p.2 ∧ p.2 < r + e) := by
  unfold extendedStaircase
  simp only [mem_union, mem_staircase, mem_map, mem_Ico]
  constructor
  · rintro (h | ⟨j, hj, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨rfl, hj⟩
  · rintro (h | ⟨h0, h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨p.2, ⟨h1, h2⟩, Prod.ext h0.symm rfl⟩

/-- The extended staircase has `T_r + e` cells. -/
theorem card_extendedStaircase (r e : ℕ) :
    (extendedStaircase r e).card = (staircase r).card + e := by
  unfold extendedStaircase
  rw [card_union_of_disjoint, card_map, Nat.card_Ico]
  · omega
  · rw [disjoint_left]
    intro p hp hq
    rw [mem_staircase] at hp
    obtain ⟨j, hj, rfl⟩ := mem_map.mp hq
    rw [mem_Ico] at hj
    change 0 + j < r at hp
    omega

/-- The `r + 1` addable cells of the extended staircase: `(0, r + e)` and `(i, r - i)` for
`1 ≤ i ≤ r`. -/
def extendedAddable (r e : ℕ) : Finset (ℕ × ℕ) :=
  (range (r + 1)).image (fun i => (i, if i = 0 then r + e else r - i))

/-- There are exactly `r + 1` such cells. -/
theorem card_extendedAddable (r e : ℕ) : (extendedAddable r e).card = r + 1 := by
  unfold extendedAddable
  rw [card_image_of_injOn, card_range]
  intro i _ j _ hij
  exact (Prod.ext_iff.mp hij).1

/-- Each listed cell is addable to the extended staircase. -/
theorem extendedAddable_spec {r e : ℕ} :
    ∀ a ∈ extendedAddable r e, a ∉ extendedStaircase r e ∧
      IsLowerSet ((insert a (extendedStaircase r e) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
  intro a ha
  unfold extendedAddable at ha
  obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
  rw [mem_range] at hi
  constructor
  · rw [mem_extendedStaircase]
    split_ifs with h0 <;> simp only [] <;> omega
  · intro x y hyx hx
    rw [coe_insert, Set.mem_insert_iff, mem_coe, mem_extendedStaircase] at hx ⊢
    rw [Prod.le_def] at hyx
    rcases hx with hx | hx
    · rw [hx] at hyx
      split_ifs at hyx ⊢ with h0
      · rcases Nat.lt_or_ge y.2 (r + e) with h | h
        · right
          omega
        · left
          exact Prod.ext (by simp only []; omega) (by simp only []; omega)
      · by_cases hy : y = (i, r - i)
        · exact Or.inl hy
        · right
          left
          have hne : y.1 ≠ i ∨ y.2 ≠ r - i := by
            by_contra hcon
            push Not at hcon
            exact hy (Prod.ext hcon.1 hcon.2)
          simp only [] at hyx
          omega
    · right
      omega

/-- Lower bound: if `T_r + 1 ≤ n`, then `G_n` has an `(r + 1)`-clique. -/
theorem exists_isNClique_of_le {n r : ℕ} (hn : (staircase r).card + 1 ≤ n) :
    ∃ s, (partitionGraph n).IsNClique (r + 1) s := by
  obtain ⟨s, hs, -⟩ := exists_isNClique_of_addable n
    (extendedStaircase r (n - 1 - (staircase r).card)) (by rw [card_extendedStaircase]; omega)
    (extendedAddable r (n - 1 - (staircase r).card))
    extendedAddable_spec
  rw [card_extendedAddable] at hs
  exact ⟨s, hs⟩

/-! ### Main theorems -/

/-- **Triangular threshold (Lyudogovskiy, arXiv:2603.23228, Conjecture
`conj:triangular-threshold`), clique-number form.**  For every `n` and every `r ≥ 1`, the
partition graph `G_n` contains a clique on `r + 1` vertices (a simplex of dimension `r` of the
clique complex `K_n`) iff `T_r + 1 ≤ n`, where `T_r = r (r + 1) / 2`.  Equivalently
`Δ(n) = max {r : 1 + T_r ≤ n}` and the first `n` with a vertex of local dimension `≥ r` is
`1 + T_r`. -/
theorem exists_isNClique_iff (n r : ℕ) (hr : 1 ≤ r) :
    (∃ s, (partitionGraph n).IsNClique (r + 1) s) ↔ r * (r + 1) / 2 + 1 ≤ n := by
  rw [← card_staircase]
  constructor
  · rintro ⟨s, hs⟩
    rcases isNClique_structure hs hr with ⟨I, hIn, -, hsub⟩ | ⟨U, hUn, hsub⟩
    · have hle := card_le_card hsub
      omega
    · have hle := card_le_card hsub
      rw [card_staircase_succ] at hle
      omega
  · exact exists_isNClique_of_le

/-- **Staircase first-occurrence family (Lyudogovskiy, arXiv:2603.23228, Conjecture
`conj:first-family`).**  For `r ≥ 2` and `n = T_r + 1`, a partition `μ` of `n` lies in a clique
of `G_n` with `r + 1` vertices (i.e. `dim_loc(μ) = r`, the maximum possible at this size by
`exists_isNClique_iff`) iff `μ` is the staircase `δ_r = (r, r - 1, …, 1)` with one cell
added. -/
theorem exists_mem_isNClique_iff (r : ℕ) (hr : 2 ≤ r)
    (μ : {μ : YoungDiagram // μ.cells.card = r * (r + 1) / 2 + 1}) :
    (∃ s, μ ∈ s ∧ (partitionGraph (r * (r + 1) / 2 + 1)).IsNClique (r + 1) s) ↔
      ∃ c ∉ staircase r, μ.1.cells = insert c (staircase r) := by
  have hT := card_staircase r
  constructor
  · rintro ⟨s, hμs, hs⟩
    rcases isNClique_structure hs (by omega) with ⟨I, hIn, hmem, hsub⟩ | ⟨U, hUn, hsub⟩
    · have hIeq : staircase r = I := eq_of_subset_of_card_le hsub (by omega)
      obtain ⟨hIμ, hμI⟩ := hmem μ hμs
      obtain ⟨c, hc⟩ := card_eq_one.mp hμI
      have hcmem : c ∈ μ.1.cells \ I := by
        rw [hc]
        exact mem_singleton_self c
      refine ⟨c, hIeq ▸ (mem_sdiff.mp hcmem).2, ?_⟩
      rw [hIeq, insert_eq, ← hc, sdiff_union_of_subset hIμ]
    · have hle := card_le_card hsub
      rw [card_staircase_succ] at hle
      omega
  · rintro ⟨c, hc, hμ⟩
    -- the added cell lies on the anti-diagonal `i + j = r`
    have hcr : c ∈ antidiagonal r := by
      rw [HasAntidiagonal.mem_antidiagonal]
      rw [mem_staircase] at hc
      have hlow : ∀ y : ℕ × ℕ, y ≤ c → y ≠ c → y.1 + y.2 < r := by
        intro y hyc hne
        have hyμ : y ∈ μ.1.cells :=
          μ.1.isLowerSet hyc (by rw [mem_coe, hμ]; exact mem_insert_self _ _)
        rw [hμ, mem_insert] at hyμ
        rcases hyμ with h | h
        · exact absurd h hne
        · exact mem_staircase.mp h
      by_contra hne
      rcases Nat.eq_zero_or_pos c.2 with h2 | h2
      · have h := hlow (c.1 - 1, c.2) (by rw [Prod.le_def]; exact ⟨Nat.sub_le _ _, le_rfl⟩)
          (by intro h; have := congrArg Prod.fst h; simp only [] at this; omega)
        simp only [] at h
        omega
      · have h := hlow (c.1, c.2 - 1) (by rw [Prod.le_def]; exact ⟨le_rfl, Nat.sub_le _ _⟩)
          (by intro h; have := congrArg Prod.snd h; simp only [] at this; omega)
        simp only [] at h
        omega
    have hspec : ∀ a ∈ antidiagonal r, a ∉ staircase r ∧
        IsLowerSet ((insert a (staircase r) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
      intro a ha
      rw [HasAntidiagonal.mem_antidiagonal] at ha
      refine ⟨by rw [mem_staircase]; omega, ?_⟩
      intro x y hyx hx
      rw [coe_insert, Set.mem_insert_iff, mem_coe, mem_staircase] at hx ⊢
      rw [Prod.le_def] at hyx
      rcases hx with rfl | hx
      · by_cases hy : y = x
        · exact Or.inl hy
        · right
          have hne : y.1 ≠ x.1 ∨ y.2 ≠ x.2 := by
            by_contra hcon
            push Not at hcon
            exact hy (Prod.ext hcon.1 hcon.2)
          omega
      · right
        omega
    obtain ⟨s, hs, hsmem⟩ := exists_isNClique_of_addable (r * (r + 1) / 2 + 1) (staircase r)
      (by rw [hT]) (antidiagonal r) hspec
    rw [Nat.card_antidiagonal] at hs
    obtain ⟨v, hv, hvc⟩ := hsmem c hcr
    exact ⟨s, vertex_ext (hvc.trans hμ.symm) ▸ hv, hs⟩

/-! ### Ground-truth checks on small instances -/

/-- The diagram of `(3)`, a vertex of `G_3`. -/
private def v3 : {μ : YoungDiagram // μ.cells.card = 3} :=
  ⟨YoungDiagram.ofRowLens [3] (by decide), by decide⟩

/-- The diagram of `(2, 1)`, a vertex of `G_3`. -/
private def v21 : {μ : YoungDiagram // μ.cells.card = 3} :=
  ⟨YoungDiagram.ofRowLens [2, 1] (by decide), by decide⟩

/-- The diagram of `(1, 1, 1)`, a vertex of `G_3`. -/
private def v111 : {μ : YoungDiagram // μ.cells.card = 3} :=
  ⟨YoungDiagram.ofRowLens [1, 1, 1] (by decide), by decide⟩

-- `(3) → (2, 1)` is one elementary transfer, so they are adjacent.
example : (partitionGraph 3).Adj v3 v21 := by
  rw [partitionGraph_adj]
  decide

-- `(3)` and `(1, 1, 1)` differ by two transfers, so they are not adjacent.
example : ¬ (partitionGraph 3).Adj v3 v111 := by
  rw [partitionGraph_adj]
  decide

-- `G_3` is the path `(3) — (2, 1) — (1, 1, 1)`: it has an edge but no triangle (`T_2 + 1 = 4`).
example : ∃ s, (partitionGraph 3).IsNClique 2 s :=
  (exists_isNClique_iff 3 1 le_rfl).mpr (by norm_num)

example : ¬ ∃ s, (partitionGraph 3).IsNClique 3 s := by
  rw [exists_isNClique_iff 3 2 (by norm_num)]
  norm_num

-- `G_4` has a triangle (`(3,1), (2,2), (2,1,1)` over the core `(2,1)`), but no `K_4`.
example : ∃ s, (partitionGraph 4).IsNClique 3 s :=
  (exists_isNClique_iff 4 2 (by norm_num)).mpr (by norm_num)

example : ¬ ∃ s, (partitionGraph 10).IsNClique 5 s := by
  rw [exists_isNClique_iff 10 4 (by norm_num)]
  norm_num

-- First family at `r = 2`, `n = 4`: `(3, 1) = δ_2 + (0, 2)` lies in a triangle of `G_4`.
example : ∃ s, (⟨YoungDiagram.ofRowLens [3, 1] (by decide), by decide⟩ :
    {μ : YoungDiagram // μ.cells.card = 2 * (2 + 1) / 2 + 1}) ∈ s ∧
    (partitionGraph (2 * (2 + 1) / 2 + 1)).IsNClique (2 + 1) s := by
  rw [exists_mem_isNClique_iff 2 le_rfl]
  exact ⟨(0, 2), by decide, by decide⟩

-- whereas `(4)` is not of that form, so it lies in no triangle of `G_4`.
example : ¬ ∃ s, (⟨YoungDiagram.ofRowLens [4] (by decide), by decide⟩ :
    {μ : YoungDiagram // μ.cells.card = 2 * (2 + 1) / 2 + 1}) ∈ s ∧
    (partitionGraph (2 * (2 + 1) / 2 + 1)).IsNClique (2 + 1) s := by
  rw [exists_mem_isNClique_iff 2 le_rfl]
  rintro ⟨c, hc, hcells⟩
  have h01 : ((1, 0) : ℕ × ℕ) ∈ insert c (staircase 2) := mem_insert_of_mem (by decide)
  rw [← hcells] at h01
  revert h01
  decide

end LyudogovskiySimplexStratificationPhase
