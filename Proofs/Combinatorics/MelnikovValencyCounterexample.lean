/-
# Melnikov's valency-variety problem: the 37-vertex counterexample `G_*`

## Source

Yang–Zeng, arXiv:2610.09649, "Melnikov's valency variety problem".
Conjecture 1.1 (Melnikov; recorded by Vizing 1968 and Zykov 1968, Open
Problem Garden), Section 4.1 ("A 37-Vertex Extremal Graph"), Table 1,
Proposition 4.1 and the Remark following it.  Recorded 2026-10-21.

Verbatim informal claims:

* Conjecture 1.1: "Every simple graph `G` with at least two vertices
  satisfies `χ(G) > ⌈⌊w(G)/2⌋ / (|V(G)| - w(G))⌉`", where the valency
  variety `w(G)` is the number of distinct vertex degrees of `G`.
* Section 4.1: "Let `A, B, C` be pairwise disjoint independent sets with
  `|A| = 8`, `|B| = 10` and `|C| = 19`. Assign to their vertices the integer
  weights displayed below. [...] For vertices `u, v` in different parts, put
  `uv ∈ E(G_*) ⟺ λ(u) + λ(v) ≥ 0` [...]. There are no edges within any of the
  three parts."  Weights: `A: -9,-8,2,4,5,6,7,9`;
  `B: -6,-5,-2,-1,0,1,2,3,6,8`; `C: -8,-7,-6,-4,-3,-2,-1,0,1^(8),4,5,7`.
* Proposition 4.1: "The degree set of `G_*` is exactly `{0,1,…,29}`.
  Consequently, `|V(G_*)| = 37`, `w(G_*) = 30` and `χ(G_*) = ω(G_*) = 3`."
* Remark: "`⌈⌊w(G_*)/2⌋/(|V(G_*)| - w(G_*))⌉ = ⌈15/7⌉ = 3 = χ(G_*)`. Thus
  the strict inequality in Conjecture 1.1 fails for `G_*`."

## Status

Proved in the paper (Proposition 4.1 and Remark); Conjecture 1.1 is false.

## Encoding

Vertices are `Fin 37`, listed in the order of Table 1: indices `0–7` form
`A`, `8–17` form `B`, `18–36` form `C`.  `part` records the part and `wt`
the weight `λ`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.MelnikovValencyCounterexample

open SimpleGraph Finset

/-! ## The general notions of Conjecture 1.1 -/

/-- The valency variety `w(G)`: the number of distinct vertex degrees of a
finite simple graph `G`. -/
def valencyVariety {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.image fun v => G.degree v).card

/-- The Melnikov bound `⌈⌊w/2⌋ / (n - w)⌉` for a graph on `n` vertices with
valency variety `w`, computed in `ℚ` (subtraction is performed after casting)
and rounded up to a natural number.  For every simple graph with at least two
vertices one has `w ≤ n - 1`, so the denominator is positive and the rational
quotient is nonnegative; the junk values of `/` and `⌈·⌉₊` are never reached. -/
def melnikovBound (n w : ℕ) : ℕ :=
  ⌈((w / 2 : ℕ) : ℚ) / ((n : ℚ) - (w : ℚ))⌉₊

/-- Melnikov's Conjecture 1.1 (as recorded by Vizing 1968): every finite simple
graph `G` with at least two vertices satisfies
`χ(G) > ⌈⌊w(G)/2⌋ / (|V(G)| - w(G))⌉`. -/
def MelnikovConjecture : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    2 ≤ Fintype.card V →
      ((melnikovBound (Fintype.card V) (valencyVariety G) : ℕ) : ℕ∞) < G.chromaticNumber

/-! ### Ground truth on the general notions -/

/-- The empty graph on `3` vertices has only degree `0`. -/
example : valencyVariety (⊥ : SimpleGraph (Fin 3)) = 1 := by decide
/-- All vertices of `K_3` have degree `2`, hence valency variety `1`. -/
example : valencyVariety (completeGraph (Fin 3)) = 1 := by decide
/-- For the path on `3` vertices: `⌈⌊2/2⌋/(3 - 2)⌉ = 1`. -/
example : melnikovBound 3 2 = 1 := by
  rw [melnikovBound, Nat.ceil_eq_iff (by norm_num)]
  norm_num
/-- `⌈⌊5/2⌋/(8 - 5)⌉ = ⌈2/3⌉ = 1`. -/
example : melnikovBound 8 5 = 1 := by
  rw [melnikovBound, Nat.ceil_eq_iff (by norm_num)]
  norm_num

/-! ## The graph `G_*` of Section 4.1 -/

/-- The part (`0 = A`, `1 = B`, `2 = C`) of a vertex of `G_*`: the first `8`
vertices form `A`, the next `10` form `B`, the last `19` form `C`. -/
def part (v : Fin 37) : Fin 3 :=
  if v.val < 8 then 0 else if v.val < 18 then 1 else 2

/-- The weight `λ` of a vertex of `G_*`, transcribed from Table 1 of
arXiv:2610.09649 in the order `A`, `B`, `C`. -/
def wt : Fin 37 → ℤ :=
  ![-9, -8, 2, 4, 5, 6, 7, 9,
    -6, -5, -2, -1, 0, 1, 2, 3, 6, 8,
    -8, -7, -6, -4, -3, -2, -1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 7]

/-- The graph `G_*`: two vertices are adjacent iff they lie in different parts
and their weights have nonnegative sum. -/
def Gstar : SimpleGraph (Fin 37) where
  Adj u v := part u ≠ part v ∧ 0 ≤ wt u + wt v
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [add_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Adjacency in `G_*` is decidable. -/
instance : DecidableRel Gstar.Adj := fun u v =>
  inferInstanceAs (Decidable (part u ≠ part v ∧ 0 ≤ wt u + wt v))

/-- The degree column of Table 1 of arXiv:2610.09649, in the same vertex order. -/
def degTable : Fin 37 → ℕ :=
  ![0, 1, 22, 24, 25, 27, 28, 29,
    4, 6, 9, 17, 18, 19, 20, 21, 23, 26,
    2, 3, 5, 7, 8, 10, 11, 12, 13, 13, 13, 13, 13, 13, 13, 13, 14, 15, 16]

/-! ### Ground truth on the definitions -/

example : (Finset.univ.filter fun v : Fin 37 => part v = 0).card = 8 := by decide
example : (Finset.univ.filter fun v : Fin 37 => part v = 1).card = 10 := by decide
example : (Finset.univ.filter fun v : Fin 37 => part v = 2).card = 19 := by decide
example : (Finset.univ.filter fun v : Fin 37 => part v = 2 ∧ wt v = 1).card = 8 := by decide
example : wt 0 = -9 ∧ wt 7 = 9 ∧ wt 8 = -6 ∧ wt 17 = 8 ∧ wt 18 = -8 ∧ wt 36 = 7 := by decide
example : Gstar.Adj 2 14 ∧ ¬ Gstar.Adj 2 3 ∧ ¬ Gstar.Adj 0 17 := by decide

/-- The degree of a vertex of `G_*` is the number of vertices it is adjacent to. -/
theorem degree_eq_card_filter (v : Fin 37) :
    Gstar.degree v = (Finset.univ.filter fun u => Gstar.Adj v u).card := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]

/-- Every vertex of `G_*` has the degree listed in Table 1. -/
theorem degree_eq_degTable (v : Fin 37) : Gstar.degree v = degTable v := by
  rw [degree_eq_card_filter]
  revert v
  decide


/-- Proposition 4.1, first part: the degree set of `G_*` is exactly
`{0, 1, …, 29}`. -/
theorem degree_image_eq_range :
    (Finset.univ.image fun v => Gstar.degree v) = Finset.range 30 := by
  simp_rw [degree_eq_degTable]
  decide

/-- Proposition 4.1: `|V(G_*)| = 37` and the valency variety is `w(G_*) = 30`. -/
theorem card_eq_and_valencyVariety_eq :
    Fintype.card (Fin 37) = 37 ∧ valencyVariety Gstar = 30 := by
  refine ⟨Fintype.card_fin 37, ?_⟩
  rw [valencyVariety, degree_image_eq_range, Finset.card_range]

/-- The partition into `A, B, C` is a proper `3`-colouring of `G_*`. -/
def partColoring : Gstar.Coloring (Fin 3) :=
  Coloring.mk part fun h => h.1

/-- The vertex of weight `2` in `A`, the vertex of weight `2` in `B` and a
vertex of weight `1` in `C` form a triangle of `G_*`. -/
theorem isClique_triangle : Gstar.IsClique ({2, 14, 26} : Finset (Fin 37)) := by
  rw [isClique_iff, Set.Pairwise]
  decide

/-- Proposition 4.1: `χ(G_*) = 3`. -/
theorem chromaticNumber_Gstar : Gstar.chromaticNumber = 3 := by
  apply le_antisymm
  · exact (Coloring.colorable partColoring).chromaticNumber_le
  · have hcard : ({2, 14, 26} : Finset (Fin 37)).card = 3 := by decide
    have hle := isClique_triangle.card_le_chromaticNumber
    rw [hcard] at hle
    exact hle

/-- Remark after Proposition 4.1: the Melnikov bound of `G_*` is
`⌈⌊30/2⌋/(37 - 30)⌉ = ⌈15/7⌉ = 3`. -/
theorem melnikovBound_Gstar : melnikovBound 37 30 = 3 := by
  rw [melnikovBound, Nat.ceil_eq_iff (by norm_num)]
  norm_num

/-- Yang–Zeng (arXiv:2610.09649, Proposition 4.1 and Remark): `G_*` violates
Melnikov's strict inequality, since `χ(G_*) = 3 = ⌈⌊w/2⌋/(n - w)⌉`. -/
theorem Gstar_not_melnikov :
    ¬ ((melnikovBound (Fintype.card (Fin 37)) (valencyVariety Gstar) : ℕ) : ℕ∞) <
      Gstar.chromaticNumber := by
  rw [card_eq_and_valencyVariety_eq.1, card_eq_and_valencyVariety_eq.2, melnikovBound_Gstar,
    chromaticNumber_Gstar]
  exact lt_irrefl _

/-- Yang–Zeng (arXiv:2610.09649, Section 4.1): Melnikov's Conjecture 1.1 is
false; the 37-vertex graph `G_*` is a counterexample. -/
theorem not_melnikovConjecture : ¬ MelnikovConjecture := by
  intro h
  exact Gstar_not_melnikov (h (Fin 37) Gstar (by simp))

end Candidates.MelnikovValencyCounterexample
