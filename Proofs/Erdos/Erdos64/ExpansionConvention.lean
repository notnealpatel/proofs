/-
Erdős–Gyárfás problem 64 — floor/ceil vertex-expansion convention conversion.

CONTEXT AND EXACT CLAIM BOUNDARY. The Erdős64 reduction layer works with *vertex* expansion
predicates that are indexed by how much of the vertex set a set `S` may occupy. Two conventions
are in circulation:

* the **floor** convention `2 * S.card ≤ Fintype.card V`, i.e. `|S| ≤ ⌊n/2⌋`, and
* the **ceil** convention `2 * S.card ≤ Fintype.card V + 1`, i.e. `|S| ≤ ⌈n/2⌉`.

A class proof that is organised around the floor convention and then applies its hypothesis to a
set of size `⌈n/2⌉` (for odd `n`, the case that actually occurs when the deletion layer hands back
a set of size exactly `(n+1)/2`) needs a conversion lemma. This file supplies exactly one such
conversion and nothing else.

WHAT IS PROVED. `floorVertexExpands_to_ceilVertexExpands_half`: if every floor-admissible set
expands by the constant `h > 0`, and `n ≥ 4 + 4/h` (stated as `4 * h + 4 ≤ h * n`), then every
ceil-admissible set expands by the constant `h / 2`. The conversion is *lossy by a factor 2*, and
this is unavoidable at this level of generality: the deletion argument `S ↦ S.erase v` only gives
`|∂(S \ {v})| ≤ |∂S| + 1`, and the floor hypothesis applied to `S \ {v}` bounds `h * (|S| - 1)`
rather than `h * |S|`; the same-parameter statement is simply false — see
`not_ceilVertexExpands_top_fin_three`. Note that the factor-2 loss is *not* an artifact of the
hypothesis `4 * h + 4 ≤ h * n` being slightly lossy: for odd `n` the exact arithmetic threshold is
`n ≥ 3 + 4/h`, and the file deliberately assumes the uniform, parity-free, slightly stronger
`n ≥ 4 + 4/h` (the strict inequality `n < 2 * |S|` used in the proof needs one unit of slack, and
`h * (|S| - 2) ≥ 2` is what the hypothesis is spent on).

WHAT IS *NOT* PROVED HERE. No pruning lemma, no cycle lemma, no power-of-two cycle, no
Erdős–Gyárfás theorem, no minimal-counterexample statement, and no claim about any specific class
proof's constants. In particular the constants `4` and `4/h` are sufficient, not necessary, and
`h ≤ 1` and any degree bound are *not* assumed. The file contains one self-contained bridge and
its ground-truth checks.

GROUND TRUTH. `floorVertexExpands_top_one` shows the floor hypothesis is *inhabited* at `h = 1`
for complete graphs on any finite vertex type, so the main theorem is not vacuous;
`ceilVertexExpands_top_fin_nine` discharges all three hypotheses jointly at `K₉`, `h = 1`
(`n = 9 ≥ 8 = 4 + 4/1`) and invokes the full main conclusion, which yields ceil expansion at
`1/2`; and `not_ceilVertexExpands_top_fin_three` shows `CeilVertexExpands (⊤ : SimpleGraph (Fin 3))
1` is *false*, so the halving is genuine and the floor/ceil conventions are not interchangeable.
The `Fin 3` counterexample lies outside the hypothesis `4 * h + 4 ≤ h * n` (which fails there,
`8 ≤ 3`), so it does not contradict the main theorem: it certifies that the constant really
degrades, not that the conversion is broken.

The two `example`s at the end are membership sanity checks for `ExternalVertexBoundary`: a vertex
outside `S` adjacent to `S` lies in the boundary, and a vertex of `S` never does.
-/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

set_option autoImplicit false

namespace Erdos64

open SimpleGraph

universe u

variable {V : Type u}

/-! ### Definitions -/

section Definitions

variable [Fintype V] [DecidableEq V]

/-- The **external vertex boundary** of a finite vertex set `S` in a finite simple graph `G`:
the vertices outside `S` that have a neighbour in `S`. It is the union of the Mathlib neighbour
finsets `G.neighborFinset s` over `s ∈ S`, with `S` itself removed. -/
def ExternalVertexBoundary (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  (S.biUnion fun s => G.neighborFinset s) \ S

/-- **Floor vertex expansion** with constant `h`: every vertex set `S` occupying at most
`⌊n/2⌋` vertices (`2 * S.card ≤ Fintype.card V`) has an external vertex boundary of size at
least `h * S.card`. -/
def FloorVertexExpands (G : SimpleGraph V) [DecidableRel G.Adj] (h : ℝ) : Prop :=
  ∀ S : Finset V, 2 * S.card ≤ Fintype.card V →
    h * (S.card : ℝ) ≤ ((ExternalVertexBoundary G S).card : ℝ)

/-- **Ceil vertex expansion** with constant `h`: the same inequality as `FloorVertexExpands`,
but required for every vertex set `S` occupying at most `⌈n/2⌉` vertices
(`2 * S.card ≤ Fintype.card V + 1`). For odd `n` this is a strictly larger family of sets than
the floor convention; for even `n` the two admissibility conditions coincide. -/
def CeilVertexExpands (G : SimpleGraph V) [DecidableRel G.Adj] (h : ℝ) : Prop :=
  ∀ S : Finset V, 2 * S.card ≤ Fintype.card V + 1 →
    h * (S.card : ℝ) ≤ ((ExternalVertexBoundary G S).card : ℝ)

/-- Membership in the external vertex boundary: `x` is outside `S` and adjacent to some vertex
of `S`. -/
theorem mem_externalVertexBoundary {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V}
    {x : V} :
    x ∈ ExternalVertexBoundary G S ↔ (∃ s ∈ S, G.Adj s x) ∧ x ∉ S := by
  simp [ExternalVertexBoundary, Finset.mem_biUnion, SimpleGraph.mem_neighborFinset]

end Definitions

/-! ### The convention conversion -/

section Main

variable [Fintype V] [DecidableEq V]

/-- **Floor-to-ceil conversion, at half the constant.** Let `G` be a finite simple graph on `n`
vertices with `[DecidableRel G.Adj]`, let `h > 0`, and suppose `4 * h + 4 ≤ h * n`, i.e.
`n ≥ 4 + 4/h`. If every set of at most `⌊n/2⌋` vertices has external boundary at least
`h * |S|`, then every set of at most `⌈n/2⌉` vertices has external boundary at least
`(h / 2) * |S|`.

Proof. Let `S` be ceil-admissible. If `2 * |S| ≤ n` the floor hypothesis gives `h * |S| ≤ |∂S|`
and hence `(h/2) * |S| ≤ |∂S|` since `|S| ≥ 0`. Otherwise `n < 2 * |S| ≤ n + 1`, so `|S| ≥ 1`.
Choose `v ∈ S` and put `T := S.erase v`, so `|T| = |S| - 1` and `2 * |T| ≤ n`: the floor
hypothesis applies to `T` and yields `h * (|S| - 1) ≤ |∂T|`. Since every vertex of `∂T` is either
`v` itself or lies outside `S` while being adjacent to `T ⊆ S`, we have
`∂T ⊆ insert v (∂S)` and hence `|∂T| ≤ |∂S| + 1`. Finally `n < 2 * |S|` multiplied by `h > 0`
combined with `4 * h + 4 ≤ h * n` gives `2 * h + 2 ≤ h * |S|`, which is exactly the slack needed
to turn `h * (|S| - 1) ≤ |∂S| + 1` into `(h / 2) * |S| ≤ |∂S|`. -/
theorem floorVertexExpands_to_ceilVertexExpands_half (G : SimpleGraph V) [DecidableRel G.Adj]
    {h : ℝ} (hh : 0 < h) (hn : 4 * h + 4 ≤ h * (Fintype.card V : ℝ))
    (hG : FloorVertexExpands G h) : CeilVertexExpands G (h / 2) := by
  intro S hS
  by_cases hsmall : 2 * S.card ≤ Fintype.card V
  · have hfloor := hG S hsmall
    have hnonneg : (0 : ℝ) ≤ (S.card : ℝ) := by positivity
    nlinarith [hfloor, hnonneg, hh]
  · have hlarge : Fintype.card V < 2 * S.card := Nat.lt_of_not_ge hsmall
    have hSpos : 0 < S.card := by omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hSpos
    let T : Finset V := S.erase v
    have hTcard : T.card = S.card - 1 := Finset.card_erase_of_mem hv
    have hone : 1 ≤ S.card := by omega
    have hTsmall : 2 * T.card ≤ Fintype.card V := by rw [hTcard]; omega
    have hfloorT := hG T hTsmall
    have hTcardR : (T.card : ℝ) = (S.card : ℝ) - 1 := by
      rw [hTcard, Nat.cast_sub hone]
      norm_num
    have hTsub : T ⊆ S := by
      intro x hx
      exact (Finset.mem_erase.mp hx).2
    have hBset : ExternalVertexBoundary G T ⊆ insert v (ExternalVertexBoundary G S) := by
      intro x hx
      rw [mem_externalVertexBoundary] at hx
      obtain ⟨⟨t, htT, htx⟩, hxT⟩ := hx
      rw [Finset.mem_insert]
      by_cases hxv : x = v
      · exact Or.inl hxv
      · refine Or.inr ?_
        rw [mem_externalVertexBoundary]
        refine ⟨⟨t, hTsub htT, htx⟩, ?_⟩
        intro hxS
        exact hxT (Finset.mem_erase.mpr ⟨hxv, hxS⟩)
    have hBcardNat : (ExternalVertexBoundary G T).card ≤ (ExternalVertexBoundary G S).card + 1 :=
      calc (ExternalVertexBoundary G T).card
          ≤ (insert v (ExternalVertexBoundary G S)).card := Finset.card_le_card hBset
        _ ≤ (ExternalVertexBoundary G S).card + 1 := Finset.card_insert_le _ _
    have hB : ((ExternalVertexBoundary G T).card : ℝ)
        ≤ ((ExternalVertexBoundary G S).card : ℝ) + 1 := by
      exact_mod_cast hBcardNat
    have hfloorT' : h * ((S.card : ℝ) - 1) ≤ ((ExternalVertexBoundary G T).card : ℝ) := by
      rw [← hTcardR]
      exact hfloorT
    have hlargeR : (Fintype.card V : ℝ) < 2 * (S.card : ℝ) := by exact_mod_cast hlarge
    have hmul : h * (Fintype.card V : ℝ) < h * (2 * (S.card : ℝ)) :=
      mul_lt_mul_of_pos_left hlargeR hh
    have hkey : 2 * h + 2 ≤ h * (S.card : ℝ) := by nlinarith [hn, hmul]
    nlinarith [hkey, hfloorT', hB]

end Main

/-! ### Ground truth -/

section GroundTruth

variable [Fintype V] [DecidableEq V]

/-- For the complete graph on a finite vertex type, the external boundary of a nonempty set `S`
is its complement `univ \ S`: every vertex outside `S` is adjacent to every vertex of `S`. (This
is the only place where the complete-graph computation is needed; the main theorem does not
mention it.) -/
theorem externalVertexBoundary_top_of_nonempty {S : Finset V} (hS : S.Nonempty) :
    ExternalVertexBoundary (⊤ : SimpleGraph V) S = Finset.univ \ S := by
  ext x
  rw [mem_externalVertexBoundary]
  constructor
  · rintro ⟨-, hxS⟩
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxS⟩
  · intro hx
    rw [Finset.mem_sdiff] at hx
    obtain ⟨s, hs⟩ := hS
    refine ⟨⟨s, hs, ?_⟩, hx.2⟩
    rw [SimpleGraph.top_adj]
    exact fun h => hx.2 (h ▸ hs)

/-- Ground truth: the complete graph on any finite vertex type satisfies *floor* vertex
expansion with constant `1`. Indeed `∂S = univ \ S` for nonempty `S` (and `∂∅ = ∅`), so the
claim is `|S| ≤ n - |S|`, which is precisely the floor admissibility hypothesis
`2 * |S| ≤ n`. -/
theorem floorVertexExpands_top_one : FloorVertexExpands (⊤ : SimpleGraph V) 1 := by
  intro S hS
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · simp [ExternalVertexBoundary]
  · rw [externalVertexBoundary_top_of_nonempty hSne]
    have hcard : (Finset.univ \ S).card = Fintype.card V - S.card :=
      Finset.card_sdiff_of_subset (Finset.subset_univ S)
    rw [hcard]
    have hsub : ((Fintype.card V - S.card : ℕ) : ℝ)
        = (Fintype.card V : ℝ) - (S.card : ℝ) := by
      rw [Nat.cast_sub (by omega : S.card ≤ Fintype.card V)]
    rw [hsub]
    have hle : S.card ≤ Fintype.card V - S.card := by omega
    have hleR : (S.card : ℝ) ≤ ((Fintype.card V - S.card : ℕ) : ℝ) := by exact_mod_cast hle
    rw [hsub] at hleR
    simpa using hleR

/-- Ground truth: on the complete graph `K₉` with `h = 1` all three hypotheses of
`floorVertexExpands_to_ceilVertexExpands_half` hold jointly (`0 < 1`, `4 * 1 + 4 = 8 ≤ 9 = 1 * 9`,
and `floorVertexExpands_top_one`), so the *full* main conclusion applies and gives ceil vertex
expansion of `K₉` with constant `1 / 2`. -/
theorem ceilVertexExpands_top_fin_nine :
    CeilVertexExpands (⊤ : SimpleGraph (Fin 9)) (1 / 2) :=
  floorVertexExpands_to_ceilVertexExpands_half (⊤ : SimpleGraph (Fin 9))
    (by norm_num) (by norm_num) floorVertexExpands_top_one

/-- Ground truth: the same-parameter statement `FloorVertexExpands G h → CeilVertexExpands G h`
is **false**, so the halving in `floorVertexExpands_to_ceilVertexExpands_half` is not cosmetic.
Witness: the complete graph `K₃` and `h = 1`. The set `S = {0, 1}` is ceil-admissible
(`2 * 2 = 4 ≤ 3 + 1`) and its external boundary is `{2}`, of size `1 < 2 = 1 * |S|`. Note that the
hypothesis `4 * h + 4 ≤ h * n` of the main theorem fails here (`8 ≤ 3` is false), so this
counterexample shows that the constant degrades and does not contradict the main theorem. -/
theorem not_ceilVertexExpands_top_fin_three : ¬ CeilVertexExpands (⊤ : SimpleGraph (Fin 3)) 1 := by
  intro h
  have hadm : 2 * ({0, 1} : Finset (Fin 3)).card ≤ Fintype.card (Fin 3) + 1 := by decide
  have hconc := h ({0, 1} : Finset (Fin 3)) hadm
  rw [externalVertexBoundary_top_of_nonempty
    (by decide : ({0, 1} : Finset (Fin 3)).Nonempty)] at hconc
  have hcard : (Finset.univ \ ({0, 1} : Finset (Fin 3))).card = 1 := by decide
  have hcard2 : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  rw [hcard, hcard2] at hconc
  norm_num at hconc

/-- Membership sanity check: `0` lies in the external boundary of `{1}` in `K₃`, since `0 ∉ {1}`
and `0` is adjacent to `1`. -/
example : (0 : Fin 3) ∈ ExternalVertexBoundary (⊤ : SimpleGraph (Fin 3)) ({1} : Finset (Fin 3)) := by
  rw [mem_externalVertexBoundary]
  exact ⟨⟨1, by simp, by simp [SimpleGraph.top_adj]⟩, by simp⟩

/-- Membership sanity check: a vertex of `S` never lies in the external boundary of `S`, since
the boundary removes `S` from the neighbour union. -/
example : (0 : Fin 3) ∉ ExternalVertexBoundary (⊤ : SimpleGraph (Fin 3)) ({0} : Finset (Fin 3)) := by
  intro hx
  rw [mem_externalVertexBoundary] at hx
  exact hx.2 (by simp)

end GroundTruth

end Erdos64
