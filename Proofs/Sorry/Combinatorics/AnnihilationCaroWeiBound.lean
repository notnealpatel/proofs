/-
# An annihilation-number Caro-Wei bound

## Source

Chakshu Gupta, "An annihilation-number Caro-Wei bound: a TxGraffiti
conjecture and an independence-number bracket", arXiv:2606.29553
(math.CO).  Retrieved with `fetch 2606.29553`, 2026-10-21.

Statement location: Section 2 (Results), Theorem 1, together with the
bracket of Corollary 4 and the Remark "Refining the Caro-Wei bracket"
(residue-free form `W ≤ α ≤ a ≤ (Δ+1)/2 · W`).

Verbatim informal claim (Theorem 1):

> Every graphic degree sequence with maximum degree `Δ ≥ 1` satisfies
> `a ≤ (Δ+1)/2 · W`.

where, for the nondecreasing degree sequence `d_1 ≤ ⋯ ≤ d_n` of a graph
with `m` edges, `a` (the annihilation number) is "the largest integer `j`
such that `d_1 + ⋯ + d_j ≤ m`" and `W = ∑_i 1/(d_i+1)` is the Caro-Wei
sum.  The bracket used in the Remark is `W ≤ α ≤ a ≤ (Δ+1)/2 · W`, built
from the Caro-Wei bound `α ≥ W`, Pepper's annihilation bound `α ≤ a`,
and Theorem 1.

## Status

Proved in the paper (elementary; the proof is reproduced here).  The
paper is the source of Theorem 1; `α ≥ W` (Caro 1979, Wei 1981) and
`α ≤ a` (Pepper 2009) are classical.

## Definitional fidelity

* `annihilationNumber G` is the maximum cardinality of a vertex `Finset`
  `S` with `∑_{v ∈ S} deg v ≤ #E`.  This avoids sorting: a `j`-set of
  minimum degree sum consists of `j` smallest degrees, so the maximum is
  the paper's largest `j` with `d_1 + ⋯ + d_j ≤ m`.  The bridge to the
  sorted-prefix definition is `annihilationNumber_eq_sortedPrefix` below.
* `caroWeiSum G = ∑_v 1/(deg v + 1)` in `ℝ`.
* `Δ` is Mathlib's `SimpleGraph.maxDegree`, `α` is Mathlib's
  `SimpleGraph.indepNum`.

The Caro-Wei lower bound `W ≤ α` is already proved in the production
module `Combinatorics.CaroWei` (`ErdosCandidates.CaroWei.exists_independent_set`).
That module currently has no built `.olean` in this workspace (and a
build attempt failed with a thread-creation error under the memory cap),
so its short proof is reproduced verbatim as private lemmas here; a
later promotion may replace them by the import.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.AnnihilationCaroWeiBound

open Finset

universe u

/-! ## Definitions -/

/-- The annihilation number of a finite simple graph: the largest cardinality of a
vertex set `S` whose degree sum is at most the number of edges,
`∑_{v ∈ S} deg v ≤ #E(G)`. Equivalent to the paper's sorted-prefix definition
(`annihilationNumber_eq_sortedPrefix`). -/
def annihilationNumber {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℕ :=
  ((univ : Finset (Finset V)).filter
    (fun S => ∑ v ∈ S, G.degree v ≤ #G.edgeFinset)).sup Finset.card

/-- The Caro-Wei sum `W(G) = ∑_v 1/(deg v + 1)`. -/
noncomputable def caroWeiSum {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℝ :=
  ∑ v, 1 / ((G.degree v : ℝ) + 1)


/-- The degree sequence of `G` in nondecreasing order, `d_1 ≤ d_2 ≤ ⋯ ≤ d_n`. -/
def sortedDegrees {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    List ℕ :=
  ((univ : Finset V).val.map (fun v => G.degree v)).sort

/-- The paper's definition of the annihilation number: the largest `j ≤ n` such that
`d_1 + ⋯ + d_j ≤ m` for the nondecreasing degree sequence `d_1 ≤ ⋯ ≤ d_n` and
`m = #E(G)`. -/
def annihilationNumberSorted {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℕ :=
  Nat.findGreatest (fun j => ((sortedDegrees G).take j).sum ≤ #G.edgeFinset) (Fintype.card V)

/-! ## Ground truth -/

/-- The sorted degree sequence of `K₄` is `3,3,3,3`. -/
theorem sortedDegrees_top_fin4 : sortedDegrees (⊤ : SimpleGraph (Fin 4)) = [3, 3, 3, 3] := by
  have hdeg : ∀ v : Fin 4, (⊤ : SimpleGraph (Fin 4)).degree v = 3 := by decide
  have hm : (univ : Finset (Fin 4)).val.map (fun v => (⊤ : SimpleGraph (Fin 4)).degree v) =
      3 ::ₘ 3 ::ₘ 3 ::ₘ 3 ::ₘ 0 := by
    simp only [hdeg]
    decide
  rw [sortedDegrees, hm, Multiset.sort_cons, Multiset.sort_cons, Multiset.sort_cons,
    Multiset.sort_cons, Multiset.sort_zero] <;> simp

/-- The paper's sorted-prefix annihilation number of `K₄` is `2`. -/
example : annihilationNumberSorted (⊤ : SimpleGraph (Fin 4)) = 2 := by
  rw [annihilationNumberSorted, sortedDegrees_top_fin4]
  decide

/-- The star `K_{1,3}` on `Fin 4` with centre `0`. -/
def star4 : SimpleGraph (Fin 4) := SimpleGraph.fromRel (fun a b => a = 0 ∧ b ≠ 0)

/-- Decidable adjacency for `star4`, inherited from `SimpleGraph.fromRel`. -/
instance : DecidableRel star4.Adj := fun a b => by unfold star4; infer_instance

/-- The star `K_{1,3}` (degrees `1,1,1,3`, three edges) has `a = 3`: the three
leaves have degree sum `3 ≤ 3`. -/
example : annihilationNumber star4 = 3 := by decide

/-- The sorted degree sequence of the star `K_{1,3}` is `1,1,1,3`. -/
theorem sortedDegrees_star4 : sortedDegrees star4 = [1, 1, 1, 3] := by
  have hm : (univ : Finset (Fin 4)).val.map (fun v => star4.degree v) =
      1 ::ₘ 1 ::ₘ 1 ::ₘ 3 ::ₘ 0 := by
    decide
  rw [sortedDegrees, hm, Multiset.sort_cons, Multiset.sort_cons, Multiset.sort_cons,
    Multiset.sort_cons, Multiset.sort_zero] <;> simp

/-- The paper's sorted-prefix annihilation number of the star `K_{1,3}` is `3`,
agreeing with the `Finset` definition. -/
example : annihilationNumberSorted star4 = 3 := by
  rw [annihilationNumberSorted, sortedDegrees_star4]
  decide

/-- `K₄` (degrees `3,3,3,3`, six edges): `a(K₄) = 2`, matching the paper's
Corollary 2 (`a = 2` for `K₄`). -/
example : annihilationNumber (⊤ : SimpleGraph (Fin 4)) = 2 := by decide

/-- The edgeless graph on three vertices has `a = 3` (the paper's remark that
`Δ = 0` gives `a = n`). -/
example : annihilationNumber (⊥ : SimpleGraph (Fin 3)) = 3 := by decide

/-- `K₄` has Caro-Wei sum `W = 4 · 1/4 = 1`. -/
example : caroWeiSum (⊤ : SimpleGraph (Fin 4)) = 1 := by
  have hdeg : ∀ v : Fin 4, (⊤ : SimpleGraph (Fin 4)).degree v = 3 := by decide
  simp only [caroWeiSum, hdeg]
  norm_num

/-! ## The degree-sequence lemma (proof of Theorem 1) -/

/-- Core degree-sequence inequality behind Theorem 1 of arXiv:2606.29553: if every
`d i ≤ Δ` with `1 ≤ Δ`, and the "head" `H` has degree sum at most that of its
complement, then `|H| ≤ (Δ+1)/2 · ∑_i 1/(d_i+1)`. -/
theorem card_le_caroWei {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℕ) (Δ : ℕ)
    (hΔ : 1 ≤ Δ) (hd : ∀ i, d i ≤ Δ) (H : Finset ι)
    (hH : ∑ i ∈ H, d i ≤ ∑ i ∈ Hᶜ, d i) :
    (#H : ℝ) ≤ ((Δ : ℝ) + 1) / 2 * ∑ i, 1 / ((d i : ℝ) + 1) := by
  have hΔR : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  set c : ℝ := (Δ : ℝ) * ((Δ : ℝ) + 1) with hc
  have hcpos : 0 < c := by positivity
  have hdR (i : ι) : (d i : ℝ) ≤ Δ := by exact_mod_cast hd i
  -- pointwise inequality on the head: `2/(Δ+1) - k/(Δ(Δ+1)) ≤ 1/(k+1)`
  have hhead (i : ι) : 2 / ((Δ : ℝ) + 1) - (d i : ℝ) / c ≤ 1 / ((d i : ℝ) + 1) := by
    have hk : (0 : ℝ) ≤ d i := by positivity
    have hint : (0 : ℤ) ≤ ((Δ : ℤ) - d i) * ((Δ : ℤ) - d i - 1) := by
      have hdi := hd i
      rcases Nat.eq_or_lt_of_le hdi with h | h
      · rw [h]; simp
      · apply mul_nonneg <;> omega
    have hintR : (0 : ℝ) ≤ ((Δ : ℝ) - d i) * ((Δ : ℝ) - d i - 1) := by exact_mod_cast hint
    rw [hc, div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  -- tail inequality: `k/(Δ(Δ+1)) ≤ 1/(k+1)`
  have htail (i : ι) : (d i : ℝ) / c ≤ 1 / ((d i : ℝ) + 1) := by
    have hk : (0 : ℝ) ≤ d i := by positivity
    rw [hc, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hdR i]
  have hHR : (∑ i ∈ H, (d i : ℝ)) ≤ ∑ i ∈ Hᶜ, (d i : ℝ) := by exact_mod_cast hH
  have hsplit : ∑ i, 1 / ((d i : ℝ) + 1) =
      ∑ i ∈ H, 1 / ((d i : ℝ) + 1) + ∑ i ∈ Hᶜ, 1 / ((d i : ℝ) + 1) :=
    (Finset.sum_add_sum_compl H _).symm
  have hHsum : ∑ i ∈ H, (2 / ((Δ : ℝ) + 1) - (d i : ℝ) / c) ≤ ∑ i ∈ H, 1 / ((d i : ℝ) + 1) :=
    Finset.sum_le_sum fun i _ => hhead i
  have hTsum : ∑ i ∈ Hᶜ, (d i : ℝ) / c ≤ ∑ i ∈ Hᶜ, 1 / ((d i : ℝ) + 1) :=
    Finset.sum_le_sum fun i _ => htail i
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_div] at hHsum
  rw [← Finset.sum_div] at hTsum
  have hW : 2 * (#H : ℝ) / ((Δ : ℝ) + 1) ≤ ∑ i, 1 / ((d i : ℝ) + 1) := by
    have hdiff : (∑ i ∈ H, (d i : ℝ)) / c ≤ (∑ i ∈ Hᶜ, (d i : ℝ)) / c :=
      div_le_div_of_nonneg_right hHR hcpos.le
    have hcomm : (#H : ℝ) * (2 / ((Δ : ℝ) + 1)) = 2 * (#H : ℝ) / ((Δ : ℝ) + 1) := by ring
    rw [hsplit]
    linarith
  rw [div_le_iff₀ (by positivity)] at hW
  nlinarith


/-- An independent vertex set has degree sum at most the number of edges, since the
edge sets incident to its vertices are pairwise disjoint. -/
theorem sum_degree_le_card_edgeFinset_of_isIndepSet {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (hS : G.IsIndepSet (S : Set V)) : ∑ v ∈ S, G.degree v ≤ #G.edgeFinset := by
  have hdisj : (S : Set V).PairwiseDisjoint (fun v => G.incidenceFinset v) := by
    intro v hv w hw hvw
    rw [Function.onFun, Finset.disjoint_left]
    intro e hev hew
    rw [SimpleGraph.mem_incidenceFinset] at hev hew
    have hempty := G.incidenceSet_inter_incidenceSet_of_not_adj (hS hv hw hvw) hvw
    have hmem : e ∈ G.incidenceSet v ∩ G.incidenceSet w := ⟨hev, hew⟩
    rw [hempty] at hmem
    exact hmem
  calc ∑ v ∈ S, G.degree v = ∑ v ∈ S, #(G.incidenceFinset v) := by
        simp only [SimpleGraph.card_incidenceFinset_eq_degree]
    _ = #(S.biUnion (fun v => G.incidenceFinset v)) := (card_biUnion hdisj).symm
    _ ≤ #G.edgeFinset := card_le_card (biUnion_subset.2 fun v _ => G.incidenceFinset_subset v)

/-- The annihilation number is attained: some vertex set `S` with
`∑_{v ∈ S} deg v ≤ #E` has cardinality `annihilationNumber G`. -/
theorem exists_card_eq_annihilationNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ S : Finset V, ∑ v ∈ S, G.degree v ≤ #G.edgeFinset ∧ #S = annihilationNumber G := by
  have hne : ((univ : Finset (Finset V)).filter
      (fun S => ∑ v ∈ S, G.degree v ≤ #G.edgeFinset)).Nonempty :=
    ⟨∅, by simp⟩
  obtain ⟨S, hS, hSeq⟩ := exists_mem_eq_sup _ hne Finset.card
  exact ⟨S, (mem_filter.1 hS).2, hSeq.symm⟩

/-- Any vertex set with degree sum at most `#E` has cardinality at most the
annihilation number. -/
theorem card_le_annihilationNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (hS : ∑ v ∈ S, G.degree v ≤ #G.edgeFinset) : #S ≤ annihilationNumber G :=
  le_sup (f := Finset.card) (mem_filter.2 ⟨mem_univ S, hS⟩)

/-! ## Agreement with the sorted-prefix definition -/

/-- In a nondecreasing list `L`, the sum of the first `|N|` entries is at most the sum
of any sub-multiset `N ≤ L`: the `j` smallest values minimise the sum of `j` values. -/
theorem sum_take_card_le_sum_of_le (L : List ℕ) (hL : L.Pairwise (· ≤ ·))
    (N : Multiset ℕ) (hN : N ≤ (L : Multiset ℕ)) :
    (L.take (Multiset.card N)).sum ≤ N.sum := by
  induction L generalizing N with
  | nil =>
    have hN0 : N = 0 := Multiset.le_zero.1 hN
    subst hN0
    simp
  | cons a t ih =>
    rw [List.pairwise_cons] at hL
    obtain ⟨hat, ht⟩ := hL
    rw [← Multiset.cons_coe] at hN
    rcases Multiset.empty_or_exists_mem N with hN0 | ⟨x, hx⟩
    · subst hN0
      simp
    by_cases ha : a ∈ N
    · have h1 : N.erase a ≤ t := Multiset.erase_le_iff_le_cons.2 hN
      have hc : Multiset.card N = Multiset.card (N.erase a) + 1 :=
        (Multiset.card_erase_add_one ha).symm
      have hs : a + (N.erase a).sum = N.sum := Multiset.sum_erase ha
      have hih := ih ht (N.erase a) h1
      rw [hc, List.take_succ_cons, List.sum_cons]
      omega
    · have h1 : N ≤ t := (Multiset.le_cons_of_notMem ha).1 hN
      have hxt : x ∈ t := Multiset.mem_coe.1 (Multiset.mem_of_le h1 hx)
      have h2 : N.erase x ≤ t := (Multiset.erase_le x N).trans h1
      have hc : Multiset.card N = Multiset.card (N.erase x) + 1 :=
        (Multiset.card_erase_add_one hx).symm
      have hs : x + (N.erase x).sum = N.sum := Multiset.sum_erase hx
      have hax : a ≤ x := hat x hxt
      have hih := ih ht (N.erase x) h2
      rw [hc, List.take_succ_cons, List.sum_cons]
      omega

/-- Every sub-multiset of `f '' s` (with multiplicity) is the image of a subset of `s`. -/
theorem exists_subset_map_val_eq {ι : Type*} [DecidableEq ι] (f : ι → ℕ) (s : Finset ι)
    (P : Multiset ℕ) (hP : P ≤ s.val.map f) : ∃ T ⊆ s, T.val.map f = P := by
  induction s using Finset.induction_on generalizing P with
  | empty =>
    have hP0 : P = 0 := Multiset.le_zero.1 (by simpa using hP)
    exact ⟨∅, Finset.empty_subset _, by simp [hP0]⟩
  | insert a s has ih =>
    rw [Finset.insert_val_of_notMem has, Multiset.map_cons] at hP
    by_cases hfa : f a ∈ P
    · obtain ⟨T, hTs, hTP⟩ := ih (P.erase (f a)) (Multiset.erase_le_iff_le_cons.2 hP)
      have haT : a ∉ T := fun haT => has (hTs haT)
      refine ⟨insert a T, Finset.insert_subset_insert a hTs, ?_⟩
      rw [Finset.insert_val_of_notMem haT, Multiset.map_cons, hTP, Multiset.cons_erase hfa]
    · obtain ⟨T, hTs, hTP⟩ := ih P ((Multiset.le_cons_of_notMem hfa).1 hP)
      exact ⟨T, hTs.trans (Finset.subset_insert a s), hTP⟩

/-- The `Finset` definition of the annihilation number agrees with the paper's
sorted-prefix definition: the largest `j` with `d_1 + ⋯ + d_j ≤ m`. -/
theorem annihilationNumber_eq_sortedPrefix {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    annihilationNumber G = annihilationNumberSorted G := by
  set L := sortedDegrees G with hLdef
  have hLsorted : L.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  have hLval : (L : Multiset ℕ) = (univ : Finset V).val.map (fun v => G.degree v) := Multiset.sort_eq _ _
  have hLlen : L.length = Fintype.card V := by
    rw [hLdef, sortedDegrees, Multiset.length_sort, Multiset.card_map, ← Finset.card_def,
      Finset.card_univ]
  apply le_antisymm
  · obtain ⟨S, hS, hSeq⟩ := exists_card_eq_annihilationNumber G
    have hSle : S.val.map (fun v => G.degree v) ≤ (L : Multiset ℕ) := by
      rw [hLval]
      exact Multiset.map_le_map (Finset.val_le_iff.2 (Finset.subset_univ S))
    have hpre := sum_take_card_le_sum_of_le L hLsorted _ hSle
    have hsumS : (S.val.map (fun v => G.degree v)).sum = ∑ v ∈ S, G.degree v := rfl
    rw [Multiset.card_map, ← Finset.card_def, hsumS] at hpre
    rw [← hSeq]
    exact Nat.le_findGreatest (Finset.card_le_univ S) (hpre.trans hS)
  · set j := annihilationNumberSorted G with hjdef
    have hjle : j ≤ Fintype.card V := Nat.findGreatest_le _
    have hj : (L.take j).sum ≤ #G.edgeFinset :=
      Nat.findGreatest_spec (P := fun j => (L.take j).sum ≤ #G.edgeFinset)
        (Nat.zero_le _) (by simp)
    have hsub : ((L.take j : List ℕ) : Multiset ℕ) ≤ (univ : Finset V).val.map (fun v => G.degree v) := by
      rw [← hLval]
      exact Multiset.coe_le.2 (List.take_sublist j L).subperm
    obtain ⟨T, -, hT⟩ := exists_subset_map_val_eq (fun v => G.degree v) univ _ hsub
    have hTcard : #T = j := by
      rw [Finset.card_def, ← Multiset.card_map (fun v => G.degree v), hT, Multiset.coe_card,
        List.length_take, hLlen]
      exact min_eq_left hjle
    have hTsum : ∑ v ∈ T, G.degree v = (L.take j).sum := by
      rw [← Finset.sum_map_val, hT, Multiset.sum_coe]
    rw [← hTcard]
    exact card_le_annihilationNumber G T (hTsum ▸ hj)

/-! ## Main results -/

/-- **Theorem 1 of arXiv:2606.29553.** For a finite simple graph with maximum degree
`Δ ≥ 1`, the annihilation number satisfies `a ≤ (Δ+1)/2 · W`, where
`W = ∑_v 1/(deg v + 1)` is the Caro-Wei sum. -/
theorem annihilationNumber_le_caroWeiSum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : 1 ≤ G.maxDegree) :
    (annihilationNumber G : ℝ) ≤ ((G.maxDegree : ℝ) + 1) / 2 * caroWeiSum G := by
  obtain ⟨S, hS, hSeq⟩ := exists_card_eq_annihilationNumber G
  have htotal : ∑ v ∈ S, G.degree v + ∑ v ∈ Sᶜ, G.degree v = 2 * #G.edgeFinset := by
    rw [sum_add_sum_compl, G.sum_degrees_eq_twice_card_edges]
  have hhead : ∑ v ∈ S, G.degree v ≤ ∑ v ∈ Sᶜ, G.degree v := by omega
  rw [← hSeq]
  exact card_le_caroWei (fun v => G.degree v) G.maxDegree hΔ G.degree_le_maxDegree S hhead

/-- Pepper's bound, as used in arXiv:2606.29553: the independence number is at most
the annihilation number, `α ≤ a`. -/
theorem indepNum_le_annihilationNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : G.indepNum ≤ annihilationNumber G := by
  obtain ⟨S, hSmax⟩ := SimpleGraph.maximumIndepSet_exists (G := G)
  rw [← SimpleGraph.maximumIndepSet_card_eq_indepNum S hSmax]
  exact card_le_annihilationNumber G S
    (sum_degree_le_card_edgeFinset_of_isIndepSet G S hSmax.1)

/-! ### The Caro-Wei lower bound (reproduced from `Combinatorics.CaroWei`) -/

private theorem degree_induce_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R : Set V)
    [DecidablePred (· ∈ R)] (x : R) : (G.induce R).degree x ≤ G.degree x := by
  classical
  have h := Finset.card_le_card
    (Finset.inter_subset_left (s₁ := G.neighborFinset x) (s₂ := R.toFinset))
  rw [← G.map_neighborFinset_induce x, Finset.card_map] at h
  exact h

private theorem exists_of_card (n : ℕ) :
    ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n →
      ∃ S : Finset V, G.IsIndepSet (S : Set V) ∧
        (∑ v : V, (1 : ℝ) / ((G.degree v : ℝ) + 1)) ≤ (S.card : ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ G _ hcard
    classical
    by_cases hV : IsEmpty V
    · letI := hV
      exact ⟨∅, by simp [SimpleGraph.IsIndepSet], by simp⟩
    · haveI : Nonempty V := not_isEmpty_iff.mp hV
      obtain ⟨v, _, hv⟩ := Finset.exists_min_image Finset.univ (fun x => G.degree x) Finset.univ_nonempty
      have hmin (x : V) : G.degree v ≤ G.degree x := hv x (Finset.mem_univ x)
      let C : Finset V := insert v (G.neighborFinset v)
      let R := {x : V // x ∉ C}
      let H : SimpleGraph R := G.induce {x | x ∉ C}
      have hvC : v ∈ C := Finset.mem_insert_self _ _
      have hsmall : Fintype.card R < n := by
        rw [← hcard]
        exact Fintype.card_subtype_lt (by simpa using hvC)
      have hCcard : C.card = G.degree v + 1 := by
        simp [C, G.card_neighborFinset_eq_degree]
      have hCweight : (∑ x ∈ C, (1 : ℝ) / ((G.degree x : ℝ) + 1)) ≤ 1 := by
        calc
          _ ≤ ∑ _x ∈ C, (1 : ℝ) / ((G.degree v : ℝ) + 1) := by
            apply Finset.sum_le_sum
            intro x _
            apply one_div_le_one_div_of_le (by positivity)
            exact_mod_cast Nat.add_le_add_right (hmin x) 1
          _ = 1 := by
            rw [Finset.sum_const, hCcard, nsmul_eq_mul]
            push_cast
            field_simp
      have hRweight : (∑ x : R, (1 : ℝ) / ((G.degree x : ℝ) + 1)) ≤
          ∑ x : R, (1 : ℝ) / ((H.degree x : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro x _
        apply one_div_le_one_div_of_le (by positivity)
        have hd : H.degree x ≤ G.degree x := degree_induce_le G {x | x ∉ C} x
        exact_mod_cast Nat.add_le_add_right hd 1
      obtain ⟨T, hTind, hTweight⟩ := ih (Fintype.card R) hsmall R H rfl
      let e : R ↪ V := Function.Embedding.subtype (fun x => x ∉ C)
      let U : Finset V := T.map e
      have hU (x : V) (hx : x ∈ U) : x ∉ C := by
        obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hx
        exact y.property
      have hvU : v ∉ U := fun hvU => hU v hvU hvC
      have hUind : G.IsIndepSet (U : Set V) := by
        intro x hx y hy hxy
        obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
        obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
        have hab : a ≠ b := fun hab => hxy (congrArg e hab)
        exact hTind ha hb hab
      have hvnotadj (x : V) (hx : x ∈ U) : ¬ G.Adj v x := by
        intro hadj
        exact hU x hx (Finset.mem_insert_of_mem ((G.mem_neighborFinset v x).mpr hadj))
      have hSind : G.IsIndepSet ((insert v U : Finset V) : Set V) := by
        intro x hx y hy hxy
        simp only [Finset.mem_coe, Finset.mem_insert] at hx hy
        rcases hx with rfl | hx
        · rcases hy with rfl | hy
          · exact (hxy rfl).elim
          · exact hvnotadj y hy
        · rcases hy with rfl | hy
          · exact fun hadj => hvnotadj x hx hadj.symm
          · exact hUind hx hy hxy
      have hScard : (insert v U).card = T.card + 1 := by
        rw [Finset.card_insert_of_notMem hvU, Finset.card_map]
      have hpart : (∑ x ∈ C, (1 : ℝ) / ((G.degree x : ℝ) + 1)) +
          (∑ x : R, (1 : ℝ) / ((G.degree x : ℝ) + 1)) =
          ∑ x : V, (1 : ℝ) / ((G.degree x : ℝ) + 1) := by
        rw [Finset.sum_subtype C (fun _ => Iff.rfl)]
        exact Fintype.sum_subtype_add_sum_subtype (fun x => x ∈ C)
          (fun x => (1 : ℝ) / ((G.degree x : ℝ) + 1))
      refine ⟨insert v U, hSind, ?_⟩
      rw [← hpart, hScard, Nat.cast_add, Nat.cast_one]
      linarith

/-- The Caro-Wei bound `W ≤ α`: the Caro-Wei sum is at most the independence
number. -/
theorem caroWeiSum_le_indepNum {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : caroWeiSum G ≤ (G.indepNum : ℝ) := by
  obtain ⟨S, hSind, hSW⟩ := exists_of_card (Fintype.card V) V G rfl
  have hcard : #S ≤ G.indepNum := hSind.card_le_indepNum
  calc caroWeiSum G ≤ (#S : ℝ) := hSW
    _ ≤ (G.indepNum : ℝ) := by exact_mod_cast hcard

/-- **Residue-free bracket (arXiv:2606.29553, Corollary 4 / Remark).** For a finite
simple graph with maximum degree `Δ ≥ 1`,
`W ≤ α ≤ a ≤ (Δ+1)/2 · W`, where `W` is the Caro-Wei sum, `α` the independence
number and `a` the annihilation number. -/
theorem caroWei_bracket {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hΔ : 1 ≤ G.maxDegree) :
    caroWeiSum G ≤ (G.indepNum : ℝ) ∧ G.indepNum ≤ annihilationNumber G ∧
      (annihilationNumber G : ℝ) ≤ ((G.maxDegree : ℝ) + 1) / 2 * caroWeiSum G :=
  ⟨caroWeiSum_le_indepNum G, indepNum_le_annihilationNumber G,
    annihilationNumber_le_caroWeiSum G hΔ⟩

/-- Non-vacuity and sharpness: `K₄` satisfies the hypothesis `1 ≤ Δ`, and Theorem 1
holds with equality there (`a = 2 = (3+1)/2 · 1`). -/
example : 1 ≤ (⊤ : SimpleGraph (Fin 4)).maxDegree ∧
    (annihilationNumber (⊤ : SimpleGraph (Fin 4)) : ℝ) =
      (((⊤ : SimpleGraph (Fin 4)).maxDegree : ℝ) + 1) / 2 *
        caroWeiSum (⊤ : SimpleGraph (Fin 4)) := by
  have hmax : (⊤ : SimpleGraph (Fin 4)).maxDegree = 3 := by
    rw [SimpleGraph.maxDegree_top]
    rfl
  have ha : annihilationNumber (⊤ : SimpleGraph (Fin 4)) = 2 := by decide
  have hdeg : ∀ v : Fin 4, (⊤ : SimpleGraph (Fin 4)).degree v = 3 := by decide
  refine ⟨by omega, ?_⟩
  simp only [ha, hmax, caroWeiSum, hdeg]
  norm_num

end Candidates.AnnihilationCaroWeiBound
