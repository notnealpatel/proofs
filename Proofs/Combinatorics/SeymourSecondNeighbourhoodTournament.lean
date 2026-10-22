/-
# Seymour's second neighbourhood conjecture for tournaments (Dean's conjecture)

Seymour's second neighbourhood conjecture (1990) asks for a vertex `v`
of a nonempty oriented graph with `|N⁺(v)| ≤ |N⁺⁺(v)|`; see also
MathOverflow answer https://mathoverflow.net/a/102040. This file treats
only tournaments (Dean's conjecture), proved by D. C. Fisher,
J. Graph Theory 23 (1996). The proof follows F. Havet and S. Thomassé,
*Median orders of tournaments: a tool for the second neighborhood problem
and Sumner's conjecture*, J. Graph Theory 35 (2000), 244–256.

## What is formalized

* `havetThomasse_card_outNbhd_le_card_goodSet`: if `σ : Fin (n + 1) ≃ V` is a
  median order of a tournament (an ordering maximizing the number of forward
  arcs), then its last vertex `d` (the *feed vertex*) satisfies
  `|N⁺(d)| ≤ |G|`, where `G` is the set of in-neighbours `w` of `d` that are
  reached by a path `d → u → w` with `u` earlier than `w` in the order.
* `goodSet_subset_secondNbhd`: `G ⊆ N⁺⁺(d)`.
* `havetThomasse`: `|N⁺(d)| ≤ |N⁺⁺(d)|` for the feed vertex of a median order.
* `dean_conjecture`: every nonempty finite tournament has a vertex `v` with
  `|N⁺(v)| ≤ |N⁺⁺(v)|`.

The proof uses only global maximality of the median order.  The *feedback
lemma* (`IsMedianOrder.feedback`) says that for positions `a ≤ j` the vertex at
position `j` has at least as many in-neighbours as out-neighbours among the
positions `[a, j)`: otherwise moving it to position `a` would increase the
number of forward arcs.  The counting core (`core_count`) is a strong induction
on the length of the suffix `[a, n)`, splitting at the first *bad* in-neighbour
of `d`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.SeymourSecondNeighbourhoodTournament

open Finset

variable {V : Type*}

/-! ## Definitions -/

/-- A digraph `G` is a *tournament* if its arcs are asymmetric (so in particular
there are no loops) and every pair of distinct vertices is joined by an arc. -/
structure IsTournament (G : Digraph V) : Prop where
  /-- No pair of vertices carries arcs in both directions (hence no loops). -/
  asymm : ∀ u v, G.Adj u v → ¬ G.Adj v u
  /-- Distinct vertices are joined by an arc in some direction. -/
  total : ∀ u v, u ≠ v → G.Adj u v ∨ G.Adj v u

/-- A tournament has no loops. -/
theorem IsTournament.loopless {G : Digraph V} (hT : IsTournament G) (v : V) :
    ¬ G.Adj v v :=
  fun h => hT.asymm v v h h

section Finite

variable [Fintype V] [DecidableEq V]

/-- The out-neighbourhood `N⁺(v) = {w | v → w}`. -/
def outNbhd (G : Digraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  univ.filter (fun w => G.Adj v w)

/-- The second out-neighbourhood `N⁺⁺(v)`: the vertices at directed distance
exactly `2` from `v`, i.e. `w ≠ v`, `w ∉ N⁺(v)` and `v → u → w` for some `u`. -/
def secondNbhd (G : Digraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  univ.filter (fun w => w ≠ v ∧ ¬ G.Adj v w ∧ ∃ u, G.Adj v u ∧ G.Adj u w)

/-- The number of *forward arcs* of an ordering `σ : Fin m ≃ V`, i.e. of arcs
`σ i → σ j` with `i < j`. -/
def forwardArcs {m : ℕ} (G : Digraph V) [DecidableRel G.Adj] (σ : Fin m ≃ V) : ℕ :=
  #(univ.filter (fun pq : Fin m × Fin m => pq.1 < pq.2 ∧ G.Adj (σ pq.1) (σ pq.2)))

/-- A *median order* of `G` is an ordering `σ : Fin m ≃ V` of the vertices with the
maximum number of forward arcs among all orderings. -/
def IsMedianOrder {m : ℕ} (G : Digraph V) [DecidableRel G.Adj] (σ : Fin m ≃ V) : Prop :=
  ∀ τ : Fin m ≃ V, forwardArcs G τ ≤ forwardArcs G σ

/-- The Havet--Thomassé *good* vertices of an ordering `σ : Fin (n + 1) ≃ V` with feed
vertex `d = σ (Fin.last n)`: the in-neighbours `w` of `d` for which some `u`
earlier than `w` in the order satisfies `d → u → w`. -/
def goodSet {n : ℕ} (G : Digraph V) [DecidableRel G.Adj] (σ : Fin (n + 1) ≃ V) :
    Finset V :=
  univ.filter (fun w => G.Adj w (σ (Fin.last n)) ∧
    ∃ u, σ.symm u < σ.symm w ∧ G.Adj (σ (Fin.last n)) u ∧ G.Adj u w)

end Finite

/-! ## Examples -/

/-- The cyclic tournament `0 → 1 → 2 → 0` on three vertices. -/
def cyc3 : Digraph (Fin 3) := ⟨fun i j => j = i + 1⟩

instance : DecidableRel cyc3.Adj := fun i j => inferInstanceAs (Decidable (j = i + 1))

/-- The transitive tournament `i → j ↔ i < j` on four vertices. -/
def trans4 : Digraph (Fin 4) := ⟨fun i j => i < j⟩

instance : DecidableRel trans4.Adj := fun i j => inferInstanceAs (Decidable (i < j))

example : IsTournament cyc3 := ⟨by decide, by decide⟩
example : IsTournament trans4 := ⟨by decide, by decide⟩
example : outNbhd cyc3 0 = {1} := by decide
example : secondNbhd cyc3 0 = {2} := by decide
example : forwardArcs cyc3 (Equiv.refl _) = 2 := by decide
example : IsMedianOrder cyc3 (Equiv.refl _) := by unfold IsMedianOrder; decide
example : goodSet cyc3 (Equiv.refl _) = {1} := by decide
example : outNbhd trans4 0 = {1, 2, 3} := by decide
example : secondNbhd trans4 0 = ∅ := by decide
example : forwardArcs trans4 (Equiv.refl _) = 6 := by decide
example : outNbhd trans4 3 = ∅ := by decide


/-! ## The counting core on positions -/

/-- Splitting a filtered interval count `[a, n)` at a position `i ∈ [a, n)`. -/
theorem card_filter_Ico_split (p : ℕ → Prop) [DecidablePred p] {a i n : ℕ}
    (hai : a ≤ i) (hin : i < n) :
    #((Ico a n).filter p) =
      #((Ico a i).filter p) + (if p i then 1 else 0) + #((Ico (i + 1) n).filter p) := by
  rw [card_filter, card_filter, card_filter, ← sum_Ico_consecutive _ hai hin.le,
    sum_eq_sum_Ico_succ_bot hin, add_assoc]

/-- **Counting core** (positions `0, …, n`, feed vertex at position `n`).  Let `T` be a
tournament relation on the positions `≤ n` satisfying the feedback property: for
`a ≤ j ≤ n`, position `j` has at most as many out-neighbours as in-neighbours in
`[a, j)`.  Then for every `a ≤ n`, the number of out-neighbours of `n` in `[a, n)` is at
most the number of positions `j ∈ [a, n)` with `j → n` and `n → i → j` for some
`i ∈ [a, j)`. -/
theorem core_count (n : ℕ) (T : ℕ → ℕ → Prop) [DecidableRel T]
    (htot : ∀ p q, p ≤ n → q ≤ n → p ≠ q → T p q ∨ T q p)
    (hasymm : ∀ p q, T p q → ¬ T q p)
    (hfb : ∀ a j, a ≤ j → j ≤ n →
      #((Ico a j).filter (T j ·)) ≤ #((Ico a j).filter (T · j))) :
    ∀ a, a ≤ n → #((Ico a n).filter (T n ·)) ≤
      #((Ico a n).filter (fun j => T j n ∧ ∃ i ∈ Ico a j, T n i ∧ T i j)) := by
  suffices H : ∀ k a, n - a ≤ k → a ≤ n → #((Ico a n).filter (T n ·)) ≤
      #((Ico a n).filter (fun j => T j n ∧ ∃ i ∈ Ico a j, T n i ∧ T i j)) from
    fun a ha => H _ a le_rfl ha
  intro k
  induction k with
  | zero =>
    intro a hk ha
    have han : a = n := by omega
    subst han
    simp
  | succ k ih =>
    intro a hk ha
    by_cases hbad : ∃ j, j ∈ Ico a n ∧ T j n ∧ ¬ ∃ i ∈ Ico a j, T n i ∧ T i j
    · obtain ⟨i, hi, hmin⟩ : ∃ i, (i ∈ Ico a n ∧ T i n ∧ ¬ ∃ i' ∈ Ico a i, T n i' ∧ T i' i) ∧
          ∀ m < i, ¬ (m ∈ Ico a n ∧ T m n ∧ ¬ ∃ i' ∈ Ico a m, T n i' ∧ T i' m) :=
        ⟨Nat.find hbad, Nat.find_spec hbad, fun m hm => Nat.find_min hbad hm⟩
      obtain ⟨hiI, hin, hibad⟩ := hi
      rw [mem_Ico] at hiI
      -- out-neighbours of `n` before `i` are out-neighbours of `i`
      have h1 : #((Ico a i).filter (T n ·)) ≤ #((Ico a i).filter (T i ·)) := by
        apply card_le_card
        intro p hp
        simp only [mem_filter, mem_Ico] at hp ⊢
        refine ⟨hp.1, ?_⟩
        have hnot : ¬ T p i := fun h => hibad ⟨p, mem_Ico.2 hp.1, hp.2, h⟩
        rcases htot p i (by omega) (by omega) (by omega) with h | h
        · exact absurd h hnot
        · exact h
      have h2 := hfb a i hiI.1 (by omega)
      have h3 : #((Ico a i).filter (T · i)) ≤
          #((Ico a i).filter (fun j => T j n ∧ ∃ i' ∈ Ico a j, T n i' ∧ T i' j)) := by
        apply card_le_card
        intro p hp
        simp only [mem_filter, mem_Ico] at hp
        have hpn : T p n := by
          have hnot : ¬ T n p := fun h => hibad ⟨p, mem_Ico.2 hp.1, h, hp.2⟩
          rcases htot p n (by omega) le_rfl (by omega) with h | h
          · exact h
          · exact absurd h hnot
        have hgood := hmin p hp.1.2
        simp only [mem_Ico, not_and, not_not] at hgood
        simp only [mem_filter, mem_Ico]
        exact ⟨hp.1, hpn, hgood ⟨hp.1.1, by omega⟩ hpn⟩
      have h45 : #((Ico (i + 1) n).filter (T n ·)) ≤
          #((Ico (i + 1) n).filter (fun j => T j n ∧ ∃ i' ∈ Ico a j, T n i' ∧ T i' j)) := by
        refine (ih (i + 1) (by omega) (by omega)).trans (card_le_card ?_)
        intro p hp
        simp only [mem_filter, mem_Ico] at hp ⊢
        obtain ⟨hp1, hpn, i', hi', h⟩ := hp
        exact ⟨hp1, hpn, i', ⟨by omega, hi'.2⟩, h⟩
      rw [card_filter_Ico_split _ hiI.1 hiI.2, card_filter_Ico_split _ hiI.1 hiI.2]
      have hni : ¬ T n i := hasymm i n hin
      have hgi : ¬ (T i n ∧ ∃ i' ∈ Ico a i, T n i' ∧ T i' i) := fun h => hibad h.2
      simp only [hni, hgi, if_false]
      omega
    · have heq : (Ico a n).filter (fun j => T j n ∧ ∃ i ∈ Ico a j, T n i ∧ T i j) =
          (Ico a n).filter (T · n) := by
        apply filter_congr
        intro j hj
        constructor
        · exact fun h => h.1
        · intro h
          refine ⟨h, ?_⟩
          by_contra hc
          exact hbad ⟨j, hj, h, hc⟩
      rw [heq]
      exact hfb a n ha le_rfl

/-- **Exchange computation.**  Re-rank position `j` to sit just before position `a`
(rank `2a + 1`; every other position `p` gets rank `2p + 2`).  If this does not increase
the number of forward pairs of `T` on `[0, m)`, then `j` has at most as many
out-neighbours as in-neighbours in `[a, j)`. -/
theorem exchange_card_le (T : ℕ → ℕ → Prop) [DecidableRel T] (m a j : ℕ) (haj : a ≤ j) (hj : j < m)
    (h : #((range m ×ˢ range m).filter (fun pq =>
            (if pq.1 = j then 2 * a + 1 else 2 * pq.1 + 2) <
              (if pq.2 = j then 2 * a + 1 else 2 * pq.2 + 2) ∧ T pq.1 pq.2)) ≤
         #((range m ×ˢ range m).filter (fun pq => pq.1 < pq.2 ∧ T pq.1 pq.2))) :
    #((Ico a j).filter (T j ·)) ≤ #((Ico a j).filter (T · j)) := by
  set r : ℕ → ℕ := fun p => if p = j then 2 * a + 1 else 2 * p + 2 with hr
  set Sr := (range m ×ˢ range m).filter (fun pq => r pq.1 < r pq.2 ∧ T pq.1 pq.2) with hSr
  set S := (range m ×ˢ range m).filter (fun pq => pq.1 < pq.2 ∧ T pq.1 pq.2) with hS
  let E : ℕ × ℕ → Prop := fun pq =>
    (pq.1 = j ∧ a ≤ pq.2 ∧ pq.2 < j) ∨ (pq.2 = j ∧ a ≤ pq.1 ∧ pq.1 < j)
  have hnE : Sr.filter (fun pq => ¬ E pq) = S.filter (fun pq => ¬ E pq) := by
    ext ⟨p, q⟩
    simp only [hSr, hS, E, hr, mem_filter, mem_product, mem_range]
    constructor
    · rintro ⟨⟨hpq, hlt, hT⟩, hE⟩
      refine ⟨⟨hpq, ?_, hT⟩, hE⟩
      split_ifs at hlt <;> omega
    · rintro ⟨⟨hpq, hlt, hT⟩, hE⟩
      refine ⟨⟨hpq, ?_, hT⟩, hE⟩
      split_ifs <;> omega
  have hEr : Sr.filter E = ((Ico a j).filter (T j ·)).image (fun q => (j, q)) := by
    ext ⟨p, q⟩
    simp only [hSr, E, hr, mem_filter, mem_product, mem_range, mem_image, mem_Ico,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hpq, hlt, hT⟩, hE⟩
      rcases hE with ⟨rfl, hq⟩ | ⟨rfl, hp⟩
      · exact ⟨q, ⟨hq, hT⟩, rfl, rfl⟩
      · exfalso
        split_ifs at hlt <;> omega
    · rintro ⟨q', ⟨hq', hT⟩, rfl, rfl⟩
      refine ⟨⟨⟨hj, by omega⟩, ?_, hT⟩, Or.inl ⟨rfl, hq'⟩⟩
      split_ifs <;> omega
  have hE : S.filter E = ((Ico a j).filter (T · j)).image (fun p => (p, j)) := by
    ext ⟨p, q⟩
    simp only [hS, E, mem_filter, mem_product, mem_range, mem_image, mem_Ico,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hpq, hlt, hT⟩, hE⟩
      rcases hE with ⟨rfl, hq⟩ | ⟨rfl, hp⟩
      · omega
      · exact ⟨p, ⟨hp, hT⟩, rfl, rfl⟩
    · rintro ⟨p', ⟨hp', hT⟩, rfl, rfl⟩
      exact ⟨⟨⟨by omega, hj⟩, hp'.2, hT⟩, Or.inr ⟨rfl, hp'⟩⟩
  have hcardr := card_filter_add_card_filter_not (s := Sr) E
  have hcard := card_filter_add_card_filter_not (s := S) E
  rw [hnE, hEr, card_image_of_injective _ (fun x y hxy => (Prod.mk.inj hxy).2)] at hcardr
  rw [hE, card_image_of_injective _ (fun x y hxy => (Prod.mk.inj hxy).1)] at hcard
  omega


/-! ## Median orders: the feedback property -/

section Median

/-- In a median order `σ`, re-ranking the positions by any injective `r` does not increase
the number of forward arcs: `r` is realised by the ordering `σ ∘ Tuple.sort r`. -/
theorem IsMedianOrder.rank_le {m : ℕ} {G : Digraph V} [DecidableRel G.Adj] {σ : Fin m ≃ V}
    (hmed : IsMedianOrder G σ) (r : Fin m → ℕ) (hr : Function.Injective r) :
    #(univ.filter (fun pq : Fin m × Fin m => r pq.1 < r pq.2 ∧ G.Adj (σ pq.1) (σ pq.2))) ≤
      forwardArcs G σ := by
  let π := Tuple.sort r
  have hmono : StrictMono (r ∘ π) :=
    (Tuple.monotone_sort r).strictMono_of_injective (hr.comp π.injective)
  refine le_trans (le_of_eq ?_) (hmed (π.trans σ))
  apply card_equiv (Equiv.prodCongr π.symm π.symm)
  intro pq
  simp only [mem_filter, mem_univ, true_and]
  simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  rw [← hmono.lt_iff_lt]
  simp only [Function.comp_apply, Equiv.apply_symm_apply]


/-- The arc relation transported to positions: `p → q` iff the vertices at positions
`p, q ≤ n` of `σ` are joined by an arc `σ p → σ q`. -/
def posAdj {n : ℕ} (G : Digraph V) (σ : Fin (n + 1) ≃ V) (p q : ℕ) : Prop :=
  ∃ x y : Fin (n + 1), x.val = p ∧ y.val = q ∧ G.Adj (σ x) (σ y)

/-- `posAdj` is decidable whenever the arc relation is. -/
instance {n : ℕ} (G : Digraph V) [DecidableRel G.Adj] (σ : Fin (n + 1) ≃ V) :
    DecidableRel (posAdj G σ) := fun p q => by unfold posAdj; infer_instance

example : posAdj cyc3 (n := 2) (Equiv.refl _) 0 1 := by decide
example : posAdj cyc3 (n := 2) (Equiv.refl _) 2 0 := by decide
example : ¬ posAdj cyc3 (n := 2) (Equiv.refl _) 1 0 := by decide
example : ¬ posAdj cyc3 (n := 2) (Equiv.refl _) 2 3 := by decide

/-- On genuine positions, `posAdj` is the arc relation of `G` read through `σ`. -/
theorem posAdj_val_iff {n : ℕ} {G : Digraph V} {σ : Fin (n + 1) ≃ V} (x y : Fin (n + 1)) :
    posAdj G σ x y ↔ G.Adj (σ x) (σ y) := by
  constructor
  · rintro ⟨x', y', hx, hy, h⟩
    rwa [Fin.ext hx, Fin.ext hy] at h
  · intro h
    exact ⟨x, y, rfl, rfl, h⟩

/-- Pair counts over the positions `[0, n]` agree with pair counts over `Fin (n + 1)`. -/
theorem card_pairs_bridge {n : ℕ} (G : Digraph V) [DecidableRel G.Adj] (σ : Fin (n + 1) ≃ V)
    (R : ℕ → ℕ → Prop) [DecidableRel R] :
    #((range (n + 1) ×ˢ range (n + 1)).filter (fun pq => R pq.1 pq.2 ∧ posAdj G σ pq.1 pq.2)) =
      #(univ.filter (fun xy : Fin (n + 1) × Fin (n + 1) =>
        R xy.1 xy.2 ∧ G.Adj (σ xy.1) (σ xy.2))) := by
  symm
  apply card_bij (fun xy _ => ((xy.1 : ℕ), (xy.2 : ℕ)))
  · intro xy hxy
    simp only [mem_filter, mem_univ, true_and] at hxy
    simp only [mem_filter, mem_product, mem_range]
    exact ⟨⟨xy.1.2, xy.2.2⟩, hxy.1, (posAdj_val_iff xy.1 xy.2).2 hxy.2⟩
  · intro xy _ xy' _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
  · intro pq hpq
    simp only [mem_filter, mem_product, mem_range] at hpq
    obtain ⟨⟨hp, hq⟩, hR, hA⟩ := hpq
    refine ⟨(⟨pq.1, hp⟩, ⟨pq.2, hq⟩), ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨hR, (posAdj_val_iff (σ := σ) ⟨pq.1, hp⟩ ⟨pq.2, hq⟩).1 hA⟩

/-- **Feedback lemma.**  In a median order `σ : Fin (n + 1) ≃ V`, for positions
`a ≤ j ≤ n` the vertex at position `j` has at most as many out-neighbours as
in-neighbours among the positions `[a, j)`. -/
theorem IsMedianOrder.feedback {n : ℕ} {G : Digraph V} [DecidableRel G.Adj]
    {σ : Fin (n + 1) ≃ V} (hmed : IsMedianOrder G σ) {a j : ℕ} (haj : a ≤ j) (hj : j ≤ n) :
    #((Ico a j).filter (posAdj G σ j ·)) ≤ #((Ico a j).filter (posAdj G σ · j)) := by
  apply exchange_card_le (posAdj G σ) (n + 1) a j haj (by omega)
  let r : Fin (n + 1) → ℕ := fun x => if x.val = j then 2 * a + 1 else 2 * x.val + 2
  have hr : Function.Injective r := by
    intro x y hxy
    simp only [r] at hxy
    apply Fin.ext
    split_ifs at hxy <;> omega
  have key := hmed.rank_le r hr
  calc _ = #(univ.filter (fun xy : Fin (n + 1) × Fin (n + 1) =>
          r xy.1 < r xy.2 ∧ G.Adj (σ xy.1) (σ xy.2))) :=
        card_pairs_bridge G σ
          (fun p q => (if p = j then 2 * a + 1 else 2 * p + 2) <
            (if q = j then 2 * a + 1 else 2 * q + 2))
    _ ≤ forwardArcs G σ := key
    _ = _ := (card_pairs_bridge G σ (fun p q => p < q)).symm

/-- Counting a filtered subset of `V` through the positions `[0, n)` of `σ`. -/
theorem card_filter_eq_card_filter_Ico [Fintype V] {n : ℕ} (σ : Fin (n + 1) ≃ V) (P : V → Prop)
    [DecidablePred P] (Q : ℕ → Prop) [DecidablePred Q]
    (hPQ : ∀ x : Fin (n + 1), P (σ x) ↔ (x.val < n ∧ Q x.val)) :
    #(univ.filter P) = #((Ico 0 n).filter Q) := by
  apply card_bij (fun v _ => (σ.symm v).val)
  · intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    have h := (hPQ (σ.symm v)).1 (by simpa using hv)
    simp only [mem_filter, mem_Ico]
    exact ⟨⟨Nat.zero_le _, h.1⟩, h.2⟩
  · intro v _ w _ h
    exact σ.symm.injective (Fin.ext h)
  · intro p hp
    simp only [mem_filter, mem_Ico] at hp
    refine ⟨σ ⟨p, by omega⟩, ?_, by simp⟩
    simp only [mem_filter, mem_univ, true_and]
    exact (hPQ ⟨p, by omega⟩).2 ⟨hp.1.2, hp.2⟩

end Median

/-! ## The Havet--Thomassé theorem and Dean's conjecture -/

section Main

variable [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- **Havet--Thomassé, counting half.**  If `σ : Fin (n + 1) ≃ V` is a median order of a
tournament `G` with feed vertex `d = σ (Fin.last n)`, then `|N⁺(d)| ≤ |G_σ|`, where
`G_σ = goodSet G σ` is the set of in-neighbours `w` of `d` with `d → u → w` for some `u`
preceding `w` in `σ`. -/
theorem havetThomasse_card_outNbhd_le_card_goodSet {n : ℕ} {G : Digraph V}
    [DecidableRel G.Adj] (hT : IsTournament G) (σ : Fin (n + 1) ≃ V)
    (hmed : IsMedianOrder G σ) :
    #(outNbhd G (σ (Fin.last n))) ≤ #(goodSet G σ) := by
  have htot : ∀ p q, p ≤ n → q ≤ n → p ≠ q → posAdj G σ p q ∨ posAdj G σ q p := by
    intro p q hp hq hpq
    have hne : σ ⟨p, by omega⟩ ≠ σ ⟨q, by omega⟩ := fun h =>
      hpq (congrArg Fin.val (σ.injective h))
    rcases hT.total _ _ hne with h | h
    · exact Or.inl ((posAdj_val_iff ⟨p, by omega⟩ ⟨q, by omega⟩).2 h)
    · exact Or.inr ((posAdj_val_iff ⟨q, by omega⟩ ⟨p, by omega⟩).2 h)
  have hasymm : ∀ p q, posAdj G σ p q → ¬ posAdj G σ q p := by
    rintro p q ⟨x, y, rfl, rfl, h⟩ h'
    exact hT.asymm _ _ h ((posAdj_val_iff y x).1 h')
  have hcore := core_count n (posAdj G σ) htot hasymm
    (fun a j haj hj => hmed.feedback haj hj) 0 (Nat.zero_le n)
  have hlast : ∀ x : Fin (n + 1), x ≠ Fin.last n → x.val < n := fun x hx =>
    Fin.val_lt_last hx
  have hout : #(outNbhd G (σ (Fin.last n))) = #((Ico 0 n).filter (posAdj G σ n ·)) := by
    apply card_filter_eq_card_filter_Ico σ
    intro x
    constructor
    · intro h
      refine ⟨hlast x ?_, (posAdj_val_iff (Fin.last n) x).2 h⟩
      rintro rfl
      exact hT.loopless _ h
    · rintro ⟨-, h⟩
      exact (posAdj_val_iff (Fin.last n) x).1 h
  -- the count of good positions, in the exact shape produced by `core_count`
  rw [hout]
  refine hcore.trans_eq ?_
  symm
  apply card_filter_eq_card_filter_Ico σ
  intro x
  constructor
  · rintro ⟨hxd, u, hu, hdu, huw⟩
    refine ⟨hlast x ?_, (posAdj_val_iff x (Fin.last n)).2 hxd, (σ.symm u).val, ?_, ?_, ?_⟩
    · rintro rfl
      exact hT.loopless _ hxd
    · simp only [Equiv.symm_apply_apply] at hu
      exact mem_Ico.2 ⟨Nat.zero_le _, hu⟩
    · exact (posAdj_val_iff (Fin.last n) (σ.symm u)).2 (by simpa using hdu)
    · exact (posAdj_val_iff (σ.symm u) x).2 (by simpa using huw)
  · rintro ⟨hx, hxd, i, hi, hni, hix⟩
    have hi' : i < x.val := (mem_Ico.1 hi).2
    refine ⟨(posAdj_val_iff x (Fin.last n)).1 hxd, σ ⟨i, by omega⟩, ?_, ?_, ?_⟩
    · simp only [Equiv.symm_apply_apply]
      exact hi'
    · exact (posAdj_val_iff (Fin.last n) ⟨i, by omega⟩).1 hni
    · exact (posAdj_val_iff ⟨i, by omega⟩ x).1 hix

/-- The good vertices of an ordering of a tournament lie in the second out-neighbourhood
of its feed vertex. -/
theorem goodSet_subset_secondNbhd {n : ℕ} {G : Digraph V} [DecidableRel G.Adj]
    (hT : IsTournament G) (σ : Fin (n + 1) ≃ V) :
    goodSet G σ ⊆ secondNbhd G (σ (Fin.last n)) := by
  intro w hw
  simp only [goodSet, secondNbhd, mem_filter, mem_univ, true_and] at hw ⊢
  obtain ⟨hwd, u, -, hdu, huw⟩ := hw
  refine ⟨?_, hT.asymm _ _ hwd, u, hdu, huw⟩
  rintro rfl
  exact hT.loopless _ hwd

/-- **Havet--Thomassé (2000).**  The feed vertex `d = σ (Fin.last n)` of a median order
`σ` of a finite tournament has `|N⁺(d)| ≤ |N⁺⁺(d)|`. -/
theorem havetThomasse {n : ℕ} {G : Digraph V} [DecidableRel G.Adj] (hT : IsTournament G)
    (σ : Fin (n + 1) ≃ V) (hmed : IsMedianOrder G σ) :
    #(outNbhd G (σ (Fin.last n))) ≤ #(secondNbhd G (σ (Fin.last n))) :=
  (havetThomasse_card_outNbhd_le_card_goodSet hT σ hmed).trans
    (card_le_card (goodSet_subset_secondNbhd hT σ))

/-- **Dean's conjecture** (Seymour's second neighbourhood conjecture for tournaments;
Fisher 1996, Havet--Thomassé 2000).  Every nonempty finite tournament has a vertex `v`
whose second out-neighbourhood is at least as large as its out-neighbourhood:
`|N⁺(v)| ≤ |N⁺⁺(v)|`. -/
theorem dean_conjecture [Nonempty V] (G : Digraph V) [DecidableRel G.Adj]
    (hT : IsTournament G) : ∃ v, #(outNbhd G v) ≤ #(secondNbhd G v) := by
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card V = n + 1 := ⟨Fintype.card V - 1, by omega⟩
  let e : Fin (n + 1) ≃ V := (Fintype.equivFinOfCardEq hn).symm
  obtain ⟨σ, -, hσ⟩ := exists_max_image (univ : Finset (Fin (n + 1) ≃ V))
    (forwardArcs G) ⟨e, mem_univ e⟩
  exact ⟨σ (Fin.last n), havetThomasse hT σ (fun τ => hσ τ (mem_univ τ))⟩

end Main

end Candidates.SeymourSecondNeighbourhoodTournament
