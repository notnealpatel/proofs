/-
# Kneser graph KG(n,2) has chromatic number n - 2

## Source

MathOverflow question 214927, "Important formulas in combinatorics",
answer 215450 by Anurag (https://mathoverflow.net/a/215450, CC BY-SA 4.0),
re-pulled verbatim through the StackExchange API on 2026-10-21:

> The Kneser graph $KG_{n,k}$ is the graph on $k$-subsets of
> $\{1, \dots, n\}$ with two subsets made adjacent when they are disjoint.
> The formula $$\chi(KG_{n,k}) = n - 2k + 2$$ was proved by Lovász in 1978
> using topological methods, which gave birth to the area of topological
> combinatorics.

References cited there: L. Lovász, "Kneser's conjecture, chromatic number,
and homotopy", J. Combin. Theory Ser. A 25 (1978) 319-324; J. Matoušek,
"Using the Borsuk-Ulam theorem" (Springer, 2003).  No arXiv ids are involved.

## Status

Proved in the literature (Lovász 1978, general `k`); the thread states the
known theorem.  This module formalizes only the elementary special case
`k = 2`: `χ(KG(n,2)) = n - 2` for `n ≥ 3`.  (For `n = 3` the graph has three
vertices and no edges, so `χ = 1 = n - 2`, matching `n - 2k + 2`.)  The general
lower bound needs Borsuk-Ulam / Tucker and is not attempted.

## Proof outline

* Upper bound: colour a pair by `min (min element) (n - 3)`.  Pairs whose
  minimum is at least `n - 3` lie in the 3-set `{n-3, n-2, n-1}`, so two of
  them cannot be disjoint.
* Lower bound, by strong induction on the ground set `S`: each colour class is
  an intersecting family of 2-sets.  If some class lies in a star at `v`,
  delete `v` and lose that colour.  Otherwise every class lies in a triangle,
  so has at most 3 members, and `3 (m - 3) < C(m, 2)` gives a contradiction.

Date: 2026-10-21.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.KneserTwoChromatic

open Finset

/-! ## Definition and ground truth -/

/-- The Kneser graph `KG(n,k)`: vertices are the `k`-subsets of `Fin n`, and two
of them are adjacent when they are distinct and disjoint.  (Distinctness only
matters for `k = 0`, where the single vertex `∅` would otherwise be a loop; see
`kneserGraph_adj_iff` for `0 < k`.) -/
def kneserGraph (n k : ℕ) : SimpleGraph {s : Finset (Fin n) // s.card = k} where
  Adj s t := s ≠ t ∧ Disjoint s.1 t.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Unfolding lemma for adjacency in `kneserGraph`. -/
theorem kneserGraph_adj {n k : ℕ} (s t : {s : Finset (Fin n) // s.card = k}) :
    (kneserGraph n k).Adj s t ↔ s ≠ t ∧ Disjoint s.1 t.1 := Iff.rfl

/-- Adjacency in the Kneser graph is decidable. -/
instance (n k : ℕ) : DecidableRel (kneserGraph n k).Adj :=
  inferInstanceAs (DecidableRel fun s t : {s : Finset (Fin n) // s.card = k} =>
    s ≠ t ∧ Disjoint s.1 t.1)

/-- For `0 < k`, adjacency in `KG(n,k)` is exactly disjointness, as in the source. -/
theorem kneserGraph_adj_iff {n k : ℕ} (hk : 0 < k) (s t : {s : Finset (Fin n) // s.card = k}) :
    (kneserGraph n k).Adj s t ↔ Disjoint s.1 t.1 := by
  rw [kneserGraph_adj]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rintro rfl
  have hne : s.1.Nonempty := card_pos.mp (by rw [s.2]; exact hk)
  exact hne.ne_empty (disjoint_self_iff_empty _ |>.mp h)

example : (kneserGraph 5 2).Adj ⟨{0, 1}, rfl⟩ ⟨{2, 3}, rfl⟩ := by decide
example : ¬ (kneserGraph 5 2).Adj ⟨{0, 1}, rfl⟩ ⟨{1, 3}, rfl⟩ := by decide
/- `KG(5,2)` is the Petersen graph: 10 vertices and 15 edges. -/
example : Fintype.card {s : Finset (Fin 5) // s.card = 2} = 10 := by decide
example : (kneserGraph 5 2).edgeFinset.card = 15 := by decide

/-! ## Combinatorial core -/

/-- An intersecting family of 2-sets that is not contained in any star
(for every `v` some member avoids `v`) has at most 3 members: it lies inside
the triangle on some 3-set. -/
theorem card_le_three_of_intersecting {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (h2 : ∀ e ∈ F, e.card = 2) (hint : ∀ e ∈ F, ∀ f ∈ F, ¬ Disjoint e f)
    (hstar : ∀ v : α, ∃ e ∈ F, v ∉ e) : F.card ≤ 3 := by
  rcases F.eq_empty_or_nonempty with rfl | ⟨e1, he1⟩
  · simp
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp (h2 e1 he1)
  obtain ⟨e2, he2, ha2⟩ := hstar a
  obtain ⟨c, d, hcd, rfl⟩ := card_eq_two.mp (h2 e2 he2)
  obtain ⟨e3, he3, hb3⟩ := hstar b
  obtain ⟨p, q, hpq, rfl⟩ := card_eq_two.mp (h2 e3 he3)
  have h12 := hint _ he1 _ he2
  have h13 := hint _ he1 _ he3
  have h23 := hint _ he2 _ he3
  simp only [disjoint_insert_left, disjoint_singleton_left, mem_insert, mem_singleton,
    not_and_or, not_not] at h12 h13 h23 ha2 hb3
  have hsub : F ⊆ (({a, b} ∪ {c, d} : Finset α)).powersetCard 2 := by
    intro e he
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp (h2 e he)
    have h1 := hint _ he1 _ he
    have h2' := hint _ he2 _ he
    have h3 := hint _ he3 _ he
    simp only [disjoint_insert_left, disjoint_singleton_left, mem_insert, mem_singleton,
      not_and_or, not_not] at h1 h2' h3
    rw [mem_powersetCard]
    refine ⟨?_, card_pair hxy⟩
    intro z hz
    simp only [mem_insert, mem_singleton, mem_union] at hz ⊢
    grind
  have hU : ({a, b} ∪ {c, d} : Finset α).card ≤ 3 := by
    have hb : b ∈ ({c, d} : Finset α) := by
      simp only [mem_insert, mem_singleton]; grind
    calc ({a, b} ∪ {c, d} : Finset α).card = ({a} ∪ {c, d} : Finset α).card := by
          congr 1; ext z; simp only [mem_insert, mem_singleton, mem_union] at hb ⊢; grind
      _ ≤ ({a} : Finset α).card + ({c, d} : Finset α).card := card_union_le _ _
      _ ≤ 3 := by rw [card_singleton]; have hcd2 := card_le_two (a := c) (b := d); omega
  calc F.card ≤ ((({a, b} ∪ {c, d} : Finset α)).powersetCard 2).card := card_le_card hsub
    _ = ({a, b} ∪ {c, d} : Finset α).card.choose 2 := card_powersetCard _ _
    _ ≤ (3 : ℕ).choose 2 := Nat.choose_le_choose 2 hU
    _ = 3 := by decide

/-- For `m ≥ 3`, `3 (m - 3) < C(m, 2)` (equivalently `m² - 7m + 18 > 0`). -/
theorem choose_two_gt (m : ℕ) (hm : 3 ≤ m) : 3 * (m - 3) < m.choose 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
  have h2 : 2 * ((j + 3).choose 2) = (j + 3) * (j + 2) := by
    rw [Nat.choose_two_right, show j + 3 - 1 = j + 2 from rfl]
    have hdvd : 2 ∣ (j + 3) * (j + 2) := by
      rcases Nat.even_or_odd j with ⟨t, ht⟩ | ⟨t, ht⟩
      · exact ⟨(j + 3) * (t + 1), by subst ht; ring⟩
      · exact ⟨(t + 2) * (j + 2), by subst ht; ring⟩
    exact Nat.mul_div_cancel' hdvd
  simp only [Nat.add_sub_cancel]
  nlinarith [h2, Nat.le_mul_self j]

/-- Elementary lower bound for colourings of 2-subsets: if `c` gives distinct
values to disjoint 2-subsets of `S` with `3 ≤ |S|`, then `c` takes at least
`|S| - 2` values on the 2-subsets of `S`. -/
theorem le_card_image_colors {α β : Type*} [DecidableEq α] [DecidableEq β]
    (c : Finset α → β) (S : Finset α) (hS : 3 ≤ S.card)
    (hc : ∀ e ∈ S.powersetCard 2, ∀ f ∈ S.powersetCard 2, Disjoint e f → c e ≠ c f) :
    S.card ≤ ((S.powersetCard 2).image c).card + 2 := by
  induction S using Finset.strongInduction with
  | H S ih =>
  set P := S.powersetCard 2 with hP
  set K := P.image c with hK
  have hPne : P.Nonempty := powersetCard_nonempty.mpr (by omega)
  have hKne : K.Nonempty := hPne.image c
  have hKpos : 0 < K.card := hKne.card_pos
  by_contra hlt
  push Not at hlt
  by_cases hstar : ∃ k ∈ K, ∃ v ∈ S, ∀ e ∈ P, c e = k → v ∈ e
  · obtain ⟨k, hk, v, hv, hkv⟩ := hstar
    have hcard' : (S.erase v).card = S.card - 1 := card_erase_of_mem hv
    by_cases h3 : S.card = 3
    · omega
    have hsub : (S.erase v).powersetCard 2 ⊆ P := powersetCard_mono (erase_subset v S)
    have ih' := ih (S.erase v) (erase_ssubset hv) (by omega)
      (fun e he f hf hef => hc e (hsub he) f (hsub hf) hef)
    have hK' : ((S.erase v).powersetCard 2).image c ⊆ K.erase k := by
      intro x hx
      obtain ⟨e, he, rfl⟩ := mem_image.mp hx
      refine mem_erase.mpr ⟨?_, mem_image_of_mem c (hsub he)⟩
      intro hek
      have hve := hkv e (hsub he) hek
      have hvS' : v ∈ S.erase v := (mem_powersetCard.mp he).1 hve
      exact (notMem_erase v S) hvS'
    have hK'card := card_le_card hK'
    rw [card_erase_of_mem hk] at hK'card
    omega
  · push Not at hstar
    have hclass : ∀ k ∈ K, (P.filter (fun e => c e = k)).card ≤ 3 := by
      intro k hk
      apply card_le_three_of_intersecting
      · intro e he
        exact (mem_powersetCard.mp (mem_filter.mp he).1).2
      · intro e he f hf hef
        have he' := mem_filter.mp he
        have hf' := mem_filter.mp hf
        exact hc e he'.1 f hf'.1 hef (he'.2.trans hf'.2.symm)
      · intro v
        by_cases hv : v ∈ S
        · obtain ⟨e, he, hce, hve⟩ := hstar k hk v hv
          exact ⟨e, mem_filter.mpr ⟨he, hce⟩, hve⟩
        · obtain ⟨e, he, hce⟩ := mem_image.mp hk
          refine ⟨e, mem_filter.mpr ⟨he, hce⟩, fun hve => hv ?_⟩
          exact (mem_powersetCard.mp he).1 hve
    have hPle : P.card ≤ 3 * K.card := card_le_mul_card_image P 3 hclass
    have hPc : P.card = S.card.choose 2 := card_powersetCard 2 S
    have hchoose := choose_two_gt S.card hS
    omega

/-! ## Upper bound -/

/-- The colour of a pair `s ⊆ Fin n`: `min (min s) (n - 3)`, a value `< n - 2`. -/
def kneserTwoColor (n : ℕ) (s : {s : Finset (Fin n) // s.card = 2}) : ℕ :=
  min (s.1.min' (card_pos.mp (by rw [s.2]; norm_num))).val (n - 3)

/-- `KG(n,2)` is `(n - 2)`-colourable for `n ≥ 3`. -/
theorem kneserTwo_colorable (n : ℕ) (hn : 3 ≤ n) : (kneserGraph n 2).Colorable (n - 2) := by
  refine ⟨SimpleGraph.Coloring.mk (fun s => ⟨kneserTwoColor n s, ?_⟩) ?_⟩
  · unfold kneserTwoColor; omega
  · intro s t hadj heq
    have hdisj : Disjoint s.1 t.1 := ((kneserGraph_adj s t).mp hadj).2
    have hc : kneserTwoColor n s = kneserTwoColor n t := congrArg Fin.val heq
    unfold kneserTwoColor at hc
    set a := s.1.min' (card_pos.mp (by rw [s.2]; norm_num)) with ha
    set b := t.1.min' (card_pos.mp (by rw [t.2]; norm_num)) with hb
    have has : a ∈ s.1 := min'_mem _ _
    have hbt : b ∈ t.1 := min'_mem _ _
    by_cases hlow : a.val < n - 3 ∨ b.val < n - 3
    · have hab : a = b := Fin.ext (by omega)
      exact disjoint_left.mp hdisj has (hab ▸ hbt)
    · push Not at hlow
      let T : Finset (Fin n) := univ.filter (fun x => n - 3 ≤ x.val)
      have hsT : s.1 ⊆ T := fun x hx =>
        mem_filter.mpr ⟨mem_univ x, hlow.1.trans (min'_le _ _ hx)⟩
      have htT : t.1 ⊆ T := fun x hx =>
        mem_filter.mpr ⟨mem_univ x, hlow.2.trans (min'_le _ _ hx)⟩
      have hTcard : T.card ≤ 3 := by
        calc T.card ≤ (Ico (n - 3) n).card :=
              card_le_card_of_injOn (fun x => x.val)
                (fun x hx => mem_Ico.mpr ⟨(mem_filter.mp hx).2, x.isLt⟩)
                (fun x _ y _ hxy => Fin.ext hxy)
          _ = 3 := by rw [Nat.card_Ico]; omega
      have hunion : (s.1 ∪ t.1).card = 4 := by
        rw [card_union_of_disjoint hdisj, s.2, t.2]
      have hsub := card_le_card (union_subset hsT htT)
      omega

/-! ## Lower bound -/

/-- `KG(n,2)` is not `(n - 3)`-colourable for `n ≥ 3`. -/
theorem kneserTwo_not_colorable (n : ℕ) (hn : 3 ≤ n) :
    ¬ (kneserGraph n 2).Colorable (n - 3) := by
  rintro ⟨C⟩
  let c : Finset (Fin n) → ℕ := fun e => if h : e.card = 2 then (C ⟨e, h⟩ : ℕ) else 0
  have hc : ∀ e ∈ (univ : Finset (Fin n)).powersetCard 2,
      ∀ f ∈ (univ : Finset (Fin n)).powersetCard 2, Disjoint e f → c e ≠ c f := by
    intro e he f hf hef hcef
    have he2 : e.card = 2 := (mem_powersetCard.mp he).2
    have hf2 : f.card = 2 := (mem_powersetCard.mp hf).2
    have hadj : (kneserGraph n 2).Adj ⟨e, he2⟩ ⟨f, hf2⟩ :=
      (kneserGraph_adj_iff (by norm_num) _ _).mpr hef
    have hval : (C ⟨e, he2⟩ : ℕ) = (C ⟨f, hf2⟩ : ℕ) := by
      simpa only [c, he2, hf2, dite_true] using hcef
    exact C.valid hadj (Fin.ext hval)
  have hbound := le_card_image_colors c univ (by rw [card_univ, Fintype.card_fin]; exact hn) hc
  have himg : ((univ : Finset (Fin n)).powersetCard 2).image c ⊆ range (n - 3) := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := mem_image.mp hx
    have he2 : e.card = 2 := (mem_powersetCard.mp he).2
    simp only [c, he2, dite_true, mem_range, Fin.is_lt]
  have hle := card_le_card himg
  rw [card_range] at hle
  rw [card_univ, Fintype.card_fin] at hbound
  omega

/-! ## Main theorem -/

/-- **Kneser graph `KG(n,2)`** (the `k = 2` case of Lovász's theorem
`χ(KG(n,k)) = n - 2k + 2`, quoted in MathOverflow answer 215450): for `n ≥ 3`,
the Kneser graph on the 2-subsets of an `n`-set has chromatic number `n - 2`. -/
theorem kneserTwo_chromaticNumber (n : ℕ) (hn : 3 ≤ n) :
    (kneserGraph n 2).chromaticNumber = (n - 2 : ℕ) := by
  have hsplit : n - 2 = (n - 3) + 1 := by omega
  rw [hsplit, Nat.cast_add, Nat.cast_one,
    SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable]
  exact ⟨hsplit ▸ kneserTwo_colorable n hn, kneserTwo_not_colorable n hn⟩

/-- Non-vacuity check: `KG(5,2)`, the Petersen graph, has chromatic number 3. -/
example : (kneserGraph 5 2).chromaticNumber = 3 := kneserTwo_chromaticNumber 5 (by norm_num)

end Candidates.KneserTwoChromatic
