/-
# Melnikov's strict inequality for bipartite graphs

## Source

arXiv:2610.09649, Zhanping Yang and Qinghou Zeng, "Melnikov's Valency Variety
Problem" (retrieved 2026-10-21).

The valency variety `w(G)` is the number of distinct vertex degrees of a finite
simple graph `G`.  The paper's Conjecture 1.1 (Melnikov; see Vizing), verbatim:

```
Every simple graph G with at least two vertices satisfies
  chi(G) > \lceil \lfloor w(G)/2 \rfloor / (|V(G)| - w(G)) \rceil.
```

The paper proves the non-strict version (Corollary 1.3) and refutes the strict
version with a 37-vertex graph `G_*` of chromatic number 3 (Section 4).  It does
not discuss bipartite graphs.

## Target (special case; not in the paper, open as far as the triage found)

Informal claim: "Melnikov strict inequality holds for bipartite graphs: a
bipartite graph on n vertices has at most floor((2n+1)/3) distinct degrees."

* Lemma: if `G` is 2-colourable on `n` vertices then `3 * w(G) ≤ 2 * n + 1`.
* Corollary: every graph with `χ(G) ≤ 2` and at least two vertices satisfies the
  strict inequality of Conjecture 1.1.

Status: both are proved below (no `sorry`).  Computational evidence: exhaustive
`nauty_geng -b` checks give `max w = ⌊(2n+1)/3⌋` exactly for `n = 2..13`
(triage `n ≤ 11`, extended here to `n = 12` (251135 graphs) and `n = 13`
(2527712 graphs)); the bound is attained, e.g. at `n = 4` by `cherry` below.

## Proof outline

Let `S`, `Sᶜ` be the colour classes, `a = |S|`, `b = |Sᶜ|`, `D_S`, `D_Sᶜ` the
degree sets of each side.  Then `D_S ⊆ [0, b]`, `D_Sᶜ ⊆ [0, a]`, `|D_S| ≤ a`,
`|D_Sᶜ| ≤ b`, and `0 ∈ D_S`, `a ∈ D_Sᶜ` cannot hold together (the vertex of degree
`a` is adjacent to the isolated vertex), and symmetrically.  The purely
combinatorial lemma `three_mul_card_union_le` turns these facts into
`3 |D_S ∪ D_Sᶜ| ≤ 2 (a + b) + 1`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.MelnikovValencyBipartite

open Finset

/-! ## Definition layer -/

/-- The valency variety `w(G)`: the number of distinct vertex degrees of the finite
simple graph `G` (arXiv:2610.09649, Section 1). -/
def valencyVariety {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (univ.image fun v => G.degree v).card

/-- The cherry `K_{1,2}` plus an isolated vertex, on `Fin 4`: vertex `0` is adjacent
to `1` and `2`, vertex `3` is isolated.  Degrees `2, 1, 1, 0`. -/
def cherry : SimpleGraph (Fin 4) where
  Adj i j := (i = 0 ∧ (j = 1 ∨ j = 2)) ∨ (j = 0 ∧ (i = 1 ∨ i = 2))
  symm := ⟨fun i j h => by tauto⟩
  loopless := ⟨by decide⟩

/-- Adjacency in `cherry` is decidable. -/
instance : DecidableRel cherry.Adj := fun i j =>
  inferInstanceAs (Decidable ((i = 0 ∧ (j = 1 ∨ j = 2)) ∨ (j = 0 ∧ (i = 1 ∨ i = 2))))

/-- Ground truth: the cherry plus an isolated vertex has degrees `{0, 1, 2}`. -/
example : valencyVariety cherry = 3 := by decide

/-- Ground truth: the empty graph on three vertices has one degree. -/
example : valencyVariety (⊥ : SimpleGraph (Fin 3)) = 1 := by decide

/-- Ground truth: the triangle has one degree. -/
example : valencyVariety (⊤ : SimpleGraph (Fin 3)) = 1 := by decide

/-- Non-vacuity and sharpness: `cherry` is bipartite and attains
`3 * w = 2 * n + 1` with `n = 4`, `w = 3`. -/
example : cherry.Colorable 2 ∧ 3 * valencyVariety cherry = 2 * Fintype.card (Fin 4) + 1 :=
  ⟨⟨SimpleGraph.Coloring.mk (fun i => if i = 0 then 0 else 1) (by decide)⟩, by decide⟩

/-! ## Combinatorial core -/

/-- Pure set lemma behind the bound.  Let `a ≤ b`, `DA ⊆ [0, b]` with `|DA| ≤ a`,
`DB ⊆ [0, a]` with `|DB| ≤ b`, and suppose neither `0 ∈ DA ∧ a ∈ DB` nor
`0 ∈ DB ∧ b ∈ DA`.  Then `3 |DA ∪ DB| ≤ 2 (a + b) + 1`. -/
theorem three_mul_card_union_le (a b : ℕ) (DA DB : Finset ℕ) (hab : a ≤ b)
    (hA : DA ⊆ range (b + 1)) (hB : DB ⊆ range (a + 1))
    (hcA : DA.card ≤ a) (hcB : DB.card ≤ b)
    (h1 : ¬(0 ∈ DA ∧ a ∈ DB)) (h2 : ¬(0 ∈ DB ∧ b ∈ DA)) :
    3 * (DA ∪ DB).card ≤ 2 * (a + b) + 1 := by
  have hU : DA ∪ DB ⊆ range (b + 1) :=
    union_subset hA (hB.trans (range_subset_range.2 (by omega)))
  have hUle : (DA ∪ DB).card ≤ b + 1 := by simpa using card_le_card hU
  have hsum : (DA ∪ DB).card ≤ DA.card + DB.card := card_union_le DA DB
  have hBle : DB.card ≤ a + 1 := by simpa using card_le_card hB
  rcases Nat.lt_or_ge (DA ∪ DB).card (b + 1) with hlt | hge
  · omega
  -- The union is all of `[0, b]`; in particular it contains `0` and `b`.
  have hEq : DA ∪ DB = range (b + 1) := eq_of_subset_of_card_le hU (by simpa using hge)
  have h0 : 0 ∈ DA ∪ DB := by rw [hEq]; simp
  have hb : b ∈ DA ∪ DB := by rw [hEq]; simp
  rw [mem_union] at h0 hb
  rcases h0 with h0A | h0B
  · have haB : a ∉ DB := fun h => h1 ⟨h0A, h⟩
    rcases hb with hbA | hbB
    · -- `DB` avoids both `0` and `a`, so `|DB| ≤ a - 1`.
      have h0B : 0 ∉ DB := fun h => h2 ⟨h, hbA⟩
      have ha1 : 1 ≤ a := by
        have hApos := card_pos.2 ⟨0, h0A⟩
        omega
      have hsub : DB ⊆ ((range (a + 1)).erase a).erase 0 := by
        intro x hx
        simp only [mem_erase, mem_range]
        refine ⟨fun h => h0B (h ▸ hx), fun h => haB (h ▸ hx), ?_⟩
        simpa using hB hx
      have hc := card_le_card hsub
      rw [card_erase_of_mem (by simp only [mem_erase, mem_range]; omega),
        card_erase_of_mem (by simp), card_range] at hc
      omega
    · have hba : b ≤ a := by simpa using hB hbB
      have hab' : a = b := le_antisymm hab hba
      subst hab'
      exact absurd hbB haB
  · -- `0 ∈ DB` forces `b ∉ DA`, hence `b ∈ DB`, hence `a = b`.
    have hbA : b ∉ DA := fun h => h2 ⟨h0B, h⟩
    have hbB : b ∈ DB := hb.resolve_left hbA
    have hba : b ≤ a := by simpa using hB hbB
    have hab' : a = b := le_antisymm hab hba
    subst hab'
    rcases Nat.lt_or_ge a 2 with ha2 | ha2
    · have ha0 : a ≠ 0 := by
        rintro rfl
        have hBpos := card_pos.2 ⟨0, h0B⟩
        omega
      have hpair : ({0, a} : Finset ℕ) ⊆ DB := by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact h0B
        · exact hbB
      have hpc := card_le_card hpair
      rw [card_pair (Ne.symm ha0)] at hpc
      omega
    · omega

/-! ## Graph layer -/

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A vertex on side `S` of a bipartition of `G` has degree at most `|Sᶜ|`. -/
theorem degree_le_card_compl_of_mem (S : Finset V)
    (hS : ∀ u v, G.Adj u v → (u ∈ S ↔ v ∉ S)) {v : V} (hv : v ∈ S) :
    G.degree v ≤ Sᶜ.card := by
  rw [← G.card_neighborFinset_eq_degree]
  refine card_le_card fun x hx => ?_
  rw [G.mem_neighborFinset] at hx
  simpa using (hS v x hx).1 hv

/-- In a bipartition `S, Sᶜ` of `G`, a vertex `u ∈ S` of degree `0` and a vertex
`v ∉ S` of degree `|S|` cannot coexist: `v` would be adjacent to `u`. -/
theorem not_degree_eq_zero_and_degree_eq_card (S : Finset V)
    (hS : ∀ u v, G.Adj u v → (u ∈ S ↔ v ∉ S)) {u v : V} (hu : u ∈ S) (hv : v ∉ S)
    (hu0 : G.degree u = 0) (hvS : G.degree v = S.card) : False := by
  have hsub : G.neighborFinset v ⊆ S := fun x hx => by
    rw [G.mem_neighborFinset] at hx
    have hvx := hS v x hx
    by_contra hxS
    exact hv (hvx.2 hxS)
  have heq : G.neighborFinset v = S :=
    eq_of_subset_of_card_le hsub (by rw [G.card_neighborFinset_eq_degree, hvS])
  have hadj : G.Adj v u := by rw [← G.mem_neighborFinset, heq]; exact hu
  have hpos : 0 < G.degree u := (G.degree_pos_iff_exists_adj u).2 ⟨v, hadj.symm⟩
  omega

/-- The three facts about the degree set of one side `S` of a bipartition that
feed `three_mul_card_union_le`. -/
theorem degree_image_facts (S : Finset V) (hS : ∀ u v, G.Adj u v → (u ∈ S ↔ v ∉ S)) :
    S.image (fun v => G.degree v) ⊆ range (Sᶜ.card + 1) ∧
      (S.image (fun v => G.degree v)).card ≤ S.card ∧
      ¬(0 ∈ S.image (fun v => G.degree v) ∧ S.card ∈ Sᶜ.image (fun v => G.degree v)) := by
  refine ⟨fun d hd => ?_, card_image_le, ?_⟩
  · obtain ⟨v, hv, rfl⟩ := mem_image.1 hd
    simpa [Nat.lt_succ_iff] using degree_le_card_compl_of_mem G S hS hv
  · rintro ⟨h0, hfull⟩
    obtain ⟨u, hu, hu0⟩ := mem_image.1 h0
    obtain ⟨v, hv, hvS⟩ := mem_image.1 hfull
    exact not_degree_eq_zero_and_degree_eq_card G S hS hu (by simpa using hv) hu0 hvS

/-- If `S, Sᶜ` is a bipartition of `G` (every edge crosses), then
`3 w(G) ≤ 2 |V| + 1`. -/
theorem three_mul_valencyVariety_le_of_bipartition (S : Finset V)
    (hS : ∀ u v, G.Adj u v → (u ∈ S ↔ v ∉ S)) :
    3 * valencyVariety G ≤ 2 * Fintype.card V + 1 := by
  have hS' : ∀ u v, G.Adj u v → (u ∈ Sᶜ ↔ v ∉ Sᶜ) := fun u v huv => by
    have huv' := hS u v huv
    simp only [mem_compl]
    tauto
  obtain ⟨hA, hcA, h1⟩ := degree_image_facts G S hS
  obtain ⟨hB, hcB, h2⟩ := degree_image_facts G Sᶜ hS'
  rw [compl_compl] at hB h2
  have hU : univ.image (fun v => G.degree v) =
      S.image (fun v => G.degree v) ∪ Sᶜ.image (fun v => G.degree v) := by
    rw [← image_union, union_compl]
  have hn := card_add_card_compl S
  rw [valencyVariety, hU, ← hn]
  rcases le_total S.card Sᶜ.card with hab | hba
  · exact three_mul_card_union_le _ _ _ _ hab hA hB hcA hcB h1 h2
  · rw [union_comm, add_comm S.card]
    exact three_mul_card_union_le _ _ _ _ hba hB hA hcB hcA h2 h1

omit [DecidableEq V] in
/-- **Bipartite valency-variety bound.**  A 2-colourable graph on `n` vertices has
at most `⌊(2n+1)/3⌋` distinct degrees, i.e. `3 w(G) ≤ 2 n + 1`.  Sharp (see
`cherry`).  Key lemma for the bipartite case of Melnikov's strict inequality
(arXiv:2610.09649, Conjecture 1.1); not stated in that paper. -/
theorem three_mul_valencyVariety_le_of_colorable_two (h : G.Colorable 2) :
    3 * valencyVariety G ≤ 2 * Fintype.card V + 1 := by
  classical
  obtain ⟨C⟩ := h
  refine three_mul_valencyVariety_le_of_bipartition G (univ.filter fun v => C v = 0)
    fun u v huv => ?_
  have hne := C.valid huv
  simp only [mem_filter, mem_univ, true_and]
  have hu := (C u).isLt
  have hv := (C v).isLt
  rw [Ne, Fin.ext_iff] at hne
  simp only [Fin.ext_iff, Fin.val_zero]
  omega

omit [DecidableEq V] in
/-- **Melnikov's strict inequality for graphs with `χ(G) ≤ 2`.**  Every 2-colourable
graph `G` with at least two vertices satisfies
`χ(G) > ⌈⌊w(G)/2⌋ / (|V(G)| - w(G))⌉` (arXiv:2610.09649, Conjecture 1.1, which
fails in general).  The first conjunct `w(G) < |V(G)|` certifies that the
denominator is positive, so the ceiling is not a division-by-zero junk value;
the ceiling is nonnegative, so `Int.toNat` is faithful. -/
theorem melnikov_strict_of_colorable_two (hn : 2 ≤ Fintype.card V) (h : G.Colorable 2) :
    valencyVariety G < Fintype.card V ∧
      ((⌈((valencyVariety G / 2 : ℕ) : ℚ) /
          ((Fintype.card V : ℚ) - valencyVariety G)⌉.toNat : ℕ) : ℕ∞) <
        G.chromaticNumber := by
  set w := valencyVariety G with hwdef
  set n := Fintype.card V with hndef
  have hw : 3 * w ≤ 2 * n + 1 := three_mul_valencyVariety_le_of_colorable_two G h
  have hlt : w < n := by omega
  refine ⟨hlt, ?_⟩
  have hfl : w / 2 + w ≤ n := by omega
  have hden : (0 : ℚ) < (n : ℚ) - w := by
    have hltq : (w : ℚ) < n := by exact_mod_cast hlt
    linarith
  have hq : ((w / 2 : ℕ) : ℚ) / ((n : ℚ) - w) ≤ 1 := by
    rw [div_le_one hden]
    have hflq : ((w / 2 : ℕ) : ℚ) + w ≤ n := by exact_mod_cast hfl
    linarith
  have hceil : ⌈((w / 2 : ℕ) : ℚ) / ((n : ℚ) - w)⌉.toNat ≤ 1 := by
    rw [Int.toNat_le, Int.ceil_le]
    exact_mod_cast hq
  haveI : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  rcases Nat.lt_or_ge w 2 with hw2 | hw2
  · -- At most one degree: the left side is `⌈0⌉ = 0 < χ(G)`.
    have h0 : w / 2 = 0 := by omega
    rw [h0]
    simp only [Nat.cast_zero, zero_div, Int.ceil_zero, Int.toNat_zero]
    exact h.chromaticNumber_pos
  · -- Two distinct degrees force an edge, so `χ(G) ≥ 2 > 1 ≥` the left side.
    obtain ⟨d₁, hd₁, d₂, hd₂, hne⟩ := one_lt_card.1 (show 1 < w by omega)
    have hpos : ∃ v, 0 < G.degree v := by
      obtain ⟨v₁, -, rfl⟩ := mem_image.1 hd₁
      obtain ⟨v₂, -, rfl⟩ := mem_image.1 hd₂
      rcases Nat.eq_zero_or_pos (G.degree v₁) with h₁ | h₁
      · exact ⟨v₂, by omega⟩
      · exact ⟨v₁, h₁⟩
    obtain ⟨v, hv⟩ := hpos
    obtain ⟨u, huv⟩ := (G.degree_pos_iff_exists_adj v).1 hv
    have h2 := G.two_le_chromaticNumber_of_adj huv
    refine lt_of_lt_of_le ?_ h2
    have hle1 : ((⌈((w / 2 : ℕ) : ℚ) / ((n : ℚ) - w)⌉.toNat : ℕ) : ℕ∞) ≤ 1 := by
      exact_mod_cast hceil
    exact lt_of_le_of_lt hle1 (by norm_num)

end Graph

end Candidates.MelnikovValencyBipartite
