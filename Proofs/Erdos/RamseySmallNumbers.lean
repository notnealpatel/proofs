/-
# Greenwood–Gleason small Ramsey numbers: `R(3,4) = 9` and `R(4,4) = 18`

## Source

R. E. Greenwood and A. M. Gleason, *Combinatorial relations and chromatic
graphs*, Canad. J. Math. 7 (1955), 1–7; surveyed in S. P. Radziszowski,
*Small Ramsey Numbers*, Electron. J. Combin., Dynamic Survey DS1
(table of two-colour classical numbers: `R(3,4) = 9`, `R(4,4) = 18`).

## Informal statement (target spec, recorded 2026-10-21)

  "Every graph on 9 vertices contains a triangle or an independent 4-set,
  and the circulant C8(1,4) shows 8 does not suffice. Every graph on 18
  vertices contains K4 or an independent 4-set, and the Paley graph P17
  (quadratic residues mod 17) shows 17 does not suffice. Hence R(4)=18."

## Encoding

A two-colouring of the edges of `K_n` is a graph `G` on `Fin n` (colour 1 =
edges of `G`, colour 2 = edges of `Gᶜ`); a red `K_a` is `¬ G.CliqueFree a`
and an independent `b`-set is `¬ Gᶜ.CliqueFree b`.  The diagonal Ramsey
number `R` and `HasRamseyProperty` are reused from the production module
`Erdos.Erdos77.ClassicalBounds` (Erdős #77 lane); Mathlib has no Ramsey
numbers (leandoc searches "Ramsey number", "SimpleGraph ramsey clique free
complement", and a grep of `Mathlib/` for `ramsey`, 2026-10-21: only
Hindman / Hales–Jewett hits).

## Proof outline

* `R(3,4) ≤ 9` (Greenwood–Gleason degree argument): in a triangle-free graph
  with no independent 4-set, every neighbourhood is independent (degree
  `≤ 3`), and every non-neighbourhood has no triangle and no independent
  3-set, hence `≤ 5` vertices by `R(3,3) ≤ 6`.  So `9` vertices force a
  `3`-regular graph on `9` vertices, contradicting the handshake lemma.
* `R(4,4) ≤ 18`: a vertex has `≥ 9` neighbours or `≥ 9` non-neighbours;
  apply `R(3,4) ≤ 9` there and extend by the vertex.
* Lower bounds: the circulant `C₈(1,4)` and the Paley graph `P₁₇`, checked by
  kernel `decide` (no `native_decide`).
-/
import Mathlib
import Erdos.Erdos77.ClassicalBounds

set_option autoImplicit false

namespace ErdosCandidates.RamseySmallNumbers

open SimpleGraph Finset
open ErdosCandidates.E77 (HasRamseyProperty R R_le_iff offDiagonal_cliques)

/-! ## Off-diagonal Ramsey property -/

/-- Every graph on `Fin n` contains an `a`-clique or an independent `b`-set
(a `b`-clique of the complement). -/
def HasRamseyProperty₂ (n a b : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬G.CliqueFree a ∨ ¬Gᶜ.CliqueFree b

/-- On the diagonal, the off-diagonal property is the repository's diagonal
Ramsey property `HasRamseyProperty` (definitional). -/
theorem hasRamseyProperty₂_self_iff (n k : ℕ) :
    HasRamseyProperty₂ n k k ↔ HasRamseyProperty n k := Iff.rfl

/-- The off-diagonal Ramsey number `R(a,b)`: the least `n` with
`HasRamseyProperty₂ n a b`. -/
noncomputable def ramseyNumber (a b : ℕ) : ℕ := sInf {n : ℕ | HasRamseyProperty₂ n a b}

example (a b : ℕ) : ramseyNumber a b = sInf {n : ℕ | HasRamseyProperty₂ n a b} := rfl

/-- Ground truth: a single vertex is a `1`-clique, so `n = 1` has the `(1,1)`
property, while `Fin 0` carries no `1`-clique. -/
example : HasRamseyProperty₂ 1 1 1 ∧ ¬HasRamseyProperty₂ 0 1 1 := by
  refine ⟨fun G => Or.inl fun h => h {0} (by simp), fun h => ?_⟩
  rcases h ⊥ with h' | h'
  · exact h' fun t ht => by
      have hc := t.card_le_univ
      rw [ht.card_eq] at hc
      simp at hc
  · exact h' fun t ht => by
      have hc := t.card_le_univ
      rw [ht.card_eq] at hc
      simp at hc

/-- The complement of a pulled-back graph is the pull-back of the complement. -/
theorem compl_comap_embedding {V W : Type*} (f : V ↪ W) (G : SimpleGraph W) :
    (G.comap f)ᶜ = Gᶜ.comap f := by
  ext x y
  simp only [compl_adj, comap_adj, ne_eq, f.injective.eq_iff]

/-- The off-diagonal Ramsey property is upward closed in the vertex count. -/
theorem hasRamseyProperty₂_of_le {n m a b : ℕ} (hnm : n ≤ m) (h : HasRamseyProperty₂ n a b) :
    HasRamseyProperty₂ m a b := by
  intro G
  let f : Fin n ↪ Fin m := ⟨Fin.castLE hnm, Fin.castLE_injective hnm⟩
  rcases h (G.comap f) with hr | hb
  · exact Or.inl fun hG => hr (hG.comap (SimpleGraph.Embedding.comap f G).isContained)
  · rw [compl_comap_embedding] at hb
    exact Or.inr fun hG => hb (hG.comap (SimpleGraph.Embedding.comap f Gᶜ).isContained)

/-- If `n + 1` vertices have the `(a,b)` property and `n` do not, then `R(a,b) = n + 1`. -/
theorem ramseyNumber_eq_of {n a b : ℕ} (h : HasRamseyProperty₂ (n + 1) a b)
    (hnot : ¬HasRamseyProperty₂ n a b) : ramseyNumber a b = n + 1 := by
  apply le_antisymm (Nat.sInf_le h)
  apply le_csInf ⟨n + 1, h⟩
  intro m hm
  by_contra hlt
  exact hnot (hasRamseyProperty₂_of_le (by omega) hm)

/-- On the diagonal, `ramseyNumber k k` is the repository's diagonal `R k`. -/
theorem ramseyNumber_self (k : ℕ) : ramseyNumber k k = R k := rfl

/-! ## `R(3,4) ≤ 9`: the Greenwood–Gleason degree argument -/

section Upper

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In a triangle-free graph with no independent `4`-set, every vertex has degree
at most `3` (its neighbourhood is an independent set). -/
theorem degree_le_three (h3 : G.CliqueFree 3) (h4 : Gᶜ.CliqueFree 4) (v : V) :
    G.degree v ≤ 3 := by
  by_contra hlt
  push Not at hlt
  have hcard : 4 ≤ (G.neighborFinset v).card := by
    rw [card_neighborFinset_eq_degree]; omega
  obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq hcard
  apply h4 t
  refine ⟨?_, htc⟩
  intro x hx y hy hxy
  rw [compl_adj]
  refine ⟨hxy, fun hadj => h3 {v, x, y} ?_⟩
  have hvx : G.Adj v x := (G.mem_neighborFinset v x).mp (ht hx)
  have hvy : G.Adj v y := (G.mem_neighborFinset v y).mp (ht hy)
  exact is3Clique_iff.mpr ⟨v, x, y, hvx, hvy, hadj, rfl⟩

/-- In a triangle-free graph with no independent `4`-set, every vertex has at
most `5` non-neighbours: the non-neighbourhood has no triangle and no independent
`3`-set, so `R(3,3) ≤ 6` bounds it. -/
theorem compl_degree_le_five (h3 : G.CliqueFree 3) (h4 : Gᶜ.CliqueFree 4) (v : V) :
    Gᶜ.degree v ≤ 5 := by
  by_contra hlt
  push Not at hlt
  have hcard : (2 + 2).choose 2 ≤ (Gᶜ.neighborFinset v).card := by
    rw [card_neighborFinset_eq_degree]
    have hchoose : (2 + 2).choose 2 = 6 := by decide
    omega
  rcases offDiagonal_cliques 2 2 G (Gᶜ.neighborFinset v) hcard with
    ⟨t, _, ht⟩ | ⟨t, hts, ht⟩
  · exact h3 t ht
  · apply h4 (insert v t)
    exact ht.insert fun b hb => (Gᶜ.mem_neighborFinset v b).mp (hts hb)

end Upper

/-- **`R(3,4) ≤ 9`** (Greenwood–Gleason 1955), for an arbitrary finite vertex
type: every graph on at least `9` vertices contains a triangle or an independent
`4`-set. -/
theorem not_cliqueFree_three_or_compl_four {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hV : 9 ≤ Fintype.card V) : ¬G.CliqueFree 3 ∨ ¬Gᶜ.CliqueFree 4 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨h3, h4⟩ := hcon
  have hdeg : ∀ v, G.degree v = 3 ∧ Fintype.card V = 9 := by
    intro v
    have hle := degree_le_three G h3 h4 v
    have hcle := compl_degree_le_five G h3 h4 v
    rw [degree_compl] at hcle
    omega
  have hsum : ∑ v, G.degree v = 2 * #G.edgeFinset := G.sum_degrees_eq_twice_card_edges
  have hconst : ∑ v, G.degree v = 27 := by
    rw [Finset.sum_congr rfl fun v _ => (hdeg v).1, Finset.sum_const, Finset.card_univ]
    obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    rw [(hdeg v).2, smul_eq_mul]
  omega

/-! ## Relative form and `R(4,4) ≤ 18` -/

/-- The complement of an induced graph is the induced graph of the complement. -/
theorem compl_induce {V : Type*} (G : SimpleGraph V) (s : Set V) :
    (G.induce s)ᶜ = Gᶜ.induce s := by
  ext x y
  simp only [compl_adj, comap_adj, Function.Embedding.subtype_apply, ne_eq, Subtype.ext_iff]

/-- `R(3,4) ≤ 9` relative to a vertex set: any set of at least `9` vertices
contains a triangle or an independent `4`-set. -/
theorem not_cliqueFreeOn_three_or_compl_four {V : Type*} (G : SimpleGraph V) (s : Set V)
    [Fintype s] (hs : 9 ≤ Fintype.card s) :
    ¬G.CliqueFreeOn s 3 ∨ ¬Gᶜ.CliqueFreeOn s 4 := by
  classical
  rcases not_cliqueFree_three_or_compl_four (G.induce s) hs with h | h
  · exact Or.inl fun hon => h ((cliqueFree_induce_iff G s 3).mpr hon)
  · rw [compl_induce] at h
    exact Or.inr fun hon => h ((cliqueFree_induce_iff Gᶜ s 4).mpr hon)

/-- A clique inside the neighbourhood of `v` extends by `v`. -/
theorem not_cliqueFree_succ_of_neighborSet {V : Type*} (G : SimpleGraph V) (v : V) {n : ℕ}
    (h : ¬G.CliqueFreeOn (G.neighborSet v) n) : ¬G.CliqueFree (n + 1) := by
  intro hfree
  apply h
  have hon := CliqueFreeOn.of_succ G (hfree.cliqueFreeOn (s := Set.univ)) (Set.mem_univ v)
  rwa [Set.univ_inter] at hon

/-- A clique inside some vertex set is a clique of the graph. -/
theorem not_cliqueFree_of_not_cliqueFreeOn {V : Type*} (G : SimpleGraph V) (s : Set V)
    {n : ℕ} (h : ¬G.CliqueFreeOn s n) : ¬G.CliqueFree n :=
  fun hfree => h (hfree.cliqueFreeOn)

/-- **`R(4,4) ≤ 18`** (Greenwood–Gleason 1955), for an arbitrary finite vertex
type: every graph on at least `18` vertices contains `K₄` or an independent
`4`-set. -/
theorem not_cliqueFree_four_or_compl_four {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hV : 18 ≤ Fintype.card V) : ¬G.CliqueFree 4 ∨ ¬Gᶜ.CliqueFree 4 := by
  classical
  obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hsplit : 9 ≤ G.degree v ∨ 9 ≤ Gᶜ.degree v := by
    have hlt := G.degree_lt_card_verts v
    rw [degree_compl]
    omega
  rcases hsplit with hdeg | hdeg
  · have hs : 9 ≤ Fintype.card (G.neighborSet v) := by rwa [card_neighborSet_eq_degree]
    rcases not_cliqueFreeOn_three_or_compl_four G (G.neighborSet v) hs with h | h
    · exact Or.inl (not_cliqueFree_succ_of_neighborSet G v h)
    · exact Or.inr (not_cliqueFree_of_not_cliqueFreeOn Gᶜ _ h)
  · have hs : 9 ≤ Fintype.card (Gᶜ.neighborSet v) := by rwa [card_neighborSet_eq_degree]
    rcases not_cliqueFreeOn_three_or_compl_four Gᶜ (Gᶜ.neighborSet v) hs with h | h
    · exact Or.inr (not_cliqueFree_succ_of_neighborSet Gᶜ v h)
    · rw [compl_compl] at h
      exact Or.inl (not_cliqueFree_of_not_cliqueFreeOn G _ h)

/-! ## Clique-freeness from vertex-tuple checks -/

/-- A graph is triangle-free when no three vertices are pairwise adjacent. -/
theorem cliqueFree_three_of_forall {V : Type*} (G : SimpleGraph V)
    (h : ∀ a b c : V, G.Adj a b → G.Adj a c → ¬G.Adj b c) : G.CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := is3Clique_iff.mp ht
  exact h a b c hab hac hbc

/-- A graph on a linearly ordered vertex type is `K₄`-free when no four
increasing vertices `a < b < c < d` are pairwise adjacent. -/
theorem cliqueFree_four_of_forall_lt {V : Type*} [LinearOrder V] (G : SimpleGraph V)
    (h : ∀ a b c d : V, a < b → b < c → c < d → G.Adj a b → G.Adj a c → G.Adj b c →
      G.Adj a d → G.Adj b d → ¬G.Adj c d) : G.CliqueFree 4 := by
  intro t ht
  let f := t.orderEmbOfFin ht.card_eq
  have hmem : ∀ i, f i ∈ t := fun i => t.orderEmbOfFin_mem ht.card_eq i
  have hlt : ∀ i j : Fin 4, i < j → f i < f j := fun i j hij => f.strictMono hij
  have hadj : ∀ i j : Fin 4, i < j → G.Adj (f i) (f j) := fun i j hij =>
    ht.isClique (hmem i) (hmem j) (hlt i j hij).ne
  exact h (f 0) (f 1) (f 2) (f 3) (hlt 0 1 (by decide)) (hlt 1 2 (by decide))
    (hlt 2 3 (by decide)) (hadj 0 1 (by decide)) (hadj 0 2 (by decide))
    (hadj 1 2 (by decide)) (hadj 0 3 (by decide)) (hadj 1 3 (by decide))
    (hadj 2 3 (by decide))

/-! ## The circulant `C₈(1,4)`: `8` vertices do not suffice for `(3,4)` -/

/-- Connection-set test of the circulant `C₈(1,4)`: `b - a ≡ ±1` or `4 (mod 8)`. -/
def circulant8Bool (a b : Fin 8) : Bool := [1, 4, 7].contains ((b.val + 8 - a.val) % 8)

/-- The circulant graph `C₈(1,4)` on `ℤ/8`: `i ~ j` iff `i - j ≡ ±1` or `4 (mod 8)`
(the 8-cycle with its four long diagonals). -/
def circulant8 : SimpleGraph (Fin 8) where
  Adj a b := circulant8Bool a b = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel circulant8.Adj := fun a b =>
  inferInstanceAs (Decidable (circulant8Bool a b = true))

/-- Ground truth: `C₈(1,4)` is the Cayley graph of `ℤ/8` with connection set
`{1, 4, 7} = {±1, 4}`. -/
theorem circulant8_adj_iff (a b : Fin 8) :
    circulant8.Adj a b ↔ ((b.val : ZMod 8) - (a.val : ZMod 8)) ∈ ({1, 4, -1} : Finset (ZMod 8)) := by
  revert a b
  decide

example : circulant8.Adj 0 1 ∧ circulant8.Adj 0 4 ∧ circulant8.Adj 0 7 ∧ ¬circulant8.Adj 0 2 := by
  decide

/-- `C₈(1,4)` is triangle-free. -/
theorem circulant8_cliqueFree_three : circulant8.CliqueFree 3 :=
  cliqueFree_three_of_forall _ (by decide)

/-- `C₈(1,4)` has no independent `4`-set. -/
theorem circulant8_compl_cliqueFree_four : circulant8ᶜ.CliqueFree 4 :=
  cliqueFree_four_of_forall_lt _ (by decide)

/-! ## The Paley graph `P₁₇`: `17` vertices do not suffice for `(4,4)` -/

/-- Quadratic-residue test mod `17`: `b - a ∈ {1, 2, 4, 8, 9, 13, 15, 16}`,
the nonzero squares of `ℤ/17`. -/
def paley17Bool (a b : Fin 17) : Bool :=
  [1, 2, 4, 8, 9, 13, 15, 16].contains ((b.val + 17 - a.val) % 17)

/-- The Paley graph `P₁₇` on `ℤ/17`: `i ~ j` iff `i - j` is a nonzero quadratic
residue mod `17` (symmetric since `-1` is a square mod `17`). -/
def paley17 : SimpleGraph (Fin 17) where
  Adj a b := paley17Bool a b = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel paley17.Adj := fun a b =>
  inferInstanceAs (Decidable (paley17Bool a b = true))

/-- Ground truth: `P₁₇` adjacency is "the difference is a nonzero square in `ZMod 17`". -/
theorem paley17_adj_iff (a b : Fin 17) :
    paley17.Adj a b ↔
      ((b.val : ZMod 17) - (a.val : ZMod 17)) ≠ 0 ∧
        IsSquare ((b.val : ZMod 17) - (a.val : ZMod 17)) := by
  revert a b
  decide

example : paley17.Adj 0 1 ∧ paley17.Adj 0 16 ∧ ¬paley17.Adj 0 3 := by decide

/-- Kernel check: no four increasing vertices of `P₁₇` are pairwise adjacent. -/
theorem paley17_no_four_adj :
    ∀ a b : Fin 17, a < b → paley17Bool a b = true →
      ∀ c : Fin 17, b < c → paley17Bool a c = true → paley17Bool b c = true →
      ∀ d : Fin 17, c < d → paley17Bool a d = true → paley17Bool b d = true →
      paley17Bool c d = false := by
  decide

/-- Kernel check: no four increasing vertices of `P₁₇` are pairwise non-adjacent. -/
theorem paley17_no_four_nonadj :
    ∀ a b : Fin 17, a < b → paley17Bool a b = false →
      ∀ c : Fin 17, b < c → paley17Bool a c = false → paley17Bool b c = false →
      ∀ d : Fin 17, c < d → paley17Bool a d = false → paley17Bool b d = false →
      paley17Bool c d = true := by
  decide

/-- `P₁₇` is `K₄`-free. -/
theorem paley17_cliqueFree_four : paley17.CliqueFree 4 := by
  refine cliqueFree_four_of_forall_lt _ fun a b c d hab hbc hcd ab ac bc ad bd cd => ?_
  have hfalse := paley17_no_four_adj a b hab ab c hbc ac bc d hcd ad bd
  change paley17Bool c d = true at cd
  rw [hfalse] at cd
  exact Bool.false_ne_true cd

/-- `P₁₇` has no independent `4`-set. -/
theorem paley17_compl_cliqueFree_four : paley17ᶜ.CliqueFree 4 := by
  refine cliqueFree_four_of_forall_lt _ fun a b c d hab hbc hcd ab ac bc ad bd cd => ?_
  simp only [compl_adj, paley17, Bool.not_eq_true] at ab ac bc ad bd cd
  have htrue := paley17_no_four_nonadj a b hab ab.2 c hbc ac.2 bc.2 d hcd ad.2 bd.2
  rw [cd.2] at htrue
  exact Bool.false_ne_true htrue

/-! ## Main theorems -/

/-- Every graph on `9` vertices contains a triangle or an independent `4`-set. -/
theorem hasRamseyProperty₂_nine_three_four : HasRamseyProperty₂ 9 3 4 := fun G =>
  not_cliqueFree_three_or_compl_four G (by simp)

/-- `8` vertices do not suffice for `(3,4)`: the circulant `C₈(1,4)` is
triangle-free with no independent `4`-set. -/
theorem not_hasRamseyProperty₂_eight_three_four : ¬HasRamseyProperty₂ 8 3 4 := by
  intro h
  rcases h circulant8 with h3 | h4
  · exact h3 circulant8_cliqueFree_three
  · exact h4 circulant8_compl_cliqueFree_four

/-- **Greenwood–Gleason (1955), `R(3,4) = 9`**, as the pair of finite statements:
every graph on `9` vertices has a triangle or an independent `4`-set, and some
graph on `8` vertices has neither. -/
theorem ramsey34 : HasRamseyProperty₂ 9 3 4 ∧ ¬HasRamseyProperty₂ 8 3 4 :=
  ⟨hasRamseyProperty₂_nine_three_four, not_hasRamseyProperty₂_eight_three_four⟩

/-- **Greenwood–Gleason (1955)**: the off-diagonal Ramsey number `R(3,4)` is `9`. -/
theorem ramseyNumber_three_four : ramseyNumber 3 4 = 9 :=
  ramseyNumber_eq_of hasRamseyProperty₂_nine_three_four not_hasRamseyProperty₂_eight_three_four

/-- Every graph on `18` vertices contains `K₄` or an independent `4`-set. -/
theorem hasRamseyProperty_eighteen_four : HasRamseyProperty 18 4 := fun G =>
  not_cliqueFree_four_or_compl_four G (by simp)

/-- `17` vertices do not suffice for `(4,4)`: the Paley graph `P₁₇` is
`K₄`-free with no independent `4`-set. -/
theorem not_hasRamseyProperty_seventeen_four : ¬HasRamseyProperty 17 4 := by
  intro h
  rcases h paley17 with h4 | h4c
  · exact h4 paley17_cliqueFree_four
  · exact h4c paley17_compl_cliqueFree_four

/-- **Greenwood–Gleason (1955), `R(4) = R(4,4) = 18`**, for the repository's
diagonal Ramsey number `R` (Erdős #77 lane). -/
theorem R_four : R 4 = 18 := by
  apply le_antisymm ((R_le_iff 18 4).mpr hasRamseyProperty_eighteen_four)
  by_contra hlt
  exact not_hasRamseyProperty_seventeen_four ((R_le_iff 17 4).mp (by omega))

/-- **Greenwood–Gleason (1955)**: the off-diagonal Ramsey number `R(4,4)` is `18`. -/
theorem ramseyNumber_four_four : ramseyNumber 4 4 = 18 := R_four

end ErdosCandidates.RamseySmallNumbers
