/-
# Extremal number of digraphs without a 2-strongly connected subdigraph

## Source

Qinglin Wang, Yingzhi Tian, "Extremal Problems for the Family of
k-Strongly Connected Digraphs", arXiv:2605.01269.  Section 4: Definition 4.1 (the
construction `D_U(n,k)`), Theorem 4.2 (saturation and arc count), and
the Conjecture stated right after Theorem 4.2:

```
Conjecture. For sufficiently large n,
  ex(n, D_k) = (3/2)(k - 4/3)(n - k + 1) + binom(n, 2).
```

## Result

The `k = 2` case of the conjecture, for every `n ≥ 1`:

  ex(n, D_2) = binom(n, 2) + (n - 1),

which is the conjectured value since (3/2)(2 - 4/3) = 1.  The paper
proves only the general upper bound binom(n-k+1, 2) + (17/6)(k-1)(n-k+1)
for n ≥ 3(k-1) and the lower-bound construction of Theorem 4.2; the
`k = 2` equality is not stated or proved there. The paper defines `ex`
as the maximum arc count among saturated digraphs; both the free and
saturated formulations are proved below.

Argument (elementary, digon forest).  The digon graph `G₂` joins `u ≠ v`
when both arcs `(u,v)` and `(v,u)` are present.  A cycle of length
`≥ 3` in `G₂` spans a 2-strongly connected subdigraph (deleting one
vertex leaves a bidirected path), so for a `D_2`-free digraph `G₂` is a
forest and has at most `n - 1` edges; every unordered pair carries at
most one arc unless it is a digon, so `|A| ≤ binom(n,2) + (n - 1)`.
Sharpness: vertex `0` is joined by digons to every other vertex, and
the remaining vertices carry the transitive tournament `i → j` for
`i < j`.  The same digon count gives the general reduction
`|A| ≤ binom(n,2) + |E(G_k)|` with `G_k` free of `k`-connected
subgraphs (`card_le_choose_two_add_card_digonGraph`,
`digonGraph_not_kStrongOn`).

## Formal conventions

* A digraph on `V` is a loopless arc set `A : Finset (V × V)`.
* `StrongOn R W`: every ordered pair of `W` is joined by an `R`-walk
  inside `W` (walks and dipaths give the same reachability).
* `KStrongOn R U k`: `k + 1 ≤ |U|` and `U \ S` is strongly connected
  for every `S ⊆ U` with `|S| < k`.  This is `κ ≥ k` in the paper's
  sense: a separator of size `< k` would be a set whose removal leaves a
  non-strong or trivial digraph, and `|U| ≥ k + 1` rules out the
  trivial case.
* `ContainsKStrong A k`: some subdigraph `(U, B)`, `B ⊆ A`, is
  `k`-strongly connected; `containsKStrong_iff` shows this is the same
  as an induced one.
* `IsSaturated A k`: `A` is loopless, `D_k`-free, and adding any missing
  non-loop arc creates a `k`-strongly connected subdigraph.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.StronglyConnectedDigraphExtremalTwo

open Finset

variable {V : Type*}

/-! ## Definitions -/

/-- `StrongOn R W`: the subdigraph induced on `W` by the arc relation `R` is strongly
connected, i.e. every ordered pair `u, v ∈ W` is joined by an `R`-walk staying in `W`. -/
def StrongOn (R : V → V → Prop) (W : Finset V) : Prop :=
  ∀ u ∈ W, ∀ v ∈ W, Relation.ReflTransGen (fun a b => a ∈ W ∧ b ∈ W ∧ R a b) u v

/-- `KStrongOn R U k`: the subdigraph induced on `U` by `R` is `k`-strongly connected in the
sense of arXiv:2605.01269 (`κ ≥ k`): it has at least `k + 1` vertices and deleting any set
`S` of fewer than `k` vertices leaves a strongly connected digraph. -/
def KStrongOn [DecidableEq V] (R : V → V → Prop) (U : Finset V) (k : ℕ) : Prop :=
  k + 1 ≤ U.card ∧ ∀ S ⊆ U, S.card < k → StrongOn R (U \ S)

/-- The digraph with arc set `A` contains a `k`-strongly connected subdigraph: a vertex set
`U` and an arc set `B ⊆ A` such that `(U, B)` is `k`-strongly connected. -/
def ContainsKStrong [DecidableEq V] (A : Finset (V × V)) (k : ℕ) : Prop :=
  ∃ B ⊆ A, ∃ U : Finset V, KStrongOn (fun a b => (a, b) ∈ B) U k

/-- The arc set `A` has no loops (a strict digraph in the sense of the paper). -/
def IsLoopless (A : Finset (V × V)) : Prop := ∀ p ∈ A, p.1 ≠ p.2

/-- `D_k`-saturation (arXiv:2605.01269, Section 1): `A` is loopless, contains no
`k`-strongly connected subdigraph, and adding any missing non-loop arc creates one. -/
def IsSaturated [DecidableEq V] (A : Finset (V × V)) (k : ℕ) : Prop :=
  IsLoopless A ∧ ¬ContainsKStrong A k ∧
    ∀ p : V × V, p.1 ≠ p.2 → p ∉ A → ContainsKStrong (insert p A) k

/-- The digon graph of `A`: `u ≠ v` are adjacent iff both arcs `(u,v)` and `(v,u)` lie
in `A`. -/
def digonGraph (A : Finset (V × V)) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (u, v) ∈ A ∧ (v, u) ∈ A
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Adjacency in the digon graph is decidable. -/
instance digonGraph.decidableRel [DecidableEq V] (A : Finset (V × V)) :
    DecidableRel (digonGraph A).Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧ (u, v) ∈ A ∧ (v, u) ∈ A))

/-- The extremal construction on `Fin n`: arcs `i → j` for `i < j` (a transitive
tournament, containing the arcs `0 → j`) together with the reverse arcs `j → 0` for
`j ≠ 0`, so vertex `0` is joined by digons to every other vertex. -/
def extremalDigraph (n : ℕ) : Finset (Fin n × Fin n) :=
  univ.filter (fun p => p.1 < p.2 ∨ (p.2.val = 0 ∧ p.1.val ≠ 0))

/-! ## Generic relation lemmas -/

/-- Monotonicity of reflexive-transitive closure in the relation. -/
lemma reflTransGen_mono' {r p : V → V → Prop} (hrp : ∀ a b, r a b → p a b) {u v : V}
    (h : Relation.ReflTransGen r u v) : Relation.ReflTransGen p u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (hrp _ _ hbc)

/-- The reflexive-transitive closure of a symmetric relation is symmetric. -/
lemma reflTransGen_symm' {r : V → V → Prop} (hr : ∀ a b, r a b → r b a) {u v : V}
    (h : Relation.ReflTransGen r u v) : Relation.ReflTransGen r v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hr _ _ hbc) ih

/-- Walks inside `W` are walks inside any `W' ⊇ W`. -/
lemma reflTransGen_restrict_mono {R : V → V → Prop} {W W' : Finset V} (hW : W ⊆ W')
    {u v : V} (h : Relation.ReflTransGen (fun a b => a ∈ W ∧ b ∈ W ∧ R a b) u v) :
    Relation.ReflTransGen (fun a b => a ∈ W' ∧ b ∈ W' ∧ R a b) u v :=
  reflTransGen_mono' (fun _ _ hab => ⟨hW hab.1, hW hab.2.1, hab.2.2⟩) h

/-- `k`-strong connectivity is monotone in the arc relation. -/
lemma kStrongOn_mono [DecidableEq V] {R R' : V → V → Prop} (hRR' : ∀ a b, R a b → R' a b)
    {U : Finset V} {k : ℕ} (h : KStrongOn R U k) : KStrongOn R' U k := by
  refine ⟨h.1, fun S hS hSk u hu v hv => ?_⟩
  exact reflTransGen_mono' (fun a b hab => ⟨hab.1, hab.2.1, hRR' a b hab.2.2⟩)
    (h.2 S hS hSk u hu v hv)

/-- Containing a `k`-strongly connected subdigraph is the same as containing an induced
one. -/
lemma containsKStrong_iff [DecidableEq V] (A : Finset (V × V)) (k : ℕ) :
    ContainsKStrong A k ↔ ∃ U : Finset V, KStrongOn (fun a b => (a, b) ∈ A) U k := by
  constructor
  · rintro ⟨B, hBA, U, hU⟩
    exact ⟨U, kStrongOn_mono (fun a b h => hBA h) hU⟩
  · rintro ⟨U, hU⟩
    exact ⟨A, subset_refl A, U, hU⟩

/-- The complete digraph on `k + 1` vertices is `k`-strongly connected. -/
lemma kStrongOn_complete (k : ℕ) :
    KStrongOn (fun a b : Fin (k + 1) => a ≠ b) univ k := by
  refine ⟨by simp, fun S _ _ u hu v hv => ?_⟩
  by_cases huv : u = v
  · subst huv
    exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨hu, hv, huv⟩

/-! ## Examples -/

/-- `K₃*` is `2`-strongly connected. -/
example : KStrongOn (fun a b : Fin 3 => a ≠ b) univ 2 := kStrongOn_complete 2

/-- `K₄*` is `3`-strongly connected but not `4`-strongly connected (too few vertices). -/
example : KStrongOn (fun a b : Fin 4 => a ≠ b) univ 3 ∧
    ¬KStrongOn (fun a b : Fin 4 => a ≠ b) univ 4 :=
  ⟨kStrongOn_complete 3, fun h => by simpa using h.1⟩

/-- The directed triangle `0 → 1 → 2 → 0` is not `2`-strongly connected: deleting `0`
leaves the single arc `1 → 2`. -/
example : ¬KStrongOn (fun a b : Fin 3 => b = a + 1) univ 2 := by
  rintro ⟨-, hS⟩
  have h := hS {0} (subset_univ _) (by simp) 2 (by decide) 1 (by decide)
  have hinv : ∀ x y : Fin 3, Relation.ReflTransGen
      (fun a b => a ∈ univ \ {(0 : Fin 3)} ∧ b ∈ univ \ {(0 : Fin 3)} ∧ b = a + 1) x y →
      x = 2 → y = 2 := by
    intro x y hxy
    induction hxy with
    | refl => exact id
    | tail _ hcd ih =>
      intro hx
      obtain ⟨-, hd, hd1⟩ := hcd
      rw [ih hx] at hd1
      subst hd1
      exact absurd hd (by decide)
  exact absurd (hinv 2 1 h rfl) (by decide)

example : (extremalDigraph 3).card = 5 := by decide
example : (extremalDigraph 4).card = 9 := by decide
example : (5, 0) ∈ extremalDigraph 6 ∧ (0, 5) ∈ extremalDigraph 6 ∧
    (2, 4) ∈ extremalDigraph 6 ∧ (4, 2) ∉ extremalDigraph 6 := by
  decide

/-! ## Digon cycles are 2-strongly connected -/
/-- A path `g 0, g 1, ..., g (j+1)` of digons, avoiding `g (last)`, is strongly connected. -/
lemma strongOn_path [DecidableEq V] (A : Finset (V × V)) (j : ℕ) (g : Fin (j + 3) → V)
    (hg : Function.Injective g)
    (hstep : ∀ e (he : e + 1 < j + 3), (digonGraph A).Adj (g ⟨e, by omega⟩) (g ⟨e + 1, he⟩)) :
    StrongOn (fun a b => (a, b) ∈ A) ((univ.image g) \ {g (Fin.last (j + 2))}) := by
  set W := (univ.image g) \ {g (Fin.last (j + 2))} with hW
  let D : V → V → Prop := fun a b => a ∈ W ∧ b ∈ W ∧ (digonGraph A).Adj a b
  have hDsymm : ∀ a b, D a b → D b a := fun a b h => ⟨h.2.1, h.1, h.2.2.symm⟩
  have hmemW : ∀ e (he : e < j + 2), g ⟨e, by omega⟩ ∈ W := by
    intro e he
    simp only [hW, mem_sdiff, mem_image, mem_univ, true_and, mem_singleton]
    refine ⟨⟨_, rfl⟩, fun h => ?_⟩
    have := congrArg Fin.val (hg h)
    simp only [Fin.val_last] at this
    omega
  have hchain : ∀ e (he : e < j + 2), Relation.ReflTransGen D (g 0) (g ⟨e, by omega⟩) := by
    intro e
    induction e with
    | zero => intro _; exact Relation.ReflTransGen.refl
    | succ e ih =>
      intro he
      exact (ih (by omega)).tail ⟨hmemW e (by omega), hmemW (e + 1) he, hstep e (by omega)⟩
  have hreach : ∀ u ∈ W, Relation.ReflTransGen D (g 0) u := by
    intro u hu
    simp only [hW, mem_sdiff, mem_image, mem_univ, true_and, mem_singleton] at hu
    obtain ⟨⟨y, rfl⟩, hy⟩ := hu
    have hylt : y.val < j + 2 := by
      have hy' : y ≠ Fin.last (j + 2) := fun h => hy (h ▸ rfl)
      have := Fin.val_lt_last hy'
      simpa using this
    exact hchain y.val hylt
  intro u hu v hv
  have huv : Relation.ReflTransGen D u v :=
    (reflTransGen_symm' hDsymm (hreach u hu)).trans (hreach v hv)
  exact reflTransGen_mono' (fun a b h => ⟨h.1, h.2.1, h.2.2.2.1⟩) huv

/-- A cycle of digons of length at least `3` spans a `2`-strongly connected subdigraph. -/
lemma kStrongOn_two_of_copy_cycleGraph [DecidableEq V] (A : Finset (V × V)) (j : ℕ)
    (f : SimpleGraph.Copy (SimpleGraph.cycleGraph (j + 3)) (digonGraph A)) :
    ∃ U : Finset V, KStrongOn (fun a b => (a, b) ∈ A) U 2 := by
  have hinj : Function.Injective f := f.injective
  have hadj : ∀ i : Fin (j + 3), (digonGraph A).Adj (f i) (f (i + 1)) := by
    intro i
    apply f.toHom.map_adj
    exact (SimpleGraph.cycleGraph_adj (n := j + 1)).mpr (Or.inr (by simp))
  let U : Finset V := univ.image f
  have hcard : U.card = j + 3 := by
    rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  -- removing any single vertex `f x` leaves a strongly connected digraph
  have hone : ∀ x : Fin (j + 3), StrongOn (fun a b => (a, b) ∈ A) (U \ {f x}) := by
    intro x
    let g : Fin (j + 3) → V := fun i => f (i + (x + 1))
    have hg : Function.Injective g := fun a b h => add_right_cancel (hinj h)
    have hgU : univ.image g = U := by
      ext v
      simp only [mem_image, mem_univ, true_and, U, g]
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨_, rfl⟩
      · rintro ⟨i, rfl⟩; exact ⟨i - (x + 1), by rw [sub_add_cancel]⟩
    have hglast : g (Fin.last (j + 2)) = f x := by
      simp only [g]
      congr 1
      rw [← add_assoc, add_right_comm, Fin.last_add_one, zero_add]
    have hstep : ∀ e (he : e + 1 < j + 3),
        (digonGraph A).Adj (g ⟨e, by omega⟩) (g ⟨e + 1, he⟩) := by
      intro e he
      have h1 : (⟨e + 1, he⟩ : Fin (j + 3)) = ⟨e, by omega⟩ + 1 := by
        ext
        simp [Fin.val_add]
        exact (Nat.mod_eq_of_lt he).symm
      simp only [g, h1]
      rw [add_right_comm]
      exact hadj _
    have := strongOn_path A j g hg hstep
    rwa [hgU, hglast] at this
  refine ⟨U, by rw [hcard]; omega, ?_⟩
  intro S hSU hS
  rcases Nat.lt_succ_iff.mp hS |> Nat.le_one_iff_eq_zero_or_eq_one.mp with h0 | h1
  · rw [card_eq_zero] at h0
    subst h0
    rw [sdiff_empty]
    intro u hu v hv
    have hlt : ({u, v} : Finset V).card < U.card := by
      rw [hcard]
      exact (card_le_two).trans_lt (by omega)
    obtain ⟨w, hwU, hwuv⟩ := exists_mem_notMem_of_card_lt_card hlt
    obtain ⟨x, -, rfl⟩ := mem_image.mp hwU
    simp only [mem_insert, mem_singleton, not_or] at hwuv
    have hsub : U \ {f x} ⊆ U := sdiff_subset
    exact reflTransGen_restrict_mono hsub
      (hone x u (by simp [hu, Ne.symm hwuv.1]) v (by simp [hv, Ne.symm hwuv.2]))
  · obtain ⟨s, rfl⟩ := card_eq_one.mp h1
    obtain ⟨x, -, rfl⟩ := mem_image.mp (hSU (mem_singleton_self s))
    exact hone x

/-! ## Upper bound: the digon graph is a forest -/
/-- If no vertex set spans a `2`-strong subdigraph, the digon graph is a forest. -/
lemma digonGraph_isAcyclic [DecidableEq V] (A : Finset (V × V))
    (hfree : ∀ U : Finset V, ¬KStrongOn (fun a b => (a, b) ∈ A) U 2) :
    (digonGraph A).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_free_cycleGraph]
  intro m hm hcopy
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
  obtain ⟨f⟩ := hcopy
  obtain ⟨U, hU⟩ := kStrongOn_two_of_copy_cycleGraph A j f
  exact hfree U hU

/-- A forest on a finite nonempty vertex type has at most `|V| - 1` edges. -/
lemma card_edgeFinset_le_of_isAcyclic [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (hG : G.IsAcyclic) :
    G.edgeFinset.card ≤ Fintype.card V - 1 := by
  classical
  obtain ⟨F, hGF, -, hF⟩ :=
    SimpleGraph.connected_top.exists_isTree_le_of_le_of_isAcyclic le_top hG
  have hcardF := hF.card_edgeFinset
  have hsub : G.edgeFinset ⊆ F.edgeFinset := SimpleGraph.edgeFinset_subset_edgeFinset.mpr hGF
  have := card_le_card hsub
  omega

/-- Arc count of a loopless digraph is at most `C(n,2)` plus the number of digons. -/
lemma card_le_card_top_add_card_digon [Fintype V] [LinearOrder V] (A : Finset (V × V))
    (hloop : ∀ p ∈ A, p.1 ≠ p.2) :
    A.card ≤ (⊤ : SimpleGraph V).edgeFinset.card + (digonGraph A).edgeFinset.card := by
  let φ : V × V → Sym2 V × Bool := fun p =>
    (s(p.1, p.2), decide (p.1 < p.2 ∨ (p.2, p.1) ∉ A))
  let T : Finset (Sym2 V × Bool) :=
    ((⊤ : SimpleGraph V).edgeFinset ×ˢ {true}) ∪ ((digonGraph A).edgeFinset ×ˢ {false})
  have hmaps : Set.MapsTo φ A T := by
    rintro ⟨a, b⟩ hp
    rw [Finset.mem_coe] at hp
    have hab : a ≠ b := hloop _ hp
    simp only [T, Finset.mem_coe, mem_union, mem_product, mem_singleton,
      SimpleGraph.mem_edgeFinset]
    by_cases hb : a < b ∨ (b, a) ∉ A
    · have hφ : φ (a, b) = (s(a, b), true) := Prod.ext rfl (decide_eq_true hb)
      rw [hφ]
      exact Or.inl ⟨hab, rfl⟩
    · have hφ : φ (a, b) = (s(a, b), false) := Prod.ext rfl (decide_eq_false hb)
      have hba : (b, a) ∈ A := by
        by_contra h
        exact hb (Or.inr h)
      rw [hφ]
      exact Or.inr ⟨⟨hab, hp, hba⟩, rfl⟩
  have hinj : Set.InjOn φ A := by
    rintro ⟨a, b⟩ hp ⟨c, d⟩ hq hφ
    rw [Finset.mem_coe] at hp hq
    simp only [φ, Prod.mk.injEq, Sym2.eq_iff, decide_eq_decide] at hφ
    obtain ⟨hs, hdec⟩ := hφ
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exfalso
      have hab : a ≠ b := hloop _ hp
      simp only [hp, hq, not_true_eq_false, or_false] at hdec
      rcases lt_or_gt_of_ne hab with h | h
      · exact lt_asymm h (hdec.mp h)
      · exact lt_asymm h (hdec.mpr h)
  calc A.card ≤ T.card := card_le_card_of_injOn φ hmaps hinj
    _ ≤ ((⊤ : SimpleGraph V).edgeFinset ×ˢ {true}).card +
        ((digonGraph A).edgeFinset ×ˢ {false}).card := card_union_le _ _
    _ = _ := by simp

/-- **Reduction to graphs.** Every loopless digraph on `Fin n` has at most
`binom(n,2) + |E(G₂)|` arcs, where `G₂` is its digon graph. -/
theorem card_le_choose_two_add_card_digonGraph (n : ℕ) (A : Finset (Fin n × Fin n))
    (hloop : IsLoopless A) :
    A.card ≤ n.choose 2 + (digonGraph A).edgeFinset.card := by
  have hcount := card_le_card_top_add_card_digon A hloop
  rwa [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin] at hcount

/-- **Reduction to graphs.** If a digraph contains no `k`-strongly connected subdigraph, its
digon graph contains no `k`-connected subgraph (a bidirected `k`-connected graph is
`k`-strongly connected).  Together with `card_le_choose_two_add_card_digonGraph` this gives
`ex(n, D_k) ≤ binom(n,2) + ex(n, H_k)` for the family `H_k` of `k`-connected graphs. -/
theorem digonGraph_not_kStrongOn [DecidableEq V] (A : Finset (V × V)) (k : ℕ)
    (hfree : ¬ContainsKStrong A k) (U : Finset V) :
    ¬KStrongOn (digonGraph A).Adj U k := fun hU =>
  hfree ((containsKStrong_iff A k).mpr ⟨U, kStrongOn_mono (fun _ _ h => h.2.1) hU⟩)

/-- **Upper bound for `k = 2`.** A loopless digraph on `n ≥ 1` vertices with no
`2`-strongly connected subdigraph has at most `binom(n,2) + (n - 1)` arcs. -/
theorem card_le_of_not_containsKStrong_two (n : ℕ) (hn : 0 < n) (A : Finset (Fin n × Fin n))
    (hloop : IsLoopless A) (hfree : ¬ContainsKStrong A 2) :
    A.card ≤ n.choose 2 + (n - 1) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hfree' : ∀ U : Finset (Fin n), ¬KStrongOn (fun a b => (a, b) ∈ A) U 2 :=
    fun U hU => hfree ((containsKStrong_iff A 2).mpr ⟨U, hU⟩)
  have hacyc := digonGraph_isAcyclic A hfree'
  have hforest := card_edgeFinset_le_of_isAcyclic (digonGraph A) hacyc
  have hcount := card_le_choose_two_add_card_digonGraph n A hloop
  rw [Fintype.card_fin] at hforest
  omega

/-! ## Sharpness: the construction -/

/-- The construction has no loops. -/
lemma extremalDigraph_isLoopless (n : ℕ) : IsLoopless (extremalDigraph n) := by
  rintro ⟨a, b⟩ hp hab
  simp only [extremalDigraph, mem_filter, mem_univ, true_and] at hp
  simp only at hab
  subst hab
  rcases hp with h | h
  · exact lt_irrefl a h
  · exact h.2 h.1

/-- The construction has `binom(n,2) + (n - 1)` arcs for `n ≥ 1`. -/
lemma card_extremalDigraph (n : ℕ) (hn : 0 < n) :
    (extremalDigraph n).card = n.choose 2 + (n - 1) := by
  let L : Finset (Fin n × Fin n) := univ.filter (fun p => p.1 < p.2)
  let B : Finset (Fin n × Fin n) := univ.filter (fun p => p.2.val = 0 ∧ p.1.val ≠ 0)
  have hunion : extremalDigraph n = L ∪ B := by
    ext p
    simp [extremalDigraph, L, B]
  have hdisj : Disjoint L B := by
    rw [disjoint_left]
    rintro ⟨a, b⟩ hL hB
    simp only [L, B, mem_filter, mem_univ, true_and] at hL hB
    have : a.val < b.val := hL
    omega
  have hL : L.card = n.choose 2 := by
    simpa using Fintype.card_product_filter_lt (α := Fin n)
  have hB : B.card = n - 1 := by
    let z : Fin n := ⟨0, hn⟩
    have hBimg : B = (univ.erase z).image (fun i => (i, z)) := by
      ext ⟨a, b⟩
      simp only [B, mem_filter, mem_univ, true_and, mem_image, mem_erase, ne_eq, Prod.mk.injEq,
        z, Fin.ext_iff]
      constructor
      · rintro ⟨hb, ha⟩
        exact ⟨a, ⟨ha, trivial⟩, rfl, hb.symm⟩
      · rintro ⟨i, ⟨hi, -⟩, hia, hb⟩
        exact ⟨hb.symm, by rw [← hia]; exact hi⟩
    rw [hBimg, card_image_of_injective _ (fun i j h => (Prod.mk.inj h).1),
      card_erase_of_mem (mem_univ z), card_univ, Fintype.card_fin]
  rw [hunion, card_union_of_disjoint hdisj, hL, hB]

/-- The construction contains no `2`-strongly connected induced subdigraph: deleting vertex
`0` (if present) leaves a transitive tournament on at least two vertices. -/
lemma extremalDigraph_not_kStrongOn_two (n : ℕ) (U : Finset (Fin n)) :
    ¬KStrongOn (fun a b => (a, b) ∈ extremalDigraph n) U 2 := by
  rintro ⟨hcard, hS⟩
  let S : Finset (Fin n) := U.filter (fun i => i.val = 0)
  have hSU : S ⊆ U := filter_subset _ _
  have hS1 : S.card ≤ 1 := by
    rw [card_le_one]
    intro a ha b hb
    simp only [S, mem_filter] at ha hb
    exact Fin.ext (ha.2.trans hb.2.symm)
  have hW : 1 < (U \ S).card := by
    rw [card_sdiff_of_subset hSU]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp hW
  have hstrong := hS S hSU (by omega)
  -- along any path inside `U \ S` the vertices strictly increase
  have hmono : ∀ x y : Fin n, Relation.ReflTransGen
      (fun c d => c ∈ U \ S ∧ d ∈ U \ S ∧ (c, d) ∈ extremalDigraph n) x y → x ≤ y := by
    intro x y hxy
    induction hxy with
    | refl => exact le_refl _
    | tail _ hcd ih =>
      obtain ⟨-, hd, hcd⟩ := hcd
      simp only [extremalDigraph, mem_filter, mem_univ, true_and] at hcd
      simp only [S, mem_sdiff, mem_filter, not_and] at hd
      rcases hcd with h | h
      · exact ih.trans h.le
      · exact absurd h.1 (hd.2 hd.1)
  rcases lt_or_gt_of_ne hab with h | h
  · exact absurd (hmono b a (hstrong b hb a ha)) (not_le.mpr h)
  · exact absurd (hmono a b (hstrong a ha b hb)) (not_le.mpr h)

/-- The construction contains no `2`-strongly connected subdigraph. -/
theorem extremalDigraph_not_containsKStrong_two (n : ℕ) :
    ¬ContainsKStrong (extremalDigraph n) 2 := by
  rw [containsKStrong_iff]
  rintro ⟨U, hU⟩
  exact extremalDigraph_not_kStrongOn_two n U hU

/-! ## Main theorems -/

/-- **`ex(n, D_2)` over `D_2`-free digraphs.** For `n ≥ 1`, the maximum number of arcs of a
loopless digraph on `n` vertices with no `2`-strongly connected subdigraph is
`binom(n,2) + (n - 1)`. -/
theorem isGreatest_card_free_two (n : ℕ) (hn : 0 < n) :
    IsGreatest {m | ∃ A : Finset (Fin n × Fin n),
      IsLoopless A ∧ ¬ContainsKStrong A 2 ∧ A.card = m} (n.choose 2 + (n - 1)) := by
  refine ⟨⟨extremalDigraph n, extremalDigraph_isLoopless n,
    extremalDigraph_not_containsKStrong_two n, card_extremalDigraph n hn⟩, ?_⟩
  rintro m ⟨A, hloop, hfree, rfl⟩
  exact card_le_of_not_containsKStrong_two n hn A hloop hfree

/-- **`ex(n, D_2) = binom(n,2) + (n - 1)`** (the `k = 2` case of the Conjecture after
Theorem 4.2 of arXiv:2605.01269, for every `n ≥ 1`).  With the paper's definition of
`ex(n, D)` as the maximum number of arcs of an `n`-vertex `D`-saturated digraph, the
maximum over `D_2`-saturated loopless digraphs on `Fin n` is `binom(n,2) + (n - 1)`. -/
theorem isGreatest_card_saturated_two (n : ℕ) (hn : 0 < n) :
    IsGreatest {m | ∃ A : Finset (Fin n × Fin n), IsSaturated A 2 ∧ A.card = m}
      (n.choose 2 + (n - 1)) := by
  refine ⟨⟨extremalDigraph n, ⟨extremalDigraph_isLoopless n,
    extremalDigraph_not_containsKStrong_two n, fun p hp hpA => ?_⟩,
    card_extremalDigraph n hn⟩, ?_⟩
  · by_contra hfree
    have hloop : IsLoopless (insert p (extremalDigraph n)) := by
      intro q hq
      rcases mem_insert.mp hq with rfl | hq
      · exact hp
      · exact extremalDigraph_isLoopless n q hq
    have hle := card_le_of_not_containsKStrong_two n hn _ hloop hfree
    rw [card_insert_of_notMem hpA, card_extremalDigraph n hn] at hle
    omega
  · rintro m ⟨A, ⟨hloop, hfree, -⟩, rfl⟩
    exact card_le_of_not_containsKStrong_two n hn A hloop hfree

end Candidates.StronglyConnectedDigraphExtremalTwo
