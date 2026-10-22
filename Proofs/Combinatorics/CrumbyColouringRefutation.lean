/-
# Crumby colourings: refutation of Conjecture 16 of Barát–Blázsik–Damásdi

József Pintér, *Subcubic K4-minor-free graphs without crumby colorings*,
arXiv:2605.04706, Section 2, Lemma 1 and Theorem 2, refutes Conjecture 16
of Barát, Blázsik and Damásdi, *Crumby colorings — red-blue vertex
partition of subcubic graphs regarding a conjecture of Thomassen*.

The counterexample `G18` is connected, subcubic, K4-minor-free, and has
no crumby colouring. It consists of two rooted copies of the 9-vertex
graph `F`, with edges `{xa, xb, ac, bd, cd, ce, df, eg, eh, fg, fh}`,
joined by `x₁x₂`. A crumby colouring has blue maximum degree at most 1,
red minimum degree at least 1, and no red simple path on four vertices;
the path need not be induced.

## Formalization choices

* Vertices of `G18` are `Fin 18`; the first copy of `F` uses
  `x,a,b,c,d,e,f,g,h = 0,…,8`, the second copy the same labels shifted by `9`,
  and the bridge edge is `0 — 9`.
* A red-blue colouring is `c : V → Bool` with `true` meaning red.
* Mathlib has no graph minors. `HasK4Minor` is the standard branch-set
  definition: four pairwise disjoint vertex sets, each inducing a connected
  (hence nonempty) subgraph, with an edge between every two of them.
* K4-minor-freeness of `G18` is proved through a general bridge proved here:
  a graph with a width-2 perfect elimination ordering (every vertex has at
  most two later neighbours, and these are adjacent) has no K4 minor
  (`not_hasK4Minor_of_elimOrder`). The paper's ordering
  `g,h,e,f,c,d,a,b` in each copy, then `x₁, x₂`, is applied to the fill-in
  supergraph `T18 ≥ G18`.
* Paper Lemma 1 is used in the specialised form `gadget_copy1`: inside `G18`,
  in every crumby colouring the root `x₁` is red and one of `a₁, b₁` is red.
  The finite core is a `decide` over the `2⁹` colourings of `F`
  (`local_gadget`); the constraints fed to it are instances of the crumby
  axioms at specific vertices.
-/
import Mathlib

set_option autoImplicit false

namespace CrumbyColouringRefutation

/-! ## Crumby colourings -/

/-- A red-blue vertex colouring `c` of `G` (`c v = true` means `v` is red) is
*crumby*: the blue vertices induce maximum degree at most `1`, the red
vertices induce minimum degree at least `1`, and the red vertices contain no
(not necessarily induced) path on four vertices. -/
structure IsCrumby {V : Type*} (G : SimpleGraph V) (c : V → Bool) : Prop where
  /-- A blue vertex has at most one blue neighbour. -/
  blue_le_one : ∀ v u w, c v = false → c u = false → c w = false →
    G.Adj v u → G.Adj v w → u = w
  /-- Every red vertex has a red neighbour. -/
  red_pos : ∀ v, c v = true → ∃ u, G.Adj v u ∧ c u = true
  /-- There is no red path `p — q — r — s` on four distinct vertices. -/
  no_red_P4 : ∀ p q r s, G.Adj p q → G.Adj q r → G.Adj r s → p ≠ r → q ≠ s → p ≠ s →
    ¬ (c p = true ∧ c q = true ∧ c r = true ∧ c s = true)

/-- A single red edge is crumby. -/
example : IsCrumby (⊤ : SimpleGraph (Fin 2)) (fun _ => true) :=
  ⟨by decide, by decide, by decide⟩

/-- Adjacency of the path graph `P4` is decidable (used by the examples). -/
instance : DecidableRel (SimpleGraph.pathGraph 4).Adj := fun _ _ =>
  decidable_of_iff _ SimpleGraph.pathGraph_adj.symm

/-- The path `0 — 1 — 2 — 3` coloured red, red, blue, blue is crumby. -/
example : IsCrumby (SimpleGraph.pathGraph 4) ![true, true, false, false] :=
  ⟨by decide, by decide, by decide⟩

/-- An isolated red vertex violates the red minimum-degree condition. -/
example : ¬ IsCrumby (⊥ : SimpleGraph (Fin 1)) (fun _ => true) := fun h => by
  obtain ⟨u, hu, -⟩ := h.red_pos 0 rfl
  exact hu

/-- An all-red `P4` is not crumby. -/
example : ¬ IsCrumby (SimpleGraph.pathGraph 4) (fun _ => true) := fun h =>
  h.no_red_P4 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ⟨rfl, rfl, rfl, rfl⟩

/-! ## K4 minors -/

/-- `G` has a `K4` minor: there are four pairwise disjoint branch sets, each
inducing a connected subgraph of `G`, with an edge of `G` between any two of
them. -/
def HasK4Minor {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ B : Fin 4 → Set V, (∀ i, (G.induce (B i)).Connected) ∧
    Pairwise (fun i j => Disjoint (B i) (B j)) ∧
    Pairwise (fun i j => ∃ u ∈ B i, ∃ w ∈ B j, G.Adj u w)

/-- `K4` has a `K4` minor (singleton branch sets). -/
example : HasK4Minor (⊤ : SimpleGraph (Fin 4)) := by
  refine ⟨fun i => {i}, fun i => ?_, fun i j hij => ?_, fun i j hij => ⟨i, rfl, j, rfl, hij⟩⟩
  · haveI : Nonempty ({i} : Set (Fin 4)) := ⟨⟨i, rfl⟩⟩
    exact ⟨fun a b => Subsingleton.elim a b ▸ SimpleGraph.Reachable.refl a⟩
  · exact Set.disjoint_singleton.2 hij

section K4

variable {V : Type*}

/-- Having a `K4` minor is monotone under adding edges. -/
theorem HasK4Minor.mono {G G' : SimpleGraph V} (hle : G ≤ G') (h : HasK4Minor G) :
    HasK4Minor G' := by
  obtain ⟨B, hconn, hdisj, hadj⟩ := h
  refine ⟨B, fun i => (hconn i).mono fun a b hab => hle hab, hdisj, fun i j hij => ?_⟩
  obtain ⟨u, hu, w, hw, huw⟩ := hadj hij
  exact ⟨u, hu, w, hw, hle huw⟩

/-- The edgeless graph has no `K4` minor. -/
theorem not_hasK4Minor_bot : ¬ HasK4Minor (⊥ : SimpleGraph V) := by
  rintro ⟨B, -, -, hadj⟩
  obtain ⟨u, -, w, -, huw⟩ := hadj (show (0 : Fin 4) ≠ 1 by decide)
  exact huw

/-- In a connected induced subgraph with a second vertex, `v` has a neighbour inside. -/
theorem exists_adj_of_induce_connected {G : SimpleGraph V} {S : Set V}
    (hS : (G.induce S).Connected) {v u : V} (hv : v ∈ S) (hu : u ∈ S) (hne : u ≠ v) :
    ∃ n ∈ S, G.Adj v n := by
  have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).1 (hS.preconnected ⟨v, hv⟩ ⟨u, hu⟩)
  rcases hr.cases_head with heq | ⟨c, hc, -⟩
  · exact absurd (congrArg Subtype.val heq).symm hne
  · exact ⟨c.1, c.2, hc⟩

/-- Three further indices of `Fin 4`, all distinct from `i` and from each other. -/
theorem fin4_others : ∀ i : Fin 4, i ≠ i + 1 ∧ i ≠ i + 2 ∧ i ≠ i + 3 ∧
    i + 1 ≠ i + 2 ∧ i + 1 ≠ i + 3 ∧ i + 2 ≠ i + 3 := by decide

/-- **Elimination step.** Let `v` have at most two `G`-neighbours, and let `G'`
contain every edge of `G` avoiding `v` together with the fill edge between
the (at most two) neighbours of `v`. If `G` has a `K4` minor then so does `G'`;
the new branch sets are the old ones with `v` removed. -/
theorem hasK4Minor_of_elim {G G' : SimpleGraph V} (v : V)
    (h1 : ∀ x y, x ≠ v → y ≠ v → G.Adj x y → G'.Adj x y)
    (h2 : ∀ x y, G.Adj v x → G.Adj v y → x ≠ y → G'.Adj x y)
    (h3 : ∀ x y z, G.Adj v x → G.Adj v y → G.Adj v z → x = y ∨ x = z ∨ y = z)
    (h : HasK4Minor G) : HasK4Minor G' := by
  classical
  obtain ⟨B, hconn, hdisj, hadj⟩ := h
  -- Step A: a vertex `v` lying in a branch set has a neighbour in that branch set.
  have hnb : ∀ i, v ∈ B i → ∃ n ∈ B i, G.Adj v n := by
    intro i hvi
    by_contra hno
    simp only [not_exists, not_and] at hno
    have hsingle : ∀ u ∈ B i, u = v := by
      intro u hu
      by_contra hne
      obtain ⟨n, hn, hvn⟩ := exists_adj_of_induce_connected (hconn i) hvi hu hne
      exact hno n hn hvn
    have hnbj : ∀ j, j ≠ i → ∃ w ∈ B j, G.Adj v w := by
      intro j hji
      obtain ⟨u, hu, w, hw, huw⟩ := hadj hji.symm
      rw [hsingle u hu] at huw
      exact ⟨w, hw, huw⟩
    obtain ⟨o1, o2, o3, o12, o13, o23⟩ := fin4_others i
    obtain ⟨w1, hw1, hvw1⟩ := hnbj (i + 1) o1.symm
    obtain ⟨w2, hw2, hvw2⟩ := hnbj (i + 2) o2.symm
    obtain ⟨w3, hw3, hvw3⟩ := hnbj (i + 3) o3.symm
    rcases h3 w1 w2 w3 hvw1 hvw2 hvw3 with e | e | e
    · exact Set.disjoint_left.1 (hdisj o12) hw1 (e ▸ hw2)
    · exact Set.disjoint_left.1 (hdisj o13) hw1 (e ▸ hw3)
    · exact Set.disjoint_left.1 (hdisj o23) hw2 (e ▸ hw3)
  -- Step B: a default vertex in each shrunken branch set.
  have hdef : ∀ i, ∃ d ∈ B i, d ≠ v ∧ (v ∈ B i → G.Adj v d) := by
    intro i
    by_cases hvi : v ∈ B i
    · obtain ⟨n, hn, hvn⟩ := hnb i hvi
      exact ⟨n, hn, hvn.ne.symm, fun _ => hvn⟩
    · obtain ⟨⟨d, hd⟩⟩ := (hconn i).nonempty
      exact ⟨d, hd, fun hdv => hvi (hdv ▸ hd), fun hv => absurd hv hvi⟩
  choose d hdB hdv hdadj using hdef
  refine ⟨fun i => B i \ {v}, fun i => ?_, fun i j hij => ?_, fun i j hij => ?_⟩
  · -- connectivity of `B i \ {v}` in `G'`
    let S' : Set V := B i \ {v}
    have hdS : d i ∈ S' := ⟨hdB i, hdv i⟩
    let f : B i → S' := fun z =>
      if hz : z.1 = v then ⟨d i, hdS⟩ else ⟨z.1, z.2, fun h' => hz h'⟩
    have hedge : ∀ a b : B i, (G.induce (B i)).Adj a b →
        Relation.ReflTransGen (G'.induce S').Adj (f a) (f b) := by
      intro a b hab
      have hab' : G.Adj a.1 b.1 := hab
      by_cases ha : a.1 = v
      · have hb : b.1 ≠ v := fun hb => hab'.ne (ha.trans hb.symm)
        have hva : v ∈ B i := ha ▸ a.2
        have hfa : f a = ⟨d i, hdS⟩ := dif_pos ha
        have hfb : f b = ⟨b.1, b.2, fun h' => hb h'⟩ := dif_neg hb
        rw [hfa, hfb]
        by_cases hdb : d i = b.1
        · have : (⟨d i, hdS⟩ : S') = ⟨b.1, b.2, fun h' => hb h'⟩ := Subtype.ext hdb
          rw [this]
        · exact Relation.ReflTransGen.single
            (h2 (d i) b.1 (hdadj i hva) (ha ▸ hab') hdb)
      · by_cases hb : b.1 = v
        · have hvb : v ∈ B i := hb ▸ b.2
          have hfa : f a = ⟨a.1, a.2, fun h' => ha h'⟩ := dif_neg ha
          have hfb : f b = ⟨d i, hdS⟩ := dif_pos hb
          rw [hfa, hfb]
          by_cases had : a.1 = d i
          · have : (⟨a.1, a.2, fun h' => ha h'⟩ : S') = ⟨d i, hdS⟩ := Subtype.ext had
            rw [this]
          · exact Relation.ReflTransGen.single
              (h2 a.1 (d i) (hb ▸ hab'.symm) (hdadj i hvb) had)
        · have hfa : f a = ⟨a.1, a.2, fun h' => ha h'⟩ := dif_neg ha
          have hfb : f b = ⟨b.1, b.2, fun h' => hb h'⟩ := dif_neg hb
          rw [hfa, hfb]
          exact Relation.ReflTransGen.single (h1 a.1 b.1 ha hb hab')
    haveI : Nonempty S' := ⟨⟨d i, hdS⟩⟩
    refine ⟨fun x y => ?_⟩
    have hxy := (SimpleGraph.reachable_iff_reflTransGen _ _).1
      ((hconn i).preconnected ⟨x.1, x.2.1⟩ ⟨y.1, y.2.1⟩)
    have hlift : Relation.ReflTransGen (G'.induce S').Adj (f ⟨x.1, x.2.1⟩) (f ⟨y.1, y.2.1⟩) :=
      Relation.ReflTransGen.lift' f hedge _ _ hxy
    have hfx : f ⟨x.1, x.2.1⟩ = x := dif_neg fun h' => x.2.2 h'
    have hfy : f ⟨y.1, y.2.1⟩ = y := dif_neg fun h' => y.2.2 h'
    rw [hfx, hfy] at hlift
    exact (SimpleGraph.reachable_iff_reflTransGen _ _).2 hlift
  · exact (hdisj hij).mono Set.sdiff_subset Set.sdiff_subset
  · obtain ⟨u, hu, w, hw, huw⟩ := hadj hij
    by_cases huv : u = v
    · have hwv : w ≠ v := fun hwv => Set.disjoint_left.1 (hdisj hij) (huv ▸ hu) (hwv ▸ hw)
      have hvi : v ∈ B i := huv ▸ hu
      have hdw : d i ≠ w := fun e => Set.disjoint_left.1 (hdisj hij) (hdB i) (e ▸ hw)
      exact ⟨d i, ⟨hdB i, hdv i⟩, w, ⟨hw, hwv⟩, h2 (d i) w (hdadj i hvi) (huv ▸ huw) hdw⟩
    · by_cases hwv : w = v
      · have hvj : v ∈ B j := hwv ▸ hw
        have hud : u ≠ d j := fun e => Set.disjoint_left.1 (hdisj hij) hu (e ▸ hdB j)
        exact ⟨u, ⟨hu, huv⟩, d j, ⟨hdB j, hdv j⟩, h2 u (d j) (hwv ▸ huw.symm) (hdadj j hvj) hud⟩
      · exact ⟨u, ⟨hu, huv⟩, w, ⟨hw, hwv⟩, h1 u w huv hwv huw⟩

/-- The subgraph of `G` on the vertices of rank at least `k`. -/
def rankRestrict (G : SimpleGraph V) (r : V → ℕ) (k : ℕ) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ k ≤ r x ∧ k ≤ r y
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

/-- **Width-2 elimination orderings exclude `K4` minors.** If an injective
rank `r` (bounded by `N`) orders the vertices of `G` so that every vertex has
at most two later neighbours, and any two distinct later neighbours of a vertex
are adjacent (a perfect elimination ordering of width at most `2`), then `G`
has no `K4` minor. -/
theorem not_hasK4Minor_of_elimOrder (G : SimpleGraph V) (r : V → ℕ)
    (hr : Function.Injective r) (N : ℕ) (hN : ∀ v, r v < N)
    (hdeg : ∀ v x y z, G.Adj v x → G.Adj v y → G.Adj v z → r v < r x → r v < r y →
      r v < r z → x = y ∨ x = z ∨ y = z)
    (hfill : ∀ v x y, G.Adj v x → G.Adj v y → r v < r x → r v < r y → x ≠ y → G.Adj x y) :
    ¬ HasK4Minor G := by
  intro hG
  have hlater : ∀ v x, (rankRestrict G r (r v)).Adj v x → r v < r x := fun v x hvx =>
    lt_of_le_of_ne hvx.2.2 fun e => hvx.1.ne (hr e)
  have step : ∀ k, HasK4Minor (rankRestrict G r k) → HasK4Minor (rankRestrict G r (k + 1)) := by
    intro k hk
    by_cases hv : ∃ v, r v = k
    · obtain ⟨v, rfl⟩ := hv
      refine hasK4Minor_of_elim v (fun x y hx hy hxy => ?_) (fun x y hvx hvy hxy => ?_)
        (fun x y z hvx hvy hvz => ?_) hk
      · exact ⟨hxy.1, lt_of_le_of_ne hxy.2.1 fun e => hx (hr e).symm,
          lt_of_le_of_ne hxy.2.2 fun e => hy (hr e).symm⟩
      · have hx := hlater v x hvx
        have hy := hlater v y hvy
        exact ⟨hfill v x y hvx.1 hvy.1 hx hy hxy, hx, hy⟩
      · exact hdeg v x y z hvx.1 hvy.1 hvz.1 (hlater v x hvx) (hlater v y hvy) (hlater v z hvz)
    · refine hk.mono fun x y (hxy : (rankRestrict G r k).Adj x y) => ⟨hxy.1, ?_, ?_⟩
      · exact lt_of_le_of_ne hxy.2.1 fun e => hv ⟨x, e.symm⟩
      · exact lt_of_le_of_ne hxy.2.2 fun e => hv ⟨y, e.symm⟩
  have hall : ∀ n, HasK4Minor (rankRestrict G r n) := by
    intro n
    induction n with
    | zero => exact hG.mono fun x y hxy => ⟨hxy, Nat.zero_le _, Nat.zero_le _⟩
    | succ n ih => exact step n ih
  exact not_hasK4Minor_bot ((hall N).mono fun x _ (hxy : (rankRestrict G r N).Adj x _) =>
    absurd hxy.2.1 (not_le.2 (hN x)))

/-- The triangle `K3` has no `K4` minor. -/
example : ¬ HasK4Minor (⊤ : SimpleGraph (Fin 3)) :=
  not_hasK4Minor_of_elimOrder _ Fin.val Fin.val_injective 3 (fun v => v.isLt)
    (by decide) (by decide)

end K4

/-! ## Crumby-colouring helper lemmas -/

section helpers

variable {V : Type*} {G : SimpleGraph V} {c : V → Bool}

/-- A blue vertex `v` and two distinct neighbours are not all blue. -/
theorem IsCrumby.blue_or (h : IsCrumby G c) {v u w : V} (hvu : G.Adj v u) (hvw : G.Adj v w)
    (huw : u ≠ w) : (c v || c u || c w) = true := by
  by_contra hc
  simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hc
  exact huw (h.blue_le_one v u w hc.1.1 hc.1.2 hc.2 hvu hvw)

/-- A red vertex whose neighbours lie in `{n₁, n₂}` has a red one among them. -/
theorem IsCrumby.red_or2 (h : IsCrumby G c) {v n₁ n₂ : V}
    (hN : ∀ u, G.Adj v u → u = n₁ ∨ u = n₂) : (!c v || c n₁ || c n₂) = true := by
  cases hv : c v
  · rfl
  · obtain ⟨u, hu, hcu⟩ := h.red_pos v hv
    rcases hN u hu with rfl | rfl <;> simp [hcu]

/-- A red vertex whose neighbours lie in `{n₁, n₂, n₃}` has a red one among them. -/
theorem IsCrumby.red_or3 (h : IsCrumby G c) {v n₁ n₂ n₃ : V}
    (hN : ∀ u, G.Adj v u → u = n₁ ∨ u = n₂ ∨ u = n₃) :
    (!c v || c n₁ || c n₂ || c n₃) = true := by
  cases hv : c v
  · rfl
  · obtain ⟨u, hu, hcu⟩ := h.red_pos v hv
    rcases hN u hu with rfl | rfl | rfl <;> simp [hcu]

/-- Boolean form of the no-red-`P4` condition. -/
theorem IsCrumby.not_P4 (h : IsCrumby G c) {p q r s : V} (hpq : G.Adj p q) (hqr : G.Adj q r)
    (hrs : G.Adj r s) (hpr : p ≠ r) (hqs : q ≠ s) (hps : p ≠ s) :
    (!(c p && c q && c r && c s)) = true := by
  have hn := h.no_red_P4 p q r s hpq hqr hrs hpr hqs hps
  cases hp : c p <;> cases hq : c q <;> cases hr : c r <;> cases hs : c s <;> simp_all

/-- Crumby colourings pull back along an involutive automorphism `σ`. -/
theorem IsCrumby.comp_iso (h : IsCrumby G c) (σ : V → V) (hσ : ∀ v, σ (σ v) = v)
    (hadj : ∀ v w, G.Adj (σ v) (σ w) ↔ G.Adj v w) : IsCrumby G (c ∘ σ) where
  blue_le_one v u w hv hu hw hvu hvw := by
    have := h.blue_le_one (σ v) (σ u) (σ w) hv hu hw ((hadj v u).2 hvu) ((hadj v w).2 hvw)
    rw [← hσ u, this, hσ w]
  red_pos v hv := by
    obtain ⟨u, hu, hcu⟩ := h.red_pos (σ v) hv
    refine ⟨σ u, (hadj v (σ u)).1 ?_, ?_⟩
    · rwa [hσ u]
    · simp only [Function.comp_apply, hσ u, hcu]
  no_red_P4 p q r s hpq hqr hrs hpr hqs hps := by
    have hinj : Function.Injective σ := fun a b hab => by rw [← hσ a, hab, hσ b]
    exact h.no_red_P4 (σ p) (σ q) (σ r) (σ s) ((hadj p q).2 hpq) ((hadj q r).2 hqr)
      ((hadj r s).2 hrs) (hinj.ne hpr) (hinj.ne hqs) (hinj.ne hps)

end helpers

/-! ## The graph `G18` -/

/-- Edge list of the rooted gadget `F` with `x,a,b,c,d,e,f,g,h = 0,…,8`:
`xa, xb, ac, bd, cd, ce, df, eg, eh, fg, fh`. -/
def fEdges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (1, 3), (2, 4), (3, 4), (3, 5), (4, 6), (5, 7), (5, 8), (6, 7), (6, 8)]

/-- Edge list of `G18`: two copies of `F` (offsets `0` and `9`) and the edge `x₁x₂ = 0 — 9`. -/
def g18Edges : List (ℕ × ℕ) :=
  fEdges ++ fEdges.map (fun e => (e.1 + 9, e.2 + 9)) ++ [(0, 9)]

/-- The paper's graph `G18` on `Fin 18`. -/
def G18 : SimpleGraph (Fin 18) where
  Adj i j := (i.val, j.val) ∈ g18Edges ∨ (j.val, i.val) ∈ g18Edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

/-- Adjacency in `G18` is decidable (list membership). -/
instance : DecidableRel G18.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

/-- `G18` has the `23` edges listed in the paper. -/
example : G18.edgeFinset.card = 23 := by decide

/-- The bridge edge `x₁x₂` is present; `x₁c₁` is not. -/
example : G18.Adj 0 9 ∧ ¬ G18.Adj 0 3 := by decide

/-- Degrees as in the paper (`x₁` and `c₁` have degree 3, `a₁`
and `g₁` have degree 2). -/
example : G18.degree 0 = 3 ∧ G18.degree 3 = 3 ∧ G18.degree 1 = 2 ∧ G18.degree 7 = 2 := by
  decide

/-! ## No crumby colouring -/

/-- The finite core of paper Lemma 1 on the gadget `F`: Boolean constraints
(instances of the crumby axioms at the vertices `a, …, h`). -/
def gadgetOK (x a b c d e f g h : Bool) : Bool :=
    (a || x || c) && (b || x || d) && (c || a || e) &&
    (d || b || c) && (d || b || f) && (e || g || h) && (f || g || h) &&
    (!a || x || c) && (!b || x || d) && (!c || a || d || e) &&
    (!d || b || c || f) && (!e || c || g || h) && (!f || d || g || h) &&
    (!g || e || f) && (!h || e || f) &&
    !(c && d && f && h) && !(c && d && f && g) &&
    !(c && e && h && f) && !(c && e && g && f) &&
    !(d && c && e && h) && !(d && c && e && g) &&
    !(d && f && h && e) && !(d && f && g && e) &&
    !(e && c && d && f)

/-- Exhaustive check over the `2⁹` colourings of `F`: the constraints force the
root `x` red and one of `a, b` red. -/
theorem local_gadget : ∀ x a b c d e f g h : Bool, gadgetOK x a b c d e f g h = true →
    x = true ∧ (a || b) = true := by
  decide

/-- Paper Lemma 1, specialised to the first copy of `F` in `G18`: in a crumby
colouring of `G18`, `x₁ = 0` is red and one of `a₁ = 1`, `b₁ = 2` is red. -/
theorem gadget_copy1 {c : Fin 18 → Bool} (h : IsCrumby G18 c) :
    c 0 = true ∧ (c 1 || c 2) = true := by
  have b1 := h.blue_or (v := 1) (u := 0) (w := 3) (by decide) (by decide) (by decide)
  have b2 := h.blue_or (v := 2) (u := 0) (w := 4) (by decide) (by decide) (by decide)
  have b3 := h.blue_or (v := 3) (u := 1) (w := 5) (by decide) (by decide) (by decide)
  have b4 := h.blue_or (v := 4) (u := 2) (w := 3) (by decide) (by decide) (by decide)
  have b5 := h.blue_or (v := 4) (u := 2) (w := 6) (by decide) (by decide) (by decide)
  have b6 := h.blue_or (v := 5) (u := 7) (w := 8) (by decide) (by decide) (by decide)
  have b7 := h.blue_or (v := 6) (u := 7) (w := 8) (by decide) (by decide) (by decide)
  have r1 := h.red_or2 (v := 1) (n₁ := 0) (n₂ := 3) (by decide)
  have r2 := h.red_or2 (v := 2) (n₁ := 0) (n₂ := 4) (by decide)
  have r3 := h.red_or3 (v := 3) (n₁ := 1) (n₂ := 4) (n₃ := 5) (by decide)
  have r4 := h.red_or3 (v := 4) (n₁ := 2) (n₂ := 3) (n₃ := 6) (by decide)
  have r5 := h.red_or3 (v := 5) (n₁ := 3) (n₂ := 7) (n₃ := 8) (by decide)
  have r6 := h.red_or3 (v := 6) (n₁ := 4) (n₂ := 7) (n₃ := 8) (by decide)
  have r7 := h.red_or2 (v := 7) (n₁ := 5) (n₂ := 6) (by decide)
  have r8 := h.red_or2 (v := 8) (n₁ := 5) (n₂ := 6) (by decide)
  have p1 := h.not_P4 (p := 3) (q := 4) (r := 6) (s := 8) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have p2 := h.not_P4 (p := 3) (q := 4) (r := 6) (s := 7) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have p3 := h.not_P4 (p := 3) (q := 5) (r := 8) (s := 6) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have p4 := h.not_P4 (p := 3) (q := 5) (r := 7) (s := 6) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have p5 := h.not_P4 (p := 4) (q := 3) (r := 5) (s := 8) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have p6 := h.not_P4 (p := 4) (q := 3) (r := 5) (s := 7) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have p7 := h.not_P4 (p := 4) (q := 6) (r := 8) (s := 5) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have p8 := h.not_P4 (p := 4) (q := 6) (r := 7) (s := 5) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have p9 := h.not_P4 (p := 5) (q := 3) (r := 4) (s := 6) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  refine local_gadget (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6) (c 7) (c 8) ?_
  simp only [gadgetOK, b1, b2, b3, b4, b5, b6, b7, r1, r2, r3, r4, r5, r6, r7, r8,
    p1, p2, p3, p4, p5, p6, p7, p8, p9, Bool.and_self]

/-- The automorphism of `G18` exchanging the two copies of `F`. -/
def swapCopies (i : Fin 18) : Fin 18 := ⟨(i.val + 9) % 18, Nat.mod_lt _ (by norm_num)⟩

/-- `swapCopies` is an involution. -/
theorem swapCopies_swapCopies : ∀ i, swapCopies (swapCopies i) = i := by decide

/-- `swapCopies` preserves adjacency of `G18`. -/
theorem G18_adj_swapCopies : ∀ i j, G18.Adj (swapCopies i) (swapCopies j) ↔ G18.Adj i j := by
  decide

/-- **Paper Theorem 2 (colouring part).** `G18` has no crumby colouring. -/
theorem G18_not_isCrumby (c : Fin 18 → Bool) : ¬ IsCrumby G18 c := by
  intro h
  obtain ⟨hx₁, hp₁⟩ := gadget_copy1 h
  obtain ⟨hx₂, hp₂⟩ := gadget_copy1 (h.comp_iso swapCopies swapCopies_swapCopies
    G18_adj_swapCopies)
  have hx₂' : c 9 = true := hx₂
  have hp₂' : (c 10 || c 11) = true := hp₂
  rw [Bool.or_eq_true] at hp₁ hp₂'
  rcases hp₁ with hp₁ | hp₁ <;> rcases hp₂' with hp₂ | hp₂
  · exact h.no_red_P4 1 0 9 10 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) ⟨hp₁, hx₁, hx₂', hp₂⟩
  · exact h.no_red_P4 1 0 9 11 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) ⟨hp₁, hx₁, hx₂', hp₂⟩
  · exact h.no_red_P4 2 0 9 10 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) ⟨hp₁, hx₁, hx₂', hp₂⟩
  · exact h.no_red_P4 2 0 9 11 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) ⟨hp₁, hx₁, hx₂', hp₂⟩

/-! ## Connectivity and degrees -/

/-- A graph on `Fin (n + 1)` in which every nonzero vertex has a neighbour of
smaller index is connected. -/
theorem connected_of_parent {n : ℕ} (G : SimpleGraph (Fin (n + 1)))
    (par : Fin (n + 1) → Fin (n + 1))
    (h : ∀ v : Fin (n + 1), v ≠ 0 → G.Adj v (par v) ∧ par v < v) : G.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, fun w => ?_⟩
  induction w using WellFoundedLT.induction with
  | _ w ih =>
    by_cases hw : w = 0
    · rw [hw]
    · obtain ⟨hadj, hlt⟩ := h w hw
      exact (ih (par w) hlt).trans hadj.symm.reachable

/-- A parent function witnessing connectivity of `G18`. -/
def g18Parent : Fin 18 → Fin 18 := ![0, 0, 0, 1, 2, 3, 4, 5, 5, 0, 9, 9, 10, 11, 12, 13, 14, 14]

/-- **Paper Theorem 2 (connectivity).** `G18` is connected. -/
theorem G18_connected : G18.Connected :=
  connected_of_parent G18 g18Parent (by decide)

/-- **Paper Theorem 2 (subcubic).** `G18` has maximum degree at most `3`. -/
theorem G18_maxDegree_le : G18.maxDegree ≤ 3 :=
  SimpleGraph.maxDegree_le_of_forall_degree_le (G := G18) 3 (by decide)

/-! ## K4-minor-freeness -/

/-- The fill edges `ef, cf, ad, ab` of the paper's elimination of one copy of `F`. -/
def fillEdges : List (ℕ × ℕ) := [(5, 6), (3, 6), (1, 4), (1, 2)]

/-- The fill-in supergraph `T18 ≥ G18` of the paper's elimination ordering. -/
def T18 : SimpleGraph (Fin 18) where
  Adj i j := (i.val, j.val) ∈ g18Edges ++ (fillEdges ++ fillEdges.map (fun e => (e.1 + 9, e.2 + 9)))
    ∨ (j.val, i.val) ∈ g18Edges ++ (fillEdges ++ fillEdges.map (fun e => (e.1 + 9, e.2 + 9)))
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

/-- Adjacency in `T18` is decidable (list membership). -/
instance : DecidableRel T18.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

/-- `G18` is a subgraph of its fill-in `T18`. -/
theorem G18_le_T18 : G18 ≤ T18 := fun _ _ h =>
  h.imp (List.mem_append_left _) (List.mem_append_left _)

/-- Position in the paper's elimination ordering
`g₁,h₁,e₁,f₁,c₁,d₁,a₁,b₁, g₂,h₂,e₂,f₂,c₂,d₂,a₂,b₂, x₁, x₂`. -/
def g18Rank : Fin 18 → ℕ := ![16, 6, 7, 4, 5, 2, 3, 0, 1, 17, 14, 15, 12, 13, 10, 11, 8, 9]

/-- First remaining neighbour at elimination time (paper's table). -/
def g18ParentP : Fin 18 → Fin 18 := ![9, 0, 0, 1, 1, 3, 3, 5, 5, 9, 9, 9, 10, 10, 12, 12, 14, 14]

/-- Second remaining neighbour at elimination time (paper's table). -/
def g18ParentQ : Fin 18 → Fin 18 := ![9, 2, 0, 4, 2, 6, 4, 6, 6, 9, 11, 9, 13, 11, 15, 13, 15, 15]

/-- Every later `T18`-neighbour of `v` is one of its two recorded parents. -/
theorem T18_later_mem : ∀ v x, T18.Adj v x → g18Rank v < g18Rank x →
    x = g18ParentP v ∨ x = g18ParentQ v := by decide

/-- The two recorded parents, when distinct and adjacent to `v`, are adjacent. -/
theorem T18_fill : ∀ v, T18.Adj v (g18ParentP v) → T18.Adj v (g18ParentQ v) →
    g18ParentP v ≠ g18ParentQ v → T18.Adj (g18ParentP v) (g18ParentQ v) := by decide

/-- The elimination ranks are distinct. -/
theorem g18Rank_injective : Function.Injective g18Rank := by decide

/-- **Paper Theorem 2 (K4-minor-freeness).** `G18` has no `K4` minor. -/
theorem G18_not_hasK4Minor : ¬ HasK4Minor G18 := by
  have hT : ¬ HasK4Minor T18 := by
    refine not_hasK4Minor_of_elimOrder T18 g18Rank g18Rank_injective 18 (by decide) ?_ ?_
    · intro v x y z hx hy hz rx ry rz
      rcases T18_later_mem v x hx rx with rfl | rfl <;>
        rcases T18_later_mem v y hy ry with rfl | rfl <;>
        rcases T18_later_mem v z hz rz with rfl | rfl <;> simp
    · intro v x y hx hy rx ry hxy
      rcases T18_later_mem v x hx rx with rfl | rfl <;>
        rcases T18_later_mem v y hy ry with rfl | rfl
      · exact absurd rfl hxy
      · exact T18_fill v hx hy hxy
      · exact (T18_fill v hy hx (Ne.symm hxy)).symm
      · exact absurd rfl hxy
  exact fun h => hT (h.mono G18_le_T18)

/-! ## Main results -/

/-- **Paper Theorem 2.** `G18` is connected, subcubic, `K4`-minor-free, and has
no crumby colouring. -/
theorem thm_2 : G18.Connected ∧ G18.maxDegree ≤ 3 ∧ ¬ HasK4Minor G18 ∧
    ∀ c : Fin 18 → Bool, ¬ IsCrumby G18 c :=
  ⟨G18_connected, G18_maxDegree_le, G18_not_hasK4Minor, G18_not_isCrumby⟩

/-- Conjecture 16 of Barát–Blázsik–Damásdi in its subcubic setting, further
restricted to connected graphs: every finite connected graph of maximum degree
at most `3` with no `K4` minor admits a crumby colouring. (Restricting the
hypotheses only weakens the conjecture, so refuting this form refutes the
literal statement too.) -/
def CrumbyConjecture16 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → G.maxDegree ≤ 3 → ¬ HasK4Minor G → ∃ c : V → Bool, IsCrumby G c

/-- **Refutation of Conjecture 16 (Barát–Blázsik–Damásdi)**, via `G18`
(Pintér, arXiv:2605.04706, Theorem 2). -/
theorem not_crumbyConjecture16 : ¬ CrumbyConjecture16 := by
  intro hconj
  obtain ⟨c, hc⟩ := hconj (Fin 18) G18 G18_connected G18_maxDegree_le G18_not_hasK4Minor
  exact G18_not_isCrumby c hc

/-- The literal form of Conjecture 16 is false: some finite graph with no `K4`
minor admits no crumby colouring. -/
theorem exists_not_hasK4Minor_forall_not_isCrumby :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V), ¬ HasK4Minor G ∧
      ∀ c : V → Bool, ¬ IsCrumby G c :=
  ⟨Fin 18, inferInstance, G18, G18_not_hasK4Minor, G18_not_isCrumby⟩

end CrumbyColouringRefutation
