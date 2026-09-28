/-
Erdős–Gyárfás problem 64 — the edge-rooted Moore reduction for cubic bipartite graphs.

PROVENANCE. arXiv:2608.02675, Julius Tranquilli, "A 60-Vertex Lower Bound for
Cubic Bipartite Counterexamples to the Erdős–Gyárfás Conjecture" (2 August 2026),
Section 3.1, the lemma labelled `lem:moore` and titled "Edge-rooted Moore
reduction" (Lemma 8 in the paper's shared numbering).  Graphs are finite,
undirected and simple throughout.

SOURCE CLAIM BOUNDARY.  The source's lemma reads:

  Every simple cubic bipartite graph on at most 58 vertices with no `C₄` and no
  `C₈` contains a `C₆`.

Its proof is the Moore-bound observation reproduced here: assume in addition that
there is no `C₆`, pick an edge `uv`, and in `G − uv` expose the nonbacktracking
cubic tree from `u` to depth four (level sizes `1,2,4,8,16`) and likewise from
`v`; a repeat inside one exposure yields a cycle of length at most `8`, and an
intersection of the two exposures together with `uv` yields a closed walk of
length at most `9` whose length is even by bipartiteness, hence a cycle of length
at most `8`; so all `2(1+2+4+8+16) = 62` exposed vertices are distinct.

WHAT IS FORMALIZED HERE.  Only that observation.  `card_verts_ge_62_of_edge_of_cubic_bipartite`
is its contrapositive in the sharp form actually proved: a finite cubic bipartite
graph with an edge and *no simple cycle of length at most `8`* has at least `62`
vertices.  The hypothesis is stronger than "no `C₄` and no `C₈`" because it also
rules out `C₆` (and every odd cycle, which bipartiteness already forbids); that is
exactly what the source's proof by contradiction assumes.  The corollary
`exists_six_cycle_of_cubic_bipartite` is the source's lemma with an added formal nonemptiness
guard `Nonempty V` (the source works under the standard nonempty-graph convention), obtained by
adding "no `C₆`" to "no `C₄` and no `C₈`".

NOT FORMALIZED HERE.  The source's *main* theorem (`thm:main`) and its corollary
(`cor:bound`) are a certified exhaustive computation: the Moore reduction turns a
hypothetical `C₆` into a Berge triangle of a linear symmetric `v₃`-configuration,
after which a complete restricted-growth search on at most `29` points closes both
rooted search trees, checked by two independently implemented searches and a
static witness certificate.  Nothing about that computation, the incidence
translation of `C₄`/`C₈`/`C₁₆`, the triangle-root orbits, or the search trees is
claimed or used below.  In particular this module does **not** establish the
60-vertex lower bound; it establishes the human-verifiable Moore step that the
computation takes as its input.

METHOD.  Everything is kernel-checked; no computational shortcut is used for any mathematical
content.  The two exposures are modelled as the balls
of radius `4` about `u` and about `v` in `H := G.deleteEdges {s(u,v)}`, and the
level structure is proved through `H.dist`.  All cycle extractions go through
`SimpleGraph.Walk.IsPath.exists_isCycle_length_le_add_of_ne` (two distinct paths
with the same endpoints bound a cycle) or through the parity of closed walks in a
bipartite graph (`SimpleGraph.two_colorable_iff_forall_loop_even`).  `dist` is a
junk-valued function (`0` on unreachable pairs), so every level carries its
`Reachable` proof.
-/

import Erdos.Erdos64.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Tactic

set_option autoImplicit false

namespace Erdos64

open SimpleGraph

universe u

variable {V : Type u}

section Moore

variable [Fintype V] [DecidableEq V]

/-! ### Levels and balls of `H.dist` -/

/-- The vertices at distance exactly `k` from `u` in `H`.  The `Reachable` conjunct is part of the
definition because `H.dist` takes the junk value `0` on unreachable pairs; without it a level `0`
would also contain every vertex of another component. -/
private noncomputable def level (H : SimpleGraph V) (u : V) (k : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun w => H.Reachable u w ∧ H.dist u w = k)

private lemma mem_level {H : SimpleGraph V} {u w : V} {k : ℕ} :
    w ∈ level H u k ↔ H.Reachable u w ∧ H.dist u w = k := by
  simp [level]

private lemma level_disjoint {H : SimpleGraph V} {u : V} {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (level H u j) (level H u k) := by
  rw [Finset.disjoint_left]
  intro w hwj hwk
  rw [mem_level] at hwj hwk
  exact hjk (hwj.2.symm.trans hwk.2)

private lemma level_zero {H : SimpleGraph V} {u : V} : level H u 0 = {u} := by
  ext w
  rw [mem_level, Finset.mem_singleton]
  constructor
  · rintro ⟨hr, hd⟩
    exact (hr.dist_eq_zero_iff.mp hd).symm
  · rintro rfl
    exact ⟨Reachable.refl _, dist_self⟩

/-- The vertices reachable from `u` in `H` within distance `r`. -/
private noncomputable def ball (H : SimpleGraph V) (u : V) (r : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun w => H.Reachable u w ∧ H.dist u w ≤ r)

private lemma mem_ball {H : SimpleGraph V} {u w : V} {r : ℕ} :
    w ∈ ball H u r ↔ H.Reachable u w ∧ H.dist u w ≤ r := by
  simp [ball]

private lemma ball_eq_biUnion_level (H : SimpleGraph V) (u : V) (r : ℕ) :
    ball H u r = (Finset.range (r + 1)).biUnion (fun k => level H u k) := by
  ext w
  rw [mem_ball, Finset.mem_biUnion]
  constructor
  · rintro ⟨hr, hd⟩
    exact ⟨H.dist u w, Finset.mem_range.mpr (by omega), mem_level.mpr ⟨hr, rfl⟩⟩
  · rintro ⟨k, hk, hwk⟩
    rw [mem_level] at hwk
    exact ⟨hwk.1, by rw [hwk.2]; exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)⟩

/-- A depth-four exposure with level sizes `1,2,4,8,16` has exactly `31` vertices. -/
private lemma card_ball_four (H : SimpleGraph V) (u : V)
    (h1 : (level H u 1).card = 2) (h2 : (level H u 2).card = 4)
    (h3 : (level H u 3).card = 8) (h4 : (level H u 4).card = 16) :
    (ball H u 4).card = 31 := by
  rw [ball_eq_biUnion_level,
    Finset.card_biUnion (fun a _ b _ hab => level_disjoint hab)]
  have hpt : ∀ k ∈ Finset.range 5, (level H u k).card = 2 ^ k := by
    intro k hk
    rw [Finset.mem_range] at hk
    rcases k with _ | _ | _ | _ | k
    · rw [level_zero, Finset.card_singleton]; norm_num
    · simpa using h1
    · simpa using h2
    · simpa using h3
    · rcases k with _ | k
      · simpa using h4
      · have : False := by omega
        contradiction
  rw [Finset.sum_congr rfl hpt]
  norm_num

/-! ### Parity of closed walks, and cycles of even length at most `9` -/

private lemma even_length_of_colorable {G : SimpleGraph V} (hbip : G.Colorable 2) {x : V}
    (c : G.Walk x x) : Even c.length :=
  (two_colorable_iff_forall_loop_even.mp hbip) x c

private lemma false_of_isCycle_le_nine {G : SimpleGraph V} (hbip : G.Colorable 2)
    (hshort : ∀ {x : V} (c : G.Walk x x), c.IsCycle → c.length ≤ 8 → False)
    {x : V} {c : G.Walk x x} (hc : c.IsCycle) (hlen : c.length ≤ 9) : False := by
  obtain ⟨m, hm⟩ := even_length_of_colorable hbip c
  exact hshort c hc (by omega)

/-! ### The level recurrence -/

/-- Two distinct neighbours of `w` at distance `n - 1` from `u` would give two distinct shortest
`u`–`w` paths, hence a cycle of length at most `2n ≤ 8`. -/
private lemma eq_of_two_parents {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    {u w z₁ z₂ : V} {n : ℕ} (hle : H ≤ G) (hbip : G.Colorable 2)
    (hshort : ∀ {x : V} (c : G.Walk x x), c.IsCycle → c.length ≤ 8 → False)
    (hn : n ≤ 4) (hn1 : 1 ≤ n)
    (hw : H.Reachable u w) (hwd : H.dist u w = n)
    (hz₁ : H.Reachable u z₁) (hd₁ : H.dist u z₁ = n - 1) (ha₁ : H.Adj z₁ w)
    (hz₂ : H.Reachable u z₂) (hd₂ : H.dist u z₂ = n - 1) (ha₂ : H.Adj z₂ w) :
    z₁ = z₂ := by
  obtain ⟨p₁, hp₁⟩ := hz₁.exists_walk_length_eq_dist
  obtain ⟨p₂, hp₂⟩ := hz₂.exists_walk_length_eq_dist
  have hp₁len : p₁.length = n - 1 := by rw [hp₁, hd₁]
  have hp₂len : p₂.length = n - 1 := by rw [hp₂, hd₂]
  have hr₁len : (p₁.concat ha₁).length = n := by
    rw [Walk.length_concat, hp₁len]; omega
  have hr₂len : (p₂.concat ha₂).length = n := by
    rw [Walk.length_concat, hp₂len]; omega
  have hpath₁ : (p₁.concat ha₁).IsPath :=
    Walk.isPath_of_length_eq_dist _ (by rw [hr₁len, hwd])
  have hpath₂ : (p₂.concat ha₂).IsPath :=
    Walk.isPath_of_length_eq_dist _ (by rw [hr₂len, hwd])
  have heq : (p₁.concat ha₁) = (p₂.concat ha₂) := by
    by_contra hne
    obtain ⟨x, -, -, c, hc, hclen⟩ := hpath₁.exists_isCycle_length_le_add_of_ne hpath₂ hne
    have hc_le : c.length ≤ 8 := by
      rw [hr₁len, hr₂len] at hclen
      omega
    exact hshort (c.mapLe hle) (hc.mapLe hle) (by
      change (c.map (.ofLE hle)).length ≤ 8
      simpa only [Walk.length_map] using hc_le)
  have hpen₁ : (p₁.concat ha₁).penultimate = z₁ := by simp
  have hpen₂ : (p₂.concat ha₂).penultimate = z₂ := by simp
  calc z₁ = (p₁.concat ha₁).penultimate := hpen₁.symm
    _ = (p₂.concat ha₂).penultimate := by rw [heq]
    _ = z₂ := hpen₂

/-- Every vertex at distance `n ≥ 1` from `u` has a neighbour at distance `n - 1`. -/
private lemma exists_parent {H : SimpleGraph V} [DecidableRel H.Adj]
    {u w : V} {n : ℕ} (hw : H.Reachable u w) (hwd : H.dist u w = n) (hn : 1 ≤ n) :
    ∃ y, H.Adj y w ∧ H.dist u y = n - 1 := by
  obtain ⟨p, hp_path, hp_len⟩ := hw.exists_path_of_dist
  have hlen : p.length = n := by rw [hp_len, hwd]
  have hnil : ¬ p.Nil := by
    rw [← Walk.length_eq_zero_iff, hlen]; omega
  refine ⟨p.penultimate, p.adj_penultimate hnil, ?_⟩
  have hup : H.dist u p.penultimate ≤ n - 1 := by
    have := dist_le p.dropLast
    rw [Walk.length_dropLast, hlen] at this
    exact this
  have hlo : n ≤ H.dist u p.penultimate + 1 := by
    have h := (p.adj_penultimate hnil).reachable.dist_triangle_right u
    rw [dist_eq_one_iff_adj.mpr (p.adj_penultimate hnil)] at h
    rw [hwd] at h
    exact h
  omega

/-- A neighbour of `w` cannot also be at the same distance from `u` as `w`: the resulting closed
walk has odd length `2k + 1`, which a bipartite graph cannot contain. -/
private lemma not_dist_eq_of_adj {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    {u w z : V} {k : ℕ} (hle : H ≤ G) (hbip : G.Colorable 2)
    (hwr : H.Reachable u w) (hwd : H.dist u w = k) (hadj : H.Adj w z)
    (hzd : H.dist u z = k) : False := by
  obtain ⟨p, hp⟩ := hwr.exists_walk_length_eq_dist
  have hzr : H.Reachable u z := hwr.trans hadj.reachable
  obtain ⟨q, hq⟩ := hzr.exists_walk_length_eq_dist
  have hlen : ((p.concat hadj).append q.reverse).length = 2 * k + 1 := by
    rw [Walk.length_append, Walk.length_concat, Walk.length_reverse, hp, hq, hwd, hzd]
    omega
  have hev : Even ((p.concat hadj).append q.reverse).length := by
    have h := even_length_of_colorable hbip (((p.concat hadj).append q.reverse).mapLe hle)
    change Even ((((p.concat hadj).append q.reverse).map (.ofLE hle)).length) at h
    simpa only [Walk.length_map] using h
  rw [hlen] at hev
  obtain ⟨m, hm⟩ := hev
  omega

/-- One step of the Moore exposure: if every vertex of the two levels has degree `3` in `H` and the
excluded vertex `v` is outside the levels up to `4`, then the level sizes double. -/
private lemma card_level_succ {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    {u v : V} (hle : H ≤ G) (hbip : G.Colorable 2)
    (hshort : ∀ {x : V} (c : G.Walk x x), c.IsCycle → c.length ≤ 8 → False)
    (hdeg : ∀ w, w ≠ u → w ≠ v → H.degree w = 3)
    (hfar : ∀ j ≤ 4, v ∉ level H u j)
    {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    (level H u (k + 1)).card = 2 * (level H u k).card := by
  classical
  -- every vertex of `level k` has exactly two neighbours in `level (k+1)`
  have hchild : ∀ w ∈ level H u k, ((H.neighborFinset w) ∩ level H u (k + 1)).card = 2 := by
    intro w hw
    have hwmem : w ∈ level H u k := hw
    rw [mem_level] at hw
    obtain ⟨hwr, hwd⟩ := hw
    have hwu : w ≠ u := by
      rintro rfl
      rw [dist_self] at hwd
      omega
    have hwv : w ≠ v := fun h => hfar k (by omega) (by rw [← h]; exact hwmem)
    have hwdeg : (H.neighborFinset w).card = 3 := by
      rw [H.card_neighborFinset_eq_degree]
      exact hdeg w hwu hwv
    -- classification of the neighbours of `w`
    have hclass : ∀ z ∈ H.neighborFinset w,
        H.dist u z ≤ k + 1 ∧ k - 1 ≤ H.dist u z ∧ H.dist u z ≠ k := by
      intro z hz
      have hadj : H.Adj w z := (H.mem_neighborFinset w z).mp hz
      refine ⟨?_, ?_, ?_⟩
      · have h := (hadj.reachable).dist_triangle_right u
        rw [dist_eq_one_iff_adj.mpr hadj] at h
        omega
      · have h := (hwr.trans hadj.reachable).dist_triangle_left w
        rw [dist_eq_one_iff_adj.mpr hadj.symm] at h
        omega
      · intro hzd
        exact not_dist_eq_of_adj hle hbip hwr hwd hadj hzd
    -- at most one neighbour at distance `k - 1`
    have hparent_le : ((H.neighborFinset w) ∩ level H u (k - 1)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro z₁ hz₁ z₂ hz₂
      rw [Finset.mem_inter, mem_level] at hz₁ hz₂
      exact eq_of_two_parents hle hbip hshort (by omega) hk1 hwr hwd
        hz₁.2.1 hz₁.2.2 ((H.mem_neighborFinset w z₁).mp hz₁.1).symm
        hz₂.2.1 hz₂.2.2 ((H.mem_neighborFinset w z₂).mp hz₂.1).symm
    obtain ⟨y, hyadj, hydist⟩ := exists_parent hwr hwd hk1
    have hparent_ge : 1 ≤ ((H.neighborFinset w) ∩ level H u (k - 1)).card := by
      refine Finset.card_pos.mpr ⟨y, ?_⟩
      rw [Finset.mem_inter, mem_level]
      exact ⟨(H.mem_neighborFinset w y).mpr hyadj.symm,
        hwr.trans hyadj.symm.reachable, hydist⟩
    have hparent : ((H.neighborFinset w) ∩ level H u (k - 1)).card = 1 := by omega
    -- the neighbours split into distance `k - 1` and distance `k + 1`
    have hpart : H.neighborFinset w = (H.neighborFinset w ∩ level H u (k - 1))
        ∪ (H.neighborFinset w ∩ level H u (k + 1)) := by
      ext z
      rw [Finset.mem_union, Finset.mem_inter, Finset.mem_inter]
      constructor
      · intro hz
        obtain ⟨hup, hlo, hne⟩ := hclass z hz
        have hadj : H.Adj w z := (H.mem_neighborFinset w z).mp hz
        have hzr : H.Reachable u z := hwr.trans hadj.reachable
        by_cases hcase : H.dist u z = k - 1
        · exact Or.inl ⟨hz, mem_level.mpr ⟨hzr, hcase⟩⟩
        · refine Or.inr ⟨hz, mem_level.mpr ⟨hzr, ?_⟩⟩
          omega
      · rintro (⟨hz, -⟩ | ⟨hz, -⟩)
        · exact hz
        · exact hz
    have hdisj : Disjoint (H.neighborFinset w ∩ level H u (k - 1))
        (H.neighborFinset w ∩ level H u (k + 1)) := by
      rw [Finset.disjoint_left]
      intro z hz₁ hz₂
      rw [Finset.mem_inter] at hz₁ hz₂
      exact (Finset.disjoint_left.mp (level_disjoint (by omega : k - 1 ≠ k + 1)))
        hz₁.2 hz₂.2
    have hcard : (H.neighborFinset w).card
        = ((H.neighborFinset w) ∩ level H u (k - 1)).card
          + ((H.neighborFinset w) ∩ level H u (k + 1)).card := by
      calc
        (H.neighborFinset w).card =
            ((H.neighborFinset w ∩ level H u (k - 1)) ∪
              (H.neighborFinset w ∩ level H u (k + 1))).card := congrArg Finset.card hpart
        _ = _ := Finset.card_union_of_disjoint hdisj
    omega
  -- every vertex of `level (k+1)` has exactly one neighbour in `level k`
  have hpar : ∀ z ∈ level H u (k + 1), ((H.neighborFinset z) ∩ level H u k).card = 1 := by
    intro z hz
    have hzmem : z ∈ level H u (k + 1) := hz
    rw [mem_level] at hz
    obtain ⟨hzr, hzd⟩ := hz
    have hle1 : ((H.neighborFinset z) ∩ level H u k).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro w₁ hw₁ w₂ hw₂
      rw [Finset.mem_inter, mem_level] at hw₁ hw₂
      exact eq_of_two_parents hle hbip hshort (by omega) (by omega) hzr hzd
        hw₁.2.1 hw₁.2.2 ((H.mem_neighborFinset z w₁).mp hw₁.1).symm
        hw₂.2.1 hw₂.2.2 ((H.mem_neighborFinset z w₂).mp hw₂.1).symm
    obtain ⟨y, hyadj, hydist⟩ := exists_parent hzr hzd (by omega : 1 ≤ k + 1)
    have hge1 : 1 ≤ ((H.neighborFinset z) ∩ level H u k).card := by
      refine Finset.card_pos.mpr ⟨y, ?_⟩
      rw [Finset.mem_inter, mem_level]
      exact ⟨(H.mem_neighborFinset z y).mpr hyadj.symm,
        hzr.trans hyadj.symm.reachable, by omega⟩
    omega
  have hdisj : ∀ a ∈ level H u k, ∀ b ∈ level H u k, a ≠ b →
      Disjoint (H.neighborFinset a ∩ level H u (k + 1))
        (H.neighborFinset b ∩ level H u (k + 1)) := by
    intro a ha b hb hab
    rw [Finset.disjoint_left]
    intro z hza hzb
    rw [Finset.mem_inter] at hza hzb
    have h1 : a ∈ H.neighborFinset z ∩ level H u k := by
      rw [Finset.mem_inter]
      exact ⟨(H.mem_neighborFinset z a).mpr
        ((H.mem_neighborFinset a z).mp hza.1).symm, ha⟩
    have h2 : b ∈ H.neighborFinset z ∩ level H u k := by
      rw [Finset.mem_inter]
      exact ⟨(H.mem_neighborFinset z b).mpr
        ((H.mem_neighborFinset b z).mp hzb.1).symm, hb⟩
    exact hab ((Finset.card_le_one.mp (le_of_eq (hpar z hza.2))) a h1 b h2)
  have hbU : level H u (k + 1)
      = (level H u k).biUnion (fun w => H.neighborFinset w ∩ level H u (k + 1)) := by
    ext z
    rw [Finset.mem_biUnion]
    constructor
    · intro hz
      have hzmem : z ∈ level H u (k + 1) := hz
      rw [mem_level] at hz
      obtain ⟨y, hyadj, hydist⟩ := exists_parent hz.1 hz.2 (by omega : 1 ≤ k + 1)
      exact ⟨y, mem_level.mpr ⟨hz.1.trans hyadj.symm.reachable, hydist⟩,
        by rw [Finset.mem_inter]; exact ⟨(H.mem_neighborFinset y z).mpr hyadj, hzmem⟩⟩
    · rintro ⟨y, -, hy⟩
      rw [Finset.mem_inter] at hy
      exact hy.2
  rw [hbU, Finset.card_biUnion hdisj,
    Finset.sum_const_nat (fun w hw => hchild w hw)]
  omega

/-! ### The excluded vertex is far from the root -/

/-- If `b` is adjacent to `a` in `G` but not in `H ≤ G`, then `b` is not in any level of `a` up to
depth `4`: a shortest `H`-path `a → b` would close up with the `G`-edge `ab` into a cycle of length
at most `5`. -/
private lemma notMem_level_of_not_adj {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    {a b : V} (hab : G.Adj a b) (hle : H ≤ G) (hnadj : ¬ H.Adj a b)
    (hbip : G.Colorable 2)
    (hshort : ∀ {x : V} (c : G.Walk x x), c.IsCycle → c.length ≤ 8 → False)
    {k : ℕ} (hk : k ≤ 4) : b ∉ level H a k := by
  intro hb
  rw [mem_level] at hb
  obtain ⟨hr, hd⟩ := hb
  have hk_ne0 : k ≠ 0 := by
    rintro rfl
    exact hab.ne (hr.dist_eq_zero_iff.mp hd)
  have hk_ne1 : k ≠ 1 := by
    rintro rfl
    exact hnadj (dist_eq_one_iff_adj.mp hd)
  have hk2 : 2 ≤ k := by omega
  obtain ⟨p, hp_path, hp_len⟩ := hr.exists_path_of_dist
  have hp_len' : p.length = k := by rw [hp_len, hd]
  have hne : (p.mapLe hle) ≠ hab.toWalk := by
    intro heq
    have h := congrArg Walk.length heq
    have hmaplen : (p.mapLe hle).length = p.length := by
      change (p.map (.ofLE hle)).length = p.length
      exact Walk.length_map _ _
    rw [hmaplen, hab.length_toWalk, hp_len'] at h
    omega
  obtain ⟨x, -, -, c, hc, hclen⟩ :=
    (hp_path.mapLe hle).exists_isCycle_length_le_add_of_ne hab.isPath_toWalk hne
  refine hshort c hc ?_
  have hmaplen : (p.mapLe hle).length = p.length := by
    change (p.map (.ofLE hle)).length = p.length
    exact Walk.length_map _ _
  rw [hmaplen, hab.length_toWalk, hp_len'] at hclen
  omega

end Moore

/-! ### The Moore bound -/

/-- **Edge-rooted Moore reduction (contrapositive form).**  A finite simple cubic bipartite graph
with at least one edge and no simple cycle of length at most `8` has at least `62` vertices.

This is the Moore-bound observation behind arXiv:2608.02675, Lemma `lem:moore`: in
`H := G.deleteEdges {s(u,v)}` the balls of radius `4` about the endpoints of an edge `uv` are
disjoint depth-four cubic trees with level sizes `1,2,4,8,16`, contributing `2 * 31 = 62` distinct
vertices. -/
theorem card_verts_ge_62_of_edge_of_cubic_bipartite
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree 3) (hbip : G.IsBipartite)
    {u v : V} (huv : G.Adj u v)
    (hshort : ∀ {x : V} (c : G.Walk x x), c.IsCycle → c.length ≤ 8 → False) :
    62 ≤ Fintype.card V := by
  classical
  set H : SimpleGraph V := G.deleteEdges {s(u, v)} with hHdef
  have hle : H ≤ G := by rw [hHdef]; exact SimpleGraph.deleteEdges_le _
  have hnadj : ¬ H.Adj u v := by rw [hHdef]; simp
  -- degree bookkeeping
  have hdeg : ∀ w, w ≠ u → w ≠ v → H.degree w = 3 := by
    intro w hwu hwv
    have hnb : H.neighborFinset w = G.neighborFinset w := by
      ext x
      rw [mem_neighborFinset, mem_neighborFinset]
      constructor
      · intro h
        rw [hHdef, deleteEdges_adj] at h
        exact h.1
      · intro h
        rw [hHdef, deleteEdges_adj]
        refine ⟨h, fun hc => ?_⟩
        rw [Set.mem_singleton_iff, Sym2.eq_iff] at hc
        rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hwu rfl
        · exact hwv rfl
    rw [← H.card_neighborFinset_eq_degree, hnb, G.card_neighborFinset_eq_degree]
    exact hreg.degree_eq w
  have hdegu : (H.neighborFinset u).card = 2 := by
    have hsym : ∀ x, s(u, x) = s(u, v) ↔ x = v := by
      intro x
      rw [Sym2.eq_iff]
      constructor
      · rintro (⟨-, rfl⟩ | ⟨huv', -⟩)
        · rfl
        · exact absurd huv' huv.ne
      · rintro rfl
        exact Or.inl ⟨rfl, rfl⟩
    have hset : H.neighborFinset u = G.neighborFinset u \ {v} := by
      ext x
      rw [Finset.mem_sdiff, mem_neighborFinset, mem_neighborFinset, hHdef, deleteEdges_adj,
        Set.mem_singleton_iff, Finset.mem_singleton, hsym x]
    rw [hset, Finset.card_sdiff]
    have hv_mem : v ∈ G.neighborFinset u := by
      rw [mem_neighborFinset]; exact huv
    rw [Finset.singleton_inter_of_mem hv_mem, Finset.card_singleton,
      G.card_neighborFinset_eq_degree, hreg.degree_eq u]
  -- the excluded vertex is outside both depth-four balls
  have hfar : ∀ j ≤ 4, v ∉ level H u j :=
    fun j hj => notMem_level_of_not_adj huv hle hnadj hbip hshort hj
  have hfar' : ∀ j ≤ 4, u ∉ level H v j :=
    fun j hj => notMem_level_of_not_adj huv.symm hle (fun h => hnadj h.symm) hbip hshort hj
  -- level sizes from `u`
  have h1u : (level H u 1).card = 2 := by
    have hset : level H u 1 = H.neighborFinset u := by
      ext w
      rw [mem_level, mem_neighborFinset, dist_eq_one_iff_adj]
      exact ⟨fun h => h.2, fun h => ⟨h.reachable, h⟩⟩
    rw [hset, hdegu]
  have h2u : (level H u 2).card = 4 := by
    have := card_level_succ hle hbip hshort hdeg hfar (k := 1) le_rfl (by omega)
    rw [h1u] at this
    norm_num at this ⊢
    exact this
  have h3u : (level H u 3).card = 8 := by
    have := card_level_succ hle hbip hshort hdeg hfar (k := 2) (by omega) (by omega)
    rw [h2u] at this
    norm_num at this ⊢
    exact this
  have h4u : (level H u 4).card = 16 := by
    have := card_level_succ hle hbip hshort hdeg hfar (k := 3) (by omega) le_rfl
    rw [h3u] at this
    norm_num at this ⊢
    exact this
  -- level sizes from `v`
  have h1v : (level H v 1).card = 2 := by
    have hset : level H v 1 = H.neighborFinset v := by
      ext w
      rw [mem_level, mem_neighborFinset, dist_eq_one_iff_adj]
      exact ⟨fun h => h.2, fun h => ⟨h.reachable, h⟩⟩
    have hsetv : H.neighborFinset v = G.neighborFinset v \ {u} := by
      have hsym : ∀ x, s(v, x) = s(u, v) ↔ x = u := by
        intro x
        rw [Sym2.eq_iff]
        constructor
        · rintro (⟨hvu', -⟩ | ⟨-, rfl⟩)
          · exact absurd hvu' huv.ne.symm
          · rfl
        · rintro rfl
          exact Or.inr ⟨rfl, rfl⟩
      ext x
      rw [Finset.mem_sdiff, mem_neighborFinset, mem_neighborFinset, hHdef, deleteEdges_adj,
        Set.mem_singleton_iff, Finset.mem_singleton, hsym x]
    rw [hset, hsetv, Finset.card_sdiff]
    have hu_mem : u ∈ G.neighborFinset v := by
      rw [mem_neighborFinset]; exact huv.symm
    rw [Finset.singleton_inter_of_mem hu_mem, Finset.card_singleton,
      G.card_neighborFinset_eq_degree, hreg.degree_eq v]
  have h2v : (level H v 2).card = 4 := by
    have := card_level_succ (u := v) (v := u) hle hbip hshort
      (fun w _ _ => hdeg w ‹w ≠ u› ‹w ≠ v›) hfar' (k := 1) le_rfl (by omega)
    rw [h1v] at this
    norm_num at this ⊢
    exact this
  have h3v : (level H v 3).card = 8 := by
    have := card_level_succ (u := v) (v := u) hle hbip hshort
      (fun w _ _ => hdeg w ‹w ≠ u› ‹w ≠ v›) hfar' (k := 2) (by omega) (by omega)
    rw [h2v] at this
    norm_num at this ⊢
    exact this
  have h4v : (level H v 4).card = 16 := by
    have := card_level_succ (u := v) (v := u) hle hbip hshort
      (fun w _ _ => hdeg w ‹w ≠ u› ‹w ≠ v›) hfar' (k := 3) (by omega) le_rfl
    rw [h3v] at this
    norm_num at this ⊢
    exact this
  have hcardu : (ball H u 4).card = 31 := card_ball_four H u h1u h2u h3u h4u
  have hcardv : (ball H v 4).card = 31 := card_ball_four H v h1v h2v h3v h4v
  -- the two balls are disjoint
  have hdisj : Disjoint (ball H u 4) (ball H v 4) := by
    rw [Finset.disjoint_left]
    intro w hwu hwv
    rw [mem_ball] at hwu hwv
    obtain ⟨hwu_r, hwu_d⟩ := hwu
    obtain ⟨hwv_r, hwv_d⟩ := hwv
    obtain ⟨p, hp_len⟩ := hwu_r.exists_walk_length_eq_dist
    obtain ⟨q, hq_len⟩ := hwv_r.exists_walk_length_eq_dist
    have hreach : H.Reachable u v := hwu_r.trans hwv_r.symm
    obtain ⟨r, hr_path, hr_len⟩ := hreach.exists_path_of_dist
    have hr_le : r.length ≤ 8 := by
      have h := dist_le (p.append q.reverse)
      rw [Walk.length_append, Walk.length_reverse, hp_len, hq_len] at h
      omega
    have hr_ge : 2 ≤ r.length := by
      rw [hr_len]
      exact hreach.one_lt_dist_of_ne_of_not_adj huv.ne hnadj
    have hne : (r.mapLe hle) ≠ huv.toWalk := by
      intro heq
      have h := congrArg Walk.length heq
      have hr_map_len : (r.mapLe hle).length = r.length := by
        change (r.map (.ofLE hle)).length = r.length
        exact Walk.length_map _ _
      rw [hr_map_len, huv.length_toWalk] at h
      omega
    obtain ⟨x, -, -, c, hc, hclen⟩ :=
      (hr_path.mapLe hle).exists_isCycle_length_le_add_of_ne huv.isPath_toWalk hne
    have hc_le : c.length ≤ 9 := by
      have hr_map_len : (r.mapLe hle).length = r.length := by
        change (r.map (.ofLE hle)).length = r.length
        exact Walk.length_map _ _
      rw [hr_map_len, huv.length_toWalk] at hclen
      omega
    exact false_of_isCycle_le_nine hbip hshort hc hc_le
  have hunion : (ball H u 4 ∪ ball H v 4).card = 62 := by
    rw [Finset.card_union_of_disjoint hdisj, hcardu, hcardv]
  have hle_card : (ball H u 4 ∪ ball H v 4).card ≤ Fintype.card V := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  omega

/-! ### The source's stated corollary -/

/-- **Edge-rooted Moore reduction.**  Every finite simple cubic bipartite graph on at most `58`
vertices with no `C₄` and no `C₈` contains a `C₆`.

This is arXiv:2608.02675, Lemma `lem:moore`, in its stated form with one added formal guard:
`hV : Nonempty V` makes the source's standard nonempty-graph convention explicit, because Mathlib's
`IsRegularOfDegree 3` is vacuous on the empty vertex type.  If a `C₆` were also absent then the
hypotheses of `card_verts_ge_62_of_edge_of_cubic_bipartite` hold, forcing at least `62` vertices and
contradicting `Fintype.card V ≤ 58`.  The source's *main* theorem — the `60`-vertex bound obtained
by a certified exhaustive search on the triangle-rooted configurations — is not formalized here. -/
theorem exists_six_cycle_of_cubic_bipartite
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hV : Nonempty V) (hreg : G.IsRegularOfDegree 3) (hbip : G.IsBipartite)
    (h4 : ∀ (x : V) (c : G.Walk x x), c.IsCycle → c.length ≠ 4)
    (h8 : ∀ (x : V) (c : G.Walk x x), c.IsCycle → c.length ≠ 8)
    (hcard : Fintype.card V ≤ 58) :
    ∃ (x : V) (c : G.Walk x x), c.IsCycle ∧ c.length = 6 := by
  classical
  by_contra hcon
  push Not at hcon
  have hshort : ∀ {x : V} (c : G.Walk x x), c.IsCycle → c.length ≤ 8 → False := by
    intro x c hc hlen
    have h3 : 3 ≤ c.length := hc.three_le_length
    obtain ⟨m, hm⟩ := even_length_of_colorable hbip c
    have hmem : c.length = 4 ∨ c.length = 6 ∨ c.length = 8 := by omega
    rcases hmem with h | h | h
    · exact h4 x c hc h
    · exact hcon x c hc h
    · exact h8 x c hc h
  obtain ⟨x⟩ := hV
  have hne : (G.neighborFinset x).Nonempty := by
    rw [← Finset.card_pos, G.card_neighborFinset_eq_degree, hreg.degree_eq x]
    norm_num
  obtain ⟨y, hy⟩ := hne
  have hxy : G.Adj x y := (G.mem_neighborFinset x y).mp hy
  have := card_verts_ge_62_of_edge_of_cubic_bipartite hreg hbip hxy hshort
  omega

end Erdos64