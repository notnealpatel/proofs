import Erdos.Erdos64.UniqueCubicClawCenter

/-!
# Canonical quotient for cubic graphs with at most two claw centers

The blocks here are constructed from actual three-cliques and actual induced-claw
centers of the original graph. This module proves the canonical partition, uniqueness
of edges between blocks, cubicity of the quotient, and its strict order reduction.
The finite `Finset V`-valued block carrier stays in the original universe, allowing
unrestricted smaller-order minimality to supply a quotient dyadic cycle. The doubled
ordinary original-graph cycle and final bounded exclusion are proved downstream in
`CubicFewClawCenters`. The at-most-two restriction is explicit; these modules do not
prove the unrestricted Erdős–Gyárfás conjecture.
-/

set_option autoImplicit false

namespace Erdos64.CubicFewClawCenters

open SimpleGraph

universe u

noncomputable local instance (V : Type*) : DecidableEq V := Classical.decEq V

/-- In a graph without ordinary four-cycles, an edge belongs to at most one triangle. -/
theorem triangle_third_unique {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) {x a b c : V}
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hab : G.Adj a b)
    (hxc : G.Adj x c) (hac : G.Adj a c) : b = c := by
  by_contra hbc
  exact UniqueCubicClawCenter.not_four_cycle G hG hab.ne.symm hbc hxb.ne.symm
    hac.ne hxa.ne.symm hxc.ne.symm hab.symm hac hxc.symm hxb

/-- Two triangles through a cubic vertex have the same other two vertices. -/
theorem triangle_pair_unique {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) {x a b c d : V}
    (hx : G.degree x = 3)
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hab : G.Adj a b)
    (hxc : G.Adj x c) (hxd : G.Adj x d) (hcd : G.Adj c d) :
    (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  by_cases hca : c = a
  · subst c
    exact Or.inl ⟨rfl, (triangle_third_unique G hG hxa hxb hab hxd hcd).symm⟩
  by_cases hcb : c = b
  · subst c
    exact Or.inr ⟨rfl, (triangle_third_unique G hG hxb hxa hab.symm hxd hcd).symm⟩
  have hexhaust := UniqueCubicClawCenter.neighbors_eq_claw_leaves G hx
    hab.ne (Ne.symm hca) (Ne.symm hcb) hxa hxb hxc
  rcases (hexhaust d).mp hxd with hda | hdb | hdc
  · subst d
    exact False.elim (hcb (triangle_third_unique G hG hxa hxb hab hxc hcd.symm).symm)
  · subst d
    exact False.elim (hca (triangle_third_unique G hG hxb hxa hab.symm hxc hcd.symm).symm)
  · exact False.elim (hcd.ne hdc.symm)

/-- A three-clique containing `x` can be displayed as `x` and two adjacent neighbors. -/
theorem triangle_at_vertex {V : Type u} (G : SimpleGraph V) {s : Finset V}
    (hs : G.IsNClique 3 s) {x : V} (hx : x ∈ s) :
    ∃ a b : V, a ≠ b ∧ G.Adj x a ∧ G.Adj x b ∧ G.Adj a b ∧ s = {x, a, b} := by
  classical
  have herase : (s.erase x).card = 2 := by
    have hc := Finset.card_erase_add_one hx
    rw [hs.card_eq] at hc
    omega
  obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp herase
  have ha : a ∈ s.erase x := by rw [he]; simp
  have hb : b ∈ s.erase x := by rw [he]; simp
  have ha' := Finset.mem_erase.mp ha
  have hb' := Finset.mem_erase.mp hb
  refine ⟨a, b, hab, hs.isClique hx ha'.2 ha'.1.symm,
    hs.isClique hx hb'.2 hb'.1.symm, hs.isClique ha'.2 hb'.2 hab, ?_⟩
  rw [← Finset.insert_erase hx, he]

/-- Actual triangles meeting at a cubic vertex coincide in a counterexample. -/
theorem triangles_eq_of_mem {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) (hCubic : ∀ x, G.degree x = 3)
    {s t : Finset V} (hs : G.IsNClique 3 s) (ht : G.IsNClique 3 t)
    {x : V} (hxs : x ∈ s) (hxt : x ∈ t) : s = t := by
  classical
  obtain ⟨a, b, _, hxa, hxb, hab, hs'⟩ := triangle_at_vertex G hs hxs
  obtain ⟨c, d, _, hxc, hxd, hcd, ht'⟩ := triangle_at_vertex G ht hxt
  rcases triangle_pair_unique G hG (hCubic x) hxa hxb hab hxc hxd hcd with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hs'.trans ht'.symm
  · rw [hs', ht']
    ext y
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

/-- Distinct actual triangles are disjoint in a cubic counterexample. -/
theorem triangles_disjoint {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) (hCubic : ∀ x, G.degree x = 3)
    {s t : Finset V} (hs : G.IsNClique 3 s) (ht : G.IsNClique 3 t)
    (hne : s ≠ t) : Disjoint s t := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxs hxt
  exact hne (triangles_eq_of_mem G hG hCubic hs ht hxs hxt)

/-- In a cubic graph, a vertex is not a claw center exactly when it is in an actual triangle. -/
theorem not_claw_iff_mem_triangle {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {x : V} (hx : G.degree x = 3) :
    ¬ UniqueCubicClawCenter.Claw G x ↔ ∃ s : Finset V, G.IsNClique 3 s ∧ x ∈ s := by
  classical
  constructor
  · intro hn
    have hc : 2 < (G.neighborFinset x).card := by change 2 < G.degree x; omega
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hc
    have hxa := (G.mem_neighborFinset x a).mp ha
    have hxb := (G.mem_neighborFinset x b).mp hb
    have hxc := (G.mem_neighborFinset x c).mp hc
    have he : G.Adj a b ∨ G.Adj a c ∨ G.Adj b c := by
      by_contra he
      push Not at he
      exact hn ⟨a, b, c, hab, hac, hbc, hxa, hxb, hxc, he.1, he.2.1, he.2.2⟩
    have make (a b : V) (hxa : G.Adj x a) (hxb : G.Adj x b) (hab : G.Adj a b) :
        ∃ s : Finset V, G.IsNClique 3 s ∧ x ∈ s := by
      refine ⟨{x, a, b}, ⟨?_, ?_⟩, by simp⟩
      · intro y hy z hz hyz
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hy hz
        rcases hy with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl
        all_goals first
          | exact False.elim (hyz rfl)
          | exact hxa
          | exact hxb
          | exact hab
          | exact hxa.symm
          | exact hxb.symm
          | exact hab.symm
      · simp [hxa.ne, hxb.ne, hab.ne]
    rcases he with he | he | he
    · exact make a b hxa hxb he
    · exact make a c hxa hxc he
    · exact make b c hxb hxc he
  · rintro ⟨s, hs, hxs⟩ hclaw
    obtain ⟨a, b, _, hxa, hxb, hab, _⟩ := triangle_at_vertex G hs hxs
    exact UniqueCubicClawCenter.poles_nonadjacent G hx hclaw hxa hxb hab

/-- Canonical blocks are actual three-cliques and singleton induced-claw centers.
As a subtype of `Finset V`, the block type remains in the universe of `V`. -/
def Block {V : Type u} (G : SimpleGraph V) : Type u :=
  {s : Finset V // G.IsNClique 3 s ∨
    ∃ x : V, UniqueCubicClawCenter.Claw G x ∧ s = {x}}

example {V : Type u} (G : SimpleGraph V) (s : Finset V) :
    (G.IsNClique 3 s ∨ ∃ x : V, UniqueCubicClawCenter.Claw G x ∧ s = {x}) ↔
      ∃ b : Block G, b.val = s := by
  constructor
  · intro hs
    exact ⟨⟨s, hs⟩, rfl⟩
  · rintro ⟨b, rfl⟩
    exact b.property

/-- Canonical blocks form a finite type. -/
noncomputable instance blockFintype {V : Type u} [Fintype V] (G : SimpleGraph V) :
    Fintype (Block G) := by
  unfold Block
  exact Fintype.ofFinite _

/-- Every canonical block contains a vertex. -/
theorem block_nonempty {V : Type u} (G : SimpleGraph V) (b : Block G) :
    b.val.Nonempty := by
  rcases b.property with ht | ⟨x, _, hs⟩
  · exact Finset.card_pos.mp (by rw [ht.card_eq]; decide)
  · rw [hs]
    exact Finset.singleton_nonempty x

/-- Every original vertex lies in a canonical block. -/
theorem exists_block {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hCubic : ∀ x, G.degree x = 3) (x : V) :
    ∃ b : Block G, x ∈ b.val := by
  classical
  by_cases hc : UniqueCubicClawCenter.Claw G x
  · exact ⟨⟨{x}, Or.inr ⟨x, hc, rfl⟩⟩, by simp⟩
  · obtain ⟨s, hs, hxs⟩ := (not_claw_iff_mem_triangle G (hCubic x)).mp hc
    exact ⟨⟨s, Or.inl hs⟩, hxs⟩

/-- Two canonical blocks that meet must be equal. -/
theorem blocks_eq_of_mem {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) (hCubic : ∀ x, G.degree x = 3)
    {s t : Block G} {x : V} (hxs : x ∈ s.val) (hxt : x ∈ t.val) : s = t := by
  apply Subtype.ext
  rcases s.property with hs | ⟨a, ha, hs⟩ <;>
    rcases t.property with ht | ⟨b, hb, ht⟩
  · exact triangles_eq_of_mem G hG hCubic hs ht hxs hxt
  · have hxb : x = b := by simpa [ht] using hxt
    subst b
    exact False.elim (((not_claw_iff_mem_triangle G (hCubic x)).mpr ⟨s.val, hs, hxs⟩) hb)
  · have hxa : x = a := by simpa [hs] using hxs
    subst a
    exact False.elim (((not_claw_iff_mem_triangle G (hCubic x)).mpr ⟨t.val, ht, hxt⟩) ha)
  · have hxa : x = a := by simpa [hs] using hxs
    have hxb : x = b := by simpa [ht] using hxt
    rw [hs, ht, ← hxa, ← hxb]

/-- Distinct canonical blocks are disjoint as sets of original vertices. -/
theorem blocks_disjoint {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) (hCubic : ∀ x, G.degree x = 3)
    {s t : Block G} (hne : s ≠ t) : Disjoint s.val t.val := by
  apply Finset.disjoint_left.mpr
  intro x hxs hxt
  exact hne (blocks_eq_of_mem G hG hCubic hxs hxt)

/-- A vertex of an actual triangle has a unique external neighbor in a cubic graph. -/
theorem triangle_external_unique {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hCubic : ∀ x, G.degree x = 3)
    {s : Finset V} (hs : G.IsNClique 3 s) {x y z : V} (hx : x ∈ s)
    (hxy : G.Adj x y) (hy : y ∉ s) (hxz : G.Adj x z) (hz : z ∉ s) : y = z := by
  obtain ⟨a, b, hab, hxa, hxb, _, he⟩ := triangle_at_vertex G hs hx
  have hya : y ≠ a := by intro heq; subst y; exact hy (by rw [he]; simp)
  have hyb : y ≠ b := by intro heq; subst y; exact hy (by rw [he]; simp)
  have hza : z ≠ a := by intro heq; subst z; exact hz (by rw [he]; simp)
  have hzb : z ≠ b := by intro heq; subst z; exact hz (by rw [he]; simp)
  have hexhaust := UniqueCubicClawCenter.neighbors_eq_claw_leaves G (hCubic x)
    hab (Ne.symm hya) (Ne.symm hyb) hxa hxb hxy
  rcases (hexhaust z).mp hxz with h | h | h
  · exact False.elim (hza h)
  · exact False.elim (hzb h)
  · exact h.symm

/-- A singleton claw block cannot have two different ports in the same triangle. -/
theorem claw_triangle_neighbor_unique {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hCubic : ∀ x, G.degree x = 3) {x : V}
    (hc : UniqueCubicClawCenter.Claw G x) {s : Finset V} (hs : G.IsNClique 3 s)
    {a b : V} (ha : a ∈ s) (hb : b ∈ s) (hxa : G.Adj x a) (hxb : G.Adj x b) :
    a = b := by
  by_contra hab
  exact UniqueCubicClawCenter.poles_nonadjacent G (hCubic x) hc hxa hxb
    (hs.isClique ha hb hab)

/-- The actual simple quotient graph: distinct blocks are adjacent when an original edge
joins one vertex in each. Internal triangle edges do not become quotient loops. -/
def quotient {V : Type u} (G : SimpleGraph V) : SimpleGraph (Block G) where
  Adj s t := s ≠ t ∧ ∃ a ∈ s.val, ∃ b ∈ t.val, G.Adj a b
  symm := ⟨by
    rintro s t ⟨hne, a, ha, b, hb, hab⟩
    exact ⟨hne.symm, b, hb, a, ha, hab.symm⟩⟩
  loopless := ⟨by intro s h; exact h.1 rfl⟩

example {V : Type u} (G : SimpleGraph V) (s t : Block G) :
    (quotient G).Adj s t ↔ s ≠ t ∧ ∃ a ∈ s.val, ∃ b ∈ t.val, G.Adj a b := Iff.rfl

/-- The original edges between two distinct canonical blocks are unique, including
both endpoints; this rules out multiplicity loss in the simple quotient. -/
theorem external_edge_unique {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) (hCubic : ∀ x, G.degree x = 3)
    {s t : Block G} (hne : s ≠ t) {a b c d : V}
    (ha : a ∈ s.val) (hb : b ∈ t.val) (hc : c ∈ s.val) (hd : d ∈ t.val)
    (hab : G.Adj a b) (hcd : G.Adj c d) : a = c ∧ b = d := by
  have hdis := Finset.disjoint_left.mp (blocks_disjoint G hG hCubic hne)
  have across {x y : V} (hx : x ∈ s.val) (hy : y ∈ t.val) : x ≠ y := by
    intro he
    subst y
    exact hdis hx hy
  rcases s.property with hs | ⟨x, hclaw, hs⟩ <;>
    rcases t.property with ht | ⟨y, hclaw', ht⟩
  · have hbout : b ∉ s.val := fun h => hdis h hb
    have hdout : d ∉ s.val := fun h => hdis h hd
    have haout : a ∉ t.val := fun h => hdis ha h
    have hcout : c ∉ t.val := fun h => hdis hc h
    by_cases hac : a = c
    · subst c
      exact ⟨rfl, triangle_external_unique G hCubic hs ha hab hbout hcd hdout⟩
    have hbd : b ≠ d := by
      intro he
      subst d
      exact hac (triangle_external_unique G hCubic ht hb hab.symm haout hcd.symm hcout)
    exact False.elim (UniqueCubicClawCenter.not_four_cycle G hG hab.ne (across ha hd)
      hac hbd (Ne.symm (across hc hb)) hcd.ne.symm
      hab (ht.isClique hb hd hbd) hcd.symm (hs.isClique hc ha (Ne.symm hac)))
  · have hby : b = y := by simpa [ht] using hb
    have hdy : d = y := by simpa [ht] using hd
    subst b
    subst d
    exact ⟨claw_triangle_neighbor_unique G hCubic hclaw' hs ha hc hab.symm hcd.symm, rfl⟩
  · have hax : a = x := by simpa [hs] using ha
    have hcx : c = x := by simpa [hs] using hc
    subst a
    subst c
    exact ⟨rfl, claw_triangle_neighbor_unique G hCubic hclaw ht hb hd hab hcd⟩
  · have hax : a = x := by simpa [hs] using ha
    have hcx : c = x := by simpa [hs] using hc
    have hby : b = y := by simpa [ht] using hb
    have hdy : d = y := by simpa [ht] using hd
    exact ⟨hax.trans hcx.symm, hby.trans hdy.symm⟩

/-- Each vertex of an actual triangle has an external neighbor in a cubic graph. -/
theorem triangle_external_exists {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hCubic : ∀ x, G.degree x = 3)
    {s : Finset V} (hs : G.IsNClique 3 s) {x : V} (hx : x ∈ s) :
    ∃ y, G.Adj x y ∧ y ∉ s := by
  classical
  obtain ⟨a, b, hab, hxa, hxb, _, he⟩ := triangle_at_vertex G hs hx
  have hnot : ¬ G.neighborFinset x ⊆ {a, b} := by
    intro hsub
    have hcard := Finset.card_le_card hsub
    have htwo : ({a, b} : Finset V).card = 2 := by simp [hab]
    rw [htwo] at hcard
    change G.degree x ≤ 2 at hcard
    rw [hCubic x] at hcard
    omega
  obtain ⟨y, hy, hyab⟩ := Finset.not_subset.mp hnot
  refine ⟨y, (G.mem_neighborFinset x y).mp hy, ?_⟩
  intro hys
  rw [he] at hys
  simp only [Finset.mem_insert, Finset.mem_singleton] at hys
  rcases hys with h | h | h
  · subst y
    exact G.notMem_neighborFinset_self x hy
  · exact hyab (by simp [h])
  · exact hyab (by simp [h])

/-- Assign each original vertex its canonical block, without assuming a supplied partition. -/
noncomputable def blockOf {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hCubic : ∀ x, G.degree x = 3) (x : V) : Block G :=
  Classical.choose (exists_block G hCubic x)

/-- The canonical assignment always contains the original vertex. -/
theorem mem_blockOf {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hCubic : ∀ x, G.degree x = 3) (x : V) :
    x ∈ (blockOf G hCubic x).val := Classical.choose_spec (exists_block G hCubic x)

/-- The assignment equals a block exactly on its original vertices. -/
theorem blockOf_eq_iff {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) (hCubic : ∀ x, G.degree x = 3)
    (x : V) (s : Block G) : blockOf G hCubic x = s ↔ x ∈ s.val := by
  constructor
  · intro he
    rw [← he]
    exact mem_blockOf G hCubic x
  · intro hx
    exact blocks_eq_of_mem G hG hCubic (mem_blockOf G hCubic x) hx

/-- Every canonical block occurs as the block of an original vertex. -/
theorem blockOf_surjective {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) (hCubic : ∀ x, G.degree x = 3) :
    Function.Surjective (blockOf G hCubic) := by
  intro s
  obtain ⟨x, hx⟩ := block_nonempty G s
  exact ⟨x, (blockOf_eq_iff G hG hCubic x s).mpr hx⟩

/-- Classical decidable adjacency for the actual quotient. -/
noncomputable instance quotientDecidableRel {V : Type u} (G : SimpleGraph V) :
    DecidableRel (quotient G).Adj := Classical.decRel _

/-- The quotient has a vertex whenever the original cubic graph does. -/
theorem block_type_nonempty {V : Type u} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hCubic : ∀ x, G.degree x = 3) : Nonempty (Block G) := by
  obtain ⟨x⟩ := ‹Nonempty V›
  obtain ⟨s, _⟩ := exists_block G hCubic x
  exact ⟨s⟩

/-- At most two claw centers in a nonempty cubic graph force an actual triangle. -/
theorem exists_triangle_of_few_claws {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hCubic : ∀ x, G.degree x = 3)
    (hFew : Nat.card {x : V // UniqueCubicClawCenter.Claw G x} ≤ 2) :
    ∃ s : Finset V, G.IsNClique 3 s := by
  classical
  have hlarge : 4 ≤ Fintype.card V := by
    obtain ⟨x⟩ := ‹Nonempty V›
    have hlt := G.degree_lt_card_verts x
    rw [hCubic x] at hlt
    omega
  have hex : ∃ x : V, ¬ UniqueCubicClawCenter.Claw G x := by
    by_contra hn
    push Not at hn
    let f : V → {x : V // UniqueCubicClawCenter.Claw G x} := fun x => ⟨x, hn x⟩
    have hinj : Function.Injective f := by
      intro x y he
      exact congrArg Subtype.val he
    have hcard := Fintype.card_le_of_injective f hinj
    rw [Nat.card_eq_fintype_card] at hFew
    omega
  obtain ⟨x, hx⟩ := hex
  obtain ⟨s, hs, _⟩ := (not_claw_iff_mem_triangle G (hCubic x)).mp hx
  exact ⟨s, hs⟩

/-- The canonical quotient is strictly smaller under the original at-most-two restriction.
A triangle makes the canonical surjection noninjective, so no weighted block count is needed. -/
theorem card_block_lt {V : Type u} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) (hCubic : ∀ x, G.degree x = 3)
    (hFew : Nat.card {x : V // UniqueCubicClawCenter.Claw G x} ≤ 2) :
    Fintype.card (Block G) < Fintype.card V := by
  classical
  obtain ⟨s, hs⟩ := exists_triangle_of_few_claws G hCubic hFew
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by rw [hs.card_eq]; decide)
  let t : Block G := ⟨s, Or.inl hs⟩
  have hea : blockOf G hCubic a = t := (blockOf_eq_iff G hG hCubic a t).mpr ha
  have heb : blockOf G hCubic b = t := (blockOf_eq_iff G hG hCubic b t).mpr hb
  apply Fintype.card_lt_of_surjective_not_injective (blockOf G hCubic)
    (blockOf_surjective G hG hCubic)
  intro hinj
  exact hab (hinj (hea.trans heb.symm))

/-- The actual quotient has degree three at a triangle block. Each triangle vertex gives
one external edge, and edge uniqueness prevents two of them reaching the same block. -/
theorem quotient_degree_triangle {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) (hCubic : ∀ x, G.degree x = 3)
    (s : Block G) (hs : G.IsNClique 3 s.val) : (quotient G).degree s = 3 := by
  classical
  let port : s.val → V := fun a =>
    Classical.choose (triangle_external_exists G hCubic hs a.property)
  have hp (a : s.val) : G.Adj a.val (port a) ∧ port a ∉ s.val :=
    Classical.choose_spec (triangle_external_exists G hCubic hs a.property)
  have hne (a : s.val) : s ≠ blockOf G hCubic (port a) := by
    intro he
    exact (hp a).2 (by rw [he]; exact mem_blockOf G hCubic (port a))
  let f : s.val → (quotient G).neighborSet s := fun a =>
    ⟨blockOf G hCubic (port a), hne a, a.val, a.property, port a,
      mem_blockOf G hCubic (port a), (hp a).1⟩
  have hinj : Function.Injective f := by
    intro a c he
    have heq : blockOf G hCubic (port a) = blockOf G hCubic (port c) :=
      congrArg Subtype.val he
    have hc : port c ∈ (blockOf G hCubic (port a)).val := by
      rw [heq]
      exact mem_blockOf G hCubic (port c)
    have hends := external_edge_unique G hG hCubic (hne a) a.property
      (mem_blockOf G hCubic (port a)) c.property hc (hp a).1 (hp c).1
    exact Subtype.ext hends.1
  have hsurj : Function.Surjective f := by
    intro t
    obtain ⟨hst, a, ha, b, hb, hab⟩ := t.property
    let aa : s.val := ⟨a, ha⟩
    have hbout : b ∉ s.val := fun h =>
      Finset.disjoint_left.mp (blocks_disjoint G hG hCubic hst) h hb
    have he : port aa = b := triangle_external_unique G hCubic hs ha
      (hp aa).1 (hp aa).2 hab hbout
    refine ⟨aa, Subtype.ext ?_⟩
    change blockOf G hCubic (port aa) = t.val
    rw [he]
    exact (blockOf_eq_iff G hG hCubic b t.val).mpr hb
  calc
    (quotient G).degree s = Fintype.card ((quotient G).neighborSet s) :=
      ((quotient G).card_neighborSet_eq_degree s).symm
    _ = Fintype.card s.val := (Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm
    _ = s.val.card := Fintype.card_coe _
    _ = 3 := hs.card_eq

/-- The actual quotient has degree three at a singleton claw block. No two original
neighbors enter the same triangle block, and no quotient edge is lost. -/
theorem quotient_degree_singleton {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) (hCubic : ∀ x, G.degree x = 3)
    (s : Block G) {x : V} (hs : s.val = {x}) : (quotient G).degree s = 3 := by
  classical
  have hx : x ∈ s.val := by rw [hs]; simp
  have hne (a : G.neighborSet x) : s ≠ blockOf G hCubic a.val := by
    intro he
    have ha : a.val ∈ s.val := by rw [he]; exact mem_blockOf G hCubic a.val
    have heq : a.val = x := by simpa [hs] using ha
    exact a.property.ne heq.symm
  let f : G.neighborSet x → (quotient G).neighborSet s := fun a =>
    ⟨blockOf G hCubic a.val, hne a, x, hx, a.val,
      mem_blockOf G hCubic a.val, a.property⟩
  have hinj : Function.Injective f := by
    intro a c he
    have heq : blockOf G hCubic a.val = blockOf G hCubic c.val := congrArg Subtype.val he
    have hc : c.val ∈ (blockOf G hCubic a.val).val := by
      rw [heq]
      exact mem_blockOf G hCubic c.val
    have hends := external_edge_unique G hG hCubic (hne a) hx
      (mem_blockOf G hCubic a.val) hx hc a.property c.property
    exact Subtype.ext hends.2
  have hsurj : Function.Surjective f := by
    intro t
    obtain ⟨_, a, ha, b, hb, hab⟩ := t.property
    have heq : a = x := by simpa [hs] using ha
    subst a
    refine ⟨⟨b, hab⟩, Subtype.ext ?_⟩
    exact (blockOf_eq_iff G hG hCubic b t.val).mpr hb
  calc
    (quotient G).degree s = Fintype.card ((quotient G).neighborSet s) :=
      ((quotient G).card_neighborSet_eq_degree s).symm
    _ = Fintype.card (G.neighborSet x) :=
      (Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm
    _ = G.degree x := G.card_neighborSet_eq_degree x
    _ = 3 := hCubic x

/-- The canonical actual-block quotient of a cubic counterexample is cubic. -/
theorem quotient_cubic {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) (hCubic : ∀ x, G.degree x = 3) :
    ∀ s : Block G, (quotient G).degree s = 3 := by
  intro s
  rcases s.property with hs | ⟨x, _, hs⟩
  · exact quotient_degree_triangle G hG hCubic s hs
  · exact quotient_degree_singleton G hG hCubic s hs

/-- Same-universe smaller-order minimality supplies a dyadic cycle in the internally
constructed actual quotient. Its ordinary original-graph cycle lift is proved downstream
in `CubicFewClawCenters`. -/
theorem quotient_hasPowerOfTwoCycle {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hminimal : ∀ {W : Type u} [Fintype W] [Nonempty W]
      (Q : SimpleGraph W) [DecidableRel Q.Adj],
      Fintype.card W < Fintype.card V → (∀ x, 3 ≤ Q.degree x) → HasPowerOfTwoCycle Q)
    (hCubic : ∀ x, G.degree x = 3)
    (hFew : Nat.card {x : V // UniqueCubicClawCenter.Claw G x} ≤ 2) :
    HasPowerOfTwoCycle (quotient G) := by
  letI : Nonempty (Block G) := block_type_nonempty G hCubic
  apply hminimal (quotient G) (card_block_lt G hG hCubic hFew)
  intro s
  rw [quotient_cubic G hG hCubic s]

example : (∀ x : Fin 4, (⊤ : SimpleGraph (Fin 4)).degree x = 3) ∧
    Nat.card {x : Fin 4 // UniqueCubicClawCenter.Claw (⊤ : SimpleGraph (Fin 4)) x} ≤ 2 := by
  classical
  constructor
  · decide
  · have hn : ∀ x : Fin 4, ¬ UniqueCubicClawCenter.Claw (⊤ : SimpleGraph (Fin 4)) x := by
      intro x hc
      obtain ⟨a, b, c, hab, _, _, _, _, _, hnab, _, _⟩ := hc
      exact hnab hab
    have he : IsEmpty {x : Fin 4 // UniqueCubicClawCenter.Claw (⊤ : SimpleGraph (Fin 4)) x} :=
      ⟨fun x => hn x.val x.property⟩
    rw [Nat.card_eq_zero.mpr (Or.inl he)]
    decide

end Erdos64.CubicFewClawCenters
