/-
# Foundations for the reviewed subcubic four-path funnel / induced-H7 dichotomy

This is a locally derived, independently reviewed graph-structural result, not
an assertion of the Erdős–Gyárfás conjecture or of gadget coverage. The aligned
seven-vertex graph is the H7 associated with arXiv:2609.04686; the local
dichotomy is not attributed to that source. Cycles below are genuine Mathlib
walk cycles, not induced cycles.
-/
import Erdos.Erdos64.Incidence
import Mathlib.Combinatorics.SimpleGraph.Metric

set_option autoImplicit false

namespace Erdos64.SubcubicFunnel

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V} {s t : V}

/-- A simple four-edge path, recorded by its three internal vertices.
The nodup condition includes both endpoints. -/
structure Path4 (G : SimpleGraph V) (s t : V) where
  first : V
  middle : V
  last : V
  edge₀ : G.Adj s first
  edge₁ : G.Adj first middle
  edge₂ : G.Adj middle last
  edge₃ : G.Adj last t
  distinct : [s, first, middle, last, t].Nodup

/-- The standard walk represented by a four-path tuple. -/
def Path4.walk (p : Path4 G s t) : G.Walk s t :=
  .cons p.edge₀ (.cons p.edge₁ (.cons p.edge₂ (.cons p.edge₃ .nil)))

/-- The tuple walk has exactly four edges. -/
@[simp] theorem Path4.walk_length (p : Path4 G s t) : p.walk.length = 4 := rfl

/-- Tuple distinctness is exactly standard simple-path distinctness. -/
theorem Path4.walk_isPath (p : Path4 G s t) : p.walk.IsPath := by
  have hd := p.distinct
  simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true] at hd
  simp only [Path4.walk, Walk.cons_isPath_iff, Walk.support_cons, Walk.support_nil,
    List.mem_cons, not_or]
  exact ⟨⟨⟨⟨Walk.IsPath.nil, by simp [hd]⟩, by simp [hd]⟩,
    by simp [hd]⟩, by simp [hd]⟩

/-- A vertex is internal to the tuple when it is one of the three internal vertices. -/
def Path4.Internal (p : Path4 G s t) (z : V) : Prop :=
  z = p.first ∨ z = p.middle ∨ z = p.last

/-- Tuple-internal membership agrees with walk support minus the two endpoints. -/
theorem Path4.internal_iff (p : Path4 G s t) (z : V) :
    p.Internal z ↔ z ∈ p.walk.support ∧ z ≠ s ∧ z ≠ t := by
  have hd := p.distinct
  simp only [List.nodup_cons, List.mem_cons, not_or,
    List.nodup_nil, and_true] at hd
  simp only [Path4.Internal, Path4.walk, Walk.support_cons, Walk.support_nil,
    List.mem_cons]
  grind

/-- Every standard simple four-edge walk admits an exact tuple representation. -/
theorem path4_of_walk (w : G.Walk s t) (hw : w.IsPath) (hlen : w.length = 4) :
    ∃ p : Path4 G s t, p.walk = w := by
  cases w with
  | nil => simp at hlen
  | cons e₀ w =>
    cases w with
    | nil => simp at hlen
    | cons e₁ w =>
      cases w with
      | nil => simp at hlen
      | cons e₂ w =>
        cases w with
        | nil => simp at hlen
        | cons e₃ w =>
          cases w with
          | nil =>
            exact ⟨⟨_, _, _, e₀, e₁, e₂, e₃, hw.support_nodup⟩, rfl⟩
          | cons e₄ w => simp only [Walk.length_cons] at hlen; omega

/-- Nonempty tuple families and nonempty standard four-edge path families coincide. -/
theorem nonempty_path4_iff :
    Nonempty (Path4 G s t) ↔ ∃ w : G.Walk s t, w.IsPath ∧ w.length = 4 := by
  constructor
  · rintro ⟨p⟩
    exact ⟨p.walk, p.walk_isPath, p.walk_length⟩
  · rintro ⟨w, hw, hlen⟩
    obtain ⟨p, _⟩ := path4_of_walk w hw hlen
    exact ⟨p⟩

/-- A common internal vertex for all four-tuples is exactly one for all standard
simple four-edge walks. -/
theorem common_internal_iff (z : V) :
    (∀ p : Path4 G s t, p.Internal z) ↔
      ∀ w : G.Walk s t, w.IsPath → w.length = 4 →
        z ∈ w.support ∧ z ≠ s ∧ z ≠ t := by
  constructor
  · intro h w hw hlen
    obtain ⟨p, rfl⟩ := path4_of_walk w hw hlen
    exact (p.internal_iff z).mp (h p)
  · intro h p
    exact (p.internal_iff z).mpr (h p.walk p.walk_isPath p.walk_length)

/-- With no simple C4, two distinct vertices have at most one common neighbor. -/
theorem common_neighbor_unique (h4 : ¬ HasSimpleCycleOfLength G 4)
    {x y a b : V} (hxy : x ≠ y)
    (hxa : G.Adj x a) (hya : G.Adj y a)
    (hxb : G.Adj x b) (hyb : G.Adj y b) : a = b := by
  by_contra hab
  let p : G.Walk x y := .cons hxa (.cons hya.symm .nil)
  let q : G.Walk y x := .cons hyb (.cons hxb.symm .nil)
  have hp : p.IsPath := by simp [p, hxy, hxa.ne, hya.ne.symm]
  have hq : q.IsPath := by simp [q, hxy.symm, hyb.ne, hxb.ne.symm]
  have hd : p.support.tail.Disjoint q.support.tail := by
    simp [p, q, List.disjoint_left, hab, hxa.ne.symm, hxy.symm, hyb.ne]
  exact h4 ⟨x, p.append q, hp.isCycle_append hq hd (Or.inl (by simp [p])), by
    simp [p, q]⟩

/-- In the absence of C8, any two simple four-edge paths intersect internally. -/
theorem Path4.internal_intersects (h8 : ¬ HasSimpleCycleOfLength G 8)
    (p q : Path4 G s t) : ∃ z, p.Internal z ∧ q.Internal z := by
  by_contra h
  have hd : p.walk.support.tail.Disjoint q.walk.reverse.support.tail := by
    have hp := p.distinct
    have hq := q.distinct
    simp only [List.nodup_cons, List.mem_cons, not_or,
      List.nodup_nil, and_true] at hp hq
    simp only [List.disjoint_left, Path4.walk, Walk.reverse_cons,
      Walk.reverse_nil, Walk.support_append, Walk.support_cons, Walk.support_nil,
      List.tail_cons, List.mem_cons]
    simp only [Path4.Internal, not_exists, not_and] at h
    grind
  have hc := p.walk_isPath.isCycle_append q.walk_isPath.reverse hd
    (Or.inl (by simp))
  exact h8 ⟨s, p.walk.append q.walk.reverse, hc, by simp [Walk.length_append]⟩

/-- The absence of two distinct common neighbors excludes every genuine C4. -/
theorem not_cycle_four_of_common_neighbor_unique
    (h : ∀ x y a b : V, x ≠ y → G.Adj x a → G.Adj y a →
      G.Adj x b → G.Adj y b → a = b) : ¬ HasSimpleCycleOfLength G 4 := by
  rintro ⟨x, w, hw, hlen⟩
  cases w with
  | nil => simp at hlen
  | cons e₀ w =>
    cases w with
    | nil => simp at hlen
    | cons e₁ w =>
      cases w with
      | nil => simp at hlen
      | cons e₂ w =>
        cases w with
        | nil => simp at hlen
        | cons e₃ w =>
          cases w with
          | cons e₄ w => simp only [Walk.length_cons] at hlen; omega
          | nil =>
            have hd := hw.support_nodup
            simp only [Walk.support_cons, Walk.support_nil, List.tail_cons,
              List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true] at hd
            have he := h _ _ _ _ (by grind) e₀ e₁.symm e₃.symm e₂
            grind

/-- A genuine simple cycle uses at least its length in distinct vertices. -/
theorem cycle_length_le_card [Fintype V] {v : V} {w : G.Walk v v}
    (hw : w.IsCycle) : w.length ≤ Fintype.card V := by
  have hn := hw.support_nodup.length_le_card
  have hl := w.length_support
  rw [List.length_tail] at hn
  omega

end Erdos64.SubcubicFunnel
