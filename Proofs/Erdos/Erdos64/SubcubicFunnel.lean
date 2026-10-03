import Erdos.Erdos64.SubcubicFunnelUnique
import Erdos.Erdos64.SubcubicFunnelFixtures

set_option autoImplicit false

namespace Erdos64.SubcubicFunnel
open SimpleGraph
universe u
variable {V : Type u} {G : SimpleGraph V} {s t : V}

/-- The nonempty tuple family either has a common endpoint-neighbor vertex or
contains an aligned induced H7. Zero-clean paths use matching-coordinate Helly;
otherwise paths avoiding the two labels of a clean path supply the H7 witness. -/
theorem tuple_dichotomy [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) (h4 : ¬ HasSimpleCycleOfLength G 4)
    (h8 : ¬ HasSimpleCycleOfLength G 8) (hsep : 2 < G.edist s t)
    (hne : Nonempty (Path4 G s t)) :
    (∃ z, (G.Adj s z ∨ G.Adj t z) ∧ ∀ p : Path4 G s t, p.Internal z) ∨
      AlignedH7 G s t := by
  classical
  by_cases hclean : ∃ p : Path4 G s t, p.Clean
  · obtain ⟨p, hp⟩ := hclean
    by_cases hf : ∀ q : Path4 G s t, q.Internal p.first
    · exact Or.inl ⟨p.first, Or.inl p.edge₀, hf⟩
    by_cases hl : ∀ q : Path4 G s t, q.Internal p.last
    · exact Or.inl ⟨p.last, Or.inr p.edge₃.symm, hl⟩
    push Not at hf hl
    obtain ⟨r, hr⟩ := hf
    obtain ⟨l, hll⟩ := hl
    exact Or.inr (alignedH7_of_clean_avoiding hdeg h4 h8 hsep p l r hp hll hr)
  · obtain ⟨p⟩ := hne
    have hnclean : ∀ q : Path4 G s t, ¬ q.Clean := by
      intro q hc
      exact hclean ⟨q, hc⟩
    exact Or.inl (zero_clean_funnel hdeg h4 h8 hsep hnclean p)

/-- The finite subcubic funnel/induced-H7 dichotomy for the full family of
Mathlib simple four-edge walks. The distance is Mathlib's standard extended
shortest-path distance; nonemptiness of the family guarantees it is finite.
The funnel vertex is selectable in the union of the two endpoint neighborhoods. -/
theorem walk_dichotomy [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) (h4 : ¬ HasSimpleCycleOfLength G 4)
    (h8 : ¬ HasSimpleCycleOfLength G 8) (_hst : s ≠ t)
    (hsep : 2 < G.edist s t)
    (hne : ∃ w : G.Walk s t, w.IsPath ∧ w.length = 4) :
    (∃ z, (G.Adj s z ∨ G.Adj t z) ∧
      ∀ w : G.Walk s t, w.IsPath → w.length = 4 →
        z ∈ w.support ∧ z ≠ s ∧ z ≠ t) ∨ AlignedH7 G s t := by
  rcases tuple_dichotomy hdeg h4 h8 hsep (nonempty_path4_iff.mpr hne) with hf | hh
  · obtain ⟨z, hz, hall⟩ := hf
    exact Or.inl ⟨z, hz, (common_internal_iff z).mp hall⟩
  · exact Or.inr hh

/-- Under exactly the finite subcubic, C4/C8-free, separated-endpoint and
nonempty-family hypotheses, failure of a common internal vertex in all standard
simple four-edge walks is equivalent to an aligned induced H7. The backward
implication uses only the three explicit H7 paths and no structural hypotheses. -/
theorem no_common_walk_internal_iff_alignedH7 [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) (h4 : ¬ HasSimpleCycleOfLength G 4)
    (h8 : ¬ HasSimpleCycleOfLength G 8) (hst : s ≠ t)
    (hsep : 2 < G.edist s t)
    (hne : ∃ w : G.Walk s t, w.IsPath ∧ w.length = 4) :
    (¬ ∃ z, ∀ w : G.Walk s t, w.IsPath → w.length = 4 →
      z ∈ w.support ∧ z ≠ s ∧ z ≠ t) ↔ AlignedH7 G s t := by
  constructor
  · intro hn
    rcases walk_dichotomy hdeg h4 h8 hst hsep hne with hf | hh
    · obtain ⟨z, _, hall⟩ := hf
      exact False.elim (hn ⟨z, hall⟩)
    · exact hh
  · exact AlignedH7.no_common_walk_internal

/-- The two standard-walk alternatives are mutually exclusive, including the
unrestricted common-internal-vertex formulation. -/
theorem walk_alternatives_exclusive :
    ¬ ((∃ z, ∀ w : G.Walk s t, w.IsPath → w.length = 4 →
      z ∈ w.support ∧ z ≠ s ∧ z ≠ t) ∧ AlignedH7 G s t) := by
  rintro ⟨hf, hh⟩
  exact hh.no_common_walk_internal hf

/-- Every common internal vertex can be replaced by an endpoint-neighbor common
internal vertex under the structural hypotheses. Thus the funnel alternative
has the required endpoint-neighbor strengthening, not merely an arbitrary center. -/
theorem endpoint_neighbor_funnel_of_common [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) (h4 : ¬ HasSimpleCycleOfLength G 4)
    (h8 : ¬ HasSimpleCycleOfLength G 8) (hst : s ≠ t)
    (hsep : 2 < G.edist s t)
    (hne : ∃ w : G.Walk s t, w.IsPath ∧ w.length = 4)
    (hc : ∃ z, ∀ w : G.Walk s t, w.IsPath → w.length = 4 →
      z ∈ w.support ∧ z ≠ s ∧ z ≠ t) :
    ∃ z, (G.Adj s z ∨ G.Adj t z) ∧
      ∀ w : G.Walk s t, w.IsPath → w.length = 4 →
        z ∈ w.support ∧ z ≠ s ∧ z ≠ t := by
  rcases walk_dichotomy hdeg h4 h8 hst hsep hne with hf | hh
  · exact hf
  · exact False.elim (hh.no_common_walk_internal hc)

/-- Nonemptiness of the standard four-edge path family guarantees finite
standard distance, bounded above by four. Thus the main theorem's extended
separation hypothesis never uses the disconnected-distance junk case. -/
theorem edist_le_four_of_path_family
    (hne : ∃ w : G.Walk s t, w.IsPath ∧ w.length = 4) :
    G.edist s t ≤ 4 ∧ G.edist s t < ⊤ := by
  obtain ⟨w, _, hw⟩ := hne
  have hle : G.edist s t ≤ 4 := by simpa [hw] using G.edist_le w
  exact ⟨hle, lt_of_le_of_lt hle (by decide)⟩

/-- With a nonempty standard four-edge path family, extended distance greater
than two is equivalent to natural shortest-path distance at least three. The
reachability witness prevents Mathlib's totalized natural distance from using
its disconnected value. -/
theorem separation_iff_dist_of_path_family
    (hne : ∃ w : G.Walk s t, w.IsPath ∧ w.length = 4) :
    2 < G.edist s t ↔ 3 ≤ G.dist s t := by
  obtain ⟨w, _, _⟩ := hne
  have hreach : G.Reachable s t := ⟨w⟩
  rw [← hreach.coe_dist_eq_edist]
  norm_cast

/-- The reviewed finite subcubic funnel/induced-H7 dichotomy, stated with
Mathlib's natural shortest-path distance at least three and the full family of
standard simple four-edge walks. Nonemptiness supplies reachability, so distance
is finite and is not the disconnected default. -/
theorem dist_walk_dichotomy [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) (h4 : ¬ HasSimpleCycleOfLength G 4)
    (h8 : ¬ HasSimpleCycleOfLength G 8) (hst : s ≠ t)
    (hdist : 3 ≤ G.dist s t)
    (hne : ∃ w : G.Walk s t, w.IsPath ∧ w.length = 4) :
    (∃ z, (G.Adj s z ∨ G.Adj t z) ∧
      ∀ w : G.Walk s t, w.IsPath → w.length = 4 →
        z ∈ w.support ∧ z ≠ s ∧ z ≠ t) ∨ AlignedH7 G s t := by
  exact walk_dichotomy hdeg h4 h8 hst
    ((separation_iff_dist_of_path_family hne).mpr hdist) hne

/-- For distinct endpoints at finite natural distance at least three in a
finite subcubic C4/C8-free graph, a nonempty full simple four-edge path family
has no common internal vertex exactly when an aligned induced H7 exists. -/
theorem dist_no_common_walk_internal_iff_alignedH7 [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) (h4 : ¬ HasSimpleCycleOfLength G 4)
    (h8 : ¬ HasSimpleCycleOfLength G 8) (hst : s ≠ t)
    (hdist : 3 ≤ G.dist s t)
    (hne : ∃ w : G.Walk s t, w.IsPath ∧ w.length = 4) :
    (¬ ∃ z, ∀ w : G.Walk s t, w.IsPath → w.length = 4 →
      z ∈ w.support ∧ z ≠ s ∧ z ≠ t) ↔ AlignedH7 G s t := by
  exact no_common_walk_internal_iff_alignedH7 hdeg h4 h8 hst
    ((separation_iff_dist_of_path_family hne).mpr hdist) hne

example : AlignedH7 h7 0 1 := by
  obtain ⟨hdeg, h4, h8, hst, hsep, hne, _, hn⟩ := h7_fixture
  have hdist := (separation_iff_dist_of_path_family hne).mp hsep
  exact (dist_no_common_walk_internal_iff_alignedH7 hdeg h4 h8 hst hdist hne).mp hn

example : ¬ AlignedH7 funnel5 0 1 := by
  obtain ⟨_, _, _, _, _, _, _, hall⟩ := funnel5_fixture
  intro hh
  exact hh.no_common_walk_internal ⟨2, hall⟩

end Erdos64.SubcubicFunnel
