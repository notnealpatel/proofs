/-
Erdős–Gyárfás problem 64 — assembly of cycles from low attachments.

This module preserves attachment geometry which is not present in scalar
DyadicKernel weights.  A certificate consists of a positive path in the
canonical `doublingGraph`, a degree-three path in the original graph, the two
attachment edges, and separation of the entire low support from the entire
lifted support.  The lifted path is joined to the reverse of the attached low
path, in the orientation

  x -- lift(m) --> y -- b -- reverse(p) --> a -- x.

This is only an assembly lemma.  It does not prove that low attachments exist,
that their path has a prescribed length, that the assembled length is dyadic,
or the Erdős 64 conjecture.  In particular, none of the certificate fields is
claimed to follow automatically from the graph hypotheses.
-/

import Erdos.Erdos64.Doubling

set_option autoImplicit false

namespace Erdos64

open SimpleGraph

universe u

variable {V : Type u}

/-- Data sufficient to attach a low degree-three path to a positive path in the
canonical doubled graph.  Separation covers the low endpoints and every high
or witness vertex in the lifted doubled path. -/
structure LowAttachmentCertificate (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (r k : ℕ) (x y : ↥(degreeGeFourFinset G)) (a b : V) where
  m : (doublingGraph G).Walk x y
  m_isPath : m.IsPath
  m_length : m.length = k
  k_pos : 1 ≤ k
  p : G.Walk a b
  p_isPath : p.IsPath
  p_length : p.length = r
  left_attach : G.Adj (x : V) a
  right_attach : G.Adj b (y : V)
  low : ∀ z ∈ p.support, degreeThree G z
  separated : p.support.Disjoint (liftDoublingWalk m).support

namespace LowAttachmentCertificate

variable {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {r k : ℕ} {x y : ↥(degreeGeFourFinset G)} {a b : V}

private noncomputable def attachmentPath (C : LowAttachmentCertificate G r k x y a b) :
    G.Walk (x : V) (y : V) :=
  (Walk.cons C.left_attach C.p).concat C.right_attach

/-- The canonical closed attachment walk, oriented as the lifted doubled path
from `x` to `y`, the edge from `y` to `b`, the reverse low path to `a`, and the
edge from `a` to `x`. -/
noncomputable def closedWalk (C : LowAttachmentCertificate G r k x y a b) :
    G.Walk (x : V) (x : V) :=
  (liftDoublingWalk C.m).append C.attachmentPath.reverse

private lemma endpoints_ne (C : LowAttachmentCertificate G r k x y a b) : x ≠ y := by
  intro hxy
  have hnil : C.m.Nil := C.m_isPath.nil_iff_eq.mpr hxy
  have hzero : C.m.length = 0 := Walk.length_eq_zero_iff.mpr hnil
  rw [C.m_length] at hzero
  have hk := C.k_pos
  omega

private lemma endpoint_values_ne (C : LowAttachmentCertificate G r k x y a b) :
    (x : V) ≠ (y : V) := by
  intro hxy
  exact C.endpoints_ne (Subtype.ext hxy)

private lemma left_not_mem_low_support (C : LowAttachmentCertificate G r k x y a b) :
    (x : V) ∉ C.p.support := by
  intro hx
  exact C.separated hx (liftDoublingWalk C.m).start_mem_support

private lemma right_not_mem_low_support (C : LowAttachmentCertificate G r k x y a b) :
    (y : V) ∉ C.p.support := by
  intro hy
  exact C.separated hy (liftDoublingWalk C.m).end_mem_support

private lemma attachmentPath_isPath (C : LowAttachmentCertificate G r k x y a b) :
    C.attachmentPath.IsPath := by
  have hleft : (Walk.cons C.left_attach C.p).IsPath :=
    (Walk.cons_isPath_iff _ _).mpr ⟨C.p_isPath, C.left_not_mem_low_support⟩
  apply hleft.concat
  simp only [Walk.support_cons, List.mem_cons, not_or]
  exact ⟨C.endpoint_values_ne.symm, C.right_not_mem_low_support⟩

private lemma support_tail_disjoint (C : LowAttachmentCertificate G r k x y a b)
    (hG : ¬ HasPowerOfTwoCycle G) :
    (liftDoublingWalk C.m).support.tail.Disjoint C.attachmentPath.reverse.support.tail := by
  rw [List.disjoint_left]
  intro z hzq hzl
  have hzq' : z ∈ (liftDoublingWalk C.m).support := List.mem_of_mem_tail hzq
  have hsupport : C.attachmentPath.reverse.support.tail = C.p.support.reverse ++ [(x : V)] := by
    simp [attachmentPath, Walk.support_append]
  rw [hsupport] at hzl
  simp only [List.mem_append, List.mem_reverse, List.mem_singleton] at hzl
  rcases hzl with hz | hz
  · exact C.separated hz hzq'
  · subst z
    have hnodup := (isPath_liftDoublingWalk hG C.m C.m_isPath).support_nodup
    rw [← (liftDoublingWalk C.m).cons_tail_support, List.nodup_cons] at hnodup
    exact hnodup.1 hzq

/-- The canonical closed attachment walk has length `r + 2 * k + 2`.
This theorem also provides the ground-truth check for `closedWalk`: lifting
contributes `2 * k`, reversing preserves length, and the attachments contribute
two edges. -/
theorem closedWalk_length (C : LowAttachmentCertificate G r k x y a b) :
    C.closedWalk.length = r + 2 * k + 2 := by
  simp only [closedWalk, Walk.length_append, Walk.length_reverse, attachmentPath,
    Walk.length_concat, Walk.length_cons, length_liftDoublingWalk, C.m_length, C.p_length]
  omega

/-- In a graph with no power-of-two cycle, the canonical closed attachment walk
is a genuine simple cycle.  The no-power-of-two hypothesis is used by
`isPath_liftDoublingWalk` to make the canonical witness lift a simple path. -/
theorem closedWalk_isCycle (C : LowAttachmentCertificate G r k x y a b)
    (hG : ¬ HasPowerOfTwoCycle G) : C.closedWalk.IsCycle := by
  apply (isPath_liftDoublingWalk hG C.m C.m_isPath).isCycle_append
    C.attachmentPath_isPath.reverse (C.support_tail_disjoint hG)
  left
  have hmpos : 1 ≤ C.m.length := by
    rw [C.m_length]
    exact C.k_pos
  rw [length_liftDoublingWalk]
  omega

/-- A low-attachment certificate in a graph without power-of-two cycles
exhibits a simple closed cycle of exactly the assembled length. -/
theorem exists_isCycle (C : LowAttachmentCertificate G r k x y a b)
    (hG : ¬ HasPowerOfTwoCycle G) :
    ∃ c : G.Walk (x : V) (x : V), c.IsCycle ∧ c.length = r + 2 * k + 2 :=
  ⟨C.closedWalk, C.closedWalk_isCycle hG, C.closedWalk_length⟩

/-- If the assembled attachment length is `2 ^ j` for `2 ≤ j`, then the graph
has a power-of-two cycle.  No prior absence assumption is needed: if absence is
assumed, `closedWalk_isCycle` constructs the contradictory witness. -/
theorem hasPowerOfTwoCycle (C : LowAttachmentCertificate G r k x y a b) {j : ℕ}
    (hj : 2 ≤ j) (hlen : r + 2 * k + 2 = 2 ^ j) : HasPowerOfTwoCycle G := by
  by_cases hG : HasPowerOfTwoCycle G
  · exact hG
  · refine ⟨j, hj, (x : V), C.closedWalk, C.closedWalk_isCycle hG, ?_⟩
    exact C.closedWalk_length.trans hlen

/-- Contradiction form: a dyadic assembled attachment length is impossible in a
graph with no power-of-two cycle. -/
theorem false_of_length_eq_pow (C : LowAttachmentCertificate G r k x y a b)
    (hG : ¬ HasPowerOfTwoCycle G) {j : ℕ} (hj : 2 ≤ j)
    (hlen : r + 2 * k + 2 = 2 ^ j) : False :=
  hG (C.hasPowerOfTwoCycle hj hlen)

end LowAttachmentCertificate

/-! The next two small boundary lemmas explain why positivity and full support
separation are part of the certificate rather than consequences of assembly. -/

variable {G : SimpleGraph V}

/-- A nil doubled path and nil low path with coincident attachment edges give a
length-two backtrack, not a cycle.  This is the boundary behavior excluded by
`LowAttachmentCertificate.k_pos`. -/
theorem two_edge_backtrack_length_and_not_isCycle {x a : V} (h : G.Adj x a) :
    (Walk.cons h (Walk.cons h.symm Walk.nil)).length = 2 ∧
      ¬(Walk.cons h (Walk.cons h.symm Walk.nil)).IsCycle := by
  constructor
  · simp
  · intro hc
    have hthree := hc.three_le_length
    simp at hthree

/-- If two assembled paths share an internal vertex `c`, their closed
concatenation repeats `c` and is not a cycle.  This models an endpoint or
internal collision with a lifted witness and motivates separation of the full
supports, rather than only the low path's internal vertices. -/
theorem endpoint_collision_not_isCycle {x c y a : V} (hxc : G.Adj x c)
    (hcy : G.Adj c y) (hyc : G.Adj y c) (hca : G.Adj c a) (hax : G.Adj a x) :
    ¬((Walk.cons hxc (Walk.cons hcy Walk.nil)).append
      (Walk.cons hyc (Walk.cons hca (Walk.cons hax Walk.nil)))).IsCycle := by
  intro hc
  have hn := (Walk.isCycle_def _).mp hc |>.2.2
  simp at hn

/-- The length-two boundary configuration is inhabited: it occurs on the
complete simple graph on two Boolean vertices. -/
example : ∃ (G : SimpleGraph Bool) (x a : Bool) (h : G.Adj x a),
    (Walk.cons h (Walk.cons h.symm Walk.nil)).length = 2 ∧
      ¬(Walk.cons h (Walk.cons h.symm Walk.nil)).IsCycle := by
  let G : SimpleGraph Bool := ⊤
  have h : G.Adj false true := by simp [G]
  exact ⟨G, false, true, h, two_edge_backtrack_length_and_not_isCycle h⟩

end Erdos64
