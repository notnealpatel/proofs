/-
Erdős–Gyárfás problem 64 — the released one-state attempted candidate schedule.

PROVENANCE.  arXiv:2608.02675, Julius Tranquilli, "A 60-Vertex Lower Bound for Cubic Bipartite
Counterexamples to the Erdős–Gyárfás Conjecture" (2 August 2026), Section 3.2 (the triangle-rooted
reduced search).  The released artifact of the paper (`research/certificates/TRIANGLE_FORMAT.md`,
the `EG58TRI1` triangle-rooted certificate format, and its streaming checker
`research/src/verify_triangle_universal_certificate.cpp`) drives a deterministic restricted-growth
traversal over the `29` candidate points of a triangle-rooted linear `3`-uniform configuration.
The released `visit` member function of the checker performs, *for one search state*, the following
work before it does anything else:

* it advances a *point cursor* from a starting label by an ascending `while` loop that stops at the
  first label `p` with `p < introduced` and `degree(p) != 3` — the first not-yet-full introduced
  point at or after the start;
* it maintains a *candidate cursor*, a pair `(q₀, r₀)` of previously attempted labels (the
  released checker encodes the absent cursor as `(-1, -1)`), and it resets that cursor to the
  absent value whenever the point advance skipped at least one full point;
* it enumerates the candidate pool of the selected point `p`: the ascending old labels `q > p`
  below `introduced` that are not full and not already paired with `p`, followed by the two fresh
  labels `introduced` and `introduced + 1` when those are still inside the `29`-point range;
* it walks that pool with the nested loops `for i`, `for j = i + 1`, discards a pair `(q, r)` when
  the *fresh guard* forbids it (the pair `(q, introduced + 1)` is admissible only when `q` is
  itself the fresh label `introduced`), discards a pair not strictly after the candidate cursor in
  the lexicographic order, and turns each surviving pair into the ordered block `{p, q, r}`;
* it *counts* each such block as an attempted candidate.  The structural rejection test
  `structurally_invalid` and the `C₈`/`C₁₆` cycle oracles run only afterwards, on the candidate
  just built.

This module formalizes exactly that one-state attempted candidate schedule.  It is the
*generation* side of the traversal that `Erdos.Erdos64.TriangleTraversalKernel` leaves as an
untrusted input: that module consumes a state `s` and a candidate `t` and proves the structural
rejection test and the combined expansion step sound, and it explicitly does not formalize the
pool of candidates, the point selection, the cursor schedule or the candidate order.

WHAT IS FORMALIZED HERE.  The released `visit`'s one-state schedule, as pure data.

* `SearchCursor = Option (SearchPoint × SearchPoint)` — the released candidate cursor, with `none`
  standing for the released `(-1, -1)` sentinel.  It is an `Option`, not a pair of `Int`s, so that
  "no cursor" is not confused with a real label and no signed arithmetic is used anywhere;
* `VisitSchedule` — the one-state schedule record the released `visit` computes before recursing:
  the selected point (or `none`), the cursor it leaves behind, and the list of attempted candidate
  blocks in the released nested-loop order;
* `toSearchPoint` and `freshLabels` — the non-wrapping label decoder.  `toSearchPoint n` is
  `some ⟨n, _⟩` exactly when `n < 29`, so the fresh labels of a counter value `u` are exactly
  `u` and `u + 1` when those are still points, and are dropped (not wrapped, not truncated to
  `28`) when they are not.  `freshLabels` at the boundary counts `0`, `28` and `29` is
  `decide`d, which pins the "no `Fin` wrapping" requirement;
* `possibleLabels s p` — *exactly* the released pool of the selected point `p`: the ascending old
  labels `q` with `p < q`, `q.val < introduced`, `pointDegree s q < 3` and `¬ pairUsed s p q`,
  followed by `freshLabels s.introduced`.  `possibleLabels_mem_iff` characterises membership by
  the three disjuncts "old label", "fresh label `introduced`", "fresh label `introduced + 1`",
  and `possibleLabels_pairwise` / `possibleLabels_nodup` prove that the pool is strictly increasing
  with no repeated label, so the nested-loop order is a genuine strict order;
* `advanceFrom` / `advancePoint s start` — the released ascending `while` loop, as a bounded
  search over the offsets `0, 1, …` from `start`.  `advancePoint` returns the first label `p`
  with `p.val < introduced` and `pointDegree s p ≠ 3`, or `none`.  `advancePoint_spec` records the
  bounds of the result, `advancePoint_least` records that it is the *first* such label, and under
  the cubic degree bound `advancePoint_degree_lt` and `advancePoint_skipped` record that the
  selected label has degree `< 3` while every introduced label from `start` to the selected one
  that was skipped has degree *exactly* `3`;
* `orderedPairs xs` — the generic nested loop: for the list `xs = [x₀, x₁, …]` it is
  `[(x₀,x₁), (x₀,x₂), …, (x₁,x₂), …]`, i.e. exactly the order of `for i`, `for j = i + 1`.
  `mem_orderedPairs_iff` characterises membership by the exact suffix decomposition
  `∃ l₁ l₂ l₃, xs = l₁ ++ q :: l₂ ++ r :: l₃` (`OccursBefore`), and `occursBefore_lt` turns
  strict increase of `xs` into `q < r`;
* `freshGuard u q r` — the released fresh-label guard: the pair `(q, r)` is inadmissible when
  `r` is the second fresh label `u + 1` and `q` is not the first fresh label `u`;
* `afterCursor cursor q r` — the released strict lexicographic cursor guard, with `none` accepting
  every pair;
* `mkCandidate? p q r` — the total ordered-block constructor: `some ⟨p, q, r, _, _⟩` when
  `p < q < r` and `none` otherwise, so the schedule never fabricates a malformed block;
* `effectiveCursor s start cursor` — the cursor the schedule leaves behind: the input cursor when
  the point advance selected `start` itself, and `none` otherwise.  `candidateSchedule_cursor`
  proves the exact value, `candidateSchedule_cursor_preserved` and
  `candidateSchedule_cursor_reset` record the two cases, and
  `candidateSchedule_cursor_reset_of_skipped` records that *one or more skipped degree-`3` points*
  reset the cursor to `none`;
* `candidateSchedule s start cursor` — the one-state schedule.  `candidateSchedule_point` and
  `candidateSchedule_cursor` identify the point and cursor components,
  `candidateSchedule_none` records that a `none` point forces a `none` cursor and an empty
  candidate list, and `candidateSchedule_mem_iff` is the main characterisation: a block is
  attempted exactly when there are points `p, q, r` with `advancePoint s start = some p`, `q`
  before `r` in the pool of `p` (the nested-loop order), the fresh guard and the effective cursor
  guard both pass, and the block's components are `p, q, r`;
* `discipline_of_possible` and `candidateSchedule_discipline` — every attempted candidate is
  *disciplined* in the sense of `CandidateDiscipline s.introduced`: all its labels are at most
  `introduced + 1`, and a candidate using the second fresh label `introduced + 1` also uses the
  first fresh label `introduced`.  The stronger triple-level lemma is factored out and consumes
  only membership in the pool, the fresh guard and `p.val < introduced`;
* fixtures.  `orbitOneState` (the artifact's triangle-root orbit 1, reused from
  `Erdos.Erdos64.TriangleTraversalKernel`) drives three kernel-`decide`d schedules: with
  `start = 1` and cursor `(2,4)` the pool is `[5,6,7,8]` and the shapes are exactly
  `(1,5,6), (1,5,7), (1,6,7), (1,7,8)`; with the same start and cursor `(5,6)` the schedule is the
  exact suffix `(1,5,7), (1,6,7), (1,7,8)`; with `start = 3` and the absent cursor the pool is
  `[4,5,6,7,8]` and the shapes are exactly
  `(3,4,5), (3,4,6), (3,4,7), (3,5,6), (3,5,7), (3,6,7), (3,7,8)`.  The block `{3,4,6}` is
  attempted by the third schedule even though `cppStructurallyInvalid orbitOneState 7 {3,4,6}` is
  `true` — it reuses the old pair `{4,6}` of the installed block `{0,4,6}` — which is the concrete
  witness that the structural test is a *later*, separate step.  The `freshLabels` boundary
  fixtures at counts `0`, `28` and `29` are also `decide`d.

WHY `SearchBlock.shape`.  `SearchBlock` carries the two inequality proofs `a < b` and `b < c` as
fields, so its `DecidableEq` is entangled with proof terms.  The fixtures therefore compare
`SearchBlock.shape t = (t.a, t.b, t.c)`, and `SearchBlock.shape_injective` proves that the shape
determines the block — so shape equality is an honest proxy for block equality, and
`mkCandidate?_eq_some_iff` states the constructor's behaviour in those terms.

ATTEMPTED, NOT ACCEPTED.  The released `visit` increments its *attempted* candidate counter for
every block this schedule produces, *before* it asks `structurally_invalid` and before it runs the
`C₈`/`C₁₆` oracles.  This module therefore deliberately does **not** filter the schedule by
`cppStructurallyInvalid` or by `CleanStructuralOK`: the fixture `{3,4,6}` above is an attempted,
structurally invalid candidate, and it is present in the schedule on purpose.  Structural rejection
belongs to the *consumption* side, which is formalized in `Erdos.Erdos64.TriangleTraversalKernel`.

NOT FORMALIZED HERE.  This is the schedule of *one* state, not the traversal.  No recursion, no
state stack, no `install` and no rollback; no candidate record tags or payload consumption, and in
particular no `C₈`/`C₁₆` payload bookkeeping — this module does not model record consumption at
all, and the statement "an attempted but structurally invalid candidate consumes no record" is a
property of the *later* record layer, not of this schedule; no counter bookkeeping beyond reading
`s.introduced` (the counter *update* `nextIntroducedNat` lives in the traversal kernel and is not
reproduced here); no completion or terminal handling of the traversal; no certificate-stream
parser, byte-level or tag-level decoding, and no EOF handling; no root normalization and no orbit
classification; no completeness of the schedule (that the released traversal, when it reaches a
state, really does call `visit` with these candidates in this order), no lower bound on the number
of attempts, no `60`-vertex lower bound (`thm:main`, `cor:bound`) and no Erdős–Gyárfás conjecture.
This module makes no novelty claim: it is a formal restatement of the released `visit`'s one-state
candidate schedule, its cursor update and its label decoding, together with the label discipline
that every attempted candidate satisfies.

Graphs here are finite, undirected and simple.
-/

import Erdos.Erdos64.TriangleTraversalKernel

set_option autoImplicit false

namespace Erdos64

/-! ### The cursor, the schedule record and label decoding -/

/-- The released traversal's candidate cursor: a pair `(q₀, r₀)` of previously attempted labels,
with `none` standing for the released checker's `(-1, -1)` sentinel.  Modelling the sentinel as
`none` rather than as a signed label keeps "no cursor" disjoint from every real label and keeps the
whole schedule free of wrapping arithmetic. -/
abbrev SearchCursor := Option (SearchPoint × SearchPoint)

/-- The one-state schedule the released `visit` computes before recursing: the selected point (or
`none`), the cursor it leaves for the next state, and the attempted candidate blocks in the
released nested-loop order. -/
structure VisitSchedule where
  /-- The selected point, or `none` when the point advance found no unfinished introduced point. -/
  point : Option SearchPoint
  /-- The candidate cursor left behind. -/
  cursor : SearchCursor
  /-- The attempted candidate blocks, in nested-loop order. -/
  candidates : List SearchBlock

/-- The non-wrapping label decoder: `n` decodes to the point `n` exactly when `n` is still inside
the `29`-point range, and to nothing otherwise.  In particular a fresh label at or beyond `29` is
*dropped* rather than wrapped or truncated. -/
def toSearchPoint (n : Nat) : Option SearchPoint :=
  if h : n < 29 then some ⟨n, h⟩ else none

/-- `toSearchPoint` accepts exactly the in-range labels, and the accepted point is that label. -/
theorem toSearchPoint_eq_some_iff {n : Nat} {p : SearchPoint} :
    toSearchPoint n = some p ↔ p.val = n ∧ n < 29 := by
  unfold toSearchPoint
  split
  · rename_i h
    rw [Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨rfl, h⟩
    · rintro ⟨hp, -⟩
      exact Fin.ext hp.symm
  · rename_i h
    constructor
    · intro heq
      exact absurd heq (by simp)
    · rintro ⟨-, hn⟩
      exact absurd hn h

/-- `toSearchPoint` rejects exactly the out-of-range labels. -/
theorem toSearchPoint_eq_none_iff {n : Nat} : toSearchPoint n = none ↔ 29 ≤ n := by
  constructor
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    have hsome : toSearchPoint n = some (⟨n, hlt⟩ : SearchPoint) :=
      toSearchPoint_eq_some_iff.mpr ⟨rfl, hlt⟩
    have hne : (none : Option SearchPoint) ≠ some (⟨n, hlt⟩ : SearchPoint) := by simp
    rw [h] at hsome
    exact hne hsome
  · intro h
    unfold toSearchPoint
    rw [dif_neg (by omega)]

/-- The two fresh labels of a counter value `u`: the label `u` and the label `u + 1`, each present
exactly when it is still a point of the `29`-point range.  This is the released `visit`'s fresh
label pair, with the range check performed by `toSearchPoint` instead of by wrapping. -/
def freshLabels (u : Fin 30) : List SearchPoint :=
  (toSearchPoint u.val).toList ++ (toSearchPoint (u.val + 1)).toList

/-- The exact membership characterisation of the fresh labels. -/
theorem mem_freshLabels_iff (u : Fin 30) (x : SearchPoint) :
    x ∈ freshLabels u ↔
      (x.val = u.val ∧ u.val < 29) ∨ (x.val = u.val + 1 ∧ u.val + 1 < 29) := by
  rw [freshLabels, List.mem_append, Option.mem_toList, Option.mem_toList,
    toSearchPoint_eq_some_iff, toSearchPoint_eq_some_iff]

/-- A strictly increasing two-element list of points. -/
theorem pairwise_lt_pair {p q : SearchPoint} (h : p < q) : [p, q].Pairwise (· < ·) := by
  rw [List.pairwise_cons]
  refine ⟨?_, List.pairwise_singleton _ _⟩
  intro y hy
  rw [List.mem_singleton] at hy
  subst hy
  exact h

/-- The `29`-point range, listed ascending by `List.finRange`, is strictly increasing.  This is the
order the released pool inherits from the ascending label scan. -/
theorem finRange_pairwise_lt (n : Nat) : (List.finRange n).Pairwise (· < ·) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.finRange_succ, List.pairwise_cons]
      refine ⟨?_, ?_⟩
      · intro y hy
        obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy
        exact Fin.succ_pos x
      · exact List.Pairwise.map Fin.succ (fun a b hab => Fin.succ_lt_succ_iff.mpr hab) ih

/-- The fresh labels are strictly increasing: they are the two consecutive labels `u` and `u + 1`,
and at the range boundary the list is a singleton or empty. -/
theorem freshLabels_pairwise (u : Fin 30) : (freshLabels u).Pairwise (· < ·) := by
  rw [freshLabels]
  rcases h : toSearchPoint u.val with _ | p
  · rcases h2 : toSearchPoint (u.val + 1) with _ | q
    · simp
    · simp
  · rcases h2 : toSearchPoint (u.val + 1) with _ | q
    · simp
    · rw [toSearchPoint_eq_some_iff] at h h2
      have hpq : p < q := by show p.val < q.val; omega
      have hlist : (some p).toList ++ (some q).toList = [p, q] := by simp
      rw [hlist]
      exact pairwise_lt_pair hpq

/-! ### The candidate pool of a selected point -/

/-- *Exactly* the released pool of the selected point `p`: the ascending old labels `q` with
`p < q`, `q.val < introduced`, `pointDegree s q < 3` and `¬ pairUsed s p q`, followed by the fresh
labels `introduced` and `introduced + 1` when those are still points. -/
def possibleLabels {m : Nat} (s : SearchState m) (p : SearchPoint) : List SearchPoint :=
  ((List.finRange 29).filter (fun q =>
      decide (p < q ∧ q.val < s.introduced.val ∧ pointDegree s q < 3 ∧ ¬ pairUsed s p q))) ++
    freshLabels s.introduced

/-- **The exact membership characterisation of the pool.**  A point is in the pool of `p` exactly
when it is an old label satisfying the four released conditions, or the fresh label `introduced`,
or the fresh label `introduced + 1`. -/
theorem possibleLabels_mem_iff {m : Nat} (s : SearchState m) (p x : SearchPoint) :
    x ∈ possibleLabels s p ↔
      (p < x ∧ x.val < s.introduced.val ∧ pointDegree s x < 3 ∧ ¬ pairUsed s p x) ∨
      (x.val = s.introduced.val ∧ s.introduced.val < 29) ∨
      (x.val = s.introduced.val + 1 ∧ s.introduced.val + 1 < 29) := by
  simp only [possibleLabels, List.mem_append, List.mem_filter, List.mem_finRange,
    decide_eq_true_iff, mem_freshLabels_iff, true_and]

/-- Every pool label is at most the second fresh label `introduced + 1`; this is the label bound
that makes the pool compatible with `CandidateDiscipline`. -/
theorem possibleLabels_value_le {m : Nat} {s : SearchState m} {p x : SearchPoint}
    (hx : x ∈ possibleLabels s p) : x.val ≤ s.introduced.val + 1 := by
  rw [possibleLabels_mem_iff] at hx
  rcases hx with ⟨-, hx, -, -⟩ | ⟨hx, -⟩ | ⟨hx, -⟩ <;> omega

/-- The pool is strictly increasing: it is an ascending list of distinct old labels followed by the
ascending fresh labels, and every old label is strictly below every fresh label. -/
theorem possibleLabels_pairwise {m : Nat} (s : SearchState m) (p : SearchPoint) :
    (possibleLabels s p).Pairwise (· < ·) := by
  rw [possibleLabels, List.pairwise_append]
  refine ⟨List.Pairwise.filter _ (finRange_pairwise_lt 29), freshLabels_pairwise s.introduced, ?_⟩
  intro x hx y hy
  rw [List.mem_filter, decide_eq_true_iff] at hx
  rw [mem_freshLabels_iff] at hy
  have hxval : x.val < s.introduced.val := hx.2.2.1
  have hyval : s.introduced.val ≤ y.val := by
    rcases hy with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
  exact Fin.lt_def.mpr (lt_of_lt_of_le hxval hyval)

/-- The pool has no repeated label. -/
theorem possibleLabels_nodup {m : Nat} (s : SearchState m) (p : SearchPoint) :
    (possibleLabels s p).Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  exact List.Pairwise.imp (fun h => ne_of_lt h) (possibleLabels_pairwise s p)

/-! ### The released ascending point advance -/

/-- The ascending search from `start` over the offsets `0, 1, …`, with `fuel` steps available: this
is the released `visit`'s `while` loop over the point labels, written as a bounded recursion so
that it terminates by construction.  The loop stops at the first label `p` with
`p.val < introduced` and `pointDegree s p ≠ 3`, matching the released `while` condition exactly —
including on malformed states, where the condition is simply never satisfied and the loop runs out
of fuel.  It is *not* the traversal's recursion: it is one state's point advance. -/
def advanceFrom {m : Nat} (s : SearchState m) (start : SearchPoint) (offset : Nat) :
    Nat → Option SearchPoint
  | 0 => none
  | fuel + 1 =>
      match toSearchPoint (start.val + offset) with
      | none => none
      | some p =>
          if p.val < s.introduced.val ∧ pointDegree s p ≠ 3 then some p
          else advanceFrom s start (offset + 1) fuel

/-- The released point advance for one state: search from `start` up to the end of the point range.
The fuel `29 - start.val` is exactly the number of offsets from `start` to the last point `28`. -/
def advancePoint {m : Nat} (s : SearchState m) (start : SearchPoint) : Option SearchPoint :=
  advanceFrom s start 0 (29 - start.val)

/-- The success shape of the bounded advance: a returned point sits at some offset inside the
fuel, and the released `while` condition holds there. -/
theorem advanceFrom_spec {m : Nat} {s : SearchState m} {start : SearchPoint} :
    ∀ (fuel offset : Nat) {p : SearchPoint}, advanceFrom s start offset fuel = some p →
      ∃ k, k < fuel ∧ p.val = start.val + offset + k ∧
        p.val < s.introduced.val ∧ pointDegree s p ≠ 3 := by
  intro fuel
  induction fuel with
  | zero =>
      intro offset p h
      simp [advanceFrom] at h
  | succ fuel ih =>
      intro offset p h
      unfold advanceFrom at h
      rcases hts : toSearchPoint (start.val + offset) with _ | p'
      · rw [hts] at h
        simp at h
      · rw [hts] at h
        dsimp only at h
        by_cases hc : p'.val < s.introduced.val ∧ pointDegree s p' ≠ 3
        · rw [if_pos hc] at h
          have hp : p = p' := (Option.some.inj h).symm
          subst hp
          rw [toSearchPoint_eq_some_iff] at hts
          exact ⟨0, Nat.succ_pos fuel, by omega, hc.1, hc.2⟩
        · rw [if_neg hc] at h
          obtain ⟨k, hk, hval, hlt, hdeg⟩ := ih (offset + 1) h
          exact ⟨k + 1, Nat.succ_lt_succ hk, by omega, hlt, hdeg⟩

/-- The leastness of the bounded advance: any point at or after the search start that satisfies the
released `while` condition is at or after the returned point.  This is what makes the returned point
the *first* unfinished introduced label, not merely one of them. -/
theorem advanceFrom_least {m : Nat} {s : SearchState m} {start : SearchPoint} :
    ∀ (fuel offset : Nat) {p : SearchPoint}, advanceFrom s start offset fuel = some p →
      ∀ q : SearchPoint, start.val + offset ≤ q.val →
        q.val < s.introduced.val → pointDegree s q ≠ 3 → p.val ≤ q.val := by
  intro fuel
  induction fuel with
  | zero =>
      intro offset p h
      simp [advanceFrom] at h
  | succ fuel ih =>
      intro offset p h q hq hv hd
      unfold advanceFrom at h
      rcases hts : toSearchPoint (start.val + offset) with _ | p'
      · rw [hts] at h
        simp at h
      · rw [hts] at h
        dsimp only at h
        by_cases hc : p'.val < s.introduced.val ∧ pointDegree s p' ≠ 3
        · rw [if_pos hc] at h
          have hp : p = p' := (Option.some.inj h).symm
          subst hp
          rw [toSearchPoint_eq_some_iff] at hts
          omega
        · rw [if_neg hc] at h
          by_cases hstep : start.val + offset + 1 ≤ q.val
          · exact ih (offset + 1) h q hstep hv hd
          · exfalso
            rw [toSearchPoint_eq_some_iff] at hts
            have hqeq : q = p' := Fin.ext (by omega)
            rw [hqeq] at hv hd
            exact hc ⟨hv, hd⟩

/-- The bounds of the released point advance: the returned point is at or after the start, still
below `introduced`, and its degree is not `3`. -/
theorem advancePoint_spec {m : Nat} {s : SearchState m} {start p : SearchPoint}
    (h : advancePoint s start = some p) :
    start ≤ p ∧ p.val < s.introduced.val ∧ pointDegree s p ≠ 3 := by
  obtain ⟨k, hk, hval, hlt, hdeg⟩ := advanceFrom_spec (29 - start.val) 0 h
  refine ⟨?_, hlt, hdeg⟩
  show start.val ≤ p.val
  omega

/-- The selected point is the first label at or after the start satisfying the released `while`
condition. -/
theorem advancePoint_least {m : Nat} {s : SearchState m} {start p q : SearchPoint}
    (h : advancePoint s start = some p) (hstart : start ≤ q) (hval : q.val < s.introduced.val)
    (hdeg : pointDegree s q ≠ 3) : p.val ≤ q.val := by
  exact advanceFrom_least (29 - start.val) 0 h q (by
    have hs : start.val ≤ q.val := hstart
    omega) hval hdeg

/-- Under the cubic degree bound the selected point is genuinely unfinished: its degree is `< 3`. -/
theorem advancePoint_degree_lt {m : Nat} {s : SearchState m} {start p : SearchPoint}
    (hdeg : ∀ q, pointDegree s q ≤ 3) (h : advancePoint s start = some p) :
    pointDegree s p < 3 := by
  have h1 := hdeg p
  have h2 := (advancePoint_spec h).2.2
  omega

/-- Every introduced label from the start that lies strictly before the selected point was *skipped*
by the advance, so — since the advance only skips labels whose degree is `3` — it has degree exactly
`3`. -/
theorem advancePoint_skipped {m : Nat} {s : SearchState m} {start p q : SearchPoint}
    (h : advancePoint s start = some p) (hstart : start ≤ q) (hqp : q < p) :
    pointDegree s q = 3 := by
  have hp_lt : p.val < s.introduced.val := (advancePoint_spec h).2.1
  have hqval : q.val < p.val := hqp
  by_contra hne
  have hval : q.val < s.introduced.val := lt_trans hqval hp_lt
  have hle := advancePoint_least h hstart hval hne
  omega

/-! ### The released nested loop over the pool -/

/-- The generic nested loop `for i`, `for j = i + 1`: for `xs = [x₀, x₁, …]` it produces
`[(x₀,x₁), (x₀,x₂), …, (x₁,x₂), …]`, i.e. all pairs of positions `i < j` in the order of the
outer loop first and the inner loop second. -/
def orderedPairs {α : Type*} : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ orderedPairs xs

/-- `q` occurs strictly before `r` in the list `xs`, exhibited by the exact suffix decomposition
`xs = l₁ ++ q :: l₂ ++ r :: l₃`. -/
def OccursBefore {α : Type*} (xs : List α) (q r : α) : Prop :=
  ∃ l₁ l₂ l₃ : List α, xs = l₁ ++ q :: l₂ ++ r :: l₃

/-- **The membership characterisation of the nested loop.**  A pair is produced by `orderedPairs`
exactly when its first component occurs strictly before its second in the input list. -/
theorem mem_orderedPairs_iff {α : Type*} {xs : List α} {q r : α} :
    (q, r) ∈ orderedPairs xs ↔ OccursBefore xs q r := by
  induction xs with
  | nil => simp [orderedPairs, OccursBefore]
  | cons x xs ih =>
      rw [orderedPairs, List.mem_append, List.mem_map, ih]
      constructor
      · rintro (⟨y, hy, hpair⟩ | ⟨l₁, l₂, l₃, heq⟩)
        · injection hpair with h1 h2
          subst h1
          subst h2
          obtain ⟨l₂, l₃, hsplit⟩ := List.mem_iff_append.mp hy
          exact ⟨[], l₂, l₃, by simp [hsplit]⟩
        · exact ⟨x :: l₁, l₂, l₃, by rw [heq]; rfl⟩
      · rintro ⟨l₁, l₂, l₃, heq⟩
        cases l₁ with
        | nil =>
            simp only [List.nil_append] at heq
            injection heq with hx hxs
            subst hx
            exact Or.inl ⟨r, by rw [hxs]; simp, rfl⟩
        | cons z zs =>
            simp only [List.cons_append] at heq
            injection heq with hx hxs
            exact Or.inr ⟨zs, l₂, l₃, hxs⟩

/-- The suffix decomposition underlying `OccursBefore` is a genuine sublist. -/
theorem occursBefore_sublist {α : Type*} {xs : List α} {q r : α}
    (h : OccursBefore xs q r) : List.Sublist [q, r] xs := by
  obtain ⟨l₁, l₂, l₃, rfl⟩ := h
  induction l₁ with
  | nil =>
      rw [List.nil_append]
      exact List.Sublist.cons_cons q
        (List.Sublist.append (List.nil_sublist l₂)
          (List.Sublist.cons_cons r (List.nil_sublist l₃)))
  | cons z zs ih =>
      rw [List.cons_append]
      exact List.Sublist.cons z ih

/-- In a strictly increasing list, an earlier occurrence is a strictly smaller element.  This is
what turns the nested-loop order into the strict order on labels the schedule relies on. -/
theorem occursBefore_lt {α : Type*} [LT α] {xs : List α} {q r : α}
    (hpair : xs.Pairwise (· < ·)) (h : OccursBefore xs q r) : q < r :=
  hpair.forall_sublist (occursBefore_sublist h)

/-! ### The candidate guards and the ordered block constructor -/

/-- The released fresh-label guard: a pool pair `(q, r)` is admissible unless its second component
is the second fresh label `introduced + 1` while its first component is not the first fresh label
`introduced`.  This is exactly the released check that a candidate may introduce `introduced + 1`
only together with `introduced`. -/
def freshGuard (u : Fin 30) (q r : SearchPoint) : Prop :=
  ¬(r.val = u.val + 1 ∧ q.val ≠ u.val)

instance instDecidableFreshGuard (u : Fin 30) (q r : SearchPoint) :
    Decidable (freshGuard u q r) := by
  unfold freshGuard
  infer_instance

/-- The released strict lexicographic candidate-cursor guard.  With no cursor every pair is
admissible; with a cursor `(q₀, r₀)` the pair `(q, r)` must come strictly after it in the
lexicographic order `q` then `r`. -/
def afterCursor : SearchCursor → SearchPoint → SearchPoint → Prop
  | none, _, _ => True
  | some (q₀, r₀), q, r => q₀ < q ∨ (q₀ = q ∧ r₀ < r)

instance instDecidableAfterCursor (cursor : SearchCursor) (q r : SearchPoint) :
    Decidable (afterCursor cursor q r) := by
  cases cursor with
  | none => simp only [afterCursor]; infer_instance
  | some qr => cases qr; simp only [afterCursor]; infer_instance

/-- With no cursor the guard accepts everything. -/
theorem afterCursor_none (q r : SearchPoint) : afterCursor none q r = True :=
  rfl

/-- The total ordered-block constructor: it produces the block exactly when its three arguments are
strictly increasing, and `none` otherwise.  Totality is what makes it usable under `filterMap`. -/
def mkCandidate? (p q r : SearchPoint) : Option SearchBlock :=
  if h : p < q ∧ q < r then some ⟨p, q, r, h.1, h.2⟩ else none

/-- The `(a, b, c)` shape of a block, used to compare blocks without comparing their inequality
proof fields. -/
def SearchBlock.shape (t : SearchBlock) : SearchPoint × SearchPoint × SearchPoint :=
  (t.a, t.b, t.c)

/-- A block is determined by its shape; the two inequality proofs are irrelevant. -/
theorem SearchBlock.ext' {t₁ t₂ : SearchBlock} (ha : t₁.a = t₂.a) (hb : t₁.b = t₂.b)
    (hc : t₁.c = t₂.c) : t₁ = t₂ := by
  obtain ⟨a₁, b₁, c₁, hab₁, hbc₁⟩ := t₁
  obtain ⟨a₂, b₂, c₂, hab₂, hbc₂⟩ := t₂
  simp only at ha hb hc
  subst ha
  subst hb
  subst hc
  rw [Subsingleton.elim hab₁ hab₂, Subsingleton.elim hbc₁ hbc₂]

/-- The shape is injective, so comparing shapes is comparing blocks. -/
theorem SearchBlock.shape_injective : Function.Injective SearchBlock.shape := by
  intro t₁ t₂ h
  refine SearchBlock.ext' ?_ ?_ ?_
  · simpa only [SearchBlock.shape] using
      congrArg (fun x : SearchPoint × SearchPoint × SearchPoint => x.1) h
  · simpa only [SearchBlock.shape] using
      congrArg (fun x : SearchPoint × SearchPoint × SearchPoint => x.2.1) h
  · simpa only [SearchBlock.shape] using
      congrArg (fun x : SearchPoint × SearchPoint × SearchPoint => x.2.2) h

/-- The ordered-block constructor succeeds exactly on strictly increasing triples, and the shape of
the result is that triple. -/
theorem mkCandidate?_eq_some_iff (p q r : SearchPoint) (t : SearchBlock) :
    mkCandidate? p q r = some t ↔ p < q ∧ q < r ∧ t.shape = (p, q, r) := by
  constructor
  · intro h
    unfold mkCandidate? at h
    split at h
    · rename_i hc
      rw [Option.some.injEq] at h
      subst h
      exact ⟨hc.1, hc.2, rfl⟩
    · simp at h
  · rintro ⟨hpq, hqr, hshape⟩
    have hsome : mkCandidate? p q r = some ⟨p, q, r, hpq, hqr⟩ := by
      unfold mkCandidate?
      rw [dif_pos ⟨hpq, hqr⟩]
    rw [hsome, Option.some.injEq]
    exact SearchBlock.shape_injective (by rw [hshape]; rfl)

/-! ### The one-state schedule -/

/-- The cursor the released `visit` leaves behind: the input cursor when the point advance selected
`start` itself, and the absent cursor `none` otherwise.  A skip of one or more full points therefore
resets the candidate cursor. -/
def effectiveCursor {m : Nat} (s : SearchState m) (start : SearchPoint)
    (cursor : SearchCursor) : SearchCursor :=
  if advancePoint s start = some start then cursor else none

/-- **The released one-state attempted candidate schedule.**  The point advance selects `p`; the
cursor is preserved exactly when `p` is the start and is otherwise reset; the pool of `p` is walked
by the nested loop `orderedPairs`; each pair is kept when it passes the fresh guard and the strict
lexicographic effective-cursor guard; and each kept pair is turned into the ordered block `{p,q,r}`.
No structural rejection and no cycle oracle is applied here: every block this produces is an
*attempted* candidate, counted before those tests run. -/
def candidateSchedule {m : Nat} (s : SearchState m) (start : SearchPoint)
    (cursor : SearchCursor) : VisitSchedule :=
  match advancePoint s start with
  | none => ⟨none, none, []⟩
  | some p =>
      ⟨some p, effectiveCursor s start cursor,
        ((orderedPairs (possibleLabels s p)).filter (fun qr =>
            decide (freshGuard s.introduced qr.1 qr.2 ∧
              afterCursor (effectiveCursor s start cursor) qr.1 qr.2))).filterMap
          (fun qr => mkCandidate? p qr.1 qr.2)⟩

/-- The selected point of the schedule is exactly the point advance's result. -/
theorem candidateSchedule_point {m : Nat} (s : SearchState m) (start : SearchPoint)
    (cursor : SearchCursor) :
    (candidateSchedule s start cursor).point = advancePoint s start := by
  unfold candidateSchedule
  split
  · rename_i h
    simp [h]
  · rename_i p h
    simp [h]

/-- The cursor of the schedule is the effective cursor, in the exact form the released `visit`
computes: preserved when the advance selected the start, reset to `none` otherwise. -/
theorem candidateSchedule_cursor {m : Nat} (s : SearchState m) (start : SearchPoint)
    (cursor : SearchCursor) :
    (candidateSchedule s start cursor).cursor =
      if advancePoint s start = some start then cursor else none := by
  unfold candidateSchedule
  split
  · rename_i h
    rw [h]
    simp
  · rename_i p h
    simp only [effectiveCursor, h]

/-- A `none` point means a `none` cursor and an empty candidate list. -/
theorem candidateSchedule_none {m : Nat} (s : SearchState m) (start : SearchPoint)
    (cursor : SearchCursor) (h : advancePoint s start = none) :
    (candidateSchedule s start cursor).point = none ∧
      (candidateSchedule s start cursor).cursor = none ∧
      (candidateSchedule s start cursor).candidates = [] := by
  unfold candidateSchedule
  rw [h]
  exact ⟨rfl, rfl, rfl⟩

/-- When the advance selects the start itself, the input cursor is preserved. -/
theorem candidateSchedule_cursor_preserved {m : Nat} (s : SearchState m) (start : SearchPoint)
    (cursor : SearchCursor) (h : advancePoint s start = some start) :
    (candidateSchedule s start cursor).cursor = cursor := by
  rw [candidateSchedule_cursor, if_pos h]

/-- When the advance does not select the start, the input cursor is reset to `none`. -/
theorem candidateSchedule_cursor_reset {m : Nat} (s : SearchState m) (start : SearchPoint)
    (cursor : SearchCursor) (h : advancePoint s start ≠ some start) :
    (candidateSchedule s start cursor).cursor = none := by
  rw [candidateSchedule_cursor, if_neg h]

/-- If a real cursor is supplied, it is preserved exactly when the advance selected the start. -/
theorem candidateSchedule_cursor_eq_iff {m : Nat} (s : SearchState m) (start : SearchPoint)
    (cursor : SearchCursor) (hc : cursor ≠ none) :
    (candidateSchedule s start cursor).cursor = cursor ↔ advancePoint s start = some start := by
  constructor
  · intro h
    by_contra hne
    rw [candidateSchedule_cursor_reset s start cursor hne] at h
    exact hc h.symm
  · intro h
    exact candidateSchedule_cursor_preserved s start cursor h

/-- If the advance selected `p` after skipping at least one full point — witnessed by an introduced
label `q` with `start ≤ q < p` — then the candidate cursor is reset to `none`. -/
theorem candidateSchedule_cursor_reset_of_skipped {m : Nat} (s : SearchState m)
    (start : SearchPoint) (cursor : SearchCursor) {p q : SearchPoint}
    (hp : advancePoint s start = some p) (hstart : start ≤ q) (hqp : q < p) :
    (candidateSchedule s start cursor).cursor = none := by
  refine candidateSchedule_cursor_reset s start cursor ?_
  intro hcontra
  have hpq : p = start := Option.some.inj (hp.symm.trans hcontra)
  subst p
  exact (not_lt_of_ge hstart) hqp

/-- The candidate list is empty when the advance finds no point. -/
theorem candidateSchedule_candidates_none {m : Nat} (s : SearchState m) (start : SearchPoint)
    (cursor : SearchCursor) (h : advancePoint s start = none) :
    (candidateSchedule s start cursor).candidates = [] :=
  (candidateSchedule_none s start cursor h).2.2

/-- The candidate list when the advance selects `p`: the nested loop over the pool of `p`, filtered
by the fresh guard and the effective-cursor guard, mapped to ordered blocks. -/
theorem candidateSchedule_candidates_some {m : Nat} (s : SearchState m) (start : SearchPoint)
    (cursor : SearchCursor) {p : SearchPoint} (h : advancePoint s start = some p) :
    (candidateSchedule s start cursor).candidates =
      ((orderedPairs (possibleLabels s p)).filter (fun qr =>
          decide (freshGuard s.introduced qr.1 qr.2 ∧
            afterCursor (effectiveCursor s start cursor) qr.1 qr.2))).filterMap
        (fun qr => mkCandidate? p qr.1 qr.2) := by
  unfold candidateSchedule
  rw [h]

/-- **The main characterisation of the schedule.**  A block is attempted by the one-state schedule
exactly when the advance selects a point `p`, the pool of `p` contains `q` strictly before `r` (the
released nested-loop order), the fresh guard and the effective-cursor guard both pass, and the
block's components are `p, q, r`. -/
theorem candidateSchedule_mem_iff {m : Nat} (s : SearchState m) (start : SearchPoint)
    (cursor : SearchCursor) (t : SearchBlock) :
    t ∈ (candidateSchedule s start cursor).candidates ↔
      ∃ p q r : SearchPoint,
        advancePoint s start = some p ∧
        OccursBefore (possibleLabels s p) q r ∧
        freshGuard s.introduced q r ∧
        afterCursor (effectiveCursor s start cursor) q r ∧
        mkCandidate? p q r = some t := by
  unfold candidateSchedule
  split
  · rename_i h
    constructor
    · intro ht
      exact absurd ht (by simp)
    · rintro ⟨p, q, r, hp, -⟩
      rw [h] at hp
      exact absurd hp (by simp)
  · rename_i p h
    simp only [List.mem_filterMap, List.mem_filter, decide_eq_true_iff]
    constructor
    · rintro ⟨⟨q, r⟩, ⟨hordered, hguard, hafter⟩, hmk⟩
      have hbefore : OccursBefore (possibleLabels s p) q r :=
        mem_orderedPairs_iff.mp hordered
      exact ⟨p, q, r, h, hbefore, hguard, hafter, hmk⟩
    · rintro ⟨p', q, r, hp', hbefore, hguard, hafter, hmk⟩
      have hp_eq : p' = p := by
        rw [h] at hp'
        exact (Option.some.inj hp').symm
      subst p'
      have hordered : (q, r) ∈ orderedPairs (possibleLabels s p) :=
        mem_orderedPairs_iff.mpr hbefore
      exact ⟨(q, r), ⟨hordered, hguard, hafter⟩, hmk⟩

/-! ### The label discipline of attempted candidates -/

/-- **The generated-triple discipline.**  If `p` is an introduced label, `q` and `r` are pool labels
of `p` with `q < r`, and the fresh guard holds, then the ordered block `{p, q, r}` is disciplined at
`introduced`: every label is at most `introduced + 1`, and a block using the second fresh label
`introduced + 1` also uses the first fresh label `introduced`.

The proof is the released guard's whole point.  `p` is below `introduced`, so it can never be the
second fresh label.  `q` cannot be the second fresh label either: the pool bounds both `q` and `r`
by `introduced + 1`, while `q < r` would force `r` above `introduced + 1`.  Hence an occurrence of
`introduced + 1` is necessarily `r`, and the fresh guard then forces `q` to be `introduced`. -/
theorem discipline_of_possible {m : Nat} {s : SearchState m} {p q r : SearchPoint}
    (hp : p.val < s.introduced.val) (hq : q ∈ possibleLabels s p) (hr : r ∈ possibleLabels s p)
    (hpq : p < q) (hqr : q < r) (hguard : freshGuard s.introduced q r) :
    CandidateDiscipline s.introduced ⟨p, q, r, hpq, hqr⟩ := by
  have hqle : q.val ≤ s.introduced.val + 1 := possibleLabels_value_le hq
  have hrle : r.val ≤ s.introduced.val + 1 := possibleLabels_value_le hr
  have hpq' : p.val < q.val := hpq
  have hqr' : q.val < r.val := hqr
  constructor
  · intro x hx
    rw [SearchBlock.mem_points] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  · intro hcont
    rw [containsLabel] at hcont
    obtain ⟨x, hx, hxval⟩ := hcont
    rw [SearchBlock.mem_points] at hx
    rcases hx with rfl | rfl | rfl
    · omega
    · omega
    · refine ⟨q, ?_, ?_⟩
      · rw [SearchBlock.mem_points]
        exact Or.inr (Or.inl rfl)
      · by_contra hne
        exact hguard ⟨hxval, hne⟩

/-- **Every attempted candidate is disciplined.**  This is the label-discipline half of the
generation side: the released schedule can never produce a candidate that introduces the second
fresh label without the first, or that labels a point above `introduced + 1`. -/
theorem candidateSchedule_discipline {m : Nat} (s : SearchState m) (start : SearchPoint)
    (cursor : SearchCursor) {t : SearchBlock}
    (ht : t ∈ (candidateSchedule s start cursor).candidates) :
    CandidateDiscipline s.introduced t := by
  obtain ⟨p, q, r, hadv, hbefore, hguard, -, hmk⟩ :=
    (candidateSchedule_mem_iff s start cursor t).mp ht
  obtain ⟨hpq, hqr, hshape⟩ := (mkCandidate?_eq_some_iff p q r t).mp hmk
  have hp : p.val < s.introduced.val := (advancePoint_spec hadv).2.1
  obtain ⟨l₁, l₂, l₃, heq⟩ := hbefore
  have hq : q ∈ possibleLabels s p := by rw [heq]; simp
  have hr : r ∈ possibleLabels s p := by rw [heq]; simp
  have ht_eq : t = ⟨p, q, r, hpq, hqr⟩ :=
    SearchBlock.shape_injective (by rw [hshape]; rfl)
  rw [ht_eq]
  exact discipline_of_possible hp hq hr hpq hqr hguard

/-! ### Fixtures from the artifact's triangle-root orbit 1 -/

section Fixtures

/- The fixture decisions run `decide` over the point advance, the pool filters and the nested loop;
a little more elaborator recursion depth than the default is needed.  This is an elaboration knob
only: it does not weaken any proof, which remains a kernel check of the computed `Decidable`
instance. -/
set_option maxRecDepth 4000

/-- Boundary fixture: at the counter value `0` both fresh labels `0` and `1` are still points. -/
theorem freshLabels_zero : freshLabels (0 : Fin 30) = [(0 : SearchPoint), (1 : SearchPoint)] := by
  decide

/-- Boundary fixture: at the counter value `28` only the fresh label `28` is still a point, and the
fresh label `29` is dropped rather than wrapped to `0`. -/
theorem freshLabels_twentyeight : freshLabels (28 : Fin 30) = [(28 : SearchPoint)] := by
  decide

/-- Boundary fixture: at the counter value `29` neither fresh label is a point, so the fresh label
list is empty. -/
theorem freshLabels_twentynine : freshLabels (29 : Fin 30) = [] := by
  decide

/-- The pool of the orbit-1 state at `start = 1`: the old labels `5` and `6` (the labels `2`, `3`,
`4` are either paired with `1` or full), followed by the fresh labels `7` and `8`. -/
theorem orbitOne_possible_one :
    possibleLabels orbitOneState (1 : SearchPoint) =
      [(5 : SearchPoint), (6 : SearchPoint), (7 : SearchPoint), (8 : SearchPoint)] := by
  decide

/-- The pool of the orbit-1 state at `start = 3`: the old labels `4`, `5`, `6` followed by the fresh
labels `7` and `8`. -/
theorem orbitOne_possible_three :
    possibleLabels orbitOneState (3 : SearchPoint) =
      [(4 : SearchPoint), (5 : SearchPoint), (6 : SearchPoint), (7 : SearchPoint),
        (8 : SearchPoint)] := by
  decide

/-- The selected point at `start = 1` is `1` itself: it is introduced (`1 < 7`) and has degree `2`,
so no point is skipped and the cursor `(2,4)` is preserved.  The fresh guard removes the pairs
ending in the second fresh label `8` whose first component is not `7`, leaving exactly the four
attempted blocks `{1,5,6}`, `{1,5,7}`, `{1,6,7}`, `{1,7,8}`. -/
theorem orbitOne_startOne_cursor24 :
    (List.map SearchBlock.shape
        (candidateSchedule orbitOneState (1 : SearchPoint)
          (some ((2 : SearchPoint), (4 : SearchPoint)))).candidates) =
      [((1 : SearchPoint), (5 : SearchPoint), (6 : SearchPoint)),
        ((1 : SearchPoint), (5 : SearchPoint), (7 : SearchPoint)),
        ((1 : SearchPoint), (6 : SearchPoint), (7 : SearchPoint)),
        ((1 : SearchPoint), (7 : SearchPoint), (8 : SearchPoint))] := by
  decide

/-- The same start with the cursor `(5,6)`: the strict lexicographic cursor guard cuts the schedule
to the exact suffix of the previous one, namely `{1,5,7}`, `{1,6,7}`, `{1,7,8}`. -/
theorem orbitOne_startOne_cursor56 :
    (List.map SearchBlock.shape
        (candidateSchedule orbitOneState (1 : SearchPoint)
          (some ((5 : SearchPoint), (6 : SearchPoint)))).candidates) =
      [((1 : SearchPoint), (5 : SearchPoint), (7 : SearchPoint)),
        ((1 : SearchPoint), (6 : SearchPoint), (7 : SearchPoint)),
        ((1 : SearchPoint), (7 : SearchPoint), (8 : SearchPoint))] := by
  decide

/-- `start = 3` with the absent cursor: the selected point is `3` itself and the schedule is the
full nested loop over the pool `[4,5,6,7,8]` after the fresh guard removes the three pairs ending
in the second fresh label `8` whose first component is not `7`. -/
theorem orbitOne_startThree_none :
    (List.map SearchBlock.shape
        (candidateSchedule orbitOneState (3 : SearchPoint) none).candidates) =
      [((3 : SearchPoint), (4 : SearchPoint), (5 : SearchPoint)),
        ((3 : SearchPoint), (4 : SearchPoint), (6 : SearchPoint)),
        ((3 : SearchPoint), (4 : SearchPoint), (7 : SearchPoint)),
        ((3 : SearchPoint), (5 : SearchPoint), (6 : SearchPoint)),
        ((3 : SearchPoint), (5 : SearchPoint), (7 : SearchPoint)),
        ((3 : SearchPoint), (6 : SearchPoint), (7 : SearchPoint)),
        ((3 : SearchPoint), (7 : SearchPoint), (8 : SearchPoint))] := by
  decide

/-- The structurally invalid candidate `{3,4,6}`: its points are ordered and each has old degree
below `3`, but the old block `{0,4,6}` already contains the pair `{4,6}`. -/
def orbitOneInvalidCandidate : SearchBlock :=
  ⟨3, 4, 6, by decide, by decide⟩

/-- **A structurally invalid candidate is still attempted.**  The block `{3,4,6}` is generated by
the one-state schedule at `start = 3`, because the schedule runs before the structural test: the
released `visit` counts it as an attempted candidate and only then asks
`structurally_invalid`. -/
theorem orbitOneInvalidCandidate_generated :
    orbitOneInvalidCandidate ∈
      (candidateSchedule orbitOneState (3 : SearchPoint) none).candidates := by
  rw [candidateSchedule_mem_iff]
  refine ⟨3, 4, 6, by decide, ?_, ?_, ?_, ?_⟩
  · refine ⟨[], [(5 : SearchPoint)], [(7 : SearchPoint), (8 : SearchPoint)], ?_⟩
    rw [orbitOne_possible_three]
    decide
  · decide
  · show True
    trivial
  · rw [mkCandidate?_eq_some_iff]
    exact ⟨by decide, by decide, rfl⟩

/-- The shape of the structurally invalid candidate occurs in the schedule's shapes. -/
theorem orbitOneInvalidCandidate_shape_occurs :
    orbitOneInvalidCandidate.shape ∈
      (List.map SearchBlock.shape
        (candidateSchedule orbitOneState (3 : SearchPoint) none).candidates) := by
  rw [orbitOne_startThree_none]
  decide

/-- The released structural test rejects the attempted candidate `{3,4,6}`: the old block `{0,4,6}`
already contains two of its points.  Together with `orbitOneInvalidCandidate_generated` this records
that the schedule and the structural test are separate layers. -/
theorem orbitOneInvalidCandidate_cppStructurallyInvalid :
    cppStructurallyInvalid orbitOneState 7 orbitOneInvalidCandidate = true := by
  decide

/-- The attempted candidate `{3,4,6}` is disciplined at `introduced = 7`, as
`candidateSchedule_discipline` predicts for every attempted candidate. -/
theorem orbitOneInvalidCandidate_discipline :
    CandidateDiscipline orbitOneState.introduced orbitOneInvalidCandidate :=
  candidateSchedule_discipline orbitOneState (3 : SearchPoint) none
    orbitOneInvalidCandidate_generated

end Fixtures

end Erdos64