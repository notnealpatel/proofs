/-
Erdős–Gyárfás problem 64 — executable structural state, candidate and expansion soundness.

PROVENANCE.  arXiv:2608.02675, Julius Tranquilli, "A 60-Vertex Lower Bound for Cubic Bipartite
Counterexamples to the Erdős–Gyárfás Conjecture" (2 August 2026), Section 3.2 (the triangle-rooted
reduced search).  The released artifact of the paper (`research/certificates/TRIANGLE_FORMAT.md`,
the `EG58TRI1` triangle-rooted certificate format, and its streaming checker
`research/src/verify_triangle_universal_certificate.cpp`) drives a deterministic
restricted-growth traversal over the `29` candidate points of a triangle-rooted linear
`3`-uniform configuration.  Three of its member functions are the subject of this module:

* `visit(state, candidate)` — the traversal's single candidate test.  It computes the candidate's
  `next_introduced` value, asks `structurally_invalid(state, candidate)`, and only when that
  returns false does it run the `C₈`/`C₁₆` rejection oracles (`check_c8_witness`,
  `check_c16_witness`, formalized in `Erdos.Erdos64.TriangleC8Kernel` and
  `Erdos.Erdos64.TriangleC16Kernel`); only after the structural test and the cycle oracles have
  both cleared the candidate does it assign `introduced := next_introduced` and call `install`;
* `structurally_invalid(state, candidate)` — the released *structural* rejection test.  It is
  deliberately written against the **old** blocks only: it walks the candidate's three point
  labels and tests each label `l` for `l < state.introduced`, rejecting when an old block
  already has three incidences through `l`, or when an old block already contains two of the
  candidate's points.  Labels `≥ state.introduced` are skipped, because the released checker
  maintains the invariant that a label at or above `introduced` occurs in no installed block;
* `install(state, candidate)` — the released state *mutation*.  It re-validates the candidate
  itself: it checks that the candidate's three points are ordered and in range, that each of them
  has degree `< 3`, and that no two of them are already paired, and then mutates the block,
  degree and pair arrays in place.  It does **not** advance `introduced`: that counter is computed
  and assigned by `visit`, before `install` is called.

Graphs here are finite, undirected and simple.

WHAT IS FORMALIZED HERE.  The executable structural layer that `visit` needs *before* the exact
restricted-growth traversal: state predicates, candidate predicates, the released structural
rejection test, and the soundness of the expansion step that appends a candidate and advances the
counter.

* `pointDegree s p` — the number of installed blocks through the point `p`, i.e. the degree of
  the point vertex `Sum.inl p` in the Levi graph of `s.config`; `pointDegree_eq_leviDegree` is
  the bridge to the degree already available in `Erdos.Erdos64.Incidence`, so the degree bound
  below is a genuine cubic-degree statement and not a re-encoding;
* `pairUsed s p q` — two points lie in a common installed block, with the elementary lemmas
  `pairUsed_iff`, `pairUsed_comm`, `pairUsed_of_mem` and the label bound `pairUsed_labels_lt`;
* `LabelsBelow s u` — every label occurring in an installed block is `< u`; this is exactly the
  invariant that makes the released `structurally_invalid`'s old-label restriction sound;
* `StateInvariant s` — the three properties the traversal maintains: labels below `introduced`,
  point degree at most `3`, and linearity of the configuration.  `stateCheck` is its executable
  form, with `stateCheck_iff` the reflection theorem;
* `containsLabel t n`, `CandidateDiscipline u t` — *exactly* the restricted-growth fresh-label /
  no-gap component of candidate validity, and nothing more: every candidate label is at most
  `u + 1`, and a candidate using the fresh label `u + 1` must also use the label `u` (fresh labels
  are introduced consecutively and without gaps, so the candidate's new labels form the initial
  segment `{u}, {u, u+1}`).  It is not a specification of candidate *generation*: the least
  unfinished point, the restriction of the candidate pool to old labels, and the lexicographic
  candidate order and cursor all remain outside it (see the exclusions below);
* `nextIntroducedNat u t` — the *Nat* counter update `u + [u ∈ t] + [u+1 ∈ t]` that the released
  `visit` computes and assigns before calling `install`; it mirrors the counter update performed
  in `visit`, not any computation inside the released `install`, which never touches the counter.
  Under `CandidateDiscipline` it is `< 30`, which `nextIntroducedNat_lt_thirty`
  proves and `nextIntroduced` packages into a `Fin 30`.  The three refinement lemmas
  `nextIntroducedNat_eq_of_not_contains`, `nextIntroducedNat_eq_add_one` and
  `nextIntroducedNat_eq_add_two` record the no-fresh, one-fresh and two-fresh cases, and
  `candidate_lt_nextIntroducedNat` records that every candidate label is strictly below the new
  counter value.  `SearchPoint = Fin 29` labels are `0, …, 28` while `introduced : Fin 30` is a
  *count* of labels, not a point: `nextIntroduced` stays a count and no `Fin` wrapping arithmetic
  is used anywhere;
* `CleanStructuralOK s t` — the mathematical structural validity of a candidate: every candidate
  point has degree `< 3` in the old state, and no old block contains two distinct candidate
  points.  These are the same two conditions the released `install` re-checks before mutating its
  arrays.  `candidateCheck` is the executable form of "discipline and clean validity", with
  `candidateCheck_iff` its reflection theorem;
* `cppStructurallyInvalid s oldIntroduced t` — the *executable* released test, `decide` of the
  disjunction "some candidate label `< oldIntroduced` has old degree `≥ 3`, or some two distinct
  candidate labels `< oldIntroduced` are already paired in an old block".  The key bridge
  `cppStructurallyInvalid_iff` proves that under `LabelsBelow s s.introduced` this released
  old-label-only test accepts exactly the mathematically clean candidates:
  `cppStructurallyInvalid s s.introduced.val t = true ↔ ¬ CleanStructuralOK s t`.  The direction
  that needs the hypothesis is the completeness direction: a candidate point of degree `≥ 3`
  necessarily occurs in an old block, hence — by `LabelsBelow` — carries an old label, so the
  released test cannot miss it.  Without `LabelsBelow` the released test is *incomplete*; this
  module therefore states the bridge only under the invariant, which is exactly the situation
  `visit` runs in;
* `SearchState.install s t h` — the *combined functional post-validation expansion transition*:
  one pure function that both appends the candidate and advances the counter.  Its type requires
  only `CandidateDiscipline s.introduced t`, not cleanliness, and it performs no validation of
  its own; clean structural validity enters as the separate hypothesis `hclean` of
  `degreeBound_install`, `linear_install` and `stateInvariant_install`.  It therefore models the
  *joint effect* on reachable states of `visit`'s counter assignment together with the released
  `install`'s array mutation, and it is deliberately **not** a transcription of the released
  `install`: the released `install` re-validates the candidate and never advances `introduced`,
  so a candidate that is not clean can technically be passed to `SearchState.install` even though
  the released `install` would refuse it.  `install_blocks_castSucc` and
  `install_blocks_last` are the lookup lemmas, `install_config` proves that the installed
  configuration *is* `s.addConfig t`, and the accounting lemmas
  `pointDegree_install : pointDegree (install s t h) p = pointDegree s p + [p ∈ t.points]` and
  `pairUsed_install_iff : pairUsed (install s t h) p q ↔ pairUsed s p q ∨ (p, q ∈ t.points)`
  are exact;
* the preservation theorems `labelsBelow_install`, `degreeBound_install`, `linear_install` and
  their combination `stateInvariant_install`: a state satisfying `StateInvariant` whose candidate
  is disciplined and clean installs to a state satisfying `StateInvariant`.  `linear_install`
  goes through the shared-pair characterisation of linearity of `Erdos.Erdos64.Incidence`
  (`IncidenceConfig.isLinear_iff_not_hasSharedPair`) rather than reproving any graph cycle, via
  the decomposition `hasSharedPair_addConfig`;
* fixtures.  `orbitOneState` / `orbitOneCandidate` (the artifact's triangle-root orbit 1, reused
  from `Erdos.Erdos64.TriangleC8Kernel`) are kernel-`decide`d to satisfy `StateInvariant`,
  `CandidateDiscipline` and `CleanStructuralOK`, so `candidateCheck` accepts the candidate and
  the installed state again satisfies `StateInvariant`.  The same candidate is *separately*
  `C₈`-rejected: `orbitOne_candidateAccepted_c8Rejected` records that the structural test accepts
  while the `C₈` oracle rejects, which matches the ordering of the released `visit` (structural
  test first, cycle oracles second, counter assignment and `install` last).  `pairReuseCandidate
  = {1,2,6}` reuses the old pair `{1,2}` and is
  rejected; `degreeFullCandidate = {0,5,6}` drives the old point `0` to degree `3` and is
  rejected.

TRUST BOUNDARY.  `orbitOneState`-shaped states and candidate blocks are *inputs* to this layer.
The exact restricted-growth traversal that generates the candidate pool, the point and cursor
schedule, and the recursive state stack is **not** formalized here; neither is the certificate
stream parser.  So the state `s` and candidate `t` must still be regarded as untrusted until the
generation side is formalized, and the released `visit` order — structural test, then `C₈`/`C₁₆`
oracles, then the `introduced` assignment and `install` — is only *modelled*, not implemented.
`SearchState.install` in particular is the combined pure transition (append plus counter update),
not the released `install`: the released `install`'s own re-validation of the candidate, its
in-place mutation of the block, degree and pair arrays, and its leaving `introduced` untouched are
not reproduced here.  What this module does establish is
the soundness of that structural test, and of the combined expansion step, relative to the
mathematical
predicates they stand for, so that a later formalization of the traversal has the executable
bridge available.  `CleanStructuralOK` is the *mathematical* predicate; `cppStructurallyInvalid`
is the *released implementation* of its negation restricted to old labels, and the two are
related by the proved iff above and not by definition.

NOT FORMALIZED HERE.  No exact possible pool of candidates, no least-unfinished-point selection,
no lexicographic candidate order or cursor schedule, no point schedule, no recursion or
state-stack management, no certificate stream or byte/tag-level parser, no `introduced` counter
bookkeeping beyond the single expansion step, no exhaustion or acceptance criterion for the
certificate, no root normalization or orbit classification, no completeness of the structural
test or of the traversal, no `60`-vertex lower bound (`thm:main`, `cor:bound`) and no
Erdős–Gyárfás conjecture.  In particular the *completeness* direction of the structural test
(that a clean candidate always passes the released test for every reachable state, not merely
under `LabelsBelow`) and the *converse* of the preservation theorem (that a state reachable by
the traversal satisfies `StateInvariant`) are not proved.  This module makes no novelty claim: it
is a formal restatement of the released checker's structural test and of the counter update that
`visit` performs, together with the soundness of their combined effect on reachable states
relative to the mathematical predicates above.
-/

import Erdos.Erdos64.TriangleC16Kernel

set_option autoImplicit false

namespace Erdos64

/-! ### Point degrees and used point pairs -/

/-- The number of installed blocks through the point `p`: the size of the incident-block set of
`s.config` at `p`.  This is the quantity the released `structurally_invalid` compares against `3`
for each candidate label below `introduced`. -/
def pointDegree {m : Nat} (s : SearchState m) (p : SearchPoint) : Nat :=
  (s.config.incidentBlocks p).card

/-- `pointDegree` is exactly the Levi-graph degree of the point vertex `Sum.inl p`, so the degree
bound of `StateInvariant` is the configuration's cubic point-degree bound and not a separate
notion.  The bridge is the `IncidenceConfig.degree_inl` of `Erdos.Erdos64.Incidence`. -/
theorem pointDegree_eq_leviDegree {m : Nat} (s : SearchState m) (p : SearchPoint) :
    pointDegree s p = s.config.leviGraph.degree (Sum.inl p) :=
  (IncidenceConfig.degree_inl s.config p).symm

/-- A point has positive degree exactly when it lies in some installed block.  This is the
direction used to recover an old-label bound from a positive degree: a candidate point of degree
`≥ 3` is necessarily in an old block, so `LabelsBelow` bounds its label. -/
theorem pointDegree_pos_iff {m : Nat} {s : SearchState m} {p : SearchPoint} :
    0 < pointDegree s p ↔ ∃ i : Fin m, p ∈ (s.blocks i).points := by
  rw [pointDegree, IncidenceConfig.incidentBlocks, SearchState.config, Finset.card_pos]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩

/-- Every label occurring in an installed block is strictly below `u`.  For `u = s.introduced`
this is the released checker's invariant that a label at or above `introduced` occurs in no
installed block, and it is what makes the old-label restriction of `structurally_invalid` sound. -/
def LabelsBelow {m : Nat} (s : SearchState m) (u : Fin 30) : Prop :=
  ∀ i p, p ∈ (s.blocks i).points → p.val < u.val

/-- Two points are *paired* when some installed block contains both of them.  This is the relation
the released `structurally_invalid` tests between two candidate labels below `introduced`. -/
def pairUsed {m : Nat} (s : SearchState m) (p q : SearchPoint) : Prop :=
  ∃ i : Fin m, p ∈ (s.blocks i).points ∧ q ∈ (s.blocks i).points

/-- The pairing relation is a finite existential, hence decidable; the instance is made explicit so
that `pairUsed` can appear under `decide` and under `if`. -/
instance instDecidablePairUsed {m : Nat} (s : SearchState m) (p q : SearchPoint) :
    Decidable (pairUsed s p q) :=
  inferInstanceAs (Decidable (∃ i : Fin m, p ∈ (s.blocks i).points ∧ q ∈ (s.blocks i).points))

/-- Unfolding of `pairUsed`. -/
theorem pairUsed_iff {m : Nat} (s : SearchState m) (p q : SearchPoint) :
    pairUsed s p q ↔ ∃ i : Fin m, p ∈ (s.blocks i).points ∧ q ∈ (s.blocks i).points :=
  Iff.rfl

/-- The pairing relation is symmetric. -/
theorem pairUsed_comm {m : Nat} (s : SearchState m) (p q : SearchPoint) :
    pairUsed s p q ↔ pairUsed s q p := by
  constructor <;> rintro ⟨i, hp, hq⟩ <;> exact ⟨i, hq, hp⟩

/-- A single installed block containing both points witnesses that they are paired. -/
theorem pairUsed_of_mem {m : Nat} {s : SearchState m} {i : Fin m} {p q : SearchPoint}
    (hp : p ∈ (s.blocks i).points) (hq : q ∈ (s.blocks i).points) : pairUsed s p q :=
  ⟨i, hp, hq⟩

/-- Both points of a used pair lie below any label bound of the state. -/
theorem pairUsed_labels_lt {m : Nat} {s : SearchState m} {u : Fin 30} (hbelow : LabelsBelow s u)
    {p q : SearchPoint} (h : pairUsed s p q) : p.val < u.val ∧ q.val < u.val := by
  obtain ⟨i, hp, hq⟩ := h
  exact ⟨hbelow i p hp, hbelow i q hq⟩

/-! ### The label discipline of the restricted-growth traversal -/

/-- The three properties the traversal maintains on the state: labels below `introduced`, point
degree at most `3`, and linearity.  Point degree `≤ 3` is the cubic bound; linearity is the
absence of a shared point pair (`Erdos.Erdos64.Incidence`). -/
def StateInvariant {m : Nat} (s : SearchState m) : Prop :=
  LabelsBelow s s.introduced ∧ (∀ p, pointDegree s p ≤ 3) ∧ s.config.IsLinear

/-- The state invariant is decidable: a label bound, a finite degree bound and linearity of a finite
configuration. -/
instance instDecidableStateInvariant {m : Nat} (s : SearchState m) :
    Decidable (StateInvariant s) := by
  unfold StateInvariant LabelsBelow IncidenceConfig.IsLinear
  infer_instance

/-- The candidate block `t` uses the label `n`. -/
def containsLabel (t : SearchBlock) (n : Nat) : Prop :=
  ∃ p, p ∈ t.points ∧ p.val = n

/-- Occurrence of a label in a block is a finite existential, hence decidable; the instance is made
explicit so that `containsLabel` can appear under `if` in `nextIntroducedNat`. -/
instance instDecidableContainsLabel (t : SearchBlock) (n : Nat) : Decidable (containsLabel t n) :=
  inferInstanceAs (Decidable (∃ p, p ∈ t.points ∧ p.val = n))

/-- A label occurs in the block exactly when it is the value of one of its points. -/
theorem containsLabel_iff {t : SearchBlock} {n : Nat} :
    containsLabel t n ↔ ∃ p ∈ t.points, p.val = n :=
  Iff.rfl

/-- A point of the block witnesses that its label occurs. -/
theorem containsLabel_of_mem {t : SearchBlock} {p : SearchPoint} (hp : p ∈ t.points) :
    containsLabel t p.val :=
  ⟨p, hp, rfl⟩

/-- The block does not use the label `n`. -/
theorem not_containsLabel_iff {t : SearchBlock} {n : Nat} :
    ¬ containsLabel t n ↔ ∀ p ∈ t.points, p.val ≠ n := by
  simp only [containsLabel, not_exists, not_and]

/-- **The exact restricted-growth fresh-label discipline.**  Every candidate label is at most
`u + 1`, and a candidate using the fresh label `u + 1` also uses the label `u`.  The second
conjunct is what forces the candidate's labels above `u` to form an initial segment: no candidate
may introduce `u + 1` while leaving `u` unused. -/
def CandidateDiscipline (u : Fin 30) (t : SearchBlock) : Prop :=
  (∀ p ∈ t.points, p.val ≤ u.val + 1) ∧ (containsLabel t (u.val + 1) → containsLabel t u.val)

/-- The fresh-label discipline is decidable. -/
instance instDecidableCandidateDiscipline (u : Fin 30) (t : SearchBlock) :
    Decidable (CandidateDiscipline u t) := by
  unfold CandidateDiscipline
  infer_instance

/-- The `Nat` counter update that the released `visit` computes and assigns before calling
`install`: the old counter value plus one indicator for each of the two labels that can be fresh,
namely `u` and `u + 1`.  It mirrors the update performed in `visit`, not any computation inside
the released `install`, which never advances the counter.  It is a plain `Nat` computation, not a
`Fin 30` one, precisely so that the `< 30` bound below is a real obligation rather than a wrapping
artefact. -/
def nextIntroducedNat (u : Fin 30) (t : SearchBlock) : Nat :=
  u.val + (if containsLabel t u.val then 1 else 0) +
    (if containsLabel t (u.val + 1) then 1 else 0)

/-- No fresh label: a candidate that uses neither `u` nor `u + 1` leaves the counter unchanged.
Discipline is needed only to exclude the label `u + 1` from a candidate that avoids `u`. -/
theorem nextIntroducedNat_eq_of_not_contains {u : Fin 30} {t : SearchBlock}
    (hdisc : CandidateDiscipline u t) (hu : ¬ containsLabel t u.val) :
    nextIntroducedNat u t = u.val := by
  have hu1 : ¬ containsLabel t (u.val + 1) := fun h => hu (hdisc.2 h)
  simp only [nextIntroducedNat, if_neg hu, if_neg hu1, Nat.add_zero]

/-- Exactly one fresh label: a candidate that uses `u` but not `u + 1` advances the counter by
one. -/
theorem nextIntroducedNat_eq_add_one {u : Fin 30} {t : SearchBlock}
    (_hdisc : CandidateDiscipline u t) (hu : containsLabel t u.val)
    (hu1 : ¬ containsLabel t (u.val + 1)) :
    nextIntroducedNat u t = u.val + 1 := by
  simp only [nextIntroducedNat, if_pos hu, if_neg hu1, Nat.add_zero]

/-- Two fresh labels: a candidate that uses `u + 1` — hence, by discipline, also `u` — advances
the counter by two. -/
theorem nextIntroducedNat_eq_add_two {u : Fin 30} {t : SearchBlock}
    (hdisc : CandidateDiscipline u t) (hu1 : containsLabel t (u.val + 1)) :
    nextIntroducedNat u t = u.val + 2 := by
  have hu : containsLabel t u.val := hdisc.2 hu1
  simp only [nextIntroducedNat, if_pos hu, if_pos hu1]

/-- The counter never decreases. -/
theorem le_nextIntroducedNat (u : Fin 30) (t : SearchBlock) :
    u.val ≤ nextIntroducedNat u t := by
  simp only [nextIntroducedNat]
  omega

/-- Every candidate label is strictly below the new counter value, so the label invariant is
preserved by the install.  This is the arithmetic core of `labelsBelow_install`. -/
theorem candidate_lt_nextIntroducedNat {u : Fin 30} {t : SearchBlock}
    (hdisc : CandidateDiscipline u t) : ∀ p ∈ t.points, p.val < nextIntroducedNat u t := by
  intro p hp
  have hle : p.val ≤ u.val + 1 := hdisc.1 p hp
  by_cases hu1 : containsLabel t (u.val + 1)
  · rw [nextIntroducedNat_eq_add_two hdisc hu1]
    omega
  · by_cases hu : containsLabel t u.val
    · rw [nextIntroducedNat_eq_add_one hdisc hu hu1]
      have hne : p.val ≠ u.val + 1 := fun heq => hu1 ⟨p, hp, heq⟩
      omega
    · rw [nextIntroducedNat_eq_of_not_contains hdisc hu]
      have hne : p.val ≠ u.val := fun heq => hu ⟨p, hp, heq⟩
      have hne1 : p.val ≠ u.val + 1 := fun heq => hu1 ⟨p, hp, heq⟩
      omega

/-- Under the discipline the counter update stays below `30`.  The three cases are the no-fresh,
one-fresh and two-fresh cases; in the two-fresh case a witness point of the label `u + 1` is a
point of `SearchPoint = Fin 29`, so `u + 2 ≤ 29`. -/
theorem nextIntroducedNat_lt_thirty {u : Fin 30} {t : SearchBlock}
    (hdisc : CandidateDiscipline u t) : nextIntroducedNat u t < 30 := by
  by_cases hu1 : containsLabel t (u.val + 1)
  · rw [nextIntroducedNat_eq_add_two hdisc hu1]
    obtain ⟨p, hp, hpval⟩ := hu1
    have hp29 : p.val < 29 := p.isLt
    omega
  · by_cases hu : containsLabel t u.val
    · rw [nextIntroducedNat_eq_add_one hdisc hu hu1]
      obtain ⟨p, hp, hpval⟩ := hu
      have hp29 : p.val < 29 := p.isLt
      omega
    · rw [nextIntroducedNat_eq_of_not_contains hdisc hu]
      exact u.isLt

/-- The new `introduced` count, packaged as a `Fin 30`.  It is a count of labels, not a point:
`SearchPoint` is `Fin 29` while `introduced` is `Fin 30`, and the discipline proof is exactly what
supplies the `< 30` obligation. -/
def nextIntroduced (u : Fin 30) (t : SearchBlock) (h : CandidateDiscipline u t) : Fin 30 :=
  ⟨nextIntroducedNat u t, nextIntroducedNat_lt_thirty h⟩

/-- The value of the packaged counter is the `Nat` computation. -/
@[simp]
theorem nextIntroduced_val (u : Fin 30) (t : SearchBlock) (h : CandidateDiscipline u t) :
    (nextIntroduced u t h).val = nextIntroducedNat u t :=
  rfl

/-! ### Clean structural validity and the released structural test -/

/-- The *mathematical* structural validity of a candidate: every candidate point has old degree
strictly below `3`, and no old block contains two distinct candidate points.  This is the
predicate the released `structurally_invalid` implements the negation of. -/
def CleanStructuralOK {m : Nat} (s : SearchState m) (t : SearchBlock) : Prop :=
  (∀ p ∈ t.points, pointDegree s p < 3) ∧
    ∀ p q, p ∈ t.points → q ∈ t.points → p ≠ q → ¬ pairUsed s p q

/-- Clean structural validity is decidable: it is a conjunction of two finite universal quantifiers
over decidable predicates. -/
instance instDecidableCleanStructuralOK {m : Nat} (s : SearchState m) (t : SearchBlock) :
    Decidable (CleanStructuralOK s t) := by
  unfold CleanStructuralOK
  infer_instance

/-- **The executable released structural test.**  This is `decide` of the disjunction the released
`structurally_invalid` computes: some candidate label below `oldIntroduced` has old degree at
least `3`, or some two distinct candidate labels below `oldIntroduced` are already paired in an
old block.  The `oldIntroduced` argument is the *old* counter value, so a caller that has already
installed blocks passes the counter of the state it is testing against. -/
def cppStructurallyInvalid {m : Nat} (s : SearchState m) (oldIntroduced : Nat)
    (t : SearchBlock) : Bool :=
  decide
    ((∃ p ∈ t.points, p.val < oldIntroduced ∧ 3 ≤ pointDegree s p) ∨
      (∃ p ∈ t.points, ∃ q ∈ t.points,
        p.val < oldIntroduced ∧ q.val < oldIntroduced ∧ p ≠ q ∧ pairUsed s p q))

/-- **The bridge from the released old-label-only test to the mathematical predicate.**  Under the
label invariant `LabelsBelow s s.introduced`, the released structural test rejects exactly the
candidates that are not clean:

`cppStructurallyInvalid s s.introduced.val t = true ↔ ¬ CleanStructuralOK s t`.

The hypothesis is used only in the completeness direction, and necessarily so: a candidate point
with old degree `≥ 3` lies in an old block, so by `LabelsBelow` its label is below `introduced`
and the released test does see it.  Without the label invariant the released test may skip such a
point, which is why the iff is stated under the invariant that the traversal maintains. -/
theorem cppStructurallyInvalid_iff {m : Nat} {s : SearchState m} {t : SearchBlock}
    (hbelow : LabelsBelow s s.introduced) :
    cppStructurallyInvalid s s.introduced.val t = true ↔ ¬ CleanStructuralOK s t := by
  rw [cppStructurallyInvalid, decide_eq_true_iff]
  constructor
  · rintro (⟨p, hp, _hlabel, hthree⟩ | ⟨p, hp, q, hq, _hplabel, _hqlabel, hpq, hused⟩) hclean
    · exact absurd (hclean.1 p hp) (by omega)
    · exact hclean.2 p q hp hq hpq hused
  · intro hnotclean
    classical
    by_cases hdeg : ∀ p ∈ t.points, pointDegree s p < 3
    · refine Or.inr ?_
      have hpair : ¬∀ p q, p ∈ t.points → q ∈ t.points → p ≠ q → ¬ pairUsed s p q :=
        fun hpairs => hnotclean ⟨hdeg, hpairs⟩
      push Not at hpair
      obtain ⟨p, q, hp, hq, hpq, hused⟩ := hpair
      obtain ⟨hplabel, hqlabel⟩ := pairUsed_labels_lt hbelow hused
      exact ⟨p, hp, q, hq, hplabel, hqlabel, hpq, hused⟩
    · refine Or.inl ?_
      push Not at hdeg
      obtain ⟨p, hp, hthree⟩ := hdeg
      have hpos : 0 < pointDegree s p := by omega
      obtain ⟨i, hi⟩ := pointDegree_pos_iff.mp hpos
      exact ⟨p, hp, hbelow i p hi, by omega⟩

/-- The executable state check: `decide` of `StateInvariant`. -/
def stateCheck {m : Nat} (s : SearchState m) : Bool :=
  decide (StateInvariant s)

/-- The state check accepts exactly the invariant states. -/
theorem stateCheck_iff {m : Nat} (s : SearchState m) :
    stateCheck s = true ↔ StateInvariant s :=
  decide_eq_true_iff

/-- The executable candidate check: discipline *and* clean structural validity.  Discipline is
deliberately not folded into `CleanStructuralOK` or into the released structural test; it is a
separate conjunct here, exactly as the fresh-label bookkeeping is separate from
`structurally_invalid` in the released checker. -/
def candidateCheck {m : Nat} (s : SearchState m) (t : SearchBlock) : Bool :=
  decide (CandidateDiscipline s.introduced t ∧ CleanStructuralOK s t)

/-- The candidate check accepts exactly the disciplined, clean candidates. -/
theorem candidateCheck_iff {m : Nat} (s : SearchState m) (t : SearchBlock) :
    candidateCheck s t = true ↔ CandidateDiscipline s.introduced t ∧ CleanStructuralOK s t :=
  decide_eq_true_iff

/-! ### The dependent install -/

/-- **Install one further block.**  This is the *combined functional post-validation expansion
transition*: the candidate is appended at the fresh index `Fin.last m`, the old blocks are
preserved through `Fin.castSucc`, and the `introduced` counter is advanced by the `Nat`
computation `nextIntroducedNat`.  The discipline proof is a genuine argument: it is what makes the
new counter value a `Fin 30`, and it is not derivable from the state alone.

It is deliberately **not** a transcription of the released C++ `install`.  The released `install`
re-validates the candidate itself — ordered and in-range points, degree `< 3` at each of them, no
pair of them already used — and then mutates the block, degree and pair arrays, and it never
touches `introduced`; the counter is computed and assigned by `visit` before `install` is called.
This function instead performs no validation of its own and covers both effects at once, so it
models the joint effect of that counter assignment and the released array mutation on reachable
states.  Its type therefore requires only `CandidateDiscipline s.introduced t`; clean structural
validity is a *separate* hypothesis of `degreeBound_install`, `linear_install` and
`stateInvariant_install`, and a candidate that is not clean can technically be passed here even
though the released `install` would refuse it. -/
def SearchState.install {m : Nat} (s : SearchState m) (t : SearchBlock)
    (h : CandidateDiscipline s.introduced t) : SearchState (m + 1) where
  blocks := Fin.lastCases t (fun i => s.blocks i)
  introduced := nextIntroduced s.introduced t h

/-- An old block is unchanged by the install. -/
@[simp]
theorem SearchState.install_blocks_castSucc {m : Nat} (s : SearchState m) (t : SearchBlock)
    (h : CandidateDiscipline s.introduced t) (i : Fin m) :
    (s.install t h).blocks i.castSucc = s.blocks i :=
  Fin.lastCases_castSucc (motive := fun _ => SearchBlock) i

/-- The fresh index carries the candidate. -/
@[simp]
theorem SearchState.install_blocks_last {m : Nat} (s : SearchState m) (t : SearchBlock)
    (h : CandidateDiscipline s.introduced t) :
    (s.install t h).blocks (Fin.last m) = t :=
  Fin.lastCases_last (motive := fun _ => SearchBlock)

/-- The installed counter is the packaged `nextIntroduced`. -/
@[simp]
theorem SearchState.install_introduced {m : Nat} (s : SearchState m) (t : SearchBlock)
    (h : CandidateDiscipline s.introduced t) :
    (s.install t h).introduced = nextIntroduced s.introduced t h :=
  rfl

/-- The configuration of the installed state is exactly `s.addConfig t`: appending the candidate at
the fresh index is one `addConfig` of the old configuration. -/
theorem install_config {m : Nat} (s : SearchState m) (t : SearchBlock)
    (h : CandidateDiscipline s.introduced t) :
    (s.install t h).config = s.addConfig t := by
  rw [IncidenceConfig.mk.injEq]
  funext i
  simp only [SearchState.config]
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [SearchState.install_blocks_castSucc, SearchState.addConfig_blocks_castSucc]
  · rw [SearchState.install_blocks_last, SearchState.addConfig_blocks_last]

/-! ### Exact accounting: degree and pairing after the install -/

/-- Cardinality of a filtered `Finset.univ` over `Fin (n + 1)`, split into the `castSucc` part and
the last index.  The two `Finset.card_filter` rewrites turn both cardinalities into indicator
sums, which `Fin.sum_univ_castSucc` then splits. -/
private theorem card_filter_univ_fin_succ {n : Nat} (pred : Fin (n + 1) → Prop)
    [DecidablePred pred] :
    (Finset.univ.filter pred).card =
      (Finset.univ.filter (fun i : Fin n => pred i.castSucc)).card +
        (if pred (Fin.last n) then 1 else 0) := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]

/-- **Exact degree accounting.**  Installing the candidate raises the degree of exactly the
candidate's points, by exactly one. -/
theorem pointDegree_install {m : Nat} (s : SearchState m) (t : SearchBlock)
    (h : CandidateDiscipline s.introduced t) (p : SearchPoint) :
    pointDegree (s.install t h) p = pointDegree s p + (if p ∈ t.points then 1 else 0) := by
  show (Finset.univ.filter fun b : Fin (m + 1) =>
      p ∈ ((s.install t h).blocks b).points).card =
    (Finset.univ.filter fun b : Fin m => p ∈ (s.blocks b).points).card +
      (if p ∈ t.points then 1 else 0)
  rw [card_filter_univ_fin_succ (n := m)
    (pred := fun b : Fin (m + 1) => p ∈ ((s.install t h).blocks b).points)]
  simp only [SearchState.install_blocks_castSucc, SearchState.install_blocks_last]

/-- **Exact pairing accounting.**  After the install, two points are paired exactly when they were
already paired in the old state or when both of them are points of the candidate. -/
theorem pairUsed_install_iff {m : Nat} (s : SearchState m) (t : SearchBlock)
    (h : CandidateDiscipline s.introduced t) (p q : SearchPoint) :
    pairUsed (s.install t h) p q ↔ pairUsed s p q ∨ (p ∈ t.points ∧ q ∈ t.points) := by
  constructor
  · rintro ⟨i, hp, hq⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · refine Or.inl ⟨j, ?_, ?_⟩
      · simpa only [SearchState.install_blocks_castSucc] using hp
      · simpa only [SearchState.install_blocks_castSucc] using hq
    · exact Or.inr ⟨by simpa only [SearchState.install_blocks_last] using hp,
        by simpa only [SearchState.install_blocks_last] using hq⟩
  · rintro (⟨i, hp, hq⟩ | ⟨hp, hq⟩)
    · refine ⟨i.castSucc, ?_, ?_⟩
      · simpa only [SearchState.install_blocks_castSucc] using hp
      · simpa only [SearchState.install_blocks_castSucc] using hq
    · exact ⟨Fin.last m, by simpa only [SearchState.install_blocks_last] using hp,
        by simpa only [SearchState.install_blocks_last] using hq⟩

/-! ### Preservation of the state invariant -/

/-- The label invariant is preserved: old blocks keep their old labels, which are below the old
counter value, and every candidate label is strictly below the new counter value. -/
theorem labelsBelow_install {m : Nat} (s : SearchState m) (t : SearchBlock)
    (h : CandidateDiscipline s.introduced t) (hbelow : LabelsBelow s s.introduced) :
    LabelsBelow (s.install t h) (s.install t h).introduced := by
  intro i p hp
  rw [SearchState.install_introduced, nextIntroduced_val]
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · have hold : p.val < s.introduced.val := by
      refine hbelow j p ?_
      simpa only [SearchState.install_blocks_castSucc] using hp
    exact lt_of_lt_of_le hold (le_nextIntroducedNat s.introduced t)
  · have hmem : p ∈ t.points := by
      simpa only [SearchState.install_blocks_last] using hp
    exact candidate_lt_nextIntroducedNat h p hmem

/-- The degree bound is preserved: a candidate point has old degree `< 3` by cleanliness, so the
install brings it to at most `3`, and every other point keeps its old degree. -/
theorem degreeBound_install {m : Nat} (s : SearchState m) (t : SearchBlock)
    (h : CandidateDiscipline s.introduced t) (hdeg : ∀ p, pointDegree s p ≤ 3)
    (hclean : CleanStructuralOK s t) : ∀ p, pointDegree (s.install t h) p ≤ 3 := by
  intro p
  rw [pointDegree_install s t h p]
  by_cases hp : p ∈ t.points
  · rw [if_pos hp]
    have hlt := hclean.1 p hp
    omega
  · rw [if_neg hp]
    exact hdeg p

/-- A shared point pair of `s.addConfig t` is either an old shared pair, or a distinct pair of
candidate points already paired in an old block.  This is the decomposition the linearity
preservation consumes; the reverse direction builds two *distinct* indices from a single used old
block `i` and the fresh index `Fin.last m`. -/
theorem hasSharedPair_addConfig {m : Nat} (s : SearchState m) (t : SearchBlock) :
    (s.addConfig t).HasSharedPair ↔
      s.config.HasSharedPair ∨
        ∃ p q : SearchPoint, p ≠ q ∧ p ∈ t.points ∧ q ∈ t.points ∧ pairUsed s p q := by
  constructor
  · rintro ⟨b₁, b₂, hbne, p, q, hpq, hpb₁, hpb₂, hqb₁, hqb₂⟩
    rcases Fin.eq_castSucc_or_eq_last b₁ with ⟨i₁, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last b₂ with ⟨i₂, rfl⟩ | rfl
      · refine Or.inl ⟨i₁, i₂, ?_, p, q, hpq, ?_, ?_, ?_, ?_⟩
        · exact fun heq => hbne (by rw [heq])
        · simpa only [SearchState.config, SearchState.addConfig_blocks_castSucc] using hpb₁
        · simpa only [SearchState.config, SearchState.addConfig_blocks_castSucc] using hpb₂
        · simpa only [SearchState.config, SearchState.addConfig_blocks_castSucc] using hqb₁
        · simpa only [SearchState.config, SearchState.addConfig_blocks_castSucc] using hqb₂
      · refine Or.inr ⟨p, q, hpq, ?_, ?_, i₁, ?_, ?_⟩
        · simpa only [SearchState.addConfig_blocks_last] using hpb₂
        · simpa only [SearchState.addConfig_blocks_last] using hqb₂
        · simpa only [SearchState.config, SearchState.addConfig_blocks_castSucc] using hpb₁
        · simpa only [SearchState.config, SearchState.addConfig_blocks_castSucc] using hqb₁
    · rcases Fin.eq_castSucc_or_eq_last b₂ with ⟨i₂, rfl⟩ | rfl
      · refine Or.inr ⟨p, q, hpq, ?_, ?_, i₂, ?_, ?_⟩
        · simpa only [SearchState.addConfig_blocks_last] using hpb₁
        · simpa only [SearchState.addConfig_blocks_last] using hqb₁
        · simpa only [SearchState.config, SearchState.addConfig_blocks_castSucc] using hpb₂
        · simpa only [SearchState.config, SearchState.addConfig_blocks_castSucc] using hqb₂
      · exact absurd rfl hbne
  · rintro (⟨i₁, i₂, hij, p, q, hpq, hpi₁, hpi₂, hqi₁, hqi₂⟩ |
      ⟨p, q, hpq, hpt, hqt, i, hpi, hqi⟩)
    · refine ⟨i₁.castSucc, i₂.castSucc, ?_, p, q, hpq, ?_, ?_, ?_, ?_⟩
      · exact fun heq => hij (Fin.castSucc_injective m heq)
      · simpa only [SearchState.config, SearchState.addConfig_blocks_castSucc] using hpi₁
      · simpa only [SearchState.config, SearchState.addConfig_blocks_castSucc] using hpi₂
      · simpa only [SearchState.config, SearchState.addConfig_blocks_castSucc] using hqi₁
      · simpa only [SearchState.config, SearchState.addConfig_blocks_castSucc] using hqi₂
    · refine ⟨i.castSucc, Fin.last m, ?_, p, q, hpq, ?_, ?_, ?_, ?_⟩
      · exact Fin.castSucc_ne_last i
      · simpa only [SearchState.config, SearchState.addConfig_blocks_castSucc] using hpi
      · simpa only [SearchState.addConfig_blocks_last] using hpt
      · simpa only [SearchState.config, SearchState.addConfig_blocks_castSucc] using hqi
      · simpa only [SearchState.addConfig_blocks_last] using hqt

/-- Linearity is preserved: the installed configuration is `s.addConfig t`, whose only new shared
pair would be an old block containing two distinct candidate points, which cleanliness excludes;
so the installed configuration has no shared pair, hence is linear. -/
theorem linear_install {m : Nat} (s : SearchState m) (t : SearchBlock)
    (h : CandidateDiscipline s.introduced t) (hlin : s.config.IsLinear)
    (hclean : CleanStructuralOK s t) : (s.install t h).config.IsLinear := by
  rw [install_config, IncidenceConfig.isLinear_iff_not_hasSharedPair, hasSharedPair_addConfig]
  rintro (hold | ⟨p, q, hpq, hpt, hqt, hused⟩)
  · exact (IncidenceConfig.isLinear_iff_not_hasSharedPair s.config).mp hlin hold
  · exact hclean.2 p q hpt hqt hpq hused

/-- **Full preservation.**  A state satisfying `StateInvariant` whose candidate is disciplined and
clean installs to a state satisfying `StateInvariant`. -/
theorem stateInvariant_install {m : Nat} (s : SearchState m) (t : SearchBlock)
    (hinv : StateInvariant s) (h : CandidateDiscipline s.introduced t)
    (hclean : CleanStructuralOK s t) : StateInvariant (s.install t h) := by
  obtain ⟨hbelow, hdeg, hlin⟩ := hinv
  exact ⟨labelsBelow_install s t h hbelow, degreeBound_install s t h hdeg hclean,
    linear_install s t h hlin hclean⟩

/-! ### Fixtures from the artifact's triangle-root orbit 1 -/

section Fixtures

/- The fixture decisions run `decide` over a nest of quantifiers and `Finset` filters; a little
more elaborator recursion depth than the default is needed.  This is an elaboration knob only: it
does not weaken any proof, which remains a kernel check of the computed `Decidable` instance. -/
set_option maxRecDepth 4000

/-- The artifact's orbit-1 state (`orbitOneState` of `Erdos.Erdos64.TriangleC8Kernel`) satisfies
the state invariant: the labels `0, …, 6` are below `introduced = 7`, no point has degree above
`3`, and the four installed blocks are pairwise at most one point apart. -/
theorem orbitOne_stateInvariant : StateInvariant orbitOneState := by
  decide

/-- The orbit-1 candidate `{1,5,6}` is disciplined at `introduced = 7`: all its labels are below
`7`, so in particular at most `8`, and it uses neither the fresh label `7` nor the fresh label
`8`. -/
theorem orbitOne_candidateDiscipline :
    CandidateDiscipline orbitOneState.introduced orbitOneCandidate := by
  decide

/-- The orbit-1 candidate is clean: the old degrees of `1`, `5`, `6` are `2`, `1`, `1`, and no old
block contains two of them. -/
theorem orbitOne_clean : CleanStructuralOK orbitOneState orbitOneCandidate := by
  decide

/-- The executable candidate check accepts the orbit-1 candidate. -/
theorem orbitOne_candidateCheck : candidateCheck orbitOneState orbitOneCandidate = true := by
  decide

/-- The executable state check accepts the orbit-1 state. -/
theorem orbitOne_stateCheck : stateCheck orbitOneState = true := by
  decide

/-- The released structural test does *not* reject the orbit-1 candidate, as the bridge
`cppStructurallyInvalid_iff` predicts from `orbitOne_clean`. -/
theorem orbitOne_cppStructurallyValid :
    cppStructurallyInvalid orbitOneState orbitOneState.introduced.val orbitOneCandidate = false := by
  rw [Bool.eq_false_iff]
  exact fun h => (cppStructurallyInvalid_iff orbitOne_stateInvariant.1).mp h orbitOne_clean

/-- Installing the orbit-1 candidate preserves the state invariant. -/
theorem orbitOne_installed_stateInvariant :
    StateInvariant (orbitOneState.install orbitOneCandidate orbitOne_candidateDiscipline) :=
  stateInvariant_install orbitOneState orbitOneCandidate orbitOne_stateInvariant
    orbitOne_candidateDiscipline orbitOne_clean

/-- The installed orbit-1 state passes the executable state check. -/
theorem orbitOne_installed_stateCheck :
    stateCheck (orbitOneState.install orbitOneCandidate orbitOne_candidateDiscipline) = true :=
  (stateCheck_iff _).mpr orbitOne_installed_stateInvariant

/-- **The structural test accepts while the `C₈` oracle rejects.**  The orbit-1 candidate passes
the structural layer — it is disciplined and clean — and is nevertheless rejected by the released
`C₈` witness oracle.  This matches the ordering of the released `visit`, which runs the structural
test before the `C₈`/`C₁₆` oracles and assigns the new `introduced` and calls `install` only once
both have cleared the candidate: the structural test is a *cheap necessary* filter, not a decision
procedure, and the cycle oracles do the rejecting.  The two facts are recorded here jointly so
that the separation of concerns is explicit. -/
theorem orbitOne_candidateAccepted_c8Rejected :
    candidateCheck orbitOneState orbitOneCandidate = true ∧
      c8Check orbitOneState orbitOneCandidate orbitOneIds = true :=
  ⟨orbitOne_candidateCheck, orbitOne_c8Check⟩

/-- A rejected fixture: the candidate `{1,2,6}` reuses the old pair `{1,2}` — the block `{1,2,4}`
contains both — so the released structural test rejects it. -/
def pairReuseCandidate : SearchBlock :=
  ⟨1, 2, 6, by decide, by decide⟩

/-- The pair-reusing candidate is not clean. -/
theorem pairReuse_not_clean : ¬ CleanStructuralOK orbitOneState pairReuseCandidate := by
  intro hclean
  exact hclean.2 1 2 (by decide) (by decide) (by decide)
    (pairUsed_of_mem (i := 1) (by decide) (by decide))

/-- The released structural test rejects the pair-reusing candidate. -/
theorem pairReuse_cppStructurallyInvalid :
    cppStructurallyInvalid orbitOneState orbitOneState.introduced.val pairReuseCandidate = true :=
  (cppStructurallyInvalid_iff orbitOne_stateInvariant.1).mpr pairReuse_not_clean

/-- The executable candidate check also rejects the pair-reusing candidate. -/
theorem pairReuse_candidateCheck :
    candidateCheck orbitOneState pairReuseCandidate = false := by
  decide

/-- A rejected fixture: the candidate `{0,5,6}` contains the point `0`, which already has degree
`3` in the orbit-1 state, so the released structural test rejects it on the degree test. -/
def degreeFullCandidate : SearchBlock :=
  ⟨0, 5, 6, by decide, by decide⟩

/-- The released structural test rejects the degree-filling candidate. -/
theorem degreeFull_cppStructurallyInvalid :
    cppStructurallyInvalid orbitOneState orbitOneState.introduced.val degreeFullCandidate = true :=
  (cppStructurallyInvalid_iff orbitOne_stateInvariant.1).mpr (by
    intro hclean
    exact absurd (hclean.1 0 (by decide)) (by decide))

end Fixtures

end Erdos64