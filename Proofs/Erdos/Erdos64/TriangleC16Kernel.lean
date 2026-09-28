/-
Erdős–Gyárfás problem 64 — the executable `C₁₆` certificate-checking kernel.

PROVENANCE.  arXiv:2608.02675, Julius Tranquilli, "A 60-Vertex Lower Bound for Cubic Bipartite
Counterexamples to the Erdős–Gyárfás Conjecture" (2 August 2026), Section 3.2 (the triangle-rooted
reduced search), Lemma `lem:c16` ("Incremental `C₁₆` oracle") and Figure `fig:c16-oracle`.  The
released artifact of the paper (`research/certificates/TRIANGLE_FORMAT.md`, the `EG58TRI1`
triangle-rooted certificate format, and its streaming checker
`research/src/verify_triangle_universal_certificate.cpp`, member function `check_c16_witness`)
records the on-the-wire shape of a single positive rejection witness: a `10` record carries an
*endpoint code* plus seven *old-block indices*, and the checker validates them against the state
that the deterministic traversal has regenerated up to that point.  Graphs here are finite,
undirected and simple; the paper's Berge length convention is `2 * k` for a Levi `C_{2k}`, so Berge
length `8` is the source's graph `C₁₆` and the Levi `C₁₆` proved below.

WHAT IS FORMALIZED HERE.  One *positive* `C₁₆` rejection witness, exactly as the artifact's
`check_c16_witness` accepts it, together with its soundness:

* `c16Endpoints t code` — the endpoint code of the `10` record.  It is a function
  `Fin 3 → SearchPoint × SearchPoint` selecting an ordered pair of the candidate block's points:
  code `0` gives `(a, b)`, code `1` gives `(a, c)` and code `2` gives `(b, c)`, matching the
  released checker's three endpoint cases exactly.  The two selected points are the *start* and
  the *finish* of the old path, hence the two neighbours of the new block on the `C₁₆`;
* `C16Witness s t code ids` — the payload predicate.  The seven indices `ids : Fin 7 → Fin m` are
  **old-block** indices (they index `s.blocks`, never the candidate `t`), they are injective, the
  selected start lies in the old block `ids 0`, the selected finish lies in the old block `ids 6`,
  and there are six intermediate points `p₁, …, p₆` whose six consecutive old-block intersections
  `old (ids 0) ∩ old (ids 1)`, `…`, `old (ids 5) ∩ old (ids 6)` are the singletons
  `{p₁}, …, {p₆}`, with `[start, p₁, p₂, p₃, p₄, p₅, p₆, finish]` nodup.  These are precisely the
  acceptance conditions of the artifact's `check_c16_witness`.  In particular the checker requires
  only *endpoint membership* `start ∈ old (ids 0)` and `finish ∈ old (ids 6)`; it does **not**
  require the intersections `t ∩ old (ids 0)` or `old (ids 6) ∩ t` to be singletons, and this
  predicate does not require it either.  The six bounded existential quantifiers are bounded by the
  corresponding three-point finsets (each bound is implied by the singleton equality that follows
  it), which keeps the kernel decision procedure small without changing the predicate;
* `c16Check s t code ids` — the executable Boolean check, `decide` of the witness predicate, with
  `c16Check_iff : c16Check s t code ids = true ↔ C16Witness s t code ids`;
* `C16Witness.hasBergeCycleLength` — the **semantic** soundness theorem: any accepted witness
  yields `(s.addConfig t).HasBergeCycleLength 8`, i.e. a genuine `SimpleGraph.Walk.IsCycle` of
  length `16` in the Levi graph of the extended configuration, walked in the order
  `new – start – old (ids 0) – p₁ – old (ids 1) – p₂ – old (ids 2) – p₃ – old (ids 3) – p₄ –
   old (ids 4) – p₅ – old (ids 5) – p₆ – old (ids 6) – finish – new`.  This is a real
  `Walk.IsCycle`, not a list-level informal cycle: every one of the sixteen incidences is proved
  from the endpoint memberships and the six singleton-intersection equations, and the sixteen
  vertices are pairwise distinct by the path-point nodup, injectivity of `ids`, the `Sum`-side
  separation and `Fin.castSucc_ne_last`.  Old indices are transported along `Fin.castSucc`; the
  candidate sits at `Fin.last m`;
* two documented fixtures.  `c16FixtureState` / `c16FixtureCandidate` / `c16FixtureIds` reproduce
  the **first `C₁₆` record of the official `tri_v29_o1.cert`**: the `13` installed blocks `{0,1,3}`,
  `{1,2,4}`, `{0,2,5}`, `{0,4,6}`, `{1,7,8}`, `{2,9,10}`, `{3,7,11}`, `{3,8,12}`, `{4,13,14}`,
  `{5,9,15}`, `{5,10,16}`, `{6,13,17}`, `{6,14,18}` with `introduced = 19`, the candidate
  `{7,15,17}`, the endpoint code `0` and the payload indices `(4, 0, 3, 1, 5, 10, 9)`;
  `c16Fixture_check`, `c16Fixture_witness` and `c16Fixture_hasBergeCycleLength` check it, turn it
  into the witness and derive the semantic Berge `C₁₆`.  `c16Fixture_repeatedIdCheck` and
  `c16Fixture_wrongCodeCheck` are negative fixtures (a repeated payload index, and an endpoint code
  whose finish is not in the last old block) proved by the same kernel `decide`;
* `decodeEndpointCode` — a raw decoder for endpoint codes `< 3`, with its acceptance and rejection
  characterisations.  No byte-level or tag-level parsing is attempted here: reading the raw
  certificate stream is later work.

TRUST BOUNDARY.  The endpoint code `code` and the seven block indices `ids` are the **untrusted**
`10` record payload read from the certificate; nothing about them is assumed beyond what
`C16Witness` checks.  The ordered state `s`, the candidate `t`, the point labels and the
`introduced` counter are *regenerated* runtime state, reproduced by the deterministic
restricted-growth traversal and by the state regeneration that this module does not formalize;
they are not read from the certificate.  What this module establishes is exactly the soundness
direction that makes such untrusted payloads safe: an accepted `C16Witness` really does exhibit a
Levi `C₁₆` of the extended configuration, so a stream that passes `c16Check` cannot be describing a
configuration free of Berge `C₁₆`.  Nothing is proved about the completeness of the check, and
nothing is proved about the traversal that regenerates `s` and `t`.  This module makes no novelty
claim: it is a formal restatement of the released checker's positive acceptance condition.

NOT FORMALIZED HERE.  No converse witness completeness (an existing Berge `C₁₆` need not be
reported by any payload), no state/candidate/point regeneration, no structural filtering (degree,
pair or linearity tests), no recursion or state-stack management, no header or `introduced`
counters, no certificate exhaustion or acceptance criterion, no root normalization or orbit
classification, no `60`-vertex lower bound (`thm:main`, `cor:bound`) and no Erdős–Gyárfás
conjecture.  This file is the `C₁₆` companion of the executable certificate-checking kernel of
`Erdos.Erdos64.TriangleC8Kernel`, and only its positive `C₁₆` soundness half.
-/

import Erdos.Erdos64.TriangleC8Kernel

set_option autoImplicit false

namespace Erdos64

/-! ### The endpoint code of a `10` record -/

/-- The endpoint code of a `10` record, as the released checker's `check_c16_witness` reads it: it
selects an ordered pair of the candidate block's points.  Code `0` selects `(t.a, t.b)`, code `1`
selects `(t.a, t.c)` and code `2` selects `(t.b, t.c)`.  The first component is the *start* and the
second the *finish* of the old path that the new block closes into a `C₁₆`. -/
def c16Endpoints (t : SearchBlock) : Fin 3 → SearchPoint × SearchPoint
  | 0 => (t.a, t.b)
  | 1 => (t.a, t.c)
  | 2 => (t.b, t.c)

/-- Endpoint code `0` selects `(a, b)`. -/
@[simp]
theorem c16Endpoints_zero (t : SearchBlock) : c16Endpoints t 0 = (t.a, t.b) := rfl

/-- Endpoint code `1` selects `(a, c)`. -/
@[simp]
theorem c16Endpoints_one (t : SearchBlock) : c16Endpoints t 1 = (t.a, t.c) := rfl

/-- Endpoint code `2` selects `(b, c)`. -/
@[simp]
theorem c16Endpoints_two (t : SearchBlock) : c16Endpoints t 2 = (t.b, t.c) := rfl

/-- The selected start point is a point of the candidate block. -/
theorem c16Endpoints_fst_mem (t : SearchBlock) (code : Fin 3) :
    (c16Endpoints t code).1 ∈ t.points := by
  fin_cases code <;> simp [c16Endpoints, SearchBlock.points]

/-- The selected finish point is a point of the candidate block. -/
theorem c16Endpoints_snd_mem (t : SearchBlock) (code : Fin 3) :
    (c16Endpoints t code).2 ∈ t.points := by
  fin_cases code <;> simp [c16Endpoints, SearchBlock.points]

/-! ### The `C₁₆` payload witness -/

/-- **The `C₁₆` rejection witness.**  The candidate block `t`, the endpoint code `code` and the
seven old-block indices `ids` exhibit a Berge `C₁₆` when

* the seven indices are injective (seven distinct old blocks, as the artifact's
  `check_c16_witness` requires);
* the selected start `(c16Endpoints t code).1` lies in the old block `ids 0` and the selected
  finish `(c16Endpoints t code).2` lies in the old block `ids 6` — only *membership* is required
  here, exactly as in the released checker, which does **not** ask `t ∩ old (ids 0)` or
  `old (ids 6) ∩ t` to be singletons;
* there are six points `p₁, …, p₆` such that the six consecutive old-block intersections
  `old (ids 0) ∩ old (ids 1)`, `old (ids 1) ∩ old (ids 2)`, `old (ids 2) ∩ old (ids 3)`,
  `old (ids 3) ∩ old (ids 4)`, `old (ids 4) ∩ old (ids 5)`, `old (ids 5) ∩ old (ids 6)` are the
  singletons `{p₁}, …, {p₆}`;
* `[start, p₁, p₂, p₃, p₄, p₅, p₆, finish]` is nodup.

Because the intersections are singleton *finsets*, two consecutive blocks sharing a repeated point
pair are rejected, matching the artifact's `intersection` failing on two common points.  Each of
the six quantifiers is bounded by a three-point finset (a bound implied by the singleton equality
that follows it), so the predicate does not change but its `Decidable` instance stays small.  The
predicate is a `Prop` with a purely finite, computable body, so `c16Check` below can `decide` it in
the kernel. -/
def C16Witness {m : Nat} (s : SearchState m) (t : SearchBlock) (code : Fin 3)
    (ids : Fin 7 → Fin m) : Prop :=
  Function.Injective ids ∧
    (c16Endpoints t code).1 ∈ (s.blocks (ids 0)).points ∧
    (c16Endpoints t code).2 ∈ (s.blocks (ids 6)).points ∧
    ∃ p1 ∈ (s.blocks (ids 0)).points, ∃ p2 ∈ (s.blocks (ids 1)).points,
    ∃ p3 ∈ (s.blocks (ids 2)).points, ∃ p4 ∈ (s.blocks (ids 3)).points,
    ∃ p5 ∈ (s.blocks (ids 4)).points, ∃ p6 ∈ (s.blocks (ids 5)).points,
      (s.blocks (ids 0)).points ∩ (s.blocks (ids 1)).points = {p1} ∧
      (s.blocks (ids 1)).points ∩ (s.blocks (ids 2)).points = {p2} ∧
      (s.blocks (ids 2)).points ∩ (s.blocks (ids 3)).points = {p3} ∧
      (s.blocks (ids 3)).points ∩ (s.blocks (ids 4)).points = {p4} ∧
      (s.blocks (ids 4)).points ∩ (s.blocks (ids 5)).points = {p5} ∧
      (s.blocks (ids 5)).points ∩ (s.blocks (ids 6)).points = {p6} ∧
      List.Nodup
        [(c16Endpoints t code).1, p1, p2, p3, p4, p5, p6, (c16Endpoints t code).2]

/-- The witness predicate is decidable: the point side is a finite `Fin`, the index side is a
finite `Fin`, and every field is a `Finset` equality, a `List.Nodup` or a disequality of finite
elements.  The instance is deliberately computable, so `c16Check` below reduces by kernel
evaluation and no `native_decide` escape is needed. -/
instance instDecidableC16Witness {m : Nat} (s : SearchState m) (t : SearchBlock)
    (code : Fin 3) (ids : Fin 7 → Fin m) : Decidable (C16Witness s t code ids) := by
  unfold C16Witness
  infer_instance

/-- The executable `C₁₆` check: `decide` of the witness predicate.  Because the point side is a
`Fin` and the intersections are `Finset` equalities, this reduces in the kernel without any
`native_decide` escape. -/
def c16Check {m : Nat} (s : SearchState m) (t : SearchBlock) (code : Fin 3)
    (ids : Fin 7 → Fin m) : Bool :=
  decide (C16Witness s t code ids)

/-- The executable check accepts exactly the witnesses. -/
theorem c16Check_iff {m : Nat} (s : SearchState m) (t : SearchBlock) (code : Fin 3)
    (ids : Fin 7 → Fin m) : c16Check s t code ids = true ↔ C16Witness s t code ids :=
  decide_eq_true_iff

/-- A point whose singleton is an intersection of two finsets lies in both. -/
private theorem mem_of_inter_eq_singleton {A B : Finset SearchPoint} {p : SearchPoint}
    (h : A ∩ B = {p}) : p ∈ A ∧ p ∈ B := by
  have hp : p ∈ A ∩ B := by
    rw [h]
    exact Finset.mem_singleton_self p
  exact Finset.mem_inter.mp hp

/-! ### Soundness: an accepted witness is a genuine Levi `C₁₆` -/

/-- **Soundness of the `C₁₆` check.**  An accepted witness produces a genuine simple cycle of
length `16` in the Levi graph of the extended configuration, namely

`new – start – old (ids 0) – p₁ – old (ids 1) – p₂ – old (ids 2) – p₃ – old (ids 3) – p₄ –
 old (ids 4) – p₅ – old (ids 5) – p₆ – old (ids 6) – finish – new`,

so `(s.addConfig t).HasBergeCycleLength 8`.  The two endpoint memberships and the six singleton
intersections give the sixteen incidences; injectivity of `ids`, `Fin.castSucc_ne_last` (the
candidate is a genuinely new index) and the nodup of the eight path points make the sixteen
vertices distinct, which is what makes the walk a cycle. -/
theorem C16Witness.hasBergeCycleLength {m : Nat} {s : SearchState m} {t : SearchBlock}
    {code : Fin 3} {ids : Fin 7 → Fin m} (w : C16Witness s t code ids) :
    (s.addConfig t).HasBergeCycleLength 8 := by
  obtain ⟨hids, hstart0, hfinish6, p1, -, p2, -, p3, -, p4, -, p5, -, p6, -,
    hinter01, hinter12, hinter23, hinter34, hinter45, hinter56, hnd⟩ := w
  have hp1 : p1 ∈ (s.blocks (ids 0)).points ∧ p1 ∈ (s.blocks (ids 1)).points :=
    mem_of_inter_eq_singleton hinter01
  have hp2 : p2 ∈ (s.blocks (ids 1)).points ∧ p2 ∈ (s.blocks (ids 2)).points :=
    mem_of_inter_eq_singleton hinter12
  have hp3 : p3 ∈ (s.blocks (ids 2)).points ∧ p3 ∈ (s.blocks (ids 3)).points :=
    mem_of_inter_eq_singleton hinter23
  have hp4 : p4 ∈ (s.blocks (ids 3)).points ∧ p4 ∈ (s.blocks (ids 4)).points :=
    mem_of_inter_eq_singleton hinter34
  have hp5 : p5 ∈ (s.blocks (ids 4)).points ∧ p5 ∈ (s.blocks (ids 5)).points :=
    mem_of_inter_eq_singleton hinter45
  have hp6 : p6 ∈ (s.blocks (ids 5)).points ∧ p6 ∈ (s.blocks (ids 6)).points :=
    mem_of_inter_eq_singleton hinter56
  -- the eight path points are pairwise distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, and_true,
    List.nodup_nil, not_or] at hnd
  obtain ⟨⟨hsp1, hsp2, hsp3, hsp4, hsp5, hsp6, hsf⟩,
    ⟨hp12, hp13, hp14, hp15, hp16, hpf⟩,
    ⟨hp23, hp24, hp25, hp26, hpf2⟩,
    ⟨hp34, hp35, hp36, hpf3⟩,
    ⟨hp45, hp46, hpf4⟩,
    ⟨hp56, hpf5⟩,
    hpf6⟩ := hnd
  -- the seven old-block indices are pairwise distinct
  have hI01 : ids 0 ≠ ids 1 := hids.ne (by decide)
  have hI02 : ids 0 ≠ ids 2 := hids.ne (by decide)
  have hI03 : ids 0 ≠ ids 3 := hids.ne (by decide)
  have hI04 : ids 0 ≠ ids 4 := hids.ne (by decide)
  have hI05 : ids 0 ≠ ids 5 := hids.ne (by decide)
  have hI06 : ids 0 ≠ ids 6 := hids.ne (by decide)
  have hI12 : ids 1 ≠ ids 2 := hids.ne (by decide)
  have hI13 : ids 1 ≠ ids 3 := hids.ne (by decide)
  have hI14 : ids 1 ≠ ids 4 := hids.ne (by decide)
  have hI15 : ids 1 ≠ ids 5 := hids.ne (by decide)
  have hI16 : ids 1 ≠ ids 6 := hids.ne (by decide)
  have hI23 : ids 2 ≠ ids 3 := hids.ne (by decide)
  have hI24 : ids 2 ≠ ids 4 := hids.ne (by decide)
  have hI25 : ids 2 ≠ ids 5 := hids.ne (by decide)
  have hI26 : ids 2 ≠ ids 6 := hids.ne (by decide)
  have hI34 : ids 3 ≠ ids 4 := hids.ne (by decide)
  have hI35 : ids 3 ≠ ids 5 := hids.ne (by decide)
  have hI36 : ids 3 ≠ ids 6 := hids.ne (by decide)
  have hI45 : ids 4 ≠ ids 5 := hids.ne (by decide)
  have hI46 : ids 4 ≠ ids 6 := hids.ne (by decide)
  have hI56 : ids 5 ≠ ids 6 := hids.ne (by decide)
  -- the transported block vertices are pairwise distinct
  have hB01 : (ids 0).castSucc ≠ (ids 1).castSucc := fun h => hI01 (Fin.castSucc_injective m h)
  have hB02 : (ids 0).castSucc ≠ (ids 2).castSucc := fun h => hI02 (Fin.castSucc_injective m h)
  have hB03 : (ids 0).castSucc ≠ (ids 3).castSucc := fun h => hI03 (Fin.castSucc_injective m h)
  have hB04 : (ids 0).castSucc ≠ (ids 4).castSucc := fun h => hI04 (Fin.castSucc_injective m h)
  have hB05 : (ids 0).castSucc ≠ (ids 5).castSucc := fun h => hI05 (Fin.castSucc_injective m h)
  have hB06 : (ids 0).castSucc ≠ (ids 6).castSucc := fun h => hI06 (Fin.castSucc_injective m h)
  have hB12 : (ids 1).castSucc ≠ (ids 2).castSucc := fun h => hI12 (Fin.castSucc_injective m h)
  have hB13 : (ids 1).castSucc ≠ (ids 3).castSucc := fun h => hI13 (Fin.castSucc_injective m h)
  have hB14 : (ids 1).castSucc ≠ (ids 4).castSucc := fun h => hI14 (Fin.castSucc_injective m h)
  have hB15 : (ids 1).castSucc ≠ (ids 5).castSucc := fun h => hI15 (Fin.castSucc_injective m h)
  have hB16 : (ids 1).castSucc ≠ (ids 6).castSucc := fun h => hI16 (Fin.castSucc_injective m h)
  have hB23 : (ids 2).castSucc ≠ (ids 3).castSucc := fun h => hI23 (Fin.castSucc_injective m h)
  have hB24 : (ids 2).castSucc ≠ (ids 4).castSucc := fun h => hI24 (Fin.castSucc_injective m h)
  have hB25 : (ids 2).castSucc ≠ (ids 5).castSucc := fun h => hI25 (Fin.castSucc_injective m h)
  have hB26 : (ids 2).castSucc ≠ (ids 6).castSucc := fun h => hI26 (Fin.castSucc_injective m h)
  have hB34 : (ids 3).castSucc ≠ (ids 4).castSucc := fun h => hI34 (Fin.castSucc_injective m h)
  have hB35 : (ids 3).castSucc ≠ (ids 5).castSucc := fun h => hI35 (Fin.castSucc_injective m h)
  have hB36 : (ids 3).castSucc ≠ (ids 6).castSucc := fun h => hI36 (Fin.castSucc_injective m h)
  have hB45 : (ids 4).castSucc ≠ (ids 5).castSucc := fun h => hI45 (Fin.castSucc_injective m h)
  have hB46 : (ids 4).castSucc ≠ (ids 6).castSucc := fun h => hI46 (Fin.castSucc_injective m h)
  have hB56 : (ids 5).castSucc ≠ (ids 6).castSucc := fun h => hI56 (Fin.castSucc_injective m h)
  have hB0N : (ids 0).castSucc ≠ Fin.last m := Fin.castSucc_ne_last _
  have hB1N : (ids 1).castSucc ≠ Fin.last m := Fin.castSucc_ne_last _
  have hB2N : (ids 2).castSucc ≠ Fin.last m := Fin.castSucc_ne_last _
  have hB3N : (ids 3).castSucc ≠ Fin.last m := Fin.castSucc_ne_last _
  have hB4N : (ids 4).castSucc ≠ Fin.last m := Fin.castSucc_ne_last _
  have hB5N : (ids 5).castSucc ≠ Fin.last m := Fin.castSucc_ne_last _
  have hB6N : (ids 6).castSucc ≠ Fin.last m := Fin.castSucc_ne_last _
  have estart : (c16Endpoints t code).1 ∈ t.points := c16Endpoints_fst_mem t code
  have efinish : (c16Endpoints t code).2 ∈ t.points := c16Endpoints_snd_mem t code
  -- the sixteen incidences
  have e0 : (s.addConfig t).leviGraph.Adj (Sum.inr (Fin.last m)) (Sum.inl (c16Endpoints t code).1) :=
    (IncidenceConfig.leviGraph_adj_inr_inl _ _ _).2 (by simpa using estart)
  have e1 : (s.addConfig t).leviGraph.Adj (Sum.inl (c16Endpoints t code).1)
      (Sum.inr (ids 0).castSucc) :=
    (IncidenceConfig.leviGraph_adj_inl_inr _ _ _).2 (by simpa using hstart0)
  have e2 : (s.addConfig t).leviGraph.Adj (Sum.inr (ids 0).castSucc) (Sum.inl p1) :=
    (IncidenceConfig.leviGraph_adj_inr_inl _ _ _).2 (by simpa using hp1.1)
  have e3 : (s.addConfig t).leviGraph.Adj (Sum.inl p1) (Sum.inr (ids 1).castSucc) :=
    (IncidenceConfig.leviGraph_adj_inl_inr _ _ _).2 (by simpa using hp1.2)
  have e4 : (s.addConfig t).leviGraph.Adj (Sum.inr (ids 1).castSucc) (Sum.inl p2) :=
    (IncidenceConfig.leviGraph_adj_inr_inl _ _ _).2 (by simpa using hp2.1)
  have e5 : (s.addConfig t).leviGraph.Adj (Sum.inl p2) (Sum.inr (ids 2).castSucc) :=
    (IncidenceConfig.leviGraph_adj_inl_inr _ _ _).2 (by simpa using hp2.2)
  have e6 : (s.addConfig t).leviGraph.Adj (Sum.inr (ids 2).castSucc) (Sum.inl p3) :=
    (IncidenceConfig.leviGraph_adj_inr_inl _ _ _).2 (by simpa using hp3.1)
  have e7 : (s.addConfig t).leviGraph.Adj (Sum.inl p3) (Sum.inr (ids 3).castSucc) :=
    (IncidenceConfig.leviGraph_adj_inl_inr _ _ _).2 (by simpa using hp3.2)
  have e8 : (s.addConfig t).leviGraph.Adj (Sum.inr (ids 3).castSucc) (Sum.inl p4) :=
    (IncidenceConfig.leviGraph_adj_inr_inl _ _ _).2 (by simpa using hp4.1)
  have e9 : (s.addConfig t).leviGraph.Adj (Sum.inl p4) (Sum.inr (ids 4).castSucc) :=
    (IncidenceConfig.leviGraph_adj_inl_inr _ _ _).2 (by simpa using hp4.2)
  have e10 : (s.addConfig t).leviGraph.Adj (Sum.inr (ids 4).castSucc) (Sum.inl p5) :=
    (IncidenceConfig.leviGraph_adj_inr_inl _ _ _).2 (by simpa using hp5.1)
  have e11 : (s.addConfig t).leviGraph.Adj (Sum.inl p5) (Sum.inr (ids 5).castSucc) :=
    (IncidenceConfig.leviGraph_adj_inl_inr _ _ _).2 (by simpa using hp5.2)
  have e12 : (s.addConfig t).leviGraph.Adj (Sum.inr (ids 5).castSucc) (Sum.inl p6) :=
    (IncidenceConfig.leviGraph_adj_inr_inl _ _ _).2 (by simpa using hp6.1)
  have e13 : (s.addConfig t).leviGraph.Adj (Sum.inl p6) (Sum.inr (ids 6).castSucc) :=
    (IncidenceConfig.leviGraph_adj_inl_inr _ _ _).2 (by simpa using hp6.2)
  have e14 : (s.addConfig t).leviGraph.Adj (Sum.inr (ids 6).castSucc)
      (Sum.inl (c16Endpoints t code).2) :=
    (IncidenceConfig.leviGraph_adj_inr_inl _ _ _).2 (by simpa using hfinish6)
  have e15 : (s.addConfig t).leviGraph.Adj (Sum.inl (c16Endpoints t code).2)
      (Sum.inr (Fin.last m)) :=
    (IncidenceConfig.leviGraph_adj_inl_inr _ _ _).2 (by simpa using efinish)
  -- the two halves of the cycle
  let mid : Sum SearchPoint (Fin (m + 1)) := Sum.inr (ids 3).castSucc
  let path₁ : (s.addConfig t).leviGraph.Walk (Sum.inr (Fin.last m)) mid :=
    .cons e0 (.cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 .nil)))))))
  let path₂ : (s.addConfig t).leviGraph.Walk mid (Sum.inr (Fin.last m)) :=
    .cons e8 (.cons e9 (.cons e10 (.cons e11 (.cons e12 (.cons e13 (.cons e14 (.cons e15 .nil)))))))
  have hpath₁ : path₁.IsPath := by
    simp [path₁, mid, hsp1, hsp2, hsp3, hp12, hp13, hp23,
      hB01, hB02, hB03, hB12, hB13, hB23, hB0N.symm, hB1N.symm, hB2N.symm, hB3N.symm]
  have hpath₂ : path₂.IsPath := by
    simp [path₂, mid, hp45, hp46, hpf4, hp56, hpf5, hpf6,
      hB34, hB35, hB36, hB45, hB46, hB56, hB3N, hB4N, hB5N, hB6N]
  have hdisj : path₁.support.tail.Disjoint path₂.support.tail := by
    simp [path₁, path₂, mid, List.disjoint_left,
      hsp4, hsp5, hsp6, hsf, hp14, hp15, hp16, hpf, hp24, hp25, hp26, hpf2,
      hp34, hp35, hp36, hpf3,
      hB04, hB05, hB06, hB14, hB15, hB16, hB24, hB25, hB26, hB34, hB35, hB36,
      hB0N, hB1N, hB2N, hB3N]
  refine (IncidenceConfig.hasBergeCycleLength_eight_iff (s.addConfig t)).mpr ?_
  refine ⟨Sum.inr (Fin.last m), path₁.append path₂, ?_, ?_⟩
  · exact SimpleGraph.Walk.IsPath.isCycle_append hpath₁ hpath₂ hdisj (Or.inl (by simp [path₁]))
  · simp [path₁, path₂]

/-! ### The artifact's `tri_v29_o1.cert` first `C₁₆` record -/

section Fixtures

/- The decision procedure for `C16Witness` is a nest of six bounded existential quantifiers, and
`decide` needs a little more elaborator recursion depth than the default to reduce it.  This is an
elaboration knob only: it does not weaken the proof, which remains a kernel check of the computed
`Decidable` instance (`of_decide_eq_true rfl`).  It is scoped to the fixture section. -/
set_option maxRecDepth 4000

/-- The thirteen blocks installed when the first `C₁₆` record of the official `tri_v29_o1.cert`
is emitted. -/
def c16FixtureBlocks : Fin 13 → SearchBlock :=
  ![⟨0, 1, 3, by decide, by decide⟩,
    ⟨1, 2, 4, by decide, by decide⟩,
    ⟨0, 2, 5, by decide, by decide⟩,
    ⟨0, 4, 6, by decide, by decide⟩,
    ⟨1, 7, 8, by decide, by decide⟩,
    ⟨2, 9, 10, by decide, by decide⟩,
    ⟨3, 7, 11, by decide, by decide⟩,
    ⟨3, 8, 12, by decide, by decide⟩,
    ⟨4, 13, 14, by decide, by decide⟩,
    ⟨5, 9, 15, by decide, by decide⟩,
    ⟨5, 10, 16, by decide, by decide⟩,
    ⟨6, 13, 17, by decide, by decide⟩,
    ⟨6, 14, 18, by decide, by decide⟩]

/-- The regenerated state of the first `C₁₆` record: thirteen installed blocks and `introduced`
`19`.  The `introduced` counter is regenerated runtime state; nothing here claims it bounds the
labels occurring in `blocks`. -/
def c16FixtureState : SearchState 13 where
  blocks := c16FixtureBlocks
  introduced := 19

/-- The candidate block `{7,15,17}` of the first `C₁₆` record. -/
def c16FixtureCandidate : SearchBlock :=
  ⟨7, 15, 17, by decide, by decide⟩

/-- The endpoint code `0` of the first `C₁₆` record, selecting the start `7` and the finish `15`. -/
def c16FixtureCode : Fin 3 := 0

/-- The payload of the first `C₁₆` record: the seven old-block indices `(4,0,3,1,5,10,9)`. -/
def c16FixtureIds : Fin 7 → Fin 13 :=
  ![4, 0, 3, 1, 5, 10, 9]

/-- The eight points of the witness path, in order: start `7`, the six intermediate points
`1, 0, 4, 2, 10, 5`, and the finish `15`.  They are pairwise distinct, as the released checker's
`nodup` requirement demands. -/
theorem c16Fixture_pathPoints :
    List.Nodup [(7 : SearchPoint), 1, 0, 4, 2, 10, 5, 15] := by
  decide

/-- The kernel check accepts the first `C₁₆` record of `tri_v29_o1.cert`. -/
theorem c16Fixture_check :
    c16Check c16FixtureState c16FixtureCandidate c16FixtureCode c16FixtureIds = true := by
  decide

/-- The accepted check is the witness predicate. -/
theorem c16Fixture_witness :
    C16Witness c16FixtureState c16FixtureCandidate c16FixtureCode c16FixtureIds :=
  (c16Check_iff c16FixtureState c16FixtureCandidate c16FixtureCode c16FixtureIds).mp
    c16Fixture_check

/-- The first `C₁₆` record really is a Berge `C₁₆` of the extended configuration: the Levi cycle
`{7,15,17} – 7 – {1,7,8} – 1 – {0,1,3} – 0 – {0,4,6} – 4 – {1,2,4} – 2 – {2,9,10} – 10 –
 {5,10,16} – 5 – {5,9,15} – 15 – {7,15,17}`. -/
theorem c16Fixture_hasBergeCycleLength :
    (c16FixtureState.addConfig c16FixtureCandidate).HasBergeCycleLength 8 :=
  c16Fixture_witness.hasBergeCycleLength

/-- A negative fixture: the payload `(4,0,3,1,5,10,10)` repeats the last old-block index, so the
released `check_c16_witness` rejects it and so does the kernel check. -/
def c16FixtureRepeatedIds : Fin 7 → Fin 13 :=
  ![4, 0, 3, 1, 5, 10, 10]

/-- The repeated-index payload is rejected. -/
theorem c16Fixture_repeatedIdCheck :
    c16Check c16FixtureState c16FixtureCandidate c16FixtureCode c16FixtureRepeatedIds = false := by
  decide

/-- A negative fixture: the endpoint code `1` selects the start `7` and the finish `17`, but `17`
is not a point of the last old block `{5,9,15}`, so the released `check_c16_witness` rejects the
record and so does the kernel check. -/
theorem c16Fixture_wrongCodeCheck :
    c16Check c16FixtureState c16FixtureCandidate 1 c16FixtureIds = false := by
  decide

end Fixtures

/-! ### Raw endpoint-code decoding -/

/-- Decode a raw `Nat` endpoint code: accept it only when it is one of the three endpoint codes
`0`, `1`, `2`.  This is the released checker's endpoint-code guard lifted to a total function.
Byte- and tag-level parsing of the certificate stream is not part of this module. -/
def decodeEndpointCode (n : Nat) : Option (Fin 3) :=
  if h : n < 3 then some ⟨n, h⟩ else none

/-- A raw endpoint code decodes to `c` exactly when it *is* `c`. -/
theorem decodeEndpointCode_eq_some_iff {n : Nat} {c : Fin 3} :
    decodeEndpointCode n = some c ↔ n = c := by
  unfold decodeEndpointCode
  split
  · rename_i h
    rw [Option.some.injEq, Fin.ext_iff]
  · rename_i h
    refine ⟨fun hh => absurd hh (by simp), fun hh => absurd h (by omega)⟩

/-- A raw endpoint code is rejected exactly when it is out of range. -/
theorem decodeEndpointCode_eq_none_iff {n : Nat} :
    decodeEndpointCode n = none ↔ 3 ≤ n := by
  unfold decodeEndpointCode
  split
  · rename_i h
    exact iff_of_false (by simp) (by omega)
  · rename_i h
    exact iff_of_true rfl (by omega)

end Erdos64