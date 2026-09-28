/-
Erdős–Gyárfás problem 64 — the executable `C₈` certificate-checking kernel.

PROVENANCE.  arXiv:2608.02675, Julius Tranquilli, "A 60-Vertex Lower Bound for Cubic Bipartite
Counterexamples to the Erdős–Gyárfás Conjecture" (2 August 2026), Section 3.2 (the triangle-rooted
reduced search).  The released artifact of the paper
(`research/certificates/TRIANGLE_FORMAT.md`, the `EG58TRI1` triangle-rooted certificate format, and
its streaming checker `research/src/verify_triangle_universal_certificate.cpp`, member function
`check_c8_witness`) records the on-the-wire shape of a single positive rejection witness: a `08`
record carries the three old-block indices of a `C₈` witness for the candidate block that the
checker is about to install.  Graphs here are finite, undirected and simple; the paper's Berge
length convention is `2 * k` for a Levi `C_{2k}` (so Berge length `4` is the source's graph `C₈`).

WHAT IS FORMALIZED HERE.  One *positive* `C₈` rejection witness, exactly as the artifact's
`check_c8_witness` accepts it, together with its soundness:

* `SearchPoint`, `SearchBlock` (an ordered, strictly increasing triple of the `29` candidate
  points) and `SearchBlock.points` — the finite labelled representation the checker walks over;
* `SearchState m` (the ordered list of already-installed blocks plus the `introduced` point
  counter) with `SearchState.config`, its reading as an `IncidenceConfig`, and
  `SearchState.addConfig`, which installs one further block at the new index `Fin.last m` while
  preserving the old block indices through `Fin.castSucc`.  The module makes **no** claim that
  `introduced` bounds the labels occurring in `blocks`: that bookkeeping belongs to the state
  regeneration that is not part of this kernel;
* `C8Witness s t ids` — the payload predicate: the three old-block indices `ids` are injective, the
  four consecutive intersections `t ∩ old (ids 0)`, `old (ids 0) ∩ old (ids 1)`,
  `old (ids 1) ∩ old (ids 2)`, `old (ids 2) ∩ t` are each a *singleton* `{p₀}`, `{p₁}`, `{p₂}`,
  `{p₃}`, and `p₀, p₁, p₂, p₃` are pairwise distinct.  This is precisely the acceptance condition
  of the artifact's `check_c8_witness`;
* `c8Check s t ids` — the executable Boolean check, `decide` of the witness predicate, with
  `c8Check_iff : c8Check s t ids = true ↔ C8Witness s t ids`;
* `C8Witness.hasBergeCycleLength` — the **semantic** soundness theorem: any accepted witness
  yields `(s.addConfig t).HasBergeCycleLength 4`, i.e. a genuine `SimpleGraph.Walk.IsCycle` of
  length `8` in the Levi graph of the extended configuration, walked in the order
  `new – p₀ – old (ids 0) – p₁ – old (ids 1) – p₂ – old (ids 2) – p₃ – new`.  This is a real
  `Walk.IsCycle`, not a list-level informal cycle;
* two documented fixtures.  `orbitOneState` / `orbitOneCandidate` / `orbitOneIds` reproduce the
  first positive `C₈` rejection of the artifact's triangle-root orbit 1 — the installed blocks
  `{0,1,3}`, `{1,2,4}`, `{0,2,5}`, `{0,4,6}`, `introduced = 7`, the candidate `{1,5,6}` and the
  payload indices `(1,2,3)` — and `orbitOne_c8Check`, `orbitOne_c8Witness`,
  `orbitOne_hasBergeCycleLength` check it, turn it into the witness, and derive the semantic
  Berge `C₈`.  `repeatedIdsCheck` and `misorderedIdsCheck` are negative fixtures (a repeated
  payload index, and an index triple whose intersections are not four distinct singletons) proved
  by the same kernel `decide`;
* `decodeBlockIndex` — a raw-index decoding helper that accepts a `Nat` only when it is `< m`,
  with its acceptance and rejection characterisations.  No byte-level or tag-level parsing is
  attempted here: reading the raw certificate stream is later work.

TRUST BOUNDARY.  The ordered state `s` and the candidate `t` are inputs that will eventually be
*regenerated* by the deterministic restricted-growth traversal; the payload `ids` is **untrusted**
data read from the certificate.  What this module establishes is exactly the soundness direction
that makes such untrusted payloads safe: an accepted `C8Witness` really does exhibit a Levi `C₈` of
the extended configuration, so a stream that passes `c8Check` cannot be describing a configuration
free of Berge `C₈`.  Nothing is proved about the completeness of the check, and nothing is proved
about the traversal that produces `s`, `t` and `ids`.

NOT FORMALIZED HERE.  No converse completeness (an existing Berge `C₈` need not be reported by any
payload), no structural candidate generation, no `C₁₆` checker, no recursion or state-stack
management, no header counters, no root normalization or orbit classification, no certificate
exhaustion or acceptance criterion, no `60`-vertex lower bound (`thm:main`, `cor:bound`) and no
Erdős–Gyárfás conjecture.  This file is the first executable certificate-checking kernel of the
search, and only its positive `C₈` soundness half.
-/

import Erdos.Erdos64.CertificateReduction

set_option autoImplicit false

namespace Erdos64

/-! ### The finite labelled representation -/

/-- The `29` candidate points of the artifact's triangle-rooted search, modelled as regenerated
point labels.  `SearchPoint := Fin 29` is the *point* side of the search, not a payload encoding:
a `08` payload's three bytes are *old-block* indices, represented later in this file by `Fin m` and
range-checked against the current old-block count, which is why both sides are `Fin` rather than
`Nat`. -/
abbrev SearchPoint := Fin 29

/-- A block of the search: three candidate points in strictly increasing order, so that every block
has a unique representation and the artifact's "install only an ordered block" invariant is
structural rather than a side condition. -/
structure SearchBlock where
  /-- The least point of the block. -/
  a : SearchPoint
  /-- The middle point of the block. -/
  b : SearchPoint
  /-- The greatest point of the block. -/
  c : SearchPoint
  /-- Strict increase, first step. -/
  hab : a < b
  /-- Strict increase, second step. -/
  hbc : b < c

/-- The three-point finset carried by a block. -/
def SearchBlock.points (t : SearchBlock) : Finset SearchPoint :=
  {t.a, t.b, t.c}

/-- Membership in a block, in the order the block stores its points. -/
@[simp]
theorem SearchBlock.mem_points {t : SearchBlock} {p : SearchPoint} :
    p ∈ t.points ↔ p = t.a ∨ p = t.b ∨ p = t.c := by
  simp [SearchBlock.points]

/-- An ordered search state: the blocks installed so far, indexed by `Fin m` in installation
order, together with the number of points introduced so far.  The `introduced` count is *regenerated
runtime state* maintained by the artifact's checker and traversal; it is not a per-state field of
the `TRIANGLE_FORMAT` wire stream, and this module proves nothing about it — in particular it does
**not** claim that it bounds the labels occurring in `blocks`. -/
structure SearchState (m : Nat) where
  /-- The installed blocks, in installation order. -/
  blocks : Fin m → SearchBlock
  /-- The number of points introduced so far. -/
  introduced : Fin 30

/-- The incidence configuration read off a search state: the block indexed by `i` is the three-point
set of `s.blocks i`. -/
def SearchState.config {m : Nat} (s : SearchState m) : IncidenceConfig SearchPoint (Fin m) :=
  ⟨fun i => (s.blocks i).points⟩

/-- Install one further block.  The old block indices are preserved through `Fin.castSucc` and the
new block sits at the fresh index `Fin.last m`, so the resulting configuration is the old one with
one block appended. -/
def SearchState.addConfig {m : Nat} (s : SearchState m) (t : SearchBlock) :
    IncidenceConfig SearchPoint (Fin (m + 1)) :=
  ⟨Fin.lastCases t.points (fun i => (s.blocks i).points)⟩

/-- The block at an old index is unchanged by `addConfig`. -/
@[simp]
theorem SearchState.addConfig_blocks_castSucc {m : Nat} (s : SearchState m) (t : SearchBlock)
    (i : Fin m) : (s.addConfig t).blocks i.castSucc = (s.blocks i).points :=
  Fin.lastCases_castSucc (motive := fun _ => Finset SearchPoint) i

/-- The new index of `addConfig` carries the candidate block. -/
@[simp]
theorem SearchState.addConfig_blocks_last {m : Nat} (s : SearchState m) (t : SearchBlock) :
    (s.addConfig t).blocks (Fin.last m) = t.points :=
  Fin.lastCases_last (motive := fun _ => Finset SearchPoint)

/-! ### The `C₈` payload witness -/

/-- **The `C₈` rejection witness.**  The candidate block `t` together with the three old-block
indices `ids` exhibit a Berge `C₈` when

* the three indices are injective (three distinct old blocks, as the artifact's
  `check_c8_witness` requires);
* there are four points `p₀, p₁, p₂, p₃` such that the consecutive intersections
  `t ∩ old (ids 0)`, `old (ids 0) ∩ old (ids 1)`, `old (ids 1) ∩ old (ids 2)` and
  `old (ids 2) ∩ t` are the singletons `{p₀}`, `{p₁}`, `{p₂}`, `{p₃}`;
* those four points are pairwise distinct.

The four singleton equalities are exactly the artifact's four `intersection(...)` values being
unique common points, and the pairwise distinctness is exactly the artifact's "four distinct
consecutive intersection points".  Because the intersections are singleton *finsets*, a repeated
point pair (two points shared by both blocks) is rejected as well, matching the artifact's
`intersection` returning a failure code for two common points.  The four quantifiers are bounded by
the corresponding finsets (`p₀ ∈ t.points`, `p₁ ∈ old (ids 0)`, …); those bounds are implied by the
singleton equalities that follow them, so they do not change the predicate, but they keep the
kernel decision procedure small.  The predicate is a `Prop` with a purely finite, computable body,
so `c8Check` below can `decide` it in the kernel. -/
def C8Witness {m : Nat} (s : SearchState m) (t : SearchBlock) (ids : Fin 3 → Fin m) : Prop :=
  Function.Injective ids ∧
    ∃ p0 ∈ t.points, ∃ p1 ∈ (s.blocks (ids 0)).points,
      ∃ p2 ∈ (s.blocks (ids 1)).points, ∃ p3 ∈ (s.blocks (ids 2)).points,
        t.points ∩ (s.blocks (ids 0)).points = {p0} ∧
        (s.blocks (ids 0)).points ∩ (s.blocks (ids 1)).points = {p1} ∧
        (s.blocks (ids 1)).points ∩ (s.blocks (ids 2)).points = {p2} ∧
        (s.blocks (ids 2)).points ∩ t.points = {p3} ∧
        p0 ≠ p1 ∧ p0 ≠ p2 ∧ p0 ≠ p3 ∧ p1 ≠ p2 ∧ p1 ≠ p3 ∧ p2 ≠ p3

/-- The witness predicate is decidable: the point side is a finite `Fin`, the index side is a
finite `Fin`, and every field is a `Finset` equality or a disequality of finite elements.  The
instance is deliberately computable, so `c8Check` below reduces by kernel evaluation and no
`native_decide` escape is needed. -/
instance instDecidableC8Witness {m : Nat} (s : SearchState m) (t : SearchBlock)
    (ids : Fin 3 → Fin m) : Decidable (C8Witness s t ids) := by
  unfold C8Witness
  infer_instance

/-- The executable `C₈` check: `decide` of the witness predicate.  Because the point side is a
`Fin` and the intersections are `Finset` equalities, this reduces in the kernel without any
`native_decide` escape. -/
def c8Check {m : Nat} (s : SearchState m) (t : SearchBlock) (ids : Fin 3 → Fin m) : Bool :=
  decide (C8Witness s t ids)

/-- The executable check accepts exactly the witnesses. -/
theorem c8Check_iff {m : Nat} (s : SearchState m) (t : SearchBlock) (ids : Fin 3 → Fin m) :
    c8Check s t ids = true ↔ C8Witness s t ids :=
  decide_eq_true_iff

/-- A point whose singleton is an intersection of two finsets lies in both. -/
private theorem mem_of_inter_eq_singleton {A B : Finset SearchPoint} {p : SearchPoint}
    (h : A ∩ B = {p}) : p ∈ A ∧ p ∈ B := by
  have hp : p ∈ A ∩ B := by
    rw [h]
    exact Finset.mem_singleton_self p
  exact Finset.mem_inter.mp hp

/-- The three payload indices of an accepted witness are pairwise distinct. -/
theorem C8Witness.ids_zero_ne_one {m : Nat} {s : SearchState m} {t : SearchBlock}
    {ids : Fin 3 → Fin m} (w : C8Witness s t ids) : ids 0 ≠ ids 1 :=
  w.1.ne (by decide)

theorem C8Witness.ids_zero_ne_two {m : Nat} {s : SearchState m} {t : SearchBlock}
    {ids : Fin 3 → Fin m} (w : C8Witness s t ids) : ids 0 ≠ ids 2 :=
  w.1.ne (by decide)

theorem C8Witness.ids_one_ne_two {m : Nat} {s : SearchState m} {t : SearchBlock}
    {ids : Fin 3 → Fin m} (w : C8Witness s t ids) : ids 1 ≠ ids 2 :=
  w.1.ne (by decide)

/-! ### Soundness: an accepted witness is a genuine Levi `C₈` -/

/-- **Soundness of the `C₈` check.**  An accepted witness produces a genuine simple cycle of length
`8` in the Levi graph of the extended configuration, namely

`new – p₀ – old (ids 0) – p₁ – old (ids 1) – p₂ – old (ids 2) – p₃ – new`,

so `(s.addConfig t).HasBergeCycleLength 4`.  The four singleton intersections give the eight
incidences; injectivity of `ids`, `Fin.castSucc_ne_last` (the candidate is a genuinely new index)
and the pairwise distinctness of the four points make the eight vertices distinct, which is what
makes the walk a cycle. -/
theorem C8Witness.hasBergeCycleLength {m : Nat} {s : SearchState m} {t : SearchBlock}
    {ids : Fin 3 → Fin m} (w : C8Witness s t ids) :
    (s.addConfig t).HasBergeCycleLength 4 := by
  obtain ⟨hids, p0, -, p1, -, p2, -, p3, -, h0, h1, h2, h3, hp01, hp02, hp03, hp12, hp13, hp23⟩ :=
    w
  have hm0 : p0 ∈ t.points ∧ p0 ∈ (s.blocks (ids 0)).points :=
    mem_of_inter_eq_singleton h0
  have hm1 : p1 ∈ (s.blocks (ids 0)).points ∧ p1 ∈ (s.blocks (ids 1)).points :=
    mem_of_inter_eq_singleton h1
  have hm2 : p2 ∈ (s.blocks (ids 1)).points ∧ p2 ∈ (s.blocks (ids 2)).points :=
    mem_of_inter_eq_singleton h2
  have hm3 : p3 ∈ (s.blocks (ids 2)).points ∧ p3 ∈ t.points :=
    mem_of_inter_eq_singleton h3
  have hI01 : ids 0 ≠ ids 1 := hids.ne (by decide)
  have hI02 : ids 0 ≠ ids 2 := hids.ne (by decide)
  have hI12 : ids 1 ≠ ids 2 := hids.ne (by decide)
  have hB01 : (ids 0).castSucc ≠ (ids 1).castSucc :=
    fun h => hI01 (Fin.castSucc_injective m h)
  have hB02 : (ids 0).castSucc ≠ (ids 2).castSucc :=
    fun h => hI02 (Fin.castSucc_injective m h)
  have hB12 : (ids 1).castSucc ≠ (ids 2).castSucc :=
    fun h => hI12 (Fin.castSucc_injective m h)
  have hB0N : (ids 0).castSucc ≠ Fin.last m := Fin.castSucc_ne_last _
  have hB1N : (ids 1).castSucc ≠ Fin.last m := Fin.castSucc_ne_last _
  have hB2N : (ids 2).castSucc ≠ Fin.last m := Fin.castSucc_ne_last _
  have e0 : (s.addConfig t).leviGraph.Adj (Sum.inr (Fin.last m)) (Sum.inl p0) :=
    (IncidenceConfig.leviGraph_adj_inr_inl _ _ _).2 (by simpa using hm0.1)
  have e1 : (s.addConfig t).leviGraph.Adj (Sum.inl p0) (Sum.inr (ids 0).castSucc) :=
    (IncidenceConfig.leviGraph_adj_inl_inr _ _ _).2 (by simpa using hm0.2)
  have e2 : (s.addConfig t).leviGraph.Adj (Sum.inr (ids 0).castSucc) (Sum.inl p1) :=
    (IncidenceConfig.leviGraph_adj_inr_inl _ _ _).2 (by simpa using hm1.1)
  have e3 : (s.addConfig t).leviGraph.Adj (Sum.inl p1) (Sum.inr (ids 1).castSucc) :=
    (IncidenceConfig.leviGraph_adj_inl_inr _ _ _).2 (by simpa using hm1.2)
  have e4 : (s.addConfig t).leviGraph.Adj (Sum.inr (ids 1).castSucc) (Sum.inl p2) :=
    (IncidenceConfig.leviGraph_adj_inr_inl _ _ _).2 (by simpa using hm2.1)
  have e5 : (s.addConfig t).leviGraph.Adj (Sum.inl p2) (Sum.inr (ids 2).castSucc) :=
    (IncidenceConfig.leviGraph_adj_inl_inr _ _ _).2 (by simpa using hm2.2)
  have e6 : (s.addConfig t).leviGraph.Adj (Sum.inr (ids 2).castSucc) (Sum.inl p3) :=
    (IncidenceConfig.leviGraph_adj_inr_inl _ _ _).2 (by simpa using hm3.1)
  have e7 : (s.addConfig t).leviGraph.Adj (Sum.inl p3) (Sum.inr (Fin.last m)) :=
    (IncidenceConfig.leviGraph_adj_inl_inr _ _ _).2 (by simpa using hm3.2)
  let mid : Sum SearchPoint (Fin (m + 1)) := Sum.inr (ids 1).castSucc
  let path₁ : (s.addConfig t).leviGraph.Walk (Sum.inr (Fin.last m)) mid :=
    .cons e0 (.cons e1 (.cons e2 (.cons e3 .nil)))
  let path₂ : (s.addConfig t).leviGraph.Walk mid (Sum.inr (Fin.last m)) :=
    .cons e4 (.cons e5 (.cons e6 (.cons e7 .nil)))
  have hpath₁ : path₁.IsPath := by
    simp [path₁, mid, hp01, hB01, hB0N.symm, hB1N.symm]
  have hpath₂ : path₂.IsPath := by
    simp [path₂, mid, hp23, hB12, hB1N, hB2N]
  have hdisj : path₁.support.tail.Disjoint path₂.support.tail := by
    simp [path₁, path₂, mid, List.disjoint_left,
      hp02, hp03, hp12, hp13, hB02, hB12, hB0N, hB1N]
  refine (IncidenceConfig.hasBergeCycleLength_four_iff (s.addConfig t)).mpr ?_
  refine ⟨Sum.inr (Fin.last m), path₁.append path₂, ?_, ?_⟩
  · exact SimpleGraph.Walk.IsPath.isCycle_append hpath₁ hpath₂ hdisj (Or.inl (by simp [path₁]))
  · simp [path₁, path₂]

/-! ### The artifact's triangle-root orbit 1 fixture -/

section Fixtures

/- The decision procedure for `C8Witness` is a nest of four bounded existential quantifiers, and
`decide` needs a little more elaborator recursion depth than the default to reduce it.  This is an
elaboration knob only: it does not weaken the proof, which remains a kernel check of the computed
`Decidable` instance (`of_decide_eq_true rfl`).  It is scoped to the fixture section. -/
set_option maxRecDepth 4000

/-- The four blocks installed at the start of the artifact's triangle-root orbit 1: the root
triangle `{0,1,3}`, `{1,2,4}`, `{0,2,5}` followed by the orbit-1 block `{0,4,6}`. -/
def orbitOneBlocks : Fin 4 → SearchBlock :=
  ![⟨0, 1, 3, by decide, by decide⟩,
    ⟨1, 2, 4, by decide, by decide⟩,
    ⟨0, 2, 5, by decide, by decide⟩,
    ⟨0, 4, 6, by decide, by decide⟩]

/-- The orbit-1 search state: four installed blocks and `introduced = 7` introduced points
(`0, …, 6`). -/
def orbitOneState : SearchState 4 where
  blocks := orbitOneBlocks
  introduced := 7

/-- The orbit-1 candidate block `{1,5,6}`, which the artifact rejects by a `C₈` witness. -/
def orbitOneCandidate : SearchBlock :=
  ⟨1, 5, 6, by decide, by decide⟩

/-- The orbit-1 payload: the three old-block indices `(1,2,3)`. -/
def orbitOneIds : Fin 3 → Fin 4 :=
  ![1, 2, 3]

/-- The kernel check accepts the artifact's orbit-1 positive witness. -/
theorem orbitOne_c8Check : c8Check orbitOneState orbitOneCandidate orbitOneIds = true := by
  decide

/-- The accepted check is the witness predicate. -/
theorem orbitOne_c8Witness : C8Witness orbitOneState orbitOneCandidate orbitOneIds :=
  (c8Check_iff orbitOneState orbitOneCandidate orbitOneIds).mp orbitOne_c8Check

/-- The artifact's orbit-1 witness really is a Berge `C₈` of the extended configuration: the
Levi cycle `{1,5,6} – 1 – {1,2,4} – 2 – {0,2,5} – 0 – {0,4,6} – 6 – {1,5,6}`. -/
theorem orbitOne_hasBergeCycleLength :
    (orbitOneState.addConfig orbitOneCandidate).HasBergeCycleLength 4 :=
  orbitOne_c8Witness.hasBergeCycleLength

/-- A negative fixture: the payload `(0,0,1)` repeats an old-block index, so the artifact's
`check_c8_witness` rejects it and so does the kernel check. -/
def repeatedIdsPayload : Fin 3 → Fin 4 :=
  ![0, 0, 1]

/-- The repeated-index payload is rejected. -/
theorem repeatedIdsCheck : c8Check orbitOneState orbitOneCandidate repeatedIdsPayload = false := by
  decide

/-- A negative fixture: the payload `(0,1,2)` names three distinct old blocks, but the consecutive
intersections are not four distinct singletons — the candidate meets `{0,1,3}` and `{0,1,3}` meets
`{1,2,4}` both in the point `1` — so the check is rejected. -/
def misorderedIdsPayload : Fin 3 → Fin 4 :=
  ![0, 1, 2]

/-- The non-witness payload is rejected. -/
theorem misorderedIdsCheck :
    c8Check orbitOneState orbitOneCandidate misorderedIdsPayload = false := by
  decide

end Fixtures

/-! ### Raw-index decoding -/

/-- Decode a raw `Nat` block index: accept it only when it is a genuine index of the current
state, i.e. strictly below `m`.  This is the artifact's "C8 witness has an invalid block index"
guard, lifted to a total function.  Byte- and tag-level parsing of the certificate stream is not
part of this module. -/
def decodeBlockIndex (m : Nat) (i : Nat) : Option (Fin m) :=
  if h : i < m then some ⟨i, h⟩ else none

/-- A raw index decodes to `j` exactly when it *is* `j`. -/
theorem decodeBlockIndex_eq_some_iff {m i : Nat} {j : Fin m} :
    decodeBlockIndex m i = some j ↔ i = j := by
  unfold decodeBlockIndex
  split
  · rename_i h
    rw [Option.some.injEq, Fin.ext_iff]
  · rename_i h
    refine ⟨fun hh => absurd hh (by simp), fun hh => absurd h (by omega)⟩

/-- A raw index is rejected exactly when it is out of range. -/
theorem decodeBlockIndex_eq_none_iff {m i : Nat} :
    decodeBlockIndex m i = none ↔ m ≤ i := by
  unfold decodeBlockIndex
  split
  · rename_i h
    exact iff_of_false (by simp) (by omega)
  · rename_i h
    exact iff_of_true rfl (by omega)

end Erdos64