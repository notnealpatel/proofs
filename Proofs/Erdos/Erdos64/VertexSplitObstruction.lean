/-
Erdős–Gyárfás problem 64 — a finite vertex-split obstruction certificate.

PROVENANCE AND SCOPE. This module is an *internally constructed finite
certificate* about the balanced degree-4 vertex splitting step that appears in
this repository's investigation of Erdős–Gyárfás problem 64. It is not quoted
from any source, and no novelty is claimed for it. Everything below is a finite
statement about one explicit seven-vertex graph and three explicit eight-vertex
normalizations; no general theorem about vertex splitting in arbitrary graphs is
formalized here, and the conditional method obstruction described at the end of
this header is **not** formalized.

WHAT IS PROVED. Let `core` be the simple graph on `Fin 7` with the path
`1-2-3-4-5-6` and the four hub edges `0-1`, `0-2`, `0-5`, `0-6`. Then:

* `core` has no power-of-two cycle in the sense of `Erdos64.HasPowerOfTwoCycle`
  (`core_not_hasPowerOfTwoCycle`). The informal reason is that every cycle of
  `core` passes through the hub `0` and therefore is a hub together with a path
  between two of its neighbours; the cycle lengths of `core` are `3, 3, 5, 6, 6,
  7` (a Sage computation, *not* a Lean proof, recorded outside this repository).
  The formal proof avoids enumerating cycles: a power-of-two cycle has length
  `2 ^ k ≤ 7` with `k ≥ 2`, hence length `4`, and a simple `4`-cycle would
  exhibit two distinct vertices with two distinct common neighbours, which the
  computable criterion `core_no_common_neighbors` forbids.

* The degrees of `core` are `0 ↦ 4`, `1 ↦ 2`, `2 ↦ 3`, `3 ↦ 2`, `4 ↦ 2`,
  `5 ↦ 3`, `6 ↦ 2` (`core_degree_zero`, `core_degree_ne_zero_le_three`,
  `core_degree_ge_two`), so `core.minDegree = 2` (`core_minDegree_eq_two`) and
  `core` is **not** a counterexample to the Erdős–Gyárfás conjecture
  (`core_not_counterexample`): the hub `0` has degree `4`, but the minimum
  degree of `core` is `2`, far below the required `3`. This certificate is an
  obstruction to a splitting *method*, not a counterexample to the conjecture.

* The balanced splitting normalizations. The hub neighbourhood is
  `N = {1, 2, 5, 6}`; a balanced `2 + 2` split of `N` is determined by the unique
  side containing `1`, giving the three normal forms `S₀ = {1, 2}`,
  `S₁ = {1, 5}`, `S₂ = {1, 6}` (`splitPart_complete`, proved by finite `decide`
  over all pairs drawn from `N`, via `Finset.card_eq_two`). For each `i : Fin 3`, `splitCore i` retains
  the path `1-…-6`, adds the new vertex `7` with the edge `0-7`, makes `0`
  adjacent to `splitPart i`, and makes `7` adjacent to `N \ splitPart i`
  (complement within `N`). Each of the three normalizations *does* contain a
  power-of-two cycle (`all_splitCore`): `splitCore 0` contains the `8`-cycle
  `0-1-2-3-4-5-6-7-0`, while `splitCore 1` and `splitCore 2` contain the
  `4`-cycle `0-1-2-7-0`. Hence no split of the hub `0` into two degree-`3`
  vertices by this balanced scheme is dyadic-cycle-free.

* Separately, `Documents/erdos64-vertex-split-obstruction.md` gives an
  informal conditional bridge-completion argument and safe-splitting
  equivalences. Those extensions are not formalized in this module. Nothing here
  asserts the Erdős–Gyárfás conjecture, its negation, or the existence of a
  counterexample.

Closed finite checks use kernel-reduced `decide`; the cycle-absence and witness
arguments also use ordinary structural Lean proofs. No `native_decide`,
`sorry`, `axiom`, `partial` or `unsafe` is used.
-/

import Erdos.Erdos64.Basic

set_option autoImplicit false

namespace Erdos64.VertexSplitObstruction

open SimpleGraph

/-! ### The seven-vertex core graph

`coreAdj` is a computable decision procedure for the adjacency relation; the
graph itself is packaged as a `SimpleGraph` with symmetry and looplessness
discharged by finite computation. -/

/-- Adjacency of the core graph on `Fin 7`: the path edges `1-2`, `2-3`, `3-4`, `4-5`,
`5-6` and the hub edges `0-1`, `0-2`, `0-5`, `0-6`. -/
def coreAdj (a b : Fin 7) : Bool :=
  (a.val + 1 == b.val && 1 ≤ a.val && b.val ≤ 6) ||
  (b.val + 1 == a.val && 1 ≤ b.val && a.val ≤ 6) ||
  (a.val == 0 && (b.val == 1 || b.val == 2 || b.val == 5 || b.val == 6)) ||
  (b.val == 0 && (a.val == 1 || a.val == 2 || a.val == 5 || a.val == 6))

/-- The core graph on `Fin 7`: the path `1-2-3-4-5-6` plus the hub edges
`0-1`, `0-2`, `0-5`, `0-6`. The hub `0` has degree `4`, and the minimum degree of `core` is
`2`, so `core` is not a counterexample to the Erdős–Gyárfás conjecture. -/
def core : SimpleGraph (Fin 7) where
  Adj a b := coreAdj a b = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel core.Adj := fun a b => by
  change Decidable (coreAdj a b = true)
  infer_instance

/-- Unfolding of `core` adjacency: it is exactly the computable predicate `coreAdj`. -/
theorem core_adj_iff (a b : Fin 7) : core.Adj a b ↔ coreAdj a b = true := Iff.rfl

/-- The hub neighbourhood `N = {1, 2, 5, 6}` of `core`. -/
def hubNeighbors : Finset (Fin 7) := {1, 2, 5, 6}

/-! ### Degrees of the core graph

`degree` is `#(neighborFinset ·)`, and `neighborFinset` is a noncomputable
`Set.toFinset`, so we compare it with the computable filter `coreNeighbors` and
then evaluate the latter by `decide`. -/

/-- The computable neighbour list of `v` in `core`. -/
def coreNeighbors (v : Fin 7) : Finset (Fin 7) :=
  Finset.univ.filter fun w => coreAdj v w

/-- `coreNeighbors v` is exactly the Mathlib `neighborFinset` of `v` in `core`. -/
theorem core_neighborFinset_eq (v : Fin 7) : core.neighborFinset v = coreNeighbors v := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset, coreNeighbors, Finset.mem_filter, Finset.mem_univ,
    true_and]
  change (coreAdj v w = true) ↔ (coreAdj v w = true)
  exact Iff.rfl

/-- The degree of `v` in `core` is the cardinality of the computable neighbour list. -/
theorem core_degree_eq (v : Fin 7) : core.degree v = (coreNeighbors v).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, core_neighborFinset_eq]

/-- The hub `0` has degree `4` in `core`. -/
theorem core_degree_zero : core.degree 0 = 4 := by
  rw [core_degree_eq]
  decide

/-- Every vertex of `core` other than the hub `0` has degree at most `3`. -/
theorem core_degree_ne_zero_le_three : ∀ v : Fin 7, v ≠ 0 → core.degree v ≤ 3 := by
  intro v hv
  rw [core_degree_eq]
  exact (by decide : ∀ w : Fin 7, w ≠ 0 → (coreNeighbors w).card ≤ 3) v hv

/-- Every vertex of `core` has degree at least `2`; `core` therefore has minimum degree `2`, not
`3`. -/
theorem core_degree_ge_two : ∀ v : Fin 7, 2 ≤ core.degree v := by
  intro v
  rw [core_degree_eq]
  exact (by decide : ∀ w : Fin 7, 2 ≤ (coreNeighbors w).card) v

/-- An explicit degree-`2` witness in `core`, namely the vertex `1`. -/
theorem core_degree_one : core.degree 1 = 2 := by
  rw [core_degree_eq]
  decide

/-- The minimum degree of `core` is `2`. -/
theorem core_minDegree_eq_two : core.minDegree = 2 := by
  haveI : Nonempty (Fin 7) := ⟨0⟩
  have hle : 2 ≤ core.minDegree :=
    SimpleGraph.le_minDegree_of_forall_le_degree core 2 core_degree_ge_two
  have hge : core.minDegree ≤ 2 := by
    have := SimpleGraph.minDegree_le_degree core 1
    rw [core_degree_one] at this
    exact this
  omega

/-- `core` is not a counterexample to the Erdős–Gyárfás conjecture: it has minimum degree `2`,
below the required `3`. This is an obstruction to a splitting method, not a counterexample. -/
theorem core_not_counterexample : ¬ IsCounterexample core := by
  intro h
  have hmin := h.minDegree_ge_three
  rw [core_minDegree_eq_two] at hmin
  omega

/-! ### The common-neighbour criterion

The computable criterion below is the finite certificate excluding `4`-cycles in
`core`: two distinct vertices of a simple graph cannot have two distinct common
neighbours. It is decided over all `7 ^ 4` quadruples. -/

/-- Two distinct vertices of `core` have at most one common neighbour. -/
theorem core_no_common_neighbors :
    ∀ a b x y : Fin 7, a ≠ b → core.Adj a x → core.Adj b x → core.Adj a y →
      core.Adj b y → x = y := by
  decide

/-- `core` has no power-of-two cycle.

Proof route: a power-of-two cycle has length `2 ^ k` with `k ≥ 2`, and a cycle at a vertex is a
path after deleting its first edge, so its length is at most `7 = Fintype.card (Fin 7)`; hence
the length is `4`. The vertices at distance `0` and `2` along such a cycle are distinct, as are
those at distance `1` and `3`, and both latter vertices are common neighbours of the former,
contradicting `core_no_common_neighbors`. -/
theorem core_not_hasPowerOfTwoCycle : ¬ HasPowerOfTwoCycle core := by
  rintro ⟨k, hk, v, c, hc, hlen⟩
  have htail : c.tail.length < 7 := by
    simpa using (Walk.IsPath.length_lt hc.isPath_tail)
  have hle : c.length ≤ 7 := by
    have hsucc : c.tail.length + 1 = c.length := Walk.length_tail_add_one hc.not_nil
    omega
  have hpow : 2 ^ k ≤ 7 := by
    rw [← hlen]
    exact hle
  have hklt : k < 3 := by
    by_contra h
    have hk3 : 3 ≤ k := by omega
    have hpow3 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk3
    have hpow8 : 8 ≤ 2 ^ k := by simpa using hpow3
    omega
  have hk2 : k = 2 := by omega
  have hlen4 : c.length = 4 := by
    calc
      c.length = 2 ^ k := hlen
      _ = 4 := by simp [hk2]
  have hax : core.Adj (c.getVert 0) (c.getVert 1) :=
    Walk.adj_getVert_succ c (by omega)
  have hxb : core.Adj (c.getVert 1) (c.getVert 2) :=
    Walk.adj_getVert_succ c (by omega)
  have hby : core.Adj (c.getVert 2) (c.getVert 3) :=
    Walk.adj_getVert_succ c (by omega)
  have h40 : c.getVert 4 = c.getVert 0 := by
    calc
      c.getVert 4 = c.getVert c.length := by simp [hlen4]
      _ = v := Walk.getVert_length c
      _ = c.getVert 0 := (Walk.getVert_zero c).symm
  have hya : core.Adj (c.getVert 3) (c.getVert 0) := by
    have h3 : core.Adj (c.getVert 3) (c.getVert 4) :=
      Walk.adj_getVert_succ c (by omega)
    rwa [h40] at h3
  have hinj : Set.InjOn c.getVert {i : ℕ | i ≤ c.length - 1} :=
    Walk.IsCycle.getVert_injOn' hc
  have hmem : ∀ i : ℕ, i ≤ 3 → i ∈ {j : ℕ | j ≤ c.length - 1} := by
    intro i hi
    simp only [Set.mem_ofPred_eq]
    omega
  have hab : c.getVert 0 ≠ c.getVert 2 := by
    intro hab'
    have h02 : (0 : ℕ) = 2 := hinj (hmem 0 (by decide)) (hmem 2 (by decide)) hab'
    omega
  have hxy : c.getVert 1 ≠ c.getVert 3 := by
    intro hxy'
    have h13 : (1 : ℕ) = 3 := hinj (hmem 1 (by decide)) (hmem 3 (by decide)) hxy'
    omega
  exact hxy (core_no_common_neighbors (c.getVert 0) (c.getVert 2) (c.getVert 1) (c.getVert 3)
    hab hax hxb.symm hya.symm hby)

/-! ### The balanced splitting normalizations

The hub neighbourhood is `N = {1, 2, 5, 6}`. An unordered balanced `2 + 2`
partition of `N` is determined by the unique part containing `1`, so there are
exactly three normal forms; `splitPart_complete` records this finite fact by
`decide` over all pairs drawn from `N`. -/

/-- The three normal-form parts of the hub neighbourhood, indexed by `Fin 3`:
`S₀ = {1, 2}`, `S₁ = {1, 5}`, `S₂ = {1, 6}`. -/
def splitPartNat : ℕ → Finset (Fin 7)
  | 0 => {1, 2}
  | 1 => {1, 5}
  | _ => {1, 6}

/-- The part of the hub neighbourhood `N = {1, 2, 5, 6}` containing the hub neighbour `1`, as a
function of the split index `i : Fin 3`. -/
def splitPart (i : Fin 3) : Finset (Fin 7) := splitPartNat i.val

/-- The first normal form is `{1, 2}`. -/
theorem splitPart_zero : splitPart 0 = {1, 2} := rfl

/-- The second normal form is `{1, 5}`. -/
theorem splitPart_one : splitPart 1 = {1, 5} := rfl

/-- The third normal form is `{1, 6}`. -/
theorem splitPart_two : splitPart 2 = {1, 6} := rfl

/-- **Completeness of the three normal forms, in pair form.** A `2`-element subset of the hub
neighbourhood `N = {1, 2, 5, 6}` containing `1` is written `{a, b}` with `a, b ∈ N`; the finite
computation then shows it is one of `S₀ = {1, 2}`, `S₁ = {1, 5}`, `S₂ = {1, 6}`. -/
theorem splitPart_complete_pairs :
    ∀ a b : Fin 7, a ≠ b → a ∈ hubNeighbors → b ∈ hubNeighbors →
      (1 : Fin 7) ∈ ({a, b} : Finset (Fin 7)) →
      ∃ i : Fin 3, ({a, b} : Finset (Fin 7)) = splitPart i := by
  decide

/-- **Completeness of the three normal forms.** Every balanced split of the hub neighbourhood
`N = {1, 2, 5, 6}` — that is, every `2`-element subset of `N` containing `1` — is one of
`S₀ = {1, 2}`, `S₁ = {1, 5}`, `S₂ = {1, 6}`. Since the two parts of an unordered balanced
partition are interchanged by relabelling, and exactly one part contains `1`, this exhausts all
balanced unlabelled splits. The proof extracts the two elements of `S` via `Finset.card_eq_two`
and finishes by `splitPart_complete_pairs`. -/
theorem splitPart_complete (S : Finset (Fin 7)) (hsub : S ⊆ hubNeighbors) (hcard : S.card = 2)
    (h1 : (1 : Fin 7) ∈ S) : ∃ i : Fin 3, S = splitPart i := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  exact splitPart_complete_pairs a b hab (hsub (by simp)) (hsub (by simp)) h1

/-! ### The split graphs

`splitCore i` retains the path `1-…-6`, adds the vertex `7` and the edge `0-7`,
attaches `0` to `splitPart i`, and attaches `7` to the complement of
`splitPart i` inside `N = {1, 2, 5, 6}`. -/

/-- Membership in `splitPart i`, as a computable predicate on natural numbers
(`i.val` is the split index). -/
def inSplitPart (i b : ℕ) : Bool :=
  b == 1 || (b == 2 && i == 0) || (b == 5 && i == 1) || (b == 6 && i == 2)

/-- Membership in the complement of `splitPart i` inside `N = {1, 2, 5, 6}`, as a computable
predicate on natural numbers. -/
def inOtherPart (i b : ℕ) : Bool :=
  (b == 5 && i == 0) || (b == 6 && i == 0) || (b == 2 && i == 1) ||
  (b == 6 && i == 1) || (b == 2 && i == 2) || (b == 5 && i == 2)

/-- Adjacency of the split graph `splitCore i` on `Fin 8`: the path `1-…-6`, the edge `0-7`, the
edges from `0` to `splitPart i`, and the edges from `7` to `N \ splitPart i`. -/
def splitAdj (i : Fin 3) (a b : Fin 8) : Bool :=
  (a.val + 1 == b.val && 1 ≤ a.val && b.val ≤ 6) ||
  (b.val + 1 == a.val && 1 ≤ b.val && a.val ≤ 6) ||
  (a.val == 0 && b.val == 7) ||
  (b.val == 0 && a.val == 7) ||
  (a.val == 0 && inSplitPart i.val b.val) ||
  (b.val == 0 && inSplitPart i.val a.val) ||
  (a.val == 7 && inOtherPart i.val b.val) ||
  (b.val == 7 && inOtherPart i.val a.val)

/-- `splitAdj` is symmetric in its last two arguments. -/
theorem splitAdj_comm : ∀ i : Fin 3, ∀ a b : Fin 8, splitAdj i a b = splitAdj i b a := by
  decide

/-- `splitAdj` is irreflexive. -/
theorem splitAdj_irrefl : ∀ i : Fin 3, ∀ a : Fin 8, splitAdj i a a = false := by
  decide

/-- The `i`-th balanced normalization of `core`: the path `1-…-6`, the vertex `7` joined to `0`,
`0` joined to `splitPart i`, and `7` joined to `N \ splitPart i`. -/
def splitCore (i : Fin 3) : SimpleGraph (Fin 8) where
  Adj a b := splitAdj i a b = true
  symm := ⟨fun a b hab => by rw [← splitAdj_comm i a b]; exact hab⟩
  loopless := ⟨fun a => by rw [splitAdj_irrefl i a]; exact Bool.false_ne_true⟩

instance (i : Fin 3) : DecidableRel (splitCore i).Adj := fun a b => by
  change Decidable (splitAdj i a b = true)
  infer_instance

/-! ### Explicit power-of-two cycles in every split

`splitCore 0` carries the `8`-cycle `0-1-2-3-4-5-6-7-0`, while `splitCore 1` and
`splitCore 2` carry the `4`-cycle `0-1-2-7-0`. Each walk is an honest
`SimpleGraph.Walk.IsCycle` witness; `IsCycle` is proved through
`Walk.isCycle_iff_isPath_tail_and_le_length`, so the closed walk is verified to be
a simple cycle rather than assumed to be one. -/

/-- The `8`-cycle `0-1-2-3-4-5-6-7-0` in `splitCore 0`. -/
def c8Walk : (splitCore 0).Walk 0 0 :=
  Walk.cons (by decide : (splitCore 0).Adj 0 1)
    (Walk.cons (by decide : (splitCore 0).Adj 1 2)
      (Walk.cons (by decide : (splitCore 0).Adj 2 3)
        (Walk.cons (by decide : (splitCore 0).Adj 3 4)
          (Walk.cons (by decide : (splitCore 0).Adj 4 5)
            (Walk.cons (by decide : (splitCore 0).Adj 5 6)
              (Walk.cons (by decide : (splitCore 0).Adj 6 7)
                (Walk.cons (by decide : (splitCore 0).Adj 7 0) Walk.nil)))))))

/-- The `4`-cycle `0-1-2-7-0` in `splitCore 1`. -/
def c4WalkOne : (splitCore 1).Walk 0 0 :=
  Walk.cons (by decide : (splitCore 1).Adj 0 1)
    (Walk.cons (by decide : (splitCore 1).Adj 1 2)
      (Walk.cons (by decide : (splitCore 1).Adj 2 7)
        (Walk.cons (by decide : (splitCore 1).Adj 7 0) Walk.nil)))

/-- The `4`-cycle `0-1-2-7-0` in `splitCore 2`. -/
def c4WalkTwo : (splitCore 2).Walk 0 0 :=
  Walk.cons (by decide : (splitCore 2).Adj 0 1)
    (Walk.cons (by decide : (splitCore 2).Adj 1 2)
      (Walk.cons (by decide : (splitCore 2).Adj 2 7)
        (Walk.cons (by decide : (splitCore 2).Adj 7 0) Walk.nil)))

/-- `splitCore 0` has a power-of-two cycle, namely the `8`-cycle `0-1-2-3-4-5-6-7-0`. -/
theorem splitCore_zero_hasPowerOfTwoCycle : HasPowerOfTwoCycle (splitCore 0) :=
  ⟨3, by decide, 0, c8Walk, by
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    exact ⟨Walk.IsPath.mk' (by decide), by decide⟩, by decide⟩

/-- `splitCore 1` has a power-of-two cycle, namely the `4`-cycle `0-1-2-7-0`. -/
theorem splitCore_one_hasPowerOfTwoCycle : HasPowerOfTwoCycle (splitCore 1) :=
  ⟨2, by decide, 0, c4WalkOne, by
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    exact ⟨Walk.IsPath.mk' (by decide), by decide⟩, by decide⟩

/-- `splitCore 2` has a power-of-two cycle, namely the `4`-cycle `0-1-2-7-0`. -/
theorem splitCore_two_hasPowerOfTwoCycle : HasPowerOfTwoCycle (splitCore 2) :=
  ⟨2, by decide, 0, c4WalkTwo, by
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    exact ⟨Walk.IsPath.mk' (by decide), by decide⟩, by decide⟩

/-- **Every balanced split of the hub is unsafe.** For each of the three normal forms, the split
graph contains a power-of-two cycle; by `splitPart_complete` these three cases exhaust all
balanced `2 + 2` splits of the hub neighbourhood. -/
theorem all_splitCore (i : Fin 3) : HasPowerOfTwoCycle (splitCore i) := by
  have hcases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases hcases with h | h | h
  · have hi : i = 0 := Fin.ext h
    rw [hi]
    exact splitCore_zero_hasPowerOfTwoCycle
  · have hi : i = 1 := Fin.ext h
    rw [hi]
    exact splitCore_one_hasPowerOfTwoCycle
  · have hi : i = 2 := Fin.ext h
    rw [hi]
    exact splitCore_two_hasPowerOfTwoCycle

end Erdos64.VertexSplitObstruction