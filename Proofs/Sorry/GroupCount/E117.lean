/-
  Erdős Problem #117 — covering groups by abelian subgroups.
  Status: open.  Tier UC lemma mine (fits Proofs/GroupCount's
  commuting-pair scope).

  Verbatim statement (`goof erdos fetch 117`, pulled 2026-08-05):

    "Let $h(n)$ be minimal such that any group $G$ with the property
    that any subset of $>n$ elements contains some $x\neq y$ such
    that $xy=yx$ can be covered by at most $h(n)$ many Abelian
    subgroups.

    Estimate $h(n)$ as well as possible."

  DB remarks: Pyber [Py87]: c₁ⁿ < h(n) < c₂ⁿ for constants
  c₂ > c₁ > 1; Erdős [Er97f] notes the lower bound was known to
  Isaacs.

  The group property "every subset of > n elements contains a
  commuting pair" says: every set of pairwise NON-commuting elements
  has size ≤ n (no "anticlique" of size n+1 in the commuting graph's
  complement).  h(n) well-defined = the covering number is bounded
  over ALL such groups (finite and infinite; Pyber's theorem).

  Repo adjacency: `Proofs/GroupCount` (commuting-pair structure is in
  scope: `CommutingTriples.lean`).  Exploratory flag from the
  candidates doc: no computed h(n) table exists — scope a probe
  before promising values.

  Mathlib inventory: `Subgroup`, `IsCommutative` (as
  `Subgroup.IsCommutative`? — in current Mathlib the spelling is
  `Std.Commutative`-free: `S.IsCommutative` instance class for
  subgroups exists; re-probe leandoc at campaign start), `Commute`.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E117

/-- `NoncommBounded G n`: every subset of more than `n` elements
    contains a commuting pair — equivalently every pairwise
    non-commuting subset has at most `n` elements.  Encoded on
    finite subsets (`Finset G` via sets with `Set.Finite`… we use
    `Set.ncard` on arbitrary sets: any set of pairwise non-commuting
    elements has ncard ≤ n; infinite antichains are excluded
    separately by `Set.Finite` bookkeeping in the campaign). -/
def NoncommBounded (G : Type*) [Group G] (n : ℕ) : Prop :=
  ∀ S : Set G, (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ Commute x y) →
    S.Finite ∧ S.ncard ≤ n

/-- `CoveredByAbelian G h`: `G` is the union of at most `h` abelian
    subgroups. -/
def CoveredByAbelian (G : Type*) [Group G] (h : ℕ) : Prop :=
  ∃ (H : Fin h → Subgroup G),
    (∀ i, ∀ x ∈ H i, ∀ y ∈ H i, Commute x y) ∧
    ∀ g : G, ∃ i, g ∈ H i

/-- Ground truth: an abelian group satisfies `NoncommBounded G 1`
    (no two distinct elements fail to commute) and is covered by one
    abelian subgroup (itself).  -- PROVABLE (effort S). -/
example (G : Type*) [CommGroup G] :
    NoncommBounded G 1 ∧ CoveredByAbelian G 1 := by
  sorry

/-- **Pyber's theorem, qualitative core** ([Py87]) — h(n) is
    well-defined: there is a bound `h` (depending only on `n`) such
    that every group with the n-commuting property is covered by `h`
    abelian subgroups.  This finiteness is itself the headline
    formalization target (the quantitative bounds refine it). -/
theorem pyber_welldefined (n : ℕ) (hn : 1 ≤ n) :
    ∃ h : ℕ, ∀ (G : Type) (_ : Group G), NoncommBounded G n →
      CoveredByAbelian G h := by
  sorry

/-- `hFun n`: the minimal such `h` — the `h(n)` of the problem
    (sInf over the bounds valid for all groups; honest given
    `pyber_welldefined`). -/
noncomputable def hFun (n : ℕ) : ℕ :=
  sInf {h : ℕ | ∀ (G : Type) (_ : Group G), NoncommBounded G n →
    CoveredByAbelian G h}

/-- **Pyber's bounds** ([Py87]), archived: `c₁ⁿ < h(n) < c₂ⁿ` for
    constants `1 < c₁ < c₂`.  Lower bound already known to Isaacs
    (extraspecial 2-groups are the standard witnesses). -/
theorem pyber_bounds :
    ∃ c₁ c₂ : ℝ, 1 < c₁ ∧ c₁ < c₂ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c₁ ^ (n : ℝ) < (hFun n : ℝ) ∧ (hFun n : ℝ) < c₂ ^ (n : ℝ) := by
  sorry

/-- Small-case probe target: `h(1) = 1` — a group where every 2
    distinct elements commute is abelian, covered by itself.
    -- PROVABLE (effort S; the natural first landing, pinning the
    definitional plumbing). -/
theorem hFun_one : hFun 1 = 1 := by
  sorry

/-- Sanity witness that the property is nontrivial at n ≥ 3: the
    quaternion group Q₈ has pairwise non-commuting {i, j, k}, so
    ¬NoncommBounded Q₈ 2, while its 3 maximal cyclic subgroups
    ⟨i⟩, ⟨j⟩, ⟨k⟩ cover it: CoveredByAbelian Q₈ 3.  (Mathlib:
    `QuaternionGroup 2`.)  -- PROVABLE (decide-scale group
    computation; effort S–M). -/
example : ¬ NoncommBounded (QuaternionGroup 2) 2 ∧
    CoveredByAbelian (QuaternionGroup 2) 3 := by
  sorry

end ErdosCandidates.E117

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB fetch exactly.
   - NoncommBounded encoding is correct: the contrapositive of "every > n
     subset has a commuting pair" is "every pairwise non-commuting set has
     size <= n". Including S.Finite in the conclusion is NECESSARY — without
     it, Set.ncard of an infinite set is 0, so ncard <= n would hold vacuously,
     admitting infinite antichains. The encoding is faithful and well-guarded.
   - Pyber bounds c1^n < h(n) < c2^n with 1 < c1 < c2 match DB.
   - Isaacs lower bound attribution matches DB ("Erdos writes the lower bound
     was already known to Isaacs").
   - Q8 arithmetic verified: {i,j,k} pairwise non-commuting (size 3 > 2),
     covered by 3 maximal cyclic subgroups.
   - hFun sInf is honest given pyber_welldefined.
-/
