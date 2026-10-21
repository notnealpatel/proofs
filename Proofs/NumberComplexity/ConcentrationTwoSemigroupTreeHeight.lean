/-
# Concentration-two numerical semigroups: height of the tree `G(C̄₂[m])` for odd `m`

## Source

arXiv:2103.16723, J. C. Rosales, M. B. Branco, M. A. Traesel, *Numerical semigroups
with concentration two*.  End of Section 3 ("The genus of the elements in
`C₂[m]`"), after Example 16, open problem (2); restated as open in Traesel's 2022
Évora PhD thesis.

Definitions (Section 1–2).  A numerical semigroup is a submonoid `S` of `(ℕ, +)`
with `ℕ \ S` finite; `m(S)` is its least nonzero element, `g(S) = #(ℕ \ S)` its
genus, `F(S) = max (ℤ \ S)` its Frobenius number, `next_S(s) = min {x ∈ S | s < x}`
and the concentration is `C(S) = max {next_S(s) - s | s ∈ S \ {0}}`.
`C̄₂[m]` is the set of numerical semigroups with `C(S) ≤ 2` and `m(S) = m`, and
`G(C̄₂[m])` is the graph on `C̄₂[m]` with an edge `(S, T)` when `T = S ∪ {F(S)}`;
it is a tree rooted at `Δ(m) = {0, m, →}` (Theorem 6).  The height of a rooted
tree is the largest depth of a vertex.

Verbatim printed problem:

> We finished this section by putting two problems :
> 1. What is the cardinality of $\mathsf{C}_2[m]$ if $m$ is odd belongs to
>    $\N\backslash \{0,1\}$?
> 2. What is the height of the tree $G(\overline {\mathsf{C}_2[m]})$ if $m$ is odd
>    belongs to $\N\backslash \{0,1\}$?

Proposition 14(1) of the paper: depth `k` vertices are exactly the `S ∈ C̄₂[m]` with
`g(S) = m - 1 + k`.

Status (2026-10-21): open in the paper (printed as a problem, no answer given).
Target answer (triage conjecture, re-validated by exhaustive enumeration for odd
`m = 3, …, 15`): for odd `m ≥ 3` the maximum genus in `C̄₂[m]` is `2m - 2`, attained
only by `⟨m, m+2, m+4, …, 2m-1⟩`, so the height is `m - 1`.  (For `m = 1`,
excluded by the paper's `m ∈ ℕ \ {0,1}`.)

## What this module proves (no `sorry`)

* `genus_le_two_mul_sub_two`: odd `m ≥ 3`, multiplicity `m`, `C(S) ≤ 2` ⟹ `S` is a
  numerical semigroup and `g(S) ≤ 2m - 2`;
* `genus_topSemigroup`: `g(⟨m, m+2, …, 2m-1⟩) = 2m - 2`;
* `eq_topSemigroup_of_genus_eq`: that semigroup is the unique one of genus `2m - 2`;
* `isGreatest_genus`: the maximum genus over `C̄₂[m]` is `2m - 2`;
* `isAtDepth_iff`: Proposition 14(1) (depth `k` ⇔ genus `m - 1 + k`);
* `isGreatest_depth`: the height of `G(C̄₂[m])` is `m - 1` — the answer to Problem 2.

Proof idea: if `C(S) ≤ 2` then gaps `h > m` are isolated (`h + 1 ∈ S`); hence every
even number `2c + 2m` (`c ≥ 1`) lies in `S` (from `c + m`, or from `c - 1 + m` and
`c + 1 + m`), so for odd `m` everything from `3m` on lies in `S`.  The gaps above
`m` then sit in the `(m - 1)/2` blocks `{m+2j+1, m+2j+2, 2m+2j+1}`, each holding
at most two gaps, which gives `g(S) ≤ (m - 1) + (m - 1)`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.ConcentrationTwoSemigroupTreeHeight

/-! ## Definitions and the genus bound -/

/-- A submonoid `S` of `(ℕ, +)` is a *numerical semigroup* when `ℕ \ S` is finite
(paper, Section 1). -/
def IsNumericalSemigroup (S : AddSubmonoid ℕ) : Prop := ((S : Set ℕ)ᶜ).Finite

/-- `S` has *multiplicity* `m`: `m` is the least positive element of `S`
(paper: `m(S)`, the least nonzero element of `S`). -/
def HasMultiplicity (S : AddSubmonoid ℕ) (m : ℕ) : Prop :=
  0 < m ∧ m ∈ S ∧ ∀ x, 0 < x → x < m → x ∉ S

/-- `C(S) ≤ 2`: for every nonzero `s ∈ S`, `next_S(s) - s ≤ 2`, where
`next_S(s) = min {x ∈ S | s < x}`.  Spelled without `min`: some element of `S` lies
in `(s, s + 2]`.  This is literally the paper's definition of the concentration
`C(S) = max {next_S(s) - s | s ∈ S \ {0}}` bounded by `2`. -/
def ConcentrationLeTwo (S : AddSubmonoid ℕ) : Prop :=
  ∀ s ∈ S, s ≠ 0 → ∃ x ∈ S, s < x ∧ x ≤ s + 2

/-- The genus `g(S) = #(ℕ \ S)` (as `Set.ncard`, hence `0` on an infinite complement;
every semigroup below has finite complement, which is part of the hypotheses or
proved). -/
noncomputable def genus (S : AddSubmonoid ℕ) : ℕ := ((S : Set ℕ)ᶜ).ncard

/-- Proposition 1, (1) ⇒ (2) of the paper: if `C(S) ≤ 2` and `h > m(S)` is a gap,
then `h + 1 ∈ S`. -/
theorem succ_mem_of_notMem {S : AddSubmonoid ℕ} {m : ℕ} (hS : HasMultiplicity S m)
    (hC : ConcentrationLeTwo S) {h : ℕ} (hmh : m < h) (hh : h ∉ S) : h + 1 ∈ S := by
  by_contra hh1
  have key : ∀ j, j ≤ h - m → h - j ∉ S ∧ h - j + 1 ∉ S := by
    intro j
    induction j with
    | zero => intro _; exact ⟨by simpa using hh, by simpa using hh1⟩
    | succ j ih =>
      intro hj
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have e1 : h - (j + 1) + 1 = h - j := by omega
      refine ⟨fun hs => ?_, e1 ▸ ih1⟩
      obtain ⟨x, hx, hlt, hle⟩ := hC _ hs (by have := hS.1; omega)
      have hx' : x = h - j ∨ x = h - j + 1 := by omega
      rcases hx' with rfl | rfl
      · exact ih1 hx
      · exact ih2 hx
  have := (key (h - m) le_rfl).1
  rw [show h - (h - m) = m by omega] at this
  exact this hS.2.1

/-- Key lemma: if `C(S) ≤ 2` and `m(S) = m`, then every even number `2c + 2m` with
`c ≥ 1` lies in `S` (either `c + m ∈ S`, or `c - 1 + m` and `c + 1 + m` lie in `S`). -/
theorem two_mul_add_mem {S : AddSubmonoid ℕ} {m : ℕ} (hS : HasMultiplicity S m)
    (hC : ConcentrationLeTwo S) {c : ℕ} (hc : 1 ≤ c) : 2 * c + 2 * m ∈ S := by
  by_cases hcm : c + m ∈ S
  · have := S.add_mem hcm hcm
    rwa [show c + m + (c + m) = 2 * c + 2 * m by ring] at this
  · have hlow : c - 1 + m ∈ S := by
      rcases Nat.lt_or_ge c 2 with h2 | h2
      · rw [show c - 1 + m = m by omega]; exact hS.2.1
      · by_contra hlow
        have := succ_mem_of_notMem hS hC (by omega) hlow
        rw [show c - 1 + m + 1 = c + m by omega] at this
        exact hcm this
    have hhigh : c + m + 1 ∈ S := succ_mem_of_notMem hS hC (by omega) hcm
    have := S.add_mem hlow hhigh
    rwa [show c - 1 + m + (c + m + 1) = 2 * c + 2 * m by omega] at this

/-- For odd `m ≥ 3`, a semigroup with multiplicity `m` and `C(S) ≤ 2` contains every
`x ≥ 3m` (so its Frobenius number is below `3m`). -/
theorem mem_of_three_mul_le {S : AddSubmonoid ℕ} {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m)
    (hS : HasMultiplicity S m) (hC : ConcentrationLeTwo S) {x : ℕ} (hx : 3 * m ≤ x) : x ∈ S := by
  obtain ⟨r, rfl⟩ := hm
  rcases Nat.even_or_odd' x with ⟨k, rfl | rfl⟩
  · have := two_mul_add_mem hS hC (c := k - (2 * r + 1)) (by omega)
    rwa [show 2 * (k - (2 * r + 1)) + 2 * (2 * r + 1) = 2 * k by omega] at this
  · rcases Nat.lt_or_ge (2 * k + 1) (3 * (2 * r + 1) + 1) with h | h
    · rw [show 2 * k + 1 = (2 * r + 1) + (2 * r + 1) + (2 * r + 1) by omega]
      exact S.add_mem (S.add_mem hS.2.1 hS.2.1) hS.2.1
    · have := two_mul_add_mem hS hC (c := k - 3 * r - 1) (by omega)
      have := S.add_mem this hS.2.1
      rwa [show 2 * (k - 3 * r - 1) + 2 * (2 * r + 1) + (2 * r + 1) = 2 * k + 1 by omega] at this

open Classical in
/-- The gaps of `S` in the block `{m+2j+1, m+2j+2, 2m+2j+1}`.  For `m = 2r + 1` the
blocks `j < r` cover `(m, 3m)` except `2m` and the even numbers `2m + 2j + 2`, all of
which lie in `S` when `C(S) ≤ 2`. -/
noncomputable def gapBlock (S : AddSubmonoid ℕ) (m j : ℕ) : Finset ℕ :=
  ({m + 2 * j + 1, m + 2 * j + 2, 2 * m + 2 * j + 1} : Finset ℕ).filter (· ∉ S)

/-- Each block contains at most two gaps, and at most one unless both `m+2j+1` and
`2m+2j+1` are gaps. -/
theorem card_gapBlock_le {S : AddSubmonoid ℕ} {m : ℕ} (hS : HasMultiplicity S m)
    (hC : ConcentrationLeTwo S) (j : ℕ) :
    (gapBlock S m j).card ≤ 2 ∧
      ((m + 2 * j + 1 ∈ S ∨ 2 * m + 2 * j + 1 ∈ S) → (gapBlock S m j).card ≤ 1) := by
  classical
  have hshift : m + 2 * j + 1 ∈ S → 2 * m + 2 * j + 1 ∈ S := fun h => by
    have := S.add_mem h hS.2.1
    rwa [show m + 2 * j + 1 + m = 2 * m + 2 * j + 1 by ring] at this
  have hiso : m + 2 * j + 1 ∉ S → m + 2 * j + 2 ∈ S := fun h =>
    succ_mem_of_notMem (h := m + 2 * j + 1) hS hC (by omega) h
  by_cases h1 : m + 2 * j + 1 ∈ S
  · have h3 := hshift h1
    have hsub : gapBlock S m j ⊆ {m + 2 * j + 2} := by
      intro x hx
      simp only [gapBlock, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with ⟨rfl | rfl | rfl, hx⟩
      · exact absurd h1 hx
      · rfl
      · exact absurd h3 hx
    have := (Finset.card_le_card hsub).trans (Finset.card_singleton _).le
    exact ⟨this.trans (by norm_num), fun _ => this⟩
  · have h2 := hiso h1
    have hsub : gapBlock S m j ⊆ {m + 2 * j + 1, 2 * m + 2 * j + 1} := by
      intro x hx
      simp only [gapBlock, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with ⟨rfl | rfl | rfl, hx⟩
      · exact Or.inl rfl
      · exact absurd h2 hx
      · exact Or.inr rfl
    refine ⟨(Finset.card_le_card hsub).trans (Finset.card_le_two), fun h => ?_⟩
    have h3 : 2 * m + 2 * j + 1 ∈ S := h.resolve_left h1
    have hsub' : gapBlock S m j ⊆ {m + 2 * j + 1} := by
      intro x hx
      simp only [gapBlock, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with ⟨rfl | rfl | rfl, hx⟩
      · rfl
      · exact absurd h2 hx
      · exact absurd h3 hx
    exact (Finset.card_le_card hsub').trans (Finset.card_singleton _).le

/-- For `m = 2r + 1`, every gap lies in `[1, m)` or in one of the blocks `j < r`. -/
theorem compl_subset_cover {S : AddSubmonoid ℕ} {r : ℕ} (hr : 1 ≤ r)
    (hS : HasMultiplicity S (2 * r + 1)) (hC : ConcentrationLeTwo S) :
    (S : Set ℕ)ᶜ ⊆
      ↑(Finset.Ico 1 (2 * r + 1) ∪ (Finset.range r).biUnion (gapBlock S (2 * r + 1))) := by
  classical
  intro x hx
  have hx : x ∉ S := hx
  have hx0 : x ≠ 0 := fun h => hx (h ▸ S.zero_mem)
  have hxm : x ≠ 2 * r + 1 := fun h => hx (h ▸ hS.2.1)
  have hx3 : x < 3 * (2 * r + 1) := by
    by_contra h
    exact hx (mem_of_three_mul_le ⟨r, rfl⟩ (by omega) hS hC (by omega))
  simp only [Finset.coe_union, Finset.coe_Ico, Finset.coe_biUnion, Finset.coe_range,
    Set.mem_union, Set.mem_Ico, Set.mem_iUnion, Set.mem_Iio, Finset.mem_coe, exists_prop]
  rcases Nat.lt_or_ge x (2 * r + 1) with h | h
  · exact Or.inl ⟨by omega, h⟩
  · right
    rcases Nat.even_or_odd' x with ⟨k, rfl | rfl⟩
    · -- even gap: lies in `(m, 2m)`, since `2m + 2c ∈ S`
      have hk : 2 * k < 2 * (2 * r + 1) := by
        by_contra hk
        rcases Nat.eq_or_lt_of_le (not_lt.mp hk) with hk | hk
        · have := S.add_mem hS.2.1 hS.2.1
          rw [← two_mul, hk] at this
          exact hx this
        · have := two_mul_add_mem hS hC (c := k - (2 * r + 1)) (by omega)
          rw [show 2 * (k - (2 * r + 1)) + 2 * (2 * r + 1) = 2 * k by omega] at this
          exact hx this
      refine ⟨k - r - 1, by omega, ?_⟩
      simp only [gapBlock, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨Or.inl (by omega), hx⟩
    · rcases Nat.lt_or_ge (2 * k + 1) (2 * (2 * r + 1)) with h2 | h2
      · refine ⟨k - r - 1, by omega, ?_⟩
        simp only [gapBlock, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨Or.inr (Or.inl (by omega)), hx⟩
      · refine ⟨k - 2 * r - 1, by omega, ?_⟩
        simp only [gapBlock, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨Or.inr (Or.inr (by omega)), hx⟩

/-- Finiteness of the gap set, and the genus bound by the block counts. -/
theorem genus_le_sum {S : AddSubmonoid ℕ} {r : ℕ} (hr : 1 ≤ r)
    (hS : HasMultiplicity S (2 * r + 1)) (hC : ConcentrationLeTwo S) :
    IsNumericalSemigroup S ∧
      genus S ≤ 2 * r + ∑ j ∈ Finset.range r, (gapBlock S (2 * r + 1) j).card := by
  classical
  have hcov := compl_subset_cover hr hS hC
  refine ⟨Set.Finite.subset (Finset.finite_toSet _) hcov, ?_⟩
  calc genus S ≤ (Finset.Ico 1 (2 * r + 1) ∪
          (Finset.range r).biUnion (gapBlock S (2 * r + 1))).card := by
        rw [genus, ← Set.ncard_coe_finset]
        exact Set.ncard_le_ncard hcov (Finset.finite_toSet _)
    _ ≤ (Finset.Ico 1 (2 * r + 1)).card +
          ((Finset.range r).biUnion (gapBlock S (2 * r + 1))).card := Finset.card_union_le _ _
    _ ≤ 2 * r + ∑ j ∈ Finset.range r, (gapBlock S (2 * r + 1) j).card := by
        rw [Nat.card_Ico]
        exact Nat.add_le_add (by omega) Finset.card_biUnion_le

/-- **Answer to Problem 2, genus form (upper bound).**  If `m ≥ 3` is odd and `S` is a
submonoid of `ℕ` with multiplicity `m` and `C(S) ≤ 2`, then `S` is a numerical
semigroup and `g(S) ≤ 2m - 2`. -/
theorem genus_le_two_mul_sub_two {S : AddSubmonoid ℕ} {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m)
    (hS : HasMultiplicity S m) (hC : ConcentrationLeTwo S) :
    IsNumericalSemigroup S ∧ genus S ≤ 2 * m - 2 := by
  obtain ⟨r, rfl⟩ := hm
  obtain ⟨hfin, hle⟩ := genus_le_sum (r := r) (by omega) hS hC
  refine ⟨hfin, hle.trans ?_⟩
  have hsum : ∑ j ∈ Finset.range r, (gapBlock S (2 * r + 1) j).card ≤ ∑ _j ∈ Finset.range r, 2 :=
    Finset.sum_le_sum fun j _ => (card_gapBlock_le hS hC j).1
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum
  omega

/-- In the extremal case `g(S) = 2m - 2`, every block has exactly the two gaps
`m + 2j + 1` and `2m + 2j + 1`. -/
theorem notMem_of_genus_eq {S : AddSubmonoid ℕ} {r : ℕ} (hr : 1 ≤ r)
    (hS : HasMultiplicity S (2 * r + 1)) (hC : ConcentrationLeTwo S)
    (hg : genus S = 2 * (2 * r + 1) - 2) {j : ℕ} (hj : j < r) :
    2 * r + 1 + 2 * j + 1 ∉ S ∧ 2 * (2 * r + 1) + 2 * j + 1 ∉ S := by
  by_contra hcon
  have hcon' : 2 * r + 1 + 2 * j + 1 ∈ S ∨ 2 * (2 * r + 1) + 2 * j + 1 ∈ S := by tauto
  obtain ⟨_, hle⟩ := genus_le_sum hr hS hC
  have hsum : ∑ i ∈ Finset.range r, (gapBlock S (2 * r + 1) i).card < ∑ _i ∈ Finset.range r, 2 :=
    Finset.sum_lt_sum (fun i _ => (card_gapBlock_le hS hC i).1)
      ⟨j, Finset.mem_range.mpr hj, lt_of_le_of_lt ((card_gapBlock_le hS hC j).2 hcon') (by norm_num)⟩
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum
  omega

/-- The semigroup `⟨m, m+2, m+4, ..., 2m-1⟩`, i.e. generated by `m` and `m + 2j` for
`1 ≤ j ≤ (m-1)/2`. -/
def topSemigroup (m : ℕ) : AddSubmonoid ℕ :=
  AddSubmonoid.closure (insert m ((fun j => m + 2 * j) '' Set.Icc 1 ((m - 1) / 2)))

/-- Explicit description of `⟨m, m+2, ..., 2m-1⟩` for odd `m`: `0`, the odd numbers in
`[m, 2m)`, the even numbers in `[2m, 3m)`, and everything from `3m` on. -/
def TopPred (m x : ℕ) : Prop :=
  x = 0 ∨ (m ≤ x ∧ x < 2 * m ∧ x % 2 = 1) ∨ (2 * m ≤ x ∧ x < 3 * m ∧ x % 2 = 0) ∨ 3 * m ≤ x

/-- Membership in `⟨m, m+2, ..., 2m-1⟩` for odd `m`. -/
theorem mem_topSemigroup_iff {m : ℕ} (hm : Odd m) (x : ℕ) :
    x ∈ topSemigroup m ↔ TopPred m x := by
  obtain ⟨r, rfl⟩ := hm
  have hgen : ∀ y, 2 * r + 1 ≤ y → y < 2 * (2 * r + 1) → y % 2 = 1 → y ∈ topSemigroup (2 * r + 1) := by
    intro y h1 h2 h3
    apply AddSubmonoid.subset_closure
    rcases Nat.eq_or_lt_of_le h1 with h | h
    · exact h ▸ Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨(y - (2 * r + 1)) / 2, ⟨by omega, by omega⟩, by dsimp only; omega⟩
  constructor
  · intro hx
    induction hx using AddSubmonoid.closure_induction with
    | mem y hy =>
      rcases hy with rfl | ⟨j, ⟨hj1, hj2⟩, rfl⟩
      · unfold TopPred; omega
      · dsimp only; unfold TopPred; omega
    | zero => exact Or.inl rfl
    | add y z _ _ hy hz => unfold TopPred at hy hz ⊢; omega
  · intro hx
    induction x using Nat.strong_induction_on with
    | _ x ih =>
      unfold TopPred at hx
      rcases hx with rfl | hx | hx | hx
      · exact (topSemigroup _).zero_mem
      · exact hgen x hx.1 hx.2.1 hx.2.2
      · have h1 := hgen (x - (2 * r + 1)) (by omega) (by omega) (by omega)
        have h2 := (topSemigroup _).add_mem h1 (hgen (2 * r + 1) le_rfl (by omega) (by omega))
        rwa [show x - (2 * r + 1) + (2 * r + 1) = x by omega] at h2
      · by_cases hpred : TopPred (2 * r + 1) (x - (2 * r + 1))
        · have h1 := ih (x - (2 * r + 1)) (by omega) hpred
          have h2 := (topSemigroup _).add_mem h1 (hgen (2 * r + 1) le_rfl (by omega) (by omega))
          rwa [show x - (2 * r + 1) + (2 * r + 1) = x by omega] at h2
        · unfold TopPred at hpred
          have h1 := hgen (x - (4 * r + 1)) (by omega) (by omega) (by omega)
          have h2 := (topSemigroup _).add_mem h1 (hgen (4 * r + 1) (by omega) (by omega) (by omega))
          rwa [show x - (4 * r + 1) + (4 * r + 1) = x by omega] at h2

/-- `⟨m, m+2, ..., 2m-1⟩` has multiplicity `m` (odd `m`). -/
theorem topSemigroup_hasMultiplicity {m : ℕ} (hm : Odd m) : HasMultiplicity (topSemigroup m) m := by
  have hm0 : 0 < m := hm.pos
  have hm2 : m % 2 = 1 := Nat.odd_iff.mp hm
  refine ⟨hm0, (mem_topSemigroup_iff hm m).mpr ?_, fun x hx0 hxm hx => ?_⟩
  · unfold TopPred; omega
  · rw [mem_topSemigroup_iff hm] at hx; unfold TopPred at hx; omega

/-- `⟨m, m+2, ..., 2m-1⟩` has concentration at most `2` (odd `m`). -/
theorem topSemigroup_concentrationLeTwo {m : ℕ} (hm : Odd m) :
    ConcentrationLeTwo (topSemigroup m) := by
  have hm2 : m % 2 = 1 := Nat.odd_iff.mp hm
  intro s hs hs0
  rw [mem_topSemigroup_iff hm] at hs
  unfold TopPred at hs
  by_cases h1 : TopPred m (s + 1)
  · exact ⟨s + 1, (mem_topSemigroup_iff hm _).mpr h1, by omega, by omega⟩
  · refine ⟨s + 2, (mem_topSemigroup_iff hm _).mpr ?_, by omega, le_rfl⟩
    unfold TopPred at h1 ⊢; omega

/-- Lower bound: `⟨m, m+2, ..., 2m-1⟩` has at least `2m - 2` gaps (odd `m ≥ 3`). -/
theorem two_mul_sub_two_le_genus_topSemigroup {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    2 * m - 2 ≤ genus (topSemigroup m) := by
  classical
  have hm2 : m % 2 = 1 := Nat.odd_iff.mp hm
  let f : ℕ → ℕ := fun i =>
    if i < m - 1 then i + 1
    else if (i - (m - 1)) % 2 = 0 then m + (i - (m - 1)) + 1 else 2 * m + (i - (m - 1))
  have hsub : ↑((Finset.range (2 * m - 2)).image f) ⊆ ((topSemigroup m : Set ℕ)ᶜ) := by
    intro y hy
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    show f i ∉ topSemigroup m
    rw [mem_topSemigroup_iff hm]
    unfold TopPred
    simp only [f]
    split_ifs <;> simp only [false_or, not_or] <;> omega
  have hinj : Set.InjOn f ↑(Finset.range (2 * m - 2)) := by
    intro i hi j hj hij
    simp only [f] at hij
    split_ifs at hij <;> omega
  have hcard := Finset.card_image_of_injOn hinj
  rw [Finset.card_range] at hcard
  rw [← hcard, genus, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard hsub (genus_le_two_mul_sub_two hm hm3 (topSemigroup_hasMultiplicity hm)
    (topSemigroup_concentrationLeTwo hm)).1

/-- **Attainment.**  For odd `m ≥ 3`, `g(⟨m, m+2, ..., 2m-1⟩) = 2m - 2`. -/
theorem genus_topSemigroup {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    genus (topSemigroup m) = 2 * m - 2 :=
  le_antisymm (genus_le_two_mul_sub_two hm hm3 (topSemigroup_hasMultiplicity hm)
    (topSemigroup_concentrationLeTwo hm)).2 (two_mul_sub_two_le_genus_topSemigroup hm hm3)

/-- **Uniqueness of the extremal semigroup.**  For odd `m ≥ 3`, the only semigroup with
multiplicity `m`, `C(S) ≤ 2` and genus `2m - 2` is `⟨m, m+2, ..., 2m-1⟩`. -/
theorem eq_topSemigroup_of_genus_eq {S : AddSubmonoid ℕ} {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m)
    (hS : HasMultiplicity S m) (hC : ConcentrationLeTwo S) (hg : genus S = 2 * m - 2) :
    S = topSemigroup m := by
  have hm' := hm
  obtain ⟨r, rfl⟩ := hm'
  have hno := fun j (hj : j < r) => notMem_of_genus_eq (by omega) hS hC hg hj
  ext x
  rw [mem_topSemigroup_iff hm]
  unfold TopPred
  constructor
  · intro hx
    by_contra hcon
    have hx0 : x ≠ 0 := by omega
    have hxm : 2 * r + 1 ≤ x := by
      by_contra h
      exact hS.2.2 x (by omega) (by omega) hx
    rcases Nat.lt_or_ge x (2 * (2 * r + 1)) with h | h
    · have := (hno ((x - (2 * r + 1) - 1) / 2) (by omega)).1
      rw [show 2 * r + 1 + 2 * ((x - (2 * r + 1) - 1) / 2) + 1 = x by omega] at this
      exact this hx
    · have := (hno ((x - 2 * (2 * r + 1) - 1) / 2) (by omega)).2
      rw [show 2 * (2 * r + 1) + 2 * ((x - 2 * (2 * r + 1) - 1) / 2) + 1 = x by omega] at this
      exact this hx
  · rintro (rfl | hx | hx | hx)
    · exact S.zero_mem
    · rcases Nat.eq_or_lt_of_le hx.1 with h | h
      · exact h ▸ hS.2.1
      · have := succ_mem_of_notMem hS hC (by omega) (hno ((x - (2 * r + 1) - 2) / 2) (by omega)).1
        rwa [show 2 * r + 1 + 2 * ((x - (2 * r + 1) - 2) / 2) + 1 + 1 = x by omega] at this
    · rcases Nat.eq_or_lt_of_le hx.1 with h | h
      · rw [← h, two_mul]; exact S.add_mem hS.2.1 hS.2.1
      · have := two_mul_add_mem hS hC (c := (x - 2 * (2 * r + 1)) / 2) (by omega)
        rwa [show 2 * ((x - 2 * (2 * r + 1)) / 2) + 2 * (2 * r + 1) = x by omega] at this
    · exact mem_of_three_mul_le hm hm3 hS hC hx

/-- **Maximum genus in `C̄₂[m]`.**  For odd `m ≥ 3`, the greatest genus of a numerical
semigroup with multiplicity `m` and concentration at most `2` is `2m - 2`. -/
theorem isGreatest_genus {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    IsGreatest {g | ∃ S : AddSubmonoid ℕ, IsNumericalSemigroup S ∧ HasMultiplicity S m ∧
      ConcentrationLeTwo S ∧ genus S = g} (2 * m - 2) := by
  refine ⟨⟨topSemigroup m, (genus_le_two_mul_sub_two hm hm3 (topSemigroup_hasMultiplicity hm)
    (topSemigroup_concentrationLeTwo hm)).1, topSemigroup_hasMultiplicity hm,
    topSemigroup_concentrationLeTwo hm, genus_topSemigroup hm hm3⟩, ?_⟩
  rintro g ⟨S, -, hS, hC, rfl⟩
  exact (genus_le_two_mul_sub_two hm hm3 hS hC).2

/-! ## The tree `G(C̄₂[m])` and its height -/

/-- The ordinary (half-line) semigroup `Δ(m) = {0, m, →}`, root of the tree. -/
def ordinary (m : ℕ) : AddSubmonoid ℕ where
  carrier := {x | x = 0 ∨ m ≤ x}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    omega
  zero_mem' := Or.inl rfl

/-- Membership in `Δ(m)`. -/
theorem mem_ordinary {m x : ℕ} : x ∈ ordinary m ↔ x = 0 ∨ m ≤ x := Iff.rfl

/-- The Frobenius number `F(S) = max (ℕ \ S)` (as `sSup`; meaningful when the
complement is finite and nonempty, which is the only case used). -/
noncomputable def frobenius (S : AddSubmonoid ℕ) : ℕ := sSup ((S : Set ℕ)ᶜ)

/-- The parent of `S` in the tree `G(C̄₂[m])`: the semigroup `S ∪ {F(S)}`, written as
the submonoid generated by `S ∪ {F(S)}` (`mem_addFrobenius` shows it is exactly
`S ∪ {F(S)}`). -/
noncomputable def addFrobenius (S : AddSubmonoid ℕ) : AddSubmonoid ℕ :=
  AddSubmonoid.closure (insert (frobenius S) (S : Set ℕ))

/-- Membership in `C̄₂[m]`: numerical semigroups with multiplicity `m` and `C(S) ≤ 2`. -/
def InC2Bar (m : ℕ) (S : AddSubmonoid ℕ) : Prop :=
  IsNumericalSemigroup S ∧ HasMultiplicity S m ∧ ConcentrationLeTwo S

/-- Depth in the tree `G(C̄₂[m])`, whose edges are `(S, S ∪ {F(S)})`: `S` has depth `k`
when the path `S, S ∪ {F(S)}, ...` of length `k` stays in `C̄₂[m]`, ends at the root
`Δ(m)`, and does not meet the root earlier. -/
def IsAtDepth (m : ℕ) (S : AddSubmonoid ℕ) (k : ℕ) : Prop :=
  (∀ i ≤ k, InC2Bar m (addFrobenius^[i] S)) ∧ addFrobenius^[k] S = ordinary m ∧
    ∀ i < k, addFrobenius^[i] S ≠ ordinary m

/-- `F(S)` is a gap and every integer above it lies in `S`. -/
theorem frobenius_spec {S : AddSubmonoid ℕ} (hfin : IsNumericalSemigroup S)
    (hne : ((S : Set ℕ)ᶜ).Nonempty) :
    frobenius S ∉ S ∧ ∀ x, frobenius S < x → x ∈ S := by
  refine ⟨Nat.sSup_mem hne hfin.bddAbove, fun x hx => ?_⟩
  by_contra h
  exact absurd (le_csSup hfin.bddAbove (show x ∈ (S : Set ℕ)ᶜ from h)) (not_le.mpr hx)

/-- The generated submonoid `addFrobenius S` is exactly `S ∪ {F(S)}`. -/
theorem mem_addFrobenius {S : AddSubmonoid ℕ} (hfin : IsNumericalSemigroup S)
    (hne : ((S : Set ℕ)ᶜ).Nonempty) (x : ℕ) :
    x ∈ addFrobenius S ↔ x ∈ S ∨ x = frobenius S := by
  obtain ⟨hF, hgt⟩ := frobenius_spec hfin hne
  have hF0 : frobenius S ≠ 0 := fun h => hF (h ▸ S.zero_mem)
  constructor
  · intro hx
    induction hx using AddSubmonoid.closure_induction with
    | mem y hy =>
      rcases hy with rfl | hy
      · exact Or.inr rfl
      · exact Or.inl hy
    | zero => exact Or.inl S.zero_mem
    | add y z _ _ hy hz =>
      rcases hy with hy | rfl <;> rcases hz with hz | rfl
      · exact Or.inl (S.add_mem hy hz)
      · rcases Nat.eq_zero_or_pos y with rfl | hy0
        · exact Or.inr (zero_add _)
        · exact Or.inl (hgt _ (by omega))
      · rcases Nat.eq_zero_or_pos z with rfl | hz0
        · exact Or.inr (add_zero _)
        · exact Or.inl (hgt _ (by omega))
      · exact Or.inl (hgt _ (by omega))
  · rintro (hx | rfl)
    · exact AddSubmonoid.subset_closure (Set.mem_insert_of_mem _ hx)
    · exact AddSubmonoid.subset_closure (Set.mem_insert _ _)

/-- The gaps of `Δ(m)` are `[1, m)`. -/
theorem compl_ordinary (m : ℕ) : ((ordinary m : Set ℕ)ᶜ) = Set.Ico 1 m := by
  ext x
  simp only [Set.mem_compl_iff, SetLike.mem_coe, mem_ordinary, Set.mem_Ico]
  omega

/-- `g(Δ(m)) = m - 1`. -/
theorem genus_ordinary (m : ℕ) : genus (ordinary m) = m - 1 := by
  rw [genus, compl_ordinary, Set.ncard_Ico_nat]

/-- Every semigroup of multiplicity `m` has the gaps `[1, m)`. -/
theorem Ico_subset_compl {S : AddSubmonoid ℕ} {m : ℕ} (hS : HasMultiplicity S m) :
    Set.Ico 1 m ⊆ (S : Set ℕ)ᶜ := fun x hx => hS.2.2 x (by have := hx.1; omega) hx.2

/-- A numerical semigroup of multiplicity `m` and genus at most `m - 1` is `Δ(m)`. -/
theorem eq_ordinary_of_genus_le {S : AddSubmonoid ℕ} {m : ℕ} (hfin : IsNumericalSemigroup S)
    (hS : HasMultiplicity S m) (hg : genus S ≤ m - 1) : S = ordinary m := by
  have hEq : Set.Ico 1 m = (S : Set ℕ)ᶜ :=
    Set.eq_of_subset_of_ncard_le (Ico_subset_compl hS) (by rw [Set.ncard_Ico_nat]; exact hg) hfin
  rw [← compl_ordinary] at hEq
  exact SetLike.coe_injective (compl_injective hEq).symm

/-- A numerical semigroup of multiplicity `m` other than `Δ(m)` has a gap and
`F(S) > m`. -/
theorem frobenius_gt {S : AddSubmonoid ℕ} {m : ℕ} (hfin : IsNumericalSemigroup S)
    (hS : HasMultiplicity S m) (hne : S ≠ ordinary m) :
    ((S : Set ℕ)ᶜ).Nonempty ∧ m < frobenius S := by
  have : ∃ x, m < x ∧ x ∉ S := by
    by_contra h
    push Not at h
    apply hne
    ext x
    rw [mem_ordinary]
    constructor
    · intro hx
      by_contra h'
      exact hS.2.2 x (by omega) (by omega) hx
    · rintro (rfl | hx)
      · exact S.zero_mem
      · rcases Nat.eq_or_lt_of_le hx with rfl | hx
        · exact hS.2.1
        · exact h x hx
  obtain ⟨x, hx, hxS⟩ := this
  exact ⟨⟨x, hxS⟩, lt_of_lt_of_le hx (le_csSup hfin.bddAbove hxS)⟩

/-- Lemma 4 of the paper: for `S ∈ C̄₂[m]`, `S ≠ Δ(m)`, the parent `S ∪ {F(S)}` lies in
`C̄₂[m]`, and its genus is one less. -/
theorem addFrobenius_spec {S : AddSubmonoid ℕ} {m : ℕ} (hS : InC2Bar m S)
    (hne : S ≠ ordinary m) :
    InC2Bar m (addFrobenius S) ∧ genus (addFrobenius S) + 1 = genus S := by
  obtain ⟨hfin, hmul, hC⟩ := hS
  obtain ⟨hnon, hFm⟩ := frobenius_gt hfin hmul hne
  obtain ⟨hF, hgt⟩ := frobenius_spec hfin hnon
  have hcompl : ((addFrobenius S : Set ℕ)ᶜ) = (S : Set ℕ)ᶜ \ {frobenius S} := by
    ext x
    simp only [Set.mem_compl_iff, SetLike.mem_coe, mem_addFrobenius hfin hnon, Set.mem_sdiff,
      Set.mem_singleton_iff, not_or]
  refine ⟨⟨?_, ⟨hmul.1, ?_, fun x hx0 hxm hx => ?_⟩, fun s hs hs0 => ?_⟩, ?_⟩
  · rw [IsNumericalSemigroup, hcompl]; exact hfin.sdiff
  · exact (mem_addFrobenius hfin hnon _).mpr (Or.inl hmul.2.1)
  · rcases (mem_addFrobenius hfin hnon _).mp hx with hx | rfl
    · exact hmul.2.2 x hx0 hxm hx
    · omega
  · rcases (mem_addFrobenius hfin hnon _).mp hs with hs | rfl
    · obtain ⟨x, hx, h1, h2⟩ := hC s hs hs0
      exact ⟨x, (mem_addFrobenius hfin hnon _).mpr (Or.inl hx), h1, h2⟩
    · exact ⟨frobenius S + 1, (mem_addFrobenius hfin hnon _).mpr (Or.inl (hgt _ (by omega))),
        by omega, by omega⟩
  · rw [genus, genus, hcompl]
    exact Set.ncard_sdiff_singleton_add_one hF hfin

/-- Every `S ∈ C̄₂[m]` of genus `m - 1 + n` has depth `n`. -/
theorem isAtDepth_of_genus {m : ℕ} (n : ℕ) :
    ∀ S : AddSubmonoid ℕ, InC2Bar m S → genus S = m - 1 + n → IsAtDepth m S n := by
  induction n with
  | zero =>
    intro S hS hg
    have hSo := eq_ordinary_of_genus_le hS.1 hS.2.1 (by omega)
    refine ⟨fun i hi => ?_, hSo, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    rw [Nat.le_zero.mp hi]
    exact hS
  | succ n ih =>
    intro S hS hg
    have hne : S ≠ ordinary m := by
      rintro rfl
      rw [genus_ordinary] at hg
      omega
    obtain ⟨hS', hg'⟩ := addFrobenius_spec hS hne
    obtain ⟨h1, h2, h3⟩ := ih _ hS' (by omega)
    refine ⟨fun i hi => ?_, by rwa [Function.iterate_succ_apply], fun i hi => ?_⟩
    · rcases i with _ | i
      · exact hS
      · rw [Function.iterate_succ_apply]; exact h1 i (by omega)
    · rcases i with _ | i
      · exact hne
      · rw [Function.iterate_succ_apply]; exact h3 i (by omega)

/-- Depth is unique. -/
theorem IsAtDepth.unique {m : ℕ} {S : AddSubmonoid ℕ} {k k' : ℕ} (h : IsAtDepth m S k)
    (h' : IsAtDepth m S k') : k = k' := by
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · exact absurd h.2.1 (h'.2.2 k hlt)
  · exact heq
  · exact absurd h'.2.1 (h.2.2 k' hgt)

/-- Proposition 14(1) of the paper: for `S ∈ C̄₂[m]`, depth `k` ⇔ `g(S) = m - 1 + k`. -/
theorem isAtDepth_iff {m : ℕ} {S : AddSubmonoid ℕ} (hS : InC2Bar m S) (k : ℕ) :
    IsAtDepth m S k ↔ genus S = m - 1 + k := by
  have hge : m - 1 ≤ genus S :=
    (Set.ncard_Ico_nat 1 m).symm.le.trans (Set.ncard_le_ncard (Ico_subset_compl hS.2.1) hS.1)
  have hd := isAtDepth_of_genus (genus S - (m - 1)) S hS (by omega)
  constructor
  · intro h
    rw [h.unique hd]
    omega
  · intro hg
    exact isAtDepth_of_genus k S hS hg

/-- **Problem 2 of Rosales–Branco–Traesel (answer).**  For odd `m ≥ 3`, the height of the
tree `G(C̄₂[m])`, i.e. the greatest depth of a vertex, is `m - 1`. -/
theorem isGreatest_depth {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    IsGreatest {k | ∃ S : AddSubmonoid ℕ, InC2Bar m S ∧ IsAtDepth m S k} (m - 1) := by
  have hT : InC2Bar m (topSemigroup m) :=
    ⟨(genus_le_two_mul_sub_two hm hm3 (topSemigroup_hasMultiplicity hm) (topSemigroup_concentrationLeTwo hm)).1,
      topSemigroup_hasMultiplicity hm, topSemigroup_concentrationLeTwo hm⟩
  refine ⟨⟨topSemigroup m, hT, (isAtDepth_iff hT _).mpr ?_⟩, ?_⟩
  · rw [genus_topSemigroup hm hm3]; omega
  · rintro k ⟨S, hS, hk⟩
    have := (isAtDepth_iff hS k).mp hk
    have := (genus_le_two_mul_sub_two hm hm3 hS.2.1 hS.2.2).2
    omega

/-- `Δ(m)` lies in `C̄₂[m]` (it is the root of the tree). -/
theorem ordinary_mem_C2Bar {m : ℕ} (hm : 0 < m) : InC2Bar m (ordinary m) := by
  refine ⟨?_, ⟨hm, Or.inr le_rfl, fun x hx0 hxm hx => ?_⟩, fun s hs hs0 => ?_⟩
  · rw [IsNumericalSemigroup, compl_ordinary]; exact Set.finite_Ico _ _
  · rw [mem_ordinary] at hx; omega
  · rw [mem_ordinary] at hs
    exact ⟨s + 1, Or.inr (by omega), by omega, by omega⟩

/-! ## Ground truth and boundary checks -/

-- Paper Example 2: `⟨5, 7, 9⟩` is the case `m = 5` of `topSemigroup`, and it has
-- concentration `2` (in particular `≤ 2`).
example : topSemigroup 5 = AddSubmonoid.closure {5, 7, 9} := by
  unfold topSemigroup
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_image, Set.mem_Icc, Set.mem_singleton_iff]
  constructor
  · rintro (h | ⟨j, ⟨h1, h2⟩, rfl⟩)
    · exact Or.inl h
    · have : j ≤ 2 := by omega
      interval_cases j <;> simp
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr ⟨1, ⟨le_rfl, by norm_num⟩, by omega⟩
    · exact Or.inr ⟨2, ⟨by norm_num, by norm_num⟩, by omega⟩

example : ConcentrationLeTwo (topSemigroup 5) := topSemigroup_concentrationLeTwo ⟨2, rfl⟩

-- `3ℕ` has concentration `3`, so it fails `ConcentrationLeTwo`.
example : ¬ ConcentrationLeTwo (AddSubmonoid.closure {3}) := by
  intro h
  obtain ⟨x, hx, h1, h2⟩ := h 3 (AddSubmonoid.subset_closure rfl) (by norm_num)
  obtain ⟨n, rfl⟩ := AddSubmonoid.mem_closure_singleton.mp hx
  rw [smul_eq_mul] at h1 h2
  omega

-- `⟨3, 5⟩ = {0, 3, 5, 6, 8, 9, 10, …}`: gaps `1, 2, 4, 7`.
example : 7 ∉ topSemigroup 3 ∧ 8 ∈ topSemigroup 3 := by
  rw [mem_topSemigroup_iff (m := 3) ⟨1, rfl⟩, mem_topSemigroup_iff (m := 3) ⟨1, rfl⟩]
  unfold TopPred
  omega

example : genus (topSemigroup 3) = 4 := genus_topSemigroup ⟨1, rfl⟩ le_rfl

-- Paper Example 9 (the tree `G(C̄₂[3])`): the root `⟨3, 4, 5⟩ = Δ(3)` has depth `0`
-- and `⟨3, 5⟩` has depth `2`, the height.
example : IsAtDepth 3 (ordinary 3) 0 :=
  (isAtDepth_iff (ordinary_mem_C2Bar (by norm_num)) 0).mpr (by rw [genus_ordinary])

example : IsAtDepth 3 (topSemigroup 3) 2 := by
  have hT : InC2Bar 3 (topSemigroup 3) :=
    ⟨(genus_le_two_mul_sub_two ⟨1, rfl⟩ le_rfl (topSemigroup_hasMultiplicity ⟨1, rfl⟩)
      (topSemigroup_concentrationLeTwo ⟨1, rfl⟩)).1,
      topSemigroup_hasMultiplicity ⟨1, rfl⟩, topSemigroup_concentrationLeTwo ⟨1, rfl⟩⟩
  exact (isAtDepth_iff hT 2).mpr (by rw [genus_topSemigroup (m := 3) ⟨1, rfl⟩ le_rfl])

/-- Boundary check for the hypothesis `Odd m` (paper, Proposition 12): the semigroup
`{0, 4, 6, 8, 10, 12, 13, 14, …}` has multiplicity `4` and concentration `≤ 2` but genus
`7 > 2 · 4 - 2`. -/
def evenExample : AddSubmonoid ℕ where
  carrier := {x | x = 0 ∨ (4 ≤ x ∧ x % 2 = 0) ∨ 12 ≤ x}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    omega
  zero_mem' := Or.inl rfl

example : HasMultiplicity evenExample 4 ∧ ConcentrationLeTwo evenExample ∧
    IsNumericalSemigroup evenExample ∧ 2 * 4 - 2 < genus evenExample := by
  have hc : ((evenExample : Set ℕ)ᶜ) = ↑({1, 2, 3, 5, 7, 9, 11} : Finset ℕ) := by
    ext x
    simp only [Set.mem_compl_iff, SetLike.mem_coe, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    show ¬ (x = 0 ∨ (4 ≤ x ∧ x % 2 = 0) ∨ 12 ≤ x) ↔ _
    omega
  refine ⟨⟨by norm_num, Or.inr (Or.inl ⟨le_rfl, rfl⟩), fun x hx0 hx4 hx => ?_⟩,
    fun s hs hs0 => ?_, by rw [IsNumericalSemigroup, hc]; exact Finset.finite_toSet _, ?_⟩
  · change x = 0 ∨ (4 ≤ x ∧ x % 2 = 0) ∨ 12 ≤ x at hx; omega
  · change s = 0 ∨ (4 ≤ s ∧ s % 2 = 0) ∨ 12 ≤ s at hs
    exact ⟨s + 2, show s + 2 = 0 ∨ (4 ≤ s + 2 ∧ (s + 2) % 2 = 0) ∨ 12 ≤ s + 2 by omega,
      by omega, le_rfl⟩
  · rw [genus, hc, Set.ncard_coe_finset]; decide

/-- Paper-facing alias: **Problem 2** of Rosales–Branco–Traesel (arXiv:2103.16723,
end of Section 3).  For odd `m ≥ 3`, the height of the tree `G(C̄₂[m])` is `m - 1`. -/
theorem problem_2 {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    IsGreatest {k | ∃ S : AddSubmonoid ℕ, InC2Bar m S ∧ IsAtDepth m S k} (m - 1) :=
  isGreatest_depth hm hm3

end Candidates.ConcentrationTwoSemigroupTreeHeight
