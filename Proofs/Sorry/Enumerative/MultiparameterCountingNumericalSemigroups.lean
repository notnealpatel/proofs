/-
# Multiparameter counting of numerical semigroups: the refined Kaplan recurrence

## Source

arXiv:2607.23111, *Multiparameter counting of numerical semigroups: recurrences
and leaf-discriminating trees*, Section 2 ("Multiparameter exact Fibonacci
growth by genus and two-step doubling growth by Frobenius number"):
Theorem `t:twostepdoubling` (Section 2.3), Lemma `fmgmgran`, Theorem
`kaplanrefinat` and Remark `remkaplan` (Section 2.4, "Fibonacci-like growth by
the genus").

`n_{F,m,g}` is the number of numerical semigroups with Frobenius number `F`,
multiplicity `m` (least nonzero element) and genus `g` (number of gaps);
`n_{F,m}` drops the genus.

Verbatim printed claims:

> Theorem (kaplanrefinat). Let $F,m$ be nonnegative integers such that
> $\frac{F+2}{3}\leq m\leq F-1$. It holds
> $$n_{F,m,g}=n_{F-2,m-1,g-1}+n_{F-2,m-1,g-2}.$$

> Theorem (t:twostepdoubling). Let $F,m$ be nonnegative integers. If
> $\frac{F+2}{3}\leq m<F-1$, then $$n_{F,m}=2n_{F-2,m-1}.$$

Status (2026-10-21): proved in the paper, but `kaplanrefinat` as printed is
false at the boundary `m = F - 1`: `S = ⟨2,5⟩` gives `n_{3,2,2} = 1` while
`n_{1,1,1} + n_{1,1,0} = 0` (the proof applies Lemma `fmgmgran` at
`m - 1 = F - 2`, outside its range).  The corrected bound is `m ≤ F - 2`, the
same as in `t:twostepdoubling`.

## What this module proves

* `kaplan_refined`: for `F + 2 ≤ 3m`, `m + 2 ≤ F`, `2 ≤ g`,
  `n_{F,m,g} = n_{F-2,m-1,g-1} + n_{F-2,m-1,g-2}`;
* `two_step_doubling`: for `F + 2 ≤ 3m`, `m + 2 ≤ F`, `n_{F,m} = 2 n_{F-2,m-1}`;
* `printed_bound_false`: the printed hypothesis `m ≤ F - 1` does not suffice.

Proof: one explicit bijection `𝒮_{F,m} ≃ 𝒮_{F-2,m-1} × Bool` in each regime,
`S ↦ (ψ⁻¹(S), [d ∈ S])`, abstracted in `Transfer`.  For `2m < F` the
reindexing `ψ(q(m-1)+r) = qm + r` deletes the last Kunz coordinate (Remark
`remkaplan`, `d = 2m - 1`); for `F < 2m` the reindexing shifts `[1, F-2)` by
one and `[F-2, ∞)` by two (Lemma `fmgmgran`, `d = F - 1`); `F = 2m` is empty on
both sides.  The genus drops by `1` if `d ∈ S` and by `2` otherwise.
-/
import Mathlib
import Enumerative.NumericalSemigroupLeafInternal

set_option autoImplicit false

namespace Candidates.MultiparameterCountingNumericalSemigroups

open Candidates.NumericalSemigroupLeafInternal

/-- The genus of `S`: the number of gaps, `#(ℕ \ S)` (`Set.ncard`, so `0` if infinite;
every semigroup counted below has finite complement). -/
noncomputable def genus (S : AddSubmonoid ℕ) : ℕ := ((S : Set ℕ)ᶜ).ncard

/-- Numerical semigroups with Frobenius number `F`, multiplicity `m`, and genus satisfying `P`. -/
def nsSetP (F m : ℕ) (P : ℕ → Prop) : Set (AddSubmonoid ℕ) :=
  {S | HasFrobenius S F ∧ HasMultiplicity S m ∧ P (genus S)}

/-- `𝒮_{F,m,g}`: numerical semigroups with Frobenius number `F`, multiplicity `m`, genus `g`. -/
def nsSet (F m g : ℕ) : Set (AddSubmonoid ℕ) := nsSetP F m (· = g)

/-- `n_{F,m,g} = #𝒮_{F,m,g}`, the number of numerical semigroups with Frobenius number `F`,
multiplicity `m` and genus `g` (arXiv:2607.23111, Section 2.1). -/
noncomputable def nFmg (F m g : ℕ) : ℕ := (nsSet F m g).ncard

/-- Abstract data of the bijection `𝒮_{F,m} ≃ 𝒮_{F',m'} × Bool`: a strictly monotone
reindexing `ψ` whose range misses only the forced gap `c` and the free position `d`
below `F`, and which is additive on the sums of nonzero elements that matter. -/
structure Transfer (F m F' m' c d : ℕ) (ψ : ℕ → ℕ) : Prop where
  mono : StrictMono ψ
  zero : ψ 0 = 0
  cover : ∀ x ≤ F, (∃ y, ψ y = x) ∨ x = c ∨ x = d
  ne_c : ∀ y, ψ y ≠ c
  ne_d : ∀ y, ψ y ≠ d
  c_pos : 0 < c
  c_lt : c < m
  m_lt_d : m < d
  d_lt : d < F
  lt_d_add : F < d + m
  frob : ψ F' = F
  mult : ψ m' = m
  add_le : ∀ y₁ y₂, m' ≤ y₁ → m' ≤ y₂ → y₁ + y₂ ≤ F' → ψ (y₁ + y₂) = ψ y₁ + ψ y₂
  add_gt : ∀ y₁ y₂, m' ≤ y₁ → m' ≤ y₂ → F' < y₁ + y₂ → F < ψ y₁ + ψ y₂

/-- The submonoid `ψ⁻¹(S)`, given the closure facts that make it a submonoid. -/
def pull (ψ : ℕ → ℕ) (S : AddSubmonoid ℕ) (h0 : ψ 0 ∈ S)
    (hadd : ∀ a b, ψ a ∈ S → ψ b ∈ S → ψ (a + b) ∈ S) : AddSubmonoid ℕ where
  carrier := {y | ψ y ∈ S}
  zero_mem' := h0
  add_mem' := fun {a b} ha hb => hadd a b ha hb

/-- A positive number below the multiplicity is a gap. -/
theorem notMem_of_pos_of_lt {S : AddSubmonoid ℕ} {m x : ℕ} (hm : HasMultiplicity S m)
    (hx0 : 0 < x) (hxm : x < m) : x ∉ S := fun hx => absurd (hm.2.2 x hx hx0) (not_le.2 hxm)

/-- Membership predicate of the reconstructed semigroup. -/
def pushPred (F d : ℕ) (ψ : ℕ → ℕ) (T : AddSubmonoid ℕ) (b : Bool) (x : ℕ) : Prop :=
  F < x ∨ (∃ y ∈ T, ψ y = x) ∨ (b = true ∧ x = d)

/-- The submonoid `ψ(T) ∪ (F, ∞) ∪ ({d} if b)`, given its closure facts. -/
def push (F d : ℕ) (ψ : ℕ → ℕ) (T : AddSubmonoid ℕ) (b : Bool)
    (h0 : pushPred F d ψ T b 0)
    (hadd : ∀ x₁ x₂, pushPred F d ψ T b x₁ → pushPred F d ψ T b x₂ →
      pushPred F d ψ T b (x₁ + x₂)) : AddSubmonoid ℕ where
  carrier := {x | pushPred F d ψ T b x}
  zero_mem' := h0
  add_mem' := fun {a b} ha hb => hadd a b ha hb

namespace Transfer

variable {F m F' m' c d : ℕ} {ψ : ℕ → ℕ}

/-- `ψ y < m ↔ y < m'`. -/
theorem lt_m_iff (hT : Transfer F m F' m' c d ψ) (y : ℕ) : ψ y < m ↔ y < m' := by
  rw [← hT.mult]; exact hT.mono.lt_iff_lt

/-- `F < ψ y ↔ F' < y`. -/
theorem gt_F_iff (hT : Transfer F m F' m' c d ψ) (y : ℕ) : F < ψ y ↔ F' < y := by
  rw [← hT.frob]; exact hT.mono.lt_iff_lt

/-- `ψ` preserves positivity. -/
theorem pos_iff (hT : Transfer F m F' m' c d ψ) (y : ℕ) : 0 < ψ y ↔ 0 < y := by
  have h := hT.mono.lt_iff_lt (a := 0) (b := y)
  rwa [hT.zero] at h

/-- The smaller multiplicity is positive. -/
theorem m'_pos (hT : Transfer F m F' m' c d ψ) : 0 < m' := by
  rw [← hT.pos_iff, hT.mult]; exact hT.c_pos.trans hT.c_lt

/-- `ψ 0 = 0` lies in every submonoid. -/
theorem zero_mem (hT : Transfer F m F' m' c d ψ) (S : AddSubmonoid ℕ) : ψ 0 ∈ S := by
  rw [hT.zero]; exact S.zero_mem

/-- `ψ⁻¹(S)` is closed under addition when `S` has Frobenius number `F` and multiplicity `m`. -/
theorem pull_closed (hT : Transfer F m F' m' c d ψ) {S : AddSubmonoid ℕ}
    (hF : HasFrobenius S F) (hm : HasMultiplicity S m) :
    ∀ a b, ψ a ∈ S → ψ b ∈ S → ψ (a + b) ∈ S := by
  intro a b ha hb
  rcases Nat.eq_zero_or_pos a with rfl | ha0
  · simpa using hb
  rcases Nat.eq_zero_or_pos b with rfl | hb0
  · simpa using ha
  have hma : m' ≤ a := by
    rw [← not_lt, ← hT.lt_m_iff]; exact not_lt.2 (hm.2.2 _ ha ((hT.pos_iff a).2 ha0))
  have hmb : m' ≤ b := by
    rw [← not_lt, ← hT.lt_m_iff]; exact not_lt.2 (hm.2.2 _ hb ((hT.pos_iff b).2 hb0))
  by_cases hab : a + b ≤ F'
  · rw [hT.add_le a b hma hmb hab]; exact S.add_mem ha hb
  · exact hF.2 _ ((hT.gt_F_iff _).2 (Nat.lt_of_not_le hab))



section PullFacts

variable (hT : Transfer F m F' m' c d ψ) {S : AddSubmonoid ℕ}
  (hF : HasFrobenius S F) (hm : HasMultiplicity S m)
include hT hF hm

/-- `ψ⁻¹(S)` has Frobenius number `F'`. -/
theorem pull_hasFrobenius :
    HasFrobenius (pull ψ S (hT.zero_mem S) (hT.pull_closed hF hm)) F' := by
  refine ⟨?_, fun y hy => ?_⟩
  · change ψ F' ∉ S
    rw [hT.frob]; exact hF.1
  · exact hF.2 _ ((hT.gt_F_iff y).2 hy)

/-- `ψ⁻¹(S)` has multiplicity `m'`. -/
theorem pull_hasMultiplicity :
    HasMultiplicity (pull ψ S (hT.zero_mem S) (hT.pull_closed hF hm)) m' := by
  refine ⟨hT.m'_pos, ?_, fun y hy hy0 => ?_⟩
  · change ψ m' ∈ S
    rw [hT.mult]; exact hm.2.1
  · rw [← not_lt, ← hT.lt_m_iff]
    exact not_lt.2 (hm.2.2 _ hy ((hT.pos_iff y).2 hy0))

/-- Gaps of `S` when `d ∈ S`: `c` together with `ψ` of the gaps of `ψ⁻¹(S)`. -/
theorem compl_eq_of_mem (hd : d ∈ S) :
    (S : Set ℕ)ᶜ = insert c (ψ '' ((pull ψ S (hT.zero_mem S) (hT.pull_closed hF hm) : Set ℕ)ᶜ)) := by
  ext x
  simp only [Set.mem_compl_iff, SetLike.mem_coe, Set.mem_insert_iff, Set.mem_image]
  constructor
  · intro hx
    have hxF : x ≤ F := by
      by_contra h; exact hx (hF.2 x (Nat.lt_of_not_le h))
    rcases hT.cover x hxF with ⟨y, rfl⟩ | rfl | rfl
    · exact Or.inr ⟨y, hx, rfl⟩
    · exact Or.inl rfl
    · exact absurd hd hx
  · rintro (rfl | ⟨y, hy, rfl⟩)
    · exact notMem_of_pos_of_lt hm hT.c_pos hT.c_lt
    · exact hy

/-- Gaps of `S` when `d ∉ S`: `d`, `c`, and `ψ` of the gaps of `ψ⁻¹(S)`. -/
theorem compl_eq_of_not_mem (hd : d ∉ S) :
    (S : Set ℕ)ᶜ = insert d (insert c
      (ψ '' ((pull ψ S (hT.zero_mem S) (hT.pull_closed hF hm) : Set ℕ)ᶜ))) := by
  ext x
  simp only [Set.mem_compl_iff, SetLike.mem_coe, Set.mem_insert_iff, Set.mem_image]
  constructor
  · intro hx
    have hxF : x ≤ F := by
      by_contra h; exact hx (hF.2 x (Nat.lt_of_not_le h))
    rcases hT.cover x hxF with ⟨y, rfl⟩ | rfl | rfl
    · exact Or.inr (Or.inr ⟨y, hx, rfl⟩)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  · rintro (rfl | rfl | ⟨y, hy, rfl⟩)
    · exact hd
    · exact notMem_of_pos_of_lt hm hT.c_pos hT.c_lt
    · exact hy

/-- `ψ⁻¹(S)` has finitely many gaps. -/
theorem pull_compl_finite :
    ((pull ψ S (hT.zero_mem S) (hT.pull_closed hF hm) : Set ℕ)ᶜ).Finite := by
  refine (Set.finite_Iic F').subset fun y hy => ?_
  by_contra h
  exact hy ((pull_hasFrobenius hT hF hm).2 y (Nat.lt_of_not_le h))

/-- If `d ∈ S`, the genus drops by one under `S ↦ ψ⁻¹(S)`. -/
theorem genus_of_mem (hd : d ∈ S) :
    genus S = genus (pull ψ S (hT.zero_mem S) (hT.pull_closed hF hm)) + 1 := by
  have hfin := pull_compl_finite hT hF hm
  unfold genus
  rw [compl_eq_of_mem hT hF hm hd, Set.ncard_insert_of_notMem _ (hfin.image ψ),
    Set.ncard_image_of_injective _ hT.mono.injective]
  rintro ⟨y, -, hy⟩
  exact hT.ne_c y hy

/-- If `d ∉ S`, the genus drops by two under `S ↦ ψ⁻¹(S)`. -/
theorem genus_of_not_mem (hd : d ∉ S) :
    genus S = genus (pull ψ S (hT.zero_mem S) (hT.pull_closed hF hm)) + 2 := by
  have hfin := pull_compl_finite hT hF hm
  have hc : c ∉ ψ '' ((pull ψ S (hT.zero_mem S) (hT.pull_closed hF hm) : Set ℕ)ᶜ) := by
    rintro ⟨y, -, hy⟩
    exact hT.ne_c y hy
  have hdc : d ∉ insert c (ψ '' ((pull ψ S (hT.zero_mem S) (hT.pull_closed hF hm) : Set ℕ)ᶜ)) := by
    rintro (h | ⟨y, -, hy⟩)
    · exact absurd h (ne_of_gt (hT.c_lt.trans hT.m_lt_d))
    · exact hT.ne_d y hy
  unfold genus
  rw [compl_eq_of_not_mem hT hF hm hd, Set.ncard_insert_of_notMem hdc ((hfin.image ψ).insert c),
    Set.ncard_insert_of_notMem hc (hfin.image ψ),
    Set.ncard_image_of_injective _ hT.mono.injective]

end PullFacts


/-- `0` satisfies the reconstruction predicate. -/
theorem push_zero (hT : Transfer F m F' m' c d ψ) (T : AddSubmonoid ℕ) (b : Bool) :
    pushPred F d ψ T b 0 :=
  Or.inr (Or.inl ⟨0, T.zero_mem, hT.zero⟩)

section PushFacts

variable (hT : Transfer F m F' m' c d ψ) {T : AddSubmonoid ℕ}
  (hF : HasFrobenius T F') (hm : HasMultiplicity T m') (b : Bool)
include hT hF hm

omit hF in
/-- Nonzero elements of the reconstruction are at least `m`. -/
theorem m_le_of_pushPred {x : ℕ} (hx : pushPred F d ψ T b x) (hx0 : 0 < x) : m ≤ x := by
  rcases hx with hx | ⟨y, hyT, rfl⟩ | ⟨-, rfl⟩
  · exact (hT.m_lt_d.trans hT.d_lt).le.trans hx.le
  · have hy0 : 0 < y := (hT.pos_iff y).1 hx0
    rw [← not_lt, hT.lt_m_iff, not_lt]
    exact hm.2.2 y hyT hy0
  · exact hT.m_lt_d.le

omit hF in
/-- The reconstruction predicate is closed under addition. -/
theorem push_closed :
    ∀ x₁ x₂, pushPred F d ψ T b x₁ → pushPred F d ψ T b x₂ → pushPred F d ψ T b (x₁ + x₂) := by
  intro x₁ x₂ h₁ h₂
  rcases Nat.eq_zero_or_pos x₁ with rfl | h₁0
  · simpa using h₂
  rcases Nat.eq_zero_or_pos x₂ with rfl | h₂0
  · simpa using h₁
  have hm₁ := m_le_of_pushPred hT hm b h₁ h₁0
  have hm₂ := m_le_of_pushPred hT hm b h₂ h₂0
  by_cases hsum : F < x₁ + x₂
  · exact Or.inl hsum
  have hsum' : x₁ + x₂ ≤ F := Nat.le_of_not_lt hsum
  have hd := hT.lt_d_add
  rcases h₁ with h₁ | ⟨y₁, hy₁T, rfl⟩ | ⟨-, rfl⟩
  · omega
  · rcases h₂ with h₂ | ⟨y₂, hy₂T, rfl⟩ | ⟨-, rfl⟩
    · omega
    · have hy₁ : m' ≤ y₁ := by rw [← not_lt, ← hT.lt_m_iff]; omega
      have hy₂ : m' ≤ y₂ := by rw [← not_lt, ← hT.lt_m_iff]; omega
      by_cases hy : y₁ + y₂ ≤ F'
      · exact Or.inr (Or.inl ⟨y₁ + y₂, T.add_mem hy₁T hy₂T, hT.add_le y₁ y₂ hy₁ hy₂ hy⟩)
      · exact absurd (hT.add_gt y₁ y₂ hy₁ hy₂ (Nat.lt_of_not_le hy)) hsum
    · omega
  · omega

/-- The reconstruction has Frobenius number `F`. -/
theorem push_hasFrobenius :
    HasFrobenius (push F d ψ T b (hT.push_zero T b) (hT.push_closed hm b)) F := by
  refine ⟨?_, fun x hx => Or.inl hx⟩
  rintro (h | ⟨y, hyT, hy⟩ | ⟨-, h⟩)
  · exact lt_irrefl F h
  · rw [← hT.frob] at hy
    rw [hT.mono.injective hy] at hyT
    exact hF.1 hyT
  · exact absurd h (ne_of_gt hT.d_lt)

omit hF in
/-- The reconstruction has multiplicity `m`. -/
theorem push_hasMultiplicity :
    HasMultiplicity (push F d ψ T b (hT.push_zero T b) (hT.push_closed hm b)) m := by
  refine ⟨hT.c_pos.trans hT.c_lt, Or.inr (Or.inl ⟨m', hm.2.1, hT.mult⟩), fun x hx hx0 => ?_⟩
  exact m_le_of_pushPred hT hm b hx hx0

omit hF in
/-- The free position `d` lies in the reconstruction iff the bit is set. -/
theorem mem_push_d :
    d ∈ push F d ψ T b (hT.push_zero T b) (hT.push_closed hm b) ↔ b = true := by
  constructor
  · rintro (h | ⟨y, -, hy⟩ | ⟨hb, -⟩)
    · exact absurd h (not_lt.2 hT.d_lt.le)
    · exact absurd hy (hT.ne_d y)
    · exact hb
  · intro hb
    exact Or.inr (Or.inr ⟨hb, rfl⟩)

/-- Pulling back the reconstruction recovers `T`. -/
theorem pull_push :
    pull ψ (push F d ψ T b (hT.push_zero T b) (hT.push_closed hm b))
      (hT.zero_mem _) (hT.pull_closed (push_hasFrobenius hT hF hm b) (push_hasMultiplicity hT hm b))
      = T := by
  ext y
  change pushPred F d ψ T b (ψ y) ↔ y ∈ T
  constructor
  · rintro (h | ⟨y', hy'T, hy'⟩ | ⟨-, h⟩)
    · exact hF.2 y ((hT.gt_F_iff y).1 h)
    · rwa [← hT.mono.injective hy']
    · exact absurd h (hT.ne_d y)
  · intro hy
    exact Or.inr (Or.inl ⟨y, hy, rfl⟩)

end PushFacts

/-- A semigroup in `𝒮_{F,m}` is determined by `ψ⁻¹(S)` and whether `d ∈ S`. -/
theorem eq_of_pull (hT : Transfer F m F' m' c d ψ) {S₁ S₂ : AddSubmonoid ℕ}
    (hF₁ : HasFrobenius S₁ F) (hm₁ : HasMultiplicity S₁ m)
    (hF₂ : HasFrobenius S₂ F) (hm₂ : HasMultiplicity S₂ m)
    (hd : d ∈ S₁ ↔ d ∈ S₂) (h : ∀ y, ψ y ∈ S₁ ↔ ψ y ∈ S₂) : S₁ = S₂ := by
  ext x
  by_cases hxF : F < x
  · exact iff_of_true (hF₁.2 x hxF) (hF₂.2 x hxF)
  rcases hT.cover x (Nat.le_of_not_lt hxF) with ⟨y, rfl⟩ | rfl | rfl
  · exact h y
  · exact iff_of_false (notMem_of_pos_of_lt hm₁ hT.c_pos hT.c_lt)
      (notMem_of_pos_of_lt hm₂ hT.c_pos hT.c_lt)
  · exact hd

/-- The semigroups in `𝒮_{F,m}` with prescribed membership of `d` correspond to `𝒮_{F',m'}`,
with genus shifted by `1` (if `d ∈ S`) or `2` (if `d ∉ S`). -/
theorem ncard_part (hT : Transfer F m F' m' c d ψ) (P : ℕ → Prop) (b : Bool) :
    (nsSetP F m P ∩ {S | d ∈ S ↔ b = true}).ncard =
      (nsSetP F' m' (fun k => P (k + cond b 1 2))).ncard := by
  refine Set.ncard_congr
    (fun S hS => pull ψ S (hT.zero_mem S) (hT.pull_closed hS.1.1 hS.1.2.1)) ?_ ?_ ?_
  · rintro S ⟨⟨hF, hm, hg⟩, hd⟩
    refine ⟨pull_hasFrobenius hT hF hm, pull_hasMultiplicity hT hF hm, ?_⟩
    cases b with
    | true =>
      rw [genus_of_mem hT hF hm (hd.2 rfl)] at hg
      exact hg
    | false =>
      rw [genus_of_not_mem hT hF hm (fun h' => Bool.false_ne_true (hd.1 h'))] at hg
      exact hg
  · intro S₁ S₂ hS₁ hS₂ hpull
    exact eq_of_pull hT hS₁.1.1 hS₁.1.2.1 hS₂.1.1 hS₂.1.2.1 (hS₁.2.trans hS₂.2.symm)
      fun y => SetLike.ext_iff.1 hpull y
  · rintro T ⟨hF, hm, hg⟩
    refine ⟨push F d ψ T b (hT.push_zero T b) (hT.push_closed hm b),
      ⟨⟨push_hasFrobenius hT hF hm b, push_hasMultiplicity hT hm b, ?_⟩,
        mem_push_d hT hm b⟩, pull_push hT hF hm b⟩
    have hFp := push_hasFrobenius hT hF hm b
    have hmp := push_hasMultiplicity hT hm b
    cases b with
    | true =>
      rw [genus_of_mem hT hFp hmp ((mem_push_d hT hm true).2 rfl), pull_push hT hF hm true]
      exact hg
    | false =>
      rw [genus_of_not_mem hT hFp hmp
        (fun h' => Bool.false_ne_true ((mem_push_d hT hm false).1 h')), pull_push hT hF hm false]
      exact hg

/-- Abstract recurrence: `#{S ∈ 𝒮_{F,m} | P(g(S))} =
#{T ∈ 𝒮_{F',m'} | P(g(T)+1)} + #{T ∈ 𝒮_{F',m'} | P(g(T)+2)}`. -/
theorem ncard_split (hT : Transfer F m F' m' c d ψ) (P : ℕ → Prop) :
    (nsSetP F m P).ncard =
      (nsSetP F' m' (fun k => P (k + 1))).ncard + (nsSetP F' m' (fun k => P (k + 2))).ncard := by
  have hfin : (nsSetP F m P).Finite :=
    (setOf_hasFrobenius_finite F).subset fun S hS => hS.1
  have h1 := ncard_part hT P true
  have h2 := ncard_part hT P false
  simp only [cond_true, cond_false] at h1 h2
  rw [← Set.ncard_inter_add_ncard_sdiff_eq_ncard (nsSetP F m P) {S | d ∈ S} hfin, ← h1, ← h2]
  congr 2
  · ext S
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, iff_true]
  · ext S
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h, hd⟩; exact ⟨h, fun h' => absurd h' hd, fun h' => absurd h' Bool.false_ne_true⟩
    · rintro ⟨h, hd⟩; exact ⟨h, fun h' => Bool.false_ne_true (hd.1 h')⟩

end Transfer

/-! ## The two instances -/

/-- Kunz reindexing `q (m-1) + r ↦ q m + r` (`r < m - 1`), written with `n = m - 1`. -/
def kunzShift (n y : ℕ) : ℕ := y + y / n

/-- `kunzShift n` on the ranges `[0,n)`, `[n,2n)`, `[2n,3n)`, `[3n,∞)`. -/
theorem kunzShift_cases {n : ℕ} (hn : 0 < n) (y : ℕ) :
    (y < n ∧ kunzShift n y = y) ∨ (n ≤ y ∧ y < 2 * n ∧ kunzShift n y = y + 1) ∨
      (2 * n ≤ y ∧ y < 3 * n ∧ kunzShift n y = y + 2) ∨ (3 * n ≤ y ∧ y + 3 ≤ kunzShift n y) := by
  unfold kunzShift
  rcases lt_or_ge y n with h1 | h1
  · exact Or.inl ⟨h1, by rw [Nat.div_eq_of_lt h1, Nat.add_zero]⟩
  rcases lt_or_ge y (2 * n) with h2 | h2
  · refine Or.inr (Or.inl ⟨h1, h2, ?_⟩)
    rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
  rcases lt_or_ge y (3 * n) with h3 | h3
  · refine Or.inr (Or.inr (Or.inl ⟨h2, h3, ?_⟩))
    rw [Nat.div_eq_of_lt_le (k := 2) (by omega) (by omega)]
  · refine Or.inr (Or.inr (Or.inr ⟨h3, ?_⟩))
    have h : 3 ≤ y / n := (Nat.le_div_iff_mul_le hn).2 (by omega)
    omega

/-- Case `2m < F ≤ 3m - 2` (Remark `remkaplan`): Kunz deletion of the last residue. -/
theorem transfer_kunz {F' n : ℕ} (h1 : 2 * n < F') (h2 : F' + 1 ≤ 3 * n) :
    Transfer (F' + 2) (n + 1) F' n n (2 * n + 1) (kunzShift n) := by
  have hn : 0 < n := by omega
  have hc := kunzShift_cases hn
  refine
    { mono := ?_, zero := ?_, cover := ?_, ne_c := ?_, ne_d := ?_, c_pos := hn, c_lt := ?_,
      m_lt_d := ?_, d_lt := ?_, lt_d_add := ?_, frob := ?_, mult := ?_, add_le := ?_,
      add_gt := ?_ }
  · intro a b hab
    exact add_lt_add_of_lt_of_le hab (Nat.div_le_div_right hab.le)
  · simp [kunzShift]
  · intro x hx
    by_cases hx1 : x < n
    · exact Or.inl ⟨x, by have hA := hc x; omega⟩
    by_cases hx2 : x = n
    · exact Or.inr (Or.inl hx2)
    by_cases hx3 : x ≤ 2 * n
    · exact Or.inl ⟨x - 1, by have hA := hc (x - 1); omega⟩
    by_cases hx4 : x = 2 * n + 1
    · exact Or.inr (Or.inr hx4)
    · exact Or.inl ⟨x - 2, by have hA := hc (x - 2); omega⟩
  · intro y; have hA := hc y; omega
  · intro y; have hA := hc y; omega
  · omega
  · omega
  · omega
  · omega
  · have hA := hc F'; omega
  · have hA := hc n; omega
  · intro y₁ y₂ hy₁ hy₂ hy
    have hA := hc y₁; have hB := hc y₂; have hC := hc (y₁ + y₂); omega
  · intro y₁ y₂ hy₁ hy₂ hy
    have hA := hc y₁; have hB := hc y₂; omega

/-- Shift used below `2m`: `0 ↦ 0`, `[1, F - 2) ↦ +1`, `[F - 2, ∞) ↦ +2`. -/
def stepShift (F' y : ℕ) : ℕ := if y = 0 then 0 else if y < F' then y + 1 else y + 2

/-- `stepShift F'` on its three pieces. -/
theorem stepShift_cases (F' y : ℕ) :
    (y = 0 ∧ stepShift F' y = 0) ∨ (0 < y ∧ y < F' ∧ stepShift F' y = y + 1) ∨
      (0 < y ∧ F' ≤ y ∧ stepShift F' y = y + 2) := by
  unfold stepShift
  by_cases h0 : y = 0
  · exact Or.inl ⟨h0, if_pos h0⟩
  rw [if_neg h0]
  by_cases h1 : y < F'
  · exact Or.inr (Or.inl ⟨Nat.pos_of_ne_zero h0, h1, if_pos h1⟩)
  · exact Or.inr (Or.inr ⟨Nat.pos_of_ne_zero h0, Nat.le_of_not_lt h1, if_neg h1⟩)

/-- Case `m + 2 ≤ F < 2m` (Lemma `fmgmgran`): the free position is `F - 1`. -/
theorem transfer_step {F' n : ℕ} (h1 : n + 1 ≤ F') (h2 : F' < 2 * n) :
    Transfer (F' + 2) (n + 1) F' n 1 (F' + 1) (stepShift F') := by
  have hc := stepShift_cases F'
  refine
    { mono := ?_, zero := ?_, cover := ?_, ne_c := ?_, ne_d := ?_, c_pos := Nat.one_pos,
      c_lt := ?_, m_lt_d := ?_, d_lt := ?_, lt_d_add := ?_, frob := ?_, mult := ?_,
      add_le := ?_, add_gt := ?_ }
  · intro a b hab
    have ha := hc a
    have hb := hc b
    omega
  · simp [stepShift]
  · intro x hx
    by_cases hx0 : x = 0
    · exact Or.inl ⟨0, by have hA := hc 0; omega⟩
    by_cases hx1 : x = 1
    · exact Or.inr (Or.inl hx1)
    by_cases hx2 : x ≤ F'
    · exact Or.inl ⟨x - 1, by have hA := hc (x - 1); omega⟩
    by_cases hx3 : x = F' + 1
    · exact Or.inr (Or.inr hx3)
    · exact Or.inl ⟨F', by have hA := hc F'; omega⟩
  · intro y; have hA := hc y; omega
  · intro y; have hA := hc y; omega
  · omega
  · omega
  · omega
  · omega
  · have hA := hc F'; omega
  · have hA := hc n; omega
  · intro y₁ y₂ hy₁ hy₂ hy
    omega
  · intro y₁ y₂ hy₁ hy₂ hy
    have hA := hc y₁; have hB := hc y₂; omega

/-- No numerical semigroup has Frobenius number twice its multiplicity. -/
theorem nsSetP_two_mul_eq_empty (n : ℕ) (P : ℕ → Prop) : nsSetP (2 * n) n P = ∅ := by
  ext S
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hF, hm, -⟩
  apply hF.1
  rw [two_mul]
  exact S.add_mem hm.2.1 hm.2.1

/-- The abstract recurrence at `F = F' + 2`, `m = n + 1` with `F' + 1 ≤ 3n`, `n + 1 ≤ F'`. -/
theorem ncard_nsSetP_step (F' n : ℕ) (h1 : F' + 1 ≤ 3 * n) (h2 : n + 1 ≤ F') (P : ℕ → Prop) :
    (nsSetP (F' + 2) (n + 1) P).ncard =
      (nsSetP F' n (fun k => P (k + 1))).ncard + (nsSetP F' n (fun k => P (k + 2))).ncard := by
  rcases lt_trichotomy F' (2 * n) with h | rfl | h
  · exact (transfer_step h2 h).ncard_split P
  · have h' : 2 * n + 2 = 2 * (n + 1) := by ring
    rw [h', nsSetP_two_mul_eq_empty, nsSetP_two_mul_eq_empty, nsSetP_two_mul_eq_empty]
    simp
  · exact (transfer_kunz h h1).ncard_split P

/-- **Theorem `kaplanrefinat` of arXiv:2607.23111, corrected.** If `(F + 2)/3 ≤ m ≤ F - 2`
then `n_{F,m,g} = n_{F-2,m-1,g-1} + n_{F-2,m-1,g-2}` (here for `2 ≤ g`, so that the
subtractions are genuine). The printed upper bound `m ≤ F - 1` is false at `m = F - 1`;
see `printed_bound_false`. -/
theorem kaplan_refined {F m g : ℕ} (h1 : F + 2 ≤ 3 * m) (h2 : m + 2 ≤ F) (hg : 2 ≤ g) :
    nFmg F m g = nFmg (F - 2) (m - 1) (g - 1) + nFmg (F - 2) (m - 1) (g - 2) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
  have h := ncard_nsSetP_step F' n (by omega) (by omega) (· = k + 2)
  simp only [Nat.add_sub_cancel, show k + 2 - 1 = k + 1 by omega]
  unfold nFmg nsSet
  rw [h]
  congr 3
  · funext j; exact propext (by omega)
  · funext j; exact propext (by omega)

/-- `n_{F,m} = #𝒮_{F,m}`, numerical semigroups with Frobenius number `F` and multiplicity `m`. -/
noncomputable def nFm (F m : ℕ) : ℕ :=
  {S : AddSubmonoid ℕ | HasFrobenius S F ∧ HasMultiplicity S m}.ncard

/-- `n_{F,m}` as the genus-unrestricted count. -/
theorem nFm_eq (F m : ℕ) : nFm F m = (nsSetP F m (fun _ => True)).ncard := by
  unfold nFm nsSetP
  simp only [and_true]

/-- **Theorem `t:twostepdoubling` of arXiv:2607.23111.** If `(F + 2)/3 ≤ m < F - 1`, then
`n_{F,m} = 2 n_{F-2,m-1}`. -/
theorem two_step_doubling {F m : ℕ} (h1 : F + 2 ≤ 3 * m) (h2 : m + 2 ≤ F) :
    nFm F m = 2 * nFm (F - 2) (m - 1) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel, nFm_eq, nFm_eq,
    ncard_nsSetP_step F' n (by omega) (by omega), two_mul]

/-- `⟨2, 5⟩ = {0, 2, 4, 5, 6, …}`. -/
def twoFive : AddSubmonoid ℕ where
  carrier := {x | x ≠ 1 ∧ x ≠ 3}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    omega

/-- Membership in `⟨2, 5⟩`. -/
theorem mem_twoFive {x : ℕ} : x ∈ twoFive ↔ x ≠ 1 ∧ x ≠ 3 := Iff.rfl

/-- `⟨2, 5⟩` is the only numerical semigroup with Frobenius number `3` and multiplicity `2`. -/
theorem eq_twoFive {S : AddSubmonoid ℕ} (hF : HasFrobenius S 3) (hm : HasMultiplicity S 2) :
    S = twoFive := by
  ext x
  rw [mem_twoFive]
  rcases Nat.lt_or_ge 3 x with hx | hx
  · exact iff_of_true (hF.2 x hx) (by omega)
  interval_cases x
  · exact iff_of_true S.zero_mem (by omega)
  · exact iff_of_false (notMem_of_pos_of_lt hm (by omega) (by omega)) (by omega)
  · exact iff_of_true hm.2.1 (by omega)
  · exact iff_of_false hF.1 (by omega)

/-- `⟨2, 5⟩` has genus `2` (gaps `1, 3`). -/
theorem genus_twoFive : genus twoFive = 2 := by
  have h : ((twoFive : AddSubmonoid ℕ) : Set ℕ)ᶜ = {1, 3} := by
    ext x
    simp only [Set.mem_compl_iff, SetLike.mem_coe, mem_twoFive, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    omega
  unfold genus
  rw [h, Set.ncard_pair (by omega)]

/-- `⟨2, 5⟩ ∈ 𝒮_{3,2,2}`. -/
theorem twoFive_mem_nsSet : twoFive ∈ nsSet 3 2 2 := by
  refine ⟨⟨by simp [mem_twoFive], fun x hx => by rw [mem_twoFive]; omega⟩,
    ⟨by omega, by simp [mem_twoFive], fun x hx hx0 => ?_⟩, genus_twoFive⟩
  rw [mem_twoFive] at hx
  omega

/-- Ground truth: `n_{3,2,2} = 1`. -/
theorem nFmg_three_two_two : nFmg 3 2 2 = 1 := by
  unfold nFmg
  rw [Set.ncard_eq_one]
  refine ⟨twoFive, Set.eq_singleton_iff_unique_mem.2 ⟨twoFive_mem_nsSet, fun S hS => ?_⟩⟩
  exact eq_twoFive hS.1 hS.2.1

/-- Ground truth: `n_{3,2,g} = 0` for `g ≠ 2`. -/
theorem nFmg_three_two_of_ne {g : ℕ} (hg : g ≠ 2) : nFmg 3 2 g = 0 := by
  unfold nFmg
  rw [show nsSet 3 2 g = ∅ from ?_, Set.ncard_empty]
  ext S
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hF, hm, hgen⟩
  rw [eq_twoFive hF hm, genus_twoFive] at hgen
  exact hg hgen.symm

/-- Ground truth: `n_{1,1,g} = 0` (no semigroup has `F = m`). -/
theorem nFmg_one_one (g : ℕ) : nFmg 1 1 g = 0 := by
  unfold nFmg
  rw [show nsSet 1 1 g = ∅ from ?_, Set.ncard_empty]
  ext S
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hF, hm, -⟩
  exact hF.1 hm.2.1

/-- The theorem as printed (hypothesis `(F + 2)/3 ≤ m ≤ F - 1`) is false:
at `F = 3`, `m = 2`, `g = 2` one has `n_{3,2,2} = 1` but `n_{1,1,1} + n_{1,1,0} = 0`. -/
theorem printed_bound_false :
    ¬ ∀ F m g : ℕ, F + 2 ≤ 3 * m → m + 1 ≤ F → 2 ≤ g →
      nFmg F m g = nFmg (F - 2) (m - 1) (g - 1) + nFmg (F - 2) (m - 1) (g - 2) := by
  intro h
  have h' := h 3 2 2 (by norm_num) (by norm_num) le_rfl
  rw [nFmg_three_two_two, nFmg_one_one, nFmg_one_one] at h'
  exact absurd h' (by norm_num)

example : nFmg 5 3 3 = 1 := by
  rw [kaplan_refined (by norm_num) (by norm_num) (by norm_num)]
  rw [show 5 - 2 = 3 from rfl, show 3 - 1 = 2 from rfl, show 3 - 2 = 1 from rfl,
    nFmg_three_two_two, nFmg_three_two_of_ne (by norm_num)]

end Candidates.MultiparameterCountingNumericalSemigroups
