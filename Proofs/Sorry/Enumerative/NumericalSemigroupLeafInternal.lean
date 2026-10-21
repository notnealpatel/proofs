/-
# Leaf ≤ internal numerical semigroups, fixed multiplicity and Frobenius number

## Source

M. Casas, J. A. Madrid and J. C. Rosales, *Internal numerical semigroups*,
arXiv:2608.19984 (version of 19 August 2026), Section
"Internal numerical semigroups with fixed multiplicity and Frobenius number"
(`sec:fixedmulFrob`), the conjecture stated just before Proposition 34.

Definitions (Section 1 of the paper): for a numerical semigroup `S`,
`m(S) = min (S \ {0})`, `F(S) = max (ℤ \ S)`, `msg(S)` is the minimal system of
generators, and `μ(S) = #{x ∈ msg(S) | x > F(S)}`.  `S` is *internal* when
`μ(S) ≠ 0` and a *leaf* when `μ(S) = 0`.  `𝓘(mul = m, Frob = F)` and
`𝓛(mul = m, Frob = F)` are the internal, resp. leaf, semigroups with
multiplicity `m` and Frobenius number `F`.

Verbatim conjecture:

> Let $m$ and $F$ be two integer numbers such that $2\leq m\leq F+1$ and
> $m\not | F$, then
> $\#\mathscr{L}(\text{mul}=m,\text{ Frob}=F)\leq
>  \#\mathscr{I}(\text{mul}=m,\text{ Frob}=F)$.

Status (2026-10-21): open in the paper (supported by tables up to `F = 26`).

## What this module proves

The special case `m ∈ {2, 3}` (`leafSet_ncard_le_internalSet_ncard_of_le_three`),
not stated in the paper.  The proof splits into two reusable facts:

* for every `m ≥ 2`, `m ≤ F + 1`, `m ∤ F`, the semigroup
  `D(m, F) = ⟨m⟩ ∪ {F + 1, →}` is internal (`D_mem_internalSet`), so
  `1 ≤ #𝓘(mul = m, Frob = F)`;
* for `m = 2` there is no leaf, and for `m = 3` any leaf is the semigroup
  `{x | 3 ∣ x ∨ F < x ∨ (x ≢ F (mod 3) ∧ F + 3 ≤ 2x)}` (that is `⟨3, (F+3)/2⟩`),
  so `#𝓛(mul = 3, Frob = F) ≤ 1`.

Computational evidence (2026-10-21): brute force over all semigroups with
`m ∈ {2,3}`, `F ≤ 21` confirms `#𝓛 = 1` exactly for `m = 3`, `F` odd `≥ 5`,
and `0` otherwise; the triage enumeration of the full conjecture, extended
to `F ≤ 31`, finds no violation.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.NumericalSemigroupLeafInternal

/-! ## Definitions

A numerical semigroup is an additive submonoid of `ℕ` with finite complement.
Every predicate `HasFrobenius S F` forces the complement to be finite, so the
families below range exactly over numerical semigroups `S ≠ ℕ`. -/

/-- `S` has multiplicity `m`: `m` is the least nonzero element of `S`. -/
def HasMultiplicity (S : AddSubmonoid ℕ) (m : ℕ) : Prop :=
  0 < m ∧ m ∈ S ∧ ∀ x ∈ S, 0 < x → m ≤ x

/-- `S` has Frobenius number `F`: `F` is the largest natural number not in `S`. -/
def HasFrobenius (S : AddSubmonoid ℕ) (F : ℕ) : Prop :=
  F ∉ S ∧ ∀ x, F < x → x ∈ S

/-- `x` is a minimal generator of `S`: `x ∈ S \ {0}` and `x` is not a sum of two
nonzero elements of `S` (i.e. `x ∈ S* \ (S* + S*)`). -/
def IsMinimalGenerator (S : AddSubmonoid ℕ) (x : ℕ) : Prop :=
  x ∈ S ∧ x ≠ 0 ∧ ∀ a ∈ S, ∀ b ∈ S, a + b = x → a = 0 ∨ b = 0

/-- `S` is a leaf: every minimal generator lies below some gap of `S`, i.e. no
minimal generator exceeds the Frobenius number (`μ(S) = 0`).  See
`isLeaf_iff_of_hasFrobenius`.  (`ℕ` itself is not a leaf, matching the paper,
where `⟨1⟩` is internal.) -/
def IsLeaf (S : AddSubmonoid ℕ) : Prop :=
  ∀ x, IsMinimalGenerator S x → ∃ y, y ∉ S ∧ x < y

/-- `𝓛(mul = m, Frob = F)`: leaf numerical semigroups with multiplicity `m` and
Frobenius number `F`. -/
def leafSet (m F : ℕ) : Set (AddSubmonoid ℕ) :=
  {S | HasMultiplicity S m ∧ HasFrobenius S F ∧ IsLeaf S}

/-- `𝓘(mul = m, Frob = F)`: internal numerical semigroups with multiplicity `m`
and Frobenius number `F`. -/
def internalSet (m F : ℕ) : Set (AddSubmonoid ℕ) :=
  {S | HasMultiplicity S m ∧ HasFrobenius S F ∧ ¬ IsLeaf S}

/-- The open conjecture of arXiv:2608.19984, Section 7 (before Proposition 34):
for `2 ≤ m ≤ F + 1` with `m ∤ F`, `#𝓛(mul = m, Frob = F) ≤ #𝓘(mul = m, Frob = F)`. -/
def LeafLeInternalConjecture : Prop :=
  ∀ m F : ℕ, 2 ≤ m → m ≤ F + 1 → ¬ m ∣ F → (leafSet m F).ncard ≤ (internalSet m F).ncard

/-- With Frobenius number `F`, `S` is a leaf iff every minimal generator is `≤ F`
(the paper's `μ(S) = 0`). -/
theorem isLeaf_iff_of_hasFrobenius {S : AddSubmonoid ℕ} {F : ℕ} (hF : HasFrobenius S F) :
    IsLeaf S ↔ ∀ x, IsMinimalGenerator S x → x ≤ F := by
  constructor
  · intro hleaf x hx
    obtain ⟨y, hyS, hxy⟩ := hleaf x hx
    have hyF : y ≤ F := by
      by_contra hlt
      exact hyS (hF.2 y (Nat.lt_of_not_le hlt))
    omega
  · intro hle x hx
    have hxF : x ≠ F := fun h => hF.1 (h ▸ hx.1)
    exact ⟨F, hF.1, lt_of_le_of_ne (hle x hx) hxF⟩

/-! ## Finiteness: the counted families are finite, so `ncard` is meaningful -/

/-- The numerical semigroups with Frobenius number `F` form a finite set
(each is determined by its trace on `[0, F]`). -/
theorem setOf_hasFrobenius_finite (F : ℕ) : {S : AddSubmonoid ℕ | HasFrobenius S F}.Finite := by
  classical
  let f : AddSubmonoid ℕ → Finset ℕ := fun S => (Finset.range (F + 1)).filter (· ∈ S)
  apply Set.Finite.of_finite_image (f := f)
  · apply (Finset.range (F + 1)).powerset.finite_toSet.subset
    rintro _ ⟨S, -, rfl⟩
    exact Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.filter_subset _ _))
  · intro S hS T hT hST
    ext x
    by_cases hx : x ≤ F
    · have h := congrArg (fun s : Finset ℕ => x ∈ s) hST
      simpa [f, Nat.lt_succ_of_le hx] using h
    · have hlt : F < x := Nat.lt_of_not_le hx
      exact iff_of_true (hS.2 x hlt) (hT.2 x hlt)

/-- `𝓛(mul = m, Frob = F)` is finite. -/
theorem leafSet_finite (m F : ℕ) : (leafSet m F).Finite :=
  (setOf_hasFrobenius_finite F).subset fun _ hS => hS.2.1

/-- `𝓘(mul = m, Frob = F)` is finite. -/
theorem internalSet_finite (m F : ℕ) : (internalSet m F).Finite :=
  (setOf_hasFrobenius_finite F).subset fun _ hS => hS.2.1

/-! ## Basic closure facts -/

/-- Adding multiples of an element `m ∈ S` stays in `S`. -/
theorem add_mul_mem {S : AddSubmonoid ℕ} {m s : ℕ} (hm : m ∈ S) (hs : s ∈ S) (k : ℕ) :
    s + m * k ∈ S := by
  have hk : k • m ∈ S := AddSubmonoid.nsmul_mem S hm k
  rw [smul_eq_mul, mul_comm] at hk
  exact S.add_mem hs hk

/-- If `S` has multiplicity `m` and Frobenius number `F`, no element `s ≤ F` of `S`
is congruent to `F` modulo `m` (else `F = s + m k ∈ S`). -/
theorem mod_ne_of_mem_of_le {S : AddSubmonoid ℕ} {m F s : ℕ} (hm : HasMultiplicity S m)
    (hF : HasFrobenius S F) (hs : s ∈ S) (hsF : s ≤ F) : s % m ≠ F % m := by
  intro hmod
  have hdvd : m ∣ F - s := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod.symm)
  obtain ⟨k, hk⟩ := hdvd
  have hFeq : F = s + m * k := by omega
  exact hF.1 (hFeq ▸ add_mul_mem hm.2.1 hs k)

/-! ## The minimum `D(m, F)` is internal -/

/-- `D(m, F) = ⟨m⟩ ∪ {F + 1, →}`, the minimum of `𝓘(mul = m, Frob = F)`. -/
def D (m F : ℕ) : AddSubmonoid ℕ where
  carrier := {x | m ∣ x ∨ F < x}
  zero_mem' := Or.inl (dvd_zero m)
  add_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (dvd_add ha hb)
    all_goals exact Or.inr (by omega)

/-- Membership in `D(m, F)`. -/
theorem mem_D {m F x : ℕ} : x ∈ D m F ↔ m ∣ x ∨ F < x := Iff.rfl

/-- For `2 ≤ m ≤ F + 1` and `m ∤ F`, `D(m, F)` is an internal numerical semigroup
with multiplicity `m` and Frobenius number `F`. -/
theorem D_mem_internalSet {m F : ℕ} (hm : 2 ≤ m) (hmF : m ≤ F + 1) (hdvd : ¬ m ∣ F) :
    D m F ∈ internalSet m F := by
  classical
  refine ⟨⟨by omega, mem_D.2 (Or.inl dvd_rfl), ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro x hx hx0
    rcases mem_D.1 hx with h | h
    · exact Nat.le_of_dvd hx0 h
    · omega
  · rintro (h | h)
    · exact hdvd h
    · exact lt_irrefl F h
  · intro x hx
    exact mem_D.2 (Or.inr hx)
  · -- the least `x > F` with `m ∤ x` is a minimal generator above every gap
    have hex : ∃ x, F < x ∧ ¬ m ∣ x := by
      refine ⟨m * (F + 1) + 1, by nlinarith, ?_⟩
      intro h
      have h1 : m ∣ 1 := (Nat.dvd_add_right (dvd_mul_right m (F + 1))).1 h
      have := Nat.le_of_dvd one_pos h1
      omega
    let x := Nat.find hex
    have hxspec : F < x ∧ ¬ m ∣ x := Nat.find_spec hex
    have hxmin : ∀ y, y < x → F < y → m ∣ y := by
      intro y hy hFy
      by_contra hny
      exact Nat.find_min hex hy ⟨hFy, hny⟩
    have hgen : IsMinimalGenerator (D m F) x := by
      refine ⟨mem_D.2 (Or.inr hxspec.1), by omega, ?_⟩
      intro a ha b hb hab
      by_contra hne
      push Not at hne
      have hda : m ∣ a := by
        rcases mem_D.1 ha with h | h
        · exact h
        · exact hxmin a (by omega) h
      have hdb : m ∣ b := by
        rcases mem_D.1 hb with h | h
        · exact h
        · exact hxmin b (by omega) h
      exact hxspec.2 (hab ▸ dvd_add hda hdb)
    intro hleaf
    obtain ⟨y, hyS, hxy⟩ := hleaf x hgen
    exact hyS (mem_D.2 (Or.inr (lt_trans hxspec.1 hxy)))

/-- `1 ≤ #𝓘(mul = m, Frob = F)` whenever `2 ≤ m ≤ F + 1` and `m ∤ F`. -/
theorem one_le_ncard_internalSet {m F : ℕ} (hm : 2 ≤ m) (hmF : m ≤ F + 1) (hdvd : ¬ m ∣ F) :
    1 ≤ (internalSet m F).ncard :=
  (Set.ncard_pos (internalSet_finite m F)).2 ⟨D m F, D_mem_internalSet hm hmF hdvd⟩

/-! ## Multiplicity two: no leaves -/

/-- There is no leaf numerical semigroup of multiplicity `2`: `F + 2` is always a
minimal generator above `F`. -/
theorem leafSet_two_eq_empty (F : ℕ) : leafSet 2 F = ∅ := by
  ext S
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hm, hF, hleaf⟩
  have hgen : IsMinimalGenerator S (F + 2) := by
    refine ⟨hF.2 _ (by omega), by omega, ?_⟩
    intro a ha b hb hab
    by_contra hne
    push Not at hne
    have ha2 : 2 ≤ a := hm.2.2 a ha (Nat.pos_of_ne_zero hne.1)
    have hb2 : 2 ≤ b := hm.2.2 b hb (Nat.pos_of_ne_zero hne.2)
    have hma := mod_ne_of_mem_of_le hm hF ha (by omega)
    have hmb := mod_ne_of_mem_of_le hm hF hb (by omega)
    have hF0 := mod_ne_of_mem_of_le hm hF S.zero_mem (Nat.zero_le F)
    omega
  obtain ⟨y, hyS, hxy⟩ := hleaf _ hgen
  exact hyS (hF.2 y (by omega))

/-! ## Multiplicity three: at most one leaf -/

/-- In a leaf of multiplicity `3` and Frobenius number `F`, `F + 3 = 2a` for some
`a ∈ S`. -/
theorem exists_two_mul_eq_of_leaf_three {S : AddSubmonoid ℕ} {F : ℕ}
    (hm : HasMultiplicity S 3) (hF : HasFrobenius S F) (hleaf : IsLeaf S) :
    ∃ a ∈ S, 2 * a = F + 3 := by
  have hnotgen : ¬ IsMinimalGenerator S (F + 3) := by
    intro hgen
    obtain ⟨y, hyS, hxy⟩ := hleaf _ hgen
    exact hyS (hF.2 y (by omega))
  have hmem : F + 3 ∈ S := hF.2 _ (by omega)
  have hsplit : ∃ a ∈ S, ∃ b ∈ S, a + b = F + 3 ∧ a ≠ 0 ∧ b ≠ 0 := by
    by_contra hno
    push Not at hno
    refine hnotgen ⟨hmem, by omega, ?_⟩
    intro a ha b hb hab
    by_contra hne
    push Not at hne
    exact hne.2 (hno a ha b hb hab hne.1)
  obtain ⟨a, ha, b, hb, hab, ha0, hb0⟩ := hsplit
  have ha3 : 3 ≤ a := hm.2.2 a ha (Nat.pos_of_ne_zero ha0)
  have hb3 : 3 ≤ b := hm.2.2 b hb (Nat.pos_of_ne_zero hb0)
  have hF0 : F % 3 ≠ 0 := by
    have := mod_ne_of_mem_of_le hm hF S.zero_mem (Nat.zero_le F)
    omega
  have hma := mod_ne_of_mem_of_le hm hF ha (by omega)
  have hmb := mod_ne_of_mem_of_le hm hF hb (by omega)
  -- residue bookkeeping: `a ≡ b (mod 3)` and `2a ≡ 2b ≡ F (mod 3)`
  have hres : a % 3 = b % 3 ∧ (a + a) % 3 = F % 3 ∧ (b + b) % 3 = F % 3 := by
    have hFr : F % 3 = 1 ∨ F % 3 = 2 := by omega
    have har : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
    have hbr : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
    rcases hFr with hFr | hFr <;> rcases har with har | har | har <;>
      rcases hbr with hbr | hbr | hbr <;> omega
  have h2a : a + a ∈ S := S.add_mem ha ha
  have h2b : b + b ∈ S := S.add_mem hb hb
  rcases lt_trichotomy a b with hlt | heq | hgt
  · have := mod_ne_of_mem_of_le hm hF h2a (by omega)
    exact absurd hres.2.1 this
  · exact ⟨a, ha, by omega⟩
  · have := mod_ne_of_mem_of_le hm hF h2b (by omega)
    exact absurd hres.2.2 this

/-- Closed form of a leaf of multiplicity `3` and Frobenius number `F`:
`x ∈ S ↔ 3 ∣ x ∨ F < x ∨ (x ≢ F (mod 3) ∧ F + 3 ≤ 2x)`. -/
theorem mem_iff_of_leaf_three {S : AddSubmonoid ℕ} {F : ℕ}
    (hm : HasMultiplicity S 3) (hF : HasFrobenius S F) (hleaf : IsLeaf S) (x : ℕ) :
    x ∈ S ↔ 3 ∣ x ∨ F < x ∨ (x % 3 ≠ F % 3 ∧ F + 3 ≤ 2 * x) := by
  obtain ⟨a, ha, h2a⟩ := exists_two_mul_eq_of_leaf_three hm hF hleaf
  have hF0 : F % 3 ≠ 0 := by
    have := mod_ne_of_mem_of_le hm hF S.zero_mem (Nat.zero_le F)
    omega
  by_cases h3 : 3 ∣ x
  · refine iff_of_true ?_ (Or.inl h3)
    obtain ⟨k, rfl⟩ := h3
    simpa using add_mul_mem hm.2.1 S.zero_mem k
  by_cases hFx : F < x
  · exact iff_of_true (hF.2 x hFx) (Or.inr (Or.inl hFx))
  have hx3 : x % 3 ≠ 0 := fun h => h3 (Nat.dvd_of_mod_eq_zero h)
  -- residue bookkeeping: if `x ≢ 0, F (mod 3)` then `2x ≡ F` and `x ≡ a (mod 3)`
  have hres : x % 3 ≠ F % 3 → (x + x) % 3 = F % 3 ∧ x % 3 = a % 3 := by
    intro hmx
    have hFr : F % 3 = 1 ∨ F % 3 = 2 := by omega
    have hxr : x % 3 = 1 ∨ x % 3 = 2 := by omega
    have har : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
    rcases hFr with hFr | hFr <;> rcases hxr with hxr | hxr <;>
      rcases har with har | har | har <;> omega
  constructor
  · intro hx
    have hmx := mod_ne_of_mem_of_le hm hF hx (by omega)
    have h2x : x + x ∈ S := S.add_mem hx hx
    refine Or.inr (Or.inr ⟨hmx, ?_⟩)
    by_contra hlt
    have h2xF := (hres hmx).1
    have := mod_ne_of_mem_of_le hm hF h2x (by omega)
    exact this h2xF
  · rintro (h | h | ⟨hmx, hle⟩)
    · exact absurd h h3
    · exact absurd h hFx
    · have hxa' := (hres hmx).2
      have hxa : x = a + 3 * ((x - a) / 3) := by omega
      rw [hxa]
      exact add_mul_mem hm.2.1 ha _

/-- `#𝓛(mul = 3, Frob = F) ≤ 1`: a leaf of multiplicity `3` is determined by `F`. -/
theorem ncard_leafSet_three_le_one (F : ℕ) : (leafSet 3 F).ncard ≤ 1 := by
  rw [Set.ncard_le_one (leafSet_finite 3 F)]
  intro S hS T hT
  ext x
  rw [mem_iff_of_leaf_three hS.1 hS.2.1 hS.2.2, mem_iff_of_leaf_three hT.1 hT.2.1 hT.2.2]

/-! ## Main result -/

/-- **Special case `m ∈ {2, 3}` of the leaf ≤ internal conjecture** (arXiv:2608.19984,
Section 7, conjecture before Proposition 34; the general conjecture is open):
for `2 ≤ m ≤ 3`, `m ≤ F + 1` and `m ∤ F`,
`#𝓛(mul = m, Frob = F) ≤ #𝓘(mul = m, Frob = F)`. -/
theorem leafSet_ncard_le_internalSet_ncard_of_le_three {m F : ℕ} (hm : 2 ≤ m) (hm3 : m ≤ 3)
    (hmF : m ≤ F + 1) (hdvd : ¬ m ∣ F) :
    (leafSet m F).ncard ≤ (internalSet m F).ncard := by
  have hint := one_le_ncard_internalSet hm hmF hdvd
  interval_cases m
  · rw [leafSet_two_eq_empty, Set.ncard_empty]
    exact Nat.zero_le _
  · exact (ncard_leafSet_three_le_one F).trans hint

/-! ## Ground truth (paper: `⟨3, 4⟩` is a leaf; table row `F = 5`, `m = 3`) -/

/-- `⟨3, 4⟩ = {0, 3, 4, 6, 7, 8, …}`, a leaf with multiplicity `3` and Frobenius
number `5` (paper, Section 2). -/
def threeFour : AddSubmonoid ℕ where
  carrier := {x | 3 ∣ x ∨ 5 < x ∨ x = 4}
  zero_mem' := Or.inl (dvd_zero 3)
  add_mem' := by
    rintro a b ha hb
    change 3 ∣ a ∨ 5 < a ∨ a = 4 at ha
    change 3 ∣ b ∨ 5 < b ∨ b = 4 at hb
    show 3 ∣ a + b ∨ 5 < a + b ∨ a + b = 4
    omega

example : 4 ∈ threeFour ∧ 5 ∉ threeFour ∧ 2 ∉ threeFour := by
  refine ⟨?_, ?_, ?_⟩
  · show 3 ∣ 4 ∨ 5 < 4 ∨ 4 = 4
    decide
  · show ¬ (3 ∣ 5 ∨ 5 < 5 ∨ 5 = 4)
    decide
  · show ¬ (3 ∣ 2 ∨ 5 < 2 ∨ 2 = 4)
    decide

/-- `⟨3, 4⟩ ∈ 𝓛(mul = 3, Frob = 5)`: the leaf count in the main theorem is attained. -/
theorem threeFour_mem_leafSet : threeFour ∈ leafSet 3 5 := by
  have h5 : (5 : ℕ) ∉ threeFour := by
    show ¬ (3 ∣ 5 ∨ 5 < 5 ∨ 5 = 4)
    decide
  refine ⟨⟨by norm_num, Or.inl dvd_rfl, ?_⟩, ⟨h5, ?_⟩, ?_⟩
  · intro x hx hx0
    change 3 ∣ x ∨ 5 < x ∨ x = 4 at hx
    omega
  · intro x hx
    exact Or.inr (Or.inl hx)
  · intro x hx
    refine ⟨5, h5, ?_⟩
    obtain ⟨hxS, hx0, hmin⟩ := hx
    change 3 ∣ x ∨ 5 < x ∨ x = 4 at hxS
    by_contra hge
    have h3 : (3 : ℕ) ∈ threeFour := Or.inl dvd_rfl
    have h4 : (4 : ℕ) ∈ threeFour := Or.inr (Or.inr rfl)
    -- `x ≥ 6`: write `x = 3 + (x - 3)` or `x = 4 + 4`
    by_cases h8 : x = 8
    · have := hmin 4 h4 4 h4 (by omega)
      omega
    · have hrest : x - 3 ∈ threeFour := by
        change 3 ∣ x - 3 ∨ 5 < x - 3 ∨ x - 3 = 4
        omega
      have := hmin 3 h3 (x - 3) hrest (by omega)
      omega

/-- The case `m = 3`, `F = 5` is non-vacuous: both families are nonempty. -/
example : (leafSet 3 5).Nonempty ∧ (internalSet 3 5).Nonempty :=
  ⟨⟨threeFour, threeFour_mem_leafSet⟩, ⟨D 3 5, D_mem_internalSet (by norm_num) (by norm_num) (by decide)⟩⟩

end Candidates.NumericalSemigroupLeafInternal
