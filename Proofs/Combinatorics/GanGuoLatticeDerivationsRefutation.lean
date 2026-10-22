/-
# Gan–Guo: the derivations of a lattice need not form a lattice

## Source

Aiping Gan and Li Guo, *On differential lattices*, arXiv:2106.08481 (v1).
Section "Lattice structures for derivations" (the last section), Conjecture
`qu:do` / `cj:00`, item (1), posed after "Based on the results in this section,
it seems reasonable to pose the following conjectures."

Here a derivation (Eq. (eq:der), following Xin et al., *without* the linearity
condition `d(x ∨ y) = d x ∨ d y`; see Remark `rk:cond`) is a map `d : L → L` with

```
d(x ∧ y) = (d(x) ∧ y) ∨ (x ∧ d(y))   for all x, y ∈ L,
```

`DO(L)` is the set of derivations, and `d ⪯ d'` iff `d(x) ≤ d'(x)` for all `x`
(the pointwise order).  The paper proves the conjecture for finite distributive
lattices and for complete infinitely distributive lattices; for general lattices
it is posed as a conjecture. Item (2) presupposes item (1).

## Counterexample

Conjecture (1), that the pointwise derivation poset is always a lattice, is
false. Counterexample `L8` on `{0, …, 7}` with covers
`0<1, 0<2, 0<3, 1<4, 1<5, 2<4, 3<4, 4<6, 5<7, 6<7` (non-distributive: `{0,1,2,3,4}`
is an `M3`).  The derivations

* `d₁ = (0,0,0,3,3,0,0,0)` and `d₂ = (0,0,2,0,2,0,0,0)` (values at `0, …, 7`)

have the two incomparable upper bounds `u₁ = (0,1,2,3,4,0,1,0)` and
`u₂ = (0,1,2,3,4,1,0,0)` in `DO(L8)`, and no least upper bound.  Hand argument:
a join `j` satisfies `j ≤ u₁, u₂`, so `j 5 = j 6 = 0`, and `3 ⊔ 2 = 4 ≤ j 4`; then
`j 1 = j (4 ⊓ 5) = (j 4 ⊓ 5) ⊔ (4 ⊓ j 5) ≥ 4 ⊓ 5 = 1` but also
`j 1 = j (5 ⊓ 6) = (j 5 ⊓ 6) ⊔ (5 ⊓ j 6) = 0`.
-/
import Mathlib

set_option autoImplicit false


set_option Elab.async false

namespace GanGuoLatticeDerivationsRefutation

/-! ## The lattice `L8` -/

/-- Down-set bitmasks of the cover relation `0<1, 0<2, 0<3, 1<4, 1<5, 2<4, 3<4, 4<6, 5<7, 6<7`:
bit `a` of `downMask b` is set iff `a ≤ b`. -/
def downMask : Fin 8 → ℕ := ![1, 3, 5, 9, 31, 35, 95, 255]

/-- Join table of `L8`. -/
def supTable : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![1, 1, 4, 4, 4, 5, 6, 7], ![2, 4, 2, 4, 4, 7, 6, 7],
    ![3, 4, 4, 3, 4, 7, 6, 7], ![4, 4, 4, 4, 4, 7, 6, 7], ![5, 5, 7, 7, 7, 5, 7, 7],
    ![6, 6, 6, 6, 6, 7, 6, 7], ![7, 7, 7, 7, 7, 7, 7, 7]]

/-- Meet table of `L8`. -/
def infTable : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 1, 1, 1, 1], ![0, 0, 2, 0, 2, 0, 2, 2],
    ![0, 0, 0, 3, 3, 0, 3, 3], ![0, 1, 2, 3, 4, 1, 4, 4], ![0, 1, 0, 0, 1, 5, 1, 5],
    ![0, 1, 2, 3, 4, 1, 6, 6], ![0, 1, 2, 3, 4, 5, 6, 7]]

/-- The carrier of the eight-element lattice `L8`, with elements labelled `0, …, 7`. -/
structure L8 where
  /-- The label in `{0, …, 7}`. -/
  val : Fin 8
  deriving Fintype

/-- Equality on `L8` is decidable through the labels. -/
instance : DecidableEq L8 := fun a b =>
  decidable_of_iff (a.val = b.val) (by cases a; cases b; simp)

/-- The order of `L8`: `a ≤ b` iff `a` lies in the down-set of `b`. -/
instance : LE L8 := ⟨fun a b => (downMask b.val).testBit a.val = true⟩

/-- The order of `L8` is decidable. -/
instance : DecidableRel (α := L8) (· ≤ ·) := fun a b =>
  inferInstanceAs (Decidable ((downMask b.val).testBit a.val = true))

/-- `L8` is a lattice, with join and meet read off the tables. -/
instance : Lattice L8 where
  sup a b := ⟨supTable a.val b.val⟩
  inf a b := ⟨infTable a.val b.val⟩
  le_refl := by decide +kernel
  le_trans := by decide +kernel
  le_antisymm := by decide +kernel
  le_sup_left := by decide +kernel
  le_sup_right := by decide +kernel
  sup_le := by decide +kernel
  inf_le_left := by decide +kernel
  inf_le_right := by decide +kernel
  le_inf := by decide +kernel

/-- `L8` is bounded, with bottom `0` and top `7`. -/
instance : BoundedOrder L8 where
  top := ⟨7⟩
  le_top := by decide +kernel
  bot := ⟨0⟩
  bot_le := by decide +kernel

/-- The strict order of `L8` is decidable. -/
instance : DecidableRel (α := L8) (· < ·) := fun a b =>
  inferInstanceAs (Decidable (a ≤ b ∧ ¬ b ≤ a))

-- the covering relation of `L8` is exactly the source's list of covers, so
-- the order is the one of the source (a finite poset is determined by its covers).
example : ∀ a b : L8, a ⋖ b ↔ (a.val, b.val) ∈
    ([(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 4), (3, 4), (4, 6), (5, 7), (6, 7)] :
      List (Fin 8 × Fin 8)) := by
  unfold CovBy; decide +kernel

-- `{0,1,2,3,4}` is an `M3`, `4 ⊓ 5 = 1`, `5 ⊓ 6 = 1`.
example : (⟨1⟩ : L8) ⊔ ⟨2⟩ = ⟨4⟩ ∧ (⟨1⟩ : L8) ⊔ ⟨3⟩ = ⟨4⟩ ∧ (⟨2⟩ : L8) ⊔ ⟨3⟩ = ⟨4⟩ ∧
    (⟨1⟩ : L8) ⊓ ⟨2⟩ = ⟨0⟩ ∧ (⟨1⟩ : L8) ⊓ ⟨3⟩ = ⟨0⟩ ∧ (⟨2⟩ : L8) ⊓ ⟨3⟩ = ⟨0⟩ ∧
    (⟨4⟩ : L8) ⊓ ⟨5⟩ = ⟨1⟩ ∧ (⟨5⟩ : L8) ⊓ ⟨6⟩ = ⟨1⟩ := by
  decide +kernel

-- `L8` is not distributive.
example : ¬ ∀ a b c : L8, a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) := by decide +kernel

/-! ## Derivations -/

/-- A *derivation* on a lattice `L` (Gan–Guo, Eq. (eq:der), following Xin et al., without the
linearity condition): a map `d : L → L` with `d (x ⊓ y) = (d x ⊓ y) ⊔ (x ⊓ d y)` for all
`x y`.  The set `DO(L)` of the paper is the subtype `{d : L → L // IsDerivation d}`, ordered
pointwise (the paper's `⪯`). -/
def IsDerivation {L : Type*} [Lattice L] (d : L → L) : Prop :=
  ∀ x y, d (x ⊓ y) = (d x ⊓ y) ⊔ (x ⊓ d y)

/-- Being a derivation is decidable on a finite lattice with decidable equality. -/
instance {L : Type*} [Lattice L] [Fintype L] [DecidableEq L] :
    DecidablePred (IsDerivation (L := L)) := fun d => by
  unfold IsDerivation; infer_instance

/-- The pointwise order on `DO(L)` is the paper's `⪯`. -/
theorem le_iff_forall {L : Type*} [Lattice L] (d d' : {d : L → L // IsDerivation d}) :
    d ≤ d' ↔ ∀ x, d.1 x ≤ d'.1 x := Iff.rfl

-- the identity and the zero map are derivations (Gan–Guo, Example exm:000).
example : IsDerivation (id : L8 → L8) := by decide +kernel
example : IsDerivation (fun _ : L8 => (⊥ : L8)) := by decide +kernel

-- the pointwise join `(0,0,2,3,4,0,0,0)` of `d₁, d₂` is *not* a derivation.
example : ¬ IsDerivation (fun x : L8 => (⟨![0, 0, 2, 3, 4, 0, 0, 0] x.val⟩ : L8)) := by
  decide +kernel

/-! ## The counterexample pair and its two upper bounds -/

/-- `d₁ = (0,0,0,3,3,0,0,0)`. -/
def d₁ : L8 → L8 := fun x => ⟨![0, 0, 0, 3, 3, 0, 0, 0] x.val⟩

/-- `d₂ = (0,0,2,0,2,0,0,0)`. -/
def d₂ : L8 → L8 := fun x => ⟨![0, 0, 2, 0, 2, 0, 0, 0] x.val⟩

/-- `u₁ = (0,1,2,3,4,0,1,0)`. -/
def u₁ : L8 → L8 := fun x => ⟨![0, 1, 2, 3, 4, 0, 1, 0] x.val⟩

/-- `u₂ = (0,1,2,3,4,1,0,0)`. -/
def u₂ : L8 → L8 := fun x => ⟨![0, 1, 2, 3, 4, 1, 0, 0] x.val⟩

/-- `d₁` is a derivation of `L8`. -/
theorem isDerivation_d₁ : IsDerivation d₁ := by decide +kernel

/-- `d₂` is a derivation of `L8`. -/
theorem isDerivation_d₂ : IsDerivation d₂ := by decide +kernel

/-- `u₁` is a derivation of `L8`. -/
theorem isDerivation_u₁ : IsDerivation u₁ := by decide +kernel

/-- `u₂` is a derivation of `L8`. -/
theorem isDerivation_u₂ : IsDerivation u₂ := by decide +kernel

/-- `d₁` as an element of `DO(L8)`. -/
def D₁ : {d : L8 → L8 // IsDerivation d} := ⟨d₁, isDerivation_d₁⟩

/-- `d₂` as an element of `DO(L8)`. -/
def D₂ : {d : L8 → L8 // IsDerivation d} := ⟨d₂, isDerivation_d₂⟩

/-- `u₁` as an element of `DO(L8)`. -/
def U₁ : {d : L8 → L8 // IsDerivation d} := ⟨u₁, isDerivation_u₁⟩

/-- `u₂` as an element of `DO(L8)`. -/
def U₂ : {d : L8 → L8 // IsDerivation d} := ⟨u₂, isDerivation_u₂⟩

/-- `u₁` is an upper bound of `{d₁, d₂}` in `DO(L8)`. -/
theorem U₁_mem_upperBounds :
    U₁ ∈ upperBounds ({D₁, D₂} : Set {d : L8 → L8 // IsDerivation d}) := by
  rintro D (rfl | rfl)
  · exact (le_iff_forall _ _).2 (by decide +kernel)
  · exact (le_iff_forall _ _).2 (by decide +kernel)

/-- `u₂` is an upper bound of `{d₁, d₂}` in `DO(L8)`. -/
theorem U₂_mem_upperBounds :
    U₂ ∈ upperBounds ({D₁, D₂} : Set {d : L8 → L8 // IsDerivation d}) := by
  rintro D (rfl | rfl)
  · exact (le_iff_forall _ _).2 (by decide +kernel)
  · exact (le_iff_forall _ _).2 (by decide +kernel)

/-- The two upper bounds `u₁, u₂` are incomparable. -/
theorem U₁_U₂_incomparable : ¬ U₁ ≤ U₂ ∧ ¬ U₂ ≤ U₁ := by
  constructor <;> rw [le_iff_forall] <;> decide +kernel

/-- `d₁ ≠ d₂`, so the pair is a genuine two-element set. -/
theorem D₁_ne_D₂ : D₁ ≠ D₂ := fun h => by
  have h4 : d₁ ⟨2⟩ = d₂ ⟨2⟩ := congrArg (fun D : {d : L8 → L8 // IsDerivation d} => D.1 ⟨2⟩) h
  exact absurd h4 (by decide +kernel)

/-! ## No least upper bound -/

/-- The finite core of the argument: if `a ⊒ 3, 2` and `b, c ⊑ 0`, then the two Leibniz
expansions of `j 1 = j (4 ⊓ 5) = j (5 ⊓ 6)` with `a = j 4`, `b = j 5`, `c = j 6` disagree. -/
theorem leibniz_mismatch :
    ∀ a b c : L8, (⟨3⟩ : L8) ≤ a → (⟨2⟩ : L8) ≤ a → b ≤ ⟨0⟩ → c ≤ ⟨0⟩ →
      (a ⊓ ⟨5⟩) ⊔ (⟨4⟩ ⊓ b) ≠ (b ⊓ ⟨6⟩) ⊔ (⟨5⟩ ⊓ c) := by
  decide +kernel

/-- In `DO(L8)` the pair `{d₁, d₂}` has no least upper bound. -/
theorem not_exists_isLUB :
    ¬ ∃ j, IsLUB ({D₁, D₂} : Set {d : L8 → L8 // IsDerivation d}) j := by
  rintro ⟨j, hub, hleast⟩
  have hj₁ : j ≤ U₁ := hleast U₁_mem_upperBounds
  have hj₂ : j ≤ U₂ := hleast U₂_mem_upperBounds
  have hd₁ : D₁ ≤ j := hub (Set.mem_insert _ _)
  have hd₂ : D₂ ≤ j := hub (Set.mem_insert_of_mem _ rfl)
  have hmeet : (⟨4⟩ : L8) ⊓ ⟨5⟩ = ⟨5⟩ ⊓ ⟨6⟩ := by decide +kernel
  have hexp : (j.1 ⟨4⟩ ⊓ ⟨5⟩) ⊔ (⟨4⟩ ⊓ j.1 ⟨5⟩) = (j.1 ⟨5⟩ ⊓ ⟨6⟩) ⊔ (⟨5⟩ ⊓ j.1 ⟨6⟩) :=
    (j.2 _ _).symm.trans ((congrArg j.1 hmeet).trans (j.2 _ _))
  exact leibniz_mismatch (j.1 ⟨4⟩) (j.1 ⟨5⟩) (j.1 ⟨6⟩)
    ((le_iff_forall _ _).1 hd₁ ⟨4⟩) ((le_iff_forall _ _).1 hd₂ ⟨4⟩)
    ((le_iff_forall _ _).1 hj₁ ⟨5⟩) ((le_iff_forall _ _).1 hj₂ ⟨6⟩) hexp

/-- **Gan–Guo, Conjecture `qu:do` (1), is false** (arXiv:2106.08481, last section).
The conjecture asserts that for every lattice `(L, ∨, ∧, 0, 1)` the poset `DO(L)` of
derivations, ordered pointwise, is a lattice, i.e. every pair of derivations has a least
upper bound and a greatest lower bound in `DO(L)`.  This fails already for the
eight-element bounded lattice `L8` and the derivations `d₁, d₂`, which have no join. -/
theorem gan_guo_conjecture_false :
    ¬ ∀ (L : Type) [Lattice L] [BoundedOrder L] [Finite L]
        (e₁ e₂ : {d : L → L // IsDerivation d}),
        (∃ j, IsLUB ({e₁, e₂} : Set {d : L → L // IsDerivation d}) j) ∧
          ∃ m, IsGLB ({e₁, e₂} : Set {d : L → L // IsDerivation d}) m := fun h =>
  not_exists_isLUB (h L8 D₁ D₂).1

end GanGuoLatticeDerivationsRefutation
