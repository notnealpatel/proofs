import Mathlib

/-!
# Explicit group structures on `Fin n`

`GroupCount.GroupStructure n` is an explicit, finitely enumerable representation of
the group structures on the carrier `Fin n`: a multiplication table, an identity
element, and an inversion table, subject to the three *left* group axioms
(associativity, left identity, left inverse) — decidable finite checks which are
classically known to imply the full group axioms (`Group.ofLeftAxioms`).

Main results:

* `GroupCount.GroupStructure.instFintype` — the type of group structures on `Fin n`
  is a `Fintype`, via the subtype of raw table triples satisfying the axioms.
* `GroupCount.GroupStructure.toGroup`, `GroupCount.GroupStructure.ofGroup`,
  `GroupCount.GroupStructure.equivGroup` — the representation is faithful: it is
  equivalent to the type `Group (Fin n)` of Mathlib group structures on `Fin n`.
  In particular `Group (Fin n)` is itself a `Fintype`
  (`GroupCount.instFintypeGroupFin`).
* `GroupCount.GroupStructure.cyclic` — the cyclic witness (addition modulo `n`,
  written multiplicatively), giving nonemptiness for `1 ≤ n`.
* `GroupCount.GroupStructure.instIsEmptyZero`,
  `GroupCount.GroupStructure.nonempty_iff` — there is no group structure on the
  empty carrier `Fin 0`, and `Nonempty (GroupStructure n) ↔ 1 ≤ n`.

Ground truth: `Fintype.card (GroupStructure n) = 0, 1, 2` at `n = 0, 1, 2`
(closed by `decide`), matching OEIS A034383 ("Number of labeled groups":
`1, 2, 3, 16, 30, 480, …` at `n = 1, 2, 3, …`; the identity and inversion
tables are uniquely determined by the multiplication table, so `GroupStructure n`
counts labeled groups).
-/

set_option autoImplicit false

namespace GroupCount

/-- A group structure on the carrier `Fin n`, given by explicit multiplication,
identity, and inverse tables together with the three left group axioms
(associativity, left identity, left inverse).  By `Group.ofLeftAxioms` these
imply the full group axioms; see `GroupCount.GroupStructure.toGroup`.
All three axiom fields are decidable finite checks, so this type is finitely
enumerable (`GroupCount.GroupStructure.instFintype`). -/
structure GroupStructure (n : ℕ) where
  /-- The multiplication table. -/
  mul : Fin n → Fin n → Fin n
  /-- The identity element.  (Its existence forces `1 ≤ n`.) -/
  one : Fin n
  /-- The inversion table. -/
  inv : Fin n → Fin n
  /-- Multiplication is associative. -/
  mul_assoc : ∀ a b c : Fin n, mul (mul a b) c = mul a (mul b c)
  /-- `one` is a left identity. -/
  one_mul : ∀ a : Fin n, mul one a = a
  /-- `inv a` is a left inverse of `a`. -/
  inv_mul_cancel : ∀ a : Fin n, mul (inv a) a = one

namespace GroupStructure

variable {n : ℕ}

/-! ## Emptiness and nonemptiness of the carrier of structures -/

/-- There is no group structure on the empty carrier `Fin 0`: a group structure
provides an identity element, and `Fin 0` has none. -/
instance instIsEmptyZero : IsEmpty (GroupStructure 0) :=
  ⟨fun S => S.one.elim0⟩

/-- A group structure on `Fin n` forces `1 ≤ n`: the carrier contains the
identity element. -/
theorem one_le (S : GroupStructure n) : 1 ≤ n := S.one.pos

/-! ## The raw-tables representation and the `Fintype` instance -/

/-- The raw data of a candidate group structure on `Fin n`: a multiplication
table, an identity element, and an inversion table, with no axioms imposed. -/
abbrev RawTables (n : ℕ) : Type :=
  (Fin n → Fin n → Fin n) × Fin n × (Fin n → Fin n)

/-- The (decidable) predicate on raw tables asserting the three left group
axioms: associativity, left identity, left inverse. -/
abbrev IsGroupTables (t : RawTables n) : Prop :=
  (∀ a b c, t.1 (t.1 a b) c = t.1 a (t.1 b c)) ∧
    (∀ a, t.1 t.2.1 a = a) ∧
    (∀ a, t.1 (t.2.2 a) a = t.2.1)

/-- `GroupStructure n` is equivalent to the subtype of raw table triples
satisfying the (decidable) left group axioms.  This equivalence powers the
`Fintype` and `DecidableEq` instances. -/
def equivSubtype (n : ℕ) : GroupStructure n ≃ { t : RawTables n // IsGroupTables t } where
  toFun S := ⟨(S.mul, S.one, S.inv), ⟨S.mul_assoc, S.one_mul, S.inv_mul_cancel⟩⟩
  invFun t :=
    { mul := t.val.1
      one := t.val.2.1
      inv := t.val.2.2
      mul_assoc := t.property.1
      one_mul := t.property.2.1
      inv_mul_cancel := t.property.2.2 }
  left_inv _ := rfl
  right_inv _ := rfl

/-- The type of group structures on `Fin n` is finite: it is (equivalent to) a
decidable subtype of the finite type of raw table triples. -/
instance instFintype : Fintype (GroupStructure n) :=
  Fintype.ofEquiv _ (equivSubtype n).symm

/-- Equality of group structures on `Fin n` is decidable (compare the tables). -/
instance instDecidableEq : DecidableEq (GroupStructure n) :=
  (equivSubtype n).decidableEq

/-! ## The bridge to Mathlib `Group (Fin n)` instances -/

/-- The Mathlib `Group (Fin n)` instance packaged by a `GroupStructure n`,
via the minimal-axioms constructor `Group.ofLeftAxioms`.  The data fields are
preserved definitionally; see `GroupCount.GroupStructure.toGroup_mul`,
`toGroup_one`, `toGroup_inv`, and the round trip `ofGroup_toGroup`. -/
@[instance_reducible] def toGroup (S : GroupStructure n) : Group (Fin n) :=
  letI : Mul (Fin n) := ⟨S.mul⟩
  letI : One (Fin n) := ⟨S.one⟩
  letI : Inv (Fin n) := ⟨S.inv⟩
  Group.ofLeftAxioms S.mul_assoc S.one_mul S.inv_mul_cancel

/-- The explicit table representation of a Mathlib `Group (Fin n)` instance.
Stated via the structure projections of `G` (not via `*`/`1`/`⁻¹` notation,
whose instance resolution at the carrier `Fin n` would pick up the ambient
`Fin` arithmetic instances rather than `G`). -/
def ofGroup (G : Group (Fin n)) : GroupStructure n where
  mul := G.mul
  one := G.one
  inv := G.inv
  mul_assoc := G.mul_assoc
  one_mul := G.one_mul
  inv_mul_cancel := G.inv_mul_cancel

/-- The multiplication of the group `S.toGroup` is the table `S.mul`. -/
theorem toGroup_mul (S : GroupStructure n) (a b : Fin n) :
    S.toGroup.mul a b = S.mul a b := rfl

/-- The identity of the group `S.toGroup` is the element `S.one`. -/
theorem toGroup_one (S : GroupStructure n) :
    S.toGroup.one = S.one := rfl

/-- The inversion of the group `S.toGroup` is the table `S.inv`. -/
theorem toGroup_inv (S : GroupStructure n) (a : Fin n) :
    S.toGroup.inv a = S.inv a := rfl

/-- Round trip: reading the tables back off `S.toGroup` recovers `S`.
In particular `toGroup` is injective. -/
@[simp] theorem ofGroup_toGroup (S : GroupStructure n) : ofGroup S.toGroup = S := rfl

/-- Round trip: rebuilding a group from its tables gives back the same group.
In particular `toGroup` is surjective onto `Group (Fin n)`. -/
@[simp] theorem toGroup_ofGroup (G : Group (Fin n)) : (ofGroup G).toGroup = G :=
  Group.ext rfl

/-- Explicit group structures on `Fin n` are exactly the Mathlib group
structures on `Fin n`: the table representation loses no information. -/
def equivGroup (n : ℕ) : GroupStructure n ≃ Group (Fin n) where
  toFun := toGroup
  invFun := ofGroup
  left_inv := ofGroup_toGroup
  right_inv := toGroup_ofGroup

/-! ## The cyclic witness -/

/-- The cyclic group structure on `Fin n` for `n ≠ 0`: addition modulo `n`,
written multiplicatively.  Witnesses nonemptiness of `GroupStructure n`. -/
def cyclic (n : ℕ) [NeZero n] : GroupStructure n where
  mul a b := a + b
  one := 0
  inv a := -a
  mul_assoc := add_assoc
  one_mul := zero_add
  inv_mul_cancel := neg_add_cancel

/-- For `n ≠ 0` there is a group structure on `Fin n` (the cyclic one). -/
instance instNonempty [NeZero n] : Nonempty (GroupStructure n) := ⟨cyclic n⟩

/-- For `1 ≤ n` the type of group structures on `Fin n` is nonempty, witnessed
by the cyclic structure `GroupCount.GroupStructure.cyclic`. -/
theorem nonempty (hn : 1 ≤ n) : Nonempty (GroupStructure n) :=
  haveI : NeZero n := ⟨Nat.one_le_iff_ne_zero.mp hn⟩
  ⟨cyclic n⟩

/-- The carrier `Fin n` admits a group structure iff `1 ≤ n`. -/
theorem nonempty_iff (n : ℕ) : Nonempty (GroupStructure n) ↔ 1 ≤ n :=
  ⟨fun h => h.elim fun S => S.one_le, fun hn => nonempty hn⟩

end GroupStructure

/-! ## Finiteness of `Group (Fin n)` itself -/

/-- The type of Mathlib group structures on `Fin n` is finite, via the table
representation `GroupCount.GroupStructure.equivGroup`. -/
instance instFintypeGroupFin (n : ℕ) : Fintype (Group (Fin n)) :=
  Fintype.ofEquiv _ (GroupStructure.equivGroup n)

/-- Counting group structures on `Fin n` via tables or via Mathlib `Group`
instances agrees. -/
theorem card_group_fin (n : ℕ) :
    Fintype.card (Group (Fin n)) = Fintype.card (GroupStructure n) :=
  Fintype.card_congr (GroupStructure.equivGroup n).symm

/-- There are no group structures on the empty carrier: the count at `n = 0`
is `0`. -/
theorem card_groupStructure_zero : Fintype.card (GroupStructure 0) = 0 :=
  Fintype.card_eq_zero

/-! ## Ground truth

Satisfiability and sanity checks required by `STYLE.md`: every hypothesis
instantiated jointly at concrete models, and `decide`-closed counts at tiny `n`
cross-checked against OEIS A034383 (number of labeled groups: `1, 2, 3, …`). -/

section GroundTruth

open GroupStructure

-- The cyclic tables satisfy the axiom predicate at a nondegenerate size…
example : IsGroupTables (((· + ·), 0, (- ·)) : RawTables 3) := by decide
-- …and the predicate is not vacuous: constant tables fail it.
example : ¬ IsGroupTables (((fun _ _ => 0), 0, fun _ => 0) : RawTables 2) := by decide

-- The cyclic witness computes as addition modulo `n`.
example : (cyclic 3).mul 1 2 = 0 := by decide
example : (cyclic 3).one = 0 := by decide
example : (cyclic 3).inv 1 = 2 := by decide
example : (cyclic 5).mul 2 4 = 1 := by decide

-- The bridge round trip at a concrete model: both bridge directions
-- instantiated jointly at the cyclic structure on `Fin 3`.
example : ofGroup (cyclic 3).toGroup = cyclic 3 := ofGroup_toGroup (cyclic 3)

-- `nonempty` instantiated with its hypothesis discharged at `n = 3`.
example : Nonempty (GroupStructure 3) := GroupStructure.nonempty (by omega)

-- Labeled group counts at tiny sizes (OEIS A034383, prepended with the empty
-- carrier): 0, 1, 2 group structures at n = 0, 1, 2.
example : Fintype.card (GroupStructure 0) = 0 := by decide
example : Fintype.card (GroupStructure 1) = 1 := by decide
example : Fintype.card (GroupStructure 2) = 2 := by decide

-- A034383 continues 3, 16, 30, …  Kernel reduction is infeasible at `n = 3`
-- (the raw search space has `3^9 · 3 · 3^3 ≈ 1.6 · 10^6` table triples), so
-- this one check uses `native_decide`: it enlarges the trusted base with the
-- compiler (`Lean.ofReduceBool`).  It is a sanity example only; no named
-- theorem depends on it.
example : Fintype.card (GroupStructure 3) = 3 := by native_decide

end GroundTruth

end GroupCount
