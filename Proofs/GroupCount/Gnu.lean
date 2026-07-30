import GroupCount.Structures

/-!
# `gnu n`: groups of order `n` up to isomorphism (OEIS A000001)

`GroupCount.gnu n` is the *group number* of `n` — the number of groups of order `n` up
to isomorphism, OEIS A000001, called `gnu(n)` after Conway–Dietrich–O'Brien (2008).  It
is built on the committed labeled layer `GroupCount/Structures.lean`
(`GroupStructure n ≃ Group (Fin n)`, a `Fintype` with decidable equality) by quotienting
by isomorphism.

**No classification theorem is needed to define it.**  Group structures on the carrier
`Fin n` form a finite type; isomorphism between two of them is a decidable search over
the `n!` permutations of the carrier; so the quotient is a `Fintype` and `gnu n` is its
cardinality.

## Main definitions

* `GroupCount.GroupStructure.Iso` — table-preserving permutation of the carrier;
  decidable (`instDecidableIso`), an equivalence relation (`isoSetoid`).
* `GroupCount.GroupStructure.Carrier` — `Fin n` re-tagged by the structure, carrying the
  `Group`/`Fintype`/`DecidableEq` instances of that structure.  Tagging lets *two*
  structures carry simultaneous non-conflicting instances on the same underlying type,
  so ordinary Mathlib group theory (`orderOf`, `IsCyclic`, `Monoid.exponent`, …) applies
  to each without `@`-gymnastics.
* `GroupCount.IsoClass n` — the quotient; `GroupCount.gnu n` — its cardinality.
* `GroupCount.GroupStructure.prod` / `GroupCount.IsoClass.prod` — direct product, and
  its descent to isomorphism classes.
* `GroupCount.GroupStructure.powOneCount` — the decidable invariant `#{x | xᵏ = 1}`.

## Main results

* `GroupCount.GroupStructure.iso_iff_nonempty_mulEquiv` (**soundness**) — `S.Iso T` iff
  the groups `S.Carrier` and `T.Carrier` are `MulEquiv`.
* `GroupCount.GroupStructure.exists_carrier_mulEquiv` (**completeness**) — every finite
  group of order `n` is isomorphic to some `S.Carrier`.  Together these are what make
  `gnu n` a count of *all* groups of order `n`, not only the `Fin n`-carried ones.
* `GroupCount.gnu_eq_zero_iff` — the junk value is pinned: `gnu n = 0 ↔ n = 0`.
* `GroupCount.card_eq_gnu_of_classification`, `card_le_gnu_of_pairwise_not_iso` — a
  classification computes `gnu`; irredundancy alone bounds it below.
* `GroupCount.mul_gnu_le_gnu_of_injective` — the reduction of the Lopes conjecture
  `gnu i * gnu j ≤ gnu (i * j)` to injectivity of the descended product map.  The
  injectivity itself is **not** proved here; it is the downstream lane's job.
* `GroupCount.gnu_prime` — `gnu p = 1` at every prime.
* `GroupCount.gnu_four` — `gnu 4 = 2`, via `GroupCount.isCyclic_or_isKleinFour`.

## Trust policy (USER decision, binding for this file)

**Zero `native_decide` anywhere in this module — no exceptions, not even in anonymous
trust-noted examples.**  Every numeric value of `gnu` asserted here is certified by one
of exactly two routes:

1. **kernel `decide`**, where kernel evaluation is actually feasible; or
2. **a genuine classification proof**, using Mathlib's group theory.

Anything reachable by neither route is *omitted*, never asserted from a compiled
evaluation.  The axiom sweep at the end of the file is the check: no declaration depends
on `Lean.ofReduceBool`.

### Measured kernel-evaluation wall

Deciding a *value* of `gnu n` forces the kernel to enumerate the raw table space
`(Fin n → Fin n → Fin n) × Fin n × (Fin n → Fin n)`, of size `n ^ (n² + n + 1)`.
Measured (12 GB cgroup cap, `MemorySwapMax=0`):

| `n` | raw tables | `decide` outcome |
|---|---|---|
| 0, 1 | 1 | instant |
| 2 | 128 | ≈ 1 s |
| 3 | 1 594 323 | **wall** |

At `n = 3` the elaborator hits `maximum recursion depth` in ≈ 1 s; `decide +kernel` hits
the kernel's own `deep recursion` in ≈ 1 s; and with `maxRecDepth 100000` the build was
**OOM-killed at 12 GB after 114 s of CPU**.  The recursion depth needed is proportional
to the list length `3^9 · 3 · 3^3 ≈ 1.6 · 10⁶`, so this is a genuine wall, not a tuning
artifact.  (Consistent with `GroupCount/Structures.lean`, which records the labeled count
at `n = 3` as kernel-infeasible.)  **So the exact-value `decide` route stops at `n = 2`.**

Two cheaper computations stay far inside the wall and are used here:

* deciding `Iso` between two *given* structures (`n!` permutations × `n²` entries), and
* the invariant `powOneCount` (`O(k · n)`),

so *lower* bounds on `gnu` are kernel-certifiable well past `n = 3`
(`GroupCount.two_le_gnu_four` is proved this way, at `n = 4`).  Pushing the *exact-value*
wall would need a reduced enumeration — Cayley tables normalised so the identity is `0`,
i.e. reduced Latin squares — proved to meet every isomorphism class; that is a separate
piece of work and is not attempted here.

## References

* OEIS A000001 (`oeis show A000001`): `0, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 5, 1, 2, 1,
  14, …` at `n = 0, 1, 2, …`.
* J. H. Conway, H. Dietrich, E. A. O'Brien, *Counting groups: gnus, moas and other
  exotica*, Math. Intelligencer 30 (2008) — the source of the name `gnu(n)`.
-/

set_option autoImplicit false

namespace GroupCount

namespace GroupStructure

variable {n : ℕ}

/-! ## Isomorphism of explicit structures -/

/-- Two explicit group structures on the carrier `Fin n` are *isomorphic* when some
permutation of `Fin n` carries the first multiplication table to the second.  This is
a decidable finite condition (`GroupCount.GroupStructure.instDecidableIso`); it agrees
with the existence of a Mathlib `MulEquiv` between the two groups
(`GroupCount.GroupStructure.iso_iff_nonempty_mulEquiv`). -/
def Iso (S T : GroupStructure n) : Prop :=
  ∃ e : Fin n ≃ Fin n, ∀ a b : Fin n, e (S.mul a b) = T.mul (e a) (e b)

/-- Isomorphism of explicit structures is decidable: search the `n!` permutations of
the carrier and check the `n²` table entries for each. -/
instance instDecidableIso (S T : GroupStructure n) : Decidable (S.Iso T) :=
  inferInstanceAs
    (Decidable (∃ e : Fin n ≃ Fin n, ∀ a b : Fin n, e (S.mul a b) = T.mul (e a) (e b)))

/-- Isomorphism is reflexive (the identity permutation). -/
@[refl] theorem Iso.refl (S : GroupStructure n) : S.Iso S := ⟨Equiv.refl _, fun _ _ => rfl⟩

/-- Isomorphism is symmetric (invert the permutation). -/
theorem Iso.symm {S T : GroupStructure n} (h : S.Iso T) : T.Iso S := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun a b => e.injective ?_⟩
  rw [Equiv.apply_symm_apply, he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Isomorphism is transitive (compose the permutations). -/
theorem Iso.trans {S T U : GroupStructure n} (h₁ : S.Iso T) (h₂ : T.Iso U) : S.Iso U := by
  obtain ⟨e₁, he₁⟩ := h₁
  obtain ⟨e₂, he₂⟩ := h₂
  refine ⟨e₁.trans e₂, fun a b => ?_⟩
  rw [Equiv.trans_apply, he₁, he₂, Equiv.trans_apply, Equiv.trans_apply]

/-- Isomorphism is an equivalence relation on the explicit structures on `Fin n`.
Registered as the canonical `Setoid` so that `S ≈ T` means `S.Iso T`. -/
instance isoSetoid (n : ℕ) : Setoid (GroupStructure n) where
  r := Iso
  iseqv := ⟨Iso.refl, Iso.symm, Iso.trans⟩

/-- The `Setoid` relation `S ≈ T` unfolds to `S.Iso T`. -/
theorem isoSetoid_r (S T : GroupStructure n) : S ≈ T ↔ S.Iso T := Iff.rfl

/-- The setoid relation is decidable, which is what makes the quotient a `Fintype`. -/
instance instDecidableSetoidIso (S T : GroupStructure n) : Decidable (S ≈ T) :=
  instDecidableIso S T

/-! ## The carrier as a genuine Mathlib group

`Carrier S` is the type `Fin n` re-tagged by `S`.  Tagging is what lets two structures
carry *simultaneous* non-conflicting `Group` instances on the same underlying type, so
that ordinary Mathlib group theory (`orderOf`, `IsCyclic`, `Monoid.exponent`, …) applies
to each of them without `@`-gymnastics. -/

/-- The carrier `Fin n`, tagged by the structure `S` so that the `Group` instance below
is attached to `S` rather than to `Fin n` itself. -/
def Carrier (_S : GroupStructure n) : Type := Fin n

/-- The group whose multiplication table is `S`. -/
instance instGroupCarrier (S : GroupStructure n) : Group S.Carrier := S.toGroup

/-- The tagged carrier is finite, with the `Fin n` enumeration. -/
instance instFintypeCarrier (S : GroupStructure n) : Fintype S.Carrier :=
  inferInstanceAs (Fintype (Fin n))

/-- Equality on the tagged carrier is decidable, as on `Fin n`. -/
instance instDecidableEqCarrier (S : GroupStructure n) : DecidableEq S.Carrier :=
  inferInstanceAs (DecidableEq (Fin n))

/-- Untagging: the carrier of `S` is `Fin n`. -/
def carrierEquiv (S : GroupStructure n) : S.Carrier ≃ Fin n := Equiv.refl _

/-- Multiplication in the group `S.Carrier` is the table `S.mul`. -/
theorem carrierEquiv_mul (S : GroupStructure n) (a b : S.Carrier) :
    S.carrierEquiv (a * b) = S.mul (S.carrierEquiv a) (S.carrierEquiv b) := rfl

/-- Multiplication in the group `S.Carrier` is the table `S.mul` (untagged form). -/
theorem carrierEquiv_symm_mul (S : GroupStructure n) (a b : Fin n) :
    S.carrierEquiv.symm (S.mul a b) = S.carrierEquiv.symm a * S.carrierEquiv.symm b := rfl

/-- The identity of the group `S.Carrier` is the element `S.one`. -/
theorem carrierEquiv_one (S : GroupStructure n) : S.carrierEquiv 1 = S.one := rfl

/-- The identity of the group `S.Carrier` is the element `S.one` (untagged form). -/
theorem carrierEquiv_symm_one (S : GroupStructure n) : S.carrierEquiv.symm S.one = 1 := rfl

/-- The group `S.Carrier` has order `n`: it is a group *of order `n`*. -/
@[simp] theorem card_carrier (S : GroupStructure n) : Fintype.card S.Carrier = n :=
  Fintype.card_fin n

/-- The group `S.Carrier` has order `n` (`Nat.card` form, for the Mathlib lemmas
stated with `Nat.card`). -/
@[simp] theorem natCard_carrier (S : GroupStructure n) : Nat.card S.Carrier = n := by
  rw [Nat.card_eq_fintype_card, card_carrier]

/-! ## Soundness: `Iso` is isomorphism of groups -/

/-- A table-preserving permutation of `Fin n` is a group isomorphism of the tagged
carriers. -/
def isoMulEquiv {S T : GroupStructure n} (e : Fin n ≃ Fin n)
    (he : ∀ a b : Fin n, e (S.mul a b) = T.mul (e a) (e b)) : S.Carrier ≃* T.Carrier where
  toFun a := T.carrierEquiv.symm (e (S.carrierEquiv a))
  invFun b := S.carrierEquiv.symm (e.symm (T.carrierEquiv b))
  left_inv a := by simp
  right_inv b := by simp
  map_mul' a b := by
    apply T.carrierEquiv.injective
    simp only [carrierEquiv_mul, Equiv.apply_symm_apply, he]

/-- A group isomorphism of tagged carriers is a table-preserving permutation. -/
theorem iso_of_mulEquiv {S T : GroupStructure n} (f : S.Carrier ≃* T.Carrier) : S.Iso T := by
  refine ⟨⟨fun a => T.carrierEquiv (f (S.carrierEquiv.symm a)),
           fun b => S.carrierEquiv (f.symm (T.carrierEquiv.symm b)),
           fun a => by simp, fun b => by simp⟩, fun a b => ?_⟩
  show T.carrierEquiv (f (S.carrierEquiv.symm (S.mul a b))) = _
  rw [carrierEquiv_symm_mul, map_mul, carrierEquiv_mul]
  rfl

/-- **Soundness of the quotient.**  Two explicit structures on `Fin n` are `Iso` exactly
when the groups they present are isomorphic in Mathlib's sense. -/
theorem iso_iff_nonempty_mulEquiv (S T : GroupStructure n) :
    S.Iso T ↔ Nonempty (S.Carrier ≃* T.Carrier) :=
  ⟨fun ⟨e, he⟩ => ⟨isoMulEquiv e he⟩, fun ⟨f⟩ => iso_of_mulEquiv f⟩

/-! ## Transporting an arbitrary group onto `Fin n` -/

/-- The explicit structure on `Fin n` induced by a group `G` together with a bijection
`Fin n ≃ G`: the transported multiplication `a * b := e⁻¹ (e a * e b)`. -/
def ofEquiv {G : Type*} [Group G] (e : Fin n ≃ G) : GroupStructure n :=
  ofGroup (Equiv.group e)

/-- The transported table is `a * b := e⁻¹ (e a * e b)`. -/
theorem ofEquiv_mul {G : Type*} [Group G] (e : Fin n ≃ G) (a b : Fin n) :
    (ofEquiv e).mul a b = e.symm (e a * e b) := rfl

/-- `ofEquiv e` presents a group isomorphic to `G`: the transport loses nothing. -/
def ofEquivMulEquiv {G : Type*} [Group G] (e : Fin n ≃ G) : (ofEquiv e).Carrier ≃* G where
  toFun a := e ((ofEquiv e).carrierEquiv a)
  invFun g := (ofEquiv e).carrierEquiv.symm (e.symm g)
  left_inv a := e.symm_apply_apply _
  right_inv g := e.apply_symm_apply g
  map_mul' a b := by
    rw [carrierEquiv_mul, ofEquiv_mul, Equiv.apply_symm_apply]

/-- **Completeness of the labeled layer.**  Every finite group of order `n` is isomorphic
to the group presented by some explicit structure on `Fin n`.  Together with
`GroupCount.GroupStructure.iso_iff_nonempty_mulEquiv` this is what makes the quotient
below a count of *all* groups of order `n`, not merely of the `Fin n`-carried ones. -/
theorem exists_carrier_mulEquiv {G : Type*} [Group G] [Fintype G]
    (h : Fintype.card G = n) : ∃ S : GroupStructure n, Nonempty (G ≃* S.Carrier) :=
  ⟨ofEquiv (Fintype.equivFinOfCardEq h).symm, ⟨(ofEquivMulEquiv _).symm⟩⟩

/-! ## Direct products -/

/-- `Fin (i * j)` split as a product of tagged carriers, along `finProdFinEquiv`. -/
def prodEquiv {i j : ℕ} (S : GroupStructure i) (T : GroupStructure j) :
    Fin (i * j) ≃ S.Carrier × T.Carrier :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr S.carrierEquiv.symm T.carrierEquiv.symm)

/-- The direct product of explicit structures, as an explicit structure on `Fin (i * j)`. -/
def prod {i j : ℕ} (S : GroupStructure i) (T : GroupStructure j) : GroupStructure (i * j) :=
  ofEquiv (S.prodEquiv T)

/-- The group presented by `S.prod T` is the direct product of the groups presented by
`S` and `T`. -/
def prodMulEquiv {i j : ℕ} (S : GroupStructure i) (T : GroupStructure j) :
    (S.prod T).Carrier ≃* S.Carrier × T.Carrier :=
  ofEquivMulEquiv _

/-- The direct product respects isomorphism in each argument, hence descends to the
isomorphism-class quotient (`GroupCount.IsoClass.prod`). -/
theorem prod_iso_prod {i j : ℕ} {S S' : GroupStructure i} {T T' : GroupStructure j}
    (h₁ : S.Iso S') (h₂ : T.Iso T') : (S.prod T).Iso (S'.prod T') := by
  obtain ⟨f⟩ := (iso_iff_nonempty_mulEquiv S S').mp h₁
  obtain ⟨g⟩ := (iso_iff_nonempty_mulEquiv T T').mp h₂
  exact iso_of_mulEquiv
    ((prodMulEquiv S T).trans ((f.prodCongr g).trans (prodMulEquiv S' T').symm))

/-! ## A decidable isomorphism invariant

Deciding `Iso` between two *given* structures costs `n! · n²` — cheap.  Deciding a
*value* of `gnu` costs an enumeration of all `n^(n²+n+1)` raw tables — the kernel wall.
The invariant below is cheaper still (`O(k · n)`) and certifies non-isomorphism, hence
lower bounds on `gnu`, without either search. -/

/-- Iterated multiplication in the table; `S.npow k a` is the `k`-th power of `a`
(`GroupCount.GroupStructure.carrierEquiv_symm_npow`). -/
def npow (S : GroupStructure n) : ℕ → Fin n → Fin n
  | 0, _ => S.one
  | (k + 1), a => S.mul a (S.npow k a)

/-- The bridge between the table-level `npow` and Mathlib's `^` on the tagged
carrier: transporting `S.npow k a` along `carrierEquiv.symm` is the `k`-th power
in the group. This is the lemma a consumer needs first to move between table
iteration and group-theoretic powers. -/
theorem carrierEquiv_symm_npow (S : GroupStructure n) (k : ℕ) (a : Fin n) :
    S.carrierEquiv.symm (S.npow k a) = S.carrierEquiv.symm a ^ k := by
  induction k with
  | zero => rw [pow_zero]; rfl
  | succ k ih => rw [show S.npow (k + 1) a = S.mul a (S.npow k a) from rfl,
      carrierEquiv_symm_mul, ih, ← pow_succ']

/-- The number of solutions of `x ^ k = 1` in `S` — a decidable isomorphism invariant. -/
def powOneCount (S : GroupStructure n) (k : ℕ) : ℕ :=
  Fintype.card {a : Fin n // S.npow k a = S.one}

/-- `powOneCount` counts the `k`-th roots of unity of the group `S.Carrier`. -/
theorem powOneCount_eq_card_pow (S : GroupStructure n) (k : ℕ) :
    S.powOneCount k = Fintype.card {a : S.Carrier // a ^ k = 1} := by
  refine Fintype.card_congr (Equiv.subtypeEquiv S.carrierEquiv.symm fun a => ?_)
  rw [← carrierEquiv_symm_npow]
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact S.carrierEquiv.symm.injective h

/-- `powOneCount` is an isomorphism invariant. -/
theorem powOneCount_eq_of_iso {S T : GroupStructure n} (h : S.Iso T) (k : ℕ) :
    S.powOneCount k = T.powOneCount k := by
  obtain ⟨f⟩ := (iso_iff_nonempty_mulEquiv S T).mp h
  rw [powOneCount_eq_card_pow, powOneCount_eq_card_pow]
  refine Fintype.card_congr (Equiv.subtypeEquiv f.toEquiv fun a => ?_)
  show a ^ k = 1 ↔ f a ^ k = 1
  rw [← map_pow, f.map_eq_one_iff]

/-- Distinct invariant values certify non-isomorphism — the cheap route to lower bounds
on `gnu` (`GroupCount.two_le_gnu_of_not_iso`). -/
theorem not_iso_of_powOneCount_ne {S T : GroupStructure n} {k : ℕ}
    (h : S.powOneCount k ≠ T.powOneCount k) : ¬ S.Iso T :=
  fun hiso => h (powOneCount_eq_of_iso hiso k)

/-- The Klein four-group as an explicit structure on `Fin 4`, namely
`C₂ × C₂` transported along `finProdFinEquiv` (note `2 * 2` reduces to `4`). -/
def klein : GroupStructure 4 := (cyclic 2).prod (cyclic 2)

/-! ## Recognising cyclic and exponent-two structures

Both criteria below are *decidable bounded searches* on the tables, so a concrete
structure can be recognised by kernel `decide` and then handed to Mathlib's group
theory through `Carrier`. -/

/-- A structure whose iterated powers of a single carrier element reach everything
presents a cyclic group.  The hypothesis is a decidable finite search. -/
theorem isCyclic_carrier_of_generator {S : GroupStructure n} (g : Fin n)
    (h : ∀ x : Fin n, ∃ k : Fin n, S.npow k.val g = x) : IsCyclic S.Carrier := by
  refine ⟨S.carrierEquiv.symm g, fun x => ?_⟩
  obtain ⟨k, hk⟩ := h (S.carrierEquiv x)
  refine ⟨(k.val : ℤ), ?_⟩
  show S.carrierEquiv.symm g ^ ((k.val : ℕ) : ℤ) = x
  rw [zpow_natCast, ← carrierEquiv_symm_npow, hk, Equiv.symm_apply_apply]

/-- A table-level check `∀ a, a ^ k = 1`, transported to the group `S.Carrier`. -/
theorem pow_eq_one_of_npow_eq_one {S : GroupStructure n} {k : ℕ}
    (h : ∀ a : Fin n, S.npow k a = S.one) (a : S.Carrier) : a ^ k = 1 := by
  have key := carrierEquiv_symm_npow S k (S.carrierEquiv a)
  rw [h, Equiv.symm_apply_apply] at key
  exact key.symm

open Fin.NatCast in
/-- Powers of the generator in the cyclic structure are the carrier elements themselves. -/
theorem cyclic_npow (n : ℕ) [NeZero n] (k : ℕ) : (cyclic n).npow k 1 = (k : Fin n) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (cyclic n).mul 1 ((cyclic n).npow k 1) = _
    rw [ih]
    show (1 : Fin n) + (k : Fin n) = ((k + 1 : ℕ) : Fin n)
    push_cast
    abel

open Fin.NatCast in
/-- The cyclic witness really is cyclic. -/
instance isCyclic_carrier_cyclic (n : ℕ) [NeZero n] : IsCyclic (cyclic n).Carrier :=
  isCyclic_carrier_of_generator 1 fun x => ⟨x, by rw [cyclic_npow, Fin.cast_val_eq_self]⟩

/-- `klein` is a Klein four-group in Mathlib's sense: order four and exponent two.
Exponent two is a kernel `decide` on the table; nontriviality rules out exponent one. -/
instance isKleinFour_klein : IsKleinFour klein.Carrier where
  card_four := klein.natCard_carrier
  exponent_two := by
    have hdvd : Monoid.exponent klein.Carrier ∣ 2 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one (pow_eq_one_of_npow_eq_one (by decide))
    have hne : Monoid.exponent klein.Carrier ≠ 1 := by
      rw [Ne, Monoid.exp_eq_one_iff]
      intro hs
      have hle : Fintype.card klein.Carrier ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr hs
      rw [klein.card_carrier] at hle
      omega
    exact (Nat.prime_two.eq_one_or_self_of_dvd _ hdvd).resolve_left hne

end GroupStructure

/-! ## The isomorphism-class quotient and `gnu` -/

/-- The isomorphism classes of group structures on the carrier `Fin n`; equivalently
(by `GroupCount.GroupStructure.exists_carrier_mulEquiv` and
`GroupCount.GroupStructure.iso_iff_nonempty_mulEquiv`) the isomorphism classes of
groups of order `n`. -/
abbrev IsoClass (n : ℕ) : Type := Quotient (GroupStructure.isoSetoid n)

/-- The isomorphism class of an explicit structure. -/
def GroupStructure.isoClass {n : ℕ} (S : GroupStructure n) : IsoClass n := Quotient.mk _ S

/-- Two structures have the same isomorphism class exactly when they are isomorphic. -/
theorem GroupStructure.isoClass_eq_iff {n : ℕ} (S T : GroupStructure n) :
    S.isoClass = T.isoClass ↔ S.Iso T := Quotient.eq

/-- Every isomorphism class is the class of some explicit structure. -/
theorem GroupStructure.isoClass_surjective (n : ℕ) :
    Function.Surjective (GroupStructure.isoClass (n := n)) := Quotient.mk_surjective

/-- **`gnu n` — OEIS A000001**: the number of groups of order `n` up to isomorphism,
defined as the number of isomorphism classes of group structures on the carrier `Fin n`.
No classification theorem is needed: the structures form a `Fintype` and isomorphism is
a decidable finite search, so this is an honest (if astronomically inefficient)
definition.  `gnu 0 = 0` because there is no group on the empty carrier. -/
def gnu (n : ℕ) : ℕ := Fintype.card (IsoClass n)

/-- Bridge to the `Nat.card` spelling, for Mathlib lemmas stated that way. -/
theorem gnu_eq_natCard (n : ℕ) : gnu n = Nat.card (IsoClass n) :=
  (Nat.card_eq_fintype_card).symm

/-- The direct product descended to isomorphism classes. -/
def IsoClass.prod {i j : ℕ} : IsoClass i → IsoClass j → IsoClass (i * j) :=
  Quotient.map₂ GroupStructure.prod fun _ _ h₁ _ _ h₂ => GroupStructure.prod_iso_prod h₁ h₂

/-- `isoClass` commutes with the direct product: the class of `S.prod T` is the
descended product of the classes. Definitional; the `@[simp]` direction pushes
`isoClass` inward. -/
@[simp] theorem GroupStructure.isoClass_prod {i j : ℕ} (S : GroupStructure i)
    (T : GroupStructure j) : (S.prod T).isoClass = IsoClass.prod S.isoClass T.isoClass := rfl

/-- Characterizing equation for `prodMulEquiv` (definitional): it is `prodEquiv`
composed with `carrierEquiv` on the product structure. This is the computation
rule the coprime-injectivity (Lopes/Submult) lane rewrites with. -/
theorem GroupStructure.prodMulEquiv_apply {i j : ℕ} (S : GroupStructure i)
    (T : GroupStructure j) (x : (S.prod T).Carrier) :
    GroupStructure.prodMulEquiv S T x = S.prodEquiv T ((S.prod T).carrierEquiv x) := rfl

/-! ## Junk values, positivity, and the `gnu n = 1` criterion -/

/-- The quotient is empty exactly when there is no structure to classify. -/
theorem isEmpty_isoClass_iff (n : ℕ) : IsEmpty (IsoClass n) ↔ IsEmpty (GroupStructure n) := by
  constructor
  · intro h
    exact ⟨fun S => h.elim S.isoClass⟩
  · intro h
    refine ⟨fun q => ?_⟩
    obtain ⟨S, _⟩ := GroupStructure.isoClass_surjective n q
    exact h.elim S

/-- **The junk value is pinned.**  `gnu n = 0` happens exactly at `n = 0`: the empty
carrier supports no group, and every `1 ≤ n` supports at least the cyclic one. -/
theorem gnu_eq_zero_iff (n : ℕ) : gnu n = 0 ↔ n = 0 := by
  rw [gnu, Fintype.card_eq_zero_iff, isEmpty_isoClass_iff, ← not_nonempty_iff,
    GroupStructure.nonempty_iff]
  omega

/-- There is no group of order `0`, so `gnu 0 = 0` (A000001 begins `a(0) = 0`). -/
theorem gnu_zero : gnu 0 = 0 := (gnu_eq_zero_iff 0).mpr rfl

/-- Every `n ≥ 1` has at least the cyclic group of order `n`. -/
theorem one_le_gnu {n : ℕ} (hn : 1 ≤ n) : 1 ≤ gnu n := by
  rcases Nat.eq_zero_or_pos (gnu n) with h | h
  · exact absurd ((gnu_eq_zero_iff n).mp h) (by omega)
  · exact h

/-- `gnu n = 1` exactly when `n ≥ 1` and all explicit structures on `Fin n` are
isomorphic. -/
theorem gnu_eq_one_iff {n : ℕ} :
    gnu n = 1 ↔ 1 ≤ n ∧ ∀ S T : GroupStructure n, S.Iso T := by
  constructor
  · intro h
    obtain ⟨q⟩ : Nonempty (IsoClass n) := Fintype.card_pos_iff.mp (by rw [← gnu]; omega)
    obtain ⟨S₀, _⟩ := GroupStructure.isoClass_surjective n q
    have hsub : Subsingleton (IsoClass n) :=
      Fintype.card_le_one_iff_subsingleton.mp (by rw [← gnu]; omega)
    exact ⟨(GroupStructure.nonempty_iff n).mp ⟨S₀⟩,
      fun S T => (GroupStructure.isoClass_eq_iff S T).mp (Subsingleton.elim _ _)⟩
  · rintro ⟨hn, hall⟩
    obtain ⟨S₀⟩ := (GroupStructure.nonempty_iff n).mpr hn
    refine Fintype.card_eq_one_iff.mpr ⟨S₀.isoClass, fun q => ?_⟩
    obtain ⟨T, rfl⟩ := GroupStructure.isoClass_surjective n q
    exact (GroupStructure.isoClass_eq_iff T S₀).mpr (hall T S₀)

/-! ## Counting from a classification

These are the workhorses for certifying a value of `gnu` beyond the kernel-evaluation
wall: exhibit a finite family of structures, prove it exhausts everything (upper bound)
and is irredundant (lower bound). -/

/-- **A classification computes `gnu`.**  A finite family of structures that is
exhaustive up to isomorphism and pairwise non-isomorphic has exactly `gnu n` members. -/
theorem card_eq_gnu_of_classification {n : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → GroupStructure n)
    (hexh : ∀ S : GroupStructure n, ∃ i, (F i).Iso S)
    (hirr : ∀ i j, (F i).Iso (F j) → i = j) :
    Fintype.card ι = gnu n := by
  have hbij : Function.Bijective fun i => (F i).isoClass := by
    refine ⟨fun i j hij => hirr i j ((GroupStructure.isoClass_eq_iff _ _).mp hij), fun q => ?_⟩
    obtain ⟨S, rfl⟩ := GroupStructure.isoClass_surjective n q
    obtain ⟨i, hi⟩ := hexh S
    exact ⟨i, (GroupStructure.isoClass_eq_iff _ _).mpr hi⟩
  exact Fintype.card_of_bijective hbij

/-- **Lower bounds from pairwise non-isomorphism.**  This direction needs no
classification: any irredundant family of structures bounds `gnu n` from below. -/
theorem card_le_gnu_of_pairwise_not_iso {n : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → GroupStructure n) (hirr : ∀ i j, (F i).Iso (F j) → i = j) :
    Fintype.card ι ≤ gnu n :=
  Fintype.card_le_of_injective (fun i => (F i).isoClass)
    fun i j hij => hirr i j ((GroupStructure.isoClass_eq_iff _ _).mp hij)

/-- Two non-isomorphic structures on `Fin n` give `2 ≤ gnu n`. -/
theorem two_le_gnu_of_not_iso {n : ℕ} {S T : GroupStructure n} (h : ¬ S.Iso T) :
    2 ≤ gnu n := by
  have key : Fintype.card Bool ≤ gnu n := by
    refine card_le_gnu_of_pairwise_not_iso (fun b => cond b T S) ?_
    intro i j hij
    cases i <;> cases j
    · rfl
    · exact absurd hij h
    · exact absurd hij.symm h
    · rfl
  simpa using key

/-- Two non-isomorphic groups of order `n` give `2 ≤ gnu n`. -/
theorem two_le_gnu_of_isEmpty_mulEquiv {n : ℕ} {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (hG : Fintype.card G = n) (hH : Fintype.card H = n)
    (h : IsEmpty (G ≃* H)) : 2 ≤ gnu n := by
  obtain ⟨S, ⟨f⟩⟩ := GroupStructure.exists_carrier_mulEquiv hG
  obtain ⟨T, ⟨g⟩⟩ := GroupStructure.exists_carrier_mulEquiv hH
  refine two_le_gnu_of_not_iso (S := S) (T := T) fun hiso => ?_
  obtain ⟨k⟩ := (GroupStructure.iso_iff_nonempty_mulEquiv S T).mp hiso
  exact h.elim (f.trans (k.trans g.symm))

/-- `gnu n = 1` transported to arbitrary groups: if there is only one group of order `n`
up to isomorphism then any two concrete groups of order `n` are isomorphic. -/
theorem nonempty_mulEquiv_of_gnu_eq_one {n : ℕ} (h : gnu n = 1) {G H : Type*}
    [Group G] [Group H] [Fintype G] [Fintype H]
    (hG : Fintype.card G = n) (hH : Fintype.card H = n) : Nonempty (G ≃* H) := by
  obtain ⟨S, ⟨f⟩⟩ := GroupStructure.exists_carrier_mulEquiv hG
  obtain ⟨T, ⟨g⟩⟩ := GroupStructure.exists_carrier_mulEquiv hH
  obtain ⟨k⟩ := (GroupStructure.iso_iff_nonempty_mulEquiv S T).mp ((gnu_eq_one_iff.mp h).2 S T)
  exact ⟨f.trans (k.trans g.symm)⟩

/-- The converse: if all groups of order `n` are isomorphic (and `1 ≤ n`), `gnu n = 1`.
Quantifying over `Type` loses nothing — every finite group of order `n` is isomorphic to
one carried by `Fin n` (`GroupCount.GroupStructure.exists_carrier_mulEquiv`). -/
theorem gnu_eq_one_of_forall_mulEquiv {n : ℕ} (hn : 1 ≤ n)
    (h : ∀ (G H : Type) [Group G] [Group H] [Fintype G] [Fintype H],
      Fintype.card G = n → Fintype.card H = n → Nonempty (G ≃* H)) : gnu n = 1 :=
  gnu_eq_one_iff.mpr ⟨hn, fun S T =>
    (GroupStructure.iso_iff_nonempty_mulEquiv S T).mpr
      (h S.Carrier T.Carrier S.card_carrier T.card_carrier)⟩

/-! ## Submultiplicativity scaffolding (the Lopes A000001 conjecture)

The direct product descends to isomorphism classes, so `gnu i * gnu j ≤ gnu (i * j)`
reduces to injectivity of the descended product map.  Proving that injectivity is the
content of the Lopes conjecture and is *not* attempted here; this lane supplies the
reduction only. -/

/-- `gnu i * gnu j ≤ gnu (i * j)` reduces to injectivity of the descended direct-product
map on isomorphism classes. -/
theorem mul_gnu_le_gnu_of_injective {i j : ℕ}
    (h : Function.Injective fun p : IsoClass i × IsoClass j => IsoClass.prod p.1 p.2) :
    gnu i * gnu j ≤ gnu (i * j) := by
  have key := Fintype.card_le_of_injective _ h
  rwa [Fintype.card_prod] at key

/-! ## Certified values against OEIS A000001

`0, 1, 1, 1, 2, 1, 2, 1, 5, 2, …` at `n = 0, 1, 2, 3, 4, …` (pulled live with
`oeis show A000001`).  See the module docstring for the trust policy and for the
measured kernel-evaluation wall. -/

/-- **`gnu p = 1` for every prime `p`.**  Every group of prime order is cyclic
(`isCyclic_of_prime_card`), and cyclic groups of equal order are isomorphic
(`mulEquivOfCyclicCardEq`).  This certifies A000001 at every prime index at once. -/
theorem gnu_prime {p : ℕ} (hp : p.Prime) : gnu p = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine gnu_eq_one_iff.mpr ⟨hp.one_lt.le, fun S T => ?_⟩
  haveI : IsCyclic S.Carrier := isCyclic_of_prime_card S.natCard_carrier
  haveI : IsCyclic T.Carrier := isCyclic_of_prime_card T.natCard_carrier
  exact (GroupStructure.iso_iff_nonempty_mulEquiv S T).mpr
    ⟨mulEquivOfCyclicCardEq (by rw [S.natCard_carrier, T.natCard_carrier])⟩

/-- **Every group of order four is cyclic or Klein four.**  If some element has order
four the group is cyclic; otherwise every element order divides `2`, so the exponent
divides `2`, and it is not `1` because the group has four elements. -/
theorem isCyclic_or_isKleinFour {G : Type*} [Group G] [Fintype G] (h : Fintype.card G = 4) :
    IsCyclic G ∨ IsKleinFour G := by
  by_cases hex : ∃ a : G, orderOf a = 4
  · obtain ⟨a, ha⟩ := hex
    exact Or.inl (isCyclic_of_orderOf_eq_card a (by rw [Nat.card_eq_fintype_card, h]; exact ha))
  · push Not at hex
    have hsmall : ∀ d, d < 5 → d ∣ 4 → d ≠ 4 → d ∣ 2 := by decide
    have hpow : ∀ a : G, a ^ 2 = 1 := by
      intro a
      have hdvd : orderOf a ∣ 4 := h ▸ orderOf_dvd_card
      have hlt : orderOf a < 5 := Nat.lt_succ_of_le (Nat.le_of_dvd (by norm_num) hdvd)
      exact orderOf_dvd_iff_pow_eq_one.mp (hsmall _ hlt hdvd (hex a))
    have hdvd2 : Monoid.exponent G ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one hpow
    have hne1 : Monoid.exponent G ≠ 1 := by
      rw [Ne, Monoid.exp_eq_one_iff]
      intro hs
      have hle : Fintype.card G ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr hs
      omega
    exact Or.inr ⟨by rw [Nat.card_eq_fintype_card, h],
      (Nat.prime_two.eq_one_or_self_of_dvd _ hdvd2).resolve_left hne1⟩

/-- `2 ≤ gnu 4`, certified by kernel `decide` alone: `C₄` and the Klein four-group have
`2` and `4` solutions of `x² = 1` respectively, so they are non-isomorphic.  No
classification theorem is used. -/
theorem two_le_gnu_four : 2 ≤ gnu 4 :=
  two_le_gnu_of_not_iso (S := GroupStructure.cyclic 4) (T := GroupStructure.klein)
    (GroupStructure.not_iso_of_powOneCount_ne (k := 2) (by decide))

/-- **`gnu 4 = 2`** — A000001 at `n = 4`.  Beyond the kernel-evaluation wall, so the
value is carried by a genuine classification: `GroupCount.isCyclic_or_isKleinFour` gives
exhaustiveness, and the kernel-`decide` invariant of `GroupCount.two_le_gnu_four` gives
irredundancy. -/
theorem gnu_four : gnu 4 = 2 := by
  have hne : ¬ (GroupStructure.cyclic 4).Iso GroupStructure.klein :=
    GroupStructure.not_iso_of_powOneCount_ne (k := 2) (by decide)
  have key : Fintype.card Bool = gnu 4 := by
    refine card_eq_gnu_of_classification
      (fun b => cond b GroupStructure.klein (GroupStructure.cyclic 4)) ?_ ?_
    · intro S
      rcases isCyclic_or_isKleinFour (G := S.Carrier) S.card_carrier with hc | hk
      · refine ⟨false, ?_⟩
        show (GroupStructure.cyclic 4).Iso S
        haveI := hc
        exact (GroupStructure.iso_iff_nonempty_mulEquiv _ S).mpr
          ⟨mulEquivOfCyclicCardEq (by simp)⟩
      · refine ⟨true, ?_⟩
        show GroupStructure.klein.Iso S
        haveI := hk
        exact (GroupStructure.iso_iff_nonempty_mulEquiv _ S).mpr IsKleinFour.nonempty_mulEquiv
    · intro i j hij
      cases i <;> cases j
      · rfl
      · exact absurd hij hne
      · exact absurd hij.symm hne
      · rfl
  rw [← key]
  exact Fintype.card_bool

/-- `gnu 1 = 1` — A000001 at `n = 1`.  Inside the kernel-evaluation wall: proved by
`decide`, with no classification input. -/
theorem gnu_one : gnu 1 = 1 := by decide

/-- `gnu 2 = 1` — A000001 at `n = 2`.  Also inside the kernel wall; see the independent
`decide` cross-check in the ground-truth section below. -/
theorem gnu_two : gnu 2 = 1 := gnu_prime Nat.prime_two

/-- `gnu 3 = 1` — A000001 at `n = 3`.  This is the first value *past* the kernel wall;
only the classification route reaches it. -/
theorem gnu_three : gnu 3 = 1 := gnu_prime Nat.prime_three

/-- `gnu 5 = 1` — A000001 at `n = 5`. -/
theorem gnu_five : gnu 5 = 1 := gnu_prime (by norm_num)

/-- `gnu 7 = 1` — A000001 at `n = 7`. -/
theorem gnu_seven : gnu 7 = 1 := gnu_prime (by norm_num)

/-! ## Ground truth and satisfiability

Checked against `oeis show A000001`, whose terms at `n = 0, 1, 2, …` are
`0, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 5, 1, 2, 1, 14, …`.

Values certified in this file: `gnu 0 = 0`, `gnu 1 = 1`, `gnu 2 = 1`, `gnu 3 = 1`,
`gnu 4 = 2`, `gnu 5 = 1`, `gnu 7 = 1`, and `gnu p = 1` at every prime.  Every remaining
term of A000001 is **omitted**, not asserted: `gnu 6, gnu 8, gnu 9, …` need either an
enumeration past the kernel wall or a classification this file does not carry.  Nothing
here rests on compiled evaluation. -/

section GroundTruth

/-- Both group structures on `Fin 2` (A034383 counts `2` labeled ones) fall into a single
isomorphism class, so the quotient genuinely collapses — `Iso` is not equality. -/
example : Fintype.card (GroupStructure 2) = 2 := by decide

example : gnu 2 = 1 := by decide

example : gnu 0 = 0 := by decide

example : gnu 1 = 1 := by decide

-- `Iso` is not the total relation: the two structures on `Fin 4` are separated by a
-- kernel-decidable invariant (`2` versus `4` solutions of `x² = 1`).
example : (GroupStructure.cyclic 4).powOneCount 2 = 2 := by decide

example : GroupStructure.klein.powOneCount 2 = 4 := by decide

example : ¬ (GroupStructure.cyclic 4).Iso GroupStructure.klein :=
  GroupStructure.not_iso_of_powOneCount_ne (k := 2) (by decide)

-- …and not the empty relation either.
example : (GroupStructure.cyclic 4).Iso (GroupStructure.cyclic 4) := .refl _

-- `card_eq_gnu_of_classification` genuinely applied, both hypotheses discharged,
-- at the nondegenerate `n = 3` (it is also the engine inside `gnu_four`).
example : Fintype.card Unit = gnu 3 :=
  card_eq_gnu_of_classification (fun _ : Unit => GroupStructure.cyclic 3)
    (fun S => ⟨(), (gnu_eq_one_iff.mp gnu_three).2 _ S⟩) (fun _ _ _ => rfl)

-- `card_le_gnu_of_pairwise_not_iso` genuinely applied at `n = 4`.
example : Fintype.card Bool ≤ gnu 4 :=
  card_le_gnu_of_pairwise_not_iso
    (fun b => cond b GroupStructure.klein (GroupStructure.cyclic 4)) (by
      have hne : ¬ (GroupStructure.cyclic 4).Iso GroupStructure.klein :=
        GroupStructure.not_iso_of_powOneCount_ne (k := 2) (by decide)
      rintro (_ | _) (_ | _) h
      · rfl
      · exact absurd h hne
      · exact absurd h.symm hne
      · rfl)

-- `two_le_gnu_of_isEmpty_mulEquiv`: its `IsEmpty` hypothesis needs a genuine
-- non-isomorphism proof — cyclic-vs-Klein at order 4 (vacuity audit).
private theorem isEmpty_mulEquiv_zmod4_klein :
    IsEmpty (Multiplicative (ZMod 4) ≃* Multiplicative (ZMod 2 × ZMod 2)) := by
  refine ⟨fun e => ?_⟩
  haveI : IsCyclic (Multiplicative (ZMod 4)) := inferInstance
  haveI : IsCyclic (Multiplicative (ZMod 2 × ZMod 2)) :=
    isCyclic_of_surjective e.toMonoidHom e.surjective
  exact IsKleinFour.not_isCyclic this

example : 2 ≤ gnu 4 :=
  two_le_gnu_of_isEmpty_mulEquiv (by simp) (by simp) isEmpty_mulEquiv_zmod4_klein

-- `gnu_eq_one_of_forall_mulEquiv` discharged at `n = 2`, using no `gnu` value.
example : gnu 2 = 1 :=
  gnu_eq_one_of_forall_mulEquiv (by omega) fun G H _ _ _ _ hG hH => by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : IsCyclic G := isCyclic_of_prime_card (p := 2)
      (by rw [Nat.card_eq_fintype_card, hG])
    haveI : IsCyclic H := isCyclic_of_prime_card (p := 2)
      (by rw [Nat.card_eq_fintype_card, hH])
    exact ⟨mulEquivOfCyclicCardEq
      (by rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hG, hH])⟩

-- `gnu_eq_one_iff` with both conjuncts discharged at `n = 3`.
example : 1 ≤ 3 ∧ ∀ S T : GroupStructure 3, S.Iso T := gnu_eq_one_iff.mp gnu_three

-- `nonempty_mulEquiv_of_gnu_eq_one` at a concrete pair of groups of order `3`.
example : Nonempty ((GroupStructure.cyclic 3).Carrier ≃* Multiplicative (ZMod 3)) :=
  nonempty_mulEquiv_of_gnu_eq_one gnu_three (GroupStructure.cyclic 3).card_carrier (by simp)

/-- The hypothesis of `mul_gnu_le_gnu_of_injective` is the *open* Lopes injectivity, so it
is exhibited satisfiable rather than proved: at `i = j = 1` the source is a subsingleton,
hence every map out of it is injective. -/
example : Function.Injective fun p : IsoClass 1 × IsoClass 1 => IsoClass.prod p.1 p.2 := by
  haveI : Subsingleton (IsoClass 1) := Fintype.card_le_one_iff_subsingleton.mp gnu_one.le
  exact fun a b _ => Subsingleton.elim a b

example : gnu 1 * gnu 1 ≤ gnu (1 * 1) := by
  haveI : Subsingleton (IsoClass 1) := Fintype.card_le_one_iff_subsingleton.mp gnu_one.le
  exact mul_gnu_le_gnu_of_injective fun a b _ => Subsingleton.elim a b

section NondegenerateWitnesses
open GroupStructure

-- Nondegenerate reduction witness (vacuity audit): at `i = 1, j = 4` the
-- injectivity hypothesis is genuinely proved and the conclusion has content —
-- both sides equal `2`, not the collapsed `1 ≤ 1`.
private theorem prod_iso_cancel_one_left {j : ℕ} (S : GroupStructure 1)
    {T T' : GroupStructure j} (h : (S.prod T).Iso (S.prod T')) : T.Iso T' := by
  haveI hss : Subsingleton S.Carrier :=
    Fintype.card_le_one_iff_subsingleton.mp (by rw [S.card_carrier])
  haveI : Inhabited S.Carrier := ⟨1⟩
  haveI : Unique S.Carrier := Unique.mk' S.Carrier
  obtain ⟨k⟩ := (iso_iff_nonempty_mulEquiv _ _).mp h
  refine iso_of_mulEquiv ?_
  exact (MulEquiv.uniqueProd (N := S.Carrier) (M := T.Carrier)).symm.trans
    (((prodMulEquiv S T).symm.trans (k.trans (prodMulEquiv S T'))).trans
      (MulEquiv.uniqueProd (N := S.Carrier) (M := T'.Carrier)))

private theorem prod_injective_one_left (j : ℕ) :
    Function.Injective fun p : IsoClass 1 × IsoClass j => IsoClass.prod p.1 p.2 := by
  haveI : Subsingleton (IsoClass 1) := Fintype.card_le_one_iff_subsingleton.mp gnu_one.le
  rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ h
  have hfst : a₁ = b₁ := Subsingleton.elim _ _
  subst hfst
  refine Prod.ext rfl ?_
  induction a₁ using Quotient.inductionOn with
  | _ S =>
    induction a₂ using Quotient.inductionOn with
    | _ T =>
      induction b₂ using Quotient.inductionOn with
      | _ T' =>
        exact Quotient.sound (prod_iso_cancel_one_left S (Quotient.exact h))

example : gnu 1 * gnu 4 ≤ gnu (1 * 4) :=
  mul_gnu_le_gnu_of_injective (prod_injective_one_left 4)

-- …and that conclusion has content: both sides are 2, not the degenerate 1 ≤ 1.
example : gnu 1 * gnu 4 = 2 := by rw [gnu_one, gnu_four]
example : gnu (1 * 4) = 2 := gnu_four

-- `prod_iso_prod` at genuinely DISTINCT isomorphic structures (vacuity audit):
-- `swap2` is the other group structure on `Fin 2` (identity element at `1`),
-- provably distinct from `cyclic 2` yet in the same class — the sharpest
-- in-file demonstration that the quotient genuinely collapses (gnu 2 = 1
-- while the labeled count A034383(2) = 2).
private def swap2 : GroupStructure 2 where
  mul a b := a + b + 1
  one := 1
  inv a := a
  mul_assoc := by decide
  one_mul := by decide
  inv_mul_cancel := by decide

example : swap2 ≠ cyclic 2 := by decide
example : (cyclic 2).Iso swap2 := by decide
example : swap2.isoClass = (cyclic 2).isoClass := by decide

example : ((cyclic 2).prod (cyclic 2)).Iso (swap2.prod swap2) :=
  prod_iso_prod (by decide) (by decide)
example : klein.Iso (swap2.prod swap2) := prod_iso_prod (by decide) (by decide)

-- Ground checks for `prodMulEquiv`/`IsoClass.prod` (vacuity audit): the
-- characterizing equation at a concrete point, and the class-level product
-- pinned against `klein` positively and `cyclic 4` negatively.
example (x : klein.Carrier) :
    prodMulEquiv (cyclic 2) (cyclic 2) x =
      (cyclic 2).prodEquiv (cyclic 2) (klein.carrierEquiv x) := rfl

example : IsoClass.prod (cyclic 2).isoClass (cyclic 2).isoClass = klein.isoClass := rfl

example : IsoClass.prod (cyclic 2).isoClass (cyclic 2).isoClass ≠ (cyclic 4).isoClass := by
  rw [← isoClass_prod]
  intro h
  exact not_iso_of_powOneCount_ne (k := 2) (by decide)
    ((isoClass_eq_iff (cyclic 4) klein).mp h.symm)

end NondegenerateWitnesses

end GroundTruth

/-! ## Axiom audit

Every declaration above is `sorry`-free; the sweep below confirms each rests only on
`{propext, Classical.choice, Quot.sound}`.  In particular no `Lean.ofReduceBool`
appears anywhere in this module: there is no `native_decide` in this file. -/

#print axioms GroupStructure.Iso
#print axioms GroupStructure.instDecidableIso
#print axioms GroupStructure.Iso.refl
#print axioms GroupStructure.Iso.symm
#print axioms GroupStructure.Iso.trans
#print axioms GroupStructure.isoSetoid
#print axioms GroupStructure.isoSetoid_r
#print axioms GroupStructure.instDecidableSetoidIso
#print axioms GroupStructure.Carrier
#print axioms GroupStructure.instGroupCarrier
#print axioms GroupStructure.instFintypeCarrier
#print axioms GroupStructure.instDecidableEqCarrier
#print axioms GroupStructure.carrierEquiv
#print axioms GroupStructure.carrierEquiv_mul
#print axioms GroupStructure.carrierEquiv_symm_mul
#print axioms GroupStructure.carrierEquiv_one
#print axioms GroupStructure.carrierEquiv_symm_one
#print axioms GroupStructure.card_carrier
#print axioms GroupStructure.natCard_carrier
#print axioms GroupStructure.isoMulEquiv
#print axioms GroupStructure.iso_of_mulEquiv
#print axioms GroupStructure.iso_iff_nonempty_mulEquiv
#print axioms GroupStructure.ofEquiv
#print axioms GroupStructure.ofEquiv_mul
#print axioms GroupStructure.ofEquivMulEquiv
#print axioms GroupStructure.exists_carrier_mulEquiv
#print axioms GroupStructure.prodEquiv
#print axioms GroupStructure.prod
#print axioms GroupStructure.prodMulEquiv
#print axioms GroupStructure.prod_iso_prod
#print axioms GroupStructure.npow
#print axioms GroupStructure.carrierEquiv_symm_npow
#print axioms GroupStructure.powOneCount
#print axioms GroupStructure.powOneCount_eq_card_pow
#print axioms GroupStructure.powOneCount_eq_of_iso
#print axioms GroupStructure.not_iso_of_powOneCount_ne
#print axioms GroupStructure.klein
#print axioms GroupStructure.isCyclic_carrier_of_generator
#print axioms GroupStructure.pow_eq_one_of_npow_eq_one
#print axioms GroupStructure.cyclic_npow
#print axioms GroupStructure.isCyclic_carrier_cyclic
#print axioms GroupStructure.isKleinFour_klein
#print axioms GroupStructure.isoClass
#print axioms GroupStructure.isoClass_eq_iff
#print axioms GroupStructure.isoClass_surjective
#print axioms GroupStructure.isoClass_prod
#print axioms IsoClass
#print axioms IsoClass.prod
#print axioms gnu
#print axioms gnu_eq_natCard
#print axioms isEmpty_isoClass_iff
#print axioms gnu_eq_zero_iff
#print axioms gnu_zero
#print axioms one_le_gnu
#print axioms gnu_eq_one_iff
#print axioms card_eq_gnu_of_classification
#print axioms card_le_gnu_of_pairwise_not_iso
#print axioms two_le_gnu_of_not_iso
#print axioms two_le_gnu_of_isEmpty_mulEquiv
#print axioms nonempty_mulEquiv_of_gnu_eq_one
#print axioms gnu_eq_one_of_forall_mulEquiv
#print axioms mul_gnu_le_gnu_of_injective
#print axioms gnu_prime
#print axioms isCyclic_or_isKleinFour
#print axioms two_le_gnu_four
#print axioms gnu_four
#print axioms gnu_one
#print axioms gnu_two
#print axioms gnu_three
#print axioms gnu_five
#print axioms gnu_seven

end GroupCount
