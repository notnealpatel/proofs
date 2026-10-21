/-
# McKay's counting form of Cauchy's theorem

## Classical source (recorded 2026-10-21)

* J. H. McKay, "Another proof of Cauchy's group theorem",
  Amer. Math. Monthly 66 (1959), p. 119.  The rotation action of the cyclic
  group of order `p` on `{(x₁, …, x_p) ∈ Gᵖ : x₁ ⋯ x_p = 1}` is used there; the
  orbit count gives the congruence below.
* Special case `n = p` of G. Frobenius (1895), "Verallgemeinerung des
  Sylow'schen Satzes", Berliner Sitzungsberichte: for `n ∣ |G|` the number of
  solutions of `xⁿ = 1` in `G` is a multiple of `n`.

## Informal statement (verbatim from the target card)

```
If G is a finite group and p is a prime dividing |G|, then p divides
#{x in G : x^p = 1}; equivalently the number of elements of order p is
≡ -1 (mod p).
```

## Mathlib absence check

`Mathlib/GroupTheory/Perm/Cycle/Type.lean` (section `Cauchy`) has
`Equiv.Perm.vectorsProdEqOne`, its cardinality `|G|^(n-1)`, the rotation, and
`exists_prime_orderOf_dvd_card` (existence only).  `OrderOfElement.lean` has
`sum_card_orderOf_eq_card_pow_eq_one`.  No counting statement
`p ∣ #{x | x ^ p = 1}` was found by `leandoc` or `grep` (2026-10-21).

## Formal conventions

* Counts are `Nat.card` of subtypes of a `[Finite G]` group; the hypothesis is
  `p ∣ Nat.card G`.
* "`≡ -1 (mod p)`" is stated without subtraction as
  `p ∣ Nat.card {x : G // orderOf x = p} + 1`.
-/
import Mathlib

set_option autoImplicit false

namespace GroupCount.McKayPowerSolutions

open Equiv Equiv.Perm

variable {G : Type*} [Group G]

/-- The rotation `(x₁, x₂, …, x_p) ↦ (x₂, …, x_p, x₁)` as a permutation of the
vectors of length `p` (prime) with product `1`. -/
def rotatePerm (p : ℕ) [hp : Fact p.Prime] : Perm (vectorsProdEqOne G p) where
  toFun v := VectorsProdEqOne.rotate v 1
  invFun v := VectorsProdEqOne.rotate v (p - 1)
  left_inv v := by
    simp only [VectorsProdEqOne.rotate_rotate]
    rw [add_tsub_cancel_of_le hp.out.one_lt.le, VectorsProdEqOne.rotate_length]
  right_inv v := by
    simp only [VectorsProdEqOne.rotate_rotate]
    rw [tsub_add_cancel_of_le hp.out.one_lt.le, VectorsProdEqOne.rotate_length]

/-- Iterating the rotation `k` times rotates by `k`. -/
theorem rotatePerm_pow_apply (p : ℕ) [Fact p.Prime] (k : ℕ) (v : vectorsProdEqOne G p) :
    (rotatePerm p ^ k) v = VectorsProdEqOne.rotate v k := by
  induction k generalizing v with
  | zero => exact (VectorsProdEqOne.rotate_zero v).symm
  | succ k ih =>
    rw [pow_succ, Perm.mul_apply, ih]
    show VectorsProdEqOne.rotate (VectorsProdEqOne.rotate v 1) k = _
    rw [VectorsProdEqOne.rotate_rotate, Nat.add_comm]

/-- The rotation has order dividing `p`: `rotatePerm p ^ p ^ 1 = 1`. -/
theorem rotatePerm_pow_prime (p : ℕ) [Fact p.Prime] :
    (rotatePerm p : Perm (vectorsProdEqOne G p)) ^ p ^ 1 = 1 := by
  ext1 v
  rw [pow_one, rotatePerm_pow_apply, VectorsProdEqOne.rotate_length, Perm.one_apply]

/-- The rotation acts on the underlying list as `List.rotate · 1`. -/
theorem rotatePerm_apply_val (p : ℕ) [Fact p.Prime] (v : vectorsProdEqOne G p) :
    (rotatePerm p v).1.1 = v.1.1.rotate 1 :=
  rfl

/-- A product-one vector is fixed by the rotation iff it is constant. -/
theorem rotatePerm_apply_eq_self_iff (p : ℕ) [Fact p.Prime] (v : vectorsProdEqOne G p) :
    rotatePerm p v = v ↔ ∃ x : G, v.1.1 = List.replicate p x := by
  have hlen : v.1.1.length = p := v.1.2
  constructor
  · intro h
    have h' : v.1.1.rotate 1 = v.1.1 := congrArg (fun w : vectorsProdEqOne G p => w.1.1) h
    obtain ⟨a, ha⟩ := List.rotate_one_eq_self_iff_eq_replicate.mp h'
    rw [hlen] at ha
    exact ⟨a, ha⟩
  · rintro ⟨x, hx⟩
    apply Subtype.ext
    apply Subtype.ext
    show v.1.1.rotate 1 = v.1.1
    rw [hx, List.rotate_replicate]

/-- The constant vector `(x, …, x)` of length `p`, for `x ^ p = 1`; its product is `x ^ p = 1`. -/
def constVec (p : ℕ) (x : {x : G // x ^ p = 1}) : vectorsProdEqOne G p :=
  ⟨List.Vector.replicate p x.1, by
    rw [VectorsProdEqOne.mem_iff]
    show (List.replicate p x.1).prod = 1
    rw [List.prod_replicate, x.2]⟩

/-- The fixed points of the rotation are the constant vectors `(x, …, x)` with
`x ^ p = 1`; they are in bijection with `{x : G // x ^ p = 1}`. -/
theorem card_fixed_rotatePerm (p : ℕ) [hp : Fact p.Prime] [Fintype G] [DecidableEq G] :
    Fintype.card {v : vectorsProdEqOne G p // rotatePerm p v = v} =
      Fintype.card {x : G // x ^ p = 1} := by
  symm
  let f : {x : G // x ^ p = 1} → {v : vectorsProdEqOne G p // rotatePerm p v = v} :=
    fun x => ⟨constVec p x, (rotatePerm_apply_eq_self_iff p _).mpr ⟨x.1, rfl⟩⟩
  refine Fintype.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · intro x y hxy
    have h : List.replicate p x.1 = List.replicate p y.1 :=
      congrArg (fun w : {v : vectorsProdEqOne G p // rotatePerm p v = v} => w.1.1.1) hxy
    exact Subtype.ext ((List.replicate_right_inj hp.out.ne_zero).mp h)
  · rintro ⟨v, hv⟩
    obtain ⟨x, hx⟩ := (rotatePerm_apply_eq_self_iff p v).mp hv
    have hxp : x ^ p = 1 := by
      rw [← List.prod_replicate, ← hx]
      exact v.2
    refine ⟨⟨x, hxp⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact hx.symm

/-- McKay's congruence: `|G| ^ (p - 1) ≡ #{x : G | x ^ p = 1} (mod p)`. -/
theorem card_pow_eq_one_modEq (p : ℕ) [Fact p.Prime] [Fintype G] [DecidableEq G] :
    Fintype.card {x : G // x ^ p = 1} ≡ Fintype.card G ^ (p - 1) [MOD p] := by
  have hcompl := card_compl_support_modEq (rotatePerm_pow_prime (G := G) p)
  rw [VectorsProdEqOne.card] at hcompl
  have hsupp : (rotatePerm p : Perm (vectorsProdEqOne G p)).supportᶜ.card =
      Fintype.card {v : vectorsProdEqOne G p // rotatePerm p v = v} := by
    rw [Fintype.card_subtype]
    congr 1
    ext v
    simp
  rw [← card_fixed_rotatePerm, ← hsupp]
  exact hcompl

/-- **McKay (1959).** If `G` is a finite group and `p` is a prime dividing `|G|`, then `p`
divides the number of solutions of `x ^ p = 1` in `G`. -/
theorem prime_dvd_card_pow_eq_one [Finite G] (p : ℕ) [hp : Fact p.Prime]
    (hdvd : p ∣ Nat.card G) : p ∣ Nat.card {x : G // x ^ p = 1} := by
  classical
  have := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card] at hdvd ⊢
  have hpow : p ∣ Fintype.card G ^ (p - 1) :=
    dvd_pow hdvd (Nat.sub_ne_zero_of_lt hp.out.one_lt)
  exact Nat.modEq_zero_iff_dvd.mp
    ((card_pow_eq_one_modEq p).trans (Nat.modEq_zero_iff_dvd.mpr hpow))

/-- Splitting off the identity: the solutions of `x ^ p = 1` are `1` together with the
elements of order exactly `p`. -/
theorem card_pow_eq_one_eq_card_orderOf_add_one [Finite G] (p : ℕ) [Fact p.Prime] :
    Nat.card {x : G // x ^ p = 1} = Nat.card {x : G // orderOf x = p} + 1 := by
  classical
  have := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_subtype]
  have herase : (Finset.univ.filter fun x : G => x ^ p = 1).erase 1 =
      Finset.univ.filter fun x : G => orderOf x = p := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and,
      orderOf_eq_prime_iff]
    exact and_comm
  rw [← herase, Finset.card_erase_add_one]
  simp

/-- **Cauchy–McKay count.** If `G` is a finite group and `p` is a prime dividing `|G|`, the
number of elements of order `p` is `≡ -1 (mod p)`, stated as
`p ∣ #{x : G | orderOf x = p} + 1`. -/
theorem prime_dvd_card_orderOf_eq_prime_add_one [Finite G] (p : ℕ) [Fact p.Prime]
    (hdvd : p ∣ Nat.card G) : p ∣ Nat.card {x : G // orderOf x = p} + 1 := by
  rw [← card_pow_eq_one_eq_card_orderOf_add_one]
  exact prime_dvd_card_pow_eq_one p hdvd

/-! ## Ground truth and non-vacuity -/

/-- Non-vacuity: the hypotheses hold jointly for `G = ℤ/6` (multiplicatively), `p = 3`. -/
example : Fact (Nat.Prime 3) ∧ 3 ∣ Nat.card (Multiplicative (ZMod 6)) :=
  ⟨⟨by norm_num⟩, by rw [Nat.card_eq_fintype_card]; decide⟩

/-- Ground truth: in `ℤ/6` exactly three elements satisfy `3 • x = 0`. -/
example : Fintype.card {x : Multiplicative (ZMod 6) // x ^ 3 = 1} = 3 := by decide

/-- Ground truth: in `ℤ/6` exactly two elements have order `3` (and `3 ∣ 2 + 1`). -/
example : Nat.card {x : Multiplicative (ZMod 6) // orderOf x = 3} = 2 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hsplit := card_pow_eq_one_eq_card_orderOf_add_one (G := Multiplicative (ZMod 6)) 3
  have hthree : Nat.card {x : Multiplicative (ZMod 6) // x ^ 3 = 1} = 3 := by
    rw [Nat.card_eq_fintype_card]
    decide
  omega

end GroupCount.McKayPowerSolutions
