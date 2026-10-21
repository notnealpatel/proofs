/-
# Order of `SL_n(F_q)`

## Source (classical; recorded 2026-10-21)

Standard textbook fact, e.g. R. A. Wilson, *The Finite Simple Groups*
(Springer GTM 251, 2009), Sec. 3.3.1; J. J. Rotman, *An Introduction to the
Theory of Groups* (4th ed., Springer GTM 148, 1995), Ch. 8 (the orders of
`GL(n, q)` and `SL(n, q)`).

Informal statement (verbatim from the target spec):

```
For a finite field K with q elements,
|SL_n(K)| = |GL_n(K)|/(q-1) = q^{n(n-1)/2} · prod_{i=2}^{n} (q^i - 1)   (n >= 1).
```

## Mathlib absence check (re-done 2026-10-21)

`leandoc` / `grep` over Mathlib: `Matrix.card_GL_field` (the `GL` order, in
`Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Card.lean`) exists; no
cardinality statement for `Matrix.SpecialLinearGroup` exists (the only `card`
hits in the `SpecialLinearGroup` files concern the index type, the center, and
`PSL₂` generation).

## Formalization choices

* Objects are Mathlib's own: `Matrix.SpecialLinearGroup (Fin n) K`,
  `GL (Fin n) K`, `Nat.card`, and `q = Fintype.card K`.
* The exponent `n(n-1)/2` is written `n.choose 2`; Mathlib's
  `Nat.choose_two_right : n.choose 2 = n * (n - 1) / 2` identifies them, and
  `n.choose 2` avoids the truncated `Nat` subtraction and division.
* The closed form `card_SL_field` holds for every `n` (at `n = 0` both sides are
  `1`), so it carries no hypothesis.  The quotient forms involving `q - 1`
  need `n ≠ 0` (at `n = 0`, `|GL| = |SL| = 1` while `q - 1` may exceed `1`),
  matching the source's `n ≥ 1`.
* `q - 1` and `q ^ n - q ^ i` (with `i < n`) are true differences, since a
  finite field has `2 ≤ q`.

No new definitions are introduced.
-/
import Mathlib

set_option autoImplicit false

namespace GroupTPP.SpecialLinearOrder

open Matrix

variable {K : Type*} [Field K] [Fintype K]

omit [Fintype K] in
/-- The kernel of the determinant `GL_n(K) → Kˣ` is the image of `SL_n(K)` under the
canonical embedding `Matrix.SpecialLinearGroup.toGL`. -/
theorem ker_det_eq_range_toGL (n : ℕ) :
    (GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker = SpecialLinearGroup.toGL.range := by
  ext A
  constructor
  · intro hA
    have hdet : (A : Matrix (Fin n) (Fin n) K).det = 1 := by
      simpa using congrArg Units.val (MonoidHom.mem_ker.mp hA)
    exact ⟨⟨A.1, hdet⟩, Units.ext rfl⟩
  · rintro ⟨B, rfl⟩
    rw [MonoidHom.mem_ker]
    ext
    simp [SpecialLinearGroup.coeToGL_det]

/-- Lagrange for the determinant: `|SL_n(K)| · (q - 1) = |GL_n(K)|` for `n ≥ 1`,
where `q = |K|`. -/
theorem card_SL_mul_card_sub_one_eq_card_GL (n : ℕ) [NeZero n] :
    Nat.card (SpecialLinearGroup (Fin n) K) * (Fintype.card K - 1) =
      Nat.card (GL (Fin n) K) := by
  have hSL : Nat.card (SpecialLinearGroup (Fin n) K) =
      Nat.card (GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker := by
    rw [ker_det_eq_range_toGL]
    exact Nat.card_congr (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective).toEquiv
  have hunits : Nat.card Kˣ = Fintype.card K - 1 := by
    classical
    rw [Nat.card_eq_fintype_card, Fintype.card_units]
  have hquot : Nat.card (GL (Fin n) K ⧸ (GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker) =
      Nat.card Kˣ :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      GeneralLinearGroup.det_surjective).toEquiv
  rw [hSL, ← hunits, ← hquot, mul_comm, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]

/-- The `SL` order in the product form of the target spec: for `n ≥ 1`,
`|SL_n(K)| · (q - 1) = ∏_{i < n} (q^n - q^i)`. -/
theorem card_SL_field_mul_sub_one (n : ℕ) [NeZero n] :
    Nat.card (SpecialLinearGroup (Fin n) K) * (Fintype.card K - 1) =
      ∏ i : Fin n, (Fintype.card K ^ n - Fintype.card K ^ (i : ℕ)) := by
  rw [card_SL_mul_card_sub_one_eq_card_GL, card_GL_field]

/-- Closed form of the `GL` product: for all naturals `q, n`,
`∏_{i < n} (q^n - q^i) = q^(n choose 2) · ∏_{j=1}^{n} (q^j - 1)`. -/
theorem prod_pow_sub_pow_eq (q n : ℕ) :
    ∏ i : Fin n, (q ^ n - q ^ (i : ℕ)) =
      q ^ n.choose 2 * ∏ j ∈ Finset.Icc 1 n, (q ^ j - 1) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => q ^ n - q ^ i)]
  have hfac : ∀ i ∈ Finset.range n, q ^ n - q ^ i = q ^ i * (q ^ (n - 1 - i) * q - 1) := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    rw [Nat.mul_sub, mul_one, ← mul_assoc, ← pow_add, ← pow_succ]
    congr 2
    omega
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.sum_range_id, ← Nat.choose_two_right]
  congr 1
  rw [Finset.prod_range_reflect (fun i => q ^ i * q - 1) n]
  simp_rw [← pow_succ]
  rw [Finset.range_eq_Ico, Finset.prod_Ico_add' (fun j => q ^ j - 1) 0 n 1, zero_add,
    Finset.Ico_add_one_right_eq_Icc]

omit [Fintype K] in
/-- The special linear group over a field, indexed by `Fin 0`, is trivial. -/
theorem card_SL_fin_zero : Nat.card (SpecialLinearGroup (Fin 0) K) = 1 := by
  have hsub : Subsingleton (SpecialLinearGroup (Fin 0) K) :=
    ⟨fun A B => Subtype.ext (Subsingleton.elim A.1 B.1)⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩

/-- **Order of `SL_n(F_q)`.** For a finite field `K` with `q` elements and every `n`,
`|SL_n(K)| = q^(n(n-1)/2) · ∏_{i=2}^{n} (q^i - 1)` (the exponent is written `n.choose 2`,
equal to `n * (n - 1) / 2` by `Nat.choose_two_right`). -/
theorem card_SL_field (n : ℕ) :
    Nat.card (SpecialLinearGroup (Fin n) K) =
      Fintype.card K ^ n.choose 2 * ∏ i ∈ Finset.Icc 2 n, (Fintype.card K ^ i - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [card_SL_fin_zero]
    simp
  · haveI : NeZero n := ⟨hn.ne'⟩
    have hq2 : 1 < Fintype.card K := Fintype.one_lt_card
    have hsplit : ∏ j ∈ Finset.Icc 1 n, (Fintype.card K ^ j - 1) =
        (Fintype.card K - 1) * ∏ j ∈ Finset.Icc 2 n, (Fintype.card K ^ j - 1) := by
      rw [← Finset.insert_Icc_add_one_left_eq_Icc (Nat.one_le_iff_ne_zero.mpr hn.ne'),
        Finset.prod_insert (by simp), pow_one]
      rfl
    have hmul : Nat.card (SpecialLinearGroup (Fin n) K) * (Fintype.card K - 1) =
        (Fintype.card K ^ n.choose 2 * ∏ i ∈ Finset.Icc 2 n, (Fintype.card K ^ i - 1)) *
          (Fintype.card K - 1) := by
      rw [card_SL_field_mul_sub_one, prod_pow_sub_pow_eq, hsplit]
      ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hq2) hmul

/-- The quotient form of the source: for `n ≥ 1`, `|SL_n(K)| = |GL_n(K)| / (q - 1)`
(the natural-number division is exact by `card_SL_mul_card_sub_one_eq_card_GL`). -/
theorem card_SL_eq_card_GL_div (n : ℕ) [NeZero n] :
    Nat.card (SpecialLinearGroup (Fin n) K) = Nat.card (GL (Fin n) K) / (Fintype.card K - 1) := by
  have hq2 : 1 < Fintype.card K := Fintype.one_lt_card
  rw [← card_SL_mul_card_sub_one_eq_card_GL, Nat.mul_div_cancel _ (Nat.sub_pos_of_lt hq2)]

/-! ## Ground-truth checks

Hypotheses are jointly satisfiable at concrete fields; the values agree with the
classical orders `|SL_2(F_2)| = 6`, `|SL_2(F_3)| = 24`, `|SL_3(F_2)| = 168`. -/

example : Nat.card (SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
  rw [card_SL_field, ZMod.card]
  decide

example : Nat.card (SpecialLinearGroup (Fin 2) (ZMod 3)) = 24 := by
  rw [card_SL_field, ZMod.card]
  decide

example : Nat.card (SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [card_SL_field, ZMod.card]
  decide

example : Nat.card (SpecialLinearGroup (Fin 2) (ZMod 3)) * (Fintype.card (ZMod 3) - 1) =
    Nat.card (GL (Fin 2) (ZMod 3)) :=
  card_SL_mul_card_sub_one_eq_card_GL 2

end GroupTPP.SpecialLinearOrder
