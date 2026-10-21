/-
# Counting squares and sums of two squares over a finite field

## Classical source

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number
  Theory*, 2nd ed. (1990), Ch. 8, Prop. 8.1.1 and Sec. 8.3
  (counting `x ^ 2 + y ^ 2 = a` via Jacobi sums).
* R. Lidl and H. Niederreiter, *Finite Fields* (1997), Thm. 6.26.

## Informal statement (verbatim from the target card, 2026-10-21)

Let F be a finite field of odd order q and χ its quadratic character. Then
#{a in F : IsSquare a} = (q+1)/2, and for a ≠ 0,
#{(x,y) in F^2 : x^2 + y^2 = a} = q - χ(-1); for a = 0 the count is
1 + (q-1)(1+χ(-1)).

## Formal conventions

* "Odd order" is expressed as `ringChar F ≠ 2`, the hypothesis used by
  Mathlib's `quadraticChar` API (for a finite field this is equivalent to
  `Fintype.card F` odd).
* χ is Mathlib's `quadraticChar F : MulChar F ℤ`, with χ(0) = 0.
* Counts are `Finset.card` of filters of `Finset.univ`; the point counts are
  cast to `ℤ` before subtracting, since `χ(-1) ∈ {±1}`.
* The Nat division `(q + 1) / 2` is exact because `q` is odd; the companion
  statement `2 * #squares = q + 1` is also recorded.

## Mathlib absence check (2026-10-21)

`leandoc` for "card squares finite field", "card isSquare finite field half",
"number of solutions x^2 + y^2 = a finite field" and a grep for
`card_sq|sq_add_sq` in `NumberTheory/LegendreSymbol` and `FieldTheory/Finite`
find only `quadraticChar_card_sqrts`, `quadraticChar_sum_zero`,
`ZMod.sq_add_sq` (existence only) and the Jacobi sum API
(`jacobiSum_nontrivial_inv`), none of which state these counts.
-/
import Mathlib

set_option autoImplicit false

namespace FiniteFieldTwoSquares

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Pointwise identity behind the square count: for every `a`,
`2·[a is a square] = 1 + χ(a) + [a = 0]`. -/
lemma two_mul_indicator_isSquare (a : F) :
    2 * (if IsSquare a then (1 : ℤ) else 0) =
      1 + quadraticChar F a + (if a = 0 then 1 else 0) := by
  by_cases h₀ : a = 0
  · subst h₀
    simp
  · by_cases hs : IsSquare a
    · rw [if_pos hs, (quadraticChar_one_iff_isSquare h₀).mpr hs, if_neg h₀]
      norm_num
    · rw [if_neg hs, quadraticChar_neg_one_iff_not_isSquare.mpr hs, if_neg h₀]
      norm_num

/-- Doubled form of the square count: in a finite field of odd
characteristic, `2 · #{a | IsSquare a} = q + 1`. -/
theorem two_mul_card_isSquare (hF : ringChar F ≠ 2) :
    2 * #{a : F | IsSquare a} = Fintype.card F + 1 := by
  have hZ : (2 * #{a : F | IsSquare a} : ℤ) = Fintype.card F + 1 := by
    rw [Finset.natCast_card_filter, Finset.mul_sum]
    simp_rw [two_mul_indicator_isSquare]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, quadraticChar_sum_zero hF]
    simp
  exact_mod_cast hZ

/-- **Square count.** In a finite field `F` of odd order `q`, exactly
`(q + 1) / 2` elements are squares (zero included). -/
theorem card_isSquare (hF : ringChar F ≠ 2) :
    #{a : F | IsSquare a} = (Fintype.card F + 1) / 2 := by
  have h := two_mul_card_isSquare hF
  omega

/-- Summing a function of `x ^ 2` over `F` equals summing it against the
number of square roots `1 + χ(u)` of each `u`. -/
lemma sum_comp_sq (hF : ringChar F ≠ 2) (f : F → ℤ) :
    ∑ x : F, f (x ^ 2) = ∑ u : F, (1 + quadraticChar F u) * f u := by
  rw [← Finset.sum_fiberwise' univ (fun x : F => x ^ 2) f]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul, add_comm, ← quadraticChar_card_sqrts hF u,
    Set.toFinset_ofPred]

/-- The point count `N(a) = #{(x, y) | x² + y² = a}` equals
`q + ∑ₓ χ(a - x²)`. -/
lemma card_sq_add_sq_eq_sum (hF : ringChar F ≠ 2) (a : F) :
    (#{p : F × F | p.1 ^ 2 + p.2 ^ 2 = a} : ℤ) =
      Fintype.card F + ∑ x : F, quadraticChar F (a - x ^ 2) := by
  rw [Finset.natCast_card_filter, Fintype.sum_prod_type]
  have hx : ∀ x : F, (∑ y : F, if x ^ 2 + y ^ 2 = a then (1 : ℤ) else 0) =
      1 + quadraticChar F (a - x ^ 2) := by
    intro x
    rw [← Finset.natCast_card_filter, add_comm, ← quadraticChar_card_sqrts hF,
      Set.toFinset_ofPred]
    congr 2
    ext y
    simp only [mem_filter, mem_univ, true_and]
    constructor <;> intro h <;> linear_combination h
  simp_rw [hx]
  rw [Finset.sum_add_distrib]
  simp

/-- The quadratic character sums to zero along `u ↦ a - u`. -/
lemma sum_quadraticChar_sub (hF : ringChar F ≠ 2) (a : F) :
    ∑ u : F, quadraticChar F (a - u) = 0 :=
  ((Equiv.subLeft a).sum_comp (fun v => quadraticChar F v)).trans
    (quadraticChar_sum_zero hF)

/-- Reduction to a Jacobi-type sum: `∑ₓ χ(a - x²) = ∑ᵤ χ(u) χ(a - u)`. -/
lemma sum_quadraticChar_sub_sq (hF : ringChar F ≠ 2) (a : F) :
    ∑ x : F, quadraticChar F (a - x ^ 2) =
      ∑ u : F, quadraticChar F u * quadraticChar F (a - u) := by
  rw [sum_comp_sq hF (fun u => quadraticChar F (a - u))]
  simp_rw [add_mul, one_mul]
  rw [Finset.sum_add_distrib, sum_quadraticChar_sub hF a, zero_add]

/-- For `a ≠ 0`, the Jacobi-type sum `∑ᵤ χ(u) χ(a - u)` equals `-χ(-1)`
(rescale `u = a t` and apply `J(χ, χ⁻¹) = -χ(-1)` with `χ⁻¹ = χ`). -/
lemma sum_mul_sub_of_ne_zero (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    ∑ u : F, quadraticChar F u * quadraticChar F (a - u) = -quadraticChar F (-1) := by
  rw [← Equiv.sum_comp (Equiv.mulLeft₀ a ha)]
  have hpt : ∀ t : F, quadraticChar F ((Equiv.mulLeft₀ a ha) t) *
      quadraticChar F (a - (Equiv.mulLeft₀ a ha) t) =
      quadraticChar F t * (quadraticChar F)⁻¹ (1 - t) := by
    intro t
    rw [(quadraticChar_isQuadratic F).inv, Equiv.mulLeft₀_apply]
    have hfac : a - a * t = a * (1 - t) := by ring
    rw [hfac, map_mul, map_mul]
    linear_combination (quadraticChar F t * quadraticChar F (1 - t)) * quadraticChar_sq_one ha
  simp_rw [hpt]
  exact jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)

/-- At `a = 0`, the sum `∑ᵤ χ(u) χ(-u)` equals `χ(-1) (q - 1)`. -/
lemma sum_mul_zero_sub :
    ∑ u : F, quadraticChar F u * quadraticChar F (0 - u) =
      quadraticChar F (-1) * (Fintype.card F - 1) := by
  have hpt : ∀ u : F, quadraticChar F u * quadraticChar F (0 - u) =
      quadraticChar F (-1) * (1 - if u = 0 then 1 else 0) := by
    intro u
    by_cases hu : u = 0
    · subst hu
      simp
    · rw [if_neg hu, zero_sub, neg_eq_neg_one_mul, map_mul]
      linear_combination (quadraticChar F (-1)) * quadraticChar_sq_one hu
  simp_rw [hpt]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp

/-- **Sums of two squares, `a ≠ 0`.** In a finite field `F` of odd order `q`
with quadratic character `χ`, for `a ≠ 0` the equation `x² + y² = a` has
exactly `q - χ(-1)` solutions `(x, y) ∈ F²`. -/
theorem card_sq_add_sq_of_ne_zero (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    (#{p : F × F | p.1 ^ 2 + p.2 ^ 2 = a} : ℤ) =
      Fintype.card F - quadraticChar F (-1) := by
  rw [card_sq_add_sq_eq_sum hF, sum_quadraticChar_sub_sq hF, sum_mul_sub_of_ne_zero hF ha,
    sub_eq_add_neg]

/-- **Sums of two squares, `a = 0`.** In a finite field `F` of odd order `q`
with quadratic character `χ`, the equation `x² + y² = 0` has exactly
`1 + (q - 1)(1 + χ(-1))` solutions `(x, y) ∈ F²`. -/
theorem card_sq_add_sq_zero (hF : ringChar F ≠ 2) :
    (#{p : F × F | p.1 ^ 2 + p.2 ^ 2 = 0} : ℤ) =
      1 + (Fintype.card F - 1) * (1 + quadraticChar F (-1)) := by
  rw [card_sq_add_sq_eq_sum hF, sum_quadraticChar_sub_sq hF, sum_mul_zero_sub]
  ring

/-! ## Non-vacuity and ground-truth checks -/

/-- The hypothesis `ringChar F ≠ 2` is satisfiable: `ZMod 5`. -/
example : ringChar (ZMod 5) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  decide

/-- Direct count over `ZMod 5`: three squares `{0, 1, 4} = (5 + 1) / 2`. -/
example : #{a : ZMod 5 | ∃ r : ZMod 5, a = r * r} = 3 := by decide

/-- Direct count over `ZMod 5` (`-1 = 4` is a square, `χ(-1) = 1`):
`x² + y² = 1` has `5 - 1 = 4` solutions. -/
example : #{p : ZMod 5 × ZMod 5 | p.1 ^ 2 + p.2 ^ 2 = 1} = 4 := by decide

/-- Direct count over `ZMod 5`: `x² + y² = 0` has `1 + 4 · 2 = 9` solutions. -/
example : #{p : ZMod 5 × ZMod 5 | p.1 ^ 2 + p.2 ^ 2 = 0} = 9 := by decide

/-- Direct count over `ZMod 3` (`-1` is a nonsquare, `χ(-1) = -1`):
`x² + y² = 0` has only the trivial solution and `x² + y² = 1` has `3 + 1 = 4`. -/
example : #{p : ZMod 3 × ZMod 3 | p.1 ^ 2 + p.2 ^ 2 = 0} = 1 ∧
    #{p : ZMod 3 × ZMod 3 | p.1 ^ 2 + p.2 ^ 2 = 1} = 4 := by decide

end FiniteFieldTwoSquares
