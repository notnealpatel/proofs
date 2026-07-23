import Mathlib
import Xlib.TotalDegreeAeval
import Xlib.ShearCircuit

/-!
# Reversible modular inversion needs `⌈log₂ (q − 2)⌉` multiply-add shears

Flagship lower bound for the shear-circuit model of `Xlib.ShearCircuit`.

Over a finite field `K` with `q` elements, the inverse function (with the
`0⁻¹ = 0` convention) is the polynomial function `x ↦ x ^ (q - 2)`, and *no
polynomial of degree `< q - 2` computes it* (`card_sub_two_le_natDegree`):
a lower-degree interpolant would disagree with `X ^ (q - 2)` somewhere, since
their difference has fewer than `q` roots.

A shear circuit with `s` multiply-add gates has every register of total
degree `≤ 2 ^ s` (`Circuit.totalDegree_polys_le`), and restricting the input
register to a single line keeps that bound
(`Xlib.TotalDegreeAeval.natDegree_aeval_le`). Combining:

* `card_sub_two_le_two_pow_shearCount` — a circuit computing `x⁻¹` from
  `(x, 0, …, 0)` satisfies `q - 2 ≤ 2 ^ s`;
* `clog_le_shearCount` — equivalently `s ≥ ⌈log₂ (q - 2)⌉`;
* `secp256k1_inversion_needs_256_shears` — for the secp256k1 base field
  (`p = 2^256 - 2^32 - 977`), at least `256` shears.

This is the folklore addition-chain-style floor, transplanted to the
reversible multiply-add model: it explains why reversible (and quantum)
elliptic-curve arithmetic is dominated by modular inversions — each one costs
a `Θ(log p)`-deep cascade of nonlinear gates, whereas every other step of the
affine group law is a bounded number of shears (`Xlib.ShearAddition`).

The bound needs **no** reversibility or invertibility assumption on the
affine layers, so it holds a fortiori for the reversible subclass.

## References

The core mathematics is classical: the degree-doubling bound for
multiplication gates is Strassen's degree-bound circle of ideas, and the
`⌊log₂ n⌋` floor for `x ↦ xⁿ` is the trivial addition-chain lower bound. No
prior statement (or formalization) of the bound for the reversible
affine-plus-multiply-add gate set is known; the quantum-EC literature gives
only upper bounds/resource estimates.

* V. Strassen, *Die Berechnungskomplexität von elementarsymmetrischen
  Funktionen und von Interpolationskoeffizienten*, Numer. Math. 20 (1973),
  238–251 — Ω(log r) product gates for `x^r` (degree bound).
* A. Shpilka, A. Yehudayoff, *Arithmetic circuits: a survey*, Found. Trends
  Theor. Comput. Sci. 5 (2010), Theorem 3.2 and Remark 3.1.
* D. E. Knuth, *TAOCP* vol. 2, §4.6.3 — addition chains (OEIS A003313);
  Itoh–Tsujii inversion realizes the matching `O(log q)` upper bound.
* M. Roetteler, M. Naehrig, K. Svore, K. Lauter, *Quantum resource estimates
  for computing elliptic curve discrete logarithms*, ASIACRYPT 2017.
* T. Häner, S. Jaques, M. Naehrig, M. Roetteler, M. Soeken, *Improved quantum
  circuits for elliptic curve discrete logarithms*, PQCrypto 2020.
-/

namespace Xlib.ShearInversionLB

open Xlib.ShearCircuit Xlib.ShearCircuit.Circuit

variable {K : Type*} [Field K] [Fintype K]

section OneVariable

open Polynomial

/-- **Inversion has algebraic degree `q − 2`.** Any one-variable polynomial
computing the field inverse (with `0⁻¹ = 0`) on all of a finite field `K`
has `natDegree ≥ |K| - 2`. -/
theorem card_sub_two_le_natDegree (g : Polynomial K)
    (hg : ∀ x : K, g.eval x = x⁻¹) :
    Fintype.card K - 2 ≤ g.natDegree := by
  rcases le_or_gt (Fintype.card K - 2) g.natDegree with h | h
  · exact h
  exfalso
  set q := Fintype.card K with hq
  have hq3 : 3 ≤ q := by omega
  have heval : ∀ x : K, (X ^ (q - 2) - g).eval x = 0 := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp [hg, zero_pow (show q - 2 ≠ 0 by omega)]
    · have h1 : x * x ^ (q - 2) = 1 := by
        rw [← pow_succ', show q - 2 + 1 = q - 1 by omega]
        exact FiniteField.pow_card_sub_one_eq_one x hx
      simp only [eval_sub, eval_pow, eval_X, hg, sub_eq_zero]
      exact (inv_eq_of_mul_eq_one_right h1).symm
  have hlt : g.natDegree < (X ^ (q - 2) : Polynomial K).natDegree := by
    rwa [natDegree_X_pow]
  have hdeg : (X ^ (q - 2) - g).natDegree = q - 2 := by
    rw [natDegree_sub_eq_left_of_natDegree_lt hlt, natDegree_X_pow]
  have h0 : (X ^ (q - 2) - g : Polynomial K) = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _
      Function.injective_id (fun x => heval x) (by rw [hdeg]; omega)
  have hXg : g = X ^ (q - 2) := (sub_eq_zero.mp h0).symm
  rw [hXg, natDegree_X_pow] at h
  omega

end OneVariable

section Circuit

open MvPolynomial

/-- **The flagship bound.** If a shear circuit, run on the register file
`(x, 0, …, 0)` (input `x` in register `inp`, all other registers zeroed),
outputs `x⁻¹` in register `out` for every `x : K`, then

  `|K| - 2 ≤ 2 ^ (number of shear gates)`.

Clean reversible modular inversion is exponentially expensive in shear depth:
the multiply-add cascade must double degree `⌈log₂ (|K| - 2)⌉` times. -/
theorem card_sub_two_le_two_pow_shearCount {n : ℕ} (C : Circuit n K)
    (inp out : Fin n)
    (hspec : ∀ x : K, run C (fun i => if i = inp then x else 0) out = x⁻¹) :
    Fintype.card K - 2 ≤ 2 ^ shearCount C := by
  classical
  set g : Polynomial K :=
    aeval (fun i => if i = inp then (Polynomial.X : Polynomial K) else 0)
      (polys C out) with hgdef
  have hdeg : g.natDegree ≤ 2 ^ shearCount C := by
    have h1 : g.natDegree ≤ (polys C out).totalDegree * 1 := by
      refine Xlib.TotalDegreeAeval.natDegree_aeval_le _ _ fun i => ?_
      by_cases h : i = inp <;> simp [h]
    rw [mul_one] at h1
    exact h1.trans (totalDegree_polys_le C out)
  have hg : ∀ x : K, g.eval x = x⁻¹ := by
    intro x
    rw [hgdef, Xlib.TotalDegreeAeval.eval_aeval]
    have hpt : (fun i => Polynomial.eval x
          (if i = inp then (Polynomial.X : Polynomial K) else 0))
        = fun i => if i = inp then x else 0 := by
      funext i
      by_cases h : i = inp <;> simp [h]
    rw [hpt, ← run_eq_eval_polys]
    exact hspec x
  exact (card_sub_two_le_natDegree g hg).trans hdeg

/-- Bit-length form: computing the inverse costs at least `⌈log₂ (q − 2)⌉`
multiply-add gates. -/
theorem clog_le_shearCount {n : ℕ} (C : Circuit n K) (inp out : Fin n)
    (hspec : ∀ x : K, run C (fun i => if i = inp then x else 0) out = x⁻¹) :
    Nat.clog 2 (Fintype.card K - 2) ≤ shearCount C :=
  Nat.clog_le_of_le_pow (card_sub_two_le_two_pow_shearCount C inp out hspec)

end Circuit

section Secp256k1

/-- The secp256k1 base-field prime `p = 2^256 - 2^32 - 977`. -/
def secp256k1P : ℕ := 2 ^ 256 - 2 ^ 32 - 977

/-- **secp256k1 instantiation**: any shear circuit computing modular inversion
in the secp256k1 base field uses at least `256` multiply-add gates. This is
why reversible/quantum elliptic-curve point addition is dominated by its
modular inversions. -/
theorem secp256k1_inversion_needs_256_shears [Fact (Nat.Prime secp256k1P)]
    {n : ℕ} (C : Circuit n (ZMod secp256k1P)) (inp out : Fin n)
    (hspec : ∀ x : ZMod secp256k1P,
      run C (fun i => if i = inp then x else 0) out = x⁻¹) :
    256 ≤ shearCount C := by
  haveI : NeZero secp256k1P := ⟨by norm_num [secp256k1P]⟩
  have h := card_sub_two_le_two_pow_shearCount C inp out hspec
  rw [ZMod.card] at h
  by_contra hs
  have h2 : (2 : ℕ) ^ shearCount C ≤ 2 ^ 255 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : secp256k1P - 2 ≤ 2 ^ 255 := h.trans h2
  norm_num [secp256k1P] at h3

end Secp256k1

end Xlib.ShearInversionLB
