/-
# Gauss's formula for the number of monic irreducible polynomials over `𝔽_q`

## Source (classical)

* C. F. Gauss, *Disquisitiones Arithmeticae*, the unpublished eighth section
  ("Disquisitiones generales de congruentiis", Werke Bd. II, 1863).
* R. Lidl and H. Niederreiter, *Finite Fields*, Encyclopedia of Mathematics
  and its Applications 20, Cambridge University Press, 1997:
  Corollary 3.21 (the divisor-sum identity) and Theorem 3.25 (the Möbius form).
* OEIS A001037 (`q = 2`) and A027376 (`q = 3`).

Recorded 2026-10-21.

## Informal statement (verbatim from the target specification)

Let K be a finite field with q elements and N_q(d) the number of monic
irreducible polynomials of degree d in K[X]. Then
sum_{d | n} d·N_q(d) = q^n for n >= 1, hence
n·N_q(n) = sum_{d | n} μ(d) q^{n/d}; in particular N_q(n) >= 1.

## Mathlib absence

Re-checked with `leandoc` on 2026-10-21 ("card monic irreducible polynomials
finite field degree", "number of irreducible polynomials degree divisors sum",
"necklace polynomial moebius irreducible count") and by grep for
`Monic ∧ Irreducible` cardinalities: no count of monic irreducible polynomials
is present.  The ingredients used below are
`Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X`,
`galois_poly_separable`, `Polynomial.mem_normalizedFactors_iff`,
`UniqueFactorizationMonoid.prod_normalizedFactors` and
`ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq`.

## Conventions

`q` is spelled `Nat.card K` and `N_q(d)` is `monicIrreducibleCount K d`, a
`Nat.card` of a subtype of `K[X]`; one cardinality API is used throughout.
Finiteness of `K` is the typeclass `[Finite K]`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.GaussIrreduciblePolynomialCount

open Polynomial UniqueFactorizationMonoid ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- `N_q(d)`: the number of monic irreducible polynomials of degree `d` in `K[X]`. -/
noncomputable def monicIrreducibleCount (K : Type*) [Field K] (d : ℕ) : ℕ :=
  Nat.card {f : K[X] // f.Monic ∧ Irreducible f ∧ f.natDegree = d}

/-- No monic polynomial of degree `0` is irreducible (it is the unit `1`), so `N_q(0) = 0`. -/
theorem monicIrreducibleCount_zero (K : Type*) [Field K] : monicIrreducibleCount K 0 = 0 := by
  rw [monicIrreducibleCount, Nat.card_eq_zero]
  left
  refine ⟨fun ⟨f, hmon, hirr, hdeg⟩ => hirr.not_isUnit ?_⟩
  rw [eq_one_of_monic_natDegree_zero hmon hdeg]
  exact isUnit_one

variable {K : Type*} [Field K] [Finite K]

/-- The characteristic of a finite field divides its cardinality. -/
theorem ringChar_dvd_natCard : ringChar K ∣ Nat.card K := by
  have := Fintype.ofFinite K
  rw [← Fintype.card_eq_nat_card]
  exact (CharP.cast_eq_zero_iff K (ringChar K) _).mp (Nat.cast_card_eq_zero K)

/-- For `n ≠ 0`, the Galois polynomial `X ^ (q ^ n) - X` is nonzero. -/
theorem galoisPoly_ne_zero {n : ℕ} (hn : n ≠ 0) : (X ^ Nat.card K ^ n - X : K[X]) ≠ 0 :=
  FiniteField.X_pow_card_pow_sub_X_ne_zero K hn Finite.one_lt_card

/-- For `n ≠ 0`, the Galois polynomial `X ^ (q ^ n) - X` is squarefree (it is separable). -/
theorem galoisPoly_squarefree {n : ℕ} (hn : n ≠ 0) :
    Squarefree (X ^ Nat.card K ^ n - X : K[X]) :=
  (galois_poly_separable (ringChar K) _ (dvd_pow ringChar_dvd_natCard hn)).squarefree

/-- The normalized factors of `X ^ (q ^ n) - X` are exactly the monic irreducible
polynomials whose degree divides `n`. -/
theorem mem_normalizedFactors_galoisPoly_iff [DecidableEq K] {n : ℕ} (hn : n ≠ 0) (g : K[X]) :
    g ∈ normalizedFactors (X ^ Nat.card K ^ n - X : K[X]) ↔
      g.Monic ∧ Irreducible g ∧ g.natDegree ∣ n := by
  rw [Polynomial.mem_normalizedFactors_iff (galoisPoly_ne_zero hn)]
  constructor
  · rintro ⟨hirr, hmon, hdvd⟩
    exact ⟨hmon, hirr, hirr.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mpr hdvd⟩
  · rintro ⟨hmon, hirr, hdeg⟩
    exact ⟨hirr, hmon, hirr.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp hdeg⟩

/-- **Gauss's divisor-sum identity** (Lidl–Niederreiter, Cor. 3.21):
for `n ≥ 1`, `∑_{d ∣ n} d · N_q(d) = q ^ n`. -/
theorem sum_divisors_mul_monicIrreducibleCount {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, d * monicIrreducibleCount K d = Nat.card K ^ n := by
  classical
  have hn0 : n ≠ 0 := hn.ne'
  set f : K[X] := X ^ Nat.card K ^ n - X with hf
  have hf0 : f ≠ 0 := galoisPoly_ne_zero hn0
  set S : Finset K[X] := (normalizedFactors f).toFinset with hS
  have hnodup : (normalizedFactors f).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hf0).mp (galoisPoly_squarefree hn0)
  have hmem : ∀ g, g ∈ S ↔ g.Monic ∧ Irreducible g ∧ g.natDegree ∣ n := fun g => by
    rw [hS, Multiset.mem_toFinset]
    exact mem_normalizedFactors_galoisPoly_iff hn0 g
  -- the degree of `f` is the sum of the degrees of its (distinct) normalized factors
  have hdeg : ∑ g ∈ S, g.natDegree = Nat.card K ^ n := by
    have hprod : (normalizedFactors f).prod.natDegree = f.natDegree :=
      natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (prod_normalizedFactors hf0))
    rw [natDegree_multiset_prod _ (zero_notMem_normalizedFactors f),
      FiniteField.X_pow_card_pow_sub_X_natDegree_eq K hn0 Finite.one_lt_card] at hprod
    rw [hS, Finset.sum_eq_multiset_sum, Multiset.toFinset_val, hnodup.dedup]
    exact hprod
  -- each fibre of `natDegree` over a divisor `d` of `n` is counted by `N_q(d)`
  have hcount : ∀ d ∈ n.divisors,
      monicIrreducibleCount K d = (S.filter (fun g => g.natDegree = d)).card := by
    intro d hd
    rw [monicIrreducibleCount, ← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
    rw [Finset.mem_filter, hmem]
    constructor
    · rintro ⟨hmon, hirr, rfl⟩
      exact ⟨⟨hmon, hirr, Nat.dvd_of_mem_divisors hd⟩, rfl⟩
    · rintro ⟨⟨hmon, hirr, _⟩, rfl⟩
      exact ⟨hmon, hirr, rfl⟩
  calc ∑ d ∈ n.divisors, d * monicIrreducibleCount K d
      = ∑ d ∈ n.divisors, ∑ g ∈ S.filter (fun g => g.natDegree = d), g.natDegree := by
        refine Finset.sum_congr rfl fun d hd => ?_
        rw [hcount d hd, Finset.sum_congr rfl fun g hg => (Finset.mem_filter.mp hg).2,
          Finset.sum_const, smul_eq_mul, mul_comm]
    _ = ∑ g ∈ S, g.natDegree :=
        Finset.sum_fiberwise_of_maps_to
          (fun g hg => Nat.mem_divisors.mpr ⟨((hmem g).mp hg).2.2, hn0⟩) _
    _ = Nat.card K ^ n := hdeg

/-- **Gauss's formula** (Lidl–Niederreiter, Thm. 3.25): for `n ≥ 1`,
`n · N_q(n) = ∑_{d ∣ n} μ(d) q ^ (n / d)`. -/
theorem mul_monicIrreducibleCount_eq_sum_moebius {n : ℕ} (hn : 0 < n) :
    (n : ℤ) * monicIrreducibleCount K n =
      ∑ d ∈ n.divisors, μ d * (Nat.card K : ℤ) ^ (n / d) := by
  have hsum : ∀ m > 0, ∑ d ∈ m.divisors, (((d : ℕ) : ℤ) * monicIrreducibleCount K d) =
      (Nat.card K : ℤ) ^ m := fun m hm => by
    exact_mod_cast sum_divisors_mul_monicIrreducibleCount (K := K) hm
  have key := (sum_eq_iff_sum_mul_moebius_eq (R := ℤ)
    (f := fun d => (d : ℤ) * monicIrreducibleCount K d)
    (g := fun m => (Nat.card K : ℤ) ^ m)).mp hsum n hn
  simp only [Int.cast_id] at key
  rw [Nat.sum_divisorsAntidiagonal (fun a b => μ a * (Nat.card K : ℤ) ^ b)] at key
  exact key.symm

/-- **Existence** (Lidl–Niederreiter, Cor. 3.21 consequence): for every `n ≥ 1` there is
at least one monic irreducible polynomial of degree `n` over `K`, i.e. `0 < N_q(n)`. -/
theorem monicIrreducibleCount_pos {n : ℕ} (hn : 0 < n) : 0 < monicIrreducibleCount K n := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hle : ∀ d ∈ n.properDivisors, d * monicIrreducibleCount K d ≤ Nat.card K ^ d := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_properDivisors hd
    rw [← sum_divisors_mul_monicIrreducibleCount hd0]
    exact Finset.single_le_sum (f := fun e => e * monicIrreducibleCount K e)
      (fun _ _ => Nat.zero_le _) (Nat.mem_divisors_self d hd0.ne')
  have hlt : ∑ d ∈ n.properDivisors, d * monicIrreducibleCount K d < Nat.card K ^ n :=
    (Finset.sum_le_sum hle).trans_lt
      (Nat.geomSum_lt hq fun d hd => (Nat.mem_properDivisors.mp hd).2)
  have htot := sum_divisors_mul_monicIrreducibleCount (K := K) hn
  rw [← Nat.cons_self_properDivisors hn.ne', Finset.sum_cons] at htot
  have hpos : 0 < n * monicIrreducibleCount K n := by omega
  exact Nat.pos_of_ne_zero fun h => by simp [h] at hpos

/-! ## Ground-truth checks (OEIS A001037 for `q = 2`, A027376 for `q = 3`) -/

/-- Over `𝔽₂` there are two monic irreducible polynomials of degree 1 (`X`, `X + 1`). -/
example : monicIrreducibleCount (ZMod 2) 1 = 2 := by
  have h := sum_divisors_mul_monicIrreducibleCount (K := ZMod 2) (n := 1) one_pos
  simpa [Nat.card_zmod] using h

/-- Over `𝔽₂` there is exactly one monic irreducible quadratic (`X ^ 2 + X + 1`). -/
example : monicIrreducibleCount (ZMod 2) 2 = 1 := by
  have h := sum_divisors_mul_monicIrreducibleCount (K := ZMod 2) (n := 2) two_pos
  have h1 := sum_divisors_mul_monicIrreducibleCount (K := ZMod 2) (n := 1) one_pos
  rw [show Nat.divisors 2 = {1, 2} by decide] at h
  rw [Nat.divisors_one] at h1
  simp only [Nat.card_zmod, Finset.sum_singleton] at h h1
  rw [Finset.sum_pair (by decide)] at h
  omega

/-- Over `𝔽₃` there are three monic irreducible quadratics (A027376(2) = 3). -/
example : monicIrreducibleCount (ZMod 3) 2 = 3 := by
  have h := mul_monicIrreducibleCount_eq_sum_moebius (K := ZMod 3) (n := 2) two_pos
  rw [show Nat.divisors 2 = {1, 2} by decide, Finset.sum_pair (by decide)] at h
  have hμ2 : μ 2 = -1 := ArithmeticFunction.moebius_apply_prime Nat.prime_two
  simp only [Nat.card_zmod, ArithmeticFunction.moebius_apply_one, hμ2] at h
  norm_num at h
  omega

end Candidates.GaussIrreduciblePolynomialCount
