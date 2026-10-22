/-
Schulte's convolution identity for Ω (OEIS A001222; Werner Schulte, Feb 10 2018).

For nonzero n, (x+y)^Ω(n) = ∑_{d∣n} x^Ω(d) (x+y)^(Ω(n/d)-ω(n/d)) y^ω(n/d).
The identity is proved over every commutative ring and specialized to ℂ, with 0^0 = 1.
Here Ω counts prime factors with multiplicity, ω counts distinct prime factors
(A001221), and Ω-ω is A046660. The guard n ≠ 0 is necessary.
Dressler–van de Lune give the x+y=1 case cited in the entry.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A001222SchulteComplexOmega

open ArithmeticFunction
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega

/-! ## Definition layer

* `Ω = ArithmeticFunction.cardFactors` (A001222): `Ω n = n.primeFactorsList.length`,
  the number of prime factors counted with multiplicity.
* `ω = ArithmeticFunction.cardDistinctFactors` (A001221):
  `ω n = n.primeFactorsList.dedup.length`.
* A046660 is `Ω n - ω n`; the `ℕ` subtraction is exact by
  `cardDistinctFactors_le_cardFactors`.
* `0 ^ 0 = 1` is Lean's `Monoid.npow` convention (`pow_zero`), matching the
  entry's stipulation. -/

/-- `ω n ≤ Ω n`: the number of distinct prime factors is at most the number
counted with multiplicity, so `Ω n - ω n` (A046660) is never truncated. -/
theorem cardDistinctFactors_le_cardFactors (n : ℕ) : ω n ≤ Ω n := by
  rw [cardDistinctFactors_apply, cardFactors_apply]
  exact (List.dedup_sublist _).length_le

/-- The prime-power case of Schulte's identity:
`∑_{j=0}^{i} x^j (x+y)^(Ω(p^(i-j)) - ω(p^(i-j))) y^(ω(p^(i-j))) = (x+y)^i`,
written with `ω(p^k) = [k ≠ 0]` and `Ω(p^k) = k`.  This is the telescoping
identity `(x+y)^i - x^i = y * ∑_{j<i} x^j (x+y)^(i-1-j)`. -/
theorem prime_pow_sum {R : Type*} [CommRing R] (x y : R) (i : ℕ) :
    ∑ j ∈ Finset.range (i + 1),
        x ^ j * (x + y) ^ ((i - j) - (if i - j = 0 then 0 else 1)) *
          y ^ (if i - j = 0 then 0 else 1) = (x + y) ^ i := by
  rw [Finset.sum_range_succ]
  have hgeom := (Commute.all x (x + y)).geom_sum₂_mul i
  have hterms : ∑ j ∈ Finset.range i,
      x ^ j * (x + y) ^ ((i - j) - (if i - j = 0 then 0 else 1)) *
        y ^ (if i - j = 0 then 0 else 1) =
      (∑ j ∈ Finset.range i, x ^ j * (x + y) ^ (i - 1 - j)) * y := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hji : j < i := Finset.mem_range.mp hj
    have hne : i - j ≠ 0 := by omega
    rw [if_neg hne, pow_one, show i - j - 1 = i - 1 - j by omega]
  rw [hterms]
  simp only [Nat.sub_self, if_true, pow_zero, mul_one]
  have hy : x - (x + y) = -y := by ring
  rw [hy] at hgeom
  linear_combination -hgeom

section Convolution

variable {R : Type*} [CommRing R]

/-- The arithmetic function `n ↦ a ^ Ω(n)` for `n ≠ 0` (and `0` at `0`);
Schulte's `g` (with `a = x`) and `f` (with `a = x + y`). -/
def powCardFactors (a : R) : ArithmeticFunction R :=
  ⟨fun n => if n = 0 then 0 else a ^ Ω n, if_pos rfl⟩

/-- The arithmetic function `n ↦ (x+y)^(Ω(n) - ω(n)) * y^ω(n)` for `n ≠ 0`
(and `0` at `0`); this is Schulte's `h(n) = (x+y)^A046660(n) * y^A001221(n)`. -/
def schulteH (x y : R) : ArithmeticFunction R :=
  ⟨fun n => if n = 0 then 0 else (x + y) ^ (Ω n - ω n) * y ^ ω n, if_pos rfl⟩

/-- Evaluation of `powCardFactors` away from `0`. -/
theorem powCardFactors_apply (a : R) {n : ℕ} (hn : n ≠ 0) :
    powCardFactors a n = a ^ Ω n := if_neg hn

/-- Evaluation of `schulteH` away from `0`. -/
theorem schulteH_apply (x y : R) {n : ℕ} (hn : n ≠ 0) :
    schulteH x y n = (x + y) ^ (Ω n - ω n) * y ^ ω n := if_neg hn

/-- `n ↦ a ^ Ω(n)` is multiplicative (indeed completely multiplicative). -/
theorem isMultiplicative_powCardFactors (a : R) :
    (powCardFactors a).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [powCardFactors_apply], fun {m n} hm hn _ => ?_⟩
  rw [powCardFactors_apply a (mul_ne_zero hm hn), powCardFactors_apply a hm,
    powCardFactors_apply a hn, cardFactors_mul hm hn, pow_add]

/-- Schulte's `h` is multiplicative. -/
theorem isMultiplicative_schulteH (x y : R) : (schulteH x y).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [schulteH_apply], fun {m n} hm hn hmn => ?_⟩
  rw [schulteH_apply x y (mul_ne_zero hm hn), schulteH_apply x y hm,
    schulteH_apply x y hn, cardFactors_mul hm hn, cardDistinctFactors_mul hmn]
  have hm' := cardDistinctFactors_le_cardFactors m
  have hn' := cardDistinctFactors_le_cardFactors n
  rw [show Ω m + Ω n - (ω m + ω n) = (Ω m - ω m) + (Ω n - ω n) by omega,
    pow_add, pow_add]
  ring

/-- Dirichlet-convolution form of Schulte's identity: `f = g * h`, i.e.
`(x+y)^Ω = x^Ω * h` as arithmetic functions. -/
theorem powCardFactors_add_eq_mul (x y : R) :
    powCardFactors (x + y) = powCardFactors x * schulteH x y := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _
    (isMultiplicative_powCardFactors (x + y)) _
    ((isMultiplicative_powCardFactors x).mul (isMultiplicative_schulteH x y))).mpr ?_
  intro p i hp
  have hp0 : p ^ i ≠ 0 := pow_ne_zero i hp.ne_zero
  rw [powCardFactors_apply _ hp0, cardFactors_apply_prime_pow hp, mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => powCardFactors x a * schulteH x y b),
    Nat.sum_divisors_prime_pow hp, ← prime_pow_sum x y i]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [Nat.pow_div hji hp.pos, powCardFactors_apply _ (pow_ne_zero j hp.ne_zero),
    schulteH_apply _ _ (pow_ne_zero _ hp.ne_zero), cardFactors_apply_prime_pow hp,
    cardFactors_apply_prime_pow hp, mul_assoc]
  by_cases hk : i - j = 0
  · rw [hk, if_pos rfl, pow_zero, pow_zero, pow_zero, cardDistinctFactors_one]
    simp
  · rw [if_neg hk, cardDistinctFactors_apply_prime_pow hp hk]

end Convolution

/-! ## The conjecture -/

/-- **Schulte's identity over any commutative ring.**  For `n ≠ 0`,
`(x+y)^Ω(n) = ∑_{d ∣ n} x^Ω(d) * (x+y)^(Ω(n/d) - ω(n/d)) * y^ω(n/d)`.
The natural-number subtraction is exact by `cardDistinctFactors_le_cardFactors`. -/
theorem schulte_identity {R : Type*} [CommRing R] (x y : R) (n : ℕ) (hn : n ≠ 0) :
    (x + y) ^ Ω n =
      ∑ d ∈ n.divisors, x ^ Ω d * (x + y) ^ (Ω (n / d) - ω (n / d)) * y ^ ω (n / d) := by
  have hconv := congrArg (fun f : ArithmeticFunction R => f n) (powCardFactors_add_eq_mul x y)
  simp only [mul_apply] at hconv
  rw [powCardFactors_apply _ hn,
    Nat.sum_divisorsAntidiagonal (fun a b => powCardFactors x a * schulteH x y b)] at hconv
  rw [hconv]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
  have hnd0 : n / d ≠ 0 :=
    Nat.ne_of_gt (Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_ne_zero hd0))
  rw [powCardFactors_apply _ hd0, schulteH_apply _ _ hnd0, mul_assoc]

/-- Schulte's identity specialized to complex `x,y` and nonzero `n` (OEIS A001222). -/
theorem schulte_conjecture (x y : ℂ) (n : ℕ) (hn : n ≠ 0) :
    (x + y) ^ Ω n =
      ∑ d ∈ n.divisors, x ^ Ω d * (x + y) ^ (Ω (n / d) - ω (n / d)) * y ^ ω (n / d) :=
  schulte_identity x y n hn

/-! ## Sanity layer -/

-- `Ω` agrees with the A001222 DATA line for `n = 1, …, 24`.
example : (List.range 24).map (fun n => Ω (n + 1)) =
    [0, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 3, 1, 2, 2, 4, 1, 3, 1, 3, 2, 2, 1, 4] := by
  simp [List.range_succ, cardFactors_apply]

-- `ω` agrees with the A001221 DATA line for `n = 1, …, 12`.
example : (List.range 12).map (fun n => ω (n + 1)) =
    [0, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2] := by
  simp [List.range_succ, cardDistinctFactors_apply]

-- The guard `n ≠ 0` is key: at `n = 0` the left side is `1` and the
-- divisor sum is empty.
example : ¬ ∀ x y : ℂ, (x + y) ^ Ω 0 =
    ∑ d ∈ (0 : ℕ).divisors, x ^ Ω d * (x + y) ^ (Ω (0 / d) - ω (0 / d)) * y ^ ω (0 / d) := by
  intro h
  have h0 := h 0 0
  simp at h0

end Candidates.A001222SchulteComplexOmega
