/-
# A known refutation for A218002

Source: OEIS A218002, entry by Paul D. Hanna (Oct 17 2012), and Geoffrey
Critzer's refutation comment (Nov 08 2015).
The factorial-scaled coefficients of `exp(Σ_{p prime} x^p/p)` do not count
permutations of prime order: at `n=3` the coefficient gives 2, while the
three transpositions already have prime order.
The source's cycle-length interpretation is not proved here; only the
counterexample to the prime-order assertion is formalized.
-/
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false

namespace Candidates.A218002Refutation

open PowerSeries

/-! ## Definitions -/

/-- The inner series `∑_{p prime} x^p / p` of the entry's e.g.f., over `ℚ`. -/
noncomputable def primeSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n.Prime then (1 : ℚ) / n else 0

/-- The e.g.f. `exp(∑_{p prime} x^p / p)` of A218002, formed by genuine
formal substitution of `primeSeries` (zero constant term) into `exp`. -/
noncomputable def egf : PowerSeries ℚ := (PowerSeries.exp ℚ).subst primeSeries

/-- `a(n) = n! * [x^n] exp(∑_{p prime} x^p / p)`, the OEIS A218002 term
(offset `0`), as a rational number. -/
noncomputable def a (n : ℕ) : ℚ := (n.factorial : ℚ) * PowerSeries.coeff n egf

/-- The number of permutations of `{0, …, n-1}` whose group order is a prime. -/
noncomputable def primeOrderCount (n : ℕ) : ℕ :=
  Nat.card {σ : Equiv.Perm (Fin n) // (orderOf σ).Prime}

/-- The shifted series `∑_{p prime} x^(p-2) / p`, so that
`primeSeries = X^2 * tailSeries`. -/
noncomputable def tailSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => if (n + 2).Prime then (1 : ℚ) / (n + 2 : ℕ) else 0

/-- Every prime is at least `2`, so `primeSeries` factors through `X^2`. -/
theorem primeSeries_eq : primeSeries = X ^ 2 * tailSeries := by
  ext n
  rw [coeff_X_pow_mul']
  unfold primeSeries tailSeries
  by_cases h : 2 ≤ n
  · rw [if_pos h, coeff_mk, coeff_mk, Nat.sub_add_cancel h]
  · rw [if_neg h, coeff_mk]
    have hn : n < 2 := by omega
    interval_cases n <;> norm_num

/-- The inner series has zero constant term, so the substitution is legal. -/
theorem constantCoeff_primeSeries : constantCoeff primeSeries = 0 := by
  rw [primeSeries_eq]
  simp

/-- `primeSeries ^ d` has no coefficient below degree `2 d`. -/
theorem coeff_primeSeries_pow_of_lt {n d : ℕ} (h : n < 2 * d) :
    coeff n (primeSeries ^ d) = 0 := by
  rw [primeSeries_eq, mul_pow, ← pow_mul, coeff_X_pow_mul', if_neg (by omega)]

/-- From degree `2 d` on, the coefficients of `primeSeries ^ d` are those of
`tailSeries ^ d`, shifted by `2 d`. -/
theorem coeff_primeSeries_pow {n d : ℕ} (h : 2 * d ≤ n) :
    coeff n (primeSeries ^ d) = coeff (n - 2 * d) (tailSeries ^ d) := by
  rw [primeSeries_eq, mul_pow, ← pow_mul, coeff_X_pow_mul', if_pos h]

/-- The `n`-th coefficient of the e.g.f. is the finite sum
`∑_{d ≤ n} [x^n] primeSeries^d / d!`. -/
theorem coeff_egf (n : ℕ) :
    coeff n egf =
      ∑ d ∈ Finset.range (n + 1), (1 / (d.factorial : ℚ)) * coeff n (primeSeries ^ d) := by
  unfold egf
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' constantCoeff_primeSeries)]
  simp only [coeff_exp, smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply]
  apply finsum_eq_sum_of_support_subset
  intro d hd
  rw [Function.mem_support] at hd
  apply Finset.mem_range.mpr
  by_contra hlt
  exact hd (by rw [coeff_primeSeries_pow_of_lt (by omega), mul_zero])

/-! ## Listed terms `1, 0, 1, 2, 3, 44` -/

example : a 0 = 1 := by
  rw [a, coeff_egf]
  simp

example : a 1 = 0 := by
  rw [a, coeff_egf]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [coeff_primeSeries_pow_of_lt (by norm_num : 1 < 2 * 1)]
  simp

example : a 2 = 1 := by
  rw [a, coeff_egf]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [coeff_primeSeries_pow_of_lt (by norm_num : 2 < 2 * 2)]
  simp [primeSeries, Nat.factorial]
  norm_num

/-- `a(3) = 2`: only the two 3-cycles have all cycle lengths prime. -/
theorem a_three : a 3 = 2 := by
  rw [a, coeff_egf]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [coeff_primeSeries_pow_of_lt (by norm_num : 3 < 2 * 2),
    coeff_primeSeries_pow_of_lt (by norm_num : 3 < 2 * 3)]
  simp [primeSeries, Nat.factorial]
  norm_num

example : a 4 = 3 := by
  rw [a, coeff_egf]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [coeff_primeSeries_pow_of_lt (by norm_num : 4 < 2 * 3),
    coeff_primeSeries_pow_of_lt (by norm_num : 4 < 2 * 4),
    coeff_primeSeries_pow (by norm_num : 2 * 2 ≤ 4)]
  simp [primeSeries, tailSeries, Nat.factorial, sq, coeff_mul]
  norm_num

example : a 5 = 44 := by
  rw [a, coeff_egf]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [coeff_primeSeries_pow_of_lt (by norm_num : 5 < 2 * 3),
    coeff_primeSeries_pow_of_lt (by norm_num : 5 < 2 * 4),
    coeff_primeSeries_pow_of_lt (by norm_num : 5 < 2 * 5),
    coeff_primeSeries_pow (by norm_num : 2 * 2 ≤ 5)]
  simp [primeSeries, tailSeries, Nat.factorial, sq, coeff_mul,
    Finset.Nat.sum_antidiagonal_succ]
  norm_num

/-- `primeOrderCount`: the only permutation of one point is
the identity, of order `1`, which is not prime. -/
example : primeOrderCount 1 = 0 := by
  rw [primeOrderCount, Nat.card_eq_zero]
  left
  constructor
  rintro ⟨σ, hσ⟩
  rw [Subsingleton.elim σ 1, orderOf_one] at hσ
  exact Nat.not_prime_one hσ

/-- The three transpositions `(0 1)`, `(1 2)`, `(2 0)` of `S_3` have prime
order `2`, so `S_3` has at least three permutations of prime order. -/
theorem three_le_primeOrderCount_three : 3 ≤ primeOrderCount 3 := by
  let f : Fin 3 → {σ : Equiv.Perm (Fin 3) // (orderOf σ).Prime} := fun i =>
    ⟨Equiv.swap i (i + 1), by
      rw [Equiv.Perm.IsSwap.orderOf ⟨i, i + 1, by fin_cases i <;> decide, rfl⟩]
      exact Nat.prime_two⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hval := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> first | rfl | (exact absurd hval (by decide))
  have hle := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_fin] at hle

/-! ## The conjecture and its refutation -/

/-- The unsigned A218002 conjecture: each factorial-scaled coefficient
of `exp(Σ_{p prime} x^p/p)` counts degree-n permutations of prime order.
Indices begin at 0. -/
def Conjecture : Prop :=
  ∀ n : ℕ, a n = (primeOrderCount n : ℚ)

/-- The prime-order conjecture fails at `n=3`: `a(3)=2`, while the three
transpositions already have prime order. This refutation is recorded by
Critzer in OEIS A218002; the cycle-length interpretation is not proved here. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  have h3 := hconj 3
  rw [a_three] at h3
  have hcount : (3 : ℚ) ≤ (primeOrderCount 3 : ℚ) := by
    exact_mod_cast three_le_primeOrderCount_three
  rw [← h3] at hcount
  norm_num at hcount

end Candidates.A218002Refutation
