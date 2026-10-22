/-
# A055210 — Yanev: sum of totients of square divisors via the largest square divisor

Velin Yanev's conjecture in OEIS A055210 (2019): for `n > 0`, the sum of
totients of square divisors equals `σ₂(s)/σ₁(s)`, with `s = A008833(n)`
the largest square divisor of `n`.

Write the largest square divisor as `m * m`.  A square `d * d` divides `n` iff
`d ∣ m` (since `lcm(d, m)^2` is a square divisor of `n`), so
`a(n) = ∑_{d ∣ m} φ(d²) = ∑_{d ∣ m} d φ(d)`.  The identity
`(∑_{d ∣ m} d φ(d)) · σ₁(m²) = σ₂(m²)` is an identity of multiplicative
functions of `m`, checked on prime powers by multiplying through by `p² - 1`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A055210YanevLargestSquare

open ArithmeticFunction Finset

/-! ## Definitions -/

/-- OEIS A055210: `a(n) = ∑_{d ∣ n, d a square} φ(d)`, the sum of totients of the
square divisors of `n` (entry NAME and first FORMULA). -/
def a (n : ℕ) : ℕ := ∑ d ∈ n.divisors with IsSquare d, Nat.totient d

/-- OEIS A008833: the largest square dividing `n`, as the supremum of the square
divisors of `n`.  For `n = 0` the divisor set is empty and the value is the junk `0`;
every statement below assumes `0 < n`. -/
def largestSquareDvd (n : ℕ) : ℕ := (n.divisors.filter IsSquare).sup id

/-- Examples: the first 30 terms of A055210. -/
example : (List.range 30).map (fun n => a (n + 1)) =
    [1, 1, 1, 3, 1, 1, 1, 3, 7, 1, 1, 3, 1, 1, 1, 11, 1, 7, 1, 3, 1, 1, 1, 3, 21, 1, 7, 3,
      1, 1] := by
  decide +kernel

/-- Examples: the first 30 terms of A008833. -/
example : (List.range 30).map (fun n => largestSquareDvd (n + 1)) =
    [1, 1, 1, 4, 1, 1, 1, 4, 9, 1, 1, 4, 1, 1, 1, 16, 1, 9, 1, 4, 1, 1, 1, 4, 25, 1, 9, 4,
      1, 1] := by
  decide +kernel

/-- Examples: `a 72 = 21` and `largestSquareDvd 72 = 36`. -/
example : a 72 = 21 ∧ largestSquareDvd 72 = 36 := by decide +kernel

/-! ## The largest square divisor -/

/-- For `0 < n`, `largestSquareDvd n` is a square dividing `n` and dominates every
square divisor of `n`. -/
theorem largestSquareDvd_spec {n : ℕ} (hn : 0 < n) :
    IsSquare (largestSquareDvd n) ∧ largestSquareDvd n ∣ n ∧
      ∀ e, e ∣ n → IsSquare e → e ≤ largestSquareDvd n := by
  have hne : (n.divisors.filter IsSquare).Nonempty :=
    ⟨1, Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨one_dvd n, hn.ne'⟩, ⟨1, rfl⟩⟩⟩
  obtain ⟨s, hs, hseq⟩ := Finset.exists_mem_eq_sup _ hne id
  rw [Finset.mem_filter, Nat.mem_divisors] at hs
  refine ⟨?_, ?_, fun e he hsq => ?_⟩
  · rw [largestSquareDvd, hseq]
    exact hs.2
  · rw [largestSquareDvd, hseq]
    exact hs.1.1
  · exact Finset.le_sup (f := id)
      (Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨he, hn.ne'⟩, hsq⟩)

/-- If `m * m` is the largest square dividing `0 < n`, then `d * d ∣ n ↔ d ∣ m`. -/
theorem mul_self_dvd_iff_dvd {n m : ℕ} (hn : 0 < n) (hm : largestSquareDvd n = m * m)
    (d : ℕ) : d * d ∣ n ↔ d ∣ m := by
  obtain ⟨-, hdvd, hmax⟩ := largestSquareDvd_spec hn
  rw [hm] at hdvd hmax
  constructor
  · intro hd
    have hd0 : 0 < d := Nat.pos_of_ne_zero fun h0 => by
      subst h0
      exact hn.ne' (Nat.eq_zero_of_zero_dvd (by simpa using hd))
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun h0 => by
      subst h0
      exact hn.ne' (Nat.eq_zero_of_zero_dvd (by simpa using hdvd))
    have hl : Nat.lcm d m * Nat.lcm d m ∣ n := by
      rw [← pow_two, ← Nat.pow_lcm_pow, pow_two, pow_two]
      exact Nat.lcm_dvd hd hdvd
    have hle : Nat.lcm d m * Nat.lcm d m ≤ m * m := hmax _ hl ⟨_, rfl⟩
    have hle' : Nat.lcm d m ≤ m := Nat.mul_self_le_mul_self_iff.1 hle
    have heq : Nat.lcm d m = m :=
      le_antisymm hle' (Nat.le_of_dvd (Nat.lcm_pos hd0 hm0) (Nat.dvd_lcm_right d m))
    rw [← heq]
    exact Nat.dvd_lcm_left d m
  · intro hd
    exact (Nat.mul_dvd_mul hd hd).trans hdvd

/-- `φ(d²) = d · φ(d)`. -/
theorem totient_mul_self (d : ℕ) : Nat.totient (d * d) = d * Nat.totient d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have h := Nat.totient_gcd_mul_totient_mul d d
  rw [Nat.gcd_self, mul_assoc] at h
  exact (mul_left_cancel₀ (Nat.totient_pos.2 hd).ne' h).trans (mul_comm _ _)

/-- If `m * m` is the largest square dividing `0 < n`, then
`a n = ∑_{d ∣ m} d · φ(d)`. -/
theorem a_eq_sum {n m : ℕ} (hn : 0 < n) (hm : largestSquareDvd n = m * m) :
    a n = ∑ d ∈ m.divisors, d * Nat.totient d := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    obtain ⟨-, hdvd, -⟩ := largestSquareDvd_spec hn
    rw [hm, mul_zero] at hdvd
    exact hn.ne' (Nat.eq_zero_of_zero_dvd hdvd)
  have himg : n.divisors.filter IsSquare = m.divisors.image (fun d => d * d) := by
    ext e
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
    constructor
    · rintro ⟨⟨he, -⟩, d, rfl⟩
      exact ⟨d, ⟨(mul_self_dvd_iff_dvd hn hm d).1 he, hm0⟩, rfl⟩
    · rintro ⟨d, ⟨hd, -⟩, rfl⟩
      exact ⟨⟨(mul_self_dvd_iff_dvd hn hm d).2 hd, hn.ne'⟩, ⟨d, rfl⟩⟩
  rw [a, himg, Finset.sum_image (fun x _ y _ h => Nat.mul_self_inj.1 h)]
  exact Finset.sum_congr rfl fun d _ => totient_mul_self d

/-! ## The prime-power identity -/

/-- `(∑_{j ≤ i} p^j φ(p^j)) · (p + 1) = p^(2i+1) + 1` for a prime `p`. -/
theorem sum_totient_prime_pow_mul (p i : ℕ) (hp : p.Prime) :
    ((∑ j ∈ range (i + 1), p ^ j * Nat.totient (p ^ j) : ℕ) : ℤ) * ((p : ℤ) + 1)
      = (p : ℤ) ^ (2 * i + 1) + 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [sum_range_succ, Nat.cast_add, add_mul, ih, Nat.totient_prime_pow_succ hp]
    push_cast [Nat.cast_sub hp.one_le]
    ring

/-- The prime-power case of the identity: for prime `p`,
`(∑_{j ≤ i} p^j φ(p^j)) · σ₁(p^(2i)) = σ₂(p^(2i))`, with `σ_k` written as the
geometric sums produced by `ArithmeticFunction.sigma_apply_prime_pow`. -/
theorem prime_pow_identity (p i : ℕ) (hp : p.Prime) :
    (∑ j ∈ range (i + 1), p ^ j * Nat.totient (p ^ j)) * ∑ j ∈ range (2 * i + 1), p ^ (j * 1)
      = ∑ j ∈ range (2 * i + 1), p ^ (j * 2) := by
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hne : ((p : ℤ) ^ 2 - 1) ≠ 0 := by nlinarith
  apply Nat.cast_injective (R := ℤ)
  apply mul_right_cancel₀ hne
  have hA := sum_totient_prime_pow_mul p i hp
  have hS1 : (∑ j ∈ range (2 * i + 1), (p : ℤ) ^ (j * 1)) * ((p : ℤ) - 1)
      = (p : ℤ) ^ (2 * i + 1) - 1 := by
    simp_rw [mul_one]
    exact geom_sum_mul _ _
  have hS2 : (∑ j ∈ range (2 * i + 1), (p : ℤ) ^ (j * 2)) * ((p : ℤ) ^ 2 - 1)
      = ((p : ℤ) ^ 2) ^ (2 * i + 1) - 1 := by
    simp_rw [mul_comm _ 2, pow_mul]
    exact geom_sum_mul _ _
  push_cast
  rw [hS2]
  calc ((∑ j ∈ range (i + 1), (p : ℤ) ^ j * (Nat.totient (p ^ j) : ℤ)) *
          ∑ j ∈ range (2 * i + 1), (p : ℤ) ^ (j * 1)) * ((p : ℤ) ^ 2 - 1)
      = (((∑ j ∈ range (i + 1), p ^ j * Nat.totient (p ^ j) : ℕ) : ℤ) * ((p : ℤ) + 1)) *
          ((∑ j ∈ range (2 * i + 1), (p : ℤ) ^ (j * 1)) * ((p : ℤ) - 1)) := by
        push_cast
        ring
    _ = ((p : ℤ) ^ 2) ^ (2 * i + 1) - 1 := by
        rw [hA, hS1]
        ring

/-! ## Multiplicativity -/

/-- The arithmetic function `m ↦ g (m * m)`. -/
def sqComp (g : ArithmeticFunction ℕ) : ArithmeticFunction ℕ :=
  ⟨fun m => g (m * m), by simp⟩

/-- Evaluation of `sqComp`. -/
theorem sqComp_apply (g : ArithmeticFunction ℕ) (m : ℕ) : sqComp g m = g (m * m) := rfl

/-- `m ↦ g (m * m)` is multiplicative when `g` is. -/
theorem isMultiplicative_sqComp {g : ArithmeticFunction ℕ} (hg : g.IsMultiplicative) :
    (sqComp g).IsMultiplicative := by
  refine ⟨by simp [sqComp_apply, hg.map_one], fun {m n} hmn => ?_⟩
  simp only [sqComp_apply]
  rw [show m * n * (m * n) = (m * m) * (n * n) by ring]
  exact hg.map_mul_of_coprime
    ((Nat.Coprime.mul_left hmn hmn).mul_right (Nat.Coprime.mul_left hmn hmn))

/-- The arithmetic function `d ↦ d · φ(d)`. -/
def idTotient : ArithmeticFunction ℕ := ⟨fun d => d * Nat.totient d, by simp⟩

/-- Evaluation of `idTotient`. -/
theorem idTotient_apply (d : ℕ) : idTotient d = d * Nat.totient d := rfl

/-- `d ↦ d · φ(d)` is multiplicative. -/
theorem isMultiplicative_idTotient : idTotient.IsMultiplicative := by
  refine ⟨by simp [idTotient_apply], fun {m n} hmn => ?_⟩
  simp only [idTotient_apply, Nat.totient_mul hmn]
  ring

/-- The core identity: `(∑_{d ∣ m} d · φ(d)) · σ₁(m²) = σ₂(m²)` for every `m`. -/
theorem sum_mul_totient_mul_sigma_one (m : ℕ) :
    (∑ d ∈ m.divisors, d * Nat.totient d) * sigma 1 (m * m) = sigma 2 (m * m) := by
  let F : ArithmeticFunction ℕ := (idTotient * zeta).pmul (sqComp (sigma 1))
  have hF : F.IsMultiplicative :=
    (isMultiplicative_idTotient.mul isMultiplicative_zeta).pmul
      (isMultiplicative_sqComp isMultiplicative_sigma)
  have hG : (sqComp (sigma 2)).IsMultiplicative :=
    isMultiplicative_sqComp isMultiplicative_sigma
  have hFG : F = sqComp (sigma 2) := by
    rw [IsMultiplicative.eq_iff_eq_on_prime_powers F hF _ hG]
    intro p i hp
    simp only [F, pmul_apply, mul_zeta_apply, sqComp_apply, ← pow_add,
      Nat.sum_divisors_prime_pow hp, sigma_apply_prime_pow hp, idTotient_apply,
      show i + i + 1 = 2 * i + 1 by ring]
    exact prime_pow_identity p i hp
  have h := congrArg (fun f : ArithmeticFunction ℕ => f m) hFG
  simp only [F, pmul_apply, mul_zeta_apply, sqComp_apply, idTotient_apply] at h
  exact h

/-! ## The conjecture -/

/-- **Yanev's conjecture (A055210, Velin Yanev, 2019), cross-multiplied form.**
For `0 < n`, with `s` the largest square dividing `n`,
`a(n) · σ₁(s) = σ₂(s)`. -/
theorem a_mul_sigma_one_largestSquareDvd (n : ℕ) (hn : 0 < n) :
    a n * sigma 1 (largestSquareDvd n) = sigma 2 (largestSquareDvd n) := by
  obtain ⟨hsq, -, -⟩ := largestSquareDvd_spec hn
  obtain ⟨m, hm⟩ := hsq
  rw [a_eq_sum hn hm, hm]
  exact sum_mul_totient_mul_sigma_one m

/-- **Yanev's conjecture (A055210, Velin Yanev, 2019).**

Here `a(n) = ∑_{d ∣ n, d square} φ(d)` (A055210) and `A008833(n)` is the largest
square dividing `n`.  The quotient is taken in `ℚ`; the denominator
`σ₁(A008833(n))` is positive for `0 < n`, so the division is not at its junk value. -/
theorem yanev (n : ℕ) (hn : 0 < n) :
    (a n : ℚ) = (sigma 2 (largestSquareDvd n) : ℚ) / (sigma 1 (largestSquareDvd n) : ℚ) := by
  have hs0 : largestSquareDvd n ≠ 0 := by
    intro h0
    obtain ⟨-, hdvd, -⟩ := largestSquareDvd_spec hn
    rw [h0] at hdvd
    exact hn.ne' (Nat.eq_zero_of_zero_dvd hdvd)
  have hpos : (0 : ℚ) < (sigma 1 (largestSquareDvd n) : ℚ) := by
    exact_mod_cast sigma_pos 1 _ hs0
  rw [eq_div_iff hpos.ne', ← a_mul_sigma_one_largestSquareDvd n hn]
  push_cast
  ring

end Candidates.A055210YanevLargestSquare
