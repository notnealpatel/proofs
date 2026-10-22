/-
# A060841: a denominator counterexample

OEIS A060841, Robert G. Wilson v (Aug 02 2015); Harry J. Smith's
integrality comment (Jul 13 2009). Michael De Vlieger (Aug 20 2026)
records Adamczewski's counterexample, arXiv:2608.11941; see also A260502.
The rational matrix is indexed by `1 ≤ i,j ≤ n`, with entries `1/lcm(i,j)`.
Smith's determinant formula and a prime-product identity give the reduced
denominator of its inverse determinant at `n = 1807` as `2^2342 * 3`.
This refutes the conjunction containing Wilson's power-of-two claim;
it does not prove the complete classification of integral values.
-/
import Mathlib

set_option autoImplicit false

open Matrix Finset

namespace Candidates.A060841Refutation

/-! ## Definitions and Smith's determinant -/

/-- The `n × n` matrix of A060841, `M[i,j] = 1 / lcm(i,j)` with 1-based indices
`i, j ∈ {1, …, n}` (stored at `Fin n` positions `i - 1, j - 1`). -/
def lcmRecipMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => 1 / (Nat.lcm (i.val + 1) (j.val + 1) : ℚ)

/-- Smith's GCD matrix `G[i,j] = gcd(i,j)`, 1-based, as an auxiliary for the proof. -/
def gcdMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => (Nat.gcd (i.val + 1) (j.val + 1) : ℚ)

/-- The divisibility incidence matrix `A[i,k] = [k ∣ i]`, 1-based; `G = A · diag(φ) · Aᵀ`. -/
def divMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i k => if k.val + 1 ∣ i.val + 1 then 1 else 0

/-- For `0 < g ≤ n`, `∑_{k=1}^{n} [k ∣ g] φ(k) = g` (Gauss's identity restricted to `[1, n]`). -/
theorem sum_totient_dvd (n g : ℕ) (hg0 : g ≠ 0) (hgn : g ≤ n) :
    ∑ k : Fin n, (if k.val + 1 ∣ g then (Nat.totient (k.val + 1) : ℚ) else 0) = g := by
  have h1 : ∑ k : Fin n, (if k.val + 1 ∣ g then (Nat.totient (k.val + 1) : ℚ) else 0)
      = ∑ k ∈ range (n + 1), (if k ∣ g then (Nat.totient k : ℚ) else 0) := by
    rw [Finset.sum_range_succ',
      Fin.sum_univ_eq_sum_range (fun k => if k + 1 ∣ g then (Nat.totient (k + 1) : ℚ) else 0)]
    simp
  have h2 : (range (n + 1)).filter (· ∣ g) = g.divisors := by
    ext d
    simp only [mem_filter, mem_range, Nat.mem_divisors]
    constructor
    · rintro ⟨_, hd⟩
      exact ⟨hd, hg0⟩
    · rintro ⟨hd, _⟩
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hg0) hd
      exact ⟨by omega, hd⟩
  rw [h1, ← Finset.sum_filter, h2]
  exact_mod_cast Nat.sum_totient g

/-- Smith's factorization `G = A · diag(φ(1), …, φ(n)) · Aᵀ`. -/
theorem gcdMatrix_eq (n : ℕ) :
    gcdMatrix n = divMatrix n * diagonal (fun k => (Nat.totient (k.val + 1) : ℚ)) *
      (divMatrix n)ᵀ := by
  ext i j
  simp only [mul_apply, diagonal, of_apply, transpose_apply, divMatrix, gcdMatrix]
  have hg0 : Nat.gcd (i.val + 1) (j.val + 1) ≠ 0 := by positivity
  have hgn : Nat.gcd (i.val + 1) (j.val + 1) ≤ n :=
    (Nat.gcd_le_left _ (Nat.succ_pos _)).trans i.isLt
  rw [← sum_totient_dvd n _ hg0 hgn]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k]
  · by_cases ha : k.val + 1 ∣ i.val + 1 <;> by_cases hb : k.val + 1 ∣ j.val + 1 <;>
      simp [Nat.dvd_gcd_iff, ha, hb]
  · intro b _ hb
    rw [if_neg hb]
    ring
  · simp

/-- `A` is unitriangular, so `det A = 1`. -/
theorem det_divMatrix (n : ℕ) : (divMatrix n).det = 1 := by
  rw [det_of_lowerTriangular]
  · simp [divMatrix]
  · intro i j hij
    have hij' : i < j := hij
    simp only [divMatrix, of_apply]
    rw [if_neg]
    intro hd
    have := Nat.le_of_dvd (Nat.succ_pos _) hd
    have : i.val < j.val := hij'
    omega

/-- **Smith's determinant (1875).** `det (gcd(i,j))_{1 ≤ i,j ≤ n} = φ(1) ⋯ φ(n)`. -/
theorem det_gcdMatrix (n : ℕ) :
    (gcdMatrix n).det = ∏ k ∈ range n, (Nat.totient (k + 1) : ℚ) := by
  rw [gcdMatrix_eq, det_mul, det_mul, det_transpose, det_divMatrix, det_diagonal,
    Fin.prod_univ_eq_prod_range (fun k => (Nat.totient (k + 1) : ℚ))]
  ring

/-- `1 / lcm(i,j) = (1/i) · gcd(i,j) · (1/j)`, i.e. `M = diag(1/i) · G · diag(1/j)`. -/
theorem lcmRecipMatrix_eq (n : ℕ) :
    lcmRecipMatrix n = diagonal (fun i => 1 / (i.val + 1 : ℚ)) * gcdMatrix n *
      diagonal (fun j => 1 / (j.val + 1 : ℚ)) := by
  ext i j
  rw [mul_diagonal, diagonal_mul]
  simp only [lcmRecipMatrix, gcdMatrix, of_apply]
  have h := Nat.gcd_mul_lcm (i.val + 1) (j.val + 1)
  have hl : (Nat.lcm (i.val + 1) (j.val + 1) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.lcm_ne_zero (by omega) (by omega))
  have hq : (Nat.gcd (i.val + 1) (j.val + 1) : ℚ) * Nat.lcm (i.val + 1) (j.val + 1)
      = (i.val + 1) * (j.val + 1) := by exact_mod_cast h
  have hi : (i.val + 1 : ℚ) ≠ 0 := by positivity
  have hj : (j.val + 1 : ℚ) ≠ 0 := by positivity
  rw [eq_comm, mul_one_div, div_mul_eq_mul_div, div_div, div_eq_iff (mul_ne_zero hi hj),
    ← hq]
  field_simp

/-- `det M_n = φ(1) ⋯ φ(n) / (n!)²`. -/
theorem det_lcmRecipMatrix (n : ℕ) :
    (lcmRecipMatrix n).det =
      (∏ k ∈ range n, (Nat.totient (k + 1) : ℚ)) / ((n.factorial : ℚ) ^ 2) := by
  rw [lcmRecipMatrix_eq, det_mul, det_mul, det_diagonal, det_gcdMatrix,
    Fin.prod_univ_eq_prod_range (fun k => 1 / (k + 1 : ℚ)), ← Finset.prod_range_add_one_eq_factorial]
  push_cast
  rw [Finset.prod_div_distrib, Finset.prod_const_one]
  ring

/-- `det M_n` is positive, so `1 / det M_n` is never the junk value `1 / 0`. -/
theorem det_lcmRecipMatrix_pos (n : ℕ) : 0 < (lcmRecipMatrix n).det := by
  rw [det_lcmRecipMatrix]
  have hφ : 0 < ∏ k ∈ range n, (Nat.totient (k + 1) : ℚ) :=
    Finset.prod_pos fun k _ => by exact_mod_cast Nat.totient_pos.2 (Nat.succ_pos k)
  have hf : 0 < (n.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos n
  positivity

/-- The rational number `1 / det M_n` of A060841. -/
noncomputable def invDet (n : ℕ) : ℚ := 1 / (lcmRecipMatrix n).det

/-- A060841: `a(n)` is the numerator of `1 / det M_n`. -/
noncomputable def a (n : ℕ) : ℤ := (invDet n).num

/-- The OEIS formula `1 / det M_n = (n!)² / (φ(1) ⋯ φ(n))`. -/
theorem invDet_eq (n : ℕ) :
    invDet n = (n.factorial : ℚ) ^ 2 / ∏ k ∈ range n, (Nat.totient (k + 1) : ℚ) := by
  rw [invDet, det_lcmRecipMatrix, one_div_div]

/-! ## Examples -/

-- Direct check of the matrix definition at `n = 2`: `M = [[1, 1/2], [1/2, 1/2]]`.
example : (lcmRecipMatrix 2).det = 1 / 4 := by
  rw [det_fin_two]
  simp [lcmRecipMatrix]
  norm_num

-- The first ten listed terms 1, 4, 18, 144, 900, 16200, 132300, 2116800,
-- 28576800, 714420000.
example : a 1 = 1 ∧ a 2 = 4 ∧ a 3 = 18 ∧ a 4 = 144 ∧ a 5 = 900 ∧ a 6 = 16200 ∧
    a 7 = 132300 ∧ a 8 = 2116800 ∧ a 9 = 28576800 ∧ a 10 = 714420000 := by
  simp only [a, invDet_eq]
  decide +kernel

-- Smith's comment: `1/det(35)` has denominator `2`, while `1/det(34)` is an integer.
example : (invDet 34).den = 1 ∧ (invDet 35).den = 2 := by
  simp only [invDet_eq]
  decide +kernel

/-! ## The conjecture -/

/-- Wilson's A060841 conjunction: for `n ≥ 1`, integrality of the inverse
determinant is equivalent to `n ≤ 34` or `n = 36,38`, and every reduced
denominator is a power of two (A000079). The additional source observation
that not all powers occur (A260502) is not part of this proposition.
Determinant positivity guards the inverse. -/
def WilsonConjecture : Prop :=
  (∀ n : ℕ, 1 ≤ n → ((invDet n).den = 1 ↔ n ≤ 34 ∨ n = 36 ∨ n = 38)) ∧
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, (invDet n).den = 2 ^ k

/-! ## Prime-product form of `φ(1) ⋯ φ(n)` -/

/-- Swapping a product over `k ≤ n` and prime factors `p ∣ k`:
`∏_{k=1}^{n} ∏_{p ∣ k} g(p) = ∏_{p ≤ n prime} g(p)^⌊n/p⌋`. -/
theorem prod_prod_primeFactors (n : ℕ) (g : ℕ → ℕ) :
    ∏ k ∈ range n, ∏ p ∈ (k + 1).primeFactors, g p =
      ∏ p ∈ (range (n + 1)).filter Nat.Prime, g p ^ (n / p) := by
  rw [Finset.prod_comm' (s' := fun p => (range n).filter (fun e => p ∣ e + 1))]
  · refine Finset.prod_congr rfl fun p _ => ?_
    rw [Finset.prod_const, Nat.card_multiples]
  · intro k p
    simp only [mem_range, Nat.mem_primeFactors, mem_filter]
    constructor
    · rintro ⟨hk, hp, hd, -⟩
      have hle := Nat.le_of_dvd (Nat.succ_pos k) hd
      exact ⟨⟨hk, hd⟩, by omega, hp⟩
    · rintro ⟨⟨hk, hd⟩, -, hp⟩
      exact ⟨hk, hp, hd, Nat.succ_ne_zero k⟩

/-- `φ(1) ⋯ φ(n) · ∏_{p ≤ n} p^⌊n/p⌋ = n! · ∏_{p ≤ n} (p-1)^⌊n/p⌋`
(product of `φ(k) ∏_{p∣k} p = k ∏_{p∣k} (p-1)` over `k ≤ n`). -/
theorem prod_totient_mul_primeProd (n : ℕ) :
    (∏ k ∈ range n, Nat.totient (k + 1)) *
        ∏ p ∈ (range (n + 1)).filter Nat.Prime, p ^ (n / p) =
      n.factorial * ∏ p ∈ (range (n + 1)).filter Nat.Prime, (p - 1) ^ (n / p) := by
  rw [← prod_prod_primeFactors n (fun p => p), ← prod_prod_primeFactors n (fun p => p - 1),
    ← Finset.prod_range_add_one_eq_factorial, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => Nat.totient_mul_prod_primeFactors (k + 1)

/-- Prime-product form: `1 / det M_n = n! · ∏_{p ≤ n} p^⌊n/p⌋ / ∏_{p ≤ n} (p-1)^⌊n/p⌋`. -/
theorem one_div_det_lcmRecipMatrix_eq_primeProd (n : ℕ) :
    invDet n =
      ((n.factorial * ∏ p ∈ (range (n + 1)).filter Nat.Prime, p ^ (n / p) : ℕ) : ℚ) /
        ((∏ p ∈ (range (n + 1)).filter Nat.Prime, (p - 1) ^ (n / p) : ℕ) : ℚ) := by
  have hid := prod_totient_mul_primeProd n
  have hD : (∏ k ∈ range n, (Nat.totient (k + 1) : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => by exact_mod_cast (Nat.totient_pos.2 (Nat.succ_pos k)).ne'
  have hC : (∏ p ∈ (range (n + 1)).filter Nat.Prime, (p - 1) ^ (n / p) : ℕ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun p hp =>
      pow_ne_zero _ (by have := (Finset.mem_filter.1 hp).2.two_le; omega)
  have hidQ : (∏ k ∈ range n, (Nat.totient (k + 1) : ℚ)) *
      ((∏ p ∈ (range (n + 1)).filter Nat.Prime, p ^ (n / p) : ℕ) : ℚ) =
      (n.factorial : ℚ) *
        ((∏ p ∈ (range (n + 1)).filter Nat.Prime, (p - 1) ^ (n / p) : ℕ) : ℚ) := by
    exact_mod_cast hid
  rw [invDet_eq, div_eq_div_iff hD (by exact_mod_cast hC), Nat.cast_mul]
  linear_combination (-(n.factorial : ℚ)) * hidQ

/-! ## The counterexample `n = 1807` -/

/-- Trial-division primality, valid below `43² = 1849`. -/
abbrev SmallPrime (p : ℕ) : Prop := 2 ≤ p ∧ ∀ m < 43, 2 ≤ m → m * m ≤ p → ¬ m ∣ p

/-- For `p < 1849`, `p` is prime iff it has no divisor `m ∈ [2, 42]` with `m² ≤ p`. -/
theorem prime_iff_smallPrime {p : ℕ} (hp : p < 1849) : p.Prime ↔ SmallPrime p := by
  rw [Nat.prime_def_le_sqrt]
  constructor
  · rintro ⟨h2, h⟩
    exact ⟨h2, fun m _ hm hmm => h m hm (Nat.le_sqrt.2 hmm)⟩
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hm hms => ?_⟩
    have hmm : m * m ≤ p := Nat.le_sqrt.1 hms
    have hm43 : m < 43 := by nlinarith
    exact h m hm43 hm hmm

/-- At `n = 1807` the reduced denominator of `1 / det M_n` is `2^2342 · 3`. -/
theorem den_one_div_det_lcmRecipMatrix_1807 : (invDet 1807).den = 2 ^ 2342 * 3 := by
  have hfilter : (range (1807 + 1)).filter Nat.Prime = (range 1808).filter SmallPrime :=
    Finset.filter_congr fun p hp => prime_iff_smallPrime (by simp at hp; omega)
  rw [one_div_det_lcmRecipMatrix_eq_primeProd, hfilter]
  decide +kernel

/-- **Wilson's conjecture is false.**  At `n = 1807` (Adamczewski's
counterexample, arXiv:2608.11941) the reduced denominator of `1 / det M_n` is
`2^2342 · 3`, which is divisible by `3` and hence not a power of two.
The integrality-classification clause is not needed for this refutation. -/
theorem wilsonConjecture_false : ¬ WilsonConjecture := by
  rintro ⟨-, hpow⟩
  obtain ⟨k, hk⟩ := hpow 1807 (by norm_num)
  rw [den_one_div_det_lcmRecipMatrix_1807] at hk
  have h3 : 3 ∣ 2 ^ k := hk ▸ Dvd.intro_left _ rfl
  have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h3
  omega

end Candidates.A060841Refutation
