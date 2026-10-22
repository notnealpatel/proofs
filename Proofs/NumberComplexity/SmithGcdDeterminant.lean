/-
# Smith's GCD determinant

H. J. S. Smith, *On the value of a certain arithmetical determinant*,
Proc. London Math. Soc. 7 (1875/76), 208–212, proves the GCD determinant
formula and its factor-closed version. See also C. Krattenthaler,
*Advanced Determinant Calculus: A Complement*, arXiv:math/0503507, §5,
Theorem `thm:Smith`, as a corollary of Lindström's meet-semilattice formula.

## Formalization

Rows and columns are indexed by `Fin n`, the index `i` standing for the
positive integer `i + 1`, so `1 ≤ i + 1 ≤ n`.  The statement holds for every
`n : ℕ`; at `n = 0` both sides are `1` (empty determinant, empty product), so
the paper's hypothesis `n ≥ 1` is not needed.

Proof: the factorisation `G = A * diagonal φ * Aᵀ`, where
`A i d = 1` if `d + 1 ∣ i + 1` and `0` otherwise, is Gauss's identity
`∑_{d ∣ m} φ d = m` (`Nat.sum_totient`) applied to `m = gcd (i+1) (j+1)`; the
matrix `A` is lower unitriangular, so `det A = 1`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.SmithGcdDeterminant

open Matrix

/-- The `n × n` GCD matrix `(gcd(i, j))_{1 ≤ i, j ≤ n}` over `ℤ`, with
`Fin n` index `i` standing for the integer `i + 1`. -/
def gcdMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => ((Nat.gcd (i.val + 1) (j.val + 1) : ℕ) : ℤ)

/-- The divisibility incidence matrix: entry `(i, d)` is `1` when
`d + 1 ∣ i + 1` and `0` otherwise. -/
def divMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i d => if d.val + 1 ∣ i.val + 1 then 1 else 0

example : gcdMatrix 4 = !![1, 1, 1, 1; 1, 2, 1, 2; 1, 1, 3, 1; 1, 2, 1, 4] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

example : divMatrix 3 = !![1, 0, 0; 1, 1, 0; 1, 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

example : (gcdMatrix 3).det = 2 := by
  rw [Matrix.det_fin_three]; decide

/-- Gauss's identity restricted to a range: for `0 < g ≤ n`,
`∑_{k < n, k + 1 ∣ g} φ (k + 1) = g`. -/
theorem sum_range_totient_of_dvd {g n : ℕ} (hg : 0 < g) (hgn : g ≤ n) :
    ∑ k ∈ Finset.range n, (if k + 1 ∣ g then (Nat.totient (k + 1) : ℤ) else 0) = g := by
  rw [← Finset.sum_filter]
  have key : ∑ k ∈ (Finset.range n).filter (fun k => k + 1 ∣ g), (Nat.totient (k + 1) : ℤ)
      = ∑ m ∈ g.divisors, (Nat.totient m : ℤ) := by
    apply Finset.sum_nbij' (· + 1) (· - 1)
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      simp only [Nat.mem_divisors]
      exact ⟨hk.2, hg.ne'⟩
    · intro m hm
      simp only [Nat.mem_divisors] at hm
      have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hm.1 hg
      have hmg : m ≤ g := Nat.le_of_dvd hg hm.1
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [Nat.sub_add_cancel hm0]; exact hm.1
    · intro k _; simp
    · intro m hm
      simp only [Nat.mem_divisors] at hm
      have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hm.1 hg
      omega
    · intro k _; rfl
  rw [key]
  exact_mod_cast Nat.sum_totient g

/-- The factorisation `gcdMatrix n = A * diagonal φ * Aᵀ` with `A = divMatrix n`. -/
theorem gcdMatrix_eq_mul (n : ℕ) :
    gcdMatrix n = divMatrix n * diagonal (fun d : Fin n => (Nat.totient (d.val + 1) : ℤ)) *
      (divMatrix n)ᵀ := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, divMatrix, gcdMatrix, Matrix.of_apply]
  have hg : 0 < Nat.gcd (i.val + 1) (j.val + 1) := Nat.gcd_pos_of_pos_left _ (Nat.succ_pos _)
  have hgn : Nat.gcd (i.val + 1) (j.val + 1) ≤ n :=
    (Nat.gcd_le_left _ (Nat.succ_pos _)).trans i.isLt
  rw [← sum_range_totient_of_dvd hg hgn, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [Nat.dvd_gcd_iff]
  by_cases h1 : d.val + 1 ∣ i.val + 1 <;> by_cases h2 : d.val + 1 ∣ j.val + 1 <;> simp [h1, h2]

/-- The divisibility matrix is lower unitriangular, so its determinant is `1`. -/
theorem det_divMatrix (n : ℕ) : (divMatrix n).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [divMatrix]
  · intro i d hlt
    have hlt' : i < d := hlt
    simp only [divMatrix, Matrix.of_apply, ite_eq_right_iff, one_ne_zero, imp_false]
    intro hdvd
    have := Nat.le_of_dvd (Nat.succ_pos _) hdvd
    have : i.val < d.val := hlt'
    omega

/-- **Smith's GCD determinant** (Smith 1875; Krattenthaler, arXiv:math/0503507,
Theorem `thm:Smith`): for every `n`, `det_{1 ≤ i, j ≤ n} gcd(i, j) = ∏_{i=1}^n φ(i)`,
stated over `ℤ` with `Fin n` index `i` standing for `i + 1`. -/
theorem smith_gcd_det (n : ℕ) :
    (Matrix.of fun i j : Fin n => ((Nat.gcd (i.val + 1) (j.val + 1) : ℕ) : ℤ)).det =
      ∏ i : Fin n, ((Nat.totient (i.val + 1) : ℕ) : ℤ) := by
  change (gcdMatrix n).det = _
  rw [gcdMatrix_eq_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_divMatrix,
    Matrix.det_diagonal]
  ring

/-! ## Smith's factor-closed version

Smith's original theorem: for any finite set `S` of positive integers closed
under taking divisors, `det_{x, y ∈ S} gcd(x, y) = ∏_{x ∈ S} φ(x)`.  A finite
divisor-closed `S ⊆ ℕ` automatically omits `0` (every natural number divides
`0`), so no positivity hypothesis is needed. -/

/-- A finite divisor-closed set of naturals does not contain `0`. -/
theorem zero_not_mem_of_divisor_closed (S : Finset ℕ)
    (hS : ∀ x ∈ S, ∀ d, d ∣ x → d ∈ S) : 0 ∉ S := by
  intro h0
  have hmem : S.sup id + 1 ∈ S := hS 0 h0 _ (dvd_zero _)
  have hle : S.sup id + 1 ≤ S.sup id := Finset.le_sup (f := id) hmem
  omega

/-- **Smith's GCD determinant, factor-closed version** (Smith 1875; mentioned in
Krattenthaler, arXiv:math/0503507, before Theorem `thm:Smith`): for a finite set
`S` of naturals closed under divisors, `det_{x, y ∈ S} gcd(x, y) = ∏_{x ∈ S} φ(x)`. -/
theorem smith_gcd_det_of_divisor_closed (S : Finset ℕ)
    (hS : ∀ x ∈ S, ∀ d, d ∣ x → d ∈ S) :
    (Matrix.of fun x y : S => ((Nat.gcd x y : ℕ) : ℤ)).det =
      ∏ x : S, ((Nat.totient x : ℕ) : ℤ) := by
  have h0 : 0 ∉ S := zero_not_mem_of_divisor_closed S hS
  have hpos : ∀ x : S, 0 < (x : ℕ) := fun x =>
    Nat.pos_of_ne_zero fun hx => h0 (hx ▸ x.2)
  let A : Matrix S S ℤ := Matrix.of fun x d => if (d : ℕ) ∣ (x : ℕ) then 1 else 0
  have hfac : (Matrix.of fun x y : S => ((Nat.gcd x y : ℕ) : ℤ)) =
      A * diagonal (fun d : S => (Nat.totient d : ℤ)) * Aᵀ := by
    ext x y
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, A, Matrix.of_apply]
    have hg : 0 < Nat.gcd x y := Nat.gcd_pos_of_pos_left _ (hpos x)
    have hdiv : S.filter (· ∣ Nat.gcd x y) = (Nat.gcd x y).divisors := by
      ext m
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · intro hm; exact ⟨hm.2, hg.ne'⟩
      · intro hm
        exact ⟨hS x x.2 m (hm.1.trans (Nat.gcd_dvd_left _ _)), hm.1⟩
    have hsum : ∑ d : S, (if (d : ℕ) ∣ Nat.gcd x y then (Nat.totient d : ℤ) else 0) =
        Nat.gcd x y := by
      rw [Finset.sum_coe_sort S (fun d => if d ∣ Nat.gcd x y then (Nat.totient d : ℤ) else 0),
        ← Finset.sum_filter, hdiv]
      exact_mod_cast Nat.sum_totient _
    rw [← hsum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [Nat.dvd_gcd_iff]
    by_cases h1 : (d : ℕ) ∣ x <;> by_cases h2 : (d : ℕ) ∣ y <;> simp [h1, h2]
  have hA : A.det = 1 := by
    rw [Matrix.det_of_lowerTriangular]
    · simp [A]
    · intro x d hlt
      have hlt' : x < d := hlt
      simp only [A, Matrix.of_apply, ite_eq_right_iff, one_ne_zero, imp_false]
      intro hdvd
      have hle := Nat.le_of_dvd (hpos x) hdvd
      have hxd : (x : ℕ) < d := hlt'
      omega
  rw [hfac, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hA, Matrix.det_diagonal]
  ring

/-- Non-vacuity of the factor-closed version: `S = {1, 2, 4}` is divisor-closed. -/
example : ∀ x ∈ ({1, 2, 4} : Finset ℕ), ∀ d, d ∣ x → d ∈ ({1, 2, 4} : Finset ℕ) := by
  intro x hx d hd
  have hx' : x = 1 ∨ x = 2 ∨ x = 4 := by simpa using hx
  have hdx : d ≤ 4 := by
    rcases hx' with rfl | rfl | rfl <;> exact (Nat.le_of_dvd (by norm_num) hd).trans (by norm_num)
  interval_cases d <;> rcases hx' with rfl | rfl | rfl <;> simp_all

end Candidates.SmithGcdDeterminant
