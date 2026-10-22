/-
# A267999 — gcd(n, 2^n - 2) = 1 forces n^3 ∣ Σ_{k<n} k^n

OEIS A267999: for `n > 1`, `gcd(n,2^n-2) = 1` implies
`n³ ∣ ∑_{k=1}^{n-1} k^n` (membership in A121707).

1. `gcd(n, 2^n - 2) = 1` forces n odd and `gcd(n, 2^(n-1) - 1) = 1`.
2. Doubling `x ↦ 2x` permutes `ZMod n`, so `S = Σ_x x^(n-1)` satisfies
   `(2^(n-1) - 1) S = 0` in `ZMod n`; the factor is a unit, hence `n ∣ S`.
3. For odd n ≥ 3 the binomial theorem gives
   `(n - k)^n + k^n ≡ n^2 k^(n-1) (mod n^3)` (the `C(n,2) n^2` term dies
   because `n ∣ C(n,2)` for odd n).  Summing over `k = 0..n` and reflecting,
   `2 Σ_{k ≤ n} k^n ≡ n^2 Σ_{k ≤ n} k^(n-1) ≡ 0 (mod n^3)`; since n is odd,
   `n^3 ∣ Σ_{k ≤ n} k^n`, and dropping `n^n` gives the claim.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A267999GcdDividesSum

/-! ## Definitions -/

/-- Membership in A267999: `n > 1` and `gcd(n, 2^n - 2) = 1`.  The natural
subtraction `2 ^ n - 2` is exact here because `1 < n` gives `2 ≤ 2 ^ n`. -/
def IsA267999 (n : ℕ) : Prop := 1 < n ∧ Nat.gcd n (2 ^ n - 2) = 1

instance (n : ℕ) : Decidable (IsA267999 n) := by
  unfold IsA267999; infer_instance

/-- Membership in A121707: `n > 1` and `n^3 ∣ Σ_{k=1}^{n-1} k^n`. -/
def IsA121707 (n : ℕ) : Prop := 1 < n ∧ n ^ 3 ∣ ∑ k ∈ Finset.Ico 1 n, k ^ n

instance (n : ℕ) : Decidable (IsA121707 n) := by
  unfold IsA121707; infer_instance

/-! ## Examples -/

-- The first three terms of A267999 below 80 are exactly 35, 55, 77.
example : (Finset.range 80).filter IsA267999 = {35, 55, 77} := by decide

-- The first three terms of A121707 below 80 are exactly 35, 55, 77.
example : (Finset.range 80).filter IsA121707 = {35, 55, 77} := by decide

-- Satisfiability of the hypotheses: 35 is a term of A267999.
example : IsA267999 35 := by decide

/-! ## Helper lemmas -/

/-- If `u` is a unit of `ZMod n` with `u^e - 1` a unit, then `Σ_x x^e = 0`
in `ZMod n` (the sum is invariant under `x ↦ u x`). -/
theorem sum_pow_eq_zero_of_unit (n : ℕ) [NeZero n] (e : ℕ) (u : (ZMod n)ˣ)
    (hu : IsUnit ((u : ZMod n) ^ e - 1)) : ∑ x : ZMod n, x ^ e = 0 := by
  have hperm : ∑ x : ZMod n, x ^ e = ∑ x : ZMod n, ((u : ZMod n) * x) ^ e :=
    (Equiv.sum_comp (Units.mulLeft u) (fun x => x ^ e)).symm
  simp_rw [mul_pow, ← Finset.mul_sum] at hperm
  have hzero : ((u : ZMod n) ^ e - 1) * ∑ x : ZMod n, x ^ e = 0 := by
    rw [sub_mul, one_mul, ← hperm, sub_self]
  exact (hu.mul_right_eq_zero).mp hzero

/-- Summing `f (k : ZMod n)` over `k < n` is summing `f` over all of `ZMod n`. -/
theorem sum_range_natCast_eq (n : ℕ) [NeZero n] (f : ZMod n → ZMod n) :
    ∑ k ∈ Finset.range n, f (k : ZMod n) = ∑ x : ZMod n, f x := by
  rw [← Finset.sum_image (f := f) (g := (Nat.cast : ℕ → ZMod n))]
  · congr 1
    ext x
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_univ, iff_true]
    exact ⟨x.val, ZMod.val_lt x, ZMod.natCast_zmod_val x⟩
  · intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    rw [← ZMod.val_natCast_of_lt ha, ← ZMod.val_natCast_of_lt hb, hab]

/-- For odd `n > 1` with `gcd(2^(n-1) - 1, n) = 1`, `n ∣ Σ_{k<n} k^(n-1)`. -/
theorem dvd_sum_range_pow_pred (n : ℕ) (hn : 1 < n) (hodd : Odd n)
    (hcop : Nat.Coprime (2 ^ (n - 1) - 1) n) :
    n ∣ ∑ k ∈ Finset.range n, k ^ (n - 1) := by
  haveI : NeZero n := ⟨by omega⟩
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [sum_range_natCast_eq n (fun x => x ^ (n - 1))]
  apply sum_pow_eq_zero_of_unit n (n - 1) (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr hodd))
  rw [ZMod.coe_unitOfCoprime]
  have hle : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
  have hcast : ((2 ^ (n - 1) - 1 : ℕ) : ZMod n) = ((2 : ℕ) : ZMod n) ^ (n - 1) - 1 := by
    push_cast [Nat.cast_sub hle]
    ring
  rw [← hcast]
  exact (ZMod.isUnit_iff_coprime _ n).mpr hcop

/-- Binomial expansion to second order: `x^3` divides
`(x + y)^(M+3) - (y^(M+3) + (M+3) x y^(M+2) + C(M+3,2) x^2 y^(M+1))`. -/
theorem pow_three_dvd_add_pow_sub {R : Type*} [CommRing R] (x y : R) (M : ℕ) :
    x ^ 3 ∣ (x + y) ^ (M + 3) - (y ^ (M + 3) + x * y ^ (M + 2) * ((M + 3 : ℕ) : R)
      + x ^ 2 * y ^ (M + 1) * (((M + 3).choose 2 : ℕ) : R)) := by
  rw [add_pow, Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
  refine ⟨∑ i ∈ Finset.range (M + 1),
    x ^ i * y ^ (M + 3 - (i + 3)) * (((M + 3).choose (i + 3) : ℕ) : R), ?_⟩
  rw [Finset.mul_sum]
  have hterm : ∀ i ∈ Finset.range (M + 1),
      x ^ (i + 1 + 1 + 1) * y ^ (M + 3 - (i + 1 + 1 + 1)) * (((M + 3).choose (i + 1 + 1 + 1) : ℕ) : R)
        = x ^ 3 * (x ^ i * y ^ (M + 3 - (i + 3)) * (((M + 3).choose (i + 3) : ℕ) : R)) := by
    intro i _
    ring
  rw [Finset.sum_congr rfl hterm]
  simp only [zero_add, pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one, pow_one,
    Nat.choose_one_right, Nat.sub_zero]
  have h2 : M + 3 - (1 + 1) = M + 1 := by omega
  have h1 : M + 3 - 1 = M + 2 := by omega
  rw [h2, h1]
  ring

/-- For odd `N`, `N ∣ C(N, 2)`. -/
theorem dvd_choose_two_of_odd (N : ℕ) (hodd : Odd N) : N ∣ N.choose 2 := by
  obtain ⟨a, rfl⟩ := hodd
  refine ⟨a, ?_⟩
  rw [Nat.choose_two_right]
  have h : (2 * a + 1) * (2 * a + 1 - 1) = 2 * ((2 * a + 1) * a) := by
    rw [Nat.add_sub_cancel]; ring
  rw [h, Nat.mul_div_cancel_left _ (by norm_num)]

/-- For odd `N ≥ 3` and any integer `k`,
`(N - k)^N + k^N ≡ N^2 k^(N-1) (mod N^3)`. -/
theorem pow_three_dvd_sub_pow_add_pow (N : ℕ) (hodd : Odd N) (hN : 3 ≤ N) (k : ℤ) :
    (N : ℤ) ^ 3 ∣ ((N : ℤ) - k) ^ N + k ^ N - (N : ℤ) ^ 2 * k ^ (N - 1) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 3 := ⟨N - 3, by omega⟩
  have hbin := pow_three_dvd_add_pow_sub ((M + 3 : ℕ) : ℤ) (-k) M
  obtain ⟨c, hc⟩ := dvd_choose_two_of_odd (M + 3) hodd
  have hodd' : Odd (M + 3) := hodd
  have heven : Even (M + 2) := by
    obtain ⟨a, ha⟩ := hodd'
    exact ⟨a, by omega⟩
  have hsplit : (((M + 3 : ℕ) : ℤ) - k) ^ (M + 3) + k ^ (M + 3)
      - ((M + 3 : ℕ) : ℤ) ^ 2 * k ^ (M + 3 - 1)
      = ((((M + 3 : ℕ) : ℤ) + -k) ^ (M + 3) - ((-k) ^ (M + 3)
          + ((M + 3 : ℕ) : ℤ) * (-k) ^ (M + 2) * ((M + 3 : ℕ) : ℤ)
          + ((M + 3 : ℕ) : ℤ) ^ 2 * (-k) ^ (M + 1) * (((M + 3).choose 2 : ℕ) : ℤ)))
        + ((M + 3 : ℕ) : ℤ) ^ 3 * ((-k) ^ (M + 1) * (c : ℤ)) := by
    rw [hodd'.neg_pow, heven.neg_pow, hc, show M + 3 - 1 = M + 2 by omega]
    push_cast
    ring
  rw [hsplit]
  exact dvd_add hbin (dvd_mul_right _ _)

/-- `gcd(n, 2^n - 2) = 1` with `n > 1` forces `n` odd and
`gcd(2^(n-1) - 1, n) = 1`. -/
theorem odd_and_coprime_of_gcd_eq_one (n : ℕ) (hn : 1 < n) (h : Nat.gcd n (2 ^ n - 2) = 1) :
    Odd n ∧ Nat.Coprime (2 ^ (n - 1) - 1) n := by
  have hfac : 2 ^ n - 2 = 2 * (2 ^ (n - 1) - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    rw [Nat.add_sub_cancel, pow_succ]
    omega
  have hcop : Nat.Coprime n (2 * (2 ^ (n - 1) - 1)) := by
    rw [← hfac]
    exact h
  refine ⟨?_, (Nat.Coprime.coprime_dvd_right (dvd_mul_left _ 2) hcop).symm⟩
  rw [← Nat.coprime_two_right]
  exact Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 _) hcop

/-! ## The conjecture -/

/-- The inclusion conjectured in OEIS A267999 (unattributed): for
`n > 1` with `gcd(n,2^n-2) = 1`, `n³` divides `∑_{k=1}^{n-1} k^n`. -/
theorem cube_dvd_sum_Ico_pow (n : ℕ) (hn : 1 < n) (h : Nat.gcd n (2 ^ n - 2) = 1) :
    n ^ 3 ∣ ∑ k ∈ Finset.Ico 1 n, k ^ n := by
  obtain ⟨hodd, hcop⟩ := odd_and_coprime_of_gcd_eq_one n hn h
  have hn3 : 3 ≤ n := by
    obtain ⟨a, ha⟩ := hodd
    omega
  have hS : n ∣ ∑ k ∈ Finset.range n, k ^ (n - 1) := dvd_sum_range_pow_pred n hn hodd hcop
  set N : ℤ := (n : ℤ) with hN
  set U : ℤ := ∑ k ∈ Finset.range (n + 1), (k : ℤ) ^ n with hUdef
  have hrefl : ∑ k ∈ Finset.range (n + 1), (N - k) ^ n = U := by
    rw [hUdef, ← Finset.sum_range_reflect (fun j : ℕ => (j : ℤ) ^ n) (n + 1)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [hN, show n + 1 - 1 - j = n - j by omega, Nat.cast_sub hjn]
  have hterms : N ^ 3 ∣ ∑ k ∈ Finset.range (n + 1),
      ((N - k) ^ n + (k : ℤ) ^ n - N ^ 2 * (k : ℤ) ^ (n - 1)) :=
    Finset.dvd_sum fun k _ => pow_three_dvd_sub_pow_add_pow n hodd hn3 k
  have hSint : N ∣ ∑ k ∈ Finset.range (n + 1), (k : ℤ) ^ (n - 1) := by
    rw [Finset.sum_range_succ]
    refine dvd_add ?_ (dvd_pow_self _ (by omega))
    have hcast := Int.natCast_dvd_natCast.mpr hS
    push_cast at hcast
    exact hcast
  have hsq : N ^ 3 ∣ N ^ 2 * ∑ k ∈ Finset.range (n + 1), (k : ℤ) ^ (n - 1) := by
    rw [pow_succ]
    exact mul_dvd_mul_left _ hSint
  have h2U : N ^ 3 ∣ U * 2 := by
    have hsplit : U * 2 = ∑ k ∈ Finset.range (n + 1),
        ((N - k) ^ n + (k : ℤ) ^ n - N ^ 2 * (k : ℤ) ^ (n - 1))
        + N ^ 2 * ∑ k ∈ Finset.range (n + 1), (k : ℤ) ^ (n - 1) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hrefl, Finset.mul_sum]
      ring
    rw [hsplit]
    exact dvd_add hterms hsq
  have hcop2 : IsCoprime (N ^ 3) 2 := by
    rw [hN, show ((n : ℤ) ^ 3) = ((n ^ 3 : ℕ) : ℤ) by push_cast; rfl,
      show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_left 3 (Nat.coprime_two_right.mpr hodd)
  have hU : N ^ 3 ∣ U := hcop2.dvd_of_dvd_mul_right h2U
  have hUeq : U = ((∑ k ∈ Finset.Ico 1 n, k ^ n : ℕ) : ℤ) + N ^ n := by
    rw [hUdef, Finset.sum_range_succ, Finset.range_eq_Ico,
      Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < n)]
    push_cast
    simp [hN, zero_pow (by omega : n ≠ 0)]
  rw [hUeq] at hU
  have hT : N ^ 3 ∣ ((∑ k ∈ Finset.Ico 1 n, k ^ n : ℕ) : ℤ) :=
    (dvd_add_left (pow_dvd_pow N hn3)).mp hU
  rw [hN] at hT
  exact_mod_cast hT

/-- Set form of the conjecture: every term of A267999 is a term of A121707. -/
theorem a267999_subset_a121707 : {n | IsA267999 n} ⊆ {n | IsA121707 n} :=
  fun n hn => ⟨hn.1, cube_dvd_sum_Ico_pow n hn.1 hn.2⟩

end Candidates.A267999GcdDividesSum
