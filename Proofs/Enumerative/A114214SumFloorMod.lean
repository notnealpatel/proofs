/-
# Diagonal sums of A114213 (A114214)

Source: Georg Fischer's OEIS A114214 comment (Nov 28 2022).
For every `n`, the diagonal sum is `A007306(floor(n/2)+1)`, equivalently
`stern(2 floor(n/2)+1)`. The triangle uses Jeffrey Shallit's corrected
formula (May 18 2016).
Reference: Shallit–Spiegelhofer, arXiv:1710.06203, deriving
`d(2n)=d(2n+1)=s(2n+1)` by reduction modulo 2 and Carlitz's identity.
Here Lucas's theorem and Vandermonde reduce the sum to that identity.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A114214SumFloorMod

open Finset

/-! ## Definitions

All definitions mirror the OEIS entries; nothing is imported from the repo.

* `stern` is A002487 (Stern's diatomic sequence) by its defining recurrence.
* `a007306` is A007306 via the entry formula `a(0) = 1`,
  `a(n) = A002487(n-1) + A002487(n)` for `n > 0` (written without `Nat`
  subtraction by shifting the index).
* `T n k` is the integer inside the `mod 2` of A114213, i.e.
  `Sum_{j=0..n-k} C(k,j) C(n-k,j) (1+(-1)^j)/2`, with the weight
  `(1+(-1)^j)/2` realised as a filter to even `j`; `T_eq_weighted_sum` proves
  the two forms agree over `ℤ`.
* `d n` is the A114214 formula `Sum_{k=0..floor(n/2)} (T(n-k,k) mod 2)`; the
  `Nat` subtraction `n - k` is on its non-truncated branch since `k ≤ n/2`. -/

/-- Stern's diatomic sequence (OEIS A002487): `s(0) = 0`, `s(1) = 1`,
`s(2m) = s(m)`, `s(2m+1) = s(m) + s(m+1)`. -/
def stern : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    if (n + 2) % 2 = 0 then stern ((n + 2) / 2)
    else stern ((n + 2) / 2) + stern ((n + 2) / 2 + 1)
decreasing_by all_goals omega

/-- OEIS A007306 (denominators of Farey tree fractions), via the entry formula
`a(0) = 1` and `a(n) = A002487(n-1) + A002487(n)` for `n > 0`. -/
def a007306 : ℕ → ℕ
  | 0 => 1
  | n + 1 => stern n + stern (n + 1)

/-- The (pre-reduction) entry of Barry's generalized Pascal triangle A114213:
`T(n, k) = Sum_{j=0..n-k, j even} C(k, j) * C(n-k, j)`; A114213 lists
`T(n, k) mod 2`. -/
def T (n k : ℕ) : ℕ :=
  ∑ j ∈ (range (n - k + 1)).filter Even, k.choose j * (n - k).choose j

/-- OEIS A114214, diagonal sums of A114213:
`d(n) = Sum_{k=0..floor(n/2)} (T(n-k, k) mod 2)`. -/
def d (n : ℕ) : ℕ := ∑ k ∈ range (n / 2 + 1), T (n - k) k % 2

/-! ## Listed terms -/

example : (List.range 17).map stern = [0, 1, 1, 2, 1, 3, 2, 3, 1, 4, 3, 5, 2, 5, 3, 4, 1] := by
  decide +kernel

example : (List.range 17).map a007306 = [1, 1, 2, 3, 3, 4, 5, 5, 4, 5, 7, 8, 7, 7, 8, 7, 5] := by
  decide +kernel

/-- First six rows of A114213 (`T(n, k) mod 2`, `0 ≤ k ≤ n ≤ 5`) as listed. -/
example : ((List.range 6).flatMap fun n => (List.range (n + 1)).map fun k => T n k % 2)
    = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1] := by
  decide

example : (List.range 20).map d = [1, 1, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 5, 4, 4, 5, 5, 7, 7] := by
  decide

/-- Fidelity bridge: the even-filter form of `T` equals the entry's weighted
form `Sum_{j=0..n-k} C(k,j) C(n-k,j) (1+(-1)^j)/2` (integer division in `ℤ`). -/
theorem T_eq_weighted_sum (n k : ℕ) :
    (T n k : ℤ) = ∑ j ∈ range (n - k + 1),
      (k.choose j : ℤ) * ((n - k).choose j : ℤ) * ((1 + (-1) ^ j) / 2) := by
  rw [T, sum_filter, Nat.cast_sum]
  refine sum_congr rfl fun j _ => ?_
  rcases Nat.even_or_odd j with hj | hj
  · rw [if_pos hj, hj.neg_one_pow]
    push_cast
    norm_num
  · rw [if_neg (Nat.not_even_iff_odd.mpr hj), hj.neg_one_pow]
    norm_num

/-! ## Lucas's theorem mod 2 -/

/-- Lucas mod 2, even lower index: `C(n, 2b) ≡ C(n/2, b) (mod 2)`. -/
theorem choose_two_mul_mod (n b : ℕ) : n.choose (2 * b) % 2 = (n / 2).choose b % 2 := by
  have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat n (2 * b) 2 ⟨Nat.prime_two⟩
  simp only [Nat.mul_mod_right, Nat.choose_zero_right, one_mul] at h
  rw [Nat.mul_div_cancel_left b (by norm_num)] at h
  exact h

/-- Lucas mod 2, odd lower index: `C(n, 2b+1) ≡ (n mod 2) * C(n/2, b) (mod 2)`. -/
theorem choose_two_mul_add_one_mod (n b : ℕ) :
    n.choose (2 * b + 1) % 2 = (n % 2) * (n / 2).choose b % 2 := by
  have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat n (2 * b + 1) 2 ⟨Nat.prime_two⟩
  have h1 : (2 * b + 1) % 2 = 1 := by omega
  have h2 : (2 * b + 1) / 2 = b := by omega
  rw [h1, h2, Nat.choose_one_right] at h
  exact h


/-! ## Parity splitting and Carlitz's identity -/

/-- Split a sum over `[0, 2B)` into its even-index and odd-index parts. -/
theorem sum_range_two_mul (f : ℕ → ℕ) (B : ℕ) :
    ∑ i ∈ range (2 * B), f i = ∑ r ∈ range B, f (2 * r) + ∑ r ∈ range B, f (2 * r + 1) := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [show 2 * (B + 1) = 2 * B + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, sum_range_succ]
    ring

/-- Barry's sum `g(M) = Sum_{i=0..M} (C(M-i, i) mod 2)` (A007306 entry:
`A007306(n+1) = Sum_{k=0..n} C(2n-k, k) mod 2`). -/
def g (M : ℕ) : ℕ := ∑ i ∈ Finset.range (M + 1), (M - i).choose i % 2

/-- `g M` may be summed over any range `[0, B)` with `M/2 < B`, since
`C(M-i, i) = 0` once `M < 2i`. -/
theorem g_eq_sum (M B : ℕ) (hB : M / 2 + 1 ≤ B) :
    g M = ∑ i ∈ range B, (M - i).choose i % 2 := by
  have hz : ∀ i ≥ M / 2 + 1, (M - i).choose i % 2 = 0 := by
    intro i hi
    rw [Nat.choose_eq_zero_of_lt (by omega)]
  rw [g, eventually_constant_sum hz hB, eventually_constant_sum hz (by omega)]

/-- Lucas mod 2 recurrence: `g(2L+1) = g(L)`. -/
theorem g_two_mul_add_one (L : ℕ) : g (2 * L + 1) = g L := by
  rw [g_eq_sum (2 * L + 1) (2 * (L + 1)) (by omega), sum_range_two_mul,
    g_eq_sum L (L + 1) (by omega)]
  have h1 : ∀ r ∈ range (L + 1), (2 * L + 1 - 2 * r).choose (2 * r) % 2 = (L - r).choose r % 2 := by
    intro r hr
    rw [mem_range] at hr
    rw [choose_two_mul_mod, show (2 * L + 1 - 2 * r) / 2 = L - r by omega]
  have h2 : ∀ r ∈ range (L + 1), (2 * L + 1 - (2 * r + 1)).choose (2 * r + 1) % 2 = 0 := by
    intro r hr
    rw [choose_two_mul_add_one_mod, show (2 * L + 1 - (2 * r + 1)) % 2 = 0 by omega, zero_mul,
      Nat.zero_mod]
  rw [sum_congr rfl h1, sum_congr rfl h2, sum_const_zero, add_zero]

/-- Lucas mod 2 recurrence: `g(2L+2) = g(L+1) + g(L)`. -/
theorem g_two_mul_add_two (L : ℕ) : g (2 * L + 2) = g (L + 1) + g L := by
  rw [g_eq_sum (2 * L + 2) (2 * (L + 2)) (by omega), sum_range_two_mul,
    g_eq_sum (L + 1) (L + 2) (by omega), g_eq_sum L (L + 2) (by omega)]
  have h1 : ∀ r ∈ range (L + 2),
      (2 * L + 2 - 2 * r).choose (2 * r) % 2 = (L + 1 - r).choose r % 2 := by
    intro r _
    rw [choose_two_mul_mod, show (2 * L + 2 - 2 * r) / 2 = L + 1 - r by omega]
  have h2 : ∀ r ∈ range (L + 2),
      (2 * L + 2 - (2 * r + 1)).choose (2 * r + 1) % 2 = (L - r).choose r % 2 := by
    intro r _
    rw [choose_two_mul_add_one_mod, show (2 * L + 2 - (2 * r + 1)) / 2 = L - r by omega]
    rcases Nat.lt_or_ge L r with h | h
    · rw [show L - r = 0 by omega, Nat.choose_eq_zero_of_lt (by omega : 0 < r)]
      simp
    · rw [show (2 * L + 2 - (2 * r + 1)) % 2 = 1 by omega, one_mul]
  rw [sum_congr rfl h1, sum_congr rfl h2]

/-- Stern recurrence `s(2n) = s(n)`. -/
theorem stern_two_mul (n : ℕ) : stern (2 * n) = stern n := by
  rcases n with _ | n
  · rfl
  · rw [show 2 * (n + 1) = 2 * n + 2 by ring, stern, if_pos (by omega),
      show (2 * n + 2) / 2 = n + 1 by omega]

/-- Stern recurrence `s(2n+1) = s(n) + s(n+1)`. -/
theorem stern_two_mul_add_one (n : ℕ) : stern (2 * n + 1) = stern n + stern (n + 1) := by
  rcases n with _ | n
  · simp [stern]
  · rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring, stern, if_neg (by omega),
      show (2 * n + 1 + 2) / 2 = n + 1 by omega]

/-- Carlitz's identity: `Sum_{i=0..M} (C(M-i, i) mod 2) = s(M+1)`. -/
theorem g_eq_stern (M : ℕ) : g M = stern (M + 1) := by
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    rcases Nat.even_or_odd' M with ⟨L, rfl | rfl⟩
    · rcases L with _ | L
      · decide +kernel
      · rw [show 2 * (L + 1) = 2 * L + 2 by ring, g_two_mul_add_two, ih (L + 1) (by omega),
          ih L (by omega), show 2 * L + 2 + 1 = 2 * (L + 1) + 1 by ring, stern_two_mul_add_one,
          add_comm]
    · rw [g_two_mul_add_one, ih L (by omega), show 2 * L + 1 + 1 = 2 * (L + 1) by ring,
        stern_two_mul]


/-! ## The even-index sum mod 2 -/

/-- Vandermonde in the form `Sum_{t<B} C(a,t) C(b,t) = C(a+b, a)` for any `B > b`. -/
theorem vandermonde_range (a b B : ℕ) (hB : b < B) :
    ∑ t ∈ range B, a.choose t * b.choose t = (a + b).choose a := by
  have hz1 : ∀ t ≥ B, a.choose t * b.choose t = 0 := by
    intro t ht
    rw [Nat.choose_eq_zero_of_lt (by omega : b < t), mul_zero]
  have hz2 : ∀ t ≥ a + 1, a.choose t * b.choose t = 0 := by
    intro t ht
    rw [Nat.choose_eq_zero_of_lt (by omega : a < t), zero_mul]
  rw [← eventually_constant_sum hz1 (le_max_left B (a + 1)),
    eventually_constant_sum hz2 (le_max_right B (a + 1)), Nat.add_choose_eq,
    Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a.choose i * b.choose j)]
  rw [← sum_range_reflect (fun t => a.choose t * b.choose t) (a + 1)]
  refine sum_congr rfl fun i hi => ?_
  rw [mem_range] at hi
  rw [show a + 1 - 1 - i = a - i by omega, Nat.choose_symm (by omega)]

/-- `Sum_{j ≤ m, j even} C(k,j) C(m,j) ≡ C(k/2 + m/2, k/2) (mod 2)`
(Lucas mod 2 on each term, then Vandermonde). -/
theorem evenSum_mod (k m : ℕ) :
    (∑ j ∈ (range (m + 1)).filter Even, k.choose j * m.choose j) % 2
      = (k / 2 + m / 2).choose (k / 2) % 2 := by
  have hz : ∀ j ≥ m + 1, (if Even j then k.choose j * m.choose j else 0) = 0 := by
    intro j hj
    rw [Nat.choose_eq_zero_of_lt (by omega : m < j), mul_zero, ite_self]
  rw [sum_filter, ← eventually_constant_sum hz (by omega : m + 1 ≤ 2 * (m + 1)),
    sum_range_two_mul]
  have hodd : ∀ r ∈ range (m + 1),
      (if Even (2 * r + 1) then k.choose (2 * r + 1) * m.choose (2 * r + 1) else 0) = 0 := by
    intro r _
    rw [if_neg (by simp)]
  have heven : ∀ r ∈ range (m + 1),
      (if Even (2 * r) then k.choose (2 * r) * m.choose (2 * r) else 0)
        = k.choose (2 * r) * m.choose (2 * r) := by
    intro r _
    rw [if_pos (even_two_mul r)]
  rw [sum_congr rfl hodd, sum_const_zero, add_zero, sum_congr rfl heven,
    ← vandermonde_range (k / 2) (m / 2) (m + 1) (by omega)]
  conv_lhs => rw [sum_nat_mod]
  conv_rhs => rw [sum_nat_mod]
  congr 1
  refine sum_congr rfl fun r _ => ?_
  rw [Nat.mul_mod, choose_two_mul_mod, choose_two_mul_mod, ← Nat.mul_mod]

/-- Diagonal entries mod 2: for `k ≤ n/2`, `T(n-k, k) ≡ C(2⌊n/2⌋ - k, k) (mod 2)`. -/
theorem T_sub_mod (n k : ℕ) (hk : k ≤ n / 2) :
    T (n - k) k % 2 = (2 * (n / 2) - k).choose k % 2 := by
  have hm : n - k - k = n - 2 * k := by omega
  rw [T, hm, evenSum_mod, show (n - 2 * k) / 2 = n / 2 - k by omega]
  rcases Nat.even_or_odd' k with ⟨r, rfl | rfl⟩
  · rw [choose_two_mul_mod, show 2 * r / 2 = r by omega,
      show (2 * (n / 2) - 2 * r) / 2 = r + (n / 2 - 2 * r) by omega]
  · rw [choose_two_mul_add_one_mod, show (2 * r + 1) / 2 = r by omega,
      show (2 * (n / 2) - (2 * r + 1)) / 2 = r + (n / 2 - (2 * r + 1)) by omega,
      show (2 * (n / 2) - (2 * r + 1)) % 2 = 1 by omega, one_mul]

/-! ## The conjecture -/

/-- `d(n) = g(2⌊n/2⌋)`, i.e. A114214 agrees with Barry's binomial-sum form. -/
theorem d_eq_g (n : ℕ) : d n = g (2 * (n / 2)) := by
  rw [g_eq_sum (2 * (n / 2)) (n / 2 + 1) (by omega), d]
  refine sum_congr rfl fun k hk => ?_
  rw [mem_range] at hk
  rw [T_sub_mod n k (by omega)]

/-- The diagonal sum equals `s(2 floor(n/2)+1)` (Shallit–Spiegelhofer,
arXiv:1710.06203). -/
theorem d_eq_stern (n : ℕ) : d n = stern (2 * (n / 2) + 1) := by
  rw [d_eq_g, g_eq_stern]


/-- Fischer's identity: the diagonal sum of A114213 is
`A007306(floor(n/2)+1)`. See Shallit–Spiegelhofer, arXiv:1710.06203,
for the identity `d(2n)=d(2n+1)=s(2n+1)`. -/
theorem d_eq_a007306 (n : ℕ) : d n = a007306 (n / 2 + 1) := by
  rw [d_eq_stern, a007306, stern_two_mul_add_one]

end Candidates.A114214SumFloorMod
