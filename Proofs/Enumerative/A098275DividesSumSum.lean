/-
Divisibility of the double sum in OEIS A098275 (F. Chapoton, Jan 28 2026).

For a(n)=∑_{i,j=0}^n C(n,i)² C(n,j)² C(n+i,n) C(i+j,i), (n+1) divides a(n).
Vandermonde reduction gives terms divisible after multiplication by k and
by n-k; coprimality of n and n+1 then gives termwise divisibility.
This is a result about the entry's explicit finite sum; the separate
fourth-root generating-function conjecture (Apr 23 2026) is not addressed.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A098275DividesSumSum

open Finset

/-! ## Definition layer -/

/-- OEIS A098275, by the entry's formula:
`a(n) = ∑_{i=0..n} ∑_{j=0..n} C(n,i)^2 C(n,j)^2 C(n+i,n) C(i+j,i)`. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1),
    n.choose i ^ 2 * n.choose j ^ 2 * (n + i).choose n * (i + j).choose i

/-- The first listed terms `1, 8, 264, 13040, 778840`. -/
example : [a 0, a 1, a 2, a 3, a 4] = [1, 8, 264, 13040, 778840] := by decide

/-! ## Binomial helpers -/

/-- `(n+1) ∣ i * C(n+i, n)` for all `n i`, from `i C(n+i,i) = (n+1) C(n+i,i-1)`. -/
theorem succ_dvd_mul_add_choose (n i : ℕ) : (n + 1) ∣ i * (n + i).choose n := by
  rcases i with _ | t
  · simp
  · have h := Nat.choose_succ_right_eq (n + (t + 1)) t
    have hsub : n + (t + 1) - t = n + 1 := by omega
    rw [hsub] at h
    have hsymm : (n + (t + 1)).choose n = (n + (t + 1)).choose (t + 1) :=
      Nat.choose_symm_of_eq_add rfl
    rw [hsymm, mul_comm, h]
    exact Dvd.intro_left _ rfl

/-- `i ∣ k * C(i, k)`, from `k C(i,k) = i C(i-1,k-1)`. -/
theorem dvd_mul_choose (i k : ℕ) : i ∣ k * i.choose k := by
  rcases k with _ | k
  · simp
  · have h := Nat.choose_mul (n := i) (k := k + 1) (s := 1) (by omega)
    rw [Nat.choose_one_right, Nat.choose_one_right] at h
    rw [mul_comm, h]
    exact Dvd.intro _ rfl

/-- Vandermonde in the form `C(i+j, i) = ∑_{k ≤ j} C(i,k) C(j,k)`. -/
theorem add_choose_eq_sum (i j : ℕ) :
    (i + j).choose i = ∑ k ∈ range (j + 1), i.choose k * j.choose k := by
  rw [Nat.choose_symm_add, Nat.add_choose_eq, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine sum_congr rfl fun k hk => ?_
  rw [mem_range] at hk
  rw [Nat.choose_symm (by omega : k ≤ j)]

/-- `∑_{j ≤ k+m} C(k+m, j)^2 C(j, k) = C(k+m, k) C(m+(k+m), m)`. -/
theorem sum_choose_sq_mul_choose (k m : ℕ) :
    ∑ j ∈ range (k + m + 1), (k + m).choose j ^ 2 * j.choose k =
      (k + m).choose k * (m + (k + m)).choose m := by
  rw [show k + m + 1 = k + (m + 1) by omega, sum_range_add]
  have hzero : ∑ x ∈ range k, (k + m).choose x ^ 2 * x.choose k = 0 :=
    sum_eq_zero fun x hx => by
      rw [Nat.choose_eq_zero_of_lt (mem_range.mp hx), mul_zero]
  rw [hzero, zero_add, Nat.add_choose_eq m (k + m) m, Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
  refine sum_congr rfl fun t ht => ?_
  rw [mem_range] at ht
  have hmul := Nat.choose_mul (n := k + m) (k := k + t) (s := k) (by omega)
  rw [show k + m - k = m by omega, show k + t - k = t by omega] at hmul
  have hsymm : (k + m).choose (m - t) = (k + m).choose (k + t) :=
    Nat.choose_symm_of_eq_add (by omega)
  dsimp only
  rw [hsymm, sq, mul_assoc, hmul]
  ring

/-- Vandermonde with the `k`-range widened to `k ≤ n` whenever `j ≤ n`. -/
theorem add_choose_eq_sum_range (n i j : ℕ) (hj : j ≤ n) :
    (i + j).choose i = ∑ k ∈ range (n + 1), i.choose k * j.choose k := by
  rw [add_choose_eq_sum]
  refine sum_subset (range_subset_range.mpr (by omega)) fun k _ hk => ?_
  rw [mem_range, not_lt] at hk
  rw [Nat.choose_eq_zero_of_lt (by omega : j < k), mul_zero]

/-- Inner-sum identity: `∑_{j ≤ n} C(n,j)^2 C(i+j,i) = ∑_{k ≤ n} C(i,k) C(n,k) C(n+(n-k), n)`. -/
theorem sum_choose_sq_mul_add_choose (n i : ℕ) :
    ∑ j ∈ range (n + 1), n.choose j ^ 2 * (i + j).choose i =
      ∑ k ∈ range (n + 1), i.choose k * (n.choose k * (n + (n - k)).choose n) := by
  calc ∑ j ∈ range (n + 1), n.choose j ^ 2 * (i + j).choose i
      = ∑ j ∈ range (n + 1), ∑ k ∈ range (n + 1),
          i.choose k * (n.choose j ^ 2 * j.choose k) := by
        refine sum_congr rfl fun j hj => ?_
        rw [add_choose_eq_sum_range n i j (Nat.lt_succ_iff.mp (mem_range.mp hj)), mul_sum]
        refine sum_congr rfl fun k _ => ?_
        ring
    _ = ∑ k ∈ range (n + 1), i.choose k * ∑ j ∈ range (n + 1), n.choose j ^ 2 * j.choose k := by
        rw [sum_comm]
        simp only [mul_sum]
    _ = _ := by
        refine sum_congr rfl fun k hk => ?_
        have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
        have h := sum_choose_sq_mul_choose k (n - k)
        rw [show k + (n - k) = n by omega] at h
        rw [h, Nat.choose_symm_of_eq_add (n := n - k + n) (a := n - k) (b := n) rfl,
          add_comm (n - k) n]

/-- Each summand `C(n,i)^2 C(n+i,n) C(i,k) C(n,k) C(n+(n-k),n)` with `k ≤ n` is divisible by `n+1`. -/
theorem succ_dvd_term (n i k : ℕ) (hk : k ≤ n) :
    (n + 1) ∣ n.choose i ^ 2 * (n + i).choose n *
      (i.choose k * (n.choose k * (n + (n - k)).choose n)) := by
  set T := n.choose i ^ 2 * (n + i).choose n *
      (i.choose k * (n.choose k * (n + (n - k)).choose n)) with hT
  obtain ⟨c, hc⟩ := dvd_mul_choose i k
  have h1 : (n + 1) ∣ k * T := by
    have hkT : k * T = i * (n + i).choose n *
        (n.choose i ^ 2 * c * (n.choose k * (n + (n - k)).choose n)) := by
      rw [hT, show k * (n.choose i ^ 2 * (n + i).choose n *
          (i.choose k * (n.choose k * (n + (n - k)).choose n))) =
          (k * i.choose k) * (n.choose i ^ 2 * (n + i).choose n *
          (n.choose k * (n + (n - k)).choose n)) by ring, hc]
      ring
    rw [hkT]
    exact Dvd.dvd.mul_right (succ_dvd_mul_add_choose n i) _
  have h2 : (n + 1) ∣ (n - k) * T := by
    have hkT : (n - k) * T = (n - k) * (n + (n - k)).choose n *
        (n.choose i ^ 2 * (n + i).choose n * (i.choose k * n.choose k)) := by
      rw [hT]; ring
    rw [hkT]
    exact Dvd.dvd.mul_right (succ_dvd_mul_add_choose n (n - k)) _
  have h3 : (n + 1) ∣ n * T := by
    have hsplit : n * T = k * T + (n - k) * T := by
      rw [← add_mul, show k + (n - k) = n by omega]
    rw [hsplit]
    exact dvd_add h1 h2
  have hcop : Nat.Coprime (n + 1) n := by
    simp
  exact hcop.dvd_of_dvd_mul_left h3

/-! ## The conjecture -/

/-- For every natural `n`, `n+1` divides the explicit double sum A098275(n). -/
theorem succ_dvd_a (n : ℕ) : (n + 1) ∣ a n := by
  have hrw : a n = ∑ i ∈ range (n + 1), n.choose i ^ 2 * (n + i).choose n *
      ∑ j ∈ range (n + 1), n.choose j ^ 2 * (i + j).choose i := by
    unfold a
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    ring
  rw [hrw]
  refine dvd_sum fun i _ => ?_
  rw [sum_choose_sq_mul_add_choose, mul_sum]
  exact dvd_sum fun k hk => succ_dvd_term n i k (Nat.lt_succ_iff.mp (mem_range.mp hk))

end Candidates.A098275DividesSumSum
