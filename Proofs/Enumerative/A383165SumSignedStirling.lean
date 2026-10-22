/-
# A383165: eventual periodicity of a signed Stirling sum

OEIS A383165, Peter Bala (Feb 17 2026).
For every positive modulus, the finite sum
`Σ_{k=2}^n 2^(n-k) S₂(n,k) s(k,2)` is eventually periodic, with a positive
period; `s` denotes the signed Stirling number of the first kind.
Large first-kind Stirling factors vanish modulo the modulus, leaving a
finite-state recurrence. The identification of the sum with the source's
e.g.f. `log(1+(exp(2x)-1)/2)^2/2` is not formalized.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A383165SumSignedStirling

/-! ## Definitions -/

/-- Signed Stirling number of the first kind `s(j,k) = (-1)^(j-k) |s(j,k)|`.
Mathlib's `Nat.stirlingFirst` is the unsigned one. The sign is written as
`(-1)^(j+k)`, which agrees with `(-1)^(j-k)` when `k ≤ j` and avoids natural
subtraction; when `j < k` both sides vanish. -/
def signedStirlingFirst (j k : ℕ) : ℤ := (-1) ^ (j + k) * (Nat.stirlingFirst j k : ℤ)

/-- OEIS A383165, by the entry's formula
`a(n) = Sum_{k = 2..n} 2^(n-k) * Stirling2(n,k) * Stirling1(k,2)`.
The natural subtraction `n - k` is guarded by `k ∈ Icc 2 n`. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 2 n, 2 ^ (n - k) * (Nat.stirlingSecond n k : ℤ) * signedStirlingFirst k 2

/-! ## Examples against the DATA line -/

example : signedStirlingFirst 3 2 = -3 := by decide
example : signedStirlingFirst 4 2 = 11 := by decide

example : [a 0, a 1, a 2, a 3, a 4, a 5, a 6, a 7, a 8, a 9, a 10] =
    [0, 0, 1, 3, 3, -10, -30, 112, 588, -2448, -18960] := by decide

/-! ## Helpers -/

/-- For every modulus `m > 0` and every `k`, the unsigned Stirling number
`|s(j,k)|` is divisible by `m` for all sufficiently large `j`. -/
theorem stirlingFirst_eventually_dvd (m : ℕ) (hm : 0 < m) (k : ℕ) :
    ∃ J, ∀ j, J ≤ j → m ∣ Nat.stirlingFirst j k := by
  induction k with
  | zero =>
    refine ⟨1, fun j hj => ?_⟩
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    simp [Nat.stirlingFirst_succ_zero]
  | succ k ih =>
    obtain ⟨J, hJ⟩ := ih
    refine ⟨m * J + 1, fun j hj => ?_⟩
    induction j, hj using Nat.le_induction with
    | base =>
      rw [Nat.stirlingFirst_succ_succ]
      have hle : J ≤ m * J := Nat.le_mul_of_pos_left J hm
      exact dvd_add (Dvd.dvd.mul_right (dvd_mul_right m J) _) (hJ _ hle)
    | succ j hj ihj =>
      rw [Nat.stirlingFirst_succ_succ]
      have hle : J ≤ j := le_trans (Nat.le_mul_of_pos_left J hm) (by omega)
      exact dvd_add (Dvd.dvd.mul_left ihj _) (hJ _ hle)

/-- The scaled Stirling numbers of the second kind `u_j(n) = 2^(n-j) S2(n,j)`. -/
def u (j n : ℕ) : ℤ := 2 ^ (n - j) * (Nat.stirlingSecond n j : ℤ)

/-- `u_0(n+1) = 0`. -/
theorem u_zero_succ (n : ℕ) : u 0 (n + 1) = 0 := by
  simp [u, Nat.stirlingSecond_succ_zero]

/-- The recurrence `u_{j+1}(n+1) = 2(j+1) u_{j+1}(n) + u_j(n)`, valid for all `n`. -/
theorem u_succ_succ (j n : ℕ) :
    u (j + 1) (n + 1) = 2 * (j + 1) * u (j + 1) n + u j n := by
  unfold u
  rw [Nat.stirlingSecond_succ_succ]
  rcases Nat.lt_or_ge j n with hjn | hnj
  · obtain ⟨d, rfl⟩ : ∃ d, n = j + 1 + d := ⟨n - (j + 1), by omega⟩
    have h1 : j + 1 + d + 1 - (j + 1) = d + 1 := by omega
    have h2 : j + 1 + d - (j + 1) = d := by omega
    have h3 : j + 1 + d - j = d + 1 := by omega
    rw [h1, h2, h3]
    push_cast
    ring
  · have h0 : Nat.stirlingSecond n (j + 1) = 0 := Nat.stirlingSecond_eq_zero_of_lt (by omega)
    have h1 : n + 1 - (j + 1) = 0 := by omega
    have h2 : n - j = 0 := by omega
    rw [h0, h1, h2]
    push_cast
    ring

/-- A sequence in a finite type driven by a fixed step map is eventually periodic. -/
theorem eventually_periodic_of_step {α : Type*} [Finite α] (s : ℕ → α) (F : α → α)
    (hs : ∀ n, s (n + 1) = F (s n)) :
    ∃ N T, 0 < T ∧ ∀ n, N ≤ n → s (n + T) = s n := by
  obtain ⟨x, y, hxy, hsxy⟩ := Finite.exists_ne_map_eq_of_infinite s
  have key : ∀ i j, i < j → s i = s j → ∃ N T, 0 < T ∧ ∀ n, N ≤ n → s (n + T) = s n := by
    intro i j hij hsij
    refine ⟨i, j - i, by omega, fun n hn => ?_⟩
    induction n, hn using Nat.le_induction with
    | base =>
      rw [show i + (j - i) = j by omega]
      exact hsij.symm
    | succ n _ ihn =>
      rw [show n + 1 + (j - i) = n + (j - i) + 1 by omega, hs, hs, ihn]
  rcases Nat.lt_or_gt_of_ne hxy with h | h
  · exact key x y h hsxy
  · exact key y x h hsxy.symm

/-- `a(n)` rewritten over `range (n+1)` with `u`. -/
theorem a_eq_sum_range (n : ℕ) :
    a n = ∑ j ∈ Finset.range (n + 1), u j n * signedStirlingFirst j 2 := by
  unfold a u
  refine Finset.sum_subset (fun j hj => ?_) (fun j hj hjn => ?_)
  · simp only [Finset.mem_Icc] at hj
    simp only [Finset.mem_range]
    omega
  · simp only [Finset.mem_Icc, Finset.mem_range, not_and_or, not_le] at hj hjn
    have hj2 : j < 2 := by omega
    simp [signedStirlingFirst, Nat.stirlingFirst_eq_zero_of_lt hj2]

/-! ## The conjecture -/

/-- Bala's A383165 conjecture for the finite signed-Stirling formula:
for every positive modulus `m`, there are a threshold and a positive
period `T` with `a(n+T) ≡ a(n) (mod m)` thereafter.
The positive-modulus guard excludes eventual equality over `ℤ`. -/
theorem a_eventually_periodic_mod (m : ℕ) (hm : 0 < m) :
    ∃ N T, 0 < T ∧ ∀ n, N ≤ n → a (n + T) ≡ a n [ZMOD m] := by
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨J, hJ⟩ := stirlingFirst_eventually_dvd m hm 2
  -- state vector and step map
  let st : ℕ → (Fin J → ZMod m) := fun n i => ((u i n : ℤ) : ZMod m)
  let F : (Fin J → ZMod m) → (Fin J → ZMod m) := fun v i =>
    if h : (i : ℕ) = 0 then 0 else 2 * ((i : ℕ) : ZMod m) * v i + v ⟨(i : ℕ) - 1, by omega⟩
  have hstep : ∀ n, st (n + 1) = F (st n) := by
    intro n
    funext i
    rcases i with ⟨_ | i, hi⟩
    · simp [st, F, u_zero_succ]
    · simp only [st, F, Nat.add_one_ne_zero, dite_false, Nat.add_sub_cancel, u_succ_succ]
      push_cast
      ring
  obtain ⟨N, T, hT, hper⟩ := eventually_periodic_of_step st F hstep
  -- reduction of `a n` to a linear function of the state for `n ≥ J`
  let G : (Fin J → ZMod m) → ZMod m := fun v =>
    ∑ i : Fin J, v i * ((signedStirlingFirst i 2 : ℤ) : ZMod m)
  have hred : ∀ n, J ≤ n → ((a n : ℤ) : ZMod m) = G (st n) := by
    intro n hn
    rw [a_eq_sum_range, Int.cast_sum, ← Finset.sum_range_add_sum_Ico _ (by omega : J ≤ n + 1)]
    have htail : ∑ j ∈ Finset.Ico J (n + 1),
        (((u j n * signedStirlingFirst j 2 : ℤ)) : ZMod m) = 0 := by
      refine Finset.sum_eq_zero (fun j hj => ?_)
      simp only [Finset.mem_Ico] at hj
      obtain ⟨c, hc⟩ := hJ j hj.1
      simp [signedStirlingFirst, hc]
    rw [htail, add_zero]
    simp only [G, st]
    rw [Fin.sum_univ_eq_sum_range (fun j => ((u j n : ℤ) : ZMod m) *
      ((signedStirlingFirst j 2 : ℤ) : ZMod m)) J]
    push_cast
    rfl
  refine ⟨max N J, T, hT, fun n hn => ?_⟩
  rw [← ZMod.intCast_eq_intCast_iff, hred (n + T) (by omega), hred n (by omega),
    hper n (by omega)]

end Candidates.A383165SumSignedStirling
