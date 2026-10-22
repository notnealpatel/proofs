/-
# A029797: refutation of eventual consecutive enumeration

OEIS A029797, Charles R Greathouse IV (Jun 28 2011); David A. Corneth's
refutation (Nov 13 2023) uses `10^e + 1` (A062397).
Here the excluded family is `2*10^e`: its square and cube have different
decimal digit sets. Eventual enumeration `a(n) = m + n`, even for an integer
shift `m`, would contain every sufficiently large integer, a contradiction.
The sequence has offset `1` and is infinite, since it contains `10^e`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A029797Refutation

/-! ## Definitions -/

/-- `k` belongs to A029797: the decimal digit sets of `k^2` and `k^3`
coincide (`Nat.digits 10 0 = []`, so `k = 0` qualifies, as in the entry). -/
def IsA029797 (k : ℕ) : Prop :=
  (Nat.digits 10 (k ^ 2)).toFinset = (Nat.digits 10 (k ^ 3)).toFinset

/-- `IsA029797` is decided by comparing the two finite digit sets. -/
instance : DecidablePred IsA029797 := fun k =>
  inferInstanceAs
    (Decidable ((Nat.digits 10 (k ^ 2)).toFinset = (Nat.digits 10 (k ^ 3)).toFinset))

/-- The sequence A029797 with the OEIS offset `1`: `a n` is the `n`-th member
(meaningful for `1 ≤ n`; the conjecture below only uses such `n`). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsA029797 (n - 1)

/-! ## Examples against the listed terms -/

example : IsA029797 0 := by decide
example : IsA029797 1 := by decide
example : IsA029797 10 := by decide
example : IsA029797 146 := by decide
example : IsA029797 1203 := by decide
example : IsA029797 7652 := by decide
example : ¬ IsA029797 2 := by decide
example : ¬ IsA029797 11 := by decide
example : ¬ IsA029797 145 := by decide

/-- `a 1 = 0`, the first listed term. -/
example : a 1 = 0 := Nat.nth_zero_of_zero (p := IsA029797) (by decide)

/-- `a 3 = 10`, the third listed term (`10` is preceded by exactly two members). -/
example : a 3 = 10 := by
  have hc : Nat.count IsA029797 10 = 2 := by decide
  rw [a, show 3 - 1 = Nat.count IsA029797 10 from hc.symm]
  exact Nat.nth_count (p := IsA029797) (by decide)

/-- `a 5 = 146`, the fifth listed term. -/
example : a 5 = 146 := by
  have hc : Nat.count IsA029797 146 = 4 := by decide
  rw [a, show 5 - 1 = Nat.count IsA029797 146 from hc.symm]
  exact Nat.nth_count (p := IsA029797) (by decide)

/-! ## The conjecture -/

/-- **Greathouse's conjecture (A029797, Jun 28 2011).**  Verbatim:
"Conjecture: there exists some m and N for which a(n) = m + n for all n >= N."

The shift `m` is an integer (the comparison is made in `ℤ`), and the
`1 ≤ n` hypothesis keeps `a n` on its OEIS domain (offset `1`); it only
weakens the conjecture, so refuting this form is the stronger statement. -/
def Conjecture : Prop :=
  ∃ m : ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 ≤ n → (a n : ℤ) = m + n

/-! ## Digit-set lemmas -/

/-- Every power of ten is in the sequence (A011557 is a subsequence). -/
theorem isA029797_ten_pow (j : ℕ) : IsA029797 (10 ^ j) := by
  unfold IsA029797
  have h2 : (10 ^ j) ^ 2 = 10 ^ (2 * j) * 1 := by ring
  have h3 : (10 ^ j) ^ 3 = 10 ^ (3 * j) * 1 := by ring
  rw [h2, h3, Nat.digits_base_pow_mul (by norm_num) (by norm_num),
    Nat.digits_base_pow_mul (by norm_num) (by norm_num)]
  ext d
  simp only [List.mem_toFinset, List.mem_append, List.mem_replicate]
  constructor <;> rintro (⟨hj, hd⟩ | hd) <;>
    first
    | exact Or.inr hd
    | exact Or.inl ⟨by omega, hd⟩

/-- The sequence is infinite. -/
theorem setOf_isA029797_infinite : (Set.ofPred IsA029797).Infinite := by
  refine Set.infinite_of_not_bddAbove fun ⟨B, hB⟩ => ?_
  have hmem : 10 ^ B ∈ Set.ofPred IsA029797 := isA029797_ten_pow B
  have hle : 10 ^ B ≤ B := hB hmem
  have hlt : B < 10 ^ B := Nat.lt_pow_self (by norm_num)
  omega

/-- `2 * 10^e` is never in the sequence: `4` is a digit of its square
`4 * 10^(2e)` but not of its cube `8 * 10^(3e)`. -/
theorem not_isA029797_two_mul_ten_pow (e : ℕ) : ¬ IsA029797 (2 * 10 ^ e) := by
  unfold IsA029797
  have h2 : (2 * 10 ^ e) ^ 2 = 10 ^ (2 * e) * 4 := by ring
  have h3 : (2 * 10 ^ e) ^ 3 = 10 ^ (3 * e) * 8 := by ring
  rw [h2, h3, Nat.digits_base_pow_mul (by norm_num) (by norm_num),
    Nat.digits_base_pow_mul (by norm_num) (by norm_num)]
  intro h
  have h4 : 4 ∈ (List.replicate (2 * e) 0 ++ Nat.digits 10 4).toFinset := by simp
  rw [h] at h4
  simp [List.mem_replicate] at h4

/-! ## The refutation -/

/-- Eventual affine enumeration would contain every integer from
`a (max N 1)` onward. The excluded family `2*10^e` contradicts this:
its square contains digit `4`, whereas its cube does not.
No asymptotic density assertion is addressed. -/
theorem greathouse_false : ¬ Conjecture := by
  rintro ⟨m, N, hN⟩
  set N' := max N 1 with hN'
  have hstep : ∀ j : ℕ, a (N' + j) = a N' + j := by
    intro j
    have h1 := hN (N' + j) (by omega) (by omega)
    have h0 := hN N' (by omega) (by omega)
    push_cast at h1
    omega
  have hall : ∀ k : ℕ, a N' ≤ k → IsA029797 k := by
    intro k hk
    have hk' : k = a (N' + (k - a N')) := by rw [hstep]; omega
    rw [hk', a]
    exact Nat.nth_mem_of_infinite setOf_isA029797_infinite _
  have hbig : a N' ≤ 2 * 10 ^ (a N') := by
    have hlt : a N' < 10 ^ a N' := Nat.lt_pow_self (by norm_num)
    omega
  exact not_isA029797_two_mul_ten_pow (a N') (hall _ hbig)

end Candidates.A029797Refutation
