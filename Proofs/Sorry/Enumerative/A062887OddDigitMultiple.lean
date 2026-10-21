/-
# A062887 — Irvine: a cyclic odd-digit multiple of `2n+1` exists iff `125 ∤ 2n+1`

## OEIS source (pulled with `oeis show A062887`, 2026-10-21)

```
NAME:     Smallest multiple of 2n+1 with the property that its digits are odd
          and each digit is two less (mod 10) than the previous digit, or 0 if
          no such number exists.
TERMS:    1,3,5,7,9,319,975,75,7531,19,197531975319,3197,75,5319,319,31,
          3197531975319,53197531975,1975319,975,531975,1975319753197,
          19753197531975,75319753197531,319753197531975319,753197531975319753
COMMENT (the conjecture):
  Conjecture: The only numbers n for which a(n)=0 are those for which 2*n+1
  is divisible by 125. - _Sean A. Irvine_, Apr 14 2023
```

## Status

Triage status: open (no proof in the entry or in the literature found by the
triage).  The triage reported an elementary argument, which this file
formalizes:

* (`125 ∤ m`) Write `m = 5^e k` with `gcd(k, 10) = 1`, `e ≤ 2`.  The number
  `31975 31975 … 31975` (`j` blocks) equals `31975 (10^{5j} - 1) / 99999`;
  for `j = φ(99999 k)` it is divisible by `25 k`, hence by `m`.
* (`125 ∣ m`) A multiple of `125` ends in `5`, so a valid number is `5`, `75`
  or ends in `975`; none of these is `0 mod 125` (`975 ≡ 100 mod 125`).

Computational re-validation (2026-10-21, BFS over (residue, last digit)):
the equivalence holds for every odd `m < 16000`, and the brute-force
smallest witnesses reproduce the 26 listed terms.

## Formal reading

Digits are read with `Nat.digits 10`, which is little-endian: the head is the
units digit.  "Each digit is two less (mod 10) than the previous digit"
(reading left to right) is, little-endian, "each digit is two more (mod 10)
than the next less significant one", i.e.
`(Nat.digits 10 N).IsChain (fun a b => b = (a + 2) % 10)`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A062887OddDigitMultiple

/-! ## Definition layer -/

/-- `IsOddCyclic N`: `N` is positive (its digit list is nonempty), all decimal
digits of `N` are odd, and, reading from the most significant digit, each digit
is two less (mod 10) than the previous one.  Stated little-endian on
`Nat.digits 10 N`: each digit is the previous (less significant) one plus `2`,
mod `10`. -/
def IsOddCyclic (N : ℕ) : Prop :=
  Nat.digits 10 N ≠ [] ∧ (∀ d ∈ Nat.digits 10 N, Odd d) ∧
    (Nat.digits 10 N).IsChain (fun a b => b = (a + 2) % 10)

/-- `IsOddCyclic` is decidable (used for the ground-truth checks). -/
instance : DecidablePred IsOddCyclic := fun N => by
  unfold IsOddCyclic; infer_instance

open Classical in
/-- A062887: the smallest positive multiple of `2n+1` with the `IsOddCyclic`
digit property, or `0` if no such number exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  if h : ∃ N, 0 < N ∧ 2 * n + 1 ∣ N ∧ IsOddCyclic N then Nat.find h else 0

/-! ## Ground truth -/

example : IsOddCyclic 319 := by decide
example : IsOddCyclic 197531975319 := by decide
example : IsOddCyclic 753197531975319753 := by decide
example : ¬ IsOddCyclic 0 := by decide
example : ¬ IsOddCyclic 318 := by decide
example : ¬ IsOddCyclic 315 := by decide

/-- Ground truth for `a`: if `w` is a valid witness for `2n+1` and no smaller
number is, then `a n = w`. -/
theorem a_eq_of_witness (n w : ℕ) (hw : 0 < w ∧ 2 * n + 1 ∣ w ∧ IsOddCyclic w)
    (hmin : ∀ N < w, ¬ (0 < N ∧ 2 * n + 1 ∣ N ∧ IsOddCyclic N)) : a n = w := by
  classical
  have hex : ∃ N, 0 < N ∧ 2 * n + 1 ∣ N ∧ IsOddCyclic N := ⟨w, hw⟩
  unfold a
  rw [dif_pos hex, Nat.find_eq_iff]
  exact ⟨hw, hmin⟩

example : a 0 = 1 := a_eq_of_witness 0 1 (by decide) (by decide)
example : a 2 = 5 := a_eq_of_witness 2 5 (by decide) (by decide)
set_option maxRecDepth 10000 in
example : a 5 = 319 := a_eq_of_witness 5 319 (by decide) (by decide)
set_option maxRecDepth 10000 in
example : a 6 = 975 := a_eq_of_witness 6 975 (by decide) (by decide)
example : a 7 = 75 := a_eq_of_witness 7 75 (by decide) (by decide)
example : a 9 = 19 := a_eq_of_witness 9 19 (by decide) (by decide)
set_option maxRecDepth 10000 in
example : a 11 = 3197 := a_eq_of_witness 11 3197 (by decide) (by decide)

/-! ## The repeated block `31975 31975 …` -/

/-- Little-endian digit list of `31975` repeated `j` times: the `i`-th digit
(from the units end) is `(5 + 2 i) mod 10`, i.e. `5, 7, 9, 1, 3, 5, …`. -/
def block (j : ℕ) : List ℕ := (List.range (5 * j)).map (fun i => (5 + 2 * i) % 10)

example : Nat.ofDigits 10 (block 2) = 3197531975 := by decide

/-- Every entry of `block j` is odd. -/
theorem odd_of_mem_block {j d : ℕ} (hd : d ∈ block j) : Odd d := by
  simp only [block, List.mem_map, List.mem_range] at hd
  obtain ⟨i, -, rfl⟩ := hd
  rw [Nat.odd_iff]
  omega

/-- Every entry of `block j` is a decimal digit. -/
theorem lt_ten_of_mem_block {j d : ℕ} (hd : d ∈ block j) : d < 10 := by
  simp only [block, List.mem_map, List.mem_range] at hd
  obtain ⟨i, -, rfl⟩ := hd
  omega

/-- Consecutive entries of `block j` differ by `+2 mod 10`. -/
theorem isChain_block (j : ℕ) : (block j).IsChain (fun a b => b = (a + 2) % 10) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  simp only [block, List.getElem_map, List.getElem_range]
  omega

/-- Reading the digits of `ofDigits 10 (block j)` recovers `block j`. -/
theorem digits_ofDigits_block (j : ℕ) :
    Nat.digits 10 (Nat.ofDigits 10 (block j)) = block j := by
  refine Nat.digits_ofDigits 10 (by norm_num) _ (fun d hd => lt_ten_of_mem_block hd) ?_
  intro hne
  exact (odd_of_mem_block (List.getLast_mem hne)).pos.ne'

/-- `block (j+1)` is `block j` followed by one more copy of `5, 7, 9, 1, 3`. -/
theorem block_succ (j : ℕ) : block (j + 1) = block j ++ [5, 7, 9, 1, 3] := by
  have h5 : 5 * (j + 1) = 5 * j + 5 := by ring
  simp only [block, h5, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.ext_getElem (by simp)
  intro i hi _
  simp only [List.length_map, List.length_range] at hi
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
  interval_cases i <;>
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;> omega

/-- The value of the repeated block, without subtraction:
`99999 · (31975 repeated j times) + 31975 = 31975 · 100000^j`. -/
theorem ofDigits_block (j : ℕ) :
    99999 * Nat.ofDigits 10 (block j) + 31975 = 31975 * 100000 ^ j := by
  induction j with
  | zero => simp [block]
  | succ j ih =>
    have hlen : (block j).length = 5 * j := by simp [block]
    have hpow : (10 : ℕ) ^ (5 * j) = 100000 ^ j := by rw [pow_mul]; norm_num
    have hlast : Nat.ofDigits 10 [5, 7, 9, 1, 3] = 31975 := by norm_num [Nat.ofDigits]
    rw [block_succ, Nat.ofDigits_append, hlen, hpow, hlast, pow_succ]
    linarith [ih]

/-- The repeated block is a valid number: `ofDigits 10 (block j)` has the
`IsOddCyclic` property whenever `0 < j`. -/
theorem isOddCyclic_ofDigits_block {j : ℕ} (hj : 0 < j) :
    IsOddCyclic (Nat.ofDigits 10 (block j)) := by
  have hne : block j ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp only [block, List.length_map, List.length_range, List.length_nil] at hlen
    omega
  refine ⟨?_, ?_, ?_⟩ <;> rw [digits_ofDigits_block]
  · exact hne
  · exact fun d hd => odd_of_mem_block hd
  · exact isChain_block j

/-! ## The two directions -/

/-- **Existence (`125 ∤ m`).**  Every odd `m` not divisible by `125` has a
positive multiple with the `IsOddCyclic` property: `31975` repeated
`φ(99999 k)` times, where `m = 5^e k`, `5 ∤ k`. -/
theorem exists_of_not_dvd {m : ℕ} (hm : Odd m) (h125 : ¬ 125 ∣ m) :
    ∃ N, 0 < N ∧ m ∣ N ∧ IsOddCyclic N := by
  obtain ⟨e, k, hk5, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.pos.ne' 5 (by norm_num)
  have he : e ≤ 2 := by
    by_contra he
    exact h125 (Dvd.dvd.mul_right (pow_dvd_pow 5 (by omega : 3 ≤ e)) k)
  have hkodd : Odd k := hm.of_dvd_nat (Dvd.intro_left _ rfl)
  have hcop5 : Nat.Coprime 5 k := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hk5
  have hcop2 : Nat.Coprime 2 k := Nat.coprime_two_left.2 hkodd
  have hcop10 : Nat.Coprime 10 k := by
    simpa using Nat.Coprime.mul_left hcop2 hcop5
  have hcop : Nat.Coprime 100000 (99999 * k) := by
    refine Nat.Coprime.mul_right (by norm_num) ?_
    simpa using Nat.Coprime.pow_left 5 hcop10
  set j := Nat.totient (99999 * k)
  have hj : 0 < j := Nat.totient_pos.2 (Nat.mul_pos (by norm_num) hkodd.pos)
  set X := Nat.ofDigits 10 (block j)
  have hX : 99999 * X + 31975 = 31975 * 100000 ^ j := ofDigits_block j
  -- `99999 k ∣ 99999 X`
  have hmod : 99999 * X + 31975 ≡ 0 + 31975 [MOD 99999 * k] := by
    have hpow : 31975 * 100000 ^ j ≡ 31975 * 1 [MOD 99999 * k] :=
      (Nat.ModEq.pow_totient hcop).mul_left 31975
    rw [hX, zero_add]
    simpa only [mul_one] using hpow
  have hdvd99 : 99999 * k ∣ 99999 * X :=
    (Nat.modEq_zero_iff_dvd).1 (Nat.ModEq.add_right_cancel' 31975 hmod)
  have hkX : k ∣ X := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd99
  have h25X : 25 ∣ X := by
    have h25 : 25 ∣ 99999 * X := by
      have hrhs : 25 ∣ 31975 * 100000 ^ j := Dvd.dvd.mul_right (by norm_num) _
      rw [← hX, add_comm] at hrhs
      exact (Nat.dvd_add_right (by norm_num : 25 ∣ 31975)).1 hrhs
    exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h25)
  have hcop25 : Nat.Coprime 25 k := by
    simpa using Nat.Coprime.pow_left 2 hcop5
  have h25k : 25 * k ∣ X := hcop25.mul_dvd_of_dvd_of_dvd h25X hkX
  have hXpos : 0 < X := by
    rcases Nat.eq_zero_or_pos X with h0 | h0
    · exfalso
      have hp : 1 < 100000 ^ j := Nat.one_lt_pow hj.ne' (by norm_num)
      rw [h0] at hX
      omega
    · exact h0
  refine ⟨X, hXpos, ?_, isOddCyclic_ofDigits_block hj⟩
  have hme : 5 ^ e * k ∣ 25 * k :=
    Nat.mul_dvd_mul_right (pow_dvd_pow 5 he : 5 ^ e ∣ 5 ^ 2) k
  exact hme.trans h25k

/-- **Non-existence (`125 ∣ m`).**  No positive multiple of `125` has the
`IsOddCyclic` property: such a number ends in `5`, so it is `5`, `75`, or ends
in `975`, and `975 ≡ 100 (mod 125)`. -/
theorem not_isOddCyclic_of_dvd {N : ℕ} (h125 : 125 ∣ N) : ¬ IsOddCyclic N := by
  rintro ⟨hne, hodd, hchain⟩
  have hN := Nat.ofDigits_digits 10 N
  have hlt : ∀ d ∈ Nat.digits 10 N, d < 10 := fun d hd => Nat.digits_lt_base (by norm_num) hd
  generalize Nat.digits 10 N = L at hne hodd hchain hN hlt
  rcases L with _ | ⟨x, _ | ⟨y, _ | ⟨z, r⟩⟩⟩
  · exact hne rfl
  · have hx := hodd x (by simp)
    have hx10 := hlt x (by simp)
    rw [Nat.odd_iff] at hx
    simp only [Nat.ofDigits_singleton] at hN
    omega
  · have hx := hodd x (by simp)
    have hx10 := hlt x (by simp)
    rw [Nat.odd_iff] at hx
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hchain
    simp only [Nat.ofDigits_cons, Nat.ofDigits_nil] at hN
    omega
  · have hx := hodd x (by simp)
    have hx10 := hlt x (by simp)
    rw [Nat.odd_iff] at hx
    simp only [List.isChain_cons_cons] at hchain
    obtain ⟨hy, hz, -⟩ := hchain
    simp only [Nat.ofDigits_cons] at hN
    omega

/-! ## The conjecture -/

/-- **Irvine's conjecture (A062887, Sean A. Irvine, Apr 14 2023), existence
form.**  For odd `m`, some positive multiple of `m` has all decimal digits odd
with each digit two less (mod 10) than the previous one iff `125 ∤ m`. -/
theorem exists_isOddCyclic_iff {m : ℕ} (hm : Odd m) :
    (∃ N, 0 < N ∧ m ∣ N ∧ IsOddCyclic N) ↔ ¬ 125 ∣ m := by
  constructor
  · rintro ⟨N, -, hmN, hN⟩ h125
    exact not_isOddCyclic_of_dvd (h125.trans hmN) hN
  · exact exists_of_not_dvd hm

/-- **Irvine's conjecture (A062887, Sean A. Irvine, Apr 14 2023), verbatim
form.**  "The only numbers n for which a(n)=0 are those for which 2*n+1 is
divisible by 125." -/
theorem a_eq_zero_iff (n : ℕ) : a n = 0 ↔ 125 ∣ 2 * n + 1 := by
  classical
  have hodd : Odd (2 * n + 1) := odd_two_mul_add_one n
  unfold a
  split_ifs with h
  · have hpos : 0 < Nat.find h := (Nat.find_spec h).1
    have hnot : ¬ 125 ∣ 2 * n + 1 := (exists_isOddCyclic_iff hodd).1 h
    exact ⟨fun h0 => absurd h0 hpos.ne', fun h125 => absurd h125 hnot⟩
  · constructor
    · intro _
      by_contra h125
      exact h ((exists_isOddCyclic_iff hodd).2 h125)
    · intro _; rfl

end Candidates.A062887OddDigitMultiple
