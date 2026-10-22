/-
# A214973: records of Fibonacci-Lucas greedy length

OEIS A214973, Charles R Greathouse IV (Oct 14 2021), with A116470 and
A049651; Kimberling's least-value comment in A049651 (Oct 23 2012).
Use the positive distinct Fibonacci and Lucas values as the basis, choosing
the greatest available value at each step. For every `n ≥ 1`,
`A(n) = (F(3n+1)-1)/2` is the first argument with greedy length `n`.
The basis excludes `0`, which does not affect the greedy choices.
This uses basis values, as in the source programs, rather than the apparent
index/value typo in the source's description of the second greedy step.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A214973SetDistinctFibonacci

open Nat

/-- Lucas numbers `L(0) = 2`, `L(1) = 1`, `L(k+2) = L(k) + L(k+1)` (OEIS A000032). -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (k + 2) => lucas k + lucas (k + 1)

/-- The basis `U` of A214973: the positive terms of A116470, i.e. all distinct positive
Fibonacci and Lucas numbers. -/
def fibLucasSet : Set ℕ := {x | 0 < x ∧ ∃ i, x = fib i ∨ x = lucas i}

/-- Lucas numbers in terms of Fibonacci numbers: `L(i+1) = F(i) + F(i+2)`. -/
theorem lucas_succ (i : ℕ) : lucas (i + 1) = fib i + fib (i + 2) := by
  have key : ∀ i, lucas (i + 1) = fib i + fib (i + 2) ∧
      lucas (i + 2) = fib (i + 1) + fib (i + 3) := by
    intro i
    induction i with
    | zero => exact ⟨rfl, rfl⟩
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      have h1 : lucas (j + 3) = lucas (j + 1) + lucas (j + 2) := rfl
      have e4 : fib (j + 4) = fib (j + 2) + fib (j + 3) := fib_add_two
      have e3 : fib (j + 3) = fib (j + 1) + fib (j + 2) := fib_add_two
      obtain ⟨ih1, ih2⟩ := ih
      have e2 : fib (j + 2) = fib j + fib (j + 1) := fib_add_two
      show lucas (j + 3) = fib (j + 2) + fib (j + 4)
      omega
  exact (key i).1

/-- Every Lucas number dominates its index (up to one). -/
theorem le_lucas (i : ℕ) : i ≤ lucas i + 1 := by
  cases i with
  | zero => simp
  | succ j =>
    rw [lucas_succ]
    have h := le_fib_add_one (j + 2)
    omega

/-- Bounded description of membership in `fibLucasSet`, used for decidability. -/
theorem mem_fibLucasSet_iff_bounded (x : ℕ) :
    x ∈ fibLucasSet ↔ 0 < x ∧ ∃ i < x + 2, x = fib i ∨ x = lucas i := by
  constructor
  · rintro ⟨hx, i, hi⟩
    refine ⟨hx, i, ?_, hi⟩
    rcases hi with hi | hi
    · have h := le_fib_add_one i
      omega
    · have h := le_lucas i
      omega
  · rintro ⟨hx, i, -, hi⟩
    exact ⟨hx, i, hi⟩

/-- Membership in `U` is decidable by a bounded search over indices. -/
instance : DecidablePred (· ∈ fibLucasSet) := fun x =>
  decidable_of_iff _ (mem_fibLucasSet_iff_bounded x).symm

/-- The largest element of `U` that is at most `m` (it is `0` only when `m = 0`). -/
def maxU (m : ℕ) : ℕ := Nat.findGreatest (· ∈ fibLucasSet) m

/-- Fuel-driven greedy loop: subtract the largest available element of `U` until `0`. -/
def greedyAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | (fuel + 1), m => if m = 0 then 0 else greedyAux fuel (m - maxU m) + 1

/-- A214973: number of terms in the greedy representation of `m` by Fibonacci and Lucas
numbers. Each greedy step lowers `m` by at least one, so `m` units of fuel suffice. -/
def greedyCount (m : ℕ) : ℕ := greedyAux m m

example : (List.range 30).map greedyCount =
    [0, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 3, 2,
      1] := by decide

/-- Normal form of `U`: positive numbers of the form `F(i)` or `F(i) + F(i+2)`. -/
theorem mem_fibLucasSet_iff (x : ℕ) :
    x ∈ fibLucasSet ↔ 0 < x ∧ ∃ i, x = fib i ∨ x = fib i + fib (i + 2) := by
  constructor
  · rintro ⟨hx, i, hi⟩
    refine ⟨hx, ?_⟩
    rcases hi with hi | hi
    · exact ⟨i, Or.inl hi⟩
    · cases i with
      | zero => exact ⟨3, Or.inl (by rw [hi]; rfl)⟩
      | succ j => exact ⟨j, Or.inr (by rw [hi, lucas_succ])⟩
  · rintro ⟨hx, i, hi⟩
    refine ⟨hx, ?_⟩
    rcases hi with hi | hi
    · exact ⟨i, Or.inl hi⟩
    · exact ⟨i + 1, Or.inr (by rw [hi, lucas_succ])⟩

/-- `F(i) ∈ U` whenever `F(i)` is positive. -/
theorem fib_mem (i : ℕ) (hi : 0 < fib i) : fib i ∈ fibLucasSet :=
  (mem_fibLucasSet_iff _).2 ⟨hi, i, Or.inl rfl⟩

/-- `F(i) + F(i+2) ∈ U` (a Lucas number). -/
theorem fib_add_fib_mem (i : ℕ) : fib i + fib (i + 2) ∈ fibLucasSet :=
  (mem_fibLucasSet_iff _).2 ⟨by have := fib_pos.2 (show 0 < i + 2 by omega); omega,
    i, Or.inr rfl⟩

/-- Gap lemma: below `F(k+3)` (with `1 ≤ k`), every element `x` of `U` has a larger
element of `U` within distance `F(k)`. -/
theorem exists_mem_gt_le_add_fib {x : ℕ} (hx : x ∈ fibLucasSet) {k : ℕ} (hk : 1 ≤ k)
    (hxk : x < fib (k + 3)) : ∃ v ∈ fibLucasSet, x < v ∧ v ≤ x + fib k := by
  have hfk : 0 < fib k := fib_pos.2 hk
  obtain ⟨hx0, i, hi | hi⟩ := (mem_fibLucasSet_iff x).1 hx
  · rcases (show i ≤ 2 ∨ 3 ≤ i by omega) with h | h
    · have h1 : fib i ≤ 1 := by interval_cases i <;> simp
      refine ⟨fib 3, fib_mem 3 (by decide), ?_, ?_⟩ <;>
        simp only [show fib 3 = 2 from rfl] <;> omega
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 3 := ⟨i - 3, by omega⟩
      have hlt : j + 3 < k + 3 := (fib_lt_fib (by omega)).1 (hi ▸ hxk)
      have hmono : fib (j + 1) ≤ fib k := fib_mono (by omega)
      have hpos : 0 < fib (j + 1) := fib_pos.2 (by omega)
      refine ⟨fib (j + 1) + fib (j + 1 + 2), fib_add_fib_mem (j + 1), ?_, ?_⟩ <;>
        simp only [hi, show j + 1 + 2 = j + 3 from rfl] <;> omega
  · rcases (show i ≤ 1 ∨ 2 ≤ i by omega) with h | h
    · interval_cases i
      · refine ⟨fib 3, fib_mem 3 (by decide), ?_, ?_⟩ <;>
          simp only [hi, show fib 3 = 2 from rfl, show fib 0 = 0 from rfl,
            show fib 2 = 1 from rfl] <;> omega
      · refine ⟨fib 2 + fib (2 + 2), fib_add_fib_mem 2, ?_, ?_⟩ <;>
          simp only [hi, show fib 1 = 1 from rfl, show fib (1 + 2) = 2 from rfl,
            show fib 2 = 1 from rfl, show fib (2 + 2) = 3 from rfl] <;> omega
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
      simp only [show j + 2 + 2 = j + 4 from rfl] at hi
      have h4 : fib (j + 4) < fib (k + 3) := by
        have : fib (j + 4) ≤ x := by rw [hi]; omega
        omega
      have hlt : j + 4 < k + 3 := (fib_lt_fib (by omega)).1 h4
      have hmono : fib (j + 1) ≤ fib k := fib_mono (by omega)
      have hpos : 0 < fib (j + 1) := fib_pos.2 (by omega)
      have e5 : fib (j + 5) = fib (j + 3) + fib (j + 4) := fib_add_two
      have e3 : fib (j + 3) = fib (j + 1) + fib (j + 2) := fib_add_two
      refine ⟨fib (j + 5), fib_mem _ (fib_pos.2 (by omega)), ?_, ?_⟩ <;> omega

/-- Emptiness lemma: no element of `U` lies strictly between `F(j+2)` and the
Lucas number `F(j+2) + F(j)`. -/
theorem le_fib_of_mem_of_lt {x : ℕ} (hx : x ∈ fibLucasSet) {j : ℕ}
    (hxj : x < fib (j + 2) + fib j) : x ≤ fib (j + 2) := by
  obtain ⟨-, i, hi | hi⟩ := (mem_fibLucasSet_iff x).1 hx
  · by_contra hcon
    have hlt : j + 2 < i := (fib_lt_fib (by omega)).1 (by omega)
    have h3 : fib (j + 3) ≤ fib i := fib_mono (by omega)
    have e3 : fib (j + 3) = fib (j + 1) + fib (j + 2) := fib_add_two
    have hm : fib j ≤ fib (j + 1) := fib_mono (by omega)
    omega
  · rcases (show i + 1 ≤ j ∨ j ≤ i by omega) with h | h
    · have h1 : fib i ≤ fib j := fib_mono (by omega)
      have h2 : fib (i + 2) ≤ fib (j + 1) := fib_mono (by omega)
      have e2 : fib (j + 2) = fib j + fib (j + 1) := fib_add_two
      omega
    · have h1 : fib j ≤ fib i := fib_mono h
      have h2 : fib (j + 2) ≤ fib (i + 2) := fib_mono (by omega)
      omega

/-- `1 ∈ U`. -/
theorem one_mem : 1 ∈ fibLucasSet := fib_mem 1 (by decide)

/-- For `0 < m`, `maxU m` is an element of `U`. -/
theorem maxU_mem {m : ℕ} (hm : 0 < m) : maxU m ∈ fibLucasSet :=
  Nat.findGreatest_spec (P := (· ∈ fibLucasSet)) hm one_mem

/-- `maxU m ≤ m`. -/
theorem maxU_le (m : ℕ) : maxU m ≤ m := Nat.findGreatest_le m

/-- Maximality of `maxU m`. -/
theorem le_maxU {m x : ℕ} (hx : x ∈ fibLucasSet) (hxm : x ≤ m) : x ≤ maxU m :=
  Nat.le_findGreatest hxm hx

/-- Extra fuel does not change the greedy loop. -/
theorem greedyAux_succ (f m : ℕ) (hm : m ≤ f) : greedyAux (f + 1) m = greedyAux f m := by
  induction f generalizing m with
  | zero =>
    obtain rfl : m = 0 := by omega
    rfl
  | succ f ih =>
    by_cases h0 : m = 0
    · subst h0; rfl
    · have hpos : 0 < maxU m := ((mem_fibLucasSet_iff _).1 (maxU_mem (by omega))).1
      have hle := maxU_le m
      show (if m = 0 then 0 else greedyAux (f + 1) (m - maxU m) + 1) =
        (if m = 0 then 0 else greedyAux f (m - maxU m) + 1)
      rw [if_neg h0, if_neg h0, ih (m - maxU m) (by omega)]

/-- Any fuel `f ≥ m` computes `greedyCount m`. -/
theorem greedyAux_eq (f m : ℕ) (hm : m ≤ f) : greedyAux f m = greedyCount m := by
  induction f, hm using Nat.le_induction with
  | base => rfl
  | succ f hf ih => rw [greedyAux_succ f m hf, ih]

/-- `greedyCount 0 = 0`. -/
theorem greedyCount_zero : greedyCount 0 = 0 := rfl

/-- The greedy recursion: for `0 < m`, `g(m) = g(m - maxU m) + 1`. -/
theorem greedyCount_of_pos {m : ℕ} (hm : 0 < m) :
    greedyCount m = greedyCount (m - maxU m) + 1 := by
  obtain ⟨f, rfl⟩ : ∃ f, m = f + 1 := ⟨m - 1, by omega⟩
  have hpos : 0 < maxU (f + 1) := ((mem_fibLucasSet_iff _).1 (maxU_mem hm)).1
  have hle := maxU_le (f + 1)
  show greedyAux (f + 1) (f + 1) = _
  simp only [greedyAux, show f + 1 ≠ 0 from by omega, if_false]
  rw [greedyAux_eq f _ (by omega)]

/-- A049651: `A(n) = (F(3n+1) - 1)/2`. -/
def A (n : ℕ) : ℕ := (fib (3 * n + 1) - 1) / 2

example : (List.range 6).map A = [0, 1, 6, 27, 116, 493] := by decide

/-- `F(3n+4) = F(3n+1) + 2 F(3n+2)`. -/
theorem fib_three_mul_add_four (n : ℕ) :
    fib (3 * n + 4) = fib (3 * n + 1) + 2 * fib (3 * n + 2) := by
  have e4 : fib (3 * n + 4) = fib (3 * n + 2) + fib (3 * n + 3) := fib_add_two
  have e3 : fib (3 * n + 3) = fib (3 * n + 1) + fib (3 * n + 2) := fib_add_two
  omega

/-- `F(3n+1)` is odd and `2 A(n) + 1 = F(3n+1)`: the division in `A` is exact. -/
theorem two_mul_A_add_one (n : ℕ) : 2 * A n + 1 = fib (3 * n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e := fib_three_mul_add_four n
    have ih' : 2 * ((fib (3 * n + 1) - 1) / 2) + 1 = fib (3 * n + 1) := ih
    show 2 * ((fib (3 * (n + 1) + 1) - 1) / 2) + 1 = fib (3 * (n + 1) + 1)
    rw [show 3 * (n + 1) + 1 = 3 * n + 4 by ring, e]
    omega

/-- `A(n+1) = A(n) + F(3n+2)`. -/
theorem A_succ (n : ℕ) : A (n + 1) = A n + fib (3 * n + 2) := by
  have h1 := two_mul_A_add_one n
  have h2 := two_mul_A_add_one (n + 1)
  have e := fib_three_mul_add_four n
  rw [show 3 * (n + 1) + 1 = 3 * n + 4 by ring] at h2
  omega

/-- For `1 ≤ n`, `A(n) < F(3n)`. -/
theorem A_lt_fib {n : ℕ} (hn : 1 ≤ n) : A n < fib (3 * n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h := two_mul_A_add_one (k + 1)
  rw [show 3 * (k + 1) + 1 = 3 * k + 4 by ring] at h
  rw [show 3 * (k + 1) = 3 * k + 3 by ring]
  have e : fib (3 * k + 4) = fib (3 * k + 2) + fib (3 * k + 3) := fib_add_two
  have hm : fib (3 * k + 2) ≤ fib (3 * k + 3) := fib_mono (by omega)
  omega

/-- Minimality: if the greedy representation of `m` has at least `n` terms, then
`A(n) ≤ m`. -/
theorem A_le_of_le_greedyCount (n : ℕ) : ∀ m, n ≤ greedyCount m → A n ≤ m := by
  induction n with
  | zero => intro m _; simp [A]
  | succ n ih =>
    intro m hm
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp [greedyCount_zero] at hm
      · exact h
    set u := maxU m with hu
    have humem : u ∈ fibLucasSet := maxU_mem hm0
    have hule : u ≤ m := maxU_le m
    have hrec : greedyCount m = greedyCount (m - u) + 1 := greedyCount_of_pos hm0
    have hr : A n ≤ m - u := ih (m - u) (by omega)
    have hbig : fib (3 * n + 2) ≤ u := by
      by_contra hcon
      push Not at hcon
      rcases n with _ | n
      · have : 0 < u := ((mem_fibLucasSet_iff _).1 humem).1
        have h2 : fib (3 * 0 + 2) = 1 := rfl
        omega
      · obtain ⟨v, hv, huv, hvle⟩ := exists_mem_gt_le_add_fib humem (k := 3 * n + 2)
          (by omega) (by rw [show 3 * n + 2 + 3 = 3 * (n + 1) + 2 by ring]; exact hcon)
        have hA : fib (3 * n + 2) ≤ A (n + 1) := by rw [A_succ]; omega
        have hvm : v ≤ m := by omega
        have := le_maxU hv hvm
        omega
    rw [A_succ]
    omega

/-- Achievement: the greedy representation of `A(n)` has exactly `n` terms. -/
theorem greedyCount_A (n : ℕ) : greedyCount (A n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpos : 0 < fib (3 * n + 2) := fib_pos.2 (by omega)
    have hm0 : 0 < A (n + 1) := by rw [A_succ]; omega
    have hmax : maxU (A (n + 1)) = fib (3 * n + 2) := by
      apply le_antisymm
      · have hmem := maxU_mem hm0
        have hle := maxU_le (A (n + 1))
        rcases n with _ | n
        · have h1 : A 1 = 1 := rfl
          simp only [h1] at hle ⊢
          simpa using hle
        · apply le_fib_of_mem_of_lt hmem (j := 3 * (n + 1))
          have hlt := A_lt_fib (n := n + 1) (by omega)
          have hA := A_succ (n + 1)
          omega
      · exact le_maxU (fib_mem _ hpos) (by rw [A_succ]; omega)
    rw [greedyCount_of_pos hm0, hmax, A_succ, Nat.add_sub_cancel, ih]

/-- **A214973 records conjecture** (Greathouse, Oct 14 2021; also Kimberling in A049651,
Oct 23 2012).  Let `g(m)` be the number of terms in the greedy representation of `m` by the
distinct Fibonacci and Lucas numbers (A214973).  For every `n ≥ 1`,
`g((F(3n+1)-1)/2) = n`, and `g(m) < n` for every `0 < m < (F(3n+1)-1)/2`; i.e. A049651
without its initial term is the RECORDS transform of A214973. -/
theorem a214973_records (n : ℕ) (_hn : 1 ≤ n) :
    greedyCount ((fib (3 * n + 1) - 1) / 2) = n ∧
      ∀ m, 0 < m → m < (fib (3 * n + 1) - 1) / 2 → greedyCount m < n := by
  refine ⟨greedyCount_A n, fun m _ hm => ?_⟩
  by_contra hcon
  have hle := A_le_of_le_greedyCount n m (by omega)
  exact absurd hm (not_lt.2 hle)

/-- Satisfiability of the hypotheses: at `n = 2` the record value is `6`, and some
`0 < m < 6` exists. -/
example : (fib (3 * 2 + 1) - 1) / 2 = 6 ∧ greedyCount 6 = 2 ∧ greedyCount 5 < 2 := by
  decide

end Candidates.A214973SetDistinctFibonacci
