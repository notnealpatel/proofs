/-
# A046699 — Yanev: Conolly differences read off the limit word A215530

## OEIS source (retrieved with `oeis show A046699`, 2026-10-21)

```
NAME:     a(1) = a(2) = 1, a(n) = a(n - a(n-1)) + a(n-1 - a(n-2)) if n > 2.
TERMS:    1,1,2,2,3,4,4,4,5,6,6,7,8,8,8,8,9,10,10,11,12,12,12,13,14,14,15,16,
          16,16,16,16,17,18,18,19,20,20,20,21,22,22,23,24,24,24,24,25,26,26,
          27,28,28,28,29,30,30,31,32,32,32,32,32,32,33,34,34,35,36,36,36,37
FORMULA (the conjecture):
  Conjecture: a(n+1) = a(n) + A215530(a(n) + n) for all n > 0.
  - _Velin Yanev_, Oct 17 2019
FORMULA (context):
  First differences seem to be A079559. ... This is correct and not too hard
  to prove ... - _Paul Boddington_, Jul 30 2004
  For n>=1, a(n)=w(n-1) where w(n) is the least k such that 2^n divides
  (2k)!. - _Benoit Cloitre_, Jan 19 2007
COMMENT:  Except for the first term, n occurs A001511(n) times.
```

A215530 (offset 0): "The limit of the string "0, 1" under the operation
'repeat string twice and append 0'."  Terms
0,1,0,1,0,0,1,0,1,0,0,0,1,0,1,0,0,1,0,1,0,0,0,0,1,0,1,0,0,1,0,1,0,0,0,1,...

## Status

Triage: open (no proof in the entry or the literature as far as the triage
could tell).  Verified numerically for `1 ≤ n ≤ 200000` before formalizing.
This file proves the conjecture in full (`yanev_conjecture`, and for every function
meeting the entry's specification, `yanev_conjecture_of_isConolly`), sorry-free.

## Proof outline (this file)

Let `g = A005187`, `g k = k + g ⌊k/2⌋ = ν₂((2k)!)`.  Cloitre's formula says
`a n = min {k ≥ 1 | n ≤ g k + 1}`; we take this as the closed form
`conollyClosed` and prove that it satisfies the Conolly recurrence, via
`f (n - f (n-1)) = ⌈f n / 2⌉` and the fact that odd values occur once.
The ones of the limit word sit exactly at the positions `g i + i + 1`
(induction on the stages `W, W W 0`).  Yanev's identity then follows because
the jumps of `a` happen exactly at `n = g k + 1`, where `a n = k`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A046699ConollyOffsetLimit

/-! ## The Conolly sequence, as in the entry -/

/-- `conollyList n` is the list `[a 0, a 1, …, a n]` of the Conolly sequence
`a(1) = a(2) = 1`, `a(n) = a(n - a(n-1)) + a(n-1 - a(n-2))` for `n > 2`
(with the unused dummy value `a 0 = 0`).  Each new term is computed from the
previous list exactly by the recurrence of the entry. -/
def conollyList : ℕ → List ℕ
  | 0 => [0]
  | 1 => [0, 1]
  | 2 => [0, 1, 1]
  | n + 3 =>
    let l := conollyList (n + 2)
    l ++ [l.getD (n + 3 - l.getD (n + 2) 0) 0 + l.getD (n + 2 - l.getD (n + 1) 0) 0]

/-- The Conolly sequence A046699 (offset 1; the value at `0` is a dummy `0`). -/
def conolly (n : ℕ) : ℕ := (conollyList n).getD n 0

/-- The specification of A046699 as a predicate on functions: `a 1 = a 2 = 1` and
`a n = a (n - a (n-1)) + a (n - 1 - a (n-2))` for `n > 2`.  The value `a 0` is
never read by the recurrence (see `eq_conollyClosed_of_isConolly`). -/
def IsConolly (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧ a 2 = 1 ∧ ∀ n, 3 ≤ n → a n = a (n - a (n - 1)) + a (n - 1 - a (n - 2))

example : (List.range 72).tail.map conolly =
    [1, 1, 2, 2, 3, 4, 4, 4, 5, 6, 6, 7, 8, 8, 8, 8, 9, 10, 10, 11, 12, 12, 12, 13, 14, 14,
      15, 16, 16, 16, 16, 16, 17, 18, 18, 19, 20, 20, 20, 21, 22, 22, 23, 24, 24, 24, 24, 25,
      26, 26, 27, 28, 28, 28, 29, 30, 30, 31, 32, 32, 32, 32, 32, 32, 33, 34, 34, 35, 36, 36,
      36] := by
  decide

/-! ## The limit word A215530 -/

/-- The stages of A215530: `W 0 = 01` and `W (k+1) = W k ++ W k ++ [0]`. -/
def limitWordStage : ℕ → List ℕ
  | 0 => [0, 1]
  | k + 1 => limitWordStage k ++ limitWordStage k ++ [0]

/-- A215530 (offset 0), the limit word of `01` under `s ↦ s s 0`: its `n`-th letter is
read off any stage long enough to contain position `n`; stage `n` is (see
`length_limitWordStage` and `limitWord_eq_getD`). -/
def limitWord (n : ℕ) : ℕ := (limitWordStage n).getD n 0

example : (limitWordStage 5).take 87 =
    [0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1,
      0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1,
      0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0] := by
  decide

example : limitWord 11 = 0 ∧ limitWord 12 = 1 := by decide

/-! ## The auxiliary sequence A005187 -/

/-- A005187: `g 0 = 0`, `g k = k + g ⌊k/2⌋`; equivalently `g k = 2k - s₂(k) = ν₂((2k)!)`. -/
def a005187 : ℕ → ℕ
  | 0 => 0
  | k + 1 => (k + 1) + a005187 ((k + 1) / 2)
decreasing_by omega

example : (List.range 10).map a005187 = [0, 1, 3, 4, 7, 8, 10, 11, 15, 16] := by
  decide +kernel

/-- The defining recursion of A005187, valid at every `k`. -/
theorem a005187_eq (k : ℕ) : a005187 k = k + a005187 (k / 2) := by
  cases k with
  | zero => simp [a005187]
  | succ k => rw [a005187]

/-- A005187 increases by at least one at every step. -/
theorem a005187_succ_ge (k : ℕ) : a005187 k + 1 ≤ a005187 (k + 1) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [a005187_eq k, a005187_eq (k + 1)]
    rcases Nat.even_or_odd' k with ⟨c, hc | hc⟩
    · have h1 : (k + 1) / 2 = k / 2 := by omega
      rw [h1]; omega
    · have h1 : (k + 1) / 2 = k / 2 + 1 := by omega
      have h2 := ih (k / 2) (by omega)
      rw [h1]; omega

/-- A005187 is strictly increasing. -/
theorem a005187_strictMono : StrictMono a005187 :=
  strictMono_nat_of_lt_succ fun k => by have := a005187_succ_ge k; omega

/-- `g (2c) = 2c + g c`. -/
theorem a005187_two_mul (c : ℕ) : a005187 (2 * c) = 2 * c + a005187 c := by
  rw [a005187_eq]; congr 2; omega

/-- `g (2c+1) = 2c + 1 + g c`. -/
theorem a005187_two_mul_add_one (c : ℕ) : a005187 (2 * c + 1) = 2 * c + 1 + a005187 c := by
  rw [a005187_eq]; congr 2; omega

/-- Dyadic shift: for `i < 2^k`, `g (i + 2^k) + 1 = g i + 2^(k+1)`. -/
theorem a005187_add_two_pow (k i : ℕ) (hi : i < 2 ^ k) :
    a005187 (i + 2 ^ k) + 1 = a005187 i + 2 ^ (k + 1) := by
  induction k generalizing i with
  | zero =>
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    rw [a005187_eq (0 + 2 ^ 0)]
    simp [a005187]
  | succ k ih =>
    rw [pow_succ] at hi
    have hdiv : (i + 2 ^ (k + 1)) / 2 = i / 2 + 2 ^ k := by rw [pow_succ]; omega
    have h := ih (i / 2) (by omega)
    rw [a005187_eq (i + 2 ^ (k + 1)), a005187_eq i, hdiv, pow_succ 2 (k + 1), pow_succ 2 k]
    rw [pow_succ] at h
    omega

/-- `g k ≥ k`. -/
theorem le_a005187 (k : ℕ) : k ≤ a005187 k := by
  rw [a005187_eq k]; omega

/-! ## Cloitre's closed form -/

/-- Existence witness for `conollyClosed`. -/
theorem exists_conollyClosed (n : ℕ) : ∃ k, 1 ≤ k ∧ n ≤ a005187 k + 1 :=
  ⟨n + 1, by omega, by have := le_a005187 (n + 1); omega⟩

/-- Cloitre's closed form: the least `k ≥ 1` with `n ≤ g k + 1`, i.e. with
`2^(n-1) ∣ (2k)!` (the entry's formula `a(n) = w(n-1)`). -/
def conollyClosed (n : ℕ) : ℕ := Nat.find (exists_conollyClosed n)

/-- The closed form is at least `1`. -/
theorem one_le_conollyClosed (n : ℕ) : 1 ≤ conollyClosed n :=
  (Nat.find_spec (exists_conollyClosed n)).1

/-- Galois connection: for `k ≥ 1`, `f n ≤ k ↔ n ≤ g k + 1`. -/
theorem conollyClosed_le_iff {n k : ℕ} (hk : 1 ≤ k) :
    conollyClosed n ≤ k ↔ n ≤ a005187 k + 1 := by
  unfold conollyClosed
  rw [Nat.find_le_iff]
  constructor
  · rintro ⟨j, hjk, -, hj⟩
    have := a005187_strictMono.monotone hjk
    omega
  · intro h
    exact ⟨k, le_rfl, hk, h⟩

/-- Upper bound: `n ≤ g (f n) + 1`. -/
theorem le_a005187_conollyClosed (n : ℕ) : n ≤ a005187 (conollyClosed n) + 1 :=
  (conollyClosed_le_iff (one_le_conollyClosed n)).1 le_rfl

/-- Lower bound: `f n = 1` or `g (f n - 1) + 1 < n`. -/
theorem conollyClosed_lower (n : ℕ) :
    conollyClosed n = 1 ∨ a005187 (conollyClosed n - 1) + 1 < n := by
  by_cases h : conollyClosed n = 1
  · exact Or.inl h
  · right
    have h1 := one_le_conollyClosed n
    by_contra hc
    have := (conollyClosed_le_iff (n := n) (k := conollyClosed n - 1) (by omega)).2 (by omega)
    omega

/-- Recognising a value of the closed form from the block bounds. -/
theorem conollyClosed_eq_of_bounds {n c : ℕ} (hc : 1 ≤ c) (hup : n ≤ a005187 c + 1)
    (hlow : c = 1 ∨ a005187 (c - 1) + 1 < n) : conollyClosed n = c := by
  apply le_antisymm ((conollyClosed_le_iff hc).2 hup)
  by_contra hlt
  have h1 := one_le_conollyClosed n
  have h2 : conollyClosed n ≤ c - 1 := by omega
  have h3 := (conollyClosed_le_iff (k := c - 1) (by omega)).1 h2
  omega

/-- The closed form is monotone. -/
theorem conollyClosed_mono {m n : ℕ} (h : m ≤ n) : conollyClosed m ≤ conollyClosed n :=
  (conollyClosed_le_iff (one_le_conollyClosed n)).2
    (le_trans h (le_a005187_conollyClosed n))

/-- The closed form increases by at most one per step. -/
theorem conollyClosed_succ_le (n : ℕ) : conollyClosed (n + 1) ≤ conollyClosed n + 1 := by
  apply (conollyClosed_le_iff (by omega)).2
  have h1 := le_a005187_conollyClosed n
  have h2 := a005187_succ_ge (conollyClosed n)
  omega

/-- The block structure seen from position `n + 1`: the closed form jumps after `n`
exactly when `n = g (f n) + 1`. -/
theorem conollyClosed_succ_eq (n : ℕ) :
    conollyClosed (n + 1) = conollyClosed n + if n = a005187 (conollyClosed n) + 1 then 1 else 0 := by
  have hup := le_a005187_conollyClosed n
  split_ifs with h
  · apply conollyClosed_eq_of_bounds (by omega)
    · have := a005187_succ_ge (conollyClosed n); omega
    · right; simp only [Nat.add_sub_cancel]; omega
  · simp only [Nat.add_zero]
    apply conollyClosed_eq_of_bounds (one_le_conollyClosed n) (by omega)
    rcases conollyClosed_lower n with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by omega)

/-- Odd values of the closed form occur only once: for `n ≥ 2`, if `f n` is odd then
`f (n+1) = f n + 1`. -/
theorem conollyClosed_succ_of_odd {n : ℕ} (hn : 2 ≤ n) (hodd : Odd (conollyClosed n)) :
    conollyClosed (n + 1) = conollyClosed n + 1 := by
  obtain ⟨c, hc⟩ := hodd
  have hup := le_a005187_conollyClosed n
  have hlow := conollyClosed_lower n
  rw [hc] at hup hlow
  have hg := a005187_two_mul_add_one c
  have hg' := a005187_two_mul c
  have hjump : n = a005187 (conollyClosed n) + 1 := by
    rw [hc]
    rcases hlow with h | h
    · have hc0 : c = 0 := by omega
      subst hc0
      simp only [Nat.mul_zero, Nat.zero_add] at hup hg ⊢
      have h0 : a005187 0 = 0 := by simp [a005187]
      omega
    · simp only [Nat.add_sub_cancel] at h
      omega
  rw [conollyClosed_succ_eq n, if_pos hjump]

/-- **Halving lemma.** For `m ≥ 2`, `f (m - f (m-1)) = ⌈f m / 2⌉`. -/
theorem conollyClosed_sub_conollyClosed {m : ℕ} (hm : 2 ≤ m) :
    conollyClosed (m - conollyClosed (m - 1)) = (conollyClosed m + 1) / 2 := by
  have hstep : conollyClosed m = conollyClosed (m - 1) +
      if m - 1 = a005187 (conollyClosed (m - 1)) + 1 then 1 else 0 := by
    have h := conollyClosed_succ_eq (m - 1)
    rwa [Nat.sub_add_cancel (by omega)] at h
  have hupm := le_a005187_conollyClosed m
  have hlowm := conollyClosed_lower m
  have hupx := le_a005187_conollyClosed (m - 1)
  have hlowx := conollyClosed_lower (m - 1)
  have hx1 := one_le_conollyClosed (m - 1)
  generalize conollyClosed m = k at hstep hupm hlowm ⊢
  generalize conollyClosed (m - 1) = x at hstep hupx hlowx hx1 ⊢
  have h0 : a005187 0 = 0 := by simp [a005187]
  have h1 : a005187 1 = 1 := by rw [a005187_eq]; simp [h0]
  have hjx : m - 1 = a005187 x + 1 → x = k - 1 ∧ m - 1 = a005187 (k - 1) + 1 := by
    intro hj
    rw [if_pos hj] at hstep
    have hxk : x = k - 1 := by omega
    refine ⟨hxk, ?_⟩
    rw [← hxk]
    exact hj
  rcases Nat.even_or_odd' k with ⟨c, hc | hc⟩
  · -- `k = 2c`
    have hc1 : 1 ≤ c := by split_ifs at hstep <;> omega
    have hk : a005187 k = 2 * c + a005187 c := by rw [hc, a005187_two_mul]
    have hk1 : a005187 (k - 1) = 2 * c - 1 + a005187 (c - 1) := by
      have := a005187_two_mul_add_one (c - 1)
      rw [show k - 1 = 2 * (c - 1) + 1 by omega, this]; omega
    have hmono := a005187_succ_ge (c - 1)
    rw [Nat.sub_add_cancel hc1] at hmono
    have hres : (k + 1) / 2 = c := by omega
    rw [hres]
    apply conollyClosed_eq_of_bounds hc1
    · split_ifs at hstep with hj
      · have := hjx hj; omega
      · omega
    · right
      split_ifs at hstep with hj
      · have := hjx hj; omega
      · rcases hlowx with h | h
        · omega
        · rw [show x - 1 = k - 1 by omega] at h; omega
  · -- `k = 2c + 1`
    have hk : a005187 k = 2 * c + 1 + a005187 c := by rw [hc, a005187_two_mul_add_one]
    have hk1 : a005187 (k - 1) = 2 * c + a005187 c := by
      rw [show k - 1 = 2 * c by omega, a005187_two_mul]
    have hmono := a005187_succ_ge c
    have hres : (k + 1) / 2 = c + 1 := by omega
    rw [hres]
    apply conollyClosed_eq_of_bounds (by omega)
    · split_ifs at hstep with hj
      · have := hjx hj; omega
      · omega
    · split_ifs at hstep with hj
      · right; simp only [Nat.add_sub_cancel]; have := hjx hj; omega
      · -- `x = k`: an odd value occupies a single position unless `k = 1`
        rcases hlowx with h | h
        · left; omega
        · rw [show x - 1 = k - 1 by omega] at h
          rcases hlowm with h' | h'
          · left; omega
          · rw [show k - 1 = 2 * c by omega] at h'
            omega

/-- The closed form satisfies the Conolly recurrence for `n ≥ 3`. -/
theorem conollyClosed_rec {n : ℕ} (hn : 3 ≤ n) :
    conollyClosed n = conollyClosed (n - conollyClosed (n - 1)) +
      conollyClosed (n - 1 - conollyClosed (n - 2)) := by
  have hA := conollyClosed_sub_conollyClosed (m := n) (by omega)
  have hB := conollyClosed_sub_conollyClosed (m := n - 1) (by omega)
  rw [show n - 1 - 1 = n - 2 by omega] at hB
  rw [hA, hB]
  have hmono := conollyClosed_mono (show n - 1 ≤ n by omega)
  have hsucc := conollyClosed_succ_le (n - 1)
  rw [Nat.sub_add_cancel (by omega)] at hsucc
  rcases Nat.even_or_odd (conollyClosed (n - 1)) with hev | hodd
  · obtain ⟨c, hc⟩ := hev
    omega
  · have hj := conollyClosed_succ_of_odd (n := n - 1) (by omega) hodd
    rw [Nat.sub_add_cancel (by omega)] at hj
    obtain ⟨c, hc⟩ := hodd
    omega

/-- `f n ≤ n` for `n ≥ 1`. -/
theorem conollyClosed_le_self {n : ℕ} (hn : 1 ≤ n) : conollyClosed n ≤ n :=
  (conollyClosed_le_iff hn).2 (by have := le_a005187 n; omega)

/-- `f 1 = 1`. -/
theorem conollyClosed_one : conollyClosed 1 = 1 :=
  conollyClosed_eq_of_bounds le_rfl (by omega) (Or.inl rfl)

/-- `f 2 = 1`. -/
theorem conollyClosed_two : conollyClosed 2 = 1 :=
  conollyClosed_eq_of_bounds le_rfl (by rw [a005187_eq]; omega) (Or.inl rfl)

/-- Any function satisfying the Conolly specification agrees with Cloitre's closed form at
every `n ≥ 1` (so the specification determines A046699 uniquely). -/
theorem eq_conollyClosed_of_isConolly {a : ℕ → ℕ} (ha : IsConolly a) {n : ℕ} (hn : 1 ≤ n) :
    a n = conollyClosed n := by
  obtain ⟨ha1, ha2, harec⟩ := ha
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | h3
    · rw [ha1, conollyClosed_one]
    · rw [ha2, conollyClosed_two]
    · have e1 := ih (n - 1) (by omega) (by omega)
      have e2 := ih (n - 2) (by omega) (by omega)
      have b1 := conollyClosed_le_self (n := n - 1) (by omega)
      have b2 := conollyClosed_le_self (n := n - 2) (by omega)
      have p1 := one_le_conollyClosed (n - 1)
      have p2 := one_le_conollyClosed (n - 2)
      rw [harec n h3, e1, e2, ih _ (by omega) (by omega), ih _ (by omega) (by omega),
        ← conollyClosed_rec h3]

/-- `conollyList n` has length `n + 1`. -/
theorem length_conollyList : ∀ n, (conollyList n).length = n + 1
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | n + 3 => by
    rw [conollyList, List.length_append, length_conollyList (n + 2)]
    rfl

/-- Extending the list does not change earlier entries. -/
theorem getD_conollyList_succ (n i : ℕ) (hi : i ≤ n) :
    (conollyList (n + 1)).getD i 0 = (conollyList n).getD i 0 := by
  rcases (show n = 0 ∨ n = 1 ∨ 2 ≤ n by omega) with rfl | rfl | h2
  · interval_cases i; rfl
  · interval_cases i <;> rfl
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [conollyList, List.getD_append _ _ _ _ (by rw [length_conollyList]; omega)]

/-- Every later list agrees with `conolly` at earlier positions. -/
theorem getD_conollyList (n i : ℕ) (hi : i ≤ n) : (conollyList n).getD i 0 = conolly i := by
  induction n, hi using Nat.le_induction with
  | base => rfl
  | succ n hin ih => rw [getD_conollyList_succ n i hin, ih]

/-- The entry's recurrence, as computed by `conollyList`. -/
theorem conolly_add_three (n : ℕ) :
    conolly (n + 3) = (conollyList (n + 2)).getD (n + 3 - conolly (n + 2)) 0 +
      (conollyList (n + 2)).getD (n + 2 - conolly (n + 1)) 0 := by
  rw [conolly, conollyList, List.getD_append_right _ _ _ _ (by rw [length_conollyList]),
    length_conollyList, getD_conollyList (n + 2) (n + 2) le_rfl,
    getD_conollyList (n + 2) (n + 1) (by omega)]
  simp

/-- The list-computed Conolly sequence equals Cloitre's closed form at every `n ≥ 1`. -/
theorem conolly_eq_conollyClosed {n : ℕ} (hn : 1 ≤ n) : conolly n = conollyClosed n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | h3
    · rw [conollyClosed_one]; rfl
    · rw [conollyClosed_two]; rfl
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      have e2 := ih (m + 2) (by omega) (by omega)
      have e1 := ih (m + 1) (by omega) (by omega)
      have b2 := conollyClosed_le_self (n := m + 2) (by omega)
      have b1 := conollyClosed_le_self (n := m + 1) (by omega)
      have p2 := one_le_conollyClosed (m + 2)
      have p1 := one_le_conollyClosed (m + 1)
      rw [conolly_add_three, e2, e1, getD_conollyList _ _ (by omega),
        getD_conollyList _ _ (by omega), ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
      have hrec := conollyClosed_rec (n := m + 3) (by omega)
      simp only [show m + 3 - 2 = m + 1 by omega, show m + 3 - 1 = m + 2 by omega] at hrec
      exact hrec.symm

/-- Non-vacuity: the list-computed sequence satisfies the Conolly specification. -/
theorem isConolly_conolly : IsConolly conolly := by
  refine ⟨rfl, rfl, fun n hn => ?_⟩
  have b1 := conollyClosed_le_self (n := n - 1) (by omega)
  have b2 := conollyClosed_le_self (n := n - 2) (by omega)
  have p1 := one_le_conollyClosed (n - 1)
  have p2 := one_le_conollyClosed (n - 2)
  rw [conolly_eq_conollyClosed (by omega), conolly_eq_conollyClosed (n := n - 1) (by omega),
    conolly_eq_conollyClosed (n := n - 2) (by omega), conolly_eq_conollyClosed (by omega),
    conolly_eq_conollyClosed (by omega)]
  exact conollyClosed_rec hn

/-! ## Positions of the ones in the limit word -/

/-- The position of the `i`-th one (counting from `0`) of A215530: `g i + i + 1`. -/
def onePos (i : ℕ) : ℕ := a005187 i + i + 1

/-- `onePos` grows by at least two per step. -/
theorem onePos_succ_ge (i : ℕ) : onePos i + 2 ≤ onePos (i + 1) := by
  have := a005187_succ_ge i
  unfold onePos; omega

/-- `onePos` is strictly increasing. -/
theorem onePos_strictMono : StrictMono onePos :=
  strictMono_nat_of_lt_succ fun i => by have := onePos_succ_ge i; omega

/-- Dyadic shift of `onePos`: for `i < 2^k`, `onePos (i + 2^k) + 1 = onePos i + 3 * 2^k`. -/
theorem onePos_add_two_pow {k i : ℕ} (hi : i < 2 ^ k) :
    onePos (i + 2 ^ k) + 1 = onePos i + 3 * 2 ^ k := by
  have := a005187_add_two_pow k i hi
  rw [pow_succ] at this
  unfold onePos; omega

/-- `onePos i + 1 < 3 * 2^k ↔ i < 2^k`. -/
theorem onePos_add_one_lt_iff {k i : ℕ} : onePos i + 1 < 3 * 2 ^ k ↔ i < 2 ^ k := by
  have h2k : onePos (2 ^ k) = 3 * 2 ^ k := by
    have := onePos_add_two_pow (k := k) (i := 0) (Nat.two_pow_pos k)
    have h0 : onePos 0 = 1 := by simp [onePos, a005187]
    rw [Nat.zero_add, h0] at this; omega
  constructor
  · intro h
    by_contra hge
    have := onePos_strictMono.monotone (not_lt.1 hge)
    omega
  · intro h
    have h1 := onePos_succ_ge i
    have h2 := onePos_strictMono.monotone (show i + 1 ≤ 2 ^ k by omega)
    omega

/-- `|W k| + 1 = 3 * 2^k`. -/
theorem length_limitWordStage (k : ℕ) : (limitWordStage k).length + 1 = 3 * 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [limitWordStage, List.length_append, List.length_append, pow_succ]
    simp only [List.length_singleton]
    omega

/-- All letters of every stage are `0` or `1`. -/
theorem getD_limitWordStage_le_one (k m : ℕ) : (limitWordStage k).getD m 0 ≤ 1 := by
  induction k generalizing m with
  | zero => rcases m with _ | _ | m <;> simp [limitWordStage]
  | succ k ih =>
    rw [limitWordStage]
    by_cases h1 : m < (limitWordStage k ++ limitWordStage k).length
    · rw [List.getD_append _ _ _ _ h1]
      by_cases h2 : m < (limitWordStage k).length
      · rw [List.getD_append _ _ _ _ h2]; exact ih m
      · rw [List.getD_append_right _ _ _ _ (by omega)]; exact ih _
    · rw [List.getD_append_right _ _ _ _ (by omega)]
      rcases h : m - (limitWordStage k ++ limitWordStage k).length with _ | j <;> simp

/-- **Ones of the limit word.** Within stage `k`, the letter at `m` is `1` exactly when
`m = onePos i` for some `i`. -/
theorem getD_limitWordStage_eq_one_iff (k m : ℕ) (hm : m < (limitWordStage k).length) :
    (limitWordStage k).getD m 0 = 1 ↔ ∃ i, m = onePos i := by
  induction k generalizing m with
  | zero =>
    have h0 : onePos 0 = 1 := by simp [onePos, a005187]
    have hm' : m < 2 := by simpa [limitWordStage] using hm
    interval_cases m
    · simp only [limitWordStage, List.getD_cons_zero, zero_ne_one, false_iff, not_exists]
      intro i hi
      have := onePos_strictMono.monotone (Nat.zero_le i)
      omega
    · simp only [limitWordStage]
      exact ⟨fun _ => ⟨0, h0.symm⟩, fun _ => rfl⟩
  | succ k ih =>
    have hL := length_limitWordStage k
    set L := (limitWordStage k).length with hLdef
    have hLs := length_limitWordStage (k + 1)
    rw [pow_succ] at hLs
    rw [limitWordStage] at hm ⊢
    simp only [List.length_append, List.length_singleton] at hm
    rcases (show m < L ∨ (L ≤ m ∧ m < L + L) ∨ m = L + L by omega) with h | ⟨h, h'⟩ | h
    · rw [List.getD_append _ _ _ _ (by simp only [List.length_append]; omega),
        List.getD_append _ _ _ _ h]
      exact ih m h
    · rw [List.getD_append _ _ _ _ (by simp only [List.length_append]; omega),
        List.getD_append_right _ _ _ _ h, ih (m - L) (by omega)]
      constructor
      · rintro ⟨i, hi⟩
        have hik : i < 2 ^ k := onePos_add_one_lt_iff.1 (by omega)
        have := onePos_add_two_pow hik
        exact ⟨i + 2 ^ k, by omega⟩
      · rintro ⟨i, hi⟩
        have hik : ¬ i < 2 ^ k := fun hlt => by
          have := onePos_add_one_lt_iff.2 hlt; omega
        have hik' : i < 2 ^ (k + 1) := onePos_add_one_lt_iff.1 (by rw [pow_succ]; omega)
        rw [pow_succ] at hik'
        have := onePos_add_two_pow (k := k) (i := i - 2 ^ k) (by omega)
        rw [Nat.sub_add_cancel (by omega)] at this
        exact ⟨i - 2 ^ k, by omega⟩
    · rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append]; omega)]
      have hz : m - (limitWordStage k ++ limitWordStage k).length = 0 := by
        simp only [List.length_append]; omega
      rw [hz, h]
      simp only [List.getD_cons_zero, zero_ne_one, false_iff, not_exists]
      intro i hi
      have hik : ¬ i < 2 ^ k := fun hlt => by
        have := onePos_add_one_lt_iff.2 hlt; omega
      have hik' : i < 2 ^ (k + 1) := onePos_add_one_lt_iff.1 (by rw [pow_succ]; omega)
      rw [pow_succ] at hik'
      have := onePos_add_two_pow (k := k) (i := i - 2 ^ k) (by omega)
      rw [Nat.sub_add_cancel (by omega)] at this
      have := onePos_add_one_lt_iff.2 (show i - 2 ^ k < 2 ^ k by omega)
      omega

/-- Each stage is a prefix of the next: positions inside `W k` are unchanged in `W (k+1)`. -/
theorem getD_limitWordStage_succ (k m : ℕ) (hm : m < (limitWordStage k).length) :
    (limitWordStage (k + 1)).getD m 0 = (limitWordStage k).getD m 0 := by
  rw [limitWordStage, List.getD_append _ _ _ _ (by simp only [List.length_append]; omega),
    List.getD_append _ _ _ _ hm]

/-- The limit word can be read off any stage containing the position. -/
theorem limitWord_eq_getD (k m : ℕ) (hm : m < (limitWordStage k).length) :
    limitWord m = (limitWordStage k).getD m 0 := by
  have key : ∀ j j', j ≤ j' → m < (limitWordStage j).length →
      (limitWordStage j').getD m 0 = (limitWordStage j).getD m 0 := by
    intro j j' hjj' hj
    induction j', hjj' using Nat.le_induction with
    | base => rfl
    | succ j' hjj' ih =>
      have hlen : (limitWordStage j).length ≤ (limitWordStage j').length := by
        have h1 := length_limitWordStage j
        have h2 := length_limitWordStage j'
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hjj'
        omega
      rw [getD_limitWordStage_succ j' m (by omega), ih]
  have hmm : m < (limitWordStage m).length := by
    have h1 := length_limitWordStage m
    have h2 := Nat.lt_two_pow_self (n := m)
    omega
  unfold limitWord
  rcases le_total k m with h | h
  · exact key k m h hm
  · exact (key m k h hmm).symm

/-- The letter of the limit word at `m` is `1` iff `m = g i + i + 1` for some `i`. -/
theorem limitWord_eq_one_iff (m : ℕ) : limitWord m = 1 ↔ ∃ i, m = onePos i := by
  have hmm : m < (limitWordStage m).length := by
    have h1 := length_limitWordStage m
    have h2 := Nat.lt_two_pow_self (n := m)
    omega
  rw [limitWord_eq_getD m m hmm]
  exact getD_limitWordStage_eq_one_iff m m hmm

/-- The letters of the limit word are `0` or `1`. -/
theorem limitWord_le_one (m : ℕ) : limitWord m ≤ 1 := getD_limitWordStage_le_one m m

/-- Yanev's identity for the closed form: for `n ≥ 1`, `f (n+1) = f n + w (f n + n)`. -/
theorem conollyClosed_succ_eq_add_limitWord {n : ℕ} (hn : 1 ≤ n) :
    conollyClosed (n + 1) = conollyClosed n + limitWord (conollyClosed n + n) := by
  rw [conollyClosed_succ_eq n]
  congr 1
  have hup := le_a005187_conollyClosed n
  have hlow := conollyClosed_lower n
  have hk1 := one_le_conollyClosed n
  generalize conollyClosed n = k at hup hlow hk1 ⊢
  split_ifs with hj
  · symm
    rw [limitWord_eq_one_iff]
    exact ⟨k, by unfold onePos; omega⟩
  · symm
    have hne : limitWord (k + n) ≠ 1 := by
      rw [Ne, limitWord_eq_one_iff]
      rintro ⟨i, hi⟩
      unfold onePos at hi
      rcases lt_trichotomy i k with hik | rfl | hik
      · have hmono := a005187_strictMono.monotone (show i ≤ k - 1 by omega)
        rcases hlow with h | h
        · have hi0 : i = 0 := by omega
          subst hi0
          have h0 : a005187 0 = 0 := by simp [a005187]
          omega
        · omega
      · omega
      · have hmono := a005187_strictMono.monotone (show k + 1 ≤ i by omega)
        have hs := a005187_succ_ge k
        omega
    have := limitWord_le_one (k + n)
    omega

/-! ## Yanev's conjecture -/

/-- **Yanev's conjecture (A046699, Velin Yanev, Oct 17 2019), additive form.**
Verbatim: "Conjecture: a(n+1) = a(n) + A215530(a(n) + n) for all n > 0."
Here `conolly` is A046699 computed by the entry's recurrence and `limitWord` is A215530
(offset 0), the limit of `01` under `s ↦ s s 0`. -/
theorem conolly_succ_eq_add_limitWord {n : ℕ} (hn : 1 ≤ n) :
    conolly (n + 1) = conolly n + limitWord (conolly n + n) := by
  rw [conolly_eq_conollyClosed (by omega), conolly_eq_conollyClosed hn]
  exact conollyClosed_succ_eq_add_limitWord hn

/-- **Yanev's conjecture (A046699, Velin Yanev, Oct 17 2019), difference form.**
For all `n ≥ 1`, the first difference `a(n+1) - a(n)` of the Conolly sequence equals
`w(a(n) + n)`, where `w` is A215530, the limit word of `01` under `s ↦ s s 0`. -/
theorem yanev_conjecture {n : ℕ} (hn : 1 ≤ n) :
    (conolly (n + 1) : ℤ) - conolly n = limitWord (conolly n + n) := by
  rw [conolly_succ_eq_add_limitWord hn]
  push_cast
  ring

/-- **Yanev's conjecture, specification form.** Every function `a` satisfying
`a 1 = a 2 = 1`, `a n = a (n - a (n-1)) + a (n-1 - a (n-2))` (`n > 2`) obeys
`a (n+1) - a n = w (a n + n)` for all `n ≥ 1`. -/
theorem yanev_conjecture_of_isConolly {a : ℕ → ℕ} (ha : IsConolly a) {n : ℕ} (hn : 1 ≤ n) :
    (a (n + 1) : ℤ) - a n = limitWord (a n + n) := by
  rw [eq_conollyClosed_of_isConolly ha hn, eq_conollyClosed_of_isConolly ha (by omega),
    conollyClosed_succ_eq_add_limitWord hn]
  push_cast
  ring

end Candidates.A046699ConollyOffsetLimit
