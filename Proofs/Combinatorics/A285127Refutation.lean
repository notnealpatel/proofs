/-
# A285127 — Kimberling's bound `-3 < n*r - a(n) < 0` is false

OEIS A285127 (Clark Kimberling, April 19, 2017) lists the 1-based
positions of 1 in A285125, the limit of the even iterates of
`0 ↦ 10`, `1 ↦ 0000` starting at 0. Its conjectured bound is
`-3 < nr - a(n) < 0` for `n ≥ 1`, with `r = 3.5621...`.

Since `a(2) = 11`, every `r < 4` violates the lower bound at `n = 2`.
In fact no real constant works: `a(1) = 5` forces `r < 5`,
whereas `a(4) = 23` forces `5 < r`. No unboundedness result is formalized.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A285127Refutation

/-! ## Definition layer -/

/-- The morphism on letters: `0 ↦ 10`, `1 ↦ 0000` (letters other than `0`, `1`
never occur in the words below; they are sent like `1`). -/
def subst : ℕ → List ℕ
  | 0 => [1, 0]
  | _ => [0, 0, 0, 0]

/-- The morphism `0 ↦ 10`, `1 ↦ 0000` extended to words. -/
def sigma (w : List ℕ) : List ℕ := w.flatMap subst

/-- The `k`-th iterate of the morphism applied to the word `0`. -/
def iter (k : ℕ) : List ℕ := sigma^[k] [0]

/-- The letter at (0-based) index `i` of the 0-limiting word: the even iterates
`iter (2 * k)` form a prefix chain (`iter_prefix`) whose lengths are unbounded
(`length_iter_two_mul`), and `iter (2 * (i + 1))` already has length `> i`, so
the `getD` default is never used (`word_eq_getD`). -/
def word (i : ℕ) : ℕ := (iter (2 * (i + 1))).getD i 0

/-- A285125 with its OEIS offset 1: the `n`-th letter of the 0-limiting word of
`0 ↦ 10`, `1 ↦ 0000`.  The index `0` lies outside the OEIS domain. -/
def A285125 (n : ℕ) : ℕ := word (n - 1)

/-- `m` is a (1-based) position of a `1` in A285125. -/
def IsOnePos (m : ℕ) : Prop := 0 < m ∧ A285125 m = 1

/-- A285127 with its OEIS offset 1: `A285127 n` is the position of the `n`-th
`1` in A285125.  The index `0` lies outside the OEIS domain. -/
noncomputable def A285127 (n : ℕ) : ℕ := Nat.nth IsOnePos (n - 1)

/-! ## Structure of the iterates -/

/-- The morphism is a monoid morphism on words. -/
theorem sigma_append (a b : List ℕ) : sigma (a ++ b) = sigma a ++ sigma b := by
  simp [sigma, List.flatMap_append]

/-- Iterates of the morphism are monoid morphisms on words. -/
theorem sigma_iterate_append (k : ℕ) (a b : List ℕ) :
    sigma^[k] (a ++ b) = sigma^[k] a ++ sigma^[k] b := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      sigma_append, ih]

/-- Since `σ²(0) = 0·00010`, we get `σ^(k+2)(0) = σ^k(0) · σ^k(00010)`. -/
theorem iter_add_two (k : ℕ) : iter (k + 2) = iter k ++ sigma^[k] [0, 0, 0, 1, 0] := by
  have h2 : sigma^[2] [0] = [0] ++ [0, 0, 0, 1, 0] := by decide
  rw [iter, Function.iterate_add_apply, h2, sigma_iterate_append, iter]

/-- The morphism does not shorten words. -/
theorem length_le_length_sigma (w : List ℕ) : w.length ≤ (sigma w).length := by
  induction w with
  | nil => simp [sigma]
  | cons d w ih =>
    have hd : 1 ≤ (subst d).length := by cases d <;> simp [subst]
    have hc : sigma (d :: w) = subst d ++ sigma w := by simp [sigma]
    rw [hc, List.length_append, List.length_cons]
    omega

/-- Iterates of the morphism do not shorten words. -/
theorem length_le_length_sigma_iterate (k : ℕ) (w : List ℕ) :
    w.length ≤ (sigma^[k] w).length := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (length_le_length_sigma _)

/-- The even iterates have unbounded length: `|σ^(2k)(0)| ≥ 5k + 1`. -/
theorem length_iter_two_mul (k : ℕ) : 5 * k + 1 ≤ (iter (2 * k)).length := by
  induction k with
  | zero => simp [iter]
  | succ k ih =>
    have h := length_le_length_sigma_iterate (2 * k) [0, 0, 0, 1, 0]
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, iter_add_two, List.length_append]
    simp only [List.length_cons, List.length_nil] at h
    omega

/-- The even iterates form a prefix chain, so the 0-limiting word exists. -/
theorem iter_prefix {m k : ℕ} (h : m ≤ k) : iter (2 * m) <+: iter (2 * k) := by
  induction k, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ k _ ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, iter_add_two]
    exact ih.trans (List.prefix_append _ _)

/-- `word` agrees with every even iterate on that iterate's length: it is the
limit of the even iterates. -/
theorem word_eq_getD {i K : ℕ} (hi : i < (iter (2 * K)).length) :
    word i = (iter (2 * K)).getD i 0 := by
  have hlen : i < (iter (2 * (i + 1))).length := by
    have hl := length_iter_two_mul (i + 1)
    omega
  rcases le_total (i + 1) K with h | h
  · have hp := iter_prefix h
    rw [word, List.getD_eq_getElem _ _ hlen, List.getD_eq_getElem _ _ hi, hp.getElem hlen]
  · have hp := iter_prefix h
    rw [word, List.getD_eq_getElem _ _ hlen, List.getD_eq_getElem _ _ hi, hp.getElem hi]

/-- The sixth iterate `σ⁶(0)` has `246` letters. -/
theorem length_iter_six : (iter (2 * 3)).length = 246 := by decide +kernel

/-- On `1 ≤ m ≤ 246`, A285125 is read off the finite word `σ⁶(0)`. -/
theorem A285125_eq_getD {m : ℕ} (hm : m ≤ 246) :
    A285125 m = (iter (2 * 3)).getD (m - 1) 0 := by
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    exact word_eq_getD (by rw [length_iter_six]; norm_num)
  · exact word_eq_getD (by rw [length_iter_six]; omega)

/-- Decidable table version of `IsOnePos`, read off `σ⁶(0)`. -/
def IsOnePosTable (m : ℕ) : Prop := 0 < m ∧ (iter (2 * 3)).getD (m - 1) 0 = 1

/-- `IsOnePosTable` is decidable. -/
instance : DecidablePred IsOnePosTable := fun m => by
  unfold IsOnePosTable
  infer_instance

/-- Below `247`, the table agrees with the positions of `1`s in A285125. -/
theorem isOnePos_iff {m : ℕ} (hm : m ≤ 246) : IsOnePos m ↔ IsOnePosTable m := by
  rw [IsOnePos, IsOnePosTable, A285125_eq_getD hm]

/-- If `m ≤ 246` is a position of a `1` preceded by exactly `n - 1` earlier
`1`s, then `m` is the `n`-th term of A285127. -/
theorem A285127_eq_of {n m : ℕ} (hm : m ≤ 246) (hq : IsOnePosTable m)
    (hc : Nat.count IsOnePosTable m = n - 1) : A285127 n = m := by
  classical
  have hcount : Nat.count IsOnePos m = Nat.count IsOnePosTable m := by
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
    congr 1
    refine Finset.filter_congr fun x hx => isOnePos_iff ?_
    rw [Finset.mem_range] at hx
    omega
  have hp : IsOnePos m := (isOnePos_iff hm).2 hq
  rw [A285127, ← hc, ← hcount, Nat.nth_count hp]

/-! ## Examples against the OEIS data -/

/-- The first 86 terms of A285125 match the OEIS DATA line. -/
example : (List.range 86).map (fun n => A285125 (n + 1)) =
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0,
      1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] := by
  rw [List.map_congr_left (g := fun n => (iter (2 * 3)).getD n 0) fun n hn => by
    rw [List.mem_range] at hn
    rw [A285125_eq_getD (by omega), Nat.add_sub_cancel]]
  decide +kernel

/-- The first 56 terms of A285127 match the OEIS DATA line. -/
example : ∀ n, n < 56 → A285127 (n + 1) =
    [5, 11, 17, 23, 25, 27, 29, 31, 37, 43, 49, 55, 61, 63, 65, 67, 69, 75, 81, 87, 93, 99, 101,
      103, 105, 107, 113, 119, 125, 131, 137, 139, 141, 143, 145, 151, 153, 155, 157, 159, 165,
      167, 169, 171, 173, 179, 181, 183, 185, 187, 193, 195, 197, 199, 201, 207].getD n 0 := by
  intro n hn
  interval_cases n <;>
    exact A285127_eq_of (by norm_num) (by decide +kernel) (by decide +kernel)

/-- `a(1) = 5`. -/
theorem A285127_one : A285127 1 = 5 :=
  A285127_eq_of (by norm_num) (by decide +kernel) (by decide +kernel)

/-- `a(2) = 11`. -/
theorem A285127_two : A285127 2 = 11 :=
  A285127_eq_of (by norm_num) (by decide +kernel) (by decide +kernel)

/-- `a(4) = 23`. -/
theorem A285127_four : A285127 4 = 23 :=
  A285127_eq_of (by norm_num) (by decide +kernel) (by decide +kernel)

/-! ## The conjecture -/

/-- The conjectured two-sided bound for a given constant `r`:
`-3 < n*r - a(n) < 0` for every `n ≥ 1`. -/
def BoundsWith (r : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    -3 < (n : ℝ) * r - (A285127 n : ℝ) ∧ (n : ℝ) * r - (A285127 n : ℝ) < 0

/-- Kimberling's conjecture (OEIS A285127, April 19, 2017):
`-3 < nr - a(n) < 0` for all `n ≥ 1`, where `r = 3.5621...`.
The decimal specification is interpreted as `3.5621 ≤ r < 3.5622`. -/
def Conjecture : Prop := ∃ r : ℝ, 3.5621 ≤ r ∧ r < 3.5622 ∧ BoundsWith r

/-! ## The refutation -/

/-- Since `a(2) = 11`, every `r < 4` (in particular `r = 3.5621...`)
gives `2r - a(2) < -3`. -/
theorem two_mul_sub_A285127_two_lt {r : ℝ} (hr : r < 4) :
    (2 : ℝ) * r - (A285127 2 : ℝ) < -3 := by
  rw [A285127_two]
  push_cast
  linarith

/-- No real constant `r` makes the bound hold: `a(1) = 5` forces `r < 5`,
while `a(4) = 23` forces `4*r > 20`. -/
theorem not_boundsWith (r : ℝ) : ¬ BoundsWith r := by
  intro h
  have h1 := (h 1 le_rfl).2
  have h4 := (h 4 (by norm_num)).1
  rw [A285127_one] at h1
  rw [A285127_four] at h4
  push_cast at h1 h4
  linarith

/-- Kimberling's A285127 conjecture fails at `n = 2`: `a(2) = 11`
and `2r - 11 < -3` for every `r = 3.5621...`.
Moreover, `not_boundsWith` excludes every real constant `r`. -/
theorem conjecture_false : ¬ Conjecture := by
  rintro ⟨r, _, hr, h⟩
  have h2 := (h 2 (by norm_num)).1
  have hlt := two_mul_sub_A285127_two_lt (r := r) (by linarith)
  push_cast at h2 hlt
  linarith

end Candidates.A285127Refutation
