/-
# A284366 — Kimberling's two-sided bound on the positions of 1 is false

## OEIS source (retrieved 2026-10-21 from the local OEIS store and
## https://oeis.org/A284366)

```
NAME:     Positions of 1 in A284364; complement of A284365.
TERMS:    1,3,5,7,8,10,12,14,15,17,19,21,22,24,26,28,30,32,34,35,37,39,41,42,
          44,46,48,49,51,53,55,57,59,61,62,64,66,68,69,71,73,75,76,78,80,82,84,
          86,88,89,91,93,95,96,98,100,102,103,105,107,109,110,112,114
COMMENT:  Conjecture:  -1 < n*s - a(n) < 2 for n >= 1, where s = (-1+sqrt(21))/2.
AUTHOR:   Clark Kimberling, Mar 26 2017
```

`A284364` is the "Fixed point of the morphism 0->1, 1->101010."; its program
(`Nest[Flatten[# /. {0 -> {1}, 1 -> {1, 0, 1, 0, 1, 0}}] &, {0}, 10]`)
gives the word `u = 101010110101011...`, and `a(n)` is the 1-indexed position
of the `n`-th letter `1` in `u`.  The comment line carries no separate
signature; it is part of the original entry by Clark Kimberling.  On
2026-10-21 the live entry still lists it as a conjecture, with no retraction.

## Status

This module **refutes** the conjecture: the upper bound fails at
`n = 2977771`, where `a(n) = 5334043` and `n*s - a(n) = 2.00487...`.
(The same witness refutes the `v(n)` half of the companion conjecture in
A284364.)

## Proof outline

* `W k = σ^k [1]` is a prefix of `W (k+1)` with `k < |W k|`, so the fixed point
  is `u i = (W (i+1)).getD i 0` and agrees with every `W k` inside `W k`.
* `pc k c L` counts the letters `1` in the first `L` letters of `σ^k [c]`
  by descending through the morphism one level at a time (`pc_spec`), using
  the length/ones table `stats` (`stats_spec`).  The kernel evaluates
  `pc 12 1 L` with about 70 recursive calls, so no 13-million-letter list is
  ever built.
* `Nat.nth_count` turns the two counts at `5334042` and `5334043` into
  `a 2977771 = 5334043`, and `21 * 2977771^2 > 13645861^2` gives the real
  inequality.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A284366Refutation

/-! ## Definitions mirroring the entry -/

/-- The morphism `0 ↦ 1`, `1 ↦ 101010` of A284364, on the alphabet `Fin 2`. -/
def sigma : Fin 2 → List (Fin 2)
  | 0 => [1]
  | 1 => [1, 0, 1, 0, 1, 0]

/-- The morphism extended letterwise to finite words. -/
def morph (w : List (Fin 2)) : List (Fin 2) := w.flatMap sigma

/-- The iterates `W k = σ^k [1]`; each is a prefix of the next (`W_prefix`). -/
def W (k : ℕ) : List (Fin 2) := morph^[k] [1]

/-- The fixed point `u = 101010110101011...` of the morphism (A284364), with
0-indexed letters: letter `i` is read off `W (i+1)`, which has more than `i + 1`
letters (`length_W_lt`) and is a prefix of every later iterate. -/
def u (i : ℕ) : Fin 2 := (W (i + 1)).getD i 0

/-- A284366: `a n` is the 1-indexed position of the `n`-th letter `1` of `u`
(for `n ≥ 1`); `Nat.nth` is 0-indexed in both the count and the position. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => u i = 1) (n - 1) + 1

/-- The constant `s = (-1 + √21)/2` of the conjecture. -/
noncomputable def s : ℝ := (-1 + Real.sqrt 21) / 2

/-- **Kimberling's conjecture (A284366, Mar 26 2017).**
Verbatim: "Conjecture: -1 < n*s - a(n) < 2 for n >= 1, where
s = (-1+sqrt(21))/2." -/
def Conjecture : Prop :=
  ∀ n : ℕ, 1 ≤ n → -1 < (n : ℝ) * s - (a n : ℝ) ∧ (n : ℝ) * s - (a n : ℝ) < 2

/-! ## Computable counting layer -/

/-- `stats k = ((|σ^k[0]|, #1 in σ^k[0]), (|σ^k[1]|, #1 in σ^k[1]))`, computed by
the linear recurrence of the substitution matrix (`stats_spec`). -/
def stats : ℕ → (ℕ × ℕ) × (ℕ × ℕ)
  | 0 => ((1, 0), (1, 1))
  | k + 1 =>
    let t := stats k
    ((t.2.1, t.2.2), (3 * t.2.1 + 3 * t.1.1, 3 * t.2.2 + 3 * t.1.2))

/-- `stat k c = (|σ^k[c]|, number of 1s in σ^k[c])` (`stat_spec`). -/
def stat (k : ℕ) (c : Fin 2) : ℕ × ℕ := if c = 0 then (stats k).1 else (stats k).2

/-- Given, for each letter `d`, a prefix counter `f d` and the (length, ones)
pair `st d` of a block `g d`, `pcList f st l L` counts the 1s among the first
`L` letters of the concatenation of the blocks of `l` (`pcList_spec`). -/
def pcList (f : Fin 2 → ℕ → ℕ) (st : Fin 2 → ℕ × ℕ) : List (Fin 2) → ℕ → ℕ
  | [], _ => 0
  | d :: ds, L =>
    if L ≤ (st d).1 then f d L else (st d).2 + pcList f st ds (L - (st d).1)

/-- `pc k c L` is the number of 1s among the first `L` letters of `σ^k [c]`
(`pc_spec`). -/
def pc : ℕ → Fin 2 → ℕ → ℕ
  | 0, c, L => if L = 0 then 0 else if c = 1 then 1 else 0
  | k + 1, c, L => pcList (pc k) (stat k) (sigma c) L

/-! ## Morphism algebra -/

/-- The morphism is a monoid morphism on words. -/
theorem morph_append (x y : List (Fin 2)) : morph (x ++ y) = morph x ++ morph y := by
  simp [morph]

/-- Iterates of the morphism fix the empty word. -/
theorem iter_nil (k : ℕ) : morph^[k] [] = [] := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih

/-- Iterates of the morphism distribute over concatenation. -/
theorem iter_append (k : ℕ) (x y : List (Fin 2)) :
    morph^[k] (x ++ y) = morph^[k] x ++ morph^[k] y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply, morph_append, ih]

/-- Iterates of the morphism act letterwise. -/
theorem iter_eq_flatMap (k : ℕ) (l : List (Fin 2)) :
    morph^[k] l = l.flatMap (fun c => morph^[k] [c]) := by
  induction l with
  | nil => simp [iter_nil]
  | cons c l ih =>
    rw [List.flatMap_cons, ← ih, ← iter_append]
    rfl

/-- `σ^(k+1) [c]` is the concatenation of the blocks `σ^k [d]` for `d ∈ σ c`. -/
theorem iter_succ_single (k : ℕ) (c : Fin 2) :
    morph^[k + 1] [c] = (sigma c).flatMap (fun d => morph^[k] [d]) := by
  rw [Function.iterate_succ_apply, ← iter_eq_flatMap]
  simp [morph]

/-- `stats` computes the lengths and numbers of 1s of `σ^k [0]` and `σ^k [1]`. -/
theorem stats_spec (k : ℕ) :
    stats k = (((morph^[k] [0]).length, (morph^[k] [0]).count 1),
      ((morph^[k] [1]).length, (morph^[k] [1]).count 1)) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [iter_succ_single, iter_succ_single, stats, ih]
    simp only [sigma, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.length_append, List.count_append, Prod.mk.injEq]
    exact ⟨trivial, by ring, by ring⟩

/-- `stat k c` is the length and number of 1s of `σ^k [c]`. -/
theorem stat_spec (k : ℕ) (c : Fin 2) :
    stat k c = ((morph^[k] [c]).length, (morph^[k] [c]).count 1) := by
  unfold stat
  rw [stats_spec]
  fin_cases c <;> rfl

/-- Correctness of the block-walking prefix counter. -/
theorem pcList_spec (f : Fin 2 → ℕ → ℕ) (st : Fin 2 → ℕ × ℕ) (g : Fin 2 → List (Fin 2))
    (hf : ∀ d L, f d L = ((g d).take L).count 1)
    (hst : ∀ d, st d = ((g d).length, (g d).count 1)) :
    ∀ (l : List (Fin 2)) (L : ℕ), pcList f st l L = ((l.flatMap g).take L).count 1 := by
  intro l
  induction l with
  | nil => intro L; simp [pcList]
  | cons d ds ih =>
    intro L
    rw [pcList, List.flatMap_cons, hst d, hf d]
    split_ifs with hL
    · rw [List.take_append_of_le_length hL]
    · dsimp only at hL
      rw [List.take_append, List.count_append, ih,
        List.take_of_length_le (l := g d) (by omega)]

/-- `pc k c L` counts the 1s among the first `L` letters of `σ^k [c]`. -/
theorem pc_spec (k : ℕ) :
    ∀ (c : Fin 2) (L : ℕ), pc k c L = ((morph^[k] [c]).take L).count 1 := by
  induction k with
  | zero =>
    intro c L
    rcases L with _ | L
    · simp [pc]
    · fin_cases c <;> simp [pc]
  | succ k ih =>
    intro c L
    rw [pc, iter_succ_single]
    exact pcList_spec _ _ _ ih (stat_spec k) _ _

/-! ## The iterates form a chain of prefixes -/

/-- The morphism does not shorten words. -/
theorem length_le_length_morph (w : List (Fin 2)) : w.length ≤ (morph w).length := by
  induction w with
  | nil => simp
  | cons c w ih =>
    rw [show c :: w = [c] ++ w from rfl, morph_append, List.length_append,
      List.length_append]
    have hc : 1 ≤ (morph [c]).length := by fin_cases c <;> decide
    simp only [List.length_singleton]
    omega

/-- Every iterate begins with the letter `1`. -/
theorem exists_W_eq_cons (k : ℕ) : ∃ t, W k = 1 :: t := by
  induction k with
  | zero => exact ⟨[], rfl⟩
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨[0, 1, 0, 1, 0] ++ morph t, ?_⟩
    rw [W, Function.iterate_succ_apply', ← W, ht,
      show (1 : Fin 2) :: t = [1] ++ t from rfl, morph_append]
    rfl

/-- `W k` has more than `k` letters. -/
theorem length_W_lt (k : ℕ) : k < (W k).length := by
  induction k with
  | zero => decide
  | succ k ih =>
    obtain ⟨t, ht⟩ := exists_W_eq_cons k
    have h1 : (W (k + 1)).length = 6 + (morph t).length := by
      rw [W, Function.iterate_succ_apply', ← W, ht,
        show (1 : Fin 2) :: t = [1] ++ t from rfl, morph_append, List.length_append]
      rfl
    have h2 := length_le_length_morph t
    rw [ht, List.length_cons] at ih
    omega

/-- The morphism preserves prefixes. -/
theorem morph_prefix {x y : List (Fin 2)} (h : x <+: y) : morph x <+: morph y := by
  obtain ⟨t, rfl⟩ := h
  rw [morph_append]
  exact List.prefix_append _ _

/-- `W k` is a prefix of `W (k+1)`. -/
theorem W_prefix_succ (k : ℕ) : W k <+: W (k + 1) := by
  induction k with
  | zero => exact ⟨[0, 1, 0, 1, 0], rfl⟩
  | succ k ih =>
    rw [W, W, Function.iterate_succ_apply' _ k, Function.iterate_succ_apply' _ (k + 1),
      ← W, ← W]
    exact morph_prefix ih

/-- `W k` is a prefix of `W m` for `k ≤ m`. -/
theorem W_prefix {k m : ℕ} (h : k ≤ m) : W k <+: W m := by
  induction m, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ m _ ih => exact ih.trans (W_prefix_succ m)

/-- A prefix and its extension agree at every index inside the prefix. -/
theorem getD_eq_getD_of_prefix {x y : List (Fin 2)} (h : x <+: y) {i : ℕ}
    (hi : i < x.length) : x.getD i 0 = y.getD i 0 := by
  rw [List.getD_eq_getElem _ _ hi,
    List.getD_eq_getElem _ _ (lt_of_lt_of_le hi h.length_le), h.getElem hi]

/-- Letter `i` of the fixed point can be read off any iterate long enough. -/
theorem u_eq_getD (k i : ℕ) (hi : i < (W k).length) : u i = (W k).getD i 0 := by
  unfold u
  rcases le_total k (i + 1) with hk | hk
  · exact (getD_eq_getD_of_prefix (W_prefix hk) hi).symm
  · exact getD_eq_getD_of_prefix (W_prefix hk) (by have := length_W_lt (i + 1); omega)

/-- The number of 1s among the first `N` letters of `u`, read off an iterate. -/
theorem count_eq_count_take (k N : ℕ) (hN : N ≤ (W k).length) :
    Nat.count (fun i => u i = 1) N = ((W k).take N).count 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hN' : N < (W k).length := hN
    rw [Nat.count_succ, ih (le_of_lt hN'), List.take_add_one, List.count_append,
      List.getElem?_eq_getElem hN', u_eq_getD k N hN', List.getD_eq_getElem _ _ hN']
    by_cases h : (W k)[N] = 1 <;> simp [h]

/-- The number of 1s among the first `N` letters of `u`, via the counter `pc`. -/
theorem count_eq_pc (k N : ℕ) (hN : N ≤ (W k).length) :
    Nat.count (fun i => u i = 1) N = pc k 1 N := by
  rw [count_eq_count_take k N hN, pc_spec]
  rfl

/-- The length of `W k` from the table `stats`. -/
theorem length_W (k : ℕ) : (W k).length = (stats k).2.1 := by
  rw [stats_spec]
  rfl

/-- If the count of 1s steps up at `N`, then letter `N` of `u` is `1`. -/
theorem u_eq_one_of_count (N c : ℕ) (h1 : Nat.count (fun i => u i = 1) N = c)
    (h2 : Nat.count (fun i => u i = 1) (N + 1) = c + 1) : u N = 1 := by
  rw [Nat.count_succ, h1] at h2
  by_contra hne
  rw [if_neg hne] at h2
  omega

/-- If letter `N` of `u` is `1`, it is the `(count + 1)`-th 1, at position `N + 1`. -/
theorem a_count_add_one (N : ℕ) (hu : u N = 1) :
    a (Nat.count (fun i => u i = 1) N + 1) = N + 1 := by
  unfold a
  rw [Nat.add_sub_cancel, Nat.nth_count hu]

/-! ## Ground truth -/

/-- The first 86 letters of `u` (read from `W 4`, of length 306) are the listed
terms of A284364. -/
example : (W 4).take 86 = [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1,
    1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0,
    1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0,
    1, 0, 1, 0, 1, 0, 1] := by
  decide

/-- The 1-indexed positions of 1 among the first 114 letters of `W 4` are the
64 listed terms of A284366. -/
example : ((List.range 114).filter (fun i => (W 4).getD i 0 = 1)).map (· + 1) =
    [1, 3, 5, 7, 8, 10, 12, 14, 15, 17, 19, 21, 22, 24, 26, 28, 30, 32, 34, 35, 37, 39,
      41, 42, 44, 46, 48, 49, 51, 53, 55, 57, 59, 61, 62, 64, 66, 68, 69, 71, 73, 75, 76,
      78, 80, 82, 84, 86, 88, 89, 91, 93, 95, 96, 98, 100, 102, 103, 105, 107, 109, 110,
      112, 114] := by
  decide

/-- `a 1 = 1`, the first listed term, through the definition of `a`. -/
example : a 1 = 1 := by
  have hu : u 0 = 1 := by rw [u_eq_getD 1 0 (by decide)]; decide
  have h := a_count_add_one 0 hu
  rwa [Nat.count_zero] at h

/-- `a 64 = 114`, the last listed term, through the definition of `a`. -/
example : a 64 = 114 := by
  have hc : Nat.count (fun i => u i = 1) 113 = 63 := by
    rw [count_eq_pc 4 113 (by rw [length_W]; decide)]
    decide
  have hc' : Nat.count (fun i => u i = 1) 114 = 64 := by
    rw [count_eq_pc 4 114 (by rw [length_W]; decide)]
    decide
  have hu : u 113 = 1 := u_eq_one_of_count 113 63 hc hc'
  have h := a_count_add_one 113 hu
  rwa [hc] at h

/-! ## The counterexample -/

/-- `u` has exactly 2977770 letters `1` among its first 5334042 letters. -/
theorem count_5334042 : Nat.count (fun i => u i = 1) 5334042 = 2977770 := by
  rw [count_eq_pc 12 5334042 (by rw [length_W]; decide)]
  decide

/-- `u` has exactly 2977771 letters `1` among its first 5334043 letters. -/
theorem count_5334043 : Nat.count (fun i => u i = 1) 5334043 = 2977771 := by
  rw [count_eq_pc 12 5334043 (by rw [length_W]; decide)]
  decide

/-- Letter `5334042` (0-indexed) of `u` is `1`. -/
theorem u_5334042 : u 5334042 = 1 :=
  u_eq_one_of_count 5334042 2977770 count_5334042 count_5334043

/-- The 2977771-st letter `1` of `u` is at position 5334043. -/
theorem a_2977771 : a 2977771 = 5334043 := by
  have h := a_count_add_one 5334042 u_5334042
  rwa [count_5334042] at h

/-- `2977771 * s - 5334043 > 2`, from `21 * 2977771^2 > 13645861^2`. -/
theorem two_lt_witness : (2 : ℝ) < ((2977771 : ℕ) : ℝ) * s - ((5334043 : ℕ) : ℝ) := by
  have h : (13645861 / 2977771 : ℝ) < Real.sqrt 21 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  unfold s
  push_cast
  linarith

/-- **Kimberling's A284366 conjecture is false.** At `n = 2977771` one has
`a(n) = 5334043` and `n*s - a(n) = 2.00487... > 2`, so the upper bound fails
(the lower bound `-1 <` is not what breaks).  Numerically, 11 violations of the
upper bound occur among the first 33.5 million terms, the next at
`n = 5409958, 6051478`; the bound `2` was presumably read off a short prefix,
and the intended statement is a two-sided bound with a larger upper constant. -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  have hupper := (h 2977771 (by norm_num)).2
  rw [a_2977771] at hupper
  have hw := two_lt_witness
  linarith

end Candidates.A284366Refutation
