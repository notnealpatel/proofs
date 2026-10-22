/-
# A100691 — Mathar: a(n) = A193641(n+2) - 3 (strip SAWs vs. zero-window words)

## OEIS source (retrieved with `oeis show A100691`, `oeis show A193641`, 2026-10-21)

```
A100691
NAME:     Number of self-avoiding paths with n steps on a triangular lattice in
          the strip Z x {0,1}.
TERMS:    1,4,12,30,70,158,352,780,1724,3806,8398,18526,40864,90132,198796,
          438462,967062,2132926,4704320,10375708,22884348,50473022,111321758,
          245527870,541528768,1194379300,2634286476,5810101726,12814582758
OFFSET:   0
REFERENCE: J. Labelle, Paths in the Cartesian, triangular and hexagonal
          lattices, Bulletin of the ICA, 17, 1996, pp. 47-61.
FORMULA:  G.f.: (1+z^2)(1+z+z^2)/[(1-z)(1-2z-z^3)]
          a(n) = 2*a(n-1) + a(n-3) + 6 for n >= 4.
FORMULA (the conjecture):
          Conjecture: a(n) = A193641(n+2)-3, n>0 - _R. J. Mathar_, Jul 22 2022

A193641
NAME:     Number of arrays of -1..1 integers x(1..n) with every x(i) in a
          subsequence of length 1 or 2 with sum zero.
TERMS:    1,1,3,7,15,33,73,161,355,783,1727,3809,8401,18529,40867,...
FORMULA:  Empirical: a(n) = 2*a(n-1) + a(n-3).
          Empirical: G.f.: -x*(1+x+x^2) / ( -1+2*x+x^3 ); ...
```

## Literature status (triage)

"unclear": the A100691 g.f. is attributed to Labelle (1996); the A193641 g.f.
and recurrence are marked "Empirical" in that entry.

## What this file establishes

* **The entry's DATA disagree with its NAME from `n = 5` on.**  Read literally
  (n-step self-avoiding walks from a fixed vertex of the two-row strip of the
  triangular lattice), the count is `1, 4, 12, 30, 70, 160, …`, not `…, 158`.
  `stripSAWCount_five` proves `160` by a kernel-checked depth-first count that is
  proved equal to the declarative definition (`stripSAWCount_eq_dfs`).
* **Hence Mathar's conjecture is false for the sequence its NAME defines**:
  `mathar_conjecture_false` (witness `n = 5`: `160 + 3 ≠ 161 = A193641(7)`).
* **The identity is true for the DATA**: with `a100691Data` the entry's listed
  terms (its recurrence, checked against all 29 listed terms),
  `a100691Data_add_three` proves `a(n) + 3 = A193641(n+2)` for every `n > 0`.
  The load-bearing step is `wordCount_add_three`, a proof of A193641's
  "Empirical" recurrence `a(n) = 2*a(n-1) + a(n-3)` by a transfer argument on
  the first letter.

Computational evidence (Python, not part of the proof): two independent
brute-force models of the literal count (6-direction walks in `ℤ × {0,1}`, and
walks on `ℤ` with steps `±1, ±2`, the same graph) agree for `n ≤ 12`; the second
was run to `n = 18`, and its first 19 terms fit
`(1+z^2-z^3+z^5)/((1-z)^2(1-2z-z^3))`, which differs from Labelle's g.f. by
exactly `2z^5/((1-z)^2(1-2z-z^3))`.  The same program reproduces the square
lattice strip sequence A038577 exactly, calibrating the "from a fixed vertex"
convention.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false

namespace Candidates.A100691MatharCountsWords

/-! ## Counting helper -/

/-- Splitting a tuple `Fin (n + 1) → α` into its head and tail: the number of
tuples satisfying `P` is the sum over the head `a` of the number of tails `t`
with `P (Fin.cons a t)`. -/
theorem card_filter_fin_succ {α : Type*} [Fintype α] (n : ℕ)
    (P : (Fin (n + 1) → α) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      ∑ a : α, (Finset.univ.filter (fun t : Fin n → α => P (Fin.cons a t))).card := by
  simp only [Finset.card_filter]
  rw [← (Fin.consEquiv (fun _ => α)).sum_comp, Fintype.sum_prod_type]
  rfl

/-! ## A100691 by its NAME: self-avoiding walks in the triangular strip -/

/-- The six unit steps of the triangular lattice on `ℤ × ℤ`: the neighbours of a
vertex are at offsets `(±1, 0)`, `(0, ±1)` and `±(1, -1)`. -/
def triStep : Fin 6 → ℤ × ℤ
  | 0 => (1, 0)
  | 1 => (-1, 0)
  | 2 => (0, 1)
  | 3 => (0, -1)
  | 4 => (1, -1)
  | 5 => (-1, 1)

/-- The list of vertices visited by the walk that starts at `p` and follows the
steps `l` (length `l.length + 1`). -/
def walkFrom (p : ℤ × ℤ) (l : List (Fin 6)) : List (ℤ × ℤ) :=
  (l.map triStep).scanl (· + ·) p

/-- A vertex lies in the strip `ℤ × {0, 1}`. -/
def InStrip (v : ℤ × ℤ) : Prop := v.2 = 0 ∨ v.2 = 1

/-- Membership in the strip is decidable. -/
instance : DecidablePred InStrip := fun v => by unfold InStrip; infer_instance

/-- A step sequence `s` of length `n` is a self-avoiding path in the strip: the
walk from the origin `(0,0)` visits pairwise distinct vertices, all of them in
`ℤ × {0,1}`.  Since `triStep` is injective, step sequences and vertex sequences
from the origin determine each other. -/
def IsStripSAW {n : ℕ} (s : Fin n → Fin 6) : Prop :=
  (walkFrom 0 (List.ofFn s)).Nodup ∧ ∀ v ∈ walkFrom 0 (List.ofFn s), InStrip v

/-- Being a strip self-avoiding path is decidable. -/
instance {n : ℕ} : DecidablePred (IsStripSAW (n := n)) := fun s => by
  unfold IsStripSAW; infer_instance

/-- **A100691 as named**: the number of self-avoiding paths with `n` steps on the
triangular lattice in the strip `ℤ × {0,1}`, starting at the origin. -/
def stripSAWCount (n : ℕ) : ℕ := (Finset.univ.filter (IsStripSAW (n := n))).card

-- Sanity: the six steps are distinct, so step sequences encode paths faithfully.
example : Function.Injective triStep := by decide

-- Ground truth against the DATA line `1, 4, 12, 30, …` (direct evaluation of the
-- declarative definition).
example : stripSAWCount 0 = 1 := by decide
example : stripSAWCount 1 = 4 := by decide
example : stripSAWCount 2 = 12 := by decide
example : stripSAWCount 3 = 30 := by decide

/-! ### A depth-first count, proved equal to the definition -/

/-- Depth-first count of the `n`-step continuations from the current vertex `p`
that stay in the strip and avoid the already visited vertices `V`. -/
def dfs : List (ℤ × ℤ) → ℤ × ℤ → ℕ → ℕ
  | _, _, 0 => 1
  | V, p, n + 1 => ∑ a : Fin 6,
      if InStrip (p + triStep a) ∧ p + triStep a ∉ V then
        dfs ((p + triStep a) :: V) (p + triStep a) n else 0

/-- The walk from `p` along `l` is admissible after the visited set `V`: it is
self-avoiding, stays in the strip, and its vertices after `p` avoid `V`. -/
def Good (V : List (ℤ × ℤ)) (p : ℤ × ℤ) (l : List (Fin 6)) : Prop :=
  (walkFrom p l).Nodup ∧ (∀ v ∈ walkFrom p l, InStrip v) ∧ ∀ v ∈ (walkFrom p l).tail, v ∉ V

/-- Admissibility is decidable. -/
instance (V : List (ℤ × ℤ)) (p : ℤ × ℤ) : DecidablePred (Good V p) := fun l => by
  unfold Good; infer_instance

/-- The walk from `p` with first step `a` is `p` followed by the walk from
`p + triStep a`. -/
theorem walkFrom_cons (p : ℤ × ℤ) (a : Fin 6) (l : List (Fin 6)) :
    walkFrom p (a :: l) = p :: walkFrom (p + triStep a) l := by
  simp [walkFrom, List.scanl_cons]

/-- Every walk from `p` begins with `p`. -/
theorem walkFrom_eq_cons_tail (p : ℤ × ℤ) (l : List (Fin 6)) :
    walkFrom p l = p :: (walkFrom p l).tail := by
  cases l with
  | nil => simp [walkFrom]
  | cons a l => simp [walkFrom_cons]

/-- First-step decomposition of admissibility, when the current vertex `p` is
already visited and lies in the strip. -/
theorem good_cons_iff (V : List (ℤ × ℤ)) (p : ℤ × ℤ) (hpV : p ∈ V) (hp : InStrip p)
    (a : Fin 6) (l : List (Fin 6)) :
    Good V p (a :: l) ↔ (InStrip (p + triStep a) ∧ p + triStep a ∉ V) ∧
      Good ((p + triStep a) :: V) (p + triStep a) l := by
  obtain ⟨rest, hw⟩ : ∃ rest, walkFrom (p + triStep a) l = (p + triStep a) :: rest :=
    ⟨_, walkFrom_eq_cons_tail _ l⟩
  unfold Good
  rw [walkFrom_cons, hw]
  simp only [List.nodup_cons, List.mem_cons, List.tail_cons, forall_eq_or_imp, not_or]
  constructor
  · rintro ⟨⟨_, hq1, hnd⟩, ⟨_, hqs, hrs⟩, hqV, hrV⟩
    refine ⟨⟨hqs, hqV⟩, ⟨hq1, hnd⟩, ⟨hqs, hrs⟩, fun v hv => ⟨?_, hrV v hv⟩⟩
    rintro rfl
    exact hq1 hv
  · rintro ⟨⟨hqs, hqV⟩, ⟨hq1, hnd⟩, ⟨_, hrs⟩, hrV⟩
    refine ⟨⟨⟨?_, ?_⟩, hq1, hnd⟩, ⟨hp, hqs, hrs⟩, hqV, fun v hv => (hrV v hv).2⟩
    · intro hpq
      exact hqV (hpq ▸ hpV)
    · intro hpr
      exact (hrV p hpr).2 hpV

/-- The number of admissible `n`-step walks from a visited strip vertex `p` is the
depth-first count `dfs V p n`. -/
theorem card_good_eq_dfs (n : ℕ) : ∀ (V : List (ℤ × ℤ)) (p : ℤ × ℤ), p ∈ V → InStrip p →
    (Finset.univ.filter (fun s : Fin n → Fin 6 => Good V p (List.ofFn s))).card =
      dfs V p n := by
  induction n with
  | zero =>
    intro V p _ hp
    simp [dfs, Good, walkFrom, hp]
  | succ n ih =>
    intro V p hpV hp
    rw [card_filter_fin_succ, dfs]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
    simp_rw [good_cons_iff V p hpV hp a]
    split_ifs with h
    · simp only [h, not_false_eq_true, true_and]
      exact ih _ _ List.mem_cons_self h.1
    · simp [h]

/-- The declarative strip count equals the depth-first count from the origin. -/
theorem stripSAWCount_eq_dfs (n : ℕ) : stripSAWCount n = dfs [0] 0 n := by
  rw [← card_good_eq_dfs n [0] 0 List.mem_cons_self (Or.inl rfl)]
  unfold stripSAWCount
  congr 1
  apply Finset.filter_congr
  intro s _
  unfold IsStripSAW Good
  constructor
  · rintro ⟨hnd, hs⟩
    refine ⟨hnd, hs, fun v hv hv0 => ?_⟩
    rw [walkFrom_eq_cons_tail] at hnd
    rw [List.mem_singleton] at hv0
    subst hv0
    exact (List.nodup_cons.mp hnd).1 hv
  · rintro ⟨hnd, hs, _⟩
    exact ⟨hnd, hs⟩

/-- The literal strip count at `n = 4` is `70`, matching the DATA line. -/
theorem stripSAWCount_four : stripSAWCount 4 = 70 := by
  rw [stripSAWCount_eq_dfs]
  decide

/-- **The literal strip count at `n = 5` is `160`**, whereas the A100691 DATA line
lists `158`.  (Python enumeration, outside the proof: among the 160 walks are
`(0,0),(1,0),(2,0),(1,1),(0,1),(-1,1)` and
`(0,0),(-1,0),(-2,0),(-2,1),(-1,1),(0,1)`, which cross back over the starting
column after a turn.) -/
theorem stripSAWCount_five : stripSAWCount 5 = 160 := by
  rw [stripSAWCount_eq_dfs]
  decide

/-- The literal strip count at `n = 6` is `360`; the DATA line lists `352`. -/
theorem stripSAWCount_six : stripSAWCount 6 = 360 := by
  rw [stripSAWCount_eq_dfs]
  decide

/-! ## A193641: words over `{-1, 0, 1}` covered by zero-sum windows -/

/-- The letter `-1`, `0`, `1` encoded by `0, 1, 2 : Fin 3`. -/
def letter (a : Fin 3) : ℤ := (a : ℤ) - 1

/-- **A193641's condition**: every position `i` of the word lies in a contiguous
window of length 1 or 2 with sum zero, i.e. `x i = 0`, or `x i + x (i+1) = 0`,
or `x (i-1) + x i = 0`. -/
def IsGoodWord {n : ℕ} (x : Fin n → Fin 3) : Prop :=
  ∀ i : Fin n, letter (x i) = 0 ∨
    (∃ j : Fin n, j.val = i.val + 1 ∧ letter (x i) + letter (x j) = 0) ∨
    (∃ j : Fin n, j.val + 1 = i.val ∧ letter (x j) + letter (x i) = 0)

/-- The A193641 condition is decidable. -/
instance {n : ℕ} : DecidablePred (IsGoodWord (n := n)) := fun x => by
  unfold IsGoodWord; infer_instance

/-- **A193641(n)**: the number of words of length `n` over `{-1, 0, 1}` in which
every letter lies in a length-1 or length-2 window summing to zero. -/
def wordCount (n : ℕ) : ℕ := (Finset.univ.filter (IsGoodWord (n := n))).card

-- Ground truth against the A193641 DATA line `1, 1, 3, 7, 15, 33, …`.
example : wordCount 0 = 1 ∧ wordCount 1 = 1 ∧ wordCount 2 = 3 ∧ wordCount 3 = 7 := by
  decide
example : wordCount 4 = 15 := by decide
example : wordCount 5 = 33 := by decide

/-! ### Transfer argument on the first letter -/

/-- The A193641 condition for a word preceded by a (virtual) left neighbour of
value `b`; `b = 0` means no constraining neighbour. -/
def GoodL (b : ℤ) {n : ℕ} (x : Fin n → Fin 3) : Prop :=
  ∀ i : Fin n, letter (x i) = 0 ∨
    (∃ j : Fin n, j.val = i.val + 1 ∧ letter (x i) + letter (x j) = 0) ∨
    (∃ j : Fin n, j.val + 1 = i.val ∧ letter (x j) + letter (x i) = 0) ∨
    (i.val = 0 ∧ b + letter (x i) = 0)

/-- The left-neighbour condition is decidable. -/
instance (b : ℤ) {n : ℕ} : DecidablePred (GoodL b (n := n)) := fun x => by
  unfold GoodL; infer_instance

/-- First-letter decomposition: `a :: t` is good after left neighbour `b` iff the
first letter is covered (by itself, by `t`'s first letter, or by `b`) and `t` is
good after left neighbour `a`. -/
theorem goodL_cons_iff (b : ℤ) {n : ℕ} (a : Fin 3) (t : Fin n → Fin 3) :
    GoodL b (Fin.cons a t : Fin (n + 1) → Fin 3) ↔
      (letter a = 0 ∨ (∃ j : Fin n, j.val = 0 ∧ letter a + letter (t j) = 0) ∨
        b + letter a = 0) ∧ GoodL (letter a) t := by
  unfold GoodL
  rw [Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.exists_fin_succ, Fin.val_zero, Fin.val_succ]
  simp only [zero_add, zero_ne_one, false_and, Nat.add_eq_right, false_or,
    one_ne_zero, Nat.add_eq_zero_iff, and_false, and_self, exists_false, or_self, true_and,
    Nat.right_eq_add, OfNat.ofNat_ne_zero, Nat.add_right_cancel_iff, or_false,
    and_congr_right_iff]
  intro _
  exact forall_congr' fun _ => or_congr_right (or_congr_right or_comm)

/-- Number of words of length `n` good after left neighbour `b`. -/
def hCount (b : ℤ) (n : ℕ) : ℕ := (Finset.univ.filter (GoodL b (n := n))).card

/-- Number of words of length `n` good after left neighbour `b` whose first
letter is `-b` (so that it also covers the neighbour). -/
def kCount (b : ℤ) (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun t : Fin n → Fin 3 =>
    (∃ j : Fin n, j.val = 0 ∧ b + letter (t j) = 0) ∧ GoodL b t)).card

/-- The empty word is good. -/
theorem hCount_zero (b : ℤ) : hCount b 0 = 1 := by
  unfold hCount
  rw [Finset.filter_true_of_mem fun x _ i => i.elim0]
  rfl

/-- The empty word has no first letter. -/
theorem kCount_zero (b : ℤ) : kCount b 0 = 0 := by
  simp [kCount]

/-- Transfer equation for `hCount`. -/
theorem hCount_succ (b : ℤ) (n : ℕ) :
    hCount b (n + 1) = ∑ a : Fin 3,
      if letter a = 0 ∨ b + letter a = 0 then hCount (letter a) n else kCount (letter a) n := by
  unfold hCount kCount
  rw [card_filter_fin_succ]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp_rw [goodL_cons_iff]
  split_ifs with h
  · congr 1
    apply Finset.filter_congr
    intro t _
    constructor
    · exact fun ht => ht.2
    · intro ht
      refine ⟨?_, ht⟩
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  · congr 1
    apply Finset.filter_congr
    intro t _
    rw [not_or] at h
    constructor
    · rintro ⟨h1 | h1 | h1, h2⟩
      · exact absurd h1 h.1
      · exact ⟨h1, h2⟩
      · exact absurd h1 h.2
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inr (Or.inl h1), h2⟩

/-- Transfer equation for `kCount`. -/
theorem kCount_succ (b : ℤ) (n : ℕ) :
    kCount b (n + 1) = ∑ c : Fin 3, if b + letter c = 0 then hCount (letter c) n else 0 := by
  unfold hCount kCount
  rw [card_filter_fin_succ]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp_rw [goodL_cons_iff, Fin.exists_fin_succ]
  simp only [Fin.cons_zero, Fin.val_zero, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero,
    and_false, false_and, exists_false, or_false, true_and]
  split_ifs with h
  · congr 1
    apply Finset.filter_congr
    intro t _
    simp [h]
  · simp [h]

/-- `0 : Fin 3` encodes the letter `-1`. -/
theorem letter_zero : letter 0 = -1 := rfl

/-- `1 : Fin 3` encodes the letter `0`. -/
theorem letter_one : letter 1 = 0 := rfl

/-- `2 : Fin 3` encodes the letter `1`. -/
theorem letter_two : letter 2 = 1 := rfl

/-- Transfer equation, left neighbour `0`. -/
theorem hCount_zero_succ (n : ℕ) :
    hCount 0 (n + 1) = kCount (-1) n + hCount 0 n + kCount 1 n := by
  rw [hCount_succ, Fin.sum_univ_three]
  simp [letter_zero, letter_one, letter_two]

/-- Transfer equation, left neighbour `1`. -/
theorem hCount_one_succ (n : ℕ) :
    hCount 1 (n + 1) = hCount (-1) n + hCount 0 n + kCount 1 n := by
  rw [hCount_succ, Fin.sum_univ_three]
  simp [letter_zero, letter_one, letter_two]

/-- Transfer equation, left neighbour `-1`. -/
theorem hCount_neg_one_succ (n : ℕ) :
    hCount (-1) (n + 1) = kCount (-1) n + hCount 0 n + hCount 1 n := by
  rw [hCount_succ, Fin.sum_univ_three]
  simp [letter_zero, letter_one, letter_two]

/-- Forced first letter `-1` after neighbour `1`. -/
theorem kCount_one_succ (n : ℕ) : kCount 1 (n + 1) = hCount (-1) n := by
  rw [kCount_succ, Fin.sum_univ_three]
  simp [letter_zero, letter_one, letter_two]

/-- Forced first letter `1` after neighbour `-1`. -/
theorem kCount_neg_one_succ (n : ℕ) : kCount (-1) (n + 1) = hCount 1 n := by
  rw [kCount_succ, Fin.sum_univ_three]
  simp [letter_zero, letter_one, letter_two]

/-- A193641 is the left-neighbour-`0` count. -/
theorem wordCount_eq_hCount (n : ℕ) : wordCount n = hCount 0 n := by
  unfold wordCount hCount
  congr 1
  apply Finset.filter_congr
  intro x _
  unfold IsGoodWord GoodL
  refine forall_congr' fun i => ?_
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · rintro (h | h | h | ⟨_, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl (by simpa using h)

/-- **A193641's "Empirical" recurrence, proved**: `a(n+3) = 2 a(n+2) + a(n)` for
all `n ≥ 0`. -/
theorem wordCount_add_three (n : ℕ) :
    wordCount (n + 3) = 2 * wordCount (n + 2) + wordCount n := by
  simp only [wordCount_eq_hCount]
  have e1 : hCount 0 (n + 3) = kCount (-1) (n + 2) + hCount 0 (n + 2) + kCount 1 (n + 2) :=
    hCount_zero_succ (n + 2)
  have e2 : kCount (-1) (n + 2) = hCount 1 (n + 1) := kCount_neg_one_succ (n + 1)
  have e3 : kCount 1 (n + 2) = hCount (-1) (n + 1) := kCount_one_succ (n + 1)
  have e4 := hCount_one_succ n
  have e5 := hCount_neg_one_succ n
  have e6 : hCount 0 (n + 2) = kCount (-1) (n + 1) + hCount 0 (n + 1) + kCount 1 (n + 1) :=
    hCount_zero_succ (n + 1)
  have e7 := kCount_neg_one_succ n
  have e8 := kCount_one_succ n
  have e9 := hCount_zero_succ n
  omega

/-- `A193641(7) = 161`, from the proved recurrence. -/
theorem wordCount_seven : wordCount 7 = 161 := by
  have h0 : wordCount 0 = 1 := by decide
  have h1 : wordCount 1 = 1 := by decide
  have h2 : wordCount 2 = 3 := by decide
  have w3 := wordCount_add_three 0
  have w4 := wordCount_add_three 1
  have w5 := wordCount_add_three 2
  have w6 := wordCount_add_three 3
  have w7 := wordCount_add_three 4
  simp only [Nat.reduceAdd] at w3 w4 w5 w6 w7
  omega

/-! ## A100691 by its DATA -/

/-- **A100691 as listed**: the entry's terms, generated by its recurrence
`a(n) = 2 a(n-1) + a(n-3) + 6` (`n ≥ 4`) from `1, 4, 12, 30`; these are the
coefficients of Labelle's g.f. `(1+z^2)(1+z+z^2)/((1-z)(1-2z-z^3))`. -/
def a100691Data : ℕ → ℕ
  | 0 => 1
  | 1 => 4
  | 2 => 12
  | 3 => 30
  | n + 4 => 2 * a100691Data (n + 3) + a100691Data (n + 1) + 6

-- Ground truth: all 29 listed DATA terms of A100691.
example : (List.range 29).map a100691Data =
    [1, 4, 12, 30, 70, 158, 352, 780, 1724, 3806, 8398, 18526, 40864, 90132, 198796,
      438462, 967062, 2132926, 4704320, 10375708, 22884348, 50473022, 111321758,
      245527870, 541528768, 1194379300, 2634286476, 5810101726, 12814582758] := by
  decide

/-! ## The conjecture -/

/-- **Mathar's conjecture is false for A100691 as named (R. J. Mathar, Jul 22 2022).**

Verbatim: "Conjecture: a(n) = A193641(n+2)-3, n>0".  With `a(n)` the number of
`n`-step self-avoiding paths in the triangular strip `ℤ × {0,1}` (the entry's
NAME) and A193641 the zero-window word count, the identity fails at `n = 5`:
`stripSAWCount 5 + 3 = 163`, while `wordCount 7 = 161`. -/
theorem mathar_conjecture_false :
    ¬ ∀ n : ℕ, 0 < n → stripSAWCount n + 3 = wordCount (n + 2) := by
  intro h
  have h5 := h 5 (by decide)
  rw [stripSAWCount_five, wordCount_seven] at h5
  omega

/-- The entry's DATA line disagrees with its NAME: `a(5)` is listed as `158`, but
the number of 5-step self-avoiding paths in the triangular strip is `160`. -/
theorem stripSAWCount_five_ne_data : stripSAWCount 5 ≠ a100691Data 5 := by
  rw [stripSAWCount_five]
  decide

/-- Mathar's identity holds, for the DATA sequence, on all three consecutive
indices `n + 1, n + 2, n + 3` (strengthened form for the induction). -/
theorem a100691Data_add_three_triple (n : ℕ) :
    a100691Data (n + 1) + 3 = wordCount (n + 3) ∧
      a100691Data (n + 2) + 3 = wordCount (n + 4) ∧
      a100691Data (n + 3) + 3 = wordCount (n + 5) := by
  induction n with
  | zero =>
    have h0 : wordCount 0 = 1 := by decide
    have h1 : wordCount 1 = 1 := by decide
    have h2 : wordCount 2 = 3 := by decide
    have w3 := wordCount_add_three 0
    have w4 := wordCount_add_three 1
    have w5 := wordCount_add_three 2
    simp only [Nat.reduceAdd] at w3 w4 w5
    show a100691Data 1 + 3 = wordCount 3 ∧ a100691Data 2 + 3 = wordCount 4 ∧
      a100691Data 3 + 3 = wordCount 5
    simp only [a100691Data]
    omega
  | succ n ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    refine ⟨ih2, ih3, ?_⟩
    show a100691Data (n + 4) + 3 = wordCount (n + 6)
    have hrec : a100691Data (n + 4) = 2 * a100691Data (n + 3) + a100691Data (n + 1) + 6 := rfl
    have hw : wordCount (n + 6) = 2 * wordCount (n + 5) + wordCount (n + 3) :=
      wordCount_add_three (n + 3)
    omega

/-- **Mathar's identity for the DATA of A100691 (proved).**  For every `n > 0`,
the listed term `a(n)` (Labelle's g.f. coefficients) satisfies
`a(n) = A193641(n+2) - 3`, stated additively as `a(n) + 3 = A193641(n+2)`.
The guard `0 < n` is load-bearing: `a(0) + 3 = 4 ≠ 3 = A193641(2)`. -/
theorem a100691Data_add_three (n : ℕ) (hn : 0 < n) :
    a100691Data n + 3 = wordCount (n + 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (a100691Data_add_three_triple m).1

-- The `0 < n` guard is load-bearing.
example : a100691Data 0 + 3 ≠ wordCount 2 := by decide

-- The NAME-reading identity does hold for `1 ≤ n ≤ 4`; it first fails at `n = 5`.
example : stripSAWCount 4 + 3 = wordCount 6 := by
  rw [stripSAWCount_four, wordCount_add_three 3, wordCount_add_three 0]
  decide

end Candidates.A100691MatharCountsWords
