/-
# A065806 — Strassburger: the swap-process pseudo-random sequence

## OEIS source (pulled with `oeis show A065806` and the live
## `https://oeis.org/A065806/internal`, retrieved 2026-10-21)

```
NAME:     A pseudo-random sequence.
OFFSET:   1,1
AUTHOR:   Klaus Strassburger, Nov 21 2001
TERMS:    2,0,4,0,5,2,8,0,7,3,8,10,10,3,6,17,0,12,16,4,21,2,18,21,5,22,22,3,
          16,12,14,23,30,17,29,18,15,39,0,25,37,43,0,7,37,6,33,31,40,46,37,
          8,43,17,22,30,25,19,43,8,10,50,49,60,14,36,45,28,56,38,33,26,68,61,
          63,72,72,3
KEYWORDS: easy,nice,nonn
COMMENT:  The sequence looks like a realization of a sequence of independent
          random variables x(n), with probability function P(x(n) = i) =
          1/(n+2), i=0..n+1. The sequence (a(n)+1)/(n+3) seems to be a good
          U(0,1) pseudo-random number generator.
COMMENT (the conjecture; unsigned, hence by the entry author, Nov 21 2001):
          Conjectures: -1 < a(n) < n+2; If a(n) = n+1 then a(n+1) = 0; All
          integers >1 occur in the sequence; For each c in [0,1] there exists
          a subsequence a(i_j) with (a(i_j)+1)/(i_j+3)-> c, j->infinity.
MAPLE:    N := 2000: b := array(-N..N,[seq(i,i=-N..N)]): s := 0; for i from 0
          to N do; j := (b[i]-b[i-1]); s := s+1; a[s] := j+1; if j > N or
          j < -N then break; end if; c := b[i]; b[i] := b[j]; b[j] := c;
          end do: a := [seq(a[l], l=1..s)];
```

## Status

Triage: open (no proof in the entry or the literature as far as the triage
could tell).  Parts (1) and (2) are proved below by an invariant induction.
Parts (3) and (4) are pseudo-randomness claims and remain open; they are kept
as `sorry`.  Computation (2026-10-21, Python, `n ≤ 2·10^7`): (1) and (2) hold;
every `m ∈ [2, 2000)` occurs, the last one being `874` at `n = 10814791`.

## Definition layer

The Maple array `b` is modelled as a permutation `perm i : Equiv.Perm ℤ` (the
state before step `i`).  The Maple swap `c := b[i]; b[i] := b[j]; b[j] := c`
replaces `b` by `b ∘ swap i j`, i.e. `b * Equiv.swap i j`.  The step value is
`jump i = b(i) - b(i-1)` and `a(i+1) = jump i + 1` (offset 1; `a 0` is a junk
value and every statement carries `1 ≤ n`).  The Maple guard `|j| > N` never
fires because of part (1).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A065806SwapProcessStep

open Filter Topology

/-- The state of the swap process before step `i`: `perm 0 = id`, and step `i`
swaps the entries at positions `i` and `j = b(i) - b(i-1)`. -/
def perm : ℕ → Equiv.Perm ℤ
  | 0 => 1
  | i + 1 => perm i * Equiv.swap (i : ℤ) (perm i i - perm i ((i : ℤ) - 1))

/-- The step value `j = b(i) - b(i-1)` at step `i`. -/
def jump (i : ℕ) : ℤ := perm i i - perm i ((i : ℤ) - 1)

/-- A065806 (offset 1): `a(i+1) = jump i + 1`.  The value `a 0 = 0` is junk
outside the OEIS offset. -/
def a : ℕ → ℤ
  | 0 => 0
  | n + 1 => jump n + 1

set_option maxRecDepth 20000 in
/-- Ground truth: the 78 listed terms of A065806. -/
example : (List.range 78).map (fun n => a (n + 1)) =
    [2,0,4,0,5,2,8,0,7,3,8,10,10,3,6,17,0,12,16,4,21,2,18,21,5,22,22,3,
     16,12,14,23,30,17,29,18,15,39,0,25,37,43,0,7,37,6,33,31,40,46,37,
     8,43,17,22,30,25,19,43,8,10,50,49,60,14,36,45,28,56,38,33,26,68,61,
     63,72,72,3] := by
  decide

/-! ## The invariant -/

/-- The invariant of the state `b` before step `k`: `b` fixes every integer
outside `[-1, k]`, and either `b k = k` or the last step swapped `k-1` and `k`
out of the identity position (`b k = k - 1` and `b (k-1) = k`). -/
def Inv (k : ℕ) (b : Equiv.Perm ℤ) : Prop :=
  (∀ x : ℤ, x < -1 ∨ (k : ℤ) < x → b x = x) ∧
    (b k = k ∨ (b k = (k : ℤ) - 1 ∧ b ((k : ℤ) - 1) = k))

/-- Under the invariant, `b` maps `[-1, k]` into `[-1, k]`. -/
theorem Inv.mem_Icc {k : ℕ} {b : Equiv.Perm ℤ} (h : Inv k b) {x : ℤ}
    (hx1 : -1 ≤ x) (hx2 : x ≤ k) : -1 ≤ b x ∧ b x ≤ k := by
  by_contra hne
  have hout : b x < -1 ∨ (k : ℤ) < b x := by omega
  have hfix : b (b x) = b x := h.1 _ hout
  have hbx : b x = x := b.injective hfix
  omega

/-- Under the invariant, the step value `b k - b (k-1)` lies in `[-1, k+1]`,
and it equals `-1` unless `b k = k`. -/
theorem Inv.jump_bounds {k : ℕ} {b : Equiv.Perm ℤ} (h : Inv k b) :
    -1 ≤ b k - b ((k : ℤ) - 1) ∧ b k - b ((k : ℤ) - 1) ≤ k + 1 ∧
      (b k = k ∨ b k - b ((k : ℤ) - 1) = -1) := by
  rcases h.2 with hk | ⟨hk1, hk2⟩
  · have hr := h.mem_Icc (x := (k : ℤ) - 1) (by omega) (by omega)
    have hne : b ((k : ℤ) - 1) ≠ k := by
      intro heq
      have hinj : (k : ℤ) - 1 = k := b.injective (heq.trans hk.symm)
      omega
    refine ⟨by omega, by omega, Or.inl hk⟩
  · refine ⟨by omega, by omega, Or.inr (by omega)⟩

/-- One step of the swap process preserves the invariant. -/
theorem Inv.step {k : ℕ} {b : Equiv.Perm ℤ} (h : Inv k b) :
    Inv (k + 1) (b * Equiv.swap (k : ℤ) (b k - b ((k : ℤ) - 1))) := by
  obtain ⟨hlo, hhi, hcase⟩ := h.jump_bounds
  set j : ℤ := b k - b ((k : ℤ) - 1) with hj
  refine ⟨?_, ?_⟩
  · intro x hx
    have hxk : x ≠ k := by push_cast at hx; omega
    have hxj : x ≠ j := by push_cast at hx; omega
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxk hxj]
    exact h.1 x (by push_cast at hx; omega)
  · simp only [Nat.cast_add, Nat.cast_one]
    by_cases hjk : j = (k : ℤ) + 1
    · right
      have hbk : b k = k := by
        rcases hcase with hbk | hbk
        · exact hbk
        · omega
      have hfix : b ((k : ℤ) + 1) = (k : ℤ) + 1 := h.1 _ (Or.inr (by omega))
      constructor
      · rw [Equiv.Perm.mul_apply, ← hjk, Equiv.swap_apply_right, hbk]
        omega
      · have hsub : (k : ℤ) + 1 - 1 = k := by ring
        rw [hsub, Equiv.Perm.mul_apply, Equiv.swap_apply_left, hjk, hfix]
    · left
      have hne1 : (k : ℤ) + 1 ≠ k := by omega
      have hne2 : (k : ℤ) + 1 ≠ j := fun heq => hjk heq.symm
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hne1 hne2]
      exact h.1 _ (Or.inr (by omega))

/-- Every state of the swap process satisfies the invariant. -/
theorem inv_perm (k : ℕ) : Inv k (perm k) := by
  induction k with
  | zero =>
    refine ⟨fun x _ => rfl, Or.inl rfl⟩
  | succ k ih =>
    exact ih.step

/-- The step value at step `k` lies in `[-1, k+1]`. -/
theorem jump_mem_Icc (k : ℕ) : -1 ≤ jump k ∧ jump k ≤ k + 1 := by
  obtain ⟨hlo, hhi, -⟩ := (inv_perm k).jump_bounds
  exact ⟨hlo, hhi⟩

/-- If the step value at step `k` is `k + 1`, the next step value is `-1`. -/
theorem jump_succ_of_jump_eq (k : ℕ) (h : jump k = k + 1) : jump (k + 1) = -1 := by
  have hinv := inv_perm k
  obtain ⟨-, -, hcase⟩ := hinv.jump_bounds
  have hbk : perm k k = k := by
    rcases hcase with hbk | hbk
    · exact hbk
    · unfold jump at h; omega
  have hfix : perm k ((k : ℤ) + 1) = (k : ℤ) + 1 := hinv.1 _ (Or.inr (by omega))
  have hperm : perm (k + 1) = perm k * Equiv.swap (k : ℤ) ((k : ℤ) + 1) := by
    show perm k * Equiv.swap (k : ℤ) (jump k) = _
    rw [h]
  have hsub : (k : ℤ) + 1 - 1 = k := by ring
  unfold jump
  rw [hperm]
  simp only [Nat.cast_add, Nat.cast_one, hsub, Equiv.Perm.mul_apply,
    Equiv.swap_apply_right, Equiv.swap_apply_left, hbk, hfix]
  ring

/-! ## The conjecture -/

/-- **Part (1) of Strassburger's conjecture (A065806, Nov 21 2001), proved.**
"-1 < a(n) < n+2": for every `n ≥ 1`, `0 ≤ a(n) ≤ n + 1`. -/
theorem part_one (n : ℕ) (hn : 1 ≤ n) : 0 ≤ a n ∧ a n ≤ (n : ℤ) + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hlo, hhi⟩ := jump_mem_Icc k
  simp only [a, Nat.cast_add, Nat.cast_one]
  omega

/-- **Part (2) of Strassburger's conjecture (A065806, Nov 21 2001), proved.**
"If a(n) = n+1 then a(n+1) = 0", for every `n ≥ 1`. -/
theorem part_two (n : ℕ) (hn : 1 ≤ n) (h : a n = (n : ℤ) + 1) : a (n + 1) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hj : jump k = (k : ℤ) + 1 := by
    simp only [a, Nat.cast_add, Nat.cast_one] at h
    omega
  simp only [a, jump_succ_of_jump_eq k hj]
  norm_num

/-- Non-vacuity of part (2): `a 1 = 2 = 1 + 1`, so its hypothesis is met. -/
example : a 1 = ((1 : ℕ) : ℤ) + 1 ∧ a 2 = 0 := by decide

/-- **Part (3) of Strassburger's conjecture (A065806, Nov 21 2001), open.**
"All integers >1 occur in the sequence": every integer `m > 1` equals `a n`
for some `n ≥ 1`. -/
theorem part_three (m : ℤ) (hm : 1 < m) : ∃ n : ℕ, 1 ≤ n ∧ a n = m := by
  -- Open (pseudo-randomness). Remaining goal: `∃ n, 1 ≤ n ∧ a n = m` for
  -- `1 < m`; equivalently some step `k` has `perm k k = k` and
  -- `perm k (k-1) = k - m + 1`.  No structural route is known.
  sorry

/-- **Part (4) of Strassburger's conjecture (A065806, Nov 21 2001), open.**
"For each c in [0,1] there exists a subsequence a(i_j) with
(a(i_j)+1)/(i_j+3) -> c, j -> infinity": a strictly increasing index sequence
`i : ℕ → ℕ` with `1 ≤ i j` along which `(a(i j) + 1)/(i j + 3) → c`. -/
theorem part_four (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    ∃ i : ℕ → ℕ, StrictMono i ∧ (∀ j, 1 ≤ i j) ∧
      Tendsto (fun j => ((a (i j) : ℝ) + 1) / ((i j : ℝ) + 3)) atTop (𝓝 c) := by
  -- Open (equidistribution-type claim). Remaining goal is the statement
  -- itself; no structural route is known.
  sorry

/-- **Strassburger's conjecture (A065806, Nov 21 2001), all four parts.**
Verbatim: "Conjectures: -1 < a(n) < n+2; If a(n) = n+1 then a(n+1) = 0; All
integers >1 occur in the sequence; For each c in [0,1] there exists a
subsequence a(i_j) with (a(i_j)+1)/(i_j+3)-> c, j->infinity."
Parts (1) and (2) are proved; parts (3) and (4) depend on the open
`part_three` and `part_four`. -/
theorem conjecture :
    (∀ n : ℕ, 1 ≤ n → 0 ≤ a n ∧ a n ≤ (n : ℤ) + 1) ∧
    (∀ n : ℕ, 1 ≤ n → a n = (n : ℤ) + 1 → a (n + 1) = 0) ∧
    (∀ m : ℤ, 1 < m → ∃ n : ℕ, 1 ≤ n ∧ a n = m) ∧
    (∀ c ∈ Set.Icc (0 : ℝ) 1, ∃ i : ℕ → ℕ, StrictMono i ∧ (∀ j, 1 ≤ i j) ∧
      Tendsto (fun j => ((a (i j) : ℝ) + 1) / ((i j : ℝ) + 3)) atTop (𝓝 c)) :=
  ⟨part_one, part_two, part_three, part_four⟩

end Candidates.A065806SwapProcessStep
