/-
# A068722 — Zumkeller: first occurrence of `(2n+1)^2` in A255437

## OEIS source (retrieved with `oeis show A068722` / `oeis show A255437`, 2026-10-21)

```
A068722
NAME:     Number of solenoidal flows (flow in = flow out) in a 3 X 3 square
          array with integer velocities -n .. n.
TERMS:    1,35,247,925,2501,5551,10795,19097,31465,49051,73151,105205,...
FORMULA:  a(n) = (1+2*n+2*n^2) * (1+3*n+3*n^2).
COMMENT:  Conjecture: A255437(a(n)) = 2*n+1, i.e. a(n) = gives the position of
          the first occurrence of 2*n+1 in A255437. - _Reinhard Zumkeller_,
          Mar 23 2015

A255437
NAME:     In positive integers: replace k^2 with the first k odd numbers.
TERMS:    1,2,3,1,3,5,6,7,8,1,3,5,10,11,12,13,14,15,1,3,5,7,17,18,19,20,21,22,
          23,24,1,3,5,7,9,26,27,28,29,30,31,32,33,34,35,1,3,5,7,9,11,37,...
COMMENT:  conjecture: a(A068722(n)) = (2*n+1)^2, i.e. A068722(n) = gives the
          position of the first occurrence of n-th odd square;
PROGRAM:  Flatten[Table[If[IntegerQ[#], Range[1, 2*#, 2], m] & [Sqrt[m]],
          {m, 64}]] (* _Paolo Xausa_, May 02 2026 *)
```

## Which conjecture is formalized

The two entries state Zumkeller's conjecture differently.  The A255437 form
("`a(A068722(n)) = (2n+1)^2`, the first occurrence of the n-th odd square")
is the one formalized here as `first_occurrence`; it is **true** and proved
below.  The A068722 form ("`A255437(a(n)) = 2n+1`") is literally **false**
already at `n = 1`: `A255437(35) = 9 ≠ 3`; this is recorded as the
kernel-checked `not_a068722_comment_form`.

## Status

Triage status: open (no proof in the entry or literature found by the
triage).  The argument is elementary: `(2n+1)^2` is a square, so it occurs
only inside a replacement block `1, 3, …, 2K-1`, first in the block of
`K^2` with `2K - 1 = (2n+1)^2`, i.e. `K = 2n^2+2n+1`; counting the earlier
entries gives the position `K(3K-1)/2 = (2n^2+2n+1)(3n^2+3n+1)`.
Computationally re-checked for `n = 0..12` (Python, 2026-10-21).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A068722FirstOccurrenceReplaced

/-! ## Definition layer

`block m` mirrors the Mathematica program's
`If[IntegerQ[Sqrt[m]], Range[1, 2*Sqrt[m], 2], m]`, and `prefixList N` mirrors
`Flatten[Table[..., {m, N}]]`.  The sequence A255437 is read off with
1-based offsets: `a255437 p` is entry `p - 1` of `prefixList p`, which is long
enough because every block is nonempty (`le_length_prefixList`). -/

/-- The block replacing the positive integer `m` in A255437: the first
`√m` odd numbers `1, 3, …, 2√m - 1` when `m` is a perfect square, and `[m]`
otherwise. -/
def block (m : ℕ) : List ℕ :=
  if Nat.sqrt m * Nat.sqrt m = m then (List.range (Nat.sqrt m)).map (fun i => 2 * i + 1)
  else [m]

/-- The concatenation `block 1 ++ block 2 ++ ⋯ ++ block N`, i.e. the flattened
A255437 prefix produced by the integers `1..N`. -/
def prefixList (N : ℕ) : List ℕ := (List.range N).flatMap (fun i => block (i + 1))

/-- A255437 with OEIS offset 1: `a255437 p` is the `p`-th term (for `0 < p`).
The value at `p = 0` is junk and never used in statements. -/
def a255437 (p : ℕ) : ℕ := (prefixList p).getD (p - 1) 0

/-- Ground truth: the first 72 terms listed in OEIS A255437. -/
example : (List.range 72).map (fun i => a255437 (i + 1)) =
    [1, 2, 3, 1, 3, 5, 6, 7, 8, 1, 3, 5, 10, 11, 12, 13, 14, 15, 1, 3, 5, 7, 17, 18, 19, 20,
      21, 22, 23, 24, 1, 3, 5, 7, 9, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 1, 3, 5, 7, 9, 11,
      37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 1, 3, 5, 7, 9, 11, 13, 50, 51] := by
  decide +kernel

/-! ## Structural lemmas -/

/-- `prefixList` grows by appending the next block. -/
theorem prefixList_succ (N : ℕ) : prefixList (N + 1) = prefixList N ++ block (N + 1) := by
  simp [prefixList, List.range_succ, List.flatMap_append]

/-- The length of a block: `√m` for a perfect square `m`, otherwise `1`. -/
theorem length_block (m : ℕ) :
    (block m).length = if Nat.sqrt m * Nat.sqrt m = m then Nat.sqrt m else 1 := by
  unfold block; split_ifs <;> simp

/-- If `N + 1` is a perfect square then `√(N+1) = √N + 1`. -/
theorem sqrt_succ_of_square {N : ℕ} (h : Nat.sqrt (N + 1) * Nat.sqrt (N + 1) = N + 1) :
    Nat.sqrt (N + 1) = Nat.sqrt N + 1 := by
  set s := Nat.sqrt (N + 1) with hs
  have hpos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · rw [h0] at h; omega
    · exact h0
  obtain ⟨t, hst⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  rw [hst] at h
  have ht : t = Nat.sqrt N := by
    rw [Nat.eq_sqrt]
    constructor <;> nlinarith
  omega

/-- If `N + 1` is not a perfect square then `√(N+1) = √N`. -/
theorem sqrt_succ_of_not_square {N : ℕ} (h : ¬ Nat.sqrt (N + 1) * Nat.sqrt (N + 1) = N + 1) :
    Nat.sqrt (N + 1) = Nat.sqrt N := by
  have hle : Nat.sqrt (N + 1) ≤ Nat.sqrt N + 1 := Nat.sqrt_succ_le_succ_sqrt N
  have hge : Nat.sqrt N ≤ Nat.sqrt (N + 1) := Nat.sqrt_le_sqrt (Nat.le_succ N)
  rcases Nat.lt_or_ge (Nat.sqrt (N + 1)) (Nat.sqrt N + 1) with hlt | hge'
  · omega
  · exfalso
    have heq : Nat.sqrt (N + 1) = Nat.sqrt N + 1 := le_antisymm hle hge'
    have h1 : Nat.sqrt (N + 1) * Nat.sqrt (N + 1) ≤ N + 1 := Nat.sqrt_le (N + 1)
    have h2 : N < (Nat.sqrt N + 1) * (Nat.sqrt N + 1) := Nat.lt_succ_sqrt N
    rw [heq] at h h1
    omega

/-- Length count: with `s = √N`, the prefix has `N - s` non-square entries
plus `1 + 2 + ⋯ + s` block entries, i.e. `2·len + 2s = 2N + s(s+1)`. -/
theorem two_mul_length_prefixList (N : ℕ) :
    2 * (prefixList N).length + 2 * Nat.sqrt N = 2 * N + Nat.sqrt N * (Nat.sqrt N + 1) := by
  induction N with
  | zero => simp [prefixList]
  | succ N ih =>
    rw [prefixList_succ, List.length_append, length_block]
    split_ifs with h
    · have hs := sqrt_succ_of_square h
      rw [hs] at h ⊢
      nlinarith
    · rw [sqrt_succ_of_not_square h]
      omega

/-- Every block is nonempty, so `prefixList N` has at least `N` entries. -/
theorem le_length_prefixList (N : ℕ) : N ≤ (prefixList N).length := by
  have h := two_mul_length_prefixList N
  have hs : 2 * Nat.sqrt N ≤ Nat.sqrt N * (Nat.sqrt N + 1) := by
    rcases Nat.eq_zero_or_pos (Nat.sqrt N) with h0 | h0
    · rw [h0]
    · nlinarith
  omega

/-- The prefixes are nested: `prefixList N` is a prefix of `prefixList M` for `N ≤ M`. -/
theorem prefixList_prefix {N M : ℕ} (h : N ≤ M) : prefixList N <+: prefixList M := by
  induction M, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ M _ ih =>
    rw [prefixList_succ]
    exact ih.trans (List.prefix_append _ _)

/-- The `p`-th term of A255437 can be read off any prefix long enough to contain it. -/
theorem a255437_eq_getD {p M : ℕ} (hp : 0 < p) (hM : p ≤ (prefixList M).length) :
    a255437 p = (prefixList M).getD (p - 1) 0 := by
  unfold a255437
  have hpl : p ≤ (prefixList p).length := le_length_prefixList p
  rcases le_total p M with h | h
  · have hpre := prefixList_prefix h
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    exact hpre.getElem (by omega)
  · have hpre := prefixList_prefix h
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    exact (hpre.getElem (by omega)).symm

/-- Every entry of `prefixList N` is either a non-square (a kept integer) or an
odd number from some block, hence smaller than `2√N`. -/
theorem mem_prefixList {N x : ℕ} (hx : x ∈ prefixList N) :
    Nat.sqrt x * Nat.sqrt x ≠ x ∨ x < 2 * Nat.sqrt N := by
  simp only [prefixList, List.mem_flatMap, List.mem_range] at hx
  obtain ⟨i, hi, hxb⟩ := hx
  unfold block at hxb
  split_ifs at hxb with hsq
  · right
    simp only [List.mem_map, List.mem_range] at hxb
    obtain ⟨j, hj, rfl⟩ := hxb
    have hmono : Nat.sqrt (i + 1) ≤ Nat.sqrt N := Nat.sqrt_le_sqrt (by omega)
    omega
  · left
    simp only [List.mem_singleton] at hxb
    rw [hxb]
    exact hsq

/-- The block replacing `(k+1)^2` is `1, 3, …, 2k+1`. -/
theorem block_square (k : ℕ) :
    block ((k + 1) * (k + 1)) = (List.range (k + 1)).map (fun i => 2 * i + 1) := by
  unfold block
  rw [Nat.sqrt_eq, if_pos rfl]

/-! ## The conjecture -/

/-- **Zumkeller's conjecture (A255437 / A068722, Reinhard Zumkeller, Mar 23 2015).**

Verbatim (A255437): "conjecture: a(A068722(n)) = (2*n+1)^2, i.e. A068722(n) =
gives the position of the first occurrence of n-th odd square".

For every `n ≥ 0`, with `P = (1+2n+2n^2)(1+3n+3n^2) = A068722(n)`, the term
`A255437(P)` equals `(2n+1)^2`, and no earlier term `A255437(p)`, `1 ≤ p < P`,
equals `(2n+1)^2`.  Proved here. -/
theorem first_occurrence (n : ℕ) :
    a255437 ((1 + 2 * n + 2 * n ^ 2) * (1 + 3 * n + 3 * n ^ 2)) = (2 * n + 1) ^ 2 ∧
      ∀ p, 0 < p → p < (1 + 2 * n + 2 * n ^ 2) * (1 + 3 * n + 3 * n ^ 2) →
        a255437 p ≠ (2 * n + 1) ^ 2 := by
  -- `K = k + 1 = 2n^2 + 2n + 1` is the block containing `(2n+1)^2 = 2K - 1`;
  -- `N0 = K^2 - 1` is the last integer before that block.
  set k := 2 * n ^ 2 + 2 * n with hk
  set N0 := k * k + 2 * k with hN0
  have hsq : N0 + 1 = (k + 1) * (k + 1) := by rw [hN0]; ring
  have hsqrt : Nat.sqrt N0 = k := Nat.sqrt_add_eq k (by omega)
  set L0 := (prefixList N0).length with hL0
  have hlen := two_mul_length_prefixList N0
  rw [hsqrt, ← hL0] at hlen
  have hT : (2 * n + 1) ^ 2 = 2 * k + 1 := by rw [hk]; ring
  -- the target position is `L0 + K`
  have hP : (1 + 2 * n + 2 * n ^ 2) * (1 + 3 * n + 3 * n ^ 2) = L0 + k + 1 := by
    rw [hN0, hk] at hlen
    rw [hk]
    nlinarith
  have hsplit : prefixList (N0 + 1) =
      prefixList N0 ++ (List.range (k + 1)).map (fun i => 2 * i + 1) := by
    rw [prefixList_succ, hsq, block_square]
  have hlenM : (prefixList (N0 + 1)).length = L0 + k + 1 := by
    rw [hsplit, List.length_append, List.length_map, List.length_range, ← hL0]
    omega
  rw [hP, hT]
  constructor
  · rw [a255437_eq_getD (M := N0 + 1) (by omega) (by omega), hsplit,
      List.getD_append_right _ _ _ _ (by omega),
      List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; omega)]
    simp only [List.getElem_map, List.getElem_range]
    omega
  · intro p hp hpP
    rw [a255437_eq_getD (M := N0 + 1) hp (by omega), hsplit]
    rcases Nat.lt_or_ge (p - 1) L0 with hlt | hge
    · -- an entry before the block of `K^2`
      rw [List.getD_append _ _ _ _ hlt, List.getD_eq_getElem _ _ hlt]
      have hmem : (prefixList N0)[p - 1] ∈ prefixList N0 := List.getElem_mem hlt
      rcases mem_prefixList hmem with hns | hsmall
      · intro heq
        apply hns
        rw [heq, ← hT, ← pow_two, Nat.sqrt_eq']
      · rw [hsqrt] at hsmall
        omega
    · -- an earlier entry `2i+1`, `i < k`, of the block of `K^2`
      rw [List.getD_append_right _ _ _ _ hge,
        List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; omega)]
      simp only [List.getElem_map, List.getElem_range]
      omega

/-- Non-vacuity instance of `first_occurrence` at `n = 1`: `A255437(35) = 9`. -/
example : a255437 35 = 9 := (first_occurrence 1).1

/-- The A068722 wording of the comment, "`A255437(a(n)) = 2*n+1`", is false:
at `n = 1`, `A068722(1) = 35` but `A255437(35) = 9 ≠ 3`. -/
theorem not_a068722_comment_form :
    ¬ ∀ n : ℕ, a255437 ((1 + 2 * n + 2 * n ^ 2) * (1 + 3 * n + 3 * n ^ 2)) = 2 * n + 1 := by
  intro h
  have h1 := h 1
  rw [(first_occurrence 1).1] at h1
  omega

end Candidates.A068722FirstOccurrenceReplaced
