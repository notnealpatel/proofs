/-
# A226857 — sums and products of two Fibonacci numbers

Colin Barker (OEIS A226857, Nov 09 2014) conjectured
`a(n) = a(n-3) + a(n-6)` for `n > 12`, with offset 1.
Membership is characterized below by `F_k`, `2 F_k`, or `3 F_k` for `k ≥ 0`.

## Proof outline

* `fib_add_two_mul_fib_add_two`: `F_{a+2} F_{b+2} = F_{a+b+2} + F_a F_b`.
* Applied twice: `F_{c+5} F_{d+5} = F_{c+d+8} + F_{c+d+4} + r` with
  `0 < r = F_{c+1} F_{d+1} < F_{c+d+3}`; such a number lies strictly between
  Fibonacci numbers after subtracting any candidate `F_i`, so it is never
  `F_i + F_j` (`not_isFibSum_fib_mul`).  Products with a factor
  `F_k ∈ {0, 1, 2, 3}` give `0, F_l, 2 F_l, 3 F_l`, all of which are sums.
* The increasing enumeration is then explicit (`enum`), and Barker's
  recurrence is the Fibonacci recurrence on each of the three interleaved
  progressions `2 F_{t+4} < F_{t+6} < 3 F_{t+4} < 2 F_{t+5}`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A226857FibonacciSumProduct

open Nat

/-! ## Definitions -/

/-- `x` is a sum of two Fibonacci numbers `F_i + F_j` (`i, j ≥ 0`, `F_0 = 0`,
Mathlib's `Nat.fib`). -/
def IsFibSum (x : ℕ) : Prop := ∃ i j : ℕ, x = fib i + fib j

/-- `x` is a product of two Fibonacci numbers `F_k * F_l` (`k, l ≥ 0`). -/
def IsFibProd (x : ℕ) : Prop := ∃ k l : ℕ, x = fib k * fib l

/-- Membership in A226857: `x` is both a sum and a product of two Fibonacci
numbers. -/
def InA226857 (x : ℕ) : Prop := IsFibSum x ∧ IsFibProd x

/-- The OEIS sequence A226857 with its offset 1: `a n` is the `n`-th smallest
element of `InA226857` (`a 1 = 0`).  The value `a 0` is the junk value
`Nat.nth InA226857 0` and is never used in statements. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth InA226857 (n - 1)

/-! ## Membership examples (the entry's EXAMPLE lines)

The entry's second example reads "8 + 21 = 1 * 34 = 34", but `8 + 21 = 29`;
the intended sum is `13 + 21 = F_7 + F_8`, which is what is checked here. -/

example : InA226857 26 := ⟨⟨5, 8, rfl⟩, ⟨3, 7, rfl⟩⟩
example : InA226857 34 := ⟨⟨7, 8, rfl⟩, ⟨1, 9, rfl⟩⟩
example : InA226857 39 := ⟨⟨5, 9, rfl⟩, ⟨4, 7, rfl⟩⟩

/-! ## Fibonacci identities -/

/-- `F_{a+2} F_{b+2} = F_{a+b+2} + F_a F_b`. -/
theorem fib_add_two_mul_fib_add_two (a b : ℕ) :
    fib (a + 2) * fib (b + 2) = fib (a + b + 2) + fib a * fib b := by
  have h := Nat.fib_add (a + 1) b
  rw [show a + 1 + b + 1 = a + b + 2 by ring] at h
  rw [h, Nat.fib_add_two (n := a), Nat.fib_add_two (n := b)]
  ring

/-- `F_c F_d < F_{c+d+1}` (from `F_{c+d+1} = F_c F_d + F_{c+1} F_{d+1}`). -/
theorem fib_mul_fib_lt_fib (c d : ℕ) : fib c * fib d < fib (c + d + 1) := by
  rw [Nat.fib_add c d]
  have hpos : 0 < fib (c + 1) * fib (d + 1) :=
    Nat.mul_pos (Nat.fib_pos.2 (by omega)) (Nat.fib_pos.2 (by omega))
  omega

/-- A number strictly between `F_m` and `F_{m+1}` is not a Fibonacci number. -/
theorem fib_ne_of_between {m y : ℕ} (h1 : fib m < y) (h2 : y < fib (m + 1)) (k : ℕ) :
    fib k ≠ y := by
  rintro rfl
  rcases le_or_gt k m with hk | hk
  · exact absurd (Nat.fib_mono hk) (not_le.2 h1)
  · exact absurd (Nat.fib_mono (Nat.succ_le_of_lt hk)) (not_le.2 h2)

/-- `F_{c+5} F_{d+5} = F_{c+d+8} + F_{c+d+4} + F_{c+1} F_{d+1}`. -/
theorem fib_mul_decomp (c d : ℕ) :
    fib (c + 5) * fib (d + 5) =
      fib (c + d + 8) + fib (c + d + 4) + fib (c + 1) * fib (d + 1) := by
  rw [fib_add_two_mul_fib_add_two (c + 3) (d + 3), fib_add_two_mul_fib_add_two (c + 1) (d + 1)]
  rw [show c + 3 + (d + 3) + 2 = c + d + 8 by ring, show c + 1 + (d + 1) + 2 = c + d + 4 by ring]
  ring

/-- If `0 < r < F_N`, then `F_{N+5} + F_{N+1} + r` is not `F_i + F_j` with `j ≤ i`:
compare `F_i` with `F_{N+3}, F_{N+4}, F_{N+5}, F_{N+6}`. -/
theorem ne_fib_add_fib_aux (N r i j : ℕ) (hr0 : 0 < r) (hr : r < fib N) (hji : j ≤ i) :
    fib (N + 5) + fib (N + 1) + r ≠ fib i + fib j := by
  intro h
  have f2 : fib (N + 2) = fib N + fib (N + 1) := Nat.fib_add_two
  have f3 : fib (N + 3) = fib (N + 1) + fib (N + 2) := Nat.fib_add_two
  have f4 : fib (N + 4) = fib (N + 2) + fib (N + 3) := Nat.fib_add_two
  have f5 : fib (N + 5) = fib (N + 3) + fib (N + 4) := Nat.fib_add_two
  have f6 : fib (N + 6) = fib (N + 4) + fib (N + 5) := Nat.fib_add_two
  have hji' : fib j ≤ fib i := Nat.fib_mono hji
  obtain hi | rfl | rfl | hi : i ≤ N + 3 ∨ i = N + 4 ∨ i = N + 5 ∨ N + 6 ≤ i := by omega
  · have hmono := Nat.fib_mono hi
    omega
  · refine fib_ne_of_between (m := N + 3) (y := fib j) ?_ ?_ j rfl
    · omega
    · show fib j < fib (N + 4)
      omega
  · refine fib_ne_of_between (m := N + 1) (y := fib j) ?_ ?_ j rfl
    · omega
    · show fib j < fib (N + 2)
      omega
  · have hmono := Nat.fib_mono hi
    omega

/-- `F_{m+4} + F_m = 3 F_{m+2}`. -/
theorem fib_add_four_add_fib (m : ℕ) : fib (m + 4) + fib m = 3 * fib (m + 2) := by
  have f2 : fib (m + 2) = fib m + fib (m + 1) := Nat.fib_add_two
  have f3 : fib (m + 3) = fib (m + 1) + fib (m + 2) := Nat.fib_add_two
  have f4 : fib (m + 4) = fib (m + 2) + fib (m + 3) := Nat.fib_add_two
  omega

/-! ## The characterization -/

/-- **Load-bearing step.** A product `F_a F_b` with `5 ≤ a, b` is not a sum of two
Fibonacci numbers. -/
theorem not_isFibSum_fib_mul (c d : ℕ) : ¬ IsFibSum (fib (c + 5) * fib (d + 5)) := by
  rintro ⟨i, j, h⟩
  rw [fib_mul_decomp, show c + d + 8 = c + d + 3 + 5 by ring,
    show c + d + 4 = c + d + 3 + 1 by ring] at h
  have hr0 : 0 < fib (c + 1) * fib (d + 1) :=
    Nat.mul_pos (Nat.fib_pos.2 (by omega)) (Nat.fib_pos.2 (by omega))
  have hr : fib (c + 1) * fib (d + 1) < fib (c + d + 3) := by
    have hlt := fib_mul_fib_lt_fib (c + 1) (d + 1)
    rwa [show c + 1 + (d + 1) + 1 = c + d + 3 by ring] at hlt
  rcases le_total j i with hji | hij
  · exact ne_fib_add_fib_aux (c + d + 3) _ i j hr0 hr hji h
  · exact ne_fib_add_fib_aux (c + d + 3) _ j i hr0 hr hij (h.trans (add_comm _ _))

/-- A product `F_k F_l` with `k ≤ 4` (so `F_k ∈ {0, 1, 2, 3}`) is `F_m`, `2 F_m` or
`3 F_m` for some `m`. -/
theorem fib_mul_small (k l : ℕ) (hk : k ≤ 4) :
    ∃ m, fib k * fib l = fib m ∨ fib k * fib l = 2 * fib m ∨ fib k * fib l = 3 * fib m := by
  interval_cases k
  · exact ⟨0, Or.inl (by simp)⟩
  · exact ⟨l, Or.inl (by simp)⟩
  · exact ⟨l, Or.inl (by simp)⟩
  · exact ⟨l, Or.inr (Or.inl (by simp [Nat.fib_add_two]))⟩
  · exact ⟨l, Or.inr (Or.inr (by simp [Nat.fib_add_two]))⟩

/-- **Characterization of A226857.** A natural number is both a sum and a product of
two Fibonacci numbers iff it is `F_k`, `2 F_k` or `3 F_k` for some `k ≥ 0`.  This is the
characterization underlying Barker's recurrence. -/
theorem inA226857_iff (x : ℕ) :
    InA226857 x ↔ ∃ k, x = fib k ∨ x = 2 * fib k ∨ x = 3 * fib k := by
  constructor
  · rintro ⟨hs, k, l, rfl⟩
    rcases le_total k l with hkl | hlk
    · by_cases hk : k ≤ 4
      · exact fib_mul_small k l hk
      · obtain ⟨c, rfl⟩ : ∃ c, k = c + 5 := ⟨k - 5, by omega⟩
        obtain ⟨d, rfl⟩ : ∃ d, l = d + 5 := ⟨l - 5, by omega⟩
        exact absurd hs (not_isFibSum_fib_mul c d)
    · by_cases hl : l ≤ 4
      · rw [mul_comm]
        exact fib_mul_small l k hl
      · obtain ⟨c, rfl⟩ : ∃ c, k = c + 5 := ⟨k - 5, by omega⟩
        obtain ⟨d, rfl⟩ : ∃ d, l = d + 5 := ⟨l - 5, by omega⟩
        exact absurd hs (not_isFibSum_fib_mul c d)
  · rintro ⟨k, rfl | rfl | rfl⟩
    · exact ⟨⟨k, 0, by simp⟩, ⟨1, k, by simp⟩⟩
    · exact ⟨⟨k, k, by ring⟩, ⟨3, k, by simp [Nat.fib_add_two]⟩⟩
    · refine ⟨?_, ⟨4, k, by simp [Nat.fib_add_two]⟩⟩
      rcases k with _ | _ | m
      · exact ⟨0, 0, by simp⟩
      · exact ⟨4, 0, by simp [Nat.fib_add_two]⟩
      · exact ⟨m + 4, m, (fib_add_four_add_fib m).symm⟩

/-! ## The increasing enumeration -/

/-- Explicit increasing enumeration of A226857 (0-indexed): `0, 1, 2, 3, 4, 5`,
then for `t ≥ 0` the blocks `2 F_{t+4}, F_{t+6}, 3 F_{t+4}` at positions
`6 + 3t, 7 + 3t, 8 + 3t`. -/
def enum (m : ℕ) : ℕ :=
  if m < 6 then m else
    match (m - 6) % 3 with
    | 0 => 2 * fib ((m - 6) / 3 + 4)
    | 1 => fib ((m - 6) / 3 + 6)
    | _ => 3 * fib ((m - 6) / 3 + 4)

example : (List.range 20).map enum =
    [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 13, 15, 16, 21, 24, 26, 34, 39, 42, 55] := by decide

/-- `enum m = m` for `m < 6`. -/
theorem enum_of_lt {m : ℕ} (hm : m < 6) : enum m = m := by
  simp [enum, hm]

/-- `enum (6 + 3t) = 2 F_{t+4}`. -/
theorem enum_six (t : ℕ) : enum (6 + 3 * t) = 2 * fib (t + 4) := by
  have h1 : (6 + 3 * t - 6) % 3 = 0 := by omega
  have h2 : (6 + 3 * t - 6) / 3 = t := by omega
  simp only [enum, if_neg (by omega : ¬ 6 + 3 * t < 6), h1, h2]

/-- `enum (7 + 3t) = F_{t+6}`. -/
theorem enum_seven (t : ℕ) : enum (7 + 3 * t) = fib (t + 6) := by
  have h1 : (7 + 3 * t - 6) % 3 = 1 := by omega
  have h2 : (7 + 3 * t - 6) / 3 = t := by omega
  simp only [enum, if_neg (by omega : ¬ 7 + 3 * t < 6), h1, h2]

/-- `enum (8 + 3t) = 3 F_{t+4}`. -/
theorem enum_eight (t : ℕ) : enum (8 + 3 * t) = 3 * fib (t + 4) := by
  have h1 : (8 + 3 * t - 6) % 3 = 2 := by omega
  have h2 : (8 + 3 * t - 6) / 3 = t := by omega
  simp only [enum, if_neg (by omega : ¬ 8 + 3 * t < 6), h1, h2]

/-- Every index `m ≥ 6` lies in one of the three residue blocks. -/
theorem exists_block {m : ℕ} (hm : 6 ≤ m) :
    ∃ t, m = 6 + 3 * t ∨ m = 7 + 3 * t ∨ m = 8 + 3 * t :=
  ⟨(m - 6) / 3, by omega⟩

/-- `enum` increases at every step: `2 F_{t+4} < F_{t+6} < 3 F_{t+4} < 2 F_{t+5}`. -/
theorem enum_lt_enum_succ (m : ℕ) : enum m < enum (m + 1) := by
  rcases lt_or_ge m 6 with hm | hm
  · by_cases h5 : m = 5
    · subst h5
      decide
    · rw [enum_of_lt hm, enum_of_lt (by omega)]
      omega
  · obtain ⟨t, rfl | rfl | rfl⟩ := exists_block hm
    · have f6 : fib (t + 6) = fib (t + 4) + fib (t + 5) := Nat.fib_add_two
      have f5 : fib (t + 5) = fib (t + 3) + fib (t + 4) := Nat.fib_add_two
      have hpos : 0 < fib (t + 3) := Nat.fib_pos.2 (by omega)
      rw [enum_six, show 6 + 3 * t + 1 = 7 + 3 * t by ring, enum_seven]
      omega
    · have f6 : fib (t + 6) = fib (t + 4) + fib (t + 5) := Nat.fib_add_two
      have f5 : fib (t + 5) = fib (t + 3) + fib (t + 4) := Nat.fib_add_two
      have hlt : fib (t + 3) < fib (t + 4) := Nat.fib_lt_fib_succ (by omega)
      rw [enum_seven, show 7 + 3 * t + 1 = 8 + 3 * t by ring, enum_eight]
      omega
    · have f5 : fib (t + 5) = fib (t + 3) + fib (t + 4) := Nat.fib_add_two
      have f4 : fib (t + 4) = fib (t + 2) + fib (t + 3) := Nat.fib_add_two
      have hlt : fib (t + 2) < fib (t + 3) := Nat.fib_lt_fib_succ (by omega)
      rw [enum_eight, show 8 + 3 * t + 1 = 6 + 3 * (t + 1) by ring, enum_six,
        show t + 1 + 4 = t + 5 by ring]
      omega

/-- `enum` is strictly increasing. -/
theorem enum_strictMono : StrictMono enum := strictMono_nat_of_lt_succ enum_lt_enum_succ

/-- Every value of `enum` belongs to A226857. -/
theorem inA226857_enum (m : ℕ) : InA226857 (enum m) := by
  rw [inA226857_iff]
  rcases lt_or_ge m 6 with hm | hm
  · rw [enum_of_lt hm]
    interval_cases m
    · exact ⟨0, Or.inl rfl⟩
    · exact ⟨1, Or.inl rfl⟩
    · exact ⟨3, Or.inl rfl⟩
    · exact ⟨4, Or.inl rfl⟩
    · exact ⟨3, Or.inr (Or.inl rfl)⟩
    · exact ⟨5, Or.inl rfl⟩
  · obtain ⟨t, rfl | rfl | rfl⟩ := exists_block hm
    · exact ⟨t + 4, Or.inr (Or.inl (enum_six t))⟩
    · exact ⟨t + 6, Or.inl (enum_seven t)⟩
    · exact ⟨t + 4, Or.inr (Or.inr (enum_eight t))⟩

/-- Every element of A226857 is a value of `enum`. -/
theorem exists_enum_eq {x : ℕ} (hx : InA226857 x) : ∃ m, enum m = x := by
  rw [inA226857_iff] at hx
  obtain ⟨k, rfl | rfl | rfl⟩ := hx
  · rcases lt_or_ge k 6 with hk | hk
    · interval_cases k
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨5, rfl⟩
    · obtain ⟨t, rfl⟩ : ∃ t, k = t + 6 := ⟨k - 6, by omega⟩
      exact ⟨7 + 3 * t, enum_seven t⟩
  · rcases lt_or_ge k 4 with hk | hk
    · interval_cases k
      · exact ⟨0, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨4, rfl⟩
    · obtain ⟨t, rfl⟩ : ∃ t, k = t + 4 := ⟨k - 4, by omega⟩
      exact ⟨6 + 3 * t, enum_six t⟩
  · rcases lt_or_ge k 4 with hk | hk
    · interval_cases k
      · exact ⟨0, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨6, rfl⟩
    · obtain ⟨t, rfl⟩ : ∃ t, k = t + 4 := ⟨k - 4, by omega⟩
      exact ⟨8 + 3 * t, enum_eight t⟩

/-- A226857 is infinite. -/
theorem infinite_inA226857 : (Set.ofPred InA226857).Infinite :=
  Set.infinite_of_injective_forall_mem enum_strictMono.injective inA226857_enum

/-- `enum` is the increasing enumeration of A226857: `Nat.nth InA226857 = enum`. -/
theorem nth_eq_enum (m : ℕ) : Nat.nth InA226857 m = enum m := by
  have hdom : ∀ n : ℕ, n ∈ {n : ℕ | ∀ hf : Set.Finite (Set.ofPred InA226857),
      n < hf.toFinset.card} := fun n hf => absurd hf infinite_inA226857
  refine (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn enum ?_ ?_ ?_ (hdom m)).symm
  · intro x hx
    obtain ⟨n, hn⟩ := exists_enum_eq hx
    exact ⟨n, hdom n, hn⟩
  · exact fun n _ => inA226857_enum n
  · exact enum_strictMono.strictMonoOn _

/-- `a n = enum (n - 1)` (offset 1). -/
theorem a_eq_enum (n : ℕ) : a n = enum (n - 1) := nth_eq_enum (n - 1)

/-- `enum (m + 6) = enum (m + 3) + enum m` for `m ≥ 6`: on each residue block
this is the Fibonacci recurrence. -/
theorem enum_recurrence {m : ℕ} (hm : 6 ≤ m) : enum (m + 6) = enum (m + 3) + enum m := by
  obtain ⟨t, rfl | rfl | rfl⟩ := exists_block hm
  · rw [show 6 + 3 * t + 6 = 6 + 3 * (t + 2) by ring,
      show 6 + 3 * t + 3 = 6 + 3 * (t + 1) by ring, enum_six, enum_six, enum_six,
      show t + 2 + 4 = t + 4 + 2 by ring, show t + 1 + 4 = t + 4 + 1 by ring, Nat.fib_add_two]
    ring
  · rw [show 7 + 3 * t + 6 = 7 + 3 * (t + 2) by ring,
      show 7 + 3 * t + 3 = 7 + 3 * (t + 1) by ring, enum_seven, enum_seven, enum_seven,
      show t + 2 + 6 = t + 6 + 2 by ring, show t + 1 + 6 = t + 6 + 1 by ring, Nat.fib_add_two]
    ring
  · rw [show 8 + 3 * t + 6 = 8 + 3 * (t + 2) by ring,
      show 8 + 3 * t + 3 = 8 + 3 * (t + 1) by ring, enum_eight, enum_eight, enum_eight,
      show t + 2 + 4 = t + 4 + 2 by ring, show t + 1 + 4 = t + 4 + 1 by ring, Nat.fib_add_two]
    ring

/-- **Barker's conjecture (A226857, Colin Barker, Nov 09 2014).**

For `12 < n`, `a n = a (n-3) + a (n-6)`. Here `a n` is the `n`-th term with the entry's offset 1; the guard `12 < n` keeps
both subtractions `n - 3`, `n - 6` off truncation (and `a (n - 6)` off the junk
index `0`).  The recurrence fails at `n = 7, …, 12` (e.g. `a 7 = 6 ≠ a 4 + a 1 = 3`),
so the bound is sharp. -/
theorem barker_recurrence {n : ℕ} (hn : 12 < n) : a n = a (n - 3) + a (n - 6) := by
  rw [a_eq_enum, a_eq_enum, a_eq_enum]
  obtain ⟨m, hm, rfl⟩ : ∃ m, 6 ≤ m ∧ n = m + 7 := ⟨n - 7, by omega, by omega⟩
  rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 3 - 1 = m + 3 by omega,
    show m + 7 - 6 - 1 = m by omega]
  exact enum_recurrence hm

/-! ## Sequence examples (the first 55 listed terms) -/

example : (List.range 55).map (fun n => a (n + 1)) =
    [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 13, 15, 16, 21, 24, 26, 34, 39, 42, 55, 63, 68, 89, 102,
      110, 144, 165, 178, 233, 267, 288, 377, 432, 466, 610, 699, 754, 987, 1131, 1220, 1597,
      1830, 1974, 2584, 2961, 3194, 4181, 4791, 5168, 6765, 7752, 8362, 10946, 12543,
      13530] := by
  simp only [a_eq_enum, Nat.add_sub_cancel]
  decide

/-- `7` is not in A226857 (it lies strictly between `F_5 = 5` and `F_6 = 8` and is
not divisible by `2` or `3`). -/
theorem not_inA226857_seven : ¬ InA226857 7 := by
  rw [inA226857_iff]
  rintro ⟨k, h | h | h⟩
  · exact fib_ne_of_between (m := 5) (by decide) (by decide) k h.symm
  · omega
  · omega

/-- Barker's recurrence fails at `n = 12`, so the bound `12 < n` cannot be lowered. -/
example : a 12 ≠ a 9 + a 6 := by
  rw [a_eq_enum, a_eq_enum, a_eq_enum]
  decide
