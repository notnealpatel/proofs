/-
# A160217 — Shevelev: every admissible start merges with A160217

## OEIS source (retrieved with `oeis show A160217`, 2026-10-21)

```
NAME:     Minimal increasing sequence with a(1)=3 and the property that a(n) and n
          are both in or both not in A003159.
TERMS:    3,6,7,9,11,14,15,18,19,22,23,25,27,30,31,33,35,38,39,41,43,46,47,50,...
AUTHOR:   Vladimir Shevelev, May 04 2009 (edited by R. J. Mathar, May 08 2009)
FORMULA:  a(n)=2n+1, if A007814(n) is even. a(n)=2n+2, if A007814(n) is odd.
COMMENT (the conjecture, Vladimir Shevelev, May 2009):
  Conjecture: Let m>3 belong to A003159. Define the sequence b(n) to be the
  minimal increasing sequence with b(1)=m and the property that b(n) and n are
  both in or both not in A003159. Then a(n)=b(n) for all n larger than some
  m-dependent minimum index.
```

A003159 is the set of `l ≥ 1` whose 2-adic valuation `v_2(l)` is even.

## Status

Triage: open (no proof in the entry; Shevelev's arXiv:0904.2101 treats analogues
for other properties, not the parity of `v_2`).  This file gives a complete
elementary proof: `a(n) ∈ {2n+1, 2n+2}` by the entry formula, `b_m ≥ a` termwise,
the gap `b_m(n) - a(n)` never increases, and a 2-adic choice of index forces it to
drop while positive (`exists_drop_index`).

Computation (bounded python, 2026-10-21): every admissible start `m ≤ 21000`
(triage: `m < 20000`, here also `20001 ≤ m ≤ 21000`) and the starts
`2^k * j` (`k ∈ {16,18,20}`, `j ∈ {1,3,5}`, when admissible) merge with `a`, with the gap
never increasing.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A160217ChiEvenMembership

/-- Membership indicator of A003159: `chi l = true` iff the 2-adic valuation of `l` is even.
(For `l = 0` Mathlib's `padicValNat 2 0 = 0`, so `chi 0 = true`; the sequences below never
evaluate `chi` at `0` in a way that matters.) -/
def chi (l : ℕ) : Bool := decide (Even (padicValNat 2 l))

/-- `chi (2^j * u) = [j even]` for odd `u`. -/
theorem chi_pow_mul (j u : ℕ) (hu : Odd u) : chi (2 ^ j * u) = decide (Even j) := by
  have hu0 : u ≠ 0 := by rintro rfl; exact absurd hu (by decide)
  have hv : padicValNat 2 (2 ^ j * u) = j := by
    rw [padicValNat.mul (by positivity) hu0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd]),
      add_zero]
  simp only [chi, hv]

/-- Odd numbers belong to A003159. -/
theorem chi_of_odd (u : ℕ) (hu : Odd u) : chi u = true := by
  have h := chi_pow_mul 0 u hu
  simpa using h

/-- Doubling a positive number flips A003159 membership. -/
theorem chi_two_mul (k : ℕ) (hk : k ≠ 0) : chi (2 * k) = !chi k := by
  have hv : padicValNat 2 (2 * k) = padicValNat 2 k + 1 := by
    rw [padicValNat.mul (by norm_num) hk, padicValNat.self (by norm_num), add_comm]
  simp only [chi, hv, Nat.even_add_one, decide_not]

/-- Evaluation helper: `chi n = [j even]` whenever `n = 2^j * u` with `u` odd. -/
theorem chi_eval (j u n : ℕ) (hu : Odd u) (h : n = 2 ^ j * u) : chi n = decide (Even j) := by
  rw [h, chi_pow_mul j u hu]

/-! Ground truth for `chi` against A003159 (`1, 3, 4, 5, 7, 9, 11, 12, ...`). -/
example : chi 12 = true := by rw [chi_eval 2 3 12 (by decide) rfl]; decide
example : chi 4 = true := by rw [chi_eval 2 1 4 (by decide) rfl]; decide
example : chi 2 = false := by rw [chi_eval 1 1 2 (by decide) rfl]; decide
example : chi 8 = false := by rw [chi_eval 3 1 8 (by decide) rfl]; decide
example : chi 10 = false := by rw [chi_eval 1 5 10 (by decide) rfl]; decide


/-- Numbers congruent to `2` mod `4` are not in A003159. -/
theorem chi_of_mod_four_eq_two (y : ℕ) (h : y % 4 = 2) : chi y = false := by
  obtain ⟨k, rfl⟩ : ∃ k, y = 2 * (2 * k + 1) := ⟨y / 4, by omega⟩
  rw [chi_two_mul _ (by omega), chi_of_odd _ ⟨k, rfl⟩]; rfl

/-- Non-members of A003159 are even. -/
theorem even_of_chi_eq_false (y : ℕ) (h : chi y = false) : Even y := by
  by_contra hy
  rw [chi_of_odd y (Nat.not_even_iff_odd.mp hy)] at h
  exact Bool.noConfusion h

/-- Even members of A003159 are divisible by `4`. -/
theorem mod_four_of_chi_eq_true_of_even (y : ℕ) (h : chi y = true) (hy : Even y) :
    y % 4 = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, y = 2 * k := ⟨y / 2, by obtain ⟨r, hr⟩ := hy; omega⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rfl
  · rw [chi_two_mul k hk.ne', Bool.not_eq_true'] at h
    obtain ⟨r, hr⟩ := even_of_chi_eq_false k h
    omega

/-- Above every `x` there is an `l` with prescribed A003159 membership `t`. -/
theorem exists_next (x : ℕ) (t : Bool) : ∃ l, x < l ∧ chi l = t := by
  cases t
  · exact ⟨4 * x + 2, by omega, chi_of_mod_four_eq_two _ (by omega)⟩
  · exact ⟨2 * x + 1, by omega, chi_of_odd _ ⟨x, rfl⟩⟩

/-- `next x t = min { l > x : chi l = t }`. -/
def next (x : ℕ) (t : Bool) : ℕ := Nat.find (exists_next x t)

/-- Shevelev's sequence `b_m`: `b m 1 = m` and
`b m (n+1) = min { l > b m n : chi l = chi (n+1) }` for `n ≥ 1`.
The value `b m 0 = m` is a junk value outside the 1-indexed domain. -/
def b (m : ℕ) : ℕ → ℕ
  | 0 => m
  | 1 => m
  | n + 2 => next (b m (n + 1)) (chi (n + 2))

/-- The recursion of `b` at every index `n ≥ 1`. -/
theorem b_succ (m n : ℕ) (hn : 1 ≤ n) : b m (n + 1) = next (b m n) (chi (n + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rfl

/-- `next x t` lies above `x`. -/
theorem lt_next (x : ℕ) (t : Bool) : x < next x t := (Nat.find_spec (exists_next x t)).1

/-- `next x t` has membership `t`. -/
theorem chi_next (x : ℕ) (t : Bool) : chi (next x t) = t := (Nat.find_spec (exists_next x t)).2

/-- Minimality of `next`. -/
theorem next_le (x l : ℕ) (t : Bool) (hl : x < l) (hc : chi l = t) : next x t ≤ l :=
  Nat.find_min' (exists_next x t) ⟨hl, hc⟩

/-- `next` is monotone in its starting point. -/
theorem next_mono (x y : ℕ) (t : Bool) (hxy : x ≤ y) : next x t ≤ next y t :=
  next_le x _ t (lt_of_le_of_lt hxy (lt_next y t)) (chi_next y t)

/-- If `l` is the first number above `x` with membership `t`, then `next x t = l`. -/
theorem next_eq (x l : ℕ) (t : Bool) (hl : x < l) (hc : chi l = t)
    (hmin : ∀ k, x < k → k < l → chi k ≠ t) : next x t = l := by
  refine le_antisymm (next_le x l t hl hc) ?_
  by_contra hlt
  exact hmin _ (lt_next x t) (by omega) (chi_next x t)

/-- If `x + 1` already has membership `t`, then `next x t = x + 1`. -/
theorem next_eq_succ (x : ℕ) (t : Bool) (hc : chi (x + 1) = t) : next x t = x + 1 :=
  next_eq x _ t (by omega) hc (fun k hk hk' => absurd hk' (by omega))

/-- The next member of A003159 lies within distance `2`. -/
theorem next_true_le (y : ℕ) : next y true ≤ y + 2 := by
  rcases Nat.even_or_odd y with hy | hy
  · exact (next_le y (y + 1) _ (by omega) (chi_of_odd _ hy.add_one)).trans (by omega)
  · exact next_le _ _ _ (by omega) (chi_of_odd _ (by obtain ⟨r, hr⟩ := hy; exact ⟨r + 1, by omega⟩))

/-- From a member of A003159 the next non-member lies within distance `3`. -/
theorem next_false_le (y : ℕ) (hy : chi y = true) : next y false ≤ y + 3 := by
  rcases Nat.even_or_odd y with he | ho
  · have h4 := mod_four_of_chi_eq_true_of_even y hy he
    exact (next_le y (y + 2) _ (by omega) (chi_of_mod_four_eq_two (y + 2) (by omega))).trans
      (by omega)
  · obtain ⟨r, hr⟩ := ho
    rcases Nat.even_or_odd r with ⟨s, hs⟩ | ⟨s, hs⟩
    · exact (next_le y (y + 1) _ (by omega) (chi_of_mod_four_eq_two (y + 1) (by omega))).trans
        (by omega)
    · exact next_le _ _ _ (by omega) (chi_of_mod_four_eq_two (y + 3) (by omega))


/-- `chi 1 = true`. -/
theorem chi_one : chi 1 = true := chi_of_odd 1 odd_one

/-- One step of the closed form: from `a(n) = 2n+1` or `2n+2` (according to `chi n`) the next
term with membership `chi (n+1)` is given by the same rule at `n+1`. -/
theorem next_formula (n : ℕ) (hn : 1 ≤ n) :
    next (if chi n then 2 * n + 1 else 2 * n + 2) (chi (n + 1)) =
      if chi (n + 1) then 2 * (n + 1) + 1 else 2 * (n + 1) + 2 := by
  have h2 : chi (2 * n + 2) = !chi (n + 1) := by
    rw [show 2 * n + 2 = 2 * (n + 1) by ring, chi_two_mul _ (by omega)]
  have h3 : chi (2 * n + 3) = true := chi_of_odd _ ⟨n + 1, by ring⟩
  cases hcn : chi n
  · -- `n` is even, so `n + 1` is odd
    have hodd : chi (n + 1) = true := chi_of_odd _ (even_of_chi_eq_false n hcn).add_one
    rw [hodd, if_neg (by simp), if_pos rfl]
    exact next_eq_succ _ _ (by rw [show 2 * n + 2 + 1 = 2 * n + 3 by ring, h3])
  · rw [if_pos rfl]
    cases hcn1 : chi (n + 1)
    · -- `n + 1` is even, so `n + 2` is odd and `2n + 4` is a non-member
      have hn2 : chi (n + 2) = true :=
        chi_of_odd _ (by simpa [add_assoc] using (even_of_chi_eq_false _ hcn1).add_one)
      have h4 : chi (2 * n + 4) = false := by
        rw [show 2 * n + 4 = 2 * (n + 2) by ring, chi_two_mul _ (by omega), hn2]; rfl
      rw [if_neg (by simp)]
      refine next_eq _ _ _ (by omega) (by rw [show 2 * (n + 1) + 2 = 2 * n + 4 by ring]; exact h4) ?_
      intro k hk hk'
      rcases (show k = 2 * n + 2 ∨ k = 2 * n + 3 by omega) with rfl | rfl
      · rw [h2, hcn1]; decide
      · rw [h3]; decide
    · rw [if_pos rfl]
      refine next_eq _ _ _ (by omega) (by rw [show 2 * (n + 1) + 1 = 2 * n + 3 by ring]; exact h3) ?_
      intro k hk hk'
      obtain rfl : k = 2 * n + 2 := by omega
      rw [h2, hcn1]; decide

/-- **Entry formula (A160217).** `a(n) = 2n+1` if `v_2(n)` is even, and `a(n) = 2n+2` otherwise,
where `a = b 3`. -/
theorem b_three_eq (n : ℕ) (hn : 1 ≤ n) :
    b 3 n = if chi n then 2 * n + 1 else 2 * n + 2 := by
  induction n, hn using Nat.le_induction with
  | base => rw [chi_one]; rfl
  | succ n hn ih => rw [b_succ 3 n hn, ih, next_formula n hn]

/-- For an admissible start (`chi m = true`), `b m n` has the same membership as `n`. -/
theorem chi_b (m : ℕ) (hm : chi m = true) (n : ℕ) (hn : 1 ≤ n) : chi (b m n) = chi n := by
  induction n, hn using Nat.le_induction with
  | base => rw [chi_one]; exact hm
  | succ n hn _ => rw [b_succ m n hn, chi_next]

/-- `b m` dominates `b 3` termwise when `3 ≤ m`. -/
theorem b_three_le (m : ℕ) (hm : 3 ≤ m) (n : ℕ) (hn : 1 ≤ n) : b 3 n ≤ b m n := by
  induction n, hn using Nat.le_induction with
  | base => exact hm
  | succ n hn ih => rw [b_succ 3 n hn, b_succ m n hn]; exact next_mono _ _ _ ih


/-- **Step comparison.** From any `y` with the same membership as `n`, the step to the next
number with membership `chi (n+1)` is at most the step `a(n+1) - a(n)` of `a = b 3`. -/
theorem next_add_le (n : ℕ) (hn : 1 ≤ n) (y : ℕ) (hy : chi y = chi n) :
    next y (chi (n + 1)) + b 3 n ≤ y + b 3 (n + 1) := by
  rw [b_three_eq n hn, b_three_eq (n + 1) (by omega)]
  cases hcn : chi n
  · have hodd : chi (n + 1) = true := chi_of_odd _ (even_of_chi_eq_false n hcn).add_one
    have hy' : chi (y + 1) = true :=
      chi_of_odd _ (even_of_chi_eq_false y (hy.trans hcn)).add_one
    rw [hodd, next_eq_succ y true hy']
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega
  · cases hcn1 : chi (n + 1)
    · have hle := next_false_le y (hy.trans hcn)
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega
    · have hle := next_true_le y
      simp only [↓reduceIte]
      omega

/-- **Strict drop.** If `chi n = true` and `y + 1` already has membership `chi (n+1)`, the step
from `y` is strictly shorter than the step `a(n+1) - a(n)`. -/
theorem next_add_lt (n : ℕ) (hn : 1 ≤ n) (hcn : chi n = true) (y : ℕ)
    (hy1 : chi (y + 1) = chi (n + 1)) :
    next y (chi (n + 1)) + b 3 n + 1 ≤ y + b 3 (n + 1) := by
  rw [next_eq_succ y _ hy1, b_three_eq n hn, b_three_eq (n + 1) (by omega), hcn]
  simp only [↓reduceIte]
  split_ifs <;> omega


/-- **2-adic lemma.** For every gap `c ≥ 1` there are arbitrarily large `n ≥ 1` with
`chi n = true` and `chi (2n + 2 + c) = chi (n + 1)`; at such `n` a sequence lying `c` above
`a(n) = 2n+1` gains on `a`. -/
theorem exists_drop_index (c N : ℕ) (hc : 1 ≤ c) :
    ∃ n, N ≤ n ∧ 1 ≤ n ∧ chi n = true ∧ chi (2 * n + 1 + c + 1) = chi (n + 1) := by
  rcases Nat.even_or_odd c with ⟨d, hd⟩ | ⟨d, hd⟩
  · -- `c = 2d` with `d = 2^e * o`, `o` odd; take `n + 1 = 2^(e+1) * (2N+1)`
    obtain ⟨e, o, ho, hdo⟩ := Nat.exists_eq_two_pow_mul_odd (n := d) (by omega)
    have hp : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    set p := 2 ^ e with hpdef
    set q := p * (2 * N + 1) with hqdef
    have hq : 2 * N + 1 ≤ q := Nat.le_mul_of_pos_left _ hp
    have hs : 2 * q - 1 + 1 = 2 ^ (e + 1) * (2 * N + 1) := by
      rw [Nat.sub_add_cancel (by omega), pow_succ, hqdef, hpdef]; ring
    have ht : 2 * (2 * q - 1) + 1 + c + 1 = 2 ^ (e + 1) * (2 * (2 * N + 1) + o) := by
      have h2 : 2 * (2 * q - 1) + 1 + c + 1 = 2 * (2 * q) + c := by omega
      rw [h2, hd, hdo, pow_succ, hqdef, hpdef]; ring
    have hodd : Odd (2 * (2 * N + 1) + o) := by
      obtain ⟨r, hr⟩ := ho; exact ⟨2 * N + 1 + r, by omega⟩
    refine ⟨2 * q - 1, by omega, by omega, chi_of_odd _ ⟨q - 1, by omega⟩, ?_⟩
    rw [hs, ht, chi_pow_mul (e + 1) (2 * N + 1) ⟨N, by ring⟩, chi_pow_mul (e + 1) _ hodd]
  · -- `c` odd; take `n = 8N + 4`
    refine ⟨8 * N + 4, by omega, by omega, ?_, ?_⟩
    · rw [show 8 * N + 4 = 2 ^ 2 * (2 * N + 1) by ring, chi_pow_mul _ _ ⟨N, rfl⟩]; rfl
    · rw [chi_of_odd _ ⟨8 * N + 4 + d + 1, by omega⟩, chi_of_odd _ ⟨4 * N + 2, by ring⟩]


/-! Ground truth: `b 3` reproduces the listed terms `3, 6, 7, 9, 11, 14, 15, 18, 19, 22, 23, 25`
of A160217 (via the closed form, which is itself proved from the `Nat.find` definition). -/
example : b 3 1 = 3 := by rw [b_three_eq 1 le_rfl, chi_eval 0 1 1 (by decide) rfl]; decide
example : b 3 2 = 6 := by rw [b_three_eq 2 (by norm_num), chi_eval 1 1 2 (by decide) rfl]; decide
example : b 3 3 = 7 := by rw [b_three_eq 3 (by norm_num), chi_eval 0 3 3 (by decide) rfl]; decide
example : b 3 4 = 9 := by rw [b_three_eq 4 (by norm_num), chi_eval 2 1 4 (by decide) rfl]; decide
example : b 3 5 = 11 := by rw [b_three_eq 5 (by norm_num), chi_eval 0 5 5 (by decide) rfl]; decide
example : b 3 6 = 14 := by rw [b_three_eq 6 (by norm_num), chi_eval 1 3 6 (by decide) rfl]; decide
example : b 3 7 = 15 := by rw [b_three_eq 7 (by norm_num), chi_eval 0 7 7 (by decide) rfl]; decide
example : b 3 8 = 18 := by rw [b_three_eq 8 (by norm_num), chi_eval 3 1 8 (by decide) rfl]; decide
example : b 3 9 = 19 := by rw [b_three_eq 9 (by norm_num), chi_eval 0 9 9 (by decide) rfl]; decide
example : b 3 10 = 22 := by
  rw [b_three_eq 10 (by norm_num), chi_eval 1 5 10 (by decide) rfl]; decide
example : b 3 11 = 23 := by
  rw [b_three_eq 11 (by norm_num), chi_eval 0 11 11 (by decide) rfl]; decide
example : b 3 12 = 25 := by
  rw [b_three_eq 12 (by norm_num), chi_eval 2 3 12 (by decide) rfl]; decide

/-- The gap `b m n - b 3 n` never increases (for an admissible start `m ≥ 3`). -/
theorem gap_succ_le (m : ℕ) (hm : 3 ≤ m) (hchi : chi m = true) (n : ℕ) (hn : 1 ≤ n) :
    b m (n + 1) - b 3 (n + 1) ≤ b m n - b 3 n := by
  have hstep := next_add_le n hn (b m n) (chi_b m hchi n hn)
  have hle := b_three_le m hm n hn
  have hle' := b_three_le m hm (n + 1) (by omega)
  rw [b_succ m n hn] at hle' ⊢
  omega

/-- The gap is antitone along `n ≥ 1`. -/
theorem gap_le_of_le (m : ℕ) (hm : 3 ≤ m) (hchi : chi m = true) (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    b m (n + k) - b 3 (n + k) ≤ b m n - b 3 n := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (gap_succ_le m hm hchi (n + k) (by omega)).trans ih

/-- The gap strictly drops at an index supplied by `exists_drop_index`. -/
theorem gap_succ_lt (m : ℕ) (hm : 3 ≤ m) (n : ℕ) (hn : 1 ≤ n)
    (hcn : chi n = true)
    (hdrop : chi (2 * n + 1 + (b m n - b 3 n) + 1) = chi (n + 1)) :
    b m (n + 1) - b 3 (n + 1) < b m n - b 3 n := by
  have hle := b_three_le m hm n hn
  have hle' := b_three_le m hm (n + 1) (by omega)
  have ha : b 3 n = 2 * n + 1 := by rw [b_three_eq n hn, hcn]; rfl
  have hy1 : chi (b m n + 1) = chi (n + 1) := by
    rw [← hdrop]; congr 1; omega
  have hstep := next_add_lt n hn hcn (b m n) hy1
  rw [b_succ m n hn] at hle' ⊢
  omega

/-- From any index `n ≥ 1` the gap eventually reaches `0`. -/
theorem exists_gap_eq_zero (m : ℕ) (hm : 3 ≤ m) (hchi : chi m = true) (c : ℕ) :
    ∀ n, 1 ≤ n → b m n - b 3 n = c → ∃ N, 1 ≤ N ∧ b m N - b 3 N = 0 := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro n hn hgap
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · exact ⟨n, hn, hgap⟩
    obtain ⟨n', hnn', hn', hcn', hdrop⟩ := exists_drop_index c n hc
    have hle : b m n' - b 3 n' ≤ c := by
      have h := gap_le_of_le m hm hchi n hn (n' - n)
      rwa [Nat.add_sub_cancel' hnn', hgap] at h
    rcases hle.lt_or_eq with hlt | heq
    · exact ih _ hlt n' hn' rfl
    · rw [← heq] at hdrop
      have hlt := gap_succ_lt m hm n' hn' hcn' hdrop
      rw [heq] at hlt
      exact ih _ hlt (n' + 1) (by omega) rfl

/-- **Shevelev's conjecture (A160217, Vladimir Shevelev, 2009).**

Let `chi l = [v_2(l) is even]` (membership in A003159). For every `m > 3` in A003159 let
`b_m(1) = m` and `b_m(n+1) = min { l > b_m(n) : chi l = chi (n+1) }`. Then there is `N(m)`
with `b_m(n) = b_3(n) = A160217(n)` for all `n ≥ N(m)`.

Here `b m n` is `b_m(n)` for `n ≥ 1` and `b 3` is A160217 by the entry's definition. -/
theorem shevelev_A160217 (m : ℕ) (hm : 3 < m) (hchi : chi m = true) :
    ∃ N, ∀ n, N ≤ n → b m n = b 3 n := by
  obtain ⟨N, hN, hgap⟩ := exists_gap_eq_zero m hm.le hchi _ 1 le_rfl rfl
  refine ⟨N, fun n hn => ?_⟩
  have h := gap_le_of_le m hm.le hchi N hN (n - N)
  rw [Nat.add_sub_cancel' hn, hgap] at h
  have hle := b_three_le m hm.le n (by omega)
  omega

/-- Non-vacuity: `m = 4` is an admissible start (`3 < 4`, `v_2(4) = 2` even), so the theorem
applies; `b 4` starts `4, 6, 7, 9, ...` and merges with `b 3` from `n = 2` on. -/
example : 3 < 4 ∧ chi 4 = true := ⟨by norm_num, by rw [chi_eval 2 1 4 (by decide) rfl]; decide⟩

/-- Direct check from the `Nat.find` definition: `b 4 2 = next 4 (chi 2) = 6`. -/
example : b 4 2 = 6 := by
  show next 4 (chi 2) = 6
  have h2 : chi 2 = false := by rw [chi_eval 1 1 2 (by decide) rfl]; decide
  rw [h2]
  refine next_eq 4 6 false (by norm_num) (chi_of_mod_four_eq_two 6 (by norm_num)) ?_
  intro k hk hk'
  obtain rfl : k = 5 := by omega
  rw [chi_of_odd 5 (by decide)]; decide

end Candidates.A160217ChiEvenMembership
