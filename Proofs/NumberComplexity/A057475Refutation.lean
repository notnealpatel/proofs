/-
# A057475 — Perry: every positive integer is a value of `a` (refuted)

Jon Perry's conjecture in OEIS A057475 asserts that every positive integer
occurs as `#{1 ≤ k ≤ n : gcd(n,k) = gcd(n+1,k) = 1}`. The value `49` never
occurs.

1. `1` and every prime `p ≤ n` not dividing `n (n + 1)` are counted by `a n`,
   so `π(n) + 1 ≤ a(n) + ω(n) + ω(n + 1)`.
2. `2 ^ ω(m) ≤ m`, so `ω(m) ≤ log₂ m`.
3. Chebyshev (Mathlib `Chebyshev.two_pow_le_mul_lcmUpto`):
   `2 ^ n ≤ (n + 1) * lcmUpto n ≤ (n + 1) * n ^ π(n)`.
4. If `a n = 49` then, with `L = log₂ (n + 1)`, `π(n) ≤ 48 + 2L`, whence
   `n < (L + 1)(2L + 49)` and `2 ^ L ≤ n + 1`, forcing `L ≤ 9` and so `π(n) ≤ 66`.
   Since `π(331) = 67`, this forces `n < 331`.
5. A kernel computation checks `a n ≠ 49` for every `n < 331`.
-/
import Mathlib

set_option autoImplicit false
-- Synchronous elaboration: under the repository's address-space cap, several asynchronous
-- `decide +kernel` checks in one file fail to spawn their worker threads.
set_option Elab.async false

namespace Candidates.A057475Refutation

/-! ## Definitions -/

/-- OEIS A057475: `a n` is the number of `k` with `1 ≤ k ≤ n` such that
`gcd(n, k) = gcd(n + 1, k) = 1`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k => Nat.gcd n k = 1 ∧ Nat.gcd (n + 1) k = 1)).card

/-- terms `a 1` through `a 20` of A057475 as listed in the entry. -/
example : (List.range 20).map (fun i => a (i + 1)) =
    [1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 3, 4, 5, 3, 4, 8, 5, 6, 7, 5] := by
  decide +kernel

/-- terms `a 21` through `a 40` of A057475 as listed in the entry. -/
example : (List.range 20).map (fun i => a (i + 21)) =
    [5, 10, 7, 7, 9, 8, 8, 12, 7, 8, 15, 10, 9, 11, 8, 12, 17, 11, 9, 16] := by
  decide +kernel

/-- terms `a 41` through `a 60` of A057475 as listed in the entry. -/
example : (List.range 20).map (fun i => a (i + 41)) =
    [11, 12, 19, 11, 11, 22, 15, 14, 17, 13, 15, 24, 17, 14, 17, 15, 17, 28, 15, 16] := by
  decide +kernel

/-- terms `a 61` through `a 80` of A057475 as listed in the entry. -/
example : (List.range 20).map (fun i => a (i + 61)) =
    [29, 17, 18, 24, 15, 20, 31, 21, 15, 24, 23, 24, 35, 19, 19, 28, 18, 24, 31, 22] := by
  decide +kernel

/-! ## The conjecture -/

/-- **Perry's conjecture (A057475, Jon Perry).**
"It is conjectured that every positive integer appears."
Formally: every positive integer `m` equals `a n` for some `n ≥ 1`. -/
def Conjecture : Prop :=
  ∀ m : ℕ, 0 < m → ∃ n : ℕ, 0 < n ∧ a n = m

/-! ## Analytic part: `a n = 49` forces `n < 331` -/

/-- `ω(m) ≤ log₂ m`: a number has at most `log₂ m` distinct prime factors. -/
theorem card_primeFactors_le_log (m : ℕ) : m.primeFactors.card ≤ Nat.log 2 m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hpow : 2 ^ m.primeFactors.card ≤ m :=
      calc 2 ^ m.primeFactors.card ≤ ∏ p ∈ m.primeFactors, p :=
            Finset.pow_card_le_prod _ _ _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
        _ ≤ m := Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)
    exact Nat.le_log_of_pow_le (by norm_num) hpow

/-- `1` and every prime `p ≤ n` dividing neither `n` nor `n + 1` are counted by `a n`;
hence `π(n) + 1 ≤ a n + ω(n) + ω(n + 1)` for `n ≥ 1`. -/
theorem card_primesLE_add_one_le (n : ℕ) (hn : 0 < n) :
    (Nat.primesLE n).card + 1 ≤ a n + n.primeFactors.card + (n + 1).primeFactors.card := by
  set B : Finset ℕ := n.primeFactors ∪ (n + 1).primeFactors with hBdef
  have hsub : insert 1 (Nat.primesLE n \ B) ⊆
      (Finset.Icc 1 n).filter (fun k => Nat.gcd n k = 1 ∧ Nat.gcd (n + 1) k = 1) := by
    intro k hk
    rw [Finset.mem_insert] at hk
    rw [Finset.mem_filter, Finset.mem_Icc]
    rcases hk with rfl | hk
    · exact ⟨⟨le_rfl, hn⟩, Nat.gcd_one_right n, Nat.gcd_one_right (n + 1)⟩
    · rw [Finset.mem_sdiff, Nat.mem_primesLE] at hk
      obtain ⟨⟨hkn, hkp⟩, hkB⟩ := hk
      have hndvd : ¬ k ∣ n := fun hd =>
        hkB (Finset.mem_union_left _ (Nat.mem_primeFactors.2 ⟨hkp, hd, hn.ne'⟩))
      have hndvd1 : ¬ k ∣ n + 1 := fun hd =>
        hkB (Finset.mem_union_right _ (Nat.mem_primeFactors.2 ⟨hkp, hd, Nat.succ_ne_zero n⟩))
      exact ⟨⟨hkp.one_lt.le, hkn⟩,
        Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hkp).2 hndvd),
        Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hkp).2 hndvd1)⟩
  have h1 : (1 : ℕ) ∉ Nat.primesLE n \ B := fun h =>
    Nat.not_prime_one (Nat.prime_of_mem_primesLE (Finset.mem_sdiff.1 h).1)
  have hT : (insert 1 (Nat.primesLE n \ B)).card = (Nat.primesLE n \ B).card + 1 :=
    Finset.card_insert_of_notMem h1
  have hle := Finset.card_le_card hsub
  have hsd : (Nat.primesLE n).card ≤ (Nat.primesLE n \ B).card + B.card :=
    Finset.card_le_card_sdiff_add_card
  have hB : B.card ≤ n.primeFactors.card + (n + 1).primeFactors.card :=
    Finset.card_union_le _ _
  unfold a
  omega

/-- Chebyshev's elementary bound in exponential form: `2 ^ n ≤ (n + 1) * n ^ π(n)`. -/
theorem two_pow_le_mul_pow_card_primesLE (n : ℕ) :
    2 ^ n ≤ (n + 1) * n ^ (Nat.primesLE n).card := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · calc 2 ^ n ≤ (n + 1) * Nat.lcmUpto n := Chebyshev.two_pow_le_mul_lcmUpto n
      _ ≤ (n + 1) * n ^ (Nat.primesLE n).card := by
        apply Nat.mul_le_mul_left
        rw [Nat.lcmUpto_eq_prod_pow_log]
        exact Finset.prod_le_pow_card _ _ _ fun p _ => Nat.pow_log_le_self p hn.ne'

/-- For `L ≥ 10`, `(L + 1)(2L + 49) < 2 ^ L`. -/
theorem mul_lt_two_pow (L : ℕ) (hL : 10 ≤ L) : (L + 1) * (2 * L + 49) < 2 ^ L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    nlinarith

set_option maxRecDepth 4000 in
/-- `π(n) ≥ 67` for `n ≥ 331`: the 67 primes up to `331` are all at most `n`. -/
theorem sixty_seven_le_card_primesLE (n : ℕ) (hn : 331 ≤ n) : 67 ≤ (Nat.primesLE n).card := by
  let S : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61,
    67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157,
    163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257,
    263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331}
  have hS : S.card = 67 := by decide
  have hsub : S ⊆ Nat.primesLE n := by
    intro p hp
    rw [Nat.mem_primesLE]
    fin_cases hp <;> exact ⟨by omega, by norm_num⟩
  rw [← hS]
  exact Finset.card_le_card hsub

/-! ## Computational part: `a n ≠ 49` for `n < 331` -/

/-- `cntB m n d lo` counts the `k` in `[lo, lo + 2 ^ d)` with `k ≤ n` and `gcd(m, k) = 1`,
by binary splitting (keeps kernel recursion depth logarithmic). -/
def cntB (m n : ℕ) : ℕ → ℕ → ℕ
  | 0, lo => if lo ≤ n ∧ Nat.gcd m lo = 1 then 1 else 0
  | d + 1, lo => if n < lo then 0 else cntB m n d lo + cntB m n d (lo + 2 ^ d)

/-- Examples for `cntB`: among `1, …, 6`, those coprime to `42` are `1` and `5`. -/
example : cntB 42 6 3 0 = 2 := by decide

/-- `cntB` computes the filtered cardinality it is meant to. -/
theorem cntB_eq_card (m n d lo : ℕ) :
    cntB m n d lo =
      ((Finset.Ico lo (lo + 2 ^ d)).filter (fun k => k ≤ n ∧ Nat.gcd m k = 1)).card := by
  induction d generalizing lo with
  | zero =>
    rw [pow_zero, Nat.Ico_succ_singleton, Finset.filter_singleton]
    unfold cntB
    split_ifs <;> simp
  | succ d ih =>
    unfold cntB
    split_ifs with hlo
    · symm
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k hk hkn
      rw [Finset.mem_Ico] at hk
      omega
    · have hsplit : Finset.Ico lo (lo + 2 ^ (d + 1)) =
          Finset.Ico lo (lo + 2 ^ d) ∪ Finset.Ico (lo + 2 ^ d) (lo + 2 ^ d + 2 ^ d) := by
        rw [Finset.Ico_union_Ico_eq_Ico (Nat.le_add_right _ _) (Nat.le_add_right _ _), pow_succ]
        congr 1
        omega
      rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint, ih, ih]
      exact Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)

/-- For `n < 512`, `a n` is the binary-split count of `k < 512` with `k ≤ n` and
`gcd(n (n + 1), k) = 1`. -/
theorem a_eq_cntB (n : ℕ) (hn : n < 512) : a n = cntB (n * (n + 1)) n 9 0 := by
  rw [cntB_eq_card]
  unfold a
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
  have hmul : Nat.gcd (n * (n + 1)) k = 1 ↔ Nat.gcd n k = 1 ∧ Nat.gcd (n + 1) k = 1 :=
    Nat.coprime_mul_iff_left
  rw [hmul]
  constructor
  · rintro ⟨⟨_, hkn⟩, hcop⟩
    exact ⟨⟨Nat.zero_le k, by norm_num; omega⟩, hkn, hcop⟩
  · rintro ⟨⟨_, _⟩, hkn, hn1, hn2⟩
    refine ⟨⟨?_, hkn⟩, hn1, hn2⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [Nat.gcd_zero_right] at hn1 hn2
      omega
    · exact hk

/-- The finite check on a block of 34 consecutive values of `n` starting at `base`. -/
def ChunkOK (base : ℕ) : Prop :=
  ∀ i < 34, cntB ((base + i) * (base + i + 1)) (base + i) 9 0 ≠ 49

/-- Block `[0, 34)`. -/
theorem chunkOK_0 : ChunkOK 0 := by unfold ChunkOK; decide +kernel
/-- Block `[34, 68)`. -/
theorem chunkOK_1 : ChunkOK 34 := by unfold ChunkOK; decide +kernel
/-- Block `[68, 102)`. -/
theorem chunkOK_2 : ChunkOK 68 := by unfold ChunkOK; decide +kernel
/-- Block `[102, 136)`. -/
theorem chunkOK_3 : ChunkOK 102 := by unfold ChunkOK; decide +kernel
/-- Block `[136, 170)`. -/
theorem chunkOK_4 : ChunkOK 136 := by unfold ChunkOK; decide +kernel
/-- Block `[170, 204)`. -/
theorem chunkOK_5 : ChunkOK 170 := by unfold ChunkOK; decide +kernel
/-- Block `[204, 238)`. -/
theorem chunkOK_6 : ChunkOK 204 := by unfold ChunkOK; decide +kernel
/-- Block `[238, 272)`. -/
theorem chunkOK_7 : ChunkOK 238 := by unfold ChunkOK; decide +kernel
/-- Block `[272, 306)`. -/
theorem chunkOK_8 : ChunkOK 272 := by unfold ChunkOK; decide +kernel
/-- Block `[306, 340)`. -/
theorem chunkOK_9 : ChunkOK 306 := by unfold ChunkOK; decide +kernel

/-- `a n ≠ 49` for every `n < 331` (kernel computation). -/
theorem a_ne_49_of_lt_331 (n : ℕ) (hn : n < 331) : a n ≠ 49 := by
  rw [a_eq_cntB n (by omega)]
  have hall : ∀ j < 10, ChunkOK (34 * j) := by
    intro j hj
    interval_cases j
    exacts [chunkOK_0, chunkOK_1, chunkOK_2, chunkOK_3, chunkOK_4, chunkOK_5, chunkOK_6,
      chunkOK_7, chunkOK_8, chunkOK_9]
  have hblock := hall (n / 34) (by omega) (n % 34) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at hblock

/-! ## The refutation -/

/-- `49` is never a value of A057475: `a n ≠ 49` for every `n`. -/
theorem a_ne_49 (n : ℕ) : a n ≠ 49 := by
  intro h49
  rcases Nat.lt_or_ge n 331 with hlt | hge
  · exact a_ne_49_of_lt_331 n hlt h49
  · set L := Nat.log 2 (n + 1) with hL
    have hωn : n.primeFactors.card ≤ L :=
      (card_primeFactors_le_log n).trans (Nat.log_mono_right (Nat.le_succ n))
    have hωn1 : (n + 1).primeFactors.card ≤ L := card_primeFactors_le_log (n + 1)
    have hcount := card_primesLE_add_one_le n (by omega)
    have hπ : (Nat.primesLE n).card ≤ 2 * L + 48 := by omega
    have hpow : 2 ^ n < 2 ^ ((L + 1) * (2 * L + 49)) :=
      calc 2 ^ n ≤ (n + 1) * n ^ (Nat.primesLE n).card := two_pow_le_mul_pow_card_primesLE n
        _ ≤ (n + 1) * (n + 1) ^ (2 * L + 48) := by
          apply Nat.mul_le_mul_left
          calc n ^ (Nat.primesLE n).card ≤ (n + 1) ^ (Nat.primesLE n).card :=
                Nat.pow_le_pow_left (Nat.le_succ n) _
            _ ≤ (n + 1) ^ (2 * L + 48) := Nat.pow_le_pow_right (Nat.succ_pos n) hπ
        _ = (n + 1) ^ (2 * L + 49) := by ring
        _ < (2 ^ (L + 1)) ^ (2 * L + 49) :=
          Nat.pow_lt_pow_left (Nat.lt_pow_succ_log_self (by norm_num) (n + 1)) (by omega)
        _ = 2 ^ ((L + 1) * (2 * L + 49)) := by rw [← pow_mul]
    have hnlt : n < (L + 1) * (2 * L + 49) :=
      (Nat.pow_lt_pow_iff_right (by norm_num)).1 hpow
    have hLle : 2 ^ L ≤ n + 1 := Nat.pow_log_le_self 2 (Nat.succ_ne_zero n)
    have hL9 : L ≤ 9 := by
      by_contra hcon
      have hbig := mul_lt_two_pow L (by omega)
      omega
    have h67 := sixty_seven_le_card_primesLE n hge
    omega

/-- **Refutation of Perry's conjecture (A057475).** The positive integer `49` is not
a value of `a(n) = #{1 ≤ k ≤ n : gcd(n, k) = gcd(n + 1, k) = 1}` for any `n ≥ 1`
(indeed for any `n`). -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  obtain ⟨n, -, hn⟩ := hconj 49 (by norm_num)
  exact a_ne_49 n hn

end Candidates.A057475Refutation
