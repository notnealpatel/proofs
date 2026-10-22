/-
# A262995 — refutation of Sun's conjecture `a(n) > 0`

## OEIS source (retrieved with `oeis show A262995` and checked against the
## live entry https://oeis.org/A262995, 2026-10-21)

```
NAME:     Number of ordered pairs (k,m) with k > 0 and m > 0 such that
          n = pi(k*(k+1)/2) + pi(1+m*(m+1)/2), where pi(x) denotes the number
          of primes not exceeding x.
OFFSET:   1
TERMS:    1,1,1,3,3,3,3,5,3,6,3,6,4,6,4,7,4,6,6,6,4,8,5,6,6,7,5,8,4,9,...
COMMENT:  Conjecture: a(n) > 0 for all n > 0.
COMMENT:  This has been verified for n up to 10^5. See also A262999 for a
          similar conjecture.
AUTHOR:   Zhi-Wei Sun, Oct 07 2015
```

The conjecture comment carries no separate signature; it is by the entry's
author, Zhi-Wei Sun (Oct 07 2015).  The live entry (revision #12, Oct 07 2015)
has no later comment retracting or qualifying it (checked 2026-10-21).  The
Mathematica program evaluates `PrimePi[k(k+1)/2]` and `PrimePi[k(k+1)/2+1]`;
`k(k+1)/2` is an integer, so Lean's floor division `k * (k + 1) / 2` is exact.

## Status of this module

This module **refutes** the conjecture: `a(241540) = 0`.  Since `π` is
monotone and `π(T_2596) = 241602 > 241540` (where `T_k = k(k+1)/2`), only
`k, m ≤ 2595` can contribute, and no pair `(k, m)` with `1 ≤ k, m ≤ 2595`
has `π(T_k) + π(1 + T_m) = 241540`.  A bounded computation (Python sieve,
2026-10-21) also finds `a(350366) = 0`; it is not formalized here.  The
counterexample lies above the range `n ≤ 10^5` the entry reports as checked.

## Proof method

All needed values of `π` lie below `1837^2 = 3374569`.  Primes in a window
`[lo, lo + S)` are computed as a bitmask by a sieve of Eratosthenes on `ℕ`
(`sieveW`), using the kernel's GMP-accelerated bitwise operations: the
multiples of `d` form one doubled bitmask (`multMask`).  The sieving primes
`ds` (the primes below `1837`) are themselves read off a small sieve.  Prime
counts between consecutive points are bit counts of window slices, computed by
SWAR additions (`pc`, `segCount`).  The checker `chk` certifies two tables,
`tabA[k] = π(T_k)` and `tabB[m] = π(1 + T_m)` for `k, m ≤ 2596`, in fourteen
kernel-checked chunks; a bitmask membership test (`pairCheck`) rules out every
pair.  All computations use `decide +kernel`; no `native_decide`, no axioms.

`Elab.async false` keeps the kernel checks sequential; under a virtual-memory
cap the default asynchronous elaboration fails to create its worker threads.
-/
import Mathlib

set_option autoImplicit false
set_option Elab.async false

namespace Candidates.A262995Refutation

/-! ## Definitions -/

/-- The set of ordered pairs `(k, m)` with `k > 0`, `m > 0` and
`n = π(k(k+1)/2) + π(1 + m(m+1)/2)`. -/
def pairSet (n : ℕ) : Set (ℕ × ℕ) :=
  {p | 0 < p.1 ∧ 0 < p.2 ∧
    n = Nat.primeCounting (p.1 * (p.1 + 1) / 2) + Nat.primeCounting (1 + p.2 * (p.2 + 1) / 2)}

/-- OEIS A262995: the number of ordered pairs `(k, m)` with `k > 0`, `m > 0` and
`n = π(k(k+1)/2) + π(1 + m(m+1)/2)`.  Mathematically the set is finite for
every `n` because `π` is unbounded, but that global finiteness fact is not
proved in this module.  The refutation below instead proves the relevant pair
set empty, so its use of `Set.ncard` does not depend on that residual bridge. -/
noncomputable def a (n : ℕ) : ℕ := (pairSet n).ncard

/-- **Sun's conjecture (A262995, Zhi-Wei Sun, Oct 07 2015).**
Verbatim: "Conjecture: a(n) > 0 for all n > 0." -/
def Conjecture : Prop := ∀ n : ℕ, 0 < n → 0 < a n

/-! ## Bitmask of the multiples of `d` -/

/-- `m ||| (m <<< s)`: the bitmask `m` together with its copy shifted by `s`. -/
def dbl (s m : ℕ) : ℕ := m ||| (m <<< s)

/-- The bitmask of the multiples of `d` below `d * 2 ^ t`, built by doubling. -/
def multMask (d : ℕ) : ℕ → ℕ
  | 0 => 1
  | t + 1 => dbl (d * 2 ^ t) (multMask d t)

/-- Bit `i` of `multMask d t` is set iff `d ∣ i` and `i < d * 2 ^ t`. -/
theorem testBit_multMask {d : ℕ} (hd : 0 < d) (t i : ℕ) :
    (multMask d t).testBit i = true ↔ d ∣ i ∧ i < d * 2 ^ t := by
  induction t generalizing i with
  | zero =>
    rw [multMask, Nat.testBit_one_eq_true_iff_self_eq_zero, pow_zero, mul_one]
    constructor
    · rintro rfl
      exact ⟨dvd_zero d, hd⟩
    · rintro ⟨hdvd, hlt⟩
      exact Nat.eq_zero_of_dvd_of_lt hdvd hlt
  | succ t ih =>
    rw [multMask, dbl, Nat.testBit_lor, Nat.testBit_shiftLeft, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_iff, ih, ih]
    have hs : d ∣ d * 2 ^ t := dvd_mul_right d _
    have hpow : d * 2 ^ (t + 1) = d * 2 ^ t + d * 2 ^ t := by ring
    rw [hpow]
    constructor
    · rintro (⟨hdvd, hlt⟩ | ⟨hle, hdvd, hlt⟩)
      · exact ⟨hdvd, by omega⟩
      · refine ⟨?_, by omega⟩
        have h := Nat.dvd_add hdvd hs
        rwa [Nat.sub_add_cancel hle] at h
    · rintro ⟨hdvd, hlt⟩
      by_cases hle : d * 2 ^ t ≤ i
      · right
        exact ⟨hle, Nat.dvd_sub hdvd hs, by omega⟩
      · left
        exact ⟨hdvd, by omega⟩

/-- `clear B M`: the bits of `B` not in `M`. -/
def clear (B M : ℕ) : ℕ := B ^^^ (B &&& M)

/-- Bit `i` of `clear B M` is bit `i` of `B` and not bit `i` of `M`. -/
theorem testBit_clear (B M i : ℕ) :
    (clear B M).testBit i = (B.testBit i && !M.testBit i) := by
  rw [clear, Nat.testBit_xor, Nat.testBit_land]
  cases B.testBit i <;> cases M.testBit i <;> rfl

/-! ## A windowed sieve of Eratosthenes on bitmasks -/

/-- The number of doublings after which `d * 2 ^ t` exceeds `S`. -/
def tB (S d : ℕ) : ℕ := Nat.log2 (S / d) + 1

/-- `S < d * 2 ^ tB S d` for `0 < d`. -/
theorem lt_mul_two_pow_tB {S d : ℕ} (hd : 0 < d) : S < d * 2 ^ tB S d := by
  have h1 : S / d < 2 ^ tB S d := Nat.lt_log2_self
  have h2 : S < d * (S / d + 1) := Nat.lt_mul_div_succ S hd
  calc S < d * (S / d + 1) := h2
    _ ≤ d * 2 ^ tB S d := Nat.mul_le_mul_left d h1

/-- The least multiple of `d` that is at least `max lo (2 * d)`. -/
def firstMult (lo d : ℕ) : ℕ := (max lo (2 * d) + d - 1) / d * d

/-- `firstMult lo d` is a multiple of `d`. -/
theorem dvd_firstMult (lo d : ℕ) : d ∣ firstMult lo d := Dvd.intro_left _ rfl

/-- `firstMult lo d` is at least `max lo (2 * d)`. -/
theorem le_firstMult {lo d : ℕ} (hd : 0 < d) : max lo (2 * d) ≤ firstMult lo d := by
  set m := max lo (2 * d)
  have hdm := Nat.div_add_mod (m + d - 1) d
  have hmod := Nat.mod_lt (m + d - 1) hd
  rw [firstMult, Nat.mul_comm]
  set q := (m + d - 1) / d
  set r := (m + d - 1) % d
  omega

/-- `firstMult lo d` is at most every multiple of `d` that is at least
`max lo (2 * d)`. -/
theorem firstMult_le {lo d x : ℕ} (hd : 0 < d) (hdx : d ∣ x) (hx : max lo (2 * d) ≤ x) :
    firstMult lo d ≤ x := by
  obtain ⟨y, rfl⟩ := hdx
  rw [firstMult, Nat.mul_comm d y]
  apply Nat.mul_le_mul_right
  · rw [Nat.div_le_iff_le_mul_add_pred hd]
    set m := max lo (2 * d)
    set z := d * y
    omega

/-- One sieve step on the window `[lo, lo + S)`: clear the multiples `x` of `d`
with `2 * d ≤ x`. -/
def stepW (lo S d B : ℕ) : ℕ := clear B (multMask d (tB S d) <<< (firstMult lo d - lo))

/-- Bit `i < S` survives `stepW lo S d` iff it was set and `lo + i` is not a
multiple `x` of `d` with `2 * d ≤ x`. -/
theorem testBit_stepW {lo S d B i : ℕ} (hd : 0 < d) (hi : i < S) :
    (stepW lo S d B).testBit i = true ↔
      B.testBit i = true ∧ ¬ (2 * d ≤ lo + i ∧ d ∣ lo + i) := by
  rw [stepW, testBit_clear, Bool.and_eq_true, Bool.not_eq_true', Nat.testBit_shiftLeft,
    Bool.and_eq_false_iff, decide_eq_false_iff_not, Bool.eq_false_iff, ne_eq,
    testBit_multMask hd]
  have hc := le_firstMult (lo := lo) hd
  have hcd := dvd_firstMult lo d
  have hS := lt_mul_two_pow_tB (S := S) hd
  rw [max_le_iff] at hc
  apply and_congr_right
  intro _
  constructor
  · rintro (hlt | hnot) ⟨h2d, hdvd⟩
    · have hle := firstMult_le (lo := lo) hd hdvd (max_le_iff.mpr ⟨by omega, h2d⟩)
      omega
    · apply hnot
      have hle := firstMult_le (lo := lo) hd hdvd (max_le_iff.mpr ⟨by omega, h2d⟩)
      refine ⟨?_, by omega⟩
      have h := Nat.dvd_sub hdvd hcd
      rwa [show lo + i - firstMult lo d = i - (firstMult lo d - lo) by omega] at h
  · intro hnot
    by_cases hlt : i < firstMult lo d - lo
    · left; omega
    · right
      rintro ⟨hdvd, _⟩
      apply hnot
      refine ⟨by omega, ?_⟩
      have h := Nat.dvd_add hdvd hcd
      rwa [show i - (firstMult lo d - lo) + firstMult lo d = lo + i by omega] at h

/-- The window `[lo, lo + S)` with the integers below `2` removed. -/
def initW (lo S : ℕ) : ℕ := (2 ^ S - 1) ^^^ (2 ^ (2 - lo) - 1)

/-- Bit `i < S` of `initW lo S` is set iff `2 ≤ lo + i`. -/
theorem testBit_initW {lo S i : ℕ} (hi : i < S) :
    (initW lo S).testBit i = true ↔ 2 ≤ lo + i := by
  rw [initW, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one,
    decide_eq_true hi, Bool.true_xor, Bool.not_eq_true', decide_eq_false_iff_not]
  omega

/-- The sieve of the window `[lo, lo + S)` by the list `ds`: bit `i` stands for
`lo + i`. -/
def sieveW (lo S : ℕ) (ds : List ℕ) : ℕ := ds.foldl (fun B d => stepW lo S d B) (initW lo S)

/-- Folding sieve steps over a list. -/
theorem testBit_foldl_stepW {lo S i : ℕ} (hi : i < S) (ds : List ℕ) (hds : ∀ d ∈ ds, 0 < d) :
    ∀ B : ℕ, (ds.foldl (fun B d => stepW lo S d B) B).testBit i = true ↔
      B.testBit i = true ∧ ∀ d ∈ ds, ¬ (2 * d ≤ lo + i ∧ d ∣ lo + i) := by
  induction ds with
  | nil => intro B; simp
  | cons d ds ih =>
    intro B
    rw [List.foldl_cons, ih (fun e he => hds e (List.mem_cons_of_mem d he)),
      testBit_stepW (hds d List.mem_cons_self) hi, List.forall_mem_cons, and_assoc]

/-- Bit `i < S` of `sieveW lo S ds` is set iff `2 ≤ lo + i` and no `d ∈ ds`
has `2 * d ≤ lo + i` and `d ∣ lo + i`. -/
theorem testBit_sieveW {lo S i : ℕ} (hi : i < S) (ds : List ℕ) (hds : ∀ d ∈ ds, 0 < d) :
    (sieveW lo S ds).testBit i = true ↔
      2 ≤ lo + i ∧ ∀ d ∈ ds, ¬ (2 * d ≤ lo + i ∧ d ∣ lo + i) := by
  rw [sieveW, testBit_foldl_stepW hi ds hds, testBit_initW hi]

/-- If `ds` contains every prime `p` with `p * p < N` and consists of integers
`≥ 2`, then below `N` the sieve condition characterizes the primes. -/
theorem sieve_cond_iff_prime {N x : ℕ} (hx : x < N) (ds : List ℕ)
    (hall : ∀ p : ℕ, p.Prime → p * p < N → p ∈ ds) (hds : ∀ d ∈ ds, 2 ≤ d) :
    (2 ≤ x ∧ ∀ d ∈ ds, ¬ (2 * d ≤ x ∧ d ∣ x)) ↔ x.Prime := by
  constructor
  · rintro ⟨h2, hnone⟩
    by_contra hnp
    have hx1 : x ≠ 1 := by omega
    have hq := Nat.minFac_prime hx1
    have hsq : x.minFac ^ 2 ≤ x := Nat.minFac_sq_le_self (by omega) hnp
    have hmem : x.minFac ∈ ds := hall _ hq (by nlinarith)
    apply hnone _ hmem
    refine ⟨?_, Nat.minFac_dvd x⟩
    obtain ⟨y, hy⟩ := Nat.minFac_dvd x
    have hy2 : 2 ≤ y := by
      by_contra hy2
      interval_cases y
      · omega
      · rw [mul_one] at hy
        exact hnp (hy ▸ hq)
    nlinarith
  · intro hp
    refine ⟨hp.two_le, ?_⟩
    rintro d hd ⟨h2d, hdvd⟩
    rcases hp.eq_one_or_self_of_dvd d hdvd with h1 | hself
    · have := hds d hd
      omega
    · have := hp.two_le
      omega

/-! ## Population count by SWAR -/

/-- The sum of the first `L` base-`2 ^ w` digits of `x`. -/
def dsum (w : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | L + 1, x => x % 2 ^ w + dsum w L (x / 2 ^ w)

/-- The mask selecting the low `w` bits of each of `L` consecutive `2 * w`-bit
fields. -/
def evenMask (w : ℕ) : ℕ → ℕ
  | 0 => 0
  | L + 1 => 2 ^ (2 * w) * evenMask w L + (2 ^ w - 1)

/-- One SWAR step: add adjacent `w`-bit fields into `2 * w`-bit fields. -/
def swar (w L x : ℕ) : ℕ := (x &&& evenMask w L) + ((x >>> w) &&& evenMask w L)

/-- Peeling one field off `x &&& evenMask w (L + 1)`. -/
theorem land_evenMask_succ (w L x : ℕ) :
    x &&& evenMask w (L + 1) = 2 ^ (2 * w) * ((x / 2 ^ (2 * w)) &&& evenMask w L) + x % 2 ^ w := by
  have hpow : 2 ^ w ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 : 2 ^ w - 1 < 2 ^ (2 * w) := by have := Nat.one_le_two_pow (n := w); omega
  have h2 : x % 2 ^ w < 2 ^ (2 * w) := lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) hpow
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_land, evenMask, Nat.testBit_two_pow_mul_add _ h1,
    Nat.testBit_two_pow_mul_add _ h2]
  split_ifs with hj
  · rw [Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, Bool.and_comm]
  · rw [Nat.testBit_land, Nat.testBit_div_two_pow, Nat.sub_add_cancel (by omega)]

/-- Peeling one field off a SWAR step. -/
theorem swar_succ (w L x : ℕ) :
    swar w (L + 1) x =
      2 ^ (2 * w) * swar w L (x / 2 ^ (2 * w)) + (x % 2 ^ w + x / 2 ^ w % 2 ^ w) := by
  have hshift : x >>> w / 2 ^ (2 * w) = (x / 2 ^ (2 * w)) >>> w := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
      Nat.div_div_eq_div_mul, Nat.mul_comm]
  rw [swar, swar, land_evenMask_succ, land_evenMask_succ, hshift, Nat.shiftRight_eq_div_pow x w]
  ring

/-- A SWAR step preserves digit sums: the base-`2 ^ (2 * w)` digit sum of
`swar w L x` is the base-`2 ^ w` digit sum of the low `2 * L` fields of `x`. -/
theorem dsum_swar {w : ℕ} (hw : 0 < w) (L : ℕ) :
    ∀ x : ℕ, dsum (2 * w) L (swar w L x) = dsum w (2 * L) x := by
  induction L with
  | zero => intro x; rfl
  | succ L ih =>
    intro x
    have hd0 : x % 2 ^ w < 2 ^ w := Nat.mod_lt _ (by positivity)
    have hd1 : x / 2 ^ w % 2 ^ w < 2 ^ w := Nat.mod_lt _ (by positivity)
    have hpow : 2 ^ w + 2 ^ w ≤ 2 ^ (2 * w) := by
      rw [← two_mul, ← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hr : x % 2 ^ w + x / 2 ^ w % 2 ^ w < 2 ^ (2 * w) := by omega
    have hdiv : x / 2 ^ w / 2 ^ w = x / 2 ^ (2 * w) := by
      rw [Nat.div_div_eq_div_mul, ← pow_add, two_mul]
    rw [swar_succ, show 2 * (L + 1) = 2 * L + 1 + 1 by ring, dsum, dsum, dsum,
      Nat.add_comm (2 ^ (2 * w) * _), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr,
      Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hr, zero_add, ih, hdiv, add_assoc]

/-- `dsum_swar` with the widths named, for rewriting at numerals. -/
theorem dsum_swar' {w w2 L L2 : ℕ} (hw : 0 < w) (hw2 : w2 = 2 * w) (hL2 : L2 = 2 * L)
    (x : ℕ) : dsum w2 L (swar w L x) = dsum w L2 x := by
  rw [hw2, hL2, dsum_swar hw]

/-- Population count of the low `4096` bits, by twelve SWAR steps. -/
def pc (x : ℕ) : ℕ :=
  swar 2048 1 (swar 1024 2 (swar 512 4 (swar 256 8 (swar 128 16 (swar 64 32 (swar 32 64
    (swar 16 128 (swar 8 256 (swar 4 512 (swar 2 1024 (swar 1 2048 x))))))))))) % 2 ^ 4096

/-- `pc x` is the binary digit sum of the low `4096` bits of `x`. -/
theorem pc_eq_dsum (x : ℕ) : pc x = dsum 1 4096 x := by
  have h : pc x = dsum 4096 1 (swar 2048 1 (swar 1024 2 (swar 512 4 (swar 256 8 (swar 128 16
      (swar 64 32 (swar 32 64 (swar 16 128 (swar 8 256 (swar 4 512 (swar 2 1024
        (swar 1 2048 x)))))))))))) := by
    rw [pc, dsum, dsum, add_zero]
  rw [h, dsum_swar' (w := 2048) (w2 := 4096) (L := 1) (L2 := 2) (by norm_num) rfl rfl,
    dsum_swar' (w := 1024) (w2 := 2048) (L := 2) (L2 := 4) (by norm_num) rfl rfl,
    dsum_swar' (w := 512) (w2 := 1024) (L := 4) (L2 := 8) (by norm_num) rfl rfl,
    dsum_swar' (w := 256) (w2 := 512) (L := 8) (L2 := 16) (by norm_num) rfl rfl,
    dsum_swar' (w := 128) (w2 := 256) (L := 16) (L2 := 32) (by norm_num) rfl rfl,
    dsum_swar' (w := 64) (w2 := 128) (L := 32) (L2 := 64) (by norm_num) rfl rfl,
    dsum_swar' (w := 32) (w2 := 64) (L := 64) (L2 := 128) (by norm_num) rfl rfl,
    dsum_swar' (w := 16) (w2 := 32) (L := 128) (L2 := 256) (by norm_num) rfl rfl,
    dsum_swar' (w := 8) (w2 := 16) (L := 256) (L2 := 512) (by norm_num) rfl rfl,
    dsum_swar' (w := 4) (w2 := 8) (L := 512) (L2 := 1024) (by norm_num) rfl rfl,
    dsum_swar' (w := 2) (w2 := 4) (L := 1024) (L2 := 2048) (by norm_num) rfl rfl,
    dsum_swar' (w := 1) (w2 := 2) (L := 2048) (L2 := 4096) (by norm_num) rfl rfl]

/-- The binary digit sum of the low `L` bits counts the set bits below `L`. -/
theorem dsum_one_eq_count (L : ℕ) :
    ∀ x : ℕ, dsum 1 L x = Nat.count (fun i => x.testBit i = true) L := by
  induction L with
  | zero => intro x; rfl
  | succ L ih =>
    intro x
    rw [dsum, Nat.count_succ', ih, pow_one]
    simp only [Nat.testBit_div_two]
    rw [Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h, add_comm]

/-- Counting a predicate cut off at `len` over a longer range. -/
theorem count_lt_and {len M : ℕ} (q : ℕ → Prop) [DecidablePred q] (h : len ≤ M) :
    Nat.count (fun i => i < len ∧ q i) M = Nat.count q len := by
  induction M, h using Nat.le_induction with
  | base =>
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
    congr 1
    apply Finset.filter_congr
    intro i hi
    rw [Finset.mem_range] at hi
    simp [hi]
  | succ M hM ih =>
    rw [Nat.count_succ, ih]
    simp only [show ¬ M < len by omega, false_and, if_false, add_zero]

/-- The number of set bits of `B` at positions `a, …, a + len - 1`, for
`len ≤ 4096`. -/
def segCount (B a len : ℕ) : ℕ := pc ((B >>> a) % 2 ^ len)

/-- `segCount B a len` counts the `i < len` with bit `a + i` of `B` set. -/
theorem segCount_eq {len : ℕ} (B a : ℕ) (hlen : len ≤ 4096) :
    segCount B a len = Nat.count (fun i => B.testBit (a + i) = true) len := by
  rw [segCount, pc_eq_dsum, dsum_one_eq_count, ← count_lt_and _ hlen]
  congr 1
  funext i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Bool.and_eq_true, decide_eq_true_iff]

/-! ## Certified tables of prime counts -/

/-- Two counting predicates agreeing below `n` have the same count below `n`. -/
theorem count_congr_lt {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] {n : ℕ}
    (h : ∀ i < n, p i ↔ q i) : Nat.count p n = Nat.count q n := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  congr 1
  apply Finset.filter_congr
  intro i hi
  exact h i (Finset.mem_range.mp hi)

/-- `Good f j L`: the list `L` records the number of primes below `f (j + i)`
at its index `i`. -/
def Good (f : ℕ → ℕ) (j : ℕ) (L : List ℕ) : Prop :=
  ∀ i < L.length, Nat.count Nat.Prime (f (j + i)) = L.getD i 0

/-- Concatenating certified tables. -/
theorem Good.append {f : ℕ → ℕ} {j j' : ℕ} {L1 L2 : List ℕ} (h1 : Good f j L1)
    (h2 : Good f j' L2) (hj : j + L1.length = j') : Good f j (L1 ++ L2) := by
  intro i hi
  rw [List.length_append] at hi
  by_cases hlt : i < L1.length
  · rw [List.getD_append _ _ _ _ hlt]
    exact h1 i hlt
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    have h := h2 (i - L1.length) (by omega)
    rwa [show j' + (i - L1.length) = j + i by omega] at h

/-- Reading off one entry of a certified table. -/
theorem Good.count_eq {f : ℕ → ℕ} {j : ℕ} {L : List ℕ} (h : Good f j L) {i c : ℕ}
    (hi : i < L.length) (hc : L.getD i 0 = c) : Nat.count Nat.Prime (f (j + i)) = c :=
  (h i hi).trans hc

/-- Checker for a list of claimed prime counts along the points `f j, f (j + 1), …`,
starting from the count `c` below `f j`, using the bitmask `B` of the primes in
the window `[lo, lo + S)`. -/
def chk (f : ℕ → ℕ) (B lo S : ℕ) : ℕ → ℕ → List ℕ → Bool
  | _, _, [] => true
  | j, c, v :: l =>
      (lo ≤ f j && f j ≤ f (j + 1) && f (j + 1) - f j ≤ 4096 && f (j + 1) ≤ lo + S &&
        v == c + segCount B (f j - lo) (f (j + 1) - f j)) && chk f B lo S (j + 1) v l

/-- Soundness of `chk`: if `B` is the prime bitmask of `[lo, lo + S)` and the
count below `f j` is `c`, a passing check certifies the list. -/
theorem chk_sound (f : ℕ → ℕ) (B lo S : ℕ)
    (hB : ∀ i < S, B.testBit i = true ↔ (lo + i).Prime) (l : List ℕ) :
    ∀ j c : ℕ, chk f B lo S j c l = true → Nat.count Nat.Prime (f j) = c →
      Good f (j + 1) l := by
  induction l with
  | nil => intro j c _ _ i hi; simp at hi
  | cons v l ih =>
    intro j c hchk hc
    simp only [chk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hchk
    obtain ⟨⟨⟨⟨⟨hlo, hmono⟩, hgap⟩, hS⟩, hv⟩, hrest⟩ := hchk
    have hcount : Nat.count Nat.Prime (f (j + 1)) = v := by
      have hsplit : f (j + 1) = f j + (f (j + 1) - f j) := by omega
      rw [hsplit, Nat.count_add, hc, hv, segCount_eq _ _ hgap]
      congr 1
      apply count_congr_lt
      intro i hi
      rw [hB _ (by omega), show lo + (f j - lo + i) = f j + i by omega]
    have hgood := ih (j + 1) v hrest hcount
    intro i hi
    rcases i with _ | i
    · simpa using hcount
    · have h := hgood i (by simpa using hi)
      rw [List.getD_cons_succ, ← h, show j + 1 + (i + 1) = j + 1 + 1 + i by omega]

/-! ## The sieving primes -/

/-- The prime bitmask of `[0, 1837)`, sieved by `2, …, 42`. -/
def smallSieve : ℕ := sieveW 0 1837 (List.range' 2 41)

/-- The primes below `1837`, read off `smallSieve`. -/
def ds : List ℕ := (List.range 1837).filter (fun p => smallSieve.testBit p)

/-- `smallSieve` is the prime bitmask of `[0, 1837)`. -/
theorem testBit_smallSieve {i : ℕ} (hi : i < 1837) : smallSieve.testBit i = true ↔ i.Prime := by
  have hpos : ∀ d ∈ List.range' 2 41, 0 < d := by
    intro d hd
    rw [List.mem_range'_1] at hd
    omega
  have hall : ∀ p : ℕ, p.Prime → p * p < 1837 → p ∈ List.range' 2 41 := by
    intro p hp hpp
    have h2 := hp.two_le
    rw [List.mem_range'_1]
    constructor
    · exact h2
    · nlinarith
  have h2 : ∀ d ∈ List.range' 2 41, 2 ≤ d := by
    intro d hd
    rw [List.mem_range'_1] at hd
    omega
  rw [smallSieve, testBit_sieveW hi _ hpos,
    sieve_cond_iff_prime (by omega : 0 + i < 1837) _ hall h2, zero_add]

/-- Membership in `ds`: exactly the primes below `1837`. -/
theorem mem_ds {p : ℕ} : p ∈ ds ↔ p < 1837 ∧ p.Prime := by
  rw [ds, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hp, hbit⟩
    exact ⟨hp, (testBit_smallSieve hp).mp hbit⟩
  · rintro ⟨hp, hprime⟩
    exact ⟨hp, (testBit_smallSieve hp).mpr hprime⟩

/-- The bound up to which sieving by `ds` is exact: `1837 ^ 2`. -/
def NMax : ℕ := 1837 * 1837

/-- For a window inside `[0, 1837 ^ 2)`, `sieveW lo S ds` is its prime bitmask. -/
theorem testBit_sieveW_ds {lo S : ℕ} (hN : lo + S ≤ NMax) :
    ∀ i < S, (sieveW lo S ds).testBit i = true ↔ (lo + i).Prime := by
  intro i hi
  have hpos : ∀ d ∈ ds, 0 < d := fun d hd => (mem_ds.mp hd).2.pos
  have h2 : ∀ d ∈ ds, 2 ≤ d := fun d hd => (mem_ds.mp hd).2.two_le
  have hall : ∀ p : ℕ, p.Prime → p * p < NMax → p ∈ ds := by
    intro p hp hpp
    refine mem_ds.mpr ⟨?_, hp⟩
    by_contra hbig
    unfold NMax at hpp
    nlinarith
  rw [testBit_sieveW hi _ hpos, sieve_cond_iff_prime (by omega : lo + i < NMax) _ hall h2]

/-! ## The two point sequences -/

/-- `fA k = k(k+1)/2 + 1`: the number of primes below `fA k` is `π(k(k+1)/2)`. -/
def fA (k : ℕ) : ℕ := k * (k + 1) / 2 + 1

/-- `fB k = k(k+1)/2 + 2`: the number of primes below `fB k` is
`π(1 + k(k+1)/2)`. -/
def fB (k : ℕ) : ℕ := k * (k + 1) / 2 + 2

/-- The count below `fA k` is `π(k(k+1)/2)`. -/
theorem count_fA (k : ℕ) :
    Nat.count Nat.Prime (fA k) = Nat.primeCounting (k * (k + 1) / 2) := rfl

/-- The count below `fB k` is `π(1 + k(k+1)/2)`. -/
theorem count_fB (k : ℕ) :
    Nat.count Nat.Prime (fB k) = Nat.primeCounting (1 + k * (k + 1) / 2) := by
  rw [Nat.primeCounting, Nat.primeCounting', fB]
  congr 1
  omega

/-! ## The table `tabA`: `π(k(k+1)/2)` for `k ≤ 2596` -/

/-- Chunk 0 of `tabA`: `π(k(k+1)/2)` for `k ∈ [1, 1023]`. -/
def sA0 : List ℕ := [
    0, 2, 3, 4, 6, 8, 9, 11, 14, 16, 18, 21, 24, 27, 30, 32, 36, 39, 42, 46, 50, 54, 58, 62, 66,
    70, 74, 79, 84, 90, 94, 99, 102, 108, 114, 121, 126, 131, 137, 141, 149, 154, 160, 166, 174,
    180, 188, 193, 200, 205, 216, 220, 226, 235, 242, 250, 259, 267, 274, 281, 290, 297, 305,
    312, 324, 329, 338, 347, 358, 367, 374, 381, 393, 403, 413, 422, 431, 440, 446, 457, 467,
    478, 487, 499, 510, 522, 531, 541, 552, 564, 574, 587, 596, 607, 617, 629, 640, 650, 661,
    675, 686, 697, 708, 721, 734, 747, 757, 775, 783, 796, 808, 823, 836, 847, 859, 873, 887,
    903, 914, 928, 938, 950, 968, 982, 994, 1007, 1022, 1035, 1049, 1061, 1076, 1093, 1108,
    1124, 1137, 1152, 1170, 1184, 1199, 1217, 1231, 1246, 1262, 1277, 1290, 1308, 1322, 1336,
    1354, 1369, 1383, 1398, 1411, 1430, 1446, 1463, 1480, 1500, 1518, 1532, 1553, 1570, 1585,
    1602, 1619, 1637, 1654, 1669, 1683, 1701, 1720, 1742, 1757, 1776, 1799, 1816, 1837, 1857,
    1875, 1891, 1908, 1926, 1943, 1961, 1981, 2000, 2020, 2039, 2057, 2080, 2101, 2122, 2137,
    2152, 2169, 2188, 2213, 2230, 2250, 2271, 2293, 2313, 2330, 2352, 2373, 2394, 2416, 2437,
    2460, 2484, 2502, 2524, 2547, 2565, 2591, 2609, 2631, 2654, 2679, 2700, 2721, 2738, 2759,
    2781, 2803, 2825, 2847, 2868, 2893, 2915, 2939, 2963, 2984, 3004, 3022, 3052, 3074, 3095,
    3124, 3147, 3169, 3195, 3217, 3238, 3259, 3282, 3302, 3330, 3352, 3380, 3401, 3424, 3447,
    3476, 3503, 3525, 3553, 3578, 3607, 3632, 3653, 3679, 3707, 3731, 3754, 3780, 3801, 3829,
    3854, 3879, 3907, 3935, 3960, 3990, 4009, 4034, 4059, 4086, 4112, 4140, 4166, 4196, 4221,
    4241, 4266, 4295, 4324, 4352, 4381, 4411, 4444, 4473, 4502, 4522, 4549, 4572, 4604, 4632,
    4660, 4687, 4714, 4739, 4765, 4794, 4822, 4849, 4873, 4905, 4935, 4963, 4990, 5022, 5051,
    5081, 5110, 5141, 5172, 5197, 5224, 5254, 5289, 5319, 5349, 5375, 5406, 5437, 5465, 5497,
    5521, 5557, 5585, 5615, 5641, 5679, 5709, 5741, 5776, 5811, 5836, 5870, 5903, 5933, 5962,
    5996, 6033, 6060, 6091, 6120, 6152, 6179, 6214, 6243, 6273, 6304, 6333, 6369, 6407, 6434,
    6462, 6492, 6526, 6563, 6595, 6623, 6656, 6691, 6727, 6762, 6794, 6822, 6855, 6885, 6914,
    6949, 6985, 7016, 7053, 7091, 7128, 7164, 7197, 7232, 7260, 7295, 7330, 7363, 7399, 7434,
    7472, 7503, 7537, 7570, 7606, 7649, 7681, 7713, 7746, 7782, 7813, 7852, 7885, 7926, 7965,
    8000, 8038, 8078, 8109, 8145, 8178, 8214, 8250, 8283, 8321, 8357, 8393, 8429, 8464, 8502,
    8542, 8569, 8605, 8644, 8686, 8726, 8763, 8798, 8835, 8869, 8908, 8949, 8991, 9032, 9065,
    9102, 9143, 9184, 9222, 9261, 9299, 9339, 9373, 9410, 9443, 9482, 9526, 9563, 9600, 9641,
    9675, 9716, 9759, 9804, 9841, 9872, 9911, 9952, 9989, 10031, 10073, 10108, 10151, 10193,
    10229, 10264, 10306, 10344, 10388, 10430, 10465, 10508, 10549, 10586, 10627, 10668, 10708,
    10752, 10790, 10828, 10868, 10909, 10958, 10995, 11033, 11076, 11121, 11159, 11200, 11243,
    11282, 11326, 11367, 11411, 11458, 11501, 11543, 11583, 11630, 11671, 11712, 11756, 11800,
    11843, 11885, 11920, 11969, 12007, 12055, 12100, 12146, 12186, 12232, 12271, 12314, 12355,
    12403, 12448, 12488, 12535, 12572, 12617, 12665, 12714, 12761, 12805, 12846, 12896, 12934,
    12978, 13022, 13071, 13117, 13166, 13210, 13252, 13289, 13337, 13378, 13422, 13466, 13516,
    13559, 13603, 13651, 13693, 13738, 13789, 13838, 13886, 13930, 13979, 14030, 14076, 14123,
    14168, 14214, 14260, 14307, 14357, 14395, 14441, 14493, 14535, 14582, 14623, 14677, 14721,
    14770, 14817, 14862, 14909, 14955, 15005, 15057, 15094, 15143, 15185, 15233, 15287, 15332,
    15373, 15418, 15465, 15517, 15570, 15615, 15665, 15716, 15765, 15812, 15864, 15912, 15952,
    16002, 16062, 16108, 16150, 16202, 16257, 16313, 16366, 16410, 16451, 16503, 16558, 16604,
    16656, 16706, 16757, 16810, 16869, 16915, 16970, 17014, 17064, 17115, 17172, 17216, 17267,
    17318, 17369, 17424, 17475, 17525, 17573, 17625, 17678, 17726, 17778, 17832, 17884, 17932,
    17988, 18035, 18084, 18141, 18188, 18236, 18289, 18341, 18391, 18446, 18502, 18552, 18611,
    18664, 18716, 18774, 18834, 18887, 18940, 18992, 19036, 19090, 19145, 19202, 19249, 19299,
    19349, 19406, 19454, 19508, 19563, 19624, 19675, 19729, 19787, 19835, 19899, 19947, 20003,
    20057, 20113, 20167, 20220, 20271, 20330, 20389, 20452, 20509, 20563, 20618, 20669, 20715,
    20769, 20827, 20880, 20928, 20983, 21032, 21093, 21148, 21202, 21258, 21314, 21375, 21435,
    21488, 21542, 21605, 21659, 21716, 21773, 21830, 21890, 21953, 22011, 22064, 22114, 22179,
    22235, 22288, 22347, 22400, 22466, 22521, 22577, 22630, 22685, 22749, 22801, 22858, 22914,
    22970, 23024, 23080, 23141, 23197, 23259, 23319, 23375, 23442, 23508, 23564, 23626, 23683,
    23743, 23801, 23862, 23918, 23972, 24031, 24093, 24156, 24213, 24270, 24330, 24384, 24443,
    24504, 24567, 24631, 24693, 24747, 24809, 24871, 24930, 24986, 25039, 25093, 25159, 25218,
    25286, 25346, 25401, 25463, 25516, 25579, 25639, 25696, 25762, 25814, 25877, 25932, 25990,
    26054, 26120, 26178, 26242, 26308, 26373, 26438, 26500, 26566, 26630, 26682, 26747, 26805,
    26869, 26924, 26990, 27051, 27122, 27185, 27245, 27307, 27373, 27442, 27506, 27576, 27644,
    27703, 27768, 27833, 27894, 27951, 28026, 28092, 28150, 28219, 28286, 28343, 28412, 28478,
    28542, 28607, 28665, 28729, 28792, 28858, 28922, 28991, 29056, 29118, 29178, 29241, 29307,
    29376, 29435, 29502, 29568, 29630, 29701, 29770, 29831, 29896, 29964, 30024, 30098, 30164,
    30232, 30299, 30369, 30436, 30496, 30555, 30623, 30694, 30755, 30810, 30877, 30949, 31011,
    31079, 31147, 31215, 31284, 31356, 31421, 31483, 31542, 31599, 31664, 31733, 31801, 31864,
    31943, 32009, 32078, 32141, 32207, 32280, 32345, 32412, 32473, 32542, 32613, 32682, 32752,
    32826, 32883, 32949, 33016, 33089, 33163, 33230, 33308, 33385, 33449, 33522, 33585, 33653,
    33722, 33794, 33864, 33928, 33988, 34057, 34125, 34200, 34257, 34328, 34389, 34463, 34537,
    34610, 34681, 34753, 34826, 34885, 34956, 35031, 35101, 35169, 35242, 35320, 35389, 35459,
    35529, 35593, 35672, 35746, 35819, 35881, 35950, 36025, 36086, 36172, 36243, 36316, 36394,
    36470, 36541, 36625, 36694, 36764, 36825, 36894, 36971, 37047, 37118, 37197, 37278, 37355,
    37417, 37483, 37552, 37617, 37694, 37773, 37851, 37918, 37979, 38053, 38129, 38196, 38278,
    38343, 38418, 38483, 38555, 38620, 38686, 38769, 38853, 38925, 38987, 39069, 39151, 39220,
    39304, 39380, 39453, 39523, 39604, 39686, 39765, 39829, 39907, 39983, 40060, 40135, 40212,
    40288, 40363, 40422, 40494, 40570, 40652, 40731, 40808, 40885, 40955, 41031, 41107, 41191,
    41273, 41343, 41418, 41497, 41579, 41658, 41724, 41795, 41871, 41957, 42029, 42106, 42181,
    42251, 42334, 42413, 42478, 42562, 42640, 42707, 42794, 42885, 42956, 43037, 43114, 43194,
    43276, 43350]

/-- Chunk 1 of `tabA`: `π(k(k+1)/2)` for `k ∈ [1024, 1447]`. -/
def sA1 : List ℕ := [
    43419, 43507, 43592, 43667, 43740, 43817, 43901, 43972, 44055, 44134, 44203, 44279, 44371,
    44441, 44521, 44592, 44668, 44753, 44835, 44908, 44980, 45058, 45136, 45214, 45298, 45379,
    45461, 45535, 45618, 45700, 45765, 45857, 45928, 46004, 46093, 46177, 46241, 46329, 46409,
    46489, 46566, 46636, 46720, 46801, 46891, 46972, 47060, 47137, 47212, 47296, 47379, 47458,
    47538, 47620, 47708, 47785, 47872, 47948, 48037, 48123, 48215, 48291, 48368, 48445, 48522,
    48613, 48694, 48778, 48859, 48946, 49020, 49101, 49185, 49268, 49352, 49437, 49520, 49599,
    49684, 49767, 49857, 49938, 50022, 50104, 50184, 50268, 50360, 50449, 50525, 50607, 50695,
    50775, 50850, 50940, 51022, 51098, 51179, 51258, 51341, 51413, 51507, 51589, 51676, 51766,
    51850, 51939, 52004, 52088, 52168, 52250, 52326, 52419, 52508, 52590, 52683, 52764, 52852,
    52933, 53020, 53103, 53195, 53275, 53358, 53443, 53526, 53621, 53702, 53790, 53879, 53972,
    54052, 54139, 54216, 54301, 54389, 54480, 54564, 54649, 54738, 54820, 54899, 54994, 55092,
    55181, 55265, 55350, 55435, 55527, 55612, 55702, 55789, 55871, 55960, 56047, 56139, 56229,
    56313, 56405, 56483, 56569, 56657, 56748, 56833, 56935, 57020, 57107, 57206, 57290, 57388,
    57474, 57567, 57642, 57732, 57824, 57901, 57985, 58073, 58172, 58257, 58355, 58448, 58533,
    58627, 58716, 58801, 58889, 58980, 59067, 59161, 59257, 59340, 59428, 59526, 59614, 59701,
    59784, 59863, 59945, 60032, 60121, 60214, 60301, 60402, 60487, 60588, 60679, 60757, 60846,
    60938, 61036, 61135, 61220, 61316, 61411, 61510, 61596, 61689, 61786, 61878, 61966, 62061,
    62146, 62232, 62329, 62423, 62507, 62608, 62697, 62793, 62891, 62974, 63070, 63165, 63258,
    63348, 63445, 63544, 63634, 63734, 63828, 63910, 64019, 64103, 64189, 64282, 64386, 64471,
    64558, 64654, 64752, 64844, 64940, 65030, 65121, 65219, 65307, 65407, 65503, 65599, 65697,
    65793, 65894, 65989, 66079, 66167, 66263, 66371, 66465, 66550, 66645, 66734, 66828, 66919,
    67015, 67113, 67208, 67300, 67391, 67489, 67585, 67679, 67775, 67865, 67959, 68054, 68156,
    68247, 68344, 68443, 68551, 68634, 68739, 68834, 68937, 69036, 69138, 69222, 69321, 69410,
    69518, 69613, 69707, 69810, 69912, 70006, 70106, 70194, 70296, 70396, 70496, 70584, 70683,
    70783, 70885, 70983, 71073, 71176, 71262, 71359, 71454, 71545, 71649, 71748, 71856, 71962,
    72061, 72164, 72254, 72339, 72436, 72538, 72641, 72737, 72835, 72940, 73043, 73148, 73249,
    73339, 73441, 73538, 73633, 73730, 73840, 73931, 74028, 74128, 74223, 74330, 74433, 74535,
    74627, 74717, 74816, 74916, 75023, 75121, 75218, 75315, 75404, 75504, 75603, 75709, 75812,
    75917, 76019, 76118, 76213, 76316, 76417, 76530, 76625, 76733, 76832, 76919, 77026, 77113,
    77217, 77316, 77412, 77517, 77617, 77712, 77817, 77918, 78018, 78118, 78218, 78326, 78433,
    78531, 78638, 78747, 78844, 78944, 79055, 79167, 79268, 79372, 79478, 79581, 79685, 79791,
    79883, 79995, 80105, 80206, 80306, 80413, 80518, 80619, 80726, 80826, 80923, 81032, 81133,
    81237, 81339, 81433, 81542, 81643, 81752, 81856, 81958]

/-- Chunk 2 of `tabA`: `π(k(k+1)/2)` for `k ∈ [1448, 1772]`. -/
def sA2 : List ℕ := [
    82061, 82171, 82266, 82364, 82469, 82573, 82672, 82781, 82886, 82980, 83080, 83194, 83293,
    83398, 83504, 83616, 83717, 83820, 83932, 84045, 84142, 84246, 84366, 84472, 84573, 84672,
    84780, 84885, 84979, 85095, 85202, 85319, 85432, 85535, 85633, 85746, 85848, 85962, 86071,
    86181, 86288, 86401, 86506, 86623, 86731, 86838, 86944, 87055, 87151, 87268, 87365, 87468,
    87573, 87679, 87793, 87898, 88011, 88125, 88233, 88343, 88447, 88553, 88654, 88765, 88868,
    88979, 89079, 89186, 89291, 89412, 89514, 89624, 89731, 89849, 89963, 90071, 90183, 90307,
    90419, 90529, 90635, 90747, 90856, 90961, 91065, 91177, 91288, 91404, 91524, 91638, 91751,
    91865, 91972, 92089, 92201, 92311, 92420, 92533, 92642, 92755, 92857, 92968, 93073, 93180,
    93286, 93391, 93495, 93601, 93712, 93832, 93951, 94061, 94181, 94285, 94394, 94504, 94612,
    94724, 94842, 94944, 95056, 95173, 95275, 95376, 95477, 95594, 95711, 95821, 95930, 96045,
    96152, 96272, 96391, 96510, 96615, 96715, 96843, 96951, 97075, 97188, 97296, 97413, 97519,
    97651, 97763, 97878, 97996, 98104, 98225, 98325, 98436, 98551, 98661, 98778, 98892, 99004,
    99125, 99244, 99358, 99464, 99579, 99687, 99803, 99915, 100026, 100144, 100261, 100373,
    100489, 100595, 100712, 100836, 100949, 101058, 101165, 101286, 101403, 101504, 101643,
    101756, 101868, 101984, 102095, 102204, 102324, 102442, 102546, 102667, 102784, 102904,
    103028, 103145, 103253, 103364, 103479, 103587, 103705, 103819, 103938, 104066, 104171,
    104291, 104407, 104522, 104647, 104758, 104877, 104993, 105108, 105222, 105339, 105457,
    105586, 105710, 105830, 105934, 106051, 106175, 106289, 106402, 106524, 106632, 106756,
    106885, 107021, 107146, 107254, 107368, 107484, 107591, 107713, 107831, 107951, 108081,
    108179, 108288, 108401, 108518, 108638, 108757, 108879, 109007, 109121, 109235, 109366,
    109492, 109625, 109741, 109864, 109978, 110097, 110213, 110334, 110464, 110573, 110702,
    110817, 110934, 111073, 111180, 111298, 111418, 111553, 111669, 111799, 111913, 112028,
    112139, 112267, 112386, 112491, 112627, 112756, 112873, 113001, 113120, 113236, 113355,
    113491, 113612, 113742, 113863, 113987, 114097, 114216, 114340, 114464, 114602, 114725,
    114848, 114975, 115094, 115225, 115340, 115465, 115582, 115698, 115813, 115947, 116061,
    116180, 116304, 116416, 116530, 116654, 116780, 116905, 117033, 117152, 117261, 117386,
    117514, 117643, 117759, 117888, 118002, 118139, 118260, 118398, 118505, 118628, 118757,
    118885, 118994, 119119]

/-- Chunk 3 of `tabA`: `π(k(k+1)/2)` for `k ∈ [1773, 2046]`. -/
def sA3 : List ℕ := [
    119255, 119378, 119498, 119623, 119741, 119866, 119984, 120111, 120228, 120343, 120482,
    120591, 120709, 120846, 120965, 121088, 121208, 121352, 121492, 121607, 121732, 121854,
    121987, 122099, 122224, 122347, 122476, 122602, 122728, 122854, 122986, 123118, 123245,
    123367, 123499, 123640, 123765, 123872, 123995, 124113, 124247, 124374, 124501, 124625,
    124752, 124882, 125017, 125151, 125263, 125391, 125510, 125631, 125759, 125907, 126041,
    126165, 126284, 126421, 126547, 126685, 126814, 126941, 127049, 127188, 127315, 127430,
    127564, 127693, 127817, 127946, 128084, 128218, 128357, 128470, 128598, 128728, 128860,
    128987, 129106, 129240, 129366, 129490, 129619, 129744, 129874, 130005, 130130, 130257,
    130385, 130514, 130640, 130764, 130903, 131034, 131158, 131281, 131425, 131567, 131698,
    131838, 131965, 132088, 132215, 132329, 132447, 132583, 132711, 132840, 132972, 133099,
    133232, 133367, 133498, 133634, 133768, 133902, 134036, 134161, 134290, 134419, 134556,
    134683, 134821, 134949, 135089, 135222, 135344, 135480, 135618, 135754, 135888, 136013,
    136152, 136278, 136399, 136538, 136664, 136814, 136951, 137087, 137222, 137361, 137489,
    137614, 137735, 137860, 137991, 138135, 138266, 138406, 138540, 138669, 138805, 138948,
    139083, 139221, 139351, 139484, 139624, 139772, 139907, 140033, 140165, 140293, 140431,
    140573, 140696, 140838, 140967, 141104, 141238, 141381, 141513, 141657, 141789, 141920,
    142049, 142177, 142311, 142438, 142580, 142720, 142857, 142995, 143137, 143280, 143404,
    143541, 143670, 143804, 143958, 144098, 144233, 144363, 144496, 144629, 144767, 144910,
    145048, 145183, 145329, 145459, 145591, 145720, 145872, 146003, 146130, 146269, 146411,
    146537, 146676, 146804, 146930, 147063, 147189, 147327, 147460, 147609, 147755, 147890,
    148019, 148162, 148296, 148436, 148573, 148719, 148867, 149002, 149139, 149277, 149414,
    149569, 149699, 149835, 149988, 150131, 150266, 150404, 150544, 150672, 150810, 150958,
    151092, 151242, 151389, 151524, 151652, 151793, 151935, 152067, 152210, 152335, 152478,
    152609, 152754, 152891, 153035, 153176, 153309, 153459, 153599, 153737, 153879, 154020,
    154149, 154279, 154431, 154564, 154704, 154839, 154989, 155131, 155270, 155411]

/-- Chunk 4 of `tabA`: `π(k(k+1)/2)` for `k ∈ [2047, 2287]`. -/
def sA4 : List ℕ := [
    155546, 155681, 155821, 155968, 156112, 156257, 156396, 156539, 156673, 156814, 156962,
    157109, 157238, 157380, 157516, 157667, 157808, 157948, 158094, 158225, 158376, 158512,
    158655, 158802, 158961, 159094, 159233, 159370, 159513, 159659, 159814, 159967, 160103,
    160249, 160382, 160517, 160664, 160806, 160953, 161099, 161248, 161381, 161516, 161662,
    161802, 161949, 162094, 162239, 162378, 162524, 162647, 162792, 162933, 163076, 163234,
    163383, 163529, 163653, 163798, 163938, 164073, 164215, 164360, 164509, 164663, 164802,
    164946, 165099, 165246, 165387, 165529, 165668, 165816, 165964, 166098, 166236, 166385,
    166546, 166701, 166849, 166983, 167134, 167287, 167438, 167594, 167748, 167899, 168037,
    168177, 168314, 168447, 168590, 168737, 168886, 169034, 169178, 169316, 169468, 169630,
    169773, 169907, 170057, 170210, 170356, 170492, 170640, 170778, 170919, 171064, 171204,
    171356, 171505, 171641, 171796, 171946, 172091, 172231, 172386, 172530, 172663, 172815,
    172963, 173098, 173258, 173395, 173555, 173697, 173858, 174006, 174158, 174308, 174449,
    174585, 174738, 174882, 175040, 175189, 175331, 175492, 175649, 175798, 175936, 176076,
    176243, 176386, 176537, 176684, 176833, 176965, 177113, 177272, 177422, 177581, 177726,
    177882, 178024, 178175, 178321, 178466, 178613, 178762, 178906, 179058, 179206, 179362,
    179510, 179661, 179817, 179977, 180123, 180274, 180433, 180578, 180740, 180882, 181021,
    181176, 181320, 181473, 181621, 181769, 181922, 182068, 182230, 182382, 182531, 182673,
    182829, 182983, 183133, 183289, 183450, 183591, 183742, 183899, 184057, 184203, 184341,
    184498, 184653, 184827, 184968, 185134, 185290, 185434, 185588, 185738, 185878, 186031,
    186189, 186326, 186487, 186640, 186798, 186942, 187094, 187253, 187415, 187558, 187720,
    187871, 188025, 188181, 188346, 188503, 188671, 188826, 188975, 189128, 189282, 189430,
    189594, 189747, 189901, 190051, 190200, 190348, 190501, 190654, 190806, 190975]

/-- Chunk 5 of `tabA`: `π(k(k+1)/2)` for `k ∈ [2288, 2505]`. -/
def sA5 : List ℕ := [
    191131, 191274, 191427, 191585, 191735, 191887, 192060, 192220, 192367, 192514, 192676,
    192832, 193003, 193155, 193308, 193464, 193620, 193795, 193950, 194100, 194256, 194414,
    194560, 194697, 194857, 195015, 195170, 195328, 195481, 195643, 195799, 195962, 196118,
    196283, 196436, 196595, 196757, 196903, 197073, 197231, 197389, 197547, 197707, 197868,
    198035, 198177, 198337, 198483, 198642, 198798, 198954, 199095, 199246, 199414, 199579,
    199731, 199894, 200038, 200202, 200351, 200510, 200670, 200839, 200992, 201155, 201320,
    201472, 201629, 201782, 201943, 202099, 202255, 202424, 202577, 202724, 202887, 203046,
    203196, 203373, 203527, 203701, 203859, 204024, 204197, 204365, 204519, 204683, 204851,
    205022, 205177, 205316, 205485, 205652, 205827, 205999, 206155, 206313, 206464, 206625,
    206794, 206950, 207112, 207261, 207419, 207583, 207744, 207913, 208069, 208218, 208392,
    208534, 208690, 208852, 209016, 209175, 209341, 209504, 209656, 209817, 209971, 210142,
    210300, 210464, 210626, 210795, 210949, 211103, 211267, 211438, 211600, 211768, 211931,
    212080, 212247, 212399, 212568, 212741, 212895, 213047, 213214, 213366, 213539, 213700,
    213862, 214009, 214179, 214346, 214516, 214679, 214851, 215006, 215169, 215326, 215490,
    215666, 215834, 215995, 216146, 216313, 216478, 216643, 216817, 216979, 217150, 217312,
    217473, 217650, 217810, 217963, 218121, 218293, 218443, 218619, 218781, 218939, 219105,
    219258, 219430, 219588, 219766, 219924, 220085, 220242, 220415, 220574, 220741, 220908,
    221063, 221212, 221387, 221562, 221729, 221918, 222083, 222254, 222411, 222580, 222757,
    222927, 223097, 223262, 223422, 223562, 223744, 223916, 224085, 224252, 224409, 224582,
    224766, 224932, 225096, 225256, 225422, 225600, 225761, 225926, 226082]

/-- Chunk 6 of `tabA`: `π(k(k+1)/2)` for `k ∈ [2506, 2596]`. -/
def sA6 : List ℕ := [
    226256, 226419, 226586, 226755, 226918, 227102, 227272, 227434, 227602, 227762, 227946,
    228102, 228276, 228457, 228617, 228788, 228944, 229131, 229292, 229465, 229638, 229809,
    229979, 230156, 230331, 230509, 230669, 230852, 231030, 231186, 231368, 231538, 231705,
    231875, 232042, 232219, 232381, 232554, 232740, 232918, 233073, 233235, 233410, 233574,
    233747, 233907, 234081, 234259, 234428, 234595, 234774, 234940, 235108, 235278, 235466,
    235628, 235794, 235963, 236133, 236320, 236484, 236645, 236819, 236975, 237142, 237316,
    237487, 237665, 237844, 238016, 238180, 238346, 238519, 238701, 238872, 239036, 239199,
    239366, 239541, 239728, 239898, 240061, 240239, 240399, 240569, 240734, 240888, 241051,
    241239, 241424, 241602]

/-- `tabA[k]` is `π(k(k+1)/2)` for `k = 0, …, 2596` (certified by `goodA`). -/
def tabA : List ℕ :=
  [0] ++ sA0 ++ sA1 ++ sA2 ++ sA3 ++ sA4 ++ sA5 ++ sA6

/-- Kernel check of chunk 0 of `tabA`, in the window `[1, 523777)`. -/
theorem chunkA0 : chk fA (sieveW 1 523776 ds) 1 523776 0 0 sA0 = true := by
  decide +kernel

/-- Kernel check of chunk 1 of `tabA`, in the window `[523777, 1047629)`. -/
theorem chunkA1 : chk fA (sieveW 523777 523852 ds) 523777 523852 1023 43350 sA1 = true := by
  decide +kernel

/-- Kernel check of chunk 2 of `tabA`, in the window `[1047629, 1570879)`. -/
theorem chunkA2 : chk fA (sieveW 1047629 523250 ds) 1047629 523250 1447 81958 sA2 = true := by
  decide +kernel

/-- Kernel check of chunk 3 of `tabA`, in the window `[1570879, 2094082)`. -/
theorem chunkA3 : chk fA (sieveW 1570879 523203 ds) 1570879 523203 1772 119119 sA3 = true := by
  decide +kernel

/-- Kernel check of chunk 4 of `tabA`, in the window `[2094082, 2616329)`. -/
theorem chunkA4 : chk fA (sieveW 2094082 522247 ds) 2094082 522247 2046 155411 sA4 = true := by
  decide +kernel

/-- Kernel check of chunk 5 of `tabA`, in the window `[2616329, 3138766)`. -/
theorem chunkA5 : chk fA (sieveW 2616329 522437 ds) 2616329 522437 2287 190975 sA5 = true := by
  decide +kernel

/-- Kernel check of chunk 6 of `tabA`, in the window `[3138766, 3370907)`. -/
theorem chunkA6 : chk fA (sieveW 3138766 232141 ds) 3138766 232141 2505 226082 sA6 = true := by
  decide +kernel

/-- The table `tabA` is certified: `tabA[k]` is the number of primes below
`fA k`. -/
theorem goodA : Good fA 0 tabA := by
  have hc0 : Nat.count Nat.Prime (fA 0) = 0 := by decide
  have base : Good fA 0 [0] := by
    intro i hi
    obtain rfl : i = 0 := by simpa using hi
    simpa using hc0
  have g0 : Good fA 1 sA0 :=
    chk_sound fA _ 1 523776 (testBit_sieveW_ds (by norm_num [NMax])) _ _ _ chunkA0 hc0
  have L0 : Good fA 0 ([0] ++ sA0) :=
    Good.append base g0 (by decide +kernel)
  have hc1 : Nat.count Nat.Prime (fA 1023) = 43350 :=
    g0.count_eq (i := 1022) (by decide +kernel) (by decide +kernel)
  have g1 : Good fA 1024 sA1 :=
    chk_sound fA _ 523777 523852 (testBit_sieveW_ds (by norm_num [NMax])) _ _ _ chunkA1 hc1
  have L1 : Good fA 0 ([0] ++ sA0 ++ sA1) :=
    Good.append L0 g1 (by decide +kernel)
  have hc2 : Nat.count Nat.Prime (fA 1447) = 81958 :=
    g1.count_eq (i := 423) (by decide +kernel) (by decide +kernel)
  have g2 : Good fA 1448 sA2 :=
    chk_sound fA _ 1047629 523250 (testBit_sieveW_ds (by norm_num [NMax])) _ _ _ chunkA2 hc2
  have L2 : Good fA 0 ([0] ++ sA0 ++ sA1 ++ sA2) :=
    Good.append L1 g2 (by decide +kernel)
  have hc3 : Nat.count Nat.Prime (fA 1772) = 119119 :=
    g2.count_eq (i := 324) (by decide +kernel) (by decide +kernel)
  have g3 : Good fA 1773 sA3 :=
    chk_sound fA _ 1570879 523203 (testBit_sieveW_ds (by norm_num [NMax])) _ _ _ chunkA3 hc3
  have L3 : Good fA 0 ([0] ++ sA0 ++ sA1 ++ sA2 ++ sA3) :=
    Good.append L2 g3 (by decide +kernel)
  have hc4 : Nat.count Nat.Prime (fA 2046) = 155411 :=
    g3.count_eq (i := 273) (by decide +kernel) (by decide +kernel)
  have g4 : Good fA 2047 sA4 :=
    chk_sound fA _ 2094082 522247 (testBit_sieveW_ds (by norm_num [NMax])) _ _ _ chunkA4 hc4
  have L4 : Good fA 0 ([0] ++ sA0 ++ sA1 ++ sA2 ++ sA3 ++ sA4) :=
    Good.append L3 g4 (by decide +kernel)
  have hc5 : Nat.count Nat.Prime (fA 2287) = 190975 :=
    g4.count_eq (i := 240) (by decide +kernel) (by decide +kernel)
  have g5 : Good fA 2288 sA5 :=
    chk_sound fA _ 2616329 522437 (testBit_sieveW_ds (by norm_num [NMax])) _ _ _ chunkA5 hc5
  have L5 : Good fA 0 ([0] ++ sA0 ++ sA1 ++ sA2 ++ sA3 ++ sA4 ++ sA5) :=
    Good.append L4 g5 (by decide +kernel)
  have hc6 : Nat.count Nat.Prime (fA 2505) = 226082 :=
    g5.count_eq (i := 217) (by decide +kernel) (by decide +kernel)
  have g6 : Good fA 2506 sA6 :=
    chk_sound fA _ 3138766 232141 (testBit_sieveW_ds (by norm_num [NMax])) _ _ _ chunkA6 hc6
  have L6 : Good fA 0 ([0] ++ sA0 ++ sA1 ++ sA2 ++ sA3 ++ sA4 ++ sA5 ++ sA6) :=
    Good.append L5 g6 (by decide +kernel)
  exact L6

/-! ## The table `tabB`: `π(1 + m(m+1)/2)` for `m ≤ 2596` -/

/-- Chunk 0 of `tabB`: `π(1 + m(m+1)/2)` for `m ∈ [1, 1023]`. -/
def sB0 : List ℕ := [
    1, 2, 4, 5, 6, 8, 10, 12, 14, 16, 19, 22, 24, 27, 30, 33, 36, 39, 43, 47, 50, 54, 59, 62,
    66, 70, 75, 79, 84, 90, 94, 99, 102, 108, 115, 121, 126, 131, 137, 142, 149, 154, 161, 167,
    174, 180, 189, 193, 200, 205, 217, 220, 226, 235, 242, 251, 259, 267, 274, 282, 290, 297,
    306, 313, 324, 329, 338, 348, 358, 367, 375, 381, 393, 403, 414, 423, 431, 440, 446, 457,
    467, 478, 487, 500, 510, 522, 531, 542, 552, 564, 574, 587, 596, 607, 618, 630, 640, 650,
    662, 676, 686, 697, 708, 721, 734, 747, 758, 775, 783, 796, 809, 824, 836, 847, 859, 873,
    887, 903, 914, 928, 938, 950, 968, 982, 994, 1007, 1022, 1035, 1049, 1061, 1077, 1094, 1108,
    1124, 1138, 1152, 1170, 1184, 1199, 1218, 1231, 1246, 1262, 1277, 1290, 1308, 1322, 1337,
    1354, 1369, 1383, 1398, 1411, 1430, 1446, 1463, 1480, 1500, 1519, 1532, 1553, 1570, 1586,
    1602, 1619, 1637, 1655, 1670, 1683, 1701, 1720, 1743, 1757, 1776, 1800, 1816, 1837, 1857,
    1876, 1891, 1908, 1926, 1943, 1962, 1981, 2000, 2021, 2039, 2057, 2080, 2101, 2122, 2137,
    2152, 2169, 2188, 2213, 2230, 2250, 2272, 2293, 2313, 2331, 2352, 2373, 2394, 2417, 2438,
    2460, 2484, 2503, 2524, 2547, 2565, 2591, 2609, 2631, 2654, 2680, 2700, 2721, 2738, 2760,
    2781, 2803, 2825, 2847, 2869, 2893, 2915, 2939, 2963, 2984, 3004, 3022, 3053, 3074, 3095,
    3124, 3148, 3169, 3195, 3217, 3238, 3259, 3282, 3302, 3330, 3352, 3380, 3402, 3424, 3447,
    3476, 3503, 3525, 3553, 3578, 3607, 3633, 3653, 3679, 3707, 3732, 3754, 3780, 3801, 3829,
    3854, 3879, 3908, 3935, 3960, 3990, 4010, 4034, 4059, 4086, 4112, 4141, 4166, 4196, 4221,
    4242, 4266, 4295, 4324, 4353, 4381, 4411, 4445, 4473, 4502, 4522, 4550, 4572, 4604, 4632,
    4661, 4687, 4714, 4739, 4765, 4794, 4822, 4849, 4874, 4905, 4935, 4963, 4990, 5022, 5051,
    5081, 5110, 5142, 5172, 5197, 5224, 5255, 5289, 5319, 5349, 5375, 5406, 5437, 5466, 5497,
    5521, 5557, 5585, 5615, 5641, 5679, 5709, 5741, 5776, 5811, 5836, 5870, 5903, 5933, 5963,
    5997, 6033, 6060, 6091, 6121, 6152, 6179, 6214, 6244, 6273, 6304, 6333, 6369, 6407, 6434,
    6463, 6492, 6526, 6563, 6596, 6624, 6656, 6691, 6727, 6762, 6794, 6822, 6855, 6886, 6914,
    6949, 6986, 7017, 7053, 7091, 7128, 7164, 7197, 7232, 7260, 7295, 7330, 7363, 7400, 7434,
    7472, 7503, 7537, 7571, 7606, 7649, 7681, 7714, 7746, 7782, 7814, 7852, 7885, 7926, 7965,
    8000, 8038, 8078, 8109, 8146, 8178, 8214, 8250, 8283, 8321, 8357, 8393, 8429, 8464, 8502,
    8543, 8570, 8605, 8644, 8686, 8726, 8763, 8798, 8835, 8870, 8908, 8949, 8992, 9033, 9065,
    9102, 9143, 9185, 9222, 9261, 9300, 9340, 9373, 9410, 9444, 9482, 9526, 9563, 9601, 9641,
    9675, 9716, 9759, 9804, 9841, 9872, 9911, 9952, 9989, 10031, 10073, 10109, 10151, 10193,
    10229, 10265, 10306, 10344, 10389, 10430, 10465, 10508, 10549, 10586, 10627, 10668, 10709,
    10752, 10790, 10828, 10868, 10909, 10958, 10995, 11033, 11077, 11121, 11159, 11200, 11243,
    11282, 11326, 11367, 11411, 11458, 11501, 11544, 11583, 11630, 11671, 11712, 11756, 11800,
    11843, 11886, 11921, 11969, 12007, 12055, 12101, 12146, 12186, 12233, 12271, 12314, 12355,
    12403, 12449, 12488, 12535, 12572, 12618, 12665, 12714, 12761, 12805, 12846, 12896, 12934,
    12978, 13022, 13071, 13117, 13166, 13210, 13252, 13289, 13337, 13378, 13422, 13467, 13516,
    13559, 13603, 13651, 13693, 13738, 13789, 13838, 13887, 13930, 13979, 14031, 14077, 14123,
    14168, 14215, 14260, 14307, 14357, 14396, 14442, 14493, 14535, 14582, 14623, 14677, 14721,
    14770, 14817, 14862, 14909, 14956, 15005, 15057, 15094, 15144, 15185, 15233, 15287, 15333,
    15374, 15418, 15465, 15517, 15570, 15615, 15665, 15716, 15765, 15812, 15864, 15912, 15952,
    16002, 16062, 16108, 16151, 16202, 16257, 16313, 16366, 16410, 16451, 16504, 16559, 16604,
    16656, 16706, 16758, 16810, 16869, 16915, 16970, 17014, 17064, 17116, 17172, 17216, 17267,
    17318, 17369, 17424, 17475, 17526, 17573, 17625, 17678, 17727, 17779, 17832, 17884, 17932,
    17989, 18035, 18084, 18141, 18189, 18236, 18289, 18342, 18391, 18446, 18502, 18552, 18611,
    18664, 18716, 18774, 18835, 18887, 18940, 18993, 19036, 19090, 19145, 19202, 19250, 19299,
    19349, 19406, 19455, 19508, 19563, 19624, 19675, 19729, 19787, 19836, 19899, 19947, 20003,
    20058, 20114, 20167, 20220, 20271, 20330, 20389, 20452, 20510, 20563, 20618, 20669, 20715,
    20770, 20827, 20880, 20929, 20983, 21032, 21093, 21149, 21203, 21258, 21314, 21376, 21435,
    21488, 21542, 21605, 21659, 21716, 21773, 21830, 21891, 21953, 22011, 22065, 22114, 22179,
    22235, 22288, 22347, 22400, 22466, 22522, 22578, 22630, 22685, 22749, 22801, 22858, 22914,
    22970, 23024, 23080, 23141, 23197, 23259, 23319, 23375, 23442, 23508, 23564, 23626, 23683,
    23744, 23801, 23862, 23918, 23973, 24031, 24093, 24156, 24213, 24270, 24330, 24384, 24443,
    24504, 24567, 24632, 24693, 24747, 24809, 24871, 24930, 24986, 25039, 25093, 25160, 25218,
    25286, 25346, 25402, 25463, 25516, 25580, 25639, 25696, 25762, 25815, 25877, 25932, 25990,
    26054, 26120, 26178, 26242, 26308, 26373, 26438, 26500, 26566, 26630, 26682, 26747, 26805,
    26870, 26924, 26990, 27051, 27122, 27185, 27245, 27307, 27373, 27442, 27506, 27577, 27645,
    27703, 27768, 27834, 27894, 27951, 28026, 28092, 28150, 28219, 28286, 28344, 28412, 28478,
    28542, 28607, 28666, 28729, 28792, 28858, 28922, 28991, 29056, 29118, 29178, 29241, 29307,
    29377, 29435, 29502, 29568, 29630, 29702, 29770, 29831, 29896, 29964, 30024, 30098, 30165,
    30232, 30299, 30369, 30436, 30497, 30555, 30623, 30695, 30755, 30810, 30877, 30949, 31012,
    31079, 31147, 31216, 31284, 31356, 31421, 31483, 31542, 31599, 31664, 31734, 31801, 31864,
    31943, 32009, 32079, 32141, 32207, 32280, 32346, 32412, 32473, 32542, 32613, 32682, 32752,
    32826, 32884, 32949, 33016, 33089, 33163, 33230, 33308, 33385, 33450, 33522, 33585, 33653,
    33722, 33794, 33864, 33928, 33988, 34057, 34125, 34200, 34257, 34328, 34389, 34463, 34537,
    34610, 34681, 34754, 34826, 34885, 34956, 35031, 35101, 35169, 35242, 35320, 35389, 35459,
    35529, 35593, 35672, 35746, 35819, 35882, 35951, 36025, 36086, 36172, 36243, 36316, 36394,
    36471, 36541, 36625, 36694, 36764, 36826, 36894, 36971, 37047, 37119, 37197, 37278, 37356,
    37418, 37483, 37552, 37618, 37694, 37773, 37851, 37918, 37979, 38053, 38129, 38196, 38278,
    38343, 38418, 38483, 38555, 38620, 38686, 38769, 38853, 38925, 38987, 39070, 39151, 39220,
    39304, 39381, 39453, 39523, 39604, 39686, 39765, 39829, 39907, 39983, 40060, 40135, 40212,
    40288, 40364, 40422, 40494, 40570, 40653, 40731, 40808, 40886, 40955, 41031, 41107, 41192,
    41273, 41343, 41418, 41497, 41580, 41658, 41724, 41795, 41871, 41957, 42029, 42106, 42181,
    42251, 42334, 42413, 42479, 42562, 42640, 42708, 42794, 42885, 42956, 43038, 43114, 43194,
    43276, 43351]

/-- Chunk 1 of `tabB`: `π(1 + m(m+1)/2)` for `m ∈ [1024, 1447]`. -/
def sB1 : List ℕ := [
    43420, 43507, 43592, 43667, 43740, 43817, 43901, 43973, 44055, 44134, 44203, 44279, 44371,
    44441, 44521, 44592, 44668, 44753, 44835, 44908, 44980, 45058, 45136, 45215, 45298, 45379,
    45461, 45535, 45618, 45700, 45765, 45858, 45928, 46004, 46093, 46177, 46241, 46329, 46409,
    46490, 46566, 46636, 46720, 46801, 46891, 46972, 47060, 47137, 47213, 47296, 47379, 47458,
    47539, 47620, 47708, 47785, 47872, 47948, 48037, 48123, 48215, 48291, 48368, 48445, 48522,
    48613, 48694, 48779, 48860, 48946, 49020, 49101, 49185, 49268, 49352, 49437, 49521, 49599,
    49684, 49768, 49857, 49938, 50022, 50105, 50185, 50268, 50360, 50450, 50525, 50607, 50695,
    50775, 50850, 50940, 51022, 51098, 51179, 51258, 51341, 51413, 51508, 51589, 51676, 51766,
    51850, 51939, 52004, 52088, 52169, 52250, 52326, 52419, 52508, 52590, 52683, 52764, 52852,
    52933, 53020, 53104, 53195, 53275, 53358, 53444, 53526, 53621, 53702, 53790, 53879, 53972,
    54052, 54139, 54217, 54301, 54389, 54480, 54565, 54649, 54738, 54820, 54899, 54994, 55092,
    55181, 55266, 55350, 55435, 55527, 55612, 55702, 55789, 55871, 55960, 56047, 56139, 56229,
    56313, 56405, 56483, 56569, 56657, 56748, 56833, 56936, 57021, 57107, 57206, 57290, 57388,
    57474, 57567, 57642, 57732, 57824, 57901, 57985, 58073, 58172, 58257, 58355, 58448, 58533,
    58627, 58716, 58802, 58889, 58980, 59068, 59161, 59257, 59340, 59429, 59526, 59614, 59701,
    59785, 59864, 59945, 60032, 60121, 60215, 60301, 60402, 60487, 60588, 60679, 60757, 60846,
    60938, 61036, 61135, 61220, 61316, 61411, 61510, 61596, 61690, 61786, 61878, 61967, 62061,
    62146, 62232, 62329, 62424, 62507, 62608, 62697, 62794, 62891, 62974, 63070, 63165, 63258,
    63348, 63445, 63544, 63634, 63734, 63828, 63911, 64019, 64103, 64189, 64282, 64386, 64471,
    64558, 64655, 64752, 64844, 64940, 65030, 65121, 65219, 65308, 65407, 65503, 65599, 65697,
    65793, 65894, 65989, 66080, 66168, 66263, 66371, 66465, 66550, 66645, 66734, 66829, 66920,
    67015, 67113, 67209, 67300, 67391, 67489, 67585, 67679, 67775, 67865, 67959, 68054, 68156,
    68247, 68344, 68443, 68551, 68634, 68739, 68834, 68937, 69036, 69138, 69222, 69321, 69410,
    69518, 69613, 69707, 69810, 69912, 70006, 70106, 70194, 70296, 70396, 70496, 70584, 70683,
    70784, 70885, 70983, 71073, 71176, 71262, 71359, 71454, 71546, 71649, 71748, 71856, 71962,
    72061, 72164, 72254, 72340, 72436, 72538, 72641, 72737, 72835, 72940, 73043, 73148, 73249,
    73339, 73441, 73539, 73633, 73730, 73840, 73931, 74028, 74128, 74223, 74331, 74433, 74535,
    74627, 74718, 74816, 74916, 75023, 75121, 75218, 75315, 75405, 75504, 75603, 75709, 75812,
    75917, 76019, 76118, 76214, 76316, 76417, 76530, 76625, 76733, 76832, 76919, 77026, 77113,
    77217, 77316, 77412, 77517, 77617, 77712, 77818, 77918, 78018, 78118, 78219, 78326, 78433,
    78531, 78639, 78747, 78844, 78944, 79055, 79168, 79268, 79372, 79478, 79581, 79685, 79791,
    79884, 79995, 80105, 80206, 80306, 80414, 80518, 80619, 80726, 80826, 80923, 81032, 81133,
    81237, 81339, 81433, 81542, 81644, 81752, 81856, 81958]

/-- Chunk 2 of `tabB`: `π(1 + m(m+1)/2)` for `m ∈ [1448, 1772]`. -/
def sB2 : List ℕ := [
    82062, 82171, 82266, 82364, 82469, 82573, 82672, 82781, 82886, 82980, 83080, 83194, 83294,
    83398, 83504, 83616, 83718, 83820, 83932, 84045, 84143, 84246, 84366, 84472, 84573, 84672,
    84780, 84885, 84980, 85095, 85202, 85320, 85432, 85535, 85633, 85747, 85849, 85962, 86071,
    86181, 86288, 86401, 86506, 86623, 86731, 86838, 86944, 87056, 87151, 87268, 87365, 87469,
    87573, 87679, 87793, 87899, 88011, 88125, 88233, 88343, 88447, 88553, 88654, 88765, 88869,
    88979, 89079, 89186, 89292, 89412, 89514, 89624, 89732, 89849, 89963, 90071, 90183, 90307,
    90419, 90529, 90635, 90747, 90856, 90961, 91065, 91177, 91288, 91404, 91524, 91638, 91751,
    91865, 91972, 92089, 92201, 92311, 92420, 92533, 92642, 92755, 92858, 92968, 93073, 93180,
    93286, 93391, 93495, 93601, 93712, 93832, 93951, 94062, 94181, 94285, 94394, 94505, 94612,
    94724, 94842, 94944, 95056, 95173, 95275, 95376, 95477, 95594, 95711, 95821, 95930, 96045,
    96152, 96272, 96392, 96510, 96615, 96716, 96844, 96951, 97075, 97188, 97296, 97413, 97519,
    97651, 97763, 97878, 97996, 98105, 98225, 98325, 98436, 98551, 98661, 98778, 98892, 99005,
    99125, 99244, 99358, 99465, 99579, 99687, 99803, 99916, 100026, 100144, 100261, 100373,
    100489, 100595, 100712, 100836, 100949, 101058, 101165, 101286, 101403, 101504, 101643,
    101756, 101868, 101984, 102095, 102204, 102324, 102442, 102546, 102668, 102784, 102904,
    103028, 103145, 103254, 103364, 103479, 103587, 103706, 103819, 103938, 104067, 104171,
    104291, 104407, 104523, 104647, 104758, 104877, 104993, 105108, 105222, 105339, 105458,
    105586, 105710, 105830, 105934, 106051, 106175, 106289, 106402, 106524, 106632, 106756,
    106885, 107021, 107146, 107254, 107369, 107484, 107591, 107713, 107832, 107952, 108081,
    108179, 108288, 108402, 108518, 108638, 108757, 108879, 109007, 109121, 109236, 109366,
    109492, 109625, 109741, 109864, 109978, 110097, 110213, 110334, 110464, 110573, 110702,
    110817, 110934, 111073, 111180, 111298, 111418, 111553, 111669, 111800, 111913, 112028,
    112139, 112268, 112386, 112491, 112627, 112756, 112873, 113001, 113121, 113237, 113355,
    113491, 113612, 113742, 113863, 113987, 114097, 114216, 114340, 114464, 114602, 114725,
    114848, 114975, 115094, 115226, 115340, 115465, 115582, 115698, 115813, 115947, 116061,
    116181, 116304, 116416, 116531, 116655, 116780, 116905, 117033, 117152, 117261, 117386,
    117515, 117643, 117759, 117888, 118002, 118139, 118260, 118398, 118505, 118628, 118757,
    118885, 118994, 119120]

/-- Chunk 3 of `tabB`: `π(1 + m(m+1)/2)` for `m ∈ [1773, 2046]`. -/
def sB3 : List ℕ := [
    119255, 119378, 119498, 119623, 119741, 119866, 119985, 120111, 120228, 120343, 120483,
    120591, 120709, 120846, 120965, 121088, 121208, 121352, 121493, 121608, 121732, 121854,
    121987, 122100, 122224, 122347, 122476, 122602, 122728, 122854, 122986, 123118, 123245,
    123367, 123499, 123640, 123765, 123872, 123995, 124114, 124247, 124374, 124502, 124625,
    124752, 124882, 125017, 125151, 125263, 125391, 125510, 125631, 125759, 125907, 126042,
    126166, 126284, 126421, 126548, 126685, 126814, 126941, 127050, 127189, 127315, 127430,
    127564, 127693, 127817, 127946, 128084, 128218, 128357, 128470, 128599, 128728, 128860,
    128987, 129106, 129240, 129366, 129490, 129620, 129744, 129874, 130005, 130131, 130257,
    130385, 130514, 130640, 130764, 130903, 131034, 131158, 131282, 131425, 131567, 131698,
    131838, 131965, 132088, 132215, 132329, 132447, 132583, 132711, 132841, 132972, 133099,
    133232, 133368, 133498, 133634, 133768, 133902, 134036, 134161, 134290, 134419, 134556,
    134683, 134821, 134949, 135089, 135222, 135344, 135480, 135618, 135754, 135889, 136014,
    136152, 136278, 136399, 136538, 136664, 136814, 136952, 137088, 137222, 137361, 137489,
    137614, 137735, 137860, 137991, 138135, 138266, 138406, 138540, 138670, 138805, 138948,
    139083, 139221, 139351, 139484, 139624, 139772, 139907, 140033, 140165, 140293, 140431,
    140573, 140697, 140838, 140967, 141104, 141239, 141382, 141513, 141657, 141789, 141920,
    142049, 142177, 142311, 142438, 142580, 142720, 142858, 142995, 143137, 143280, 143404,
    143542, 143670, 143804, 143958, 144098, 144233, 144363, 144496, 144629, 144767, 144910,
    145048, 145183, 145329, 145459, 145591, 145721, 145872, 146003, 146130, 146269, 146411,
    146537, 146677, 146804, 146930, 147063, 147189, 147328, 147460, 147609, 147755, 147890,
    148019, 148162, 148296, 148436, 148573, 148719, 148867, 149002, 149139, 149277, 149414,
    149570, 149699, 149835, 149988, 150131, 150266, 150404, 150545, 150672, 150810, 150958,
    151093, 151242, 151389, 151524, 151652, 151793, 151935, 152067, 152210, 152336, 152478,
    152609, 152754, 152891, 153035, 153176, 153310, 153459, 153599, 153737, 153880, 154021,
    154149, 154279, 154431, 154564, 154704, 154839, 154989, 155131, 155270, 155411]

/-- Chunk 4 of `tabB`: `π(1 + m(m+1)/2)` for `m ∈ [2047, 2287]`. -/
def sB4 : List ℕ := [
    155546, 155681, 155821, 155968, 156112, 156257, 156396, 156539, 156674, 156814, 156962,
    157109, 157239, 157380, 157516, 157667, 157808, 157949, 158094, 158225, 158377, 158512,
    158655, 158802, 158961, 159094, 159233, 159370, 159513, 159659, 159814, 159967, 160103,
    160249, 160382, 160517, 160664, 160807, 160953, 161099, 161249, 161381, 161516, 161662,
    161802, 161949, 162094, 162239, 162378, 162524, 162647, 162792, 162934, 163076, 163234,
    163383, 163529, 163653, 163798, 163938, 164073, 164215, 164360, 164509, 164663, 164803,
    164946, 165099, 165247, 165387, 165529, 165668, 165817, 165964, 166098, 166236, 166386,
    166546, 166701, 166849, 166983, 167134, 167287, 167438, 167594, 167748, 167899, 168037,
    168177, 168314, 168447, 168590, 168738, 168886, 169034, 169178, 169317, 169468, 169630,
    169773, 169907, 170057, 170210, 170356, 170492, 170640, 170778, 170919, 171064, 171204,
    171356, 171505, 171641, 171796, 171946, 172091, 172232, 172386, 172530, 172663, 172815,
    172963, 173098, 173258, 173395, 173555, 173697, 173858, 174006, 174159, 174308, 174449,
    174586, 174738, 174882, 175040, 175189, 175331, 175492, 175649, 175798, 175936, 176076,
    176243, 176386, 176537, 176684, 176833, 176965, 177113, 177272, 177422, 177581, 177726,
    177882, 178024, 178175, 178321, 178466, 178613, 178763, 178906, 179058, 179206, 179362,
    179511, 179661, 179817, 179977, 180124, 180274, 180433, 180578, 180740, 180882, 181021,
    181176, 181320, 181473, 181621, 181769, 181922, 182068, 182230, 182383, 182531, 182673,
    182829, 182984, 183133, 183289, 183450, 183591, 183742, 183899, 184057, 184203, 184341,
    184498, 184653, 184828, 184968, 185134, 185290, 185435, 185588, 185738, 185878, 186032,
    186189, 186326, 186487, 186640, 186798, 186942, 187094, 187253, 187415, 187558, 187720,
    187871, 188026, 188181, 188346, 188503, 188671, 188826, 188975, 189128, 189282, 189430,
    189594, 189747, 189902, 190051, 190200, 190348, 190502, 190654, 190806, 190975]

/-- Chunk 5 of `tabB`: `π(1 + m(m+1)/2)` for `m ∈ [2288, 2505]`. -/
def sB5 : List ℕ := [
    191132, 191274, 191427, 191586, 191735, 191887, 192060, 192220, 192368, 192514, 192676,
    192832, 193003, 193155, 193308, 193464, 193621, 193795, 193950, 194100, 194256, 194414,
    194560, 194697, 194857, 195015, 195170, 195329, 195481, 195643, 195799, 195963, 196118,
    196283, 196436, 196596, 196757, 196903, 197073, 197231, 197390, 197547, 197707, 197868,
    198035, 198177, 198337, 198483, 198642, 198798, 198954, 199095, 199246, 199414, 199579,
    199731, 199894, 200038, 200202, 200351, 200510, 200670, 200839, 200992, 201156, 201320,
    201472, 201629, 201782, 201943, 202099, 202255, 202424, 202577, 202724, 202888, 203047,
    203196, 203373, 203527, 203701, 203859, 204024, 204197, 204365, 204519, 204683, 204852,
    205022, 205177, 205316, 205486, 205652, 205827, 205999, 206155, 206313, 206464, 206625,
    206795, 206951, 207112, 207261, 207419, 207583, 207744, 207913, 208069, 208218, 208392,
    208534, 208690, 208852, 209016, 209175, 209341, 209504, 209656, 209817, 209972, 210143,
    210300, 210464, 210626, 210795, 210949, 211103, 211267, 211438, 211600, 211768, 211931,
    212081, 212247, 212399, 212568, 212741, 212895, 213047, 213214, 213366, 213539, 213700,
    213863, 214009, 214179, 214346, 214516, 214679, 214851, 215006, 215169, 215326, 215490,
    215666, 215834, 215996, 216146, 216313, 216478, 216643, 216817, 216979, 217150, 217312,
    217473, 217650, 217811, 217963, 218121, 218293, 218443, 218619, 218781, 218939, 219105,
    219259, 219430, 219588, 219766, 219924, 220085, 220242, 220415, 220574, 220741, 220908,
    221063, 221212, 221387, 221562, 221729, 221918, 222083, 222254, 222411, 222581, 222757,
    222927, 223097, 223262, 223422, 223562, 223744, 223916, 224085, 224252, 224409, 224583,
    224766, 224932, 225097, 225256, 225422, 225600, 225761, 225927, 226082]

/-- Chunk 6 of `tabB`: `π(1 + m(m+1)/2)` for `m ∈ [2506, 2596]`. -/
def sB6 : List ℕ := [
    226256, 226419, 226586, 226755, 226918, 227102, 227272, 227434, 227602, 227762, 227946,
    228102, 228276, 228457, 228617, 228788, 228944, 229131, 229292, 229465, 229638, 229810,
    229979, 230156, 230331, 230510, 230669, 230852, 231030, 231187, 231368, 231538, 231705,
    231875, 232042, 232219, 232381, 232554, 232740, 232918, 233073, 233235, 233411, 233574,
    233747, 233907, 234081, 234259, 234428, 234595, 234774, 234940, 235108, 235278, 235467,
    235628, 235794, 235963, 236133, 236320, 236484, 236645, 236820, 236975, 237142, 237316,
    237487, 237665, 237844, 238017, 238181, 238346, 238519, 238701, 238872, 239036, 239199,
    239367, 239541, 239728, 239898, 240061, 240239, 240399, 240569, 240734, 240889, 241051,
    241239, 241424, 241603]

/-- `tabB[m]` is `π(1 + m(m+1)/2)` for `m = 0, …, 2596` (certified by `goodB`). -/
def tabB : List ℕ :=
  [0] ++ sB0 ++ sB1 ++ sB2 ++ sB3 ++ sB4 ++ sB5 ++ sB6

/-- Kernel check of chunk 0 of `tabB`, in the window `[2, 523778)`. -/
theorem chunkB0 : chk fB (sieveW 2 523776 ds) 2 523776 0 0 sB0 = true := by
  decide +kernel

/-- Kernel check of chunk 1 of `tabB`, in the window `[523778, 1047630)`. -/
theorem chunkB1 : chk fB (sieveW 523778 523852 ds) 523778 523852 1023 43351 sB1 = true := by
  decide +kernel

/-- Kernel check of chunk 2 of `tabB`, in the window `[1047630, 1570880)`. -/
theorem chunkB2 : chk fB (sieveW 1047630 523250 ds) 1047630 523250 1447 81958 sB2 = true := by
  decide +kernel

/-- Kernel check of chunk 3 of `tabB`, in the window `[1570880, 2094083)`. -/
theorem chunkB3 : chk fB (sieveW 1570880 523203 ds) 1570880 523203 1772 119120 sB3 = true := by
  decide +kernel

/-- Kernel check of chunk 4 of `tabB`, in the window `[2094083, 2616330)`. -/
theorem chunkB4 : chk fB (sieveW 2094083 522247 ds) 2094083 522247 2046 155411 sB4 = true := by
  decide +kernel

/-- Kernel check of chunk 5 of `tabB`, in the window `[2616330, 3138767)`. -/
theorem chunkB5 : chk fB (sieveW 2616330 522437 ds) 2616330 522437 2287 190975 sB5 = true := by
  decide +kernel

/-- Kernel check of chunk 6 of `tabB`, in the window `[3138767, 3370908)`. -/
theorem chunkB6 : chk fB (sieveW 3138767 232141 ds) 3138767 232141 2505 226082 sB6 = true := by
  decide +kernel

/-- The table `tabB` is certified: `tabB[m]` is the number of primes below
`fB m`. -/
theorem goodB : Good fB 0 tabB := by
  have hc0 : Nat.count Nat.Prime (fB 0) = 0 := by decide
  have base : Good fB 0 [0] := by
    intro i hi
    obtain rfl : i = 0 := by simpa using hi
    simpa using hc0
  have g0 : Good fB 1 sB0 :=
    chk_sound fB _ 2 523776 (testBit_sieveW_ds (by norm_num [NMax])) _ _ _ chunkB0 hc0
  have L0 : Good fB 0 ([0] ++ sB0) :=
    Good.append base g0 (by decide +kernel)
  have hc1 : Nat.count Nat.Prime (fB 1023) = 43351 :=
    g0.count_eq (i := 1022) (by decide +kernel) (by decide +kernel)
  have g1 : Good fB 1024 sB1 :=
    chk_sound fB _ 523778 523852 (testBit_sieveW_ds (by norm_num [NMax])) _ _ _ chunkB1 hc1
  have L1 : Good fB 0 ([0] ++ sB0 ++ sB1) :=
    Good.append L0 g1 (by decide +kernel)
  have hc2 : Nat.count Nat.Prime (fB 1447) = 81958 :=
    g1.count_eq (i := 423) (by decide +kernel) (by decide +kernel)
  have g2 : Good fB 1448 sB2 :=
    chk_sound fB _ 1047630 523250 (testBit_sieveW_ds (by norm_num [NMax])) _ _ _ chunkB2 hc2
  have L2 : Good fB 0 ([0] ++ sB0 ++ sB1 ++ sB2) :=
    Good.append L1 g2 (by decide +kernel)
  have hc3 : Nat.count Nat.Prime (fB 1772) = 119120 :=
    g2.count_eq (i := 324) (by decide +kernel) (by decide +kernel)
  have g3 : Good fB 1773 sB3 :=
    chk_sound fB _ 1570880 523203 (testBit_sieveW_ds (by norm_num [NMax])) _ _ _ chunkB3 hc3
  have L3 : Good fB 0 ([0] ++ sB0 ++ sB1 ++ sB2 ++ sB3) :=
    Good.append L2 g3 (by decide +kernel)
  have hc4 : Nat.count Nat.Prime (fB 2046) = 155411 :=
    g3.count_eq (i := 273) (by decide +kernel) (by decide +kernel)
  have g4 : Good fB 2047 sB4 :=
    chk_sound fB _ 2094083 522247 (testBit_sieveW_ds (by norm_num [NMax])) _ _ _ chunkB4 hc4
  have L4 : Good fB 0 ([0] ++ sB0 ++ sB1 ++ sB2 ++ sB3 ++ sB4) :=
    Good.append L3 g4 (by decide +kernel)
  have hc5 : Nat.count Nat.Prime (fB 2287) = 190975 :=
    g4.count_eq (i := 240) (by decide +kernel) (by decide +kernel)
  have g5 : Good fB 2288 sB5 :=
    chk_sound fB _ 2616330 522437 (testBit_sieveW_ds (by norm_num [NMax])) _ _ _ chunkB5 hc5
  have L5 : Good fB 0 ([0] ++ sB0 ++ sB1 ++ sB2 ++ sB3 ++ sB4 ++ sB5) :=
    Good.append L4 g5 (by decide +kernel)
  have hc6 : Nat.count Nat.Prime (fB 2505) = 226082 :=
    g5.count_eq (i := 217) (by decide +kernel) (by decide +kernel)
  have g6 : Good fB 2506 sB6 :=
    chk_sound fB _ 3138767 232141 (testBit_sieveW_ds (by norm_num [NMax])) _ _ _ chunkB6 hc6
  have L6 : Good fB 0 ([0] ++ sB0 ++ sB1 ++ sB2 ++ sB3 ++ sB4 ++ sB5 ++ sB6) :=
    Good.append L5 g6 (by decide +kernel)
  exact L6

/-! ## Reading the tables -/

/-- `tabA` has `2597` entries. -/
theorem tabA_length : tabA.length = 2597 := by decide +kernel

/-- `tabB` has `2597` entries. -/
theorem tabB_length : tabB.length = 2597 := by decide +kernel

/-- `π(k(k+1)/2) = tabA[k]` for `k ≤ 2596`. -/
theorem primeCounting_tri (k : ℕ) (hk : k ≤ 2596) :
    Nat.primeCounting (k * (k + 1) / 2) = tabA.getD k 0 := by
  rw [← count_fA]
  have h := goodA k (by rw [tabA_length]; omega)
  rwa [zero_add] at h

/-- `π(1 + m(m+1)/2) = tabB[m]` for `m ≤ 2596`. -/
theorem primeCounting_one_add_tri (m : ℕ) (hm : m ≤ 2596) :
    Nat.primeCounting (1 + m * (m + 1) / 2) = tabB.getD m 0 := by
  rw [← count_fB]
  have h := goodB m (by rw [tabB_length]; omega)
  rwa [zero_add] at h

/-- `k ↦ k(k+1)/2` is monotone. -/
theorem tri_mono {k k' : ℕ} (h : k ≤ k') : k * (k + 1) / 2 ≤ k' * (k' + 1) / 2 :=
  Nat.div_le_div_right (Nat.mul_le_mul h (by omega))

/-- An entry of index `1 ≤ k` lies in `L.drop 1`. -/
theorem getD_mem_drop_one {L : List ℕ} {k : ℕ} (hk1 : 1 ≤ k) (hk : k < L.length) :
    L.getD k 0 ∈ L.drop 1 := by
  rw [List.getD_eq_getElem _ _ hk]
  have hlen : k - 1 < (L.drop 1).length := by
    rw [List.length_drop]
    omega
  have h := List.getElem_mem hlen
  rw [List.getElem_drop] at h
  have hidx : 1 + (k - 1) = k := by omega
  simp only [hidx] at h
  exact h

/-! ## Bounding the pair set and ground truth -/

/-- If `n < π(K(K+1)/2)` and `n < π(1 + M(M+1)/2)`, every pair counted by
`a(n)` has `k < K` and `m < M`. -/
theorem pairSet_subset (n K M : ℕ) (hK : n < Nat.primeCounting (K * (K + 1) / 2))
    (hM : n < Nat.primeCounting (1 + M * (M + 1) / 2)) :
    pairSet n ⊆ ↑(Finset.Ioo 0 K ×ˢ Finset.Ioo 0 M) := by
  rintro ⟨k, m⟩ ⟨hk, hm, heq⟩
  simp only at hk hm heq
  simp only [Finset.coe_product, Finset.coe_Ioo, Set.mem_prod, Set.mem_Ioo]
  refine ⟨⟨hk, ?_⟩, ⟨hm, ?_⟩⟩
  · by_contra hKk
    have hmono := Nat.monotone_primeCounting (tri_mono (show K ≤ k by omega))
    omega
  · by_contra hMm
    have hmono := Nat.monotone_primeCounting
      (Nat.add_le_add_left (tri_mono (show M ≤ m by omega)) 1)
    omega

/-- Under the bounds of `pairSet_subset`, `a(n)` is the cardinality of an
explicit finite filter. -/
theorem a_eq_card (n K M : ℕ) (hK : n < Nat.primeCounting (K * (K + 1) / 2))
    (hM : n < Nat.primeCounting (1 + M * (M + 1) / 2)) :
    a n = ((Finset.Ioo 0 K ×ˢ Finset.Ioo 0 M).filter fun p =>
      n = Nat.primeCounting (p.1 * (p.1 + 1) / 2) +
        Nat.primeCounting (1 + p.2 * (p.2 + 1) / 2)).card := by
  have hset : pairSet n = ↑((Finset.Ioo 0 K ×ˢ Finset.Ioo 0 M).filter fun p =>
      n = Nat.primeCounting (p.1 * (p.1 + 1) / 2) +
        Nat.primeCounting (1 + p.2 * (p.2 + 1) / 2)) := by
    ext p
    constructor
    · intro hp
      have hsub := pairSet_subset n K M hK hM hp
      rw [Finset.coe_filter]
      exact ⟨Finset.mem_coe.mp hsub, hp.2.2⟩
    · intro hp
      rw [Finset.coe_filter] at hp
      obtain ⟨hmem, heq⟩ := hp
      rw [Finset.mem_product, Finset.mem_Ioo, Finset.mem_Ioo] at hmem
      exact ⟨hmem.1.1, hmem.2.1, heq⟩
  rw [a, hset, Set.ncard_coe_finset]

/-- `a(n)` computed from the tables, for `K, M ≤ 2596`. -/
def aTab (n K M : ℕ) : ℕ :=
  ((Finset.Ioo 0 K ×ˢ Finset.Ioo 0 M).filter fun p =>
    n = tabA.getD p.1 0 + tabB.getD p.2 0).card

/-- Under table-checkable bounds, `a n = aTab n K M`. -/
theorem a_eq_aTab (n K M : ℕ) (hK : K ≤ 2596) (hM : M ≤ 2596) (hnK : n < tabA.getD K 0)
    (hnM : n < tabB.getD M 0) : a n = aTab n K M := by
  rw [a_eq_card n K M (by rwa [primeCounting_tri K hK])
    (by rwa [primeCounting_one_add_tri M hM]), aTab]
  congr 1
  apply Finset.filter_congr
  intro p hp
  rw [Finset.mem_product, Finset.mem_Ioo, Finset.mem_Ioo] at hp
  rw [primeCounting_tri p.1 (by omega), primeCounting_one_add_tri p.2 (by omega)]

/-- The first twenty listed terms `a(1), …, a(20)`. -/
theorem a_ground_truth : ∀ n ∈ List.range' 1 20,
    a n = [1, 1, 1, 3, 3, 3, 3, 5, 3, 6, 3, 6, 4, 6, 4, 7, 4, 6, 6, 6].getD (n - 1) 0 := by
  intro n hn
  have hn20 : n < 21 := by
    rw [List.mem_range'_1] at hn
    omega
  have hA : tabA.getD 12 0 = 21 := by decide +kernel
  have hB : tabB.getD 12 0 = 22 := by decide +kernel
  rw [a_eq_aTab n 12 12 (by norm_num) (by norm_num) (by omega) (by omega)]
  revert n
  decide +kernel

/-! ## The counterexample `n = 241540` -/

/-- OR of `2 ^ b` over a list: a bitmask of its elements. -/
def orMask (L : List ℕ) : ℕ := L.foldr (fun b acc => 2 ^ b ||| acc) 0

/-- Bit `t` of `orMask L` is set iff `t ∈ L`. -/
theorem testBit_orMask (L : List ℕ) (t : ℕ) : (orMask L).testBit t = true ↔ t ∈ L := by
  induction L with
  | nil => simp [orMask]
  | cons b L ih =>
    simp only [orMask, List.foldr_cons] at ih ⊢
    rw [Nat.testBit_lor, Nat.testBit_two_pow, Bool.or_eq_true, ih, decide_eq_true_eq,
      List.mem_cons, eq_comm]

/-- For every `m ∈ [1, 2596]`, either `π(1 + T_m) > 241540` or
`241540 - π(1 + T_m)` is not of the form `π(T_k)` with `k ∈ [1, 2596]`. -/
def pairCheck : Bool :=
  (tabB.drop 1).all fun b => 241540 < b || !(orMask (tabA.drop 1)).testBit (241540 - b)

/-- Kernel check of `pairCheck`. -/
theorem pairCheck_eq : pairCheck = true := by decide +kernel

/-- No pair `(k, m)` with `k, m > 0` has `241540 = π(k(k+1)/2) + π(1 + m(m+1)/2)`. -/
theorem pairSet_241540 : pairSet 241540 = ∅ := by
  ext ⟨k, m⟩
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hk, hm, heq⟩
  simp only at hk hm heq
  have hA2596 : tabA.getD 2596 0 = 241602 := by decide +kernel
  have hB2596 : tabB.getD 2596 0 = 241603 := by decide +kernel
  have hk' : k ≤ 2595 := by
    by_contra hbig
    have hmono := Nat.monotone_primeCounting (tri_mono (show 2596 ≤ k by omega))
    rw [primeCounting_tri 2596 le_rfl, hA2596] at hmono
    omega
  have hm' : m ≤ 2595 := by
    by_contra hbig
    have hmono := Nat.monotone_primeCounting
      (Nat.add_le_add_left (tri_mono (show 2596 ≤ m by omega)) 1)
    rw [primeCounting_one_add_tri 2596 le_rfl, hB2596] at hmono
    omega
  rw [primeCounting_tri k (by omega), primeCounting_one_add_tri m (by omega)] at heq
  have hmemA := getD_mem_drop_one (L := tabA) hk (by rw [tabA_length]; omega)
  have hmemB := getD_mem_drop_one (L := tabB) hm (by rw [tabB_length]; omega)
  have hchk := pairCheck_eq
  rw [pairCheck, List.all_eq_true] at hchk
  have hb := hchk _ hmemB
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hb
  rcases hb with hlt | hbit
  · omega
  · rw [show 241540 - tabB.getD m 0 = tabA.getD k 0 by omega,
      (testBit_orMask _ _).mpr hmemA] at hbit
    exact Bool.noConfusion hbit

/-- `a(241540) = 0`. -/
theorem a_241540 : a 241540 = 0 := by
  rw [a, pairSet_241540, Set.ncard_empty]

/-- `241540` is not of the form `π(k(k+1)/2) + π(1 + m(m+1)/2)` with `k, m > 0`. -/
theorem not_exists_rep_241540 :
    ¬ ∃ k m : ℕ, 0 < k ∧ 0 < m ∧
      241540 = Nat.primeCounting (k * (k + 1) / 2) + Nat.primeCounting (1 + m * (m + 1) / 2) := by
  rintro ⟨k, m, hk, hm, heq⟩
  have hmem : (k, m) ∈ pairSet 241540 := ⟨hk, hm, heq⟩
  rw [pairSet_241540] at hmem
  exact hmem

/-- **Sun's global conjecture is false.**  Counterexample `n = 241540`: there
is no pair `(k, m)` with `k, m > 0` and
`241540 = π(k(k+1)/2) + π(1 + m(m+1)/2)`, so `a(241540) = 0`.  The primary
OEIS entry states the conjecture for every positive `n` and separately reports
verification through `10^5`; the counterexample lies beyond that verified
range.  A further zero, `a(350366) = 0`, was found by computation but is not
formalized here. -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  have hpos := h 241540 (by norm_num)
  rw [a_241540] at hpos
  exact lt_irrefl 0 hpos

end Candidates.A262995Refutation
