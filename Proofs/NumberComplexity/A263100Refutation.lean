/-
# A263100 — refutation of Sun's uniqueness conjecture (part (i))

## OEIS source (retained from `oeis show A263100`; see the external
## evidence capture recorded for this repair)

```
NAME:     Number of ordered pairs (k, m) with k > 0 and m > 0 such that
          n = pi(k^2) + pi(m^2/2), where pi(x) denotes the number of primes
          not exceeding x.
OFFSET:   1
TERMS:    1,2,1,3,2,3,3,2,4,2,6,2,5,2,5,4,4,4,4,5,3,5,5,4,4,6,6,1,7,4,6,4,...
COMMENT:  Conjecture: (i) a(n) > 0 for all n > 0, and a(n) = 1 only for
          n = 1, 3, 28.
COMMENT:  (ii) Any integer n > 0 can be written as pi(k^2) + pi((m^2+1)/2)
          with k and m positive integers.
COMMENT:  (iii) Each n = 1,2,3,... can be written as pi(k^2/2) +
          pi((m^2+1)/2) with k and m positive integers.
```

The retained primary capture states part (i) as a global conjecture and does
not restrict it to the displayed terms or to a finite table.  Its Mathematica
program evaluates `PrimePi[m^2/2]`, the number of primes not exceeding the
rational `m^2/2`; this equals `π(⌊m^2/2⌋)`, which is what `Nat.primeCounting
(m ^ 2 / 2)` computes with floor division.

## Status of this module

This module **refutes** part (i): `a(15293) = 1`, the unique pair being
`(k, m) = (339, 291)`, since `π(339^2) = π(114921) = 10867` and
`π(⌊291^2/2⌋) = π(42340) = 4426`.  A separate bounded computation (Python
sieve, 2026-10-21) finds that the `n ≤ 10^5` with
`a(n) = 1` are exactly `1, 3, 28, 15293, 72102`, and that `a(n) > 0` for all
`1 ≤ n ≤ 10^5`; the positivity half of part (i) is not addressed here.

## Proof method

All values of `π` needed lie below `411^2`.  For `2 ≤ i < 411^2`, `i` is
prime iff `gcd(i, (i-1)!) = 1` (for `i ≤ 410`) or `gcd(i, P) = 1` (for
`i > 410`), where `P` is the product of the primes up to `410`
(`piTest_iff`).  A chain checker (`checkRange`) verifies the tables `tabA`
(`π(k^2)`, `k ≤ 410`) and `tabB` (`π(⌊m^2/2⌋)`, `m ≤ 579`) segment by
segment against this test, in kernel-checked chunks of about `2 * 10^4`
integers each.  The pair search is a bitmask membership test (`kCheck`) plus
a scan of `tabB` (`mCheck`).  All computations use `decide +kernel`; no
`native_decide` and no axioms.

`Elab.async false` keeps the kernel checks sequential; under a virtual-memory
cap the default asynchronous elaboration fails to create its worker threads.
-/
import Mathlib

set_option autoImplicit false
set_option Elab.async false

namespace Candidates.A263100Refutation

/-! ## Definitions -/

/-- The set of ordered pairs `(k, m)` with `k > 0`, `m > 0` and
`n = π(k^2) + π(⌊m^2/2⌋)`. -/
def pairSet (n : ℕ) : Set (ℕ × ℕ) :=
  {p | 0 < p.1 ∧ 0 < p.2 ∧ n = Nat.primeCounting (p.1 ^ 2) + Nat.primeCounting (p.2 ^ 2 / 2)}

/-- OEIS A263100: the number of ordered pairs `(k, m)` with `k > 0`, `m > 0`
and `n = π(k^2) + π(⌊m^2/2⌋)`.  The set is finite for every `n`
(`pairSet_finite`), so `Set.ncard` is the honest count. -/
noncomputable def a (n : ℕ) : ℕ := (pairSet n).ncard

/-- **Sun's conjecture, part (i) (A263100, Zhi-Wei Sun, Oct 09 2015).**
Verbatim: "Conjecture: (i) a(n) > 0 for all n > 0, and a(n) = 1 only for
n = 1, 3, 28."  The "only for" clause is read as the implication
`a(n) = 1 → n ∈ {1, 3, 28}`; this is the weaker reading (the converse
`a(1) = a(3) = a(28) = 1` holds, see `a_ground_truth`), so refuting it refutes
every reading. -/
def Conjecture : Prop :=
  (∀ n : ℕ, 0 < n → 0 < a n) ∧ (∀ n : ℕ, 0 < n → a n = 1 → n = 1 ∨ n = 3 ∨ n = 28)

/-! ## Bounding the pair set -/

/-- If `n < π(K^2)` and `n < π(⌊M^2/2⌋)`, every pair counted by `a(n)` has
`k < K` and `m < M`. -/
theorem pairSet_subset (n K M : ℕ) (hK : n < Nat.primeCounting (K ^ 2))
    (hM : n < Nat.primeCounting (M ^ 2 / 2)) :
    pairSet n ⊆ ↑(Finset.Ioo 0 K ×ˢ Finset.Ioo 0 M) := by
  rintro ⟨k, m⟩ ⟨hk, hm, heq⟩
  simp only at hk hm heq
  simp only [Finset.coe_product, Finset.coe_Ioo, Set.mem_prod, Set.mem_Ioo]
  refine ⟨⟨hk, ?_⟩, ⟨hm, ?_⟩⟩
  · by_contra hKk
    have hmono : Nat.primeCounting (K ^ 2) ≤ Nat.primeCounting (k ^ 2) :=
      Nat.monotone_primeCounting (Nat.pow_le_pow_left (by omega) 2)
    omega
  · by_contra hMm
    have hmono : Nat.primeCounting (M ^ 2 / 2) ≤ Nat.primeCounting (m ^ 2 / 2) :=
      Nat.monotone_primeCounting (Nat.div_le_div_right (Nat.pow_le_pow_left (by omega) 2))
    omega

/-- The pair set is finite for every `n`, because `π` is unbounded. -/
theorem pairSet_finite (n : ℕ) : (pairSet n).Finite := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (Nat.tendsto_primeCounting.eventually (Filter.eventually_gt_atTop n))
  have hK : n < Nat.primeCounting (N ^ 2) := hN _ (Nat.le_self_pow two_ne_zero N)
  have hM : n < Nat.primeCounting ((2 * N) ^ 2 / 2) := by
    apply hN
    have h : (2 * N) ^ 2 / 2 = 2 * N ^ 2 := by
      rw [mul_pow, show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, mul_assoc, Nat.mul_div_cancel_left _ two_pos]
    rw [h]
    exact (Nat.le_self_pow two_ne_zero N).trans (Nat.le_mul_of_pos_left _ two_pos)
  exact (Finset.finite_toSet _).subset (pairSet_subset n N (2 * N) hK hM)

/-- Under the bounds of `pairSet_subset`, `a(n)` is the cardinality of an
explicit finite filter. -/
theorem a_eq_card (n K M : ℕ) (hK : n < Nat.primeCounting (K ^ 2))
    (hM : n < Nat.primeCounting (M ^ 2 / 2)) :
    a n = ((Finset.Ioo 0 K ×ˢ Finset.Ioo 0 M).filter fun p =>
      n = Nat.primeCounting (p.1 ^ 2) + Nat.primeCounting (p.2 ^ 2 / 2)).card := by
  have hset : pairSet n = ↑((Finset.Ioo 0 K ×ˢ Finset.Ioo 0 M).filter fun p =>
      n = Nat.primeCounting (p.1 ^ 2) + Nat.primeCounting (p.2 ^ 2 / 2)) := by
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

/-! ## A certified primality test below `411^2` -/

/-- The product of the primes `p ≤ 410` (the primorial of `409`). -/
def P : ℕ :=
  16681652761084211919179159418724436936084403222565933843061705761318156534633165693010396587115320816578125913093533540343113453511622786292849190442459895794911314610

/-- Primality test valid for `i < 411^2`: `i ≥ 2` and `i` is coprime to
`(i-1)!` (for `i ≤ 410`) or to `P` (for `i > 410`). -/
def piTest (i : ℕ) : Bool :=
  2 ≤ i && Nat.gcd i (if i ≤ 410 then Nat.factorial (i - 1) else P) == 1

/-- Every `2 ≤ q ≤ 410` shares a factor with `P`; in particular every prime
`q ≤ 410` divides `P`. -/
theorem P_gcd_ne_one : ∀ q < 411, 2 ≤ q → Nat.gcd q P ≠ 1 := by decide +kernel

/-- `P` divides `410!`, so every prime factor of `P` is at most `410`. -/
theorem P_dvd_factorial : P ∣ Nat.factorial 410 := by
  apply Nat.dvd_of_mod_eq_zero
  decide +kernel

/-- Correctness of `piTest`: for `i < 411^2`, `piTest i` holds iff `i` is
prime. -/
theorem piTest_iff {i : ℕ} (hi : i < 411 ^ 2) : piTest i = true ↔ i.Prime := by
  unfold piTest
  by_cases h2 : 2 ≤ i
  · have hi1 : i ≠ 1 := by omega
    have hq := Nat.minFac_prime hi1
    have hqdvd : Nat.minFac i ∣ i := Nat.minFac_dvd i
    have hqle : Nat.minFac i ≤ i := Nat.minFac_le (by omega)
    simp only [h2, decide_true, Bool.true_and, beq_iff_eq]
    split_ifs with hsmall
    · constructor
      · intro hcop
        rw [Nat.prime_def_minFac]
        refine ⟨h2, ?_⟩
        by_contra hne
        have hlt : Nat.minFac i ≤ i - 1 := by omega
        have hdf : Nat.minFac i ∣ Nat.factorial (i - 1) :=
          Nat.dvd_factorial hq.pos hlt
        have hg : Nat.minFac i ∣ Nat.gcd i (Nat.factorial (i - 1)) := Nat.dvd_gcd hqdvd hdf
        rw [hcop] at hg
        exact hq.one_lt.ne' (Nat.dvd_one.mp hg)
      · intro hp
        have hnd : ¬ i ∣ Nat.factorial (i - 1) := by
          rw [hp.dvd_factorial]
          omega
        exact (hp.coprime_iff_not_dvd).mpr hnd
    · constructor
      · intro hcop
        by_contra hnp
        have hsq : Nat.minFac i ^ 2 ≤ i := Nat.minFac_sq_le_self (by omega) hnp
        by_cases hq410 : Nat.minFac i < 411
        · have hgq : Nat.gcd (Nat.minFac i) P ≠ 1 := P_gcd_ne_one _ hq410 hq.two_le
          have hqP : Nat.minFac i ∣ P := by
            by_contra hnd
            exact hgq ((hq.coprime_iff_not_dvd).mpr hnd)
          have hg : Nat.minFac i ∣ Nat.gcd i P := Nat.dvd_gcd hqdvd hqP
          rw [hcop] at hg
          exact hq.one_lt.ne' (Nat.dvd_one.mp hg)
        · have h411 : 411 ^ 2 ≤ Nat.minFac i ^ 2 := Nat.pow_le_pow_left (by omega) 2
          omega
      · intro hp
        have hnd : ¬ i ∣ P := by
          intro hdvd
          have hf : i ∣ Nat.factorial 410 := hdvd.trans P_dvd_factorial
          rw [hp.dvd_factorial] at hf
          omega
        exact (hp.coprime_iff_not_dvd).mpr hnd
  · have hnp : ¬ i.Prime := fun hp => h2 hp.two_le
    simp [h2, hnp]

/-- The number of `i ∈ [a, a + n)` passing `piTest`. -/
def segCount (a n : ℕ) : ℕ := (List.range n).countP (fun k => piTest (a + k))

/-- Below `411^2`, `segCount` counts the primes in `[a, a + n)`. -/
theorem count_prime_add (a n : ℕ) (h : a + n ≤ 411 ^ 2) :
    Nat.count Nat.Prime (a + n) = Nat.count Nat.Prime a + segCount a n := by
  rw [Nat.count_add]
  congr 1
  unfold segCount Nat.count
  apply List.countP_congr
  intro k hk
  rw [List.mem_range] at hk
  rw [decide_eq_true_iff, piTest_iff (by omega)]

/-- Chain checker: along the points `f j ≤ f (j+1) ≤ … ≤ f (j+n) ≤ 411^2`, the
claimed values `g` increase by the number of primes in each segment
`[f i, f (i+1))`. -/
def checkRange (f g : ℕ → ℕ) (j : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 =>
      (f j ≤ f (j + 1) && f (j + 1) ≤ 411 ^ 2 &&
        g (j + 1) == g j + segCount (f j) (f (j + 1) - f j)) && checkRange f g (j + 1) n

/-- Soundness of `checkRange`: if the chain checks and `g` is correct at the
start, then `g (j + i)` is the number of primes below `f (j + i)` for all
`i ≤ n`. -/
theorem checkRange_sound (f g : ℕ → ℕ) (n : ℕ) : ∀ j : ℕ, checkRange f g j n = true →
    Nat.count Nat.Prime (f j) = g j →
    ∀ i ≤ n, Nat.count Nat.Prime (f (j + i)) = g (j + i) := by
  induction n with
  | zero =>
    intro j _ h0 i hi
    obtain rfl : i = 0 := by omega
    simpa using h0
  | succ n ih =>
    intro j hchk h0 i hi
    simp only [checkRange, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hchk
    obtain ⟨⟨⟨hmono, hbound⟩, hstep⟩, hrest⟩ := hchk
    have h1 : Nat.count Nat.Prime (f (j + 1)) = g (j + 1) := by
      have hsplit : f (j + 1) = f j + (f (j + 1) - f j) := by omega
      rw [hsplit, count_prime_add _ _ (by omega), h0]
      exact hstep.symm
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simpa using h0
    · have hnext := ih (j + 1) hrest h1 (i - 1) (by omega)
      have hidx : j + 1 + (i - 1) = j + i := by omega
      rwa [hidx] at hnext

/-- Two consecutive checked chains combine into one. -/
theorem checkRange_add (f g : ℕ → ℕ) (n m : ℕ) : ∀ j : ℕ, checkRange f g j n = true →
    checkRange f g (j + n) m = true → checkRange f g j (n + m) = true := by
  induction n with
  | zero => intro j _ h; simpa using h
  | succ n ih =>
    intro j h1 h2
    rw [show n + 1 + m = (n + m) + 1 by omega]
    simp only [checkRange, Bool.and_eq_true] at h1 ⊢
    refine ⟨h1.1, ih (j + 1) h1.2 ?_⟩
    rwa [show j + 1 + n = j + (n + 1) by omega]

/-! ## The tables `π(k^2)` and `π(⌊m^2/2⌋)` -/

/-- `tabA[k] = π(k^2)` for `k = 0, …, 410` (certified by `primeCounting_sq`). -/
def tabA : List ℕ := [
    0, 0, 2, 4, 6, 9, 11, 15, 18, 22, 25, 30, 34, 39, 44, 48, 54, 61, 66, 72, 78, 85, 92, 99, 105,
    114, 122, 129, 137, 146, 154, 162, 172, 181, 191, 200, 210, 219, 228, 240, 251, 263, 274, 283,
    295, 306, 319, 329, 342, 357, 367, 378, 393, 409, 421, 434, 445, 457, 474, 487, 503, 519, 532,
    549, 564, 578, 594, 609, 624, 641, 654, 675, 690, 705, 722, 739, 757, 779, 793, 811, 834, 847,
    867, 886, 906, 923, 939, 960, 982, 1000, 1018, 1038, 1058, 1077, 1100, 1121, 1142, 1163, 1185,
    1208, 1229, 1252, 1274, 1294, 1315, 1336, 1357, 1381, 1400, 1423, 1447, 1471, 1498, 1523,
    1547, 1572, 1594, 1617, 1646, 1667, 1686, 1715, 1743, 1766, 1796, 1821, 1848, 1877, 1900,
    1924, 1948, 1976, 2004, 2032, 2057, 2088, 2118, 2141, 2163, 2190, 2223, 2248, 2281, 2310,
    2334, 2366, 2392, 2426, 2456, 2489, 2515, 2547, 2580, 2607, 2637, 2672, 2702, 2729, 2757,
    2788, 2818, 2851, 2883, 2915, 2951, 2980, 3010, 3043, 3076, 3107, 3145, 3178, 3211, 3241,
    3274, 3302, 3338, 3377, 3407, 3436, 3476, 3512, 3551, 3585, 3625, 3656, 3695, 3731, 3765,
    3795, 3834, 3868, 3908, 3945, 3986, 4018, 4052, 4089, 4127, 4164, 4203, 4236, 4271, 4313,
    4352, 4396, 4436, 4480, 4515, 4551, 4589, 4627, 4669, 4707, 4743, 4781, 4821, 4857, 4899,
    4942, 4978, 5022, 5065, 5106, 5152, 5191, 5229, 5274, 5318, 5356, 5397, 5442, 5483, 5522,
    5570, 5611, 5652, 5698, 5743, 5792, 5835, 5882, 5926, 5968, 6018, 6059, 6101, 6147, 6186,
    6232, 6275, 6320, 6365, 6414, 6454, 6495, 6542, 6595, 6636, 6684, 6735, 6783, 6823, 6869,
    6910, 6960, 7007, 7057, 7108, 7161, 7206, 7252, 7300, 7351, 7399, 7450, 7499, 7544, 7594,
    7650, 7694, 7743, 7789, 7842, 7891, 7950, 7999, 8053, 8103, 8152, 8198, 8251, 8303, 8354,
    8405, 8452, 8506, 8555, 8600, 8657, 8713, 8769, 8821, 8870, 8928, 8985, 9041, 9089, 9147,
    9205, 9260, 9309, 9361, 9416, 9466, 9525, 9580, 9631, 9685, 9745, 9805, 9855, 9907, 9964,
    10022, 10077, 10127, 10191, 10238, 10298, 10353, 10415, 10466, 10523, 10580, 10639, 10690,
    10756, 10811, 10867, 10921, 10987, 11041, 11098, 11159, 11214, 11274, 11335, 11399, 11460,
    11522, 11578, 11641, 11701, 11762, 11823, 11882, 11936, 11998, 12064, 12131, 12187, 12248,
    12307, 12366, 12433, 12490, 12553, 12613, 12677, 12751, 12813, 12873, 12934, 12997, 13062,
    13129, 13196, 13255, 13314, 13372, 13435, 13499, 13566, 13631, 13692, 13756, 13829, 13895,
    13960, 14034, 14100, 14164, 14228, 14293, 14360, 14420, 14490, 14552, 14615, 14683, 14752,
    14818, 14877, 14951, 15018, 15084, 15146, 15209, 15283, 15346]

/-- `tabB[m] = π(⌊m^2/2⌋)` for `m = 0, …, 579` (certified by
`primeCounting_half`). -/
def tabB : List ℕ := [
    0, 0, 1, 2, 4, 5, 7, 9, 11, 12, 15, 17, 20, 23, 25, 29, 31, 34, 37, 41, 46, 47, 53, 56, 61,
    64, 68, 72, 77, 81, 87, 92, 97, 100, 106, 111, 118, 124, 128, 134, 139, 146, 152, 157, 163,
    169, 177, 185, 190, 196, 204, 211, 217, 222, 231, 240, 247, 257, 263, 270, 278, 283, 293, 299,
    309, 318, 326, 334, 344, 352, 363, 368, 377, 386, 399, 409, 418, 427, 436, 444, 452, 462, 474,
    481, 492, 504, 516, 526, 536, 548, 558, 570, 580, 590, 600, 611, 623, 635, 647, 654, 669, 681,
    692, 703, 713, 728, 738, 753, 765, 780, 789, 802, 816, 832, 842, 854, 867, 881, 894, 909, 919,
    932, 942, 960, 975, 987, 1003, 1013, 1028, 1044, 1057, 1068, 1085, 1102, 1116, 1130, 1146,
    1160, 1179, 1192, 1208, 1225, 1237, 1254, 1271, 1285, 1300, 1315, 1330, 1345, 1359, 1376,
    1392, 1405, 1421, 1440, 1457, 1472, 1489, 1509, 1526, 1543, 1561, 1577, 1593, 1608, 1629,
    1648, 1663, 1675, 1695, 1710, 1733, 1752, 1768, 1788, 1808, 1827, 1847, 1864, 1883, 1899,
    1917, 1935, 1952, 1972, 1988, 2011, 2030, 2047, 2069, 2090, 2110, 2129, 2146, 2160, 2177,
    2197, 2223, 2240, 2262, 2284, 2305, 2323, 2343, 2362, 2385, 2405, 2429, 2449, 2470, 2492,
    2513, 2533, 2555, 2580, 2601, 2617, 2643, 2666, 2693, 2711, 2729, 2749, 2769, 2792, 2812,
    2837, 2858, 2881, 2906, 2923, 2952, 2976, 2993, 3013, 3041, 3063, 3085, 3107, 3136, 3159,
    3181, 3204, 3227, 3246, 3271, 3293, 3315, 3340, 3368, 3389, 3415, 3433, 3460, 3489, 3512,
    3540, 3562, 3590, 3620, 3643, 3668, 3693, 3720, 3744, 3767, 3793, 3815, 3840, 3862, 3893,
    3922, 3946, 3974, 3999, 4023, 4049, 4070, 4099, 4127, 4154, 4179, 4208, 4231, 4257, 4283,
    4310, 4337, 4366, 4397, 4426, 4455, 4486, 4512, 4534, 4564, 4590, 4618, 4646, 4675, 4699,
    4727, 4754, 4780, 4808, 4837, 4861, 4891, 4921, 4950, 4975, 5005, 5033, 5066, 5095, 5126,
    5157, 5186, 5211, 5239, 5273, 5304, 5333, 5358, 5389, 5421, 5451, 5481, 5509, 5541, 5573,
    5601, 5629, 5658, 5693, 5722, 5758, 5792, 5824, 5856, 5886, 5922, 5948, 5983, 6017, 6047,
    6076, 6104, 6136, 6163, 6195, 6226, 6260, 6290, 6320, 6350, 6390, 6421, 6448, 6477, 6510,
    6542, 6581, 6610, 6641, 6675, 6708, 6743, 6779, 6806, 6840, 6870, 6904, 6931, 6968, 7003,
    7037, 7076, 7107, 7145, 7178, 7215, 7243, 7281, 7311, 7347, 7384, 7417, 7454, 7488, 7519,
    7554, 7585, 7628, 7663, 7695, 7730, 7763, 7796, 7837, 7871, 7908, 7949, 7980, 8020, 8056,
    8095, 8126, 8163, 8193, 8233, 8269, 8303, 8340, 8370, 8413, 8445, 8482, 8524, 8555, 8584,
    8624, 8663, 8701, 8745, 8781, 8818, 8856, 8889, 8930, 8974, 9013, 9047, 9085, 9125, 9161,
    9206, 9244, 9282, 9320, 9355, 9392, 9427, 9465, 9505, 9544, 9585, 9618, 9657, 9696, 9738,
    9783, 9824, 9857, 9891, 9927, 9971, 10014, 10049, 10090, 10125, 10171, 10213, 10244, 10285,
    10327, 10368, 10410, 10452, 10483, 10526, 10566, 10609, 10653, 10686, 10735, 10769, 10811,
    10849, 10888, 10929, 10976, 11013, 11056, 11095, 11143, 11179, 11220, 11258, 11306, 11342,
    11394, 11437, 11476, 11525, 11565, 11607, 11652, 11693, 11734, 11776, 11819, 11865, 11901,
    11941, 11987, 12035, 12079, 12126, 12163, 12211, 12251, 12291, 12333, 12377, 12426, 12467,
    12509, 12551, 12593, 12644, 12685, 12739, 12782, 12825, 12870, 12915, 12956, 13001, 13048,
    13095, 13140, 13188, 13231, 13271, 13314, 13356, 13399, 13442, 13491, 13537, 13580, 13629,
    13672, 13714, 13763, 13817, 13862, 13907, 13955, 14008, 14051, 14102, 14147, 14189, 14234,
    14282, 14331, 14375, 14420, 14472, 14516, 14557, 14601, 14648, 14700, 14747, 14793, 14841,
    14880, 14935, 14979, 15028, 15077, 15115, 15167, 15209, 15260, 15308]

/-- Lookup in `tabA`. -/
def gA (k : ℕ) : ℕ := tabA.getD k 0

/-- Lookup in `tabB`. -/
def gB (m : ℕ) : ℕ := tabB.getD m 0

/-- Chain points for `tabA`: `π(k^2)` is the number of primes below `k^2 + 1`. -/
def sqPt (k : ℕ) : ℕ := k ^ 2 + 1

/-- Chain points for `tabB`: `π(⌊m^2/2⌋)` is the number of primes below
`⌊m^2/2⌋ + 1`. -/
def halfPt (m : ℕ) : ℕ := m ^ 2 / 2 + 1

/-! Kernel-checked chunks of about `1.1 * 10^4` integers each (larger chunks
exceed the memory cap). -/

/-- Kernel check of the `tabA` chain for `k ∈ [0, 104]`. -/
theorem chunkA0 : checkRange sqPt gA 0 104 = true := by
  decide +kernel
/-- Kernel check of the `tabA` chain for `k ∈ [104, 147]`. -/
theorem chunkA1 : checkRange sqPt gA 104 43 = true := by
  decide +kernel
/-- Kernel check of the `tabA` chain for `k ∈ [147, 180]`. -/
theorem chunkA2 : checkRange sqPt gA 147 33 = true := by
  decide +kernel
/-- Kernel check of the `tabA` chain for `k ∈ [180, 208]`. -/
theorem chunkA3 : checkRange sqPt gA 180 28 = true := by
  decide +kernel
/-- Kernel check of the `tabA` chain for `k ∈ [208, 232]`. -/
theorem chunkA4 : checkRange sqPt gA 208 24 = true := by
  decide +kernel
/-- Kernel check of the `tabA` chain for `k ∈ [232, 254]`. -/
theorem chunkA5 : checkRange sqPt gA 232 22 = true := by
  decide +kernel
/-- Kernel check of the `tabA` chain for `k ∈ [254, 274]`. -/
theorem chunkA6 : checkRange sqPt gA 254 20 = true := by
  decide +kernel
/-- Kernel check of the `tabA` chain for `k ∈ [274, 293]`. -/
theorem chunkA7 : checkRange sqPt gA 274 19 = true := by
  decide +kernel
/-- Kernel check of the `tabA` chain for `k ∈ [293, 311]`. -/
theorem chunkA8 : checkRange sqPt gA 293 18 = true := by
  decide +kernel
/-- Kernel check of the `tabA` chain for `k ∈ [311, 328]`. -/
theorem chunkA9 : checkRange sqPt gA 311 17 = true := by
  decide +kernel
/-- Kernel check of the `tabA` chain for `k ∈ [328, 344]`. -/
theorem chunkA10 : checkRange sqPt gA 328 16 = true := by
  decide +kernel
/-- Kernel check of the `tabA` chain for `k ∈ [344, 359]`. -/
theorem chunkA11 : checkRange sqPt gA 344 15 = true := by
  decide +kernel
/-- Kernel check of the `tabA` chain for `k ∈ [359, 374]`. -/
theorem chunkA12 : checkRange sqPt gA 359 15 = true := by
  decide +kernel
/-- Kernel check of the `tabA` chain for `k ∈ [374, 388]`. -/
theorem chunkA13 : checkRange sqPt gA 374 14 = true := by
  decide +kernel
/-- Kernel check of the `tabA` chain for `k ∈ [388, 401]`. -/
theorem chunkA14 : checkRange sqPt gA 388 13 = true := by
  decide +kernel
/-- Kernel check of the `tabA` chain for `k ∈ [401, 410]`. -/
theorem chunkA15 : checkRange sqPt gA 401 9 = true := by
  decide +kernel

/-- The full chain for `tabA`, assembled from the chunks. -/
theorem chainA : checkRange sqPt gA 0 410 = true := by
  have h1 := checkRange_add sqPt gA 104 43 0 chunkA0 chunkA1
  have h2 := checkRange_add sqPt gA _ 33 0 h1 chunkA2
  have h3 := checkRange_add sqPt gA _ 28 0 h2 chunkA3
  have h4 := checkRange_add sqPt gA _ 24 0 h3 chunkA4
  have h5 := checkRange_add sqPt gA _ 22 0 h4 chunkA5
  have h6 := checkRange_add sqPt gA _ 20 0 h5 chunkA6
  have h7 := checkRange_add sqPt gA _ 19 0 h6 chunkA7
  have h8 := checkRange_add sqPt gA _ 18 0 h7 chunkA8
  have h9 := checkRange_add sqPt gA _ 17 0 h8 chunkA9
  have h10 := checkRange_add sqPt gA _ 16 0 h9 chunkA10
  have h11 := checkRange_add sqPt gA _ 15 0 h10 chunkA11
  have h12 := checkRange_add sqPt gA _ 15 0 h11 chunkA12
  have h13 := checkRange_add sqPt gA _ 14 0 h12 chunkA13
  have h14 := checkRange_add sqPt gA _ 13 0 h13 chunkA14
  have h15 := checkRange_add sqPt gA _ 9 0 h14 chunkA15
  exact h15

/-- Kernel check of the `tabB` chain for `m ∈ [0, 148]`. -/
theorem chunkB0 : checkRange halfPt gB 0 148 = true := by
  decide +kernel
/-- Kernel check of the `tabB` chain for `m ∈ [148, 209]`. -/
theorem chunkB1 : checkRange halfPt gB 148 61 = true := by
  decide +kernel
/-- Kernel check of the `tabB` chain for `m ∈ [209, 256]`. -/
theorem chunkB2 : checkRange halfPt gB 209 47 = true := by
  decide +kernel
/-- Kernel check of the `tabB` chain for `m ∈ [256, 295]`. -/
theorem chunkB3 : checkRange halfPt gB 256 39 = true := by
  decide +kernel
/-- Kernel check of the `tabB` chain for `m ∈ [295, 330]`. -/
theorem chunkB4 : checkRange halfPt gB 295 35 = true := by
  decide +kernel
/-- Kernel check of the `tabB` chain for `m ∈ [330, 361]`. -/
theorem chunkB5 : checkRange halfPt gB 330 31 = true := by
  decide +kernel
/-- Kernel check of the `tabB` chain for `m ∈ [361, 390]`. -/
theorem chunkB6 : checkRange halfPt gB 361 29 = true := by
  decide +kernel
/-- Kernel check of the `tabB` chain for `m ∈ [390, 417]`. -/
theorem chunkB7 : checkRange halfPt gB 390 27 = true := by
  decide +kernel
/-- Kernel check of the `tabB` chain for `m ∈ [417, 442]`. -/
theorem chunkB8 : checkRange halfPt gB 417 25 = true := by
  decide +kernel
/-- Kernel check of the `tabB` chain for `m ∈ [442, 466]`. -/
theorem chunkB9 : checkRange halfPt gB 442 24 = true := by
  decide +kernel
/-- Kernel check of the `tabB` chain for `m ∈ [466, 489]`. -/
theorem chunkB10 : checkRange halfPt gB 466 23 = true := by
  decide +kernel
/-- Kernel check of the `tabB` chain for `m ∈ [489, 511]`. -/
theorem chunkB11 : checkRange halfPt gB 489 22 = true := by
  decide +kernel
/-- Kernel check of the `tabB` chain for `m ∈ [511, 532]`. -/
theorem chunkB12 : checkRange halfPt gB 511 21 = true := by
  decide +kernel
/-- Kernel check of the `tabB` chain for `m ∈ [532, 552]`. -/
theorem chunkB13 : checkRange halfPt gB 532 20 = true := by
  decide +kernel
/-- Kernel check of the `tabB` chain for `m ∈ [552, 571]`. -/
theorem chunkB14 : checkRange halfPt gB 552 19 = true := by
  decide +kernel
/-- Kernel check of the `tabB` chain for `m ∈ [571, 579]`. -/
theorem chunkB15 : checkRange halfPt gB 571 8 = true := by
  decide +kernel

/-- The full chain for `tabB`, assembled from the chunks. -/
theorem chainB : checkRange halfPt gB 0 579 = true := by
  have h1 := checkRange_add halfPt gB 148 61 0 chunkB0 chunkB1
  have h2 := checkRange_add halfPt gB _ 47 0 h1 chunkB2
  have h3 := checkRange_add halfPt gB _ 39 0 h2 chunkB3
  have h4 := checkRange_add halfPt gB _ 35 0 h3 chunkB4
  have h5 := checkRange_add halfPt gB _ 31 0 h4 chunkB5
  have h6 := checkRange_add halfPt gB _ 29 0 h5 chunkB6
  have h7 := checkRange_add halfPt gB _ 27 0 h6 chunkB7
  have h8 := checkRange_add halfPt gB _ 25 0 h7 chunkB8
  have h9 := checkRange_add halfPt gB _ 24 0 h8 chunkB9
  have h10 := checkRange_add halfPt gB _ 23 0 h9 chunkB10
  have h11 := checkRange_add halfPt gB _ 22 0 h10 chunkB11
  have h12 := checkRange_add halfPt gB _ 21 0 h11 chunkB12
  have h13 := checkRange_add halfPt gB _ 20 0 h12 chunkB13
  have h14 := checkRange_add halfPt gB _ 19 0 h13 chunkB14
  have h15 := checkRange_add halfPt gB _ 8 0 h14 chunkB15
  exact h15

/-- `π(k^2) = tabA[k]` for `k ≤ 410`. -/
theorem primeCounting_sq (k : ℕ) (hk : k ≤ 410) : Nat.primeCounting (k ^ 2) = gA k := by
  have h := checkRange_sound sqPt gA 410 0 chainA (by decide) k hk
  rw [zero_add] at h
  exact h

/-- `π(⌊m^2/2⌋) = tabB[m]` for `m ≤ 579`. -/
theorem primeCounting_half (m : ℕ) (hm : m ≤ 579) : Nat.primeCounting (m ^ 2 / 2) = gB m := by
  have h := checkRange_sound halfPt gB 579 0 chainB (by decide) m hm
  rw [zero_add] at h
  exact h

/-! ## Ground truth -/

/-- `a(n)` computed from the tables, for `K ≤ 410`, `M ≤ 579`. -/
def aTab (n K M : ℕ) : ℕ :=
  ((Finset.Ioo 0 K ×ˢ Finset.Ioo 0 M).filter fun p => n = gA p.1 + gB p.2).card

/-- Under table-checkable bounds, `a(n) = aTab n K M`. -/
theorem a_eq_aTab (n K M : ℕ) (hK : K ≤ 410) (hM : M ≤ 579) (hnK : n < gA K)
    (hnM : n < gB M) : a n = aTab n K M := by
  rw [a_eq_card n K M (by rwa [primeCounting_sq K hK]) (by rwa [primeCounting_half M hM]),
    aTab]
  congr 1
  apply Finset.filter_congr
  intro p hp
  rw [Finset.mem_product, Finset.mem_Ioo, Finset.mem_Ioo] at hp
  rw [primeCounting_sq p.1 (by omega), primeCounting_half p.2 (by omega)]

/-- The first twenty-eight listed terms `a(1), …, a(28)`; in particular
`a(1) = a(3) = a(28) = 1`. -/
theorem a_ground_truth : ∀ n ∈ List.range' 1 28,
    a n = [1, 2, 1, 3, 2, 3, 3, 2, 4, 2, 6, 2, 5, 2, 5, 4, 4, 4, 4, 5, 3, 5, 5, 4, 4, 6, 6,
      1].getD (n - 1) 0 := by
  intro n hn
  have hn28 : n < 29 := by
    rw [List.mem_range'] at hn
    omega
  have hgA : gA 11 = 30 := by decide +kernel
  have hgB : gB 15 = 29 := by decide +kernel
  rw [a_eq_aTab n 11 15 (by norm_num) (by norm_num) (by omega) (by omega)]
  revert n
  decide +kernel

/-! ## The counterexample `n = 15293` -/

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

/-- For every `k ≤ 410` other than `339`, either `π(k^2) > 15293` or
`15293 - π(k^2)` is not a value of `π(⌊m^2/2⌋)`, `m ≤ 579`. -/
def kCheck : Bool :=
  tabA.zipIdx.all fun x => x.2 == 339 || 15293 < x.1 || !((orMask tabB).testBit (15293 - x.1))

/-- The only `m ≤ 579` with `π(⌊m^2/2⌋) = 4426` is `m = 291`. -/
def mCheck : Bool := tabB.zipIdx.all fun x => x.1 != 4426 || x.2 == 291

/-- Kernel check of `kCheck`. -/
theorem kCheck_eq : kCheck = true := by decide +kernel

/-- Kernel check of `mCheck`. -/
theorem mCheck_eq : mCheck = true := by decide +kernel

/-- The pairs counted by `a(15293)`: exactly `(339, 291)`. -/
theorem mem_pairSet_15293 (k m : ℕ) : (k, m) ∈ pairSet 15293 ↔ k = 339 ∧ m = 291 := by
  have hA410 : gA 410 = 15346 := by decide +kernel
  have hB579 : gB 579 = 15308 := by decide +kernel
  have hA339 : gA 339 = 10867 := by decide +kernel
  have hB291 : gB 291 = 4426 := by decide +kernel
  have hlenA : tabA.length = 411 := by decide +kernel
  have hlenB : tabB.length = 580 := by decide +kernel
  constructor
  · rintro ⟨hk, hm, heq⟩
    simp only at hk hm heq
    have hk409 : k ≤ 409 := by
      by_contra hbig
      have hmono : Nat.primeCounting (410 ^ 2) ≤ Nat.primeCounting (k ^ 2) :=
        Nat.monotone_primeCounting (Nat.pow_le_pow_left (by omega) 2)
      rw [primeCounting_sq 410 le_rfl, hA410] at hmono
      omega
    have hm578 : m ≤ 578 := by
      by_contra hbig
      have hmono : Nat.primeCounting (579 ^ 2 / 2) ≤ Nat.primeCounting (m ^ 2 / 2) :=
        Nat.monotone_primeCounting (Nat.div_le_div_right (Nat.pow_le_pow_left (by omega) 2))
      rw [primeCounting_half 579 le_rfl, hB579] at hmono
      omega
    rw [primeCounting_sq k (by omega), primeCounting_half m (by omega)] at heq
    have hkA : k < tabA.length := by omega
    have hmB : m < tabB.length := by omega
    have hgA : gA k = tabA[k] := List.getD_eq_getElem _ _ hkA
    have hgB : gB m = tabB[m] := List.getD_eq_getElem _ _ hmB
    have hkc := kCheck_eq
    rw [kCheck, List.all_eq_true, List.forall_mem_zipIdx] at hkc
    have hkk := hkc k hkA
    simp only [zero_add, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true']
      at hkk
    have hk339 : k = 339 := by
      rcases hkk with (hk339 | hgt) | hbit
      · exact hk339
      · omega
      · have hmem : 15293 - tabA[k] ∈ tabB := by
          rw [show 15293 - tabA[k] = tabB[m] by omega]
          exact List.getElem_mem hmB
        rw [← testBit_orMask] at hmem
        rw [hmem] at hbit
        exact absurd hbit (by decide)
    subst hk339
    refine ⟨rfl, ?_⟩
    have hmc := mCheck_eq
    rw [mCheck, List.all_eq_true, List.forall_mem_zipIdx] at hmc
    have hmm := hmc m hmB
    simp only [zero_add, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hmm
    rcases hmm with hne | hm291
    · exact absurd (by omega) hne
    · exact hm291
  · rintro ⟨rfl, rfl⟩
    refine ⟨by norm_num, by norm_num, ?_⟩
    rw [primeCounting_sq 339 (by norm_num), primeCounting_half 291 (by norm_num), hA339, hB291]

/-- `a(15293) = 1`. -/
theorem a_15293 : a 15293 = 1 := by
  have hset : pairSet 15293 = {(339, 291)} := by
    ext ⟨k, m⟩
    rw [mem_pairSet_15293, Set.mem_singleton_iff, Prod.mk.injEq]
  rw [a, hset, Set.ncard_singleton]

/-- **Part (i) of Sun's global conjecture is false.**  Counterexample
`n = 15293`: the only pair is `(k, m) = (339, 291)`, with
`π(339^2) = 10867` and `π(⌊291^2/2⌋) = 4426`, so `a(15293) = 1` although
`15293 ∉ {1, 3, 28}`.  The primary OEIS entry states this as a global
conjecture; it is not restricted to the displayed finite data.  Further
exceptions found by computation are
`72102` (and, per the triage, `448785` and `994007`). -/
theorem conjecture_false : ¬ Conjecture := by
  rintro ⟨_, honly⟩
  have h := honly 15293 (by norm_num) a_15293
  omega

end Candidates.A263100Refutation
