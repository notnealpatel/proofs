/-
# A209332 — refutation of "for even n, a(n) > 0"

Vladimir Shevelev's conjecture in OEIS A209332 says that for positive even
`n` some `n<+>k` with `k ≥ 1` is prime. Here `a<+>b` (A206853) is the least
`c ≥ a` at binary Hamming distance `b` from `a`. The even number
`108292506` is a counterexample.

* For `k ≥ 28` we have `n < 2^(k-1)`, hence `n<+>k = 2^k - 1 - n`
  (`hamOp_eq_two_pow_sub`). With `m = n + 1 = 108292507`, every
  `2^k - m` is divisible by one of `3, 5, 7, 13, 17, 241` according to
  `k mod 24` (Erdős-type covering system); the quotient is greater than `1`.
* For `1 ≤ k ≤ 27` the value `n<+>k` is certified by a dyadic-block
  minimality check (`noHit`, proved sound in `noHit_sound`) and shown
  composite with an explicit proper factor (`smallTable`).
-/
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Nat.Bitwise

set_option autoImplicit false

namespace Candidates.A209332Refutation

/-! ## Definitions mirroring A206853 and A209332 -/

/-- The number of `1` digits in the binary expansion of `n`. -/
def popcount (n : ℕ) : ℕ := (Nat.digits 2 n).sum

/-- The Hamming distance `D(a, c)` of the binary expansions of `a` and `c`:
the number of `1` bits of `a XOR c`. -/
def hammingD (a c : ℕ) : ℕ := popcount (a ^^^ c)

/-- `popcount 0 = 0`. -/
theorem popcount_zero : popcount 0 = 0 := by simp [popcount]

/-- The binary recursion for `popcount`. -/
theorem popcount_eq (n : ℕ) : popcount n = n % 2 + popcount (n / 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [popcount]
  · rw [popcount, Nat.digits_def' (by norm_num) hn, List.sum_cons, popcount]

/-- `popcount` splits additively over the low `j` bits and the high bits. -/
theorem popcount_split (j n : ℕ) :
    popcount n = popcount (n % 2 ^ j) + popcount (n / 2 ^ j) := by
  induction j generalizing n with
  | zero => simp [Nat.mod_one, popcount_zero]
  | succ j ih =>
    have h1 : n % 2 ^ (j + 1) % 2 = n % 2 := by
      rw [pow_succ', Nat.mod_mul_right_mod]
    have h2 : n % 2 ^ (j + 1) / 2 = n / 2 % 2 ^ j := by
      rw [pow_succ', Nat.mod_mul_right_div_self]
    have h3 : n / 2 ^ (j + 1) = n / 2 / 2 ^ j := by
      rw [pow_succ', Nat.div_div_eq_div_mul]
    rw [popcount_eq n, ih (n / 2), popcount_eq (n % 2 ^ (j + 1)), h1, h2, h3]
    ring

/-- A number below `2^j` has at most `j` one bits. -/
theorem popcount_le_of_lt (j x : ℕ) (hx : x < 2 ^ j) : popcount x ≤ j := by
  induction j generalizing x with
  | zero =>
    have hx0 : x = 0 := by simpa using hx
    simp [hx0, popcount_zero]
  | succ j ih =>
    have hlt : x / 2 < 2 ^ j := by
      rw [pow_succ] at hx; omega
    rw [popcount_eq]
    have hrec := ih (x / 2) hlt
    omega

/-- A number with at least `k` one bits is at least `2^k - 1`. -/
theorem two_pow_le_of_le_popcount (x k : ℕ) (h : k ≤ popcount x) : 2 ^ k ≤ x + 1 := by
  induction x using Nat.strong_induction_on generalizing k with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · rw [popcount_zero] at h
      have hk : k = 0 := by omega
      simp [hk]
    · cases k with
      | zero => simp
      | succ k =>
        rw [popcount_eq] at h
        have hlt : x / 2 < x := Nat.div_lt_self hx (by norm_num)
        rcases Nat.mod_two_eq_zero_or_one x with h0 | h1
        · have hrec := ih (x / 2) hlt (k + 1) (by omega)
          rw [pow_succ]
          have hmono : 2 ^ k ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        · have hrec := ih (x / 2) hlt k (by omega)
          rw [pow_succ]
          omega

/-- Bitwise XOR never exceeds the sum. -/
theorem xor_le_add (a b : ℕ) : a ^^^ b ≤ a + b := by
  induction a using Nat.strong_induction_on generalizing b with
  | _ a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · have hsplit := Nat.mod_add_div (a ^^^ b) 2
      rw [Nat.xor_div_two, Nat.xor_mod_two_eq] at hsplit
      have hrec := ih (a / 2) (Nat.div_lt_self ha (by norm_num)) (b / 2)
      omega

/-- XOR with the all-ones word `2^k - 1` is the complement: `(x XOR (2^k-1)) + x = 2^k - 1`
for `x < 2^k`. -/
theorem xor_all_ones (k x : ℕ) (hx : x < 2 ^ k) : (x ^^^ (2 ^ k - 1)) + x = 2 ^ k - 1 := by
  induction k generalizing x with
  | zero =>
    have hx0 : x = 0 := by simpa using hx
    simp [hx0]
  | succ k ih =>
    have hP : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hsplit := Nat.mod_add_div (x ^^^ (2 ^ (k + 1) - 1)) 2
    have hdiv : (2 ^ (k + 1) - 1) / 2 = 2 ^ k - 1 := by rw [pow_succ]; omega
    rw [Nat.xor_div_two, Nat.xor_mod_two_eq, hdiv] at hsplit
    have hlt : x / 2 < 2 ^ k := by rw [pow_succ] at hx; omega
    have hrec := ih (x / 2) hlt
    rw [pow_succ] at hsplit ⊢
    omega

/-- The all-ones word `2^k - 1` has exactly `k` one bits. -/
theorem popcount_two_pow_sub_one (k : ℕ) : popcount (2 ^ k - 1) = k := by
  induction k with
  | zero => simp [popcount_zero]
  | succ k ih =>
    have hP : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [popcount_eq]
    have h1 : (2 ^ (k + 1) - 1) % 2 = 1 := by rw [pow_succ]; omega
    have h2 : (2 ^ (k + 1) - 1) / 2 = 2 ^ k - 1 := by rw [pow_succ]; omega
    rw [h1, h2, ih]; omega

/-- XOR cancellation `a XOR (a XOR b) = b`. -/
theorem xor_xor_cancel (a b : ℕ) : a ^^^ (a ^^^ b) = b := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

/-- Shifting left does not change `popcount`. -/
theorem popcount_mul_two_pow (y s : ℕ) : popcount (y * 2 ^ s) = popcount y := by
  have hpos : 0 < 2 ^ s := Nat.two_pow_pos s
  rw [popcount_split s, Nat.mul_mod_left, Nat.mul_div_cancel _ hpos, popcount_zero, zero_add]

/-- For all `a, b` some `c ≥ a` has `D(a, c) = b` (flip `b` bits above the top bit of `a`),
so `a<+>b` is well defined. -/
theorem exists_hamOp (a b : ℕ) : ∃ c, a ≤ c ∧ hammingD a c = b := by
  refine ⟨a ^^^ ((2 ^ b - 1) * 2 ^ a), ?_, ?_⟩
  · have hmod : (a ^^^ ((2 ^ b - 1) * 2 ^ a)) % 2 ^ a = a := by
      rw [Nat.xor_mod_two_pow, Nat.mul_mod_left, Nat.xor_zero,
        Nat.mod_eq_of_lt Nat.lt_two_pow_self]
    calc a = (a ^^^ ((2 ^ b - 1) * 2 ^ a)) % 2 ^ a := hmod.symm
      _ ≤ a ^^^ ((2 ^ b - 1) * 2 ^ a) := Nat.mod_le _ _
  · rw [hammingD, xor_xor_cancel, popcount_mul_two_pow, popcount_two_pow_sub_one]

/-- The operation `a<+>b` of A206853: the least `c ≥ a` with Hamming distance `D(a, c) = b`. -/
noncomputable def hamOp (a b : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_hamOp a b)

/-- **A209332**: `a(n)` is the least `k > 0` with `n<+>k` prime, or `0` if there is none. -/
noncomputable def A209332 (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ k, 0 < k ∧ (hamOp n k).Prime then Nat.find h else 0

/-- **Shevelev's conjecture (A209332).** "Conjecture: for even n,
a(n) > 0." The sequence has offset 1, so `n` ranges over positive even integers. -/
def EvenPositiveConjecture : Prop :=
  ∀ n : ℕ, 0 < n → Even n → 0 < A209332 n

/-! ## Basic API for `<+>` and `a(n)` -/

/-- `a<+>b` satisfies its defining property. -/
theorem hamOp_spec (a b : ℕ) : a ≤ hamOp a b ∧ hammingD a (hamOp a b) = b := by
  classical
  exact Nat.find_spec (exists_hamOp a b)

/-- `a<+>b` is below every admissible `c`. -/
theorem hamOp_le (a b c : ℕ) (hc : a ≤ c) (hD : hammingD a c = b) : hamOp a b ≤ c := by
  classical
  exact Nat.find_min' (exists_hamOp a b) ⟨hc, hD⟩

/-- Characterisation of `a<+>b` as the least admissible value. -/
theorem hamOp_eq_of (a b c : ℕ) (hc : a ≤ c) (hD : hammingD a c = b)
    (hmin : ∀ d, a ≤ d → d < c → hammingD a d ≠ b) : hamOp a b = c := by
  refine le_antisymm (hamOp_le a b c hc hD) ?_
  by_contra hle
  have hlt : hamOp a b < c := not_le.mp hle
  obtain ⟨h1, h2⟩ := hamOp_spec a b
  exact hmin _ h1 hlt h2

/-- `a(n) > 0` exactly when some `n<+>k` with `k > 0` is prime. -/
theorem A209332_pos_iff (n : ℕ) : 0 < A209332 n ↔ ∃ k, 0 < k ∧ (hamOp n k).Prime := by
  classical
  unfold A209332
  constructor
  · intro hpos
    by_contra hnone
    rw [dif_neg hnone] at hpos
    exact lt_irrefl 0 hpos
  · intro hex
    rw [dif_pos hex]
    exact (Nat.find_spec hex).1

/-- Evaluation of `a(n)` from a positive witness and the failure of all smaller `k`. -/
theorem A209332_eq_of (n v : ℕ) (hv : 0 < v) (hp : (hamOp n v).Prime)
    (hlt : ∀ k, 0 < k → k < v → ¬ (hamOp n k).Prime) : A209332 n = v := by
  classical
  have hex : ∃ k, 0 < k ∧ (hamOp n k).Prime := ⟨v, hv, hp⟩
  unfold A209332
  rw [dif_pos hex]
  refine le_antisymm (Nat.find_min' hex ⟨hv, hp⟩) ?_
  by_contra hle
  have hfind := Nat.find_spec hex
  exact hlt _ hfind.1 (not_le.mp hle) hfind.2

/-! ## The value of `n<+>k` once `n < 2^(k-1)` -/

/-- If `2n < 2^k` (i.e. `n < 2^(k-1)`), then `n<+>k = 2^k - 1 - n`: the complement of `n`
in `k` bits is admissible, and any admissible `c` has `c + n ≥ c XOR n ≥ 2^k - 1`. -/
theorem hamOp_eq_two_pow_sub (n k : ℕ) (h : 2 * n < 2 ^ k) : hamOp n k = 2 ^ k - 1 - n := by
  have hn : n < 2 ^ k := by omega
  have hc0 := xor_all_ones k n hn
  have hD0 : hammingD n (n ^^^ (2 ^ k - 1)) = k := by
    rw [hammingD, xor_xor_cancel, popcount_two_pow_sub_one]
  have hle : hamOp n k ≤ 2 ^ k - 1 - n :=
    (hamOp_le n k _ (by omega) hD0).trans (by omega)
  obtain ⟨_, hspec⟩ := hamOp_spec n k
  have hlow := two_pow_le_of_le_popcount (n ^^^ hamOp n k) k (by rw [← hammingD, hspec])
  have hxor := xor_le_add n (hamOp n k)
  omega

/-! ## A sound dyadic-block certificate for minimality -/

/-- Within the dyadic block `d / 2^j = q`, the distance `D(n, d)` lies between the high-part
distance `P = popcount (n / 2^j XOR q)` and `P + j`. -/
theorem hammingD_block (n d j : ℕ) :
    popcount (n / 2 ^ j ^^^ d / 2 ^ j) ≤ hammingD n d ∧
      hammingD n d ≤ popcount (n / 2 ^ j ^^^ d / 2 ^ j) + j := by
  have hsplit := popcount_split j (n ^^^ d)
  rw [Nat.xor_div_two_pow] at hsplit
  have hlow := popcount_le_of_lt j ((n ^^^ d) % 2 ^ j) (Nat.mod_lt _ (Nat.two_pow_pos j))
  rw [hammingD]
  omega

/-- A fuel-bounded `popcount`, reducible by the kernel. -/
def pcF : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, x => x % 2 + pcF f (x / 2)

/-- `pcF f` computes `popcount` below `2^f`. -/
theorem pcF_eq (f x : ℕ) (hx : x < 2 ^ f) : pcF f x = popcount x := by
  induction f generalizing x with
  | zero =>
    have hx0 : x = 0 := by simpa using hx
    simp [pcF, hx0, popcount_zero]
  | succ f ih =>
    have hlt : x / 2 < 2 ^ f := by rw [pow_succ] at hx; omega
    rw [pcF, ih (x / 2) hlt, ← popcount_eq]

/-- `noHit n k lo hi j q` checks that no `d ∈ [lo, hi)` in the dyadic block `d / 2^j = q`
has `D(n, d) = k`: the block is disjoint from the window, or `k` lies outside the block's
distance range `[P, P + j]`, or both halves pass recursively. -/
def noHit (n k lo hi : ℕ) : ℕ → ℕ → Bool
  | 0, q => decide (hi ≤ q) || decide (q + 1 ≤ lo) ||
      (decide (n ^^^ q < 2 ^ 64) && decide (pcF 64 (n ^^^ q) ≠ k))
  | j + 1, q => decide (hi ≤ q * 2 ^ (j + 1)) || decide ((q + 1) * 2 ^ (j + 1) ≤ lo) ||
      (decide (n / 2 ^ (j + 1) ^^^ q < 2 ^ 64) &&
        (decide (k < pcF 64 (n / 2 ^ (j + 1) ^^^ q)) ||
          decide (pcF 64 (n / 2 ^ (j + 1) ^^^ q) + (j + 1) < k))) ||
      (noHit n k lo hi j (2 * q) && noHit n k lo hi j (2 * q + 1))

/-- Soundness of `noHit`. -/
theorem noHit_sound (n k lo hi j q : ℕ) (h : noHit n k lo hi j q = true) :
    ∀ d, lo ≤ d → d < hi → d / 2 ^ j = q → hammingD n d ≠ k := by
  induction j generalizing q with
  | zero =>
    intro d hlo hhi hq
    simp only [pow_zero, Nat.div_one] at hq
    subst hq
    simp only [noHit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with (h | h) | ⟨hlt, hne⟩
    · omega
    · omega
    · rw [hammingD, ← pcF_eq 64 _ hlt]
      exact hne
  | succ j ih =>
    intro d hlo hhi hq
    have hpos : 0 < 2 ^ (j + 1) := Nat.two_pow_pos _
    have hq1 : q * 2 ^ (j + 1) ≤ d := by
      rw [← hq]; exact Nat.div_mul_le_self d _
    have hq2 : d < (q + 1) * 2 ^ (j + 1) := (Nat.div_lt_iff_lt_mul hpos).mp (by omega)
    simp only [noHit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ((h | h) | ⟨hlt, hP⟩) | ⟨h0, h1⟩
    · omega
    · omega
    · have hblock := hammingD_block n d (j + 1)
      rw [hq, ← pcF_eq 64 _ hlt] at hblock
      omega
    · have hdiv : d / 2 ^ j / 2 = q := by
        rw [Nat.div_div_eq_div_mul, ← pow_succ]; exact hq
      have hcases : d / 2 ^ j = 2 * q ∨ d / 2 ^ j = 2 * q + 1 := by omega
      rcases hcases with hc | hc
      · exact ih (2 * q) h0 d hlo hhi hc
      · exact ih (2 * q + 1) h1 d hlo hhi hc

/-- Evaluation of `n<+>k = c` from a checked `noHit` certificate. -/
theorem hamOp_eq_of_noHit (n k c J : ℕ) (hnc : n ≤ c) (hlt : n ^^^ c < 2 ^ 64)
    (hD : pcF 64 (n ^^^ c) = k) (hJ : c ≤ 2 ^ J) (hchk : noHit n k n c J 0 = true) :
    hamOp n k = c := by
  refine hamOp_eq_of n k c hnc (by rw [hammingD, ← pcF_eq 64 _ hlt, hD]) ?_
  intro d hd hdc
  refine noHit_sound n k n c J 0 hchk d hd hdc ?_
  exact Nat.div_eq_of_lt (by omega)

/-! ## Examples -/

-- A206853 (iterating `<+>2` from 1): 1, 2, 4, 7, 11, 13, 14, 22, ..., 31, 47.
example : hamOp 1 2 = 2 :=
  hamOp_eq_of_noHit 1 2 2 2 (by decide) (by decide) (by decide) (by decide) (by decide)
example : hamOp 4 2 = 7 :=
  hamOp_eq_of_noHit 4 2 7 3 (by decide) (by decide) (by decide) (by decide) (by decide)
example : hamOp 14 2 = 22 :=
  hamOp_eq_of_noHit 14 2 22 5 (by decide) (by decide) (by decide) (by decide) (by decide)
example : hamOp 31 2 = 47 :=
  hamOp_eq_of_noHit 31 2 47 6 (by decide) (by decide) (by decide) (by decide) (by decide)

-- A209332 data (offset 1): a(1) = 1 since 1<+>1 = 3; a(7) = 2 since 7<+>1 = 15 and 7<+>2 = 11.
example : A209332 1 = 1 := by
  refine A209332_eq_of 1 1 (by norm_num) ?_ (fun k hk hk1 => by omega)
  rw [hamOp_eq_of_noHit 1 1 3 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  norm_num

example : A209332 7 = 2 := by
  refine A209332_eq_of 7 2 (by norm_num) ?_ ?_
  · rw [hamOp_eq_of_noHit 7 2 11 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
    norm_num
  · intro k hk hk2
    obtain rfl : k = 1 := by omega
    rw [hamOp_eq_of_noHit 7 1 15 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
    norm_num

-- Non-vacuity of the conjecture's hypothesis: `n = 2` is positive, even, with `a(2) > 0`.
example : 0 < 2 ∧ Even 2 ∧ 0 < A209332 2 := by
  refine ⟨by norm_num, even_two, (A209332_pos_iff 2).mpr ⟨1, by norm_num, ?_⟩⟩
  rw [hamOp_eq_of_noHit 2 1 3 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  norm_num

/-! ## The counterexample `n = 108292506` -/

/-- The covering primes: each divides `2^24 - 1`. -/
def coverPrimes : List ℕ := [3, 5, 7, 13, 17, 241]

/-- Covering system for `m = 108292507`: for every residue `r` of `k` modulo `24` some covering
prime `p` has `2^r ≡ m (mod p)`. -/
theorem cover_residues :
    ∀ r < 24, ∃ p ∈ coverPrimes, 2 ^ r % p = 108292507 % p := by
  decide

/-- Every covering prime has `2^24 ≡ 1`, and lies in `[3, 241]`. -/
theorem coverPrimes_spec : ∀ p ∈ coverPrimes, 2 ^ 24 % p = 1 ∧ 3 ≤ p ∧ p ≤ 241 := by
  decide

/-- For `k ≥ 28`, `2^k - 108292507` is composite. -/
theorem not_prime_large (k : ℕ) (hk : 28 ≤ k) : ¬ (2 ^ k - 108292507).Prime := by
  obtain ⟨p, hp, hres⟩ := cover_residues (k % 24) (Nat.mod_lt _ (by norm_num))
  obtain ⟨hp24, hp3, hp241⟩ := coverPrimes_spec p hp
  have hpow : 2 ^ k % p = 2 ^ (k % 24) % p := by
    conv_lhs => rw [← Nat.div_add_mod k 24, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod, hp24, one_pow, Nat.one_mod_eq_one.mpr (by omega), one_mul,
      Nat.mod_mod]
  have hbig : 2 ^ 28 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hdvd : p ∣ 2 ^ k - 108292507 :=
    Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq (hpow.trans hres))
  intro hprime
  rcases hprime.eq_one_or_self_of_dvd p hdvd with h1 | hself
  · omega
  · have h28 : (2 : ℕ) ^ 28 = 268435456 := by norm_num
    omega

/-- Certificate rows `(k, c, p)` for `1 ≤ k ≤ 27`: `108292506<+>k = c`, and `p` is a proper
factor of `c`. -/
def smallTable : List (ℕ × ℕ × ℕ) :=
  [(1, 108292507, 61), (2, 108292508, 2), (3, 108292509, 3), (4, 108292512, 2),
   (5, 108292513, 7), (6, 108292517, 31), (7, 108292581, 3), (8, 108292613, 11),
   (9, 108292645, 5), (10, 108292709, 7), (11, 108293733, 3), (12, 108294757, 829),
   (13, 108295781, 11), (14, 108298853, 13), (15, 108299877, 3), (16, 108303973, 269),
   (17, 108369509, 17), (18, 108500581, 7), (19, 108631653, 3), (20, 108762725, 5),
   (21, 109090405, 5), (22, 109155941, 449), (23, 109287013, 11), (24, 109811301, 3),
   (25, 126588517, 11), (26, 134977125, 3), (27, 143365733, 7)]

/-- The check performed on each certificate row. -/
def rowOK (row : ℕ × ℕ × ℕ) : Bool :=
  decide (108292506 ≤ row.2.1) && decide (108292506 ^^^ row.2.1 < 2 ^ 64) &&
    decide (pcF 64 (108292506 ^^^ row.2.1) = row.1) && decide (row.2.1 ≤ 2 ^ 28) &&
    noHit 108292506 row.1 108292506 row.2.1 28 0 &&
    decide (row.2.1 % row.2.2 = 0) && decide (1 < row.2.2) && decide (row.2.2 < row.2.1)

/-- All certificate rows pass. -/
theorem smallTable_ok : ∀ row ∈ smallTable, rowOK row = true := by
  decide +kernel

/-- The certificate rows cover `k = 1, …, 27`. -/
theorem smallTable_covers : ∀ k < 28, 0 < k → ∃ row ∈ smallTable, row.1 = k := by
  decide

/-- For `1 ≤ k ≤ 27`, `108292506<+>k` is composite. -/
theorem not_prime_small (k : ℕ) (hk0 : 0 < k) (hk : k < 28) :
    ¬ (hamOp 108292506 k).Prime := by
  obtain ⟨⟨k', c, p⟩, hrow, hk'⟩ := smallTable_covers k hk hk0
  have hok := smallTable_ok _ hrow
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hnc, hlt⟩, hD⟩, hJ⟩, hchk⟩, hmod⟩, hp1⟩, hpc⟩ := hok
  simp only at hk' hnc hlt hD hJ hchk hmod hp1 hpc
  subst hk'
  rw [hamOp_eq_of_noHit 108292506 k' c 28 hnc hlt hD hJ hchk]
  intro hprime
  rcases hprime.eq_one_or_self_of_dvd p (Nat.dvd_of_mod_eq_zero hmod) with h1 | hself
  · omega
  · omega

/-- For every `k ≥ 1`, `108292506<+>k` is composite. -/
theorem not_prime_hamOp (k : ℕ) (hk : 0 < k) : ¬ (hamOp 108292506 k).Prime := by
  by_cases hk28 : 28 ≤ k
  · have hbig : 2 ^ 28 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk28
    have h28 : (2 : ℕ) ^ 28 = 268435456 := by norm_num
    rw [hamOp_eq_two_pow_sub 108292506 k (by omega)]
    have hrw : 2 ^ k - 1 - 108292506 = 2 ^ k - 108292507 := by omega
    rw [hrw]
    exact not_prime_large k hk28
  · exact not_prime_small k hk (by omega)

/-- `a(108292506) = 0`. -/
theorem A209332_counterexample : A209332 108292506 = 0 := by
  by_contra hne
  obtain ⟨k, hk, hprime⟩ := (A209332_pos_iff 108292506).mp (Nat.pos_of_ne_zero hne)
  exact not_prime_hamOp k hk hprime

/-- **Shevelev's conjecture "for even n, a(n) > 0" (A209332) is false.** The even number
`n = 108292506` has `a(n) = 0`: `n<+>k` is composite for `1 ≤ k ≤ 27` (explicit factors), and
for `k ≥ 28` it equals `2^k - 108292507`, which the covering system with primes
`3, 5, 7, 13, 17, 241` (period 24) always divides properly. -/
theorem evenPositiveConjecture_false : ¬ EvenPositiveConjecture := by
  intro hconj
  have hpos := hconj 108292506 (by norm_num) ⟨54146253, by norm_num⟩
  rw [A209332_counterexample] at hpos
  exact lt_irrefl 0 hpos

end Candidates.A209332Refutation
