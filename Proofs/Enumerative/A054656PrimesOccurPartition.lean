/-
# Primes absent from distinct-prime partitions (A054656)

Source: the unsigned conjecture in OEIS A054656.
A partition into distinct primes is a finite set of primes with sum `n`.
For `n ≥ 23`, the absent primes at most `n` are precisely the primes among
`n-1`, `n-4`, `n-6`. This yields the entry's case split for their number.
A Richert window argument represents all sufficiently large differences
while avoiding a prescribed prime; the remaining differences have explicit witnesses.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A054656PrimesOccurPartition

open Finset

/-! ## Definitions -/

/-- The prime `q` occurs in some partition of `n` into distinct primes: there is
a finite set `S` of primes containing `q` with `∑ S = n`. -/
def OccursIn (n q : ℕ) : Prop :=
  ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ q ∈ S ∧ ∑ p ∈ S, p = n

/-- The primes `≤ n`, as a finset. -/
def primesLE (n : ℕ) : Finset ℕ := (range (n + 1)).filter Nat.Prime

/-- Decidable bounded form of `OccursIn`: the parts range over subsets of the
primes `≤ n`.  `occursInB_iff` proves it equivalent to `OccursIn`. -/
def OccursInB (n q : ℕ) : Prop :=
  ∃ S ∈ (primesLE n).powerset, q ∈ S ∧ ∑ p ∈ S, p = n

instance (n q : ℕ) : Decidable (OccursInB n q) := by
  unfold OccursInB; infer_instance

/-- **A054656.** `a n` is the number of primes `q ≤ n` that occur in no partition
of `n` into distinct primes. -/
def a (n : ℕ) : ℕ :=
  ((range (n + 1)).filter (fun q => q.Prime ∧ ¬ OccursInB n q)).card

/-- The bounded form agrees with the unbounded definition. -/
theorem occursInB_iff (n q : ℕ) : OccursInB n q ↔ OccursIn n q := by
  constructor
  · rintro ⟨S, hS, hqS, hsum⟩
    refine ⟨S, fun p hp => ?_, hqS, hsum⟩
    have hp' := mem_powerset.mp hS hp
    exact (mem_filter.mp hp').2
  · rintro ⟨S, hprime, hqS, hsum⟩
    refine ⟨S, mem_powerset.mpr fun p hp => ?_, hqS, hsum⟩
    have hle : p ≤ n := hsum ▸ single_le_sum (fun i _ => Nat.zero_le i) hp
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hle), hprime p hp⟩

set_option maxRecDepth 100000 in
/-- The first twenty-six terms of A054656 (offset 0). -/
example : (List.range 26).map a =
    [0, 0, 0, 1, 2, 0, 3, 1, 2, 2, 0, 4, 1, 3, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1] := by
  decide

/-! ## Sums of primes below `n` -/

/-- The sum of the primes `< n`. -/
def primeSumBelow (n : ℕ) : ℕ := ∑ p ∈ (range n).filter Nat.Prime, p

/-- Any finset of primes `< n` sums to at most `primeSumBelow n`. -/
theorem sum_le_primeSumBelow (L : Finset ℕ) (n : ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p < n) :
    ∑ p ∈ L, p ≤ primeSumBelow n :=
  sum_le_sum_of_subset fun p hp => mem_filter.mpr ⟨mem_range.mpr (hL p hp).2, (hL p hp).1⟩

/-- Checkpoint: a finset `L` of primes `< c` with `2d + 24 ≤ ∑ L` gives
`2n + 24 ≤ primeSumBelow n` for every `n ∈ [c, d]`. -/
theorem checkpoint (L : Finset ℕ) (c d n : ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p < c)
    (hs : 2 * d + 24 ≤ ∑ p ∈ L, p) (hcn : c ≤ n) (hnd : n ≤ d) :
    2 * n + 24 ≤ primeSumBelow n := by
  have h := sum_le_primeSumBelow L n fun p hp => ⟨(hL p hp).1, lt_of_lt_of_le (hL p hp).2 hcn⟩
  omega

/-- The prime-sum bound on `20 ≤ n ≤ 3001`, from six explicit checkpoints. -/
theorem primeSumBelow_ge_small (n : ℕ) (h20 : 20 ≤ n) (hn : n ≤ 3001) :
    2 * n + 24 ≤ primeSumBelow n := by
  rcases le_or_gt n 26 with h1 | h1
  · exact checkpoint {2, 3, 5, 7, 11, 13, 17, 19} 20 26 n (by decide) (by decide) h20 h1
  rcases le_or_gt n 37 with h2 | h2
  · exact checkpoint {3, 5, 7, 11, 13, 17, 19, 23} 27 37 n (by decide) (by decide) h1 h2
  rcases le_or_gt n 78 with h3 | h3
  · exact checkpoint {11, 13, 17, 19, 23, 29, 31, 37} 38 78 n (by decide) (by decide) h2 h3
  rcases le_or_gt n 225 with h4 | h4
  · exact checkpoint {43, 47, 53, 59, 61, 67, 71, 73} 79 225 n (by decide) (by decide) h3 h4
  rcases le_or_gt n 775 with h5 | h5
  · exact checkpoint {179, 181, 191, 193, 197, 199, 211, 223} 226 775 n
      (by
        intro p hp
        simp only [mem_insert, mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num)
      (by decide) h4 h5
  · exact checkpoint {733, 739, 743, 751, 757, 761, 769, 773} 776 3001 n
      (by
        intro p hp
        simp only [mem_insert, mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num)
      (by decide) h5 hn

/-- A finset of `c` distinct naturals has sum at least `c(c-1)/2`, stated without
subtraction as `c * c ≤ 2 * ∑ s + c`. -/
theorem card_mul_card_le_two_mul_sum (s : Finset ℕ) :
    s.card * s.card ≤ 2 * ∑ p ∈ s, p + s.card := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert x s hlt ih =>
    have hxs : x ∉ s := fun hx => lt_irrefl x (hlt x hx)
    have hcard : s.card ≤ x := by
      have hsub : s ⊆ range x := fun y hy => mem_range.mpr (hlt y hy)
      simpa using card_le_card hsub
    rw [card_insert_of_notMem hxs, sum_insert hxs]
    nlinarith

/-- Chebyshev's lower bound at powers of two: `2^k ≤ k π(2^k) + k + 1`. -/
theorem two_pow_le_primeCounting (k : ℕ) (hk : 1 ≤ k) :
    2 ^ k ≤ k * Nat.primeCounting (2 ^ k) + k + 1 := by
  have hge := Chebyshev.pi_ge (2 ^ k)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogpow : Real.log ((2 ^ k : ℕ) : ℝ) = k * Real.log 2 := by
    push_cast; rw [Real.log_pow]
  have hlogsucc : Real.log (((2 ^ k : ℕ) : ℝ) + 1) ≤ (k + 1) * Real.log 2 := by
    have h1 : (((2 ^ k : ℕ) : ℝ) + 1) ≤ 2 ^ (k + 1) := by
      push_cast
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      rw [pow_succ]; linarith
    calc Real.log (((2 ^ k : ℕ) : ℝ) + 1) ≤ Real.log (2 ^ (k + 1)) :=
          Real.log_le_log (by positivity) h1
      _ = (k + 1) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
  rw [hlogpow] at hge
  have hkpos : (0 : ℝ) < k * Real.log 2 := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  rw [div_le_iff₀ hkpos] at hge
  have key : ((2 ^ k : ℕ) : ℝ) ≤ k * (Nat.primeCounting (2 ^ k) : ℝ) + k + 1 := by
    nlinarith
  exact_mod_cast key


/-- `16 k² ≤ 2^k` for `k ≥ 11`. -/
theorem sixteen_mul_sq_le_two_pow (k : ℕ) (hk : 11 ≤ k) : 16 * (k * k) ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    nlinarith

/-- The prime counting function as a filtered card. -/
theorem primeCounting_eq_card (X : ℕ) :
    Nat.primeCounting X = ((range (X + 1)).filter Nat.Prime).card := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

/-- The prime-sum bound for `n ≥ 2049`, from Chebyshev's lower bound on `π`. -/
theorem primeSumBelow_ge_large (n : ℕ) (hn : 2049 ≤ n) :
    2 * n + 24 ≤ primeSumBelow n := by
  set k := Nat.log 2 (n - 1) with hk_def
  set X := 2 ^ k with hX_def
  have hXle : X ≤ n - 1 := Nat.pow_log_le_self 2 (by omega)
  have hXlt : n - 1 < 2 * X := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (n - 1)
    rw [← hk_def, Nat.succ_eq_add_one, pow_succ, ← hX_def] at h
    omega
  have hk11 : 11 ≤ k := by
    rw [hk_def]
    exact Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  set m := Nat.primeCounting X with hm_def
  have hcheb : X ≤ k * m + k + 1 := two_pow_le_primeCounting k (by omega)
  have hsq : 16 * (k * k) ≤ X := sixteen_mul_sq_le_two_pow k hk11
  have hmX : m ≤ X + 1 := by
    rw [hm_def, primeCounting_eq_card]
    exact (card_filter_le _ _).trans (card_range _).le
  have hsub : (range (X + 1)).filter Nat.Prime ⊆ (range n).filter Nat.Prime := by
    intro p hp
    rw [mem_filter, mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hsum : m * m ≤ 2 * primeSumBelow n + m := by
    have h1 := card_mul_card_le_two_mul_sum ((range (X + 1)).filter Nat.Prime)
    have h2 : ∑ p ∈ (range (X + 1)).filter Nat.Prime, p ≤ primeSumBelow n :=
      sum_le_sum_of_subset hsub
    rw [hm_def, primeCounting_eq_card]
    omega
  -- the analytic core: `9X + 49 ≤ m²`
  have h10 : 9 * X ≤ 10 * (k * m) := by nlinarith
  have hsq81 : 81 * (X * X) ≤ 100 * ((k * m) * (k * m)) := by nlinarith
  have hkk : 0 < k * k := by positivity
  have hm2 : 1296 * X ≤ 100 * (m * m) := by
    have h3 : (k * k) * (1296 * X) ≤ (k * k) * (100 * (m * m)) := by nlinarith
    exact Nat.le_of_mul_le_mul_left h3 hkk
  have hX2048 : 2048 ≤ X := by
    calc 2048 = 2 ^ 11 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk11
  omega

/-- **Prime-sum bound.** For `n ≥ 20`, the primes below `n` sum to at least
`2n + 24`. -/
theorem primeSumBelow_ge (n : ℕ) (hn : 20 ≤ n) : 2 * n + 24 ≤ primeSumBelow n := by
  rcases le_or_gt n 3001 with h | h
  · exact primeSumBelow_ge_small n hn h
  · exact primeSumBelow_ge_large n (by omega)

/-! ## Richert's window argument, avoiding one prime -/

/-- The primes `< B` other than `q`. -/
def allowed (q B : ℕ) : Finset ℕ := (range B).filter (fun p => p.Prime ∧ p ≠ q)

/-- Window property at threshold `B`: every `x` with `13 ≤ x` and
`x + 13 ≤ ∑ allowed q B` is a sum of a subset of `allowed q B`. -/
def Window (q B : ℕ) : Prop :=
  ∀ x, 13 ≤ x → x + 13 ≤ ∑ p ∈ allowed q B, p → ∃ T ⊆ allowed q B, ∑ p ∈ T, p = x

/-- One step of Richert's argument: crossing an allowed prime `B` with
`B + 25 ≤ ∑ allowed q B` extends the window; crossing anything else changes
nothing. -/
theorem window_succ (q B : ℕ) (hW : Window q B)
    (hstep : B.Prime → B ≠ q → B + 25 ≤ ∑ p ∈ allowed q B, p) : Window q (B + 1) := by
  by_cases hB : B.Prime ∧ B ≠ q
  · have hins : allowed q (B + 1) = insert B (allowed q B) := by
      rw [allowed, range_add_one, filter_insert, if_pos hB]; rfl
    have hnot : B ∉ allowed q B := by
      simp [allowed]
    have hS := hstep hB.1 hB.2
    intro x hx hxS
    rw [hins, sum_insert hnot] at hxS
    rw [hins]
    by_cases hsmall : x + 13 ≤ ∑ p ∈ allowed q B, p
    · obtain ⟨T, hT, hTs⟩ := hW x hx hsmall
      exact ⟨T, hT.trans (subset_insert _ _), hTs⟩
    · obtain ⟨T, hT, hTs⟩ := hW (x - B) (by omega) (by omega)
      have hBT : B ∉ T := fun h => hnot (hT h)
      refine ⟨insert B T, insert_subset_insert _ hT, ?_⟩
      rw [sum_insert hBT, hTs]
      omega
  · have heq : allowed q (B + 1) = allowed q B := by
      rw [allowed, range_add_one, filter_insert, if_neg hB]; rfl
    intro x hx hxS
    rw [heq] at hxS ⊢
    exact hW x hx hxS

/-- Decidable bounded form of `Window`, for the base case. -/
def WindowB (q B : ℕ) : Prop :=
  ∀ x ∈ Icc 13 (∑ p ∈ allowed q B, p - 13), ∃ T ∈ (allowed q B).powerset, ∑ p ∈ T, p = x

instance (q B : ℕ) : Decidable (WindowB q B) := by
  unfold WindowB; infer_instance

/-- The bounded form implies the window property. -/
theorem window_of_windowB (q B : ℕ) (h : WindowB q B) : Window q B := by
  intro x hx hxS
  obtain ⟨T, hT, hTs⟩ := h x (mem_Icc.mpr ⟨hx, by omega⟩)
  exact ⟨T, mem_powerset.mp hT, hTs⟩

set_option maxRecDepth 100000 in
/-- Base case of the window argument: the window holds at `B = 20` for every `q`. -/
theorem window_twenty (q : ℕ) : Window q 20 := by
  apply window_of_windowB
  have hsmall : ∀ q ∈ range 21, WindowB q 20 := by decide
  rcases le_or_gt q 20 with hq | hq
  · exact hsmall q (mem_range.mpr (by omega))
  · have heq : allowed q 20 = allowed 20 20 := by
      apply filter_congr
      intro p hp
      have hp20 := mem_range.mp hp
      constructor
      · rintro ⟨hpp, -⟩; exact ⟨hpp, by omega⟩
      · rintro ⟨hpp, -⟩; exact ⟨hpp, by omega⟩
    have h20 := hsmall 20 (mem_range.mpr (by omega))
    unfold WindowB at h20 ⊢
    rw [heq]
    exact h20

/-- Removing one prime `q` from the primes below `B` costs at most `B - 1`. -/
theorem primeSumBelow_le_allowed (q B : ℕ) :
    primeSumBelow B ≤ ∑ p ∈ allowed q B, p + (B - 1) := by
  unfold primeSumBelow
  rw [← sum_filter_add_sum_filter_not ((range B).filter Nat.Prime) (fun p => p ≠ q)]
  have hfil : ((range B).filter Nat.Prime).filter (fun p => p ≠ q) = allowed q B := by
    rw [allowed, filter_filter]
  rw [hfil]
  have hrest : ∑ p ∈ ((range B).filter Nat.Prime).filter (fun p => ¬ p ≠ q), p ≤ B - 1 := by
    set t := ((range B).filter Nat.Prime).filter (fun p => ¬ p ≠ q) with ht
    have hcard : t.card ≤ 1 := by
      apply card_le_one.mpr
      intro a ha b hb
      have ha' : a = q := not_not.mp (mem_filter.mp ha).2
      have hb' : b = q := not_not.mp (mem_filter.mp hb).2
      rw [ha', hb']
    have hle : ∀ p ∈ t, p ≤ B - 1 := by
      intro p hp
      have := mem_range.mp (mem_filter.mp (mem_filter.mp hp).1).1
      omega
    calc ∑ p ∈ t, p ≤ t.card • (B - 1) := sum_le_card_nsmul t _ _ hle
      _ ≤ 1 • (B - 1) := by gcongr
      _ = B - 1 := one_smul _ _
  omega

/-- For `B ≥ 20`, the allowed primes below `B` sum to at least `B + 25`. -/
theorem allowed_sum_ge (q B : ℕ) (hB : 20 ≤ B) : B + 25 ≤ ∑ p ∈ allowed q B, p := by
  have h1 := primeSumBelow_ge B hB
  have h2 := primeSumBelow_le_allowed q B
  omega

/-- The window holds at every threshold `B ≥ 20`. -/
theorem window_of_le (q B : ℕ) (hB : 20 ≤ B) : Window q B := by
  induction B, hB using Nat.le_induction with
  | base => exact window_twenty q
  | succ B hB ih => exact window_succ q B ih fun _ _ => allowed_sum_ge q B hB

/-- **Key lemma.** Every `m ≥ 13` is a sum of distinct primes avoiding any
prescribed `q`. -/
theorem exists_primeSum_avoid (q m : ℕ) (hm : 13 ≤ m) :
    ∃ T : Finset ℕ, (∀ p ∈ T, p.Prime) ∧ q ∉ T ∧ ∑ p ∈ T, p = m := by
  have hW := window_of_le q (max 20 m) (le_max_left _ _)
  have hS := allowed_sum_ge q (max 20 m) (le_max_left _ _)
  obtain ⟨T, hT, hTs⟩ := hW m hm (by have := le_max_right 20 m; omega)
  refine ⟨T, fun p hp => (mem_filter.mp (hT hp)).2.1, fun hq => ?_, hTs⟩
  exact (mem_filter.mp (hT hq)).2.2 rfl

/-! ## Which primes occur -/

/-- No set of primes sums to `1`, `4` or `6`. -/
theorem not_primeSum_one_four_six (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime)
    (h : ∑ p ∈ T, p = 1 ∨ ∑ p ∈ T, p = 4 ∨ ∑ p ∈ T, p = 6) : False := by
  have hsub : T ∈ (primesLE 6).powerset := by
    refine mem_powerset.mpr fun p hp => ?_
    have hle : p ≤ ∑ p ∈ T, p := single_le_sum (fun i _ => Nat.zero_le i) hp
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), hT p hp⟩
  have hall : ∀ U ∈ (primesLE 6).powerset,
      ¬ (∑ p ∈ U, p = 1 ∨ ∑ p ∈ U, p = 4 ∨ ∑ p ∈ U, p = 6) := by decide
  exact hall T hsub h

/-- A set of primes all `< q` avoids `q`. -/
theorem avoid_of_lt (q : ℕ) (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime ∧ p < q) :
    (∀ p ∈ T, p.Prime) ∧ q ∉ T := ⟨fun p hp => (hT p hp).1, fun hq => lt_irrefl q (hT q hq).2⟩

/-- Small cases: for `m ≤ 12`, `m ∉ {1, 4, 6}` and `q ≥ 11` (with `q ≠ 11` when
`m = 11`), `m` is a sum of distinct primes avoiding `q`. -/
theorem exists_primeSum_avoid_small (q m : ℕ) (hm : m ≤ 12) (h1 : m ≠ 1) (h4 : m ≠ 4)
    (h6 : m ≠ 6) (hq : 11 ≤ q) (h11 : m = 11 → q ≠ 11) :
    ∃ T : Finset ℕ, (∀ p ∈ T, p.Prime) ∧ q ∉ T ∧ ∑ p ∈ T, p = m := by
  have wit : ∀ T : Finset ℕ, (∀ p ∈ T, p.Prime ∧ p < q) → ∑ p ∈ T, p = m →
      ∃ T : Finset ℕ, (∀ p ∈ T, p.Prime) ∧ q ∉ T ∧ ∑ p ∈ T, p = m :=
    fun T hT hs => ⟨T, (avoid_of_lt q T hT).1, (avoid_of_lt q T hT).2, hs⟩
  have hq11 : m = 11 → 12 ≤ q := fun h => by have := h11 h; omega
  interval_cases m
  · exact wit ∅ (by simp) rfl
  · omega
  · exact wit {2} (fun p hp => by fin_cases hp; exact ⟨by norm_num, by omega⟩) rfl
  · exact wit {3} (fun p hp => by fin_cases hp; exact ⟨by norm_num, by omega⟩) rfl
  · omega
  · exact wit {5} (fun p hp => by fin_cases hp; exact ⟨by norm_num, by omega⟩) rfl
  · omega
  · exact wit {7} (fun p hp => by fin_cases hp; exact ⟨by norm_num, by omega⟩) rfl
  · exact wit {3, 5} (fun p hp => by fin_cases hp <;> exact ⟨by norm_num, by omega⟩) rfl
  · exact wit {2, 7} (fun p hp => by fin_cases hp <;> exact ⟨by norm_num, by omega⟩) rfl
  · exact wit {3, 7} (fun p hp => by fin_cases hp <;> exact ⟨by norm_num, by omega⟩) rfl
  · exact wit {11} (fun p hp => by
      have := hq11 rfl; fin_cases hp; exact ⟨by norm_num, by omega⟩) rfl
  · exact wit {5, 7} (fun p hp => by fin_cases hp <;> exact ⟨by norm_num, by omega⟩) rfl

/-- **Characterization.** For `n ≥ 23` and a prime `q ≤ n`, `q` occurs in a
partition of `n` into distinct primes iff `n - q ∉ {1, 4, 6}`. -/
theorem occursIn_iff (n q : ℕ) (hn : 23 ≤ n) (hq : q.Prime) (hqn : q ≤ n) :
    OccursIn n q ↔ n - q ≠ 1 ∧ n - q ≠ 4 ∧ n - q ≠ 6 := by
  constructor
  · rintro ⟨S, hS, hqS, hsum⟩
    have hT : ∑ p ∈ S.erase q, p = n - q := by
      have := sum_erase_add S (fun p => p) hqS
      omega
    have hTp : ∀ p ∈ S.erase q, p.Prime := fun p hp => hS p (mem_of_mem_erase hp)
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
      exact not_primeSum_one_four_six _ hTp (by omega)
  · rintro ⟨h1, h4, h6⟩
    obtain ⟨T, hTp, hqT, hTs⟩ : ∃ T : Finset ℕ, (∀ p ∈ T, p.Prime) ∧ q ∉ T ∧
        ∑ p ∈ T, p = n - q := by
      rcases le_or_gt 13 (n - q) with hbig | hsmall
      · exact exists_primeSum_avoid q (n - q) hbig
      · exact exists_primeSum_avoid_small q (n - q) (by omega) h1 h4 h6 (by omega)
          (by omega)
    refine ⟨insert q T, fun p hp => ?_, mem_insert_self q T, ?_⟩
    · rcases mem_insert.mp hp with rfl | hp
      · exact hq
      · exact hTp p hp
    · rw [sum_insert hqT, hTs]
      omega

/-! ## The conjecture -/

/-- For `n ≥ 23`, the number of primes at most `n` absent from every
distinct-prime partition equals the number of primes among `n-1`, `n-4`, `n-6`
(the unsigned conjecture in OEIS A054656). -/
theorem a_eq_card_filter_prime (n : ℕ) (hn : 23 ≤ n) :
    a n = (({n - 1, n - 4, n - 6} : Finset ℕ).filter Nat.Prime).card := by
  unfold a
  congr 1
  ext q
  simp only [mem_filter, mem_range, mem_insert, mem_singleton, occursInB_iff]
  constructor
  · rintro ⟨hqn, hq, hnot⟩
    refine ⟨?_, hq⟩
    by_contra hne
    exact hnot ((occursIn_iff n q hn hq (by omega)).mpr ⟨by omega, by omega, by omega⟩)
  · rintro ⟨hk, hq⟩
    have hqn : q ≤ n := by omega
    refine ⟨by omega, hq, fun hocc => ?_⟩
    have := (occursIn_iff n q hn hq hqn).mp hocc
    omega

/-- An even number `k > 2` is not prime. -/
theorem not_prime_of_mod_two (k : ℕ) (hk : 2 < k) (he : k % 2 = 0) : ¬ k.Prime := fun hp => by
  rcases hp.eq_two_or_odd with h | h <;> omega

/-- The A054656 case split: For `n ≥ 23`: `a n = 2` if both `n - 6`
and `n - 4` are prime; otherwise `a n = 1` if one of `n - 6`, `n - 4`, `n - 1` is
prime; otherwise `a n = 0`.  (Unsigned comment in
OEIS A054656; `n ≥ 23` keeps every subtraction off its truncation.) -/
theorem a_eq_entry (n : ℕ) (hn : 23 ≤ n) :
    a n = if (n - 6).Prime ∧ (n - 4).Prime then 2
      else if (n - 6).Prime ∨ (n - 4).Prime ∨ (n - 1).Prime then 1 else 0 := by
  rw [a_eq_card_filter_prime n hn]
  have h14 : n - 1 ≠ n - 4 := by omega
  have h16 : n - 1 ≠ n - 6 := by omega
  have h46 : n - 4 ≠ n - 6 := by omega
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨r, hr⟩ := he
    have hn4 : ¬ (n - 4).Prime := not_prime_of_mod_two _ (by omega) (by omega)
    have hn6 : ¬ (n - 6).Prime := not_prime_of_mod_two _ (by omega) (by omega)
    by_cases h1 : (n - 1).Prime <;> simp [filter_insert, filter_singleton, hn4, hn6, h1]
  · obtain ⟨r, hr⟩ := ho
    have hn1 : ¬ (n - 1).Prime := not_prime_of_mod_two _ (by omega) (by omega)
    by_cases h4 : (n - 4).Prime <;> by_cases h6 : (n - 6).Prime <;>
      simp [filter_insert, filter_singleton, hn1, h4, h6, h46]

/-- Non-vacuity: at `n = 23` both `n - 4 = 19` and `n - 6 = 17` are prime and
`a 23 = 2`. -/
example : a 23 = 2 ∧ (23 - 4).Prime ∧ (23 - 6).Prime :=
  ⟨by rw [a_eq_entry 23 le_rfl]; decide, by norm_num, by norm_num⟩

end Candidates.A054656PrimesOccurPartition
