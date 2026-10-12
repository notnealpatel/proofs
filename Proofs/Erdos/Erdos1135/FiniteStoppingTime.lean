import Mathlib

set_option autoImplicit false

namespace Erdos1135

/-- The shortcut Collatz map on natural numbers, with zero fixed. -/
def T (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

example : T 0 = 0 := rfl
example : T 1 = 2 := rfl
example : T 2 = 1 := rfl
example : T 3 = 5 := rfl

/-- The parity of the actual orbit at time `i`, represented by zero or one. -/
def orbitParity (n i : ℕ) : ℕ := (T^[i]) n % 2

example : orbitParity 3 0 = 1 := rfl
example : orbitParity 2 0 = 0 := rfl

/-- The number of odd steps among the first `k` steps of the actual orbit. -/
def oddCount (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => oddCount n k + orbitParity n k

example : oddCount 3 1 = 1 := rfl
example : oddCount 2 1 = 0 := rfl

/-- The accumulated affine error on the actual orbit. -/
def affineError (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 3 ^ orbitParity n k * affineError n k + orbitParity n k * 2 ^ k

example : affineError 3 1 = 1 := rfl
example : affineError 2 1 = 0 := rfl

/-- Positive starts with a positive-time iterate strictly below the start. -/
def finiteStoppingTime (n : ℕ) : Prop :=
  0 < n ∧ ∃ t : ℕ, 1 ≤ t ∧ (T^[t]) n < n

example : finiteStoppingTime 2 := ⟨by decide, 1, by decide, by decide⟩
example : ¬ finiteStoppingTime 0 := by simp [finiteStoppingTime]

/-- The one-step affine identity, including the even and odd division guards. -/
theorem two_mul_T (n : ℕ) : 2 * T n = 3 ^ (n % 2) * n + n % 2 := by
  have hp : n % 2 < 2 := Nat.mod_lt n (by decide)
  by_cases he : n % 2 = 0
  · simp only [T, he, if_pos, pow_zero, one_mul, add_zero]
    omega
  · have ho : n % 2 = 1 := by omega
    unfold T
    rw [if_neg he, ho, pow_one]
    omega

/-- Adding an even increment preserves parity and has the expected branchwise effect. -/
theorem T_add_two_mul (n a : ℕ) :
    T (n + 2 * a) = T n + 3 ^ (n % 2) * a := by
  have hp : (n + 2 * a) % 2 = n % 2 := by omega
  have h₁ := two_mul_T (n + 2 * a)
  have h₂ := two_mul_T n
  rw [hp] at h₁
  nlinarith

/-- The affine formula uses precisely the parities of the same actual trajectory. -/
theorem iterate_affine (n k : ℕ) :
    2 ^ k * (T^[k]) n = 3 ^ oddCount n k * n + affineError n k := by
  induction k with
  | zero => simp [oddCount, affineError]
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ, oddCount, affineError, pow_add]
    have hs := two_mul_T ((T^[k]) n)
    change 2 * T ((T^[k]) n) = 3 ^ orbitParity n k * (T^[k]) n + orbitParity n k at hs
    calc
      2 ^ k * 2 * T ((T^[k]) n) = 2 ^ k * (2 * T ((T^[k]) n)) := by ring
      _ = 2 ^ k * (3 ^ orbitParity n k * (T^[k]) n + orbitParity n k) := by rw [hs]
      _ = 3 ^ orbitParity n k * (2 ^ k * (T^[k]) n) + orbitParity n k * 2 ^ k := by ring
      _ = _ := by rw [ih]; ring

/-- The affine error is bounded without truncated natural subtraction. -/
theorem affineError_add_pow_le (n k : ℕ) : affineError n k + 2 ^ k ≤ 3 ^ k := by
  induction k with
  | zero => simp [affineError]
  | succ k ih =>
    have hp : orbitParity n k < 2 := Nat.mod_lt _ (by decide)
    have hpow : 2 ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by decide : 2 ≤ 3) k
    rcases (by omega : orbitParity n k = 0 ∨ orbitParity n k = 1) with he | ho
    · simp only [affineError, he, pow_zero, one_mul, zero_mul, add_zero, pow_succ]
      omega
    · simp only [affineError, ho, one_mul, pow_succ]
      omega

/-- Every positive power of three is odd, including the zeroth power. -/
theorem three_pow_mod_two (j : ℕ) : 3 ^ j % 2 = 1 := by
  simp [Nat.pow_mod]

/-- A power-of-two shift follows the same branches through the indicated time. -/
theorem iterate_shift (n h i d : ℕ) :
    (T^[i]) (n + h * 2 ^ (i + d)) =
      (T^[i]) n + h * 2 ^ d * 3 ^ oddCount n i := by
  induction i generalizing d with
  | zero => simp [oddCount]
  | succ i ih =>
    have hexp : i + 1 + d = i + (d + 1) := by omega
    rw [hexp, Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    have heven : h * 2 ^ (d + 1) * 3 ^ oddCount n i =
        2 * (h * 2 ^ d * 3 ^ oddCount n i) := by rw [pow_succ]; ring
    rw [heven, T_add_two_mul, oddCount, pow_add]
    simp only [orbitParity]
    ring

/-- A shift by a multiple of `2^k` preserves every parity before time `k`. -/
theorem orbitParity_shift (n h k i : ℕ) (hi : i < k) :
    orbitParity (n + h * 2 ^ k) i = orbitParity n i := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hi
  rw [hd]
  have hshift := iterate_shift n h i (d + 1)
  have hexp : i + (d + 1) = i + d + 1 := by omega
  rw [hexp] at hshift
  unfold orbitParity
  rw [hshift]
  have heven : h * 2 ^ (d + 1) * 3 ^ oddCount n i =
      2 * (h * 2 ^ d * 3 ^ oddCount n i) := by rw [pow_succ]; ring
  rw [heven]
  omega

/-- The two lifts of a residue have opposite next parities. -/
theorem orbitParity_lift (n k : ℕ) :
    orbitParity (n + 2 ^ k) k ≠ orbitParity n k := by
  have hs := iterate_shift n 1 k 0
  simp only [Nat.add_zero, pow_zero, mul_one, one_mul] at hs
  have hp := three_pow_mod_two (oddCount n k)
  unfold orbitParity
  rw [hs]
  omega

/-- Powers of two halve along their actual trajectory until reaching one. -/
theorem iterate_two_pow (k d : ℕ) : (T^[k]) (2 ^ (k + d)) = 2 ^ d := by
  induction k generalizing d with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    have he : T (2 ^ (k + 1 + d)) = 2 ^ (k + d) := by
      have hexp : k + 1 + d = (k + d) + 1 := by omega
      rw [hexp, pow_succ]
      simp [T]
    rw [he, ih]

/-- One remains exceptional: its orbit alternates between one and two. -/
theorem iterate_one_or_two (k : ℕ) : (T^[k]) 1 = 1 ∨ (T^[k]) 1 = 2 := by
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h
    · rw [h]; exact Or.inr rfl
    · rw [h]; exact Or.inl rfl

/-- The start one does not have finite stopping time. -/
theorem not_finiteStoppingTime_one : ¬ finiteStoppingTime 1 := by
  rintro ⟨_, t, _, ht⟩
  rcases iterate_one_or_two t with h | h
  · omega
  · omega

/-- The actual length-`k` parity word, including the orbit of residue zero. -/
def parityWord (k n : ℕ) : Fin k → Fin 2 :=
  fun i => ⟨orbitParity n i, Nat.mod_lt _ (by decide)⟩

example : parityWord 1 0 0 = 0 := rfl
example : parityWord 1 3 0 = 1 := rfl

/-- Equal initial actual parity words have equal odd counts and affine errors. -/
theorem coefficients_eq_of_parity (k a b : ℕ)
    (h : ∀ i < k, orbitParity a i = orbitParity b i) :
    oddCount a k = oddCount b k ∧ affineError a k = affineError b k := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    have hprev := ih (fun i hi => h i (by omega))
    have hlast := h k (by omega)
    simp [oddCount, affineError, hprev.1, hprev.2, hlast]

/-- An actual parity word identifies its residue modulo the appropriate power of two. -/
theorem modEq_of_parityWord_eq (k a b : ℕ) (h : parityWord k a = parityWord k b) :
    Nat.ModEq (2 ^ k) a b := by
  have hc := coefficients_eq_of_parity k a b (fun i hi =>
    congrArg Fin.val (congrFun h ⟨i, hi⟩))
  have ha := iterate_affine a k
  have hb := iterate_affine b k
  have hm : Nat.ModEq (2 ^ k)
      (3 ^ oddCount a k * a + affineError a k)
      (3 ^ oddCount a k * b + affineError a k) := by
    rw [← ha, hc.1, hc.2, ← hb]
    simp [Nat.ModEq]
  have hm' := Nat.ModEq.add_right_cancel (Nat.ModEq.refl (affineError a k)) hm
  exact Nat.ModEq.cancel_left_of_coprime
    ((by decide : Nat.Coprime 2 3).pow k (oddCount a k)) hm'

/-- Actual parity words are a bijection on the full residue system, not an oracle model. -/
theorem parityWord_bijective (k : ℕ) :
    Function.Bijective (fun r : Fin (2 ^ k) => parityWord k r.val) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro a b h
    apply Fin.ext
    have hm := modEq_of_parityWord_eq k a.val b.val h
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using hm
  · simp

/-- The actual parity word depends only on the start modulo `2^k`. -/
theorem parityWord_mod (k n : ℕ) : parityWord k (n % 2 ^ k) = parityWord k n := by
  funext i
  apply Fin.ext
  have hs := orbitParity_shift (n % 2 ^ k) (n / 2 ^ k) k i.val i.isLt
  have hn : n % 2 ^ k + n / 2 ^ k * 2 ^ k = n := by
    simpa only [Nat.mul_comm] using Nat.mod_add_div n (2 ^ k)
  rw [hn] at hs
  exact hs.symm

/-- The original finite exceptional count, on positive starts and actual iterates. -/
def exceptionalCount (ell N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun n => 7 ^ ell * n ≤ 8 ^ ell * (T^[5 * ell]) n)).card

example : exceptionalCount 0 1 = 1 := by decide
example : exceptionalCount 3 0 = 0 := by decide

/-- A nontrivial coefficient witness for the proposed finite bound. -/
theorem coefficient_nontrivial : 3 * 3125 ^ 12 < (3456 : ℕ) ^ 12 := by norm_num

/-- A same-object fixture: the proposed parameters and actual sixty-step halving orbit. -/
theorem halving_fixture :
    3 ≤ (12 : ℕ) ∧ 32 ^ 12 ≤ (32 : ℕ) ^ 12 ∧
      (T^[5 * 12]) (32 ^ 12) = 1 ∧
      (∀ i < 60, orbitParity (32 ^ 12) i = 0) ∧
      8 ^ 12 * (T^[5 * 12]) (32 ^ 12) < 7 ^ 12 * (32 ^ 12) := by
  have hn : (32 : ℕ) ^ 12 = 2 ^ 60 := by norm_num
  have ht : (T^[5 * 12]) (32 ^ 12) = 1 := by
    rw [hn]
    exact iterate_two_pow 60 0
  refine ⟨by decide, le_rfl, ht, ?_, ?_⟩
  · intro i hi
    have hsplit : 60 = i + (60 - i) := by omega
    have hd : 0 < 60 - i := by omega
    obtain ⟨d, hd'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : 60 - i ≠ 0)
    unfold orbitParity
    rw [hn, hsplit, iterate_two_pow, hd', pow_succ]
    omega
  · rw [ht]
    norm_num

/-- The sum of the actual bits is the recursive odd count. -/
theorem oddCount_eq_sum (n k : ℕ) : oddCount n k = ∑ i : Fin k, (parityWord k n i).val := by
  induction k with
  | zero => simp [oddCount]
  | succ k ih =>
    rw [oddCount, Fin.sum_univ_castSucc]
    simpa only [parityWord, Fin.val_castSucc, Fin.val_last] using congrArg
      (fun x => x + orbitParity n k) ih

/-- Deterministic weighted enumeration of all length-`k` binary words. -/
theorem word_weight_sum (k : ℕ) :
    (∑ w : Fin k → Fin 2, (3 / 2 : ℚ) ^ (∑ i, (w i).val)) = (5 / 2 : ℚ) ^ k := by
  have h := Fintype.prod_sum (fun (_ : Fin k) (b : Fin 2) => (3 / 2 : ℚ) ^ b.val)
  have hbit : (∑ b : Fin 2, (3 / 2 : ℚ) ^ b.val) = 5 / 2 := by
    norm_num [Fin.sum_univ_two]
  simpa only [← Finset.prod_pow_eq_pow_sum, hbit, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] using h.symm

/-- Weighted counting bounds the number of bad binary words without randomness. -/
theorem bad_word_count_bound (ell : ℕ) :
    (((Finset.univ : Finset (Fin (5 * ell) → Fin 2)).filter
      (fun w => 3 * ell < ∑ i, (w i).val)).card : ℚ) * (3 / 2 : ℚ) ^ (3 * ell)
        ≤ (5 / 2 : ℚ) ^ (5 * ell) := by
  classical
  let s := (Finset.univ : Finset (Fin (5 * ell) → Fin 2)).filter
    (fun w => 3 * ell < ∑ i, (w i).val)
  calc
    (s.card : ℚ) * (3 / 2 : ℚ) ^ (3 * ell) = ∑ _w ∈ s, (3 / 2 : ℚ) ^ (3 * ell) := by simp
    _ ≤ ∑ w ∈ s, (3 / 2 : ℚ) ^ (∑ i, (w i).val) := by
      apply Finset.sum_le_sum
      intro w hw
      have hj : 3 * ell ≤ ∑ i, (w i).val := Nat.le_of_lt (Finset.mem_filter.mp hw).2
      exact pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 3 / 2) hj
    _ ≤ ∑ w : Fin (5 * ell) → Fin 2, (3 / 2 : ℚ) ^ (∑ i, (w i).val) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro w _ _
      positivity
    _ = _ := word_weight_sum (5 * ell)

/-- Good actual words force strict terminal contraction for the specified large starts. -/
theorem contraction_of_oddCount_le (ell n : ℕ) (hell : 1 ≤ ell)
    (hn : 27 * 9 ^ ell ≤ n) (hj : oddCount n (5 * ell) ≤ 3 * ell) :
    8 ^ ell * (T^[5 * ell]) n < 7 ^ ell * n := by
  have ha := iterate_affine n (5 * ell)
  have hc := affineError_add_pow_le n (5 * ell)
  have hcoeff : 3 ^ oddCount n (5 * ell) ≤ 27 ^ ell := by
    calc
      _ ≤ 3 ^ (3 * ell) := Nat.pow_le_pow_right (by decide) hj
      _ = _ := by rw [pow_mul]; norm_num
  have hp : 0 < 2 ^ (5 * ell) := by positivity
  have hc' : affineError n (5 * ell) < 243 ^ ell := by
    have he : (3 : ℕ) ^ (5 * ell) = 243 ^ ell := by rw [pow_mul]; norm_num
    rw [he] at hc
    omega
  have he₁ : ell - 1 + 1 = ell := by omega
  have hgap : 243 ^ ell ≤ 27 ^ (ell - 1) * n := by
    calc
      243 ^ ell = 27 ^ (ell - 1) * (27 * 9 ^ ell) := by
        rw [← mul_assoc, ← pow_succ, he₁, ← mul_pow]
        norm_num
      _ ≤ _ := Nat.mul_le_mul_left _ hn
  have hbase : 27 ^ ell + 27 ^ (ell - 1) ≤ 28 ^ ell := by
    calc
      _ = 28 * 27 ^ (ell - 1) := by
        have hepow : (27 : ℕ) ^ ell = 27 ^ (ell - 1) * 27 := by rw [← pow_succ, he₁]
        rw [hepow]; ring
      _ ≤ 28 * 28 ^ (ell - 1) := Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (by decide : 27 ≤ 28) _)
      _ = _ := by rw [mul_comm, ← pow_succ, he₁]
  have hterm : 32 ^ ell * (T^[5 * ell]) n < 28 ^ ell * n := by
    have he : (2 : ℕ) ^ (5 * ell) = 32 ^ ell := by rw [pow_mul]; norm_num
    rw [he] at ha
    have hmul := Nat.mul_le_mul_right n hbase
    have hmul' := Nat.mul_le_mul_right n hcoeff
    nlinarith
  have he₂ : (32 : ℕ) ^ ell = 4 ^ ell * 8 ^ ell := by rw [← mul_pow]; norm_num
  have he₃ : (28 : ℕ) ^ ell = 4 ^ ell * 7 ^ ell := by rw [← mul_pow]; norm_num
  rw [he₂, he₃] at hterm
  have hp' : 0 < (4 : ℕ) ^ ell := by positivity
  nlinarith

/-- Original positive-start exceptions are bounded by small starts and actual bad-word blocks. -/
theorem exceptionalCount_le_small_add_blocks (ell N : ℕ) (hell : 1 ≤ ell) :
    exceptionalCount ell N ≤ 27 * 9 ^ ell +
      (((Finset.univ : Finset (Fin (5 * ell) → Fin 2)).filter
        (fun w => 3 * ell < ∑ i, (w i).val)).card) * (N / 2 ^ (5 * ell) + 1) := by
  classical
  let s := (Finset.Icc 1 N).filter (fun n => 7 ^ ell * n ≤ 8 ^ ell * (T^[5 * ell]) n)
  let small := s.filter (fun n => n < 27 * 9 ^ ell)
  let large := s.filter (fun n => ¬ n < 27 * 9 ^ ell)
  let bad := (Finset.univ : Finset (Fin (5 * ell) → Fin 2)).filter
    (fun w => 3 * ell < ∑ i, (w i).val)
  have hsmall : small.card ≤ 27 * 9 ^ ell := by
    calc
      small.card ≤ (Finset.range (27 * 9 ^ ell)).card := by
        apply Finset.card_le_card
        intro n hn
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hn).2
      _ = _ := Finset.card_range _
  have hlarge : large.card ≤ bad.card * (N / 2 ^ (5 * ell) + 1) := by
    let f := fun n : ℕ => (parityWord (5 * ell) n, n / 2 ^ (5 * ell))
    have hm : Set.MapsTo f (large : Set ℕ)
        ((bad ×ˢ Finset.range (N / 2 ^ (5 * ell) + 1) : Finset _) : Set _) := by
      intro n hn
      have hnl := Finset.mem_filter.mp hn
      have hns := Finset.mem_filter.mp hnl.1
      have hinterval := Finset.mem_Icc.mp hns.1
      have hbad : 3 * ell < oddCount n (5 * ell) := by
        by_contra h
        have hc := contraction_of_oddCount_le ell n hell (by omega) (by omega)
        omega
      apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, by rw [← oddCount_eq_sum]; exact hbad⟩
      · apply Finset.mem_range.mpr
        change n / 2 ^ (5 * ell) < N / 2 ^ (5 * ell) + 1
        have hdiv : n / 2 ^ (5 * ell) ≤ N / 2 ^ (5 * ell) := Nat.div_le_div_right hinterval.2
        omega
    have hinj : (large : Set ℕ).InjOn f := by
      intro a _ b _ hab
      have hw : parityWord (5 * ell) a = parityWord (5 * ell) b := congrArg Prod.fst hab
      have hq : a / 2 ^ (5 * ell) = b / 2 ^ (5 * ell) := congrArg Prod.snd hab
      have hr := modEq_of_parityWord_eq (5 * ell) a b hw
      have ha := Nat.mod_add_div a (2 ^ (5 * ell))
      have hb := Nat.mod_add_div b (2 ^ (5 * ell))
      change a % 2 ^ (5 * ell) = b % 2 ^ (5 * ell) at hr
      rw [hq, hr] at ha
      omega
    simpa only [Finset.card_product, Finset.card_range] using
      Finset.card_le_card_of_injOn f hm hinj
  have hsplit : small.card + large.card = s.card :=
    Finset.card_filter_add_card_filter_not _
  change s.card ≤ 27 * 9 ^ ell + bad.card * (N / 2 ^ (5 * ell) + 1)
  omega

/-- Clearing the weighted-word denominators gives an integral bad-word bound. -/
theorem bad_word_count_integral (ell : ℕ) :
    (((Finset.univ : Finset (Fin (5 * ell) → Fin 2)).filter
      (fun w => 3 * ell < ∑ i, (w i).val)).card) * 108 ^ ell ≤ 3125 ^ ell := by
  have h := mul_le_mul_of_nonneg_right (bad_word_count_bound ell)
    (by positivity : (0 : ℚ) ≤ 32 ^ ell)
  norm_num [pow_mul, mul_assoc, ← mul_pow] at h
  exact_mod_cast h

/-- The unconditional finite exceptional-count inequality for the actual shortcut map. -/
theorem finite_exceptional_bound (ell N : ℕ) (hell : 3 ≤ ell) (hN : 32 ^ ell ≤ N) :
    3456 ^ ell * exceptionalCount ell N ≤ 3 * N * 3125 ^ ell := by
  let B := ((Finset.univ : Finset (Fin (5 * ell) → Fin 2)).filter
    (fun w => 3 * ell < ∑ i, (w i).val)).card
  have hB : B * 108 ^ ell ≤ 3125 ^ ell := bad_word_count_integral ell
  have hsmall : (27 * 9 ^ ell) * 108 ^ ell ≤ 3125 ^ ell := by
    have h27 : 27 ≤ (3 : ℕ) ^ ell := by
      calc
        27 = (3 : ℕ) ^ 3 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by decide) hell
    calc
      (27 * 9 ^ ell) * 108 ^ ell = 27 * 972 ^ ell := by rw [mul_assoc, ← mul_pow]; norm_num
      _ ≤ 3 ^ ell * 972 ^ ell := Nat.mul_le_mul_right _ h27
      _ = 2916 ^ ell := by rw [← mul_pow]; norm_num
      _ ≤ _ := Nat.pow_le_pow_left (by decide) ell
  have hm : 2 ^ (5 * ell) = (32 : ℕ) ^ ell := by rw [pow_mul]; norm_num
  have hF := exceptionalCount_le_small_add_blocks ell N (by omega)
  change exceptionalCount ell N ≤ 27 * 9 ^ ell + B * (N / 2 ^ (5 * ell) + 1) at hF
  rw [hm] at hF
  have hdiv : (N / 32 ^ ell + 1) * 32 ^ ell ≤ 2 * N := by
    have hd := Nat.div_mul_le_self N (32 ^ ell)
    nlinarith
  have hsmall' := Nat.mul_le_mul_right (32 ^ ell) hsmall
  have hN' := Nat.mul_le_mul_right (3125 ^ ell) hN
  have hB' := Nat.mul_le_mul_right ((N / 32 ^ ell + 1) * 32 ^ ell) hB
  have hdiv' := Nat.mul_le_mul_right (3125 ^ ell) hdiv
  have hF' := Nat.mul_le_mul_right (108 ^ ell * 32 ^ ell) hF
  have he : (3456 : ℕ) ^ ell = 108 ^ ell * 32 ^ ell := by rw [← mul_pow]; norm_num
  rw [he]
  nlinarith

open scoped Classical
open Filter Topology

/-- The number of positive starts up to `N` having finite stopping time. -/
noncomputable def stoppingCount (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter finiteStoppingTime).card

example : stoppingCount 0 = 0 := by simp [stoppingCount]

/-- The complementary count on the same positive starting interval. -/
noncomputable def nonStoppingCount (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun n => ¬ finiteStoppingTime n)).card

example : nonStoppingCount 0 = 0 := by simp [nonStoppingCount]

/-- The two complementary predicates partition exactly the original positive interval. -/
theorem stoppingCount_add_nonStoppingCount (N : ℕ) :
    stoppingCount N + nonStoppingCount N = N := by
  have h := (Finset.Icc 1 N).card_filter_add_card_filter_not finiteStoppingTime
  simpa [stoppingCount, nonStoppingCount, Nat.card_Icc] using h

/-- A positive start with no stopping time is an exception at every fixed positive scale. -/
theorem nonStoppingCount_le_exceptionalCount (ell N : ℕ) (hell : 1 ≤ ell) :
    nonStoppingCount N ≤ exceptionalCount ell N := by
  apply Finset.card_le_card
  intro n hn
  have h := Finset.mem_filter.mp hn
  have hp : 0 < n := by have hi := (Finset.mem_Icc.mp h.1).1; omega
  have ht : n ≤ (T^[5 * ell]) n := by
    by_contra hc
    exact h.2 ⟨hp, 5 * ell, by omega, by omega⟩
  apply Finset.mem_filter.mpr
  refine ⟨h.1, ?_⟩
  have hpow : (7 : ℕ) ^ ell ≤ 8 ^ ell := Nat.pow_le_pow_left (by decide) ell
  exact le_trans (Nat.mul_le_mul_right n hpow) (Nat.mul_le_mul_left _ ht)

/-- For each fixed scale, the real complementary ratio is uniformly small beyond its cutoff. -/
theorem nonStopping_ratio_le (ell N : ℕ) (hell : 3 ≤ ell) (hN : 32 ^ ell ≤ N) :
    (nonStoppingCount N : ℝ) / (N : ℝ) ≤ 3 * (3125 / 3456 : ℝ) ^ ell := by
  have hpN : 0 < N := lt_of_lt_of_le (by positivity : 0 < (32 : ℕ) ^ ell) hN
  have hrN : (0 : ℝ) < N := by exact_mod_cast hpN
  have hc : 3456 ^ ell * nonStoppingCount N ≤ 3 * N * 3125 ^ ell :=
    le_trans (Nat.mul_le_mul_left _ (nonStoppingCount_le_exceptionalCount ell N (by omega)))
      (finite_exceptional_bound ell N hell hN)
  have hcR : (3456 : ℝ) ^ ell * (nonStoppingCount N : ℝ) ≤
      3 * (N : ℝ) * (3125 : ℝ) ^ ell := by exact_mod_cast hc
  apply (div_le_iff₀ hrN).2
  have hd : (0 : ℝ) < (3456 : ℝ) ^ ell := by positivity
  have he : 3 * (3125 / 3456 : ℝ) ^ ell * (N : ℝ) =
      (3 * (N : ℝ) * (3125 : ℝ) ^ ell) / (3456 : ℝ) ^ ell := by
    rw [div_pow]
    ring
  rw [he]
  apply (le_div_iff₀ hd).2
  nlinarith

/-- Finite stopping time has ordinary natural density one, with real rather than natural division.
This asserts descent below the start, not convergence to one or stopping of every positive start. -/
theorem finiteStoppingTime_density_one :
    Tendsto (fun N : ℕ =>
      (((Finset.Icc 1 N).filter finiteStoppingTime).card : ℝ) / (N : ℝ))
      atTop (𝓝 1) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hpow : Tendsto (fun ell : ℕ => (3125 / 3456 : ℝ) ^ ell) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hevent : ∀ᶠ ell : ℕ in atTop, (3125 / 3456 : ℝ) ^ ell < ε / 3 :=
    hpow.eventually_lt_const (by linarith)
  obtain ⟨L, hL⟩ := eventually_atTop.mp hevent
  let ell := max 3 L
  have hell : 3 ≤ ell := le_max_left _ _
  have hsmall : 3 * (3125 / 3456 : ℝ) ^ ell < ε := by
    have hs := hL ell (le_max_right _ _)
    linarith
  refine ⟨32 ^ ell, ?_⟩
  intro N hN
  have hpN : 0 < N := lt_of_lt_of_le (by positivity : 0 < (32 : ℕ) ^ ell) hN
  have hrN : (0 : ℝ) < N := by exact_mod_cast hpN
  have hc := nonStopping_ratio_le ell N hell hN
  have hsplit : (stoppingCount N : ℝ) + (nonStoppingCount N : ℝ) = (N : ℝ) := by
    exact_mod_cast stoppingCount_add_nonStoppingCount N
  have hratio : (stoppingCount N : ℝ) / (N : ℝ) +
      (nonStoppingCount N : ℝ) / (N : ℝ) = 1 := by
    rw [← add_div, hsplit, div_self (ne_of_gt hrN)]
  have hnonneg : (0 : ℝ) ≤ (nonStoppingCount N : ℝ) / (N : ℝ) := by positivity
  change dist ((stoppingCount N : ℝ) / (N : ℝ)) 1 < ε
  rw [Real.dist_eq, abs_of_nonpos (by linarith : (stoppingCount N : ℝ) / (N : ℝ) - 1 ≤ 0)]
  linarith

/-- Joint nonvacuity of the actual finite theorem: admissible parameters, the same halving orbit,
its actual even word, the instantiated finite count bound, and a genuinely nontrivial coefficient. -/
theorem finite_bound_fixture :
    3 ≤ (12 : ℕ) ∧ 32 ^ 12 ≤ (32 : ℕ) ^ 12 ∧
      (T^[5 * 12]) (32 ^ 12) = 1 ∧
      (∀ i < 60, orbitParity (32 ^ 12) i = 0) ∧
      8 ^ 12 * (T^[5 * 12]) (32 ^ 12) < 7 ^ 12 * (32 ^ 12) ∧
      3456 ^ 12 * exceptionalCount 12 (32 ^ 12) ≤ 3 * 32 ^ 12 * 3125 ^ 12 ∧
      3 * 3125 ^ 12 < (3456 : ℕ) ^ 12 := by
  obtain ⟨h₁, h₂, ht, hw, hc⟩ := halving_fixture
  exact ⟨h₁, h₂, ht, hw, hc, finite_exceptional_bound 12 (32 ^ 12) h₁ h₂,
    coefficient_nontrivial⟩

end Erdos1135
