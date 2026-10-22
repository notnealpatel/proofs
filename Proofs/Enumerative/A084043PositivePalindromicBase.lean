/-
Palindromic multiples containing an interior digit string (OEIS A084043;
Amarnath Murthy, May 26 2003; extension by Ray Chandler, Jun 11 2003).

The least-witness-or-zero value for positive palindromic multiples of n
containing the digits of n with at least one digit on each side is zero
iff 10∣n; zero denotes absence.
Digits use Nat.digits 10, hence are little-endian. Reversing both strings
preserves the sandwiched-occurrence condition and palindromicity.
For 10∤n a repeated palindromic block constructs a witness; for 10∣n
the units zero would force a forbidden leading zero.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A084043PositivePalindromicBase

open Finset

/-! ## Definition layer -/

/-- `IsSandwiched n P`: the base-10 digit string of `n` occurs inside the base-10
digit string of `P` with at least one digit of `P` on each side.  Stated on the
little-endian `Nat.digits 10`, which is equivalent to the big-endian reading. -/
def IsSandwiched (n P : ℕ) : Prop :=
  ∃ l r : List ℕ, l ≠ [] ∧ r ≠ [] ∧ Nat.digits 10 P = l ++ Nat.digits 10 n ++ r

/-- `IsWitness n P`: `P` is a palindromic (base 10) multiple of `n` in which the
digit string of `n` appears sandwiched between at least a pair of digits. -/
def IsWitness (n P : ℕ) : Prop :=
  n ∣ P ∧ (Nat.digits 10 P).Palindrome ∧ IsSandwiched n P

/-- OEIS A084043: the smallest `P` with `IsWitness n P`, or `0` if there is none. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ P, IsWitness n P then Nat.find h else 0

/-! ## Examples against the listed terms -/

/-- `111` is a witness for `n = 1` (first term). -/
theorem isWitness_one_111 : IsWitness 1 111 := by
  refine ⟨by norm_num, ?_, [1], [1], by simp, by simp, by norm_num⟩
  rw [show Nat.digits 10 111 = [1, 1, 1] by norm_num]
  exact List.Palindrome.of_reverse_eq rfl

example : IsWitness 12 82128 := by
  refine ⟨by norm_num, ?_, [8], [2, 8], by simp, by simp, by norm_num⟩
  rw [show Nat.digits 10 82128 = [8, 2, 1, 2, 8] by norm_num]
  exact List.Palindrome.of_reverse_eq rfl

example : IsWitness 24 2324232 := by
  refine ⟨by norm_num, ?_, [2, 3, 2], [3, 2], by simp, by simp, by norm_num⟩
  rw [show Nat.digits 10 2324232 = [2, 3, 2, 4, 2, 3, 2] by norm_num]
  exact List.Palindrome.of_reverse_eq rfl

example : IsWitness 38 88388 := by
  refine ⟨by norm_num, ?_, [8], [8, 8], by simp, by simp, by norm_num⟩
  rw [show Nat.digits 10 88388 = [8, 8, 3, 8, 8] by norm_num]
  exact List.Palindrome.of_reverse_eq rfl

/-- No `P < 111` is a witness for `n = 1` (minimality of the first term). -/
theorem le_of_isWitness_one {P : ℕ} (h : IsWitness 1 P) : 111 ≤ P := by
  obtain ⟨-, hpal, l, r, hl, hr, hdig⟩ := h
  have hlen : 3 ≤ (Nat.digits 10 P).length := by
    rw [hdig]
    have hl1 : l.length ≠ 0 := by simpa using hl
    have hr1 : r.length ≠ 0 := by simpa using hr
    simp only [List.length_append, Nat.digits_of_lt 10 1 one_ne_zero (by norm_num),
      List.length_singleton]
    omega
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp at hlen
  have hpow := Nat.base_pow_length_digits_le 10 P (by norm_num) hP0
  have h100 : 100 ≤ P := by
    have h1000 : 10 ^ 3 ≤ 10 ^ (Nat.digits 10 P).length :=
      Nat.pow_le_pow_right (by norm_num) hlen
    omega
  by_contra hlt
  have hrev := hpal.reverse_eq
  interval_cases P <;> try (norm_num at hrev; done)
  rw [show Nat.digits 10 101 = [1, 0, 1] by norm_num,
    Nat.digits_of_lt 10 1 one_ne_zero (by norm_num)] at hdig
  rcases l with _ | ⟨x, _ | ⟨y, l⟩⟩
  · exact hl rfl
  · simp at hdig
  · simp only [List.cons_append, List.cons.injEq] at hdig
    obtain ⟨-, -, hrest⟩ := hdig
    rcases l with _ | ⟨z, l⟩
    · simp only [List.nil_append, List.singleton_append, List.cons.injEq] at hrest
      exact hr hrest.2.symm
    · simp at hrest

/-- `a 1 = 111`, the first listed term. -/
theorem a_one : a 1 = 111 := by
  classical
  have hex : ∃ P, IsWitness 1 P := ⟨111, isWitness_one_111⟩
  rw [a, dif_pos hex, Nat.find_eq_iff]
  exact ⟨isWitness_one_111, fun P hP hw => absurd (le_of_isWitness_one hw) (by omega)⟩

/-! ## Helper lemmas -/

/-- If a list is its own reverse and has head `a`, then its last element is `a`. -/
theorem getLast_eq_of_reverse_eq (L : List ℕ) (a : ℕ) (h : L.reverse = L)
    (hhead : L.head? = some a) (hne : L ≠ []) : L.getLast hne = a := by
  have h1 : L.getLast? = some a := by
    rw [← List.head?_reverse, h, hhead]
  rw [List.getLast?_eq_some_getLast hne] at h1
  exact Option.some.inj h1

/-- (⇒) A witness forces `¬ 10 ∣ n`: otherwise `P` ends in `0`, so the palindrome
`P` would have leading digit `0`. -/
theorem not_ten_dvd_of_isWitness {n P : ℕ} (h : IsWitness n P) : ¬ 10 ∣ n := by
  obtain ⟨hdvd, hpal, l, r, hl, hr, hdig⟩ := h
  intro h10
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp only [Nat.digits_zero, List.append_assoc, List.nil_eq, List.append_eq_nil_iff] at hdig
    exact hl hdig.1
  have hP10 : P % 10 = 0 := Nat.mod_eq_zero_of_dvd (h10.trans hdvd)
  have hhead : (Nat.digits 10 P).head? = some 0 := by
    rw [Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero hP0), hP10]
    rfl
  have hlast := getLast_eq_of_reverse_eq _ 0 hpal.reverse_eq hhead
    (Nat.digits_ne_nil_iff_ne_zero.2 hP0)
  exact Nat.getLast_digit_ne_zero 10 hP0 hlast

/-- A witness is positive (its digit list is nonempty). -/
theorem pos_of_isWitness {n P : ℕ} (h : IsWitness n P) : 0 < P := by
  obtain ⟨-, -, l, r, hl, -, hdig⟩ := h
  rcases Nat.eq_zero_or_pos P with rfl | hP
  · simp only [Nat.digits_zero, List.append_assoc, List.nil_eq, List.append_eq_nil_iff] at hdig
    exact absurd hdig.1 hl
  · exact hP

/-- The value of `t` concatenated copies of a digit list `R`:
`ofDigits b (R^t) = ofDigits b R * ∑_{i<t} (b ^ |R|) ^ i`. -/
theorem ofDigits_flatten_replicate (b : ℕ) (R : List ℕ) (t : ℕ) :
    Nat.ofDigits b (List.replicate t R).flatten =
      Nat.ofDigits b R * ∑ i ∈ range t, (b ^ R.length) ^ i := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [List.replicate_succ, List.flatten_cons, Nat.ofDigits_append, ih, sum_range_succ']
    simp only [pow_succ, ← Finset.sum_mul]
    ring

/-- If `gcd(10, m) = 1` and `0 < L`, some positive-length geometric sum
`∑_{i<t} (10 ^ L) ^ i` is divisible by `m` (Euler's theorem modulo
`m * (10 ^ L - 1)`). -/
theorem exists_dvd_geom_sum (m L : ℕ) (hm : Nat.Coprime 10 m) (hL : 0 < L) :
    ∃ t, 0 < t ∧ m ∣ ∑ i ∈ range t, (10 ^ L) ^ i := by
  set x : ℕ := 10 ^ L with hx
  have hx2 : 2 ≤ x := by
    calc 2 ≤ 10 ^ 1 := by norm_num
      _ ≤ 10 ^ L := Nat.pow_le_pow_right (by norm_num) hL
  have hm0 : m ≠ 0 := by
    rintro rfl
    norm_num at hm
  set M : ℕ := m * (x - 1) with hM
  have hxm1 : 0 < x - 1 := by omega
  have hM0 : 0 < M := Nat.mul_pos (Nat.pos_of_ne_zero hm0) hxm1
  have hcopx : Nat.Coprime x M := by
    refine Nat.Coprime.mul_right (Nat.Coprime.pow_left L hm) ?_
    exact (Nat.coprime_self_sub_right (by omega)).2 (Nat.coprime_one_right x)
  have hmod : x ^ M.totient ≡ 1 [MOD M] := Nat.ModEq.pow_totient hcopx
  have hdvd : M ∣ x ^ M.totient - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).1 hmod.symm
  have hgeom : x ^ M.totient - 1 = (∑ i ∈ range M.totient, x ^ i) * (x - 1) := by
    rw [Nat.geomSum_eq hx2]
    have hd : x - 1 ∣ x ^ M.totient - 1 := Nat.sub_one_dvd_pow_sub_one x M.totient
    exact (Nat.div_mul_cancel hd).symm
  refine ⟨M.totient, Nat.totient_pos.2 hM0, ?_⟩
  rw [hgeom, hM] at hdvd
  exact Nat.dvd_of_mul_dvd_mul_right hxm1 hdvd

/-- Every `n ≠ 0` splits as `n = q * m` with `q ∣ 10 ^ k` (the `{2,5}`-part)
and `gcd(10, m) = 1`. -/
theorem exists_smooth_mul_coprime (n : ℕ) (hn : n ≠ 0) :
    ∃ q m k : ℕ, n = q * m ∧ q ∣ 10 ^ k ∧ Nat.Coprime 10 m := by
  obtain ⟨a, n1, h2, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 2 (by norm_num)
  have hn1 : n1 ≠ 0 := by
    rintro rfl
    simp at h2
  obtain ⟨b, m, h5, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn1 5 (by norm_num)
  refine ⟨2 ^ a * 5 ^ b, m, a + b, by ring, ?_, ?_⟩
  · rw [pow_add]
    exact mul_dvd_mul (pow_dvd_pow_of_dvd (by norm_num) a) (pow_dvd_pow_of_dvd (by norm_num) b)
  · have h2m : ¬ 2 ∣ m := fun h => h2 (Dvd.dvd.mul_left h _)
    have hc2 : Nat.Coprime 2 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2m
    have hc5 : Nat.Coprime 5 m := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h5
    have h10 : (10 : ℕ) = 2 * 5 := by norm_num
    rw [h10]
    exact Nat.Coprime.mul_left hc2 hc5

/-- (⇐) If `¬ 10 ∣ n` then a witness exists: the explicit palindrome built from
`Y = digits q ++ 0^k`, `A = Y ++ digits n`, `R = A ++ reverse A`, repeated `t`
times. -/
theorem exists_isWitness_of_not_ten_dvd (n : ℕ) (h10 : ¬ 10 ∣ n) : ∃ P, IsWitness n P := by
  have hn : 0 < n := Nat.pos_of_ne_zero fun h => h10 (h ▸ dvd_zero 10)
  obtain ⟨q, m, k, hnqm, hqk, hm⟩ := exists_smooth_mul_coprime n hn.ne'
  have hq0 : q ≠ 0 := by
    rintro rfl
    omega
  have hq10 : q % 10 ≠ 0 := fun h =>
    h10 (hnqm ▸ Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h) m)
  set Y : List ℕ := Nat.digits 10 q ++ List.replicate k 0 with hY
  set D : List ℕ := Nat.digits 10 n with hD
  set A : List ℕ := Y ++ D with hA
  set R : List ℕ := A ++ A.reverse with hR
  have hDne : D ≠ [] := Nat.digits_ne_nil_iff_ne_zero.2 hn.ne'
  have hYne : Y ≠ [] := by
    simp [Y, Nat.digits_ne_nil_iff_ne_zero.2 hq0]
  have hDlen : D.length ≠ 0 := by simpa using hDne
  have hRlen : 0 < R.length := by
    simp only [R, A, List.length_append, List.length_reverse]
    omega
  obtain ⟨t, ht, hmt⟩ := exists_dvd_geom_sum m R.length hm hRlen
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  set Lst : List ℕ := (List.replicate (s + 1) R).flatten with hLst_def
  have hRpal : R.reverse = R := by simp [R]
  have hLpal : Lst.reverse = Lst := by
    simp [Lst, List.reverse_flatten, hRpal]
  have hLst : Lst = Y ++ D ++ (D.reverse ++ Y.reverse ++ (List.replicate s R).flatten) := by
    rw [hLst_def, List.replicate_succ, List.flatten_cons]
    simp [R, A]
  have hhead : Lst.head? = some (q % 10) := by
    rw [hLst, hY, Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero hq0)]
    rfl
  have hY10 : ∀ d ∈ Y, d < 10 := by
    intro d hd
    simp only [Y, List.mem_append, List.mem_replicate] at hd
    rcases hd with h | ⟨-, rfl⟩
    · exact Nat.digits_lt_base (by norm_num) h
    · norm_num
  have hD10 : ∀ d ∈ D, d < 10 := fun d hd => Nat.digits_lt_base (by norm_num) hd
  have hR10 : ∀ d ∈ R, d < 10 := by
    intro d hd
    simp only [R, A, List.mem_append, List.mem_reverse] at hd
    rcases hd with (h | h) | (h | h)
    · exact hY10 d h
    · exact hD10 d h
    · exact hY10 d h
    · exact hD10 d h
  have hlt : ∀ d ∈ Lst, d < 10 := by
    intro d hd
    simp only [Lst, List.mem_flatten, List.mem_replicate] at hd
    obtain ⟨l, ⟨-, rfl⟩, hdl⟩ := hd
    exact hR10 d hdl
  have hlast : ∀ h : Lst ≠ [], Lst.getLast h ≠ 0 := fun h => by
    rw [getLast_eq_of_reverse_eq Lst _ hLpal hhead h]
    exact hq10
  have hdig : Nat.digits 10 (Nat.ofDigits 10 Lst) = Lst :=
    Nat.digits_ofDigits 10 (by norm_num) Lst hlt hlast
  have hYval : Nat.ofDigits 10 Y = q := by
    rw [hY, Nat.ofDigits_append, Nat.ofDigits_digits, Nat.ofDigits_replicate_zero, mul_zero,
      add_zero]
  have hkY : k ≤ Y.length := by simp [Y]
  have hqR : q ∣ Nat.ofDigits 10 R := by
    rw [hR, hA, List.append_assoc, Nat.ofDigits_append, hYval]
    exact dvd_add dvd_rfl (Dvd.dvd.mul_right (hqk.trans (pow_dvd_pow 10 hkY)) _)
  refine ⟨Nat.ofDigits 10 Lst, ?_, ?_, ?_⟩
  · rw [hLst_def, ofDigits_flatten_replicate, hnqm]
    exact mul_dvd_mul hqR hmt
  · rw [hdig]
    exact List.Palindrome.of_reverse_eq hLpal
  · refine ⟨Y, D.reverse ++ Y.reverse ++ (List.replicate s R).flatten, hYne, ?_, ?_⟩
    · simp [hDne]
    · rw [hdig, hLst]

/-! ## The conjecture -/

/-- **A084043, existence form.** For every `n`, there is a palindromic (base 10)
multiple of `n` whose digit string contains that of `n` with at least one digit
on each side if and only if `10 ∤ n`.  (At `n = 0` both sides are false, so no
positivity guard is needed; the entry's offset is `1`.) -/
theorem exists_isWitness_iff (n : ℕ) : (∃ P, IsWitness n P) ↔ ¬ 10 ∣ n :=
  ⟨fun ⟨_, hP⟩ => not_ten_dvd_of_isWitness hP, exists_isWitness_of_not_ten_dvd n⟩

/-- The least sandwiched palindromic multiple is zero iff `10∣n`. -/
theorem a_eq_zero_iff (n : ℕ) : a n = 0 ↔ 10 ∣ n := by
  classical
  rw [← not_iff_not, ← exists_isWitness_iff]
  constructor
  · intro ha
    by_contra hne
    exact ha (by rw [a, dif_neg hne])
  · intro hex ha
    rw [a, dif_pos hex] at ha
    exact (pos_of_isWitness (Nat.find_spec hex)).ne' ha

end Candidates.A084043PositivePalindromicBase
