/-
# A084013 — every `n` has an `n`-digit palindromic multiple

## OEIS source (retrieved with `oeis show A084013` and https://oeis.org/A084013, 2026-10-21)

```
NAME:     Smallest n-digit palindromic multiple of n. For n = 10k it is
          sufficient that the multiple is palindromic with leading zeros
          ignored. 0 if no such number exists.
TERMS:    1,22,111,2112,50005,201102,1002001,21100112,100070001,1000000010,
          10000200001,210000000012,1000029200001,20000055000002,...
KEYWORDS: base,nonn
AUTHOR:   Amarnath Murthy and Meenakshi Srikanth, May 23 2003
          (corrected and extended by Ray Chandler, Jun 08 2003; a(12) corrected
          and more terms from Sean A. Irvine, Mar 02 2026)
COMMENT (the conjecture; the comment carries no author or date on the page):
  Conjecture: no entry is zero.
```

Equivalently: for every `n ≥ 1` there is an `n`-digit palindromic multiple of
`n`, where for `10 ∣ n` the palindrome condition applies after stripping the
trailing zeros ("leading zeros ignored" in the reversed number).

## Status

Triage (2026-10-21): open as far as the entry and its cross-references
A084014/A084015/A084016 show; no literature proof was located (literature not
searched exhaustively, so the statement may be folklore).

## Proof (formalised below, no `sorry`)

Write `n = 10^t * N` with `¬ 10 ∣ N` and `N = p^e * m` with `p ∈ {2, 5}` and
`gcd(m, 10) = 1`.  It suffices to build a palindromic digit list of length
`L = n - t ≥ N` with nonzero leading digit whose value is divisible by `N`, and
then append `t` zeros.  Pigeonhole on geometric sums gives `r ≤ m` with
`m ∣ ∑_{i<r} x^i` for any `x` coprime to `m`.
* `p^e ≤ 9`: the list `c^D 0^(L-2D) c^D` with `c = p^e`, `m ∣ R_D`, when
  `2D ≤ L`; otherwise `p^e = 1` and `1^(L-D) 2^(2D-L) 1^(L-D)` has value
  `R_D (1 + 10^(L-D))`.
* `p^e ≥ 10`: `Y` is `p^e` written with exactly `e` digits, `W = rev(Y) Y` is a
  palindrome divisible by `p^e` (as `p^e ∣ 10^e`), and `U = W^r` with
  `m ∣ ∑_{i<r} 10^(2e i)`; the list `U 0^(L-2|U|) U` fits since `4e ≤ p^e`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A084013ThereDigitPalindromic

open Finset

/-! ## Definition layer -/

/-- `P` is palindromic in base 10: its decimal digit list reads the same reversed. -/
def IsPal (P : ℕ) : Prop := (Nat.digits 10 P).reverse = Nat.digits 10 P

instance : DecidablePred IsPal := fun _ => inferInstanceAs (Decidable (_ = _))

/-- `P` is palindromic in base 10 after stripping its trailing decimal zeros
(`Nat.digits` is little-endian, so trailing zeros of `P` are the leading entries of
the list). This is the entry's "palindromic with leading zeros ignored" for `n = 10k`. -/
def IsPalStripped (P : ℕ) : Prop :=
  ((Nat.digits 10 P).dropWhile (· == 0)).reverse = (Nat.digits 10 P).dropWhile (· == 0)

instance : DecidablePred IsPalStripped := fun _ => inferInstanceAs (Decidable (_ = _))

/-- `P` is an admissible term for A084013 at `n`: `P` has exactly `n` decimal digits,
`n ∣ P`, and `P` is palindromic (after stripping trailing zeros when `10 ∣ n`). -/
def IsWitness (n P : ℕ) : Prop :=
  (Nat.digits 10 P).length = n ∧ n ∣ P ∧ (if 10 ∣ n then IsPalStripped P else IsPal P)

instance (n : ℕ) : DecidablePred (IsWitness n) := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A084013(n): the smallest `n`-digit number `P` (searched over `[10^(n-1), 10^n)`)
that is an admissible palindromic multiple of `n`, and `0` if there is none. -/
def a084013 (n : ℕ) : ℕ :=
  ((List.range' (10 ^ (n - 1)) (10 ^ n - 10 ^ (n - 1))).find?
    (fun P => decide (IsWitness n P))).getD 0

/-! ## Ground truth against the listed terms -/

example : a084013 1 = 1 := by decide
example : a084013 2 = 22 := by decide
example : a084013 3 = 111 := by decide
example : IsWitness 4 2112 := by decide
example : IsWitness 5 50005 := by decide
example : IsWitness 6 201102 := by decide
example : IsWitness 10 1000000010 := by decide
/-- The `n = 10` term is not itself a palindrome: the stripping clause is load-bearing. -/
example : ¬ IsPal 1000000010 := by decide
example : ¬ IsWitness 4 2002 := by decide

/-! ## Digit-list helpers -/

/-- The value of `r` concatenated copies of a digit block `W` is `W * ∑_{i<r} (10^|W|)^i`. -/
theorem ofDigits_flatten_replicate (W : List ℕ) (r : ℕ) :
    Nat.ofDigits 10 (List.replicate r W).flatten =
      Nat.ofDigits 10 W * ∑ i ∈ range r, (10 ^ W.length) ^ i := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.replicate_succ, List.flatten_cons, Nat.ofDigits_append, ih, sum_range_succ',
      mul_add, mul_sum, mul_sum, pow_zero, mul_one, add_comm]
    congr 1
    rw [mul_sum]
    exact sum_congr rfl fun i _ => by ring

/-- A list of zeros has value `0`. -/
theorem ofDigits_replicate_zero (k : ℕ) : Nat.ofDigits 10 (List.replicate k 0) = 0 := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, Nat.ofDigits_cons, ih]

/-- Pigeonhole: if `gcd(m, x) = 1` then `m ∣ ∑_{i<r} x^i` for some `1 ≤ r ≤ m`. -/
theorem exists_geom_dvd (m x : ℕ) (hm : 0 < m) (hx : Nat.Coprime m x) :
    ∃ r, 0 < r ∧ r ≤ m ∧ m ∣ ∑ i ∈ range r, x ^ i := by
  have hcard : (range m).card < (range (m + 1)).card := by simp
  have hmaps : Set.MapsTo (fun j => (∑ i ∈ range j, x ^ i) % m) (range (m + 1) : Set ℕ)
      (range m : Set ℕ) := by
    intro j _
    simpa using Nat.mod_lt _ hm
  obtain ⟨i, hi, j, hj, hij, hmod⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  wlog hlt : i < j generalizing i j
  · exact this j hj i hi hij.symm hmod.symm (lt_of_le_of_ne (not_lt.mp hlt) hij.symm)
  have hsplit : ∑ k ∈ range j, x ^ k = ∑ k ∈ range i, x ^ k + x ^ i * ∑ k ∈ range (j - i), x ^ k := by
    rw [← Nat.add_sub_cancel' hlt.le, sum_range_add, mul_sum, Nat.add_sub_cancel_left]
    simp only [pow_add]
  refine ⟨j - i, by omega, by simp only [mem_range] at hi hj; omega, ?_⟩
  have hdvd : m ∣ x ^ i * ∑ k ∈ range (j - i), x ^ k := by
    have h1 : (∑ k ∈ range i, x ^ k) ≡ ∑ k ∈ range i, x ^ k + x ^ i * ∑ k ∈ range (j - i), x ^ k [MOD m] := by
      rw [← hsplit]; exact hmod
    have h2 : ∑ k ∈ range i, x ^ k + 0 ≡
        ∑ k ∈ range i, x ^ k + x ^ i * ∑ k ∈ range (j - i), x ^ k [MOD m] := by
      simpa using h1
    exact (Nat.modEq_zero_iff_dvd).mp (Nat.ModEq.add_left_cancel' _ h2).symm
  exact (Nat.Coprime.pow_right i hx).dvd_of_dvd_mul_left hdvd

/-- A palindromic list of decimal digits with nonzero first entry is the digit list
of its own value. -/
theorem digits_ofDigits_of_pal (l : List ℕ) (hrev : l.reverse = l)
    (hdig : ∀ x ∈ l, x < 10) (hh : l.head? ≠ some 0) :
    Nat.digits 10 (Nat.ofDigits 10 l) = l := by
  refine Nat.digits_ofDigits 10 (by norm_num) l hdig fun hne hlast => hh ?_
  rw [← hrev, List.head?_reverse, List.getLast?_eq_some_getLast hne, hlast]

/-- Given a palindromic digit block `W` with nonzero first digit and `2 r |W| ≤ L`, the list
`W^r 0^(L - 2r|W|) W^r` is a length-`L` palindrome whose value is divisible by
`W * ∑_{i<r} (10^|W|)^i`. -/
theorem exists_list_of_block (W : List ℕ) (d r L : ℕ) (hWrev : W.reverse = W)
    (hWd : ∀ x ∈ W, x < 10) (hWh : W.head? = some d) (hr : 0 < r)
    (hL : 2 * (r * W.length) ≤ L) :
    ∃ l : List ℕ, l.length = L ∧ l.reverse = l ∧ (∀ x ∈ l, x < 10) ∧ l.head? = some d ∧
      Nat.ofDigits 10 W * ∑ i ∈ range r, (10 ^ W.length) ^ i ∣ Nat.ofDigits 10 l := by
  set U := (List.replicate r W).flatten with hU
  have hUlen : U.length = r * W.length := by simp [hU]
  have hUrev : U.reverse = U := by simp [hU, List.reverse_flatten, hWrev]
  have hUd : ∀ x ∈ U, x < 10 := by
    intro x hx
    simp only [hU, List.mem_flatten, List.mem_replicate] at hx
    obtain ⟨W', ⟨_, rfl⟩, hxW⟩ := hx
    exact hWd x hxW
  have hUh : U.head? = some d := by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    simp [hU, List.replicate_succ, List.head?_append, hWh]
  refine ⟨U ++ List.replicate (L - 2 * U.length) 0 ++ U, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_replicate]
    omega
  · simp [hUrev]
  · intro x hx
    simp only [List.mem_append, List.mem_replicate] at hx
    rcases hx with (hx | ⟨_, rfl⟩) | hx
    · exact hUd x hx
    · norm_num
    · exact hUd x hx
  · rw [List.append_assoc, List.head?_append, hUh]
    rfl
  · rw [← ofDigits_flatten_replicate, ← hU, Nat.ofDigits_append, Nat.ofDigits_append,
      ofDigits_replicate_zero, mul_zero, add_zero]
    exact dvd_add (dvd_refl _) (dvd_mul_left _ _)

/-- The value of `k` copies of the digit `c` is `c * R_k`. -/
theorem ofDigits_replicate (k c : ℕ) :
    Nat.ofDigits 10 (List.replicate k c) = c * ∑ i ∈ range k, 10 ^ i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons, ih, sum_range_succ', mul_add, mul_sum, mul_sum,
      pow_zero, mul_one, add_comm]
    congr 1
    rw [mul_sum]
    exact sum_congr rfl fun i _ => by ring

/-- For `D ≤ L ≤ 2D`, the list `1^(L-D) 2^(2D-L) 1^(L-D)` is a length-`L` palindrome
with value `R_D (1 + 10^(L-D))`, hence divisible by `R_D = ∑_{i<D} 10^i`. -/
theorem exists_list_overlap (D L : ℕ) (hDL : D ≤ L) (hL2 : L ≤ 2 * D) :
    ∃ l : List ℕ, l.length = L ∧ l.reverse = l ∧ (∀ x ∈ l, x < 10) ∧ l.head? ≠ some 0 ∧
      ∑ i ∈ range D, 10 ^ i ∣ Nat.ofDigits 10 l := by
  obtain ⟨s, t, rfl, rfl⟩ : ∃ s t, L = 2 * s + t ∧ D = s + t := ⟨L - D, 2 * D - L, by omega, by omega⟩
  refine ⟨List.replicate s 1 ++ List.replicate t 2 ++ List.replicate s 1, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_replicate]
    omega
  · simp
  · intro x hx
    simp only [List.mem_append, List.mem_replicate] at hx
    omega
  · rcases Nat.eq_zero_or_pos s with rfl | hs
    · rcases Nat.eq_zero_or_pos t with rfl | ht
      · simp
      · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        simp [List.replicate_succ]
    · obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
      simp [List.replicate_succ]
  · have h1 : ∑ i ∈ range (s + t), 10 ^ i =
        ∑ i ∈ range s, 10 ^ i + 10 ^ s * ∑ i ∈ range t, 10 ^ i := by
      rw [sum_range_add, mul_sum]
      simp only [pow_add]
    have h2 : ∑ i ∈ range (t + s), 10 ^ i =
        ∑ i ∈ range t, 10 ^ i + 10 ^ t * ∑ i ∈ range s, 10 ^ i := by
      rw [sum_range_add, mul_sum]
      simp only [pow_add]
    have hval : Nat.ofDigits 10 (List.replicate s 1 ++ List.replicate t 2 ++ List.replicate s 1) =
        ∑ i ∈ range (s + t), 10 ^ i * (1 + 10 ^ s) := by
      rw [← sum_mul, Nat.ofDigits_append, Nat.ofDigits_append, ofDigits_replicate,
        ofDigits_replicate, List.length_append, List.length_replicate, List.length_replicate]
      calc 1 * ∑ i ∈ range s, 10 ^ i + 10 ^ s * (2 * ∑ i ∈ range t, 10 ^ i) +
            10 ^ (s + t) * (1 * ∑ i ∈ range s, 10 ^ i)
          = (∑ i ∈ range s, 10 ^ i + 10 ^ s * ∑ i ∈ range t, 10 ^ i) +
              10 ^ s * (∑ i ∈ range t, 10 ^ i + 10 ^ t * ∑ i ∈ range s, 10 ^ i) := by ring
        _ = (∑ i ∈ range (s + t), 10 ^ i) * (1 + 10 ^ s) := by
          rw [← h1, ← h2, add_comm t s]; ring
    rw [hval, ← sum_mul]
    exact dvd_mul_right _ _

/-- Every positive `N` with `¬ 10 ∣ N` factors as `p^e * m` with `p ∈ {2, 5}` and
`gcd(m, 10) = 1`. -/
theorem exists_decomp (N : ℕ) (hN : 0 < N) (h10 : ¬ 10 ∣ N) :
    ∃ p e m : ℕ, (p = 2 ∨ p = 5) ∧ N = p ^ e * m ∧ Nat.Coprime m 10 := by
  have hcop : ∀ m : ℕ, ¬ 2 ∣ m → ¬ 5 ∣ m → Nat.Coprime m 10 := by
    intro m h2 h5
    have c2 : Nat.Coprime m 2 :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2)
    have c5 : Nat.Coprime m 5 :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h5)
    simpa using Nat.Coprime.mul_right c2 c5
  by_cases h5 : 5 ∣ N
  · have h2 : ¬ 2 ∣ N := fun h2 => h10 (by omega)
    obtain ⟨e, m, hm5, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' 5 (by norm_num)
    exact ⟨5, e, m, Or.inr rfl, rfl, hcop m (fun h => h2 (h.mul_left _)) hm5⟩
  · obtain ⟨e, m, hm2, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' 2 (by norm_num)
    exact ⟨2, e, m, Or.inl rfl, rfl, hcop m hm2 (fun h => h5 (h.mul_left _))⟩

/-- For `p ∈ {2, 5}` and `10 ≤ p^e`, `4e ≤ p^e`. -/
theorem four_mul_le_pow (p e : ℕ) (hp : p = 2 ∨ p = 5) (h : 10 ≤ p ^ e) : 4 * e ≤ p ^ e := by
  rcases hp with rfl | rfl
  · have he : 4 ≤ e := by
      by_contra hlt
      interval_cases e <;> norm_num at h
    induction e, he using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      have hk4 : 4 ≤ 2 ^ k := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
      rw [pow_succ]
      have := ih (by
        have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
        omega)
      omega
  · clear h
    induction e with
    | zero => norm_num
    | succ k ih =>
      have : 1 ≤ 5 ^ k := Nat.one_le_pow _ _ (by norm_num)
      rw [pow_succ]
      omega

/-- Key lemma: for positive `N` with `¬ 10 ∣ N` and `N ≤ L` there is a palindromic list of
`L` decimal digits with nonzero first entry whose value is divisible by `N`. -/
theorem exists_good_list (N L : ℕ) (hN : 0 < N) (h10 : ¬ 10 ∣ N) (hL : N ≤ L) :
    ∃ l : List ℕ, l.length = L ∧ l.reverse = l ∧ (∀ x ∈ l, x < 10) ∧ l.head? ≠ some 0 ∧
      N ∣ Nat.ofDigits 10 l := by
  obtain ⟨p, e, m, hp, rfl, hm⟩ := exists_decomp N hN h10
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hN)
  have hpe0 : 0 < p ^ e := Nat.pos_of_ne_zero (by rintro h; simp [h] at hN)
  by_cases hsmall : p ^ e ≤ 9
  · obtain ⟨D, hD0, hDm, hdvd⟩ := exists_geom_dvd m 10 hm0 hm
    by_cases h2D : 2 * D ≤ L
    · obtain ⟨l, hlen, hrev, hdig, hhead, hldvd⟩ :=
        exists_list_of_block [p ^ e] (p ^ e) D L (by simp) (by simp only [List.mem_singleton]; omega) (by simp) hD0
          (by simpa using h2D)
      refine ⟨l, hlen, hrev, hdig, by rw [hhead]; simpa using hpe0.ne', ?_⟩
      refine dvd_trans ?_ hldvd
      simpa using mul_dvd_mul_left (p ^ e) hdvd
    · have hpe1 : p ^ e = 1 := by
        by_contra hne
        have h2 : 2 * m ≤ p ^ e * m := Nat.mul_le_mul_right m (by omega)
        omega
      obtain ⟨l, hlen, hrev, hdig, hhead, hldvd⟩ :=
        exists_list_overlap D L (by rw [hpe1] at hL; omega) (by omega)
      exact ⟨l, hlen, hrev, hdig, hhead, by rw [hpe1, one_mul]; exact dvd_trans hdvd hldvd⟩
  · have hbig : 10 ≤ p ^ e := by omega
    have he0 : e ≠ 0 := by rintro rfl; simp at hbig
    have hp10 : p < 10 := by rcases hp with rfl | rfl <;> norm_num
    have hlt : p ^ e < 10 ^ e := Nat.pow_lt_pow_left hp10 he0
    have hYlen' : (Nat.digits 10 (p ^ e)).length ≤ e :=
      (Nat.digits_length_le_iff (by norm_num) (p ^ e)).mpr hlt
    set Y := Nat.digits 10 (p ^ e) ++ List.replicate (e - (Nat.digits 10 (p ^ e)).length) 0
      with hY
    have hYlen : Y.length = e := by
      simp only [hY, List.length_append, List.length_replicate]
      omega
    have hYval : Nat.ofDigits 10 Y = p ^ e := by
      rw [hY, Nat.ofDigits_append, ofDigits_replicate_zero, mul_zero, add_zero,
        Nat.ofDigits_digits]
    have hp10dvd : ¬ 10 ∣ p ^ e := fun h => h10 (dvd_mul_of_dvd_left h m)
    have hYhead : Y.head? = some (p ^ e % 10) := by
      rw [hY, Nat.digits_def' (by norm_num) hpe0]
      rfl
    set W := Y ++ Y.reverse with hW
    have hWlen : W.length = 2 * e := by
      simp only [hW, List.length_append, List.length_reverse, hYlen]
      ring
    have hpe_dvd : p ^ e ∣ 10 ^ e := pow_dvd_pow_of_dvd (by rcases hp with rfl | rfl <;> norm_num) e
    have hWdvd : p ^ e ∣ Nat.ofDigits 10 W := by
      rw [hW, Nat.ofDigits_append, hYval, hYlen]
      exact dvd_add (dvd_refl _) (dvd_mul_of_dvd_left hpe_dvd _)
    obtain ⟨r, hr0, hrm, hrdvd⟩ := exists_geom_dvd m (10 ^ W.length) hm0 (Nat.Coprime.pow_right _ hm)
    have h4e := four_mul_le_pow p e hp hbig
    have hrL : 2 * (r * W.length) ≤ L := by
      rw [hWlen]
      have : 4 * e * r ≤ p ^ e * m := Nat.mul_le_mul h4e hrm
      nlinarith
    obtain ⟨l, hlen, hrev, hdig, hhead, hldvd⟩ :=
      exists_list_of_block W (p ^ e % 10) r L (by simp [hW])
        (by
          intro x hx
          simp only [hW, hY, List.mem_append, List.mem_reverse, List.mem_replicate] at hx
          rcases hx with (hx | ⟨_, rfl⟩) | (hx | ⟨_, rfl⟩)
          · exact Nat.digits_lt_base (by norm_num) hx
          · norm_num
          · exact Nat.digits_lt_base (by norm_num) hx
          · norm_num)
        (by rw [hW, List.head?_append, hYhead]; rfl) hr0 hrL
    refine ⟨l, hlen, hrev, hdig, by rw [hhead]; simpa [Nat.dvd_iff_mod_eq_zero] using hp10dvd, ?_⟩
    exact dvd_trans (mul_dvd_mul hWdvd hrdvd) hldvd

/-- Stripping leading zeros from `0^t ++ l` returns `l` when `l` does not start with `0`. -/
theorem dropWhile_replicate_zero_append (t : ℕ) (l : List ℕ) (hl : l.head? ≠ some 0) :
    (List.replicate t 0 ++ l).dropWhile (· == 0) = l := by
  induction t with
  | zero =>
    cases l with
    | nil => rfl
    | cons a l' =>
      have ha : a ≠ 0 := fun h => hl (by simp [h])
      simp [ha]
  | succ t ih => simpa [List.replicate_succ, List.dropWhile_cons] using ih

/-- For every `n ≥ 1` there is an `n`-digit palindromic multiple of `n` (palindromic after
stripping trailing zeros when `10 ∣ n`). -/
theorem exists_witness (n : ℕ) (hn : 0 < n) : ∃ P, IsWitness n P := by
  obtain ⟨t, N, hN10, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' 10 (by norm_num)
  have hN : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have ht : t < 10 ^ t := Nat.lt_pow_self (by norm_num)
  have hNt : N + t ≤ 10 ^ t * N := by nlinarith
  obtain ⟨l, hlen, hrev, hdig, hhead, hdvd⟩ :=
    exists_good_list N (10 ^ t * N - t) hN hN10 (by omega)
  have hQ : Nat.digits 10 (Nat.ofDigits 10 l) = l := digits_ofDigits_of_pal l hrev hdig hhead
  have hQ0 : 0 < Nat.ofDigits 10 l := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0, Nat.digits_zero] at hQ
    rw [← hQ] at hlen
    simp only [List.length_nil] at hlen
    omega
  have hP : Nat.digits 10 (10 ^ t * Nat.ofDigits 10 l) = List.replicate t 0 ++ l := by
    rw [Nat.digits_base_pow_mul (by norm_num) hQ0, hQ]
  refine ⟨10 ^ t * Nat.ofDigits 10 l, ?_, mul_dvd_mul_left _ hdvd, ?_⟩
  · rw [hP, List.length_append, List.length_replicate, hlen]
    omega
  · split_ifs with h10
    · unfold IsPalStripped
      rw [hP, dropWhile_replicate_zero_append t l hhead, hrev]
    · have ht0 : t = 0 := by
        by_contra hne
        exact h10 (dvd_mul_of_dvd_left (dvd_pow_self 10 hne) N)
      subst ht0
      unfold IsPal
      rw [hP, List.replicate_zero, List.nil_append, hrev]

/-- For `n ≥ 1`, `a084013 n` is an admissible term, i.e. the search in its definition succeeds. -/
theorem isWitness_a084013 (n : ℕ) (hn : 0 < n) : IsWitness n (a084013 n) := by
  obtain ⟨P, hP⟩ := exists_witness n hn
  have hmem : P ∈ List.range' (10 ^ (n - 1)) (10 ^ n - 10 ^ (n - 1)) := by
    have hlt : P < 10 ^ n := (Nat.digits_length_le_iff (by norm_num) P).mp hP.1.le
    have hge : 10 ^ (n - 1) ≤ P := by
      by_contra hlt'
      have hle := (Nat.digits_length_le_iff (by norm_num) P).mpr (not_le.mp hlt')
      have hlen := hP.1
      omega
    rw [List.mem_range'_1]
    omega
  have hsome : ((List.range' (10 ^ (n - 1)) (10 ^ n - 10 ^ (n - 1))).find?
      (fun P => decide (IsWitness n P))).isSome := by
    rw [List.find?_isSome]
    exact ⟨P, hmem, by simpa using hP⟩
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
  have hxW : IsWitness n x := by simpa using List.find?_some hx
  unfold a084013
  rw [hx, Option.getD_some]
  exact hxW

/-! ## The conjecture -/

/-- **A084013 conjecture** (OEIS A084013 comment, entry by Amarnath Murthy and
Meenakshi Srikanth, May 23 2003): "Conjecture: no entry is zero." That is, for every
`n ≥ 1` there is an `n`-digit palindromic multiple of `n` (palindromic after stripping
trailing zeros when `10 ∣ n`), so A084013(n) ≠ 0. Proved here. -/
theorem a084013_ne_zero (n : ℕ) (hn : 0 < n) : a084013 n ≠ 0 := by
  intro h0
  have hW := isWitness_a084013 n hn
  rw [h0, IsWitness, Nat.digits_zero, List.length_nil] at hW
  omega

end Candidates.A084013ThereDigitPalindromic
