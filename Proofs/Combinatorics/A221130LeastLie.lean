/-
# A221130 — Krizek: least start of a run of `n` consecutive members of A221129

Jaroslav Krizek's conjecture in OEIS A221130 (January 2, 2013) identifies
`2^(2n-1) + n` as the least start of a run of `n ≥ 1` consecutive members
of A221129, the numbers `h*2^m + m` with `m ≥ 1` and `1 ≤ h < 2^m`.

## Proof outline (proved below)

* Key lemma `succ_rep_index`: if `x = h*2^a + a` and `x + 1 = k*2^b + b` are
  admissible representations, then `b = a + 1`.  Otherwise `2^min(a,b)` divides
  the nonzero `|a + 1 - b|`, which pushes the larger index past twice the smaller
  one and contradicts `h*2^a < 4^a` (resp. `k*2^b < 4^b`).
* Hence along a run starting at `w = h0*2^m0 + m0` the value `x - m` is constant
  and the index of `w + i` is `m0 + i`.  At `i = n - 1`, `2^(m0+n-1) ≤ h0*2^m0 <
  4^m0` forces `n ≤ m0`, so `w ≥ 2^(2n-1) + n`.
* The run `2^(2n-1) + n + i = 2^(n-1-i) * 2^(n+i) + (n+i)` attains the bound.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A221130LeastLie

/-- Key lemma (consecutive members): if `h * 2^a + a + 1 = k * 2^b + b` with both representations admissible,
then `b = a + 1`. -/
theorem succ_rep_index {a b h k : ℕ} (hh1 : 1 ≤ h) (hh2 : h < 2 ^ a)
    (hk1 : 1 ≤ k) (hk2 : k < 2 ^ b) (heq : h * 2 ^ a + a + 1 = k * 2 ^ b + b) : b = a + 1 := by
  rcases lt_trichotomy b (a + 1) with hlt | heq' | hgt
  · -- `b ≤ a`
    exfalso
    have hba : b ≤ a := by omega
    have hdvd : 2 ^ b ∣ h * 2 ^ a := Dvd.dvd.mul_left (pow_dvd_pow 2 hba) h
    have hsum : h * 2 ^ a + (a + 1 - b) = k * 2 ^ b := by omega
    have hdvd2 : 2 ^ b ∣ a + 1 - b := by
      have hk : 2 ^ b ∣ k * 2 ^ b := Dvd.intro_left k rfl
      rw [← hsum] at hk
      exact (Nat.dvd_add_right hdvd).mp hk
    have hpos : 0 < a + 1 - b := by omega
    have hle : 2 ^ b ≤ a + 1 - b := Nat.le_of_dvd hpos hdvd2
    have hb2 : b + 1 ≤ 2 ^ b := Nat.lt_two_pow_self
    have h2b : 2 * b ≤ a := by omega
    have hpow : 2 ^ (2 * b) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) h2b
    have hka : k * 2 ^ b < 2 ^ (2 * b) := by
      rw [two_mul, pow_add]
      exact Nat.mul_lt_mul_of_pos_right hk2 (by positivity)
    have hha : 2 ^ a ≤ h * 2 ^ a := Nat.le_mul_of_pos_left _ hh1
    omega
  · exact heq'
  · exfalso
    have hab : a ≤ b := by omega
    have hdvd : 2 ^ a ∣ k * 2 ^ b := Dvd.dvd.mul_left (pow_dvd_pow 2 hab) k
    have hsum : k * 2 ^ b + (b - a - 1) = h * 2 ^ a := by omega
    have hdvd2 : 2 ^ a ∣ b - a - 1 := by
      have hh : 2 ^ a ∣ h * 2 ^ a := Dvd.intro_left h rfl
      rw [← hsum] at hh
      exact (Nat.dvd_add_right hdvd).mp hh
    have hpos : 0 < b - a - 1 := by omega
    have hle : 2 ^ a ≤ b - a - 1 := Nat.le_of_dvd hpos hdvd2
    have ha2 : a + 1 ≤ 2 ^ a := Nat.lt_two_pow_self
    have h2a : 2 * a ≤ b := by omega
    have hpow : 2 ^ (2 * a) ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h2a
    have hha : h * 2 ^ a < 2 ^ (2 * a) := by
      rw [two_mul, pow_add]
      exact Nat.mul_lt_mul_of_pos_right hh2 (by positivity)
    have hkb : 2 ^ b ≤ k * 2 ^ b := Nat.le_mul_of_pos_left _ hk1
    omega


/-- Membership in `T`: `x = h * 2^m + m` for some `m ≥ 1` and `1 ≤ h < 2^m` (OEIS A221129). -/
def InT (x : ℕ) : Prop :=
  ∃ m h : ℕ, 1 ≤ m ∧ 1 ≤ h ∧ h < 2 ^ m ∧ x = h * 2 ^ m + m

/-- Bounded form of `InT`: both the index `m` and the multiplier `h` are below `x`. -/
theorem inT_iff_bounded (x : ℕ) :
    InT x ↔ ∃ m < x, ∃ h < x, 1 ≤ m ∧ 1 ≤ h ∧ h < 2 ^ m ∧ x = h * 2 ^ m + m := by
  constructor
  · rintro ⟨m, h, hm, hh1, hh2, hx⟩
    have hpow : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have hhm : 2 * h ≤ h * 2 ^ m := by
      rw [mul_comm 2 h]
      exact Nat.mul_le_mul_left h hpow
    exact ⟨m, by omega, h, by omega, hm, hh1, hh2, hx⟩
  · rintro ⟨m, -, h, -, hm, hh1, hh2, hx⟩
    exact ⟨m, h, hm, hh1, hh2, hx⟩

/-- Decidability of `InT` through the bounded form `inT_iff_bounded`. -/
instance : DecidablePred InT := fun x => decidable_of_iff _ (inT_iff_bounded x).symm

/-- The members of `T` below `30` are the first terms of A221129. -/
example : (List.range 30).filter (fun x => decide (InT x)) = [3, 6, 10, 11, 14, 19, 20, 27] := by
  decide

/-- The OEIS sequence A221130: `a(n) = 2^(2n-1) + n` (for `n ≥ 1`). -/
def a (n : ℕ) : ℕ := 2 ^ (2 * n - 1) + n

/-- The first listed terms of A221130. -/
example : (List.range 6).map (fun i => a (i + 1)) = [3, 10, 35, 132, 517, 2054] := by decide

/-- The run `517, ..., 521` from the entry's example comment. -/
example : ∀ i < 5, InT (517 + i) := by
  intro i hi
  interval_cases i
  · exact ⟨5, 16, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨6, 8, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, 4, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨8, 2, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨9, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chain lemma: along a run of members of `T` starting at `w = h0 * 2^m0 + m0`, the element
`w + i` has a representation with index `m0 + i` and the same value of `x - m`. -/
theorem run_chain {w m0 h0 n : ℕ} (hw : w = h0 * 2 ^ m0 + m0)
    (hh01 : 1 ≤ h0) (hh02 : h0 < 2 ^ m0) (hrun : ∀ i < n, InT (w + i)) :
    ∀ i < n, ∃ k : ℕ, 1 ≤ k ∧ k < 2 ^ (m0 + i) ∧ w + i = k * 2 ^ (m0 + i) + (m0 + i) ∧
      k * 2 ^ (m0 + i) = h0 * 2 ^ m0 := by
  intro i
  induction i with
  | zero => exact fun _ => ⟨h0, hh01, hh02, hw, rfl⟩
  | succ i ih =>
    intro hi
    obtain ⟨k, hk1, hk2, hkw, hkeq⟩ := ih (by omega)
    obtain ⟨b, k', hb, hk'1, hk'2, hk'w⟩ := hrun (i + 1) hi
    have hidx : b = m0 + (i + 1) :=
      succ_rep_index (a := m0 + i) hk1 hk2 hk'1 hk'2 (by omega)
    subst hidx
    exact ⟨k', hk'1, hk'2, hk'w, by omega⟩

/-- Upper half: `2^(2n-1) + n, ..., 2^(2n-1) + 2n - 1` all lie in `T`, via
`2^(2n-1) + n + i = 2^(n-1-i) * 2^(n+i) + (n+i)`. -/
theorem run_mem {n : ℕ} (hn : 1 ≤ n) : ∀ i < n, InT (2 ^ (2 * n - 1) + n + i) := by
  intro i hi
  refine ⟨n + i, 2 ^ (n - 1 - i), by omega, Nat.one_le_two_pow, ?_, ?_⟩
  · exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · have hexp : 2 * n - 1 = (n - 1 - i) + (n + i) := by omega
    rw [hexp, pow_add]
    ring

/-- Lower half: any run of `n ≥ 1` consecutive members of `T` starts at `w ≥ 2^(2n-1) + n`. -/
theorem le_of_run {n w : ℕ} (hn : 1 ≤ n) (hrun : ∀ i < n, InT (w + i)) :
    2 ^ (2 * n - 1) + n ≤ w := by
  obtain ⟨m0, h0, -, hh01, hh02, hw⟩ := by simpa using hrun 0 (by omega)
  obtain ⟨k, hk1, -, -, hkeq⟩ := run_chain hw hh01 hh02 hrun (n - 1) (by omega)
  have hlow : 2 ^ (m0 + (n - 1)) ≤ h0 * 2 ^ m0 := by
    rw [← hkeq]
    exact Nat.le_mul_of_pos_left _ hk1
  have hhigh : h0 * 2 ^ m0 < 2 ^ (m0 + m0) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_right hh02 (by positivity)
  have hexp : m0 + (n - 1) < m0 + m0 :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_le_of_lt hlow hhigh)
  have hpow : 2 ^ (2 * n - 1) ≤ 2 ^ (m0 + (n - 1)) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- **Krizek's conjecture (A221130, Jaroslav Krizek, Jan 02 2013).**
For every `n ≥ 1`, the least `w` such that `w, w+1, ..., w+n-1` all lie in
`T = {h*2^m + m : m ≥ 1, 1 ≤ h < 2^m}` (A221129) is `a(n) = 2^(2n-1) + n`. -/
theorem a221130_isLeast (n : ℕ) (hn : 1 ≤ n) :
    IsLeast {w : ℕ | ∀ i < n, InT (w + i)} (a n) :=
  ⟨run_mem hn, fun _ hw => le_of_run hn hw⟩

end Candidates.A221130LeastLie
