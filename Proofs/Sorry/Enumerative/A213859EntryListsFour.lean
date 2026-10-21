/-
# A213859 — the four conjectures listed in the entry for `2^n mod (n+2)`

## OEIS source (retrieved 2026-10-21 with `oeis show A213859` and oeis.org)

```
NAME:     a(n) = 2^n mod (n+2).
TERMS:    1,2,0,3,4,4,0,2,6,6,4,7,8,2,0,9,16,10,4,2,12,12,16,8,14,20,4,15,16,
          16,0,2,18,22,16,19,20,2,24,21,16,22,4,38,24,24,16,32,6,2,4,27,34,52,
          8,2,30,30,4,31,32,2,0,8,16,34,4,2,46,36,16,37,38,17
KEYWORDS: nonn,easy
AUTHOR:   _Alex Ratushnyak_, Jun 22 2012
COMMENT (verbatim; the conjectures are the author's, Jun 22 2012):
  Conjectures:
  1. Indices of zeros: 2^(x+2)-2, x >= 0.
  2. There are infinitely many n's such that a(n) = n.
  3. Every integer k >= 0 appears in a(n) at least once.
  4. Every k >= 0 appears in a(n) infinitely many times.
```

## Status (triage, 2026-10-21)

Open as a whole, as far as the triage could tell.  Part 1 is elementary
(`n + 2 ∣ 2^n` forces `n + 2` to be a power of two).  Part 2 is proved here
via the tower family `n = 2^(2^(2^i))` (cf. A252606, where `2^(2^k)` being a
term was recorded only empirically for `k = 1, 2, 4, 8, 16`).  Parts 3 and 4
are shifted analogues of Graham's problem on `2^n mod n` (Erdős problem 479,
open): computation to `n < 3·10^6` leaves `k = 13, 25, 71, 89, …` unattained.
Part 4 is the single remaining `sorry`; part 3 is derived from it.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A213859EntryListsFour

/-- OEIS A213859: `a n = 2^n mod (n+2)`. -/
def a (n : ℕ) : ℕ := 2 ^ n % (n + 2)

example : a 0 = 1 := by decide
example : a 1 = 2 := by decide
example : a 2 = 0 := by decide
example : a 3 = 3 := by decide
example : a 4 = 4 := by decide
example : a 6 = 0 := by decide
example : a 11 = 7 := by decide
example : a 16 = 16 := by decide

/-! ## Part 1: indices of zeros -/

/-- **Conjecture 1 of A213859 (proved).** `a n = 0` iff `n = 2^(x+2) - 2` for
some `x ≥ 0`; stated subtraction-free as `n + 2 = 2^(x+2)` (equivalent, since
`2 ≤ 2^(x+2)`). -/
theorem a_eq_zero_iff (n : ℕ) : a n = 0 ↔ ∃ x : ℕ, n + 2 = 2 ^ (x + 2) := by
  unfold a
  constructor
  · intro h
    have hdvd : n + 2 ∣ 2 ^ n := Nat.dvd_of_mod_eq_zero h
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    match k, hk with
    | 0, hk => simp at hk
    | 1, hk =>
      have hn : n = 0 := by simpa using hk
      subst hn
      simp at h
    | k + 2, hk => exact ⟨k, hk⟩
  · rintro ⟨x, hx⟩
    have hle : x + 2 ≤ n := by
      have h4 : 4 * (x + 1) ≤ 4 * 2 ^ x := by
        have hlt : x < 2 ^ x := Nat.lt_two_pow_self
        omega
      have h2 : 2 ^ (x + 2) = 4 * 2 ^ x := by ring
      omega
    rw [hx]
    exact Nat.mod_eq_zero_of_dvd (pow_dvd_pow 2 hle)

/-! ## Part 2: infinitely many fixed points, via the tower `2^(2^(2^i))` -/

/-- If `j ∣ 2^j` then `2^(2^j) ≡ 1 (mod 2^j - 1)`. -/
theorem two_pow_two_pow_modEq_one (j : ℕ) (hj : j ∣ 2 ^ j) :
    2 ^ (2 ^ j) ≡ 1 [MOD 2 ^ j - 1] := by
  have hbase : 2 ^ j ≡ 1 [MOD 2 ^ j - 1] :=
    ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).2 dvd_rfl).symm
  obtain ⟨c, hc⟩ := hj
  calc 2 ^ (2 ^ j) = (2 ^ j) ^ c := by rw [← pow_mul, ← hc]
    _ ≡ 1 ^ c [MOD 2 ^ j - 1] := hbase.pow c
    _ = 1 := one_pow c

/-- The key step: if `2 ≤ m` and `2^m ≡ m (mod 2(m-1))`, then `n = 2^m`
satisfies `2^n mod (n+2) = n`. -/
theorem a_two_pow_of_modEq (m : ℕ) (hm : 2 ≤ m) (h : 2 ^ m ≡ m [MOD 2 * (m - 1)]) :
    a (2 ^ m) = 2 ^ m := by
  unfold a
  set n := 2 ^ m with hn_def
  set x := 2 ^ (m - 1) with hx_def
  have hxn : 2 * x = n := by
    rw [hx_def, hn_def, mul_comm, Nat.two_pow_pred_mul_two (by omega)]
  have hx2 : 2 ∣ x := by
    rw [hx_def]
    exact dvd_pow_self 2 (by omega)
  have hmn : m ≤ n := Nat.lt_two_pow_self.le
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hmn).1 h.symm
  have hnt : n = m + 2 * (m - 1) * t := by omega
  -- `2^(2(m-1)) ≡ 1 (mod x + 1)`
  have hsq : 2 ^ (2 * (m - 1)) ≡ 1 [MOD x + 1] := by
    have hx1 : 1 ≤ x := Nat.one_le_two_pow
    have hpow : 2 ^ (2 * (m - 1)) = x * x := by
      rw [hx_def, ← pow_add]; ring_nf
    rw [hpow]
    refine ((Nat.modEq_iff_dvd' (Nat.one_le_iff_ne_zero.2 (by positivity))).2 ?_).symm
    have hfac : x * x - 1 = (x + 1) * (x - 1) := by
      simpa using Nat.mul_self_sub_mul_self_eq x 1
    rw [hfac]
    exact dvd_mul_right _ _
  have hmodq : 2 ^ n ≡ n [MOD x + 1] := by
    calc 2 ^ n = 2 ^ m * (2 ^ (2 * (m - 1))) ^ t := by
          conv_lhs => rw [hnt]
          rw [pow_add, pow_mul]
      _ ≡ 2 ^ m * 1 ^ t [MOD x + 1] := (hsq.pow t).mul_left _
      _ = n := by rw [one_pow, mul_one]
  have hmod2 : 2 ^ n ≡ n [MOD 2] := by
    have h1 : 2 ^ n ≡ 0 [MOD 2] :=
      Nat.modEq_zero_iff_dvd.2 (dvd_pow_self 2 (by positivity))
    have h2 : n ≡ 0 [MOD 2] := Nat.modEq_zero_iff_dvd.2 ⟨x, hxn.symm⟩
    exact h1.trans h2.symm
  have hcop : Nat.Coprime 2 (x + 1) := by
    rw [Nat.coprime_two_left]
    exact (even_iff_two_dvd.2 hx2).add_one
  have hmod : 2 ^ n ≡ n [MOD 2 * (x + 1)] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨hmod2, hmodq⟩
  have hq : 2 * (x + 1) = n + 2 := by omega
  rw [hq] at hmod
  rw [hmod]
  exact Nat.mod_eq_of_lt (by omega)

/-- Every tower `2^(2^(2^i))` is a fixed point: `a (2^(2^(2^i))) = 2^(2^(2^i))`. -/
theorem a_tower (i : ℕ) : a (2 ^ (2 ^ (2 ^ i))) = 2 ^ (2 ^ (2 ^ i)) := by
  set j := 2 ^ i with hj_def
  set m := 2 ^ j with hm_def
  have hj1 : 1 ≤ j := Nat.one_le_two_pow
  have hm2 : 2 ≤ m := by
    rw [hm_def]
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj1
  have hjdvd : j ∣ 2 ^ j := pow_dvd_pow 2 Nat.lt_two_pow_self.le
  have hmod1 : 2 ^ m ≡ m [MOD m - 1] := by
    have hm1 : m ≡ 1 [MOD m - 1] :=
      ((Nat.modEq_iff_dvd' (by omega)).2 dvd_rfl).symm
    exact (two_pow_two_pow_modEq_one j hjdvd).trans hm1.symm
  have hmod2 : 2 ^ m ≡ m [MOD 2] := by
    have h1 : 2 ^ m ≡ 0 [MOD 2] :=
      Nat.modEq_zero_iff_dvd.2 (dvd_pow_self 2 (by omega))
    have h2 : m ≡ 0 [MOD 2] :=
      Nat.modEq_zero_iff_dvd.2 (by rw [hm_def]; exact dvd_pow_self 2 (by omega))
    exact h1.trans h2.symm
  have hcop : Nat.Coprime 2 (m - 1) := by
    rw [Nat.coprime_two_left]
    have hev : Even m := by
      rw [hm_def]
      exact (Nat.even_pow' (by omega)).2 even_two
    obtain ⟨r, hr⟩ := hev
    exact ⟨r - 1, by omega⟩
  exact a_two_pow_of_modEq m hm2 ((Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨hmod2, hmod1⟩)

/-- **Conjecture 2 of A213859 (proved).** There are infinitely many `n` with
`a n = n`, i.e. `n + 2 ∣ 2^n - n`; the witnesses `2^(2^(2^i))` suffice. -/
theorem infinite_fixed : {n : ℕ | a n = n}.Infinite := by
  have hinj : Function.Injective (fun i : ℕ => 2 ^ (2 ^ (2 ^ i))) :=
    (Nat.pow_right_injective le_rfl).comp
      ((Nat.pow_right_injective le_rfl).comp (Nat.pow_right_injective le_rfl))
  exact Set.infinite_of_injective_forall_mem hinj a_tower

/-! ## Parts 3 and 4: every value, infinitely often (open) -/

/-- **Conjecture 4 of A213859 (open).** Every `k ≥ 0` appears in `a`
infinitely many times. -/
theorem infinite_fiber (k : ℕ) : {n : ℕ | a n = k}.Infinite := by
  -- Remaining goal: `{n : ℕ | 2 ^ n % (n + 2) = k}.Infinite`; a shifted
  -- Graham-type problem (cf. Erdős problem 479), open even for `k = 13`.
  sorry

/-- **Conjecture 3 of A213859 (open; follows from conjecture 4).** Every
integer `k ≥ 0` appears in `a` at least once. -/
theorem exists_eq (k : ℕ) : ∃ n : ℕ, a n = k :=
  (infinite_fiber k).nonempty

/-- **The four conjectures of A213859 (Alex Ratushnyak, Jun 22 2012)**, as one
conjunction: (1) zeros are exactly at `n = 2^(x+2) - 2`; (2) infinitely many
fixed points; (3) every value attained; (4) every value attained infinitely
often.  Parts 1 and 2 are proved; parts 3 and 4 rest on `infinite_fiber`. -/
theorem entry_conjectures :
    (∀ n : ℕ, a n = 0 ↔ ∃ x : ℕ, n + 2 = 2 ^ (x + 2)) ∧
    {n : ℕ | a n = n}.Infinite ∧
    (∀ k : ℕ, ∃ n : ℕ, a n = k) ∧
    (∀ k : ℕ, {n : ℕ | a n = k}.Infinite) :=
  ⟨a_eq_zero_iff, infinite_fixed, exists_eq, infinite_fiber⟩

end Candidates.A213859EntryListsFour
