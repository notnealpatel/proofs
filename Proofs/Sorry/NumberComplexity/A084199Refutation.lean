/-
# A084199 — the range conjecture is false

## OEIS source (retrieved with `oeis show A084199` and https://oeis.org/A084199, 2026-10-21)

```
A084199
NAME:     Smallest prime q < prime(n) such that q+1 divides prime(n)+1,
          a(n) = 1 if no such q exists.
OFFSET:   1,3
TERMS:    1,1,2,3,2,1,2,3,2,2,3,1,2,3,2,2,2,1,3,2,1,3,2,2,13,2,3,2,1,2,...
COMMENT:  Conjecture: A008578 is the range of values (or A000040 = range of
          values > 1).
AUTHOR:   Reinhard Zumkeller, May 18 2003
```

The comment is unsigned, so it carries the entry author's attribution
(Reinhard Zumkeller, May 18 2003). A008578 is `{1} ∪ primes`. No later
comment retracts the conjecture.

## Verdict

This module refutes the conjecture. `5` is never a value: if `6 ∣ p + 1`
then `3 ∣ p + 1`, so the prime `2 < 5` already qualifies. The same argument
excludes every prime `q` for which some smaller prime `r` has
`(r + 1) ∣ (q + 1)`. The values that do occur are `1` together with the
primes having no such smaller `r` (A082539: 2, 3, 13, 37, 61, 73, ...);
`range_eq` proves this corrected description, with Dirichlet's theorem on
primes in arithmetic progressions supplying the reverse inclusion.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A084199Refutation

/-- `a p` is the least prime `q < p` with `(q + 1) ∣ (p + 1)`, or `1` if
there is no such prime. The OEIS term is `A084199(n) = a (prime(n))`. -/
noncomputable def a (p : ℕ) : ℕ := by
  classical
  exact if h : ∃ q, q.Prime ∧ q < p ∧ (q + 1) ∣ (p + 1) then Nat.find h else 1

/-- The OEIS sequence with zero-based index: `seq n = A084199(n + 1)`, the
value of `a` at the `(n + 1)`-st prime `Nat.nth Nat.Prime n`. -/
noncomputable def seq (n : ℕ) : ℕ := a (Nat.nth Nat.Prime n)

/-- Characterization of a nontrivial value: `a p = q` whenever `q` is a prime
below `p` with `(q + 1) ∣ (p + 1)` and no smaller prime qualifies. -/
theorem a_eq_of {p q : ℕ} (hq : q.Prime) (hqp : q < p) (hdvd : (q + 1) ∣ (p + 1))
    (hmin : ∀ r < q, r.Prime → ¬ (r + 1) ∣ (p + 1)) : a p = q := by
  classical
  have hex : ∃ q, q.Prime ∧ q < p ∧ (q + 1) ∣ (p + 1) := ⟨q, hq, hqp, hdvd⟩
  unfold a
  rw [dif_pos hex, Nat.find_eq_iff]
  refine ⟨⟨hq, hqp, hdvd⟩, ?_⟩
  rintro r hr ⟨hrp, -, hrdvd⟩
  exact hmin r hr hrp hrdvd

/-- Characterization of the default value: `a p = 1` when no prime `q < p`
has `(q + 1) ∣ (p + 1)`. -/
theorem a_eq_one_of {p : ℕ} (h : ∀ q < p, q.Prime → ¬ (q + 1) ∣ (p + 1)) : a p = 1 := by
  classical
  have hne : ¬ ∃ q, q.Prime ∧ q < p ∧ (q + 1) ∣ (p + 1) := by
    rintro ⟨q, hq, hqp, hdvd⟩
    exact h q hqp hq hdvd
  unfold a
  rw [dif_neg hne]

/-! ## Ground truth against the DATA line `1, 1, 2, 3, 2, 1, ..., 13 (n = 25)` -/

example : seq 0 = 1 := by
  rw [seq, Nat.nth_prime_zero_eq_two]
  exact a_eq_one_of (by decide)

example : seq 1 = 1 := by
  rw [seq, Nat.nth_prime_one_eq_three]
  exact a_eq_one_of (by decide)

example : seq 2 = 2 := by
  rw [seq, Nat.nth_prime_two_eq_five]
  exact a_eq_of Nat.prime_two (by norm_num) (by norm_num) (by decide)

example : seq 3 = 3 := by
  rw [seq, Nat.nth_prime_three_eq_seven]
  exact a_eq_of Nat.prime_three (by norm_num) (by norm_num) (by decide)

example : seq 4 = 2 := by
  rw [seq, Nat.nth_prime_four_eq_eleven]
  exact a_eq_of Nat.prime_two (by norm_num) (by norm_num) (by decide)

/-- `A084199(6) = a 13 = 1`. -/
example : a 13 = 1 := a_eq_one_of (by decide)

/-- `A084199(25) = a 97 = 13`, the first value other than `1, 2, 3`. -/
example : a 97 = 13 := a_eq_of (by norm_num) (by norm_num) (by norm_num) (by decide)

/-! ## The conjecture and its refutation -/

/-- **Zumkeller's conjecture (A084199, May 18 2003).** Verbatim: "Conjecture:
A008578 is the range of values (or A000040 = range of values > 1)." Here
A008578 is `{1} ∪ primes`, and the values are `a p` over the primes `p`,
enumerated as `Nat.nth Nat.Prime n`. -/
def Conjecture : Prop :=
  Set.range seq = {m : ℕ | m = 1 ∨ m.Prime}

/-- `a p` never equals `5`: a prime `q = 5` would give `6 ∣ p + 1`, hence
`3 ∣ p + 1` with the smaller prime `2 < p`. -/
theorem a_ne_five (p : ℕ) : a p ≠ 5 := by
  classical
  unfold a
  split_ifs with hex
  · intro h5
    have hspec := Nat.find_spec hex
    rw [h5] at hspec
    obtain ⟨-, h5p, h6⟩ := hspec
    have h3 : (2 + 1) ∣ (p + 1) := Nat.dvd_trans (by norm_num) h6
    have hle : Nat.find hex ≤ 2 := Nat.find_min' hex ⟨Nat.prime_two, by omega, h3⟩
    omega
  · norm_num

/-- **Refutation of the A084199 range conjecture.** The prime `5` lies in
A008578 but is never a value of the sequence (`a_ne_five`). The author
presumably intended the range to be `{1}` together with the primes `q` having
no smaller prime `r` with `(r + 1) ∣ (q + 1)` (A082539); see `range_eq`. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  have h5 : (5 : ℕ) ∈ {m : ℕ | m = 1 ∨ m.Prime} := Or.inr Nat.prime_five
  rw [← hconj] at h5
  obtain ⟨n, hn⟩ := h5
  exact a_ne_five _ hn

/-! ## The corrected range -/

/-- The primes that can be values: primes `q` such that no smaller prime `r`
has `(r + 1) ∣ (q + 1)` (OEIS A082539). -/
def Corrected (q : ℕ) : Prop :=
  q.Prime ∧ ∀ r, r.Prime → r < q → ¬ (r + 1) ∣ (q + 1)

example : Corrected 13 := by
  have hsmall : ∀ r < 13, r.Prime → ¬ (r + 1) ∣ (13 + 1) := by decide
  exact ⟨by norm_num, fun r hr hr13 => hsmall r hr13 hr⟩
example : ¬ Corrected 5 := fun h => h.2 2 Nat.prime_two (by norm_num) (by norm_num)

/-- Every value `a p` (for any `p`, in particular any prime) is `1` or a prime in
`Corrected`. -/
theorem a_mem_corrected {p : ℕ} : a p = 1 ∨ Corrected (a p) := by
  classical
  unfold a
  split_ifs with hex
  · right
    obtain ⟨hq, hqp, hqdvd⟩ := Nat.find_spec hex
    refine ⟨hq, fun r hr hrq hrdvd => ?_⟩
    exact Nat.find_min hex hrq ⟨hr, hrq.trans hqp, Nat.dvd_trans hrdvd hqdvd⟩
  · left
    rfl

/-- Every prime in `Corrected` is attained as `a p` at some prime `p`. The
cases `q = 2, 3` use `p = 5, 7`; for `q ≥ 5` Dirichlet's theorem supplies a
prime `p > q` with `p ≡ q [MOD (q - 1)! * (q + 1)]`. -/
theorem exists_prime_a_eq {q : ℕ} (hq : Corrected q) : ∃ p, p.Prime ∧ a p = q := by
  obtain ⟨hqprime, hqmin⟩ := hq
  have hq2 : 2 ≤ q := hqprime.two_le
  rcases (show q = 2 ∨ q = 3 ∨ q = 4 ∨ 5 ≤ q by omega) with h | h | h | h5
  · subst h
    exact ⟨5, Nat.prime_five, a_eq_of Nat.prime_two (by norm_num) (by norm_num) (by decide)⟩
  · subst h
    exact ⟨7, by norm_num, a_eq_of Nat.prime_three (by norm_num) (by norm_num) (by decide)⟩
  · subst h
    exact absurd hqprime (by norm_num)
  · let M : ℕ := (q - 1).factorial * (q + 1)
    have hM : M ≠ 0 := by positivity
    have hcopFact : q.Coprime (q - 1).factorial := by
      rw [hqprime.coprime_iff_not_dvd, hqprime.dvd_factorial]
      omega
    have hcopSucc : q.Coprime (q + 1) :=
      Nat.coprime_self_add_right.2 (Nat.coprime_one_right q)
    have hcop : q.Coprime M := Nat.Coprime.mul_right hcopFact hcopSucc
    obtain ⟨p, hpq, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq q hM hcop
    have hmod1 : p + 1 ≡ q + 1 [MOD M] := hmod.add_right 1
    refine ⟨p, hp, a_eq_of hqprime hpq ?_ ?_⟩
    · exact (hmod1.dvd_iff (Nat.dvd_mul_left (q + 1) (q - 1).factorial)).2 dvd_rfl
    · intro r hrq hr hrdvd
      have hrle : r + 1 ≤ q - 1 := by
        by_contra hcon
        have hrodd : Odd r := hr.odd_of_ne_two (by omega)
        have hqodd : Odd q := hqprime.odd_of_ne_two (by omega)
        obtain ⟨k, hk⟩ := hrodd
        obtain ⟨l, hl⟩ := hqodd
        omega
      have hrM : (r + 1) ∣ M :=
        Nat.dvd_trans (Nat.dvd_factorial (by omega) hrle) (Nat.dvd_mul_right _ _)
      exact hqmin r hr hrq ((hmod1.dvd_iff hrM).1 hrdvd)

/-- **Corrected form of the A084199 range statement.** The set of values of
the sequence is exactly `{1}` together with the primes `q` that have no
smaller prime `r` with `(r + 1) ∣ (q + 1)` (A082539). -/
theorem range_eq : Set.range seq = {m : ℕ | m = 1 ∨ Corrected m} := by
  ext m
  constructor
  · rintro ⟨n, rfl⟩
    exact a_mem_corrected
  · rintro (rfl | hm)
    · refine ⟨0, ?_⟩
      rw [seq, Nat.nth_prime_zero_eq_two]
      exact a_eq_one_of (by decide)
    · obtain ⟨p, hp, hpa⟩ := exists_prime_a_eq hm
      have hprange : p ∈ Set.range (Nat.nth Nat.Prime) := by
        rw [Nat.range_nth_of_infinite Nat.infinite_setOfPred_prime]
        exact hp
      obtain ⟨n, hn⟩ := hprange
      exact ⟨n, by rw [seq, hn, hpa]⟩

end Candidates.A084199Refutation
