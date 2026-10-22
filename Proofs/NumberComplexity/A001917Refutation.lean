/-
# A001917 — Shevelev: `k * a(n) = A006694((p_n^k - 1)/2)` for all `k`

Vladimir Shevelev's conjecture in OEIS A001917 (2008), refuted by Andrew R.
Epstein (2026). A001917 assigns `(p - 1) / ord(2,p)` to each odd prime `p`.
A006694 counts cyclotomic cosets of `2` modulo `2n+1`, excluding `{0}`.

The counterexample is `p = 1093`, `k = 2`. Since `2^364 ≡ 1 (mod 1093^2)`,
each coset has at most `364` elements, so the `1194648` nonzero residues
require at least `3282` cosets, whereas `2 * a(183) ≤ 2 * 1092`.
The proof needs some index for `1093`, not its exact index `183`.

Restricting to non-Wieferich primes gives a corrected identity via
`ord(2,p^j) = p^(j-1) ord(2,p)` and
`A006694(n) = Σ_{d ∣ 2n+1, d > 1} φ(d)/ord(2,d)`; that form is not formalized here.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A001917Refutation

/-! ## Definitions -/

/-- The `n`-th prime in OEIS (1-based) indexing: `oeisPrime 1 = 2`,
`oeisPrime 2 = 3`.  Only used for `2 ≤ n`, where `n - 1` is honest. -/
noncomputable def oeisPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The A001917 value attached to a prime `p`: `(p - 1) / ord(2, p)`, with
`ord(2, p) = orderOf (2 : ZMod p)` the least positive `x` with `2^x ≡ 1 (mod p)`.
For odd primes `p` the order is positive and divides `p - 1`, so the division
is exact. -/
noncomputable def a001917OfPrime (p : ℕ) : ℕ := (p - 1) / orderOf (2 : ZMod p)

/-- **A001917** (offset 2): `a(n) = (p - 1) / ord(2, p)` with `p = prime(n)`. -/
noncomputable def a001917 (n : ℕ) : ℕ := a001917OfPrime (oeisPrime n)

/-- The cyclotomic coset of `2` modulo `m` through `s`: the residues
`s * 2^j mod m`.  The exponent range `j < m` is exhaustive for odd `m`; see
`mem_cycCoset_iff`. -/
def cycCoset (m s : ℕ) : Finset ℕ := (Finset.range m).image (fun j => s * 2 ^ j % m)

/-- **A006694**: the number of cyclotomic cosets of `2` modulo `2n + 1`, not
counting the trivial coset `{0}` (as the data `a(0) = 0` and the formula
`a(n) = A000374(2n+1) - 1` require). -/
def a006694 (n : ℕ) : ℕ :=
  ((Finset.Ico 1 (2 * n + 1)).image (cycCoset (2 * n + 1))).card

/-! ## Faithfulness of the coset definition -/

/-- For odd `m`, membership in `cycCoset m s` is exactly membership in the
full orbit `{s * 2^j mod m : j ∈ ℕ}`. -/
theorem mem_cycCoset_iff {m s x : ℕ} (hm : Odd m) :
    x ∈ cycCoset m s ↔ ∃ j : ℕ, x = s * 2 ^ j % m := by
  constructor
  · intro hx
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hx
    exact ⟨j, hj.symm⟩
  · rintro ⟨j, rfl⟩
    have hmpos : 0 < m := hm.pos
    have hcop : Nat.Coprime 2 m := (Nat.coprime_two_left).mpr hm
    have htot : 2 ^ m.totient ≡ 1 [MOD m] := Nat.ModEq.pow_totient hcop
    have htpos : 0 < m.totient := Nat.totient_pos.mpr hmpos
    have hpow : 2 ^ j ≡ 2 ^ (j % m.totient) [MOD m] := by
      have hsplit : 2 ^ j = (2 ^ m.totient) ^ (j / m.totient) * 2 ^ (j % m.totient) := by
        rw [← pow_mul, ← pow_add, Nat.div_add_mod]
      calc 2 ^ j = (2 ^ m.totient) ^ (j / m.totient) * 2 ^ (j % m.totient) := hsplit
        _ ≡ 1 ^ (j / m.totient) * 2 ^ (j % m.totient) [MOD m] :=
          (htot.pow _).mul_right _
        _ = 2 ^ (j % m.totient) := by rw [one_pow, one_mul]
    refine Finset.mem_image.mpr ⟨j % m.totient, ?_, ?_⟩
    · exact Finset.mem_range.mpr
        (lt_of_lt_of_le (Nat.mod_lt _ htpos) (Nat.totient_le m))
    · exact (hpow.mul_left s).symm

/-! ## Examples -/

-- A006694, first 20 terms of the DATA line (offset 0).
example : a006694 0 = 0 ∧ a006694 1 = 1 ∧ a006694 2 = 1 ∧ a006694 3 = 2 ∧
    a006694 4 = 2 ∧ a006694 5 = 1 ∧ a006694 6 = 1 ∧ a006694 7 = 4 ∧
    a006694 8 = 2 ∧ a006694 9 = 1 ∧ a006694 10 = 5 ∧ a006694 11 = 2 ∧
    a006694 12 = 2 ∧ a006694 13 = 3 ∧ a006694 14 = 1 ∧ a006694 15 = 6 ∧
    a006694 16 = 4 ∧ a006694 17 = 5 ∧ a006694 18 = 1 ∧ a006694 19 = 4 := by
  decide +kernel

-- A001917, first four terms of the DATA line: a(2..5) = 1, 1, 2, 1.
example : a001917 2 = 1 := by
  have hp : oeisPrime 2 = 3 := Nat.nth_prime_one_eq_three
  have hord : orderOf (2 : ZMod 3) = 2 := by
    rw [orderOf_eq_iff (by norm_num)]; decide
  unfold a001917 a001917OfPrime
  rw [hp, hord]

example : a001917 3 = 1 := by
  have hp : oeisPrime 3 = 5 := Nat.nth_prime_two_eq_five
  have hord : orderOf (2 : ZMod 5) = 4 := by
    rw [orderOf_eq_iff (by norm_num)]; decide
  unfold a001917 a001917OfPrime
  rw [hp, hord]

example : a001917 4 = 2 := by
  have hp : oeisPrime 4 = 7 := Nat.nth_prime_three_eq_seven
  have hord : orderOf (2 : ZMod 7) = 3 := by
    rw [orderOf_eq_iff (by norm_num)]; decide
  unfold a001917 a001917OfPrime
  rw [hp, hord]

example : a001917 5 = 1 := by
  have hp : oeisPrime 5 = 11 := Nat.nth_prime_four_eq_eleven
  have hord : orderOf (2 : ZMod 11) = 10 := by
    rw [orderOf_eq_iff (by norm_num)]; decide
  unfold a001917 a001917OfPrime
  rw [hp, hord]

-- Shevelev's proved `k = 1` case at `p = 7`: `a(4) = 2 = A006694(3)`.
example : a006694 ((7 ^ 1 - 1) / 2) = 2 := by decide +kernel

-- The `k = 2` identity does hold at the non-Wieferich prime `p = 3`:
-- `2 * a(2) = 2 = A006694((3^2 - 1)/2)` and at `p = 7`: `2 * 2 = 4 = A006694(24)`.
example : a006694 ((3 ^ 2 - 1) / 2) = 2 ∧ a006694 ((7 ^ 2 - 1) / 2) = 4 := by
  decide +kernel

/-! ## The conjecture -/

/-- **Shevelev's conjecture (A001917, Vladimir Shevelev, 2008).**

Indices follow the entry: `n ≥ 2` (offset 2, `p_n = prime(n)` ranges over the
odd primes) and `k ≥ 1`.  The subtraction `p_n^k - 1` is honest since
`p_n^k ≥ 1`, and the division by `2` is exact since `p_n` is odd. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ, 1 ≤ k →
    k * a001917 n = a006694 ((oeisPrime n ^ k - 1) / 2)

/-! ## Refutation -/

/-- If `2^e ≡ 1 (mod m)` with `e > 0`, every cyclotomic coset modulo `m` has
at most `e` elements. -/
theorem card_cycCoset_le {m e s : ℕ} (he : 2 ^ e % m = 1) (hepos : 0 < e) :
    (cycCoset m s).card ≤ e := by
  have hsub : cycCoset m s ⊆ (Finset.range e).image (fun j => s * 2 ^ j % m) := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    have hmod : 2 ^ e ≡ 1 [MOD m] := by
      have hm1 : m ≠ 1 := by
        rintro rfl
        rw [Nat.mod_one] at he
        exact absurd he Nat.zero_ne_one
      rw [Nat.ModEq, he, Nat.one_mod_eq_one.mpr hm1]
    have hpow : 2 ^ j ≡ 2 ^ (j % e) [MOD m] := by
      calc 2 ^ j = (2 ^ e) ^ (j / e) * 2 ^ (j % e) := by
            rw [← pow_mul, ← pow_add, Nat.div_add_mod]
        _ ≡ 1 ^ (j / e) * 2 ^ (j % e) [MOD m] := (hmod.pow _).mul_right _
        _ = 2 ^ (j % e) := by rw [one_pow, one_mul]
    exact Finset.mem_image.mpr
      ⟨j % e, Finset.mem_range.mpr (Nat.mod_lt _ hepos), (hpow.mul_left s).symm⟩
  calc (cycCoset m s).card
      ≤ ((Finset.range e).image (fun j => s * 2 ^ j % m)).card := Finset.card_le_card hsub
    _ ≤ (Finset.range e).card := Finset.card_image_le
    _ = e := Finset.card_range e

/-- Orbit-counting lower bound: if `2^e ≡ 1 (mod 2n+1)` with `e > 0`, then the
`2n` nonzero residues are covered by `A006694(n)` cosets of size `≤ e`. -/
theorem two_mul_le_a006694_mul {n e : ℕ} (he : 2 ^ e % (2 * n + 1) = 1) (hepos : 0 < e) :
    2 * n ≤ a006694 n * e := by
  set m := 2 * n + 1 with hm
  have hcover : Finset.Ico 1 m ⊆
      ((Finset.Ico 1 m).image (cycCoset m)).biUnion id := by
    intro s hs
    have hsm : s < m := (Finset.mem_Ico.mp hs).2
    refine Finset.mem_biUnion.mpr ⟨cycCoset m s, Finset.mem_image_of_mem _ hs, ?_⟩
    refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
    rw [pow_zero, mul_one, Nat.mod_eq_of_lt hsm]
  have hbound : ∀ c ∈ (Finset.Ico 1 m).image (cycCoset m), (id c).card ≤ e := by
    intro c hc
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hc
    exact card_cycCoset_le he hepos
  calc 2 * n = (Finset.Ico 1 m).card := by rw [Nat.card_Ico]; omega
    _ ≤ (((Finset.Ico 1 m).image (cycCoset m)).biUnion id).card := Finset.card_le_card hcover
    _ ≤ ((Finset.Ico 1 m).image (cycCoset m)).card * e :=
      Finset.card_biUnion_le_card_mul _ _ _ hbound
    _ = a006694 n * e := rfl

/-- The Wieferich congruence at `1093`: `2^364 ≡ 1 (mod 1093^2)`. -/
theorem two_pow_364_mod_1093_sq : 2 ^ 364 % (2 * ((1093 ^ 2 - 1) / 2) + 1) = 1 := by
  decide +kernel

/-- `A006694((1093^2 - 1)/2) ≥ 3282`: the `1093^2 - 1` nonzero residues modulo
`1093^2` split into cosets of size at most `364`.  (The exact value is `3282`.) -/
theorem le_a006694_1093_sq : 3282 ≤ a006694 ((1093 ^ 2 - 1) / 2) := by
  have h := two_mul_le_a006694_mul two_pow_364_mod_1093_sq (by norm_num)
  have hval : 2 * ((1093 ^ 2 - 1) / 2) = 3282 * 364 := by norm_num
  rw [hval] at h
  exact Nat.le_of_mul_le_mul_right h (by norm_num)

/-- `1093` is a prime, hence occurs as `prime(n)` for `n = π(1093) = 183`;
we only need some index `n ≥ 2`. -/
theorem exists_oeisPrime_eq_1093 : ∃ n : ℕ, 2 ≤ n ∧ oeisPrime n = 1093 := by
  have hprime : Nat.Prime 1093 := by norm_num
  refine ⟨Nat.count Nat.Prime 1093 + 1, ?_, ?_⟩
  · have hlt : Nat.count Nat.Prime 2 < Nat.count Nat.Prime 1093 :=
      Nat.count_strict_mono Nat.prime_two (by norm_num)
    omega
  · simp only [oeisPrime, Nat.add_sub_cancel]
    exact Nat.nth_count hprime

/-- **Shevelev's conjecture is false.**  Counterexample: `p_183 = 1093` (a
Wieferich prime), `k = 2`.  Here `2 * a(183) ≤ 2 * 1092` (in fact `= 6`), while
`A006694((1093^2 - 1)/2) ≥ 3282` (in fact `= 3282`), because
`ord(2, 1093^2) = ord(2, 1093) = 364`.  The restriction to non-Wieferich primes is not formalized here. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  obtain ⟨n, hn, hp⟩ := exists_oeisPrime_eq_1093
  have heq := hconj n hn 2 (by norm_num)
  rw [hp] at heq
  have hleft : 2 * a001917 n ≤ 2 * 1092 := by
    have hdiv : a001917 n ≤ 1092 := by
      simp only [a001917, a001917OfPrime, hp]
      exact Nat.div_le_self _ _
    omega
  have hright := le_a006694_1093_sq
  omega

end Candidates.A001917Refutation
