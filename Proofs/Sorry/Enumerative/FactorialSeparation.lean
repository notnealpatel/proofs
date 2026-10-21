/-
# Factorial Separation (arXiv:2610.25661, Section 2)

Squares never lie just below `n!`, and `|n! - m^k| > n` when every prime factor of `m` is at
most `n + 2`.

## Source

Valmir Krasniqi, *The Factorial Separation Conjecture*, arXiv:2610.25661.
Retrieved with `fetch 2610.25661` (LaTeX source) on 2026-10-21.

Where the statements sit: Section 2 ("Elementary reductions"; the triage note numbered it
Section 3): Lemma 2.1 (`lem:valuation`), Lemma 2.2 (`lem:dichotomy`), Lemma 2.3
(`lem:not-power`), Theorem 2.4 (`thm:lower`, eq. `lower`), Lemma 2.5 (`lem:nonresidue`),
Theorem 2.6 (`thm:classification`), and Subsection 2.3 "Bases with bounded prime divisors":
Lemma 2.7 (`lem:two-part-growth`), the 2-adic bound (eq. `LTE-bound`), Theorem 2.8
(`thm:bounded-base`) and Corollary 2.9 (`cor:large-base-prime`). Conjecture 1.1
(`conj:fsc`) is in Section 1.

Verbatim informal claims:

* Conjecture 1.1 (FSC): "For every integer $n\ge8$ and all integers $m,k\ge2$,
  $|n!-m^k|>n$."
* Theorem 2.4: "Let $n\ge4$ and $m\ge1$ be integers. If $m^2<n!$, then $n!-m^2>n$."
* Theorem 2.6: "Let $n\ge4$ and $m\ge1$ be integers. If $|n!-m^2|\le n$, then there are
  integers $a,b\ge1$ such that $m=ab$, $m^2-n!=a^2$, $a^2\le n$, $n!=a^2(b^2-1)$, with
  $\gcd(a,b)=1$ and $b$ odd. In addition, $\gcd(b,n!)=1$, $\gcd(m,n!)=a$, $b\ge n+1$.
  Conversely, any positive integers $a,b$ satisfying $a^2\le n$ and $n!=a^2(b^2-1)$ give a
  square $(ab)^2$ within distance $n$ above $n!$."
* Theorem 2.8: "Let $n\ge8$ and $m,k\ge2$ be integers. Then
  $P^+(m)\le n+2 \Longrightarrow |n!-m^k|>n$."
* Corollary 2.9: "Every counterexample to Conjecture 1.1 satisfies $P^+(m)>n+2$."

## Status

Theorems 2.4, 2.6 and 2.8 (and Corollary 2.9) are **proved in the paper**; they are
formalized and proved below without `sorry`. Conjecture 1.1 itself is **open**
(the paper proves it only in the special cases listed in its Theorem 1.2); it is recorded
here only as the `Prop` `FactorialSeparationConjecture`, with no proof claimed.

## Formalization notes

* `P⁺(m) ≤ n + 2` is rendered as `∀ p ∈ m.primeFactors, p ≤ n + 2` (for `m ≥ 2` the two are
  equivalent).
* Differences are taken in `ℤ` after casting, so no truncated `ℕ` subtraction occurs in the
  statements.
* Theorems 2.4 and 2.6 are stated for all `m : ℕ` (the paper assumes `m ≥ 1`; for `m = 0`
  the hypotheses fail or the claim is immediate).
* The proofs follow the paper: Lemma 2.1 is proved in divisibility form (`p ^ e ∣ d` implies
  `p ^ (e + 1) ∣ n!`), the dichotomy of Lemma 2.2 through `exists_eq_pow_of_mul_eq_pow`, the
  prime alternative of Theorem 2.4 through the Jacobi symbol `J(-1 | (p - 1)/2) = -1`
  (instead of choosing a prime factor `q ≡ 3 (mod 4)`), Lemma 2.5 in the Jacobi form
  "`J(x | p) = 1` for all `0 < x < p` is impossible" (via Jacobi reciprocity for
  `p ≡ 1 (mod 4)` and `J(2 | p) = 1` for `p ≡ 1 (mod 8)`), Wilson's theorem
  `ZMod.wilsons_lemma`, and the 2-adic bound through Mathlib's `padicValNat.pow_two_sub_pow`
  (even exponents) and an explicit odd-cofactor factorization (odd exponents).
-/
import Mathlib

set_option autoImplicit false

open Nat

namespace FactorialSeparation

/-! ## The conjecture and ground truth -/

/-- **Factorial Separation Conjecture** (Conjecture 1.1 of arXiv:2610.25661, open):
for every `n ≥ 8` and all `m, k ≥ 2`, `|n! - m ^ k| > n`. Recorded as a `Prop` only. -/
def FactorialSeparationConjecture : Prop :=
  ∀ n m k : ℕ, 8 ≤ n → 2 ≤ m → 2 ≤ k → (n : ℤ) < |((n ! : ℕ) : ℤ) - (m : ℤ) ^ k|

/-- The threshold `n ≥ 8` is necessary: `7! + 1 = 71 ^ 2`, so `|7! - 71 ^ 2| = 1 ≤ 7`. -/
example : |((7 ! : ℕ) : ℤ) - (71 : ℤ) ^ 2| = 1 := by
  norm_num [Nat.factorial]

/-- The threshold `n ≥ 4` of Theorem 2.4 is sharp: `3! - 2 ^ 2 = 2 ≤ 3`. -/
example : ((3 ! : ℕ) : ℤ) - (2 : ℤ) ^ 2 = 2 := by
  norm_num [Nat.factorial]

/-- Brocard–Ramanujan solutions: `4! + 1 = 5 ^ 2` and `5! + 1 = 11 ^ 2`. -/
example : (4 ! + 1 = 5 ^ 2) ∧ (5 ! + 1 = 11 ^ 2) := by
  decide

/-! ## Elementary reductions -/

/-- Two distinct positive integers not exceeding `n` have product dividing `n!`. -/
theorem mul_dvd_factorial_of_ne {a b n : ℕ} (ha : 0 < a) (hb : 0 < b) (han : a ≤ n)
    (hbn : b ≤ n) (hab : a ≠ b) : a * b ∣ n ! := by
  wlog h : a < b generalizing a b
  · rw [mul_comm]
    exact this hb ha hbn han (Ne.symm hab) (by omega)
  have h1 : a ∣ (b - 1)! := Nat.dvd_factorial ha (by omega)
  have h2 : (b - 1)! * b = b ! := by
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    simp [Nat.factorial_succ, mul_comm]
  calc a * b ∣ (b - 1)! * b := Nat.mul_dvd_mul_right h1 b
    _ = b ! := h2
    _ ∣ n ! := Nat.factorial_dvd_factorial hbn

/-- **Lemma 2.1** (dvd form). If `p` is a prime with `2p ≤ n` and `1 ≤ d ≤ n`, then
`p ^ e ∣ d` implies `p ^ (e + 1) ∣ n!`; i.e. `v_p(n!) > v_p(d)`. -/
theorem pow_succ_dvd_factorial {p n d e : ℕ} (hp : p.Prime) (hpn : 2 * p ≤ n) (hd : 0 < d)
    (hdn : d ≤ n) (hpe : p ^ e ∣ d) : p ^ (e + 1) ∣ n ! := by
  by_cases hdp : d = p
  · subst hdp
    have he : e ≤ 1 := by
      have := Nat.le_of_dvd hd hpe
      by_contra hcon
      have : d ^ 2 ≤ d ^ e := Nat.pow_le_pow_right hp.pos (by omega)
      nlinarith [hp.two_le]
    have h2 : d * (2 * d) ∣ n ! :=
      mul_dvd_factorial_of_ne hp.pos (by omega) (by omega) hpn (by omega)
    have h3 : d ^ (e + 1) ∣ d * (2 * d) := by
      have : d ^ (e + 1) ∣ d ^ 2 := Nat.pow_dvd_pow d (by omega)
      exact this.trans ⟨2, by ring⟩
    exact h3.trans h2
  · have h2 : d * p ∣ n ! := mul_dvd_factorial_of_ne hd hp.pos hdn (by omega) hdp
    rw [pow_succ]
    exact (Nat.mul_dvd_mul_right hpe p).trans h2

/-- `2 ^ n * n! ≤ (n + 1) ^ n` (AM-GM for the factorial). -/
theorem two_pow_mul_factorial_le (n : ℕ) : 2 ^ n * n ! ≤ (n + 1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hb : 2 * (n + 1) ^ (n + 1) ≤ (n + 2) ^ (n + 1) := by
      have := one_add_mul_le_pow (a := (1 : ℚ) / (n + 1))
        (by have : (0 : ℚ) ≤ 1 / (n + 1) := by positivity
            linarith) (n + 1)
      have hpos : (0 : ℚ) < (n + 1) ^ (n + 1) := by positivity
      have key : ((n : ℚ) + 2) ^ (n + 1) = (n + 1) ^ (n + 1) * (1 + 1 / (n + 1)) ^ (n + 1) := by
        rw [← mul_pow]; congr 1; field_simp; ring
      have : (2 : ℚ) * (n + 1) ^ (n + 1) ≤ ((n : ℚ) + 2) ^ (n + 1) := by
        rw [key]
        have h1 : (1 : ℚ) + ((n + 1 : ℕ) : ℚ) * (1 / (n + 1)) = 2 := by
          push_cast; field_simp; ring
        rw [h1] at this
        nlinarith
      exact_mod_cast this
    calc 2 ^ (n + 1) * (n + 1)! = 2 * (n + 1) * (2 ^ n * n !) := by
          rw [Nat.factorial_succ]; ring
      _ ≤ 2 * (n + 1) * (n + 1) ^ n := Nat.mul_le_mul_left _ ih
      _ = 2 * (n + 1) ^ (n + 1) := by ring
      _ ≤ (n + 1 + 1) ^ (n + 1) := hb


/-- **Lemma 2.2** (dichotomy). Let `1 ≤ d ≤ n` and `k ≥ 1`, and suppose that `m ^ k` and `d`
have the same divisors among the divisors of `n!` (this holds when `m ^ k = n! ± d`). Then
either `d` is a prime `p` with `n < 2p`, or `d = a ^ k` and `m = a * b` with `a, b` coprime. -/
theorem dichotomy {n m k d : ℕ} (hk : 0 < k) (hd : 0 < d) (hdn : d ≤ n)
    (hcong : ∀ x, x ∣ n ! → (x ∣ m ^ k ↔ x ∣ d)) :
    (∃ p, p.Prime ∧ n < 2 * p ∧ d = p) ∨
      ∃ a b, d = a ^ k ∧ m = a * b ∧ Nat.Coprime a b := by
  by_cases hbig : ∃ p, p.Prime ∧ p ∣ d ∧ n < 2 * p
  · obtain ⟨p, hp, hpd, hnp⟩ := hbig
    left
    obtain ⟨c, rfl⟩ := hpd
    have hc : c = 1 := by
      rcases Nat.lt_or_ge c 2 with h | h
      · interval_cases c <;> simp_all
      · nlinarith
    exact ⟨p, hp, hnp, by simp [hc]⟩
  push Not at hbig
  right
  -- every prime power dividing `d` divides `m ^ k`
  have hdvd : d ∣ m ^ k := by
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p j hp hpj
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    have hpd : p ∣ d := (dvd_pow_self p hj.ne').trans hpj
    have h1 : p ^ (j + 1) ∣ n ! := pow_succ_dvd_factorial hp (hbig p hp hpd) hd hdn hpj
    exact (hcong _ ((pow_dvd_pow p (Nat.le_succ j)).trans h1)).2 hpj
  obtain ⟨c, hc⟩ := hdvd
  have hcop : Nat.Coprime d c := by
    apply Nat.coprime_of_dvd
    intro p hp hpd hpc
    have h1 : p ^ (d.factorization p + 1) ∣ n ! :=
      pow_succ_dvd_factorial hp (hbig p hp hpd) hd hdn (Nat.ordProj_dvd d p)
    have h2 : p ^ (d.factorization p + 1) ∣ m ^ k := by
      rw [hc, pow_succ]
      exact Nat.mul_dvd_mul (Nat.ordProj_dvd d p) hpc
    exact Nat.pow_succ_factorization_not_dvd hd.ne' hp ((hcong _ h1).1 h2)
  obtain ⟨a, ha⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.2 hcop) hc.symm
  have hak : a ^ k ∣ m ^ k := ⟨c, by rw [← ha, hc]⟩
  obtain ⟨b, hb⟩ := (Nat.pow_dvd_pow_iff hk.ne').1 hak
  refine ⟨a, b, ha, hb, ?_⟩
  have ha0 : a ^ k ≠ 0 := by rw [← ha]; exact hd.ne'
  have hcb : c = b ^ k := by
    have : a ^ k * c = a ^ k * b ^ k := by
      calc a ^ k * c = d * c := by rw [ha]
        _ = m ^ k := hc.symm
        _ = a ^ k * b ^ k := by rw [hb, mul_pow]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha0) this
  rw [ha, hcb] at hcop
  exact (Nat.coprime_pow_left_iff hk _ _).1 ((Nat.coprime_pow_right_iff hk _ _).1 hcop)

/-- **Lemma 2.3.** For `n ≥ 2` and `k ≥ 2`, `n!` is not a perfect `k`-th power. -/
theorem factorial_ne_pow {n m k : ℕ} (hn : 2 ≤ n) (hk : 2 ≤ k) : n ! ≠ m ^ k := by
  intro h
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) (by omega)
  have hpn : p ≤ n := by omega
  have hpd : p ∣ m := hp.dvd_of_dvd_pow (h ▸ Nat.dvd_factorial hp.pos hpn)
  have h2 : p ^ 2 ∣ n ! := by
    rw [h]; exact (pow_dvd_pow p hk).trans (pow_dvd_pow_of_dvd hpd k)
  have hn2p : n < 2 * p := by omega
  have hlog : Nat.log p n < 2 := by
    rw [Nat.log_lt_iff_lt_pow hp.one_lt (by omega)]
    nlinarith [hp.two_le]
  rw [hp.pow_dvd_factorial_iff hlog] at h2
  have hdiv : n / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  simp [hdiv] at h2


/-- **Lemma 2.7** (dvd form). For `n ≥ 8` there is `s` with `2 ^ s ∣ n!` and
`(n + 3) * (n - 1) < 2 ^ s`; i.e. `S_n = 2^{v_2(n!)} > (n + 3)(n - 1)`. -/
theorem exists_two_pow_dvd_factorial {n : ℕ} (hn : 8 ≤ n) :
    ∃ s, 2 ^ s ∣ n ! ∧ (n + 3) * (n - 1) < 2 ^ s := by
  have step : ∀ i s, 2 ^ s ∣ (i + 8)! → (i + 8 + 3) * (i + 8 - 1) < 2 ^ s →
      2 ^ (s + 1) ∣ (i + 10)! ∧ (i + 10 + 3) * (i + 10 - 1) < 2 ^ (s + 1) := by
    intro i s hs hlt
    refine ⟨?_, ?_⟩
    · have h2 : 2 ∣ (i + 9) * (i + 10) := even_iff_two_dvd.1 (Nat.even_mul_succ_self (i + 9))
      have : (i + 10)! = (i + 10) * ((i + 9) * (i + 8)!) := by
        rw [show i + 10 = (i + 9) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
      rw [this, pow_succ]
      calc 2 ^ s * 2 ∣ (i + 8)! * ((i + 9) * (i + 10)) := Nat.mul_dvd_mul hs h2
        _ = _ := by ring
    · have e1 : i + 8 - 1 = i + 7 := rfl
      have e2 : i + 10 - 1 = i + 9 := rfl
      rw [e1] at hlt
      rw [e2, pow_succ]
      nlinarith
  have key : ∀ i, (∃ s, 2 ^ s ∣ (i + 8)! ∧ (i + 8 + 3) * (i + 8 - 1) < 2 ^ s) ∧
      (∃ s, 2 ^ s ∣ (i + 9)! ∧ (i + 9 + 3) * (i + 9 - 1) < 2 ^ s) := by
    intro i
    induction i with
    | zero => exact ⟨⟨7, by decide, by norm_num⟩, ⟨7, by decide, by norm_num⟩⟩
    | succ i ih =>
      obtain ⟨⟨s, hs, hlt⟩, h9⟩ := ih
      refine ⟨by simpa [Nat.add_right_comm] using h9, ?_⟩
      obtain ⟨h1, h2⟩ := step i s hs hlt
      exact ⟨s + 1, by simpa [Nat.add_right_comm] using h1, by
        have : i + 1 + 9 = i + 10 := by ring
        rw [this]; exact h2⟩
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 8 := ⟨n - 8, by omega⟩
  exact (key i).1

/-- For odd `q`, odd exponent `2i+1` and `ε = ±1`, `q^(2i+1) - ε = (q - ε) * G` with `G` odd. -/
theorem odd_pow_sub_eq_mul_odd {q ε : ℤ} (hq : Odd q) (hε : ε = 1 ∨ ε = -1) (i : ℕ) :
    ∃ G, Odd G ∧ q ^ (2 * i + 1) - ε = (q - ε) * G := by
  have hε2 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hεodd : Odd ε := by rcases hε with rfl | rfl <;> decide
  induction i with
  | zero => exact ⟨1, odd_one, by ring⟩
  | succ i ih =>
    obtain ⟨G, hG, hEq⟩ := ih
    refine ⟨q ^ 2 * G + ε * (q + ε), ?_, ?_⟩
    · have h1 : Odd (q ^ 2 * G) := (hq.pow).mul hG
      have h2 : Even (ε * (q + ε)) := (hq.add_odd hεodd).mul_left ε
      exact h1.add_even h2
    · have : q ^ (2 * (i + 1) + 1) = q ^ 2 * q ^ (2 * i + 1) := by ring
      rw [this]
      linear_combination q ^ 2 * hEq + ε * hε2


/-- `2`-adic bound for `q^E - 1` with `q` odd and `E` even (via Mathlib's lifting-the-exponent
lemma `padicValNat.pow_two_sub_pow`): `2^j ∣ q^E - 1` implies `2^j ≤ (q + 1) * E`. -/
theorem two_pow_le_of_dvd_pow_sub_one_even {q E j : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) (hE : 0 < E)
    (hev : Even E) (h : 2 ^ j ∣ q ^ E - 1) : 2 ^ j ≤ (q + 1) * E := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hqE : 3 ≤ q ^ E := le_trans hq3 (Nat.le_self_pow hE.ne' q)
  have hne : q ^ E - 1 ≠ 0 := by omega
  have hj : j ≤ padicValNat 2 (q ^ E - 1) := (padicValNat_dvd_iff_le hne).1 h
  have h2q : 2 ∣ q - 1 := by
    obtain ⟨r, rfl⟩ := hq; exact ⟨r, by omega⟩
  have hnq : ¬ 2 ∣ q := by
    obtain ⟨r, rfl⟩ := hq; omega
  have key := padicValNat.pow_two_sub_pow (x := q) (y := 1) (by omega) h2q hnq hE.ne' hev
  rw [one_pow] at key
  set v := padicValNat 2 (q ^ E - 1)
  set a := padicValNat 2 (q + 1)
  set b := padicValNat 2 (q - 1)
  set c := padicValNat 2 E
  have hc : 2 ^ c ≤ E := Nat.le_of_dvd hE pow_padicValNat_dvd
  have hdvda : 2 ^ a ∣ q + 1 := pow_padicValNat_dvd
  have hdvdb : 2 ^ b ∣ q - 1 := pow_padicValNat_dvd
  have hab : 2 ^ a * 2 ^ b ≤ 2 * (q + 1) := by
    by_cases ha : a ≤ 1
    · have h1 : 2 ^ a ≤ 2 := by
        calc 2 ^ a ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) ha
          _ = 2 := by norm_num
      have h2 : 2 ^ b ≤ q - 1 := Nat.le_of_dvd (by omega) hdvdb
      calc 2 ^ a * 2 ^ b ≤ 2 * (q - 1) := Nat.mul_le_mul h1 h2
        _ ≤ 2 * (q + 1) := by omega
    · have h4a : 4 ∣ q + 1 := (pow_dvd_pow 2 (show 2 ≤ a by omega)).trans hdvda
      have hb : b ≤ 1 := by
        by_contra hb
        have h4b : 4 ∣ q - 1 := (pow_dvd_pow 2 (show 2 ≤ b by omega)).trans hdvdb
        omega
      have h1 : 2 ^ b ≤ 2 := by
        calc 2 ^ b ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hb
          _ = 2 := by norm_num
      have h2 : 2 ^ a ≤ q + 1 := Nat.le_of_dvd (by omega) hdvda
      calc 2 ^ a * 2 ^ b ≤ (q + 1) * 2 := Nat.mul_le_mul h2 h1
        _ = 2 * (q + 1) := by ring
  have hpow : 2 ^ (v + 1) = 2 ^ a * 2 ^ b * 2 ^ c := by
    rw [key, pow_add, pow_add]
  have : 2 ^ j * 2 ≤ 2 * (q + 1) * E := by
    calc 2 ^ j * 2 = 2 ^ (j + 1) := by ring
      _ ≤ 2 ^ (v + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 ^ a * 2 ^ b * 2 ^ c := hpow
      _ ≤ 2 * (q + 1) * E := Nat.mul_le_mul hab hc
  nlinarith

/-- **The `2`-adic bound (eq. LTE-bound).** For odd `q ≥ 3`, `E ≥ 1` and `ε = ±1`,
`2^j ∣ q^E - ε` implies `2^j ≤ (q + 1) * E`. -/
theorem two_pow_le_of_dvd_pow_sub {q E j : ℕ} {ε : ℤ} (hq : Odd q) (hq3 : 3 ≤ q)
    (hε : ε = 1 ∨ ε = -1) (hE : 0 < E) (h : (2 : ℤ) ^ j ∣ (q : ℤ) ^ E - ε) :
    2 ^ j ≤ (q + 1) * E := by
  rcases Nat.even_or_odd E with hev | hodd
  · rcases hε with rfl | rfl
    · -- `ε = 1`: move to `ℕ` and use the lifting-the-exponent lemma
      have hqE : 1 ≤ q ^ E := Nat.one_le_pow _ _ (by omega)
      have hcast : (((q ^ E - 1 : ℕ)) : ℤ) = (q : ℤ) ^ E - 1 := by
        push_cast [hqE]; ring
      rw [← hcast, show (2 : ℤ) ^ j = ((2 ^ j : ℕ) : ℤ) by push_cast; ring] at h
      exact two_pow_le_of_dvd_pow_sub_one_even hq hq3 hE hev (Int.natCast_dvd_natCast.1 h)
    · -- `ε = -1`: `q^E + 1 ≡ 2 (mod 4)` for even `E`
      obtain ⟨F, rfl⟩ := hev
      have hodd : Odd ((q : ℤ) ^ F) := (by exact_mod_cast hq : Odd (q : ℤ)).pow
      have hsq := Int.sq_mod_four_eq_one_of_odd hodd
      have hj : j ≤ 1 := by
        by_contra hj
        have h4 : (4 : ℤ) ∣ (q : ℤ) ^ (F + F) - -1 :=
          (pow_dvd_pow (2 : ℤ) (show 2 ≤ j by omega)).trans h |> fun h' => by
            simpa using h'
        rw [show (q : ℤ) ^ (F + F) = ((q : ℤ) ^ F) ^ 2 by ring] at h4
        omega
      calc 2 ^ j ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj
        _ ≤ (q + 1) * (F + F) := by nlinarith
  · obtain ⟨i, rfl⟩ := hodd
    obtain ⟨G, hG, hEq⟩ := odd_pow_sub_eq_mul_odd (by exact_mod_cast hq : Odd (q : ℤ)) hε i
    rw [hEq] at h
    have hcop : IsCoprime ((2 : ℤ) ^ j) G := by
      apply IsCoprime.pow_left
      rw [Prime.coprime_iff_not_dvd Int.prime_two]
      exact (Int.not_even_iff_odd.2 hG) ∘ even_iff_two_dvd.2
    have h1 : (2 : ℤ) ^ j ∣ (q : ℤ) - ε := hcop.dvd_of_dvd_mul_right h
    have h2 : (2 : ℤ) ^ j ≤ (q : ℤ) - ε :=
      Int.le_of_dvd (by rcases hε with rfl | rfl <;> omega) h1
    have h3 : ((2 ^ j : ℕ) : ℤ) ≤ (((q + 1) * (2 * i + 1) : ℕ) : ℤ) := by
      push_cast
      rcases hε with rfl | rfl <;> nlinarith
    exact_mod_cast h3


/-- Divisibility transfer: if `u + d = n!` then a divisor of `n!` divides `u` iff it divides
`d`. -/
theorem dvd_iff_of_add_eq_factorial {u d n : ℕ} (h : u + d = n !) :
    ∀ x, x ∣ n ! → (x ∣ u ↔ x ∣ d) := by
  intro x hx
  rw [← h] at hx
  exact ⟨fun hu => (Nat.dvd_add_right hu).1 hx, fun hd => (Nat.dvd_add_left hd).1 hx⟩

/-- Divisibility transfer: if `u = n! + d` then a divisor of `n!` divides `u` iff it divides
`d`. -/
theorem dvd_iff_of_eq_factorial_add {u d n : ℕ} (h : u = n ! + d) :
    ∀ x, x ∣ n ! → (x ∣ u ↔ x ∣ d) := by
  intro x hx
  rw [h]
  exact Nat.dvd_add_right hx

/-- Core of **Theorem 2.4**: for `n ≥ 4` there is no `d` with `1 ≤ d ≤ n` and
`m ^ 2 + d = n!`. -/
theorem sq_add_ne_factorial {n m d : ℕ} (hn : 4 ≤ n) (hd0 : 0 < d) (hdn : d ≤ n)
    (h : m ^ 2 + d = n !) : False := by
  rcases Nat.lt_or_ge n 6 with hsmall | hn6
  · have hm : m ≤ 10 := by
      have h120 : n ! ≤ 120 := by
        interval_cases n <;> decide
      nlinarith
    interval_cases n <;>
      simp only [factorial, succ_eq_add_one, reduceAdd, zero_add, mul_one, reduceMul] at h <;>
      interval_cases m <;> omega
  rcases dichotomy (k := 2) (by norm_num) hd0 hdn (dvd_iff_of_add_eq_factorial h) with
    ⟨p, hp, hnp, hdp⟩ | ⟨a, b, rfl, rfl, -⟩
  · subst d
    -- prime alternative: `p ≡ 7 (mod 8)` and `-1` would be a square modulo `(p - 1) / 2`
    have h8 : 8 ∣ n ! :=
      (show 8 ∣ (4)! by decide).trans (Nat.factorial_dvd_factorial hn)
    have hpodd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h2 | h2
      · omega
      · exact h2
    have hm8 : m ^ 2 % 8 = 0 ∨ m ^ 2 % 8 = 1 ∨ m ^ 2 % 8 = 4 := by
      rw [Nat.pow_mod]
      have := Nat.mod_lt m (show 8 > 0 by norm_num)
      interval_cases (m % 8) <;> simp
    have hp8 : p % 8 = 7 := by omega
    set N := p / 2 with hN
    have hpN : p = 2 * N + 1 := by omega
    have hN4 : N % 4 = 3 := by omega
    have hNodd : Odd N := Nat.odd_iff.2 (by omega)
    have hNfac : N ∣ n ! := Nat.dvd_factorial (by omega) (by omega)
    have hdiv : (N : ℤ) ∣ (m : ℤ) ^ 2 + 1 := by
      have hz : (m : ℤ) ^ 2 + 1 = (n ! : ℤ) - 2 * N := by
        have : ((m ^ 2 + p : ℕ) : ℤ) = (n ! : ℕ) := by rw [h]
        push_cast [hpN] at this
        linarith
      rw [hz]
      exact dvd_sub (Int.natCast_dvd_natCast.2 hNfac) (dvd_mul_left _ _)
    obtain ⟨t, ht⟩ := hdiv
    have hcop : (m : ℤ).gcd (N : ℤ) = 1 :=
      Int.isCoprime_iff_gcd_eq_one.1 ⟨-(m : ℤ), t, by linear_combination -ht⟩
    have hJ1 : jacobiSym ((m : ℤ) ^ 2) N = 1 := jacobiSym.sq_one' hcop
    have hJ2 : jacobiSym (-1) N = -1 := by
      rw [jacobiSym.at_neg_one hNodd, ZMod.χ₄_nat_three_mod_four hN4]
    have hmod : ((m : ℤ) ^ 2) % (N : ℤ) = (-1 : ℤ) % (N : ℤ) := by
      exact (Int.modEq_iff_dvd).2 ⟨-t, by linear_combination -ht⟩
    rw [jacobiSym.mod_left, hmod, ← jacobiSym.mod_left, hJ2] at hJ1
    norm_num at hJ1
  · -- square alternative: `n! = a^2 (b^2 + 1)` and `3 ∤ b^2 + 1`
    have ha0 : a ^ 2 ≠ 0 := hd0.ne'
    have h3 : 3 ^ ((a ^ 2).factorization 3 + 1) ∣ n ! :=
      pow_succ_dvd_factorial Nat.prime_three (by omega) hd0 hdn (Nat.ordProj_dvd _ _)
    have hfac : n ! = a ^ 2 * (b ^ 2 + 1) := by rw [← h]; ring
    have hb3 : ¬ 3 ∣ b ^ 2 + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod]
      have := Nat.mod_lt b (show 3 > 0 by norm_num)
      interval_cases (b % 3) <;> simp
    have hcop : Nat.Coprime (3 ^ ((a ^ 2).factorization 3 + 1)) (b ^ 2 + 1) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hb3)
    rw [hfac] at h3
    exact Nat.pow_succ_factorization_not_dvd ha0 Nat.prime_three
      (hcop.dvd_of_dvd_mul_right h3)


/-- Wilson's theorem at `q = n + 1`: `n! ≡ -1 (mod q)`. -/
theorem factorial_cast_eq_neg_one {n : ℕ} (hq : (n + 1).Prime) :
    ((n ! : ℕ) : ZMod (n + 1)) = -1 := by
  haveI : Fact (n + 1).Prime := ⟨hq⟩
  have := ZMod.wilsons_lemma (p := n + 1)
  simpa using this

/-- Wilson's theorem at `q = n + 2`: `n! ≡ 1 (mod q)`. -/
theorem factorial_cast_eq_one {n : ℕ} (hq : (n + 2).Prime) :
    ((n ! : ℕ) : ZMod (n + 2)) = 1 := by
  haveI : Fact (n + 2).Prime := ⟨hq⟩
  have hw := ZMod.wilsons_lemma (p := n + 2)
  have h1 : ((n + 1 : ℕ) : ZMod (n + 2)) = -1 := by
    have : ((n + 2 : ℕ) : ZMod (n + 2)) = 0 := ZMod.natCast_self _
    push_cast at this ⊢
    linear_combination this
  rw [show n + 2 - 1 = n + 1 from rfl, Nat.factorial_succ, Nat.cast_mul, h1] at hw
  linear_combination -hw

/-- For `n ≥ 2`, the consecutive integers `n + 1` and `n + 2` are not both prime. -/
theorem not_prime_and_prime_succ {n : ℕ} (hn : 2 ≤ n) (h1 : (n + 1).Prime)
    (h2 : (n + 2).Prime) : False := by
  rcases Nat.even_or_odd n with he | ho
  · have : Even (n + 2) := he.add even_two
    have := h2.even_iff.1 this
    omega
  · have : Even (n + 1) := ho.add_one
    have := h1.even_iff.1 this
    omega

/-- If `q ∣ y`, `0 < y ≤ q` then `y = q`. -/
theorem eq_of_dvd_of_le {q y : ℕ} (hy : 0 < y) (hyq : y ≤ q) (h : q ∣ y) : y = q :=
  le_antisymm hyq (Nat.le_of_dvd hy h)

/-- A natural number `x < q` with `x ≡ 1 (mod q)` equals `1` (for `q ≥ 2`). -/
theorem eq_one_of_cast_eq_one {q x : ℕ} (hq : 2 ≤ q) (hx : x < q) (h : (x : ZMod q) = 1) :
    x = 1 := by
  have h' : ((x : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by simpa using h
  rw [ZMod.natCast_eq_natCast_iff'] at h'
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (by omega)] at h'

/-- A natural number `x < q` with `x ≡ -1 (mod q)` satisfies `x + 1 = q`. -/
theorem succ_eq_of_cast_eq_neg_one {q x : ℕ} (hx : x < q) (h : (x : ZMod q) = -1) :
    x + 1 = q := by
  have h' : ((x + 1 : ℕ) : ZMod q) = 0 := by push_cast; rw [h]; ring
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact eq_of_dvd_of_le (by omega) (by omega) h'

/-- The final `2`-adic contradiction: for `n ≥ 8`, an odd `q` with `3 ≤ q ≤ n + 2`,
`1 ≤ E < n`, `ε = ±1`, and `2^s > (n + 3)(n - 1)`, the power `2^s` cannot divide
`q^E - ε`. -/
theorem two_adic_contra {n q E s : ℕ} {ε : ℤ} (hq : Odd q) (hq3 : 3 ≤ q) (hqn : q ≤ n + 2)
    (hE : 0 < E) (hEn : E < n) (hε : ε = 1 ∨ ε = -1)
    (hs : (n + 3) * (n - 1) < 2 ^ s) (h : (2 : ℤ) ^ s ∣ (q : ℤ) ^ E - ε) : False := by
  have h1 := two_pow_le_of_dvd_pow_sub hq hq3 hε hE h
  have h2 : (q + 1) * E ≤ (n + 3) * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
  omega


/-- In the power alternative `d = a^k`, `m = a * b`, the cofactor `b ≥ 2` is a power of a
single prime `q ∈ {n + 1, n + 2}` when every prime factor of `m` is at most `n + 2`. -/
theorem eq_prime_pow_of_power_case {n m k a b : ℕ} (hn : 8 ≤ n) (hk : 0 < k)
    (hm0 : m ≠ 0) (hm : m = a * b) (hab : Nat.Coprime a b) (hb : 2 ≤ b)
    (hP : ∀ r ∈ m.primeFactors, r ≤ n + 2)
    (hcong : ∀ x, x ∣ n ! → (x ∣ m ^ k ↔ x ∣ a ^ k)) :
    ∃ q t, q.Prime ∧ (q = n + 1 ∨ q = n + 2) ∧ b = q ^ t ∧ 0 < t := by
  have hprime : ∀ r, r.Prime → r ∣ b → r = n + 1 ∨ r = n + 2 := by
    intro r hr hrb
    have hrm : r ∣ m := hm ▸ dvd_mul_of_dvd_right hrb a
    have hle : r ≤ n + 2 := hP r (Nat.mem_primeFactors.2 ⟨hr, hrm, hm0⟩)
    by_contra hne
    have hrn : r ≤ n := by omega
    have hrak : r ∣ a ^ k := (hcong r (Nat.dvd_factorial hr.pos hrn)).1 (dvd_pow hrm hk.ne')
    have hra : r ∣ a := hr.dvd_of_dvd_pow hrak
    exact hr.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hra hab) hrb)
  have hb1 : b ≠ 1 := by omega
  have hq : b.minFac.Prime := Nat.minFac_prime hb1
  have huniq : ∀ {r : ℕ}, r.Prime → r ∣ b → r = b.minFac := by
    intro r hr hrb
    by_contra hne
    rcases hprime r hr hrb with h1 | h1 <;>
      rcases hprime _ hq (Nat.minFac_dvd b) with h2 | h2
    · exact hne (h1.trans h2.symm)
    · exact not_prime_and_prime_succ (by omega) (h1 ▸ hr) (h2 ▸ hq)
    · exact not_prime_and_prime_succ (by omega) (h2 ▸ hq) (h1 ▸ hr)
    · exact hne (h1.trans h2.symm)
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd (by omega : b ≠ 0) huniq
  refine ⟨b.minFac, b.primeFactorsList.length, hq,
    hprime _ hq (Nat.minFac_dvd b), hpow, ?_⟩
  by_contra ht
  rw [Nat.eq_zero_of_not_pos ht, pow_zero] at hpow
  exact hb1 hpow


/-- `2n < n!` for `n ≥ 4`. -/
theorem two_mul_lt_factorial {n : ℕ} (hn : 4 ≤ n) : 2 * n < n ! := by
  obtain ⟨c, rfl⟩ : ∃ c, n = c + 1 := ⟨n - 1, by omega⟩
  rw [Nat.factorial_succ]
  have := Nat.self_le_factorial c
  nlinarith

/-- `n! + 1 < (n + 1)^n` for `n ≥ 2` (from `2^n n! ≤ (n+1)^n`). -/
theorem factorial_add_one_lt_pow {n : ℕ} (hn : 2 ≤ n) : n ! + 1 < (n + 1) ^ n := by
  have h1 := two_pow_mul_factorial_le n
  have h2 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h3 := Nat.factorial_pos n
  nlinarith

/-- Transfer of a natural divisibility `2^s ∣ X` along `X = q^E - ε` to `ℤ`. -/
theorem int_two_pow_dvd {s X q E : ℕ} {ε : ℤ} (hX : (X : ℤ) = (q : ℤ) ^ E - ε)
    (h : 2 ^ s ∣ X) : (2 : ℤ) ^ s ∣ (q : ℤ) ^ E - ε := by
  rw [← hX]
  exact_mod_cast Int.natCast_dvd_natCast.2 h

/-- **Theorem 2.8, power alternative below `n!`.** There is no solution of
`m^k + a^k = n!` with `m = a b`, `gcd(a, b) = 1`, `1 ≤ a^k ≤ n`, `n ≥ 8`, `m, k ≥ 2`
and every prime factor of `m` at most `n + 2`. -/
theorem power_case_below {n m k a b : ℕ} (hn : 8 ≤ n) (hm2 : 2 ≤ m) (hk : 2 ≤ k)
    (hP : ∀ r ∈ m.primeFactors, r ≤ n + 2) (hd0 : 0 < a ^ k) (hdn : a ^ k ≤ n)
    (hm : m = a * b) (hab : Nat.Coprime a b) (h : m ^ k + a ^ k = n !) : False := by
  have hcong := dvd_iff_of_add_eq_factorial h
  have hb : 2 ≤ b := by
    rcases Nat.lt_or_ge b 2 with hb | hb
    · interval_cases b
      · simp only [mul_zero] at hm; omega
      · rw [hm, mul_one] at h
        have := two_mul_lt_factorial (show 4 ≤ n by omega)
        omega
    · exact hb
  obtain ⟨q, t, hq, hqn, rfl, ht⟩ :=
    eq_prime_pow_of_power_case hn (by omega) (by omega) hm hab hb hP hcong
  have hqm : q ∣ m := hm ▸ dvd_mul_of_dvd_right (dvd_pow_self q ht.ne') a
  have hcast : ((a ^ k : ℕ) : ZMod q) = ((n ! : ℕ) : ZMod q) := by
    have h' : ((m ^ k + a ^ k : ℕ) : ZMod q) = ((n ! : ℕ) : ZMod q) := by rw [h]
    have hm0 : ((m : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hqm
    push_cast at h' ⊢
    rw [hm0, zero_pow (by omega), zero_add] at h'
    exact h'
  rcases hqn with rfl | rfl
  · -- `q = n + 1`: Wilson forces `a^k = n`
    rw [factorial_cast_eq_neg_one hq] at hcast
    have hakn : a ^ k = n := by
      have := succ_eq_of_cast_eq_neg_one (by omega) hcast
      omega
    rcases Nat.even_or_odd k with ⟨l, hl⟩ | hodd
    · -- even `k`: a square at distance `n` below `n!`, excluded by Theorem 2.4
      refine sq_add_ne_factorial (m := m ^ l) (d := n) (by omega) (by omega) le_rfl ?_
      rw [← pow_mul, show l * 2 = k by omega]
      rw [hakn] at h
      exact h
    · -- odd `k`: `a + 1` is a proper divisor of the prime `a^k + 1 = n + 1`
      have ha2 : 2 ≤ a := by
        rcases Nat.lt_or_ge a 2 with ha | ha
        · interval_cases a
          · rw [zero_pow (by omega)] at hakn; omega
          · rw [one_pow] at hakn; omega
        · exact ha
      have hdvd : a + 1 ∣ n + 1 := by
        have := Odd.nat_add_dvd_pow_add_pow a 1 hodd
        rwa [one_pow, hakn] at this
      have hlt : a < a ^ k := by
        calc a = a ^ 1 := (pow_one a).symm
          _ < a ^ k := Nat.pow_lt_pow_right (by omega) (by omega)
      rcases hq.eq_one_or_self_of_dvd _ hdvd with h1 | h1 <;> omega
  · -- `q = n + 2`: Wilson forces `a = 1`, then `n! = q^E + 1`
    rw [factorial_cast_eq_one hq] at hcast
    have hak1 : a ^ k = 1 := eq_one_of_cast_eq_one (by omega) (by omega) hcast
    have ha1 : a = 1 := (pow_eq_one_iff.1 hak1).resolve_right (by omega)
    subst ha1
    rw [one_mul] at hm
    subst hm
    rw [one_pow, ← pow_mul] at h
    have hE : 0 < t * k := Nat.mul_pos ht (by omega)
    have hEn : t * k < n := by
      have h1 : (n + 2) ^ (t * k) < (n + 2) ^ n := by
        have := factorial_add_one_lt_pow (show 2 ≤ n by omega)
        have h2 : (n + 1) ^ n < (n + 2) ^ n := Nat.pow_lt_pow_left (by omega) (by omega)
        omega
      exact (Nat.pow_lt_pow_iff_right (by omega)).1 h1
    obtain ⟨s, hs, hslt⟩ := exists_two_pow_dvd_factorial hn
    have hX : ((n ! : ℕ) : ℤ) = ((n + 2 : ℕ) : ℤ) ^ (t * k) - (-1) := by
      rw [← h]; push_cast; ring
    exact two_adic_contra (hq.odd_of_ne_two (by omega)) (by omega) le_rfl hE hEn
      (Or.inr rfl) hslt (int_two_pow_dvd hX hs)

/-- **Theorem 2.8, power alternative above `n!`.** There is no solution of
`m^k = n! + a^k` with `m = a b`, `gcd(a, b) = 1`, `1 ≤ a^k ≤ n`, `n ≥ 8`, `m, k ≥ 2`
and every prime factor of `m` at most `n + 2`. -/
theorem power_case_above {n m k a b : ℕ} (hn : 8 ≤ n) (hm2 : 2 ≤ m) (hk : 2 ≤ k)
    (hP : ∀ r ∈ m.primeFactors, r ≤ n + 2) (hdn : a ^ k ≤ n)
    (hm : m = a * b) (hab : Nat.Coprime a b) (h : m ^ k = n ! + a ^ k) : False := by
  have hcong := dvd_iff_of_eq_factorial_add h
  have hb : 2 ≤ b := by
    rcases Nat.lt_or_ge b 2 with hb | hb
    · interval_cases b
      · simp only [mul_zero] at hm; omega
      · rw [hm, mul_one] at h
        have := Nat.factorial_pos n
        omega
    · exact hb
  obtain ⟨q, t, hq, hqn, rfl, ht⟩ :=
    eq_prime_pow_of_power_case hn (by omega) (by omega) hm hab hb hP hcong
  have hqm : q ∣ m := hm ▸ dvd_mul_of_dvd_right (dvd_pow_self q ht.ne') a
  have hcast : ((n ! : ℕ) : ZMod q) + ((a ^ k : ℕ) : ZMod q) = 0 := by
    have h' : ((m ^ k : ℕ) : ZMod q) = ((n ! + a ^ k : ℕ) : ZMod q) := by rw [h]
    have hm0 : ((m : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hqm
    push_cast at h' ⊢
    rw [hm0, zero_pow (by omega)] at h'
    exact h'.symm
  rcases hqn with rfl | rfl
  · -- `q = n + 1`: Wilson forces `a = 1`, then `q^E = n! + 1`
    rw [factorial_cast_eq_neg_one hq] at hcast
    have hcast' : ((a ^ k : ℕ) : ZMod (n + 1)) = 1 := by linear_combination hcast
    have hak1 : a ^ k = 1 := eq_one_of_cast_eq_one (by omega) (by omega) hcast'
    have ha1 : a = 1 := (pow_eq_one_iff.1 hak1).resolve_right (by omega)
    subst ha1
    rw [one_mul] at hm
    subst hm
    rw [one_pow, ← pow_mul] at h
    have hE : 0 < t * k := Nat.mul_pos ht (by omega)
    have hEn : t * k < n := by
      have h1 : (n + 1) ^ (t * k) < (n + 1) ^ n := by
        have := factorial_add_one_lt_pow (show 2 ≤ n by omega)
        omega
      exact (Nat.pow_lt_pow_iff_right (by omega)).1 h1
    obtain ⟨s, hs, hslt⟩ := exists_two_pow_dvd_factorial hn
    have hX : ((n ! : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) ^ (t * k) - 1 := by
      have : (((n + 1) ^ (t * k) : ℕ) : ℤ) = ((n ! + 1 : ℕ) : ℤ) := by rw [h]
      push_cast at this ⊢
      linarith
    exact two_adic_contra (hq.odd_of_ne_two (by omega)) (by omega) (by omega) hE hEn
      (Or.inl rfl) hslt (int_two_pow_dvd hX hs)
  · -- `q = n + 2`: Wilson forces `a^k ≡ -1`, impossible as `a^k ≤ n`
    rw [factorial_cast_eq_one hq] at hcast
    have hcast' : ((a ^ k : ℕ) : ZMod (n + 2)) = -1 := by linear_combination hcast
    have := succ_eq_of_cast_eq_neg_one (by omega) hcast'
    omega


/-- `n! ≤ p^n` whenever `n < 2p` (AM-GM). -/
theorem factorial_le_pow_of_lt_two_mul {n p : ℕ} (h : n < 2 * p) : n ! ≤ p ^ n := by
  have h1 := two_pow_mul_factorial_le n
  have h2 : (n + 1) ^ n ≤ (2 * p) ^ n := Nat.pow_le_pow_left (by omega) n
  rw [mul_pow] at h2
  exact Nat.le_of_mul_le_mul_left (h1.trans h2) (by positivity)

/-- In the prime alternative `d = p` (`n/2 < p ≤ n`), if no prime `> n` divides `m`, then `m`
is a positive power of `p`. -/
theorem eq_pow_of_prime_case {n m k p : ℕ} (hk : 0 < k) (hm2 : 2 ≤ m) (hp : p.Prime)
    (hcong : ∀ x, x ∣ n ! → (x ∣ m ^ k ↔ x ∣ p))
    (hbig : ∀ r, r.Prime → r ∣ m → n < r → False) : ∃ t, m = p ^ t ∧ 0 < t := by
  have huniq : ∀ {r : ℕ}, r.Prime → r ∣ m → r = p := by
    intro r hr hrm
    have hrn : r ≤ n := by
      by_contra hrn
      exact hbig r hr hrm (by omega)
    have hrp : r ∣ p := (hcong r (Nat.dvd_factorial hr.pos hrn)).1 (dvd_pow hrm hk.ne')
    exact (Nat.prime_dvd_prime_iff_eq hr hp).1 hrp
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd (by omega : m ≠ 0) huniq
  refine ⟨m.primeFactorsList.length, hpow, ?_⟩
  by_contra ht
  rw [Nat.eq_zero_of_not_pos ht, pow_zero] at hpow
  omega

/-- The final step of the prime alternative: `n! = p (p^E - ε)` with `n/2 < p ≤ n`,
`1 ≤ E < n` and `ε = ±1` contradicts the `2`-adic growth of `n!` for `n ≥ 8`. -/
theorem prime_case_final {n p E : ℕ} {ε : ℤ} (hn : 8 ≤ n) (hp : p.Prime) (hnp : n < 2 * p)
    (hpn : p ≤ n) (hE : 0 < E) (hEn : E < n) (hε : ε = 1 ∨ ε = -1)
    (hX : ((n ! : ℕ) : ℤ) = (p : ℤ) * ((p : ℤ) ^ E - ε)) : False := by
  obtain ⟨s, hs, hslt⟩ := exists_two_pow_dvd_factorial hn
  have hp2 : p ≠ 2 := by omega
  have hcopN : Nat.Coprime (2 ^ s) p :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have hcop : IsCoprime ((2 : ℤ) ^ s) (p : ℤ) := by
    have := Nat.isCoprime_iff_coprime.2 hcopN
    exact_mod_cast this
  have hdvd : (2 : ℤ) ^ s ∣ (p : ℤ) * ((p : ℤ) ^ E - ε) := by
    rw [← hX]; exact_mod_cast Int.natCast_dvd_natCast.2 hs
  exact two_adic_contra (hp.odd_of_ne_two hp2) (by omega) (by omega) hE hEn hε hslt
    (hcop.dvd_of_dvd_mul_left hdvd)

/-- **Theorem 2.8, prime alternative below `n!`.** There is no solution of `m^k + p = n!`
with `p` prime, `n/2 < p ≤ n`, `n ≥ 8`, `m, k ≥ 2` and every prime factor of `m` at most
`n + 2`. -/
theorem prime_case_below {n m k p : ℕ} (hn : 8 ≤ n) (hm2 : 2 ≤ m) (hk : 2 ≤ k)
    (hP : ∀ r ∈ m.primeFactors, r ≤ n + 2) (hp : p.Prime) (hnp : n < 2 * p) (hpn : p ≤ n)
    (h : m ^ k + p = n !) : False := by
  have hcong := dvd_iff_of_add_eq_factorial h
  have hbig : ∀ r, r.Prime → r ∣ m → n < r → False := by
    intro r hr hrm hnr
    have hle : r ≤ n + 2 := hP r (Nat.mem_primeFactors.2 ⟨hr, hrm, by omega⟩)
    have hcast : ((p : ℕ) : ZMod r) = ((n ! : ℕ) : ZMod r) := by
      have h' : ((m ^ k + p : ℕ) : ZMod r) = ((n ! : ℕ) : ZMod r) := by rw [h]
      have hm0 : ((m : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hrm
      push_cast at h'
      rw [hm0, zero_pow (by omega), zero_add] at h'
      exact h'
    obtain rfl | rfl : r = n + 1 ∨ r = n + 2 := by omega
    · rw [factorial_cast_eq_neg_one hr] at hcast
      have hpn' := succ_eq_of_cast_eq_neg_one (by omega) hcast
      have hpn'' : p = n := by omega
      subst hpn''
      exact not_prime_and_prime_succ (n := p - 1) (by omega)
        (by rwa [show p - 1 + 1 = p by omega]) (by rwa [show p - 1 + 2 = p + 1 by omega])
    · rw [factorial_cast_eq_one hr] at hcast
      have := eq_one_of_cast_eq_one (by omega) (by omega) hcast
      exact hp.one_lt.ne' this
  obtain ⟨t, rfl, ht⟩ := eq_pow_of_prime_case (by omega) hm2 hp hcong hbig
  rw [← pow_mul] at h
  have htk : 2 ≤ t * k := by nlinarith
  have hEn : t * k - 1 + 1 < n + 1 := by
    have h1 : p ^ (t * k) < p ^ n := by
      have := factorial_le_pow_of_lt_two_mul hnp
      have := hp.pos
      omega
    have := (Nat.pow_lt_pow_iff_right hp.one_lt).1 h1
    omega
  refine prime_case_final (E := t * k - 1) (ε := -1) hn hp hnp hpn (by omega) (by omega)
    (Or.inr rfl) ?_
  have hpow : p ^ (t * k) = p * p ^ (t * k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have : ((p ^ (t * k) + p : ℕ) : ℤ) = ((n ! : ℕ) : ℤ) := by rw [h]
  rw [hpow] at this
  push_cast at this
  linear_combination -this

/-- **Theorem 2.8, prime alternative above `n!`.** There is no solution of `m^k = n! + p`
with `p` prime, `n/2 < p ≤ n`, `n ≥ 8`, `m, k ≥ 2` and every prime factor of `m` at most
`n + 2`. -/
theorem prime_case_above {n m k p : ℕ} (hn : 8 ≤ n) (hm2 : 2 ≤ m) (hk : 2 ≤ k)
    (hP : ∀ r ∈ m.primeFactors, r ≤ n + 2) (hp : p.Prime) (hnp : n < 2 * p) (hpn : p ≤ n)
    (h : m ^ k = n ! + p) : False := by
  have hcong := dvd_iff_of_eq_factorial_add h
  have hbig : ∀ r, r.Prime → r ∣ m → n < r → False := by
    intro r hr hrm hnr
    have hle : r ≤ n + 2 := hP r (Nat.mem_primeFactors.2 ⟨hr, hrm, by omega⟩)
    have hcast : ((n ! : ℕ) : ZMod r) + ((p : ℕ) : ZMod r) = 0 := by
      have h' : ((m ^ k : ℕ) : ZMod r) = ((n ! + p : ℕ) : ZMod r) := by rw [h]
      have hm0 : ((m : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hrm
      push_cast at h'
      rw [hm0, zero_pow (by omega)] at h'
      exact h'.symm
    obtain rfl | rfl : r = n + 1 ∨ r = n + 2 := by omega
    · rw [factorial_cast_eq_neg_one hr] at hcast
      have hcast' : ((p : ℕ) : ZMod (n + 1)) = 1 := by linear_combination hcast
      have := eq_one_of_cast_eq_one (by omega) (by omega) hcast'
      exact hp.one_lt.ne' this
    · rw [factorial_cast_eq_one hr] at hcast
      have hcast' : ((p : ℕ) : ZMod (n + 2)) = -1 := by linear_combination hcast
      have := succ_eq_of_cast_eq_neg_one (by omega) hcast'
      omega
  obtain ⟨t, rfl, ht⟩ := eq_pow_of_prime_case (by omega) hm2 hp hcong hbig
  rw [← pow_mul] at h
  have htk : 2 ≤ t * k := by nlinarith
  have hEn : t * k < n + 1 := by
    have h1 : p ^ (t * k) < p ^ (n + 1) := by
      have h2 := factorial_le_pow_of_lt_two_mul hnp
      have h3 : p < p ^ n := by
        calc p = p ^ 1 := (pow_one p).symm
          _ < p ^ n := Nat.pow_lt_pow_right hp.one_lt (by omega)
      have h4 : p ^ (n + 1) = p * p ^ n := pow_succ' p n
      have h5 : 2 * p ^ n ≤ p * p ^ n := Nat.mul_le_mul_right _ hp.two_le
      omega
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).1 h1
  refine prime_case_final (E := t * k - 1) (ε := 1) hn hp hnp hpn (by omega) (by omega)
    (Or.inl rfl) ?_
  have hpow : p ^ (t * k) = p * p ^ (t * k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have : ((p ^ (t * k) : ℕ) : ℤ) = ((n ! + p : ℕ) : ℤ) := by rw [h]
  rw [hpow] at this
  push_cast at this
  linear_combination -this


/-! ## Main results -/

/-- **Theorem 2.4 (eq. `lower`) of arXiv:2610.25661.** Squares never lie just below a
factorial: for `n ≥ 4` and `m ^ 2 < n!`, one has `n! - m ^ 2 > n`. (The paper assumes
`m ≥ 1`; the case `m = 0` is included here and is immediate.) -/
theorem thm_2_4 {n m : ℕ} (hn : 4 ≤ n) (h : m ^ 2 < n !) :
    (n : ℤ) < (n ! : ℤ) - (m : ℤ) ^ 2 := by
  by_contra hcon
  rw [not_lt] at hcon
  have hcast : (((n !) - m ^ 2 : ℕ) : ℤ) = (n ! : ℤ) - (m : ℤ) ^ 2 := by
    push_cast [h.le]; ring
  have hdn : (n !) - m ^ 2 ≤ n := by
    have : (((n !) - m ^ 2 : ℕ) : ℤ) ≤ (n : ℤ) := hcast ▸ hcon
    exact_mod_cast this
  exact sq_add_ne_factorial (m := m) hn (by omega) hdn (by omega)

/-- **Theorem 2.8 (eq. `bounded-base-theorem`) of arXiv:2610.25661.** For `n ≥ 8` and
`m, k ≥ 2`, if every prime factor of `m` is at most `n + 2` (i.e. `P⁺(m) ≤ n + 2`), then
`|n! - m ^ k| > n`. -/
theorem thm_2_8 {n m k : ℕ} (hn : 8 ≤ n) (hm : 2 ≤ m) (hk : 2 ≤ k)
    (hP : ∀ p ∈ m.primeFactors, p ≤ n + 2) : (n : ℤ) < |(n ! : ℤ) - (m : ℤ) ^ k| := by
  by_contra hcon
  rw [not_lt, abs_le] at hcon
  obtain ⟨hlo, hhi⟩ := hcon
  rcases lt_trichotomy (m ^ k) (n !) with hlt | heq | hgt
  · -- `m^k` below `n!`
    have hcast : (((n !) - m ^ k : ℕ) : ℤ) = (n ! : ℤ) - (m : ℤ) ^ k := by
      push_cast [hlt.le]; ring
    have hdn : (n !) - m ^ k ≤ n := by
      have : (((n !) - m ^ k : ℕ) : ℤ) ≤ (n : ℤ) := hcast ▸ hhi
      exact_mod_cast this
    have h : m ^ k + ((n !) - m ^ k) = n ! := by omega
    rcases dichotomy (by omega) (by omega) hdn (dvd_iff_of_add_eq_factorial h) with
      ⟨p, hp, hnp, hdp⟩ | ⟨a, b, had, hab, hcop⟩
    · rw [hdp] at h hdn
      exact prime_case_below hn hm hk hP hp hnp hdn h
    · rw [had] at h hdn
      exact power_case_below hn hm hk hP (by rw [← had]; omega) hdn hab hcop h
  · exact factorial_ne_pow (by omega) hk heq.symm
  · -- `m^k` above `n!`
    have hcast : ((m ^ k - n ! : ℕ) : ℤ) = (m : ℤ) ^ k - (n ! : ℤ) := by
      push_cast [hgt.le]; ring
    have hdn : m ^ k - n ! ≤ n := by
      have : ((m ^ k - n ! : ℕ) : ℤ) ≤ (n : ℤ) := by rw [hcast]; linarith
      exact_mod_cast this
    have h : m ^ k = n ! + (m ^ k - n !) := by omega
    rcases dichotomy (by omega) (by omega) hdn (dvd_iff_of_eq_factorial_add h) with
      ⟨p, hp, hnp, hdp⟩ | ⟨a, b, had, hab, hcop⟩
    · rw [hdp] at h hdn
      exact prime_case_above hn hm hk hP hp hnp hdn h
    · rw [had] at h hdn
      exact power_case_above hn hm hk hP hdn hab hcop h


/-- **Lemma 2.5** (Jacobi-symbol form). For an odd prime `p`, some `1 ≤ x < p` has
`J(x | p) = -1`. -/
theorem exists_jacobiSym_eq_neg_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ x : ℕ, 0 < x ∧ x < p ∧ jacobiSym (x : ℤ) p = -1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha ⟨0, by simp⟩
  refine ⟨a.val, ?_, ZMod.val_lt a, ?_⟩
  · rw [Nat.pos_iff_ne_zero]
    intro h
    exact ha0 ((ZMod.val_eq_zero a).1 h)
  · rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]
    have : (((a.val : ℕ) : ℤ) : ZMod p) = a := by
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [this]
    exact ha

/-- Core of the prime alternative of **Theorem 2.6**: for `n ≥ 4` there is no square
`m ^ 2 = n! + p` with `p` prime and `n/2 < p ≤ n`. -/
theorem sq_ne_factorial_add_prime {n m p : ℕ} (hn : 4 ≤ n) (hp : p.Prime) (hnp : n < 2 * p)
    (hpn : p ≤ n) (h : m ^ 2 = n ! + p) : False := by
  have hp2 : p ≠ 2 := by omega
  have h8 : 8 ∣ n ! :=
    (show 8 ∣ (4)! by decide).trans (Nat.factorial_dvd_factorial hn)
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | h2
    · omega
    · exact h2
  have hm8 : m ^ 2 % 8 = 0 ∨ m ^ 2 % 8 = 1 ∨ m ^ 2 % 8 = 4 := by
    rw [Nat.pow_mod]
    have := Nat.mod_lt m (show 8 > 0 by norm_num)
    interval_cases (m % 8) <;> simp
  have hp8 : p % 8 = 1 := by omega
  have hpOdd : Odd p := Nat.odd_iff.2 hpodd
  -- every `x < p` is coprime to `m` and `m ^ 2 ≡ p (mod x)`
  have hgcd : ∀ x : ℕ, 0 < x → x < p → (m : ℤ).gcd (x : ℤ) = 1 := by
    intro x hx0 hxp
    rw [Int.gcd_natCast_natCast]
    apply Nat.coprime_of_dvd
    intro r hr hrm hrx
    have hrxle : r ≤ x := Nat.le_of_dvd hx0 hrx
    have hrn : r ∣ n ! := Nat.dvd_factorial hr.pos (by omega)
    have hrm2 : r ∣ n ! + p := h ▸ dvd_pow hrm (by norm_num)
    have hrp : r ∣ p := (Nat.dvd_add_right hrn).1 hrm2
    have := Nat.le_of_dvd hp.pos hrp
    rw [(Nat.prime_dvd_prime_iff_eq hr hp).1 hrp] at hrxle
    omega
  have hmod : ∀ x : ℕ, 0 < x → x < p → ((p : ℤ) % (x : ℤ)) = ((m : ℤ) ^ 2 % (x : ℤ)) := by
    intro x hx0 hxp
    have hxn : x ∣ n ! := Nat.dvd_factorial hx0 (by omega)
    have hz : (m : ℤ) ^ 2 = (n ! : ℤ) + p := by exact_mod_cast h
    rw [hz]
    obtain ⟨c, hc⟩ := hxn
    rw [show ((n ! : ℕ) : ℤ) = (x : ℤ) * c by exact_mod_cast hc]
    rw [Int.mul_add_emod_self_left]
  -- every `0 < x < p` is a Jacobi residue modulo `p`
  have key : ∀ x : ℕ, 0 < x → x < p → jacobiSym (x : ℤ) p = 1 := by
    intro x
    induction x using Nat.strong_induction_on with
    | _ x ih =>
      intro hx0 hxp
      rcases Nat.even_or_odd x with ⟨y, rfl⟩ | hxodd
      · have h2 : jacobiSym 2 p = 1 := by
          rw [jacobiSym.at_two hpOdd, ZMod.χ₈_nat_eq_if_mod_eight]
          simp [hpodd, hp8]
        have hy : jacobiSym (y : ℤ) p = 1 := ih y (by omega) (by omega) (by omega)
        rw [show ((y + y : ℕ) : ℤ) = 2 * (y : ℤ) by push_cast; ring, jacobiSym.mul_left, h2, hy]
        norm_num
      · rw [← jacobiSym.quadratic_reciprocity_one_mod_four (a := p) (b := x) (by omega) hxodd,
          jacobiSym.mod_left, hmod x hx0 hxp, ← jacobiSym.mod_left]
        exact jacobiSym.sq_one' (hgcd x hx0 hxp)
  obtain ⟨x, hx0, hxp, hx⟩ := exists_jacobiSym_eq_neg_one hp hp2
  rw [key x hx0 hxp] at hx
  norm_num at hx


/-- **Theorem 2.6 of arXiv:2610.25661 (classification of squares near `n!`).** Let `n ≥ 4`.
If `|n! - m ^ 2| ≤ n`, then there are `a, b ≥ 1` with `m = a b`, `m ^ 2 - n! = a ^ 2`,
`a ^ 2 ≤ n`, `n! = a ^ 2 (b ^ 2 - 1)`, `gcd(a, b) = 1` and `b` odd; moreover
`gcd(b, n!) = 1`, `gcd(m, n!) = a` and `b ≥ n + 1`. -/
theorem thm_2_6 {n m : ℕ} (hn : 4 ≤ n) (h : |((n ! : ℕ) : ℤ) - (m : ℤ) ^ 2| ≤ n) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ m = a * b ∧ (m : ℤ) ^ 2 - ((n ! : ℕ) : ℤ) = (a : ℤ) ^ 2 ∧
      a ^ 2 ≤ n ∧ ((n ! : ℕ) : ℤ) = (a : ℤ) ^ 2 * ((b : ℤ) ^ 2 - 1) ∧ Nat.Coprime a b ∧
      Odd b ∧ Nat.Coprime b (n !) ∧ Nat.gcd m (n !) = a ∧ n + 1 ≤ b := by
  rw [abs_le] at h
  obtain ⟨hlo, hhi⟩ := h
  rcases lt_trichotomy (m ^ 2) (n !) with hlt | heq | hgt
  · have := thm_2_4 hn hlt
    linarith
  · exact absurd heq.symm (factorial_ne_pow (by omega) le_rfl)
  have hcast : ((m ^ 2 - (n !) : ℕ) : ℤ) = (m : ℤ) ^ 2 - ((n ! : ℕ) : ℤ) := by
    push_cast [hgt.le]; ring
  have hdn : m ^ 2 - (n !) ≤ n := by
    have : ((m ^ 2 - (n !) : ℕ) : ℤ) ≤ (n : ℤ) := by rw [hcast]; linarith
    exact_mod_cast this
  have h' : m ^ 2 = n ! + (m ^ 2 - (n !)) := by omega
  have hcong := dvd_iff_of_eq_factorial_add h'
  rcases dichotomy (by norm_num) (by omega) hdn hcong with
    ⟨p, hp, hnp, hdp⟩ | ⟨a, b, had, hab, hcop⟩
  · rw [hdp] at h' hdn
    exact (sq_ne_factorial_add_prime hn hp hnp hdn h').elim
  rw [had] at h' hdn hcast hcong
  have hfpos := Nat.factorial_pos n
  have ha2 : 0 < a ^ 2 := by
    rw [← had]; omega
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · simp [h0] at ha2
    · exact h0
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · rw [h0, mul_zero] at hab
      rw [hab] at h'
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h'
      omega
    · exact h0
  have hb1 : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ hb
  have hfacN : n ! = a ^ 2 * (b ^ 2 - 1) := by
    rw [hab, mul_pow] at h'
    have : a ^ 2 * b ^ 2 = a ^ 2 * (b ^ 2 - 1) + a ^ 2 := by
      rw [Nat.mul_sub, mul_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ hb1)]
    omega
  have hfacZ : ((n ! : ℕ) : ℤ) = (a : ℤ) ^ 2 * ((b : ℤ) ^ 2 - 1) := by
    rw [hfacN]; push_cast [hb1]; ring
  -- `b` is coprime to `n!`
  have hbfac : Nat.Coprime b (n !) := by
    apply Nat.coprime_of_dvd
    intro r hr hrb hrn
    have hrm : r ∣ m := hab ▸ dvd_mul_of_dvd_right hrb a
    have hra2 : r ∣ a ^ 2 := (hcong r hrn).1 (dvd_pow hrm (by norm_num))
    have hra : r ∣ a := hr.dvd_of_dvd_pow hra2
    exact hr.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hra hcop) hrb)
  -- `b` is odd: otherwise `v₂(n!) = v₂(a²)`, contradicting Lemma 2.1 at `p = 2`
  have hbodd : Odd b := by
    by_contra hbe
    rw [Nat.not_odd_iff_even] at hbe
    have h2 : 2 ^ ((a ^ 2).factorization 2 + 1) ∣ n ! :=
      pow_succ_dvd_factorial Nat.prime_two (by omega) ha2 hdn (Nat.ordProj_dvd _ _)
    have hodd : ¬ 2 ∣ b ^ 2 - 1 := by
      obtain ⟨c, rfl⟩ := hbe
      have : (c + c) ^ 2 = 4 * (c * c) := by ring
      omega
    have hcop2 : Nat.Coprime (2 ^ ((a ^ 2).factorization 2 + 1)) (b ^ 2 - 1) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
    rw [hfacN] at h2
    exact Nat.pow_succ_factorization_not_dvd ha2.ne' Nat.prime_two
      (hcop2.dvd_of_dvd_mul_right h2)
  -- `gcd(m, n!) = a`
  have hafac : a ∣ n ! := Nat.dvd_factorial ha (by nlinarith)
  have hgcd : Nat.gcd m (n !) = a := by
    rw [hab, Nat.Coprime.gcd_mul_right_cancel a hbfac]
    exact Nat.gcd_eq_left hafac
  -- `b ≥ n + 1`: `b > 1` and every prime factor of `b` exceeds `n`
  have hbne1 : b ≠ 1 := by
    rintro rfl
    simp only [one_pow, tsub_self, mul_zero] at hfacN
    omega
  have hbig : n + 1 ≤ b := by
    have hq := Nat.minFac_prime hbne1
    have hqb : b.minFac ≤ b := Nat.minFac_le hb
    by_contra hcon
    have hqn : b.minFac ≤ n := by omega
    have : b.minFac ∣ n ! := Nat.dvd_factorial hq.pos hqn
    exact hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (Nat.minFac_dvd b) hbfac) this)
  refine ⟨a, b, ha, hb, hab, ?_, hdn, hfacZ, hcop, hbodd, hbfac, hgcd, hbig⟩
  rw [← hcast]; push_cast; ring

/-- **Converse part of Theorem 2.6.** If `a, b ≥ 1`, `a ^ 2 ≤ n` and `n! = a ^ 2 (b ^ 2 - 1)`,
then `(a b) ^ 2` is a square within distance `n` above `n!`: `0 < (a b) ^ 2 - n! ≤ n`. -/
theorem thm_2_6_converse {n a b : ℕ} (ha : 0 < a) (han : a ^ 2 ≤ n)
    (h : ((n ! : ℕ) : ℤ) = (a : ℤ) ^ 2 * ((b : ℤ) ^ 2 - 1)) :
    0 < ((a * b : ℕ) : ℤ) ^ 2 - ((n ! : ℕ) : ℤ) ∧
      ((a * b : ℕ) : ℤ) ^ 2 - ((n ! : ℕ) : ℤ) ≤ n := by
  have hdiff : ((a * b : ℕ) : ℤ) ^ 2 - ((n ! : ℕ) : ℤ) = (a : ℤ) ^ 2 := by
    rw [h]; push_cast; ring
  rw [hdiff]
  refine ⟨by positivity, by exact_mod_cast han⟩

/-- **Corollary 2.9 of arXiv:2610.25661.** Every counterexample to the Factorial Separation
Conjecture has a prime factor `p` of `m` with `p > n + 2`. -/
theorem cor_2_9 {n m k : ℕ} (hn : 8 ≤ n) (hm : 2 ≤ m) (hk : 2 ≤ k)
    (h : |((n ! : ℕ) : ℤ) - (m : ℤ) ^ k| ≤ n) : ∃ p ∈ m.primeFactors, n + 2 < p := by
  by_contra hcon
  push Not at hcon
  exact absurd (thm_2_8 hn hm hk hcon) (not_lt.2 h)

/-! ## Non-vacuity checks -/

/-- Theorem 2.4 at `n = 4`, `m = 4`: `4! - 4 ^ 2 = 8 > 4`. -/
example : (4 : ℤ) < ((4 ! : ℕ) : ℤ) - (4 : ℤ) ^ 2 :=
  thm_2_4 le_rfl (by decide)

/-- The hypotheses of Theorem 2.8 hold jointly at `n = 10`, `m = 11 = n + 1` (prime),
`k = 5`; this instance exercises the Wilson branch `q = n + 1`. -/
example : (10 : ℤ) < |((10 ! : ℕ) : ℤ) - (11 : ℤ) ^ 5| := by
  have hP : ∀ p ∈ (11 : ℕ).primeFactors, p ≤ 10 + 2 := by
    rw [Nat.Prime.primeFactors (by norm_num)]
    simp
  exact_mod_cast thm_2_8 (n := 10) (m := 11) (k := 5) (by norm_num) (by norm_num)
    (by norm_num) hP

/-- The hypothesis of Theorem 2.6 is satisfiable: `|4! - 5 ^ 2| = 1 ≤ 4`. -/
example : |((4 ! : ℕ) : ℤ) - (5 : ℤ) ^ 2| ≤ 4 := by
  norm_num [Nat.factorial]

/-- The converse of Theorem 2.6 at the Brocard solution `7! = 1 ^ 2 (71 ^ 2 - 1)`. -/
example : 0 < ((1 * 71 : ℕ) : ℤ) ^ 2 - ((7 ! : ℕ) : ℤ) ∧
    ((1 * 71 : ℕ) : ℤ) ^ 2 - ((7 ! : ℕ) : ℤ) ≤ 7 :=
  thm_2_6_converse (by norm_num) (by norm_num) (by norm_num [Nat.factorial])

end FactorialSeparation
