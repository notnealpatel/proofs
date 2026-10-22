/-
# A139555 — Zumkeller: a(n) < phi(n) for every n > 60

Reinhard Zumkeller's conjecture in OEIS A139555 (2010). The related
A051250 classification has a proof sketch by C. R. Greathouse IV (2011)
using Dusart-type bounds and finite checks; the proof here uses Bertrand's
postulate instead.

## Proof

Let `p < q` be the two least primes not dividing `n`.  Then `p * q` is a
totative of `n` that is neither `1` nor a prime power, so it suffices that
`p * q ≤ n`.  Every prime below `q` other than `p` divides `n`, hence
`primorial (q - 1) ∣ p * n`.  A Bonse-type bound `q ^ 3 ≤ primorial (q - 1)`
for `13 ≤ q` (proved by strong induction from Bertrand's postulate) gives
`p * p * q ≤ p * n`.  For `q ≤ 11` one has `p * q ≤ 132`, and the range
`61 ≤ n ≤ 131` is checked by `decide`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A139555GcdPrimePower

/-! ## Definitions -/

/-- OEIS A139555: `a n` is the number of `k` with `1 ≤ k ≤ n`, `gcd(k, n) = 1`,
and `k` equal to `1` or a prime power. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k => Nat.Coprime k n ∧ (k = 1 ∨ IsPrimePow k))).card

/-- Kernel-reducible restatement of `a`, with the prime-power test written as a
bounded search (`p ≤ k`, `e ≤ k`); used only for evaluation. -/
def aBounded (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k => Nat.Coprime k n ∧
    (k = 1 ∨ ∃ p : ℕ, p ≤ k ∧ ∃ e : ℕ, e ≤ k ∧ p.Prime ∧ 0 < e ∧ p ^ e = k))).card

/-- The bounded restatement agrees with `a` everywhere. -/
theorem a_eq_aBounded (n : ℕ) : a n = aBounded n := by
  unfold a aBounded
  simp_rw [isPrimePow_nat_iff_bounded]

/-- Examples: the first twelve listed terms of A139555. -/
example : (List.range 12).map (fun i => a (i + 1)) = [1, 1, 2, 2, 4, 2, 5, 4, 6, 4, 8, 4] := by
  simp only [a_eq_aBounded]
  decide

/-! ## Bonse-type lower bound for the primorial -/

/-- If `r` is a prime with `h < r ≤ 2h`, then `primorial h * r ∣ primorial (2h)`. -/
theorem primorial_mul_dvd_primorial_two_mul {h r : ℕ} (hr : r.Prime) (hhr : h < r)
    (hr2 : r ≤ 2 * h) : primorial h * r ∣ primorial (2 * h) := by
  unfold primorial
  have hnot : r ∉ (Finset.range (h + 1)).filter Nat.Prime := by
    simp only [Finset.mem_filter, Finset.mem_range, not_and]
    intro hlt
    omega
  have hsub : insert r ((Finset.range (h + 1)).filter Nat.Prime) ⊆
      (Finset.range (2 * h + 1)).filter Nat.Prime := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range] at hx ⊢
    rcases hx with rfl | ⟨hx, hxp⟩
    · exact ⟨by omega, hr⟩
    · exact ⟨by omega, hxp⟩
  have hprod := Finset.prod_dvd_prod_of_subset _ _ (fun x => x) hsub
  rw [Finset.prod_insert hnot, mul_comm] at hprod
  exact hprod

/-- Bonse-type inequality: `(m + 1) ^ 3 ≤ primorial m` for `12 ≤ m`. -/
theorem cube_le_primorial (m : ℕ) (hm : 12 ≤ m) : (m + 1) ^ 3 ≤ primorial m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hsmall : m < 24
    · interval_cases m <;> decide
    · have hm24 : 24 ≤ m := Nat.le_of_not_lt hsmall
      set h := m / 2 with hh
      have hh12 : 12 ≤ h := by omega
      have hih : (h + 1) ^ 3 ≤ primorial h := ih h (by omega) hh12
      obtain ⟨r, hr, hhr, hr2⟩ := Nat.exists_prime_lt_and_le_two_mul h (by omega)
      have hle : primorial h * r ≤ primorial m :=
        (Nat.le_of_dvd (primorial_pos _) (primorial_mul_dvd_primorial_two_mul hr hhr hr2)).trans
          (primorial_mono (by omega))
      calc (m + 1) ^ 3 ≤ (2 * (h + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
        _ = 8 * (h + 1) ^ 3 := by ring
        _ ≤ (h + 1) * (h + 1) ^ 3 := Nat.mul_le_mul_right _ (by omega)
        _ = (h + 1) ^ 3 * (h + 1) := mul_comm _ _
        _ ≤ primorial h * r := Nat.mul_le_mul hih (by omega)
        _ ≤ primorial m := hle

/-! ## Two small primes not dividing `n` -/

/-- For `0 < n`, there are primes `p < q`, neither dividing `n`, with
`primorial (q - 1) ∣ p * n` (take `p`, `q` the two least primes not dividing `n`). -/
theorem exists_primes_primorial_dvd {n : ℕ} (hn : 0 < n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ ¬ p ∣ n ∧ ¬ q ∣ n ∧
      primorial (q - 1) ∣ p * n := by
  classical
  have hex1 : ∃ p, p.Prime ∧ ¬ p ∣ n := by
    obtain ⟨p, hge, hp⟩ := Nat.exists_infinite_primes (n + 1)
    exact ⟨p, hp, fun hdvd => by have hle := Nat.le_of_dvd hn hdvd; omega⟩
  set p := Nat.find hex1 with hpdef
  have hp : p.Prime ∧ ¬ p ∣ n := Nat.find_spec hex1
  have hex2 : ∃ q, q.Prime ∧ ¬ q ∣ n ∧ p < q := by
    obtain ⟨q, hge, hq⟩ := Nat.exists_infinite_primes (n + p + 1)
    exact ⟨q, hq, fun hdvd => by have hle := Nat.le_of_dvd hn hdvd; omega, by omega⟩
  set q := Nat.find hex2 with hqdef
  have hq : q.Prime ∧ ¬ q ∣ n ∧ p < q := Nat.find_spec hex2
  refine ⟨p, q, hp.1, hq.1, hq.2.2, hp.2, hq.2.1, ?_⟩
  have hq1 : q - 1 + 1 = q := Nat.sub_add_cancel hq.1.one_lt.le
  have hall : ∀ r ∈ (Finset.range q).filter Nat.Prime, r ∣ p * n := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨hrq, hrp⟩ := hr
    rcases lt_trichotomy r p with hlt | heq | hgt
    · have hmin := Nat.find_min hex1 hlt
      have hdvd : r ∣ n := by
        by_contra hnd
        exact hmin ⟨hrp, hnd⟩
      exact Dvd.dvd.mul_left hdvd p
    · rw [heq]
      exact Dvd.intro n rfl
    · have hmin := Nat.find_min hex2 hrq
      have hdvd : r ∣ n := by
        by_contra hnd
        exact hmin ⟨hrp, hnd, hgt⟩
      exact Dvd.dvd.mul_left hdvd p
  have hprod := Finset.prod_primes_dvd (p * n)
    (fun r hr => (Finset.mem_filter.mp hr).2.prime) hall
  unfold primorial
  rw [hq1]
  exact hprod

/-- Every `n > 60` has two distinct primes `p`, `q`, neither dividing `n`, with
`p * q ≤ n`. -/
theorem exists_primes_mul_le {n : ℕ} (hn : 60 < n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ ¬ p ∣ n ∧ ¬ q ∣ n ∧ p * q ≤ n := by
  by_cases hsmall : n < 132
  · have hdec : ∀ m < 132, 60 < m → ∃ p < 12, ∃ q < 12,
        p.Prime ∧ q.Prime ∧ p ≠ q ∧ ¬ p ∣ m ∧ ¬ q ∣ m ∧ p * q ≤ m := by
      decide
    obtain ⟨p, -, q, -, hpq⟩ := hdec n hsmall hn
    exact ⟨p, q, hpq⟩
  · obtain ⟨p, q, hp, hq, hpq, hpn, hqn, hdvd⟩ := exists_primes_primorial_dvd (n := n) (by omega)
    refine ⟨p, q, hp, hq, hpq.ne, hpn, hqn, ?_⟩
    by_cases hq13 : 13 ≤ q
    · have hq1 : q - 1 + 1 = q := by omega
      have hcube : q ^ 3 ≤ primorial (q - 1) := by
        have hb := cube_le_primorial (q - 1) (by omega)
        rwa [hq1] at hb
      have hle : primorial (q - 1) ≤ p * n :=
        Nat.le_of_dvd (Nat.mul_pos hp.pos (by omega)) hdvd
      have hppq : p * (p * q) ≤ q ^ 3 := by
        calc p * (p * q) ≤ q * (q * q) :=
              Nat.mul_le_mul hpq.le (Nat.mul_le_mul_right q hpq.le)
          _ = q ^ 3 := by ring
      exact Nat.le_of_mul_le_mul_left (hppq.trans (hcube.trans hle)) hp.pos
    · have hp11 : p ≤ 11 := by omega
      have hq12 : q ≤ 12 := by omega
      calc p * q ≤ 11 * 12 := Nat.mul_le_mul hp11 hq12
        _ ≤ n := by omega

/-! ## The conjecture -/

/-- The totatives of `n` in `[1, n]` number `φ n`. -/
theorem card_filter_coprime_Icc (n : ℕ) :
    ((Finset.Icc 1 n).filter (fun k => Nat.Coprime k n)).card = Nat.totient n := by
  rw [← Nat.filter_coprime_Ico_eq_totient n 1]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico, Nat.coprime_comm]
  omega

/-- A product of two distinct primes is not a prime power. -/
theorem not_isPrimePow_mul_of_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ¬ IsPrimePow (p * q) := by
  rw [isPrimePow_iff_unique_prime_dvd]
  rintro ⟨r, -, huniq⟩
  have hpr : p = r := huniq p ⟨hp, Dvd.intro q rfl⟩
  have hqr : q = r := huniq q ⟨hq, Dvd.intro_left p rfl⟩
  exact hpq (hpr.trans hqr.symm)

/-- Zumkeller's conjecture (OEIS A139555, 2010): for `60 < n`, the number of
totatives equal to `1` or a prime power is less than `φ(n)`. The threshold
is sharp: `a 60 = φ 60 = 16`. The proof constructs distinct primes `p,q`
not dividing `n` with `pq ≤ n`. -/
theorem conjecture (n : ℕ) (hn : 60 < n) : a n < Nat.totient n := by
  classical
  obtain ⟨p, q, hp, hq, hpq, hpn, hqn, hle⟩ := exists_primes_mul_le hn
  set T := (Finset.Icc 1 n).filter (fun k => Nat.Coprime k n) with hT
  have ha : a n = (T.filter (fun k => k = 1 ∨ IsPrimePow k)).card := by
    unfold a
    rw [hT, Finset.filter_filter]
  have hwit : p * q ∈ T ∧ ¬ (p * q = 1 ∨ IsPrimePow (p * q)) := by
    refine ⟨?_, ?_⟩
    · simp only [hT, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.mul_pos hp.pos hq.pos, hle⟩, ?_⟩
      exact Nat.Coprime.mul_left ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn)
        ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqn)
    · rintro (h1 | hpp)
      · exact Nat.Prime.ne_one hp (Nat.eq_one_of_mul_eq_one_right h1)
      · exact not_isPrimePow_mul_of_prime hp hq hpq hpp
  have hss : T.filter (fun k => k = 1 ∨ IsPrimePow k) ⊂ T :=
    Finset.filter_ssubset.mpr ⟨p * q, hwit.1, hwit.2⟩
  rw [ha, ← card_filter_coprime_Icc n]
  exact Finset.card_lt_card hss

/-- The threshold `60` is sharp: `a 60 = φ 60`, since every totative of `60`
is `1`, a prime, or `49 = 7 ^ 2`. -/
example : a 60 = Nat.totient 60 := by
  have hall : ∀ k < 61, Nat.Coprime k 60 → k = 1 ∨ k.Prime ∨ k = 49 := by decide
  rw [← card_filter_coprime_Icc]
  unfold a
  congr 1
  refine Finset.filter_congr (fun k hk => ?_)
  refine ⟨fun h => h.1, fun hc => ⟨hc, ?_⟩⟩
  have hk61 : k < 61 := by
    have hk' := (Finset.mem_Icc.mp hk).2
    omega
  rcases hall k hk61 hc with h1 | hpr | h49
  · exact Or.inl h1
  · exact Or.inr hpr.isPrimePow
  · right
    rw [h49, show (49 : ℕ) = 7 ^ 2 by norm_num]
    exact (Nat.prime_seven).isPrimePow.pow (by norm_num)

end Candidates.A139555GcdPrimePower
