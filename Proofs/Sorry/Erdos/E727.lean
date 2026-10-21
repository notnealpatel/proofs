/-
  Erdős Problem #727 — factorial square divisibility (n+k)!² ∣ (2n)!.
  Status: open (even k = 2).  Tier UC lemma mine (Balakran's k = 1
  theorem + factorial-divisibility lemmas).

  Verbatim statement (`goof erdos fetch 727`, pulled 2026-08-05):

    "Let $k\geq 2$. Does\[(n+k)!^2 \mid (2n)!\]for infinitely many
    $n$?"

  DB remarks (EGRS75): open even for k = 2.  Balakran [Ba29]: the
  k = 1 analogue holds infinitely often — (n+1)!² ∣ (2n)!, i.e.
  (n+1)² ∣ C(2n,n); classical: (n+1) ∣ C(2n,n) always (Catalan).
  EGRS: Balakran's method gives (n+k)!(n+1)! ∣ (2n)! infinitely often
  (even for k < c·log n).  Erdős [Er68c]: a!b! ∣ n! forces
  a + b ≤ n + O(log n).

  OEIS anchors: A002503 (positive numbers n with (n+1)² ∣ C(2n,n));
  `n = 0` is also a valid boundary case, A343507, A389396.

  Mathlib inventory: `Nat.factorial`, `Nat.centralBinom`, `catalan`
  with `succ_mul_catalan_eq_centralBinom` (`(n+1)·Cₙ = C(2n,n)`)
  — the bridge making the k = 1 statement a divisibility fact about
  Catalan numbers.
-/
import Mathlib
import Erdos.FactorialCatalan
import Erdos.FactorialSquareWitness

set_option autoImplicit false

namespace ErdosCandidates.E727

/-- Ground truth for the k = 1 shape at the first nontrivial A002503
    term: n = 5: (5+1)!² = 518400 divides 10! = 3628800 = 7·518400.
    Certified by the production ground-truth theorem. -/
example : (Nat.factorial 6) ^ 2 ∣ Nat.factorial 10 := by
  exact Erdos727.factorial_six_sq_dvd_factorial_ten

/-- The equivalence powering the k = 1 case, for every natural `n`, including `0`:
    `(n+1)!² ∣ (2n)! ↔ (n+1) ∣ catalan n`.
    Via `(2n)!/(n!)² = C(2n,n) = (n+1)·catalan n`.
    The production bridge uses `succ_mul_catalan_eq_centralBinom` and
    `Nat.choose_mul_factorial_mul_factorial`. -/
theorem sq_dvd_iff_dvd_catalan (n : ℕ) :
    (n + 1).factorial ^ 2 ∣ (2 * n).factorial ↔ (n + 1) ∣ catalan n := by
  exact Erdos727.sq_dvd_iff_dvd_catalan n

section BalakramHelpers

/-! ### Balakram's theorem (k = 1)

Kummer's criterion shows `(pq)² ∣ C(2(pq-1), pq-1)` for primes `p, q` with
`3p < 2q < 4p`; Chebyshev's `30`-combination of log-factorials gives a prime in
`(n, 1.3n)` for all large `n`, supplying infinitely many such pairs. -/

open Real Finset ArithmeticFunction Chebyshev
open scoped Nat


/-- Kummer-type criterion: two carries at levels 1 and 2 give `p² ∣ C(2N, N)`. -/
private lemma sq_dvd_choose_of_two_carries {p N : ℕ} (hp : p.Prime)
    (h1 : p ≤ 2 * (N % p)) (h2 : p ^ 2 ≤ 2 * (N % p ^ 2)) :
    p ^ 2 ∣ Nat.choose (N + N) N := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hne : Nat.choose (N + N) N ≠ 0 := (Nat.choose_pos (by omega)).ne'
  rw [padicValNat_dvd_iff_le hne,
    padicValNat_choose' (b := Nat.log p (N + N) + 1) (Nat.lt_succ_self _)]
  have hmod : N % p ^ 2 ≤ N := Nat.mod_le _ _
  have hlog : 2 ≤ Nat.log p (N + N) :=
    Nat.le_log_of_pow_le hp.one_lt (by omega)
  have hsub : ({1, 2} : Finset ℕ) ⊆
      {i ∈ Finset.Ico 1 (Nat.log p (N + N) + 1) | p ^ i ≤ N % p ^ i + N % p ^ i} := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_filter, Finset.mem_Ico]
    rcases hi with rfl | rfl
    · refine ⟨⟨le_rfl, by omega⟩, ?_⟩
      simp only [pow_one]; omega
    · exact ⟨⟨by norm_num, by omega⟩, by omega⟩
  simpa using Finset.card_le_card hsub

/-- If `m ∣ N + 1` then `N % m = m - 1`. -/
private lemma mod_eq_sub_one_of_dvd_succ {m N : ℕ} (hm : 0 < m) (h : m ∣ N + 1) :
    N % m = m - 1 := by
  obtain ⟨k, hk⟩ := h
  rcases k with _ | k
  · simp at hk
  have hN : N = (m - 1) + m * k := by rw [Nat.mul_succ] at hk; omega
  rw [hN, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- Balakram's pair: for primes `p, q` with `3p < 2q` and `q < 2p`, `n = pq - 1` satisfies
`(pq)² ∣ C(2n, n)`. -/
private lemma pq_sq_dvd_choose {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h1 : 3 * p < 2 * q) (h2 : q < 2 * p) :
    (p * q) ^ 2 ∣ Nat.choose ((p * q - 1) + (p * q - 1)) (p * q - 1) := by
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hpq : p < q := by omega
  have hcop : Nat.Coprime (p ^ 2) (q ^ 2) :=
    Nat.Coprime.pow 2 2 ((Nat.coprime_primes hp hq).mpr (by omega))
  have hpos : 0 < p * q := Nat.mul_pos (by omega) (by omega)
  have hsucc : p * q - 1 + 1 = p * q := by omega
  rw [mul_pow]
  apply hcop.mul_dvd_of_dvd_of_dvd
  · apply sq_dvd_choose_of_two_carries hp
    · rw [mod_eq_sub_one_of_dvd_succ (by omega) (by rw [hsucc]; exact dvd_mul_right p q)]
      omega
    · obtain ⟨t, rfl⟩ : ∃ t, q = p + t := ⟨q - p, by omega⟩
      have ht2 : t < p := by omega
      have hA : p * (p + t) = p ^ 2 + p * t := by ring
      have hlt : p * t < p ^ 2 := by
        rw [pow_two]; exact Nat.mul_lt_mul_of_pos_left ht2 (by omega)
      have hpt : 0 < p * t := Nat.mul_pos (by omega) (by omega)
      have hN : p * (p + t) - 1 = (p * t - 1) + p ^ 2 * 1 := by omega
      rw [hN, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      have : p * p + 2 ≤ 2 * (p * t) := by nlinarith
      rw [pow_two]; omega
  · apply sq_dvd_choose_of_two_carries hq
    · rw [mod_eq_sub_one_of_dvd_succ (by omega) (by rw [hsucc]; exact dvd_mul_left q p)]
      omega
    · have hlt : p * q - 1 < q ^ 2 := by
        rw [pow_two]; have := Nat.mul_lt_mul_of_pos_right hpq (by omega : 0 < q); omega
      rw [Nat.mod_eq_of_lt hlt]
      have : q * q + 2 ≤ 2 * (p * q) := by nlinarith
      rw [pow_two]; omega



/-- Chebyshev weight `g(m) = m - ⌊m/2⌋ - ⌊m/3⌋ - ⌊m/5⌋ + ⌊m/30⌋` lies in `{0, 1}`. -/
private lemma g_bounds (m : ℕ) :
    0 ≤ ((m : ℤ) - (m / 2 : ℕ) - (m / 3 : ℕ) - (m / 5 : ℕ) + (m / 30 : ℕ)) ∧
      ((m : ℤ) - (m / 2 : ℕ) - (m / 3 : ℕ) - (m / 5 : ℕ) + (m / 30 : ℕ)) ≤ 1 := by
  omega

/-- Chebyshev weight `g(m)` equals `1` for `1 ≤ m < 6`. -/
private lemma g_eq_one {m : ℕ} (h1 : 1 ≤ m) (h6 : m < 6) :
    ((m : ℤ) - (m / 2 : ℕ) - (m / 3 : ℕ) - (m / 5 : ℕ) + (m / 30 : ℕ)) = 1 := by
  omega

/-- `log m! = ∑_{d ≤ m} Λ(d) ⌊m/d⌋`. -/
private lemma log_factorial_eq_sum (m : ℕ) :
    Real.log (m ! : ℝ) = ∑ d ∈ Ioc 0 m, Λ d * ((m / d : ℕ) : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity), ih]
    have hsplit : ∀ d ∈ Ioc 0 (m + 1), Λ d * (((m + 1) / d : ℕ) : ℝ) =
        Λ d * ((m / d : ℕ) : ℝ) + (if d ∣ m + 1 then Λ d else 0) := by
      intro d _
      rw [Nat.succ_div]
      split_ifs <;> push_cast <;> ring
    rw [sum_congr rfl hsplit, sum_add_distrib, ← sum_filter]
    have h1 : ∑ d ∈ Ioc 0 (m + 1), Λ d * ((m / d : ℕ) : ℝ) =
        ∑ d ∈ Ioc 0 m, Λ d * ((m / d : ℕ) : ℝ) := by
      rw [Finset.sum_Ioc_succ_top (Nat.zero_le m), Nat.div_eq_of_lt (Nat.lt_succ_self m)]
      simp
    have h2 : (Ioc 0 (m + 1)).filter (· ∣ m + 1) = (m + 1).divisors := by
      ext d
      simp only [mem_filter, mem_Ioc, Nat.mem_divisors]
      constructor
      · rintro ⟨_, hd⟩; exact ⟨hd, by omega⟩
      · rintro ⟨hd, _⟩; exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), Nat.le_of_dvd (by omega) hd⟩, hd⟩
    rw [h1, h2, vonMangoldt_sum]
    push_cast
    ring

/-- `log ⌊n/k⌋! = ∑_{d ≤ n} Λ(d) ⌊⌊n/d⌋/k⌋`. -/
private lemma log_factorial_div_eq_sum (n k : ℕ) (hk : 0 < k) :
    Real.log ((n / k)! : ℝ) = ∑ d ∈ Ioc 0 n, Λ d * ((n / d / k : ℕ) : ℝ) := by
  rw [log_factorial_eq_sum]
  have hcongr : ∀ d ∈ Ioc 0 (n / k), Λ d * ((n / k / d : ℕ) : ℝ) =
      Λ d * ((n / d / k : ℕ) : ℝ) := by
    intro d _
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm k d]
  rw [sum_congr rfl hcongr]
  apply sum_subset
  · intro d hd
    simp only [mem_Ioc] at hd ⊢
    exact ⟨hd.1, hd.2.trans (Nat.div_le_self n k)⟩
  · intro d hd hnot
    simp only [mem_Ioc, not_and, not_le] at hd hnot
    have hlt : n / k < d := hnot hd.1
    have : n / d / k = 0 := by
      rw [Nat.div_div_eq_div_mul]
      apply Nat.div_eq_of_lt
      rw [Nat.div_lt_iff_lt_mul hk] at hlt
      linarith [mul_comm d k]
    simp [this]

/-- Chebyshev's combination as a weighted sum of `Λ`. -/
private lemma chebS_eq_sum (n : ℕ) :
    Real.log (n ! : ℝ) - Real.log ((n / 2)! : ℝ) - Real.log ((n / 3)! : ℝ) -
      Real.log ((n / 5)! : ℝ) + Real.log ((n / 30)! : ℝ) =
    ∑ d ∈ Ioc 0 n, Λ d * (((((n / d : ℕ) : ℤ) - ((n / d / 2 : ℕ) : ℤ) - ((n / d / 3 : ℕ) : ℤ) -
      ((n / d / 5 : ℕ) : ℤ) + ((n / d / 30 : ℕ) : ℤ)) : ℤ) : ℝ) := by
  rw [log_factorial_eq_sum, log_factorial_div_eq_sum n 2 (by norm_num),
    log_factorial_div_eq_sum n 3 (by norm_num), log_factorial_div_eq_sum n 5 (by norm_num),
    log_factorial_div_eq_sum n 30 (by norm_num), ← sum_sub_distrib, ← sum_sub_distrib,
    ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun d _ => ?_
  simp only [Int.cast_add, Int.cast_sub, Int.cast_natCast]
  ring

/-- `ψ` at a natural number is the sum of `Λ` over `(0, n]`. -/
private lemma psi_natCast (n : ℕ) : ψ (n : ℝ) = ∑ d ∈ Ioc 0 n, Λ d := by
  rw [Chebyshev.psi, Nat.floor_natCast]

/-- Chebyshev sandwich: `ψ n - ψ (n/6) ≤ S n ≤ ψ n`. -/
private lemma chebS_sandwich (n : ℕ) :
    ψ (n : ℝ) - ψ ((n / 6 : ℕ) : ℝ) ≤
      Real.log (n ! : ℝ) - Real.log ((n / 2)! : ℝ) - Real.log ((n / 3)! : ℝ) -
        Real.log ((n / 5)! : ℝ) + Real.log ((n / 30)! : ℝ) ∧
    Real.log (n ! : ℝ) - Real.log ((n / 2)! : ℝ) - Real.log ((n / 3)! : ℝ) -
        Real.log ((n / 5)! : ℝ) + Real.log ((n / 30)! : ℝ) ≤ ψ (n : ℝ) := by
  rw [chebS_eq_sum, psi_natCast, psi_natCast]
  constructor
  · have hsplit := Finset.sum_Ioc_consecutive (fun d => Λ d) (Nat.zero_le (n / 6))
      (Nat.div_le_self n 6)
    rw [← hsplit, add_sub_cancel_left]
    calc ∑ d ∈ Ioc (n / 6) n, Λ d
        = ∑ d ∈ Ioc (n / 6) n, Λ d * (((((n / d : ℕ) : ℤ) - ((n / d / 2 : ℕ) : ℤ) -
            ((n / d / 3 : ℕ) : ℤ) - ((n / d / 5 : ℕ) : ℤ) + ((n / d / 30 : ℕ) : ℤ)) : ℤ) : ℝ) := by
          refine sum_congr rfl fun d hd => ?_
          simp only [mem_Ioc] at hd
          have hd0 : 0 < d := by omega
          have h1 : 1 ≤ n / d := (Nat.le_div_iff_mul_le hd0).mpr (by omega)
          have h6 : n / d < 6 := by
            rw [Nat.div_lt_iff_lt_mul hd0]
            have := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 6)).mp hd.1
            linarith
          rw [g_eq_one h1 h6]
          simp
      _ ≤ ∑ d ∈ Ioc 0 n, Λ d * (((((n / d : ℕ) : ℤ) - ((n / d / 2 : ℕ) : ℤ) -
            ((n / d / 3 : ℕ) : ℤ) - ((n / d / 5 : ℕ) : ℤ) + ((n / d / 30 : ℕ) : ℤ)) : ℤ) : ℝ) := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro d hd
            simp only [mem_Ioc] at hd ⊢
            omega
          · intro d _ _
            apply mul_nonneg vonMangoldt_nonneg
            exact_mod_cast (g_bounds (n / d)).1
  · apply sum_le_sum
    intro d _
    calc Λ d * (((((n / d : ℕ) : ℤ) - ((n / d / 2 : ℕ) : ℤ) -
            ((n / d / 3 : ℕ) : ℤ) - ((n / d / 5 : ℕ) : ℤ) + ((n / d / 30 : ℕ) : ℤ)) : ℤ) : ℝ)
        ≤ Λ d * 1 := by
          apply mul_le_mul_of_nonneg_left _ vonMangoldt_nonneg
          exact_mod_cast (g_bounds (n / d)).2
      _ = Λ d := mul_one _



/-- Stirling-type bounds: `m log m - m ≤ log m! ≤ m log m - m + (log m)/2 + 1`. -/
private lemma log_factorial_bounds {m : ℕ} (hm : m ≠ 0) :
    (m : ℝ) * Real.log m - m ≤ Real.log (m ! : ℝ) ∧
      Real.log (m ! : ℝ) ≤ (m : ℝ) * Real.log m - m + Real.log m / 2 + 1 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm1
  constructor
  · have h := Stirling.le_log_factorial_stirling hm
    have h2pi : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
    linarith
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hanti : Stirling.stirlingSeq (k + 1) ≤ Stirling.stirlingSeq 1 :=
      Stirling.stirlingSeq'_antitone (Nat.zero_le k)
    rw [Stirling.stirlingSeq_one] at hanti
    have hpos : 0 < Stirling.stirlingSeq (k + 1) := Stirling.stirlingSeq'_pos k
    have hden : 0 < √(2 * ((k + 1 : ℕ) : ℝ)) * (((k + 1 : ℕ) : ℝ) / exp 1) ^ (k + 1) := by
      positivity
    have hfac : (((k + 1)! : ℕ) : ℝ) = Stirling.stirlingSeq (k + 1) *
        (√(2 * ((k + 1 : ℕ) : ℝ)) * (((k + 1 : ℕ) : ℝ) / exp 1) ^ (k + 1)) := by
      rw [Stirling.stirlingSeq, div_mul_cancel₀ _ hden.ne']
    have hlogS : Real.log (Stirling.stirlingSeq (k + 1)) ≤ 1 - Real.log 2 / 2 := by
      calc Real.log (Stirling.stirlingSeq (k + 1)) ≤ Real.log (exp 1 / √2) :=
            Real.log_le_log hpos hanti
        _ = 1 - Real.log 2 / 2 := by
          rw [Real.log_div (by positivity) (by positivity), Real.log_exp, Real.log_sqrt
            (by norm_num)]
    have hk0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    rw [hfac, Real.log_mul hpos.ne' hden.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_sqrt (by positivity), Real.log_pow, Real.log_div hk0.ne' (by positivity),
      Real.log_exp, Real.log_mul (by norm_num) hk0.ne']
    push_cast
    linarith

/-- Floor perturbation of `F(y) = y log y - y`. -/
private lemma floor_F_approx {y : ℝ} (hy : 1 ≤ y) :
    |((⌊y⌋₊ : ℝ) * Real.log ⌊y⌋₊ - ⌊y⌋₊) - (y * Real.log y - y)| ≤ Real.log y + 1 := by
  set m : ℝ := (⌊y⌋₊ : ℝ) with hm
  have hm1 : 1 ≤ m := by
    rw [hm]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hy).ne'
  have hmy : m ≤ y := Nat.floor_le (by linarith)
  have hym : y < m + 1 := Nat.lt_floor_add_one y
  have hm0 : 0 < m := by linarith
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm1
  have hlogmy : Real.log m ≤ Real.log y := Real.log_le_log hm0 hmy
  have hratio : Real.log y - Real.log m ≤ y / m - 1 := by
    rw [← Real.log_div (by linarith) hm0.ne']
    exact Real.log_le_sub_one_of_pos (by positivity)
  have hm_ratio : m * (Real.log y - Real.log m) ≤ y - m := by
    have h1 := mul_le_mul_of_nonneg_left hratio hm0.le
    have h2 : m * (y / m - 1) = y - m := by field_simp
    linarith
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
  rw [abs_le]
  constructor
  · -- m log m - m - (y log y - y) ≥ -(log y + 1)
    nlinarith [mul_le_mul_of_nonneg_left hlogmy (sub_nonneg.mpr hmy)]
  · nlinarith [mul_le_mul_of_nonneg_left hlogmy (sub_nonneg.mpr hmy),
      mul_le_mul_of_nonneg_left hlogmy hm0.le]

/-- `log ⌊y⌋! = y log y - y + O(log y)` with explicit error `2 log y + 2`. -/
private lemma log_factorial_floor_approx {y : ℝ} (hy : 1 ≤ y) :
    |Real.log ((⌊y⌋₊)! : ℝ) - (y * Real.log y - y)| ≤ 2 * Real.log y + 2 := by
  have hm : ⌊y⌋₊ ≠ 0 := (Nat.floor_pos.mpr hy).ne'
  have hm1 : (1 : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
  have hlogmy : Real.log ⌊y⌋₊ ≤ Real.log y :=
    Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
  have hlogm : 0 ≤ Real.log ⌊y⌋₊ := Real.log_nonneg hm1
  have hb := log_factorial_bounds hm
  have hF := floor_F_approx hy
  rw [abs_le] at hF ⊢
  constructor <;> linarith [hb.1, hb.2, hF.1, hF.2]

/-- `log ⌊n/k⌋! = (n/k) log (n/k) - n/k + O(log n)` for `1 ≤ k ≤ n`. -/
private lemma log_factorial_div_approx {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    |Real.log ((n / k)! : ℝ) - (((n : ℝ) / k) * Real.log ((n : ℝ) / k) - (n : ℝ) / k)| ≤
      2 * Real.log n + 2 := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hy : (1 : ℝ) ≤ (n : ℝ) / k := by
    rw [le_div_iff₀ hk', one_mul]; exact_mod_cast hkn
  have h := log_factorial_floor_approx hy
  rw [Nat.floor_div_eq_div] at h
  have hlog : Real.log ((n : ℝ) / k) ≤ Real.log n := by
    apply Real.log_le_log (by linarith)
    exact div_le_self (by positivity) (by exact_mod_cast hk)
  linarith

/-- Chebyshev's combination is `a n + O(log n)`. -/
private lemma chebS_approx {n : ℕ} (hn : 30 ≤ n) :
    |(Real.log (n ! : ℝ) - Real.log ((n / 2)! : ℝ) - Real.log ((n / 3)! : ℝ) -
        Real.log ((n / 5)! : ℝ) + Real.log ((n / 30)! : ℝ)) -
      (Real.log 2 / 2 + Real.log 3 / 3 + Real.log 5 / 5 - Real.log 30 / 30) * n| ≤
      10 * Real.log n + 10 := by
  have h1 := log_factorial_div_approx (n := n) (k := 1) (by norm_num) (by omega)
  have h2 := log_factorial_div_approx (n := n) (k := 2) (by norm_num) (by omega)
  have h3 := log_factorial_div_approx (n := n) (k := 3) (by norm_num) (by omega)
  have h5 := log_factorial_div_approx (n := n) (k := 5) (by norm_num) (by omega)
  have h30 := log_factorial_div_approx (n := n) (k := 30) (by norm_num) (by omega)
  simp only [Nat.div_one, Nat.cast_one, div_one] at h1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hF : ((n : ℝ) * Real.log n - n) -
      (((n : ℝ) / (2 : ℕ)) * Real.log ((n : ℝ) / (2 : ℕ)) - (n : ℝ) / (2 : ℕ)) -
      (((n : ℝ) / (3 : ℕ)) * Real.log ((n : ℝ) / (3 : ℕ)) - (n : ℝ) / (3 : ℕ)) -
      (((n : ℝ) / (5 : ℕ)) * Real.log ((n : ℝ) / (5 : ℕ)) - (n : ℝ) / (5 : ℕ)) +
      (((n : ℝ) / (30 : ℕ)) * Real.log ((n : ℝ) / (30 : ℕ)) - (n : ℝ) / (30 : ℕ)) =
      (Real.log 2 / 2 + Real.log 3 / 3 + Real.log 5 / 5 - Real.log 30 / 30) * n := by
    push_cast
    rw [Real.log_div hn0.ne' (by norm_num), Real.log_div hn0.ne' (by norm_num),
      Real.log_div hn0.ne' (by norm_num), Real.log_div hn0.ne' (by norm_num)]
    ring
  rw [← hF]
  rw [abs_le] at h1 h2 h3 h5 h30 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h5.1, h5.2, h30.1, h30.2]


/-- Error terms are eventually small: `20 log x + 4 √x log x + c ≤ ε x`. -/
private lemma eventually_error_le {ε c : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in Filter.atTop, 20 * Real.log x + 4 * (√x * Real.log x) + c ≤ ε * x := by
  have hε' : 0 < ε / 48 := by positivity
  have hA := (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).bound hε'
  have hB := isLittleO_log_id_atTop.bound hε'
  filter_upwards [hA, hB, Filter.eventually_ge_atTop (1 : ℝ),
    Filter.eventually_ge_atTop (48 * |c| / ε)] with x hxA hxB hx1 hxc
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hx0 : 0 ≤ x := by linarith
  rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg (by positivity),
    ← Real.sqrt_eq_rpow] at hxA
  rw [Real.norm_of_nonneg hlog, id, Real.norm_of_nonneg hx0] at hxB
  have hsq : √x * √x = x := Real.mul_self_sqrt hx0
  have h1 : √x * Real.log x ≤ ε / 48 * x := by
    calc √x * Real.log x ≤ √x * (ε / 48 * √x) :=
          mul_le_mul_of_nonneg_left hxA (Real.sqrt_nonneg x)
      _ = ε / 48 * (√x * √x) := by ring
      _ = ε / 48 * x := by rw [hsq]
  have h2 : c ≤ ε / 48 * x := by
    have h48 : 48 * |c| ≤ x * ε := by rwa [div_le_iff₀ hε] at hxc
    have hxε : ε / 48 * x = (x * ε) / 48 := by ring
    linarith [le_abs_self c]
  have hεx : 0 ≤ ε * x := by positivity
  linarith

/-- `θ` at a natural number is the sum of `log p` over primes in `(0, n]`. -/
private lemma theta_natCast (n : ℕ) : θ (n : ℝ) = ∑ p ∈ Ioc 0 n with p.Prime, Real.log p := by
  rw [Chebyshev.theta, Nat.floor_natCast]

/-- If `θ` increases between `n` and `M`, there is a prime in `(n, M]`. -/
private lemma exists_prime_of_theta_lt {n M : ℕ} (hnM : n ≤ M) (h : θ (n : ℝ) < θ (M : ℝ)) :
    ∃ q, q.Prime ∧ n < q ∧ q ≤ M := by
  by_contra hno
  push Not at hno
  have hset : ({p ∈ Ioc 0 M | p.Prime} : Finset ℕ) = {p ∈ Ioc 0 n | p.Prime} := by
    ext p
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨h0, hM⟩, hp⟩
      refine ⟨⟨h0, ?_⟩, hp⟩
      by_contra hgt
      exact absurd (hno p hp (by omega)) (by omega)
    · rintro ⟨⟨h0, hn⟩, hp⟩
      exact ⟨⟨h0, hn.trans hnM⟩, hp⟩
  rw [theta_natCast, theta_natCast, hset] at h
  exact lt_irrefl _ h

/-- Chebyshev-type short-interval theorem: for all large `n` there is a prime `q` with
`n < q` and `10 q < 13 n`. -/
private lemma eventually_exists_prime_short :
    ∃ K : ℕ, ∀ n : ℕ, K ≤ n → ∃ q, q.Prime ∧ n < q ∧ 10 * q < 13 * n := by
  set a : ℝ := Real.log 2 / 2 + Real.log 3 / 3 + Real.log 5 / 5 - Real.log 30 / 30 with ha
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 3 / 2 * Real.log 2 < Real.log 3 := by
    have h98 : Real.log 8 < Real.log 9 := Real.log_lt_log (by norm_num) (by norm_num)
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have h9 : Real.log 9 = 2 * Real.log 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  have hl5 : 2 * Real.log 2 < Real.log 5 := by
    have h45 : Real.log 4 < Real.log 5 := Real.log_lt_log (by norm_num) (by norm_num)
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  have ha0 : 0 < a := by rw [ha, hl30]; linarith
  set δ : ℝ := 3 * a / 10 - Real.log 4 / 6 with hδ
  have hδ0 : 0 < δ := by rw [hδ, ha, hl30, hl4]; linarith
  -- eventual smallness of error terms, transported to `x = 2n`
  have hev := eventually_error_le (ε := δ / 4) (c := a + 20) (by positivity)
  have hev2 : ∀ᶠ n : ℕ in Filter.atTop, 20 * Real.log ((2 * n : ℕ) : ℝ) +
      4 * (√((2 * n : ℕ) : ℝ) * Real.log ((2 * n : ℕ) : ℝ)) + (a + 20) ≤
      δ / 4 * ((2 * n : ℕ) : ℝ) := by
    have ht : Filter.Tendsto (fun n : ℕ => ((2 * n : ℕ) : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.comp
        (Filter.tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))
    exact ht.eventually hev
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hev2
  refine ⟨max K 300, fun n hn => ?_⟩
  have hnK : K ≤ n := le_of_max_le_left hn
  have hn300 : 300 ≤ n := le_of_max_le_right hn
  set M : ℕ := (13 * n - 1) / 10 with hM
  have hM1 : 10 * M ≤ 13 * n - 1 := Nat.mul_div_le _ _
  have hM2 : 13 * n - 10 ≤ 10 * M := by omega
  have hnM : n ≤ M := by omega
  have hM30 : 30 ≤ M := by omega
  have hM2n : M ≤ 2 * n := by omega
  suffices hθ : θ (n : ℝ) < θ (M : ℝ) by
    obtain ⟨q, hq, hnq, hqM⟩ := exists_prime_of_theta_lt hnM hθ
    exact ⟨q, hq, hnq, by omega⟩
  -- real-valued facts
  have hnR : (300 : ℝ) ≤ n := by exact_mod_cast hn300
  have hMR : (13 : ℝ) * n - 10 ≤ 10 * M := by
    have : ((13 * n - 10 : ℕ) : ℝ) ≤ ((10 * M : ℕ) : ℝ) := by exact_mod_cast hM2
    rw [Nat.cast_sub (by omega)] at this
    push_cast at this
    linarith
  have hM2nR : (M : ℝ) ≤ 2 * n := by exact_mod_cast hM2n
  have hMR1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
  have hnR1 : (1 : ℝ) ≤ n := by linarith
  have h2n : ((2 * n : ℕ) : ℝ) = 2 * n := by push_cast; ring
  have hlogM : Real.log M ≤ Real.log ((2 * n : ℕ) : ℝ) := by
    rw [h2n]; exact Real.log_le_log (by linarith) hM2nR
  have hlogn : Real.log n ≤ Real.log ((2 * n : ℕ) : ℝ) := by
    rw [h2n]; exact Real.log_le_log (by linarith) (by linarith)
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg hMR1
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hnR1
  have hsqM : √(M : ℝ) * Real.log M ≤ √((2 * n : ℕ) : ℝ) * Real.log ((2 * n : ℕ) : ℝ) := by
    apply mul_le_mul (Real.sqrt_le_sqrt (by rw [h2n]; exact hM2nR)) hlogM hlogM0
      (Real.sqrt_nonneg _)
  -- `n / 6` part
  have hn6 : (1 : ℝ) ≤ ((n / 6 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n / 6)
  have hn6le : ((n / 6 : ℕ) : ℝ) ≤ n / 6 := by
    rw [le_div_iff₀ (by norm_num)]; exact_mod_cast Nat.div_mul_le_self n 6
  have hpsi6 := Chebyshev.psi_le hn6
  have hsq6 : √((n / 6 : ℕ) : ℝ) * Real.log ((n / 6 : ℕ) : ℝ) ≤
      √((2 * n : ℕ) : ℝ) * Real.log ((2 * n : ℕ) : ℝ) := by
    have hle : ((n / 6 : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by rw [h2n]; linarith
    apply mul_le_mul (Real.sqrt_le_sqrt hle) (Real.log_le_log (by linarith) hle)
      (Real.log_nonneg hn6) (Real.sqrt_nonneg _)
  -- sandwiches
  have hSn := chebS_sandwich n
  have hSM := chebS_sandwich M
  have hAn := chebS_approx (by omega : 30 ≤ n)
  have hAM := chebS_approx hM30
  rw [← ha] at hAn hAM
  rw [abs_le] at hAn hAM
  have hθM : ψ (M : ℝ) - θ (M : ℝ) ≤ 2 * (√(M : ℝ) * Real.log M) := by
    rw [← mul_assoc]; exact Chebyshev.psi_sub_theta_le hMR1
  have hpsi6' : ψ ((n / 6 : ℕ) : ℝ) ≤ Real.log 4 * ((n / 6 : ℕ) : ℝ) +
      2 * (√((n / 6 : ℕ) : ℝ) * Real.log ((n / 6 : ℕ) : ℝ)) := by
    rw [← mul_assoc]; exact hpsi6
  have hθn := Chebyshev.theta_le_psi (n : ℝ)
  have hK' := hK n hnK
  have hl4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hK2 : δ / 4 * ((2 * n : ℕ) : ℝ) = 3 / 20 * (a * n) - 1 / 12 * (Real.log 4 * n) := by
    rw [h2n, hδ]; ring
  have hδn : 0 < 3 / 20 * (a * n) - 1 / 12 * (Real.log 4 * n) := by
    rw [← hK2]; positivity
  have hMa : 13 * (a * n) - 10 * a ≤ 10 * (a * M) := by
    have h := mul_le_mul_of_nonneg_left hMR ha0.le
    linarith [h, show a * (13 * n - 10) = 13 * (a * n) - 10 * a by ring,
      show a * (10 * M) = 10 * (a * M) by ring]
  have hl46 : Real.log 4 * ((n / 6 : ℕ) : ℝ) ≤ 1 / 6 * (Real.log 4 * n) := by
    calc Real.log 4 * ((n / 6 : ℕ) : ℝ) ≤ Real.log 4 * (n / 6) :=
          mul_le_mul_of_nonneg_left hn6le hl4pos.le
      _ = 1 / 6 * (Real.log 4 * n) := by ring
  linarith [hSn.1, hSn.2, hSM.1, hSM.2, hAn.1, hAn.2, hAM.1, hAM.2]

/-- `(n+1)² ∣ C(2n, n)` gives `(n+1)!² ∣ (2n)!`. -/
private lemma factorial_sq_dvd_of_sq_dvd_choose {n : ℕ} (h : (n + 1) ^ 2 ∣ Nat.choose (n + n) n) :
    (n + 1)! ^ 2 ∣ (2 * n)! := by
  have h2 : (2 * n)! = Nat.choose (n + n) n * (n ! * n !) := by
    have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left n n)
    rw [Nat.add_sub_cancel] at this
    rw [two_mul, ← this, mul_assoc]
  have h1 : (n + 1)! ^ 2 = (n + 1) ^ 2 * (n ! * n !) := by
    rw [Nat.factorial_succ]; ring
  rw [h1, h2]
  exact mul_dvd_mul h dvd_rfl

end BalakramHelpers

/-- **Balakran's theorem (k = 1; the lemma-mine prize)** ([Ba29]):
    `(n+1)!² ∣ (2n)!` for infinitely many `n`.
    This known infinitude theorem remains unformalized here; no sourced
    infinitude construction is formalized. -/
theorem balakran_k1 :
    {n : ℕ | (n + 1).factorial ^ 2 ∣ (2 * n).factorial}.Infinite := by
  obtain ⟨K, hK⟩ := eventually_exists_prime_short
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (N + K + 20)
  obtain ⟨q, hq, hq1, hq2⟩ := hK (3 * p / 2) (by omega)
  have h1 : 3 * p < 2 * q := by omega
  have h2 : q < 2 * p := by omega
  have hpq : 2 * p ≤ p * q := by
    have : 2 ≤ q := hq.two_le
    nlinarith
  refine ⟨p * q - 1, ?_, by omega⟩
  have hsucc : p * q - 1 + 1 = p * q := by omega
  apply factorial_sq_dvd_of_sq_dvd_choose
  rw [hsucc]
  exact pq_sq_dvd_choose hp hq h1 h2

/-- **Erdős #727 (OPEN, even for k = 2)**: for each `k ≥ 2`,
    `(n+k)!² ∣ (2n)!` for infinitely many `n`. -/
theorem erdos_727 (k : ℕ) (hk : 2 ≤ k) :
    {n : ℕ | (n + k).factorial ^ 2 ∣ (2 * n).factorial}.Infinite := by
  sorry

/-- Satisfiability of the k = 2 property: the production theorem certifies
    `(n+2)!² ∣ (2n)!` at `n = 208`. This single witness does not establish
    infinitude. -/
theorem k2_witness_exists :
    ∃ n : ℕ, (n + 2).factorial ^ 2 ∣ (2 * n).factorial := by
  exact Erdos727.k2_witness_exists

/-- **EGRS mixed-factorial theorem** (EGRS75), archived:
    `(n+k)!(n+1)! ∣ (2n)!` for infinitely many `n` (for each fixed
    `k`; in fact uniformly for `k < c log n`). -/
theorem egrs_mixed (k : ℕ) (hk : 1 ≤ k) :
    {n : ℕ | (n + k).factorial * (n + 1).factorial ∣
      (2 * n).factorial}.Infinite := by
  sorry

/-- Binary digit sum bound: `s₂(x) ≤ log₂ x + 1`. -/
private lemma digitSum_two_le_log (x : ℕ) : (Nat.digits 2 x).sum ≤ Nat.log 2 x + 1 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  have hlen : (Nat.digits 2 x).length = Nat.log 2 x + 1 :=
    Nat.length_digits 2 x (by norm_num) hx.ne'
  have hle : (Nat.digits 2 x).sum ≤ (Nat.digits 2 x).length • 1 :=
    List.sum_le_card_nsmul _ 1 fun d hd =>
      Nat.le_of_lt_succ (Nat.digits_lt_base (by norm_num) hd)
  simpa [hlen] using hle

/-- Legendre at `p = 2`: `v₂(x!) + s₂(x) = x`. -/
private lemma padicValNat_two_factorial_add (x : ℕ) :
    padicValNat 2 x.factorial + (Nat.digits 2 x).sum = x := by
  have h := sub_one_mul_padicValNat_factorial (p := 2) x
  have hs := Nat.digit_sum_le 2 x
  simp only [Nat.reduceSub, one_mul] at h
  omega

/-- If `a! ∣ n!` with `0 < n` then `a ≤ n`. -/
private lemma le_of_factorial_dvd_factorial {a n : ℕ} (hn : 0 < n)
    (h : a.factorial ∣ n.factorial) : a ≤ n := by
  by_contra hlt
  have h1 : n.factorial < a.factorial := (Nat.factorial_lt hn).mpr (not_le.mp hlt)
  have h2 : a.factorial ≤ n.factorial := Nat.le_of_dvd (Nat.factorial_pos n) h
  omega

/-- **Erdős's a!b! ∣ n! bound** ([Er68c]), archived lemma-mine target:
    there is `C` such that `a!·b! ∣ n!` (with `a, b ≥ 1, n ≥ 2`)
    forces `a + b ≤ n + C·log n`.  (Stated with `Nat.log 2` for a
    concrete logarithm; the constant absorbs the base change.) -/
theorem factorial_mul_factorial_dvd_bound :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ a b n : ℕ, 1 ≤ a → 1 ≤ b → 2 ≤ n →
      a.factorial * b.factorial ∣ n.factorial →
      a + b ≤ n + C * Nat.log 2 n := by
  refine ⟨4, by norm_num, fun a b n _ _ hn hdvd => ?_⟩
  have hn0 : 0 < n := by omega
  have ha : a ≤ n :=
    le_of_factorial_dvd_factorial hn0 (dvd_trans (dvd_mul_right _ _) hdvd)
  have hb : b ≤ n :=
    le_of_factorial_dvd_factorial hn0 (dvd_trans (dvd_mul_left _ _) hdvd)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- 2-adic valuations add along `a! * b! ∣ n!`
  have hv : padicValNat 2 a.factorial + padicValNat 2 b.factorial ≤
      padicValNat 2 n.factorial := by
    rw [← padicValNat.mul (Nat.factorial_ne_zero a) (Nat.factorial_ne_zero b)]
    exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).mp
      (dvd_trans pow_padicValNat_dvd hdvd)
  have hla : Nat.log 2 a ≤ Nat.log 2 n := Nat.log_mono_right ha
  have hlb : Nat.log 2 b ≤ Nat.log 2 n := Nat.log_mono_right hb
  have hlog : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by simpa using hn)
  have hsa := digitSum_two_le_log a
  have hsb := digitSum_two_le_log b
  have hea := padicValNat_two_factorial_add a
  have heb := padicValNat_two_factorial_add b
  have hen := padicValNat_two_factorial_add n
  -- a + b ≤ n + s₂(a) + s₂(b) ≤ n + 2 log₂ n + 2 ≤ n + 4 log₂ n
  omega

end ErdosCandidates.E727

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB text exactly.
   - Balakran k=1 claim, EGRS mixed form, Erdos a!b!|n! bound all match DB remarks.
   - OEIS identifiers A002503, A343507, A389396 are recorded above;
     the previously listed unchecked examples were removed.
   - Arithmetic: 6!^2 = 518400, 10! = 3628800, quotient 7. Correct.
   - sq_dvd_iff_dvd_catalan equivalence: (2n)!/(n!)^2 = C(2n,n) = (n+1)*catalan(n),
     so (n+1)!^2 | (2n)! iff (n+1)^2 | C(2n,n) iff (n+1) | catalan(n). Plausible.
   - Lean types faithful to the mathematical content.
-/
