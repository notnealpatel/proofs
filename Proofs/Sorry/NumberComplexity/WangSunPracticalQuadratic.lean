/-
# Wang–Sun conjecture, part (2): `n ^ 2 + b n + c` is practical for some `1 < n ≤ max {b, c}`

## Source

Ting Hon Stanford Li, *A Short Proof of a Conjecture Regarding Quadratic
Representations of Practical Numbers*, arXiv:2608.25591.  The statement is the
paper's Conjecture 1(2) (due to L.-Y. Wang and Z.-W. Sun, *On practical numbers of
some special forms*, Houston J. Math. 48 (2022), 241–247), proved as the Theorem of
Section 2 using Lemmas 3–4 (root count modulo `2 ^ m` via Hensel, and the bound
`f(n₁) < 2 ^ (2m+1)`) and Melfi's Lemma 1.

Verbatim informal claim (arXiv:2608.25591, Theorem):

> Let $b$,$c$ be positive integers such that $b$ is odd and $c$ is even. Then there
> is an integer $n$ with $1 < n \leq \max\{b,c\}$ such that $n^2 + bn +c$ is
> practical.

Recorded 2026-10-21.  Status: proved in the paper (literature status
proved-in-paper); this module gives a complete, `sorry`-free Lean proof.

## Definitions

`Nat.Practical` is the repository's definition (`Proofs/Enumerative/Practical.lean`):
`0 < n` and every `m ≤ n` is a sum of distinct divisors of `n` — exactly the paper's
definition in its abstract.  Melfi's Lemma 1 is the repository's
`Nat.Practical.mul_of_le_two_mul` (`Proofs/Enumerative/MelfiPracticalSum.lean`).

## Route (differs slightly from the paper)

With `N = 2 ^ m`, `m = ⌊log₂ max {b, c}⌋ ≥ 1`:
* one root `r < N` of `f ≡ 0 (mod N)` by an explicit Hensel-type lift
  (`exists_root_two_pow`);
* its partner `s < N` with `N ∣ r + s + b` by the symmetry `x ↦ -b - x`
  (`exists_partner`), replacing the paper's parity/coprimality argument;
* the paper's Cases 1–3 on `u + v + b = j N`, `j ∈ {1, 2, 3}`
  (`exists_of_root_pair`), each closing with Melfi's Lemma 1.
-/
import Mathlib
import Enumerative.Practical
import Enumerative.MelfiPracticalSum

set_option autoImplicit false

namespace WangSunPracticalQuadratic

/-- Melfi's Lemma 1 at a power of two: a positive multiple `x` of `2 ^ m` with
`x ≤ 2 * 2 ^ m * 2 ^ m` is practical. -/
theorem practical_of_two_pow_dvd {m x : ℕ} (hdvd : 2 ^ m ∣ x) (hx : 0 < x)
    (hle : x ≤ 2 * 2 ^ m * 2 ^ m) : x.Practical := by
  obtain ⟨k, rfl⟩ := hdvd
  have hk : 0 < k := Nat.pos_of_mul_pos_left hx
  have hk2 : k ≤ 2 * 2 ^ m := by
    have hmul : 2 ^ m * k ≤ 2 ^ m * (2 * 2 ^ m) := by
      calc 2 ^ m * k ≤ 2 * 2 ^ m * 2 ^ m := hle
        _ = 2 ^ m * (2 * 2 ^ m) := by ring
    exact Nat.le_of_mul_le_mul_left hmul (by positivity)
  exact (Nat.practical_two_pow m).mul_of_le_two_mul hk hk2

/-- Root existence (the Hensel step of the paper's Lemma 3, done by hand): for `b` odd
and `c` even, `x ^ 2 + b x + c ≡ 0 (mod 2 ^ j)` has a root in `[0, 2 ^ j)` for every
`j ≥ 1`. -/
theorem exists_root_two_pow {b c : ℕ} (hb : Odd b) (hc : Even c) :
    ∀ j, 1 ≤ j → ∃ r < 2 ^ j, 2 ^ j ∣ r ^ 2 + b * r + c := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => exact ⟨0, by norm_num, by simpa using even_iff_two_dvd.mp hc⟩
  | succ j hj ih =>
    obtain ⟨r, hr, k, hk⟩ := ih
    by_cases hk2 : 2 ∣ k
    · obtain ⟨k', rfl⟩ := hk2
      refine ⟨r, by rw [pow_succ]; omega, k', by rw [hk, pow_succ]; ring⟩
    · refine ⟨r + 2 ^ j, by rw [pow_succ]; omega, ?_⟩
      have hkodd : k % 2 = 1 := by omega
      have hbodd : b % 2 = 1 := Nat.odd_iff.mp hb
      have hPeven : 2 ^ j % 2 = 0 :=
        Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
      have heven : 2 ∣ k + 2 * r + b + 2 ^ j := by
        generalize 2 ^ j = P at hPeven
        omega
      obtain ⟨t, ht⟩ := heven
      refine ⟨t, ?_⟩
      calc (r + 2 ^ j) ^ 2 + b * (r + 2 ^ j) + c
          = (r ^ 2 + b * r + c) + 2 ^ j * (2 * r + b + 2 ^ j) := by ring
        _ = 2 ^ j * (k + 2 * r + b + 2 ^ j) := by rw [hk]; ring
        _ = 2 ^ (j + 1) * t := by rw [ht]; ring

/-- Partner root: if `r` is a root of `x ^ 2 + b x + c` modulo `N`, so is the residue
`s ∈ [0, N)` of `-b - r`, because `f(s) - f(r) = (s - r)(s + r + b)`. -/
theorem exists_partner {N b c r : ℕ} (hN : 0 < N) (hr : N ∣ r ^ 2 + b * r + c) :
    ∃ s < N, N ∣ s ^ 2 + b * s + c ∧ N ∣ r + s + b := by
  have hdm := Nat.div_add_mod (r + b) N
  have hmlt := Nat.mod_lt (r + b) hN
  obtain ⟨s, hsN, hsum⟩ : ∃ s < N, N ∣ r + s + b := by
    by_cases ht : (r + b) % N = 0
    · exact ⟨0, hN, ⟨(r + b) / N, by omega⟩⟩
    · refine ⟨N - (r + b) % N, by omega, ⟨(r + b) / N + 1, ?_⟩⟩
      rw [Nat.mul_add, Nat.mul_one]
      omega
  refine ⟨s, hsN, ?_, hsum⟩
  have hid : ((s ^ 2 + b * s + c : ℕ) : ℤ)
      = ((r ^ 2 + b * r + c : ℕ) : ℤ) + ((s : ℤ) - r) * ((r + s + b : ℕ) : ℤ) := by
    push_cast; ring
  have hZ : (N : ℤ) ∣ ((s ^ 2 + b * s + c : ℕ) : ℤ) := by
    rw [hid]
    exact dvd_add (Int.natCast_dvd_natCast.mpr hr)
      (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hsum) _)
  exact Int.natCast_dvd_natCast.mp hZ

/-- The paper's three-case argument (Theorem, Cases 1–3, with Lemma 4's bound), stated
for a pair of roots `u ≤ v < 2 ^ m` of `x ^ 2 + b x + c` modulo `2 ^ m` linked by
`2 ^ m ∣ u + v + b`, where `2 ^ m ≤ max b c < 2 ^ (m + 1)`. -/
theorem exists_of_root_pair {m b c u v : ℕ} (hm : 1 ≤ m) (hb : Odd b) (hc : Even c)
    (hc0 : 0 < c) (hbN : b < 2 * 2 ^ m) (hcN : c < 2 * 2 ^ m) (hNM : 2 ^ m ≤ max b c)
    (huv : u ≤ v) (hv : v < 2 ^ m) (hfu : 2 ^ m ∣ u ^ 2 + b * u + c)
    (hfv : 2 ^ m ∣ v ^ 2 + b * v + c) (hsum : 2 ^ m ∣ u + v + b) :
    ∃ n, 1 < n ∧ n ≤ max b c ∧ (n ^ 2 + b * n + c).Practical := by
  have hbodd : b % 2 = 1 := Nat.odd_iff.mp hb
  have hceven : c % 2 = 0 := Nat.even_iff.mp hc
  have hNeven : 2 ^ m % 2 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
  have hN2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hpos : ∀ n, 0 < n ^ 2 + b * n + c := fun n => by positivity
  -- the smaller root `u`, when it exceeds `1`, with the bound `f(u) ≤ 2 N²`
  have hcase_u : 2 ≤ u → u ^ 2 + b * u + c ≤ 2 * 2 ^ m * 2 ^ m →
      ∃ n, 1 < n ∧ n ≤ max b c ∧ (n ^ 2 + b * n + c).Practical := fun h2 hle =>
    ⟨u, by omega, by omega, practical_of_two_pow_dvd hfu (hpos u) hle⟩
  have hcase_v : 2 ≤ v → v ^ 2 + b * v + c ≤ 2 * 2 ^ m * 2 ^ m →
      ∃ n, 1 < n ∧ n ≤ max b c ∧ (n ^ 2 + b * n + c).Practical := fun h2 hle =>
    ⟨v, by omega, by omega, practical_of_two_pow_dvd hfv (hpos v) hle⟩
  obtain ⟨j, hj⟩ := hsum
  set N := 2 ^ m with hNdef
  have hj3 : j ≤ 3 := by
    by_contra hcon
    have h4 : N * 4 ≤ N * j := Nat.mul_le_mul_left N (by omega)
    omega
  have hNN : 2 * N ≤ N * N := Nat.mul_le_mul_right N hN2
  -- Case 3 of the paper: `(u, v) = (0, 1)` forces `c = N`
  have hc_eq : u = 0 → c = N := by
    intro hu0
    subst hu0
    obtain ⟨k, hk⟩ : N ∣ c := by simpa using hfu
    have hk2 : k < 2 := by
      by_contra hcon
      have h2k : N * 2 ≤ N * k := Nat.mul_le_mul_left N (by omega)
      omega
    interval_cases k <;> omega
  interval_cases j
  · omega
  · -- `u + v + b = N`
    by_cases hu2 : 2 ≤ u
    · apply hcase_u hu2
      have h1 : u * (u + b) ≤ N * N := Nat.mul_le_mul (by omega) (by omega)
      nlinarith
    · by_cases hv2 : 2 ≤ v
      · apply hcase_v hv2
        have h1 : v * (v + b) ≤ N * N := Nat.mul_le_mul (by omega) (by omega)
        nlinarith
      · -- Subcase 3a: `u = 0`, `v = 1`, `b + 1 = N`, `c = N`; take `n = N`
        have hu0 : u = 0 := by omega
        have hcN' : c = N := hc_eq hu0
        have hb1 : b + 1 = N := by omega
        have hfN : N ^ 2 + b * N + c = N * (N + (b + 1)) := by rw [hcN']; ring
        refine ⟨N, by omega, hNM, practical_of_two_pow_dvd ⟨N + (b + 1), hfN⟩ (hpos N) ?_⟩
        rw [hfN, hb1]
        nlinarith
  · -- `u + v + b = 2 N`
    by_cases hu2 : 2 ≤ u
    · apply hcase_u hu2
      have h1 : (2 * u + b + 1) * (2 * u + b + 1) ≤ (2 * N) * (2 * N) :=
        Nat.mul_le_mul (by omega) (by omega)
      nlinarith
    · by_cases hv2 : 2 ≤ v
      · apply hcase_v hv2
        have h1 : v * (v + b) ≤ (N - 1) * (2 * N) := Nat.mul_le_mul (by omega) (by omega)
        have h2 : (N - 1) * (2 * N) + 2 * N = 2 * N * N := by
          obtain ⟨N', hN'⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
          rw [hN']; simp only [Nat.add_sub_cancel]; ring
        nlinarith
      · -- Subcase 3b: `u = 0`, `v = 1`, `b + 1 = 2 N`, `c = N`; take `n = N`
        have hu0 : u = 0 := by omega
        have hcN' : c = N := hc_eq hu0
        have hb1 : b + 1 = 2 * N := by omega
        have hfN : N ^ 2 + b * N + c = 2 ^ (m * 2) * 3 := by
          rw [hcN', pow_mul, ← hNdef]
          calc N ^ 2 + b * N + N = N * N + N * (b + 1) := by ring
            _ = N ^ 2 * 3 := by rw [hb1]; ring
        have h3 : 3 ≤ 2 * 2 ^ (m * 2) := by
          rw [pow_mul, ← hNdef]
          nlinarith
        refine ⟨N, by omega, hNM, ?_⟩
        rw [hfN]
        exact (Nat.practical_two_pow (m * 2)).mul_of_le_two_mul (by norm_num) h3
  · -- `u + v + b = 3 N`: here `b ≥ N + 3`, and `u ≤ 1` is impossible
    have hu2 : 2 ≤ u := by omega
    apply hcase_u hu2
    have h1 : (2 * u + b + 1) * (2 * u + b + 1) ≤ (3 * N) * (3 * N) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : (N + 3) * (N + 3) ≤ b * b := Nat.mul_le_mul (by omega) (by omega)
    nlinarith

/-- **Wang–Sun conjecture, part (2)** (Wang–Sun, Houston J. Math. 48 (2022), Conjecture;
proved by T. H. S. Li, arXiv:2608.25591, Theorem in Section 2): for positive integers
`b`, `c` with `b` odd and `c` even, there is an integer `n` with `1 < n ≤ max {b, c}`
such that `n ^ 2 + b n + c` is a practical number. (`b` odd already forces `0 < b`.) -/
theorem wang_sun_part_two (b c : ℕ) (hb : Odd b) (hc : Even c) (hc0 : 0 < c) :
    ∃ n, 1 < n ∧ n ≤ max b c ∧ (n ^ 2 + b * n + c).Practical := by
  have hceven : c % 2 = 0 := Nat.even_iff.mp hc
  have hM2 : 2 ≤ max b c := le_max_of_le_right (by omega)
  set m := Nat.log 2 (max b c) with hmdef
  have hm : 1 ≤ m := Nat.log_pos (by norm_num) hM2
  have hNM : 2 ^ m ≤ max b c := Nat.pow_log_le_self 2 (by omega)
  have hMN : max b c < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hbN : b < 2 * 2 ^ m := by rw [pow_succ] at hMN; omega
  have hcN : c < 2 * 2 ^ m := by rw [pow_succ] at hMN; omega
  obtain ⟨r, hr, hfr⟩ := exists_root_two_pow hb hc m hm
  obtain ⟨s, hs, hfs, hsum⟩ := exists_partner (by positivity) hfr
  rcases le_total r s with hrs | hsr
  · exact exists_of_root_pair hm hb hc hc0 hbN hcN hNM hrs hs hfr hfs hsum
  · refine exists_of_root_pair hm hb hc hc0 hbN hcN hNM hsr hr hfs hfr ?_
    rwa [Nat.add_comm s r]

/-- Ground truth: the smallest instance `b = 1`, `c = 2` (`max = 2`) is witnessed by
`n = 2`, with `2 ^ 2 + 1 * 2 + 2 = 8` practical; this is the paper's Subcase 3a. -/
example : ∃ n, 1 < n ∧ n ≤ max 1 2 ∧ (n ^ 2 + 1 * n + 2).Practical :=
  ⟨2, by decide, by decide, by decide⟩

/-- Ground truth: `8` is practical and `10 = 2 * 5` is not, so `Nat.Practical` is not
trivial on the values `n ^ 2 + b n + c`. -/
example : (8 : ℕ).Practical ∧ ¬ (10 : ℕ).Practical := by decide

/-- Non-vacuity: the hypotheses of `wang_sun_part_two` hold jointly at `b = 3`,
`c = 4`; the theorem then yields a witness `n ∈ (1, 4]`. -/
example : ∃ n, 1 < n ∧ n ≤ max 3 4 ∧ (n ^ 2 + 3 * n + 4).Practical :=
  wang_sun_part_two 3 4 ⟨1, rfl⟩ ⟨2, rfl⟩ (by norm_num)

end WangSunPracticalQuadratic
