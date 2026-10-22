/-
# A131576 — Pol: even-length consecutive sums via odd and middle divisors

Omar E. Pol's conjecture in OEIS A131576 relates even-length consecutive
positive sums to odd and middle divisors:
`a(n) = (A001227(n)-A067742(n))/2 = A082647(n)-A067742(n)` for `n ≥ 1`.
Here A001227 counts odd divisors, A067742 counts divisors in
`[√(n/2), √(2n))`, and A082647 counts consecutive positive sums whose length
divides `n`.

The positivity convention agrees with the Hirschhorn–Hirschhorn divisor
characterization; the separate conjecture about mirror-image subparts of
sigma is not treated.

The middle-divisor identity used here is Theorem 1 of A067742 (Sloane),
Amer. Math. Monthly Problem 10847 (Chapman–Eriksson–Stanley, solved by
R. Martin), and Hirschhorn–Hirschhorn (2005). Together with Jovovic's
characterization of A082647 it yields Pol's formula. The proof below is a
self-contained dyadic telescoping argument.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A131576CountsRepresentationsSum

open Finset

/-- A131576: number of pairs `(a, k)` with `1 ≤ a`, `1 ≤ k`, `k` even and
`a + (a + 1) + ⋯ + (a + k - 1) = n`. -/
def evenConsecReps (n : ℕ) : ℕ :=
  ((Icc 1 n ×ˢ Icc 1 n).filter
    fun p => Even p.2 ∧ ∑ i ∈ range p.2, (p.1 + i) = n).card

/-- A082647: number of pairs `(a, d)` with `1 ≤ a`, `d ∣ n`, `0 < d` and
`a + (a + 1) + ⋯ + (a + d - 1) = n`. -/
def divisorLengthConsecReps (n : ℕ) : ℕ :=
  ((Icc 1 n ×ˢ n.divisors).filter
    fun p => ∑ i ∈ range p.2, (p.1 + i) = n).card

/-- A001227: number of odd divisors of `n`. -/
def oddDivisorCount (n : ℕ) : ℕ := (n.divisors.filter Odd).card

/-- A067742: number of divisors `d` of `n` with `√(n/2) ≤ d < √(2n)`. -/
def middleDivisorCount (n : ℕ) : ℕ :=
  (n.divisors.filter fun d => n ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * n).card

set_option maxRecDepth 20000 in
example : (List.range 30).map (fun n => evenConsecReps (n + 1)) =
    [0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0,
     2, 1, 1, 0, 1, 1, 2, 0, 1, 1] := by
  decide

set_option maxRecDepth 20000 in
example : (List.range 30).map (fun n => divisorLengthConsecReps (n + 1)) =
    [1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2,
     2, 1, 1, 2, 2, 1, 2, 2, 1, 3] := by
  decide

example : (List.range 30).map (fun n => oddDivisorCount (n + 1)) =
    [1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 2, 2, 2, 2, 4, 1, 2, 3, 2, 2,
     4, 2, 2, 2, 3, 2, 4, 2, 2, 4] := by
  decide

example : (List.range 30).map (fun n => middleDivisorCount (n + 1)) =
    [1, 1, 0, 1, 0, 2, 0, 1, 1, 0, 0, 2, 0, 0, 2, 1, 0, 1, 0, 2,
     0, 0, 0, 2, 1, 0, 0, 2, 0, 2] := by
  decide

/-- Twice the sum of `k` consecutive integers from `a`, plus `k`, is `k (2a + k)`. -/
theorem sum_consec_mul_two_add (a k : ℕ) :
    (∑ i ∈ range k, (a + i)) * 2 + k = k * (2 * a + k) := by
  rw [Finset.sum_add_distrib, add_mul, Finset.sum_range_id_mul_two]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  cases k with
  | zero => simp
  | succ k => simp only [Nat.add_sub_cancel]; ring

/-- The sum of `k` consecutive integers from `a` equals `n` iff `2n + k = k (2a + k)`. -/
theorem sum_consec_eq_iff (a k n : ℕ) :
    ∑ i ∈ range k, (a + i) = n ↔ n * 2 + k = k * (2 * a + k) := by
  rw [← sum_consec_mul_two_add a k]
  constructor
  · rintro rfl; rfl
  · intro h; omega

/-- Every representation `n = a + ⋯ + (a + k - 1)` with `1 ≤ a`, `1 ≤ k` has `a ≤ n` and
`k ≤ n`, so the finite box `Icc 1 n × Icc 1 n` in the definitions loses no representation. -/
theorem le_of_sum_consec_eq {a k n : ℕ} (ha : 1 ≤ a) (hk : 1 ≤ k)
    (h : ∑ i ∈ range k, (a + i) = n) : a ≤ n ∧ k ≤ n := by
  rw [sum_consec_eq_iff] at h
  constructor <;> nlinarith

/-- Even-length representations correspond to odd divisors `c` of `n` with `2n < c²`. -/
theorem evenConsecReps_eq (n : ℕ) (hn : 0 < n) :
    evenConsecReps n = (n.divisors.filter fun c => Odd c ∧ 2 * n < c ^ 2).card := by
  unfold evenConsecReps
  apply Finset.card_bij (fun p _ => 2 * p.1 + p.2 - 1)
  · rintro ⟨a, k⟩ hp
    simp only [mem_filter, mem_product, mem_Icc, sum_consec_eq_iff] at hp
    obtain ⟨⟨⟨ha1, -⟩, -, -⟩, ⟨q, rfl⟩, hsum⟩ := hp
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' ha1
    have hc : 2 * (s + 1) + (q + q) - 1 = 2 * (s + q) + 1 := by omega
    have hnq : n = q * (2 * (s + q) + 1) := by nlinarith
    simp only [mem_filter, Nat.mem_divisors, hc]
    refine ⟨⟨Dvd.intro_left q hnq.symm, hn.ne'⟩, odd_two_mul_add_one _, ?_⟩
    rw [hnq]; nlinarith
  · rintro ⟨a, k⟩ hp ⟨a', k'⟩ hp' heq
    simp only [mem_filter, mem_product, mem_Icc, sum_consec_eq_iff] at hp hp'
    obtain ⟨⟨⟨ha1, -⟩, -, -⟩, -, hsum⟩ := hp
    obtain ⟨⟨⟨ha1', -⟩, -, -⟩, -, hsum'⟩ := hp'
    have hX : 2 * a + k = 2 * a' + k' := by simp only at heq; omega
    rw [hX] at hsum
    have hkk : k = k' := by
      obtain ⟨X, hXdef⟩ : ∃ X, 2 * a' + k' = X + 1 := ⟨2 * a' + k' - 1, by omega⟩
      rw [hXdef] at hsum hsum'
      have h1 : k * X = k' * X := by nlinarith
      have hX0 : X ≠ 0 := by omega
      exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hX0) h1
    subst hkk
    simp only [Prod.mk.injEq, and_true]
    omega
  · intro c hc
    simp only [mem_filter, Nat.mem_divisors] at hc
    obtain ⟨⟨⟨q, rfl⟩, -⟩, ⟨t, rfl⟩, hlt⟩ := hc
    have hq : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have h2q : 2 * q < 2 * t + 1 := by nlinarith
    obtain ⟨s, rfl⟩ : ∃ s, t = q + s := ⟨t - q, by omega⟩
    refine ⟨(s + 1, q + q), ?_, ?_⟩
    · simp only [mem_filter, mem_product, mem_Icc, sum_consec_eq_iff]
      refine ⟨⟨⟨by omega, by nlinarith⟩, by omega, by nlinarith⟩, ⟨q, rfl⟩, by ring⟩
    · simp only; omega

/-- Divisor-length representations (A082647) correspond to odd divisors `c` of `n`
with `c² < 2n`. -/
theorem divisorLengthConsecReps_eq (n : ℕ) (hn : 0 < n) :
    divisorLengthConsecReps n = (n.divisors.filter fun c => Odd c ∧ c ^ 2 < 2 * n).card := by
  unfold divisorLengthConsecReps
  apply Finset.card_bij (fun p _ => p.2)
  · rintro ⟨a, d⟩ hp
    simp only [mem_filter, mem_product, mem_Icc, Nat.mem_divisors, sum_consec_eq_iff] at hp
    obtain ⟨⟨⟨ha1, -⟩, ⟨q, rfl⟩, -⟩, hsum⟩ := hp
    have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have hkey : 2 * q + 1 = 2 * a + d := by
      apply Nat.eq_of_mul_eq_mul_left hd
      linarith
    simp only [mem_filter, Nat.mem_divisors]
    refine ⟨⟨dvd_mul_right d q, hn.ne'⟩, ⟨q - a, by omega⟩, ?_⟩
    have hdq : d < 2 * q := by omega
    nlinarith
  · rintro ⟨a, d⟩ hp ⟨a', d'⟩ hp' heq
    simp only at heq
    subst heq
    simp only [mem_filter, mem_product, mem_Icc, Nat.mem_divisors, sum_consec_eq_iff] at hp hp'
    obtain ⟨⟨-, ⟨q, rfl⟩, -⟩, hsum⟩ := hp
    obtain ⟨-, hsum'⟩ := hp'
    have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have hkey : 2 * a + d = 2 * a' + d := by
      apply Nat.eq_of_mul_eq_mul_left hd
      linarith
    simp only [Prod.mk.injEq, and_true]
    omega
  · intro c hc
    simp only [mem_filter, Nat.mem_divisors] at hc
    obtain ⟨⟨⟨q, rfl⟩, -⟩, ⟨t, rfl⟩, hlt⟩ := hc
    have h2q : 2 * t + 1 < 2 * q := by nlinarith
    obtain ⟨s, rfl⟩ : ∃ s, q = t + 1 + s := ⟨q - t - 1, by omega⟩
    refine ⟨(s + 1, 2 * t + 1), ?_, rfl⟩
    simp only [mem_filter, mem_product, mem_Icc, Nat.mem_divisors, sum_consec_eq_iff]
    refine ⟨⟨⟨by omega, by nlinarith⟩, dvd_mul_right _ _, by omega⟩, by ring⟩

/-- The odd divisors of `n` split by comparing `c²` with `2n` (equality is impossible). -/
theorem oddDivisorCount_eq (n : ℕ) :
    oddDivisorCount n = (n.divisors.filter fun c => Odd c ∧ c ^ 2 < 2 * n).card +
      (n.divisors.filter fun c => Odd c ∧ 2 * n < c ^ 2).card := by
  unfold oddDivisorCount
  rw [← Finset.card_filter_add_card_filter_not (s := n.divisors.filter Odd)
    (fun c => c ^ 2 < 2 * n), Finset.filter_filter, Finset.filter_filter]
  congr 2
  apply Finset.filter_congr
  intro c _
  constructor
  · rintro ⟨hodd, hnot⟩
    refine ⟨hodd, lt_of_le_of_ne (not_lt.1 hnot) ?_⟩
    intro heq
    have h1 : Odd (c ^ 2) := hodd.pow
    rw [← heq] at h1
    exact (Nat.not_even_iff_odd.2 h1) (even_two_mul n)
  · rintro ⟨hodd, hlt⟩
    exact ⟨hodd, not_lt.2 hlt.le⟩

/-- The dyadic level predicate `2 · 4^j · c² < 4 · 2^e · m`, i.e. `c² < 2^(e+1-2j) m`. -/
abbrev Level (e m j c : ℕ) : Prop := 2 * (4 ^ j * c ^ 2) < 4 * (2 ^ e * m)

/-- The level predicate is antitone in `j`. -/
theorem level_of_level_succ {e m j c : ℕ} (h : Level e m (j + 1) c) : Level e m j c := by
  unfold Level at *
  have h4 : 4 ^ (j + 1) * c ^ 2 = 4 * (4 ^ j * c ^ 2) := by ring
  rw [h4] at h
  generalize 4 ^ j * c ^ 2 = A at *
  generalize 2 ^ e * m = B at *
  omega

/-- For odd `m`, the odd divisors of `2^e m` are exactly the divisors of `m`. -/
theorem filter_odd_divisors_eq (e m : ℕ) (hm : Odd m) (Q : ℕ → Prop) [DecidablePred Q] :
    ((2 ^ e * m).divisors.filter fun c => Odd c ∧ Q c) = m.divisors.filter Q := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  ext c
  simp only [mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdvd, -⟩, hodd, hQ⟩
    exact ⟨⟨(Nat.Coprime.pow_right e (Nat.coprime_two_right.2 hodd)).dvd_of_dvd_mul_left hdvd,
      hm0⟩, hQ⟩
  · rintro ⟨⟨hdvd, -⟩, hQ⟩
    exact ⟨⟨dvd_mul_of_dvd_right hdvd _, by positivity⟩, hm.of_dvd_nat hdvd, hQ⟩

/-- The odd divisors `c` of `2^e m` with `c² < 2 · 2^e m` are the divisors of `m` at level `0`. -/
theorem card_small_eq (e m : ℕ) (hm : Odd m) :
    ((2 ^ e * m).divisors.filter fun c => Odd c ∧ c ^ 2 < 2 * (2 ^ e * m)).card =
      (m.divisors.filter (Level e m 0)).card := by
  rw [filter_odd_divisors_eq e m hm (fun c => c ^ 2 < 2 * (2 ^ e * m))]
  congr 1
  apply filter_congr
  intro c _
  unfold Level
  rw [pow_zero, one_mul]
  generalize 2 ^ e * m = B
  omega

/-- With `m = c c'`, the condition `2 · 2^e m < c²` is the level-`(e+1)` condition on `c'`. -/
theorem large_iff (e c c' : ℕ) (hc : 0 < c) (hc' : 0 < c') :
    2 * (2 ^ e * (c * c')) < c ^ 2 ↔ Level e (c * c') (e + 1) c' := by
  unfold Level
  have h4 : (4 : ℕ) ^ (e + 1) = 4 * (2 ^ e * 2 ^ e) := by
    rw [pow_succ, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
    ring_nf
  rw [h4]
  have hX0 : 0 < 2 ^ e := by positivity
  generalize 2 ^ e = X at *
  constructor
  · intro h
    have h1 : 2 * X * c' < c := by nlinarith
    calc 2 * (4 * (X * X) * c' ^ 2) = (4 * X * c') * (2 * X * c') := by ring
      _ < (4 * X * c') * c := Nat.mul_lt_mul_of_pos_left h1 (by positivity)
      _ = 4 * (X * (c * c')) := by ring
  · intro h
    have h1 : 2 * X * c' < c := by nlinarith
    nlinarith

/-- The odd divisors `c` of `2^e m` with `2 · 2^e m < c²` correspond, via `c ↦ m / c`, to the
divisors of `m` at level `e + 1`. -/
theorem card_large_eq (e m : ℕ) (hm : Odd m) :
    ((2 ^ e * m).divisors.filter fun c => Odd c ∧ 2 * (2 ^ e * m) < c ^ 2).card =
      (m.divisors.filter (Level e m (e + 1))).card := by
  rw [filter_odd_divisors_eq e m hm (fun c => 2 * (2 ^ e * m) < c ^ 2)]
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  apply Finset.card_nbij' (m / ·) (m / ·)
  · intro c hc
    simp only [coe_filter, Set.mem_ofPred_eq, Nat.mem_divisors] at hc ⊢
    obtain ⟨⟨⟨c', hc'⟩, -⟩, hlt⟩ := hc
    have hc0 : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp_all)
    have hc'0 : 0 < c' := Nat.pos_of_ne_zero (by rintro rfl; simp_all)
    subst hc'
    rw [Nat.mul_div_cancel_left _ hc0]
    exact ⟨⟨dvd_mul_left _ _, hm0⟩, (large_iff e c c' hc0 hc'0).1 hlt⟩
  · intro c hc
    simp only [coe_filter, Set.mem_ofPred_eq, Nat.mem_divisors] at hc ⊢
    obtain ⟨⟨⟨c', hc'⟩, -⟩, hlt⟩ := hc
    have hc0 : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp_all)
    have hc'0 : 0 < c' := Nat.pos_of_ne_zero (by rintro rfl; simp_all)
    subst hc'
    rw [Nat.mul_div_cancel_left _ hc0]
    refine ⟨⟨dvd_mul_left _ _, hm0⟩, ?_⟩
    rw [mul_comm c c'] at hlt ⊢
    exact (large_iff e c' c hc'0 hc0).2 hlt
  · intro c hc
    simp only [coe_filter, Set.mem_ofPred_eq, Nat.mem_divisors] at hc
    exact Nat.div_div_self hc.1.1 hm0
  · intro c hc
    simp only [coe_filter, Set.mem_ofPred_eq, Nat.mem_divisors] at hc
    exact Nat.div_div_self hc.1.1 hm0

/-- The divisor `2^j c` of `2^e m` is a middle divisor iff `c` is at level `j` but not at
level `j + 1`. -/
theorem middle_iff_level (e m j c : ℕ) :
    (2 ^ e * m ≤ 2 * (2 ^ j * c) ^ 2 ∧ (2 ^ j * c) ^ 2 < 2 * (2 ^ e * m)) ↔
      Level e m j c ∧ ¬ Level e m (j + 1) c := by
  unfold Level
  have h1 : (2 ^ j * c) ^ 2 = 4 ^ j * c ^ 2 := by
    rw [mul_pow, ← pow_mul, mul_comm j 2, pow_mul]
    norm_num
  have h2 : 4 ^ (j + 1) * c ^ 2 = 4 * (4 ^ j * c ^ 2) := by ring
  rw [h1, h2]
  generalize 4 ^ j * c ^ 2 = A
  generalize 2 ^ e * m = B
  omega

/-- The decomposition `d = 2^j c` with `c` odd is unique. -/
theorem two_pow_mul_odd_inj {j j' c c' : ℕ} (hc : Odd c) (hc' : Odd c')
    (h : 2 ^ j * c = 2 ^ j' * c') : j = j' ∧ c = c' := by
  have hval : ∀ (i b : ℕ), Odd b → padicValNat 2 (2 ^ i * b) = i := by
    intro i b hb
    rw [padicValNat.mul (by positivity) hb.pos.ne', padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd]),
      add_zero]
  have hj : j = j' := by rw [← hval j c hc, h, hval j' c' hc']
  subst hj
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) h⟩

/-- The middle divisors of `2^e m` (`m` odd), counted level by level. -/
theorem middleDivisorCount_eq_sum (e m : ℕ) (hm : Odd m) :
    middleDivisorCount (2 ^ e * m) = ∑ j ∈ range (e + 1),
      (m.divisors.filter fun c => Level e m j c ∧ ¬ Level e m (j + 1) c).card := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hsum : ∑ j ∈ range (e + 1),
      (m.divisors.filter fun c => Level e m j c ∧ ¬ Level e m (j + 1) c).card =
      ((range (e + 1) ×ˢ m.divisors).filter
        fun p => Level e m p.1 p.2 ∧ ¬ Level e m (p.1 + 1) p.2).card := by
    rw [card_filter, sum_product]
    simp only [card_filter]
  rw [hsum]
  unfold middleDivisorCount
  symm
  apply Finset.card_bij (fun p _ => 2 ^ p.1 * p.2)
  · rintro ⟨j, c⟩ hp
    simp only [mem_filter, mem_product, mem_range, Nat.mem_divisors] at hp ⊢
    obtain ⟨⟨hj, hdvd, -⟩, hlev⟩ := hp
    refine ⟨⟨mul_dvd_mul (pow_dvd_pow 2 (by omega)) hdvd, by positivity⟩, ?_⟩
    exact (middle_iff_level e m j c).2 hlev
  · rintro ⟨j, c⟩ hp ⟨j', c'⟩ hp' heq
    simp only [mem_filter, mem_product, mem_range, Nat.mem_divisors] at hp hp' heq
    obtain ⟨hjj, hcc⟩ := two_pow_mul_odd_inj (hm.of_dvd_nat hp.1.2.1)
      (hm.of_dvd_nat hp'.1.2.1) heq
    rw [hjj, hcc]
  · intro d hd
    simp only [mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, -⟩, hmid⟩ := hd
    obtain ⟨d₁, c, hd₁, hc, rfl⟩ := Nat.dvd_mul.1 hdvd
    obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd₁
    refine ⟨(j, c), ?_, rfl⟩
    simp only [mem_filter, mem_product, mem_range, Nat.mem_divisors]
    exact ⟨⟨by omega, hc, hm0⟩, (middle_iff_level e m j c).1 hmid⟩

/-- Each level window has size `G j - G (j + 1)`, where `G j` counts divisors at level `j`. -/
theorem card_level_window (e m j : ℕ) :
    ((m.divisors.filter fun c => Level e m j c ∧ ¬ Level e m (j + 1) c).card : ℤ) =
      (m.divisors.filter (Level e m j)).card - (m.divisors.filter (Level e m (j + 1))).card := by
  rw [← card_filter_add_card_filter_not (s := m.divisors.filter (Level e m j))
    (Level e m (j + 1)), filter_filter, filter_filter]
  have hsub : (m.divisors.filter fun c => Level e m j c ∧ Level e m (j + 1) c) =
      m.divisors.filter (Level e m (j + 1)) :=
    filter_congr fun c _ => ⟨And.right, fun h => ⟨level_of_level_succ h, h⟩⟩
  rw [hsub]
  push_cast
  ring

/-- Core identity (Hirschhorn–Hirschhorn): for `n = 2^e m` with `m` odd, the number of middle
divisors equals `#{odd c ∣ n : c² < 2n} - #{odd c ∣ n : 2n < c²}`. -/
theorem middleDivisorCount_two_pow_mul (e m : ℕ) (hm : Odd m) :
    (middleDivisorCount (2 ^ e * m) : ℤ) =
      ((2 ^ e * m).divisors.filter fun c => Odd c ∧ c ^ 2 < 2 * (2 ^ e * m)).card -
      ((2 ^ e * m).divisors.filter fun c => Odd c ∧ 2 * (2 ^ e * m) < c ^ 2).card := by
  rw [middleDivisorCount_eq_sum e m hm, card_small_eq e m hm, card_large_eq e m hm]
  push_cast
  simp_rw [card_level_window]
  exact Finset.sum_range_sub' _ _

/-- **Pol's conjecture (A131576, Omar E. Pol).** For every `n ≥ 1`,
`a(n) = (A001227(n) - A067742(n)) / 2 = A082647(n) - A067742(n)`, where `a(n)` is the number of
representations of `n` as a sum of an even number of consecutive positive integers.
The halving is stated without division as `2 a(n) = A001227(n) - A067742(n)` in `ℤ`. -/
theorem a131576_conjecture (n : ℕ) (hn : 0 < n) :
    2 * (evenConsecReps n : ℤ) = oddDivisorCount n - middleDivisorCount n ∧
      (evenConsecReps n : ℤ) = divisorLengthConsecReps n - middleDivisorCount n := by
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  have hmid := middleDivisorCount_two_pow_mul e m hm
  rw [evenConsecReps_eq _ hn, divisorLengthConsecReps_eq _ hn, oddDivisorCount_eq]
  push_cast
  constructor <;> linarith

end Candidates.A131576CountsRepresentationsSum
