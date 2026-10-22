/-
# A387319 — Scheller: membership is exactly "composite, not 4, 8, 10, 25"

Kenneth J. Scheller's conjecture in OEIS A387319 characterizes membership
as composite numbers other than `4,8,10,25`. Membership means that the
fractions `(2k mod m)/m` coincide at `m = 3` and some other multiple of `3`
with `m ≤ k`.

Robert Israel's conjecture in A343311 characterizes numbers expressible as
`x+y+z` for distinct positive `x,y,z` with `x+y+z ∣ xyz`: composites other
than `4,8,9,25`. Both characterizations are proved below, as is R. J.
Mathar's equality of the two sequences from their third term onward.

Key reduction: with `m = 3j` and `r = 2k mod 3`, the equation
`r/3 = (2k mod 3j)/(3j)` holds iff `2k mod 3j = r j`; this forces `j ∣ 2k`,
and conversely any divisor `j ≡ 1 (mod 3)` of `2k` with `3j ≤ k` works.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A387319SayThereMultiple

/-- `k` is in A387319: some multiple `m` of `3` with `3 < m ≤ k` has
`(2k mod 3)/3 = (2k mod m)/m` as rationals. -/
def InA387319 (k : ℕ) : Prop :=
  ∃ m, 3 < m ∧ m ≤ k ∧ 3 ∣ m ∧
    (((2 * k) % 3 : ℕ) : ℚ) / 3 = (((2 * k) % m : ℕ) : ℚ) / m

/-- Cross-multiplied, bounded natural-number form of `InA387319`. -/
def InA387319Nat (k : ℕ) : Prop :=
  ∃ m < k + 1, 3 < m ∧ 3 ∣ m ∧ (2 * k) % 3 * m = (2 * k) % m * 3

/-- Decidability of the bounded form. -/
instance : DecidablePred InA387319Nat := fun _ => by
  unfold InA387319Nat; infer_instance

/-- The rational equation is equivalent to its cross-multiplied form. -/
theorem inA387319_iff_nat (k : ℕ) : InA387319 k ↔ InA387319Nat k := by
  constructor
  · rintro ⟨m, hm3, hmk, hdvd, heq⟩
    refine ⟨m, by omega, hm3, hdvd, ?_⟩
    have hm0 : (m : ℚ) ≠ 0 := by positivity
    rw [div_eq_div_iff (by norm_num) hm0] at heq
    exact_mod_cast heq
  · rintro ⟨m, hmk, hm3, hdvd, heq⟩
    refine ⟨m, hm3, by omega, hdvd, ?_⟩
    have hm0 : (m : ℚ) ≠ 0 := by positivity
    rw [div_eq_div_iff (by norm_num) hm0]
    exact_mod_cast heq

/-- Decidability transported from `InA387319Nat`. -/
instance : DecidablePred InA387319 := fun k =>
  decidable_of_iff _ (inA387319_iff_nat k).symm

/-- the members up to `40` are the first listed terms of A387319. -/
example : (List.range 41).filter (fun k => decide (InA387319 k)) =
    [6, 9, 12, 14, 15, 16, 18, 20, 21, 22, 24, 26, 27, 28, 30, 32, 33, 34, 35,
      36, 38, 39, 40] := by decide


/-- If `3 ∣ k` and `6 ≤ k`, the multiple `m = 6` witnesses membership. -/
theorem inA387319Nat_of_three_dvd {k : ℕ} (hk : 6 ≤ k) (h3 : 3 ∣ k) :
    InA387319Nat k := by
  refine ⟨6, by omega, by norm_num, by norm_num, ?_⟩
  omega

/-- A divisor `j ≡ 1 (mod 3)` of `2k` with `2 ≤ j` and `3j ≤ k` gives the
witness `m = 3j`. -/
theorem inA387319Nat_of_dvd {k j : ℕ} (hj : 2 ≤ j) (hjk : 3 * j ≤ k)
    (hj1 : j % 3 = 1) (hdvd : j ∣ 2 * k) : InA387319Nat k := by
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨3 * j, by omega, by omega, dvd_mul_right 3 j, ?_⟩
  have hm : 2 * k % (3 * j) = j * (c % 3) := by
    rw [hc, mul_comm 3 j, Nat.mul_mod_mul_left]
  have h3 : 2 * k % 3 = c % 3 := by
    rw [hc, Nat.mul_mod, hj1, one_mul, Nat.mod_mod]
  rw [hm, h3]
  ring

/-- Membership produces `j ≥ 2` with `3j ≤ k`, `j ∣ 2k`, and
`2k mod 3j = (2k mod 3) * j`. -/
theorem exists_dvd_of_inA387319Nat {k : ℕ} (h : InA387319Nat k) :
    ∃ j, 2 ≤ j ∧ 3 * j ≤ k ∧ j ∣ 2 * k ∧ 2 * k % (3 * j) = 2 * k % 3 * j := by
  obtain ⟨m, hmk, hm3, ⟨j, rfl⟩, heq⟩ := h
  have hmod : 2 * k % (3 * j) = 2 * k % 3 * j := by
    have h3 : 2 * k % (3 * j) * 3 = 2 * k % 3 * j * 3 := by
      rw [← heq]; ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h3
  refine ⟨j, by omega, by omega, ?_, hmod⟩
  refine ⟨3 * (2 * k / (3 * j)) + 2 * k % 3, ?_⟩
  have hdm := Nat.div_add_mod (2 * k) (3 * j)
  rw [hmod] at hdm
  calc 2 * k = 3 * j * (2 * k / (3 * j)) + 2 * k % 3 * j := hdm.symm
    _ = j * (3 * (2 * k / (3 * j)) + 2 * k % 3) := by ring

/-- No prime is in A387319. -/
theorem not_inA387319Nat_of_prime {p : ℕ} (hp : p.Prime) : ¬ InA387319Nat p := by
  intro h
  obtain ⟨j, hj2, hjp, hdvd, hmod⟩ := exists_dvd_of_inA387319Nat h
  have hpj : ¬ p ∣ j := fun hd => by
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hcop : Nat.Coprime j p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpj).symm
  have hj : j = 2 := by
    have := Nat.le_of_dvd (by norm_num) (hcop.dvd_of_dvd_mul_right hdvd)
    omega
  subst hj
  have hp3 : p % 3 ≠ 0 := fun h0 => by
    have h3 := (Nat.Prime.eq_one_or_self_of_dvd hp 3 (Nat.dvd_of_mod_eq_zero h0))
    omega
  omega


/-- Odd composites coprime to `3`, other than `25`, are in A387319. -/
theorem inA387319Nat_of_odd {k : ℕ} (hk1 : 1 < k) (hkp : ¬ k.Prime)
    (h2 : k % 2 = 1) (h3 : k % 3 ≠ 0) (h25 : k ≠ 25) : InA387319Nat k := by
  set p := k.minFac with hpdef
  have hpp : p.Prime := Nat.minFac_prime (by omega)
  have hpk : p ∣ k := Nat.minFac_dvd k
  obtain ⟨b, hb⟩ := hpk
  have hp2 : p ≠ 2 := fun h => by rw [h] at hb; omega
  have hp3 : p ≠ 3 := fun h => by rw [h] at hb; omega
  have hp4 : p ≠ 4 := fun h => by rw [h] at hpp; norm_num at hpp
  have hp5 : 5 ≤ p := by have := hpp.two_le; omega
  have hsq : p ^ 2 ≤ k := Nat.minFac_sq_le_self (by omega) hkp
  have hpb : p ≤ b := by
    rw [hb, sq] at hsq
    exact Nat.le_of_mul_le_mul_left hsq (by omega)
  have hb2 : b % 2 = 1 := by
    rcases Nat.even_or_odd b with ⟨t, ht⟩ | ⟨t, ht⟩
    · exfalso; rw [ht] at hb
      have : k = 2 * (p * t) := by rw [hb]; ring
      omega
    · omega
  have hpm3 : p % 3 ≠ 0 := fun h0 => by
    obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero h0
    have : k = 3 * (t * b) := by rw [hb, ht]; ring
    omega
  have hbm3 : b % 3 ≠ 0 := fun h0 => by
    obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero h0
    have : k = 3 * (p * t) := by rw [hb, ht]; ring
    omega
  have hdvd_p : p ∣ 2 * k := Dvd.dvd.mul_left ⟨b, hb⟩ 2
  have hdvd_b : b ∣ 2 * k := Dvd.dvd.mul_left ⟨p, by rw [hb, mul_comm]⟩ 2
  by_cases hp1 : p % 3 = 1
  · refine inA387319Nat_of_dvd (by omega) ?_ hp1 hdvd_p
    rw [hb, mul_comm 3 p]
    exact Nat.mul_le_mul_left p (by omega)
  by_cases hb1 : b % 3 = 1
  · refine inA387319Nat_of_dvd (by omega) ?_ hb1 hdvd_b
    rw [hb]
    exact Nat.mul_le_mul_right b (by omega)
  have hb5 : b ≠ 5 := fun h => by
    have hp : p = 5 := by omega
    rw [hp, h] at hb
    omega
  refine inA387319Nat_of_dvd (j := 2 * p) (by omega) ?_ (by omega)
    (Nat.mul_dvd_mul_left 2 ⟨b, hb⟩)
  rw [hb, ← mul_assoc, mul_comm (3 * 2) p]
  exact Nat.mul_le_mul_left p (by omega)

/-- **Scheller's conjecture (A387319).** `k` is in A387319 iff `k` is
composite and `k ∉ {4, 8, 10, 25}`. -/
theorem inA387319_iff (k : ℕ) :
    InA387319 k ↔ 1 < k ∧ ¬ k.Prime ∧ k ∉ ({4, 8, 10, 25} : Finset ℕ) := by
  rw [inA387319_iff_nat]
  constructor
  · intro h
    obtain ⟨j, hj2, hjk, -, -⟩ := exists_dvd_of_inA387319Nat h
    refine ⟨by omega, fun hp => not_inA387319Nat_of_prime hp h, fun hmem => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl <;> revert h <;> decide
  · rintro ⟨hk1, hkp, hmem⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hmem
    obtain ⟨h4, h8, h10, h25⟩ := hmem
    have hk2 : k ≠ 2 := fun h => hkp (h ▸ Nat.prime_two)
    have hk3 : k ≠ 3 := fun h => hkp (h ▸ Nat.prime_three)
    by_cases h3 : k % 3 = 0
    · exact inA387319Nat_of_three_dvd (by omega) (Nat.dvd_of_mod_eq_zero h3)
    by_cases h2 : k % 2 = 0
    · exact inA387319Nat_of_dvd (j := 4) (by norm_num) (by omega) (by norm_num) (by omega)
    exact inA387319Nat_of_odd hk1 hkp (by omega) h3 h25

/-- Scheller's conjecture, prime half: no prime is in A387319. -/
theorem not_inA387319_of_prime {p : ℕ} (hp : p.Prime) : ¬ InA387319 p := by
  rw [inA387319_iff_nat]
  exact not_inA387319Nat_of_prime hp


/-- `N` is in A343311: `N = x + y + z` for distinct positive integers
`x, y, z` with `N ∣ x * y * z`. -/
def InA343311 (N : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    x + y + z = N ∧ N ∣ x * y * z

/-- Bounded natural-number form of `InA343311`, with `z = N - (x + y)`. -/
def InA343311Nat (N : ℕ) : Prop :=
  ∃ x < N, ∃ y < N, 0 < x ∧ 0 < y ∧ x + y < N ∧ x ≠ y ∧ x ≠ N - (x + y) ∧
    y ≠ N - (x + y) ∧ N ∣ x * y * (N - (x + y))

/-- Decidability of the bounded form. -/
instance : DecidablePred InA343311Nat := fun _ => by
  unfold InA343311Nat; infer_instance

/-- The bounded form is equivalent to the definition. -/
theorem inA343311_iff_nat (N : ℕ) : InA343311 N ↔ InA343311Nat N := by
  constructor
  · rintro ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz, hsum, hdvd⟩
    have hzN : z = N - (x + y) := by omega
    subst hzN
    exact ⟨x, by omega, y, by omega, hx, hy, by omega, hxy, hxz, hyz, hdvd⟩
  · rintro ⟨x, -, y, -, hx, hy, hxyN, hxy, hxz, hyz, hdvd⟩
    exact ⟨x, y, N - (x + y), hx, hy, by omega, hxy, hxz, hyz, by omega, hdvd⟩

/-- Decidability transported from `InA343311Nat`. -/
instance : DecidablePred InA343311 := fun N =>
  decidable_of_iff _ (inA343311_iff_nat N).symm

/-- the members up to `30` are the first listed terms of A343311. -/
example : (List.range 31).filter (fun N => decide (InA343311 N)) =
    [6, 10, 12, 14, 15, 16, 18, 20, 21, 22, 24, 26, 27, 28, 30] := by decide

/-- `a * b` with `2 ≤ a < b`, `b ≠ 2a` is in A343311 via `(a, b(a-1), b-a)`. -/
theorem inA343311_mul {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) (h2 : b ≠ 2 * a) :
    InA343311 (a * b) := by
  obtain ⟨s, rfl⟩ : ∃ s, a = s + 1 := ⟨a - 1, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t, b = s + 1 + t := ⟨b - (s + 1), by omega⟩
  have hbs : s + 1 + t ≤ (s + 1 + t) * s := Nat.le_mul_of_pos_right _ (by omega)
  refine ⟨s + 1, (s + 1 + t) * s, t, by omega, by nlinarith, by omega, by omega,
    by omega, by omega, by ring, ?_⟩
  exact ⟨s * t, by ring⟩

/-- `a * a` with `6 ≤ a` is in A343311 via `(a, 2a, a(a-3))`. -/
theorem inA343311_sq {a : ℕ} (ha : 6 ≤ a) : InA343311 (a * a) := by
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 3 := ⟨a - 3, by omega⟩
  have hc : 3 * (c + 3) ≤ (c + 3) * c := by nlinarith
  refine ⟨c + 3, 2 * (c + 3), (c + 3) * c, by omega, by omega, by nlinarith,
    by omega, by omega, by omega, by ring, ?_⟩
  exact ⟨2 * c * (c + 3), by ring⟩

/-- No prime is in A343311. -/
theorem not_inA343311_of_prime {p : ℕ} (hp : p.Prime) : ¬ InA343311 p := by
  rintro ⟨x, y, z, hx, hy, hz, -, -, -, hsum, hdvd⟩
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with hxy | hzd
  · rcases (Nat.Prime.dvd_mul hp).mp hxy with hxd | hyd
    · have := Nat.le_of_dvd hx hxd; omega
    · have := Nat.le_of_dvd hy hyd; omega
  · have := Nat.le_of_dvd hz hzd; omega

/-- **Israel's conjecture (A343311).** `N` is in A343311 iff `N` is
composite and `N ∉ {4, 8, 9, 25}`. -/
theorem inA343311_iff (N : ℕ) :
    InA343311 N ↔ 1 < N ∧ ¬ N.Prime ∧ N ∉ ({4, 8, 9, 25} : Finset ℕ) := by
  constructor
  · intro h
    have hN : 1 < N := by
      obtain ⟨x, y, z, hx, hy, hz, hxy, -, -, hsum, -⟩ := h
      omega
    refine ⟨hN, fun hp => not_inA343311_of_prime hp h, fun hmem => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl <;> revert h <;> decide
  · rintro ⟨hN1, hNp, hmem⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hmem
    obtain ⟨h4, h8, h9, h25⟩ := hmem
    set a := N.minFac with hadef
    have hap : a.Prime := Nat.minFac_prime (by omega)
    obtain ⟨b, hb⟩ : a ∣ N := Nat.minFac_dvd N
    have ha2 : 2 ≤ a := hap.two_le
    have hsq : a ^ 2 ≤ N := Nat.minFac_sq_le_self (by omega) hNp
    have hab : a ≤ b := by
      rw [hb, sq] at hsq
      exact Nat.le_of_mul_le_mul_left hsq (by omega)
    rcases Nat.lt_or_eq_of_le hab with hlt | heq
    · by_cases h2 : b = 2 * a
      · exfalso
        have hmin : a ≤ 2 := Nat.minFac_le_of_dvd (le_refl 2) ⟨a * a, by rw [hb, h2]; ring⟩
        have ha : a = 2 := by omega
        rw [ha] at h2
        rw [hb, ha, h2] at h8
        exact h8 rfl
      · rw [hb]
        exact inA343311_mul ha2 hlt h2
    · rw [hb, ← heq]
      have h3 : a ≠ 3 := fun h => h9 (by rw [hb, ← heq, h])
      have h2 : a ≠ 2 := fun h => h4 (by rw [hb, ← heq, h])
      have h5 : a ≠ 5 := fun h => h25 (by rw [hb, ← heq, h])
      have h4' : a ≠ 4 := fun h => by rw [h] at hap; norm_num at hap
      exact inA343311_sq (by omega)


/-- From `11` on, A387319 and A343311 have the same members. -/
theorem inA387319_iff_inA343311 {k : ℕ} (hk : 11 ≤ k) : InA387319 k ↔ InA343311 k := by
  rw [inA387319_iff, inA343311_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1, h2, by omega⟩

/-- A387319 has exactly two members below `11` (namely `6` and `9`). -/
theorem count_inA387319_eleven : Nat.count InA387319 11 = 2 := by decide

/-- A343311 has exactly two members below `11` (namely `6` and `10`). -/
theorem count_inA343311_eleven : Nat.count InA343311 11 = 2 := by decide

/-- The two counting functions agree from `11` on. -/
theorem count_inA387319_eq_count_inA343311 {x : ℕ} (hx : 11 ≤ x) :
    Nat.count InA387319 x = Nat.count InA343311 x := by
  obtain ⟨t, rfl⟩ : ∃ t, x = 11 + t := ⟨x - 11, by omega⟩
  rw [Nat.count_add, Nat.count_add, count_inA387319_eleven, count_inA343311_eleven,
    Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  congr 2
  exact Finset.filter_congr fun k _ => inA387319_iff_inA343311 (by omega)

/-- A387319 is infinite: it contains every positive multiple of `6`. -/
theorem infinite_inA387319 : (Set.ofPred InA387319).Infinite := by
  refine Set.infinite_of_forall_exists_gt fun a => ⟨6 * (a + 1), ?_, by omega⟩
  show InA387319 (6 * (a + 1))
  rw [inA387319_iff_nat]
  exact inA387319Nat_of_three_dvd (by omega) ⟨2 * (a + 1), by ring⟩

/-- **Mathar's conjecture (A387319).** `A387319(n) = A343311(n)`
for `n ≥ 3` (OEIS offset 1); with `Nat.nth` indexed from `0` this is
`nth InA387319 n = nth InA343311 n` for `2 ≤ n`. -/
theorem nth_inA387319_eq_nth_inA343311 (n : ℕ) (hn : 2 ≤ n) :
    Nat.nth InA387319 n = Nat.nth InA343311 n := by
  set x := Nat.nth InA387319 n with hxdef
  have hPx : InA387319 x := Nat.nth_mem_of_infinite infinite_inA387319 n
  have hcx : Nat.count InA387319 x = n := Nat.count_nth_of_infinite infinite_inA387319 n
  have hx : 11 ≤ x := by
    by_contra hlt
    have hlt' := Nat.count_strict_mono hPx (not_le.mp hlt)
    rw [count_inA387319_eleven] at hlt'
    omega
  have hQx : InA343311 x := (inA387319_iff_inA343311 hx).mp hPx
  have hcq : Nat.count InA343311 x = n := by
    rw [← count_inA387319_eq_count_inA343311 hx, hcx]
  rw [← hcq]
  exact (Nat.nth_count hQx).symm

end Candidates.A387319SayThereMultiple
