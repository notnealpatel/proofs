/-
# A088827: Rascoe's dispersion-array identity

OEIS A088827, John Tyler Rascoe (Jul 12 2022), with A191432 and A001953.
Positive even numbers of odd abundance are exactly `4j²` or `2j²`, `j ≥ 1`.
Doubling acts on their ranks by the Beatty map defining the dispersion.
With rows and columns starting at zero, row `r`, column `c` contains the
rank of `(2r+1)² * 2^(c+1)`. Every positive rank occurs in the array.
Abundance is computed in `ℤ`.
-/
import Mathlib
import Enumerative.A016957ContainsSomeBut

set_option autoImplicit false

namespace Candidates.A088827RascoeSitsRow

open ArithmeticFunction Finset
open Candidates.A016957ContainsSomeBut (IsA088827 abundance odd_sigma_sq
  exists_two_pow_mul_sq_of_odd_sigma odd_abundance_iff odd_geom_sum_of_even)

/-! ## Definitions

Reused verbatim from `Proofs/Enumerative/A016957ContainsSomeBut.lean`:

* `abundance k : ℤ := σ₁(k) - 2k` (in `ℤ`, so deficient numbers are negative);
* `IsA088827 k : Prop := 0 < k ∧ Even k ∧ Odd (abundance k)` — the entry's
  NAME "even numbers with odd abundance", with a `Decidable` instance. -/

/-- A088827 with the entry's offset `1`: `a n` is the `n`-th even number with
odd abundance (`a 1 = 2`). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsA088827 (n - 1)

/-- The map dispersed in A191432 (A001953): `s(m) = ⌊m·√2 + 1/√2⌋`. -/
noncomputable def s (m : ℕ) : ℕ := ⌊(m : ℝ) * √2 + 1 / √2⌋₊

/-- `k` starts a row of the dispersion: `k` is a positive integer outside the
range of `s` (the complement `t` of the entry, with `t(1) = 1`).  Since
`s 0 = 0`, ranging `m` over all of `ℕ` agrees with ranging over `m ≥ 1`. -/
def IsRowStart (k : ℕ) : Prop := 0 < k ∧ ∀ m, s m ≠ k

/-- `rowStart r`: the `r`-th (0-indexed) element, in increasing order, of the
complement of `s` in the positive integers. -/
noncomputable def rowStart (r : ℕ) : ℕ := Nat.nth IsRowStart r

/-- A191432 as an array, rows and columns 0-indexed: row `r` is
`t, s(t), s(s(t)), …` with `t = rowStart r`. -/
noncomputable def T (r c : ℕ) : ℕ := s^[c] (rowStart r)

/-! ## Examples for `a` -/

/-- `a (count b + 1) = b` for every term `b` (used for the data checks). -/
theorem a_count_add_one {b : ℕ} (hb : IsA088827 b) :
    a (Nat.count IsA088827 b + 1) = b := by
  rw [a, Nat.add_sub_cancel, Nat.nth_count hb]

-- A088827 data line: its members below `100` are `2, 4, 8, …, 98`.
example : ∀ k < 100, IsA088827 k ↔
    k ∈ ({2, 4, 8, 16, 18, 32, 36, 50, 64, 72, 98} : Finset ℕ) := by decide

-- A088827 data line: `a 1 = 2`, `a 5 = 18`, `a 12 = 100`.
example : a 1 = 2 := by
  rw [show 1 = Nat.count IsA088827 2 + 1 by decide, a_count_add_one (by decide)]

example : a 5 = 18 := by
  rw [show 5 = Nat.count IsA088827 18 + 1 by decide, a_count_add_one (by decide)]

example : a 12 = 100 := by
  rw [show 12 = Nat.count IsA088827 100 + 1 by decide, a_count_add_one (by decide)]

/-! ## Proof -/

/-! ### The map `s` in integers -/

/-- Integer form of `s`: `⌊(2m+1)/√2⌋ = ⌊√((2m+1)²/2)⌋`. -/
def sNat (m : ℕ) : ℕ := Nat.sqrt ((2 * m + 1) ^ 2 / 2)

/-- `sNat m = y` as soon as `2y² ≤ (2m+1)² < 2(y+1)²`. -/
theorem sNat_eq_of {m y : ℕ} (h1 : 2 * y ^ 2 ≤ (2 * m + 1) ^ 2)
    (h2 : (2 * m + 1) ^ 2 < 2 * (y + 1) ^ 2) : sNat m = y := by
  unfold sNat
  symm
  rw [Nat.eq_sqrt']
  constructor
  · rw [Nat.le_div_iff_mul_le (by norm_num)]; linarith
  · rw [Nat.div_lt_iff_lt_mul (by norm_num)]; linarith

/-- Bounds characterizing `sNat m`. -/
theorem sNat_spec (m : ℕ) :
    2 * sNat m ^ 2 ≤ (2 * m + 1) ^ 2 ∧ (2 * m + 1) ^ 2 < 2 * (sNat m + 1) ^ 2 := by
  unfold sNat
  generalize (2 * m + 1) ^ 2 = K
  have h1 := Nat.sqrt_le' (K / 2)
  have h2 := Nat.lt_succ_sqrt' (K / 2)
  have h3 := Nat.div_add_mod K 2
  have h4 := Nat.mod_lt K (show 0 < 2 by norm_num)
  generalize K / 2 = q at h1 h2 h3
  generalize Nat.sqrt q = y at h1 h2
  rw [Nat.succ_eq_add_one] at h2
  have h5 := Nat.zero_le (K % 2)
  constructor <;> nlinarith

/-- The real-floor definition agrees with the integer form. -/
theorem s_eq_sNat (m : ℕ) : s m = sNat m := by
  obtain ⟨h1, h2⟩ := sNat_spec m
  have hs2 : (0 : ℝ) < √2 := by positivity
  have hsq : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hx : (m : ℝ) * √2 + 1 / √2 = (2 * m + 1) / √2 := by
    field_simp
    nlinarith [hsq]
  unfold s
  rw [hx, Nat.floor_eq_iff (by positivity), le_div_iff₀ hs2, div_lt_iff₀ hs2]
  set y := sNat m
  have h1' : (2 : ℝ) * (y : ℝ) ^ 2 ≤ (2 * (m : ℝ) + 1) ^ 2 := by exact_mod_cast h1
  have h2' : (2 * (m : ℝ) + 1) ^ 2 < 2 * ((y : ℝ) + 1) ^ 2 := by exact_mod_cast h2
  constructor
  · have hpos : (0 : ℝ) ≤ 2 * m + 1 := by positivity
    nlinarith [sq_nonneg ((y : ℝ) * √2 - (2 * m + 1)), sq_nonneg ((y:ℝ) * √2 + (2 * m + 1))]
  · by_contra hle
    rw [not_lt] at hle
    have hnn : (0 : ℝ) ≤ ((y : ℝ) + 1) * √2 := by positivity
    have hsq' := mul_le_mul hle hle hnn (by positivity)
    nlinarith [hsq]

/-! ## A088827 as even squares and twice squares -/

/-- `σ(2j²)` is odd for `j ≠ 0`. -/
theorem odd_sigma_two_mul_sq {j : ℕ} (hj : j ≠ 0) : Odd (sigma 1 (2 * j ^ 2)) := by
  obtain ⟨v, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hj
  have hm0 : m ≠ 0 := by rintro rfl; exact absurd hm (by decide)
  have heq : 2 * (2 ^ v * m) ^ 2 = 2 ^ (2 * v + 1) * m ^ 2 := by ring
  have hcop : Nat.Coprime (2 ^ (2 * v + 1)) (m ^ 2) :=
    Nat.Coprime.pow _ _ (Nat.coprime_two_left.mpr hm)
  rw [heq, isMultiplicative_sigma.map_mul_of_coprime hcop, Nat.odd_mul,
    sigma_one_apply_prime_pow Nat.prime_two]
  exact ⟨odd_geom_sum_of_even even_two _, odd_sigma_sq m hm0⟩

/-- A088827 membership is: `k = 4j²` or `k = 2j²` for some `j > 0`. -/
theorem isA088827_iff (k : ℕ) :
    IsA088827 k ↔ ∃ j, 0 < j ∧ (k = 4 * j ^ 2 ∨ k = 2 * j ^ 2) := by
  unfold IsA088827
  rw [odd_abundance_iff]
  constructor
  · rintro ⟨hk, ⟨w, hw⟩, hs⟩
    obtain ⟨e, s, rfl⟩ := exists_two_pow_mul_sq_of_odd_sigma _ hs
    have hs0 : s ≠ 0 := by rintro rfl; simp at hk
    rcases Nat.even_or_odd e with ⟨f, rfl⟩ | ⟨f, rfl⟩
    · rcases f with _ | f
      · simp only [add_zero, pow_zero, one_mul] at hw ⊢
        rcases Nat.even_or_odd s with ⟨u, rfl⟩ | hso
        · exact ⟨u, by omega, Or.inl (by ring)⟩
        · exfalso
          obtain ⟨u, hu⟩ := hso.pow (n := 2)
          omega
      · refine ⟨2 ^ f * s, by positivity, Or.inl (by ring)⟩
    · exact ⟨2 ^ f * s, by positivity, Or.inr (by ring)⟩
  · rintro ⟨j, hj, rfl | rfl⟩
    · refine ⟨by positivity, ⟨2 * j ^ 2, by ring⟩, ?_⟩
      rw [show 4 * j ^ 2 = (2 * j) ^ 2 by ring]
      exact odd_sigma_sq _ (by omega)
    · exact ⟨by positivity, ⟨j ^ 2, by ring⟩, odd_sigma_two_mul_sq (by omega)⟩

/-- `4i² ≠ 2j²` for `i > 0` (irrationality of `√2`, via the 2-adic valuation). -/
theorem four_mul_sq_ne_two_mul_sq {i j : ℕ} (hi : 0 < i) : 4 * i ^ 2 ≠ 2 * j ^ 2 := by
  intro h
  have hj : j ≠ 0 := by
    rintro rfl
    have hpos : 0 < 4 * i ^ 2 := by positivity
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h
    omega
  have h2 : (2 * i) ^ 2 = 2 * j ^ 2 := by rw [← h]; ring
  have hv := congrArg (padicValNat 2) h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat.pow, padicValNat.mul (by norm_num) (by omega),
    padicValNat.mul (by norm_num) (by positivity), padicValNat.pow, padicValNat_self] at hv
  all_goals omega

/-! ## Counting function -/

/-- The number of A088827 terms `≤ X` is `⌊√(X/4)⌋ + ⌊√(X/2)⌋`. -/
theorem count_isA088827 (X : ℕ) :
    Nat.count IsA088827 (X + 1) = Nat.sqrt (X / 4) + Nat.sqrt (X / 2) := by
  rw [Nat.count_eq_card_filter_range]
  have hset : ({x ∈ range (X + 1) | IsA088827 x} : Finset ℕ) =
      (Icc 1 (Nat.sqrt (X / 4))).image (fun j => 4 * j ^ 2) ∪
        (Icc 1 (Nat.sqrt (X / 2))).image (fun j => 2 * j ^ 2) := by
    ext k
    simp only [mem_filter, mem_range, mem_union, mem_image, mem_Icc, isA088827_iff,
      Nat.le_sqrt', Nat.le_div_iff_mul_le (show 0 < 4 by norm_num),
      Nat.le_div_iff_mul_le (show 0 < 2 by norm_num)]
    constructor
    · rintro ⟨hk, j, hj, rfl | rfl⟩
      · exact Or.inl ⟨j, ⟨hj, by linarith⟩, rfl⟩
      · exact Or.inr ⟨j, ⟨hj, by linarith⟩, rfl⟩
    · rintro (⟨j, ⟨hj1, hj2⟩, rfl⟩ | ⟨j, ⟨hj1, hj2⟩, rfl⟩)
      · exact ⟨by linarith, j, hj1, Or.inl rfl⟩
      · exact ⟨by linarith, j, hj1, Or.inr rfl⟩
  have hdisj : Disjoint ((Icc 1 (Nat.sqrt (X / 4))).image (fun j => 4 * j ^ 2))
      ((Icc 1 (Nat.sqrt (X / 2))).image (fun j => 2 * j ^ 2)) := by
    rw [Finset.disjoint_left]
    rintro _ hx hy
    simp only [mem_image, mem_Icc] at hx hy
    obtain ⟨i, ⟨hi, _⟩, rfl⟩ := hx
    obtain ⟨j, _, hj⟩ := hy
    exact four_mul_sq_ne_two_mul_sq hi hj.symm
  have hinj4 : Set.InjOn (fun j : ℕ => 4 * j ^ 2) (Icc 1 (Nat.sqrt (X / 4)) : Set ℕ) := by
    intro a _ b _ hab
    simp only at hab
    exact Nat.pow_left_injective (n := 2) (by norm_num) (show a ^ 2 = b ^ 2 by omega)
  have hinj2 : Set.InjOn (fun j : ℕ => 2 * j ^ 2) (Icc 1 (Nat.sqrt (X / 2)) : Set ℕ) := by
    intro a _ b _ hab
    simp only at hab
    exact Nat.pow_left_injective (n := 2) (by norm_num) (show a ^ 2 = b ^ 2 by omega)
  rw [hset, card_union_of_disjoint hdisj, card_image_of_injOn hinj4,
    card_image_of_injOn hinj2, Nat.card_Icc, Nat.card_Icc]
  omega

/-- The rank of `b` among A088827 terms: the number of terms `≤ b`. -/
def rank (b : ℕ) : ℕ := Nat.count IsA088827 (b + 1)

/-- `rank (4A²) = A + ⌊A√2⌋`. -/
theorem rank_four_mul_sq (A : ℕ) : rank (4 * A ^ 2) = A + Nat.sqrt (2 * A ^ 2) := by
  rw [rank, count_isA088827, show 4 * A ^ 2 / 4 = A ^ 2 by omega,
    show 4 * A ^ 2 / 2 = 2 * A ^ 2 by omega, Nat.sqrt_eq']

/-- `rank (2B²) = ⌊B/√2⌋ + B`. -/
theorem rank_two_mul_sq (B : ℕ) : rank (2 * B ^ 2) = Nat.sqrt (B ^ 2 / 2) + B := by
  rw [rank, count_isA088827, show 2 * B ^ 2 / 4 = B ^ 2 / 2 by omega,
    show 2 * B ^ 2 / 2 = B ^ 2 by omega, Nat.sqrt_eq']

/-- **Doubling acts on ranks as the Beatty map.** For a term `b` of A088827,
`s(rank b) = rank (2b)`. -/
theorem sNat_rank {b : ℕ} (hb : IsA088827 b) : sNat (rank b) = rank (2 * b) := by
  obtain ⟨j, hj, rfl | rfl⟩ := (isA088827_iff b).mp hb
  · -- `b = 4A²`, `2b = 2(2A)²`
    rw [rank_four_mul_sq, show 2 * (4 * j ^ 2) = 2 * (2 * j) ^ 2 by ring, rank_two_mul_sq,
      show (2 * j) ^ 2 / 2 = 2 * j ^ 2 by rw [mul_pow]; omega]
    have hf1 := Nat.sqrt_le' (2 * j ^ 2)
    have hf2 := Nat.lt_succ_sqrt' (2 * j ^ 2)
    generalize Nat.sqrt (2 * j ^ 2) = f at hf1 hf2
    rw [Nat.succ_eq_add_one] at hf2
    apply sNat_eq_of <;> nlinarith
  · -- `b = 2B²`, `2b = 4B²`
    rw [rank_two_mul_sq, show 2 * (2 * j ^ 2) = 4 * j ^ 2 by ring, rank_four_mul_sq]
    have hg1 := Nat.sqrt_le' (j ^ 2 / 2)
    have hg2 := Nat.lt_succ_sqrt' (j ^ 2 / 2)
    have hh1 := Nat.sqrt_le' (2 * j ^ 2)
    have hh2 := Nat.lt_succ_sqrt' (2 * j ^ 2)
    have hd := Nat.div_add_mod (j ^ 2) 2
    have hm := Nat.mod_lt (j ^ 2) (show 0 < 2 by norm_num)
    generalize j ^ 2 % 2 = r at hd hm
    generalize j ^ 2 / 2 = q at hg1 hg2 hd
    generalize Nat.sqrt q = g at hg1 hg2
    generalize Nat.sqrt (2 * j ^ 2) = h at hh1 hh2
    rw [Nat.succ_eq_add_one] at hg2 hh2
    -- `h ∈ {2g, 2g + 1}`
    have hlo : 2 * g ≤ h := by
      by_contra hlt
      rw [not_le] at hlt
      have : (h + 1) ^ 2 ≤ (2 * g) ^ 2 := Nat.pow_le_pow_left hlt 2
      nlinarith
    have hhi : h ≤ 2 * g + 1 := by
      by_contra hlt
      rw [not_le] at hlt
      have : (2 * g + 2) ^ 2 ≤ h ^ 2 := Nat.pow_le_pow_left hlt 2
      nlinarith
    rcases (show h = 2 * g ∨ h = 2 * g + 1 by omega) with rfl | rfl
    · apply sNat_eq_of <;> nlinarith
    · apply sNat_eq_of <;> nlinarith

/-! ## Ranks as a bijection from A088827 onto the positive integers -/

/-- A088827 has infinitely many terms. -/
theorem infinite_isA088827 : (Set.ofPred IsA088827).Infinite := by
  refine Set.infinite_of_forall_exists_gt fun x => ⟨2 * (x + 1) ^ 2, ?_, by nlinarith⟩
  exact (isA088827_iff _).mpr ⟨x + 1, by omega, Or.inr rfl⟩

/-- For a term `b`, `rank b = count b + 1`. -/
theorem rank_eq_count_add_one {b : ℕ} (hb : IsA088827 b) :
    rank b = Nat.count IsA088827 b + 1 :=
  Nat.count_succ_eq_succ_count_iff.mpr hb

/-- Every positive integer is the rank of some term. -/
theorem exists_rank_eq {k : ℕ} (hk : 0 < k) : ∃ b, IsA088827 b ∧ rank b = k := by
  refine ⟨Nat.nth IsA088827 (k - 1), Nat.nth_mem_of_infinite infinite_isA088827 _, ?_⟩
  rw [rank_eq_count_add_one (Nat.nth_mem_of_infinite infinite_isA088827 _),
    Nat.count_nth_of_infinite infinite_isA088827]
  omega

/-- Ranks are injective on terms. -/
theorem eq_of_rank_eq {b b' : ℕ} (hb : IsA088827 b) (hb' : IsA088827 b')
    (h : rank b = rank b') : b = b' := by
  rw [rank_eq_count_add_one hb, rank_eq_count_add_one hb'] at h
  rw [← Nat.nth_count hb, ← Nat.nth_count hb', Nat.add_right_cancel h]

/-- Ranks are strictly increasing on terms. -/
theorem rank_lt_rank {b b' : ℕ} (hb' : IsA088827 b') (h : b < b') : rank b < rank b' := by
  have h1 : rank b ≤ Nat.count IsA088827 b' := Nat.count_monotone _ h
  rw [rank_eq_count_add_one hb']
  omega

/-- Doubling preserves A088827. -/
theorem isA088827_two_mul {b : ℕ} (hb : IsA088827 b) : IsA088827 (2 * b) := by
  obtain ⟨j, hj, rfl | rfl⟩ := (isA088827_iff b).mp hb
  · exact (isA088827_iff _).mpr ⟨2 * j, by omega, Or.inr (by ring)⟩
  · exact (isA088827_iff _).mpr ⟨j, hj, Or.inl (by ring)⟩

/-- No term of A088827 is odd. -/
theorem even_of_isA088827 {b : ℕ} (hb : IsA088827 b) : Even b := hb.2.1

/-! ### Row starts of the dispersion -/

/-- The candidate row starts `u r = rank (2(2r+1)²)`. -/
def u (r : ℕ) : ℕ := rank (2 * (2 * r + 1) ^ 2)

/-- `2(2r+1)²` is a term of A088827. -/
theorem isA088827_u_arg (r : ℕ) : IsA088827 (2 * (2 * r + 1) ^ 2) :=
  (isA088827_iff _).mpr ⟨2 * r + 1, by omega, Or.inr rfl⟩

/-- `u` is strictly increasing. -/
theorem u_strictMono : StrictMono u := by
  intro r r' h
  apply rank_lt_rank (isA088827_u_arg r')
  have : 2 * r + 1 < 2 * r' + 1 := by omega
  have := Nat.pow_lt_pow_left this (show 2 ≠ 0 by norm_num)
  omega

/-- The row starts are exactly the values of `u`. -/
theorem isRowStart_iff (k : ℕ) : IsRowStart k ↔ ∃ r, u r = k := by
  have hs : ∀ m, s m = sNat m := s_eq_sNat
  constructor
  · rintro ⟨hk, hns⟩
    obtain ⟨b, hb, rfl⟩ := exists_rank_eq hk
    obtain ⟨j, hj, rfl | rfl⟩ := (isA088827_iff b).mp hb
    · -- `4j² = 2·(2j²)` is hit by `s`
      exfalso
      have hb' : IsA088827 (2 * j ^ 2) := (isA088827_iff _).mpr ⟨j, hj, Or.inr rfl⟩
      apply hns (rank (2 * j ^ 2))
      rw [hs, sNat_rank hb', show 2 * (2 * j ^ 2) = 4 * j ^ 2 by ring]
    · rcases Nat.even_or_odd j with ⟨i, rfl⟩ | ⟨r, rfl⟩
      · -- `2(2i)² = 2·(4i²)` is hit by `s`
        exfalso
        have hb' : IsA088827 (4 * i ^ 2) := (isA088827_iff _).mpr ⟨i, by omega, Or.inl rfl⟩
        apply hns (rank (4 * i ^ 2))
        rw [hs, sNat_rank hb', show 2 * (4 * i ^ 2) = 2 * (i + i) ^ 2 by ring]
      · exact ⟨r, by rw [u, show 2 * r + 1 = r * 2 + 1 by ring] ⟩
  · rintro ⟨r, rfl⟩
    refine ⟨?_, fun m hm => ?_⟩
    · rw [u, rank_eq_count_add_one (isA088827_u_arg r)]
      omega
    · rcases Nat.eq_zero_or_pos m with rfl | hm0
      · rw [hs] at hm
        have h0 : sNat 0 = 0 := by decide
        rw [h0, u, rank_eq_count_add_one (isA088827_u_arg r)] at hm
        omega
      · obtain ⟨b, hb, rfl⟩ := exists_rank_eq hm0
        rw [hs, sNat_rank hb] at hm
        have heq := eq_of_rank_eq (isA088827_two_mul hb) (isA088827_u_arg r) hm
        have hbodd : b = (2 * r + 1) ^ 2 := by omega
        have hev := even_of_isA088827 hb
        rw [hbodd] at hev
        exact (Nat.not_even_iff_odd.mpr (Odd.pow ⟨r, rfl⟩)) hev

/-- The `r`-th row start is `rank (2(2r+1)²)`. -/
theorem rowStart_eq (r : ℕ) : rowStart r = u r := by
  have hinf : (Set.ofPred IsRowStart).Infinite := by
    have hr : Set.range u ⊆ Set.ofPred IsRowStart := by
      rintro _ ⟨r, rfl⟩
      exact (isRowStart_iff _).mpr ⟨r, rfl⟩
    exact Set.Infinite.mono hr (Set.infinite_range_of_injective u_strictMono.injective)
  have hall : ∀ n : ℕ, n ∈ {n : ℕ | ∀ hf : Set.Finite (Set.ofPred IsRowStart),
      n < hf.toFinset.card} := fun n hf => absurd hf hinf
  refine (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn u ?_ ?_ ?_ (hall r)).symm
  · intro k hk
    obtain ⟨r', hr'⟩ := (isRowStart_iff k).mp hk
    exact ⟨r', hall r', hr'⟩
  · intro r' _
    exact (isRowStart_iff _).mpr ⟨r', rfl⟩
  · exact u_strictMono.strictMonoOn _

/-! ### Columns: iterating `s` doubles the term -/

/-- `(2r+1)² · 2^(c+1)` is a term of A088827. -/
theorem isA088827_cell (r c : ℕ) : IsA088827 ((2 * r + 1) ^ 2 * 2 ^ (c + 1)) := by
  induction c with
  | zero => simpa [mul_comm] using isA088827_u_arg r
  | succ c ih =>
    rw [show (2 * r + 1) ^ 2 * 2 ^ (c + 1 + 1) = 2 * ((2 * r + 1) ^ 2 * 2 ^ (c + 1)) by ring]
    exact isA088827_two_mul ih

/-- The array entry `T r c` is the rank of `(2r+1)² · 2^(c+1)`. -/
theorem T_eq_rank (r c : ℕ) : T r c = rank ((2 * r + 1) ^ 2 * 2 ^ (c + 1)) := by
  induction c with
  | zero =>
    rw [T, Function.iterate_zero_apply, rowStart_eq, u]
    congr 1
    ring
  | succ c ih =>
    rw [T, Function.iterate_succ_apply', ← T, ih, s_eq_sNat, sNat_rank (isA088827_cell r c),
      pow_succ 2 (c + 1)]
    congr 1
    ring

/-- `a (rank b) = b` for every term `b`. -/
theorem a_rank {b : ℕ} (hb : IsA088827 b) : a (rank b) = b := by
  rw [a, rank_eq_count_add_one hb, Nat.add_sub_cancel, Nat.nth_count hb]

/-! ### The conjecture -/

/-- **Rascoe's conjecture (A088827 / A191432, John Tyler Rascoe, Jul 12 2022).**
If `n` sits at row `r`, column `c` (0-indexed) of the dispersion array A191432 of
`s(m) = ⌊m√2 + 1/√2⌋`, then the `n`-th even number with odd abundance is
`(2r+1)² · 2^(c+1)`. -/
theorem rascoe (n r c : ℕ) (h : T r c = n) : a n = (2 * r + 1) ^ 2 * 2 ^ (c + 1) := by
  rw [← h, T_eq_rank]
  exact a_rank (isA088827_cell r c)

/-- Every positive integer sits somewhere in the array, so `rascoe` determines
every term of A088827. -/
theorem exists_T_eq {n : ℕ} (hn : 0 < n) : ∃ r c, T r c = n := by
  obtain ⟨b, hb, rfl⟩ := exists_rank_eq hn
  obtain ⟨j, hj, rfl | rfl⟩ := (isA088827_iff b).mp hb
  · obtain ⟨v, m, ⟨r, rfl⟩, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (show j ≠ 0 by omega)
    refine ⟨r, 2 * v + 1, ?_⟩
    rw [T_eq_rank]
    congr 1
    ring
  · obtain ⟨v, m, ⟨r, rfl⟩, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (show j ≠ 0 by omega)
    refine ⟨r, 2 * v, ?_⟩
    rw [T_eq_rank]
    congr 1
    ring

/-! ## Examples for `s` and the array (checked through the proved formulas) -/

-- A001953 data line: `s 0, …, s 9 = 0, 2, 3, 4, 6, 7, 9, 10, 12, 13`.
example : s 0 = 0 ∧ s 1 = 2 ∧ s 2 = 3 ∧ s 3 = 4 ∧ s 4 = 6 ∧ s 5 = 7 ∧ s 6 = 9 ∧
    s 7 = 10 ∧ s 8 = 12 ∧ s 9 = 13 := by
  simp only [s_eq_sNat]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply sNat_eq_of <;> norm_num

-- A191432 data line (antidiagonals `1; 2, 5; 3, 7, 8; 4, 10, 12, 11`).
example : T 0 0 = 1 ∧ T 0 1 = 2 ∧ T 1 0 = 5 ∧ T 0 2 = 3 ∧ T 1 1 = 7 ∧ T 2 0 = 8 ∧
    T 0 3 = 4 ∧ T 1 2 = 10 ∧ T 2 1 = 12 ∧ T 3 0 = 11 := by
  simp only [T_eq_rank, rank]
  decide

-- The entry's example `A088827(67) = 7² · 2⁶ = 3136`: `67` sits at row `3`, column `5`.
example : T 3 5 = 67 ∧ a 67 = 3136 := by
  have hT : T 3 5 = 67 := by
    rw [T_eq_rank, rank, count_isA088827]
    norm_num [Nat.sqrt]
  exact ⟨hT, by rw [rascoe 67 3 5 hT]; norm_num⟩

end Candidates.A088827RascoeSitsRow
