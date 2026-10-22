/-
Refutation of Cloitre's ultimate-periodicity conjecture (OEIS A086844;
Benoit Cloitre, Aug 10 2003).

For each integral z≥1 let r=(z+√(z²+4z))/2 and enumerate the positive odd m
whose orbit b(1)=m, b(k+1)=floor(r b(k)) stays odd. The centered sequence
is not eventually periodic. The proof reduces orbit membership to the first
two odd terms and contradicts shift invariance by irrational approximation.
Here a z n is indexed from zero, hence corresponds to source term a(n+1).
For z=2, a 2 837=3363 also refutes the bound |a(n)-4n|≤9 at source index 838.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A086844Refutation

/-- The ratio `r(z) = (z + √(z² + 4z)) / 2` of Cloitre's comment. -/
noncomputable def r (z : ℕ) : ℝ := ((z : ℝ) + √((z : ℝ) ^ 2 + 4 * z)) / 2

/-- The orbit `b(1) = m, b(k+1) = ⌊r(z) b(k)⌋` (indexed from `0`). -/
noncomputable def orb (z m : ℕ) : ℕ → ℕ
  | 0 => m
  | k + 1 => ⌊r z * orb z m k⌋₊

/-- Odd `m` whose orbit under `b ↦ ⌊r(z) b⌋` contains only odd numbers. -/
def S (z : ℕ) : Set ℕ := {m | Odd m ∧ ∀ k, Odd (orb z m k)}

/-- `a z n` is the `n`-th element (from `0`) of `S z` in increasing order, so
`a z n` is the OEIS term `a(n+1)`; `a 2` is A086844 and `a 1` is A086843. -/
noncomputable def a (z n : ℕ) : ℕ := Nat.nth (· ∈ S z) n

/-- `r(z)² = z r(z) + z`. -/
theorem r_sq (z : ℕ) : r z ^ 2 = z * r z + z := by
  have hs : √((z : ℝ) ^ 2 + 4 * z) ^ 2 = (z : ℝ) ^ 2 + 4 * z :=
    Real.sq_sqrt (by positivity)
  unfold r
  linear_combination hs / 4

/-- `z < r(z) < z + 1` for `1 ≤ z`. -/
theorem r_bounds {z : ℕ} (hz : 1 ≤ z) : (z : ℝ) < r z ∧ r z < z + 1 := by
  have hz' : (1 : ℝ) ≤ z := by exact_mod_cast hz
  have hs0 : 0 ≤ √((z : ℝ) ^ 2 + 4 * z) := Real.sqrt_nonneg _
  have hs : √((z : ℝ) ^ 2 + 4 * z) ^ 2 = (z : ℝ) ^ 2 + 4 * z :=
    Real.sq_sqrt (by positivity)
  unfold r
  constructor
  · nlinarith
  · nlinarith

/-- `r(z)` is irrational for `1 ≤ z`, since `z² + 4z` lies strictly between
`(z+1)²` and `(z+2)²`. -/
theorem irrational_r {z : ℕ} (hz : 1 ≤ z) : Irrational (r z) := by
  have hsq : ¬ IsSquare (z ^ 2 + 4 * z) := by
    rintro ⟨s, hs⟩
    have h1 : z + 1 < s := by nlinarith
    have h2 : s < z + 2 := by nlinarith
    omega
  have hirr : Irrational √(((z ^ 2 + 4 * z : ℕ) : ℝ)) := irrational_sqrt_natCast_iff.mpr hsq
  have heq : r z = (((z : ℚ) / 2 : ℚ) : ℝ) + √(((z ^ 2 + 4 * z : ℕ) : ℝ)) / ((2 : ℚ) : ℝ) := by
    unfold r; push_cast; ring
  rw [heq]
  exact (hirr.div_ratCast (by norm_num : (2 : ℚ) ≠ 0)).ratCast_add _

/-- For `1 ≤ z` and `0 < b`, `r(z) b` is not an integer: `⌊r b⌋₊ < r b`. -/
theorem floor_lt_r_mul {z : ℕ} (hz : 1 ≤ z) {b : ℕ} (hb : 0 < b) :
    (⌊r z * b⌋₊ : ℝ) < r z * b := by
  have hirr : Irrational (r z * b) := (irrational_r hz).mul_natCast (by omega)
  have hr0 : 0 < r z := lt_of_le_of_lt (Nat.cast_nonneg z) (r_bounds hz).1
  have hle : (⌊r z * b⌋₊ : ℝ) ≤ r z * b :=
    Nat.floor_le (mul_nonneg hr0.le (Nat.cast_nonneg _))
  exact lt_of_le_of_ne hle (fun h => hirr.ne_nat _ h.symm)

/-- **Collapse lemma.** For `1 ≤ z` and `b ≥ 1`, writing `c = ⌊r b⌋`, one has
`⌊r c⌋ + 1 = z c + z b`.  This follows from `r² = z r + z` and `z < r < z + 1`. -/
theorem floor_r_floor {z : ℕ} (hz : 1 ≤ z) {b : ℕ} (hb : 0 < b) :
    ⌊r z * ⌊r z * b⌋₊⌋₊ + 1 = z * ⌊r z * b⌋₊ + z * b := by
  obtain ⟨hzr, hrz⟩ := r_bounds hz
  have hz' : (1 : ℝ) ≤ z := by exact_mod_cast hz
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  set c := ⌊r z * b⌋₊ with hc
  have hlt : (c : ℝ) < r z * b := floor_lt_r_mul hz hb
  have hgt : r z * b < c + 1 := Nat.lt_floor_add_one _
  have hsq := r_sq z
  have hkey : r z * c = z * c + z * b - (r z - z) * (r z * b - c) := by
    linear_combination (b : ℝ) * hsq
  have hzb : 1 ≤ z * b := Nat.mul_pos (by omega) hb
  have hfl : ⌊r z * c⌋₊ = z * c + z * b - 1 := by
    rw [Nat.floor_eq_iff (mul_nonneg (by linarith) (Nat.cast_nonneg _))]
    have hcast : ((z * c + z * b - 1 : ℕ) : ℝ) = z * c + z * b - 1 := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hcast]
    have h1 : 0 < (r z - z) * (r z * b - c) := mul_pos (by linarith) (by linarith)
    have h2 : (r z - z) * (r z * b - c) < 1 := by
      have h3 : (r z - z) * (r z * b - c) < 1 * 1 :=
        mul_lt_mul'' (by linarith) (by linarith) (by linarith) (by linarith)
      linarith
    constructor <;> linarith
  omega

/-- **Orbit-parity reduction.** For `1 ≤ z`, an odd `m` has an all-odd orbit iff
`⌊r(z) m⌋` is odd. -/
theorem S_eq {z : ℕ} (hz : 1 ≤ z) : S z = {m : ℕ | Odd m ∧ Odd ⌊r z * (m : ℝ)⌋₊} := by
  ext m
  constructor
  · rintro ⟨hm, hall⟩
    exact ⟨hm, hall 1⟩
  · rintro ⟨hm, hm1⟩
    refine ⟨hm, ?_⟩
    have hpair : ∀ k, Odd (orb z m k) ∧ Odd (orb z m (k + 1)) := by
      intro k
      induction k with
      | zero => exact ⟨hm, hm1⟩
      | succ k ih =>
        refine ⟨ih.2, ?_⟩
        obtain ⟨hk, hk1⟩ := ih
        have hpos : 0 < orb z m k := hk.pos
        have hcol := floor_r_floor hz hpos
        have hrec : orb z m (k + 1 + 1) = ⌊r z * ⌊r z * orb z m k⌋₊⌋₊ := rfl
        have hrec1 : orb z m (k + 1) = ⌊r z * orb z m k⌋₊ := rfl
        rw [hrec]
        rw [← hrec1] at hcol ⊢
        have heven : Even (z * orb z m (k + 1) + z * orb z m k) := by
          rw [← mul_add]
          exact (hk1.add_odd hk).mul_left z
        rw [← hcol] at heven
        exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp heven)
    exact fun k => (hpair k).1

/-- **Hitting lemma.** A nonzero step `δ` with `|δ| ≤ b - a` cannot jump over the
window `[a, b) ⊆ [0, 1)` modulo `1`: some `fract (y + i δ)` lands in it. -/
theorem exists_fract_mem_Ico (y δ a b : ℝ) (hδ : δ ≠ 0) (ha : 0 ≤ a) (hb : b ≤ 1)
    (hab : |δ| ≤ b - a) : ∃ i : ℕ, a ≤ Int.fract (y + i * δ) ∧ Int.fract (y + i * δ) < b := by
  have hfl : ((⌊y⌋ : ℤ) : ℝ) ≤ y := Int.floor_le y
  have hfl' : y < ((⌊y⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one y
  -- If `y + i δ ∈ [a + k, b + k)` for an integer `k`, we are done
  have hdone : ∀ (i : ℕ) (k : ℤ), a + k ≤ y + i * δ → y + i * δ < b + k →
      a ≤ Int.fract (y + i * δ) ∧ Int.fract (y + i * δ) < b := by
    intro i k h1 h2
    have hfr : Int.fract (y + i * δ) = y + i * δ - k :=
      Int.fract_eq_iff.mpr ⟨by linarith, by linarith, k, by ring⟩
    rw [hfr]
    constructor <;> linarith
  rcases lt_or_gt_of_ne hδ with hneg | hpos
  · -- Negative step: walk down from above into `[a + k, b + k)` with `k = ⌊y⌋ - 1`
    have habs : |δ| = -δ := abs_of_neg hneg
    set k : ℤ := ⌊y⌋ - 1 with hk
    have hkc : ((k : ℤ) : ℝ) = (⌊y⌋ : ℝ) - 1 := by rw [hk]; push_cast; ring
    set u : ℝ := (y - b - k) / (-δ) with hu
    have hu0 : 0 ≤ u := div_nonneg (by linarith) (by linarith)
    have huδ : u * (-δ) = y - b - k := div_mul_cancel₀ _ (by linarith)
    refine ⟨⌊u⌋₊ + 1, hdone _ k ?_ ?_⟩
    · have h1 : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le hu0
      push_cast
      nlinarith
    · have h1 : u < (⌊u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one u
      push_cast
      nlinarith
  · -- Positive step: walk up from below into `[a + k, b + k)` with `k = ⌊y⌋ + 1`
    have habs : |δ| = δ := abs_of_pos hpos
    set k : ℤ := ⌊y⌋ + 1 with hk
    have hkc : ((k : ℤ) : ℝ) = (⌊y⌋ : ℝ) + 1 := by rw [hk]; push_cast; ring
    set u : ℝ := (a + k - y) / δ with hu
    have hu0 : 0 ≤ u := div_nonneg (by linarith) hpos.le
    have huδ : u * δ = a + k - y := div_mul_cancel₀ _ hδ
    refine ⟨⌈u⌉₊, hdone _ k ?_ ?_⟩
    · have h1 : u ≤ (⌈u⌉₊ : ℝ) := Nat.le_ceil u
      nlinarith
    · have h1 : (⌈u⌉₊ : ℝ) < u + 1 := Nat.ceil_lt_add_one hu0
      nlinarith

/-- `⌊x + y⌋ = ⌊x⌋ + ⌊y⌋` when the fractional parts sum below `1`. -/
theorem floor_add_of_fract_add_lt (x y : ℝ) (h : Int.fract x + Int.fract y < 1) :
    ⌊x + y⌋ = ⌊x⌋ + ⌊y⌋ := by
  have hx := Int.floor_add_fract x
  have hy := Int.floor_add_fract y
  have hx0 := Int.fract_nonneg x
  have hy0 := Int.fract_nonneg y
  rw [Int.floor_eq_iff]
  push_cast
  constructor <;> linarith

/-- `⌊x + y⌋ = ⌊x⌋ + ⌊y⌋ + 1` when the fractional parts sum to at least `1`. -/
theorem floor_add_of_one_le_fract_add (x y : ℝ) (h : 1 ≤ Int.fract x + Int.fract y) :
    ⌊x + y⌋ = ⌊x⌋ + ⌊y⌋ + 1 := by
  have hx := Int.floor_add_fract x
  have hy := Int.floor_add_fract y
  have hx1 := Int.fract_lt_one x
  have hy1 := Int.fract_lt_one y
  rw [Int.floor_eq_iff]
  push_cast
  constructor <;> linarith

/-- `fract (r(z) b) > 0` for `1 ≤ z` and `0 < b`. -/
theorem fract_r_mul_pos {z : ℕ} (hz : 1 ≤ z) {b : ℕ} (hb : 0 < b) :
    0 < Int.fract (r z * b) := by
  have hirr : Irrational (r z * b) := (irrational_r hz).mul_natCast (by omega)
  rcases (Int.fract_nonneg (r z * b)).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have hsum := Int.floor_add_fract (r z * b)
    rw [← heq, add_zero] at hsum
    exact hirr.ne_int _ hsum.symm

/-- Parity bookkeeping: if `A` and `A + C + e` have the same parity then
`C + e` is even. -/
theorem emod_two_of_iff (A C e : ℤ) (h : A % 2 = 1 ↔ (A + C + e) % 2 = 1) :
    (C + e) % 2 = 0 := by
  rcases Int.emod_two_eq_zero_or_one A with hA | hA
  · have hne : ¬ (A + C + e) % 2 = 1 := fun h' => by
      have hA' := h.mpr h'
      omega
    omega
  · have h' := h.mp hA
    omega

/-- Membership in `S z` for odd `m`, in terms of the integer floor. -/
theorem mem_S_iff {z : ℕ} (hz : 1 ≤ z) {m : ℕ} (hm : Odd m) :
    m ∈ S z ↔ ⌊r z * m⌋ % 2 = 1 := by
  have hr0 : 0 < r z := lt_of_le_of_lt (Nat.cast_nonneg z) (r_bounds hz).1
  rw [S_eq hz, Set.mem_ofPred_eq, ← Int.natCast_floor_eq_floor
    (mul_nonneg hr0.le (Nat.cast_nonneg _)), ← Int.odd_iff, Int.odd_coe_nat]
  exact and_iff_right hm

/-- **Key step.** For `1 ≤ z` and `0 < p`, the set `S z` is not eventually invariant
under the shift `m ↦ m + 4p`.  Invariance would force the indicator
`[fract (r m) ≥ 1 - fract (4 p r)]` to be constant on large odd `m`, but the
fractional parts `fract (r m)` over odd `m` are dense (Dirichlet approximation of
`2 r` plus the hitting lemma). -/
theorem not_shift_invariant {z : ℕ} (hz : 1 ≤ z) {p : ℕ} (hp : 0 < p) (M : ℕ) :
    ¬ ∀ m, M ≤ m → (m ∈ S z ↔ m + 4 * p ∈ S z) := by
  intro H
  have h4p : 0 < 4 * p := by omega
  set y : ℝ := r z * ((4 * p : ℕ) : ℝ) with hy
  set g : ℝ := Int.fract y with hg
  have hg0 : 0 < g := fract_r_mul_pos hz h4p
  have hg1 : g < 1 := Int.fract_lt_one y
  set t : ℝ := 1 - g with ht
  -- The indicator `[t ≤ fract (r m)]` is pinned by the parity of `⌊y⌋`
  have hpin : ∀ m : ℕ, Odd m → M ≤ m → (t ≤ Int.fract (r z * m) ↔ ⌊y⌋ % 2 = 1) := by
    intro m hm hMm
    have hm' : Odd (m + 4 * p) := hm.add_even (by
      rw [show 4 * p = 2 * (2 * p) by ring]
      exact even_two_mul _)
    have hiff := H m hMm
    rw [mem_S_iff hz hm, mem_S_iff hz hm'] at hiff
    have hsplit : r z * ((m + 4 * p : ℕ) : ℝ) = r z * m + y := by
      rw [hy]; push_cast; ring
    rw [hsplit] at hiff
    constructor
    · intro hle
      rw [floor_add_of_one_le_fract_add _ _ (by linarith)] at hiff
      have he := emod_two_of_iff _ _ _ hiff
      omega
    · intro hodd
      by_contra hlt
      rw [floor_add_of_fract_add_lt _ _ (by linarith)] at hiff
      have he := emod_two_of_iff ⌊r z * m⌋ ⌊y⌋ 0 (by simpa using hiff)
      omega
  -- Dirichlet: a small nonzero step `δ = k (2 r) - j`
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min (show (0 : ℝ) < t by linarith) hg0)
  obtain ⟨j, k, hk0, -, hjk⟩ := Real.exists_int_int_abs_mul_sub_le (2 * r z) (Nat.succ_pos n)
  obtain ⟨k', rfl⟩ := Int.eq_ofNat_of_zero_le hk0.le
  have hk' : 0 < k' := by exact_mod_cast hk0
  set δ : ℝ := ((k' : ℤ) : ℝ) * (2 * r z) - j with hδ
  have hδ0 : δ ≠ 0 := by
    intro h0
    have hirr : Irrational (r z * ((2 * k' : ℕ) : ℝ)) :=
      (irrational_r hz).mul_natCast (by omega)
    apply hirr.ne_int j
    push_cast
    linear_combination h0
  have hδsmall : |δ| < min t g := by
    refine lt_of_le_of_lt hjk (lt_of_le_of_lt ?_ hn)
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    linarith
  -- The odd numbers `m₀ + 2 k' i` all lie past `M`
  set m₀ : ℕ := 2 * M + 1 with hm₀
  have hfr : ∀ i : ℕ, Int.fract (r z * ((m₀ + 2 * k' * i : ℕ) : ℝ)) =
      Int.fract (r z * m₀ + i * δ) := by
    intro i
    have hsum : r z * ((m₀ + 2 * k' * i : ℕ) : ℝ) = (r z * m₀ + i * δ) + ((i * j : ℤ) : ℝ) := by
      rw [hδ]; push_cast; ring
    rw [hsum, Int.fract_add_intCast]
  have hodd : ∀ i : ℕ, Odd (m₀ + 2 * k' * i) := fun i => by
    rw [hm₀]
    exact ⟨M + k' * i, by ring⟩
  have hle : ∀ i : ℕ, M ≤ m₀ + 2 * k' * i := fun i => by omega
  obtain ⟨i₁, -, hi₁⟩ := exists_fract_mem_Ico (r z * m₀) δ 0 t hδ0 le_rfl (by linarith)
    (by have := min_le_left t g; linarith)
  obtain ⟨i₂, hi₂, -⟩ := exists_fract_mem_Ico (r z * m₀) δ t 1 hδ0 (by linarith) le_rfl
    (by have := min_le_right t g; linarith)
  have h₁ := hpin _ (hodd i₁) (hle i₁)
  have h₂ := hpin _ (hodd i₂) (hle i₂)
  rw [hfr] at h₁ h₂
  exact absurd (h₁.mpr (h₂.mp hi₂)) (not_le.mpr hi₁)

/-- For `1 ≤ z`, the set `S z` is infinite, so `a z` is a genuine
increasing enumeration and not eventually `0`. -/
theorem S_infinite {z : ℕ} (hz : 1 ≤ z) : (S z).Infinite := by
  intro hfin
  obtain ⟨B, hB⟩ := hfin.bddAbove
  apply not_shift_invariant hz one_pos (B + 1)
  intro m hm
  have h1 : m ∉ S z := fun hmS => by
    have := hB hmS
    omega
  have h2 : m + 4 * 1 ∉ S z := fun hmS => by
    have := hB hmS
    omega
  exact iff_of_false h1 h2

/-- For `1 ≤ z`, `a z` is strictly increasing and enumerates `S z`. -/
theorem a_strictMono {z : ℕ} (hz : 1 ≤ z) : StrictMono (a z) :=
  Nat.nth_strictMono (S_infinite hz)

/-- **Refutation of Cloitre's conjecture at a fixed `z ≥ 1`.** The sequence
`a(n) - 4n` (OEIS indexing, `a(n) = a z (n - 1)`) is not ultimately periodic. -/
theorem not_eventually_periodic {z : ℕ} (hz : 1 ≤ z) :
    ¬ ∃ N p : ℕ, 0 < p ∧ ∀ n, N ≤ n →
      (a z (n + p) : ℤ) - 4 * ((n + p + 1 : ℕ) : ℤ) = (a z n : ℤ) - 4 * ((n + 1 : ℕ) : ℤ) := by
  rintro ⟨N, p, hp, h⟩
  have hshift : ∀ n, N ≤ n → a z (n + p) = a z n + 4 * p := by
    intro n hn
    have hn' := h n hn
    push_cast at hn'
    omega
  have hinf : (S z).Infinite := by
    intro hfin
    have hc := Nat.nth_of_card_le (p := (· ∈ S z)) hfin (n := N + hfin.toFinset.card) (by omega)
    have hc' := Nat.nth_of_card_le (p := (· ∈ S z)) hfin (n := N + hfin.toFinset.card + p)
      (by omega)
    have hs := hshift (N + hfin.toFinset.card) (by omega)
    unfold a at hs
    omega
  have hmono : StrictMono (a z) := Nat.nth_strictMono hinf
  have hmem : ∀ n, a z n ∈ S z := Nat.nth_mem_of_infinite hinf
  have hrange : ∀ m ∈ S z, ∃ n, a z n = m := by
    intro m hm
    have hr : Set.range (Nat.nth (· ∈ S z)) = Set.ofPred (· ∈ S z) :=
      Nat.range_nth_of_infinite hinf
    have hm' : m ∈ Set.range (Nat.nth (· ∈ S z)) := by
      rw [hr]
      exact hm
    exact hm'
  apply not_shift_invariant hz hp (a z N)
  intro m hm
  constructor
  · intro hmS
    obtain ⟨n, rfl⟩ := hrange m hmS
    have hNn : N ≤ n := hmono.le_iff_le.mp hm
    rw [← hshift n hNn]
    exact hmem _
  · intro hmS
    obtain ⟨k, hk⟩ := hrange _ hmS
    have hNk : N + p ≤ k := by
      apply hmono.le_iff_le.mp
      rw [hshift N le_rfl, hk]
      omega
    have hk' := hshift (k - p) (by omega)
    rw [Nat.sub_add_cancel (by omega), hk] at hk'
    have hm' : m = a z (k - p) := by omega
    rw [hm']
    exact hmem _

/-- Cloitre's centered sequence is not eventually periodic for any `z≥1`
(Benoit Cloitre, Aug 10 2003), in particular at `z=2` for A086844. -/
theorem cloitre_conjecture_false :
    ¬ ∀ z : ℕ, 1 ≤ z → ∃ N p : ℕ, 0 < p ∧ ∀ n, N ≤ n →
      (a z (n + p) : ℤ) - 4 * ((n + p + 1 : ℕ) : ℤ) = (a z n : ℤ) - 4 * ((n + 1 : ℕ) : ℤ) :=
  fun h => not_eventually_periodic (by norm_num : 1 ≤ 2) (h 2 (by norm_num))

/-! ## The case `z = 2` (A086844 itself): computable form and examples -/

/-- For `z = 2`, `r = 1 + √3` and `⌊r m⌋ = m + ⌊√(3 m²)⌋`. -/
theorem floor_r_two_mul (m : ℕ) : ⌊r 2 * m⌋₊ = m + Nat.sqrt (3 * m ^ 2) := by
  have h3 : √(3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : 0 ≤ √(3 : ℝ) := Real.sqrt_nonneg _
  have hs : √(((3 * m ^ 2 : ℕ)) : ℝ) = √3 * m := by
    rw [show ((3 * m ^ 2 : ℕ) : ℝ) = (√3 * m) ^ 2 by push_cast; rw [mul_pow, h3]]
    exact Real.sqrt_sq (by positivity)
  have h12 : √(((2 : ℕ) : ℝ) ^ 2 + 4 * ((2 : ℕ) : ℝ)) = 2 * √3 := by
    rw [show ((2 : ℕ) : ℝ) ^ 2 + 4 * ((2 : ℕ) : ℝ) = (2 * √3) ^ 2 by
      rw [mul_pow, h3]; push_cast; norm_num]
    exact Real.sqrt_sq (by positivity)
  have hr : r 2 * m = √(((3 * m ^ 2 : ℕ)) : ℝ) + m := by
    rw [hs, r, h12]
    push_cast
    ring
  rw [hr, Nat.floor_add_natCast (Real.sqrt_nonneg _), Real.nat_floor_real_sqrt_eq_nat_sqrt,
    add_comm]

/-- The decidable membership test for A086844: odd `m` with `m + ⌊√(3m²)⌋` odd. -/
def IsA086844 (m : ℕ) : Prop := Odd m ∧ Odd (m + Nat.sqrt (3 * m ^ 2))

/-- Decidability of `IsA086844`. -/
instance : DecidablePred IsA086844 := fun m =>
  inferInstanceAs (Decidable (Odd m ∧ Odd (m + Nat.sqrt (3 * m ^ 2))))

/-- `S 2` is cut out by the decidable test `IsA086844`. -/
theorem mem_S_two_iff (m : ℕ) : m ∈ S 2 ↔ IsA086844 m := by
  rw [S_eq (by norm_num), Set.mem_ofPred_eq, floor_r_two_mul]
  rfl

/-- If `m` passes the test and exactly `n` smaller numbers do, then `a 2 n = m`. -/
theorem a_two_eq_of_count {m n : ℕ} (hm : IsA086844 m) (hc : Nat.count IsA086844 m = n) :
    a 2 n = m := by
  have hfun : (· ∈ S 2) = IsA086844 := funext fun k => propext (mem_S_two_iff k)
  unfold a
  rw [hfun, ← hc]
  exact Nat.nth_count hm

/-- `a 2` reproduces all 58 terms listed in A086844 (`a(1) = 5`, …,
`a(58) = 237`). -/
theorem a_two_listed : (List.range 58).map (a 2) =
    [5, 7, 13, 19, 21, 27, 29, 35, 37, 43, 49, 51, 57, 59, 65, 67, 71, 73, 79, 81, 87, 89, 95,
      97, 101, 103, 109, 111, 117, 119, 125, 131, 133, 139, 141, 147, 149, 155, 161, 163, 169,
      171, 177, 179, 183, 185, 191, 193, 199, 201, 207, 213, 215, 221, 223, 229, 231, 237] := by
  set L : List ℕ :=
    [5, 7, 13, 19, 21, 27, 29, 35, 37, 43, 49, 51, 57, 59, 65, 67, 71, 73, 79, 81, 87, 89, 95,
      97, 101, 103, 109, 111, 117, 119, 125, 131, 133, 139, 141, 147, 149, 155, 161, 163, 169,
      171, 177, 179, 183, 185, 191, 193, 199, 201, 207, 213, 215, 221, 223, 229, 231, 237]
    with hL
  have hcheck : ∀ i (hi : i < L.length), IsA086844 L[i] ∧ Nat.count IsA086844 L[i] = i := by
    rw [hL]
    decide +kernel
  apply List.ext_getElem (by simp [hL])
  intro i hi _
  rw [List.getElem_map, List.getElem_range]
  have hi' : i < L.length := by simpa [hL] using hi
  exact a_two_eq_of_count (hcheck i hi').1 (hcheck i hi').2

/-- `a(838) = 3363` in OEIS indexing, i.e. `a 2 837 = 3363`. -/
theorem a_two_837 : a 2 837 = 3363 :=
  a_two_eq_of_count (by decide +kernel) (by decide +kernel)

/-- **Cloitre's observation `|a(n) - 4n| ≤ 9` (A086844 formula line, Aug 10 2003) is
false**: at `n = 838` (OEIS indexing) `a(838) - 4·838 = 3363 - 3352 = 11`. -/
theorem cloitre_observation_false :
    ¬ ∀ n : ℕ, |(a 2 n : ℤ) - 4 * ((n + 1 : ℕ) : ℤ)| ≤ 9 := by
  intro h
  have h837 := h 837
  rw [a_two_837] at h837
  norm_num at h837

/-- **A086844 (`z = 2`) on its own**: `a(n) - 4n` is not ultimately periodic. -/
theorem a086844_not_eventually_periodic :
    ¬ ∃ N p : ℕ, 0 < p ∧ ∀ n, N ≤ n →
      (a 2 (n + p) : ℤ) - 4 * ((n + p + 1 : ℕ) : ℤ) = (a 2 n : ℤ) - 4 * ((n + 1 : ℕ) : ℤ) :=
  not_eventually_periodic (by norm_num)

end Candidates.A086844Refutation
