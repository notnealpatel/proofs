import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

set_option autoImplicit false

namespace Erdos30

/-- An original additive Sidon set: equal sums determine the unordered pair,
including pairs with equal summands. -/
def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The matching definition is exactly uniqueness of the unordered two-element
multiset; its multiplicity remembers equal summands. -/
theorem isSidon_iff_pair_multiset (A : Finset ℕ) :
    IsSidon A ↔ ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      a + b = c + d → ([a, b] : Multiset ℕ) = ([c, d] : Multiset ℕ) := by
  simp only [IsSidon, Multiset.coe_eq_coe, List.perm_pair, List.cons.injEq,
    and_true]

example : IsSidon ({1, 2, 5, 10} : Finset ℕ) := by
  norm_num [IsSidon]

/-- The increasing enumeration of the actual set, extended by zero outside its domain. -/
noncomputable def entry (A : Finset ℕ) (i : ℕ) : ℕ :=
  if hi : i < A.card then A.orderEmbOfFin rfl ⟨i, hi⟩ else 0

/-- Within the enumeration domain, entries are the standard sorted order embedding. -/
theorem entry_eq (A : Finset ℕ) {i : ℕ} (hi : i < A.card) :
    entry A i = A.orderEmbOfFin rfl ⟨i, hi⟩ := by
  simp [entry, hi]

/-- Each valid entry belongs to the original set. -/
theorem entry_mem (A : Finset ℕ) {i : ℕ} (hi : i < A.card) : entry A i ∈ A := by
  rw [entry_eq A hi]
  exact A.orderEmbOfFin_mem rfl _

/-- The valid entries are strictly increasing. -/
theorem entry_lt (A : Finset ℕ) {i j : ℕ} (hi : i < j) (hj : j < A.card) :
    entry A i < entry A j := by
  rw [entry_eq A (hi.trans hj), entry_eq A hj]
  exact (A.orderEmbOfFin rfl).strictMono hi

example : entry ({1, 2, 5, 10} : Finset ℕ) 4 = 0 := by
  simp [entry]

/-- Order `r+1` and starting position `i`, both zero based. -/
def shortIndices (k h : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.range h).sigma fun r => Finset.range (k - (r + 1))

example : (shortIndices 4 2).card = 5 := by decide
example : shortIndices 4 0 = ∅ := by rfl

/-- Membership gives precisely the positive-order bounded index conditions. -/
theorem mem_shortIndices {k h : ℕ} {p : Σ _ : ℕ, ℕ} :
    p ∈ shortIndices k h ↔ p.1 < h ∧ p.2 < k - (p.1 + 1) := by
  simp [shortIndices]

/-- All short differences are positive and their endpoints are valid entries. -/
theorem short_index_bounds (A : Finset ℕ) {h : ℕ} (_hh : h < A.card)
    {p : Σ _ : ℕ, ℕ} (hp : p ∈ shortIndices A.card h) :
    p.2 < p.2 + (p.1 + 1) ∧ p.2 + (p.1 + 1) < A.card := by
  have hp' := mem_shortIndices.mp hp
  omega

/-- Original unordered-sum Sidon implies injectivity of the short positive differences. -/
theorem short_difference_injective (A : Finset ℕ) (hA : IsSidon A)
    {h : ℕ} (hh : h < A.card) :
    Set.InjOn (fun p : Σ _ : ℕ, ℕ => entry A (p.2 + (p.1 + 1)) - entry A p.2)
      (shortIndices A.card h) := by
  intro p hp q hq heq
  dsimp only at heq
  have bp := short_index_bounds A hh hp
  have bq := short_index_bounds A hh hq
  have lp := entry_lt A bp.1 bp.2
  have lq := entry_lt A bq.1 bq.2
  have hs : entry A p.2 + entry A (q.2 + (q.1 + 1)) =
      entry A q.2 + entry A (p.2 + (p.1 + 1)) := by omega
  rcases hA _ (entry_mem A (bp.1.trans bp.2)) _ (entry_mem A bq.2)
      _ (entry_mem A (bq.1.trans bq.2)) _ (entry_mem A bp.2) hs with hm | hm
  · have ei : p.2 = q.2 := by
      by_contra hn
      rcases lt_or_gt_of_ne hn with hl | hl
      · exact (ne_of_lt (entry_lt A hl (bq.1.trans bq.2))) hm.1
      · exact (ne_of_gt (entry_lt A hl (bp.1.trans bp.2))) hm.1
    have ej : q.2 + (q.1 + 1) = p.2 + (p.1 + 1) := by
      by_contra hn
      rcases lt_or_gt_of_ne hn with hl | hl
      · exact (ne_of_lt (entry_lt A hl bp.2)) hm.2
      · exact (ne_of_gt (entry_lt A hl bq.2)) hm.2
    have er : p.1 = q.1 := by omega
    cases p
    cases q
    simp_all
  · exact False.elim ((ne_of_lt lp) hm.1)

/-- Twice the sum of the first `n` positive integers, without natural division. -/
theorem twice_sum_succ (n : ℕ) :
    2 * (∑ i ∈ Finset.range n, (i + 1)) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    nlinarith

/-- The number of short indices is the sum of the valid starts at each order. -/
theorem short_card (k h : ℕ) :
    (shortIndices k h).card = ∑ r ∈ Finset.range h, (k - (r + 1)) := by
  simp [shortIndices, Finset.card_sigma]

/-- Subtraction-free short-difference count, for every `h ≤ k`. -/
theorem short_card_identity (k h : ℕ) (hh : h ≤ k) :
    2 * (shortIndices k h).card + h * (h + 1) = 2 * h * k := by
  rw [short_card]
  induction h with
  | zero => simp
  | succ h ih =>
    have ih' := ih (by omega)
    have hs : k - (h + 1) + (h + 1) = k := Nat.sub_add_cancel hh
    rw [Finset.sum_range_succ]
    nlinarith

/-- A strictly increasing enumeration of positive naturals dominates its positive index. -/
theorem entry_index_le (s : Finset ℕ) (hs : ∀ x ∈ s, 1 ≤ x)
    {i : ℕ} (hi : i < s.card) : i + 1 ≤ entry s i := by
  induction i with
  | zero => exact hs _ (entry_mem s hi)
  | succ i ih =>
    change i + 1 < s.card at hi
    have hp := ih (by omega)
    have hl : entry s i < entry s (i + 1) := entry_lt s (Nat.lt_succ_self i) hi
    omega

/-- Distinct positive natural numbers have sum at least half the square of their count. -/
theorem card_sq_le_twice_sum (s : Finset ℕ) (hs : ∀ x ∈ s, 1 ≤ x) :
    s.card ^ 2 ≤ 2 * ∑ x ∈ s, x := by
  classical
  have hsum : (∑ i : Fin s.card, s.orderEmbOfFin rfl i) = ∑ x ∈ s, x := by
    have himage := Finset.sum_image (f := fun x : ℕ => x)
      (s := Finset.univ) (g := s.orderEmbOfFin rfl)
      (fun _ _ _ _ heq => (s.orderEmbOfFin rfl).injective heq)
    simpa only [s.image_orderEmbOfFin_univ rfl] using himage.symm
  have hlo : (∑ i : Fin s.card, (i.val + 1)) ≤
      ∑ i : Fin s.card, s.orderEmbOfFin rfl i := by
    apply Finset.sum_le_sum
    intro i _
    simpa only [entry_eq s i.isLt] using entry_index_le s hs i.isLt
  have hrange : (∑ i : Fin s.card, (i.val + 1)) =
      ∑ i ∈ Finset.range s.card, (i + 1) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  rw [hsum, hrange] at hlo
  have ht := twice_sum_succ s.card
  nlinarith

/-- At a fixed positive order, telescoping cancels the interior entries; the
remaining last `r` entries have sum at most `r*N`. -/
theorem fixed_order_sum_le (A : Finset ℕ) (N r : ℕ)
    (hN : ∀ a ∈ A, a ≤ N) (hr : 1 ≤ r) (hrk : r ≤ A.card) :
    (∑ i ∈ Finset.range (A.card - r), (entry A (i + r) - entry A i)) ≤ r * N := by
  have hd : (∑ i ∈ Finset.range (A.card - r), (entry A (i + r) - entry A i)) +
      (∑ i ∈ Finset.range (A.card - r), entry A i) =
      ∑ i ∈ Finset.range (A.card - r), entry A (i + r) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hib := Finset.mem_range.mp hi
    have hl := entry_lt A (by omega : i < i + r) (by omega : i + r < A.card)
    exact Nat.sub_add_cancel hl.le
  have hk1 : r + (A.card - r) = A.card := by omega
  have hk2 : A.card - r + r = A.card := by omega
  have hw1 : (∑ i ∈ Finset.range A.card, entry A i) =
      (∑ i ∈ Finset.range r, entry A i) +
      ∑ i ∈ Finset.range (A.card - r), entry A (i + r) := by
    simpa only [hk1, Nat.add_comm] using Finset.sum_range_add (entry A) r (A.card - r)
  have hw2 : (∑ i ∈ Finset.range A.card, entry A i) =
      (∑ i ∈ Finset.range (A.card - r), entry A i) +
      ∑ i ∈ Finset.range r, entry A (A.card - r + i) := by
    simpa only [hk2] using Finset.sum_range_add (entry A) (A.card - r) r
  have ht : (∑ i ∈ Finset.range r, entry A (A.card - r + i)) ≤ r * N := by
    calc
      _ ≤ ∑ _i ∈ Finset.range r, N := by
        apply Finset.sum_le_sum
        intro i hi
        have hib := Finset.mem_range.mp hi
        exact hN _ (entry_mem A (by omega))
      _ = r * N := by simp
  omega

/-- Summing the telescoping bound over precisely orders `1,...,h`. -/
theorem short_sum_upper (A : Finset ℕ) (N h : ℕ)
    (hN : ∀ a ∈ A, a ≤ N) (hh : h < A.card) :
    2 * (∑ p ∈ shortIndices A.card h,
      (entry A (p.2 + (p.1 + 1)) - entry A p.2)) ≤ N * h * (h + 1) := by
  rw [shortIndices, Finset.sum_sigma]
  have hu : (∑ r ∈ Finset.range h,
      ∑ i ∈ Finset.range (A.card - (r + 1)),
        (entry A (i + (r + 1)) - entry A i)) ≤
      (∑ r ∈ Finset.range h, (r + 1) * N) := by
    apply Finset.sum_le_sum
    intro r hr
    have hrb := Finset.mem_range.mp hr
    exact fixed_order_sum_le A N (r + 1) hN (by omega) (by omega)
  rw [← Finset.sum_mul] at hu
  have ht := twice_sum_succ h
  nlinarith

/-- The finite Lindström bottleneck, for every positive `h < |A|`, from
original Sidon sums rather than a supplied difference certificate. -/
theorem finite_short_difference_bound (A : Finset ℕ) (N h : ℕ)
    (hA : IsSidon A) (hN : ∀ a ∈ A, 1 ≤ a ∧ a ≤ N)
    (_hhpos : 1 ≤ h) (hh : h < A.card) :
    (shortIndices A.card h).card ^ 2 ≤ N * h * (h + 1) ∧
      2 * (shortIndices A.card h).card + h * (h + 1) = 2 * h * A.card := by
  classical
  let f : (Σ _ : ℕ, ℕ) → ℕ := fun p => entry A (p.2 + (p.1 + 1)) - entry A p.2
  let D := (shortIndices A.card h).image f
  have hinj : Set.InjOn f (shortIndices A.card h) := short_difference_injective A hA hh
  have hcard : D.card = (shortIndices A.card h).card := Finset.card_image_of_injOn hinj
  have hsum : (∑ d ∈ D, d) = ∑ p ∈ shortIndices A.card h, f p :=
    Finset.sum_image hinj
  have hpos : ∀ d ∈ D, 1 ≤ d := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    have bp := short_index_bounds A hh hp
    have hl := entry_lt A bp.1 bp.2
    dsimp only [f]
    omega
  have hlo := card_sq_le_twice_sum D hpos
  rw [hcard, hsum] at hlo
  have hup := short_sum_upper A N h (fun a ha => (hN a ha).2) hh
  exact ⟨hlo.trans hup, short_card_identity A.card h hh.le⟩

/-- Lindström's classical upper bound for every original finite Sidon subset
of `[1,N]`. The fourth root is represented by two square roots; the selected
short-difference order is the natural ceiling of that root. -/
theorem sidon_card_le_sqrt_add_sqrt_sqrt (A : Finset ℕ) (N : ℕ)
    (hA : IsSidon A) (hN : ∀ a ∈ A, 1 ≤ a ∧ a ≤ N) (hNpos : 1 ≤ N) :
    (A.card : ℝ) ≤ Real.sqrt (N : ℝ) + Real.sqrt (Real.sqrt (N : ℝ)) + 1 := by
  let s : ℝ := Real.sqrt (N : ℝ)
  let x : ℝ := Real.sqrt s
  let h : ℕ := Nat.ceil x
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hspos : 0 < s := Real.sqrt_pos.mpr hNr
  have hxpos : 0 < x := Real.sqrt_pos.mpr hspos
  have hs2 : s ^ 2 = (N : ℝ) := Real.sq_sqrt hNr.le
  have hx2 : x ^ 2 = s := Real.sq_sqrt hspos.le
  have hhpos : 1 ≤ h := Nat.one_le_ceil_iff.mpr hxpos
  have hhrpos : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hxle : x ≤ (h : ℝ) := Nat.le_ceil x
  have hhle : (h : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hxpos.le).le
  change (A.card : ℝ) ≤ s + x + 1
  by_cases hk : A.card ≤ h
  · have hkr : (A.card : ℝ) ≤ (h : ℝ) := by exact_mod_cast hk
    linarith
  · have hh : h < A.card := by omega
    obtain ⟨hb, hc⟩ := finite_short_difference_bound A N h hA hN hhpos hh
    let m : ℝ := ((shortIndices A.card h).card : ℝ)
    have hm0 : 0 ≤ m := by positivity
    have hmr : m ^ 2 ≤ (N : ℝ) * (h : ℝ) * ((h : ℝ) + 1) := by
      dsimp only [m]
      exact_mod_cast hb
    have hcr : 2 * m + (h : ℝ) * ((h : ℝ) + 1) =
        2 * (h : ℝ) * (A.card : ℝ) := by
      dsimp only [m]
      exact_mod_cast hc
    have hquad : (N : ℝ) * (h : ℝ) * ((h : ℝ) + 1) ≤
        (s * ((h : ℝ) + 1 / 2)) ^ 2 := by
      rw [mul_pow, hs2]
      nlinarith
    have hmle : m ≤ s * ((h : ℝ) + 1 / 2) :=
      (sq_le_sq₀ hm0 (by positivity)).mp (hmr.trans hquad)
    have htail : (h : ℝ) * ((h : ℝ) + 1) ≤ (h : ℝ) * (x + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hhrpos.le
    have hroot : s ≤ (h : ℝ) * x := by
      have hp := mul_le_mul_of_nonneg_right hxle hxpos.le
      nlinarith
    have hscaled : (2 * (h : ℝ)) * (A.card : ℝ) ≤
        (2 * (h : ℝ)) * (s + x + 1) := by
      nlinarith
    exact le_of_mul_le_mul_left hscaled (by positivity : 0 < 2 * (h : ℝ))

/-- The concrete original-input fixture simultaneously applies the public root
consumer and the all-orders finite theorem to the same set, with `M=5`. -/
theorem fixture_one_two_five_ten :
    (({1, 2, 5, 10} : Finset ℕ).card : ℝ) ≤
      Real.sqrt (10 : ℝ) + Real.sqrt (Real.sqrt (10 : ℝ)) + 1 ∧
    (shortIndices ({1, 2, 5, 10} : Finset ℕ).card 2).card = 5 ∧
    (shortIndices ({1, 2, 5, 10} : Finset ℕ).card 2).card ^ 2 ≤ 10 * 2 * (2 + 1) ∧
    2 * (shortIndices ({1, 2, 5, 10} : Finset ℕ).card 2).card + 2 * (2 + 1) =
      2 * 2 * ({1, 2, 5, 10} : Finset ℕ).card := by
  let A : Finset ℕ := {1, 2, 5, 10}
  have hA : IsSidon A := by norm_num [A, IsSidon]
  have hN : ∀ a ∈ A, 1 ≤ a ∧ a ≤ 10 := by
    intro a ha
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at ha
    omega
  have hroot := sidon_card_le_sqrt_add_sqrt_sqrt A 10 hA hN (by decide)
  have hfinite := finite_short_difference_bound A 10 2 hA hN (by decide) (by decide)
  exact ⟨hroot, by decide, hfinite⟩

end Erdos30
