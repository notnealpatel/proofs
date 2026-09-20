/-
  Erdős Problem #142 — the signed short residue kernel.

  For a modulus `q` and a radius bound `R` with `1 ≤ R` and `2 * R ≤ q`, this
  module formalizes the set of residues of `ZMod q` that admit an integer
  representative in `[-(R-1), R-1]`: the *signed short residues*.  It records
  the membership characterization, zero membership, negation stability, the
  exact cardinality `2 * R - 1` (with the unconditional `≤` bound), the
  membership consequence for least-nonnegative-residue differences, and the
  coordinate box of short vectors `Fin (2 * k) → ZMod q` together with its
  cardinality bound `(2 * R - 1) ^ (2 * k)`.

  This is a self-contained arithmetic kernel: it makes no claim about the
  Erdős #142 density iteration itself.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

set_option autoImplicit false

namespace Erdos142

noncomputable def shortReps (R : ℕ) : Finset ℤ :=
  Finset.Icc (-((R : ℤ) - 1)) ((R : ℤ) - 1)

noncomputable def shortSignedSet (R q : ℕ) : Finset (ZMod q) :=
  (shortReps R).image fun m : ℤ => (m : ZMod q)

theorem mem_shortReps {R : ℕ} {m : ℤ} :
    m ∈ shortReps R ↔ -((R : ℤ) - 1) ≤ m ∧ m ≤ (R : ℤ) - 1 :=
  Finset.mem_Icc

theorem mem_shortSignedSet {R q : ℕ} {a : ZMod q} :
    a ∈ shortSignedSet R q ↔
      ∃ m : ℤ, -((R : ℤ) - 1) ≤ m ∧ m ≤ (R : ℤ) - 1 ∧ (m : ZMod q) = a := by
  rw [shortSignedSet, Finset.mem_image]
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [mem_shortReps] at hm
    exact ⟨m, hm.1, hm.2, rfl⟩
  · rintro ⟨m, h1, h2, h3⟩
    exact ⟨m, by rw [mem_shortReps]; exact ⟨h1, h2⟩, h3⟩

theorem zero_mem_shortSignedSet {R q : ℕ} (hR : 1 ≤ R) :
    (0 : ZMod q) ∈ shortSignedSet R q := by
  rw [mem_shortSignedSet]
  exact ⟨0, by omega, by omega, by simp⟩

theorem neg_mem_shortSignedSet {R q : ℕ} {a : ZMod q}
    (ha : a ∈ shortSignedSet R q) : -a ∈ shortSignedSet R q := by
  rw [mem_shortSignedSet] at ha ⊢
  obtain ⟨m, h1, h2, h3⟩ := ha
  refine ⟨-m, by omega, by omega, ?_⟩
  simp only [Int.cast_neg, h3]

theorem card_shortReps {R : ℕ} (hR : 1 ≤ R) : (shortReps R).card = 2 * R - 1 := by
  rw [shortReps, Int.card_Icc]
  have h : ((2 * R - 1 : ℕ) : ℤ) = ((R : ℤ) - 1 + 1 - (-((R : ℤ) - 1))) := by omega
  rw [← h, Int.toNat_natCast]

theorem shortReps_cast_injective {R q : ℕ} (hRq : 2 * R ≤ q) :
    Set.InjOn (fun m : ℤ => (m : ZMod q)) (shortReps R : Set ℤ) := by
  intro m hm n hn hmn
  rw [Finset.mem_coe, mem_shortReps] at hm hn
  have hmn' : (m : ZMod q) = (n : ZMod q) := hmn
  have hdvd : (q : ℤ) ∣ m - n := by
    have h0 : ((m - n : ℤ) : ZMod q) = 0 := by
      rw [Int.cast_sub, hmn', sub_self]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (m - n) q).mp h0
  have habs : |m - n| < (q : ℤ) := by
    have : |m - n| ≤ 2 * (R : ℤ) - 2 := by
      rw [abs_le]; constructor <;> omega
    omega
  have hzero : m - n = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
  omega

theorem card_shortSignedSet {R q : ℕ} (hR : 1 ≤ R) (hRq : 2 * R ≤ q) :
    (shortSignedSet R q).card = 2 * R - 1 := by
  rw [shortSignedSet, Finset.card_image_of_injOn (shortReps_cast_injective hRq),
    card_shortReps hR]

theorem card_shortSignedSet_le {R q : ℕ} (hR : 1 ≤ R) :
    (shortSignedSet R q).card ≤ 2 * R - 1 := by
  rw [shortSignedSet]
  exact (Finset.card_image_le).trans (le_of_eq (card_shortReps hR))

theorem shortSignedSet_val {R q : ℕ} (hR : 1 ≤ R) (hRq : 2 * R ≤ q)
    {a : ZMod q} (ha : a ∈ shortSignedSet R q) :
    a.val ≤ R - 1 ∨ q - (R - 1) ≤ a.val := by
  obtain ⟨m, hm1, hm2, hm3⟩ := (mem_shortSignedSet).mp ha
  haveI : NeZero q := ⟨by omega⟩
  have hval : (a.val : ℤ) = m % (q : ℤ) := by
    rw [← hm3, ZMod.val_intCast]
  rcases le_or_gt 0 m with hm | hm
  · left
    have hmq : m % (q : ℤ) = m := Int.emod_eq_of_lt hm (by omega)
    have : (a.val : ℤ) ≤ ((R - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub hR, hval, hmq]; exact hm2
    exact_mod_cast this
  · right
    have hmq : m % (q : ℤ) = m + q := by
      rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
    have hge : ((q - (R - 1) : ℕ) : ℤ) ≤ (a.val : ℤ) := by
      rw [Nat.cast_sub (by omega : R - 1 ≤ q), Nat.cast_sub hR, hval, hmq]
      omega
    exact_mod_cast hge

private lemma int_eq_neg_or_eq_or_eq_of_dvd_of_abs_lt_two {q : ℕ} (hq : 0 < q)
    {x : ℤ} (hdiv : (q : ℤ) ∣ x) (hx : |x| < 2 * (q : ℤ)) :
    x = -(q : ℤ) ∨ x = 0 ∨ x = (q : ℤ) := by
  obtain ⟨k, rfl⟩ := hdiv
  have hq' : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hk2 : |k| < 2 := by
    have h2 : (q : ℤ) * |k| < (q : ℤ) * 2 := by
      rw [abs_mul, abs_of_nonneg (le_of_lt hq'), mul_comm (2 : ℤ) (q : ℤ)] at hx
      exact hx
    exact lt_of_mul_lt_mul_left h2 (le_of_lt hq')
  rw [abs_lt] at hk2
  rcases lt_trichotomy k 0 with hk' | hk' | hk'
  · have : k = -1 := by omega
    left; rw [this]; ring
  · right; left; rw [hk']; ring
  · have : k = 1 := by omega
    right; right; rw [this]; ring

theorem shortSignedSet_sub_val {R q : ℕ} (hR : 1 ≤ R) (hRq : 2 * R ≤ q)
    {X Z : ZMod q} (h : Z - X ∈ shortSignedSet R q) :
    |(Z.val : ℤ) - X.val| ≤ (R : ℤ) - 1 ∨
      (q : ℤ) - ((R : ℤ) - 1) ≤ |(Z.val : ℤ) - X.val| := by
  obtain ⟨m, hm1, hm2, hm3⟩ := (mem_shortSignedSet).mp h
  have hq : 0 < q := by have := hR; omega
  haveI : NeZero q := ⟨by omega⟩
  set d : ℤ := (Z.val : ℤ) - (X.val : ℤ) with hd
  have hdcast : (d : ZMod q) = (m : ZMod q) := by
    rw [hd]; push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]; exact hm3.symm
  have hdvd : (q : ℤ) ∣ d - m := by
    have h0 : ((d - m : ℤ) : ZMod q) = 0 := by
      rw [Int.cast_sub, hdcast, sub_self]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (d - m) q).mp h0
  have hdZ : Z.val < q := ZMod.val_lt Z
  have hdX : X.val < q := ZMod.val_lt X
  have hbounds : -(q : ℤ) < d ∧ d < (q : ℤ) := by
    rw [hd]; constructor <;> omega
  have habs : |d - m| < 2 * (q : ℤ) := by
    have h1 : |d - m| ≤ (q : ℤ) + (R : ℤ) - 2 := by
      rw [abs_le]; constructor <;> omega
    omega
  have hx := int_eq_neg_or_eq_or_eq_of_dvd_of_abs_lt_two hq hdvd habs
  rcases hx with hx | hx | hx
  · right
    have hdm : d = m - q := by omega
    rw [hdm, abs_of_neg (by omega : m - (q : ℤ) < 0)]
    omega
  · left
    have hdm : d = m := by omega
    rw [hdm]
    exact abs_le.mpr ⟨by omega, by omega⟩
  · right
    have hdm : d = m + q := by omega
    rw [hdm, abs_of_nonneg (by omega : 0 ≤ m + (q : ℤ))]
    omega

noncomputable def shortBox (R q n : ℕ) : Finset (Fin n → ZMod q) :=
  Fintype.piFinset fun _ : Fin n => shortSignedSet R q

theorem mem_shortBox {R q n : ℕ} {v : Fin n → ZMod q} :
    v ∈ shortBox R q n ↔ ∀ i, v i ∈ shortSignedSet R q := by
  simp [shortBox]

theorem card_shortBox {R q n : ℕ} :
    (shortBox R q n).card = (shortSignedSet R q).card ^ n := by
  rw [shortBox, Fintype.card_piFinset_const]

theorem zero_mem_shortBox {R q n : ℕ} (hR : 1 ≤ R) :
    (0 : Fin n → ZMod q) ∈ shortBox R q n := by
  rw [mem_shortBox]; intro i; exact zero_mem_shortSignedSet hR

theorem neg_mem_shortBox {R q n : ℕ} {v : Fin n → ZMod q}
    (hv : v ∈ shortBox R q n) : -v ∈ shortBox R q n := by
  rw [mem_shortBox] at hv ⊢
  intro i
  simpa using neg_mem_shortSignedSet (hv i)

theorem card_shortBox_le {R q n : ℕ} (hR : 1 ≤ R) :
    (shortBox R q n).card ≤ (2 * R - 1) ^ n := by
  rw [card_shortBox]
  exact Nat.pow_le_pow_left (card_shortSignedSet_le hR) n

theorem card_shortBox_two_k_le {R q k : ℕ} (hR : 1 ≤ R) :
    (shortBox R q (2 * k)).card ≤ (2 * R - 1) ^ (2 * k) :=
  card_shortBox_le hR

-- ground-truth checks
example : (1 : ZMod 4) ∈ shortSignedSet 2 4 := by
  rw [mem_shortSignedSet]; exact ⟨1, by norm_num, by norm_num, by norm_num⟩

example : (2 : ZMod 4) ∉ shortSignedSet 2 4 := by
  rw [mem_shortSignedSet]
  rintro ⟨m, h1, h2, h3⟩
  have hm : m = -1 ∨ m = 0 ∨ m = 1 := by
    interval_cases m <;> simp
  rcases hm with rfl | rfl | rfl <;> exact absurd h3 (by decide)

example : (shortSignedSet 1 2).card = 1 := by
  rw [card_shortSignedSet (by norm_num) (by norm_num)]

example : (shortBox 1 2 2).card = 1 := by
  rw [card_shortBox, card_shortSignedSet (by norm_num) (by norm_num)]
  norm_num

#print axioms mem_shortSignedSet
#print axioms zero_mem_shortSignedSet
#print axioms neg_mem_shortSignedSet
#print axioms card_shortSignedSet
#print axioms card_shortSignedSet_le
#print axioms shortSignedSet_val
#print axioms shortSignedSet_sub_val
#print axioms card_shortBox
#print axioms card_shortBox_le
#print axioms card_shortBox_two_k_le

end Erdos142