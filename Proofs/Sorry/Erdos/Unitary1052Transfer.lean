import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic

set_option autoImplicit false

namespace Erdos1052

/-- A prime congruent to three modulo four cannot divide a natural square plus one. -/
theorem not_dvd_sq_add_one (q x : ℕ) (hq : q.Prime) (hmod : q % 4 = 3) :
    ¬ q ∣ x ^ 2 + 1 := by
  letI : Fact q.Prime := ⟨hq⟩
  intro hd
  have hz : (x : ZMod q) ^ 2 + 1 = 0 := by
    rcases hd with ⟨k, hk⟩
    have hc := congrArg (fun n : ℕ => (n : ZMod q)) hk
    simpa using hc
  have hs : (x : ZMod q) ^ 2 = -(1 : ZMod q) ^ 2 := by
    simpa only [one_pow] using (eq_neg_iff_add_eq_zero.mpr hz)
  exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' one_ne_zero hs hmod

/-- An indexed square component with prime base three modulo four transfers through
an even-power canceled identity to the odd successor, including its factor two.
The scalar on the right is arbitrary and zero exponents are allowed. -/
theorem square_component_transfer {ι : Type*} (s : Finset ι) (q c : ι → ℕ)
    (a P R : ℕ) (i : ι) (hi : i ∈ s) (ha : Even a) (hP : Odd P)
    (hq : (q i).Prime) (hmod : q i % 4 = 3)
    (hid : (2 ^ a + 1) * (P + 1) * (∏ j ∈ s, (q j ^ (2 * c j) + 1)) =
      R * (∏ j ∈ s, q j ^ (2 * c j))) :
    q i ^ (2 * c i) ∣ P + 1 ∧
      2 * q i ^ (2 * c i) ∣ P + 1 ∧
      2 * q i ^ (2 * c i) ≤ P + 1 := by
  have hcop_sq (x : ℕ) : Nat.Coprime (q i) (x ^ 2 + 1) :=
    hq.coprime_iff_not_dvd.mpr (not_dvd_sq_add_one (q i) x hq hmod)
  have hcop_a : Nat.Coprime (q i) (2 ^ a + 1) := by
    obtain ⟨k, hk⟩ := ha
    rw [hk, pow_add, ← pow_two]
    exact hcop_sq (2 ^ k)
  have hcop_prod : Nat.Coprime (q i) (∏ j ∈ s, (q j ^ (2 * c j) + 1)) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro j _hj
    rw [Nat.mul_comm 2 (c j), pow_mul]
    exact hcop_sq (q j ^ c j)
  have hcop : Nat.Coprime (q i ^ (2 * c i))
      ((2 ^ a + 1) * (∏ j ∈ s, (q j ^ (2 * c j) + 1))) :=
    (hcop_a.mul_right hcop_prod).pow_left (2 * c i)
  have hfactor : q i ^ (2 * c i) ∣ ∏ j ∈ s, q j ^ (2 * c j) :=
    Finset.dvd_prod_of_mem (fun j => q j ^ (2 * c j)) hi
  have hleft : q i ^ (2 * c i) ∣
      ((2 ^ a + 1) * (∏ j ∈ s, (q j ^ (2 * c j) + 1))) * (P + 1) := by
    have hright := dvd_mul_of_dvd_right hfactor R
    rw [← hid] at hright
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hright
  have htransfer : q i ^ (2 * c i) ∣ P + 1 := hcop.dvd_of_dvd_mul_left hleft
  have hoddq : Odd (q i) := Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_three hmod)
  have htwo : 2 ∣ P + 1 := by
    obtain ⟨k, hk⟩ := hP
    exact ⟨k + 1, by omega⟩
  have hcop_two : Nat.Coprime 2 (q i ^ (2 * c i)) :=
    Nat.coprime_two_left.mpr hoddq.pow
  have hdouble : 2 * q i ^ (2 * c i) ∣ P + 1 :=
    hcop_two.mul_dvd_of_dvd_of_dvd htwo htransfer
  exact ⟨htransfer, hdouble, Nat.le_of_dvd (Nat.zero_lt_succ P) hdouble⟩

/-- Under the full conditional four-core hypotheses and canceled natural-number identity,
a square component whose prime base is three modulo four divides `P + 1`, twice that
component divides `P + 1`, and twice that component is at most `P + 1`.
No joint satisfiability of this unresolved fixed-core identity is asserted. -/
theorem fixed_core_square_component_transfer {ι : Type*} (s : Finset ι)
    (q c : ι → ℕ) (a p e P : ℕ) (i : ι)
    (ha : Even a) (_ha12 : 12 ≤ a) (_hp : p.Prime) (_hp13 : 13 < p)
    (hp24 : p % 24 = 1) (_he : 0 < e) (_heodd : Odd e) (hP : P = p ^ e)
    (hcomponents : ∀ j ∈ s, (q j).Prime ∧ Odd (q j) ∧
      q j ≠ 3 ∧ q j ≠ 5 ∧ q j ≠ 7 ∧ q j ≠ 13 ∧ q j ≠ p ∧ 0 < c j)
    (_hdistinct : Set.InjOn q (↑s : Set ι))
    (hid : (2 ^ a + 1) * (P + 1) * (∏ j ∈ s, (q j ^ (2 * c j) + 1)) =
      2 ^ (a - 6) * 65 * P * (∏ j ∈ s, q j ^ (2 * c j)))
    (hi : i ∈ s) (hmod : q i % 4 = 3) :
    q i ^ (2 * c i) ∣ P + 1 ∧
      2 * q i ^ (2 * c i) ∣ P + 1 ∧
      2 * q i ^ (2 * c i) ≤ P + 1 := by
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  have hPodd : Odd P := hP ▸ hpodd.pow
  exact square_component_transfer s q c a P (2 ^ (a - 6) * 65 * P) i hi ha hPodd
    (hcomponents i hi).1 hmod hid

-- A nonempty positive-exponent model jointly satisfies every generalized premise.
example :
    let s : Finset (Fin 1) := {0}
    let q : Fin 1 → ℕ := fun _ => 11
    let c : Fin 1 → ℕ := fun _ => 1
    (0 : Fin 1) ∈ s ∧ Even 12 ∧ Odd 241 ∧ (q 0).Prime ∧ q 0 % 4 = 3 ∧
      (2 ^ 12 + 1) * (241 + 1) * (∏ j ∈ s, (q j ^ (2 * c j) + 1)) =
        999668 * (∏ j ∈ s, q j ^ (2 * c j)) := by
  decide

-- The generalized unit includes exponent zero: its component is one.
example :
    let s : Finset (Fin 1) := {0}
    let q : Fin 1 → ℕ := fun _ => 3
    let c : Fin 1 → ℕ := fun _ => 0
    (0 : Fin 1) ∈ s ∧ Even 0 ∧ Odd 1 ∧ (q 0).Prime ∧ q 0 % 4 = 3 ∧
      (2 ^ 0 + 1) * (1 + 1) * (∏ j ∈ s, (q j ^ (2 * c j) + 1)) =
        8 * (∏ j ∈ s, q j ^ (2 * c j)) := by
  decide

-- Empty indices cannot satisfy the membership premise.
example {ι : Type*} (i : ι) (hi : i ∈ (∅ : Finset ι)) : False := by
  simp at hi

end Erdos1052
