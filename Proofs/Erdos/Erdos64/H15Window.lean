/-
Erdős–Gyárfás problem 64 — an arithmetic consequence of the H15 cycle window.

SOURCE AND SCOPE. Garcia, arXiv:2609.04686, gives a Window Lemma for H15
replacements.  In the notation used here, a base cycle has positive length `l`
and visits the exceptional `v-w` terminal pair `b` times, with `b ≤ l`; the
lemma's spectrum is every integer in `[4*l + 2*b, 15*l]` (equivalently
`[6*l - 2*a, 15*l]` for `a = l-b`).

This module formalizes the arithmetic observation that this interval always
contains `2^k` for some `k ≥ 2`, and the direct graph-theoretic consequence of
an abstract certificate realizing every length in that interval.  It reuses
`HasSimpleCycleOfLength` from `Incidence.lean` and `HasPowerOfTwoCycle` from
`Basic.lean`, so both conclusions concern honest `SimpleGraph.Walk.IsCycle`
witnesses.

CLAIM BOUNDARY. Garcia's graph-theoretic Window Lemma supplies the abstract
certificate below for an actual H15 replacement and a base cycle.  This module
does not define H15 gadgets or replacement, and does not prove Garcia's Window
Lemma.  Consequently it does not claim a fully formal global theorem about H15
replacement graphs; its graph theorem is explicitly conditional on the window
certificate.
-/

import Erdos.Erdos64.Basic
import Erdos.Erdos64.Incidence

set_option autoImplicit false

namespace Erdos64

open SimpleGraph

universe u

variable {V : Type u}

private theorem self_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      have hpow_pos : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
      omega

/-- For a positive base length `l` and an exceptional-terminal count `b ≤ l`,
the H15 length window `[4*l + 2*b, 15*l]` contains a power `2^k` with `k ≥ 2`.

The proof chooses the least `k` for which `6*l ≤ 2^k`.  Minimality makes the
preceding power smaller than `6*l`, hence `2^k < 12*l`; the two endpoints then
follow from `b ≤ l` and `12*l ≤ 15*l`. -/
theorem exists_powerOfTwo_in_h15Window (l b : ℕ) (hl : 0 < l) (hb : b ≤ l) :
    ∃ k : ℕ, 2 ≤ k ∧ 4 * l + 2 * b ≤ 2 ^ k ∧ 2 ^ k ≤ 15 * l := by
  let P : ℕ → Prop := fun k => 6 * l ≤ 2 ^ k
  have hexists : ∃ k : ℕ, P k := by
    refine ⟨6 * l, ?_⟩
    exact self_le_two_pow (6 * l)
  let k : ℕ := Nat.find hexists
  have hk_spec : P k := by
    simpa only [k] using Nat.find_spec hexists
  have hk_two : 2 ≤ k := by
    by_contra hk_not
    have hk_lt : k < 2 := Nat.lt_of_not_ge hk_not
    interval_cases k <;> norm_num [P] at hk_spec <;> omega
  have hprev_not : ¬ P (k - 1) := by
    apply Nat.find_min hexists
    omega
  have hprev_lt : 2 ^ (k - 1) < 6 * l := by
    simp only [P] at hprev_not
    omega
  have hpow_eq : 2 ^ k = 2 ^ (k - 1) * 2 := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [pow_succ]
  have hpow_lt_twelve : 2 ^ k < 12 * l := by
    rw [hpow_eq]
    omega
  refine ⟨k, hk_two, ?_, ?_⟩
  · exact le_trans (by omega : 4 * l + 2 * b ≤ 6 * l) hk_spec
  · omega

/-- Boundary fixture at `l = 1`, `b = 0`: the power `2^2 = 4` lies in the H15
window `[4,15]`. -/
theorem powerOfTwo_mem_h15Window_one_zero :
    2 ≤ 2 ∧ 4 * 1 + 2 * 0 ≤ 2 ^ 2 ∧ 2 ^ 2 ≤ 15 * 1 := by
  norm_num

/-- Boundary fixture at `l = 1`, `b = 1`: the power `2^3 = 8` lies in the H15
window `[6,15]`. -/
theorem powerOfTwo_mem_h15Window_one_one :
    2 ≤ 3 ∧ 4 * 1 + 2 * 1 ≤ 2 ^ 3 ∧ 2 ^ 3 ≤ 15 * 1 := by
  norm_num

/-- An abstract H15 cycle-window certificate says that `G` realizes a simple
cycle of every exact integer length in `[4*l + 2*b, 15*l]`.  Positivity of `l`
and the bound `b ≤ l` remain explicit hypotheses of the theorem consuming the
certificate, rather than being hidden in this realization predicate. -/
def H15CycleWindowCertificate (G : SimpleGraph V) (l b : ℕ) : Prop :=
  ∀ n : ℕ, 4 * l + 2 * b ≤ n → n ≤ 15 * l → HasSimpleCycleOfLength G n

/-- Unfolding an H15 cycle-window certificate gives its exact cycle-realization
property. -/
@[simp] theorem h15CycleWindowCertificate_iff (G : SimpleGraph V) (l b : ℕ) :
    H15CycleWindowCertificate G l b ↔
      ∀ n : ℕ, 4 * l + 2 * b ≤ n → n ≤ 15 * l → HasSimpleCycleOfLength G n :=
  Iff.rfl

/-- An H15 cycle-window certificate over valid base data forces an honest
power-of-two simple cycle in `G`.  The theorem assumes, rather than proves, the
graph-theoretic H15 Window Lemma. -/
theorem H15CycleWindowCertificate.hasPowerOfTwoCycle {G : SimpleGraph V} {l b : ℕ}
    (hwindow : H15CycleWindowCertificate G l b) (hl : 0 < l) (hb : b ≤ l) :
    HasPowerOfTwoCycle G := by
  obtain ⟨k, hk, hlower, hupper⟩ := exists_powerOfTwo_in_h15Window l b hl hb
  obtain ⟨v, c, hcycle, hlength⟩ := hwindow (2 ^ k) hlower hupper
  exact ⟨k, hk, v, c, hcycle, hlength⟩

end Erdos64
