/-
  Erdős Problem #142 — the elementary one-scale window-covering bound
  `L * rothNumberNat N ≤ 2 * N * rothNumberNat L` for `1 ≤ L ≤ N`.

  This is the smallest Lean artifact isolated by the written contract
  `Documents/erdos142-carry-discriminator.md`.  It packages the ceiling
  estimate used in the LP route audit: writing `q = N / L + 1`, the block
  (subadditivity) inequality `FixedRadixUpperEnvelope.rothNumberNat_mul_le`
  gives `rothNumberNat N ≤ q * rothNumberNat L`, and `L * q ≤ 2 * N` follows
  from `L * (N / L) ≤ N` and `L ≤ N`.  Equivalently, in terms of the density
  `ρ = rothNumberNat N / N`, it says `L * ρ / 2 ≤ rothNumberNat L`: the uniform
  LP assignment `z_v = ρ / 2` satisfies every injective affine-window cap
  `∑_{v ∈ P} z_v ≤ rothNumberNat L` for windows of length `L ≤ N`.

  What this file does and does not say.  It proves only the local-cap
  feasibility arithmetic used in the one-scale obstruction.  It does **not**
  formalize LP duality, does **not** formalize the target `P` of the contract
  (which is neither stated nor assumed here), and does **not** assert any new
  upper bound for the Roth number.  The Roth numbers are used through the
  existing `rothNumberNat_mul_le` and `rothNumberNat.monotone`, not through a
  reimplementation.

  No `sorry`, no `unsafe`, no new axioms; standard axioms only.
-/

import Erdos.Erdos142.FixedRadixUpperEnvelope

set_option autoImplicit false

namespace Erdos142

/-- **One-scale window-covering bound for the Roth number.**  For naturals `N`
and `L` with `1 ≤ L` and `L ≤ N`,

`L * rothNumberNat N ≤ 2 * N * rothNumberNat L`.

Route: set `q = N / L + 1`.  Since `N = L * (N / L) + N % L` and `N % L < L`,
we get `N ≤ q * L`; monotonicity gives `rothNumberNat N ≤ rothNumberNat (q * L)`
and the block inequality `rothNumberNat_mul_le` gives
`rothNumberNat (q * L) ≤ q * rothNumberNat L`.  Multiplying by `L` and using
`L * q = L * (N / L) + L ≤ N + L ≤ 2 * N` closes the claim.

This is the coarser always-valid estimate `rothNumberNat N ≤
(N / L + 1) * rothNumberNat L`: the proof uses the factor `N / L + 1`, which
equals the ceiling `⌈N / L⌉` exactly when `L ∤ N` and is one larger when
`L ∣ N`.  It is an arithmetic fact about Roth numbers and asserts nothing about
Erdős #142, LP duality, or `P`. -/
theorem mul_rothNumberNat_le_two_mul_mul {N L : ℕ} (hL1 : 1 ≤ L) (hLN : L ≤ N) :
    L * rothNumberNat N ≤ 2 * N * rothNumberNat L := by
  set q := N / L + 1 with hq
  have hNqL : N ≤ q * L := by
    have hmod : N % L < L := Nat.mod_lt N (by omega)
    have hdec : N = L * (N / L) + N % L := (Nat.div_add_mod N L).symm
    rw [hq]
    nlinarith [hdec, hmod]
  have hmono : rothNumberNat N ≤ rothNumberNat (q * L) := rothNumberNat.monotone hNqL
  have hblock : rothNumberNat (q * L) ≤ q * rothNumberNat L := rothNumberNat_mul_le q L
  have h1 : rothNumberNat N ≤ q * rothNumberNat L := hmono.trans hblock
  have hLq : L * q ≤ 2 * N := by
    have hdiv : (N / L) * L ≤ N := Nat.div_mul_le_self N L
    rw [hq]
    nlinarith
  calc L * rothNumberNat N ≤ L * (q * rothNumberNat L) := Nat.mul_le_mul_left L h1
    _ = (L * q) * rothNumberNat L := by ring
    _ ≤ (2 * N) * rothNumberNat L := Nat.mul_le_mul_right _ hLq
    _ = 2 * N * rothNumberNat L := by ring

/-- **Real-valued corollary matching uniform LP feasibility.**  For naturals `N`
and `L` with `1 ≤ L` and `L ≤ N`,

`(L : ℝ) * ((rothNumberNat N : ℝ) / (2 * (N : ℝ))) ≤ (rothNumberNat L : ℝ)`.

Writing `ρ = rothNumberNat N / N`, this is exactly `L * ρ / 2 ≤ rothNumberNat L`,
the affine-window cap satisfied by the uniform assignment `z_v = ρ / 2` on
`[N]`.  The denominator is the explicit positive factor `2 * N`; there is no
division-by-zero ambiguity since `N ≥ L ≥ 1`.

The proof casts the natural-number bound
`mul_rothNumberNat_le_two_mul_mul`, rewrites `L * (r(N) / (2 * N))` as
`(L * r(N)) / (2 * N)`, and divides by the positive `2 * N`. -/
theorem real_mul_rothNumberNat_div_le {N L : ℕ} (hL1 : 1 ≤ L) (hLN : L ≤ N) :
    (L : ℝ) * ((rothNumberNat N : ℝ) / (2 * (N : ℝ))) ≤ (rothNumberNat L : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hcore : L * rothNumberNat N ≤ 2 * N * rothNumberNat L :=
    mul_rothNumberNat_le_two_mul_mul hL1 hLN
  have hcast : (L : ℝ) * (rothNumberNat N : ℝ) ≤
      2 * (N : ℝ) * (rothNumberNat L : ℝ) := by
    exact_mod_cast hcore
  rw [← mul_div_assoc]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (N : ℝ))]
  nlinarith [hcast]

/-- **Ground-truth value `rothNumberNat 2 = 2`.**  `range 2 = {0, 1}` is
three-term-progression-free and has cardinality `2`, while `rothNumberNat_le`
gives the matching upper bound. -/
theorem rothNumberNat_two : rothNumberNat 2 = 2 := by
  have hge : 2 ≤ rothNumberNat 2 := by
    have hfree : ThreeAPFree ((Finset.range 2 : Finset ℕ) : Set ℕ) := by decide
    have h := ThreeAPFree.le_rothNumberNat (n := 2) (k := 2) (Finset.range 2) hfree
      (by intro x hx; simpa using Finset.mem_range.mp hx) (by simp)
    simpa using h
  have hle := rothNumberNat_le 2
  omega

/-- **Ground-truth value `rothNumberNat 3 = 2`.**  The lower bound is
monotonicity from `rothNumberNat_two`; the upper bound `≤ 3` is
`rothNumberNat_le`, and the value `3` is excluded because `rothNumberNat_spec 3`
would then produce a three-term-progression-free subset of `range 3` of size `3`,
i.e. `range 3` itself, which contains the nontrivial progression `0, 1, 2`. -/
theorem rothNumberNat_three : rothNumberNat 3 = 2 := by
  have hge : 2 ≤ rothNumberNat 3 := by
    have h2 : rothNumberNat 2 = 2 := rothNumberNat_two
    have hmono : rothNumberNat 2 ≤ rothNumberNat 3 := rothNumberNat.monotone (by norm_num)
    omega
  have hle : rothNumberNat 3 ≤ 3 := rothNumberNat_le 3
  rcases eq_or_lt_of_le hle with h | h
  · exfalso
    obtain ⟨t, ht, hcard, hfree⟩ := rothNumberNat_spec 3
    have ht_eq : t = Finset.range 3 := by
      refine Finset.eq_of_subset_of_card_le ht ?_
      rw [hcard, h]; simp
    rw [ht_eq] at hfree
    have hc := hfree (show (0 : ℕ) ∈ (Finset.range 3 : Set ℕ) by simp)
      (show (1 : ℕ) ∈ (Finset.range 3 : Set ℕ) by simp)
      (show (2 : ℕ) ∈ (Finset.range 3 : Set ℕ) by simp) (by norm_num)
    norm_num at hc
  · omega

/-- **Non-vacuity at the endpoint `N = L = 1`.**  The bound reads
`1 * rothNumberNat 1 ≤ 2 * 1 * rothNumberNat 1`, i.e. `1 ≤ 2`. -/
example : 1 * rothNumberNat 1 ≤ 2 * 1 * rothNumberNat 1 :=
  mul_rothNumberNat_le_two_mul_mul (N := 1) (L := 1) le_rfl le_rfl

/-- **Non-vacuity at `(N, L) = (3, 2)`.**  Using `rothNumberNat_three` and
`rothNumberNat_two` the bound is the concrete true statement `4 ≤ 12`. -/
example : 2 * rothNumberNat 3 ≤ 2 * 3 * rothNumberNat 2 :=
  mul_rothNumberNat_le_two_mul_mul (N := 3) (L := 2) (by norm_num) (by norm_num)

/-- **Non-vacuity at `(N, L) = (4, 3)`.**  The theorem applies at the generic
pair without needing the value of `rothNumberNat 4`. -/
example : 3 * rothNumberNat 4 ≤ 2 * 4 * rothNumberNat 3 :=
  mul_rothNumberNat_le_two_mul_mul (N := 4) (L := 3) (by norm_num) (by norm_num)

/-- **Ground-truth check of the real corollary at `(N, L) = (2, 1)`.**  With
`rothNumberNat_two` and `rothNumberNat_one` the inequality is the concrete
`1 / 2 ≤ 1`. -/
example : (1 : ℝ) * ((rothNumberNat 2 : ℝ) / (2 * (2 : ℝ))) ≤ (rothNumberNat 1 : ℝ) := by
  rw [rothNumberNat_two, rothNumberNat_one]
  norm_num

/-- **Non-vacuity of the real corollary at `(N, L) = (3, 3)`.**  The hypotheses
`1 ≤ L` and `L ≤ N` hold and the inequality reads
`3 * (rothNumberNat 3 / (2 * 3)) ≤ rothNumberNat 3`. -/
example : (3 : ℝ) * ((rothNumberNat 3 : ℝ) / (2 * (3 : ℝ))) ≤ (rothNumberNat 3 : ℝ) :=
  real_mul_rothNumberNat_div_le (N := 3) (L := 3) (by norm_num) (by norm_num)

end Erdos142

-- Axiom audit for the load-bearing declarations.
#print axioms Erdos142.mul_rothNumberNat_le_two_mul_mul
#print axioms Erdos142.real_mul_rothNumberNat_div_le
#print axioms Erdos142.rothNumberNat_two
#print axioms Erdos142.rothNumberNat_three