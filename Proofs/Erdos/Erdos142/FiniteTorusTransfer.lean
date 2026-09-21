/-
  Erdős Problem #142 — the finite torus transfer.

  This module closes the finite transfer: it assembles the ambient slice
  (`TorusProductSlicing`), the affine-translation averaging of
  `Erdos.Erdos142.AffineTranslationAverage`, and the signed short-box avoidance
  of `TorusTransferArithmetic` into a single counting statement.

  The pipeline:

  * `threeAPFree_affinePreimage` — for a direction `b` avoiding all short
    multiples of the signed box, every affine preimage of a slice is 3-AP-free.
    A hypothetical natural three-term progression in the preimage yields a
    modular progression inside the slice, whose endpoint difference lands in
    `shortBox R q (2*k)`; a positive index difference then produces a short
    multiple `t • b` inside the box, contradicting avoidance.
  * `card_mul_le_card_mul_rothNumberNat_torusProductSlice` — the finite capacity
    bound `N * #slice ≤ q^(2*k) * rothNumberNat N`.
  * `exists_torusProductSlice_certificate` — the combined slicing/capacity
    certificate for a single slice index.
  * `finiteTorusTransfer` — the final real-cast finite transfer inequality.

  This module does not perform the torus-grid census or any asymptotic
  parameter optimization.
-/

import Erdos.Erdos142.TorusProductSlicing
import Erdos.Erdos142.AffineTranslationAverage

set_option autoImplicit false

namespace Erdos142

/-- **Subtraction of natural multiples.**  For `n ≤ m` and any element `b` of an
additive commutative group, `m • b - n • b = (m - n) • b`. -/
theorem nsmul_sub_nsmul {G : Type*} [AddCommGroup G] (b : G) {m n : ℕ} (h : n ≤ m) :
    m • b - n • b = (m - n) • b := by
  have hm : m = (m - n) + n := (Nat.sub_add_cancel h).symm
  conv_lhs => rw [hm]
  rw [add_nsmul, add_sub_cancel_right]

/-- **AP-free affine preimages.**  Let `b` be a direction avoiding every short
multiple of the signed box `shortBox R q (2*k)`, i.e. `t • b ∉ shortBox R q (2*k)`
for all `1 ≤ t < N`.  Then for every translation `a` the affine preimage of the
ambient slice `torusProductSlice e q k R j` is 3-AP-free.

A natural progression `x, y, z` (with `x + z = y + y`) in the preimage gives a
modular progression `(a + x•b) + (a + z•b) = 2 • (a + y•b)` inside the slice, so
`sub_mem_shortBox_of_torusProductSlice_AP` puts the endpoint difference
`(a + x•b) - (a + z•b)` in the box.  For `x ≠ z` the positive natural difference
`t` is identified with `±(t • b)`, using negation stability in the reversed
orientation, and contradicts avoidance; hence `x = z`, and the natural AP
equation forces `x = y`.  No injectivity premise is used. -/
theorem threeAPFree_affinePreimage {e : ℝ} {q k R j N : ℕ} [NeZero q]
    (he : 6 ≤ e) (hq : 0 < q) (hR : 1 ≤ R)
    (b a : Fin (2 * k) → ZMod q)
    (hb : ∀ t : ℕ, 1 ≤ t → t < N → t • b ∉ shortBox R q (2 * k)) :
    ThreeAPFree ((affinePreimage (torusProductSlice e q k R j) N b a : Finset ℕ) : Set ℕ) := by
  rw [ThreeAPFree]
  intro x hx y hy z hz hxyz
  simp only [Finset.mem_coe, mem_affinePreimage] at hx hy hz
  obtain ⟨_, hxS⟩ := hx
  obtain ⟨hyN, hyS⟩ := hy
  obtain ⟨hzN, hzS⟩ := hz
  have hAP : (a + x • b) + (a + z • b) = 2 • (a + y • b) := by
    calc (a + x • b) + (a + z • b)
        = 2 • a + (x + z) • b := by rw [add_nsmul, two_nsmul]; abel
      _ = 2 • a + (y + y) • b := by rw [hxyz]
      _ = 2 • (a + y • b) := by rw [add_nsmul, two_nsmul]; abel
  have hbox : (a + x • b) - (a + z • b) ∈ shortBox R q (2 * k) :=
    sub_mem_shortBox_of_torusProductSlice_AP he hq hR hxS hyS hzS hAP
  rcases lt_trichotomy x z with hlt | heq | hgt
  · have hmem : (z - x) • b ∈ shortBox R q (2 * k) := by
      have hneg := neg_mem_shortBox hbox
      rwa [add_sub_add_left_eq_sub, ← neg_sub, nsmul_sub_nsmul b (le_of_lt hlt),
        neg_neg] at hneg
    exact absurd hmem (hb (z - x) (Nat.sub_pos_of_lt hlt) (by omega))
  · omega
  · have hmem : (x - z) • b ∈ shortBox R q (2 * k) := by
      rwa [add_sub_add_left_eq_sub, nsmul_sub_nsmul b (le_of_lt hgt)] at hbox
    exact absurd hmem (hb (x - z) (Nat.sub_pos_of_lt hgt) (by omega))

/-- **Finite capacity of an ambient slice.**  For prime `q` with `1 ≤ N ≤ q`,
`1 ≤ R`, and `N * (2*R - 1)^(2*k) < q^(2*k)`, every slice satisfies

  `N * (torusProductSlice e q k R j).card ≤ q^(2*k) * rothNumberNat N`.

The avoiding direction is produced by `signedShortBox_exists_avoiding`, making
every affine preimage 3-AP-free, and the Roth-number capacity bound
`mul_card_le_card_mul_rothNumberNat_of_threeAPFree` closes the count. -/
theorem card_mul_le_card_mul_rothNumberNat_torusProductSlice {e : ℝ}
    {q k R N : ℕ} [Fact q.Prime] (he : 6 ≤ e) (hR : 1 ≤ R)
    (hN1 : 1 ≤ N) (hNq : N ≤ q)
    (hscale : N * (2 * R - 1) ^ (2 * k) < q ^ (2 * k)) (j : ℕ) :
    N * (torusProductSlice e q k R j).card ≤ q ^ (2 * k) * rothNumberNat N := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hq : 0 < q := (Fact.out : q.Prime).pos
  obtain ⟨b, hb⟩ :=
    signedShortBox_exists_avoiding (q := q) (k := k) (R := R) (N := N) hR hN1 hNq hscale
  have hfree : ∀ a : Fin (2 * k) → ZMod q,
      ThreeAPFree ((affinePreimage (torusProductSlice e q k R j) N b a : Finset ℕ) : Set ℕ) :=
    fun a => threeAPFree_affinePreimage he hq hR b a hb
  have h := mul_card_le_card_mul_rothNumberNat_of_threeAPFree
    (torusProductSlice e q k R j) N b hfree
  rwa [Fintype.card_fun, ZMod.card, Fintype.card_fin] at h

/-- **Combined slice certificate.**  For prime `q` with `1 ≤ N ≤ q`, `1 ≤ R`,
`6 ≤ e`, and the scale inequality, some slice index `j` carries all three
certificates at once: the retained slicing upper bound on `j`, the real slice
lower inequality, and the natural capacity inequality. -/
theorem exists_torusProductSlice_certificate {e : ℝ} {q k R N : ℕ} [Fact q.Prime]
    (he : 6 ≤ e) (hN1 : 1 ≤ N) (hNq : N ≤ q) (hR : 1 ≤ R)
    (hscale : N * (2 * R - 1) ^ (2 * k) < q ^ (2 * k)) :
    ∃ j : ℕ,
      j < Nat.floor (((2921 / 144 : ℝ) * (k : ℝ) * e ^ 2) /
            ((R : ℝ) ^ 2 / (2 * (q : ℝ) ^ 2))) + 1 ∧
        (((torusGrid e⁻¹ q).card ^ k : ℕ) : ℝ) * (R : ℝ) ^ 2 ≤
          (41 * (k : ℝ) * e ^ 2 * (q : ℝ) ^ 2 + (R : ℝ) ^ 2) *
            ((torusProductSlice e q k R j).card : ℝ) ∧
          N * (torusProductSlice e q k R j).card ≤ q ^ (2 * k) * rothNumberNat N := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hq : 0 < q := (Fact.out : q.Prime).pos
  have hRpos : 0 < R := hR
  obtain ⟨j, hj1, hj2⟩ := exists_torusProductSlice_card_mul_le_41 he hq hRpos
  exact ⟨j, hj1, hj2,
    card_mul_le_card_mul_rothNumberNat_torusProductSlice he hR hN1 hNq hscale j⟩

/-- **Final finite torus transfer.**  For prime `q`, `6 ≤ e`, `1 ≤ N ≤ q`,
`1 ≤ R`, and the scale inequality `N * (2*R - 1)^(2*k) < q^(2*k)`:

  `(N:ℝ) * (R:ℝ)^2 * ((torusGrid e⁻¹ q).card ^ k : ℕ) ≤
     (q:ℝ)^(2*k) * (41*(k:ℝ)*e^2*(q:ℝ)^2 + (R:ℝ)^2) * (rothNumberNat N : ℝ)`.

The proof picks a slice from `exists_torusProductSlice_card_mul_le_41`, casts the
natural capacity inequality, multiplies the two monotone inequalities by the
nonnegative factors `(N:ℝ)` and the coefficient, and normalizes with `ring`. -/
theorem finiteTorusTransfer {e : ℝ} {q k R N : ℕ} [Fact q.Prime]
    (he : 6 ≤ e) (hN1 : 1 ≤ N) (hNq : N ≤ q) (hR : 1 ≤ R)
    (hscale : N * (2 * R - 1) ^ (2 * k) < q ^ (2 * k)) :
    (N : ℝ) * (R : ℝ) ^ 2 * ((((torusGrid e⁻¹ q).card ^ k : ℕ)) : ℝ) ≤
      ((q : ℝ) ^ (2 * k)) *
        (41 * (k : ℝ) * e ^ 2 * (q : ℝ) ^ 2 + (R : ℝ) ^ 2) *
        (rothNumberNat N : ℝ) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hq : 0 < q := (Fact.out : q.Prime).pos
  have hRpos : 0 < R := hR
  obtain ⟨j, _, hj2⟩ := exists_torusProductSlice_card_mul_le_41 he hq hRpos
  have hcap := card_mul_le_card_mul_rothNumberNat_torusProductSlice he hR hN1 hNq hscale j
  have hcapR : (N : ℝ) * ((torusProductSlice e q k R j).card : ℝ) ≤
      (q : ℝ) ^ (2 * k) * (rothNumberNat N : ℝ) := by
    exact_mod_cast hcap
  have hcoef : (0 : ℝ) ≤ 41 * (k : ℝ) * e ^ 2 * (q : ℝ) ^ 2 + (R : ℝ) ^ 2 := by positivity
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  calc (N : ℝ) * (R : ℝ) ^ 2 * ((((torusGrid e⁻¹ q).card ^ k : ℕ)) : ℝ)
      = (N : ℝ) * (((((torusGrid e⁻¹ q).card ^ k : ℕ)) : ℝ) * (R : ℝ) ^ 2) := by ring
    _ ≤ (N : ℝ) *
          ((41 * (k : ℝ) * e ^ 2 * (q : ℝ) ^ 2 + (R : ℝ) ^ 2) *
            ((torusProductSlice e q k R j).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hj2 hNnonneg
    _ = ((N : ℝ) * ((torusProductSlice e q k R j).card : ℝ)) *
          (41 * (k : ℝ) * e ^ 2 * (q : ℝ) ^ 2 + (R : ℝ) ^ 2) := by ring
    _ ≤ ((q : ℝ) ^ (2 * k) * (rothNumberNat N : ℝ)) *
          (41 * (k : ℝ) * e ^ 2 * (q : ℝ) ^ 2 + (R : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hcapR hcoef
    _ = ((q : ℝ) ^ (2 * k)) *
          (41 * (k : ℝ) * e ^ 2 * (q : ℝ) ^ 2 + (R : ℝ) ^ 2) *
          (rothNumberNat N : ℝ) := by ring

-- Boundary and satisfiability checks.

/-- The premises force `q > 0`. -/
example (q : ℕ) [Fact q.Prime] : 0 < q := (Fact.out : q.Prime).pos

/-- At `k = 0` and `N ≥ 1` the scale premise is unsatisfiable: it reads
`N < 1`.  The transfer theorem is therefore vacuous there, and no spurious
positivity hypothesis on `k` is introduced. -/
example (N q : ℕ) (hN : 1 ≤ N) : ¬ (N * (2 * 1 - 1) ^ (2 * 0) < q ^ (2 * 0)) := by
  simp only [Nat.mul_zero, pow_zero, mul_one]
  omega

/-- Satisfiability of the transfer hypotheses at the concrete parameters
`e = 6`, `q = 2`, `k = 1`, `R = 1`, `N = 1` (scale premise `1 < 4`), yielding
the concrete conclusion and certifying non-vacuity. -/
example :
    (1 : ℝ) * (1 : ℝ) ^ 2 * ((((torusGrid (6 : ℝ)⁻¹ 2).card ^ 1 : ℕ)) : ℝ) ≤
      ((2 : ℝ) ^ (2 * 1)) *
        (41 * (1 : ℝ) * (6 : ℝ) ^ 2 * (2 : ℝ) ^ 2 + (1 : ℝ) ^ 2) *
        (rothNumberNat 1 : ℝ) := by
  have h := finiteTorusTransfer (e := 6) (q := 2) (k := 1) (R := 1) (N := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa using h

#print axioms nsmul_sub_nsmul
#print axioms threeAPFree_affinePreimage
#print axioms card_mul_le_card_mul_rothNumberNat_torusProductSlice
#print axioms exists_torusProductSlice_certificate
#print axioms finiteTorusTransfer

end Erdos142