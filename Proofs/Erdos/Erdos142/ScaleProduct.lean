/-
  Erdős Problem #142 — a scale-product lower bound for the Roth number.

  Building a 3-AP-free subset of `range N` and one of `range M`, one can glue them
  into a 3-AP-free subset of a longer initial segment by the carry-free digit
  encoding

      `(a, b) ↦ a + 2 * N * b`.

  The key point is that the low digit ranges over `[0, N)`, so any two low digits
  that can be produced by a 3-term arithmetic progression sum to less than `2 * N`.
  Consequently the decomposition of a natural number into `a + 2 * N * b` with
  `a < 2 * N` is unique (`digits_eq_of_add_mul_eq`): a hypothetical three-term
  arithmetic progression whose middle term has this shape forces both coordinate
  triples to be arithmetic progressions, one in `A` and one in `B`, hence forces
  the outer terms to coincide.

  The encoded set is contained in `range (2 * N * M - N)`, which is sharp: the
  largest encoded value is `(N - 1) + 2 * N * (M - 1) = 2 * N * M - N - 1`.  This
  is where the requested endpoint `2 * N * M` is corrected: the naive statement
  `rothNumberNat (2 * N * M)` is *true* but strictly weaker than the sharp
  `rothNumberNat (2 * N * M - N)`; the latter is tight at `(N, M) = (1, 2)`, where
  both sides equal `2`.  Both forms are recorded below.

  Axiom status is checked with `#print axioms` at the end of the file.
-/

import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Tactic

set_option autoImplicit false

open Finset

namespace Erdos142

/-- The carry-free digit encoding of a pair of naturals with radix `2 * N`:
`(a, b) ↦ a + 2 * N * b`.  When `a < 2 * N` the decomposition of the value is
unique, which is the content of `digits_eq_of_add_mul_eq`. -/
def scaleEnc (N : ℕ) (p : ℕ × ℕ) : ℕ := p.1 + 2 * N * p.2

/-- Ground-truth check of `scaleEnc` on a concrete input. -/
example : scaleEnc 3 (1, 2) = 13 := rfl

/-- Ground-truth check of `scaleEnc` at the trivial radix. -/
example : scaleEnc 0 (5, 7) = 5 := rfl

/-- **Carry-free digit uniqueness.**  If `a + k * b = a' + k * b'` with
`a, a' < k` and `k > 0`, then both digits agree.  This is the arithmetic core of
the scale-product bound: it is the statement that a "sum" of two encoded values
can be decomposed coordinatewise without carrying. -/
theorem digits_eq_of_add_mul_eq {k a a' b b' : ℕ} (hk : 0 < k) (ha : a < k) (ha' : a' < k)
    (h : a + k * b = a' + k * b') : a = a' ∧ b = b' := by
  have hmod : a % k = a' % k := by
    have h' := congrArg (fun t => t % k) h
    rwa [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left] at h'
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at hmod
  refine ⟨hmod, ?_⟩
  rw [hmod] at h
  exact Nat.mul_left_cancel hk (Nat.add_left_cancel h)

/-- Encoding an element of `range N × range M` lands strictly below the sharp
endpoint `2 * N * M - N`.  The largest possible value is the excluded
`2 * N * M - N` itself. -/
theorem scaleEnc_lt {N M a b : ℕ} (hM : 0 < M) (ha : a < N) (hb : b < M) :
    scaleEnc N (a, b) < 2 * N * M - N := by
  simp only [scaleEnc]
  rw [Nat.lt_sub_iff_add_lt]
  obtain ⟨M', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hM)
  have hb' : b ≤ M' := by omega
  have hmul : 2 * N * b ≤ 2 * N * M' := Nat.mul_le_mul_left (2 * N) hb'
  rw [Nat.mul_succ]
  omega

/-- The encoding is injective on a box `A × B` with `A ⊆ range N`: distinct pairs
produce distinct encoded values, because the low digit is recovered as the residue
modulo `2 * N`. -/
theorem scaleEnc_injOn {N M : ℕ} (hN : 0 < N) {A B : Finset ℕ}
    (hA : A ⊆ Finset.range N) (_hB : B ⊆ Finset.range M) :
    Set.InjOn (scaleEnc N) ((A ×ˢ B : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
  rintro p hp q hq hpq
  rw [Finset.mem_coe, Finset.mem_product] at hp hq
  have hp1 : p.1 < N := Finset.mem_range.mp (hA hp.1)
  have hq1 : q.1 < N := Finset.mem_range.mp (hA hq.1)
  have hk : 0 < 2 * N := by omega
  have hpN : p.1 < 2 * N := by omega
  have hqN : q.1 < 2 * N := by omega
  have heq : p.1 + (2 * N) * p.2 = q.1 + (2 * N) * q.2 := by
    simpa only [scaleEnc] using hpq
  obtain ⟨h1, h2⟩ := digits_eq_of_add_mul_eq hk hpN hqN heq
  exact Prod.ext h1 h2

/-- **The encoding preserves 3-AP-freeness.**  If `A ⊆ range N` and `B ⊆ range M`
are 3-AP-free and `N > 0`, then `{a + 2 * N * b : a ∈ A, b ∈ B}` is 3-AP-free in
`ℕ`.  A three-term arithmetic progression among the encoded values has a
low-coordinate defect that is both `< 2 * N` and a multiple of `2 * N`, hence
zero by `digits_eq_of_add_mul_eq`; then the coordinate triples are arithmetic
progressions in `A` and `B`, so their outer terms coincide. -/
theorem scaleEnc_threeAPFree {N M : ℕ} (hN : 0 < N) {A B : Finset ℕ}
    (hA : A ⊆ Finset.range N) (_hB : B ⊆ Finset.range M)
    (hAfree : ThreeAPFree (A : Set ℕ)) (hBfree : ThreeAPFree (B : Set ℕ)) :
    ThreeAPFree (((A ×ˢ B).image (scaleEnc N)) : Set ℕ) := by
  intro x hx y hy z hz hxyz
  rw [Finset.mem_coe, Finset.mem_image] at hx hy hz
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hy
  obtain ⟨r, hr, rfl⟩ := hz
  rw [Finset.mem_product] at hp hq hr
  have hp1 : p.1 < N := Finset.mem_range.mp (hA hp.1)
  have hq1 : q.1 < N := Finset.mem_range.mp (hA hq.1)
  have hr1 : r.1 < N := Finset.mem_range.mp (hA hr.1)
  have hnorm : (p.1 + r.1) + 2 * N * (p.2 + r.2) = (q.1 + q.1) + 2 * N * (q.2 + q.2) := by
    have h := hxyz
    simp only [scaleEnc] at h
    ring_nf at h ⊢
    exact h
  have hk : 0 < 2 * N := by omega
  have hlowlt : p.1 + r.1 < 2 * N := by omega
  have hlowlt' : q.1 + q.1 < 2 * N := by omega
  obtain ⟨hlow, hhigh⟩ := digits_eq_of_add_mul_eq (k := 2 * N) hk hlowlt hlowlt' hnorm
  have hp1eq : p.1 = q.1 := hAfree hp.1 hq.1 hr.1 hlow
  have hp2eq : p.2 = q.2 := hBfree hp.2 hq.2 hr.2 hhigh
  simp only [scaleEnc]
  rw [hp1eq, hp2eq]

/-- **Sharp scale-product lower bound.**  `rothNumberNat N * rothNumberNat M` is at
most the Roth number of the sharp initial segment `2 * N * M - N`.  The subterm
reflects the range of the encoding `a + 2 * N * b` for `a < N`, `b < M`, whose
largest value is `2 * N * M - N - 1`. -/
theorem rothNumberNat_mul_le_rothNumberNat_sub (N M : ℕ) :
    rothNumberNat N * rothNumberNat M ≤ rothNumberNat (2 * N * M - N) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    simp
  obtain ⟨A, hA, hAcard, hAfree⟩ := rothNumberNat_spec N
  obtain ⟨B, hB, hBcard, hBfree⟩ := rothNumberNat_spec M
  have hcard : ((A ×ˢ B).image (scaleEnc N)).card = rothNumberNat N * rothNumberNat M := by
    rw [Finset.card_image_of_injOn (scaleEnc_injOn hN hA hB), Finset.card_product, hAcard, hBcard]
  rw [← hcard]
  refine ThreeAPFree.le_rothNumberNat _ (scaleEnc_threeAPFree hN hA hB hAfree hBfree) ?_ rfl
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  rw [Finset.mem_product] at hp
  exact scaleEnc_lt hM (Finset.mem_range.mp (hA hp.1)) (Finset.mem_range.mp (hB hp.2))

/-- **Scale-product lower bound, requested form.**  `rothNumberNat` is monotone, so
the sharp bound `2 * N * M - N` implies the rounded endpoint `2 * N * M`. -/
theorem rothNumberNat_mul_le_rothNumberNat_two_mul_mul (N M : ℕ) :
    rothNumberNat N * rothNumberNat M ≤ rothNumberNat (2 * N * M) :=
  (rothNumberNat_mul_le_rothNumberNat_sub N M).trans
    (rothNumberNat.monotone (Nat.sub_le (2 * N * M) N))

end Erdos142

-- Axiom audit for the load-bearing declarations.
#print axioms Erdos142.digits_eq_of_add_mul_eq
#print axioms Erdos142.scaleEnc_lt
#print axioms Erdos142.scaleEnc_injOn
#print axioms Erdos142.scaleEnc_threeAPFree
#print axioms Erdos142.rothNumberNat_mul_le_rothNumberNat_sub
#print axioms Erdos142.rothNumberNat_mul_le_rothNumberNat_two_mul_mul