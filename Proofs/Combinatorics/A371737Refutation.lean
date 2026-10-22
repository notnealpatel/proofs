/-
# A371737 — counterexample to part (2) of Wiseman's zero-set conjecture

Gus Wiseman (OEIS A371737, Apr 14 2024) conjectured that its zero positions
are A327782 and its positive positions are A368459. A371737 counts strict
integer partitions admitting a partition into at least two blocks of equal sum.
A327782 consists of positive integers not expressible as a sum of at least
two distinct positive parts with largest part dividing the sum. A368459 is
the negative set of `2 * (Bacher(n) - sigma(n)) + n + 1` (A368457), where
Bacher(n) (A368207) counts `n = wx + yz` with `max(w,x) < min(y,z)`.

At `n = 77`, Bacher(77) = 54 and sigma(77) = 96, so A368457(77) = -6.
However, A371737(77) = 0: a strict partition into `k ≥ 2` blocks of sum `s`
would give `77 = ks` and `154 ≤ s(s+1)`, impossible for `s ∈ {1,7,11}`.
Part (1) is not refuted here. Both parts are restricted below to `n ≥ 1`;
the literal part (1) also fails at `n = 0`, since A371737(0) = 0 but
0 is not in A327782.
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Order.Partition.Finpartition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace Candidates.A371737Refutation

open Finset

/-! ## Definitions -/

/-- A finite set `S` of natural numbers is *quanimous* when it admits a set
partition into two or more blocks all having the same sum.  (The OEIS NAME says
"more than one set partition with all equal block-sums"; the one-block
partition `{S}` always qualifies, so this is the same as asking for a
qualifying partition with at least two blocks.) -/
def Quanimous (S : Finset ℕ) : Prop :=
  ∃ P : Finpartition S, 2 ≤ #P.parts ∧ ∃ s : ℕ, ∀ B ∈ P.parts, ∑ x ∈ B, x = s

/-- A371737: the number of strict integer partitions of `n` (finite sets of
positive integers with sum `n`) that are quanimous. -/
noncomputable def A371737 (n : ℕ) : ℕ :=
  {S : Finset ℕ | (∀ x ∈ S, 0 < x) ∧ ∑ x ∈ S, x = n ∧ Quanimous S}.ncard

/-- Membership in A327782: `n` is a positive integer that cannot be written as
a sum of two or more distinct positive parts whose largest part divides `n`. -/
def InA327782 (n : ℕ) : Prop :=
  0 < n ∧ ¬ ∃ S : Finset ℕ, (∀ x ∈ S, 0 < x) ∧ 2 ≤ #S ∧ ∑ x ∈ S, x = n ∧
    ∃ h : S.Nonempty, S.max' h ∣ n

/-- A368207, the Bacher numbers: the number of quadruples `(w, x, y, z)` of
nonnegative integers with `n = w * x + y * z` and `max w x < min y z`. -/
noncomputable def bacher (n : ℕ) : ℕ :=
  {t : ℕ × ℕ × ℕ × ℕ | t.1 * t.2.1 + t.2.2.1 * t.2.2.2 = n ∧
    max t.1 t.2.1 < min t.2.2.1 t.2.2.2}.ncard

/-- A368457: `2 * (Bacher(n) - sigma(n)) + n + 1`, computed in `ℤ`. -/
noncomputable def A368457 (n : ℕ) : ℤ :=
  2 * ((bacher n : ℤ) - (ArithmeticFunction.sigma 1 n : ℤ)) + n + 1

/-- Membership in A368459: positive integers `k` with
`2 * (Bacher(k) - sigma(k)) + k + 1 < 0`. -/
def InA368459 (k : ℕ) : Prop :=
  0 < k ∧ A368457 k < 0

/-! ## A computable form of the Bacher numbers -/

/-- The triples `(w, x, y)` with `w, x ≤ r` that extend (uniquely) to a Bacher
representation `n = w * x + y * z`, `max w x < min y z`, via
`z = (n - w * x) / y`.  Used only to evaluate `bacher`. -/
def bacherTriples (n r : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (range (r + 1) ×ˢ range (r + 1) ×ˢ range (n + 1)).filter
    (fun u => u.1 * u.2.1 ≤ n ∧ 0 < u.2.2 ∧ u.2.2 ∣ n - u.1 * u.2.1 ∧
      max u.1 u.2.1 < min u.2.2 ((n - u.1 * u.2.1) / u.2.2))

/-- The Bacher number equals the size of `bacherTriples n r` whenever
`n < (r + 1)^2`: in a representation, `w, x < min y z`, so `w * w` and `x * x`
are below `y * z ≤ n`; and `z` is recovered from `(w, x, y)`. -/
theorem bacher_eq_card (n r : ℕ) (hr : n < (r + 1) * (r + 1)) :
    bacher n = #(bacherTriples n r) := by
  let f : ℕ × ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun t => (t.1, t.2.1, t.2.2.1)
  have hinj : Set.InjOn f {t : ℕ × ℕ × ℕ × ℕ | t.1 * t.2.1 + t.2.2.1 * t.2.2.2 = n ∧
      max t.1 t.2.1 < min t.2.2.1 t.2.2.2} := by
    rintro ⟨w, x, y, z⟩ ⟨h1, h2⟩ ⟨w', x', y', z'⟩ ⟨h1', h2'⟩ heq
    simp only [f, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    simp only [max_lt_iff, lt_min_iff] at h2 h1 h1'
    have hy : 0 < y := by omega
    have hyz : y * z = y * z' := by omega
    rw [Nat.eq_of_mul_eq_mul_left hy hyz]
  have himg : f '' {t : ℕ × ℕ × ℕ × ℕ | t.1 * t.2.1 + t.2.2.1 * t.2.2.2 = n ∧
      max t.1 t.2.1 < min t.2.2.1 t.2.2.2} = ↑(bacherTriples n r) := by
    ext ⟨w0, x0, y0⟩
    simp only [bacherTriples, Set.mem_image, Set.mem_ofPred_eq, Finset.coe_filter,
      Finset.mem_product, Finset.mem_range, max_lt_iff, lt_min_iff]
    constructor
    · rintro ⟨⟨w, x, y, z⟩, hmem, heq⟩
      simp only [f, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      dsimp only at hmem
      obtain ⟨h1, ⟨hwy, hxy⟩, ⟨hwz, hxz⟩⟩ := hmem
      have hz : 0 < z := by omega
      have hyz : y ≤ y * z := Nat.le_mul_of_pos_right y hz
      have hsub : n - w * x = y * z := by omega
      have hq : (n - w * x) / y = z := by
        rw [hsub, Nat.mul_div_cancel_left z (by omega)]
      have hww : w * w < (r + 1) * (r + 1) :=
        (Nat.mul_lt_mul'' hwy hwz).trans_le (show y * z ≤ (r + 1) * (r + 1) by omega)
      have hxx : x * x < (r + 1) * (r + 1) :=
        (Nat.mul_lt_mul'' hxy hxz).trans_le (show y * z ≤ (r + 1) * (r + 1) by omega)
      rw [hq]
      refine ⟨⟨Nat.mul_self_lt_mul_self_iff.mp hww, Nat.mul_self_lt_mul_self_iff.mp hxx,
        by omega⟩, by omega, by omega, ⟨z, hsub⟩, ⟨hwy, hxy⟩, ⟨hwz, hxz⟩⟩
    · rintro ⟨-, hwx, hy, hdvd, ⟨hwy, hxy⟩, ⟨hwz, hxz⟩⟩
      refine ⟨⟨w0, x0, y0, (n - w0 * x0) / y0⟩, ⟨?_, ⟨hwy, hxy⟩, ⟨hwz, hxz⟩⟩, rfl⟩
      have hmul : y0 * ((n - w0 * x0) / y0) = n - w0 * x0 := Nat.mul_div_cancel' hdvd
      dsimp only
      omega
  unfold bacher
  rw [← hinj.ncard_image, himg, Set.ncard_coe_finset]

/-! ## Examples from the OEIS data -/

-- A368207 (Bacher numbers) DATA: 1, 2, 2, 5, 3, 8, 4, 8, 9, 9, 6, 18, ...
example : bacher 1 = 1 := by rw [bacher_eq_card 1 1 (by norm_num)]; decide
example : bacher 2 = 2 := by rw [bacher_eq_card 2 1 (by norm_num)]; decide
example : bacher 4 = 5 := by rw [bacher_eq_card 4 2 (by norm_num)]; decide
example : bacher 6 = 8 := by rw [bacher_eq_card 6 2 (by norm_num)]; decide
example : bacher 12 = 18 := by rw [bacher_eq_card 12 3 (by norm_num)]; decide +kernel
example : bacher 16 = 19 := by rw [bacher_eq_card 16 4 (by norm_num)]; decide +kernel

-- A368457 DATA: 2, 1, 0, 1, 0, -1, ...; A368459 starts 6, 8, 10, ...
example : A368457 1 = 2 := by
  rw [A368457, bacher_eq_card 1 1 (by norm_num), ArithmeticFunction.sigma_apply]; decide
example : A368457 6 = -1 := by
  rw [A368457, bacher_eq_card 6 2 (by norm_num), ArithmeticFunction.sigma_apply]; decide
example : InA368459 6 := by
  refine ⟨by norm_num, ?_⟩
  rw [A368457, bacher_eq_card 6 2 (by norm_num), ArithmeticFunction.sigma_apply]; decide
example : ¬ InA368459 5 := by
  rintro ⟨-, h⟩
  rw [A368457, bacher_eq_card 5 2 (by norm_num), ArithmeticFunction.sigma_apply] at h
  revert h; decide

/-- `{1, 2, 3}` is quanimous: `{3} ∪ {1, 2}` (the first term of A371737). -/
theorem quanimous_one_two_three : Quanimous {1, 2, 3} := by
  refine ⟨⟨{{3}, {1, 2}}, ?_, ?_, ?_⟩, ?_, 3, ?_⟩
  · exact (Finset.supIndep_pair (by decide)).mpr (by decide)
  · decide
  · decide
  · decide
  · decide

/-! ## The block-sum bound -/

/-- If `S` splits into `k ≥ 2` blocks of common sum `s`, then `sum S = k * s` and
every element of `S` is at most `s`. -/
theorem exists_mul_of_quanimous {S : Finset ℕ} (hQ : Quanimous S) :
    ∃ k s : ℕ, 2 ≤ k ∧ ∑ x ∈ S, x = k * s ∧ S ⊆ range (s + 1) := by
  obtain ⟨P, hk, s, hs⟩ := hQ
  refine ⟨#P.parts, s, hk, ?_, ?_⟩
  · calc ∑ x ∈ S, x = ∑ B ∈ P.parts, ∑ x ∈ B, x := by
          conv_lhs => rw [← P.biUnion_parts]
          rw [Finset.sum_biUnion P.supIndep.pairwiseDisjoint]
          rfl
      _ = ∑ _B ∈ P.parts, s := Finset.sum_congr rfl hs
      _ = #P.parts * s := by rw [Finset.sum_const, smul_eq_mul]
  · intro x hx
    obtain ⟨B, hB, hxB⟩ := P.exists_mem hx
    have hle : x ≤ ∑ y ∈ B, y :=
      Finset.single_le_sum (f := fun y => y) (fun _ _ => Nat.zero_le _) hxB
    rw [hs B hB] at hle
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle)

/-- A quanimous set with sum `n = k * s`, `k ≥ 2`, satisfies `2 * n ≤ s * (s + 1)`. -/
theorem two_mul_sum_le_of_quanimous {S : Finset ℕ} (hQ : Quanimous S) :
    ∃ k s : ℕ, 2 ≤ k ∧ ∑ x ∈ S, x = k * s ∧ 2 * ∑ x ∈ S, x ≤ s * (s + 1) := by
  obtain ⟨k, s, hk, hsum, hsub⟩ := exists_mul_of_quanimous hQ
  refine ⟨k, s, hk, hsum, ?_⟩
  have hle : ∑ x ∈ S, x ≤ ∑ x ∈ range (s + 1), x :=
    Finset.sum_le_sum_of_subset hsub
  have hgauss : (∑ x ∈ range (s + 1), x) * 2 = (s + 1) * s :=
    Finset.sum_range_id_mul_two (s + 1)
  nlinarith

/-- `a(n) = 0` whenever no factorisation `n = k * s` with `k ≥ 2` satisfies
`2 * n ≤ s * (s + 1)` (stated with bounded quantifiers so it can be decided). -/
theorem A371737_eq_zero_of (n : ℕ) (hn : 0 < n)
    (h : ∀ k ∈ Icc 2 n, ∀ s ∈ range (n + 1), k * s = n → s * (s + 1) < 2 * n) :
    A371737 n = 0 := by
  have hempty : {S : Finset ℕ | (∀ x ∈ S, 0 < x) ∧ ∑ x ∈ S, x = n ∧ Quanimous S} = ∅ := by
    ext S
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨-, hsum, hQ⟩
    obtain ⟨k, s, hk, hks, hle⟩ := two_mul_sum_le_of_quanimous hQ
    rw [hsum] at hks hle
    have hs : 0 < s := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have hkn : k ≤ n := hks ▸ Nat.le_mul_of_pos_right k hs
    have hsn : s ≤ n := hks ▸ Nat.le_mul_of_pos_left s (by omega)
    have hlt := h k (Finset.mem_Icc.mpr ⟨hk, hkn⟩) s (Finset.mem_range.mpr (by omega)) hks.symm
    omega
  rw [A371737, hempty, Set.ncard_empty]

-- A371737 DATA: a(1) = ... = a(5) = 0, a(7) = 0, a(9) = 0.
example : A371737 1 = 0 := A371737_eq_zero_of 1 (by norm_num) (by decide)
example : A371737 5 = 0 := A371737_eq_zero_of 5 (by norm_num) (by decide)
example : A371737 7 = 0 := A371737_eq_zero_of 7 (by norm_num) (by decide)
example : A371737 9 = 0 := A371737_eq_zero_of 9 (by norm_num) (by decide)

/-- `a(n) > 0` as soon as one quanimous strict partition of `n` is exhibited
(the set of strict partitions of `n` is finite, being inside the powerset of
`{0, ..., n}`). -/
theorem A371737_pos_of (n : ℕ) (S : Finset ℕ) (hpos : ∀ x ∈ S, 0 < x)
    (hsum : ∑ x ∈ S, x = n) (hQ : Quanimous S) : 0 < A371737 n := by
  have hfin : {S : Finset ℕ | (∀ x ∈ S, 0 < x) ∧ ∑ x ∈ S, x = n ∧ Quanimous S}.Finite := by
    refine (Finset.finite_toSet ((range (n + 1)).powerset)).subset ?_
    rintro T ⟨-, hTsum, -⟩
    rw [Finset.mem_coe, Finset.mem_powerset]
    intro x hx
    have hle : x ≤ ∑ y ∈ T, y :=
      Finset.single_le_sum (f := fun y => y) (fun _ _ => Nat.zero_le _) hx
    exact Finset.mem_range.mpr (by omega)
  exact (Set.ncard_pos hfin).mpr ⟨S, hpos, hsum, hQ⟩

-- A371737 DATA: a(6) = 1 > 0, witnessed by the strict partition (3, 2, 1).
example : 0 < A371737 6 :=
  A371737_pos_of 6 {1, 2, 3} (by decide) (by decide) quanimous_one_two_three

-- A327782 example: 6 = 1 + 2 + 3 with largest part 3 dividing 6, so 6 is
-- not a term (A327782 starts 1, 2, 3, 4, 5, 7, ...).
example : ¬ InA327782 6 := by
  rintro ⟨-, h⟩
  exact h ⟨{1, 2, 3}, by decide, by decide, by decide, by decide, by decide⟩

/-! ## The counterexample `n = 77` -/

/-- `a(77) = 0`: no set of distinct positive integers with sum 77 splits into two
or more blocks with equal sums. -/
theorem A371737_seventyseven : A371737 77 = 0 :=
  A371737_eq_zero_of 77 (by norm_num) (by decide +kernel)

/-- The finite evaluation behind `Bacher(77) = 54`. -/
theorem card_bacherTriples_seventyseven : #(bacherTriples 77 8) = 54 := by
  decide +kernel

/-- `Bacher(77) = 54` (A368207). -/
theorem bacher_seventyseven : bacher 77 = 54 := by
  rw [bacher_eq_card 77 8 (by norm_num), card_bacherTriples_seventyseven]

/-- `sigma(77) = 1 + 7 + 11 + 77 = 96`. -/
theorem sigma_seventyseven : ArithmeticFunction.sigma 1 77 = 96 := by
  rw [ArithmeticFunction.sigma_apply]
  decide

/-- `A368457(77) = 2 * (54 - 96) + 77 + 1 = -6`. -/
theorem A368457_seventyseven : A368457 77 = -6 := by
  rw [A368457, bacher_seventyseven, sigma_seventyseven]
  norm_num

/-- 77 is a term of A368459. -/
theorem inA368459_seventyseven : InA368459 77 :=
  ⟨by norm_num, by rw [A368457_seventyseven]; norm_num⟩

/-- 77 is a term of A327782 (as its DATA line lists), so part (1) of the
conjecture is consistent at the counterexample: if `77` were a sum of at least
two distinct positive parts with largest part `L ∣ 77`, then `L ∈ {1, 7, 11}`
gives `2 * 77 > L * (L + 1)`, and `L = 77` leaves no room for a second part. -/
theorem inA327782_seventyseven : InA327782 77 := by
  refine ⟨by norm_num, ?_⟩
  rintro ⟨S, hpos, hcard, hsum, hne, hdvd⟩
  obtain ⟨L, hLdef⟩ : ∃ L, L = S.max' hne := ⟨_, rfl⟩
  rw [← hLdef] at hdvd
  have hLmem : L ∈ S := hLdef ▸ S.max'_mem hne
  have hsub : S ⊆ range (L + 1) := fun x hx =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (hLdef ▸ S.le_max' x hx))
  have hle : ∑ x ∈ S, x ≤ ∑ x ∈ range (L + 1), x := Finset.sum_le_sum_of_subset hsub
  have hgauss : (∑ x ∈ range (L + 1), x) * 2 = (L + 1) * L :=
    Finset.sum_range_id_mul_two (L + 1)
  obtain ⟨y, hyS, hyL⟩ := Finset.exists_mem_ne hcard L
  have hpair : L + y ≤ ∑ x ∈ S, x := by
    have hsub2 : ({L, y} : Finset ℕ) ⊆ S :=
      Finset.insert_subset hLmem (Finset.singleton_subset_iff.mpr hyS)
    have hpair' := Finset.sum_le_sum_of_subset (f := fun x => x) hsub2
    rwa [Finset.sum_pair (Ne.symm hyL)] at hpair'
  have hy : 0 < y := hpos y hyS
  have hL77 : L ∈ ({1, 7, 11, 77} : Finset ℕ) := by
    have hmem : L ∈ Nat.divisors 77 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hdiv : Nat.divisors 77 = {1, 7, 11, 77} := by decide
    rwa [hdiv] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hL77
  rcases hL77 with rfl | rfl | rfl | rfl <;> omega

/-! ## The conjecture and its refutation -/

/-- The conjecture of OEIS A371737 (Gus Wiseman, Apr 14 2024): its zero
positions are A327782 and its positive positions are A368459. Both parts
are stated for `n ≥ 1`; the literal first part fails at the offset `n = 0`,
since `a(0) = 0` but `0 ∉ A327782`. -/
def Conjecture : Prop :=
  (∀ n : ℕ, 0 < n → (A371737 n = 0 ↔ InA327782 n)) ∧
  (∀ n : ℕ, 0 < n → (0 < A371737 n ↔ InA368459 n))

/-- **The conjecture is false.**  Counterexample `n = 77` against part (2):
77 is a term of A368459 (`Bacher(77) = 54`, `sigma(77) = 96`,
`A368457(77) = -6 < 0`), yet `a(77) = 0`.  Part (1) is not contradicted. -/
theorem conjecture_false : ¬ Conjecture := by
  rintro ⟨-, h2⟩
  have hpos : 0 < A371737 77 := (h2 77 (by norm_num)).mpr inA368459_seventyseven
  rw [A371737_seventyseven] at hpos
  exact lt_irrefl 0 hpos

end Candidates.A371737Refutation
