import Mathlib

/-!
# A114976: subsets of `{1,…,n}` whose arithmetic mean is an integer dividing `n`

`a n` counts the nonempty subsets `S ⊆ {1,…,n}` whose arithmetic mean is an
integer that also divides `n` (OEIS A114976; ground truth
`1, 2, 2, 5, 2, 14, 2, 30, 11, 80, 2, 280, …`).  The mean condition is stated
multiplicatively (`S.sum id = m * S.card` with `m ∣ n`), avoiding `Nat`
division throughout.

Two observations recorded (unattributed) in the OEIS entry are proved here:

* **prime pattern** (`a_eq_two_iff_prime`): `a n = 2` iff `n` is prime;
* **parity** (`odd_a_iff_isSquare`): for `n ≠ 0`, `a n` is odd iff `n` is a
  perfect square.

Both rest on the *mean-toggle involution*: for a fixed integer mean `m`,
removing or inserting the element `m` itself preserves the mean, so away from
the singleton `{m}` it pairs up the subsets of `{1,…,n}` with mean `m`, and
their count is odd (`odd_card_meanSubsets`).  Summing over the divisors `m`
of `n` gives the congruence `a n ≡ τ n [MOD 2]` (`a_modEq_card_divisors`) —
sharpening the OEIS remark that the parity pattern "might suggest … a deeper
relationship with A000005" — and `τ n` is odd exactly on the squares
(`odd_card_divisors_iff_isSquare`, proved here from the factorization
formula, since Mathlib does not carry it).

Novelty status (literature sweep, 2026-07-29): no proof of the parity
observation or of the τ-parity congruence was found in the literature or in
the OEIS entries (searched: A114976/A051293/A063776/A000016 entries and
links; the Ramanathan 1944 / Barnes 1959 subset-sum-count circle;
arXiv:2605.22763, which settles the A051293 asymptotic conjecture but not
parity).  The OEIS entry frames both as open observations, so the involution
proofs in this file are, to our knowledge, the first recorded proofs.  The
prime-pattern iff is folklore.  Claim discipline: "first recorded proof of an
OEIS observation" — not claimed as a novel research result.
-/

set_option autoImplicit false

open Finset

namespace A114976

/-- `IsMeanDiv n S`: the sum of `S` equals `m * S.card` for some divisor `m`
of `n`.  For nonempty `S` this says exactly "the arithmetic mean of `S` is an
integer that divides `n`", stated multiplicatively to avoid `Nat` division. -/
def IsMeanDiv (n : ℕ) (S : Finset ℕ) : Prop :=
  ∃ m, S.sum id = m * S.card ∧ m ∣ n

private lemma isMeanDiv_iff_bounded (n : ℕ) (S : Finset ℕ) :
    (∃ m ∈ Finset.range (n + S.sum id + 1), S.sum id = m * S.card ∧ m ∣ n) ↔
      IsMeanDiv n S := by
  constructor
  · rintro ⟨m, -, hm⟩
    exact ⟨m, hm⟩
  · rintro ⟨m, hsum, hdvd⟩
    rcases Nat.eq_zero_or_pos S.card with hc | hc
    · refine ⟨n, Finset.mem_range.mpr (by omega), ?_, dvd_rfl⟩
      rw [hc, Nat.mul_zero]
      rw [hc, Nat.mul_zero] at hsum
      exact hsum
    · have hle : m ≤ S.sum id := by
        rw [hsum]
        exact Nat.le_mul_of_pos_right m hc
      exact ⟨m, Finset.mem_range.mpr (by omega), hsum, hdvd⟩

instance (n : ℕ) (S : Finset ℕ) : Decidable (IsMeanDiv n S) :=
  decidable_of_iff _ (isMeanDiv_iff_bounded n S)

/-- The nonempty subsets of `{1,…,n}` whose arithmetic mean is an integer
dividing `n` — the objects counted by OEIS A114976. -/
def meanDivSubsets (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 n).powerset.filter fun S => S.Nonempty ∧ IsMeanDiv n S

/-- OEIS A114976: the number of subsets of `{1,…,n}` with an arithmetic mean
that is an integer and also a divisor of `n`. -/
def a (n : ℕ) : ℕ := (meanDivSubsets n).card

/-- Membership in `meanDivSubsets n`, unfolded to the defining conditions. -/
lemma mem_meanDivSubsets {n : ℕ} {S : Finset ℕ} :
    S ∈ meanDivSubsets n ↔
      S ⊆ Finset.Icc 1 n ∧ S.Nonempty ∧ ∃ m, S.sum id = m * S.card ∧ m ∣ n := by
  constructor
  · intro h
    have h' := Finset.mem_filter.mp h
    exact ⟨Finset.mem_powerset.mp h'.1, h'.2.1, h'.2.2⟩
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr h.1, h.2.1, h.2.2⟩

-- Ground checks for `a` against `oeis show A114976`:
-- 1, 2, 2, 5, 2, 14, 2, 30, 11, 80, 2, 280, …  (offset 1; `a 0 = 0` degenerate).
example : a 0 = 0 := by decide
example : a 1 = 1 := by decide
example : a 2 = 2 := by decide
example : a 3 = 2 := by decide
example : a 4 = 5 := by decide
example : a 5 = 2 := by decide
example : a 6 = 14 := by decide
example : a 7 = 2 := by decide
example : a 8 = 30 := by decide
set_option maxRecDepth 4000 in
example : a 9 = 11 := by decide
set_option maxRecDepth 8000 in
example : a 10 = 80 := by decide

-- Ground check for `meanDivSubsets`: the five qualifying subsets at `n = 4`.
example : meanDivSubsets 4 = {{1}, {2}, {4}, {1, 3}, {1, 2, 3}} := by decide

/-- The subsets of `{1,…,n}` with arithmetic mean exactly `m`, stated
multiplicatively: nonempty `S ⊆ {1,…,n}` with `S.sum id = m * S.card`. -/
def meanSubsets (n m : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 n).powerset.filter fun S => S.Nonempty ∧ S.sum id = m * S.card

/-- Membership in `meanSubsets n m`, unfolded to the defining conditions. -/
lemma mem_meanSubsets {n m : ℕ} {S : Finset ℕ} :
    S ∈ meanSubsets n m ↔
      S ⊆ Finset.Icc 1 n ∧ S.Nonempty ∧ S.sum id = m * S.card := by
  simp only [meanSubsets, Finset.mem_filter, Finset.mem_powerset]

-- Ground checks for `meanSubsets`: at `n = 4`, mean 2 is attained by
-- `{2}, {1,3}, {1,2,3}`; mean 1 only by `{1}`; mean 3 by `{3}, {2,4}, {2,3,4}`.
example : meanSubsets 4 2 = {{2}, {1, 3}, {1, 2, 3}} := by decide
example : meanSubsets 4 1 = {{1}} := by decide
example : meanSubsets 4 3 = {{3}, {2, 4}, {2, 3, 4}} := by decide

/-- The singleton `{m}` has mean `m`. -/
lemma singleton_mem_meanSubsets {n m : ℕ} (hm : m ∈ Finset.Icc 1 n) :
    {m} ∈ meanSubsets n m := by
  rw [mem_meanSubsets]
  refine ⟨Finset.singleton_subset_iff.mpr hm, Finset.singleton_nonempty m, ?_⟩
  simp

/-- **Mean-toggle involution.**  Toggling membership of the element `m` in a
subset of mean `m` preserves the mean, and away from the singleton `{m}` it
pairs up `meanSubsets n m`; hence the count of mean-`m` subsets is odd. -/
lemma odd_card_meanSubsets {n m : ℕ} (hm : m ∈ Finset.Icc 1 n) :
    Odd (meanSubsets n m).card := by
  classical
  have hsplit :
      ((meanSubsets n m).filter fun S => m ∈ S).card +
        ((meanSubsets n m).filter fun S => m ∉ S).card = (meanSubsets n m).card :=
    Finset.card_filter_add_card_filter_not (fun S => m ∈ S)
  have hmA : ({m} : Finset ℕ) ∈ (meanSubsets n m).filter fun S => m ∈ S :=
    Finset.mem_filter.mpr ⟨singleton_mem_meanSubsets hm, Finset.mem_singleton_self m⟩
  have herase :
      (((meanSubsets n m).filter fun S => m ∈ S).erase {m}).card =
        ((meanSubsets n m).filter fun S => m ∉ S).card := by
    refine Finset.card_bij' (fun S _ => S.erase m) (fun T _ => insert m T) ?_ ?_ ?_ ?_
    · -- erasing `m` lands in the `m ∉ ·` class
      intro S hS
      obtain ⟨hSne, hSA⟩ := Finset.mem_erase.mp hS
      obtain ⟨hSmean, hmS⟩ := Finset.mem_filter.mp hSA
      obtain ⟨hsub, hne, hsum⟩ := mem_meanSubsets.mp hSmean
      refine Finset.mem_filter.mpr
        ⟨mem_meanSubsets.mpr ⟨?_, ?_, ?_⟩, Finset.notMem_erase m S⟩
      · exact (Finset.erase_subset m S).trans hsub
      · rw [Finset.nonempty_iff_ne_empty]
        intro hempty
        rcases (Finset.erase_eq_empty_iff S m).mp hempty with h0 | h1
        · exact Finset.nonempty_iff_ne_empty.mp hne h0
        · exact hSne h1
      · have hcard : S.card = (S.erase m).card + 1 := (Finset.card_erase_add_one hmS).symm
        have hkey : (S.erase m).sum id + m = S.sum id := by
          have hout := Finset.sum_erase_add S id hmS
          simpa using hout
        have hcancel : (S.erase m).sum id + m = m * (S.erase m).card + m := by
          rw [hkey, hsum, hcard, Nat.mul_succ]
        exact Nat.add_right_cancel hcancel
    · -- inserting `m` lands in the `m ∈ ·` class, away from `{m}`
      intro T hT
      obtain ⟨hTmean, hmT⟩ := Finset.mem_filter.mp hT
      obtain ⟨hsub, hne, hsum⟩ := mem_meanSubsets.mp hTmean
      refine Finset.mem_erase.mpr ⟨?_, ?_⟩
      · obtain ⟨x, hx⟩ := hne
        intro heq
        have hxm : x ∈ ({m} : Finset ℕ) := heq ▸ Finset.mem_insert_of_mem hx
        exact hmT (Finset.mem_singleton.mp hxm ▸ hx)
      · refine Finset.mem_filter.mpr
          ⟨mem_meanSubsets.mpr ⟨?_, Finset.insert_nonempty m T, ?_⟩,
            Finset.mem_insert_self m T⟩
        · exact Finset.insert_subset_iff.mpr ⟨hm, hsub⟩
        · rw [Finset.sum_insert hmT, Finset.card_insert_of_notMem hmT, hsum, Nat.mul_succ,
            id_eq, Nat.add_comm]
    · -- left inverse
      intro S hS
      obtain ⟨-, hSA⟩ := Finset.mem_erase.mp hS
      exact Finset.insert_erase (Finset.mem_filter.mp hSA).2
    · -- right inverse
      intro T hT
      exact Finset.erase_insert (Finset.mem_filter.mp hT).2
  have hAcard :
      ((meanSubsets n m).filter fun S => m ∈ S).card =
        ((meanSubsets n m).filter fun S => m ∉ S).card + 1 := by
    rw [← Finset.card_erase_add_one hmA, herase]
  exact ⟨((meanSubsets n m).filter fun S => m ∉ S).card, by omega⟩

-- Joint satisfiability of `odd_card_meanSubsets` at `n = 4`, `m = 2`:
-- the hypothesis holds and the count is the odd number 3.
example : (2 : ℕ) ∈ Finset.Icc 1 4 ∧ (meanSubsets 4 2).card = 3 := by decide

/-- A114976 partitions by the (unique) mean of each counted subset: the
counted family is the disjoint union over divisors `m` of `n` of the
mean-`m` subsets. -/
lemma meanDivSubsets_eq_biUnion (n : ℕ) :
    meanDivSubsets n = n.divisors.biUnion (meanSubsets n) := by
  ext S
  rw [Finset.mem_biUnion, mem_meanDivSubsets]
  constructor
  · rintro ⟨hsub, hne, m, hsum, hdvd⟩
    have hn : n ≠ 0 := by
      obtain ⟨x, hx⟩ := hne
      have hx' := Finset.mem_Icc.mp (hsub hx)
      omega
    exact ⟨m, Nat.mem_divisors.mpr ⟨hdvd, hn⟩, mem_meanSubsets.mpr ⟨hsub, hne, hsum⟩⟩
  · rintro ⟨m, hmem, hS⟩
    obtain ⟨hsub, hne, hsum⟩ := mem_meanSubsets.mp hS
    exact ⟨hsub, hne, m, hsum, (Nat.mem_divisors.mp hmem).1⟩

/-- `a n` is the sum over divisors `m` of `n` of the number of mean-`m`
subsets of `{1,…,n}`. -/
lemma a_eq_sum_divisors (n : ℕ) :
    a n = ∑ m ∈ n.divisors, (meanSubsets n m).card := by
  rw [a, meanDivSubsets_eq_biUnion]
  refine Finset.card_biUnion ?_
  intro x hx y hy hxy
  show Disjoint (meanSubsets n x) (meanSubsets n y)
  rw [Finset.disjoint_left]
  intro S hSx hSy
  obtain ⟨-, hne, hx'⟩ := mem_meanSubsets.mp hSx
  obtain ⟨-, -, hy'⟩ := mem_meanSubsets.mp hSy
  have hc : 0 < S.card := Finset.card_pos.mpr hne
  exact hxy (Nat.eq_of_mul_eq_mul_right hc (hx'.symm.trans hy'))

/-- **A114976 ≡ τ (mod 2).**  Each divisor `m` of `n` contributes an odd
number of mean-`m` subsets, so `a n` has the parity of the number of
divisors of `n`.  This is the "deeper relationship with A000005" suggested
in the OEIS entry. -/
theorem a_modEq_card_divisors (n : ℕ) : a n ≡ n.divisors.card [MOD 2] := by
  have hodd : ∀ m ∈ n.divisors, (meanSubsets n m).card % 2 = 1 := by
    intro m hm
    obtain ⟨hdvd, hn⟩ := Nat.mem_divisors.mp hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hn (Nat.eq_zero_of_zero_dvd hdvd)
    have hmn : m ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
    exact Nat.odd_iff.mp (odd_card_meanSubsets
      (Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hm0, hmn⟩))
  show a n % 2 = n.divisors.card % 2
  calc a n % 2
      = (∑ m ∈ n.divisors, (meanSubsets n m).card) % 2 := by rw [a_eq_sum_divisors]
    _ = (∑ m ∈ n.divisors, (meanSubsets n m).card % 2) % 2 := Finset.sum_nat_mod _ 2 _
    _ = (∑ _m ∈ n.divisors, 1) % 2 := by rw [Finset.sum_congr rfl hodd]
    _ = n.divisors.card % 2 := by rw [← Finset.card_eq_sum_ones]

-- Satisfiability check for `a_modEq_card_divisors` at `n = 6`:
-- `a 6 = 14` and `τ 6 = 4` are both even.
example : a 6 % 2 = (Nat.divisors 6).card % 2 := by decide

private lemma odd_prod_iff {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    Odd (∏ i ∈ s, f i) ↔ ∀ i ∈ s, Odd (f i) := by
  constructor
  · intro h i hi
    rw [Nat.odd_iff] at h ⊢
    by_contra hodd
    have h2 : (2 : ℕ) ∣ f i := by omega
    have hdvd : (2 : ℕ) ∣ ∏ j ∈ s, f j := h2.trans (Finset.dvd_prod_of_mem f hi)
    omega
  · intro h
    exact Finset.prod_induction f Odd (fun x y hx hy => hx.mul hy) odd_one h

private lemma isSquare_iff_even_factorization {n : ℕ} (hn : n ≠ 0) :
    IsSquare n ↔ ∀ p, Even (n.factorization p) := by
  constructor
  · rintro ⟨r, rfl⟩
    have hr : r ≠ 0 := fun h => hn (by rw [h])
    intro p
    rw [Nat.factorization_mul hr hr, Finsupp.add_apply]
    exact ⟨r.factorization p, rfl⟩
  · intro h
    refine ⟨n.factorization.prod fun p k => p ^ (k / 2), ?_⟩
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    simp only [Finsupp.prod]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_add]
    congr 1
    have hp2 := Nat.even_iff.mp (h p)
    omega

/-- τ-parity: a positive natural number has an odd number of divisors iff it
is a perfect square.  Not in Mathlib; proved here via the factorization
formula `Nat.card_divisors`. -/
theorem odd_card_divisors_iff_isSquare {n : ℕ} (hn : n ≠ 0) :
    Odd n.divisors.card ↔ IsSquare n := by
  rw [Nat.card_divisors hn, isSquare_iff_even_factorization hn, odd_prod_iff]
  constructor
  · intro h p
    by_cases hp : p ∈ n.primeFactors
    · have hodd := h p hp
      rw [Nat.odd_add_one, Nat.not_odd_iff_even] at hodd
      exact hodd
    · rw [← Nat.support_factorization] at hp
      rw [Finsupp.notMem_support_iff.mp hp]
      exact ⟨0, rfl⟩
  · intro h p _
    rw [Nat.odd_add_one, Nat.not_odd_iff_even]
    exact h p

-- Satisfiability check for `odd_card_divisors_iff_isSquare` at `n = 9`:
-- `9 ≠ 0`, `τ 9 = 3` is odd, and `9 = 3 * 3`.
example : Odd (Nat.divisors 9).card := ⟨1, by decide⟩
example : IsSquare (9 : ℕ) := ⟨3, by decide⟩

/-- **A114976 parity ↔ square** (OEIS A114976 conjectured observation,
proved): for `n ≠ 0`, the number of subsets of `{1,…,n}` whose mean is an
integer dividing `n` is odd iff `n` is a perfect square. -/
theorem odd_a_iff_isSquare {n : ℕ} (hn : n ≠ 0) : Odd (a n) ↔ IsSquare n := by
  have hmod : a n % 2 = n.divisors.card % 2 := a_modEq_card_divisors n
  rw [Nat.odd_iff, hmod, ← Nat.odd_iff, odd_card_divisors_iff_isSquare hn]

-- Joint satisfiability of `odd_a_iff_isSquare`, positive instance `n = 4`:
-- `4 ≠ 0`, `a 4 = 5` is odd, and `4` is a square.
example : Odd (a 4) := ⟨2, by decide⟩
example : IsSquare (4 : ℕ) := ⟨2, by decide⟩
-- Negative instance `n = 6`: `a 6 = 14` is even, and `6` is not a square.
example : ¬Odd (a 6) := by decide
example : ¬IsSquare (6 : ℕ) := by norm_num

/-- Every singleton divisor subset `{d}`, `d ∣ n`, is counted by A114976. -/
lemma singleton_mem_meanDivSubsets {n d : ℕ} (hn : n ≠ 0) (hd : d ∣ n) :
    {d} ∈ meanDivSubsets n := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hn (Nat.eq_zero_of_zero_dvd hd)
  have hdn : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
  rw [mem_meanDivSubsets]
  refine ⟨Finset.singleton_subset_iff.mpr
      (Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hd0, hdn⟩),
    Finset.singleton_nonempty d, d, ?_, hd⟩
  simp

/-- For prime `n`, exactly two subsets qualify: `{1}` and `{n}`.  A mean-1
subset of `{1,…,n}` must be `{1}` and a mean-`n` subset must be `{n}`. -/
theorem meanDivSubsets_prime {n : ℕ} (hp : n.Prime) :
    meanDivSubsets n = {{1}, {n}} := by
  ext S
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hS
    obtain ⟨hsub, hne, m, hsum, hdvd⟩ := mem_meanDivSubsets.mp hS
    have hbounds : ∀ x ∈ S, 1 ≤ x ∧ x ≤ n := fun x hx => Finset.mem_Icc.mp (hsub hx)
    rcases hp.eq_one_or_self_of_dvd m hdvd with rfl | hmn
    · -- mean 1: every element is 1, so `S = {1}`
      left
      rw [Finset.eq_singleton_iff_nonempty_unique_mem]
      refine ⟨hne, fun x hx => ?_⟩
      by_contra hx1
      have h1x : 1 < x := lt_of_le_of_ne (hbounds x hx).1 (Ne.symm hx1)
      have hlt : ∑ _i ∈ S, (1 : ℕ) < S.sum id :=
        Finset.sum_lt_sum (fun i hi => (hbounds i hi).1) ⟨x, hx, h1x⟩
      rw [← Finset.card_eq_sum_ones, hsum, one_mul] at hlt
      exact lt_irrefl _ hlt
    · -- mean n: every element is n, so `S = {n}`
      right
      rw [Finset.eq_singleton_iff_nonempty_unique_mem]
      refine ⟨hne, fun x hx => ?_⟩
      by_contra hxn
      have hxlt : x < n := lt_of_le_of_ne (hbounds x hx).2 hxn
      have hlt : S.sum id < ∑ _i ∈ S, n :=
        Finset.sum_lt_sum (fun i hi => (hbounds i hi).2) ⟨x, hx, hxlt⟩
      rw [Finset.sum_const, smul_eq_mul, hsum, hmn, Nat.mul_comm] at hlt
      exact lt_irrefl _ hlt
  · rintro (rfl | rfl)
    · exact singleton_mem_meanDivSubsets hp.pos.ne' (one_dvd n)
    · exact singleton_mem_meanDivSubsets hp.pos.ne' dvd_rfl

-- Ground check for `meanDivSubsets_prime` at the prime `n = 3`.
example : meanDivSubsets 3 = {{1}, {3}} := by decide

/-- For prime `n`, `a n = 2` — the same value as `τ n`. -/
theorem a_of_prime {n : ℕ} (hp : n.Prime) : a n = 2 := by
  have hne : ({1} : Finset ℕ) ∉ ({{n}} : Finset (Finset ℕ)) := by
    rw [Finset.mem_singleton]
    intro h
    exact hp.one_lt.ne (Finset.singleton_inj.mp h)
  rw [a, meanDivSubsets_prime hp, Finset.card_insert_of_notMem hne, Finset.card_singleton]

/-- A composite `n` is counted at least thrice: `{1}`, `{d}`, `{n}` for a
proper divisor `d`. -/
lemma three_le_a_of_composite {n : ℕ} (h2 : 2 ≤ n) (hnp : ¬n.Prime) : 3 ≤ a n := by
  obtain ⟨d, hdvd, hd2, hdn⟩ := Nat.exists_dvd_of_not_prime2 h2 hnp
  have hn0 : n ≠ 0 := by omega
  have hsub : ({{1}, {d}, {n}} : Finset (Finset ℕ)) ⊆ meanDivSubsets n := by
    intro S hS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl | rfl
    · exact singleton_mem_meanDivSubsets hn0 (one_dvd n)
    · exact singleton_mem_meanDivSubsets hn0 hdvd
    · exact singleton_mem_meanDivSubsets hn0 dvd_rfl
  have hcard : ({{1}, {d}, {n}} : Finset (Finset ℕ)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.singleton_inj]
        omega),
      Finset.card_insert_of_notMem (by
        rw [Finset.mem_singleton, Finset.singleton_inj]
        omega),
      Finset.card_singleton]
  calc 3 = ({{1}, {d}, {n}} : Finset (Finset ℕ)).card := hcard.symm
    _ ≤ (meanDivSubsets n).card := Finset.card_le_card hsub
    _ = a n := rfl

-- Joint satisfiability of `three_le_a_of_composite` at `n = 4`:
-- `2 ≤ 4`, `4` is not prime, and `a 4 = 5` with `3 ≤ 5`.
example : ¬(4 : ℕ).Prime := by norm_num
example : 3 ≤ a 4 := by decide

/-- **A114976 prime pattern** (OEIS A114976 observation, proved):
`a n = 2` iff `n` is prime — just as for the number of divisors of `n`. -/
theorem a_eq_two_iff_prime (n : ℕ) : a n = 2 ↔ n.Prime := by
  constructor
  · intro h
    by_contra hnp
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · interval_cases n
      · exact absurd h (by decide)
      · exact absurd h (by decide)
    · have h3 := three_le_a_of_composite hge hnp
      omega
  · exact a_of_prime

-- Joint satisfiability of `a_eq_two_iff_prime`, positive instance `n = 5`:
example : a 5 = 2 ∧ (5 : ℕ).Prime := ⟨by decide, by norm_num⟩
-- Negative instance `n = 4`: `a 4 = 5 ≠ 2` and `4` is not prime.
example : a 4 ≠ 2 ∧ ¬(4 : ℕ).Prime := ⟨by decide, by norm_num⟩

end A114976
