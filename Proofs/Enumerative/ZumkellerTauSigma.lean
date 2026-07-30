import Mathlib
import Enumerative.IsZumkeller

/-!
# A083207: Ianakiev's `τ(d)·σ(d)` conjecture, and a `2`-adic Zumkeller engine

OEIS A083207 carries the unproved comment (Ivan N. Ianakiev, 2020-04-24, cf. A331668):

> Conjecture: If `d > 1`, `d ∣ k` and `tau(d)*sigma(d) = k`, then `k` is a Zumkeller number.

The conjecture is stated here as `isZumkeller_of_sigma_zero_mul_sigma_one`; its proof is
an **intended `sorry`** — the claim is open (see the "Status" section below).  What *is*
proved here is a complete `2`-adic reduction of Zumkeller-ness, and enough of it to settle
every qualifying `k` reachable by finite certificate:

* `binIndices`, `sum_binIndices` — binary expansion of a natural as a `Finset` sum;
* `blockSet`, `sum_blockSet`, `eq_blockSet_of_subset_divisors` — the **block
  decomposition**: for `m` odd, sets of divisors of `2 ^ a * m` correspond exactly to
  choices of index sets `S e ⊆ {0, …, a}`, one per divisor `e` of `m`, with sum
  `∑ e, (∑ i ∈ S e, 2 ^ i) * e`;
* `isZumkeller_two_pow_mul_iff` — the resulting **characterisation**: for `m` odd,
  `2 ^ a * m` is Zumkeller *iff* some weighting `c` of the divisors of `m` by coefficients
  `< 2 ^ (a+1)` satisfies `2 * ∑ e, c e * e = σ(2 ^ a) · σ(m)`.  The power of two
  contributes nothing beyond the coefficient range;
* `isZumkeller_two_pow_mul_of_sum_divisors_le` — the usable sufficient condition: `m` odd
  with `σ(m)` even and `σ(m) ≤ 2 ^ (a+1)` forces `2 ^ a * m` Zumkeller;
* `isZumkeller_two_pow_mul_prime`, `isZumkeller_two_pow_mul_three` — core families;
* `isZumkeller_of_six_dvd_of_not_nine_dvd` — Neder's criterion (`6 ∣ n`, `9 ∤ n`), via the
  core family and the coprime closure engine `IsZumkeller.mul_of_coprime`.

## Status of the conjecture

A sieve over `d ≤ 10⁷` finds exactly `103` values of `d > 1` with `d ∣ τ(d)σ(d)` (`77`
below `2·10⁶`; the `d`-column of A331668), all even.  For every one of them
`k = τ(d)σ(d)` is Zumkeller, is a practical number, and has even `σ`; a greedy descent
through the divisors of `k` produces the half-`σ` witness in each case.  Of the `77`
below `2·10⁶`, `74` are reached by
`isZumkeller_two_pow_mul_of_sum_divisors_le` composed with `IsZumkeller.mul_of_coprime`;
the three that are not are

  `d = 18 ↦ k = 234 = 2·3²·13`,  `d = 468 ↦ k = 22932 = 2²·3²·7²·13`,
  `d = 22932 ↦ k = 3921372 = 2²·3⁴·7²·13·19`.

`234` is the sharper obstruction: it has *no* nontrivial unitary factorization with a
Zumkeller factor at all, so no amount of coprime closure produces it.  (`22932` and
`3921372` do have such factorizations — e.g. `22932 = 468 · 49` with `468` Zumkeller — but
the Zumkeller factor is itself outside the `σ(m) ≤ 2 ^ (a+1)` family.)  All three are
nevertheless settled by explicit coefficient certificates through
`isZumkeller_two_pow_mul_of_coeff`; two of them are formalised at the end of this file,
and the third's certificate is recorded there as well (its `decide` on
`Nat.divisors 980343` is beyond kernel reach).

What stays open is the *general* statement, and the obstruction is sharper than the
lack of a classification of `{d : d ∣ τ(d)σ(d)}`.  **The conjecture implies a new
theorem about odd perfect numbers** (see the final section): every odd perfect `N`
satisfies the hypotheses at `d := N` (since `σ(N) = 2N` forces `N ∣ τ(N)σ(N)`), with
`k = τ(N)σ(N) = 4·(w·N)` where `τ(N) = 2w`, `w` odd (Euler parity, proved below as
`card_divisors_parity`).  Were `w·N` a perfect square, `σ(k) = 7·σ(w·N)` would be odd
and `k` could not be Zumkeller.  So any proof of the conjecture proves

> no odd perfect number `N` has `(τ(N)/2)·N` a perfect square,

a constraint outside the reach of published odd-perfect structure theory — Euler
form, Steuerwald exponent constraints, Touchard-type congruences, prime-counting
bounds; literature sweep 2026-07-30, NO-REFERENCE-FOUND on the constraint, the
connection, and the hardness claim, full source list in
`.tasks/main/docs/novelty-ZumkellerTauSigma.md`
(`not_isSquare_half_sigma_zero_mul_of_perfect` is the kernel-checked reduction).  In
particular *no amount of practical-number machinery closes the conjecture*: even
granted "practical ∧ even `σ` ⟹ Zumkeller" and every finite certificate, the
hypothetical odd perfect instances remain, and for those even the necessary parity
`2 ∣ σ(k)` is equivalent to the open not-a-perfect-square constraint above.  The intended
`sorry` therefore marks a statement at least as hard as new odd-perfect-number
theory, not a formalization gap.
-/

set_option autoImplicit false

open Finset

namespace ZumkellerTauSigma

/-! ## Binary blocks

`binIndices c` is the set of positions of the `1`-bits of `c`; it is the index set of the
binary expansion `c = ∑ i ∈ binIndices c, 2 ^ i`.
-/

/-- The set of positions of the `1`-bits in the binary expansion of `c`. -/
def binIndices (c : ℕ) : Finset ℕ := c.bitIndices.toFinset

-- Ground truth: `13 = 8 + 4 + 1`, `0` has no bits, `2 ^ 5` has exactly one.
example : binIndices 13 = {0, 2, 3} := by decide
example : binIndices 0 = ∅ := by decide
example : binIndices 32 = {5} := by decide

/-- The binary expansion: summing `2 ^ i` over the `1`-bit positions of `c` returns `c`. -/
theorem sum_binIndices (c : ℕ) : ∑ i ∈ binIndices c, 2 ^ i = c :=
  Finset.sum_toFinset_bitIndices_two_pow c

/-- All `1`-bits of `c < 2 ^ (a + 1)` sit in positions `≤ a`. -/
theorem binIndices_subset_range {a c : ℕ} (hc : c < 2 ^ (a + 1)) :
    binIndices c ⊆ range (a + 1) := by
  intro i hi
  have hmem : i ∈ c.bitIndices := List.mem_toFinset.mp hi
  have hpow : 2 ^ i ≤ c := Nat.two_pow_le_of_mem_bitIndices hmem
  have hlt : 2 ^ i < 2 ^ (a + 1) := lt_of_le_of_lt hpow hc
  exact Finset.mem_range.mpr ((Nat.pow_lt_pow_iff_right one_lt_two).mp hlt)

/-! ## Odd parts separate the blocks -/

/-- With `e` and `f` odd, `2 ^ i * e` determines the pair `(i, e)`: the odd factor is the
odd part and `i` the `2`-adic valuation. -/
theorem two_pow_mul_inj {i j e f : ℕ} (he : Odd e) (hf : Odd f)
    (h : 2 ^ i * e = 2 ^ j * f) : i = j ∧ e = f := by
  -- The step: the smaller `2`-power can be cancelled, and the leftover power of two must
  -- be trivial because the surviving factor is odd.
  have step : ∀ {i' j' e' f' : ℕ}, Odd e' → i' ≤ j' → 2 ^ i' * e' = 2 ^ j' * f' →
      i' = j' ∧ e' = f' := by
    intro i' j' e' f' he' hij hcancel
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hij
    have hpos : 0 < 2 ^ i' := Nat.two_pow_pos i'
    have hsplit : 2 ^ i' * e' = 2 ^ i' * (2 ^ t * f') := by
      rw [hcancel, pow_add, mul_assoc]
    have hcan : e' = 2 ^ t * f' := Nat.eq_of_mul_eq_mul_left hpos hsplit
    have ht : t = 0 := by
      by_contra ht0
      have h2 : 2 ∣ e' := hcan ▸ Dvd.dvd.mul_right (dvd_pow_self 2 ht0) f'
      have hmod : e' % 2 = 1 := Nat.odd_iff.mp he'
      omega
    subst ht
    exact ⟨by omega, by simpa using hcan⟩
  rcases Nat.le_total i j with hij | hji
  · exact step he hij h
  · obtain ⟨hji', hfe⟩ := step hf hji h.symm
    exact ⟨hji'.symm, hfe.symm⟩

/-! ## The divisor sum of a power of two -/

/-- The geometric sum `1 + 2 + ⋯ + 2 ^ a = 2 ^ (a+1) - 1`, without truncated subtraction. -/
theorem sum_range_two_pow_add_one (a : ℕ) :
    (∑ i ∈ range (a + 1), 2 ^ i) + 1 = 2 ^ (a + 1) := by
  induction a with
  | zero => decide
  | succ a ih =>
      rw [Finset.sum_range_succ, pow_succ (n := a + 1)]
      omega

/-- `σ(2 ^ a)` as a geometric sum: the divisors of `2 ^ a` are exactly `2 ^ 0, …, 2 ^ a`. -/
theorem sum_divisors_two_pow (a : ℕ) :
    ∑ d ∈ (2 ^ a).divisors, d = ∑ i ∈ range (a + 1), 2 ^ i :=
  Nat.sum_divisors_prime_pow Nat.prime_two

/-- `σ(2 ^ a) = 2 ^ (a+1) - 1`, stated without truncated subtraction. -/
theorem sum_divisors_two_pow_add_one (a : ℕ) :
    (∑ d ∈ (2 ^ a).divisors, d) + 1 = 2 ^ (a + 1) := by
  rw [sum_divisors_two_pow, sum_range_two_pow_add_one]

/-! ## The block decomposition

Write `n = 2 ^ a * m` with `m` odd.  Every divisor of `n` is *uniquely* `2 ^ i * e` with
`i ≤ a` and `e ∣ m` — the odd part recovers `e` and the `2`-adic valuation recovers `i`.
So choosing an index set `S e ⊆ {0, …, a}` for each divisor `e` of `m` picks out a set of
divisors of `n` whose sum is `∑ e ∈ m.divisors, (∑ i ∈ S e, 2 ^ i) * e`, and every subset
of `n.divisors` arises this way exactly once.  Since `∑ i ∈ S e, 2 ^ i` ranges over
precisely `{0, …, 2 ^ (a+1) - 1}` as `S e` ranges over subsets of `{0, …, a}`, this turns
Zumkeller-ness of `n` into a *bounded-coefficient representation problem* on the divisors
of the odd part `m` alone.  That equivalence is `isZumkeller_two_pow_mul_iff`.
-/

/-- The set of numbers `2 ^ i * e` selected by an index set `S e` for each divisor `e` of
`m`.  When every `S e ⊆ {0, …, a}` these are divisors of `2 ^ a * m`
(`blockSet_subset_divisors`), and for odd `m` every set of such divisors has this shape
(`eq_blockSet_of_subset_divisors`). -/
def blockSet (m : ℕ) (S : ℕ → Finset ℕ) : Finset ℕ :=
  m.divisors.biUnion fun e => (S e).image fun i => 2 ^ i * e

-- Ground truth at `2 ^ 2 * 3 = 12`: taking `S 1 = {0}` and `S 3 = {0, 1}` selects the
-- divisors `1`, `3` and `6` of `12`.
example : blockSet 3 (fun e => if e = 3 then {0, 1} else {0}) = {1, 3, 6} := by decide
example : blockSet 3 (fun _ => ∅) = ∅ := by decide

/-- Elements of `blockSet m S` are genuine divisors of `2 ^ a * m`. -/
theorem blockSet_subset_divisors {a m : ℕ} (hm0 : 0 < m) {S : ℕ → Finset ℕ}
    (hS : ∀ e ∈ m.divisors, S e ⊆ range (a + 1)) :
    blockSet m S ⊆ (2 ^ a * m).divisors := by
  have hn0 : 0 < 2 ^ a * m := Nat.mul_pos (Nat.two_pow_pos a) hm0
  intro x hx
  obtain ⟨e, he, hxe⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxe
  have hia : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp (hS e he hi))
  exact Nat.mem_divisors.mpr
    ⟨mul_dvd_mul (pow_dvd_pow 2 hia) (Nat.mem_divisors.mp he).1, hn0.ne'⟩

/-- **Block lemma.**  The sum over `blockSet m S` factors as the weighted divisor sum of
the odd part, the weight of `e` being the binary value `∑ i ∈ S e, 2 ^ i`.

Oddness of `m` is what keeps the blocks disjoint: `2 ^ i * e` recovers both `i` and `e`. -/
theorem sum_blockSet {m : ℕ} (hm : Odd m) (S : ℕ → Finset ℕ) :
    ∑ x ∈ blockSet m S, x = ∑ e ∈ m.divisors, (∑ i ∈ S e, 2 ^ i) * e := by
  have hodd : ∀ e ∈ m.divisors, Odd e := fun e he => hm.of_dvd_nat (Nat.mem_divisors.mp he).1
  -- checkpoint 1: distinct divisors of the odd part give disjoint blocks
  have hdisj : (m.divisors : Set ℕ).PairwiseDisjoint
      fun e => (S e).image fun i => 2 ^ i * e := by
    intro e he f hf hef
    refine Finset.disjoint_left.mpr ?_
    intro x hxe hxf
    obtain ⟨i, -, hix⟩ := Finset.mem_image.mp hxe
    obtain ⟨j, -, hjx⟩ := Finset.mem_image.mp hxf
    exact hef (two_pow_mul_inj (hodd e he) (hodd f hf) (hix.trans hjx.symm)).2
  -- checkpoint 2: each block sums to its binary weight times `e`
  have hblock : ∀ e ∈ m.divisors,
      ∑ x ∈ (S e).image (fun i => 2 ^ i * e), x = (∑ i ∈ S e, 2 ^ i) * e := by
    intro e he
    have hepos : 0 < e := Nat.pos_of_mem_divisors he
    have hinj : ∀ i ∈ S e, ∀ j ∈ S e, 2 ^ i * e = 2 ^ j * e → i = j := by
      intro i _ j _ hij
      have hpow : (2 : ℕ) ^ i = 2 ^ j := Nat.eq_of_mul_eq_mul_right hepos hij
      exact Nat.pow_right_injective (le_refl 2) hpow
    calc ∑ x ∈ (S e).image (fun i => 2 ^ i * e), x
        = ∑ i ∈ S e, 2 ^ i * e := Finset.sum_image hinj
      _ = (∑ i ∈ S e, 2 ^ i) * e := (Finset.sum_mul _ _ _).symm
  rw [blockSet, Finset.sum_biUnion hdisj]
  exact Finset.sum_congr rfl hblock

/-- Conversely, *every* set of divisors of `2 ^ a * m` is a block set: split each divisor
into its `2`-power part and its odd part. -/
theorem eq_blockSet_of_subset_divisors {a m : ℕ} (hm : Odd m) {A : Finset ℕ}
    (hA : A ⊆ (2 ^ a * m).divisors) :
    A = blockSet m fun e => (range (a + 1)).filter fun i => 2 ^ i * e ∈ A := by
  have hm0 : 0 < m := hm.pos
  have hmodd : ¬ (2 ∣ m) := by
    have hmod : m % 2 = 1 := Nat.odd_iff.mp hm
    omega
  have hcop2 : ∀ i : ℕ, Nat.Coprime (2 ^ i) m := fun i =>
    Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hmodd)
  apply Finset.Subset.antisymm
  · -- `x ∈ A` splits as `2 ^ i * e` with `i ≤ a` and `e ∣ m`
    intro x hx
    have hxd : x ∣ 2 ^ a * m := (Nat.mem_divisors.mp (hA hx)).1
    have hx0 : x ≠ 0 := (Nat.pos_of_mem_divisors (hA hx)).ne'
    obtain ⟨i, e, he, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hx0
    have heodd : ¬ (2 ∣ e) := by
      have hmod : e % 2 = 1 := Nat.odd_iff.mp he
      omega
    have hcope : Nat.Coprime e (2 ^ a) :=
      Nat.Coprime.pow_right a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr heodd).symm
    have hem : e ∣ m :=
      hcope.dvd_of_dvd_mul_left (dvd_trans (dvd_mul_left e (2 ^ i)) hxd)
    have hia : i ≤ a := by
      have hdvd : (2 : ℕ) ^ i ∣ 2 ^ a :=
        (hcop2 i).dvd_of_dvd_mul_right (dvd_trans (dvd_mul_right (2 ^ i) e) hxd)
      exact (Nat.pow_dvd_pow_iff_le_right one_lt_two).mp hdvd
    refine Finset.mem_biUnion.mpr ⟨e, Nat.mem_divisors.mpr ⟨hem, hm0.ne'⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hia), hx⟩, rfl⟩
  · -- membership in a block is by definition membership in `A`
    intro x hx
    obtain ⟨e, -, hxe⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxe
    exact (Finset.mem_filter.mp hi).2

/-- The weight of a block is `< 2 ^ (a + 1)`, since the indices live in `{0, …, a}`. -/
theorem sum_lt_two_pow_of_subset_range {a : ℕ} {T : Finset ℕ} (hT : T ⊆ range (a + 1)) :
    (∑ i ∈ T, 2 ^ i) < 2 ^ (a + 1) := by
  have hle : (∑ i ∈ T, 2 ^ i) ≤ ∑ i ∈ range (a + 1), 2 ^ i :=
    Finset.sum_le_sum_of_subset hT
  have hsum := sum_range_two_pow_add_one a
  omega

/-- The forward half of the block correspondence, packaged as an existence statement:
`∑ e ∈ m.divisors, c e * e` is realised by an honest set of divisors of `2 ^ a * m`. -/
theorem exists_subset_divisors_two_pow_mul {a m : ℕ} (hm : Odd m) (c : ℕ → ℕ)
    (hc : ∀ e ∈ m.divisors, c e < 2 ^ (a + 1)) :
    ∃ A ⊆ (2 ^ a * m).divisors, ∑ x ∈ A, x = ∑ e ∈ m.divisors, c e * e := by
  refine ⟨blockSet m fun e => binIndices (c e),
    blockSet_subset_divisors hm.pos fun e he => binIndices_subset_range (hc e he), ?_⟩
  rw [sum_blockSet hm]
  exact Finset.sum_congr rfl fun e _ => by rw [sum_binIndices]

/-- **Coefficient criterion.**  For `m` odd, `2 ^ a * m` is Zumkeller as soon as some
weighting of the divisors of `m` by coefficients `< 2 ^ (a + 1)` reaches half of
`σ(2 ^ a * m) = σ(2 ^ a) · σ(m)`. -/
theorem isZumkeller_two_pow_mul_of_coeff {a m : ℕ} (hm : Odd m) (c : ℕ → ℕ)
    (hc : ∀ e ∈ m.divisors, c e < 2 ^ (a + 1))
    (hsum : 2 * ∑ e ∈ m.divisors, c e * e
              = (∑ d ∈ (2 ^ a).divisors, d) * ∑ e ∈ m.divisors, e) :
    IsZumkeller (2 ^ a * m) := by
  have hm0 : 0 < m := hm.pos
  have hn0 : 0 < 2 ^ a * m := Nat.mul_pos (Nat.two_pow_pos a) hm0
  have hnotdvd : ¬ (2 ∣ m) := by
    have hmod : m % 2 = 1 := Nat.odd_iff.mp hm
    omega
  have hcop : (2 ^ a).Coprime m :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnotdvd)
  obtain ⟨A, hA, hAsum⟩ := exists_subset_divisors_two_pow_mul hm c hc
  rw [isZumkeller_iff_two_mul_sum_eq_sum_divisors hn0]
  exact ⟨A, Finset.mem_powerset.mpr hA, by rw [hAsum, hsum, hcop.sum_divisors_mul]⟩

/-- The converse of `isZumkeller_two_pow_mul_of_coeff`: a Zumkeller number `2 ^ a * m` with
`m` odd always *has* such a weighting — read the coefficient of `e` off the `2`-powers that
occur alongside `e` in a half-`σ` witness. -/
theorem exists_coeff_of_isZumkeller_two_pow_mul {a m : ℕ} (hm : Odd m)
    (h : IsZumkeller (2 ^ a * m)) :
    ∃ c : ℕ → ℕ, (∀ e ∈ m.divisors, c e < 2 ^ (a + 1)) ∧
      2 * ∑ e ∈ m.divisors, c e * e
        = (∑ d ∈ (2 ^ a).divisors, d) * ∑ e ∈ m.divisors, e := by
  have hnotdvd : ¬ (2 ∣ m) := by
    have hmod : m % 2 = 1 := Nat.odd_iff.mp hm
    omega
  have hcop : (2 ^ a).Coprime m :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnotdvd)
  obtain ⟨A, hApow, hAhalf⟩ := (isZumkeller_iff_two_mul_sum_eq_sum_divisors h.pos).mp h
  have hA : A ⊆ (2 ^ a * m).divisors := Finset.mem_powerset.mp hApow
  refine ⟨fun e => ∑ i ∈ (range (a + 1)).filter (fun i => 2 ^ i * e ∈ A), 2 ^ i, ?_, ?_⟩
  · exact fun e _ => sum_lt_two_pow_of_subset_range (Finset.filter_subset _ _)
  · rw [← sum_blockSet hm, ← eq_blockSet_of_subset_divisors hm hA, hAhalf,
      hcop.sum_divisors_mul]

/-- **Characterisation.**  For `m` odd, Zumkeller-ness of `2 ^ a * m` is *equivalent* to the
existence of a weighting of the divisors of the odd part `m` by coefficients `< 2 ^ (a + 1)`
whose weighted sum is `σ(2 ^ a * m) / 2`.

This is the sharp form of the `2`-adic block decomposition: the power of two contributes
nothing but the coefficient range `{0, …, 2 ^ (a+1) - 1}`. -/
theorem isZumkeller_two_pow_mul_iff {a m : ℕ} (hm : Odd m) :
    IsZumkeller (2 ^ a * m) ↔
      ∃ c : ℕ → ℕ, (∀ e ∈ m.divisors, c e < 2 ^ (a + 1)) ∧
        2 * ∑ e ∈ m.divisors, c e * e
          = (∑ d ∈ (2 ^ a).divisors, d) * ∑ e ∈ m.divisors, e :=
  ⟨exists_coeff_of_isZumkeller_two_pow_mul hm,
    fun ⟨c, hc, hsum⟩ => isZumkeller_two_pow_mul_of_coeff hm c hc hsum⟩

/-! ## The usable corollary -/

/-- **Main engine.**  If `m` is odd, `σ(m)` is even and `σ(m) ≤ 2 ^ (a + 1)`, then
`2 ^ a * m` is a Zumkeller number.

The witness weights every divisor `e ≠ 1` of `m` by the full `2 ^ a` and corrects at
`e = 1` by `2 ^ a - σ(m)/2 ≥ 0`. -/
theorem isZumkeller_two_pow_mul_of_sum_divisors_le {a m : ℕ} (hm : Odd m)
    (heven : 2 ∣ ∑ e ∈ m.divisors, e) (hle : ∑ e ∈ m.divisors, e ≤ 2 ^ (a + 1)) :
    IsZumkeller (2 ^ a * m) := by
  have hm0 : 0 < m := hm.pos
  have hpow : (2 : ℕ) ^ (a + 1) = 2 ^ a * 2 := pow_succ 2 a
  obtain ⟨h, hh⟩ := heven
  -- `g` is the slack `2 ^ a - σ(m)/2`, introduced additively to avoid `Nat` subtraction
  obtain ⟨g, hg⟩ : ∃ g, h + g = 2 ^ a := ⟨2 ^ a - h, by omega⟩
  -- split the divisor `1` off, so the correction sits on a single term
  have h1 : (1 : ℕ) ∈ m.divisors := Nat.one_mem_divisors.mpr hm0.ne'
  set S : ℕ := ∑ e ∈ m.divisors.erase 1, e with hSdef
  have hS1 : 1 + S = ∑ e ∈ m.divisors, e := Finset.add_sum_erase m.divisors id h1
  refine isZumkeller_two_pow_mul_of_coeff hm (fun e => if e = 1 then g else 2 ^ a) ?_ ?_
  · intro e _
    have hlt : (2 : ℕ) ^ a < 2 ^ (a + 1) := by omega
    by_cases he1 : e = 1
    · rw [if_pos he1]; omega
    · rw [if_neg he1]; exact hlt
  · -- the weighted sum is `g + 2 ^ a * S`
    have hcoeff : ∑ e ∈ m.divisors, (if e = 1 then g else 2 ^ a) * e = g + 2 ^ a * S := by
      rw [← Finset.add_sum_erase m.divisors (fun e => (if e = 1 then g else 2 ^ a) * e) h1]
      have herase : ∑ e ∈ m.divisors.erase 1, (if e = 1 then g else 2 ^ a) * e = 2 ^ a * S := by
        rw [hSdef, Finset.mul_sum]
        refine Finset.sum_congr rfl fun e he => ?_
        rw [if_neg (Finset.ne_of_mem_erase he)]
      rw [herase]
      simp
    have hM : (∑ d ∈ (2 ^ a).divisors, d) + 1 = 2 ^ a * 2 := by
      rw [sum_divisors_two_pow_add_one, hpow]
    rw [hcoeff, ← hS1]
    generalize hMdef : (∑ d ∈ (2 ^ a).divisors, d) = M at hM ⊢
    -- `M = S + 2 * g`, so `2 * (g + 2 ^ a * S) = M * (1 + S)`
    have hMS : M = S + 2 * g := by omega
    calc 2 * (g + 2 ^ a * S) = 2 * g + 2 ^ a * 2 * S := by ring
      _ = 2 * g + (M + 1) * S := by rw [hM]
      _ = M * S + (S + 2 * g) := by ring
      _ = M * S + M := by rw [← hMS]
      _ = M * (1 + S) := by ring

/-! ## Core families -/

/-- `2 ^ a * p` is Zumkeller for every odd prime `p` with `p + 1 ≤ 2 ^ (a+1)`. -/
theorem isZumkeller_two_pow_mul_prime {a p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hle : p + 1 ≤ 2 ^ (a + 1)) : IsZumkeller (2 ^ a * p) := by
  have hsum : ∑ e ∈ p.divisors, e = 1 + p := by
    rw [hp.divisors, Finset.sum_pair hp.one_lt.ne]
  refine isZumkeller_two_pow_mul_of_sum_divisors_le hodd ?_ ?_
  · rw [hsum]
    obtain ⟨t, ht⟩ := hodd
    exact ⟨t + 1, by omega⟩
  · rw [hsum]; omega

/-- `2 ^ a * 3` is Zumkeller for every `a ≥ 1` (A083207 comment, Charlie Neder 2019). -/
theorem isZumkeller_two_pow_mul_three {a : ℕ} (ha : 1 ≤ a) : IsZumkeller (2 ^ a * 3) := by
  refine isZumkeller_two_pow_mul_prime Nat.prime_three (by decide) ?_
  calc (3 : ℕ) + 1 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Neder's criterion** (A083207 comment, Charlie Neder 2019): every multiple of `6`
that is not a multiple of `9` is a Zumkeller number. -/
theorem isZumkeller_of_six_dvd_of_not_nine_dvd {n : ℕ} (h6 : 6 ∣ n) (h9 : ¬ (9 ∣ n)) :
    IsZumkeller n := by
  have hn0 : n ≠ 0 := by rintro rfl; exact h9 (dvd_zero 9)
  obtain ⟨a, u, hu, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have humod : u % 2 = 1 := Nat.odd_iff.mp hu
  -- the `2`-adic exponent is at least one, since `u` is odd and `2 ∣ n`
  have ha : 1 ≤ a := by
    by_contra hlt
    have ha0 : a = 0 := by omega
    subst ha0
    have h2 : (2 : ℕ) ∣ u := by simpa using (dvd_trans (by norm_num) h6 : (2 : ℕ) ∣ 2 ^ 0 * u)
    omega
  -- the odd part carries the factor `3`
  have h3n : (3 : ℕ) ∣ 2 ^ a * u := dvd_trans (by norm_num) h6
  have h3u : (3 : ℕ) ∣ u := by
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3n with hbad | hgood
    · exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hbad) (by norm_num)
    · exact hgood
  obtain ⟨s, rfl⟩ := h3u
  -- and only that one factor of `3`
  have h3s : ¬ (3 : ℕ) ∣ s := by
    rintro ⟨t, rfl⟩
    exact h9 ⟨2 ^ a * t, by ring⟩
  have hsodd : Odd s := hu.of_dvd_nat (dvd_mul_left s 3)
  have h2s : ¬ (2 : ℕ) ∣ s := by
    have hsmod : s % 2 = 1 := Nat.odd_iff.mp hsodd
    omega
  -- `n = (2 ^ a * 3) * s` with the two factors coprime
  have hrw : 2 ^ a * (3 * s) = 2 ^ a * 3 * s := by ring
  rw [hrw]
  refine IsZumkeller.mul_of_coprime (isZumkeller_two_pow_mul_three ha) ?_
  exact Nat.Coprime.mul_left
    (Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2s))
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3s)

/-! ## The conjecture -/

/-- **Ianakiev's conjecture** (OEIS A083207, comment of 2020-04-24; cf. A331668).
If `d > 1` divides `k` and `τ(d) · σ(d) = k`, then `k` is a Zumkeller number.

The proof is an **intended `sorry`**: this is an open problem, and provably not just a
formalization gap — the odd-perfect reduction at the end of this file
(`not_isSquare_half_sigma_zero_mul_of_perfect`) shows any proof of this statement
settles an open question about odd perfect numbers.  See the module docstring for the
computational evidence (`d ≤ 10⁷`) and for exactly which qualifying `k` the proved
engines above do and do not reach. -/
theorem isZumkeller_of_sigma_zero_mul_sigma_one (d k : ℕ) (hd : 1 < d) (hdk : d ∣ k)
    (hk : ArithmeticFunction.sigma 0 d * ArithmeticFunction.sigma 1 d = k) :
    IsZumkeller k := by
  sorry

/-! ## Satisfiability

The hypotheses of `isZumkeller_of_sigma_zero_mul_sigma_one` are jointly instantiated at
`(d, k) = (2, 6)`, `(6, 48)`, `(12, 168)`, `(18, 234)` and `(468, 22932)`, so the
conjecture is not vacuous; each of these `k` is settled unconditionally in the next
section.
-/

/-- `(d, k) = (2, 6)`: `τ(2)·σ(2) = 2·3 = 6` and `2 ∣ 6`. -/
example : 1 < 2 ∧ (2 : ℕ) ∣ 6 ∧
    ArithmeticFunction.sigma 0 2 * ArithmeticFunction.sigma 1 2 = 6 := by
  rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_one_apply]
  decide

/-- `(d, k) = (6, 48)`: `τ(6)·σ(6) = 4·12 = 48` and `6 ∣ 48`. -/
example : 1 < 6 ∧ (6 : ℕ) ∣ 48 ∧
    ArithmeticFunction.sigma 0 6 * ArithmeticFunction.sigma 1 6 = 48 := by
  rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_one_apply]
  decide

/-- `(d, k) = (12, 168)`: `τ(12)·σ(12) = 6·28 = 168` and `12 ∣ 168`. -/
example : 1 < 12 ∧ (12 : ℕ) ∣ 168 ∧
    ArithmeticFunction.sigma 0 12 * ArithmeticFunction.sigma 1 12 = 168 := by
  rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_one_apply]
  decide

/-- `(d, k) = (18, 234)`: `τ(18)·σ(18) = 6·39 = 234` and `18 ∣ 234`. -/
example : 1 < 18 ∧ (18 : ℕ) ∣ 234 ∧
    ArithmeticFunction.sigma 0 18 * ArithmeticFunction.sigma 1 18 = 234 := by
  rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_one_apply]
  decide

/-! ## Unconditional instances

The terms of A331668 above `1` begin `6, 48, 168, 234, 336, 480, 720, …`, arising from
`d ∈ {2, 6, 12, 18, 28, 24, 40, …}`.  Each instance below is settled by the proved engines,
*not* by the open theorem above.

`234` is the first qualifying value the coprime closure engine cannot reach at all:
`234 = 2·3²·13` has no nontrivial unitary factorization with a Zumkeller factor.  It is
settled instead by handing `isZumkeller_two_pow_mul_of_coeff` the explicit certificate
`c(117) = 2`, `c(39) = 1`, i.e. the half-`σ` witness `2·117 + 39 = 273` spread over the
`2`-block `{1, 2}`.
-/

/-- `(d, k) = (468, 22932)`: `τ(468)·σ(468) = 18·1274 = 22932` and `468 ∣ 22932`. -/
example : 1 < 468 ∧ (468 : ℕ) ∣ 22932 ∧
    ArithmeticFunction.sigma 0 468 * ArithmeticFunction.sigma 1 468 = 22932 := by
  rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_one_apply]
  decide

example : IsZumkeller 6 := by
  have h : IsZumkeller (2 ^ 1 * 3) := isZumkeller_two_pow_mul_three (le_refl 1)
  norm_num at h
  exact h

example : IsZumkeller 48 := by
  have h : IsZumkeller (2 ^ 4 * 3) := isZumkeller_two_pow_mul_three (by norm_num)
  norm_num at h
  exact h

example : IsZumkeller 168 := by
  have h24 : IsZumkeller (2 ^ 3 * 3) := isZumkeller_two_pow_mul_three (by norm_num)
  norm_num at h24
  have h : IsZumkeller (24 * 7) := h24.mul_of_coprime (by decide)
  norm_num at h
  exact h

example : IsZumkeller 336 := by
  have h48 : IsZumkeller (2 ^ 4 * 3) := isZumkeller_two_pow_mul_three (by norm_num)
  norm_num at h48
  have h : IsZumkeller (48 * 7) := h48.mul_of_coprime (by decide)
  norm_num at h
  exact h

example : IsZumkeller 480 := by
  have h96 : IsZumkeller (2 ^ 5 * 3) := isZumkeller_two_pow_mul_three (by norm_num)
  norm_num at h96
  have h : IsZumkeller (96 * 5) := h96.mul_of_coprime (by decide)
  norm_num at h
  exact h

example : IsZumkeller 720 := by
  have h80 : IsZumkeller (2 ^ 4 * 5) :=
    isZumkeller_two_pow_mul_prime (by norm_num) (by decide) (by norm_num)
  norm_num at h80
  have h : IsZumkeller (80 * 9) := h80.mul_of_coprime (by decide)
  norm_num at h
  exact h

/-- `d = 496` (a perfect number) gives `k = τ(496)σ(496) = 10·992 = 9920 = 2⁶·5·31`, which
carries no factor `3` at all — Neder's criterion says nothing about it. -/
example : IsZumkeller 9920 := by
  have h320 : IsZumkeller (2 ^ 6 * 5) :=
    isZumkeller_two_pow_mul_prime (by norm_num) (by decide) (by norm_num)
  norm_num at h320
  have h : IsZumkeller (320 * 31) := h320.mul_of_coprime (by decide)
  norm_num at h
  exact h

/-- `d = 18 ↦ k = 234 = 2·3²·13`, via an explicit coefficient certificate on the odd part
`117`: the weights `c(117) = 2`, `c(39) = 1` give `2·117 + 39 = 273 = σ(234)/2`. -/
example : IsZumkeller 234 := by
  have h : IsZumkeller (2 ^ 1 * 117) := by
    refine isZumkeller_two_pow_mul_of_coeff (by decide)
      (fun e => if e = 117 then 2 else if e = 39 then 1 else 0) ?_ ?_
    · decide
    · decide
  norm_num at h
  exact h

-- `d = 468 ↦ k = 22932 = 2²·3²·7²·13`, the second value out of reach of the coprime
-- closure engine; certificate `c(5733) = 6`, `c(1911) = 1` on the odd part `5733`, giving
-- `6·5733 + 1911 = 36309 = 7 · σ(5733)/2`.  The raised recursion depth is for the kernel
-- evaluation of `Nat.divisors 5733`, not for the mathematics.
set_option maxRecDepth 40000 in
example : IsZumkeller 22932 := by
  have h : IsZumkeller (2 ^ 2 * 5733) := by
    refine isZumkeller_two_pow_mul_of_coeff (by decide)
      (fun e => if e = 5733 then 6 else if e = 1911 then 1 else 0) ?_ ?_
    · decide
    · decide
  norm_num at h
  exact h

-- The third value out of reach of `isZumkeller_two_pow_mul_of_sum_divisors_le` plus
-- coprime closure is `d = 22932 ↦ k = 3921372 = 2² · 980343` with `980343 = 3⁴·7²·13·19`.
-- Its certificate for `isZumkeller_two_pow_mul_of_coeff` (coefficients `< 2 ³ = 8`,
-- target `7 · σ(980343)/2 = 6759060`) is
--   `c(980343) = 6, c(326781) = 2, c(140049) = c(75411) = c(7371) = c(567) = c(39)
--    = c(3) = 1`,
-- verified numerically; it is not formalised here because kernel evaluation of
-- `Nat.divisors 980343` is a filter over `range 980344`.

/-! ## The odd-perfect obstruction

Machine-checked hardness: any proof of the conjecture proves a *new theorem about odd
perfect numbers*.  Every odd perfect `N` (`Odd N`, `σ(N) = 2N`) satisfies the
hypotheses of the conjecture at `d := N`, `k := τ(N)·σ(N)`, because `σ(N) = 2N`
forces `N ∣ τ(N)σ(N)`.  Euler's parity analysis (`card_divisors_parity` below) gives
`τ(N) ≡ 2 [MOD 4]`, so `k = 4·(w·N)` with `τ(N) = 2w`, `w` odd, and odd part exactly
`w·N`.  Were `w·N` a perfect square, `σ(k) = 7·σ(w·N)` would be odd
(`sum_divisors_mod_two_of_isSquare`) — and no Zumkeller number has odd `σ`.  Hence the
conjecture implies: **no odd perfect `N` has `(τ(N)/2)·N` a perfect square**
(`not_isSquare_half_sigma_zero_mul_of_perfect`), an open constraint on odd perfect
numbers that no known structure theory decides.
-/

/-- A finite sum of odd numbers has the parity of the number of summands. -/
theorem sum_mod_two_of_forall_odd {s : Finset ℕ} {f : ℕ → ℕ}
    (hf : ∀ i ∈ s, f i % 2 = 1) : (∑ i ∈ s, f i) % 2 = s.card % 2 := by
  have h1 : (∑ i ∈ s, f i) % 2 = (∑ i ∈ s, f i % 2) % 2 := Finset.sum_nat_mod s 2 f
  have h2 : ∑ i ∈ s, f i % 2 = ∑ _i ∈ s, 1 := Finset.sum_congr rfl hf
  have h3 : ∑ _i ∈ s, (1 : ℕ) = s.card := by
    rw [Finset.sum_const, smul_eq_mul, mul_one]
  omega

/-- Pairing consecutive terms: a geometric sum of even length `2t` factors as
`(1 + p)` times the sum of the even-index powers. -/
theorem geom_sum_two_mul (p t : ℕ) :
    ∑ i ∈ range (2 * t), p ^ i = (1 + p) * ∑ j ∈ range t, p ^ (2 * j) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have h2 : 2 * (t + 1) = 2 * t + 1 + 1 := by ring
      rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ (f := fun j => p ^ (2 * j)), pow_succ]
      ring

/-- If a product is `≡ 2 [MOD 4]`, then one factor is `≡ 2 [MOD 4]` and the other is
odd. -/
theorem mod_four_eq_two_of_mul {x y : ℕ} (h : x * y % 4 = 2) :
    (x % 4 = 2 ∧ y % 2 = 1) ∨ (x % 2 = 1 ∧ y % 4 = 2) := by
  rcases (by omega : x % 2 = 0 ∨ x % 2 = 1) with hx | hx <;>
    rcases (by omega : y % 2 = 0 ∨ y % 2 = 1) with hy | hy
  · -- both factors even: the product is `0 [MOD 4]`
    obtain ⟨a, ha⟩ : ∃ a, x = 2 * a := ⟨x / 2, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, y = 2 * b := ⟨y / 2, by omega⟩
    have h4 : x * y = 4 * (a * b) := by rw [ha, hb]; ring
    omega
  · -- `x` even, `y` odd: the cofactor of `2` in `x` must be odd
    obtain ⟨a, ha⟩ : ∃ a, x = 2 * a := ⟨x / 2, by omega⟩
    have h2 : x * y = 2 * (a * y) := by rw [ha]; ring
    have hay : a * y % 2 = 1 := by omega
    have ha2 : a % 2 = 1 := Nat.odd_iff.mp (Nat.odd_mul.mp (Nat.odd_iff.mpr hay)).1
    exact Or.inl ⟨by omega, hy⟩
  · -- `x` odd, `y` even: symmetric
    obtain ⟨b, hb⟩ : ∃ b, y = 2 * b := ⟨y / 2, by omega⟩
    have h2 : x * y = 2 * (b * x) := by rw [hb]; ring
    have hbx : b * x % 2 = 1 := by omega
    have hb2 : b % 2 = 1 := Nat.odd_iff.mp (Nat.odd_mul.mp (Nat.odd_iff.mpr hbx)).1
    exact Or.inr ⟨hx, by omega⟩
  · -- both factors odd: the product is odd
    have hxy : x * y % 2 = 1 :=
      Nat.odd_iff.mp (Nat.odd_mul.mpr ⟨Nat.odd_iff.mpr hx, Nat.odd_iff.mpr hy⟩)
    omega

/-- If `x ≡ 2 [MOD 4]` and `y` is odd, then `x·y ≡ 2 [MOD 4]`. -/
theorem mul_mod_four_eq_two {x y : ℕ} (hx : x % 4 = 2) (hy : y % 2 = 1) :
    x * y % 4 = 2 := by
  obtain ⟨a, ha, ha2⟩ : ∃ a, x = 2 * a ∧ a % 2 = 1 := ⟨x / 2, by omega, by omega⟩
  have h2 : x * y = 2 * (a * y) := by rw [ha]; ring
  have hay : a * y % 2 = 1 :=
    Nat.odd_iff.mp (Nat.odd_mul.mpr ⟨Nat.odd_iff.mpr ha2, Nat.odd_iff.mpr hy⟩)
  omega

/-- `τ(p^e) = e + 1`: the divisors of a prime power are `p^0, …, p^e`. -/
theorem card_divisors_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    ((p ^ e).divisors).card = e + 1 := by
  rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]

/-- An odd number whose positive power is odd has odd base; and if a prime power
`p^e` with `0 < e` is odd, `p` itself is odd. -/
theorem mod_two_eq_one_of_pow {p e : ℕ} (he : 0 < e) (h : p ^ e % 2 = 1) :
    p % 2 = 1 := by
  rcases (by omega : p % 2 = 0 ∨ p % 2 = 1) with h2 | h2
  · exfalso
    have hdvd : 2 ∣ p ^ e := (by omega : (2 : ℕ) ∣ p).trans (dvd_pow_self p he.ne')
    omega
  · exact h2

/-- **Euler's parity analysis**, raw divisor form.  For odd `n`: an odd `σ(n)` forces
an odd `τ(n)`, and `σ(n) ≡ 2 [MOD 4]` forces `τ(n) ≡ 2 [MOD 4]`.

Applied to an odd perfect `n` — where `σ(n) = 2n ≡ 2 [MOD 4]` — the second conjunct
is the parity core of Euler's theorem on odd perfect numbers: exactly one prime of
`n` has odd exponent `e`, and `e ≡ 1 [MOD 4]`, so `τ(n) = 2·odd`. -/
theorem card_divisors_parity (n : ℕ) : n % 2 = 1 →
    ((∑ d ∈ n.divisors, d) % 2 = 1 → (n.divisors).card % 2 = 1) ∧
    ((∑ d ∈ n.divisors, d) % 4 = 2 → (n.divisors).card % 4 = 2) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p e hp he =>
      intro hodd
      have hpodd : p % 2 = 1 := mod_two_eq_one_of_pow he hodd
      have hS : ∑ d ∈ (p ^ e).divisors, d = ∑ i ∈ range (e + 1), p ^ i :=
        Nat.sum_divisors_prime_pow hp
      have hT : ((p ^ e).divisors).card = e + 1 := card_divisors_prime_pow hp e
      have hpar : (∑ i ∈ range (e + 1), p ^ i) % 2 = (e + 1) % 2 := by
        rw [sum_mod_two_of_forall_odd fun i _ => by rw [Nat.pow_mod, hpodd, one_pow]; decide,
          Finset.card_range]
      refine ⟨fun h1 => ?_, fun h4 => ?_⟩
      · rw [hS] at h1
        rw [hT]
        omega
      · rw [hS] at h4
        -- `σ(p^e) ≡ 2 [MOD 4]` is even, so `e + 1 = 2t`; factor out `1 + p = 2u`
        obtain ⟨t, ht⟩ : ∃ t, e + 1 = 2 * t := ⟨(e + 1) / 2, by omega⟩
        rw [ht, geom_sum_two_mul] at h4
        obtain ⟨u, hu⟩ : ∃ u, 1 + p = 2 * u := ⟨(1 + p) / 2, by omega⟩
        rw [hu, mul_assoc] at h4
        -- `2·(u·U) ≡ 2 [MOD 4]` forces `u` and `U` odd, and `U` odd forces `t` odd
        have huU : (u * ∑ j ∈ range t, p ^ (2 * j)) % 2 = 1 := by omega
        obtain ⟨huodd, hUodd⟩ := Nat.odd_mul.mp (Nat.odd_iff.mpr huU)
        have hUpar : (∑ j ∈ range t, p ^ (2 * j)) % 2 = t % 2 := by
          rw [sum_mod_two_of_forall_odd fun j _ => by rw [Nat.pow_mod, hpodd, one_pow]; decide,
            Finset.card_range]
        have htodd : t % 2 = 1 := by
          have hU2 := Nat.odd_iff.mp hUodd
          omega
        rw [hT]
        omega
  | zero => exact fun h => absurd h (by decide)
  | one =>
      intro _
      refine ⟨fun _ => ?_, fun h4 => ?_⟩
      · rw [Nat.divisors_one, Finset.card_singleton]
      · rw [Nat.divisors_one, Finset.sum_singleton] at h4
        omega
  | coprime a b ha hb hab iha ihb =>
      intro hodd
      obtain ⟨haodd', hbodd'⟩ := Nat.odd_mul.mp (Nat.odd_iff.mpr hodd)
      have haodd : a % 2 = 1 := Nat.odd_iff.mp haodd'
      have hbodd : b % 2 = 1 := Nat.odd_iff.mp hbodd'
      have hS : ∑ d ∈ (a * b).divisors, d = (∑ d ∈ a.divisors, d) * ∑ d ∈ b.divisors, d :=
        hab.sum_divisors_mul
      have hT : ((a * b).divisors).card = (a.divisors).card * (b.divisors).card :=
        hab.card_divisors_mul
      obtain ⟨iha2, iha4⟩ := iha haodd
      obtain ⟨ihb2, ihb4⟩ := ihb hbodd
      refine ⟨fun h1 => ?_, fun h4 => ?_⟩
      · rw [hS] at h1
        obtain ⟨hx, hy⟩ := Nat.odd_mul.mp (Nat.odd_iff.mpr h1)
        rw [hT]
        exact Nat.odd_iff.mp (Nat.odd_mul.mpr
          ⟨Nat.odd_iff.mpr (iha2 (Nat.odd_iff.mp hx)),
           Nat.odd_iff.mpr (ihb2 (Nat.odd_iff.mp hy))⟩)
      · rw [hS] at h4
        rw [hT]
        rcases mod_four_eq_two_of_mul h4 with ⟨hx4, hy2⟩ | ⟨hx2, hy4⟩
        · exact mul_mod_four_eq_two (iha4 hx4) (ihb2 hy2)
        · rw [Nat.mul_comm]
          exact mul_mod_four_eq_two (ihb4 hy4) (iha2 hx2)

-- Ground truth for `card_divisors_parity` at `n = 45`: `σ(45) = 78 ≡ 2 [MOD 4]` and
-- `τ(45) = 6 ≡ 2 [MOD 4]`; cross-checked by kernel `decide`.
example : (∑ d ∈ (45 : ℕ).divisors, d) % 4 = 2 ∧ ((45 : ℕ).divisors).card % 4 = 2 := by
  decide

/-- For an odd perfect square, `σ` is odd (raw divisor form).  The proof splits the
square across coprime parts with `exists_eq_pow_of_mul_eq_pow` and reads the even
prime-power exponents off the factorization. -/
theorem sum_divisors_mod_two_of_isSquare (n : ℕ) : n % 2 = 1 → IsSquare n →
    (∑ d ∈ n.divisors, d) % 2 = 1 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p e hp he =>
      intro hodd hsq
      have hpodd : p % 2 = 1 := mod_two_eq_one_of_pow he hodd
      -- a square prime power has even exponent
      obtain ⟨r, hr⟩ := hsq
      have hr0 : r ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hr
        exact absurd hr (pow_ne_zero e hp.pos.ne')
      have he2 : e = 2 * r.factorization p := by
        have h1 : (p ^ e).factorization p = e := by
          rw [hp.factorization_pow, Finsupp.single_eq_same]
        rw [hr, Nat.factorization_mul hr0 hr0, Finsupp.add_apply] at h1
        omega
      rw [Nat.sum_divisors_prime_pow hp,
        sum_mod_two_of_forall_odd fun i _ => by rw [Nat.pow_mod, hpodd, one_pow]; decide,
        Finset.card_range]
      omega
  | zero => exact fun h _ => absurd h (by decide)
  | one =>
      intro _ _
      rw [Nat.divisors_one, Finset.sum_singleton]
  | coprime a b ha hb hab iha ihb =>
      intro hodd hsq
      obtain ⟨haodd', hbodd'⟩ := Nat.odd_mul.mp (Nat.odd_iff.mpr hodd)
      -- a square splits into squares across a coprime factorization
      obtain ⟨c, hc⟩ := hsq
      have hc2 : a * b = c ^ 2 := by rw [hc, sq]
      have hga : IsUnit (Nat.gcd a b) := by rw [Nat.isUnit_iff]; exact hab
      have hgb : IsUnit (Nat.gcd b a) := by rw [Nat.isUnit_iff]; exact hab.symm
      obtain ⟨x, hx⟩ := exists_eq_pow_of_mul_eq_pow hga hc2
      obtain ⟨y, hy⟩ := exists_eq_pow_of_mul_eq_pow hgb (by rw [Nat.mul_comm b a]; exact hc2)
      rw [hab.sum_divisors_mul]
      exact Nat.odd_iff.mp (Nat.odd_mul.mpr
        ⟨Nat.odd_iff.mpr (iha (Nat.odd_iff.mp haodd') ⟨x, by rw [hx, sq]⟩),
         Nat.odd_iff.mpr (ihb (Nat.odd_iff.mp hbodd') ⟨y, by rw [hy, sq]⟩)⟩)

-- Ground truth at the odd squares `9` and `225`: `σ(9) = 13`, `σ(225) = 403`, both odd;
-- the second instance exercises the coprime branch (`225 = 9 · 25`).
example : (∑ d ∈ (9 : ℕ).divisors, d) % 2 = 1 :=
  sum_divisors_mod_two_of_isSquare 9 (by decide) ⟨3, by norm_num⟩
example : (∑ d ∈ (225 : ℕ).divisors, d) % 2 = 1 :=
  sum_divisors_mod_two_of_isSquare 225 (by decide) ⟨15, by norm_num⟩
example : (∑ d ∈ (225 : ℕ).divisors, d) % 2 = 1 := by decide

/-- **Euler parity for `τ`.**  For odd `n` with `σ(n) ≡ 2 [MOD 4]`, also
`τ(n) ≡ 2 [MOD 4]`.  (Satisfiable: `n = 45` below; for odd *perfect* `n` the
`σ`-hypothesis is automatic, `σ(n) = 2n ≡ 2 [MOD 4]`.) -/
theorem sigma_zero_mod_four_eq_two {n : ℕ} (hn : Odd n)
    (h : ArithmeticFunction.sigma 1 n % 4 = 2) :
    ArithmeticFunction.sigma 0 n % 4 = 2 := by
  rw [ArithmeticFunction.sigma_zero_apply]
  rw [ArithmeticFunction.sigma_one_apply] at h
  exact (card_divisors_parity n (Nat.odd_iff.mp hn)).2 h

-- Satisfiability of `sigma_zero_mod_four_eq_two` at `n = 45`.
example : ArithmeticFunction.sigma 0 45 % 4 = 2 :=
  sigma_zero_mod_four_eq_two (by decide)
    (by rw [ArithmeticFunction.sigma_one_apply]; decide)

/-- Bridge to the Mathlib normal form: the raw hypothesis `σ₁ N = 2 * N` carried by
the odd-perfect theorems in this section is exactly `Nat.Perfect` for positive `N`.
The theorems state it raw because the `σ`-form is what the reduction consumes. -/
example {N : ℕ} (hN : 0 < N) :
    N.Perfect ↔ ArithmeticFunction.sigma 1 N = 2 * N := by
  rw [ArithmeticFunction.sigma_one_apply]
  exact Nat.perfect_iff_sum_divisors_eq_two_mul hN

/-- **Every odd perfect number has `τ(N) = 2·(odd)`** — the parity core of Euler's
theorem on odd perfect numbers, as an existence statement.

The hypothesis class (`Odd N`, `σ(N) = 2N`) is not known to be inhabited: whether odd
perfect numbers exist is a famous open problem.  This theorem is the bridge that puts
every *hypothetical* odd perfect number inside the reach of the reduction below; it
asserts nothing unconditional about actual numbers, and no witness is exhibitable
today. -/
theorem exists_sigma_zero_eq_two_mul_odd_of_perfect {N : ℕ} (hN : Odd N)
    (hperf : ArithmeticFunction.sigma 1 N = 2 * N) :
    ∃ w, w % 2 = 1 ∧ ArithmeticFunction.sigma 0 N = 2 * w := by
  have hNodd : N % 2 = 1 := Nat.odd_iff.mp hN
  have h4 : ArithmeticFunction.sigma 0 N % 4 = 2 :=
    sigma_zero_mod_four_eq_two hN (by rw [hperf]; omega)
  exact ⟨ArithmeticFunction.sigma 0 N / 2, by omega, by omega⟩

/-! ### The reduction

`H` below is verbatim the statement of `isZumkeller_of_sigma_zero_mul_sigma_one` —
Ianakiev's conjecture.  These theorems are *conditional by design*: they exhibit, in
kernel-checked form, an open consequence any proof of the conjecture must establish.
Their hypotheses cannot be jointly instantiated today — `H` is the open conjecture
and the class `Odd N ∧ σ(N) = 2N` is believed (but not known) to be empty — which is
precisely the point: they measure the strength of the conjecture, not facts about
exhibited numbers. -/

/-- **Reduction, step 1.**  Under Ianakiev's conjecture, `k = τ(N)σ(N)` has even
`σ(k)` for every odd perfect `N`: such an `N` satisfies the hypotheses of the
conjecture at `d := N` (as `σ(N) = 2N` gives `N ∣ τ(N)σ(N)`), and Zumkeller numbers
have even `σ`. -/
theorem two_dvd_sigma_one_of_odd_perfect
    (H : ∀ d k : ℕ, 1 < d → d ∣ k →
      ArithmeticFunction.sigma 0 d * ArithmeticFunction.sigma 1 d = k → IsZumkeller k)
    {N : ℕ} (hN : Odd N) (hperf : ArithmeticFunction.sigma 1 N = 2 * N) :
    2 ∣ ArithmeticFunction.sigma 1
      (ArithmeticFunction.sigma 0 N * ArithmeticFunction.sigma 1 N) := by
  have hNodd : N % 2 = 1 := Nat.odd_iff.mp hN
  have hN1 : 1 < N := by
    rcases (by omega : N = 1 ∨ 1 < N) with rfl | h1
    · rw [ArithmeticFunction.sigma_one_apply, Nat.divisors_one,
        Finset.sum_singleton] at hperf
      omega
    · exact h1
  have hdvd : N ∣ ArithmeticFunction.sigma 0 N * ArithmeticFunction.sigma 1 N :=
    ⟨ArithmeticFunction.sigma 0 N * 2, by rw [hperf]; ring⟩
  have hz : IsZumkeller (ArithmeticFunction.sigma 0 N * ArithmeticFunction.sigma 1 N) :=
    H N _ hN1 hdvd rfl
  have heven := hz.two_dvd_sum_divisors
  rwa [← ArithmeticFunction.sigma_one_apply] at heven

/-- **Reduction, step 2 — the blocking lemma.**  Under Ianakiev's conjecture, no odd
perfect number `N` has `(τ(N)/2)·N` a perfect square (writing `τ(N) = 2w`, which
Euler parity guarantees with `w` odd).

Why this blocks the conjecture: for odd perfect `N`, `k = τ(N)σ(N) = 4·(w·N)` with
`w·N` odd, so were `w·N` a square, `σ(k) = σ(4)·σ(w·N) = 7·σ(w·N)` would be odd and
`k` could not be Zumkeller.  Thus any proof of the conjecture decides an open
question about odd perfect numbers — no known result controls `τ(N)` modulo squares —
and conversely, no practical-number or coprime-closure machinery can settle the
conjecture without first settling this. -/
theorem not_isSquare_half_sigma_zero_mul_of_perfect
    (H : ∀ d k : ℕ, 1 < d → d ∣ k →
      ArithmeticFunction.sigma 0 d * ArithmeticFunction.sigma 1 d = k → IsZumkeller k)
    {N w : ℕ} (hN : Odd N) (hperf : ArithmeticFunction.sigma 1 N = 2 * N)
    (hw : ArithmeticFunction.sigma 0 N = 2 * w) :
    ¬ IsSquare (w * N) := by
  intro hsq
  have hNodd : N % 2 = 1 := Nat.odd_iff.mp hN
  -- Euler parity: `τ(N) ≡ 2 [MOD 4]`, so `w` is odd and `w·N` is odd
  have ht4 : ArithmeticFunction.sigma 0 N % 4 = 2 :=
    sigma_zero_mod_four_eq_two hN (by rw [hperf]; omega)
  have hwodd : w % 2 = 1 := by omega
  have hwN : w * N % 2 = 1 :=
    Nat.odd_iff.mp (Nat.odd_mul.mpr ⟨Nat.odd_iff.mpr hwodd, hN⟩)
  -- `k = τ(N)σ(N) = 4·(w·N)`
  have hk : ArithmeticFunction.sigma 0 N * ArithmeticFunction.sigma 1 N = 4 * (w * N) := by
    rw [hw, hperf]
    ring
  have heven := two_dvd_sigma_one_of_odd_perfect H hN hperf
  rw [hk] at heven
  -- but `σ(4·(w·N)) = 7·σ(w·N)` is odd when `w·N` is an odd square
  have hcop : Nat.Coprime 4 (w * N) := by
    have h2 : ¬ (2 ∣ w * N) := by omega
    have hc2 : Nat.Coprime 2 (w * N) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2
    exact (show (4 : ℕ) = 2 ^ 2 by norm_num) ▸ hc2.pow_left 2
  have hmul : ArithmeticFunction.sigma 1 (4 * (w * N)) =
      ArithmeticFunction.sigma 1 4 * ArithmeticFunction.sigma 1 (w * N) :=
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
  have h74 : ArithmeticFunction.sigma 1 4 = 7 := by
    rw [ArithmeticFunction.sigma_one_apply]
    decide
  have hsodd : (∑ d ∈ (w * N).divisors, d) % 2 = 1 :=
    sum_divisors_mod_two_of_isSquare (w * N) hwN hsq
  rw [hmul, h74, ArithmeticFunction.sigma_one_apply] at heven
  omega

end ZumkellerTauSigma

