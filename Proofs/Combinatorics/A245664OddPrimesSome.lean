/-
# A245664 — Gribble: an explicit family of prime-partitionable numbers

OEIS A245664, Christopher Hunt Gribble (2014). For odd primes `p < q` with
`q = 2kp + 1`, `1 ≤ k` and `2k + 3 ≤ p`, the block `{p,q}` witnesses that
`p + q` is prime-partitionable and belongs to A245664.
Prime-partitionability uses the Holsztynski–Strube definition recalled in
OEIS A059756 (M. F. Hasler, 2014): partition the primes below `m` into
`P1, P2` so every positive composition `n1 + n2 = m` has a prime of `P1`
dividing `n1` or a prime of `P2` dividing `n2`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A245664OddPrimesSome

/-! ## Definition layer -/

/-- `P1` witnesses the prime-partitionability of `m` (Holsztynski–Strube,
as recalled in OEIS A059756): `P1` is a set of primes below `m`, its
complement `P2` is the set of the remaining primes below `m`, and for every
composition `n1 + n2 = m` with `n1, n2` positive, some prime of `P1` divides
`n1` or some prime of `P2` divides `n2`. -/
def PrimePartitionWitness (m : ℕ) (P1 : Finset ℕ) : Prop :=
  (∀ r ∈ P1, r.Prime ∧ r < m) ∧
    ∀ n1 n2 : ℕ, 0 < n1 → 0 < n2 → n1 + n2 = m →
      (∃ r ∈ P1, r ∣ n1) ∨ ∃ r : ℕ, r.Prime ∧ r < m ∧ r ∉ P1 ∧ r ∣ n2

/-- Prime-partitionable numbers (OEIS A059756): `m ≥ 2` admits a 2-partition
`{P1, P2}` of the primes below `m` witnessing `PrimePartitionWitness m P1`.
The guard `2 ≤ m` excludes the vacuous case `m = 1`, which has no
compositions and is not listed in A059756. -/
def PrimePartitionable (m : ℕ) : Prop :=
  2 ≤ m ∧ ∃ P1 : Finset ℕ, PrimePartitionWitness m P1

/-- Membership in OEIS A245664: `m ≥ 2` is prime-partitionable by a
2-partition one of whose blocks consists of exactly two primes.  Swapping
`n1` and `n2` in a composition exchanges the roles of `P1` and `P2`, so the
two-prime block can be taken to be `P1`, as in the entry's comment. -/
def InA245664 (m : ℕ) : Prop :=
  2 ≤ m ∧ ∃ P1 : Finset ℕ, P1.card = 2 ∧ PrimePartitionWitness m P1

/-- Bounded reformulation of `PrimePartitionWitness`, used only to decide
small instances: `n1` ranges over `0 < n1 < m` and `n2 = m - n1` (the
subtraction is guarded by `n1 < m`). -/
def BoundedWitness (m : ℕ) (P1 : Finset ℕ) : Prop :=
  (∀ r ∈ P1, r.Prime ∧ r < m) ∧
    ∀ n1 ∈ Finset.Ioo 0 m, (∃ r ∈ P1, r ∣ n1) ∨
      ∃ r ∈ Finset.range m, r.Prime ∧ r ∉ P1 ∧ r ∣ m - n1

/-- The bounded reformulation agrees with `PrimePartitionWitness`. -/
theorem primePartitionWitness_iff_boundedWitness (m : ℕ) (P1 : Finset ℕ) :
    PrimePartitionWitness m P1 ↔ BoundedWitness m P1 := by
  unfold PrimePartitionWitness BoundedWitness
  refine and_congr_right fun _ => ?_
  constructor
  · intro h n1 hn1
    rw [Finset.mem_Ioo] at hn1
    rcases h n1 (m - n1) hn1.1 (by omega) (by omega) with h1 | ⟨r, hr, hrm, hrP, hrd⟩
    · exact Or.inl h1
    · exact Or.inr ⟨r, Finset.mem_range.2 hrm, hr, hrP, hrd⟩
  · intro h n1 n2 hn1 hn2 hsum
    have hmem : n1 ∈ Finset.Ioo 0 m := Finset.mem_Ioo.2 ⟨hn1, by omega⟩
    have hn2eq : n2 = m - n1 := by omega
    rcases h n1 hmem with h1 | ⟨r, hrm, hr, hrP, hrd⟩
    · exact Or.inl h1
    · exact Or.inr ⟨r, hr, Finset.mem_range.1 hrm, hrP, hn2eq ▸ hrd⟩

instance (m : ℕ) (P1 : Finset ℕ) : Decidable (BoundedWitness m P1) := by
  unfold BoundedWitness; infer_instance

instance (m : ℕ) (P1 : Finset ℕ) : Decidable (PrimePartitionWitness m P1) :=
  decidable_of_iff _ (primePartitionWitness_iff_boundedWitness m P1).symm

/-- A witness may be restricted to primes below `m`, so prime-partitionability
is a search over subsets of the primes below `m`. -/
theorem primePartitionable_iff_exists_subset (m : ℕ) :
    PrimePartitionable m ↔
      2 ≤ m ∧ ∃ P1 ∈ ((Finset.range m).filter Nat.Prime).powerset,
        PrimePartitionWitness m P1 := by
  unfold PrimePartitionable
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨P1, hP1⟩
    refine ⟨P1, Finset.mem_powerset.2 fun r hr => ?_, hP1⟩
    obtain ⟨hrp, hrm⟩ := hP1.1 r hr
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hrm, hrp⟩
  · rintro ⟨P1, -, hP1⟩
    exact ⟨P1, hP1⟩

instance (m : ℕ) : Decidable (PrimePartitionable m) :=
  decidable_of_iff _ (primePartitionable_iff_exists_subset m).symm

/-! ## Examples

The first terms of A245664 are `16, 34, 36`, with two-prime blocks
`{5, 11}`, `{11, 23}` (for `34`; `23 = 2·11 + 1`) and `{7, 29}` (for `36`; `29 = 2·2·7 + 1`). -/

example : PrimePartitionWitness 16 {5, 11} := by decide
example : PrimePartitionWitness 34 {11, 23} := by decide
example : PrimePartitionWitness 36 {7, 29} := by decide

/-- `16` is the first term of A059756 and of A245664: no `2 ≤ m < 16` is
prime-partitionable. -/
example : ∀ m ∈ Finset.Ico 2 16, ¬ PrimePartitionable m := by decide

example : InA245664 16 := ⟨by norm_num, {5, 11}, by decide, by decide⟩

/-! ## The conjecture -/

/-- Load-bearing step.  Under the hypotheses of the conjecture, if
`n1 + n2 = p + q` with `n1, n2 > 0` and every prime factor of `n2` lies in
`{p, q}`, then `p ∣ n1` or `q ∣ n1`. -/
theorem dvd_of_primeFactors_subset {p q k n1 n2 : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hk : 1 ≤ k) (hkp : 2 * k + 3 ≤ p) (hqd : q = 2 * k * p + 1)
    (hn1 : 0 < n1) (hn2 : 0 < n2) (hsum : n1 + n2 = p + q)
    (hfac : ∀ r : ℕ, r.Prime → r ∣ n2 → r = p ∨ r = q) :
    p ∣ n1 ∨ q ∣ n1 := by
  -- `p + q < p ^ 2` and `p < q`
  have hpq : p < q := by rw [hqd]; nlinarith
  have hsq : p + q < p * p := by
    have h1 : 2 * k * p + 3 * p ≤ p * p := by nlinarith
    have h2 : 1 ≤ p := hp.one_lt.le
    omega
  by_cases hqn : q ∣ n2
  · -- `n2 = q` since `n2 < 2 q`
    obtain ⟨c, hc⟩ := hqn
    have hc1 : c = 1 := by
      rcases c with _ | _ | c
      · omega
      · rfl
      · nlinarith
    subst hc1
    left
    exact ⟨1, by omega⟩
  by_cases hpn : p ∣ n2
  · obtain ⟨c, hc⟩ := hpn
    by_cases hc1 : c = 1
    · subst hc1
      right
      exact ⟨1, by omega⟩
    · exfalso
      have hc0 : c ≠ 0 := by rintro rfl; omega
      obtain ⟨r, hr, hrc⟩ := Nat.exists_prime_and_dvd hc1
      have hrn : r ∣ n2 := hc ▸ Dvd.dvd.mul_left hrc p
      rcases hfac r hr hrn with rfl | rfl
      · have hle : r ≤ c := Nat.le_of_dvd (Nat.pos_of_ne_zero hc0) hrc
        have : r * r ≤ n2 := hc ▸ Nat.mul_le_mul_left r hle
        omega
      · exact hqn hrn
  · -- `n2` has no prime factor at all, so `n2 = 1` and `n1 = p (2k + 1)`
    have hn2one : n2 = 1 := by
      by_contra hne
      obtain ⟨r, hr, hrn⟩ := Nat.exists_prime_and_dvd hne
      rcases hfac r hr hrn with rfl | rfl
      · exact hpn hrn
      · exact hqn hrn
    left
    exact ⟨2 * k + 1, by subst hn2one; rw [hqd] at hsum; nlinarith⟩

/-- **Gribble's conjecture (OEIS A245664, Christopher Hunt Gribble, Jul 28 2014).**

Formal reading: for odd primes `p < q` with `q = 2kp + 1`, `k ≥ 1` and
`2k ≤ p - 3` (stated without truncated subtraction as `2k + 3 ≤ p`; the two
agree since `k ≥ 1`), the block `P1 = {p, q}` witnesses that `m = p + q` is
prime-partitionable, hence `m` is prime-partitionable and lies in A245664. -/
theorem gribble_conjecture {p q k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (_hp_odd : Odd p) (_hq_odd : Odd q) (hpq : p < q)
    (hk : 1 ≤ k) (hkp : 2 * k + 3 ≤ p) (hqd : q = 2 * k * p + 1) :
    PrimePartitionWitness (p + q) {p, q} ∧ PrimePartitionable (p + q) ∧
      InA245664 (p + q) := by
  have hW : PrimePartitionWitness (p + q) {p, q} := by
    refine ⟨?_, ?_⟩
    · intro r hr
      rcases Finset.mem_insert.1 hr with rfl | hr
      · exact ⟨hp, by have := hq.pos; omega⟩
      · rw [Finset.mem_singleton.1 hr]
        exact ⟨hq, by have := hp.pos; omega⟩
    · intro n1 n2 hn1 hn2 hsum
      by_cases hfac : ∀ r : ℕ, r.Prime → r ∣ n2 → r = p ∨ r = q
      · left
        rcases dvd_of_primeFactors_subset hp hq hk hkp hqd hn1 hn2 hsum hfac with h | h
        · exact ⟨p, Finset.mem_insert_self p {q}, h⟩
        · exact ⟨q, Finset.mem_insert_of_mem (Finset.mem_singleton_self q), h⟩
      · right
        push Not at hfac
        obtain ⟨r, hr, hrn, hrp, hrq⟩ := hfac
        have hrle : r ≤ n2 := Nat.le_of_dvd hn2 hrn
        refine ⟨r, hr, by omega, ?_, hrn⟩
        simp [hrp, hrq]
  have hm : 2 ≤ p + q := by have := hp.two_le; omega
  have hcard : ({p, q} : Finset ℕ).card = 2 := Finset.card_pair hpq.ne
  exact ⟨hW, ⟨hm, {p, q}, hW⟩, ⟨hm, {p, q}, hcard, hW⟩⟩

/-- Non-vacuity: the hypotheses of `gribble_conjecture` hold jointly at
`p = 5`, `q = 11`, `k = 1`, giving the first term `m = 16`. -/
example : InA245664 (5 + 11) :=
  (gribble_conjecture (k := 1) (by norm_num) (by norm_num) (by decide) (by decide)
    (by norm_num) le_rfl (by norm_num) (by norm_num)).2.2

end Candidates.A245664OddPrimesSome
