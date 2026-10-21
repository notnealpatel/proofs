/-
# Landau's theorem: the order of a finite group is bounded by its class number

## Source

* E. Landau, "Über die Klassenzahl der binären quadratischen Formen von negativer
  Discriminante", Math. Ann. 56 (1903) 671–676 (the finiteness of the solutions
  of `1 = 1/c₁ + ⋯ + 1/c_k` in positive integers, and its group-theoretic
  consequence).
* M. Newman, "A bound for the number of conjugacy classes in a group",
  J. London Math. Soc. 43 (1968) 108–110.
* I. M. Isaacs, *Finite Group Theory*, discussion of class numbers.

## Informal statement (scout record, verbatim)

"For every k there are only finitely many finite groups (up to isomorphism)
with exactly k conjugacy classes; explicitly |G| <= B(k) for an explicit B
(e.g. Landau/Newman: |G| <= k^{2^{k-1}}, or the Sylvester-sequence bound)."

## What is formalized (2026-10-21)

* `egyptian_bound`: if `q · ∑_{i ∈ s} 1/c_i` is a positive integer, `0 < q ≤ Q`,
  `|s| = k` and all `c_i > 0`, then every `c_i ≤ (k·Q)^(2^k)`.
* `card_le_landauBound`: `Nat.card G ≤ k ^ (2 ^ k)` for every finite group `G`
  with `k = Nat.card (ConjClasses G)` (explicit bound `B(k) = k^(2^k)`, weaker
  than Newman's `k^(2^(k-1))` but of the same shape).
* `finite_setOf_card_of_card_conjClasses`: for each `k`, the set of orders of
  finite groups (in a fixed universe) with exactly `k` conjugacy classes is
  finite.

The "finitely many isomorphism classes" phrasing is not formalized separately;
it follows from the bound together with the finiteness of groups of each
order, which is not stated here.

## Mathlib absence check (2026-10-21)

`leandoc` searches "number of conjugacy classes bound finite group order",
"Landau class number finitely many groups" and `grep Landau` over Mathlib:
only the class equation (`Group.sum_card_conj_classes_eq_card`), commuting
probability, Landau notation and Landau's Mahler-measure inequality; no bound
of `Nat.card G` in terms of `Nat.card (ConjClasses G)`.
-/
import Mathlib

set_option autoImplicit false

namespace GroupCount.LandauClassNumber

/-- The explicit Landau-type bound `B(k) = k ^ (2 ^ k)` on the order of a finite
group with `k` conjugacy classes. -/
def landauBound (k : ℕ) : ℕ := k ^ (2 ^ k)

example : landauBound 0 = 0 := rfl
example : landauBound 1 = 1 := rfl
example : landauBound 2 = 16 := rfl
example : landauBound 3 = 6561 := rfl

/-- **Egyptian-fraction bound (Landau).** Let `s` be a finite set of `k` indices
and `c i` positive integers.  If `q · ∑_{i ∈ s} 1 / c i` equals a positive integer
`n` for some `0 < q ≤ Q`, then every `c i` is at most `(k * Q) ^ (2 ^ k)`. -/
theorem egyptian_bound (k : ℕ) : ∀ {ι : Type*} (s : Finset ι) (c : ι → ℕ) (q Q n : ℕ),
    s.card = k → (∀ i ∈ s, 0 < c i) → 0 < q → q ≤ Q → 0 < n →
    (q : ℚ) * ∑ i ∈ s, (1 : ℚ) / c i = n → ∀ i ∈ s, c i ≤ (k * Q) ^ (2 ^ k) := by
  induction k with
  | zero =>
    intro ι s c q Q n hs _ _ _ _ _ i hi
    simp [Finset.card_eq_zero.mp hs] at hi
  | succ j ih =>
    intro ι s c q Q n hs hc hq hqQ hn hsum
    classical
    have hne : s.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image s c hne
    have hc0 : 0 < c i0 := hc i0 hi0
    -- the sum is at most `k / c i0`
    have hsum_le : ∑ i ∈ s, (1 : ℚ) / c i ≤ (j + 1 : ℕ) * (1 / (c i0 : ℚ)) := by
      rw [← hs]
      have := Finset.sum_le_card_nsmul s (fun i => (1 : ℚ) / c i) (1 / (c i0 : ℚ))
        (fun i hi => by
          have h1 : (0 : ℚ) < c i0 := by exact_mod_cast hc0
          have h2 : (c i0 : ℚ) ≤ c i := by exact_mod_cast hmin i hi
          exact one_div_le_one_div_of_le h1 h2)
      simpa [nsmul_eq_mul] using this
    have hci0_le : c i0 ≤ (j + 1) * q := by
      have h1 : (0 : ℚ) < c i0 := by exact_mod_cast hc0
      have key : (n : ℚ) * c i0 ≤ (j + 1 : ℕ) * q := by
        rw [← hsum]
        have hq' : (0 : ℚ) ≤ q := by positivity
        calc (q : ℚ) * (∑ i ∈ s, (1 : ℚ) / c i) * c i0
            ≤ q * ((j + 1 : ℕ) * (1 / (c i0 : ℚ))) * c i0 := by gcongr
          _ = (j + 1 : ℕ) * q := by field_simp
      have key' : n * c i0 ≤ (j + 1) * q := by exact_mod_cast key
      nlinarith
    have hQpos : 0 < Q := lt_of_lt_of_le hq hqQ
    have hbase : (j + 1) * Q ≤ ((j + 1) * Q) ^ (2 ^ (j + 1)) :=
      Nat.le_self_pow (by positivity) _
    intro i hi
    by_cases hii : i = i0
    · subst hii
      calc c i ≤ (j + 1) * q := hci0_le
        _ ≤ (j + 1) * Q := Nat.mul_le_mul_left _ hqQ
        _ ≤ _ := hbase
    · -- the remaining classes
      have hi' : i ∈ s.erase i0 := Finset.mem_erase.mpr ⟨hii, hi⟩
      have hsplit := Finset.add_sum_erase s (fun i => (1 : ℚ) / c i) hi0
      have hrest_pos : (0 : ℚ) < ∑ i ∈ s.erase i0, (1 : ℚ) / c i := by
        apply Finset.sum_pos'
        · intro x hx
          have := hc x (Finset.mem_of_mem_erase hx)
          positivity
        · exact ⟨i, hi', by have := hc i hi; positivity⟩
      have h1 : (0 : ℚ) < c i0 := by exact_mod_cast hc0
      have hrest_eq : ((q * c i0 : ℕ) : ℚ) * ∑ i ∈ s.erase i0, (1 : ℚ) / c i
          = (n : ℚ) * c i0 - q := by
        rw [← hsum, ← hsplit]
        push_cast
        field_simp
        ring
      have hlt : q < n * c i0 := by
        have : (0 : ℚ) < (n : ℚ) * c i0 - q := by
          rw [← hrest_eq]; positivity
        exact_mod_cast (sub_pos.mp this)
      have hcard : (s.erase i0).card = j := by
        rw [Finset.card_erase_of_mem hi0, hs]; rfl
      have hq'Q : q * c i0 ≤ (j + 1) * Q * Q := by
        calc q * c i0 ≤ Q * ((j + 1) * Q) :=
              Nat.mul_le_mul hqQ (hci0_le.trans (Nat.mul_le_mul_left _ hqQ))
          _ = (j + 1) * Q * Q := by ring
      have hIH := ih (s.erase i0) c (q * c i0) ((j + 1) * Q * Q) (n * c i0 - q) hcard
        (fun x hx => hc x (Finset.mem_of_mem_erase hx)) (Nat.mul_pos hq hc0) hq'Q
        (by omega) (by rw [hrest_eq]; push_cast [hlt.le]; ring) i hi'
      calc c i ≤ (j * ((j + 1) * Q * Q)) ^ (2 ^ j) := hIH
        _ ≤ (((j + 1) * Q) ^ 2) ^ (2 ^ j) := by
          apply Nat.pow_le_pow_left
          nlinarith
        _ = ((j + 1) * Q) ^ (2 ^ (j + 1)) := by
          rw [← pow_mul, pow_succ, mul_comm 2]

/-- Every conjugacy class of a group has cardinality dividing the order of the
group (orbit–stabilizer for the conjugation action). -/
theorem ncard_carrier_dvd_card {G : Type*} [Group G] (K : ConjClasses G) :
    K.carrier.ncard ∣ Nat.card G := by
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective K
  have h := Subgroup.index_dvd_card (MulAction.stabilizer (ConjAct G) g)
  rw [MulAction.index_stabilizer, ConjAct.orbit_eq_carrier_conjClasses,
    Nat.card_congr (ConjAct.toConjAct (G := G)).toEquiv.symm] at h
  exact h

/-- The conjugacy class of the identity is the singleton `{1}`. -/
theorem ncard_carrier_mk_one {G : Type*} [Group G] :
    (ConjClasses.mk (1 : G)).carrier.ncard = 1 := by
  rw [Set.ncard_eq_one]
  refine ⟨1, ?_⟩
  ext x
  simp [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]

/-- Class equation in reciprocal form: for a finite group `G`,
`∑_K 1 / (|G| / |K|) = 1`, the sum over conjugacy classes `K`
(`|G| / |K|` is the order of the centralizer of any element of `K`). -/
theorem sum_one_div_card_div_ncard_carrier {G : Type*} [Group G] [Finite G]
    [Fintype (ConjClasses G)] :
    ∑ K : ConjClasses G, (1 : ℚ) / ((Nat.card G / K.carrier.ncard : ℕ) : ℚ) = 1 := by
  have hG : (0 : ℚ) < Nat.card G := by exact_mod_cast Nat.card_pos
  have hsum := Group.sum_card_conj_classes_eq_card G
  rw [finsum_eq_sum_of_fintype] at hsum
  have hterm : ∀ K : ConjClasses G, (1 : ℚ) / ((Nat.card G / K.carrier.ncard : ℕ) : ℚ)
      = (K.carrier.ncard : ℚ) / Nat.card G := by
    intro K
    have hK : 0 < K.carrier.ncard := by
      obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective K
      exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨g, ConjClasses.mem_carrier_mk⟩
    rw [Nat.cast_div (ncard_carrier_dvd_card K) (by exact_mod_cast hK.ne')]
    have hK' : (0 : ℚ) < K.carrier.ncard := by exact_mod_cast hK
    field_simp
  simp_rw [hterm, ← Finset.sum_div]
  rw [← Nat.cast_sum, hsum]
  field_simp

/-- **Landau's theorem (explicit form).** The order of a finite group `G` is at
most `k ^ (2 ^ k)`, where `k = Nat.card (ConjClasses G)` is its class number. -/
theorem card_le_landauBound (G : Type*) [Group G] [Finite G] :
    Nat.card G ≤ landauBound (Nat.card (ConjClasses G)) := by
  classical
  cases nonempty_fintype G
  let c : ConjClasses G → ℕ := fun K => Nat.card G / K.carrier.ncard
  have hc : ∀ K ∈ (Finset.univ : Finset (ConjClasses G)), 0 < c K := by
    intro K _
    have hK : 0 < K.carrier.ncard := by
      obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective K
      exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨g, ConjClasses.mem_carrier_mk⟩
    exact Nat.div_pos (Nat.le_of_dvd Nat.card_pos (ncard_carrier_dvd_card K)) hK
  have hcard : (Finset.univ : Finset (ConjClasses G)).card = Nat.card (ConjClasses G) := by
    rw [Finset.card_univ, Nat.card_eq_fintype_card]
  have hsum : ((1 : ℕ) : ℚ) * ∑ K ∈ (Finset.univ : Finset (ConjClasses G)), (1 : ℚ) / c K
      = (1 : ℕ) := by
    rw [Nat.cast_one, one_mul]
    exact sum_one_div_card_div_ncard_carrier
  have hbound := egyptian_bound _ Finset.univ c 1 1 1 hcard hc one_pos le_rfl one_pos hsum
    (ConjClasses.mk 1) (Finset.mem_univ _)
  have hc1 : c (ConjClasses.mk 1) = Nat.card G := by
    simp only [c, ncard_carrier_mk_one, Nat.div_one]
  rw [hc1, mul_one] at hbound
  exact hbound

/-- **Landau's theorem (finiteness form).** For each `k`, only finitely many
orders occur among finite groups (in a fixed universe) with exactly `k`
conjugacy classes. -/
theorem finite_setOf_card_of_card_conjClasses.{u} (k : ℕ) :
    {n : ℕ | ∃ (G : Type u) (_ : Group G) (_ : Finite G),
      Nat.card (ConjClasses G) = k ∧ Nat.card G = n}.Finite := by
  refine (Set.finite_Iic (landauBound k)).subset ?_
  rintro n ⟨G, _, _, hk, rfl⟩
  exact hk ▸ card_le_landauBound G

/-- Sanity instance: class number one forces the trivial group. -/
example (G : Type*) [Group G] [Finite G] (h : Nat.card (ConjClasses G) = 1) :
    Nat.card G ≤ 1 := by
  simpa [h, landauBound] using card_le_landauBound G

/-- Non-vacuity: the bound applies to the cyclic group of order `3`. -/
example : Nat.card (Multiplicative (ZMod 3)) ≤
    landauBound (Nat.card (ConjClasses (Multiplicative (ZMod 3)))) :=
  card_le_landauBound _

end GroupCount.LandauClassNumber
