/-
# Gustafson's 5/8 bound and the smallest-prime refinement for commuting probability

## Classical source (recorded 2026-10-21)

* W. H. Gustafson, *What is the probability that two group elements commute?*,
  Amer. Math. Monthly 80 (1973), 1031–1034.  The 5/8 bound is the main
  observation of the paper.
* P. Lescot, *Isoclinism classes and commutativity degrees of finite groups*,
  J. Algebra 177 (1995), 847–869, for the smallest-prime refinement; see also
  R. K. Nath and A. K. Das, arXiv:1009.5526, Section 2.

Informal statement (as recorded by the scout):

  If G is a finite nonabelian group then commProb G <= 5/8. More generally, if
  p is the smallest prime dividing |G| and G is nonabelian, then
  commProb G <= (p^2 + p - 1)/p^3 (equal to 5/8 at p = 2).

## Mathlib absence

`leandoc` (2026-10-21): `commProb_le_five_eighths` misses; searches
"commuting probability nonabelian upper bound", "commProb five eighths",
"commProb lt one nonabelian" return only `commProb_le_one`, `commProb_eq_one_iff`,
`commProb_pos`, `commProb_prod`, `commProb_pi`, `commProb_function` and the
dihedral computations.  No upper bound below `1` is in Mathlib.

## Proof

Write `n = |G|`, `z = |Z(G)|`, `k = |ConjClasses G|`, `p = minFac n`, and
`n_c` for the number of non-central classes.  Then `Pr(G) = k / n`
(`commProb_def'`) and `k = z + n_c`.

* Every class size divides `n` (orbit–stabilizer), so a non-central class has
  size `≥ p`; the class equation gives `p · n_c ≤ n - z`.
* `[G : Z(G)] ≠ 1` (nonabelian) and is not prime (a prime-order `G/Z(G)` is
  cyclic, forcing `G` abelian), so `[G : Z(G)] ≥ p²` since every divisor
  `> 1` of `n` is `≥ p`.  Hence `z p² ≤ n`.
* `k p³ ≤ z p³ + (n - z) p² ≤ (p² + p - 1) n` because `z p² (p - 1) ≤ n (p - 1)`.

Notions used are Mathlib's: `commProb`, `IsMulCommutative`, `ConjClasses`,
`Subgroup.center`, `Subgroup.index`, `Nat.minFac`, `Nat.card`.  No new
definitions are introduced.
-/
import Mathlib
import GroupTPP.IsoclinismInvariants

set_option autoImplicit false

namespace CommutingProbabilityGustafson

variable {G : Type*} [Group G]

/-- **Class sizes divide the group order.** For a finite group `G`, the size of
every conjugacy class divides `|G|` (orbit–stabilizer for the conjugation
action). -/
theorem card_carrier_dvd_card [Finite G] (c : ConjClasses G) :
    Nat.card c.carrier ∣ Nat.card G := by
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
  have horb : Nat.card (ConjClasses.mk g).carrier
      = (MulAction.stabilizer (ConjAct G) g).index := by
    rw [MulAction.index_stabilizer, ConjAct.orbit_eq_carrier_conjClasses,
      Nat.card_coe_set_eq]
  rw [horb]
  exact (MulAction.stabilizer (ConjAct G) g).index_dvd_card

/-- **Non-central classes are large.** A non-central conjugacy class of a
finite group `G` has at least `minFac |G|` elements. -/
theorem minFac_le_card_carrier [Finite G] {c : ConjClasses G}
    (hc : c ∈ ConjClasses.noncenter G) :
    (Nat.card G).minFac ≤ Nat.card c.carrier := by
  have htwo : 2 ≤ Nat.card c.carrier := by
    have hnt : c.carrier.Nontrivial := hc
    have : 1 < Nat.card c.carrier := by
      rw [Nat.card_coe_set_eq]; exact Set.one_lt_ncard_iff_nontrivial.2 hnt
    omega
  exact Nat.minFac_le_of_dvd htwo (card_carrier_dvd_card c)

/-- **Counting the non-central classes.** With `p = minFac |G|`, the number
`n_c` of non-central conjugacy classes satisfies `p · n_c ≤ |G| - |Z(G)|`. -/
theorem minFac_mul_card_noncenter_le [Finite G] :
    (Nat.card G).minFac * Nat.card (ConjClasses.noncenter G)
      ≤ Nat.card G - Nat.card (Subgroup.center G) := by
  classical
  haveI := Fintype.ofFinite G
  have hsum : ∑ x ∈ (ConjClasses.noncenter G).toFinset, x.carrier.toFinset.card
      = Nat.card G - Nat.card (Subgroup.center G) := by
    have key := Group.card_center_add_sum_card_noncenter_eq_card G
    rw [Nat.card_eq_fintype_card (α := G), Nat.card_eq_fintype_card (α := Subgroup.center G)]
    omega
  have hbound : ∀ x ∈ (ConjClasses.noncenter G).toFinset,
      (Nat.card G).minFac ≤ x.carrier.toFinset.card := by
    intro x hx
    rw [← Nat.card_eq_card_toFinset]
    exact minFac_le_card_carrier (Set.mem_toFinset.1 hx)
  rw [← hsum, Nat.card_eq_card_toFinset (ConjClasses.noncenter G), mul_comm, ← smul_eq_mul]
  exact Finset.card_nsmul_le_sum _ _ _ hbound

/-- **The central quotient is not of prime order.** If `G` is nonabelian, then
`[G : Z(G)]` is not prime: otherwise `G / Z(G)` would be cyclic and `G` abelian. -/
theorem not_prime_index_center (h : ¬ IsMulCommutative G) :
    ¬ (Subgroup.center G).index.Prime := by
  intro hprime
  haveI : Fact (Subgroup.center G).index.Prime := ⟨hprime⟩
  haveI : IsCyclic (G ⧸ Subgroup.center G) :=
    isCyclic_of_prime_card (Subgroup.index_eq_card (Subgroup.center G)).symm
  apply h
  exact (QuotientGroup.mk' (Subgroup.center G)).isMulCommutative_of_isCyclic_of_ker_le_center
    (QuotientGroup.ker_mk' (Subgroup.center G)).le

/-- **The central index is at least `p²`.** For a finite nonabelian group `G`
with `p = minFac |G|`, we have `p² ≤ [G : Z(G)]`. -/
theorem minFac_sq_le_index_center [Finite G] (h : ¬ IsMulCommutative G) :
    (Nat.card G).minFac ^ 2 ≤ (Subgroup.center G).index := by
  set m := (Subgroup.center G).index with hm
  have hdvd : m ∣ Nat.card G := (Subgroup.center G).index_dvd_card
  have hm0 : m ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hm1 : m ≠ 1 := by
    intro h1
    apply h
    have htop : Subgroup.center G = ⊤ := Subgroup.index_eq_one.1 h1
    exact ⟨⟨fun a b => (Subgroup.mem_center_iff.1 (htop ▸ Subgroup.mem_top a) b).symm⟩⟩
  have hnp : ¬ m.Prime := not_prime_index_center h
  set q := m.minFac with hq
  have hqprime : q.Prime := Nat.minFac_prime hm1
  have hqm : m = q * (m / q) := (Nat.mul_div_cancel' (Nat.minFac_dvd m)).symm
  have hr : 2 ≤ m / q := by
    rcases Nat.lt_or_ge (m / q) 2 with hlt | hge
    · interval_cases hr : m / q
      · omega
      · exact absurd (by rw [hqm, mul_one]; exact hqprime) hnp
    · exact hge
  have hpq : (Nat.card G).minFac ≤ q :=
    Nat.minFac_le_of_dvd hqprime.two_le ((Nat.minFac_dvd m).trans hdvd)
  have hpr : (Nat.card G).minFac ≤ m / q :=
    Nat.minFac_le_of_dvd hr ((Nat.div_dvd_of_dvd (Nat.minFac_dvd m)).trans hdvd)
  rw [hqm, sq]
  exact Nat.mul_le_mul hpq hpr

/-- **Lescot's smallest-prime refinement of Gustafson's bound.** If `G` is a
finite nonabelian group and `p` is the smallest prime dividing `|G|`
(`p = minFac |G|`, a prime because `|G| > 1`), then
`Pr(G) ≤ (p² + p - 1) / p³`. -/
theorem commProb_le_of_minFac [Finite G] (h : ¬ IsMulCommutative G) :
    commProb G
      ≤ (((Nat.card G).minFac : ℚ) ^ 2 + (Nat.card G).minFac - 1)
          / ((Nat.card G).minFac : ℚ) ^ 3 := by
  set n := Nat.card G with hn
  set z := Nat.card (Subgroup.center G) with hz
  set m := (Subgroup.center G).index with hm
  set nc := Nat.card (ConjClasses.noncenter G) with hnc
  set p := n.minFac with hp
  have hn0 : 0 < n := Nat.card_pos
  have hzm : z * m = n := Subgroup.card_mul_index (Subgroup.center G)
  have hk : Nat.card (ConjClasses G) = z + nc :=
    IsoclinismInvariants.card_conjClasses_eq_center_add_nc
  have hcount : p * nc ≤ n - z := minFac_mul_card_noncenter_le
  have hpm : p ^ 2 ≤ m := minFac_sq_le_index_center h
  have hp1 : 1 ≤ p := Nat.minFac_pos n
  have hzn : z ≤ n := by
    rw [← hzm]
    exact Nat.le_mul_of_pos_right z (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
  -- Cast everything to `ℚ`.
  have hcountℚ : (p : ℚ) * nc ≤ (n : ℚ) - z := by
    have := (Nat.cast_le (α := ℚ)).2 hcount
    push_cast [Nat.cast_sub hzn] at this
    exact this
  have hzmℚ : (z : ℚ) * m = n := by exact_mod_cast hzm
  have hpmℚ : (p : ℚ) ^ 2 ≤ m := by exact_mod_cast hpm
  have hp1ℚ : (1 : ℚ) ≤ p := by exact_mod_cast hp1
  have hn0ℚ : (0 : ℚ) < n := by exact_mod_cast hn0
  have hz0ℚ : (0 : ℚ) ≤ z := Nat.cast_nonneg z
  have hnc0ℚ : (0 : ℚ) ≤ nc := Nat.cast_nonneg nc
  -- `z p² ≤ n`.
  have hzp : (z : ℚ) * p ^ 2 ≤ n := by
    rw [← hzmℚ]
    exact mul_le_mul_of_nonneg_left hpmℚ hz0ℚ
  rw [commProb_def', hk, ← hn, div_le_div_iff₀ hn0ℚ (by positivity)]
  push_cast
  -- `k p³ = z p³ + n_c p · p² ≤ z p³ + (n - z) p² ≤ (p² + p - 1) n`.
  have hstep : (nc : ℚ) * p ^ 3 ≤ ((n : ℚ) - z) * p ^ 2 := by
    have := mul_le_mul_of_nonneg_right hcountℚ (by positivity : (0 : ℚ) ≤ (p : ℚ) ^ 2)
    nlinarith [this]
  have hfin : (z : ℚ) * p ^ 2 * (p - 1) ≤ n * (p - 1) :=
    mul_le_mul_of_nonneg_right hzp (by linarith)
  nlinarith [hstep, hfin]

/-- **Gustafson's 5/8 bound.** If `G` is a finite nonabelian group, then the
probability that two uniformly random elements of `G` commute is at most `5/8`. -/
theorem commProb_le_five_eighths [Finite G] (h : ¬ IsMulCommutative G) :
    commProb G ≤ 5 / 8 := by
  refine (commProb_le_of_minFac h).trans ?_
  set p := (Nat.card G).minFac with hp
  have hp2 : (2 : ℚ) ≤ p := by
    have : 2 ≤ p := by
      apply Nat.Prime.two_le
      apply Nat.minFac_prime
      intro h1
      apply h
      haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.1 h1).1
      exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
    exact_mod_cast this
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  -- `5p³ - 8p² - 8p + 8 = (p - 2)(5p² + 2p - 4) ≥ 0` for `p ≥ 2`.
  nlinarith [mul_nonneg (sub_nonneg.2 hp2) (by nlinarith : (0 : ℚ) ≤ 5 * p ^ 2 + 2 * p - 4)]

/-! ### Ground truth and non-vacuity

The hypothesis `¬ IsMulCommutative G` is satisfiable: the dihedral group of
order `6` is nonabelian.  The bound `5/8` is attained by the dihedral group of
order `8`, checked below by a finite count of commuting pairs, so it is sharp. -/

/-- The dihedral group of order 6 is nonabelian, witnessing the hypothesis. -/
example : ¬ IsMulCommutative (DihedralGroup 3) := by
  rintro ⟨⟨hcomm⟩⟩
  exact absurd (hcomm (DihedralGroup.r 1) (DihedralGroup.sr 0)) (by decide)

/-- Non-vacuity: the main theorem applies to the dihedral group of order 6. -/
example : commProb (DihedralGroup 3) ≤ 5 / 8 :=
  commProb_le_five_eighths (by
    rintro ⟨⟨hcomm⟩⟩
    exact absurd (hcomm (DihedralGroup.r 1) (DihedralGroup.sr 0)) (by decide))

/-- Sharpness: the dihedral group of order 8 has commuting probability exactly
`5/8` (40 commuting ordered pairs out of 64). -/
example : commProb (DihedralGroup 4) = 5 / 8 := by
  have h40 : Nat.card {p : DihedralGroup 4 × DihedralGroup 4 // p.1 * p.2 = p.2 * p.1} = 40 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide
  rw [commProb_def]
  simp only [Commute, SemiconjBy]
  rw [h40, DihedralGroup.nat_card]
  norm_num

end CommutingProbabilityGustafson
