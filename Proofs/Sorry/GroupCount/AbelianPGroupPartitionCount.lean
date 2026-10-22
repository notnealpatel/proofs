/-
# Abelian groups of order `p ^ n` are counted by the partitions of `n`

## Classical source (recorded 2026-10-21)

G. Frobenius and L. Stickelberger, *Über Gruppen von vertauschbaren Elementen*,
J. reine angew. Math. 86 (1879), 217–262: existence and uniqueness of the
decomposition of a finite abelian group into cyclic groups of prime-power order
(uniqueness of the elementary divisors).  Textbook statements: J. J. Rotman,
*An Introduction to the Theory of Groups*, Ch. 6 (basis theorem and uniqueness of
the elementary divisors); T. W. Hungerford, *Algebra*, §II.2.

Informal statement (verbatim from the target specification):

```
The number of isomorphism classes of abelian groups of order p^n is the number of
partitions of n; more generally the number of abelian groups of order n is
multiplicative (OEIS A000688), giving gnu(p^n) >= p(n).
```

Formalized here: the first clause and the bound `p(n) ≤ gnu(p ^ n)`.  The
multiplicativity clause (OEIS A000688 for general `n`) is **not** formalized here.

## Mathlib check (2026-10-21)

Mathlib has the existence half of the structure theorem
(`CommGroup.equiv_prod_multiplicative_zmod_of_finite`) but no uniqueness of the
elementary divisors and no count of abelian groups by partitions (`leandoc` searches
for "elementary divisors unique finite abelian group", "abelian group partition
isomorphism class count", "invariant factors uniqueness torsion module", "direct sum
zmod isomorphic iff multiset equal" found nothing of the kind).

## Proof route

* Existence: the structure theorem writes a finite abelian group of order `p ^ n` as a
  product of cyclic groups `ℤ/p^{eᵢ}`; the exponents `eᵢ ≥ 1` form a partition of `n`.
* Uniqueness: the number of solutions of `x ^ (p ^ k) = 1` in `∏ᵢ ℤ/p^{λᵢ}` is
  `p ^ (∑ᵢ min λᵢ k)`; these sums for all `k` determine the multiset `λ` of positive
  parts, since `count a λ = 2 F(a) - F(a - 1) - F(a + 1)` with `F(k) = ∑ᵢ min λᵢ k`.
* Transport into the repository's isomorphism-class layer `GroupCount.IsoClass`
  (`Proofs/GroupCount/Gnu.lean`).
-/
import Mathlib
import Sorry.GroupCount.Gnu

set_option autoImplicit false

namespace GroupCount.AbelianPGroupPartitionCount

open Finset

/-! ## Definitions -/

/-- The number of solutions of `x ^ d = 1` in a monoid `G` (an isomorphism invariant;
`0` if the solution set is infinite, as for `Nat.card`). -/
noncomputable def torsionCount (G : Type*) [Monoid G] (d : ℕ) : ℕ :=
  Nat.card {x : G // x ^ d = 1}

/-- The abelian `p`-group attached to a partition `λ` of `n`: the product
`∏_{λᵢ ∈ λ} ℤ/p^{λᵢ}` (written multiplicatively), one cyclic factor per part,
counted with multiplicity (the index type is the multiset `λ.parts` viewed as a type). -/
abbrev PartitionGroup (p : ℕ) {n : ℕ} (l : Nat.Partition n) : Type :=
  (x : l.parts) → Multiplicative (ZMod (p ^ (x : ℕ)))

/-- An isomorphism class of groups of order `m` (in the repository's model
`GroupCount.IsoClass m`) is *abelian* when it is the class of a commutative group
structure.  Commutativity is an isomorphism invariant, so then every representative
is commutative (`isAbelianClass_isoClass_iff`). -/
def IsAbelianClass {m : ℕ} (c : IsoClass m) : Prop :=
  ∃ S : GroupStructure m, S.isoClass = c ∧ ∀ a b : S.Carrier, a * b = b * a

/-! ## The torsion-count invariant -/

/-- `torsionCount` is invariant under multiplicative isomorphism. -/
theorem torsionCount_congr {G H : Type*} [Monoid G] [Monoid H] (e : G ≃* H) (d : ℕ) :
    torsionCount G d = torsionCount H d :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
    simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
    rw [← map_pow, map_eq_one_iff _ e.injective])

/-- `torsionCount` of a finite product is the product of the `torsionCount`s. -/
theorem torsionCount_pi {ι : Type*} [Fintype ι] (G : ι → Type*) [∀ i, Monoid (G i)]
    (d : ℕ) : torsionCount ((i : ι) → G i) d = ∏ i, torsionCount (G i) d := by
  unfold torsionCount
  rw [← Nat.card_pi]
  refine Nat.card_congr ?_
  refine (Equiv.subtypeEquivRight fun x => ?_).trans
    (Equiv.subtypePiEquivPi (p := fun i (y : G i) => y ^ d = 1))
  simp [funext_iff]

/-- In the cyclic group `ℤ/m` (`m ≠ 0`), `x ^ d = 1` has exactly `gcd m d` solutions. -/
theorem torsionCount_zmod (m d : ℕ) [NeZero m] :
    torsionCount (Multiplicative (ZMod m)) d = m.gcd d := by
  have h := IsCyclic.card_powMonoidHom_ker (G := Multiplicative (ZMod m)) d
  have hc : Nat.card (Multiplicative (ZMod m)) = m := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [hc] at h
  unfold torsionCount
  rw [← h]
  rfl

/-- `gcd (p ^ a) (p ^ k) = p ^ min a k`. -/
theorem gcd_pow_pow (p a k : ℕ) : (p ^ a).gcd (p ^ k) = p ^ min a k := by
  rcases le_total a k with h | h
  · rw [min_eq_left h, Nat.gcd_eq_left (pow_dvd_pow p h)]
  · rw [min_eq_right h, Nat.gcd_eq_right (pow_dvd_pow p h)]

/-- In `∏ᵢ ℤ/p^{eᵢ}`, the equation `x ^ (p ^ k) = 1` has `p ^ (∑ᵢ min eᵢ k)` solutions. -/
theorem torsionCount_pi_zmod {ι : Type*} [Fintype ι] {p : ℕ} (hp : p.Prime) (e : ι → ℕ)
    (k : ℕ) :
    torsionCount ((i : ι) → Multiplicative (ZMod (p ^ e i))) (p ^ k) =
      p ^ (∑ i, min (e i) k) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [torsionCount_pi, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [torsionCount_zmod, gcd_pow_pow]

/-- In `PartitionGroup p λ`, the equation `x ^ (p ^ k) = 1` has `p ^ (∑ᵢ min λᵢ k)`
solutions. -/
theorem torsionCount_partitionGroup {p : ℕ} (hp : p.Prime) {n : ℕ} (l : Nat.Partition n)
    (k : ℕ) :
    torsionCount (PartitionGroup p l) (p ^ k) = p ^ (l.parts.map (fun x => min x k)).sum := by
  rw [torsionCount_pi_zmod hp, Finset.sum_eq_multiset_sum,
    Multiset.map_univ l.parts (fun x => min x k)]

/-- `PartitionGroup p λ` has order `p ^ n` for a partition `λ` of `n`. -/
theorem natCard_partitionGroup (p : ℕ) {n : ℕ} (l : Nat.Partition n) :
    Nat.card (PartitionGroup p l) = p ^ n := by
  rw [Nat.card_pi]
  have h : ∀ x : l.parts, Nat.card (Multiplicative (ZMod (p ^ (x : ℕ)))) = p ^ (x : ℕ) :=
    fun x => by rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  simp only [h]
  rw [Finset.prod_pow_eq_pow_sum, Finset.sum_eq_multiset_sum, Multiset.map_univ_coe,
    l.parts_sum]

/-! ## Recovering a partition from its `min`-sums -/

/-- For `a ≥ 1`, the multiplicity of `a` in a multiset `s` of naturals is the second
difference `2 F(a) - F(a - 1) - F(a + 1)` of `F(k) = ∑_{x ∈ s} min x k`. -/
theorem count_eq_second_difference (a : ℕ) (ha : 0 < a) (s : Multiset ℕ) :
    (s.count a : ℤ) = 2 * ((s.map (fun x => min x a)).sum : ℕ)
      - ((s.map (fun x => min x (a - 1))).sum : ℕ)
      - ((s.map (fun x => min x (a + 1))).sum : ℕ) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    simp only [Multiset.count_cons, Multiset.map_cons, Multiset.sum_cons, Nat.cast_add]
    rw [ih]
    split_ifs with h <;> omega

/-- Two multisets of positive naturals with the same sums `∑ min x k` for every `k`
are equal. -/
theorem multiset_eq_of_sum_min_eq {s t : Multiset ℕ} (hs : ∀ a ∈ s, 0 < a)
    (ht : ∀ a ∈ t, 0 < a)
    (h : ∀ k, (s.map (fun x => min x k)).sum = (t.map (fun x => min x k)).sum) :
    s = t := by
  ext a
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [Multiset.count_eq_zero.mpr (fun h0 => (hs 0 h0).false),
      Multiset.count_eq_zero.mpr (fun h0 => (ht 0 h0).false)]
  · have hs' := count_eq_second_difference a ha s
    have ht' := count_eq_second_difference a ha t
    rw [h a, h (a - 1), h (a + 1), ← ht'] at hs'
    exact_mod_cast hs'

/-- **Uniqueness of elementary divisors.**  If `PartitionGroup p λ ≃* PartitionGroup p μ`
for a prime `p`, then `λ = μ`. -/
theorem partition_eq_of_mulEquiv {p : ℕ} (hp : p.Prime) {n : ℕ} {l m : Nat.Partition n}
    (e : PartitionGroup p l ≃* PartitionGroup p m) : l = m := by
  have hk : ∀ k, (l.parts.map (fun x => min x k)).sum = (m.parts.map (fun x => min x k)).sum := by
    intro k
    have h := torsionCount_congr e (p ^ k)
    rw [torsionCount_partitionGroup hp, torsionCount_partitionGroup hp] at h
    exact Nat.pow_right_injective hp.two_le h
  exact Nat.Partition.ext (multiset_eq_of_sum_min_eq (fun _ ha => l.parts_pos ha)
    (fun _ ha => m.parts_pos ha) hk)

/-! ## Existence -/

/-- Two finite families of exponents with the same multiset of values are related by
a bijection of the index types. -/
theorem exists_equiv_of_map_eq {ι κ : Type*} [Fintype ι] [Fintype κ] {e : ι → ℕ}
    {f : κ → ℕ} (h : (univ : Finset ι).val.map e = (univ : Finset κ).val.map f) :
    ∃ σ : ι ≃ κ, ∀ i, f (σ i) = e i := by
  classical
  have hc : ∀ c, Fintype.card {i // e i = c} = Fintype.card {j // f j = c} := by
    intro c
    have hcount := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at hcount
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simp only [@eq_comm ℕ c] at hcount
    exact hcount
  exact ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)), Equiv.ofFiberEquiv_map _⟩

/-- Products of cyclic `p`-power groups with the same multiset of exponents are
isomorphic. -/
theorem nonempty_mulEquiv_pi_of_map_eq (p : ℕ) {ι κ : Type*} [Fintype ι] [Fintype κ]
    {e : ι → ℕ} {f : κ → ℕ}
    (h : (univ : Finset ι).val.map e = (univ : Finset κ).val.map f) :
    Nonempty (((i : ι) → Multiplicative (ZMod (p ^ e i))) ≃*
      ((j : κ) → Multiplicative (ZMod (p ^ f j)))) := by
  obtain ⟨σ, hσ⟩ := exists_equiv_of_map_eq h
  have he : e = fun i => f (σ i) := funext fun i => (hσ i).symm
  subst he
  exact ⟨(MulEquiv.piMultiplicative _).symm.trans <|
    (AddEquiv.toMultiplicative (RingEquiv.piCongrLeft (fun j => ZMod (p ^ f j)) σ).toAddEquiv).trans
      (MulEquiv.piMultiplicative _)⟩

/-- **Existence of elementary divisors.**  Every finite abelian group of order `p ^ n`
(`p` prime) is isomorphic to `PartitionGroup p λ` for some partition `λ` of `n`. -/
theorem exists_partition_mulEquiv {p : ℕ} (hp : p.Prime) {n : ℕ} (G : Type*) [CommGroup G]
    [Finite G] (hG : Nat.card G = p ^ n) :
    ∃ l : Nat.Partition n, Nonempty (G ≃* PartitionGroup p l) := by
  obtain ⟨ι, _, m, hm1, ⟨φ⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  have hcard : ∏ i, m i = p ^ n := by
    rw [← hG, Nat.card_congr φ.toEquiv, Nat.card_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hdvd : ∀ i, m i ∣ p ^ n := fun i => hcard ▸ Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  choose e he using fun i => (Nat.dvd_prime_pow hp).1 (hdvd i)
  have hm : m = fun i => p ^ e i := funext fun i => (he i).2
  subst hm
  beta_reduce at hm1 hcard
  have hpos : ∀ i, 0 < e i := fun i => Nat.pos_of_ne_zero fun h0 => by
    have h1 := hm1 i
    rw [h0, pow_zero] at h1
    exact lt_irrefl 1 h1
  have hsum : ∑ i, e i = n := Nat.pow_right_injective hp.two_le (by
    show p ^ (∑ i, e i) = p ^ n
    rw [← Finset.prod_pow_eq_pow_sum]
    exact hcard)
  let l : Nat.Partition n :=
    { parts := (univ : Finset ι).val.map e
      parts_pos := fun {a} ha => by
        obtain ⟨i, _, rfl⟩ := Multiset.mem_map.1 ha
        exact hpos i
      parts_sum := hsum }
  obtain ⟨ψ⟩ := nonempty_mulEquiv_pi_of_map_eq p (e := e) (f := fun x : l.parts => (x : ℕ))
    (Multiset.map_univ_coe l.parts).symm
  exact ⟨l, ⟨φ.trans ψ⟩⟩

/-- **Classification of finite abelian `p`-groups.**  A finite abelian group of order
`p ^ n` (`p` prime) is isomorphic to `∏ᵢ ℤ/p^{λᵢ}` for exactly one partition `λ` of `n`. -/
theorem existsUnique_partition_mulEquiv {p : ℕ} (hp : p.Prime) {n : ℕ} (G : Type*)
    [CommGroup G] [Finite G] (hG : Nat.card G = p ^ n) :
    ∃! l : Nat.Partition n, Nonempty (G ≃* PartitionGroup p l) := by
  obtain ⟨l, ⟨φ⟩⟩ := exists_partition_mulEquiv hp G hG
  refine ⟨l, ⟨φ⟩, fun m ⟨ψ⟩ => ?_⟩
  exact (partition_eq_of_mulEquiv hp (φ.symm.trans ψ)).symm

/-! ## Transport to isomorphism classes -/

/-- Commutativity is an isomorphism invariant, so a class is abelian iff a given
representative is commutative. -/
theorem isAbelianClass_isoClass_iff {m : ℕ} (S : GroupStructure m) :
    IsAbelianClass S.isoClass ↔ ∀ a b : S.Carrier, a * b = b * a := by
  refine ⟨fun ⟨T, hT, hcomm⟩ a b => ?_, fun h => ⟨S, rfl, h⟩⟩
  obtain ⟨φ⟩ := (GroupStructure.iso_iff_nonempty_mulEquiv _ _).1
    ((GroupStructure.isoClass_eq_iff _ _).1 hT)
  apply φ.symm.injective
  rw [map_mul, map_mul, hcomm]

/-- **Frobenius–Stickelberger count.**  For a prime `p`, the number of isomorphism
classes of abelian groups of order `p ^ n` equals the number `p(n)` of partitions
of `n`. -/
theorem natCard_abelian_isoClass_prime_pow {p : ℕ} (hp : p.Prime) (n : ℕ) :
    Nat.card {c : IsoClass (p ^ n) // IsAbelianClass c} = Nat.card (Nat.Partition n) := by
  classical
  haveI : ∀ x : ℕ, NeZero (p ^ x) := fun x => ⟨pow_ne_zero x hp.ne_zero⟩
  have hcard : ∀ l : Nat.Partition n, Fintype.card (PartitionGroup p l) = p ^ n := fun l => by
    rw [← Nat.card_eq_fintype_card, natCard_partitionGroup p]
  choose S hS using fun l : Nat.Partition n =>
    GroupStructure.exists_carrier_mulEquiv (G := PartitionGroup p l) (hcard l)
  have habel : ∀ l, IsAbelianClass (S l).isoClass := fun l => by
    refine ⟨S l, rfl, fun a b => ?_⟩
    obtain ⟨φ⟩ := hS l
    apply φ.symm.injective
    rw [map_mul, map_mul, mul_comm]
  let f : Nat.Partition n → {c : IsoClass (p ^ n) // IsAbelianClass c} :=
    fun l => ⟨(S l).isoClass, habel l⟩
  have hinj : Function.Injective f := by
    intro l m hlm
    have hiso : (S l).Iso (S m) :=
      (GroupStructure.isoClass_eq_iff _ _).1 (congrArg Subtype.val hlm)
    obtain ⟨ψ⟩ := (GroupStructure.iso_iff_nonempty_mulEquiv _ _).1 hiso
    obtain ⟨φl⟩ := hS l
    obtain ⟨φm⟩ := hS m
    exact partition_eq_of_mulEquiv hp ((φl.trans ψ).trans φm.symm)
  have hsurj : Function.Surjective f := by
    rintro ⟨c, T, rfl, hT⟩
    letI : CommGroup T.Carrier := { (inferInstance : Group T.Carrier) with mul_comm := hT }
    obtain ⟨l, ⟨ψ⟩⟩ := exists_partition_mulEquiv hp T.Carrier (GroupStructure.natCard_carrier T)
    obtain ⟨φ⟩ := hS l
    refine ⟨l, Subtype.ext ?_⟩
    exact (GroupStructure.isoClass_eq_iff _ _).2
      (GroupStructure.iso_of_mulEquiv (φ.symm.trans ψ.symm))
  exact (Nat.card_eq_of_bijective f ⟨hinj, hsurj⟩).symm

/-- **`p(n) ≤ gnu(p ^ n)`.**  For a prime `p`, the number of groups of order `p ^ n` up
to isomorphism is at least the number of partitions of `n`. -/
theorem natCard_partition_le_gnu_prime_pow {p : ℕ} (hp : p.Prime) (n : ℕ) :
    Nat.card (Nat.Partition n) ≤ gnu (p ^ n) := by
  rw [← natCard_abelian_isoClass_prime_pow hp n, gnu_eq_natCard]
  exact Finite.card_subtype_le _

/-! ## Ground truth -/

/-- `ℤ/4` has two solutions of `x ^ 2 = 1`. -/
example : torsionCount (Multiplicative (ZMod 4)) 2 = 2 := by
  rw [torsionCount_zmod]
  rfl

/-- `ℤ/2 × ℤ/2` (as a product of `ℤ/2^1` factors) has four solutions of `x ^ 2 = 1`. -/
example : torsionCount ((i : Fin 2) → Multiplicative (ZMod (2 ^ 1))) (2 ^ 1) = 4 := by
  rw [torsionCount_pi_zmod Nat.prime_two]
  rfl

/-- The one-part partition of `3` gives the cyclic group of order `8`. -/
example : Nat.card (PartitionGroup 2 (Nat.Partition.indiscrete 3)) = 8 :=
  natCard_partitionGroup 2 _

/-- The cyclic class of order `4` is abelian (the predicate is satisfiable). -/
example : IsAbelianClass (GroupStructure.cyclic 4).isoClass :=
  (isAbelianClass_isoClass_iff _).2 (by decide)

/-- Non-vacuous instance of the main theorem: there are at least two abelian groups of
order `4 = 2 ^ 2` (`ℤ/4` and `ℤ/2 × ℤ/2`, from the partitions `2` and `1 + 1`). -/
example : 1 < Nat.card {c : IsoClass (2 ^ 2) // IsAbelianClass c} := by
  rw [natCard_abelian_isoClass_prime_pow Nat.prime_two]
  have hnt : Nontrivial (Nat.Partition 2) :=
    ⟨⟨Nat.Partition.indiscrete 2, ⟨{1, 1}, by simp, rfl⟩, by decide⟩⟩
  exact Finite.one_lt_card_iff_nontrivial.2 hnt

end GroupCount.AbelianPGroupPartitionCount
