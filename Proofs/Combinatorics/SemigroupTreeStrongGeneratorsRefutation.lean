/-
# Strong generators in the semigroup tree: counterexample and sharp bound

M. Bras-Amorós and S. Bulygin, *Towards a better understanding of the
semigroup tree*, arXiv:0810.1619 (Semigroup Forum 79, 2009), Section 2
(definitions following `lemma:reasonforweakstrong`, Lemma `hyper`) and
Section `sec:future` (conjecture following `start-from-arbitrary`).
The conjecture bounds the number of strong generators in genus `g` by
`⌊(g-1)/2⌋`.

For `m ≥ 2`, `S_m = {0,m} ∪ [2m,∞)` has genus `2m-2` and exactly `m-1`
strong generators `2m+1,…,3m-1`. This refutes the bound at every positive
even genus; `S_2 = ⟨2,5⟩` is the paper's own hyperelliptic example.
The sharp bound below for non-ordinary semigroups is `2s ≤ g`, attained
by this family.

## Conventions

* A numerical semigroup is a set `S ⊆ ℕ` containing `0`, closed under
  addition, with finite complement (`IsNumericalSemigroup`).
* "Non-ordinary" is `multiplicity S < conductor S`: there is a nonzero
  element below the conductor.  This excludes `ℕ` itself (conductor `0`)
  and every `{0} ∪ [c, ∞)`.  The paper defines strong generators only for
  non-ordinary semigroups; restricting the conjecture to them only weakens
  it, so its refutation below is a refutation of the printed statement.
* Generators are minimal generators: nonzero elements that are not a sum
  of two nonzero elements (`IsMinGen`).
* `IsStrong` transcribes the paper's set equality literally.
-/
import Mathlib

set_option autoImplicit false

namespace SemigroupTreeStrongGenerators

/-! ## Definitions -/

/-- A numerical semigroup: a subset of `ℕ` containing `0`, closed under
addition, with finite complement. -/
def IsNumericalSemigroup (S : Set ℕ) : Prop :=
  0 ∈ S ∧ (∀ a ∈ S, ∀ b ∈ S, a + b ∈ S) ∧ Sᶜ.Finite

/-- The genus: the number of gaps (elements of `ℕ` outside `S`). -/
noncomputable def genus (S : Set ℕ) : ℕ := Sᶜ.ncard

/-- The conductor: the least `c` such that every `y ≥ c` lies in `S`. -/
noncomputable def conductor (S : Set ℕ) : ℕ := sInf {c | ∀ y, c ≤ y → y ∈ S}

/-- The multiplicity `λ_1`: the least nonzero element of `S`. -/
noncomputable def multiplicity (S : Set ℕ) : ℕ := sInf {x | x ∈ S ∧ x ≠ 0}

/-- `x` is a (minimal) generator of `S`: a nonzero element of `S` that is not
a sum of two nonzero elements of `S`. -/
def IsMinGen (S : Set ℕ) (x : ℕ) : Prop :=
  x ∈ S ∧ x ≠ 0 ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ 0 → b ≠ 0 → a + b ≠ x

/-- The effective generators: generators of `S` that are at least the
conductor. -/
def effectiveGenerators (S : Set ℕ) : Set ℕ :=
  {x | IsMinGen S x ∧ conductor S ≤ x}

/-- An effective generator `x` of `S` is strong when the effective generators
of `S \ {x}` are exactly the effective generators of `S` larger than `x`,
together with `x + λ_1`. -/
def IsStrong (S : Set ℕ) (x : ℕ) : Prop :=
  x ∈ effectiveGenerators S ∧
    effectiveGenerators (S \ {x}) =
      {y | y ∈ effectiveGenerators S ∧ x < y} ∪ {x + multiplicity S}

/-- The number of strong generators of `S`. -/
noncomputable def numStrong (S : Set ℕ) : ℕ := {x | IsStrong S x}.ncard

/-- The conjecture of Bras-Amorós and Bulygin as printed (restricted to
non-ordinary semigroups, where strong generators are defined): every
non-ordinary numerical semigroup of genus `g` has at most `⌊(g-1)/2⌋` strong
generators.  (Non-ordinary forces `2 ≤ g`, so `g - 1` is not truncated.) -/
def PrintedConjecture : Prop :=
  ∀ S : Set ℕ, IsNumericalSemigroup S → multiplicity S < conductor S →
    numStrong S ≤ (genus S - 1) / 2

/-- The counterexample family `S_m = {0, m} ∪ [2m, ∞)`. -/
def family (m : ℕ) : Set ℕ := {0, m} ∪ Set.Ici (2 * m)

/-! ## Basic lemmas -/

/-- Membership in `S_m`. -/
theorem mem_family {m y : ℕ} : y ∈ family m ↔ y = 0 ∨ y = m ∨ 2 * m ≤ y := by
  simp [family, or_assoc]

/-- Recognizing the conductor. -/
theorem conductor_eq_of {S : Set ℕ} {c : ℕ} (h1 : ∀ y, c ≤ y → y ∈ S)
    (h2 : 0 < c → c - 1 ∉ S) : conductor S = c := by
  unfold conductor
  apply le_antisymm (Nat.sInf_le (show c ∈ {c | ∀ y, c ≤ y → y ∈ S} from h1))
  refine le_csInf ⟨c, h1⟩ fun c' hc' => ?_
  by_contra hlt
  rw [not_le] at hlt
  exact h2 (by omega) (hc' _ (by omega))

/-- Recognizing the multiplicity. -/
theorem multiplicity_eq_of {S : Set ℕ} {m : ℕ} (h1 : m ∈ S) (h0 : m ≠ 0)
    (h2 : ∀ x, 0 < x → x < m → x ∉ S) : multiplicity S = m := by
  unfold multiplicity
  apply le_antisymm (Nat.sInf_le (show m ∈ {x | x ∈ S ∧ x ≠ 0} from ⟨h1, h0⟩))
  refine le_csInf ⟨m, h1, h0⟩ fun x hx => ?_
  by_contra hlt
  rw [not_le] at hlt
  exact h2 x (Nat.pos_of_ne_zero hx.2) hlt hx.1

/-! ## The family `S_m = {0, m} ∪ [2m, ∞)` -/

/-- `S_m` is a numerical semigroup. -/
theorem family_isNumericalSemigroup (m : ℕ) : IsNumericalSemigroup (family m) := by
  refine ⟨mem_family.2 (Or.inl rfl), fun a ha b hb => ?_, ?_⟩
  · rw [mem_family] at ha hb ⊢
    omega
  · apply (Set.finite_Iio (2 * m)).subset
    intro y hy
    rw [Set.mem_compl_iff, mem_family] at hy
    rw [Set.mem_Iio]
    omega

/-- The conductor of `S_m` is `2m` (for `m ≥ 2`). -/
theorem conductor_family {m : ℕ} (hm : 2 ≤ m) : conductor (family m) = 2 * m :=
  conductor_eq_of (fun _ hy => mem_family.2 (by omega))
    (fun _ h => by rw [mem_family] at h; omega)

/-- The multiplicity of `S_m` is `m` (for `m ≥ 1`). -/
theorem multiplicity_family {m : ℕ} (hm : 1 ≤ m) : multiplicity (family m) = m :=
  multiplicity_eq_of (mem_family.2 (by omega)) (by omega)
    (fun _ _ _ h => by rw [mem_family] at h; omega)

/-- The gaps of `S_m` are `(0, m) ∪ (m, 2m)`. -/
theorem compl_family (m : ℕ) :
    (family m)ᶜ = ↑(Finset.Ioo 0 m ∪ Finset.Ioo m (2 * m)) := by
  ext y
  simp only [Set.mem_compl_iff, mem_family, Finset.coe_union, Finset.coe_Ioo,
    Set.mem_union, Set.mem_Ioo]
  omega

/-- The genus of `S_m` is `2m - 2` (for `m ≥ 1`). -/
theorem genus_family {m : ℕ} (hm : 1 ≤ m) : genus (family m) + 2 = 2 * m := by
  rw [genus, compl_family, Set.ncard_coe_finset, Finset.card_union_of_disjoint]
  · simp only [Nat.card_Ioo]
    omega
  · rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_Ioo] at ha hb
    omega

/-- The generators of `S_m` are `m` and `2m+1, …, 3m-1`. -/
theorem isMinGen_family_iff {m x : ℕ} (hm : 1 ≤ m) :
    IsMinGen (family m) x ↔ x = m ∨ (2 * m < x ∧ x < 3 * m) := by
  constructor
  · rintro ⟨hx, hx0, hdec⟩
    rw [mem_family] at hx
    by_contra hne
    exact hdec m (mem_family.2 (by omega)) (x - m) (mem_family.2 (by omega))
      (by omega) (by omega) (by omega)
  · intro h
    refine ⟨mem_family.2 (by omega), by omega, fun a ha b hb ha0 hb0 => ?_⟩
    rw [mem_family] at ha hb
    omega

/-- The effective generators of `S_m` are `2m+1, …, 3m-1` (for `m ≥ 2`). -/
theorem mem_effectiveGenerators_family {m x : ℕ} (hm : 2 ≤ m) :
    x ∈ effectiveGenerators (family m) ↔ 2 * m < x ∧ x < 3 * m := by
  simp only [effectiveGenerators, Set.mem_ofPred_eq, isMinGen_family_iff (by omega : 1 ≤ m),
    conductor_family hm]
  omega

/-- Membership in `S_m \ {x}`. -/
theorem mem_family_diff {m x y : ℕ} :
    y ∈ family m \ {x} ↔ (y = 0 ∨ y = m ∨ 2 * m ≤ y) ∧ y ≠ x := by
  rw [Set.mem_sdiff, mem_family, Set.mem_singleton_iff]

/-- For an effective generator `x` of `S_m`, the effective generators of
`S_m \ {x}` are `x+1, …, 3m-1` and `x + m`. -/
theorem mem_effectiveGenerators_family_diff {m x y : ℕ} (hm : 2 ≤ m)
    (hx1 : 2 * m < x) (hx2 : x < 3 * m) :
    y ∈ effectiveGenerators (family m \ {x}) ↔ x < y ∧ (y < 3 * m ∨ y = x + m) := by
  have hcond : conductor (family m \ {x}) = x + 1 :=
    conductor_eq_of (fun _ hy => mem_family_diff.2 ⟨by omega, by omega⟩)
      (fun _ h => by rw [mem_family_diff] at h; omega)
  simp only [effectiveGenerators, Set.mem_ofPred_eq, hcond]
  constructor
  · rintro ⟨⟨hy, hy0, hdec⟩, hxy⟩
    rw [mem_family_diff] at hy
    refine ⟨by omega, ?_⟩
    by_contra hne
    exact hdec m (mem_family_diff.2 ⟨by omega, by omega⟩) (y - m)
      (mem_family_diff.2 ⟨by omega, by omega⟩) (by omega) (by omega) (by omega)
  · intro h
    refine ⟨⟨mem_family_diff.2 ⟨by omega, by omega⟩, by omega,
      fun a ha b hb ha0 hb0 => ?_⟩, by omega⟩
    rw [mem_family_diff] at ha hb
    omega

/-- The strong generators of `S_m` are exactly `2m+1, …, 3m-1` (for `m ≥ 2`). -/
theorem isStrong_family_iff {m x : ℕ} (hm : 2 ≤ m) :
    IsStrong (family m) x ↔ 2 * m < x ∧ x < 3 * m := by
  constructor
  · rintro ⟨hx, -⟩
    exact (mem_effectiveGenerators_family hm).1 hx
  · intro hx
    refine ⟨(mem_effectiveGenerators_family hm).2 hx, ?_⟩
    ext y
    rw [mem_effectiveGenerators_family_diff hm hx.1 hx.2, Set.mem_union, Set.mem_ofPred_eq,
      mem_effectiveGenerators_family hm, Set.mem_singleton_iff,
      multiplicity_family (by omega : 1 ≤ m)]
    omega

/-- `S_m` has exactly `m - 1` strong generators (for `m ≥ 2`). -/
theorem numStrong_family {m : ℕ} (hm : 2 ≤ m) : numStrong (family m) + 1 = m := by
  have hset : {x | IsStrong (family m) x} = ↑(Finset.Ioo (2 * m) (3 * m)) := by
    ext x
    rw [Set.mem_ofPred_eq, isStrong_family_iff hm, Finset.coe_Ioo, Set.mem_Ioo]
  rw [numStrong, hset, Set.ncard_coe_finset, Nat.card_Ioo]
  omega

/-- **The printed conjecture fails at every even genus.**  For every `m ≥ 2`,
`S_m = {0, m} ∪ [2m, ∞)` is a non-ordinary numerical semigroup of genus
`2m - 2` with `m - 1` strong generators, and `⌊(g-1)/2⌋ = m - 2 < m - 1`. -/
theorem family_counterexample {m : ℕ} (hm : 2 ≤ m) :
    IsNumericalSemigroup (family m) ∧ multiplicity (family m) < conductor (family m) ∧
      genus (family m) + 2 = 2 * m ∧ numStrong (family m) + 1 = m ∧
      (genus (family m) - 1) / 2 < numStrong (family m) := by
  have hg := genus_family (by omega : 1 ≤ m)
  have hs := numStrong_family hm
  refine ⟨family_isNumericalSemigroup m, ?_, hg, hs, ?_⟩
  · rw [multiplicity_family (by omega), conductor_family hm]
    omega
  · omega

/-- **The Bras-Amorós–Bulygin conjecture `n^i_g = 0` for `i > ⌊(g-1)/2⌋` is
false**, already for the hyperelliptic semigroup `⟨2, 5⟩ = S_2` of genus `2`
with the strong generator `5`. -/
theorem not_printedConjecture : ¬ PrintedConjecture := by
  intro h
  obtain ⟨hS, hord, -, -, hlt⟩ := family_counterexample (le_refl 2)
  exact absurd (h _ hS hord) (not_le.2 hlt)

/-! ## General facts about numerical semigroups -/

/-- Every integer at least the conductor lies in a numerical semigroup. -/
theorem mem_of_conductor_le {S : Set ℕ} (hS : IsNumericalSemigroup S) {y : ℕ}
    (hy : conductor S ≤ y) : y ∈ S := by
  obtain ⟨N, hN⟩ := hS.2.2.bddAbove
  have hne : {c | ∀ y, c ≤ y → y ∈ S}.Nonempty := by
    refine ⟨N + 1, fun z hz => ?_⟩
    by_contra hzS
    have hzN : z ≤ N := hN hzS
    omega
  exact Nat.sInf_mem hne y hy

/-- The integer just below a positive conductor is a gap. -/
theorem conductor_sub_one_not_mem {S : Set ℕ} (hS : IsNumericalSemigroup S)
    (hc : 0 < conductor S) : conductor S - 1 ∉ S := by
  intro hmem
  have hset : conductor S - 1 ∈ {c | ∀ y, c ≤ y → y ∈ S} := fun y hy => by
    rcases Nat.eq_or_lt_of_le hy with h | h
    · rw [← h]
      exact hmem
    · exact mem_of_conductor_le hS (by omega)
  have hle : conductor S ≤ conductor S - 1 := Nat.sInf_le hset
  omega

/-- Every gap is below the conductor. -/
theorem lt_conductor_of_not_mem {S : Set ℕ} (hS : IsNumericalSemigroup S) {y : ℕ}
    (hy : y ∉ S) : y < conductor S := by
  by_contra h
  exact hy (mem_of_conductor_le hS (not_lt.1 h))

/-- The multiplicity is a nonzero element of `S`. -/
theorem multiplicity_mem {S : Set ℕ} (hS : IsNumericalSemigroup S) :
    multiplicity S ∈ S ∧ multiplicity S ≠ 0 := by
  have hne : {x | x ∈ S ∧ x ≠ 0}.Nonempty :=
    ⟨conductor S + 1, mem_of_conductor_le hS (by omega), by omega⟩
  exact Nat.sInf_mem hne

/-- The multiplicity is at most every nonzero element of `S`. -/
theorem multiplicity_le {S : Set ℕ} {x : ℕ} (hx : x ∈ S) (hx0 : x ≠ 0) :
    multiplicity S ≤ x :=
  Nat.sInf_le (show x ∈ {x | x ∈ S ∧ x ≠ 0} from ⟨hx, hx0⟩)

/-- Multiples of an element stay in the semigroup. -/
theorem mul_mem {S : Set ℕ} (hS : IsNumericalSemigroup S) {a : ℕ} (ha : a ∈ S) :
    ∀ k : ℕ, k * a ∈ S
  | 0 => by rw [zero_mul]; exact hS.1
  | k + 1 => by rw [add_mul, one_mul]; exact hS.2.1 _ (mul_mem hS ha k) _ ha

/-- A strong generator is a generator of `S`. -/
theorem IsStrong.isMinGen {S : Set ℕ} {x : ℕ} (h : IsStrong S x) : IsMinGen S x :=
  h.1.1

/-- A strong generator is at least the conductor. -/
theorem IsStrong.conductor_le {S : Set ℕ} {x : ℕ} (h : IsStrong S x) : conductor S ≤ x :=
  h.1.2

/-- If `x` is strong then `x + λ_1` is a generator of `S \ {x}`. -/
theorem IsStrong.isMinGen_add {S : Set ℕ} {x : ℕ} (h : IsStrong S x) :
    IsMinGen (S \ {x}) (x + multiplicity S) := by
  have hmem : x + multiplicity S ∈ effectiveGenerators (S \ {x}) := by
    rw [h.2]
    exact Or.inr rfl
  exact hmem.1

/-- A strong generator is smaller than the conductor plus the multiplicity. -/
theorem IsStrong.lt_conductor_add {S : Set ℕ} (hS : IsNumericalSemigroup S)
    (hmc : multiplicity S < conductor S) {x : ℕ} (h : IsStrong S x) : x < conductor S + multiplicity S := by
  by_contra hle
  obtain ⟨hm, hm0⟩ := multiplicity_mem hS
  exact h.isMinGen.2.2 (multiplicity S) hm (x - multiplicity S)
    (mem_of_conductor_le hS (by omega)) hm0 (by omega) (by omega)

/-! ## The corrected bound `2 s ≤ g` -/

/-- **Residue bound.**  Distinct strong generators of a non-ordinary
numerical semigroup have distinct nonzero residues modulo `λ_1`, so any finite
set of strong generators has at most `λ_1 - 1` elements. -/
theorem card_le_multiplicity_sub_one {S : Set ℕ} (hS : IsNumericalSemigroup S)
    (hmc : multiplicity S < conductor S) (St : Finset ℕ)
    (hSt : ∀ x ∈ St, IsStrong S x) : St.card ≤ multiplicity S - 1 := by
  obtain ⟨hm, hm0⟩ := multiplicity_mem hS
  set m := multiplicity S with hm_def
  have hmaps : Set.MapsTo (· % m) ↑St ↑(Finset.Ioo 0 m) := by
    intro x hx
    have hxs := hSt x hx
    have hxc := hxs.conductor_le
    rw [Finset.coe_Ioo, Set.mem_Ioo]
    refine ⟨Nat.pos_of_ne_zero fun h0 => ?_, Nat.mod_lt _ (Nat.pos_of_ne_zero hm0)⟩
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h0
    have hsub : x - m = (k - 1) * m := by rw [Nat.sub_one_mul, hk, mul_comm]
    refine hxs.isMinGen.2.2 m hm (x - m) ?_ hm0 (by omega) (by omega)
    rw [hsub]
    exact mul_mem hS hm _
  have hinj : Set.InjOn (· % m) ↑St := by
    intro x hx y hy hxy
    by_contra hne
    wlog hlt : x < y generalizing x y
    · exact this hy hx hxy.symm (Ne.symm hne) (by omega)
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hxy.symm)
    have hxs := hSt x hx
    have hys := hSt y hy
    refine hys.isMinGen.2.2 x hxs.isMinGen.1 (y - x) ?_ hxs.isMinGen.2.1 (by omega) (by omega)
    rw [hk, mul_comm]
    exact mul_mem hS hm k
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rwa [Nat.card_Ioo, Nat.sub_zero] at hcard

/-- **Corrected bound.**  A non-ordinary numerical semigroup of genus `g` has
at most `⌊g/2⌋` strong generators: `2 s ≤ g`.  (This corrects the
Bras-Amorós–Bulygin conjecture `s ≤ ⌊(g-1)/2⌋` of arXiv:0810.1619, Section
`sec:future`; equality holds at every even genus by `family_counterexample`.) -/
theorem two_mul_numStrong_le_genus {S : Set ℕ} (hS : IsNumericalSemigroup S)
    (hmc : multiplicity S < conductor S) : 2 * numStrong S ≤ genus S := by
  classical
  obtain ⟨hm, hm0⟩ := multiplicity_mem hS
  set m := multiplicity S with hm_def
  set c := conductor S with hc_def
  set St := (Finset.Ico c (c + m)).filter (IsStrong S) with hSt_def
  have hStrong : ∀ x ∈ St, IsStrong S x := fun x hx => (Finset.mem_filter.1 hx).2
  have hnum : numStrong S = St.card := by
    rw [numStrong, ← Set.ncard_coe_finset]
    congr 1
    ext x
    rw [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico]
    exact ⟨fun h => ⟨⟨h.conductor_le, h.lt_conductor_add hS hmc⟩, h⟩, fun h => h.2⟩
  rw [hnum]
  rcases St.eq_empty_or_nonempty with hE | hne
  · rw [hE, Finset.card_empty]
    omega
  set xs := St.max' hne with hxs_def
  have hxsSt : xs ∈ St := St.max'_mem hne
  have hxs := hStrong xs hxsSt
  have hle_xs : ∀ y ∈ St, y ≤ xs := fun y hy => St.le_max' y hy
  have hc_xs : c ≤ xs := hxs.conductor_le
  set P := (Finset.Ioo m xs).filter (· ∈ S) with hP_def
  set Q := (Finset.Ioo m xs).filter (· ∉ S) with hQ_def
  -- (A) residues
  have hA : St.card ≤ m - 1 := card_le_multiplicity_sub_one hS hmc St hStrong
  -- (B) the reflection `a ↦ xs + m - a` sends nongaps of `(m, xs)` to gaps
  have hB : P.card ≤ Q.card := by
    apply Finset.card_le_card_of_injOn (fun a => xs + m - a)
    · intro a ha
      dsimp only
      rw [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ioo] at ha
      rw [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ioo]
      refine ⟨by omega, fun hb => ?_⟩
      exact hxs.isMinGen_add.2.2 a ⟨ha.2, by rw [Set.mem_singleton_iff]; omega⟩
        (xs + m - a) ⟨hb, by rw [Set.mem_singleton_iff]; omega⟩ (by omega) (by omega)
        (by omega)
    · intro a ha b hb hab
      rw [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ioo] at ha hb
      simp only at hab
      omega
  -- (C) the gaps are `(0, m)` together with `Q`
  have hC : genus S = (m - 1) + Q.card := by
    have hgaps : Sᶜ = ↑(Finset.Ioo 0 m ∪ Q) := by
      ext y
      rw [Set.mem_compl_iff, Finset.coe_union, Set.mem_union, Finset.coe_Ioo, Set.mem_Ioo,
        Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ioo]
      constructor
      · intro hy
        have hyc := lt_conductor_of_not_mem hS hy
        have hy0 : y ≠ 0 := fun h => hy (h ▸ hS.1)
        have hym : y ≠ m := fun h => hy (h ▸ hm)
        rcases Nat.lt_or_gt_of_ne hym with h | h
        · exact Or.inl ⟨by omega, h⟩
        · exact Or.inr ⟨⟨h, by omega⟩, hy⟩
      · rintro (h | h)
        · intro hyS
          have := multiplicity_le hyS (by omega)
          omega
        · exact h.2
    rw [genus, hgaps, Set.ncard_coe_finset, Finset.card_union_of_disjoint, Nat.card_Ioo,
      Nat.sub_zero]
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_Ioo] at ha
    rw [Finset.mem_filter, Finset.mem_Ioo] at hb
    omega
  -- (D) every strong generator other than `xs` is a nongap in `(m, xs)`
  have hD : ∀ y ∈ St, y ≠ xs → y ∈ P := by
    intro y hy hyx
    have hys := hStrong y hy
    have := hle_xs y hy
    have := hys.conductor_le
    rw [Finset.mem_filter, Finset.mem_Ioo]
    exact ⟨⟨by omega, by omega⟩, hys.isMinGen.1⟩
  have h2m_ne : xs ≠ 2 * m := by
    intro h
    exact hxs.isMinGen.2.2 m hm m hm hm0 hm0 (by omega)
  by_cases h2m : 2 * m < xs
  · -- `2m` is a nongap in `(m, xs)` that is not a generator
    have h2mP : 2 * m ∈ P := by
      rw [Finset.mem_filter, Finset.mem_Ioo]
      exact ⟨⟨by omega, h2m⟩, by rw [two_mul]; exact hS.2.1 m hm m hm⟩
    have hsub : St ⊆ insert xs (P.erase (2 * m)) := by
      intro y hy
      rw [Finset.mem_insert, Finset.mem_erase]
      by_cases hyx : y = xs
      · exact Or.inl hyx
      · refine Or.inr ⟨fun h => ?_, hD y hy hyx⟩
        exact (hStrong y hy).isMinGen.2.2 m hm m hm hm0 hm0 (by omega)
    have hcard := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    rw [Finset.card_erase_of_mem h2mP] at hcard
    have hP1 : 1 ≤ P.card := Finset.card_pos.2 ⟨_, h2mP⟩
    omega
  · -- `xs < 2m`: all strong generators lie in `[c, xs]`, and `(m, c)` is all gaps
    have hxs2 : xs < 2 * m := by omega
    have hIcc : St ⊆ Finset.Icc c xs := by
      intro y hy
      rw [Finset.mem_Icc]
      exact ⟨(hStrong y hy).conductor_le, hle_xs y hy⟩
    have hIco : Finset.Ico c xs ⊆ P := by
      intro y hy
      rw [Finset.mem_Ico] at hy
      rw [Finset.mem_filter, Finset.mem_Ioo]
      exact ⟨⟨by omega, hy.2⟩, mem_of_conductor_le hS hy.1⟩
    have hQc : Q ⊆ Finset.Ioo m c := by
      intro y hy
      rw [Finset.mem_filter, Finset.mem_Ioo] at hy
      rw [Finset.mem_Ioo]
      exact ⟨hy.1.1, lt_conductor_of_not_mem hS hy.2⟩
    have hgap : c - 1 ∉ S := conductor_sub_one_not_mem hS (by omega)
    have hcm : c - 1 ≠ m := fun h => hgap (h ▸ hm)
    have hQ1 : c - 1 ∈ Q := by
      rw [Finset.mem_filter, Finset.mem_Ioo]
      exact ⟨⟨by omega, by omega⟩, hgap⟩
    have h1 := Finset.card_le_card hIcc
    have h2 := Finset.card_le_card hIco
    have h3 := Finset.card_le_card hQc
    have h4 : 1 ≤ Q.card := Finset.card_pos.2 ⟨_, hQ1⟩
    rw [Nat.card_Icc] at h1
    rw [Nat.card_Ico] at h2
    rw [Nat.card_Ioo] at h3
    omega

/-! ## Examples from the paper -/

-- Lemma `hyper` at `n = 2`: `S_2 = {0, 2} ∪ [4, ∞) = ⟨2, 5⟩` has genus `2`,
-- conductor `4`, and its unique effective generator `5 = c + 1` is strong.
example : genus (family 2) = 2 ∧ conductor (family 2) = 4 ∧ IsStrong (family 2) 5 ∧
    numStrong (family 2) = 1 :=
  ⟨by have := genus_family (m := 2) (by omega); omega, conductor_family le_rfl,
    (isStrong_family_iff le_rfl).2 (by omega), by have := numStrong_family le_rfl; omega⟩

/-- The pseudo-symmetric semigroup `Λ_{ps_3} = {0, 3} ∪ [5, ∞)` of Lemma
`lemma:357` of arXiv:0810.1619. -/
def ps3 : Set ℕ := {0, 3} ∪ Set.Ici 5

/-- Membership in `Λ_{ps_3}`. -/
theorem mem_ps3 {y : ℕ} : y ∈ ps3 ↔ y = 0 ∨ y = 3 ∨ 5 ≤ y := by
  simp [ps3, or_assoc]

/-- Lemma `lemma:357`(2) of arXiv:0810.1619: in `Λ_{ps_3} = {0, 3} ∪ [5, ∞)`
the effective generators are `5` and `7`; `5` is strong and `7` is weak. -/
theorem ps3_strong_weak :
    effectiveGenerators ps3 = {5, 7} ∧ IsStrong ps3 5 ∧ ¬ IsStrong ps3 7 := by
  have hc : conductor ps3 = 5 :=
    conductor_eq_of (fun _ hy => mem_ps3.2 (by omega)) (fun _ h => by rw [mem_ps3] at h; omega)
  have hm : multiplicity ps3 = 3 :=
    multiplicity_eq_of (mem_ps3.2 (by omega)) (by omega)
      (fun _ _ _ h => by rw [mem_ps3] at h; omega)
  have heff : effectiveGenerators ps3 = {5, 7} := by
    ext y
    simp only [effectiveGenerators, Set.mem_ofPred_eq, hc, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hy, hy0, hdec⟩, hcy⟩
      rw [mem_ps3] at hy
      by_contra hne
      exact hdec 3 (mem_ps3.2 (by omega)) (y - 3) (mem_ps3.2 (by omega)) (by omega)
        (by omega) (by omega)
    · intro h
      refine ⟨⟨mem_ps3.2 (by omega), by omega, fun a ha b hb ha0 hb0 => ?_⟩, by omega⟩
      rw [mem_ps3] at ha hb
      omega
  refine ⟨heff, ⟨by rw [heff]; exact Or.inl rfl, ?_⟩, ?_⟩
  · -- `ps3 \ {5} = {0, 3} ∪ [6, ∞)`: effective generators `7, 8`
    have hmem : ∀ y, y ∈ ps3 \ {5} ↔ (y = 0 ∨ y = 3 ∨ 6 ≤ y) := fun y => by
      rw [Set.mem_sdiff, mem_ps3, Set.mem_singleton_iff]
      omega
    have hc' : conductor (ps3 \ {5}) = 6 :=
      conductor_eq_of (fun _ hy => (hmem _).2 (by omega))
        (fun _ h => by rw [hmem] at h; omega)
    ext y
    rw [heff]
    simp only [effectiveGenerators, Set.mem_ofPred_eq, hc', hm, Set.mem_union,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hy, hy0, hdec⟩, hcy⟩
      rw [hmem] at hy
      by_contra hne
      exact hdec 3 ((hmem _).2 (by omega)) (y - 3) ((hmem _).2 (by omega)) (by omega)
        (by omega) (by omega)
    · intro h
      refine ⟨⟨(hmem _).2 (by omega), by omega, fun a ha b hb ha0 hb0 => ?_⟩, by omega⟩
      rw [hmem] at ha hb
      omega
  · -- `ps3 \ {7} = {0, 3, 5, 6} ∪ [8, ∞)` has no effective generator, so `10` is missing
    rintro ⟨-, heq⟩
    have h10 : (10 : ℕ) ∈ effectiveGenerators (ps3 \ {7}) := by
      rw [heq, hm]
      exact Or.inr rfl
    exact h10.1.2.2 5 ⟨mem_ps3.2 (by omega), by rw [Set.mem_singleton_iff]; omega⟩ 5
      ⟨mem_ps3.2 (by omega), by rw [Set.mem_singleton_iff]; omega⟩ (by omega) (by omega) rfl

-- Satisfiability of the hypotheses of `two_mul_numStrong_le_genus`, and sharpness:
-- `S_3 = {0, 3} ∪ [6, ∞)` is a non-ordinary numerical semigroup with `2 s = g = 4`.
example : IsNumericalSemigroup (family 3) ∧ multiplicity (family 3) < conductor (family 3) ∧
    2 * numStrong (family 3) = genus (family 3) := by
  obtain ⟨hS, hord, hg, hs, -⟩ := family_counterexample (m := 3) (by omega)
  exact ⟨hS, hord, by omega⟩

/-- **Sharpness of the corrected bound.**  For every `m ≥ 2` the semigroup
`S_m = {0, m} ∪ [2m, ∞)` attains `2 s = g`. -/
theorem two_mul_numStrong_family {m : ℕ} (hm : 2 ≤ m) :
    2 * numStrong (family m) = genus (family m) := by
  have hg := genus_family (by omega : 1 ≤ m)
  have hs := numStrong_family hm
  omega

/-- **Corrected conjecture, floor form.**  Every non-ordinary numerical
semigroup of genus `g` has at most `⌊g/2⌋` strong generators. -/
theorem numStrong_le_genus_div_two {S : Set ℕ} (hS : IsNumericalSemigroup S)
    (hmc : multiplicity S < conductor S) : numStrong S ≤ genus S / 2 := by
  have h := two_mul_numStrong_le_genus hS hmc
  omega

end SemigroupTreeStrongGenerators
