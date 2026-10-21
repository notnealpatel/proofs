/-
# Normalizer–solubilizer divisibility (Sabatini, arXiv:2610.03151, Theorem 1.1)

## Source

* arXiv:2610.03151, Luca Sabatini, *Arithmetic properties of solubilizers*
  (University of Warwick).  Retrieved 2026-10-21 with `fetch 2610.03151`.
* Statement location: Section 1, Theorem 1.1 (`thMain`); proof in Section 4
  ("Normalizers and the relative version"), after the figure.  The warm-up
  Theorem 3.1 (Hai-Reuven 2013, `thHR`) is in Section 3; the facts
  `N_G(x) ⊆ Sol_G(x)` and "`N_G(x)` normalizes `Sol_G(x)`" are in Section 2.
* Verbatim informal claim (Theorem 1.1):

  > Let $G$ be a finite group, $x \in G$, and $K \leqslant G$.  Then
  > $|N_G(x) \cap K|$ divides $|\mathrm{Sol}_G(x) \cap K|$.

  Here $\mathrm{Sol}_G(x) = \{g \in G : \langle x, g\rangle \text{ is soluble}\}$
  and $N_G(x)$ denotes the normalizer of $\langle x \rangle$.  The case $K = G$
  settles Conjecture 3 of Mousavi–Poozesh–Zamani (Ricerche Mat. 74 (2025)).
* Date of this formalization: 2026-10-21.
* Status in the source: **proved in the paper** (known result).  The only
  external input is the Cauchy–Frobenius counting lemma (Mathlib's
  `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`, used through
  `MulAction.sigmaFixedByEquivOrbitsProdGroup`).

## Formal rendering

* `solubilizer x : Set G` is `{g | Group.IsSolvable (closure {x, g})}`.
* `N_G(⟨x⟩)` is `Subgroup.normalizer (zpowers x : Set G)`.
* Cardinalities are `Nat.card` throughout; `G` is `[Finite G]`.

## Proof outline (as in the paper)

Strong induction on `|K|`.  With `H = N_G(⟨x⟩) ∩ K` and `A = Sol_G(x) ∩ K`,
choose `T ≤ H` maximal with `T ⊴ K` and `⟨x, a, T⟩` soluble for all `a ∈ A`.
Maximality forces `(H/T) ∩ Z(K/T) = 1`.  `A` is a union of `T`-cosets, and
`H/T` acts on `A/T` by conjugation.  For `1 ≠ h̄ ∈ H/T` the preimage `L` of
`C_{K/T}(h̄)` is a proper subgroup of `K`, so the induction hypothesis gives
`|C_{H/T}(h̄)| ∣ |Fix_{A/T}(h̄)|`, and the Cauchy–Frobenius lemma gives
`|H/T| ∣ |A/T|`.
-/
import Mathlib

set_option autoImplicit false

namespace GroupTPP.SolubilizerDivisibility

open MulAction

/-- Orbit–stabilizer form of the Cauchy–Frobenius lemma: for a finite group `P` acting on a
finite type `Y`, `|P|` divides `∑_{y ∈ Y} |Stab_P(y)|` (the quotient is the number of orbits). -/
theorem card_dvd_sum_card_stabilizer {P Y : Type*} [Group P] [Finite P] [MulAction P Y]
    [Fintype Y] : Nat.card P ∣ ∑ y : Y, Nat.card (stabilizer P y) := by
  rw [← Nat.card_sigma]
  let e : (Σ y : Y, stabilizer P y) ≃ (Quotient (orbitRel P Y)) × P :=
    ((Equiv.subtypeProdEquivSigmaSubtype fun (b : Y) a => a ∈ stabilizer P b).symm.trans
      ((Equiv.prodComm Y P).subtypeEquiv fun _ => Iff.rfl)).trans
      ((Equiv.subtypeProdEquivSigmaSubtype fun (g : P) (b : Y) => g • b = b).trans
        (sigmaFixedByEquivOrbitsProdGroup P Y))
  rw [Nat.card_congr e, Nat.card_prod]
  exact dvd_mul_left _ _

/-- Weighted Cauchy–Frobenius: if `f : X → ℕ` is constant on `P`-orbits, then `|P|` divides
`∑_{x ∈ X} |Stab_P(x)| · f(x)`.  Proved by applying `card_dvd_sum_card_stabilizer` to the
`P`-set `Σ x, Fin (f x)`. -/
theorem card_dvd_sum_card_stabilizer_mul {P X : Type*} [Group P] [Finite P] [MulAction P X]
    [Fintype X] (f : X → ℕ) (hf : ∀ (g : P) (x : X), f (g • x) = f x) :
    Nat.card P ∣ ∑ x : X, Nat.card (stabilizer P x) * f x := by
  let Y := Σ x : X, Fin (f x)
  letI act : MulAction P Y :=
    { smul := fun g y => ⟨g • y.1, Fin.cast (hf g y.1).symm y.2⟩
      one_smul := fun y => by
        refine Sigma.ext (one_smul P y.1) ?_
        exact (Fin.heq_ext_iff (hf 1 y.1)).2 rfl
      mul_smul := fun g h y => by
        refine Sigma.ext (mul_smul g h y.1) ?_
        exact (Fin.heq_ext_iff (congrArg f (mul_smul g h y.1))).2 rfl }
  have hstab : ∀ y : Y, stabilizer P y = stabilizer P y.1 := by
    intro y
    ext g
    simp only [mem_stabilizer_iff]
    constructor
    · intro h
      exact congrArg Sigma.fst h
    · intro h
      refine Sigma.ext h ?_
      exact (Fin.heq_ext_iff (congrArg f h)).2 rfl
  have key := card_dvd_sum_card_stabilizer (P := P) (Y := Y)
  rw [Fintype.sum_sigma] at key
  simpa [hstab, mul_comm] using key

/-- Abstract Hai-Reuven counting step.  Let a finite group `P` act on a finite type `B`.  If for
every `p ≠ 1` the order of the centralizer `C_P(p)` (the stabilizer of `p` under conjugation)
divides the number of fixed points of `p` on `B`, then `|P|` divides `|B|`.  This is the
Cauchy–Frobenius argument closing the proof of Theorem 1.1 in arXiv:2610.03151. -/
theorem card_dvd_card_of_dvd_card_fixedBy {P B : Type*} [Group P] [Finite P] [MulAction P B]
    [Finite B]
    (hdiv : ∀ p : P, p ≠ 1 → Nat.card (stabilizer (ConjAct P) p) ∣ Nat.card (fixedBy B p)) :
    Nat.card P ∣ Nat.card B := by
  classical
  haveI := Fintype.ofFinite P
  let ν : P → ℕ := fun p => Nat.card (fixedBy B p)
  let c : P → ℕ := fun p => Nat.card (stabilizer (ConjAct P) p)
  have hburn : Nat.card P ∣ ∑ p : P, ν p := by
    rw [← Nat.card_sigma, Nat.card_congr (sigmaFixedByEquivOrbitsProdGroup P B), Nat.card_prod]
    exact dvd_mul_left _ _
  have hν : ∀ (g : ConjAct P) (p : P), ν (g • p) = ν p := by
    intro g p
    simp only [ν, ConjAct.smul_def]
    rw [← smul_fixedBy, Set.natCard_smul_set]
  have hc : ∀ (g : ConjAct P) (p : P), c (g • p) = c p := fun g p =>
    Nat.card_congr (stabilizerEquivStabilizerOfOrbitRel (orbitRel_apply.mpr (mem_orbit p g))).toEquiv
  let f : P → ℕ := fun p => if p = 1 then 0 else ν p / c p
  have hf : ∀ (g : ConjAct P) (p : P), f (g • p) = f p := by
    intro g p
    have h1 : g • p = 1 ↔ p = 1 := by
      rw [ConjAct.smul_def, mul_inv_eq_one, mul_eq_left]
    simp only [f, h1, hν, hc]
  have hw := card_dvd_sum_card_stabilizer_mul (P := ConjAct P) (X := P) f hf
  have hcardP : Nat.card (ConjAct P) = Nat.card P := Nat.card_congr ConjAct.ofConjAct.toEquiv
  rw [hcardP] at hw
  have hterm : ∀ p : P, c p * f p = if p = 1 then 0 else ν p := by
    intro p
    by_cases hp : p = 1
    · simp [f, hp]
    · simp only [f, hp, if_false]
      exact Nat.mul_div_cancel' (hdiv p hp)
  have hsplit : ∑ p : P, ν p = Nat.card B + ∑ p : P, c p * f p := by
    have h1 : ∀ p : P, ν p = (if p = 1 then ν p else 0) + (if p = 1 then 0 else ν p) := by
      intro p
      by_cases hp : p = 1 <;> simp [hp]
    rw [Finset.sum_congr rfl (fun p _ => h1 p), Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (1 : P) ν]
    simp only [Finset.mem_univ, if_true, hterm]
    congr 1
    simp only [ν, fixedBy_one_eq_univ, Set.univ]
    exact Nat.card_univ
  rw [hsplit] at hburn
  exact (Nat.dvd_add_left hw).mp hburn

open Subgroup

/-- The solubilizer `Sol_G(x) = {g ∈ G | ⟨x, g⟩ is soluble}` (arXiv:2610.03151, §1). -/
def solubilizer {G : Type*} [Group G] (x : G) : Set G :=
  {g | Group.IsSolvable (closure ({x, g} : Set G))}

section helpers
variable {G : Type*} [Group G]

/-- A subgroup of a soluble subgroup is soluble. -/
theorem isSolvable_of_le {H H' : Subgroup G} (h : H ≤ H') [Group.IsSolvable H'] :
    Group.IsSolvable H :=
  Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h)

/-- If conjugation by every element of the subgroup `M` maps `U` into itself, then `M`
normalizes `U`. -/
theorem le_normalizer_of_conj_mem {M U : Subgroup G}
    (h : ∀ m ∈ M, ∀ u ∈ U, m * u * m⁻¹ ∈ U) : M ≤ normalizer (U : Set G) := by
  intro m hm
  rw [mem_normalizer_iff]
  intro u
  refine ⟨fun hu => h m hm u hu, fun hu => ?_⟩
  have h' := h m⁻¹ (inv_mem hm) _ hu
  simpa [mul_assoc] using h'

/-- The subgroup of elements `y` normalizing `U` with `g y g⁻¹ y⁻¹ ∈ U`. -/
def commSubgroup (U : Subgroup G) (g : G) : Subgroup G where
  carrier := {y | y ∈ normalizer (U : Set G) ∧ g * y * g⁻¹ * y⁻¹ ∈ U}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := by
    rintro y₁ y₂ ⟨hy₁, h₁⟩ ⟨hy₂, h₂⟩
    refine ⟨mul_mem hy₁ hy₂, ?_⟩
    have h₂' : y₁ * (g * y₂ * g⁻¹ * y₂⁻¹) * y₁⁻¹ ∈ U := (mem_normalizer_iff.mp hy₁ _).mp h₂
    have := mul_mem h₁ h₂'
    convert this using 1
    group
  inv_mem' := by
    rintro y ⟨hy, h⟩
    refine ⟨inv_mem hy, ?_⟩
    have h' : y⁻¹ * (g * y * g⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ ∈ U :=
      (mem_normalizer_iff.mp (inv_mem hy) _).mp (inv_mem h)
    convert h' using 1
    group

/-- If every element of `S` normalizes `U` and all commutators of pairs of elements of `S` lie
in `U`, then all commutators of pairs of elements of `⟨S⟩` lie in `U`. -/
theorem comm_mem_of_closure {U : Subgroup G} {S : Set G}
    (hSN : S ⊆ normalizer (U : Set G))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, s * s' * s⁻¹ * s'⁻¹ ∈ U) :
    ∀ g ∈ closure S, ∀ g' ∈ closure S, g * g' * g⁻¹ * g'⁻¹ ∈ U := by
  have step1 : ∀ s ∈ S, closure S ≤ commSubgroup U s := by
    intro s hs
    rw [closure_le]
    intro s' hs'
    exact ⟨hSN hs', hS s hs s' hs'⟩
  intro g hg
  have step2 : closure S ≤ commSubgroup U g := by
    rw [closure_le]
    intro s hs
    refine ⟨hSN hs, ?_⟩
    have h := (step1 s hs hg).2
    have h' := inv_mem h
    convert h' using 1
    group
  intro g' hg'
  exact (step2 hg').2

/-- If `U ≤ W`, `U` is soluble and every commutator of two elements of `W` lies in `U`, then
`W` is soluble (`W/U` is abelian). -/
theorem isSolvable_of_comm_mem {U W : Subgroup G} (hUW : U ≤ W) [Group.IsSolvable U]
    (hcomm : ∀ w₁ ∈ W, ∀ w₂ ∈ W, w₁ * w₂ * w₁⁻¹ * w₂⁻¹ ∈ U) : Group.IsSolvable W := by
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hUW) (Abelianization.of) ?_
  rw [Abelianization.ker_of, commutator_def, commutator_le]
  rintro w₁ - w₂ -
  refine ⟨⟨_, hcomm w₁ w₁.2 w₂ w₂.2⟩, ?_⟩
  ext
  simp [commutatorElement_def]

/-- `N_G(⟨x⟩)` normalizes `Sol_G(x)`: if `h` normalizes `⟨x⟩` and `g ∈ Sol_G(x)`, then
`h g h⁻¹ ∈ Sol_G(x)` (arXiv:2610.03151, §2). -/
theorem conj_mem_solubilizer {x h g : G} (hh : h ∈ normalizer (zpowers x : Set G))
    (hg : g ∈ solubilizer x) : h * g * h⁻¹ ∈ solubilizer x := by
  have hg' : Group.IsSolvable (closure ({x, g} : Set G)) := hg
  let f : G →* G := (MulAut.conj h).toMonoidHom
  have hinj : Function.Injective f := (MulAut.conj h).injective
  have hle : closure ({x, h * g * h⁻¹} : Set G) ≤ (closure ({x, g} : Set G)).map f := by
    rw [closure_le]
    intro y hy
    rcases hy with rfl | rfl
    · refine ⟨h⁻¹ * y * h, ?_, ?_⟩
      · have hx : h⁻¹ * y * h⁻¹⁻¹ ∈ zpowers y :=
          (mem_normalizer_iff.mp (inv_mem hh) y).mp (mem_zpowers y)
        have hz : zpowers y ≤ closure ({y, g} : Set G) :=
          zpowers_le.mpr (subset_closure (by simp))
        simpa using hz hx
      · simp [f, mul_assoc]
    · exact ⟨g, subset_closure (by simp), by simp [f]⟩
  let e := Subgroup.equivMapOfInjective (closure ({x, g} : Set G)) f hinj
  haveI : Group.IsSolvable ((closure ({x, g} : Set G)).map f) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  exact isSolvable_of_le hle

end helpers

/-! ## Ground truth for `solubilizer` -/

section groundTruth
variable {G : Type*} [Group G]

/-- If `s` normalizes `U` and `s' ∈ U`, both commutators `[s, s']` and `[s', s]` lie in `U`. -/
theorem comm_mem_of_mem_normalizer {U : Subgroup G} {s s' : G}
    (hs : s ∈ normalizer (U : Set G)) (hs' : s' ∈ U) :
    s * s' * s⁻¹ * s'⁻¹ ∈ U ∧ s' * s * s'⁻¹ * s⁻¹ ∈ U := by
  have h1 : s * s' * s⁻¹ ∈ U := (mem_normalizer_iff.mp hs s').mp hs'
  have h2 : s * s'⁻¹ * s⁻¹ ∈ U := (mem_normalizer_iff.mp hs _).mp (inv_mem hs')
  refine ⟨mul_mem h1 (inv_mem hs'), ?_⟩
  have h3 := mul_mem hs' h2
  simpa [mul_assoc] using h3

/-- `N_G(⟨x⟩) ⊆ Sol_G(x)` (arXiv:2610.03151, §2: `⟨x, h⟩` is metacyclic for
`h ∈ N_G(⟨x⟩)`). -/
theorem normalizer_subset_solubilizer (x : G) :
    (normalizer (zpowers x : Set G) : Set G) ⊆ solubilizer x := by
  intro g hg
  have hUW : zpowers x ≤ closure ({x, g} : Set G) :=
    zpowers_le.mpr (subset_closure (Set.mem_insert x _))
  haveI : Group.IsSolvable ↥(zpowers x) := Group.isSolvable_of_comm fun a b => by
    obtain ⟨a, m, rfl⟩ := a
    obtain ⟨b, n, rfl⟩ := b
    exact Subtype.ext (Commute.zpow_zpow_self x m n).eq
  have hxN : x ∈ normalizer (zpowers x : Set G) := le_normalizer (mem_zpowers x)
  have hcomm := comm_mem_of_closure (U := zpowers x) (S := ({x, g} : Set G))
    (by
      rintro s (rfl | rfl)
      · exact hxN
      · exact hg)
    (by
      intro s hs s' hs'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs hs'
      rcases hs with hs | hs <;> rcases hs' with hs' | hs' <;> rw [hs, hs']
      · exact (comm_mem_of_mem_normalizer hxN (mem_zpowers x)).1
      · exact (comm_mem_of_mem_normalizer hg (mem_zpowers x)).2
      · exact (comm_mem_of_mem_normalizer hg (mem_zpowers x)).1
      · simp)
  exact isSolvable_of_comm_mem hUW hcomm

/-- Every element lies in its own solubilizer. -/
theorem mem_solubilizer_self (x : G) : x ∈ solubilizer x :=
  normalizer_subset_solubilizer x (le_normalizer (mem_zpowers x))

/-- In a soluble group the solubilizer of every element is the whole group. -/
theorem solubilizer_eq_univ [Group.IsSolvable G] (x : G) : solubilizer x = Set.univ :=
  Set.eq_univ_of_forall fun g => (inferInstance : Group.IsSolvable ↥(closure ({x, g} : Set G)))

end groundTruth

/-- Ground truth: in `S₅` the transposition `(0 1)` is not in the solubilizer of the 5-cycle
`finRotate 5`, because the two generate `S₅`, which is not soluble.  So `solubilizer` is a
proper subset in non-soluble groups. -/
example : Equiv.swap (0 : Fin 5) (finRotate 5 0) ∉ solubilizer (finRotate 5) := by
  intro h
  have htop : closure ({finRotate 5, Equiv.swap (0 : Fin 5) (finRotate 5 0)} :
      Set (Equiv.Perm (Fin 5))) = ⊤ :=
    Equiv.Perm.closure_cycle_adjacent_swap (isCycle_finRotate (n := 3))
      (support_finRotate (n := 3)) 0
  have h' : Group.IsSolvable ↥(⊤ : Subgroup (Equiv.Perm (Fin 5))) := htop ▸ h
  let e : ↥(⊤ : Subgroup (Equiv.Perm (Fin 5))) ≃* Equiv.Perm (Fin 5) := Subgroup.topEquiv
  exact Equiv.Perm.not_isSolvable_fin_5
    (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

/-- Ground truth: the 5-cycle lies in its own solubilizer in `S₅`. -/
example : finRotate 5 ∈ solubilizer (finRotate 5) := mem_solubilizer_self _

section counting
variable {G : Type*} [Group G]

/-- If `T ≤ K` and `S ⊆ K` is a union of left `T`-cosets, then `|S| = |T| · |S/T|`, where
`S/T` is the image of `S` in the coset space `K ⧸ T`. -/
theorem card_eq_card_mul_card_image {K T : Subgroup G} (hTK : T ≤ K) {S : Set G}
    (hSK : S ⊆ K) (hsat : ∀ s ∈ S, ∀ t ∈ T, s * t ∈ S) :
    Nat.card S = Nat.card T *
      Nat.card ((QuotientGroup.mk : K → K ⧸ T.subgroupOf K) '' {k : K | (k : G) ∈ S}) := by
  set S' : Set K := {k : K | (k : G) ∈ S} with hS'
  have h1 : Nat.card S = Nat.card S' := Nat.card_congr
    { toFun := fun s => ⟨⟨s.1, hSK s.2⟩, s.2⟩
      invFun := fun k => ⟨k.1.1, k.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h2 : S' = (QuotientGroup.mk : K → K ⧸ T.subgroupOf K) ⁻¹'
      ((QuotientGroup.mk : K → K ⧸ T.subgroupOf K) '' S') := by
    refine (Set.subset_preimage_image _ _).antisymm ?_
    rintro k ⟨k', hk', hkk'⟩
    have hq : k'⁻¹ * k ∈ T.subgroupOf K := QuotientGroup.eq.mp hkk'
    have hk : (k : G) = k' * ((k'⁻¹ * k : K) : G) := by simp
    show (k : G) ∈ S
    rw [hk]
    exact hsat _ hk' _ (mem_subgroupOf.mp hq)
  have h3 : Nat.card (T.subgroupOf K) = Nat.card T :=
    Nat.card_congr (subgroupOfEquivOfLe hTK).toEquiv
  rw [h1]
  conv_lhs => rw [h2]
  rw [QuotientGroup.card_preimage_mk, h3]

end counting

section main
variable {G : Type*} [Group G] [Finite G]

/-- Inductive step of Theorem 1.1 of arXiv:2610.03151: if the divisibility
`|N_G(⟨x⟩) ∩ L| ∣ |Sol_G(x) ∩ L|` holds for every subgroup `L` with `|L| < |K|`, then it holds
for `K`.  The proof follows the paper: choose `T ≤ N_G(⟨x⟩) ∩ K` maximal with `T ⊴ K` and
`⟨x, a, T⟩` soluble for all `a ∈ Sol_G(x) ∩ K`, show `(H/T) ∩ Z(K/T) = 1`, and count fixed
points of `H/T` acting on `A/T` by conjugation. -/
theorem card_dvd_of_forall_card_lt (x : G) (K : Subgroup G)
    (ih : ∀ L : Subgroup G, Nat.card L < Nat.card K →
      Nat.card ↥(normalizer (zpowers x : Set G) ⊓ L) ∣ Nat.card ↥(solubilizer x ∩ (L : Set G))) :
    Nat.card ↥(normalizer (zpowers x : Set G) ⊓ K) ∣
      Nat.card ↥(solubilizer x ∩ (K : Set G)) := by
  classical
  set N := normalizer (zpowers x : Set G)
  -- `Good T`: `T ≤ N ∩ K`, `T ⊴ K`, and `⟨x, a, T⟩` soluble for every `a ∈ Sol_G(x) ∩ K`.
  let Good : Subgroup G → Prop := fun T => T ≤ N ⊓ K ∧ K ≤ normalizer (T : Set G) ∧
      ∀ a ∈ solubilizer x, a ∈ K → Group.IsSolvable ↥(closure ({x, a} : Set G) ⊔ T)
  have hbot : Good ⊥ := by
    refine ⟨bot_le, ?_, fun a ha _ => ?_⟩
    · rw [normalizer_eq_top_iff.mpr inferInstance]
      exact le_top
    · rw [sup_bot_eq]
      exact ha
  obtain ⟨T, hT⟩ : ∃ T, Maximal Good T :=
    Set.Finite.exists_maximal (Set.toFinite {T | Good T}) ⟨⊥, hbot⟩
  obtain ⟨hTH, hKT, hTsol⟩ := hT.1
  have hTK : T ≤ K := hTH.trans inf_le_right
  have hTN : T ≤ N := hTH.trans inf_le_left
  haveI hnorm : (T.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer hTK).mpr hKT
  let mk : K →* K ⧸ T.subgroupOf K := QuotientGroup.mk' (T.subgroupOf K)
  have hmk1 : ∀ k : K, mk k = 1 ↔ (k : G) ∈ T := fun k =>
    (QuotientGroup.eq_one_iff k).trans mem_subgroupOf
  have hcommT : ∀ d k : K, (∀ q, q * mk d = mk d * q) → ((d * k * d⁻¹ * k⁻¹ : K) : G) ∈ T := by
    intro d k hd
    rw [← hmk1, map_mul, map_mul, map_mul, map_inv, map_inv, ← hd (mk k)]
    group
  -- Claim (eqClaim): `(H/T) ∩ Z(K/T) = 1`.
  have hclaim : ∀ h : K, (h : G) ∈ N → (∀ q, q * mk h = mk h * q) → (h : G) ∈ T := by
    intro h hhN hhc
    let D : Subgroup G := N ⊓ ((Subgroup.center (K ⧸ T.subgroupOf K)).comap mk).map K.subtype
    have hDK : D ≤ K := inf_le_right.trans (map_subtype_le _)
    have hmemD : ∀ d : K, (d : G) ∈ D ↔ (d : G) ∈ N ∧ ∀ q, q * mk d = mk d * q := by
      intro d
      rw [mem_inf]
      refine and_congr Iff.rfl ?_
      rw [show (d : G) = K.subtype d from rfl, mem_map_iff_mem K.subtype_injective, mem_comap,
        mem_center_iff]
    have hTD : T ≤ D := by
      intro t ht
      have ht' : ((⟨t, hTK ht⟩ : K) : G) ∈ D := by
        rw [hmemD]
        refine ⟨hTN ht, fun q => ?_⟩
        rw [(hmk1 _).mpr ht, one_mul, mul_one]
      exact ht'
    have hDgood : Good D := by
      refine ⟨le_inf inf_le_left hDK, ?_, ?_⟩
      · refine le_normalizer_of_conj_mem fun k hk d hd => ?_
        lift d to K using hDK hd
        obtain ⟨hdN, hdc⟩ := (hmemD d).mp hd
        let k' : K := ⟨k, hk⟩
        have hkd : k * (d : G) * k⁻¹ = ((k' * d * k'⁻¹ : K) : G) := rfl
        rw [hkd, hmemD]
        refine ⟨?_, fun q => ?_⟩
        · have hT1 : ((d * k' * d⁻¹ * k'⁻¹ : K) : G) ∈ T := hcommT d k' hdc
          have heq : ((k' * d * k'⁻¹ : K) : G) =
              ((d * k' * d⁻¹ * k'⁻¹ : K) : G)⁻¹ * (d : G) := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
            group
          rw [heq]
          exact mul_mem (inv_mem (hTN hT1)) hdN
        · have hc : mk (k' * d * k'⁻¹) = mk d := by
            rw [map_mul, map_mul, map_inv, hdc (mk k')]
            group
          rw [hc]
          exact hdc q
      · intro a ha haK
        haveI hU : Group.IsSolvable ↥(closure ({x, a} : Set G) ⊔ T) := hTsol a ha haK
        set U := closure ({x, a} : Set G) ⊔ T with hUdef
        have hUW : U ≤ closure ({x, a} : Set G) ⊔ D := sup_le_sup_left hTD _
        have hTU : T ≤ U := le_sup_right
        have hDN : D ≤ normalizer (U : Set G) := by
          refine le_normalizer_of_conj_mem fun d hd u hu => ?_
          lift d to K using hDK hd
          obtain ⟨hdN, hdc⟩ := (hmemD d).mp hd
          let f : G →* G := (MulAut.conj (d : G)).toMonoidHom
          have hle : U ≤ U.comap f := by
            refine sup_le ?_ ?_
            · rw [closure_le]
              intro y hy
              rcases hy with rfl | rfl
              · have hx : (d : G) * y * (d : G)⁻¹ ∈ zpowers y :=
                  (mem_normalizer_iff.mp hdN y).mp (mem_zpowers y)
                have hz : zpowers y ≤ U :=
                  zpowers_le.mpr (le_sup_left (a := closure ({y, a} : Set G))
                    (subset_closure (by simp)))
                simpa [f] using hz hx
              · let a' : K := ⟨y, haK⟩
                have hT1 : ((d * a' * d⁻¹ * a'⁻¹ : K) : G) ∈ T := hcommT d a' hdc
                have heq : f y = ((d * a' * d⁻¹ * a'⁻¹ : K) : G) * y := by
                  simp only [f, a', Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.coe_toMonoidHom,
                    MulAut.conj_apply]
                  group
                rw [SetLike.mem_coe, mem_comap, heq]
                exact mul_mem (hTU hT1)
                  (le_sup_left (a := closure ({x, y} : Set G)) (subset_closure (by simp)))
            · intro t ht
              rw [mem_comap]
              exact hTU ((mem_normalizer_iff.mp (hKT d.2) t).mp ht)
          exact hle hu
        have hS : closure ((U : Set G) ∪ (D : Set G)) = closure ({x, a} : Set G) ⊔ D := by
          rw [Subgroup.closure_union, closure_eq, closure_eq, hUdef, sup_assoc, sup_eq_right.mpr hTD]
        have hcomm := comm_mem_of_closure (U := U) (S := (U : Set G) ∪ (D : Set G))
          (Set.union_subset le_normalizer hDN) (by
            rintro s (hs | hs) s' (hs' | hs')
            · exact mul_mem (mul_mem (mul_mem hs hs') (inv_mem hs)) (inv_mem hs')
            · exact (comm_mem_of_mem_normalizer (hDN hs') hs).2
            · exact (comm_mem_of_mem_normalizer (hDN hs) hs').1
            · lift s to K using hDK hs
              lift s' to K using hDK hs'
              exact hTU (hcommT s s' ((hmemD s).mp hs).2))
        rw [hS] at hcomm
        exact isSolvable_of_comm_mem hUW hcomm
    exact hT.2 hDgood hTD ((hmemD h).mpr ⟨hhN, hhc⟩)
  have hsatN : ∀ M : Subgroup G, T ≤ M → ∀ s ∈ ((N ⊓ M : Subgroup G) : Set G), ∀ t ∈ T,
      s * t ∈ ((N ⊓ M : Subgroup G) : Set G) :=
    fun M hTM s hs t ht => mul_mem hs (mem_inf.mpr ⟨hTN ht, hTM ht⟩)
  have hsatSol : ∀ M : Subgroup G, T ≤ M → M ≤ K → ∀ s ∈ solubilizer x ∩ (M : Set G),
      ∀ t ∈ T, s * t ∈ solubilizer x ∩ (M : Set G) := by
    rintro M hTM hMK s ⟨hs, hsM⟩ t ht
    refine ⟨?_, mul_mem hsM (hTM ht)⟩
    haveI := hTsol s hs (hMK hsM)
    have hle : closure ({x, s * t} : Set G) ≤ closure ({x, s} : Set G) ⊔ T := by
      rw [closure_le]
      rintro y (rfl | rfl)
      · exact le_sup_left (a := closure ({y, s} : Set G)) (subset_closure (by simp))
      · exact mul_mem (le_sup_left (a := closure ({x, s} : Set G)) (subset_closure (by simp)))
          (le_sup_right (a := closure ({x, s} : Set G)) ht)
    exact isSolvable_of_le hle
  have hcount : ∀ S : Set G, S ⊆ K → (∀ s ∈ S, ∀ t ∈ T, s * t ∈ S) →
      Nat.card S = Nat.card T * Nat.card (mk '' {k : K | (k : G) ∈ S}) :=
    fun S hSK hsat => card_eq_card_mul_card_image hTK hSK hsat
  let P : Subgroup (K ⧸ T.subgroupOf K) := (N.subgroupOf K).map mk
  let B : Set (K ⧸ T.subgroupOf K) := mk '' {k : K | (k : G) ∈ solubilizer x}
  have hPset : (P : Set (K ⧸ T.subgroupOf K)) =
      mk '' {k : K | (k : G) ∈ ((N ⊓ K : Subgroup G) : Set G)} := by
    rw [coe_map, coe_subgroupOf]
    congr 1
    ext k
    simp
  have hBset : B = mk '' {k : K | (k : G) ∈ solubilizer x ∩ (K : Set G)} := by
    show mk '' {k : K | (k : G) ∈ solubilizer x} = _
    congr 1
    ext k
    simp
  have hcardH : Nat.card ↥(N ⊓ K) = Nat.card T * Nat.card P := by
    have h := hcount ((N ⊓ K : Subgroup G) : Set G) (fun g hg => (mem_inf.mp hg).2)
      (hsatN K hTK)
    rw [← hPset] at h
    exact h
  have hcardA : Nat.card ↥(solubilizer x ∩ (K : Set G)) = Nat.card T * Nat.card B := by
    have h := hcount (solubilizer x ∩ (K : Set G)) (fun g hg => hg.2) (hsatSol K hTK le_rfl)
    rw [← hBset] at h
    exact h
  have hdivPB : Nat.card P ∣ Nat.card B := by
    have hPB : ∀ p ∈ P, ∀ b ∈ B, p * b * p⁻¹ ∈ B := by
      rintro p ⟨h, hh, rfl⟩ b ⟨k, hk, rfl⟩
      refine ⟨h * k * h⁻¹, ?_, by simp only [map_mul, map_inv]⟩
      show ((h * k * h⁻¹ : K) : G) ∈ solubilizer x
      simpa using conj_mem_solubilizer (mem_subgroupOf.mp hh) hk
    letI : MulAction P B :=
      { smul := fun p b => ⟨(p : K ⧸ T.subgroupOf K) * b * (p : K ⧸ T.subgroupOf K)⁻¹,
          hPB p p.2 b b.2⟩
        one_smul := fun b => Subtype.ext (by
          show ((1 : P) : K ⧸ T.subgroupOf K) * b * ((1 : P) : K ⧸ T.subgroupOf K)⁻¹ = b
          simp)
        mul_smul := fun p q b => Subtype.ext (by
          show ((p * q : P) : K ⧸ T.subgroupOf K) * b * ((p * q : P) : K ⧸ T.subgroupOf K)⁻¹ =
            (p : K ⧸ T.subgroupOf K) * ((q : K ⧸ T.subgroupOf K) * b *
              (q : K ⧸ T.subgroupOf K)⁻¹) * (p : K ⧸ T.subgroupOf K)⁻¹
          simp only [coe_mul, mul_inv_rev]
          group) }
    refine card_dvd_card_of_dvd_card_fixedBy (P := P) (B := B) fun p hp => ?_
    obtain ⟨h, hhN, hhp⟩ := p.2
    set p₀ : K ⧸ T.subgroupOf K := (p : K ⧸ T.subgroupOf K) with hp₀
    let L : Subgroup G := ((centralizer {p₀}).comap mk).map K.subtype
    have hLK : L ≤ K := map_subtype_le _
    have hmemL : ∀ k : K, (k : G) ∈ L ↔ mk k * p₀ = p₀ * mk k := by
      intro k
      rw [show (k : G) = K.subtype k from rfl, mem_map_iff_mem K.subtype_injective, mem_comap,
        mem_centralizer_singleton_iff]
    have hTL : T ≤ L := by
      intro t ht
      have ht' : ((⟨t, hTK ht⟩ : K) : G) ∈ L := by
        rw [hmemL, (hmk1 _).mpr ht, one_mul, mul_one]
      exact ht'
    have hLlt : Nat.card L < Nat.card K := by
      refine lt_of_le_of_ne (card_le_of_le hLK) fun heq => hp ?_
      have hLeq : L = K := eq_of_le_of_card_ge hLK heq.ge
      have hcen : ∀ q, q * mk h = mk h * q := by
        intro q
        obtain ⟨k, hkq⟩ := QuotientGroup.mk'_surjective (T.subgroupOf K) q
        have hk : (k : G) ∈ L := by rw [hLeq]; exact k.2
        rw [hmemL] at hk
        rw [← hkq, hhp]
        exact hk
      have hhT := hclaim h (mem_subgroupOf.mp hhN) hcen
      apply Subtype.ext
      rw [OneMemClass.coe_one, ← hp₀, ← hhp]
      exact (hmk1 h).mpr hhT
    have hih := ih L hLlt
    have hc1 : Nat.card ↥(N ⊓ L) = _ :=
      hcount ((N ⊓ L : Subgroup G) : Set G) (fun g hg => hLK (mem_inf.mp hg).2) (hsatN L hTL)
    have hc2 := hcount (solubilizer x ∩ (L : Set G)) (fun g hg => hLK hg.2)
      (hsatSol L hTL hLK)
    have hstab : Nat.card (MulAction.stabilizer (ConjAct P) p) =
        Nat.card (mk '' {k : K | (k : G) ∈ ((N ⊓ L : Subgroup G) : Set G)}) := by
      have e1 : ↥(MulAction.stabilizer (ConjAct P) p) ≃ {q : P // q * p * q⁻¹ = p} :=
        Equiv.subtypeEquiv ConjAct.ofConjAct.toEquiv (fun c => by
          rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def]
          rfl)
      have e2 : {q : P // q * p * q⁻¹ = p} ≃
          {q : K ⧸ T.subgroupOf K // q ∈ P ∧ q * p₀ * q⁻¹ = p₀} :=
        (Equiv.subtypeEquivRight (fun q => by
          rw [Subtype.ext_iff]
          simp only [coe_mul, coe_inv, hp₀])).trans
          (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ P) (fun q => q * p₀ * q⁻¹ = p₀))
      have hset : {q : K ⧸ T.subgroupOf K | q ∈ P ∧ q * p₀ * q⁻¹ = p₀} =
          mk '' {k : K | (k : G) ∈ ((N ⊓ L : Subgroup G) : Set G)} := by
        ext q
        constructor
        · rintro ⟨⟨k, hk, rfl⟩, hc⟩
          exact ⟨k, mem_inf.mpr ⟨mem_subgroupOf.mp hk, (hmemL k).mpr
            (mul_inv_eq_iff_eq_mul.mp hc)⟩, rfl⟩
        · rintro ⟨k, hk, rfl⟩
          exact ⟨⟨k, mem_subgroupOf.mpr (mem_inf.mp hk).1, rfl⟩,
            mul_inv_eq_iff_eq_mul.mpr ((hmemL k).mp (mem_inf.mp hk).2)⟩
      rw [Nat.card_congr (e1.trans e2), ← hset]
      rfl
    have hfix : Nat.card (MulAction.fixedBy B p) =
        Nat.card (mk '' {k : K | (k : G) ∈ solubilizer x ∩ (L : Set G)}) := by
      have e1 : ↥(MulAction.fixedBy B p) ≃
          {q : K ⧸ T.subgroupOf K // q ∈ B ∧ p₀ * q * p₀⁻¹ = q} :=
        (Equiv.subtypeEquivRight (fun b => by
          rw [MulAction.mem_fixedBy, Subtype.ext_iff]
          rfl)).trans
          (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ B) (fun q => p₀ * q * p₀⁻¹ = q))
      have hset : {q : K ⧸ T.subgroupOf K | q ∈ B ∧ p₀ * q * p₀⁻¹ = q} =
          mk '' {k : K | (k : G) ∈ solubilizer x ∩ (L : Set G)} := by
        ext q
        constructor
        · rintro ⟨⟨k, hk, rfl⟩, hc⟩
          exact ⟨k, ⟨hk, (hmemL k).mpr (mul_inv_eq_iff_eq_mul.mp hc).symm⟩, rfl⟩
        · rintro ⟨k, ⟨hk, hkL⟩, rfl⟩
          exact ⟨⟨k, hk, rfl⟩, mul_inv_eq_iff_eq_mul.mpr ((hmemL k).mp hkL).symm⟩
      rw [Nat.card_congr e1, ← hset]
      rfl
    rw [hstab, hfix]
    rw [hc1, hc2] at hih
    exact Nat.dvd_of_mul_dvd_mul_left Nat.card_pos hih
  rw [hcardH, hcardA]
  exact mul_dvd_mul_left _ hdivPB

/-- **Theorem 1.1** (Sabatini, arXiv:2610.03151).  Let `G` be a finite group, `x ∈ G` and
`K ≤ G`.  Then `|N_G(⟨x⟩) ∩ K|` divides `|Sol_G(x) ∩ K|`, where
`Sol_G(x) = {g ∈ G | ⟨x, g⟩ is soluble}`. -/
theorem card_normalizer_inf_dvd_card_solubilizer_inter (x : G) (K : Subgroup G) :
    Nat.card ↥(normalizer (zpowers x : Set G) ⊓ K) ∣
      Nat.card ↥(solubilizer x ∩ (K : Set G)) := by
  induction hK : Nat.card K using Nat.strong_induction_on generalizing K with
  | _ n ih => exact card_dvd_of_forall_card_lt x K fun L hL => ih _ (hK ▸ hL) L rfl

/-- `thm_1_1`: stable alias of Theorem 1.1 of arXiv:2610.03151. -/
theorem thm_1_1 (x : G) (K : Subgroup G) :
    Nat.card ↥(normalizer (zpowers x : Set G) ⊓ K) ∣
      Nat.card ↥(solubilizer x ∩ (K : Set G)) :=
  card_normalizer_inf_dvd_card_solubilizer_inter x K

/-- The normalizer–solubilizer conjecture of Mousavi, Poozesh and Zamani
(Ricerche Mat. 2025, Conjecture 3), the case `K = G` of Theorem 1.1 of arXiv:2610.03151:
`|N_G(⟨x⟩)|` divides `|Sol_G(x)|`. -/
theorem card_normalizer_dvd_card_solubilizer (x : G) :
    Nat.card ↥(normalizer (zpowers x : Set G)) ∣ Nat.card ↥(solubilizer x) := by
  have h := card_normalizer_inf_dvd_card_solubilizer_inter x ⊤
  rwa [inf_top_eq, coe_top, Set.inter_univ] at h

/-- Hai-Reuven's theorem (arXiv:2610.03151, Theorem 3.1): `|C_G(x)|` divides `|Sol_G(x)|`.
Derived here from `card_normalizer_dvd_card_solubilizer` since `C_G(x) ≤ N_G(⟨x⟩)`. -/
theorem card_centralizer_dvd_card_solubilizer (x : G) :
    Nat.card ↥(centralizer ({x} : Set G)) ∣ Nat.card ↥(solubilizer x) := by
  have hle : centralizer ({x} : Set G) ≤ normalizer (zpowers x : Set G) := by
    intro c hc
    rw [mem_normalizer_iff]
    intro y
    have hcx : c * x = x * c := mem_centralizer_singleton_iff.mp hc
    have hconj : ∀ n : ℤ, c * x ^ n * c⁻¹ = x ^ n := fun n => by
      rw [((Commute.zpow_right hcx n)).eq, mul_inv_cancel_right]
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, (hconj n).symm⟩
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have hn' : x ^ n = c * y * c⁻¹ := hn
      have h1 : c * y * c⁻¹ = c * x ^ n * c⁻¹ := by rw [hconj n]; exact hn'.symm
      exact (mul_left_cancel (mul_right_cancel h1)).symm
  exact (card_dvd_of_le hle).trans (card_normalizer_dvd_card_solubilizer x)

end main

end GroupTPP.SolubilizerDivisibility
