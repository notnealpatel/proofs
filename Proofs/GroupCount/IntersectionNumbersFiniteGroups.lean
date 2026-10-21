/-
# Intersection numbers of finite groups: `ι(G) < |m(G)|` for noncyclic `G`

## Source

arXiv:1907.02898, "On the Intersection Numbers of Finite Groups", by Kassie
Archer, Humberto Bautista Serrano, Kayla Cook, L.-K. Lauderdale, Yesenia Perez,
and Valerie Villalobos.  Section "Discussion and Open Questions"
(`sec:OPEN QUESTIONS`), third question, stated after Theorem `LOWERBOUND`
(Lauderdale 2013: `|m(G)| ≥ |π(G)|`, with equality iff `G` is cyclic).

Definition (introduction, verbatim): "For a nontrivial group `G`, we define the
intersection number of `G`, denoted `ι(G)`, to be the minimum number of maximal
subgroups whose intersection is `Φ(G)`."  The paper writes `m(G)` for the set
of maximal subgroups of `G`.

Question (verbatim): "Does the inequality `ι(G) < |m(G)|` hold for all noncyclic
groups `G`?"  The surrounding text adds: "It is clear that `ι(G) ≤ |m(G)|`."

Recorded 2026-10-21.  Status in the paper: OPEN (posed as a question).

## Result of this module

The question is answered affirmatively for all finite groups, together with the
characterization `ι(G) = |m(G)| ↔ G` cyclic (`intersectionNumber_eq_ncard_iff`).
The load-bearing step (`exists_redundant_maximal`) is: a finite group in which
every maximal subgroup `M` is irredundant (some `x_M` lies in every other maximal
subgroup but not in `M`) is cyclic, because the product of all the `x_M` lies in
no maximal subgroup.  Conversely, in a finite cyclic group every maximal
subgroup is irredundant (a Sylow argument, `irredundant_of_isCyclic`).

Computational evidence gathered before formalization (SageMath/libgap): every
noncyclic SmallGroup of order `2..127` (643 groups up to order 80 at triage,
498 further groups of order `81..127` here) has a maximal subgroup containing
the intersection of all the other maximal subgroups.

Conventions.  `ι` is stated for every group via `sInf` over the set of sizes of
finite families of maximal subgroups with intersection `Φ(G)`; for finite `G`
this set is nonempty (`isFrattiniFamily_coatoms`), so the `sInf` is a genuine
minimum.  For the trivial group (excluded by the paper) both sides are `0`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.IntersectionNumbersFiniteGroups

/-! ## Definitions -/

/-- `m(G)`: the set of maximal subgroups of `G`, i.e. the coatoms of the
subgroup lattice. -/
def maximalSubgroups (G : Type*) [Group G] : Set (Subgroup G) :=
  {K | IsCoatom K}

/-- A finite family `S` of maximal subgroups of `G` whose intersection is the
Frattini subgroup `Φ(G)`. -/
def IsFrattiniFamily {G : Type*} [Group G] (S : Finset (Subgroup G)) : Prop :=
  (∀ K ∈ S, IsCoatom K) ∧ S.inf id = frattini G

/-- The intersection number `ι(G)`: the minimum number of maximal subgroups of
`G` whose intersection is `Φ(G)`. -/
noncomputable def intersectionNumber (G : Type*) [Group G] : ℕ :=
  sInf {k : ℕ | ∃ S : Finset (Subgroup G), IsFrattiniFamily S ∧ S.card = k}

variable {G : Type*} [Group G]

/-! ## General facts -/

/-- Every element of a subgroup `H` satisfies `x ^ |H| = 1`. -/
theorem pow_card_eq_one_of_mem {H : Subgroup G} {x : G} (hx : x ∈ H) :
    x ^ Nat.card H = 1 := by
  have h : (⟨x, hx⟩ : H) ^ Nat.card H = 1 := pow_card_eq_one'
  have hval := congrArg Subtype.val h
  simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using hval

/-- For finite `G`, `m(G)` is a finite set. -/
theorem maximalSubgroups_finite [Finite G] : (maximalSubgroups G).Finite :=
  Set.toFinite _

/-- Membership in the finset of all maximal subgroups. -/
theorem mem_maximalSubgroups_toFinset [Finite G] {K : Subgroup G} :
    K ∈ (maximalSubgroups_finite (G := G)).toFinset ↔ IsCoatom K := by
  rw [Set.Finite.mem_toFinset]
  rfl

/-- For finite `G`, the family of all maximal subgroups has intersection
`Φ(G)`. -/
theorem isFrattiniFamily_coatoms [Finite G] :
    IsFrattiniFamily (maximalSubgroups_finite (G := G)).toFinset := by
  refine ⟨fun K hK => mem_maximalSubgroups_toFinset.mp hK, le_antisymm ?_ ?_⟩
  · refine le_iInf₂ fun K hK => ?_
    exact Finset.inf_le (f := id) (mem_maximalSubgroups_toFinset.mpr hK)
  · exact Finset.le_inf fun K hK => frattini_le_coatom (mem_maximalSubgroups_toFinset.mp hK)

/-- If `S` is a family of maximal subgroups with intersection `Φ(G)`, then
`ι(G) ≤ |S|`. -/
theorem intersectionNumber_le_card {S : Finset (Subgroup G)} (hS : IsFrattiniFamily S) :
    intersectionNumber G ≤ S.card :=
  Nat.sInf_le ⟨S, hS, rfl⟩

/-- `ι(G) ≤ |m(G)|` for every finite group `G`. -/
theorem intersectionNumber_le_ncard [Finite G] :
    intersectionNumber G ≤ (maximalSubgroups G).ncard := by
  rw [Set.ncard_eq_toFinset_card _ maximalSubgroups_finite]
  exact intersectionNumber_le_card isFrattiniFamily_coatoms

/-! ## The load-bearing step: noncyclic groups have a redundant maximal subgroup -/

/-- Given a choice `f M` of a witness of irredundancy for every maximal subgroup
`M`, the product of `f` along a duplicate-free list `L` of maximal subgroups
lies in a maximal subgroup `M` exactly when `M` is not in `L`. -/
theorem prod_map_mem_iff (f : Subgroup G → G)
    (hf : ∀ M : Subgroup G, IsCoatom M →
      (∀ K : Subgroup G, IsCoatom K → K ≠ M → f M ∈ K) ∧ f M ∉ M)
    (L : List (Subgroup G)) (hL : L.Nodup) (hLc : ∀ K ∈ L, IsCoatom K)
    (M : Subgroup G) (hM : IsCoatom M) :
    (L.map f).prod ∈ M ↔ M ∉ L := by
  induction L with
  | nil => simp [M.one_mem]
  | cons K L ih =>
    rw [List.nodup_cons] at hL
    have ih' := ih hL.2 (fun K' hK' => hLc K' (List.mem_cons_of_mem _ hK'))
    have hK : IsCoatom K := hLc K List.mem_cons_self
    rw [List.map_cons, List.prod_cons, List.mem_cons]
    by_cases hKM : M = K
    · subst hKM
      have hprod : (L.map f).prod ∈ M := ih'.2 hL.1
      rw [Subgroup.mul_mem_cancel_right M hprod]
      simpa using (hf M hM).2
    · rw [Subgroup.mul_mem_cancel_left M ((hf K hK).1 M hM hKM), ih']
      simp [hKM]

/-- A finite group in which every maximal subgroup `M` is irredundant (some
element lies in all other maximal subgroups but not in `M`) is cyclic. -/
theorem isCyclic_of_forall_irredundant [Finite G]
    (h : ∀ M : Subgroup G, IsCoatom M →
      ∃ x : G, (∀ K : Subgroup G, IsCoatom K → K ≠ M → x ∈ K) ∧ x ∉ M) :
    IsCyclic G := by
  classical
  have h' : ∀ M : Subgroup G, ∃ x : G, IsCoatom M →
      (∀ K : Subgroup G, IsCoatom K → K ≠ M → x ∈ K) ∧ x ∉ M := by
    intro M
    by_cases hM : IsCoatom M
    · obtain ⟨x, hx⟩ := h M hM
      exact ⟨x, fun _ => hx⟩
    · exact ⟨1, fun hM' => absurd hM' hM⟩
  choose f hf using h'
  let C : Finset (Subgroup G) := (maximalSubgroups_finite (G := G)).toFinset
  let x : G := (C.toList.map f).prod
  have hx : ∀ M : Subgroup G, IsCoatom M → x ∉ M := by
    intro M hM
    have hMC : M ∈ C.toList := by
      rw [Finset.mem_toList]
      exact mem_maximalSubgroups_toFinset.mpr hM
    have hiff := prod_map_mem_iff f hf C.toList (Finset.nodup_toList C)
      (fun K hK => mem_maximalSubgroups_toFinset.mp (Finset.mem_toList.mp hK)) M hM
    exact fun hxM => hiff.mp hxM hMC
  refine isCyclic_iff_exists_zpowers_eq_top.mpr ⟨x, ?_⟩
  by_contra hne
  obtain ⟨M, hM, hle⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom (Subgroup.zpowers x)).resolve_left hne
  exact hx M hM (hle (Subgroup.mem_zpowers x))

/-- **Core lemma.** If `G` is finite and not cyclic, then some maximal subgroup
`M` is redundant: the intersection of all the other maximal subgroups is
contained in `M`. -/
theorem exists_redundant_maximal [Finite G] (hG : ¬ IsCyclic G) :
    ∃ M : Subgroup G, IsCoatom M ∧
      (⨅ (K : Subgroup G) (_ : IsCoatom K) (_ : K ≠ M), K) ≤ M := by
  by_contra hcon
  push Not at hcon
  refine hG (isCyclic_of_forall_irredundant fun M hM => ?_)
  obtain ⟨x, hxI, hxM⟩ := SetLike.not_le_iff_exists.mp (hcon M hM)
  refine ⟨x, fun K hK hKM => ?_, hxM⟩
  exact (Subgroup.mem_iInf.mp ((Subgroup.mem_iInf.mp
    (Subgroup.mem_iInf.mp hxI K)) hK)) hKM

/-- **Answer to the question of Archer et al.** For every finite noncyclic group
`G`, `ι(G) < |m(G)|`: dropping a redundant maximal subgroup from `m(G)` leaves a
family of `|m(G)| - 1` maximal subgroups whose intersection is still `Φ(G)`. -/
theorem intersectionNumber_lt_ncard [Finite G] (hG : ¬ IsCyclic G) :
    intersectionNumber G < (maximalSubgroups G).ncard := by
  classical
  obtain ⟨M, hM, hred⟩ := exists_redundant_maximal hG
  let C : Finset (Subgroup G) := (maximalSubgroups_finite (G := G)).toFinset
  have hMC : M ∈ C := mem_maximalSubgroups_toFinset.mpr hM
  have hfam : IsFrattiniFamily (C.erase M) := by
    refine ⟨fun K hK => mem_maximalSubgroups_toFinset.mp (Finset.mem_of_mem_erase hK), ?_⟩
    have hle_others :
        (C.erase M).inf id ≤ (⨅ (K : Subgroup G) (_ : IsCoatom K) (_ : K ≠ M), K) :=
      le_iInf fun K => le_iInf fun hK => le_iInf fun hKM =>
        Finset.inf_le (f := id)
          (Finset.mem_erase.mpr ⟨hKM, mem_maximalSubgroups_toFinset.mpr hK⟩)
    have hleM : (C.erase M).inf id ≤ M := hle_others.trans hred
    have hfr : frattini G ≤ (C.erase M).inf id :=
      Finset.le_inf fun K hK =>
        frattini_le_coatom (mem_maximalSubgroups_toFinset.mp (Finset.mem_of_mem_erase hK))
    refine le_antisymm ?_ hfr
    rw [← isFrattiniFamily_coatoms.2]
    refine Finset.le_inf fun K hK => ?_
    by_cases hKM : K = M
    · rw [hKM]
      exact hleM
    · exact Finset.inf_le (f := id) (Finset.mem_erase.mpr ⟨hKM, hK⟩)
  calc intersectionNumber G ≤ (C.erase M).card := intersectionNumber_le_card hfam
    _ < C.card := Finset.card_erase_lt_of_mem hMC
    _ = (maximalSubgroups G).ncard := (Set.ncard_eq_toFinset_card _ maximalSubgroups_finite).symm

/-! ## The converse: in a finite cyclic group every maximal subgroup is irredundant -/

/-- In a finite cyclic group, a subgroup `H` contains every `x` with
`x ^ |H| = 1`. -/
theorem mem_of_pow_card_eq_one [Finite G] [IsCyclic G] (H : Subgroup G) {x : G}
    (hx : x ^ Nat.card H = 1) : x ∈ H := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  have hpos : 0 < Nat.card H := Nat.card_pos
  let T : Finset G := Finset.univ.filter (fun a => a ^ Nat.card H = 1)
  let S : Finset G := Finset.univ.filter (fun a => a ∈ H)
  have hTle : T.card ≤ Nat.card H := IsCyclic.card_pow_eq_one_le hpos
  have hScard : S.card = Nat.card H := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hST : S ⊆ T := fun a ha => by
    simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact pow_card_eq_one_of_mem ha
  have hEq : S = T := Finset.eq_of_subset_of_card_le hST (hTle.trans hScard.ge)
  have hxT : x ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
  rw [← hEq] at hxT
  simpa [S] using hxT

/-- In a finite cyclic group, two subgroups of the same index coincide. -/
theorem eq_of_index_eq [Finite G] [IsCyclic G] {H K : Subgroup G}
    (h : H.index = K.index) : H = K := by
  have hcard : Nat.card H = Nat.card K := by
    have hH := H.card_mul_index
    have hK := K.card_mul_index
    have hi : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [h] at hH
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi) (hH.trans hK.symm)
  refine Subgroup.eq_of_le_of_card_ge (fun x hx => mem_of_pow_card_eq_one K ?_) hcard.ge
  rw [← hcard]
  exact pow_card_eq_one_of_mem hx

/-- In a finite cyclic group, if a prime `p` divides the index of a maximal
subgroup `M`, then the index of `M` equals `p`. -/
theorem index_eq_of_prime_dvd_index [Finite G] [IsCyclic G] {M : Subgroup G}
    (hM : IsCoatom M) {p : ℕ} (hp : p.Prime) (hpM : p ∣ M.index) : M.index = p := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hog : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
  have hmi : Nat.card M * M.index = Nat.card G := M.card_mul_index
  have hm0 : 0 < Nat.card M := Nat.card_pos
  obtain ⟨j, hj⟩ := hpM
  have hi0 : M.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hi0 (by rw [hj, mul_zero])
  have hj_dvd : j ∣ orderOf g := ⟨Nat.card M * p, by rw [hog, ← hmi, hj]; ring⟩
  have hcardL : Nat.card (Subgroup.zpowers (g ^ j)) = Nat.card M * p := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd hj0 hj_dvd, hog, ← hmi, hj,
      show Nat.card M * (p * j) = (Nat.card M * p) * j by ring,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hj0)]
  have hML : M ≤ Subgroup.zpowers (g ^ j) := fun x hx => by
    refine mem_of_pow_card_eq_one _ ?_
    rw [hcardL, pow_mul, pow_card_eq_one_of_mem hx, one_pow]
  have hLM : Subgroup.zpowers (g ^ j) ≠ M := by
    intro hLM
    have hc := hcardL
    rw [hLM] at hc
    have hp1 : 1 < p := hp.one_lt
    nlinarith
  have hLtop : Subgroup.zpowers (g ^ j) = ⊤ := (hM.le_iff.mp hML).resolve_right hLM
  have hcG : Nat.card M * p = Nat.card M * M.index := by
    rw [← hcardL, hLtop, Subgroup.card_top, hmi]
  exact (Nat.eq_of_mul_eq_mul_left hm0 hcG).symm

/-- **Converse core lemma.** In a finite cyclic group every maximal subgroup `M`
is irredundant: some element lies in every other maximal subgroup but not in
`M`. -/
theorem irredundant_of_isCyclic [Finite G] [IsCyclic G] {M : Subgroup G}
    (hM : IsCoatom M) :
    ∃ x : G, (∀ K : Subgroup G, IsCoatom K → K ≠ M → x ∈ K) ∧ x ∉ M := by
  have hi1 : M.index ≠ 1 := fun h => hM.1 (Subgroup.index_eq_one.mp h)
  set p := M.index.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime hi1
  haveI : Fact p.Prime := ⟨hp⟩
  have hMp : M.index = p := index_eq_of_prime_dvd_index hM hp (Nat.minFac_dvd _)
  let P : Sylow p G := default
  have hPM : ¬ (P : Subgroup G) ≤ M := by
    intro hle
    have hdvd : M.index ∣ (P : Subgroup G).index := Subgroup.index_dvd_of_le hle
    rw [hMp] at hdvd
    exact P.not_dvd_index hdvd
  obtain ⟨y, hyP, hyM⟩ := SetLike.not_le_iff_exists.mp hPM
  refine ⟨y, fun K hK hKM => ?_, hyM⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp P.isPGroup' ⟨y, hyP⟩
  rw [Subgroup.orderOf_mk] at hk
  have hpK : ¬ p ∣ K.index := fun hdvd =>
    hKM (eq_of_index_eq ((index_eq_of_prime_dvd_index hK hp hdvd).trans hMp.symm))
  have hcop : (p ^ k).Coprime K.index :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpK)
  have hdvdG : p ^ k ∣ Nat.card K * K.index := by
    rw [K.card_mul_index, ← hk]
    exact orderOf_dvd_natCard y
  have hdvdK : orderOf y ∣ Nat.card K := hk ▸ hcop.dvd_of_dvd_mul_right hdvdG
  exact mem_of_pow_card_eq_one K (orderOf_dvd_iff_pow_eq_one.mp hdvdK)

/-- In a finite cyclic group, every family of maximal subgroups whose
intersection is `Φ(G)` contains every maximal subgroup. -/
theorem mem_of_isFrattiniFamily_of_isCyclic [Finite G] [IsCyclic G]
    {S : Finset (Subgroup G)} (hS : IsFrattiniFamily S) {M : Subgroup G}
    (hM : IsCoatom M) : M ∈ S := by
  by_contra hMS
  obtain ⟨x, hxK, hxM⟩ := irredundant_of_isCyclic hM
  have hle : Subgroup.zpowers x ≤ S.inf id :=
    Finset.le_inf fun K hK => (Subgroup.zpowers_le).mpr
      (hxK K (hS.1 K hK) fun hKM => hMS (hKM ▸ hK))
  have hxS : x ∈ S.inf id := hle (Subgroup.mem_zpowers x)
  rw [hS.2] at hxS
  exact hxM (frattini_le_coatom hM hxS)

/-- For a finite cyclic group, `ι(G) = |m(G)|`. -/
theorem intersectionNumber_eq_ncard_of_isCyclic [Finite G] [IsCyclic G] :
    intersectionNumber G = (maximalSubgroups G).ncard := by
  refine le_antisymm intersectionNumber_le_ncard ?_
  have hne : {k : ℕ | ∃ S : Finset (Subgroup G), IsFrattiniFamily S ∧ S.card = k}.Nonempty :=
    ⟨_, _, isFrattiniFamily_coatoms, rfl⟩
  obtain ⟨S, hS, hcard⟩ := Nat.sInf_mem hne
  have hsub : (maximalSubgroups_finite (G := G)).toFinset ⊆ S := fun M hM =>
    mem_of_isFrattiniFamily_of_isCyclic hS (mem_maximalSubgroups_toFinset.mp hM)
  rw [Set.ncard_eq_toFinset_card _ maximalSubgroups_finite]
  calc _ ≤ S.card := Finset.card_le_card hsub
    _ = intersectionNumber G := hcard

/-- **Characterization.** For a finite group `G`, `ι(G) = |m(G)|` if and only if
`G` is cyclic.  Together with `intersectionNumber_le_ncard` this answers the
question of Archer et al. (arXiv:1907.02898, Section "Discussion and Open
Questions") affirmatively: `ι(G) < |m(G)|` exactly for noncyclic finite `G`. -/
theorem intersectionNumber_eq_ncard_iff [Finite G] :
    intersectionNumber G = (maximalSubgroups G).ncard ↔ IsCyclic G := by
  constructor
  · intro h
    by_contra hG
    exact (intersectionNumber_lt_ncard hG).ne h
  · intro hG
    exact intersectionNumber_eq_ncard_of_isCyclic

/-- Equivalent form: for a finite group `G`, `ι(G) < |m(G)|` if and only if `G`
is not cyclic. -/
theorem intersectionNumber_lt_ncard_iff [Finite G] :
    intersectionNumber G < (maximalSubgroups G).ncard ↔ ¬ IsCyclic G := by
  rw [← intersectionNumber_eq_ncard_iff]
  exact ⟨fun h => h.ne, fun h => lt_of_le_of_ne intersectionNumber_le_ncard h⟩

/-! ## Ground truth -/

/-- In a group of prime order `p`, the only maximal subgroup is `⊥`. -/
theorem maximalSubgroups_eq_of_card_prime {p : ℕ} [Fact p.Prime] (hG : Nat.card G = p) :
    maximalSubgroups G = {⊥} := by
  haveI : Fact (Nat.card G).Prime := hG ▸ ‹Fact p.Prime›
  have hbt : ∀ K : Subgroup G, K = ⊥ ∨ K = ⊤ := fun K => Subgroup.eq_bot_or_eq_top_of_prime_card K
  have hnt : (⊥ : Subgroup G) ≠ ⊤ := by
    intro h
    have hc := congrArg (fun K : Subgroup G => Nat.card K) h
    simp only [Subgroup.card_bot, Subgroup.card_top, hG] at hc
    exact (Fact.out : p.Prime).one_lt.ne hc
  ext K
  simp only [maximalSubgroups, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro hK
    exact (hbt K).resolve_right hK.1
  · rintro rfl
    exact ⟨hnt, fun b hb => (hbt b).resolve_left hb.ne'⟩

/-- `ι(ℤ/5) = |m(ℤ/5)| = 1`: the only maximal subgroup is trivial. -/
example : intersectionNumber (Multiplicative (ZMod 5)) = 1 ∧
    (maximalSubgroups (Multiplicative (ZMod 5))).ncard = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcard : Nat.card (Multiplicative (ZMod 5)) = 5 := by simp
  have hm : (maximalSubgroups (Multiplicative (ZMod 5))).ncard = 1 := by
    rw [maximalSubgroups_eq_of_card_prime hcard, Set.ncard_singleton]
  exact ⟨intersectionNumber_eq_ncard_of_isCyclic.trans hm, hm⟩

/-- The trivial group has no maximal subgroups and `ι = 0` (degenerate case,
excluded by the paper). -/
example : intersectionNumber Unit = 0 ∧ (maximalSubgroups Unit).ncard = 0 := by
  refine ⟨Nat.eq_zero_of_le_zero ?_, ?_⟩
  · refine (intersectionNumber_le_card (S := ∅) ⟨fun K hK => absurd hK (Finset.notMem_empty K), ?_⟩)
    exact Subsingleton.elim _ _
  · have hempty : maximalSubgroups Unit = ∅ := by
      ext K
      simp only [maximalSubgroups, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hK => hK.1 (Subsingleton.elim _ _)
    rw [hempty, Set.ncard_empty]

/-- The Klein four-group `ℤ/2 × ℤ/2` is not cyclic, so `ι < |m|` there
(the paper computes `ι = 2`, `|m| = 3`). -/
example : intersectionNumber (Multiplicative (ZMod 2 × ZMod 2)) <
    (maximalSubgroups (Multiplicative (ZMod 2 × ZMod 2))).ncard := by
  refine intersectionNumber_lt_ncard fun hcyc => ?_
  haveI := hcyc
  have hexp := IsCyclic.exponent_eq_card (α := Multiplicative (ZMod 2 × ZMod 2))
  have hcard : Nat.card (Multiplicative (ZMod 2 × ZMod 2)) = 4 := by simp
  have hpow : ∀ x : Multiplicative (ZMod 2 × ZMod 2), x ^ 2 = 1 := by decide
  have hdvd : Monoid.exponent (Multiplicative (ZMod 2 × ZMod 2)) ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one hpow
  rw [hexp, hcard] at hdvd
  norm_num at hdvd

end Candidates.IntersectionNumbersFiniteGroups
