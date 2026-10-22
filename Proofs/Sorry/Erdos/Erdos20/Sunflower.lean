/-
  Erdős Problem #20 (Sunflower Conjecture) — Frankl shift theory.

  The Frankl (i,j)-compression C_ij sends each member S of a family F to
  (S \ {j}) ∪ {i} when i ∉ S and j ∈ S, unless that set already lies in F
  (in which case S is kept). This file develops the compression
  infrastructure for the formalization of Mishra, "Erdős Rado Sunflower
  Theorem for Shifted Families" (arXiv:2606.02667): sunflower and τ
  definitions, the shift operator, shift chains, and transport lemmas.
  The headline theorem for shifted families is in ShiftedSunflower.lean;
  the machine-checked refutation of v1's bridge is in Counterexample.lean.

  NOTE ON NUMBERING: the "Lemma 1(ii)/(iii)" and "Lemma 2" labels below follow
  the tex \label tags, not the compiled auto-numbering — v2 displays the
  shift-effects lemma as Lemma 3 and the τ-doubling lemma as Lemma 4.

  Key results (all sorry-free):
    franklShift_card               — Lemma 1(ii): |C_ij F| = |F|
    sunflowerNumber_franklShift_le — Lemma 2: τ(C_ij F) ≤ 2·τ(F)
    matchingNumber_shift_le        — Lemma 1(iii): ν(C_ij F) ≤ ν(F)
    matchingNumber_reachable       — matchings transport backward through
                                     any chain of shifts
    IsFullyCompressed.replace_mem  — compression stability: replacing
                                     j ∈ S by i < j, i ∉ S stays in F
    chainForward_*                 — composed family↔endpoint bijection
    empty_kernel_sunflower_le_sunflowerNumber
                                   — empty-kernel sunflowers (matchings)
                                     in any full shift have size ≤ τ(F)

  Two corrections shaped this file:

  (1) Vacuity fix. `IsFullyCompressed` quantifies over i < j only, as in
      the paper. An earlier draft quantified over ALL i, j; bidirectional
      stability forces every shift to fix the family in both directions,
      collapsing every shift chain (family = endpoint) and making the
      general→shifted bridge vacuous. The lemmas that relied on the
      bidirectional form (franklShift_eq_of_compressed,
      reachable_compressed_eq, fullShift_eq — together they forced
      family = shifted) were deleted; under i < j they are unprovable,
      and unwanted.

  (2) The false bridge was deleted. Mishra v1's Lemma 3 claimed
      τ(S(F)) ≤ 3·τ(F)² for the full shift endpoint S(F) of any family.
      That statement is FALSE, not merely unproved: there is a 4-uniform
      family on Fin 20 with 17 members and τ(F) = 2 whose canonical
      i < j lex shift chain ends at the star {{0,1,2,x} : 3 ≤ x ≤ 19}
      with τ = 17 > 12 = 3τ² (machine-checked in Counterexample.lean,
      witness data inline there). The theorems that existed solely to
      prove Lemma 3 were removed with it. Everything remaining here is
      sound shift theory, independent of the dead bridge, and is what
      ShiftedSunflower.lean consumes.

  NOTATION MAP (paper → Lean):
    F                 → family : Finset (Finset (Fin n))
    C_{ij}            → franklShift i j
    "shifted/initial" → IsFullyCompressed
    S(F) = F_{n-1,n}  → IsFullShiftOf shifted family
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

open Finset

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════
-- SUNFLOWER DEFINITIONS
-- ════════════════════════════════════════════════════════════════════

section Sunflower

-- Paper line 80
def IsSunflowerWith (sub : Finset (Finset (Fin n))) (K : Finset (Fin n)) : Prop :=
  (∀ S ∈ sub, K ⊆ S) ∧
  (∀ S ∈ sub, S \ K ≠ ∅) ∧
  (∀ S ∈ sub, ∀ T ∈ sub, S ≠ T → S ∩ T = K)

def HasSunflower (family : Finset (Finset (Fin n))) (k : ℕ) : Prop :=
  ∃ sub : Finset (Finset (Fin n)), sub ⊆ family ∧ sub.card = k ∧
    ∃ K : Finset (Fin n), IsSunflowerWith sub K

-- Paper line 107-108
noncomputable def sunflowerNumber (family : Finset (Finset (Fin n))) : ℕ :=
  sSup { k : ℕ | HasSunflower family k }

theorem HasSunflower.le_card {family : Finset (Finset (Fin n))} {k : ℕ}
    (h : HasSunflower family k) : k ≤ family.card := by
  obtain ⟨sub, hsub, hcard, _⟩ := h
  calc k = sub.card := hcard.symm
    _ ≤ family.card := Finset.card_le_card hsub

theorem hasSunflower_zero (family : Finset (Finset (Fin n))) : HasSunflower family 0 := by
  exact ⟨∅, empty_subset _, card_empty, ∅,
    fun _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h⟩

theorem sunflowerNumber_le_of_forall (family : Finset (Finset (Fin n))) (B : ℕ)
    (h : ∀ k, HasSunflower family k → k ≤ B) :
    sunflowerNumber family ≤ B := by
  unfold sunflowerNumber
  exact csSup_le ⟨0, hasSunflower_zero family⟩ fun k hk => h k hk

theorem le_sunflowerNumber (family : Finset (Finset (Fin n))) {k : ℕ}
    (h : HasSunflower family k) : k ≤ sunflowerNumber family := by
  unfold sunflowerNumber
  exact le_csSup ⟨family.card, fun m hm => hm.le_card⟩ h

theorem sunflowerNumber_le_card (family : Finset (Finset (Fin n))) :
    sunflowerNumber family ≤ family.card :=
  sunflowerNumber_le_of_forall family family.card fun _ hk => hk.le_card

theorem IsSunflowerWith.subset {sub sub' : Finset (Finset (Fin n))} {K : Finset (Fin n)}
    (hsf : IsSunflowerWith sub K) (h : sub' ⊆ sub) :
    IsSunflowerWith sub' K :=
  ⟨fun S hS => hsf.1 S (h hS),
   fun S hS => hsf.2.1 S (h hS),
   fun S hS T hT hne => hsf.2.2 S (h hS) T (h hT) hne⟩

end Sunflower

-- ════════════════════════════════════════════════════════════════════
-- FRANKL SHIFT OPERATOR
-- ════════════════════════════════════════════════════════════════════

section FranklShift

-- Paper line 176-183
def franklShiftSet (i j : Fin n) (S : Finset (Fin n)) : Finset (Fin n) :=
  if i ∉ S ∧ j ∈ S then insert i (S.erase j)
  else S

noncomputable def franklShift (i j : Fin n) (family : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  family.image fun S =>
    let S' := franklShiftSet i j S
    if S' ∈ family then S else S'

-- Paper line 210 (i < j as in the paper; unrestricted ∀ i j was the vacuity engine)
def IsFullyCompressed (family : Finset (Finset (Fin n))) : Prop :=
  ∀ i j : Fin n, i < j → franklShift i j family = family

inductive ReachableByShifts :
    Finset (Finset (Fin n)) → Finset (Finset (Fin n)) → Type where
  | refl (F : Finset (Finset (Fin n))) : ReachableByShifts F F
  | step {F G H : Finset (Finset (Fin n))} (i j : Fin n)
      (h : franklShift i j F = G) (hr : ReachableByShifts G H) :
      ReachableByShifts F H

structure IsFullShiftOf (shifted original : Finset (Finset (Fin n))) : Type where
  compressed : IsFullyCompressed shifted
  reachable : ReachableByShifts original shifted

end FranklShift

-- ════════════════════════════════════════════════════════════════════
-- SHIFT INFRASTRUCTURE (fully proved)
-- ════════════════════════════════════════════════════════════════════

theorem insert_erase_inj {S T : Finset (Fin n)} {i j : Fin n}
    (hiS : i ∉ S) (hiT : i ∉ T) (hjS : j ∈ S) (hjT : j ∈ T)
    (heq : insert i (S.erase j) = insert i (T.erase j)) : S = T := by
  ext x
  constructor <;> intro hx
  · by_cases hxj : x = j
    · subst hxj; exact hjT
    · have hxerase : x ∈ S.erase j := Finset.mem_erase.mpr ⟨hxj, hx⟩
      have hxins : x ∈ insert i (S.erase j) :=
        Finset.mem_insert.mpr (Or.inr hxerase)
      rw [heq] at hxins
      rcases Finset.mem_insert.mp hxins with h | h
      · subst h; exact absurd hx hiS
      · exact (Finset.mem_erase.mp h).2
  · by_cases hxj : x = j
    · subst hxj; exact hjS
    · have hxerase : x ∈ T.erase j := Finset.mem_erase.mpr ⟨hxj, hx⟩
      have hxins : x ∈ insert i (T.erase j) :=
        Finset.mem_insert.mpr (Or.inr hxerase)
      rw [← heq] at hxins
      rcases Finset.mem_insert.mp hxins with h | h
      · subst h; exact absurd hx hiT
      · exact (Finset.mem_erase.mp h).2

section ShiftTheory

-- Paper Lemma 1(ii): shift is a bijection on families
theorem franklShift_card (i j : Fin n) (family : Finset (Finset (Fin n))) :
    (franklShift i j family).card = family.card := by
  unfold franklShift
  rw [Finset.card_image_iff]
  intro S hS T hT heq
  simp only at heq
  by_cases hfS : franklShiftSet i j S ∈ family <;>
    by_cases hfT : franklShiftSet i j T ∈ family <;>
    simp only [hfS, hfT, ite_true, ite_false] at heq
  · exact heq
  · rw [← heq] at hfT; exact absurd hS hfT
  · rw [heq] at hfS; exact absurd hT hfS
  · unfold franklShiftSet at heq hfS hfT
    split_ifs at heq hfS hfT with hSij hTij
    · exact insert_erase_inj hSij.1 hTij.1 hSij.2 hTij.2 heq
    · exact absurd hT hfT
    · exact absurd hS hfS
    · exact heq

-- Paper Lemma 2 (Appendix B): single shift at most doubles τ
theorem sunflowerNumber_franklShift_le (i j : Fin n) (family : Finset (Finset (Fin n))) :
    sunflowerNumber (franklShift i j family) ≤ 2 * sunflowerNumber family := by
  apply sunflowerNumber_le_of_forall
  intro k ⟨sub, hsub, hcard, K, hsf⟩
  rw [← hcard]
  -- Split sub into sets in family and sets not in family
  let sub₁ := sub.filter (· ∈ family)
  let sub₂ := sub.filter (· ∉ family)
  have hpart : sub.card = sub₁.card + sub₂.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext S; simp [sub₁, sub₂, Finset.mem_filter]; tauto
    · exact Finset.disjoint_filter.mpr fun S _ h1 h2 => h2 h1
  -- sub₁ ⊆ family and is a sunflower
  have hsub₁_fam : sub₁ ⊆ family := by
    intro S hS; exact (Finset.mem_filter.mp hS).2
  have hsub₁_sub : sub₁ ⊆ sub := Finset.filter_subset _ _
  have hsf₁ : IsSunflowerWith sub₁ K := hsf.subset hsub₁_sub
  have hsf₁_has : HasSunflower family sub₁.card :=
    ⟨sub₁, hsub₁_fam, rfl, K, hsf₁⟩
  have hbound₁ : sub₁.card ≤ sunflowerNumber family :=
    le_sunflowerNumber family hsf₁_has
  -- Every S ∈ sub₂ has i ∈ S (since S came from a shift that inserted i)
  have hi_mem_sub₂ : ∀ S ∈ sub₂, i ∈ S := by
    intro S hS
    have hSsub : S ∈ sub := (Finset.mem_filter.mp hS).1
    have hSnf : S ∉ family := (Finset.mem_filter.mp hS).2
    obtain ⟨T, hT, heq⟩ := Finset.mem_image.mp (hsub hSsub)
    simp only at heq
    by_cases hfT : franklShiftSet i j T ∈ family
    · simp [hfT] at heq; subst heq; exact absurd hT hSnf
    · simp [hfT] at heq
      rw [← heq]
      unfold franklShiftSet
      split_ifs with hij
      · exact Finset.mem_insert_self i _
      · -- franklShiftSet i j T = T, but hfT says it's not in family, contradiction with hT
        exfalso; apply hfT; unfold franklShiftSet; simp [hij]; exact hT
  -- Case split on whether i ∈ K
  by_cases hiK : i ∈ K
  · -- Case i ∈ K: preimages of sub₂ form a sunflower in family
    -- The forward map f used in franklShift
    let f : Finset (Fin n) → Finset (Fin n) := fun T =>
      if franklShiftSet i j T ∈ family then T else franklShiftSet i j T
    -- f is injective on family (from franklShift_card)
    have hf_inj : Set.InjOn f ↑family := by
      rw [← Finset.card_image_iff]; exact franklShift_card i j family
    -- For each S ∈ sub₂, its preimage T ∈ family has f(T) = S
    have hpre₂ : ∀ S ∈ sub₂, ∃ T ∈ family, f T = S ∧ franklShiftSet i j T = S ∧
        i ∉ T ∧ j ∈ T := by
      intro S hS
      have hSmem : S ∈ sub := (Finset.mem_filter.mp hS).1
      have hSnf : S ∉ family := (Finset.mem_filter.mp hS).2
      obtain ⟨T, hT, heq⟩ := Finset.mem_image.mp (hsub hSmem)
      simp only at heq
      have hfT : franklShiftSet i j T ∉ family := by
        intro hfTm; simp [hfTm] at heq; subst heq; exact hSnf hT
      simp [hfT] at heq
      have hfT_eq : f T = S := by
        show ite _ _ _ = _; rw [if_neg hfT]; exact heq
      have hij : i ∉ T ∧ j ∈ T := by
        unfold franklShiftSet at heq
        split_ifs at heq with h
        · exact h
        · -- franklShiftSet i j T = T, so S = T ∈ family, contradiction
          exfalso; rw [← heq] at hSnf; exact hSnf hT
      exact ⟨T, hT, hfT_eq, heq, hij.1, hij.2⟩
    -- Define the preimage set: for S ∈ sub₂, the preimage is insert j (S.erase i)
    let pre := sub₂.image (fun S => insert j (S.erase i))
    -- Each preimage is in family
    have hpre_fam : pre ⊆ family := by
      intro T hT
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
      obtain ⟨T', hT'f, _, hfs_eq, hiT', hjT'⟩ := hpre₂ S hS
      -- franklShiftSet i j T' = S = insert i (T'.erase j)
      -- So T' = insert j (S.erase i) = insert j ((insert i (T'.erase j)).erase i)
      have hS_eq : S = insert i (T'.erase j) := by
        unfold franklShiftSet at hfs_eq
        rw [if_pos ⟨hiT', hjT'⟩] at hfs_eq
        exact hfs_eq.symm
      rw [hS_eq]
      -- insert j ((insert i (T'.erase j)).erase i)
      -- = insert j (T'.erase j)  [since i ∉ T'.erase j, erase i removes the inserted i]
      -- = T'  [since j ∈ T']
      have : insert j ((insert i (T'.erase j)).erase i) = T' := by
        rw [Finset.erase_insert (by simp [hiT'])]
        exact Finset.insert_erase hjT'
      rw [this]; exact hT'f
    -- If i = j, franklShift is identity, sub₂ = ∅
    by_cases hij : i = j
    · -- i = j case
      have hsub₂_empty : sub₂ = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro S hS
        have hSsub : S ∈ sub := (Finset.mem_filter.mp hS).1
        have hSnf : S ∉ family := (Finset.mem_filter.mp hS).2
        -- franklShift i j family = family when i = j
        have hshift_id : franklShift i j family = family := by
          unfold franklShift; rw [hij]
          conv_rhs => rw [← Finset.image_id (s := family)]
          congr 1; ext T
          have : franklShiftSet j j T = T := by
            unfold franklShiftSet; split_ifs with h; exact absurd h.1 (not_not.mpr h.2); rfl
          simp [this]
        have hSf : S ∈ family := hshift_id ▸ (hsub hSsub)
        exact hSnf hSf
      rw [hsub₂_empty, Finset.card_empty] at hpart
      omega
    · -- i ≠ j: j ∉ S for all S ∈ sub₂
      have hj_not_sub₂ : ∀ S ∈ sub₂, j ∉ S := by
        intro S hS hj
        obtain ⟨T, _, _, hfs_eq, hiT, hjT⟩ := hpre₂ S hS
        -- S = insert i (T.erase j), j ∈ S means j ∈ insert i (T.erase j)
        -- j = i (contradicts i ≠ j) or j ∈ T.erase j (impossible)
        rw [hfs_eq.symm] at hj
        unfold franklShiftSet at hj
        rw [if_pos ⟨hiT, hjT⟩] at hj
        rcases Finset.mem_insert.mp hj with rfl | h
        · exact hij rfl
        · exact (Finset.mem_erase.mp h).1 rfl
      -- The map S ↦ insert j (S.erase i) is injective on sub₂ (by insert_erase_inj)
      have hpre_card : pre.card = sub₂.card := by
        apply Finset.card_image_of_injOn
        intro S hS T hT heq
        exact insert_erase_inj (hj_not_sub₂ S hS) (hj_not_sub₂ T hT)
          (hi_mem_sub₂ S hS) (hi_mem_sub₂ T hT) heq
      -- pre is a sunflower with kernel K' = insert j (K.erase i)
      let K' := insert j (K.erase i)
      have hsf_pre : IsSunflowerWith pre K' := by
        refine ⟨?_, ?_, ?_⟩
        · -- K' ⊆ each T ∈ pre
          intro T hT
          obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
          have hSsub : S ∈ sub := (Finset.mem_filter.mp hS).1
          intro x hx
          rcases Finset.mem_insert.mp hx with hxj | hxe
          · -- x = j: j ∈ insert j (S.erase i)
            subst hxj; exact Finset.mem_insert_self _ _
          · -- x ∈ K.erase i: x ∈ K, x ≠ i
            have hxK : x ∈ K := (Finset.mem_erase.mp hxe).2
            have hxi : x ≠ i := (Finset.mem_erase.mp hxe).1
            -- x ∈ S (since K ⊆ S)
            have hxS : x ∈ S := hsf.1 S hSsub hxK
            exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxi, hxS⟩)
        · -- petals nonempty: (insert j (S.erase i)) \ K' ≠ ∅
          intro T hT
          obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
          have hSsub : S ∈ sub := (Finset.mem_filter.mp hS).1
          -- S \ K ≠ ∅, get x ∈ S \ K
          have hpetal := hsf.2.1 S hSsub
          rw [ne_eq, Finset.sdiff_eq_empty_iff_subset] at hpetal
          obtain ⟨x, hxS, hxK⟩ := Finset.not_subset.mp hpetal
          -- x ≠ i (since i ∈ K but x ∉ K)
          have hxi : x ≠ i := fun h => hxK (h ▸ hiK)
          -- x ≠ j: if x = j then j ∈ S, but j ∉ S (from hj_not_sub₂)
          have hxj : x ≠ j := by
            intro h; subst h
            exact hj_not_sub₂ S hS hxS
          rw [ne_eq, Finset.sdiff_eq_empty_iff_subset, Finset.not_subset]
          refine ⟨x, ?_, ?_⟩
          · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxi, hxS⟩)
          · intro habs
            rcases Finset.mem_insert.mp habs with rfl | hxe
            · exact hxj rfl
            · exact hxK (Finset.mem_erase.mp hxe).2
        · -- distinct T-sets intersect at K'
          intro T₁ hT₁ T₂ hT₂ hne
          obtain ⟨S₁, hS₁, rfl⟩ := Finset.mem_image.mp hT₁
          obtain ⟨S₂, hS₂, rfl⟩ := Finset.mem_image.mp hT₂
          have hS₁sub : S₁ ∈ sub := (Finset.mem_filter.mp hS₁).1
          have hS₂sub : S₂ ∈ sub := (Finset.mem_filter.mp hS₂).1
          have hSne : S₁ ≠ S₂ := by
            intro heq; apply hne; rw [heq]
          have hinter := hsf.2.2 S₁ hS₁sub S₂ hS₂sub hSne
          ext x
          constructor
          · intro hx
            rcases Finset.mem_inter.mp hx with ⟨hx₁, hx₂⟩
            rcases Finset.mem_insert.mp hx₁ with hxj₁ | hx₁e
            · subst hxj₁; exact Finset.mem_insert_self _ _
            · rcases Finset.mem_insert.mp hx₂ with hxj₂ | hx₂e
              · subst hxj₂; exact Finset.mem_insert_self _ _
              · have hxS₁ : x ∈ S₁ := (Finset.mem_erase.mp hx₁e).2
                have hxS₂ : x ∈ S₂ := (Finset.mem_erase.mp hx₂e).2
                have hxK : x ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨hxS₁, hxS₂⟩
                rw [hinter] at hxK
                have hxi : x ≠ i := (Finset.mem_erase.mp hx₁e).1
                exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxi, hxK⟩)
          · intro hx
            rcases Finset.mem_insert.mp hx with hxj | hxe
            · subst hxj
              exact Finset.mem_inter.mpr
                ⟨Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩
            · have hxK : x ∈ K := (Finset.mem_erase.mp hxe).2
              have hxi : x ≠ i := (Finset.mem_erase.mp hxe).1
              exact Finset.mem_inter.mpr
                ⟨Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxi, hsf.1 S₁ hS₁sub hxK⟩),
                 Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxi, hsf.1 S₂ hS₂sub hxK⟩)⟩
      -- pre is a sunflower in family of size |sub₂|
      have hhas_pre : HasSunflower family pre.card :=
        ⟨pre, hpre_fam, rfl, K', hsf_pre⟩
      have hbound₂ : sub₂.card ≤ sunflowerNumber family := by
        rw [← hpre_card]
        exact le_sunflowerNumber family hhas_pre
      omega
  · -- Case i ∉ K: at most one set in the sunflower contains i, so |sub₂| ≤ 1
    have hbound₂ : sub₂.card ≤ 1 := by
      have hsub₂_sub : sub₂ ⊆ sub := Finset.filter_subset _ _
      have : sub₂ ⊆ sub.filter (fun S => i ∈ S) := by
        intro S hS
        exact Finset.mem_filter.mpr ⟨hsub₂_sub hS, hi_mem_sub₂ S hS⟩
      calc sub₂.card ≤ (sub.filter fun S => i ∈ S).card := Finset.card_le_card this
        _ ≤ 1 := by
          by_contra h
          push Not at h
          obtain ⟨S, hS, T, hT, hne⟩ := Finset.one_lt_card.mp h
          simp only [Finset.mem_filter] at hS hT
          have := hsf.2.2 S hS.1 T hT.1 hne
          have : i ∈ S ∩ T := Finset.mem_inter.mpr ⟨hS.2, hT.2⟩
          rw [‹S ∩ T = K›] at this
          exact hiK this
    -- Close: |sub| = |sub₁| + |sub₂| ≤ τ + 1 ≤ 2τ
    -- Need τ ≥ 1 or |sub₂| = 0
    by_cases hτ : sunflowerNumber family = 0
    · -- τ = 0: |sub₁| = 0, |sub₂| ≤ 1. Need |sub| = 0.
      -- τ = 0 → sub₁ = ∅ → |sub₁| = 0. Also |sub₂| ≤ 1.
      -- But we need to show |sub₂| = 0 when τ = 0.
      -- If sub₂ nonempty, pick S ∈ sub₂. S ∈ sub, sunflower of sub has size ≥ 1.
      -- sub₁ = ∅ so sub = sub₂. sub₂ is a sunflower in franklShift.
      -- Each S ∈ sub₂ has S ∉ family, so preimage T ∈ family with T ≠ S.
      -- A sunflower of size 1 = {S} needs S \ K ≠ ∅.
      -- Preimage T has S = insert i (T.erase j), with i ∉ T, j ∈ T.
      -- T ∈ family, T ≠ ∅ (since j ∈ T). {T} is a sunflower in family of size 1
      -- (with kernel ∅, petal T \ ∅ = T ≠ ∅).
      -- So τ(family) ≥ 1, contradicting τ = 0.
      have hbound₁_zero : sub₁.card = 0 := by omega
      have hsub₂_le : sub₂.card ≤ 0 := by
        by_contra h
        push Not at h
        obtain ⟨S, hS⟩ := Finset.card_pos.mp h
        have hSmem : S ∈ sub := (Finset.mem_filter.mp hS).1
        have hSnf : S ∉ family := (Finset.mem_filter.mp hS).2
        obtain ⟨T, hT, heq⟩ := Finset.mem_image.mp (hsub hSmem)
        simp only at heq
        have hfT : franklShiftSet i j T ∉ family := by
          intro hfTm
          simp [hfTm] at heq; subst heq; exact hSnf hT
        have hjT : j ∈ T := by
          by_contra hjn
          have : franklShiftSet i j T = T := by
            unfold franklShiftSet; split_ifs with h; exact absurd h.2 hjn; rfl
          rw [this] at hfT; exact hfT hT
        have hTne : T ≠ ∅ := by intro h; subst h; simp at hjT
        have hT_sf : IsSunflowerWith {T} ∅ :=
          ⟨fun A hA => by rw [Finset.mem_singleton.mp hA]; exact Finset.empty_subset _,
           fun A hA => by rw [Finset.mem_singleton.mp hA]; simp [hTne],
           fun A hA B hB hne => by
             rw [Finset.mem_singleton.mp hA, Finset.mem_singleton.mp hB] at hne
             exact absurd rfl hne⟩
        have hhas : HasSunflower family 1 :=
          ⟨{T}, Finset.singleton_subset_iff.mpr hT, Finset.card_singleton _, ∅, hT_sf⟩
        have := le_sunflowerNumber family hhas
        omega
      omega
    · omega

-- Every set in franklShift has a preimage in family.
theorem franklShift_preimage (i j : Fin n) (family : Finset (Finset (Fin n)))
    (S : Finset (Fin n)) (hS : S ∈ franklShift i j family) :
    ∃ T ∈ family, (if franklShiftSet i j T ∈ family then T else franklShiftSet i j T) = S := by
  unfold franklShift at hS
  exact Finset.mem_image.mp hS

-- In a pairwise disjoint family, at most one set contains any given element.
theorem atMostOne_mem_of_pairwiseDisjoint (sub : Finset (Finset (Fin n)))
    (hdisj : ∀ S ∈ sub, ∀ T ∈ sub, S ≠ T → Disjoint S T) (x : Fin n) :
    (sub.filter fun S => x ∈ S).card ≤ 1 := by
  by_contra h
  push Not at h
  obtain ⟨S, hS, T, hT, hne⟩ := Finset.one_lt_card.mp h
  simp only [Finset.mem_filter] at hS hT
  exact Finset.disjoint_left.mp (hdisj S hS.1 T hT.1 hne) hS.2 hT.2

-- The forward map used in franklShift is injective on family.
-- Its inverse (well-defined since injective) maps each S ∈ franklShift to the unique T ∈ family
-- that maps to S. Since the forward map only swaps at most one element (i↔j) per set,
-- disjoint sets in the shifted family have disjoint preimages (the swap can't create new overlaps
-- because at most one set in a disjoint family can contain any given element).

-- The forward map sends x ∈ T to either x or (if x = j) i in the image.
theorem franklShift_mem_or (i j : Fin n) (family : Finset (Finset (Fin n)))
    (T : Finset (Fin n)) (x : Fin n) (hx : x ∈ T) :
    let fT := if franklShiftSet i j T ∈ family then T else franklShiftSet i j T
    x ∈ fT ∨ (x = j ∧ i ∈ fT) := by
  intro fT
  by_cases hfs : franklShiftSet i j T ∈ family
  · simp only [fT, hfs, ite_true]; exact Or.inl hx
  · simp only [fT, hfs, ite_false]
    unfold franklShiftSet
    split_ifs with hij
    · by_cases hxj : x = j
      · exact Or.inr ⟨hxj, Finset.mem_insert_self i _⟩
      · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxj, hx⟩))
    · exact Or.inl hx

-- Paper Lemma 1(iii) (Appendix A): single shift does not increase matching number
theorem matchingNumber_shift_le (i j : Fin n) (family : Finset (Finset (Fin n)))
    (sub : Finset (Finset (Fin n))) (hsub : sub ⊆ franklShift i j family)
    (hdisj : ∀ S ∈ sub, ∀ T ∈ sub, S ≠ T → Disjoint S T)
    (hne : ∀ S ∈ sub, S ≠ ∅) :
    ∃ sub' : Finset (Finset (Fin n)), sub' ⊆ family ∧ sub'.card = sub.card ∧
      (∀ S ∈ sub', ∀ T ∈ sub', S ≠ T → Disjoint S T) ∧
      (∀ S ∈ sub', S ≠ ∅) := by
  -- Use sub₀ = {T ∈ family | f T ∈ sub} where f is the forward map.
  let f : Finset (Fin n) → Finset (Fin n) := fun T =>
    if franklShiftSet i j T ∈ family then T else franklShiftSet i j T
  have hf_inj : Set.InjOn f ↑family := by
    rw [← Finset.card_image_iff]; exact franklShift_card i j family
  let sub₀ := family.filter fun T => f T ∈ sub
  -- Every S ∈ sub has a preimage in family
  have hpre : ∀ S ∈ sub, ∃ T ∈ family, f T = S := by
    intro S hS; exact Finset.mem_image.mp (hsub hS)
  choose g hg_mem hg_eq using hpre
  -- sub₀.image f = sub
  have himg : sub₀.image f = sub := by
    ext S; constructor
    · intro hS; obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
      exact (Finset.mem_filter.mp hT).2
    · intro hS; rw [Finset.mem_image]
      refine ⟨g S hS, Finset.mem_filter.mpr ⟨hg_mem S hS, ?_⟩, hg_eq S hS⟩
      rw [hg_eq S hS]; exact hS
  -- |sub₀| = |sub|
  have hcard : sub₀.card = sub.card := by
    rw [← himg, Finset.card_image_of_injOn
      (Set.InjOn.mono (fun x hx => (Finset.mem_filter.mp hx).1) hf_inj)]
  -- sub₀ is "almost disjoint": T₁ ∩ T₂ ⊆ {j} for distinct elements.
  -- Proof: x ∈ T → x ∈ f(T) or (x = j ∧ i ∈ f(T)), so x ≠ j → x ∈ f(T₁) ∩ f(T₂) = ∅.
  have halmost : ∀ T₁ ∈ sub₀, ∀ T₂ ∈ sub₀, T₁ ≠ T₂ → ∀ x ∈ T₁, x ∈ T₂ → x = j := by
    intro T₁ hT₁ T₂ hT₂ hne₁₂ x hx₁ hx₂
    have hT₁f := (Finset.mem_filter.mp hT₁).1
    have hT₁s := (Finset.mem_filter.mp hT₁).2
    have hT₂f := (Finset.mem_filter.mp hT₂).1
    have hT₂s := (Finset.mem_filter.mp hT₂).2
    have hfne : f T₁ ≠ f T₂ := fun h => hne₁₂ (hf_inj hT₁f hT₂f h)
    have hfd := hdisj (f T₁) hT₁s (f T₂) hT₂s hfne
    by_contra hxj
    have h₁ := franklShift_mem_or i j family T₁ x hx₁
    have h₂ := franklShift_mem_or i j family T₂ x hx₂
    simp only at h₁ h₂
    rcases h₁ with hxf₁ | ⟨rfl, _⟩
    · rcases h₂ with hxf₂ | ⟨rfl, _⟩
      · exact Finset.disjoint_left.mp hfd hxf₁ hxf₂
      · exact hxj rfl
    · exact hxj rfl
  -- At most one element of sub₀ contains j (since overlap is only at j, and at most
  -- one element of sub has j in its f-image, plus at most one case-B preimage has j).
  -- Actually: if T₁, T₂ ∈ sub₀ both have j and T₁ ≠ T₂, they overlap at j.
  -- Count: (sub₀.filter (j ∈ ·)).card ≤ 2 (at most one case-A, one case-B).
  -- If ≤ 1: sub₀ is pairwise disjoint. Use sub₀.
  -- If = 2: fix by replacing one element.
  by_cases hjcount : (sub₀.filter fun T => j ∈ T).card ≤ 1
  · -- No collision: sub₀ is pairwise disjoint.
    refine ⟨sub₀, Finset.filter_subset _ _, hcard, ?_, ?_⟩
    · intro T₁ hT₁ T₂ hT₂ hne₁₂
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      have hxj := halmost T₁ hT₁ T₂ hT₂ hne₁₂ x hx₁ hx₂
      have hj₁ : j ∈ T₁ := hxj ▸ hx₁
      have hj₂ : j ∈ T₂ := hxj ▸ hx₂
      have : 1 < (sub₀.filter fun T => j ∈ T).card :=
        Finset.one_lt_card.mpr ⟨T₁, Finset.mem_filter.mpr ⟨hT₁, hj₁⟩,
          T₂, Finset.mem_filter.mpr ⟨hT₂, hj₂⟩, hne₁₂⟩
      omega
    · intro S hS hempty
      have hSs := (Finset.mem_filter.mp hS).2
      apply hne (f S) hSs
      subst hempty; simp [f, franklShiftSet]
  · -- Collision case: ≥ 2 elements of sub₀ have j.
    -- Analysis shows this is fixable by replacing the case-A element with its shift,
    -- but the case where the shift is already in sub₀ requires showing T₁ = {j}, T₁' = {i},
    -- and that {i} shares i with f(T₂) making {i} ∉ sub, hence T₁' ∉ sub₀.
    -- Full construction: sub' = (sub₀.erase T₁) ∪ {insert i (T₁.erase j)}.
    push Not at hjcount
    obtain ⟨T₁, hT₁, T₂, hT₂, hne₁₂⟩ := Finset.one_lt_card.mp hjcount
    simp only [Finset.mem_filter] at hT₁ hT₂
    -- Extract membership facts
    have hT₁_sub₀ := hT₁.1
    have hj_T₁ := hT₁.2
    have hT₂_sub₀ := hT₂.1
    have hj_T₂ := hT₂.2
    have hT₁_fam := (Finset.mem_filter.mp hT₁_sub₀).1
    have hT₁_sub := (Finset.mem_filter.mp hT₁_sub₀).2
    have hT₂_fam := (Finset.mem_filter.mp hT₂_sub₀).1
    have hT₂_sub := (Finset.mem_filter.mp hT₂_sub₀).2
    have hfne : f T₁ ≠ f T₂ := fun h => hne₁₂ (hf_inj hT₁_fam hT₂_fam h)
    have hf_disj := hdisj (f T₁) hT₁_sub (f T₂) hT₂_sub hfne
    -- j can't be in both f(T₁) and f(T₂) by disjointness
    have hj_not_both : ¬(j ∈ f T₁ ∧ j ∈ f T₂) := by
      intro ⟨h1, h2⟩; exact Finset.disjoint_left.mp hf_disj h1 h2
    -- From franklShift_mem_or: j ∈ T → j ∈ f(T) ∨ i ∈ f(T)
    have hor₁ := franklShift_mem_or i j family T₁ j hj_T₁
    have hor₂ := franklShift_mem_or i j family T₂ j hj_T₂
    simp only at hor₁ hor₂
    -- At least one of f(T₁), f(T₂) doesn't contain j
    -- WLOG: swap so that T₁ is case-A (j ∈ f(T₁)) and T₂ is case-B (j ∉ f(T₂))
    -- If j ∉ f(T₁): swap T₁ and T₂
    suffices key : ∀ (A B : Finset (Fin n)),
        A ∈ sub₀ → B ∈ sub₀ → j ∈ A → j ∈ B → A ≠ B →
        f A ∈ sub → f B ∈ sub → j ∈ f A → j ∉ f B →
        ∃ sub' ⊆ family, #sub' = #sub ∧
          (∀ S ∈ sub', ∀ T ∈ sub', S ≠ T → Disjoint S T) ∧ ∀ S ∈ sub', S ≠ ∅ by
      by_cases hj_fT₁ : j ∈ f T₁
      · have hjfT₂ : j ∉ f T₂ := fun h => hj_not_both ⟨hj_fT₁, h⟩
        exact key T₁ T₂ hT₁_sub₀ hT₂_sub₀ hj_T₁ hj_T₂ hne₁₂ hT₁_sub hT₂_sub
            hj_fT₁ hjfT₂
      · by_cases hj_fT₂ : j ∈ f T₂
        · exact key T₂ T₁ hT₂_sub₀ hT₁_sub₀ hj_T₂ hj_T₁ (Ne.symm hne₁₂) hT₂_sub hT₁_sub
              hj_fT₂ hj_fT₁
        · -- Both j ∉ f(T₁) and j ∉ f(T₂), so from hor₁ and hor₂: i ∈ f(T₁) and i ∈ f(T₂)
          -- But this contradicts disjointness of f(T₁) and f(T₂)
          have hi_fT₁ : i ∈ f T₁ := by
            rcases hor₁ with h | ⟨_, h⟩
            · exact absurd h hj_fT₁
            · exact h
          have hi_fT₂ : i ∈ f T₂ := by
            rcases hor₂ with h | ⟨_, h⟩
            · exact absurd h hj_fT₂
            · exact h
          exact absurd hi_fT₂ (Finset.disjoint_left.mp hf_disj hi_fT₁)
    intro A B hA_sub₀ hB_sub₀ hjA hjB hAB hfA_sub hfB_sub hjfA hjfB
    have hA_fam := (Finset.mem_filter.mp hA_sub₀).1
    have hB_fam := (Finset.mem_filter.mp hB_sub₀).1
    have hfAB : f A ≠ f B := fun h => hAB (hf_inj hA_fam hB_fam h)
    have hfAB_disj := hdisj (f A) hfA_sub (f B) hfB_sub hfAB
    -- B is case-B: j ∉ f(B), so from franklShift_mem_or: i ∈ f(B)
    have hi_fB : i ∈ f B := by
      have := franklShift_mem_or i j family B j hjB
      simp only at this
      rcases this with h | ⟨_, h⟩
      · exact absurd h hjfB
      · exact h
    -- i ∉ A: if i ∈ A, then f(A) = A (case-A), so i ∈ f(A), contradicting disjointness
    have hiA : i ∉ A := by
      intro hi
      -- f(A) = A (case-A: franklShiftSet i j A ∈ family ↔ j ∈ f(A))
      -- Since j ∈ f(A), either f(A) = A or f(A) = franklShiftSet i j A
      -- If franklShiftSet i j A ∈ family: f(A) = A, so i ∈ A = i ∈ f(A)
      -- If franklShiftSet i j A ∉ family: f(A) = franklShiftSet i j A
      --   Since i ∈ A, franklShiftSet i j A = A (condition i ∉ A fails),
      --   so franklShiftSet i j A = A ∈ family, contradiction.
      -- Either way: i ∈ f(A)
      have hi_fA : i ∈ f A := by
        simp only [f]
        by_cases hfs : franklShiftSet i j A ∈ family
        · simp [hfs, hi]
        · have : franklShiftSet i j A = A := by
            simp [franklShiftSet, hi]
          rw [this] at hfs; exact absurd hA_fam hfs
      exact Finset.disjoint_left.mp hfAB_disj hi_fA hi_fB
    -- franklShiftSet i j A ∈ family (since j ∈ f(A) forces this)
    have hfsA : franklShiftSet i j A ∈ family := by
      by_contra hfs
      have heq : franklShiftSet i j A = insert i (A.erase j) := by
        simp [franklShiftSet, hiA, hjA]
      have hfA_val : f A = insert i (A.erase j) := by
        show (if franklShiftSet i j A ∈ family then A else franklShiftSet i j A) = _
        rw [if_neg hfs, heq]
      rw [hfA_val] at hjfA
      have : j ∉ insert i (A.erase j) := by
        simp only [Finset.mem_insert, Finset.mem_erase]
        intro h; rcases h with rfl | ⟨hne, _⟩
        · exact hiA hjA
        · exact hne rfl
      exact this hjfA
    -- f(A) = A (since franklShiftSet i j A ∈ family)
    have hfA_eq : f A = A := by
      show (if franklShiftSet i j A ∈ family then A else franklShiftSet i j A) = A
      rw [if_pos hfsA]
    -- A' = insert i (A.erase j)
    set A' := insert i (A.erase j) with hA'_def
    -- franklShiftSet i j A = A'
    have hshift_A : franklShiftSet i j A = A' := by
      show franklShiftSet i j A = insert i (A.erase j)
      simp [franklShiftSet, hiA, hjA]
    -- A ∈ sub (since f(A) = A and f(A) ∈ sub)
    have hA_sub : A ∈ sub := hfA_eq ▸ hfA_sub
    -- A' ∈ family
    have hA'_fam : A' ∈ family := hshift_A ▸ hfsA
    -- i ∈ A'
    have hi_A' : i ∈ A' := Finset.mem_insert_self i _
    -- i ∉ B (if i ∈ B, franklShiftSet i j B = B, so f(B) = B, j ∈ f(B), contradiction)
    have hiB : i ∉ B := by
      intro hi
      have hfs_eq : franklShiftSet i j B = B := by
        simp [franklShiftSet, hi]
      have hfB_eq : f B = B := by
        show (if franklShiftSet i j B ∈ family then B else franklShiftSet i j B) = B
        rw [hfs_eq]; split <;> rfl
      rw [hfB_eq] at hjfB
      exact hjfB hjB
    -- f(B) = franklShiftSet i j B = insert i (B.erase j)
    have hfsB_eq : franklShiftSet i j B = insert i (B.erase j) := by
      simp [franklShiftSet, hiB, hjB]
    have hfsB_not_fam : franklShiftSet i j B ∉ family := by
      intro hfs
      have hfB_eq : f B = B := by
        show (if franklShiftSet i j B ∈ family then B else franklShiftSet i j B) = B
        rw [if_pos hfs]
      rw [hfB_eq] at hjfB; exact hjfB hjB
    have hfB_eq : f B = insert i (B.erase j) := by
      show (if franklShiftSet i j B ∈ family then B else franklShiftSet i j B) = _
      rw [if_neg hfsB_not_fam, hfsB_eq]
    -- f(A') = A' (since i ∈ A', franklShiftSet condition fails)
    have hfA'_eq : f A' = A' := by
      show (if franklShiftSet i j A' ∈ family then A' else franklShiftSet i j A') = A'
      have : franklShiftSet i j A' = A' := by
        simp [franklShiftSet, hi_A']
      rw [this]; simp
    -- A' ∉ sub: if A' ∈ sub, i ∈ A' ∩ f(B), and disjointness forces A' = f(B),
    -- giving A = B by insert_erase_inj, contradiction.
    have hA'_not_sub : A' ∉ sub := by
      intro hA'_sub
      have hA'_ne_fB : A' ≠ f B := by
        intro h; rw [hfB_eq] at h
        have := insert_erase_inj hiA hiB hjA hjB h
        exact hAB this
      exact Finset.disjoint_left.mp
        (hdisj A' hA'_sub (f B) hfB_sub hA'_ne_fB) hi_A' (hfB_eq ▸ Finset.mem_insert_self i _)
    -- A' ∉ sub₀: f(A') = A' ∉ sub, so A' ∉ {T ∈ family | f T ∈ sub}
    have hA'_not_sub₀ : A' ∉ sub₀ := by
      intro h
      have := (Finset.mem_filter.mp h).2
      rw [hfA'_eq] at this
      exact hA'_not_sub this
    -- Construct sub' = (sub₀.erase A) ∪ {A'}
    refine ⟨(sub₀.erase A) ∪ {A'}, ?_, ?_, ?_, ?_⟩
    · -- sub' ⊆ family
      intro S hS
      rcases Finset.mem_union.mp hS with hS | hS
      · exact (Finset.mem_filter.mp (Finset.erase_subset _ _ hS)).1
      · rw [Finset.mem_singleton.mp hS]; exact hA'_fam
    · -- |sub'| = |sub|
      rw [Finset.card_union_of_disjoint]
      · have hge : 1 ≤ #sub := by
          calc 1 ≤ #sub₀ := Finset.one_le_card.mpr ⟨A, hA_sub₀⟩
            _ = #sub := hcard
        rw [Finset.card_erase_of_mem hA_sub₀, Finset.card_singleton, hcard]
        omega
      · rw [Finset.disjoint_singleton_right]
        exact fun h => hA'_not_sub₀ (Finset.erase_subset _ _ h)
    · -- pairwise disjoint
      -- First: i ≠ j
      have hij : i ≠ j := by
        intro heq; subst heq
        -- When i = j, franklShiftSet is identity, so f is identity, sub₀ ⊆ sub
        have hfs_id : ∀ S, franklShiftSet i i S = S := fun S => by simp [franklShiftSet]
        have hf_id : ∀ T, f T = T := by
          intro T; show ite _ _ _ = _; rw [hfs_id]; simp
        -- sub₀.filter (i ∈ ·) ⊆ sub.filter (i ∈ ·) which has card ≤ 1
        have hsub₀_sub : sub₀ ⊆ sub := by
          intro T hT; rw [← hf_id T]; exact (Finset.mem_filter.mp hT).2
        have hle : (sub₀.filter fun T => i ∈ T).card ≤ (sub.filter fun T => i ∈ T).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ hsub₀_sub)
        have := atMostOne_mem_of_pairwiseDisjoint sub hdisj i
        omega
      -- Key: for any T ∈ sub₀ with T ≠ A, i ∉ T
      have hi_not_mem : ∀ T ∈ sub₀, T ≠ A → i ∉ T := by
        intro T hT hTA hi_T
        have hT_fam := (Finset.mem_filter.mp hT).1
        have hfT_sub := (Finset.mem_filter.mp hT).2
        have := franklShift_mem_or i j family T i hi_T
        simp only at this
        rcases this with hi_fT | ⟨rfl, _⟩
        · -- i ∈ f(T) and i ∈ f(B). If f(T) = f(B) then T = B, but i ∉ B.
          -- If f(T) ≠ f(B), disjointness of sub contradicts i ∈ both.
          by_cases hfTeq : f T = f B
          · exact hiB (hf_inj hT_fam hB_fam hfTeq ▸ hi_T)
          · exact Finset.disjoint_left.mp (hdisj _ hfT_sub _ hfB_sub hfTeq) hi_fT hi_fB
        · exact absurd rfl hij
      intro S hS T hT hST
      rw [Finset.disjoint_left]
      intro x hxS hxT
      -- Case split on membership in sub₀.erase A vs {A'}
      rcases Finset.mem_union.mp hS with hS_era | hS_sing
      · rcases Finset.mem_union.mp hT with hT_era | hT_sing
        · -- Both in sub₀.erase A
          have hS₀ := Finset.erase_subset _ _ hS_era
          have hT₀ := Finset.erase_subset _ _ hT_era
          have hSA := Finset.ne_of_mem_erase hS_era
          have hTA := Finset.ne_of_mem_erase hT_era
          -- By halmost, x = j. Then j ∈ S ∩ f(S) and j ∈ T ∩ f(T).
          -- j ∈ f(S): by franklShift_mem_or, j ∈ S → j ∈ f(S) ∨ i ∈ f(S)
          -- If j ∈ f(S): then j ∈ f(A) ∩ f(S). f(A) = A ∈ sub, f(S) ∈ sub.
          -- If f(A) = f(S): A = S, contradicting S ≠ A.
          -- If f(A) ≠ f(S): disjointness contradiction.
          -- So j ∉ f(S), meaning i ∈ f(S). Similarly i ∈ f(T).
          -- Then i ∈ f(S) ∩ f(T). f(S) ≠ f(T) (since S ≠ T). Disjointness contradiction.
          have hxj := halmost S hS₀ T hT₀ hST x hxS hxT
          have hjS : j ∈ S := hxj ▸ hxS
          have hjT : j ∈ T := hxj ▸ hxT
          have hS_fam := (Finset.mem_filter.mp hS₀).1
          have hT_fam := (Finset.mem_filter.mp hT₀).1
          have hfS_sub := (Finset.mem_filter.mp hS₀).2
          have hfT_sub := (Finset.mem_filter.mp hT₀).2
          -- j ∉ f(S) (else j ∈ f(A) ∩ f(S), contradiction)
          have hjfS : j ∉ f S := by
            intro h
            by_cases hfAeqfS : f A = f S
            · exact hSA (hf_inj hA_fam hS_fam hfAeqfS).symm
            · exact Finset.disjoint_left.mp
                (hdisj _ hfA_sub _ hfS_sub hfAeqfS) hjfA h
          -- j ∉ f(T) (same argument)
          have hjfT : j ∉ f T := by
            intro h
            by_cases hfAeqfT : f A = f T
            · exact hTA (hf_inj hA_fam hT_fam hfAeqfT).symm
            · exact Finset.disjoint_left.mp
                (hdisj _ hfA_sub _ hfT_sub hfAeqfT) hjfA h
          -- So i ∈ f(S) and i ∈ f(T)
          have hi_fS : i ∈ f S := by
            have := franklShift_mem_or i j family S j hjS
            simp only at this
            rcases this with h | ⟨_, h⟩
            · exact absurd h hjfS
            · exact h
          have hi_fT : i ∈ f T := by
            have := franklShift_mem_or i j family T j hjT
            simp only at this
            rcases this with h | ⟨_, h⟩
            · exact absurd h hjfT
            · exact h
          have hfSneT : f S ≠ f T := fun h => hST (hf_inj hS_fam hT_fam h)
          exact Finset.disjoint_left.mp (hdisj _ hfS_sub _ hfT_sub hfSneT) hi_fS hi_fT
        · -- S ∈ sub₀.erase A, T = A'
          rw [Finset.mem_singleton.mp hT_sing] at hxT
          have hS₀ := Finset.erase_subset _ _ hS_era
          have hSA := Finset.ne_of_mem_erase hS_era
          -- x ∈ A' = insert i (A.erase j): x = i or (x ∈ A ∧ x ≠ j)
          rcases Finset.mem_insert.mp hxT with rfl | hxAej
          · -- x = i: i ∉ S by hi_not_mem
            exact hi_not_mem S hS₀ hSA hxS
          · -- x ∈ A.erase j: x ∈ A, x ≠ j, x ∈ S
            have hxA := (Finset.mem_erase.mp hxAej).2
            have hxnj := (Finset.mem_erase.mp hxAej).1
            -- x ∈ S ∩ A, S ≠ A, so x = j by halmost. Contradiction.
            exact hxnj (halmost S hS₀ A hA_sub₀ hSA x hxS hxA)
      · rcases Finset.mem_union.mp hT with hT_era | hT_sing
        · -- S = A', T ∈ sub₀.erase A (symmetric case)
          rw [Finset.mem_singleton.mp hS_sing] at hxS
          have hT₀ := Finset.erase_subset _ _ hT_era
          have hTA := Finset.ne_of_mem_erase hT_era
          rcases Finset.mem_insert.mp hxS with rfl | hxAej
          · exact hi_not_mem T hT₀ hTA hxT
          · have hxA := (Finset.mem_erase.mp hxAej).2
            have hxnj := (Finset.mem_erase.mp hxAej).1
            exact hxnj (halmost T hT₀ A hA_sub₀ hTA x hxT hxA)
        · -- Both are A': S = T, contradiction
          rw [Finset.mem_singleton.mp hS_sing, Finset.mem_singleton.mp hT_sing] at hST
          exact hST rfl
    · -- nonempty
      intro S hS
      rcases Finset.mem_union.mp hS with hS | hS
      · -- S ∈ sub₀.erase A: S ∈ sub₀, so f S ∈ sub, and sub has nonempty elements
        have hS_sub₀ := Finset.erase_subset _ _ hS
        have hS_fam := (Finset.mem_filter.mp hS_sub₀).1
        have hfS_sub := (Finset.mem_filter.mp hS_sub₀).2
        intro hempty
        apply hne (f S) hfS_sub
        subst hempty; simp [f, franklShiftSet]
      · -- S = A': insert i (A.erase j), nonempty because i ∈ A'
        rw [Finset.mem_singleton.mp hS]
        intro hempty
        have := hi_A'; rw [hempty] at this; simp at this

-- Compression stability: in a fully compressed family, replacing any
-- element j ∈ S with any smaller i ∉ S keeps the set in the family.
theorem IsFullyCompressed.replace_mem {family : Finset (Finset (Fin n))}
    (hcomp : IsFullyCompressed family)
    {S : Finset (Fin n)} (hS : S ∈ family) {i j : Fin n}
    (hij : i < j) (hi : i ∉ S) (hj : j ∈ S) :
    insert i (S.erase j) ∈ family := by
  have hstab := hcomp i j hij
  have hS' : franklShiftSet i j S = insert i (S.erase j) := by
    simp [franklShiftSet, hi, hj]
  by_cases hmem : insert i (S.erase j) ∈ family
  · exact hmem
  · have : insert i (S.erase j) ∈ franklShift i j family := by
      unfold franklShift
      rw [Finset.mem_image]
      exact ⟨S, hS, by simp [hS', hmem]⟩
    rwa [hstab] at this

-- The single-shift forward map.
noncomputable def shiftForward (i j : Fin n) (family : Finset (Finset (Fin n)))
    (S : Finset (Fin n)) : Finset (Fin n) :=
  if franklShiftSet i j S ∈ family then S else franklShiftSet i j S

-- shiftForward maps family into franklShift i j family.
theorem shiftForward_mem (i j : Fin n) (family : Finset (Finset (Fin n)))
    (S : Finset (Fin n)) (hS : S ∈ family) :
    shiftForward i j family S ∈ franklShift i j family := by
  unfold shiftForward franklShift
  exact Finset.mem_image.mpr ⟨S, hS, rfl⟩

-- shiftForward is injective on family (from franklShift_card).
theorem shiftForward_injOn (i j : Fin n) (family : Finset (Finset (Fin n))) :
    Set.InjOn (shiftForward i j family) ↑family := by
  rw [← Finset.card_image_iff]
  show (family.image (shiftForward i j family)).card = family.card
  exact franklShift_card i j family

-- Reachability preserves cardinality.
theorem card_reachable (F G : Finset (Finset (Fin n)))
    (hr : ReachableByShifts F G) : G.card = F.card := by
  induction hr with
  | refl _ => rfl
  | step i j heq hr ih => rw [ih, ← heq, franklShift_card]

-- Composed forward bijection: maps family → shifted through the shift chain.
noncomputable def chainForward {F G : Finset (Finset (Fin n))}
    (hr : ReachableByShifts F G) (S : Finset (Fin n)) : Finset (Fin n) :=
  match hr with
  | .refl _ => S
  | .step i j _ hr' => chainForward hr' (shiftForward i j F S)

-- chainForward maps family members into shifted.
theorem chainForward_mem {F G : Finset (Finset (Fin n))}
    (hr : ReachableByShifts F G) (S : Finset (Fin n)) (hS : S ∈ F) :
    chainForward hr S ∈ G := by
  induction hr generalizing S with
  | refl _ => exact hS
  | step i j heq _ ih =>
    simp only [chainForward]
    apply ih
    exact heq ▸ shiftForward_mem i j _ S hS

-- chainForward is injective on family.
theorem chainForward_injOn {F G : Finset (Finset (Fin n))}
    (hr : ReachableByShifts F G) : Set.InjOn (chainForward hr) ↑F := by
  induction hr with
  | refl _ => exact fun _ _ _ _ h => h
  | @step F' G' H' i j heq hr' ih =>
    intro a ha b hb hab
    simp only [chainForward] at hab
    have ha_f := shiftForward_mem i j F' a (Finset.mem_coe.mp ha)
    have hb_f := shiftForward_mem i j F' b (Finset.mem_coe.mp hb)
    have ha_mem : shiftForward i j F' a ∈ G' := heq ▸ ha_f
    have hb_mem : shiftForward i j F' b ∈ G' := heq ▸ hb_f
    have hinj := ih (Finset.mem_coe.mpr ha_mem) (Finset.mem_coe.mpr hb_mem) hab
    exact shiftForward_injOn i j F' ha hb hinj

-- The image of family under chainForward IS shifted.
theorem chainForward_image {F G : Finset (Finset (Fin n))}
    (hr : ReachableByShifts F G) : F.image (chainForward hr) = G := by
  apply Finset.eq_of_subset_of_card_le
  · intro S hS
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
    exact chainForward_mem hr T hT
  · rw [Finset.card_image_of_injOn (chainForward_injOn hr)]
    exact (card_reachable F G hr).le

-- For each S ∈ shifted, there exists a unique T ∈ family with chainForward T = S.
theorem chainForward_surj {F G : Finset (Finset (Fin n))}
    (hr : ReachableByShifts F G) (S : Finset (Fin n)) (hS : S ∈ G) :
    ∃ T ∈ F, chainForward hr T = S := by
  rw [← chainForward_image hr] at hS
  exact Finset.mem_image.mp hS

-- If all shifts of elements land back in F, franklShift is the identity.
theorem franklShift_id_of_forall (i j : Fin n) (F : Finset (Finset (Fin n)))
    (h : ∀ S ∈ F, franklShiftSet i j S ∈ F) :
    franklShift i j F = F := by
  unfold franklShift
  have : ∀ S ∈ F, (fun S => if franklShiftSet i j S ∈ F then S else franklShiftSet i j S) S = S := by
    intro S hS; simp [h S hS]
  rw [Finset.image_congr this]; simp

-- NOTE (i<j repair): franklShift_eq_of_compressed, reachable_compressed_eq,
-- and fullShift_eq were deleted here. Their proofs needed the REVERSE swap
-- (reinsert j, drop i, with i < j), which only bidirectional compression
-- provides; together they forced family = shifted and made mishra_case2
-- vacuous. Under i < j compression they are unprovable (and unwanted).

-- At most one set in a sunflower contains an element outside the kernel.
theorem atMostOne_contains (sub : Finset (Finset (Fin n))) (K : Finset (Fin n))
    (hsf : IsSunflowerWith sub K) (x : Fin n) (hx : x ∉ K) :
    (sub.filter fun S => x ∈ S).card ≤ 1 := by
  by_contra h
  push Not at h
  obtain ⟨S, hS, T, hT, hne⟩ := Finset.one_lt_card.mp h
  simp only [Finset.mem_filter] at hS hT
  have := hsf.2.2 S hS.1 T hT.1 hne
  have : x ∈ S ∩ T := Finset.mem_inter.mpr ⟨hS.2, hT.2⟩
  rw [‹S ∩ T = K›] at this
  exact hx this

-- K = ∅: the sunflower is a matching. Matching number doesn't increase
-- under shifts (Lemma 1(iii)), so |sub| ≤ ν(F*) ≤ ν(F) ≤ τ(F).
-- Matching preservation through ReachableByShifts.
theorem matchingNumber_reachable (F G : Finset (Finset (Fin n)))
    (hr : ReachableByShifts F G)
    (sub : Finset (Finset (Fin n))) (hsub : sub ⊆ G)
    (hdisj : ∀ S ∈ sub, ∀ T ∈ sub, S ≠ T → Disjoint S T)
    (hne : ∀ S ∈ sub, S ≠ ∅) :
    ∃ sub' : Finset (Finset (Fin n)), sub' ⊆ F ∧ sub'.card = sub.card ∧
      (∀ S ∈ sub', ∀ T ∈ sub', S ≠ T → Disjoint S T) ∧
      (∀ S ∈ sub', S ≠ ∅) := by
  induction hr generalizing sub with
  | refl _ => exact ⟨sub, hsub, rfl, hdisj, hne⟩
  | step i j heq hr ih =>
    obtain ⟨mid, hmid, hcarM, hdisjM, hneM⟩ := ih sub hsub hdisj hne
    rw [← heq] at hmid
    obtain ⟨pre, hpre, hcarP, hdisjP, hneP⟩ :=
      matchingNumber_shift_le i j _ mid hmid hdisjM hneM
    exact ⟨pre, hpre, by omega, hdisjP, hneP⟩

theorem empty_kernel_sunflower_le_sunflowerNumber
    (family shifted : Finset (Finset (Fin n)))
    (hshift : IsFullShiftOf shifted family)
    (sub : Finset (Finset (Fin n)))
    (hsub : sub ⊆ shifted)
    (hsf : IsSunflowerWith sub ∅) :
    sub.card ≤ sunflowerNumber family := by
  have hdisj : ∀ S ∈ sub, ∀ T ∈ sub, S ≠ T → Disjoint S T :=
    fun S hS T hT hne => Finset.disjoint_iff_inter_eq_empty.mpr (hsf.2.2 S hS T hT hne)
  have hne : ∀ S ∈ sub, S ≠ ∅ :=
    fun S hS h => hsf.2.1 S hS (by simp [h])
  obtain ⟨sub', hsub', hcard', hdisj', hne'⟩ :=
    matchingNumber_reachable family shifted hshift.reachable sub hsub hdisj hne
  have : HasSunflower family sub'.card :=
    ⟨sub', hsub', rfl, ∅,
     fun S _ => Finset.empty_subset S,
     fun S hS => by simp [hne' S hS],
     fun S hS T hT hne =>
       Finset.disjoint_iff_inter_eq_empty.mp (hdisj' S hS T hT hne)⟩
  rw [← hcard']
  exact le_sunflowerNumber family this

end ShiftTheory
