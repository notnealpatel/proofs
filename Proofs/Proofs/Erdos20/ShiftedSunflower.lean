/-
  Erdős Problem #20 — Sunflower Conjecture for SHIFTED families.
  Formalization of Mishra, "Erdős Rado Sunflower Theorem for Shifted
  Families" (arXiv:2606.02667v2, 2026-06-08), building on the shift
  infrastructure of Sunflower.lean.

  v2 RECONCILIATION: v1 (2026-06-01) claimed the full Erdős–Rado
  conjecture via a bridge lemma, Lemma 3: τ(S(F)) ≤ 3·τ(F)² for the full
  shift endpoint S(F). That statement is false: a 4-uniform family on
  Fin 20 with 17 members and τ = 2 has a full shift endpoint that is a
  17-set star with τ = 17 (machine-checked in Counterexample.lean,
  witness data inline there). v2 drops Lemma 3 and the full-conjecture
  claim, and instead proves the conjecture FOR SHIFTED FAMILIES:

    f'(k,s) ≤ s^(2s-2) · 2^k     (v2 Theorem 1 + Corollary 1)

  via two new ingredients this file formalizes:

    v2 Lemma 4 (shadow bound):  k·|F| ≤ τ(F)·|∂F|   for k-uniform F
      [double-counting pairs (E, S), E ∈ ∂F, E ⊂ S ∈ F; the extensions
       of a fixed (k-1)-set E form a sunflower with kernel E]

    v2 Lemma 5 (star bound):  for shifted F with τ(F) ≤ k, the star
      A_1 = {S ∈ F : 1 ∈ S} has |A_1| ≥ |F|/2
      [the lift E ↦ E ∪ {1} injects ∂B_1 into A_1 by shiftedness, and
       Lemma 4 gives |∂B_1| ≥ |B_1| since τ(B_1) ≤ τ(F) ≤ k]

  plus the standard small-k bound (v2 "Theorem 1 for small k", general
  families): k ≤ s → f(k,s) ≤ s^(2k), by maximal matching + pigeonhole.

  GAPS IN v2 REPAIRED HERE (both minor, both sound):
    (G1) v2's Theorem 1 applies Lemma 5 without establishing τ(F) ≤ k.
         Repair: if s ≤ τ(F) a sunflower of size s already exists
         (τ is attained, sunflowers restrict); otherwise
         τ(F) ≤ s-1 < s ≤ k and Lemma 5 applies.
    (G2) v2 applies the f'(k-1,s) induction hypothesis to the link
         G_1 = {S \ {1} : S ∈ A_1} without proving G_1 is shifted
         (no member of G_1 contains 1, so G_1 is not shifted on [n];
         the intended relabeling {2,…,n} ≅ [n-1] is unstated).
         Repair: `IsShiftedFrom`, shiftedness relative to a ground-set
         lower bound m, with the link at m being `IsShiftedFrom (m+1)`.
         This avoids ground-set relabeling entirely.

  UNCONDITIONAL FORM (§7–§8, beyond the paper's statement): every family
  reaches SOME fully compressed endpoint by a chain of i < j shifts
  (`exists_isFullShiftOf`; termination by the strictly decreasing
  element-value sum `familyMeasure`), and uniformity and cardinality
  transport through chains, so every k-uniform family above the
  threshold has a full shift containing an s-sunflower
  (`exists_shifted_hasSunflower`). The paper instead asserts that the
  canonical C(n,2)-sweep endpoint F_{n-1,n} is compressed and stable,
  citing Frankl's survey without proof; existence of an endpoint is all
  the corollary needs, so that is what we prove. Note the sunflower
  lives in the shifted image: by Counterexample.lean it cannot in
  general be pulled back to the original family.

  NOTATION MAP (paper → Lean):
    "1" (paper, least element)   → ⟨m, hmn⟩ : Fin n at lower bound m
    ∂F                           → ∂ F  (Finset.shadow, FinsetFamily scope)
    A_1 (star at 1)              → F.filter (fun S => a ∈ S)
    B_1                          → F.filter (fun S => a ∉ S)
    G_1 (link of 1)              → sunflowerLink a F
    shifted family               → IsShiftedFrom 0 / IsFullyCompressed
    f'(k,s) ≤ s^(2s-2)·2^k       → IsFullyCompressed.hasSunflower
-/

import Proofs.Erdos20.Sunflower
import Mathlib.Combinatorics.SetFamily.Shadow
import Mathlib.Combinatorics.Enumerative.DoubleCounting

open Finset FinsetFamily

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════
-- §1 SUNFLOWER NUMBER BASICS (monotonicity, attainment, restriction)
-- ════════════════════════════════════════════════════════════════════

section TauBasics

/-- τ is monotone under family inclusion. -/
theorem sunflowerNumber_mono {F G : Finset (Finset (Fin n))} (h : F ⊆ G) :
    sunflowerNumber F ≤ sunflowerNumber G := by
  apply sunflowerNumber_le_of_forall
  intro k hk
  obtain ⟨sub, hsub, hcard, K, hsf⟩ := hk
  exact le_sunflowerNumber G ⟨sub, hsub.trans h, hcard, K, hsf⟩

/-- A sunflower of size `m` contains one of any size `k ≤ m`. -/
theorem HasSunflower.mono {F : Finset (Finset (Fin n))} {k m : ℕ}
    (h : HasSunflower F m) (hkm : k ≤ m) : HasSunflower F k := by
  obtain ⟨sub, hsub, hcard, K, hsf⟩ := h
  obtain ⟨sub', hsub', hcard'⟩ :=
    Finset.exists_subset_card_eq (show k ≤ sub.card by rw [hcard]; exact hkm)
  exact ⟨sub', hsub'.trans hsub, hcard', K, hsf.subset hsub'⟩

/-- τ is attained: the family has a sunflower of size `sunflowerNumber F`. -/
theorem hasSunflower_sunflowerNumber (F : Finset (Finset (Fin n))) :
    HasSunflower F (sunflowerNumber F) := by
  have h := Nat.sSup_mem (s := {k : ℕ | HasSunflower F k})
    ⟨0, hasSunflower_zero F⟩ ⟨F.card, fun m hm => hm.le_card⟩
  exact h

/-- Any size below τ is realized by a sunflower. -/
theorem hasSunflower_of_le_sunflowerNumber {F : Finset (Finset (Fin n))} {s : ℕ}
    (h : s ≤ sunflowerNumber F) : HasSunflower F s :=
  (hasSunflower_sunflowerNumber F).mono h

end TauBasics

-- ════════════════════════════════════════════════════════════════════
-- §2 SHADOW BOUND (v2 Lemma 4): k·|F| ≤ τ(F)·|∂F| for k-uniform F
-- ════════════════════════════════════════════════════════════════════

section ShadowBound

/-- v2 Lemma 4, multiplicative form (avoids division):
    `k * |F| ≤ τ(F) * |∂F|` for a `k`-uniform family.
    Double-counting pairs `(S, E)` with `E ∈ ∂F`, `E = S.erase x`:
    each `S ∈ F` has exactly `k` such `E`; each `E ∈ ∂F` extends to at
    most `τ(F)` members of `F` because the extensions form a sunflower
    with kernel `E`. -/
theorem card_mul_le_sunflowerNumber_mul_shadow (k : ℕ)
    (F : Finset (Finset (Fin n))) (hunif : ∀ S ∈ F, S.card = k) :
    F.card * k ≤ (∂ F).card * sunflowerNumber F := by
  classical
  have h := Finset.card_nsmul_le_card_nsmul
    (r := fun (S E : Finset (Fin n)) => ∃ x ∈ S, S.erase x = E)
    (s := F) (t := ∂ F) (m := k) (n := sunflowerNumber F)
    ?_ ?_
  · simpa [smul_eq_mul] using h
  · -- every k-set has (at least) its k erasures in the shadow
    intro S hS
    have himg : S.image S.erase ⊆
        (∂ F).bipartiteAbove (fun S E => ∃ x ∈ S, S.erase x = E) S := by
      intro E hE
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hE
      exact (Finset.mem_bipartiteAbove _).mpr
        ⟨erase_mem_shadow hS hx, x, hx, rfl⟩
    calc k = S.card := (hunif S hS).symm
      _ = (S.image S.erase).card :=
          (Finset.card_image_of_injOn (Finset.erase_injOn S)).symm
      _ ≤ _ := Finset.card_le_card himg
  · -- the extensions of a fixed E form a sunflower with kernel E
    intro E _hE
    set ext := F.bipartiteBelow (fun S E => ∃ x ∈ S, S.erase x = E) E with hext
    have hsub : ext ⊆ F := fun S hS => ((Finset.mem_bipartiteBelow _).mp hS).1
    have hr : ∀ S ∈ ext, ∃ x ∈ S, S.erase x = E :=
      fun S hS => ((Finset.mem_bipartiteBelow _).mp hS).2
    have hsf : IsSunflowerWith ext E := by
      refine ⟨?_, ?_, ?_⟩
      · intro S hS
        obtain ⟨x, hx, rfl⟩ := hr S hS
        exact Finset.erase_subset _ _
      · intro S hS
        obtain ⟨x, hx, hxE⟩ := hr S hS
        have hxnE : x ∉ E := hxE ▸ Finset.notMem_erase x S
        exact Finset.Nonempty.ne_empty ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxnE⟩⟩
      · intro S hS T hT hne
        obtain ⟨x, hx, hxE⟩ := hr S hS
        obtain ⟨y, hy, hyE⟩ := hr T hT
        have hSx : S = insert x E := by rw [← hxE, Finset.insert_erase hx]
        have hTy : T = insert y E := by rw [← hyE, Finset.insert_erase hy]
        have hxnE : x ∉ E := hxE ▸ Finset.notMem_erase x S
        have hynE : y ∉ E := hyE ▸ Finset.notMem_erase y T
        have hxy : x ≠ y := by
          intro hxyeq
          exact hne (by rw [hSx, hTy, hxyeq])
        ext z
        constructor
        · intro hz
          obtain ⟨hzS, hzT⟩ := Finset.mem_inter.mp hz
          rw [hSx] at hzS
          rw [hTy] at hzT
          rcases Finset.mem_insert.mp hzS with rfl | hzE
          · rcases Finset.mem_insert.mp hzT with h | h
            · exact absurd h hxy
            · exact absurd h hxnE
          · exact hzE
        · intro hz
          refine Finset.mem_inter.mpr ⟨?_, ?_⟩
          · rw [hSx]; exact Finset.mem_insert_of_mem hz
          · rw [hTy]; exact Finset.mem_insert_of_mem hz
    exact le_sunflowerNumber F ⟨ext, hsub, rfl, E, hsf⟩

end ShadowBound

-- ════════════════════════════════════════════════════════════════════
-- §3 SHIFTEDNESS RELATIVE TO A LOWER BOUND (repairs v2 gap G2)
-- ════════════════════════════════════════════════════════════════════

section ShiftedFrom

/-- A family is shifted from `m` when every member lives on `{m, …, n-1}`
    and replacing any `j ∈ S` by any smaller `i ∉ S` with `m ≤ i` stays in
    the family. `IsShiftedFrom 0` is the usual shiftedness; links shift the
    bound up by one. (Paper: "shifted", v2 §2; the relative bound is ours.) -/
def IsShiftedFrom (m : ℕ) (F : Finset (Finset (Fin n))) : Prop :=
  (∀ S ∈ F, ∀ x ∈ S, m ≤ x.val) ∧
  (∀ S ∈ F, ∀ i j : Fin n, m ≤ i.val → i < j → i ∉ S → j ∈ S →
    insert i (S.erase j) ∈ F)

/-- A fully compressed family is shifted from `0`. -/
theorem IsFullyCompressed.isShiftedFrom_zero {F : Finset (Finset (Fin n))}
    (h : IsFullyCompressed F) : IsShiftedFrom 0 F :=
  ⟨fun _ _ _ _ => Nat.zero_le _,
   fun _ hS _ _ _ hij hi hj => h.replace_mem hS hij hi hj⟩

/-- v2 Lemma 5 (star bound), instance at the least available element:
    for `F` shifted from `m`, `k`-uniform, with `τ(F) ≤ k`, the star at
    `m` captures at least half the family: `|F| ≤ 2·|A|` where
    `A = {S ∈ F : m ∈ S}`. -/
theorem IsShiftedFrom.star_card_half {m k : ℕ} {F : Finset (Finset (Fin n))}
    (hshift : IsShiftedFrom m F) (hunif : ∀ S ∈ F, S.card = k)
    (hτ : sunflowerNumber F ≤ k) (hk : 1 ≤ k) (hmn : m < n) :
    F.card ≤ 2 * (F.filter fun S => (⟨m, hmn⟩ : Fin n) ∈ S).card := by
  classical
  set a : Fin n := ⟨m, hmn⟩ with ha
  set A := F.filter (fun S => a ∈ S) with hA
  set B := F.filter (fun S => a ∉ S) with hB
  -- |F| = |A| + |B|
  have hpart : A.card + B.card = F.card :=
    Finset.card_filter_add_card_filter_not (s := F) (fun S => a ∈ S)
  -- B is k-uniform
  have hBsub : B ⊆ F := Finset.filter_subset _ _
  have hBunif : ∀ S ∈ B, S.card = k := fun S hS => hunif S (hBsub hS)
  -- Lemma 4 on B, then τ(B) ≤ τ(F) ≤ k cancels against k-uniformity
  have hshadow : B.card * k ≤ (∂ B).card * k := by
    calc B.card * k ≤ (∂ B).card * sunflowerNumber B :=
          card_mul_le_sunflowerNumber_mul_shadow k B hBunif
      _ ≤ (∂ B).card * k :=
          Nat.mul_le_mul_left _ ((sunflowerNumber_mono hBsub).trans hτ)
  have hBshadow : B.card ≤ (∂ B).card :=
    Nat.le_of_mul_le_mul_right hshadow hk
  -- the lift E ↦ insert a E injects ∂B into A (this is where shiftedness acts)
  have hlift : ∀ E ∈ ∂ B, insert a E ∈ A := by
    intro E hE
    obtain ⟨S, hS, x, hx, rfl⟩ := mem_shadow_iff.mp hE
    have hSF : S ∈ F := hBsub hS
    have haS : a ∉ S := (Finset.mem_filter.mp hS).2
    have hax : a < x := by
      have hmx : m ≤ x.val := hshift.1 S hSF x hx
      have hxa : x ≠ a := fun h => haS (h ▸ hx)
      have : m < x.val :=
        lt_of_le_of_ne hmx (fun h => hxa (Fin.ext h.symm))
      exact this
    have hmem : insert a (S.erase x) ∈ F :=
      hshift.2 S hSF a x (le_refl m) hax haS hx
    exact Finset.mem_filter.mpr ⟨hmem, Finset.mem_insert_self a _⟩
  have hnotmem : ∀ E ∈ ∂ B, a ∉ E := by
    intro E hE
    obtain ⟨S, hS, x, hx, rfl⟩ := mem_shadow_iff.mp hE
    have haS : a ∉ S := (Finset.mem_filter.mp hS).2
    exact fun h => haS (Finset.mem_of_mem_erase h)
  have hinj : (∂ B).card ≤ A.card := by
    apply Finset.card_le_card_of_injOn (fun E => insert a E) hlift
    intro E₁ hE₁ E₂ hE₂ heq
    have h₁ : a ∉ E₁ := hnotmem E₁ (Finset.mem_coe.mp hE₁)
    have h₂ : a ∉ E₂ := hnotmem E₂ (Finset.mem_coe.mp hE₂)
    have heq' : insert a E₁ = insert a E₂ := heq
    calc E₁ = (insert a E₁).erase a := (Finset.erase_insert h₁).symm
      _ = (insert a E₂).erase a := by rw [heq']
      _ = E₂ := Finset.erase_insert h₂
  omega

end ShiftedFrom

-- ════════════════════════════════════════════════════════════════════
-- §4 LINKS (paper's G_1 = "link of 1")
-- ════════════════════════════════════════════════════════════════════

section Link

/-- The link of `a`: members containing `a`, with `a` removed. -/
def sunflowerLink (a : Fin n) (F : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  (F.filter fun S => a ∈ S).image fun S => S.erase a

/-- The link has the size of the star at `a`. -/
theorem sunflowerLink_card (a : Fin n) (F : Finset (Finset (Fin n))) :
    (sunflowerLink a F).card = (F.filter fun S => a ∈ S).card := by
  apply Finset.card_image_of_injOn
  intro S hS T hT heq
  have hSa : a ∈ S := (Finset.mem_filter.mp (Finset.mem_coe.mp hS)).2
  have hTa : a ∈ T := (Finset.mem_filter.mp (Finset.mem_coe.mp hT)).2
  have heq' : S.erase a = T.erase a := heq
  calc S = insert a (S.erase a) := (Finset.insert_erase hSa).symm
    _ = insert a (T.erase a) := by rw [heq']
    _ = T := Finset.insert_erase hTa

/-- The link of a `k`-uniform family is `(k-1)`-uniform. -/
theorem sunflowerLink_uniform {a : Fin n} {F : Finset (Finset (Fin n))} {k : ℕ}
    (hunif : ∀ S ∈ F, S.card = k) :
    ∀ E ∈ sunflowerLink a F, E.card = k - 1 := by
  intro E hE
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hE
  have hSF : S ∈ F := (Finset.mem_filter.mp hS).1
  have hSa : a ∈ S := (Finset.mem_filter.mp hS).2
  rw [Finset.card_erase_of_mem hSa, hunif S hSF]

/-- Links at the least available element preserve shiftedness, with the
    lower bound moving up by one. (Repairs v2 gap G2.) -/
theorem IsShiftedFrom.link_shifted {m : ℕ} {F : Finset (Finset (Fin n))}
    (hshift : IsShiftedFrom m F) (hmn : m < n) :
    IsShiftedFrom (m + 1) (sunflowerLink ⟨m, hmn⟩ F) := by
  set a : Fin n := ⟨m, hmn⟩ with ha
  constructor
  · -- ground bound moves up: members avoid a and sit above m
    intro E hE x hx
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hE
    have hSF : S ∈ F := (Finset.mem_filter.mp hS).1
    have hxS : x ∈ S := Finset.mem_of_mem_erase hx
    have hxm : m ≤ x.val := hshift.1 S hSF x hxS
    have hxa : x ≠ a := (Finset.mem_erase.mp hx).1
    have hxm' : x.val ≠ m := fun h => hxa (Fin.ext h)
    omega
  · -- shift property survives the link
    intro E hE i j hi hij hiE hjE
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hE
    have hSF : S ∈ F := (Finset.mem_filter.mp hS).1
    have haS : a ∈ S := (Finset.mem_filter.mp hS).2
    have hjS : j ∈ S := Finset.mem_of_mem_erase hjE
    have hia : i ≠ a := by
      intro h
      have : i.val = m := by rw [h]
      omega
    have hiS : i ∉ S := fun h => hiE (Finset.mem_erase.mpr ⟨hia, h⟩)
    have hmem : insert i (S.erase j) ∈ F :=
      hshift.2 S hSF i j (by omega) hij hiS hjS
    have haj : a ≠ j := fun h => (Finset.mem_erase.mp hjE).1 h.symm
    refine Finset.mem_image.mpr
      ⟨insert i (S.erase j), Finset.mem_filter.mpr ⟨hmem, ?_⟩, ?_⟩
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨haj, haS⟩)
    · show (insert i (S.erase j)).erase a = insert i ((S.erase a).erase j)
      rw [Finset.erase_insert_of_ne hia, Finset.erase_right_comm]

/-- A sunflower in the link lifts to a sunflower in the family
    (add the hinge back to every petal; kernel grows by the hinge).
    Used by both the small-k theorem and the main recurrence. -/
theorem HasSunflower.of_link {a : Fin n} {F : Finset (Finset (Fin n))} {s : ℕ}
    (h : HasSunflower (sunflowerLink a F) s) : HasSunflower F s := by
  obtain ⟨sub, hsub, hcard, K, hsf⟩ := h
  have hmemF : ∀ E ∈ sub, insert a E ∈ F := by
    intro E hE
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp (hsub hE)
    rw [Finset.insert_erase (Finset.mem_filter.mp hS).2]
    exact (Finset.mem_filter.mp hS).1
  have hnotmem : ∀ E ∈ sub, a ∉ E := by
    intro E hE
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp (hsub hE)
    exact Finset.notMem_erase a S
  have hinj : Set.InjOn (fun E => insert a E) (sub : Set (Finset (Fin n))) := by
    intro E₁ hE₁ E₂ hE₂ heq
    have heq' : insert a E₁ = insert a E₂ := heq
    calc E₁ = (insert a E₁).erase a :=
          (Finset.erase_insert (hnotmem E₁ hE₁)).symm
      _ = (insert a E₂).erase a := by rw [heq']
      _ = E₂ := Finset.erase_insert (hnotmem E₂ hE₂)
  refine ⟨sub.image (fun E => insert a E), ?_, ?_, insert a K, ?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hT
    exact hmemF E hE
  · rw [Finset.card_image_of_injOn hinj, hcard]
  · -- kernel inclusion
    intro T hT
    obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hT
    exact Finset.insert_subset_insert a (hsf.1 E hE)
  · -- nonempty petals
    intro T hT
    obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hT
    have hpetal := hsf.2.1 E hE
    rw [ne_eq, Finset.sdiff_eq_empty_iff_subset] at hpetal
    obtain ⟨x, hxE, hxK⟩ := Finset.not_subset.mp hpetal
    have hxa : x ≠ a := fun h => hnotmem E hE (h ▸ hxE)
    rw [ne_eq, Finset.sdiff_eq_empty_iff_subset, Finset.not_subset]
    refine ⟨x, Finset.mem_insert_of_mem hxE, fun habs => ?_⟩
    rcases Finset.mem_insert.mp habs with h | h
    · exact hxa h
    · exact hxK h
  · -- pairwise intersections
    intro T₁ hT₁ T₂ hT₂ hne
    obtain ⟨E₁, hE₁, rfl⟩ := Finset.mem_image.mp hT₁
    obtain ⟨E₂, hE₂, rfl⟩ := Finset.mem_image.mp hT₂
    have hEne : E₁ ≠ E₂ := fun h => hne (by rw [h])
    rw [← Finset.insert_inter_distrib, hsf.2.2 E₁ hE₁ E₂ hE₂ hEne]

end Link

-- ════════════════════════════════════════════════════════════════════
-- §5 SMALL k (v2 "Theorem 1 for small k", GENERAL families):
--    k ≤ s → any k-uniform family larger than s^(2k) has an s-sunflower
-- ════════════════════════════════════════════════════════════════════

section SmallK

/-- v2 small-k theorem (general families, no shiftedness): if `k ≤ s` and
    `|F| > s^(2k)` for a `k`-uniform `F`, then `F` has an `s`-sunflower.
    Standard Erdős–Rado-style argument: a maximum matching of size `≥ s`
    is itself an `s`-sunflower (empty kernel); otherwise the matching's
    union `U` (`|U| ≤ k(s-1)`) meets every member, pigeonhole gives a
    hinge `x` with star larger than `s^(2(k-1))`, and induction applies
    to the link of `x`. -/
theorem hasSunflower_of_small_uniformity :
    ∀ k s : ℕ, k ≤ s → ∀ F : Finset (Finset (Fin n)),
    (∀ S ∈ F, S.card = k) → s ^ (2 * k) < F.card → HasSunflower F s := by
  intro k
  induction k with
  | zero =>
    -- 0-uniform families fit in {∅}: the cardinality premise is vacuous
    intro s _ F hunif hcard
    exfalso
    have hsub : F ⊆ {∅} := fun S hS =>
      Finset.mem_singleton.mpr (Finset.card_eq_zero.mp (hunif S hS))
    have h1 : F.card ≤ 1 :=
      le_trans (Finset.card_le_card hsub) (by simp)
    simp only [Nat.mul_zero, pow_zero] at hcard
    omega
  | succ k ih =>
    intro s hks F hunif hcard
    classical
    have hs1 : 1 ≤ s := by omega
    -- a maximum matching M ⊆ F
    set MS := F.powerset.filter
      (fun M => ∀ S ∈ M, ∀ T ∈ M, S ≠ T → Disjoint S T) with hMS
    have hMS_ne : MS.Nonempty := by
      refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset F, ?_⟩⟩
      intro S hS
      simp at hS
    obtain ⟨M, hM_mem, hM_max⟩ := Finset.exists_max_image MS Finset.card hMS_ne
    have hM_sub : M ⊆ F := Finset.mem_powerset.mp (Finset.mem_filter.mp hM_mem).1
    have hM_disj : ∀ S ∈ M, ∀ T ∈ M, S ≠ T → Disjoint S T :=
      (Finset.mem_filter.mp hM_mem).2
    by_cases hMcard : s ≤ M.card
    · -- a matching of size ≥ s is an s-sunflower with empty kernel
      obtain ⟨M', hM'_sub, hM'_card⟩ := Finset.exists_subset_card_eq hMcard
      refine ⟨M', hM'_sub.trans hM_sub, hM'_card, ∅, ?_, ?_, ?_⟩
      · intro S _
        exact Finset.empty_subset S
      · intro S hS
        have hcardS : S.card = k + 1 := hunif S (hM_sub (hM'_sub hS))
        intro habs
        rw [Finset.sdiff_empty] at habs
        rw [habs] at hcardS
        simp at hcardS
      · intro S hS T hT hne
        exact Finset.disjoint_iff_inter_eq_empty.mp
          (hM_disj S (hM'_sub hS) T (hM'_sub hT) hne)
    · push Not at hMcard
      -- the matching's union U meets every member of F
      set U := M.biUnion id with hU
      have hUcard : U.card ≤ (k + 1) * M.card := by
        calc U.card ≤ ∑ S ∈ M, S.card := Finset.card_biUnion_le
          _ = (k + 1) * M.card := by
              rw [Finset.sum_congr rfl (fun S hS => hunif S (hM_sub hS)),
                Finset.sum_const, smul_eq_mul, mul_comm]
      have hmeet : ∀ S ∈ F, (S ∩ U).Nonempty := by
        intro S hS
        by_contra hdis
        rw [Finset.not_nonempty_iff_eq_empty] at hdis
        have hSdisU : Disjoint S U := Finset.disjoint_iff_inter_eq_empty.mpr hdis
        have hSnotM : S ∉ M := by
          intro hSM
          have hSU : S ⊆ U := by
            intro x hx
            exact Finset.mem_biUnion.mpr ⟨S, hSM, hx⟩
          have hSe : S = ∅ := by
            have h := Finset.inter_eq_left.mpr hSU
            rw [hdis] at h
            exact h.symm
          have hSk := hunif S hS
          rw [hSe] at hSk
          simp at hSk
        have hbig : insert S M ∈ MS := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
          · intro T hT
            rcases Finset.mem_insert.mp hT with rfl | hTM
            · exact hS
            · exact hM_sub hTM
          · intro A hA B hB hAB
            rcases Finset.mem_insert.mp hA with rfl | hAM <;>
              rcases Finset.mem_insert.mp hB with rfl | hBM
            · exact absurd rfl hAB
            · have hBU : B ⊆ U := fun x hx => Finset.mem_biUnion.mpr ⟨B, hBM, hx⟩
              exact hSdisU.mono_right hBU
            · have hAU : A ⊆ U := fun x hx => Finset.mem_biUnion.mpr ⟨A, hAM, hx⟩
              exact (hSdisU.mono_right hAU).symm
            · exact hM_disj A hAM B hBM hAB
        have hgrow := hM_max _ hbig
        rw [Finset.card_insert_of_notMem hSnotM] at hgrow
        omega
      -- pigeonhole: some x ∈ U is in more than s^(2k) members
      have hstar : ∃ x ∈ U, s ^ (2 * k) < (F.filter (fun S => x ∈ S)).card := by
        by_contra hno
        push Not at hno
        have hcount := Finset.card_nsmul_le_card_nsmul
          (r := fun (S : Finset (Fin n)) (x : Fin n) => x ∈ S)
          (s := F) (t := U) (m := 1) (n := s ^ (2 * k)) ?_ ?_
        · simp only [smul_eq_mul, mul_one] at hcount
          have hpos : 0 < s ^ (2 * k) := pow_pos (by omega) _
          have hb : s ^ (2 * (k + 1)) = s * s * s ^ (2 * k) := by ring
          have c2 : U.card * s ^ (2 * k) ≤ ((k + 1) * M.card) * s ^ (2 * k) :=
            Nat.mul_le_mul_right _ hUcard
          have c3 : (k + 1) * M.card ≤ (k + 1) * (s - 1) :=
            Nat.mul_le_mul_left _ (by omega)
          have c4 : ((k + 1) * M.card) * s ^ (2 * k) ≤
              ((k + 1) * (s - 1)) * s ^ (2 * k) :=
            Nat.mul_le_mul_right _ c3
          have c5' : (k + 1) * (s - 1) < s * s := by
            obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
            simp only [Nat.add_sub_cancel]
            nlinarith [hks]
          have c5 : ((k + 1) * (s - 1)) * s ^ (2 * k) < s ^ (2 * (k + 1)) := by
            rw [hb]
            exact mul_lt_mul_of_pos_right c5' hpos
          omega
        · intro S hS
          obtain ⟨x, hx⟩ := hmeet S hS
          have hx' := Finset.mem_inter.mp hx
          exact Finset.card_pos.mpr
            ⟨x, (Finset.mem_bipartiteAbove _).mpr ⟨hx'.2, hx'.1⟩⟩
        · intro x hxU
          exact hno x hxU
      obtain ⟨x, hxU, hxstar⟩ := hstar
      -- recurse into the link of x
      have hlink_card : s ^ (2 * k) < (sunflowerLink x F).card := by
        rw [sunflowerLink_card]
        exact hxstar
      have hlink_unif : ∀ E ∈ sunflowerLink x F, E.card = k := by
        intro E hE
        have := sunflowerLink_uniform (a := x) (F := F) hunif E hE
        omega
      exact (ih s (by omega) (sunflowerLink x F) hlink_unif hlink_card).of_link

end SmallK

-- ════════════════════════════════════════════════════════════════════
-- §6 MAIN THEOREM (v2 Theorem 1 + Corollary 1, shifted families)
-- ════════════════════════════════════════════════════════════════════

section Main

/-- Master induction (v2 Theorem 1 recurrence, closed form):
    a family shifted from `m`, `k`-uniform, larger than `s^(2(s-1))·2^k`
    has an `s`-sunflower. Induction on `k`: below `s` the small-k theorem
    applies; otherwise either `τ(F) ≥ s` (done) or the star at `m` holds
    half the family and the link (shifted from `m+1`) recurses. -/
theorem IsShiftedFrom.hasSunflower {s : ℕ} (hs : 1 ≤ s) :
    ∀ k m : ℕ, ∀ F : Finset (Finset (Fin n)), IsShiftedFrom m F →
    (∀ S ∈ F, S.card = k) →
    s ^ (2 * (s - 1)) * 2 ^ k < F.card → HasSunflower F s := by
  intro k
  induction k with
  | zero =>
    -- 0-uniform: |F| ≤ 1, but the threshold is at least 1
    intro m F _ hunif hcard
    exfalso
    have hsub : F ⊆ {∅} := fun S hS =>
      Finset.mem_singleton.mpr (Finset.card_eq_zero.mp (hunif S hS))
    have h1 : F.card ≤ 1 :=
      le_trans (Finset.card_le_card hsub) (by simp)
    have h2 : 1 ≤ s ^ (2 * (s - 1)) * 2 ^ 0 := by
      rw [pow_zero, mul_one]
      exact Nat.one_le_pow _ _ hs
    omega
  | succ k ih =>
    intro m F hshift hunif hcard
    by_cases hsmall : k + 1 ≤ s - 1
    · -- below the threshold dimension: the small-k theorem applies
      apply hasSunflower_of_small_uniformity (k + 1) s (by omega) F hunif
      have h1 : s ^ (2 * (k + 1)) ≤ s ^ (2 * (s - 1)) :=
        Nat.pow_le_pow_right hs (by omega)
      have h2 : s ^ (2 * (s - 1)) ≤ s ^ (2 * (s - 1)) * 2 ^ (k + 1) :=
        Nat.le_mul_of_pos_right _ (by positivity)
      omega
    · -- recurrence: either τ(F) ≥ s (done) or the star holds half of F
      push Not at hsmall
      by_cases hτ : s ≤ sunflowerNumber F
      · exact hasSunflower_of_le_sunflowerNumber hτ
      · push Not at hτ
        -- the ground-set bound m is realized: F has a nonempty member
        have hF_ne : F.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨S₀, hS₀⟩ := hF_ne
        have hS₀ne : S₀.Nonempty := by
          rw [← Finset.card_pos, hunif S₀ hS₀]
          omega
        obtain ⟨x₀, hx₀⟩ := hS₀ne
        have hmn : m < n := by
          have h1 : m ≤ x₀.val := hshift.1 S₀ hS₀ x₀ hx₀
          have h2 : x₀.val < n := x₀.isLt
          omega
        -- v2 Lemma 5: the star at m captures half the family
        have hτk : sunflowerNumber F ≤ k + 1 := by omega
        have hstar := hshift.star_card_half hunif hτk (by omega) hmn
        have h2k : s ^ (2 * (s - 1)) * 2 ^ (k + 1) =
            2 * (s ^ (2 * (s - 1)) * 2 ^ k) := by ring
        have hlink_card : s ^ (2 * (s - 1)) * 2 ^ k <
            (sunflowerLink ⟨m, hmn⟩ F).card := by
          rw [sunflowerLink_card]
          omega
        have hlink_unif : ∀ E ∈ sunflowerLink ⟨m, hmn⟩ F, E.card = k := by
          intro E hE
          have := sunflowerLink_uniform (a := ⟨m, hmn⟩) (F := F) hunif E hE
          omega
        exact (ih (m + 1) (sunflowerLink ⟨m, hmn⟩ F)
          (hshift.link_shifted hmn) hlink_unif hlink_card).of_link

/-- v2 HEADLINE (Theorem 1 + Corollary 1): the Erdős–Rado sunflower
    conjecture for shifted (fully compressed) families, with
    `C(s) = 2·s^(2s-2)`: any shifted `k`-uniform family with more than
    `s^(2s-2)·2^k` members contains an `s`-sunflower. -/
theorem IsFullyCompressed.hasSunflower {s k : ℕ} (hs : 1 ≤ s)
    {F : Finset (Finset (Fin n))} (hcomp : IsFullyCompressed F)
    (hunif : ∀ S ∈ F, S.card = k)
    (hcard : s ^ (2 * (s - 1)) * 2 ^ k < F.card) : HasSunflower F s :=
  IsShiftedFrom.hasSunflower hs k 0 F hcomp.isShiftedFrom_zero hunif hcard

end Main

-- ════════════════════════════════════════════════════════════════════
-- §7 SHIFT CHAINS MEET THE MAIN THEOREM
--    Any full shift of a large k-uniform family has an s-sunflower:
--    uniformity and size transport through the chain (Lemma 1(i)/(ii)),
--    then IsFullyCompressed.hasSunflower fires on the shifted family.
-- ════════════════════════════════════════════════════════════════════

section FullShift

/-- v2 Lemma 1(i): a single set-level shift preserves cardinality
    (`insert i (S.erase j)` trades `j ∈ S` for `i ∉ S` one-for-one). -/
theorem franklShiftSet_card (i j : Fin n) (S : Finset (Fin n)) :
    (franklShiftSet i j S).card = S.card := by
  unfold franklShiftSet
  split_ifs with h
  · have hie : i ∉ S.erase j := fun hmem => h.1 (Finset.mem_of_mem_erase hmem)
    have hS : 1 ≤ S.card := Finset.card_pos.mpr ⟨j, h.2⟩
    rw [Finset.card_insert_of_notMem hie, Finset.card_erase_of_mem h.2]
    omega
  · rfl

/-- A single family-level shift preserves `k`-uniformity: each image set
    is either an original member or its set-level shift. -/
theorem franklShift_uniform (i j : Fin n) {family : Finset (Finset (Fin n))} {k : ℕ}
    (hunif : ∀ S ∈ family, S.card = k) :
    ∀ S ∈ franklShift i j family, S.card = k := by
  intro S hS
  obtain ⟨T, hT, heq⟩ := Finset.mem_image.mp hS
  simp only at heq
  rw [← heq]
  split_ifs
  · exact hunif T hT
  · rw [franklShiftSet_card]
    exact hunif T hT

/-- `k`-uniformity transports through shift chains. -/
theorem reachable_uniform {F G : Finset (Finset (Fin n))} {k : ℕ}
    (hr : ReachableByShifts F G) (hunif : ∀ S ∈ F, S.card = k) :
    ∀ S ∈ G, S.card = k := by
  induction hr with
  | refl _ => exact hunif
  | step i j heq hr ih => exact ih (heq ▸ franklShift_uniform i j hunif)

/-- The full shift of a `k`-uniform family is `k`-uniform. -/
theorem IsFullShiftOf.uniform {original shifted : Finset (Finset (Fin n))} {k : ℕ}
    (hshift : IsFullShiftOf shifted original)
    (hunif : ∀ S ∈ original, S.card = k) :
    ∀ S ∈ shifted, S.card = k :=
  reachable_uniform hshift.reachable hunif

/-- Corollary of the v2 headline: the full shift of any `k`-uniform family
    with more than `s^(2s-2)·2^k` members contains an `s`-sunflower.
    Uniformity and cardinality transport along the shift chain, and the
    shifted family is fully compressed, so `IsFullyCompressed.hasSunflower`
    applies. -/
theorem IsFullShiftOf.hasSunflower {s k : ℕ} (hs : 1 ≤ s)
    {original shifted : Finset (Finset (Fin n))}
    (hshift : IsFullShiftOf shifted original)
    (hunif : ∀ S ∈ original, S.card = k)
    (hcard : s ^ (2 * (s - 1)) * 2 ^ k < original.card) :
    HasSunflower shifted s := by
  apply IsFullyCompressed.hasSunflower hs hshift.compressed (hshift.uniform hunif)
  rw [card_reachable original shifted hshift.reachable]
  exact hcard

end FullShift

-- ════════════════════════════════════════════════════════════════════
-- §8 EXISTENCE OF THE FULL SHIFT (termination of the compression chain)
--    Frankl's monovariant: the total element-value sum strictly
--    decreases under every nontrivial i<j shift, so iterated shifting
--    reaches a fully compressed family. (Same pattern as Mathlib's
--    KruskalKatona termination, with plain value weights instead of 2^a
--    since a single shift swaps exactly one element.) Combined with §7
--    this gives the unconditional form of the headline theorem.
-- ════════════════════════════════════════════════════════════════════

section ShiftTermination

/-- Termination measure for the compression chain: the total
    element-value sum of the family. -/
def familyMeasure (F : Finset (Finset (Fin n))) : ℕ :=
  ∑ S ∈ F, ∑ x ∈ S, x.val

/-- A genuine set-level shift (replace `j ∈ S` by `i ∉ S` with `i < j`)
    strictly decreases the element-value sum. -/
theorem sum_franklShiftSet_lt {i j : Fin n} (hij : i < j) {S : Finset (Fin n)}
    (hi : i ∉ S) (hj : j ∈ S) :
    ∑ x ∈ franklShiftSet i j S, x.val < ∑ x ∈ S, x.val := by
  have heq : franklShiftSet i j S = insert i (S.erase j) := by
    unfold franklShiftSet; rw [if_pos ⟨hi, hj⟩]
  have hie : i ∉ S.erase j := fun h => hi (Finset.mem_of_mem_erase h)
  rw [heq, Finset.sum_insert hie]
  have hsum : (∑ x ∈ S.erase j, x.val) + j.val = ∑ x ∈ S, x.val :=
    Finset.sum_erase_add S _ hj
  have hij' : i.val < j.val := hij
  omega

/-- `franklShift` is the image of the single-shift forward map. -/
theorem franklShift_eq_image (i j : Fin n) (F : Finset (Finset (Fin n))) :
    franklShift i j F = F.image (shiftForward i j F) := rfl

/-- Key decrease lemma: a nontrivial family-level shift with `i < j`
    strictly decreases the measure. The forward map is injective on `F`
    (Lemma 1(ii)), fixes every set whose shift collides with `F`, and
    strictly decreases the element-value sum of at least one set. -/
theorem familyMeasure_franklShift_lt {i j : Fin n} (hij : i < j)
    {F : Finset (Finset (Fin n))} (hne : franklShift i j F ≠ F) :
    familyMeasure (franklShift i j F) < familyMeasure F := by
  classical
  unfold familyMeasure
  rw [franklShift_eq_image, Finset.sum_image (shiftForward_injOn i j F)]
  -- any set moved by the forward map strictly loses measure
  have key : ∀ S ∈ F, shiftForward i j F S ≠ S →
      ∑ x ∈ shiftForward i j F S, x.val < ∑ x ∈ S, x.val := by
    intro S hS hmove
    have hmem : franklShiftSet i j S ∉ F := by
      intro h
      exact hmove (by unfold shiftForward; rw [if_pos h])
    have hcond : i ∉ S ∧ j ∈ S := by
      by_contra hc
      have heq : franklShiftSet i j S = S := by
        unfold franklShiftSet; rw [if_neg hc]
      exact hmem (by rw [heq]; exact hS)
    have heq : shiftForward i j F S = franklShiftSet i j S := by
      unfold shiftForward; rw [if_neg hmem]
    rw [heq]
    exact sum_franklShiftSet_lt hij hcond.1 hcond.2
  apply Finset.sum_lt_sum
  · intro S hS
    by_cases hmove : shiftForward i j F S = S
    · rw [hmove]
    · exact (key S hS hmove).le
  · -- hne forces at least one set to move
    obtain ⟨S, hS, hmove⟩ : ∃ S ∈ F, shiftForward i j F S ≠ S := by
      by_contra hall
      push Not at hall
      refine hne (franklShift_id_of_forall i j F fun S hS => ?_)
      have hfix := hall S hS
      unfold shiftForward at hfix
      split_ifs at hfix with h
      · exact h
      · rw [hfix]; exact hS
    exact ⟨S, hS, key S hS hmove⟩

/-- Auxiliary induction on a measure bound: any family whose measure is
    at most `N` reaches a fully compressed family by a shift chain. -/
theorem exists_isFullShiftOf_of_measure_le :
    ∀ N : ℕ, ∀ F : Finset (Finset (Fin n)), familyMeasure F ≤ N →
    ∃ shifted : Finset (Finset (Fin n)), Nonempty (IsFullShiftOf shifted F) := by
  intro N
  induction N with
  | zero =>
    intro F hF
    by_cases hcomp : IsFullyCompressed F
    · exact ⟨F, ⟨⟨hcomp, .refl F⟩⟩⟩
    · exfalso
      unfold IsFullyCompressed at hcomp
      push Not at hcomp
      obtain ⟨i, j, hij, hne⟩ := hcomp
      have := familyMeasure_franklShift_lt hij hne
      omega
  | succ N ih =>
    intro F hF
    by_cases hcomp : IsFullyCompressed F
    · exact ⟨F, ⟨⟨hcomp, .refl F⟩⟩⟩
    · unfold IsFullyCompressed at hcomp
      push Not at hcomp
      obtain ⟨i, j, hij, hne⟩ := hcomp
      have hlt := familyMeasure_franklShift_lt hij hne
      obtain ⟨shifted, ⟨hfs⟩⟩ := ih (franklShift i j F) (by omega)
      exact ⟨shifted, ⟨⟨hfs.compressed, .step i j rfl hfs.reachable⟩⟩⟩

/-- Every family has a fully compressed shift endpoint. -/
theorem exists_isFullShiftOf (family : Finset (Finset (Fin n))) :
    ∃ shifted : Finset (Finset (Fin n)), Nonempty (IsFullShiftOf shifted family) :=
  exists_isFullShiftOf_of_measure_le (familyMeasure family) family le_rfl

/-- Unconditional form of the v2 headline: every `k`-uniform family with
    more than `s^(2s-2)·2^k` members has a full shift containing an
    `s`-sunflower. -/
theorem exists_shifted_hasSunflower {s k : ℕ} (hs : 1 ≤ s)
    {family : Finset (Finset (Fin n))}
    (hunif : ∀ S ∈ family, S.card = k)
    (hcard : s ^ (2 * (s - 1)) * 2 ^ k < family.card) :
    ∃ shifted : Finset (Finset (Fin n)),
      ∃ _ : IsFullShiftOf shifted family, HasSunflower shifted s := by
  obtain ⟨shifted, ⟨hfs⟩⟩ := exists_isFullShiftOf family
  exact ⟨shifted, hfs, hfs.hasSunflower hs hunif hcard⟩

end ShiftTermination
