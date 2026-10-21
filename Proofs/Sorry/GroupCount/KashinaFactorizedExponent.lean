/-
# Exponents of factorized groups (Natale's question, Kashina-type divisibility)

## Source

arXiv:2608.14972, "Exponents of factorized groups and Kashina's conjecture for
group-theoretical Hopf algebras" (math.QA, math.GR), authors as listed on the
arXiv abstract page: Ningyi Li. v1 submitted 2026-08-15; v2 (2026-10-08) is
marked withdrawn at the request of a co-author. The TeX source could not be
retrieved (arXiv 404 on `fetch 2608.14972`), so the theorem number is unknown;
the statement sits in the abstract as the main group-theoretic theorem.

Informal claim (abstract, paraphrased by the arXiv listing): for a
factorization `G = F Γ` of a finite group `G` into subgroups `F` and `Γ`
(neither assumed normal, intersection allowed to be nontrivial), the exponent
of `G` divides `lcm(|F|, |Γ|)`; this answers a question of Natale and is the
group-theoretic input to Kashina's exponent conjecture for group-theoretical
Hopf algebras. The Hopf-algebra consequence is out of scope here.

Equivalent form: `gcd([G : F], [G : Γ]) * exp(G)` divides `|G|`.

Date recorded: 2026-10-21.
Status in the literature: claimed proved in the paper (paper withdrawn).
Status here: proved in Lean, by an elementary argument independent of the
paper (no CFSG, no characters):

1. (Wielandt-style Sylow factorization) for every prime `p` some Sylow
   `p`-subgroup `P` satisfies `P = (A ∩ P)(B ∩ P)`, by a `p`-adic counting
   argument from `|A ∩ B| * |G| = |A| * |B|`;
2. (`p`-groups) if a finite `p`-group factorizes as `P = A B`, then every
   element order is at most `max |A| |B|`, by strong induction on normal
   subgroups `N ≤ A ∩ B` with the invariant
   `[⟨g⟩ : ⟨g⟩ ∩ N] * |N| ≤ max |A| |B|`; either some conjugate of `A` or `B`
   meets `⟨g⟩` inside `N` (regular orbit on cosets), or the cores of `A` and
   `B` share an element of `⟨g⟩ \ N` and the induction climbs;
3. an element of order `p ^ k` is conjugate into `P`, so `p ^ k` divides
   `|A|` or `|B|`; the exponent is the lcm of element orders.

Hypothesis encoding: the factorization `G = A B` is the pointwise statement
`∀ g, ∃ a ∈ A, ∃ b ∈ B, a * b = g`.
-/
import Mathlib

set_option autoImplicit false

open Subgroup

namespace KashinaFactorizedExponent

variable {G : Type*} [Group G]

/-- If `G = A B`, then `A` meets every left coset of `B`, so `[G : B] ≤ [A : A ∩ B]`. -/
theorem index_le_relIndex_of_forall_mul {A B : Subgroup G}
    [Finite G] (hAB : ∀ g : G, ∃ a ∈ A, ∃ b ∈ B, a * b = g) :
    B.index ≤ B.relIndex A := by
  rw [Subgroup.relIndex, Subgroup.index, Subgroup.index]
  let f : A ⧸ B.subgroupOf A → G ⧸ B := Quotient.map' (fun a : A => (a : G)) (by
    intro a b h
    rw [QuotientGroup.leftRel_apply] at h ⊢
    simpa [Subgroup.mem_subgroupOf] using h)
  apply Nat.card_le_card_of_surjective f
  intro q
  induction q using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hAB g
    refine ⟨QuotientGroup.mk ⟨a, ha⟩, ?_⟩
    show ((a : G) : G ⧸ B) = _
    rw [QuotientGroup.eq]
    simpa using hb

/-- Bézout in a cyclic subgroup: `g ^ gcd(t, ord g)` is a power of `g ^ t`. -/
theorem pow_gcd_mem_zpowers (g : G) (t : ℕ) :
    g ^ (Nat.gcd t (orderOf g)) ∈ zpowers (g ^ t) := by
  have hb := Nat.gcd_eq_gcd_ab t (orderOf g)
  have key : g ^ (Nat.gcd t (orderOf g)) =
      (g ^ t) ^ (Nat.gcdA t (orderOf g)) := by
    rw [← zpow_natCast, hb, zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast,
      pow_orderOf_eq_one, one_zpow, mul_one]
  rw [key]
  exact zpow_mem (mem_zpowers _) _

/-- In a finite `p`-group, if `g ∉ N` with `N` normal, there is `z ∉ N` (namely
`g ^ (m / p)` with `m` the order of `g` modulo `N`) lying in the cyclic subgroup generated
by every element of `⟨g⟩` outside `N`. -/
theorem exists_mem_zpowers_of_not_mem {p : ℕ} [hp : Fact p.Prime] [Finite G] (hG : IsPGroup p G)
    (N : Subgroup G) [N.Normal] (g : G) (hg : g ∉ N) :
    ∃ z : G, z ∉ N ∧ ∀ h ∈ zpowers g, h ∉ N → z ∈ zpowers h := by
  set m := orderOf (g : G ⧸ N) with hm
  have hmem : ∀ n : ℕ, g ^ n ∈ N ↔ m ∣ n := by
    intro n
    rw [orderOf_dvd_iff_pow_eq_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  obtain ⟨c, hc⟩ := (IsPGroup.iff_orderOf.mp hG) g
  have hmd : m ∣ p ^ c := hc ▸ orderOf_map_dvd (QuotientGroup.mk' N) g
  obtain ⟨j, -, hmj⟩ := (Nat.dvd_prime_pow hp.out).1 hmd
  have hj0 : j ≠ 0 := by
    intro h0
    apply hg
    have h1 := (hmem 1).2 (by rw [hmj, h0]; exact dvd_rfl)
    simpa using h1
  refine ⟨g ^ (p ^ (j - 1)), ?_, ?_⟩
  · rw [hmem, hmj, Nat.pow_dvd_pow_iff_le_right hp.out.one_lt]
    omega
  · intro h hh hhN
    rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hh
    obtain ⟨t, rfl⟩ := hh
    rw [hmem] at hhN
    have hdmem := pow_gcd_mem_zpowers g t
    have hd : Nat.gcd t (orderOf g) ∣ p ^ c := hc ▸ Nat.gcd_dvd_right _ _
    obtain ⟨e, -, hde⟩ := (Nat.dvd_prime_pow hp.out).1 hd
    have hej : e < j := by
      by_contra hcon
      replace hcon := not_lt.mp hcon
      apply hhN
      rw [hmj]
      exact (Nat.pow_dvd_pow p hcon).trans (hde ▸ Nat.gcd_dvd_left t _)
    have hz : g ^ (p ^ (j - 1)) = (g ^ (Nat.gcd t (orderOf g))) ^ (p ^ (j - 1 - e)) := by
      rw [← pow_mul, hde, ← pow_add]
      congr 2
      omega
    rw [hz]
    exact pow_mem hdmem _

/-- Relative indices in a finite group are nonzero. -/
theorem relIndex_ne_zero_of_finite [Finite G] (H K : Subgroup G) : H.relIndex K ≠ 0 :=
  (Nat.pos_of_dvd_of_pos (relIndex_dvd_card H K) Nat.card_pos).ne'

/-- Lagrange inside `A`: `|B ∩ A| * [A : A ∩ B] = |A|`. -/
theorem card_inf_mul_relIndex (A B : Subgroup G) :
    Nat.card (B ⊓ A : Subgroup G) * B.relIndex A = Nat.card A := by
  have h := relIndex_mul_relIndex (⊥ : Subgroup G) (B ⊓ A) A bot_le inf_le_right
  rwa [relIndex_bot_left, relIndex_bot_left, inf_relIndex_right] at h

/-- A factorization `G = A B` gives the factorization `G = B A`. -/
theorem forall_mul_symm {A B : Subgroup G} (hAB : ∀ g : G, ∃ a ∈ A, ∃ b ∈ B, a * b = g) :
    ∀ g : G, ∃ b ∈ B, ∃ a ∈ A, b * a = g := by
  intro g
  obtain ⟨a, ha, b, hb, hab⟩ := hAB g⁻¹
  refine ⟨b⁻¹, inv_mem hb, a⁻¹, inv_mem ha, ?_⟩
  rw [← mul_inv_rev, hab, inv_inv]

/-- Regular-orbit case: if `G = A B`, `N ≤ A ∩ B`, and `H` meets the conjugate
`b⁻¹ B b` (written as a `comap` of conjugation by `b`) inside `N`, then
`[H : H ∩ N] * |N| ≤ |A|`. -/
theorem relIndex_mul_card_le_of_conj [Finite G] {A B N : Subgroup G}
    (hAB : ∀ g : G, ∃ a ∈ A, ∃ b ∈ B, a * b = g) (hNA : N ≤ A) (hNB : N ≤ B)
    (H : Subgroup G) (b : G) (hb : H ⊓ B.comap (MulAut.conj b).toMonoidHom ≤ N) :
    N.relIndex H * Nat.card N ≤ Nat.card A := by
  set T := B.comap (MulAut.conj b).toMonoidHom with hT
  have h1 : N.relIndex H ≤ T.relIndex H := by
    rw [← inf_relIndex_right N H, ← inf_relIndex_right T H]
    exact relIndex_le_of_le_left (le_inf (inf_comm H T ▸ hb) inf_le_right)
      (relIndex_ne_zero_of_finite _ _)
  have h2 : T.relIndex H ≤ T.index := by
    rw [← relIndex_top_right]
    exact relIndex_le_of_le_right le_top (relIndex_ne_zero_of_finite _ _)
  have h3 : T.index = B.index := index_comap_of_surjective _ (MulAut.conj b).surjective
  have h4 : B.index ≤ B.relIndex A := index_le_relIndex_of_forall_mul hAB
  have h5 : Nat.card N ≤ Nat.card (B ⊓ A : Subgroup G) := card_le_of_le (le_inf hNB hNA)
  have h6 := card_inf_mul_relIndex A B
  calc N.relIndex H * Nat.card N ≤ B.relIndex A * Nat.card (B ⊓ A : Subgroup G) :=
        Nat.mul_le_mul (by omega) h5
    _ = Nat.card A := by rw [mul_comm, h6]

/-- Monotonicity of `[H : H ∩ N] * |N|` in `N`: if `N ≤ M` then
`[H : H ∩ N] * |N| ≤ [H : H ∩ M] * |M|`. -/
theorem relIndex_mul_card_le_of_le {N M H : Subgroup G} [Finite G] (hNM : N ≤ M) :
    N.relIndex H * Nat.card N ≤ M.relIndex H * Nat.card M := by
  have h1 : N.relIndex (M ⊓ H) * M.relIndex H = N.relIndex H := by
    rw [relIndex_inf_mul_relIndex, inf_eq_left.mpr hNM]
  have h2 : N.relIndex (M ⊓ H) ≤ N.relIndex M :=
    relIndex_le_of_le_right inf_le_left (relIndex_ne_zero_of_finite _ _)
  have h3 : Nat.card N * N.relIndex M = Nat.card M := by
    have h := relIndex_mul_relIndex (⊥ : Subgroup G) N M bot_le hNM
    rwa [relIndex_bot_left, relIndex_bot_left] at h
  calc N.relIndex H * Nat.card N = N.relIndex (M ⊓ H) * Nat.card N * M.relIndex H := by
        rw [← h1]; ring
    _ ≤ N.relIndex M * Nat.card N * M.relIndex H := by gcongr
    _ = M.relIndex H * Nat.card M := by rw [← h3]; ring

/-- Induction invariant for the `p`-group case: if a finite `p`-group factorizes as
`G = A B`, then for every normal `N ≤ A ∩ B`, `[⟨g⟩ : ⟨g⟩ ∩ N] * |N| ≤ max |A| |B|`. -/
theorem relIndex_zpowers_mul_card_le {p : ℕ} [Fact p.Prime] [Finite G] (hG : IsPGroup p G)
    {A B : Subgroup G} (hAB : ∀ g : G, ∃ a ∈ A, ∃ b ∈ B, a * b = g) (g : G) :
    ∀ N : Subgroup G, N.Normal → N ≤ A → N ≤ B →
      N.relIndex (zpowers g) * Nat.card N ≤ max (Nat.card A) (Nat.card B) := by
  have hBA := forall_mul_symm hAB
  intro N
  induction hn : Nat.card G - Nat.card N using Nat.strong_induction_on generalizing N with
  | _ n ih =>
  intro hN hNA hNB
  by_cases hgN : g ∈ N
  · have h1 : N.relIndex (zpowers g) = 1 := relIndex_eq_one.mpr ((zpowers_le).mpr hgN)
    rw [h1, one_mul]
    exact (card_le_of_le hNA).trans (le_max_left _ _)
  obtain ⟨z, hzN, hz⟩ := exists_mem_zpowers_of_not_mem hG N g hgN
  by_cases hcaseB : ∃ b : G, zpowers g ⊓ B.comap (MulAut.conj b).toMonoidHom ≤ N
  · obtain ⟨b, hb⟩ := hcaseB
    exact (relIndex_mul_card_le_of_conj hAB hNA hNB _ b hb).trans (le_max_left _ _)
  by_cases hcaseA : ∃ b : G, zpowers g ⊓ A.comap (MulAut.conj b).toMonoidHom ≤ N
  · obtain ⟨b, hb⟩ := hcaseA
    exact (relIndex_mul_card_le_of_conj hBA hNB hNA _ b hb).trans (le_max_right _ _)
  -- every conjugate of `A` and of `B` contains `z`
  have hcore : ∀ (C : Subgroup G),
      (¬ ∃ b : G, zpowers g ⊓ C.comap (MulAut.conj b).toMonoidHom ≤ N) → z ∈ C.normalCore := by
    intro C hC b
    have hb : ¬ zpowers g ⊓ C.comap (MulAut.conj b).toMonoidHom ≤ N := fun h => hC ⟨b, h⟩
    obtain ⟨h, ⟨hhg, hhC⟩, hhN⟩ := Set.not_subset.mp hb
    have hzh : z ∈ zpowers h := hz h hhg hhN
    have hzC : z ∈ C.comap (MulAut.conj b).toMonoidHom :=
      (zpowers_le.mpr hhC) hzh
    simpa [MulAut.conj_apply] using hzC
  set M := A.normalCore ⊓ B.normalCore with hM
  have hMn : M.Normal := inferInstance
  have hNM : N ≤ M := le_inf (normal_le_normalCore.mpr hNA) (normal_le_normalCore.mpr hNB)
  have hzM : z ∈ M := ⟨hcore A hcaseA, hcore B hcaseB⟩
  have hlt : Nat.card N < Nat.card M := by
    refine lt_of_le_of_ne (card_le_of_le hNM) fun hcard => hzN ?_
    rw [eq_of_le_of_card_ge hNM hcard.ge]
    exact hzM
  have hMG : Nat.card M ≤ Nat.card G := card_le_card_group M
  have hIH := ih (Nat.card G - Nat.card M) (by omega) M rfl hMn
    (inf_le_left.trans (normalCore_le A)) (inf_le_right.trans (normalCore_le B))
  exact (relIndex_mul_card_le_of_le hNM).trans hIH

/-- In a finite `p`-group factorized as `G = A B`, every element order is at most
`max |A| |B|`. -/
theorem orderOf_le_max_of_isPGroup {p : ℕ} [Fact p.Prime] [Finite G] (hG : IsPGroup p G)
    {A B : Subgroup G} (hAB : ∀ g : G, ∃ a ∈ A, ∃ b ∈ B, a * b = g) (g : G) :
    orderOf g ≤ max (Nat.card A) (Nat.card B) := by
  have h := relIndex_zpowers_mul_card_le hG hAB g ⊥ inferInstance bot_le bot_le
  rwa [relIndex_bot_left, Nat.card_zpowers, card_bot, mul_one] at h

/-- Counting criterion for a factorization: if `X ≤ P` and `[P : P ∩ Y] ≤ [X : X ∩ Y]`,
then every element of `P` is a product `a * b` with `a ∈ X`, `b ∈ Y`. -/
theorem forall_mul_of_relIndex_le [Finite G] {X Y P : Subgroup G} (hXP : X ≤ P)
    (h : Y.relIndex P ≤ Y.relIndex X) : ∀ y ∈ P, ∃ a ∈ X, ∃ b ∈ Y, a * b = y := by
  let f : X ⧸ Y.subgroupOf X → P ⧸ Y.subgroupOf P :=
    Quotient.map' (fun a : X => (⟨a, hXP a.2⟩ : P)) (by
      intro a b hab
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      simpa [Subgroup.mem_subgroupOf] using hab)
  have hf : Function.Injective f := by
    intro q1 q2 hq
    induction q1 using QuotientGroup.induction_on with
    | H a =>
    induction q2 using QuotientGroup.induction_on with
    | H b =>
    change ((⟨a, hXP a.2⟩ : P) : P ⧸ Y.subgroupOf P) = ((⟨b, hXP b.2⟩ : P) : P ⧸ Y.subgroupOf P)
      at hq
    rw [QuotientGroup.eq] at hq ⊢
    simpa [Subgroup.mem_subgroupOf] using hq
  have hbij := hf.bijective_of_nat_card_le h
  intro y hy
  obtain ⟨q, hq⟩ := hbij.2 (QuotientGroup.mk ⟨y, hy⟩)
  induction q using QuotientGroup.induction_on with
  | H a =>
  change ((⟨a, hXP a.2⟩ : P) : P ⧸ Y.subgroupOf P) = ((⟨y, hy⟩ : P) : P ⧸ Y.subgroupOf P) at hq
  rw [QuotientGroup.eq] at hq
  have hmem : (a : G)⁻¹ * y ∈ Y := by simpa [Subgroup.mem_subgroupOf] using hq
  exact ⟨a, a.2, (a : G)⁻¹ * y, hmem, by group⟩

/-- Product formula for a factorization `G = A B`: `|B ∩ A| * |G| = |A| * |B|`. -/
theorem card_inf_mul_card_eq [Finite G] {A B : Subgroup G}
    (hAB : ∀ g : G, ∃ a ∈ A, ∃ b ∈ B, a * b = g) :
    Nat.card (B ⊓ A : Subgroup G) * Nat.card G = Nat.card A * Nat.card B := by
  have h1 : B.index ≤ B.relIndex A := index_le_relIndex_of_forall_mul hAB
  have h2 : B.relIndex A ≤ B.index := by
    rw [← relIndex_top_right]
    exact relIndex_le_of_le_right le_top (relIndex_ne_zero_of_finite _ _)
  have h3 := card_inf_mul_relIndex A B
  have h4 := card_mul_index B
  rw [← h3, ← h4, le_antisymm h1 h2]
  ring

/-- A `p`-subgroup contained in `K` has order at most the `p`-part of `|K|`. -/
theorem card_le_of_isPGroup_of_le [Finite G] {p : ℕ} [hp : Fact p.Prime] {Q K : Subgroup G}
    (hQ : IsPGroup p Q) (hQK : Q ≤ K) : Nat.card Q ≤ p ^ (Nat.card K).factorization p := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  have hdvd : p ^ n ∣ Nat.card K := hn ▸ card_dvd_of_le hQK
  rw [hn]
  exact Nat.pow_le_pow_right hp.out.pos
    ((hp.out.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvd)

/-- Wielandt-style Sylow factorization: if `G = A B` is finite, then for each prime `p`
some Sylow `p`-subgroup `P` satisfies `P = (A ∩ P)(B ∩ P)`. -/
theorem exists_sylow_forall_mul {p : ℕ} [hp : Fact p.Prime] [Finite G] {A B : Subgroup G}
    (hAB : ∀ g : G, ∃ a ∈ A, ∃ b ∈ B, a * b = g) :
    ∃ P : Sylow p G, ∀ y ∈ (P : Subgroup G),
      ∃ a ∈ A ⊓ (P : Subgroup G), ∃ b ∈ B ⊓ (P : Subgroup G), a * b = y := by
  have hBA := forall_mul_symm hAB
  let SA : Sylow p A := Classical.choice inferInstance
  let SB : Sylow p B := Classical.choice inferInstance
  let A0 : Subgroup G := (SA : Subgroup A).map A.subtype
  let B0 : Subgroup G := (SB : Subgroup B).map B.subtype
  have hA0 : A0 ≤ A := map_subtype_le _
  have hB0 : B0 ≤ B := map_subtype_le _
  have hA0card : Nat.card A0 = p ^ (Nat.card A).factorization p := by
    rw [card_map_of_injective A.subtype_injective, Sylow.card_eq_multiplicity]
  have hB0card : Nat.card B0 = p ^ (Nat.card B).factorization p := by
    rw [card_map_of_injective B.subtype_injective, Sylow.card_eq_multiplicity]
  obtain ⟨P1, hP1⟩ := IsPGroup.exists_le_sylow (SA.isPGroup'.map A.subtype)
  obtain ⟨P2, hP2⟩ := IsPGroup.exists_le_sylow (SB.isPGroup'.map B.subtype)
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G P1 P2
  obtain ⟨b, hb, a, ha, rfl⟩ := hBA c
  refine ⟨a • P1, ?_⟩
  set P : Sylow p G := a • P1 with hP
  have hPb : P = b⁻¹ • P2 := by
    rw [← hc, smul_smul, inv_mul_cancel_left]
  -- `A ⊓ P` contains a Sylow subgroup of `A`
  have hX : Nat.card A0 ≤ Nat.card (A ⊓ (P : Subgroup G) : Subgroup G) := by
    have hle : A0.map (MulAut.conj a).toMonoidHom ≤ A ⊓ (P : Subgroup G) := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · simpa [MulAut.conj_apply] using
          A.mul_mem (A.mul_mem ha (hA0 hx)) (A.inv_mem ha)
      · rw [hP, Sylow.coe_subgroup_smul]
        exact smul_mem_pointwise_smul x (MulAut.conj a) _ (hP1 hx)
    calc Nat.card A0 = Nat.card (A0.map (MulAut.conj a).toMonoidHom) :=
          (card_map_of_injective (MulAut.conj a).injective).symm
      _ ≤ _ := card_le_of_le hle
  have hY : Nat.card B0 ≤ Nat.card (B ⊓ (P : Subgroup G) : Subgroup G) := by
    have hle : B0.map (MulAut.conj b⁻¹).toMonoidHom ≤ B ⊓ (P : Subgroup G) := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · simpa [MulAut.conj_apply] using
          B.mul_mem (B.mul_mem (B.inv_mem hb) (hB0 hx)) hb
      · rw [hPb, Sylow.coe_subgroup_smul]
        exact smul_mem_pointwise_smul x (MulAut.conj b⁻¹) _ (hP2 hx)
    calc Nat.card B0 = Nat.card (B0.map (MulAut.conj b⁻¹).toMonoidHom) :=
          (card_map_of_injective (MulAut.conj b⁻¹).injective).symm
      _ ≤ _ := card_le_of_le hle
  set X : Subgroup G := A ⊓ (P : Subgroup G) with hXdef
  set Y : Subgroup G := B ⊓ (P : Subgroup G) with hYdef
  have hXY : Nat.card (Y ⊓ X : Subgroup G) ≤ p ^ (Nat.card (B ⊓ A : Subgroup G)).factorization p :=
    card_le_of_isPGroup_of_le (P.isPGroup'.to_le (inf_le_right.trans inf_le_right))
      (inf_le_inf inf_le_left inf_le_left)
  have hPcard := Sylow.card_eq_multiplicity P
  -- valuation identity from `|B ⊓ A| * |G| = |A| * |B|`
  have hval : p ^ (Nat.card (B ⊓ A : Subgroup G)).factorization p * p ^ (Nat.card G).factorization p
      = p ^ (Nat.card A).factorization p * p ^ (Nat.card B).factorization p := by
    have h := congrArg (fun n => n.factorization p) (card_inf_mul_card_eq hAB)
    rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne'] at h
    simp only [Finsupp.add_apply] at h
    rw [← pow_add, ← pow_add, h]
  have hrel1 : Y.relIndex (P : Subgroup G) * Nat.card Y = Nat.card (P : Subgroup G) := by
    have h := relIndex_mul_relIndex (⊥ : Subgroup G) Y P bot_le inf_le_right
    rw [relIndex_bot_left, relIndex_bot_left] at h
    rw [← h, mul_comm]
  have hrel2 := card_inf_mul_relIndex X Y
  have hmain : Y.relIndex (P : Subgroup G) * (Nat.card Y * Nat.card (Y ⊓ X : Subgroup G))
      ≤ Y.relIndex X * (Nat.card Y * Nat.card (Y ⊓ X : Subgroup G)) := by
    calc Y.relIndex (P : Subgroup G) * (Nat.card Y * Nat.card (Y ⊓ X : Subgroup G))
        = Nat.card (P : Subgroup G) * Nat.card (Y ⊓ X : Subgroup G) := by
          rw [← hrel1]; ring
      _ ≤ p ^ (Nat.card G).factorization p * p ^ (Nat.card (B ⊓ A : Subgroup G)).factorization p := by
          rw [hPcard]; exact Nat.mul_le_mul_left _ hXY
      _ = p ^ (Nat.card A).factorization p * p ^ (Nat.card B).factorization p := by
          rw [mul_comm, hval]
      _ ≤ Nat.card X * Nat.card Y := by
          rw [← hA0card, ← hB0card]; exact Nat.mul_le_mul hX hY
      _ = Y.relIndex X * (Nat.card Y * Nat.card (Y ⊓ X : Subgroup G)) := by
          rw [← hrel2]; ring
  have hpos : 0 < Nat.card Y * Nat.card (Y ⊓ X : Subgroup G) := Nat.mul_pos Nat.card_pos Nat.card_pos
  exact forall_mul_of_relIndex_le inf_le_right (Nat.le_of_mul_le_mul_right hmain hpos)

/-- If `G = A B` is finite and `g` has order `p ^ k` with `p` prime, then `p ^ k`
divides `|A|` or `|B|`. -/
theorem prime_pow_dvd_card_or_of_orderOf_eq {p : ℕ} [hp : Fact p.Prime] [Finite G]
    {A B : Subgroup G} (hAB : ∀ g : G, ∃ a ∈ A, ∃ b ∈ B, a * b = g) {g : G} {k : ℕ}
    (hg : orderOf g = p ^ k) : p ^ k ∣ Nat.card A ∨ p ^ k ∣ Nat.card B := by
  obtain ⟨P, hP⟩ := exists_sylow_forall_mul (p := p) hAB
  have hgp : IsPGroup p (zpowers g) := IsPGroup.of_card (by rw [Nat.card_zpowers, hg])
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hgp
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G P Q
  -- conjugate `g` into `P`
  set g₁ : G := MulAut.conj c⁻¹ g with hg₁
  have hg₁P : g₁ ∈ (P : Subgroup G) := by
    have hgQ : g ∈ (Q : Subgroup G) := hQ (mem_zpowers g)
    rw [← hc, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at hgQ
    simpa [hg₁, MulAut.smul_def, MulAut.conj_apply, MulAut.inv_def] using hgQ
  have hord : orderOf g₁ = p ^ k := by
    rw [hg₁, MulEquiv.orderOf_eq, hg]
  -- the factorization of `P`
  have hfac : ∀ y : (P : Subgroup G), ∃ a ∈ A.subgroupOf P, ∃ b ∈ B.subgroupOf P, a * b = y := by
    intro y
    obtain ⟨a, ⟨haA, haP⟩, b, ⟨hbB, hbP⟩, hab⟩ := hP y y.2
    exact ⟨⟨a, haP⟩, by simpa [mem_subgroupOf] using haA, ⟨b, hbP⟩,
      by simpa [mem_subgroupOf] using hbB, Subtype.ext hab⟩
  have hle := orderOf_le_max_of_isPGroup P.isPGroup' hfac ⟨g₁, hg₁P⟩
  rw [orderOf_mk, hord] at hle
  -- the factor orders are powers of `p` dividing `|A|` and `|B|`
  have hcardX : ∀ C : Subgroup G, ∃ n, Nat.card (C.subgroupOf P) = p ^ n ∧ p ^ n ∣ Nat.card C := by
    intro C
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (P.isPGroup'.to_subgroup (C.subgroupOf P))
    refine ⟨n, hn, ?_⟩
    rw [← hn, ← card_map_of_injective (P : Subgroup G).subtype_injective, subgroupOf_map_subtype]
    exact card_dvd_of_le inf_le_left
  obtain ⟨nA, hnA, hdA⟩ := hcardX A
  obtain ⟨nB, hnB, hdB⟩ := hcardX B
  rw [hnA, hnB] at hle
  rcases le_max_iff.mp hle with h | h
  · exact Or.inl ((Nat.pow_dvd_pow p ((Nat.pow_le_pow_iff_right hp.out.one_lt).mp h)).trans hdA)
  · exact Or.inr ((Nat.pow_dvd_pow p ((Nat.pow_le_pow_iff_right hp.out.one_lt).mp h)).trans hdB)

/-- **Exponents of factorized groups** (arXiv:2608.14972, main group-theoretic theorem,
answering Natale's question): if a finite group factorizes as `G = A B` with subgroups `A`
and `B` (not assumed normal; `A ∩ B` arbitrary), then `exp(G)` divides `lcm(|A|, |B|)`. -/
theorem exponent_dvd_lcm_card_of_forall_mul [Finite G] (A B : Subgroup G)
    (hAB : ∀ g : G, ∃ a ∈ A, ∃ b ∈ B, a * b = g) :
    Monoid.exponent G ∣ Nat.lcm (Nat.card A) (Nat.card B) := by
  rw [Monoid.exponent_dvd]
  intro g
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf (g ^ (orderOf g / p ^ k)) = p ^ k :=
    orderOf_pow_orderOf_div (orderOf_pos g).ne' hpk
  rcases prime_pow_dvd_card_or_of_orderOf_eq hAB hord with h | h
  · exact h.trans (Nat.dvd_lcm_left _ _)
  · exact h.trans (Nat.dvd_lcm_right _ _)

/-- **Equivalent index form** (arXiv:2608.14972): if a finite group factorizes as `G = A B`,
then `gcd([G : A], [G : B]) * exp(G)` divides `|G|`. -/
theorem gcd_index_mul_exponent_dvd_card [Finite G] (A B : Subgroup G)
    (hAB : ∀ g : G, ∃ a ∈ A, ∃ b ∈ B, a * b = g) :
    Nat.gcd A.index B.index * Monoid.exponent G ∣ Nat.card G := by
  set d := Nat.gcd A.index B.index with hd
  have hA : d * Nat.card A ∣ Nat.card G := by
    rw [← card_mul_index A, mul_comm (Nat.card A)]
    exact Nat.mul_dvd_mul_right (Nat.gcd_dvd_left _ _) _
  have hB : d * Nat.card B ∣ Nat.card G := by
    rw [← card_mul_index B, mul_comm (Nat.card B)]
    exact Nat.mul_dvd_mul_right (Nat.gcd_dvd_right _ _) _
  have hlcm : d * Nat.lcm (Nat.card A) (Nat.card B) ∣ Nat.card G := by
    rw [← Nat.lcm_mul_left]
    exact Nat.lcm_dvd hA hB
  exact (Nat.mul_dvd_mul_left d (exponent_dvd_lcm_card_of_forall_mul A B hAB)).trans hlcm

/-! ## Non-vacuity: a factorization with a non-normal factor

`S₃ = A₃ · ⟨(0 1)⟩`, where `⟨(0 1)⟩` is not normal. The hypothesis of the main theorem
holds, and the conclusion reads `exp(S₃) ∣ lcm(3, 2)`. -/

/-- `S₃` factorizes as `A₃ · ⟨(0 1)⟩`. -/
theorem perm_three_factorization :
    ∀ g : Equiv.Perm (Fin 3), ∃ a ∈ alternatingGroup (Fin 3),
      ∃ b ∈ zpowers (Equiv.swap (0 : Fin 3) 1), a * b = g := by
  intro g
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h | h
  · exact ⟨g, Equiv.Perm.mem_alternatingGroup.mpr h, 1, one_mem _, mul_one g⟩
  · refine ⟨g * Equiv.swap 0 1, ?_, Equiv.swap 0 1, mem_zpowers _, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, h,
        Equiv.Perm.sign_swap (by decide)]
      rfl
    · rw [mul_assoc, Equiv.swap_mul_self, mul_one]

/-- The factor `⟨(0 1)⟩` of `S₃` is not normal, so the example is not a semidirect
product with normal second factor. -/
theorem not_normal_zpowers_swap : ¬ (zpowers (Equiv.swap (0 : Fin 3) 1)).Normal := by
  intro h
  have hmem := h.conj_mem _ (mem_zpowers (Equiv.swap (0 : Fin 3) 1)) (Equiv.swap 1 2)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
  have hfix : (Equiv.swap (0 : Fin 3) 1 ^ k) 2 = 2 :=
    Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (by decide) k
  rw [hk] at hfix
  revert hfix
  decide

example : Monoid.exponent (Equiv.Perm (Fin 3)) ∣
    Nat.lcm (Nat.card (alternatingGroup (Fin 3))) (Nat.card (zpowers (Equiv.swap (0 : Fin 3) 1))) :=
  exponent_dvd_lcm_card_of_forall_mul _ _ perm_three_factorization

end KashinaFactorizedExponent
