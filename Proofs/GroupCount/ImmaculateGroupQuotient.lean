/-
# Immaculate (Leinster) groups: the abelian quotient theorem

## Source

* MathOverflow question 54851, "Is there an odd-order group G with
  D(G) = 2|G|?" (Tom Leinster), https://mathoverflow.net/questions/54851 .
* Tom Leinster, "Perfect numbers and groups", arXiv:math/0104012
  (Eureka 55, 2001).  Leinster calls a finite group *perfect* (later
  *immaculate*, to avoid the clash with `Group.IsPerfect`) when
  `D(G) := ∑_{N ⊴ G} |N| = 2|G|`.

Informal claim (Leinster, stated in the MO question, proved in the paper,
Sections 3-4):

> If `G` is a finite group with `D(G) ≤ 2|G|`, then every abelian quotient
> of `G` is cyclic.  In particular an abelian immaculate group is cyclic
> (and hence the abelian immaculate groups are the cyclic groups of perfect
> order).

The thread's own question (an odd-order immaculate group) was answered
positively in the thread (F. Brunault: `(C127 ⋊ C7) × C399812193`); that
existence statement is NOT formalized here.

Recorded 2026-10-21.  Status: proved in the literature (Leinster 2001).

## What this file proves (no `sorry`)

* `D_eq_sum_card_filter_mem`: the double count `D(G) = ∑_{g ∈ G} ν(g)`,
  `ν(g) = #{N ⊴ G : g ∈ N}`.
* `exists_forall_normal_mem_eq_top_of_D_le`: `D(G) ≤ 2|G|` forces an
  element whose normal closure is `G`.
* `isCyclic_of_D_le` (main): Leinster's abelian quotient theorem in the
  surjective-homomorphism form; `isCyclic_abelianization_of_D_le` and
  `isCyclic_of_isImmaculate` are corollaries.
* `D_mod_prime_of_isPGroup`, `not_isImmaculate_of_isPGroup`: for a finite
  `p`-group `D(G) ≡ 1 (mod p)`, so no `p`-group is immaculate.

Not formalized: `D(C_n) = σ(n)` (needed for the converse "cyclic of perfect
order ⇒ immaculate") and the odd immaculate examples from the thread.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.ImmaculateGroupQuotient

/-- Leinster's invariant `D(G) = ∑_{N ⊴ G} |N|`, the sum of the orders of the
normal subgroups of `G`.  It is intended for finite `G` (all theorems below
assume `[Finite G]`); for infinite `G` the `finsum` takes its junk value. -/
noncomputable def D (G : Type*) [Group G] : ℕ :=
  ∑ᶠ N ∈ {N : Subgroup G | N.Normal}, Nat.card N

section Count

variable {G : Type*} [Group G] [Fintype G]

open Classical in
/-- `D(G)` as a `Finset` sum over the normal subgroups of a finite group. -/
theorem D_eq_sum_finset :
    D G = ∑ N ∈ (Finset.univ.filter fun N : Subgroup G => N.Normal), Nat.card N := by
  rw [D, finsum_mem_eq_toFinset_sum]
  congr 1
  ext N
  simp

open Classical in
/-- Double counting of pairs `(N, g)` with `N ⊴ G` and `g ∈ N`:
`D(G) = ∑_{g ∈ G} #{N ⊴ G : g ∈ N}`. -/
theorem D_eq_sum_card_filter_mem :
    D G = ∑ g : G, ((Finset.univ.filter fun N : Subgroup G => N.Normal).filter
      fun N => g ∈ N).card := by
  rw [D_eq_sum_finset]
  have hcard : ∀ N : Subgroup G, Nat.card N = ∑ g : G, if g ∈ N then 1 else 0 := by
    intro N
    rw [← Finset.card_filter, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp_rw [hcard]
  rw [Finset.sum_comm]
  simp_rw [Finset.card_filter]

open Classical in
/-- Leinster's counting step: if `D(G) ≤ 2|G|` then some `h ∈ G` lies in no
proper normal subgroup (equivalently its normal closure is `G`).  Otherwise
every element lies in `⊤` and in a proper normal subgroup, and `1` moreover
lies in `⊥`, a third normal subgroup when `G` is nontrivial; summing
`#{N ⊴ G : g ∈ N}` gives `D(G) > 2|G|`. -/
theorem exists_forall_normal_mem_eq_top_of_D_le (hD : D G ≤ 2 * Fintype.card G) :
    ∃ h : G, ∀ N : Subgroup G, N.Normal → h ∈ N → N = ⊤ := by
  by_contra hcon
  push Not at hcon
  -- every element lies in a proper normal subgroup
  choose M hMn hMmem hMtop using hcon
  have hnt : Nontrivial G := by
    by_contra hsub
    rw [not_nontrivial_iff_subsingleton] at hsub
    exact hMtop 1 (Subsingleton.elim _ _)
  set S := Finset.univ.filter fun N : Subgroup G => N.Normal with hS
  have hle : ∀ g ∈ (Finset.univ : Finset G), 2 ≤ (S.filter fun N => g ∈ N).card := by
    intro g _
    rw [Nat.succ_le_iff, Finset.one_lt_card]
    refine ⟨⊤, ?_, M g, ?_, (hMtop g).symm⟩
    · simp [hS, Subgroup.normal_top]
    · simp [hS, hMn g, hMmem g]
  have hlt : ∃ g ∈ (Finset.univ : Finset G), 2 < (S.filter fun N => g ∈ N).card := by
    obtain ⟨x, hx⟩ := exists_ne (1 : G)
    refine ⟨1, Finset.mem_univ _, ?_⟩
    rw [Finset.two_lt_card]
    have hMx_ne_bot : M x ≠ ⊥ := by
      intro hbot
      have hxM := hMmem x
      rw [hbot, Subgroup.mem_bot] at hxM
      exact hx hxM
    refine ⟨⊤, ?_, ⊥, ?_, M x, ?_, top_ne_bot, (hMtop x).symm, hMx_ne_bot.symm⟩
    · simp [hS, Subgroup.normal_top]
    · simp [hS, Subgroup.normal_bot]
    · simp [hS, hMn x]
  have hsum := Finset.sum_lt_sum hle hlt
  rw [← D_eq_sum_card_filter_mem] at hsum
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  omega

end Count

/-- **Leinster's abelian quotient theorem** (Leinster, arXiv:math/0104012,
quoted in MathOverflow 54851): if `G` is a finite group with
`D(G) = ∑_{N ⊴ G} |N| ≤ 2|G|`, then every abelian quotient of `G` is cyclic;
here an abelian quotient is the target of a surjective homomorphism
`f : G →* A` with `A` commutative. -/
theorem isCyclic_of_D_le {G A : Type*} [Group G] [Finite G] [CommGroup A]
    (hD : D G ≤ 2 * Nat.card G) (f : G →* A) (hf : Function.Surjective f) : IsCyclic A := by
  have : Fintype G := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card] at hD
  obtain ⟨h, hh⟩ := exists_forall_normal_mem_eq_top_of_D_le hD
  have hcomap : (Subgroup.zpowers (f h)).comap f = ⊤ :=
    hh _ ((Subgroup.normal_of_isMulCommutative _).comap f) (Subgroup.mem_zpowers (f h))
  refine ⟨f h, fun a => ?_⟩
  obtain ⟨g, rfl⟩ := hf a
  have hg : g ∈ (Subgroup.zpowers (f h)).comap f := hcomap ▸ Subgroup.mem_top g
  exact Subgroup.mem_zpowers_iff.mp hg

/-- The abelianization of a finite group with `D(G) ≤ 2|G|` is cyclic
(the largest abelian quotient case of `isCyclic_of_D_le`). -/
theorem isCyclic_abelianization_of_D_le {G : Type*} [Group G] [Finite G]
    (hD : D G ≤ 2 * Nat.card G) : IsCyclic (Abelianization G) :=
  isCyclic_of_D_le hD Abelianization.of (QuotientGroup.mk_surjective)

/-- A finite group `G` is *immaculate* (Leinster's "perfect group") when
`D(G) = ∑_{N ⊴ G} |N| = 2|G|`. -/
def IsImmaculate (G : Type*) [Group G] [Finite G] : Prop := D G = 2 * Nat.card G

/-- An abelian immaculate group is cyclic (Leinster's corollary). -/
theorem isCyclic_of_isImmaculate {G : Type*} [CommGroup G] [Finite G] (hG : IsImmaculate G) :
    IsCyclic G :=
  isCyclic_of_D_le hG.le (MonoidHom.id G) Function.surjective_id

/-- A group of prime order `p` has exactly the normal subgroups `⊥` and `⊤`,
so `D(G) = p + 1`. -/
theorem D_of_card_prime {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hG : Nat.card G = p) : D G = p + 1 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  rw [D_eq_sum_finset]
  have hS : (Finset.univ.filter fun N : Subgroup G => N.Normal) = {⊥, ⊤} := by
    ext N
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro _
      have : Fact (Nat.card G).Prime := hG ▸ hp
      exact Subgroup.eq_bot_or_eq_top_of_prime_card N
    · rintro (rfl | rfl)
      · exact Subgroup.normal_bot
      · exact Subgroup.normal_top
  have hne : (⊥ : Subgroup G) ≠ ⊤ := by
    have : Nontrivial G := by
      rw [← Finite.one_lt_card_iff_nontrivial, hG]
      exact hp.out.one_lt
    exact bot_ne_top
  rw [hS, Finset.sum_pair hne, Subgroup.card_bot, Subgroup.card_top, hG]
  ring

/-- The trivial group has `D(G) = 1`. -/
theorem D_of_subsingleton {G : Type*} [Group G] [Subsingleton G] : D G = 1 := by
  have hS : {N : Subgroup G | N.Normal} = {⊥} :=
    Set.ext fun N => ⟨fun _ => Subsingleton.elim N ⊥, fun h => h ▸ Subgroup.normal_bot⟩
  rw [D, hS, finsum_mem_singleton, Subgroup.card_bot]

/-- For a finite `p`-group, `D(G) ≡ 1 (mod p)`: every normal subgroup other
than `⊥` has order a positive power of `p`. -/
theorem D_mod_prime_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hG : IsPGroup p G) : D G % p = 1 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set S := Finset.univ.filter fun N : Subgroup G => N.Normal with hS
  have hbot : (⊥ : Subgroup G) ∈ S := by simp [hS, Subgroup.normal_bot]
  have hdvd : ∀ N ∈ S.erase ⊥, p ∣ Nat.card N := by
    intro N hN
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp (hG.to_subgroup N))
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, Subgroup.card_eq_one] at hn
      exact (Finset.ne_of_mem_erase hN) hn
    rw [hn]
    exact dvd_pow_self p hn0
  rw [D_eq_sum_finset, ← hS, ← Finset.add_sum_erase S _ hbot, Subgroup.card_bot,
    Nat.add_mod, Nat.mod_eq_zero_of_dvd (Finset.dvd_sum hdvd), add_zero, Nat.mod_mod,
    Nat.mod_eq_of_lt hp.out.one_lt]

/-- No finite `p`-group is immaculate (Leinster): `D(G) ≡ 1 (mod p)` while
`2|G| ≡ 0 (mod p)` for nontrivial `G`, and `D(1) = 1 ≠ 2`. -/
theorem not_isImmaculate_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] (hG : IsPGroup p G) : ¬ IsImmaculate G := by
  intro himm
  have hmod := D_mod_prime_of_isPGroup hG
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hG
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · -- trivial group: the only normal subgroup is `⊥ = ⊤`, so `D G = 1 ≠ 2`.
    rw [pow_zero] at hn
    have : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hn).1
    rw [IsImmaculate, D_of_subsingleton, hn] at himm
    omega
  · have hdvd : p ∣ D G := by
      rw [himm, hn]
      exact Dvd.dvd.mul_left (dvd_pow_self p hn0.ne') 2
    rw [Nat.mod_eq_zero_of_dvd hdvd] at hmod
    exact zero_ne_one hmod

/-! ## Ground truth and satisfiability -/

example : D Unit = 1 := D_of_subsingleton

example : D (Multiplicative (ZMod 3)) = 4 :=
  D_of_card_prime (p := 3) (by simp)

example : D (Multiplicative (ZMod 2)) = 3 :=
  D_of_card_prime (p := 2) (by simp)

/-- The hypothesis of `isCyclic_of_D_le` is satisfiable: `C₃` has
`D = 4 ≤ 6`. -/
example : IsCyclic (Multiplicative (ZMod 3)) := by
  have hD : D (Multiplicative (ZMod 3)) ≤ 2 * Nat.card (Multiplicative (ZMod 3)) := by
    rw [D_of_card_prime (p := 3) (by simp)]
    simp
  exact isCyclic_of_D_le hD (MonoidHom.id _) Function.surjective_id

example : ¬ IsImmaculate (Multiplicative (ZMod 2)) := by
  rw [IsImmaculate, D_of_card_prime (p := 2) (by simp)]
  simp

example : ¬ IsImmaculate Unit := by
  rw [IsImmaculate, D_of_subsingleton]
  simp

end Candidates.ImmaculateGroupQuotient
