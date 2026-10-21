/-
# No metacyclic group is an Ingleton violator

## Source

arXiv:2505.22565, David A. Craven, "The Ingleton inequality holds for metacyclic
groups and fails for supersoluble groups".  Recorded 2026-10-21.

* Definition (Introduction, verbatim): "let $G$ be a finite group and let
  $\mathbf H=(H_1,H_2,H_3,H_4)$ be a quadruple of subgroups of $G$. Write $H_{12}$
  for the intersection $H_1\cap H_2$ and so on. We call $\mathbf H$ an *Ingleton
  offender* if the inequality
  $|H_1|\cdot|H_2|\cdot|H_{34}|\cdot|H_{123}|\cdot|H_{124}|\geq
  |H_{12}|\cdot|H_{13}|\cdot|H_{14}|\cdot|H_{23}|\cdot|H_{24}|$
  is not satisfied by the $H_i$. [...] If $G$ contains an Ingleton offender, we
  call $G$ an *Ingleton violator*."
* Theorem 1.1 (`thm:nometacyclic`, verbatim): "There are no metacyclic Ingleton
  violators."  Proof in Section 3: "Let $G$ be a metacyclic group with normal
  subgroup $K$ such that $K$ and $G/K$ are cyclic, and proceed by induction on
  $|G|$."
* Theorem 1.3 (`thm:removenormal`, verbatim): "Let $G$ be a finite group and
  suppose that $\mathbf H=(H_1,H_2,H_3,H_4)$ is an Ingleton offender in $G$. If
  $N$ is a normal subgroup of $G$ then either $H_i\cap N=1$ for all
  $1\leq i\leq 4$, or the images of the $H_i$ in $G/N$ form an Ingleton offender."
  Section 3 states what the proof establishes: "if $N$ is a normal subgroup of
  $G$ and $(H_1,H_2,H_3,H_4)$ is an Ingleton offender with $N\leq H_i$ for some
  $i$, then $(NH_1,NH_2,NH_3,NH_4)$ is also an Ingleton offender."

## Status

Proved in the paper (it repairs a gap in Oggier–Stancu 2012).  This module is
kernel-checked and carries no `sorry`.

## Fidelity notes

* Theorem 1.3 is formalized in the form the paper's proof establishes
  (`N ≤ H_i` for some `i`, `not_ingleton_map_of_le`), not the printed
  dichotomy "`H_i ∩ N = 1` for all `i`, or ...".  The two agree when `|N|` is prime,
  and the proof of Theorem 1.1 uses only the `N ≤ H₁` form.
* Corollary 2.7 (cyclic `H₁`) is proved as in the paper: reduce `H₁` to
  `⟨H₁₃, H₁₄⟩` (Lemma 2.4), then distributivity of the subgroup lattice of a
  cyclic group gives `H₁₂ = H₁₂₃H₁₂₄`, and Proposition 2.6 applies.  The
  distributivity, which the paper calls easy, is proved here from
  `x ∈ S ↔ x ^ |S| = 1` in a cyclic group, Bézout, and
  `gcd(p, lcm(a, b)) ∣ lcm(gcd(p, a), gcd(p, b))`.
* Theorem 1.1 is proved by strong induction on `Nat.card G` over groups in a fixed
  universe, as in the paper: an offender has `H₁` non-cyclic, so
  `N = H₁ ∩ K ≠ 1`; `N` is normal because it is a subgroup of the cyclic normal
  subgroup `K`; Theorem 1.3 moves the offender to the smaller metacyclic group
  `G/N`.
* The definitions mirror `Candidates.IngletonSufficientCriteria.Ingleton`
  (`Proofs/Sorry/GroupCount/IngletonSufficientCriteria.lean`) verbatim; that
  module is not imported because it lives in the `Sorry` library.
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.Factorization.Basic

set_option autoImplicit false

open Pointwise

namespace Candidates.MetacyclicIngleton

variable {G : Type*} [Group G]

/-- The **Ingleton inequality** for a quadruple `(H₁, H₂, H₃, H₄)` of subgroups
(arXiv:2505.22565, Introduction):
`|H₁₂|·|H₁₃|·|H₁₄|·|H₂₃|·|H₂₄| ≤ |H₁|·|H₂|·|H₃₄|·|H₁₂₃|·|H₁₂₄|`,
where `H_I` is the intersection of the `H_i` with `i ∈ I`.  The quadruple is an
*Ingleton offender* exactly when this fails. -/
def Ingleton (H₁ H₂ H₃ H₄ : Subgroup G) : Prop :=
  Nat.card ↥(H₁ ⊓ H₂) * Nat.card ↥(H₁ ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₄) *
      Nat.card ↥(H₂ ⊓ H₃) * Nat.card ↥(H₂ ⊓ H₄) ≤
    Nat.card H₁ * Nat.card H₂ * Nat.card ↥(H₃ ⊓ H₄) * Nat.card ↥(H₁ ⊓ H₂ ⊓ H₃) *
      Nat.card ↥(H₁ ⊓ H₂ ⊓ H₄)

/-- A finite group is an **Ingleton violator** if some quadruple of its subgroups is
an Ingleton offender, i.e. fails the Ingleton inequality (arXiv:2505.22565,
Introduction). -/
def IsIngletonViolator (G : Type*) [Group G] : Prop :=
  ∃ H₁ H₂ H₃ H₄ : Subgroup G, ¬ Ingleton H₁ H₂ H₃ H₄

/-! Ground truth for `Ingleton` in `C₂ = Multiplicative (ZMod 2)`, pinning the side
and factor order of the definition: for `(C₂, C₂, 1, 1)` the intersection side is
`|H₁₂|·|H₁₃|·|H₁₄|·|H₂₃|·|H₂₄| = 2·1·1·1·1` and the order side is
`|H₁|·|H₂|·|H₃₄|·|H₁₂₃|·|H₁₂₄| = 2·2·1·1·1`; for `(C₂, 1, C₂, C₂)` they are
`1·2·2·1·1` and `2·1·2·1·1`. -/
example : Ingleton (⊤ : Subgroup (Multiplicative (ZMod 2))) ⊤ ⊥ ⊥ ↔
    2 * 1 * 1 * 1 * 1 ≤ 2 * 2 * 1 * 1 * 1 := by
  have h2 : Nat.card ↥(⊤ : Subgroup (Multiplicative (ZMod 2))) = 2 := by
    rw [Subgroup.card_top, Nat.card_eq_fintype_card]; rfl
  unfold Ingleton
  simp only [inf_top_eq, inf_bot_eq]
  rw [Subgroup.card_bot, h2]

example : Ingleton (⊤ : Subgroup (Multiplicative (ZMod 2))) ⊥ ⊤ ⊤ ↔
    1 * 2 * 2 * 1 * 1 ≤ 2 * 1 * 2 * 1 * 1 := by
  have h2 : Nat.card ↥(⊤ : Subgroup (Multiplicative (ZMod 2))) = 2 := by
    rw [Subgroup.card_top, Nat.card_eq_fintype_card]; rfl
  unfold Ingleton
  simp only [inf_top_eq, inf_bot_eq]
  rw [Subgroup.card_bot, h2]

/-- `|H ∩ K|` computed inside `K`: the subgroup `H.subgroupOf K` of `K` has the order of
`H ⊓ K`. -/
theorem card_subgroupOf_eq (H K : Subgroup G) :
    Nat.card (H.subgroupOf K) = Nat.card ↥(H ⊓ K) := by
  rw [← Subgroup.inf_subgroupOf_right]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv

/-- Lagrange's theorem relative to `K`: `|H ∩ K| · |K : H ∩ K| = |K|`. -/
theorem card_inf_mul_relIndex (H K : Subgroup G) :
    Nat.card ↥(H ⊓ K) * H.relIndex K = Nat.card K := by
  rw [← card_subgroupOf_eq, Subgroup.relIndex]
  exact Subgroup.card_mul_index _

/-- Every subgroup of a finite group has positive order. -/
theorem card_subgroup_pos [Finite G] (H : Subgroup G) : 0 < Nat.card H := Nat.card_pos

/-- In a finite group every relative index is nonzero. -/
theorem relIndex_ne_zero' [Finite G] (H K : Subgroup G) : H.relIndex K ≠ 0 := by
  intro h
  have h1 := card_inf_mul_relIndex H K
  rw [h, mul_zero] at h1
  exact (card_subgroup_pos K).ne' h1.symm

/-- **Lemma 2.2** (`lem:indexreduction`) of arXiv:2505.22565: if `B ≤ A` then
`|B : B ∩ C| ≤ |A : A ∩ C|`, in multiplied-out form `|A ∩ C|·|B| ≤ |A|·|B ∩ C|`. -/
theorem card_inf_mul_card_le_of_le [Finite G] {A B : Subgroup G} (C : Subgroup G) (hBA : B ≤ A) :
    Nat.card ↥(A ⊓ C) * Nat.card B ≤ Nat.card A * Nat.card ↥(B ⊓ C) := by
  have hr : C.relIndex B ≤ C.relIndex A :=
    Subgroup.relIndex_le_of_le_right hBA (relIndex_ne_zero' C A)
  have hA := card_inf_mul_relIndex C A
  have hB := card_inf_mul_relIndex C B
  rw [inf_comm C A] at hA
  rw [inf_comm C B] at hB
  rw [← hA, ← hB]
  calc Nat.card ↥(A ⊓ C) * (Nat.card ↥(B ⊓ C) * C.relIndex B)
      = Nat.card ↥(A ⊓ C) * Nat.card ↥(B ⊓ C) * C.relIndex B := by ring
    _ ≤ Nat.card ↥(A ⊓ C) * Nat.card ↥(B ⊓ C) * C.relIndex A := Nat.mul_le_mul_left _ hr
    _ = Nat.card ↥(A ⊓ C) * C.relIndex A * Nat.card ↥(B ⊓ C) := by ring

/-- Product formula for a normal subgroup `N`: `|AN|·|N ∩ A| = |N|·|A|`. -/
theorem card_sup_mul_card_inf_of_normal (N A : Subgroup G) [N.Normal] :
    Nat.card ↥(A ⊔ N) * Nat.card ↥(N ⊓ A) = Nat.card N * Nat.card A := by
  have h1 := card_inf_mul_relIndex N (A ⊔ N)
  have h2 := card_inf_mul_relIndex N A
  rw [Subgroup.relIndex_sup_right, inf_eq_left.mpr le_sup_right] at h1
  rw [← h1, ← h2]
  ring


/-- **Lemma 2.1** (`lem:orderintersection`) of arXiv:2505.22565, inside an ambient
subgroup `C`: if `A, B ≤ C` then `|A|·|B| ≤ |C|·|A ∩ B|`. -/
theorem card_mul_card_le_of_le [Finite G] {A B C : Subgroup G} (hA : A ≤ C) (hB : B ≤ C) :
    Nat.card A * Nat.card B ≤ Nat.card C * Nat.card ↥(A ⊓ B) := by
  have h := card_inf_mul_card_le_of_le B hA
  rwa [inf_eq_right.mpr hB, mul_comm] at h

/-- **Lemma 2.3** (`lem:maxlp`) of arXiv:2505.22565, inequality: for `N` normal,
`|AN ∩ B : A ∩ B| ≤ |N : N ∩ A|`, multiplied out as
`|AN ∩ B|·|N ∩ A| ≤ |N|·|A ∩ B|`. -/
theorem card_sup_inf_mul_le [Finite G] (N A B : Subgroup G) [N.Normal] :
    Nat.card ↥((A ⊔ N) ⊓ B) * Nat.card ↥(N ⊓ A) ≤ Nat.card N * Nat.card ↥(A ⊓ B) := by
  have hXA : (A ⊔ N) ⊓ B ⊓ A = A ⊓ B :=
    le_antisymm (le_inf inf_le_right (inf_le_left.trans inf_le_right))
      (le_inf (le_inf (inf_le_left.trans le_sup_left) inf_le_right) inf_le_left)
  have h1 := card_mul_card_le_of_le (A := (A ⊔ N) ⊓ B) (B := A) (C := A ⊔ N) inf_le_left le_sup_left
  rw [hXA] at h1
  have h2 := card_sup_mul_card_inf_of_normal N A
  refine Nat.le_of_mul_le_mul_right ?_ (card_subgroup_pos A)
  calc Nat.card ↥((A ⊔ N) ⊓ B) * Nat.card ↥(N ⊓ A) * Nat.card A
      = Nat.card ↥((A ⊔ N) ⊓ B) * Nat.card A * Nat.card ↥(N ⊓ A) := by ring
    _ ≤ Nat.card ↥(A ⊔ N) * Nat.card ↥(A ⊓ B) * Nat.card ↥(N ⊓ A) := Nat.mul_le_mul_right _ h1
    _ = Nat.card ↥(A ⊔ N) * Nat.card ↥(N ⊓ A) * Nat.card ↥(A ⊓ B) := by ring
    _ = Nat.card N * Nat.card ↥(A ⊓ B) * Nat.card A := by rw [h2]; ring

/-- **Lemma 2.3** (`lem:maxlp`) of arXiv:2505.22565, equality case: if `N ≤ B` then
`|AN ∩ B : A ∩ B| ≥ |N : N ∩ A|` (so equality holds), multiplied out as
`|N|·|A ∩ B| ≤ |AN ∩ B|·|N ∩ A|`. -/
theorem le_card_sup_inf_mul [Finite G] (N A B : Subgroup G) [N.Normal] (hNB : N ≤ B) :
    Nat.card N * Nat.card ↥(A ⊓ B) ≤ Nat.card ↥((A ⊔ N) ⊓ B) * Nat.card ↥(N ⊓ A) := by
  have hY : A ⊓ B ⊔ N ≤ (A ⊔ N) ⊓ B :=
    sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right) (le_inf le_sup_right hNB)
  have hNA : N ⊓ (A ⊓ B) = N ⊓ A :=
    le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_left))
      (le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hNB)))
  have h2 := card_sup_mul_card_inf_of_normal N (A ⊓ B)
  rw [hNA] at h2
  rw [← h2]
  exact Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hY)

/-- The Ingleton inequality is invariant under swapping `H₁` and `H₂`. -/
theorem ingleton_swap₁₂ (H₁ H₂ H₃ H₄ : Subgroup G) :
    Ingleton H₁ H₂ H₃ H₄ ↔ Ingleton H₂ H₁ H₃ H₄ := by
  unfold Ingleton
  rw [inf_comm H₂ H₁]
  constructor <;> intro h <;> convert h using 1 <;> ring

/-- The Ingleton inequality is invariant under swapping `H₃` and `H₄`. -/
theorem ingleton_swap₃₄ (H₁ H₂ H₃ H₄ : Subgroup G) :
    Ingleton H₁ H₂ H₃ H₄ ↔ Ingleton H₁ H₂ H₄ H₃ := by
  unfold Ingleton
  rw [inf_comm H₄ H₃]
  constructor <;> intro h <;> convert h using 1 <;> ring

/-- Arithmetic core of enlarging `H₁` in the proof of Theorem 1.3: if one factor
`a` and one intersection factor `α` grow by the same ratio `n/m` (upper and lower
bound respectively), and the triple intersections `d, e` grow by at most the
ratios of `β, γ`, then a strict Ingleton failure is preserved. -/
theorem arith_enlarge {ja jα jβ jγ jd je a α β γ d e l r n m : ℕ} (hn : 0 < n * jβ * jγ)
    (ha : ja * m ≤ n * a) (hα : n * α ≤ jα * m) (hd : jd * β ≤ jβ * d) (he : je * γ ≤ jγ * e)
    (hoff : a * r * d * e < α * β * γ * l) : ja * r * jd * je < jα * jβ * jγ * l := by
  refine Nat.lt_of_mul_lt_mul_right (a := m * β * γ) ?_
  calc ja * r * jd * je * (m * β * γ) = (ja * m) * r * (jd * β) * (je * γ) := by ring
    _ ≤ (n * a) * r * (jβ * d) * (jγ * e) := by gcongr
    _ = (n * jβ * jγ) * (a * r * d * e) := by ring
    _ < (n * jβ * jγ) * (α * β * γ * l) := Nat.mul_lt_mul_of_pos_left hoff hn
    _ = (n * α) * jβ * jγ * l * β * γ := by ring
    _ ≤ (jα * m) * jβ * jγ * l * β * γ := by gcongr
    _ = jα * jβ * jγ * l * (m * β * γ) := by ring

/-- Arithmetic core of enlarging `H₃` in the proof of Theorem 1.3: the factors
`c, d` grow by at most `n/m` while `β, δ` grow by at least `n/m`, so a strict
Ingleton failure is preserved. -/
theorem arith_enlarge_third {jc jd jβ jδ a b c d e α β γ δ ε n m : ℕ} (hn : 0 < n * n)
    (hc : jc * m ≤ n * c) (hd : jd * m ≤ n * d) (hβ : n * β ≤ jβ * m) (hδ : n * δ ≤ jδ * m)
    (hoff : a * b * c * d * e < α * β * γ * δ * ε) :
    a * b * jc * jd * e < α * jβ * γ * jδ * ε := by
  refine Nat.lt_of_mul_lt_mul_right (a := m * m) ?_
  calc a * b * jc * jd * e * (m * m) = a * b * (jc * m) * (jd * m) * e := by ring
    _ ≤ a * b * (n * c) * (n * d) * e := by gcongr
    _ = (n * n) * (a * b * c * d * e) := by ring
    _ < (n * n) * (α * β * γ * δ * ε) := Nat.mul_lt_mul_of_pos_left hoff hn
    _ = α * (n * β) * γ * (n * δ) * ε := by ring
    _ ≤ α * (jβ * m) * γ * (jδ * m) * ε := by gcongr
    _ = α * jβ * γ * jδ * ε * (m * m) := by ring

/-- Proof of Theorem 1.3 (arXiv:2505.22565), first case: if `N` is normal with
`N ≤ H₂` and `(H₁, H₂, H₃, H₄)` is an Ingleton offender, then so is
`(H₁N, H₂, H₃, H₄)`. -/
theorem not_ingleton_sup_left_of_le_second [Finite G] (N : Subgroup G) [N.Normal]
    {H₁ H₂ H₃ H₄ : Subgroup G} (hN : N ≤ H₂) (h : ¬ Ingleton H₁ H₂ H₃ H₄) :
    ¬ Ingleton (H₁ ⊔ N) H₂ H₃ H₄ := by
  have hJ1 := (card_sup_mul_card_inf_of_normal N H₁).le
  have hJ12 := le_card_sup_inf_mul N H₁ H₂ hN
  have e3 : Nat.card ↥((H₁ ⊔ N) ⊓ H₂ ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₃) ≤
      Nat.card ↥((H₁ ⊔ N) ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₂ ⊓ H₃) := by
    have e := card_inf_mul_card_le_of_le H₂ (inf_le_inf_right H₃ (le_sup_left : H₁ ≤ H₁ ⊔ N))
    rwa [inf_right_comm (H₁ ⊔ N) H₃ H₂, inf_right_comm H₁ H₃ H₂] at e
  have e4 : Nat.card ↥((H₁ ⊔ N) ⊓ H₂ ⊓ H₄) * Nat.card ↥(H₁ ⊓ H₄) ≤
      Nat.card ↥((H₁ ⊔ N) ⊓ H₄) * Nat.card ↥(H₁ ⊓ H₂ ⊓ H₄) := by
    have e := card_inf_mul_card_le_of_le H₂ (inf_le_inf_right H₄ (le_sup_left : H₁ ≤ H₁ ⊔ N))
    rwa [inf_right_comm (H₁ ⊔ N) H₄ H₂, inf_right_comm H₁ H₄ H₂] at e
  have hn : 0 < Nat.card N * Nat.card ↥((H₁ ⊔ N) ⊓ H₃) * Nat.card ↥((H₁ ⊔ N) ⊓ H₄) :=
    Nat.mul_pos (Nat.mul_pos (card_subgroup_pos _) (card_subgroup_pos _)) (card_subgroup_pos _)
  unfold Ingleton at h ⊢
  rw [Nat.not_le] at h ⊢
  have hoff : Nat.card H₁ * (Nat.card H₂ * Nat.card ↥(H₃ ⊓ H₄)) * Nat.card ↥(H₁ ⊓ H₂ ⊓ H₃) *
      Nat.card ↥(H₁ ⊓ H₂ ⊓ H₄) < Nat.card ↥(H₁ ⊓ H₂) * Nat.card ↥(H₁ ⊓ H₃) *
      Nat.card ↥(H₁ ⊓ H₄) * (Nat.card ↥(H₂ ⊓ H₃) * Nat.card ↥(H₂ ⊓ H₄)) := by
    convert h using 1 <;> ring
  have key := arith_enlarge hn hJ1 hJ12 e3 e4 hoff
  convert key using 1 <;> ring

/-- Proof of Theorem 1.3 (arXiv:2505.22565), first case with `N ≤ H₄`: replacing
`H₁` by `H₁N` keeps an Ingleton offender an offender. -/
theorem not_ingleton_sup_left_of_le_fourth [Finite G] (N : Subgroup G) [N.Normal]
    {H₁ H₂ H₃ H₄ : Subgroup G} (hN : N ≤ H₄) (h : ¬ Ingleton H₁ H₂ H₃ H₄) :
    ¬ Ingleton (H₁ ⊔ N) H₂ H₃ H₄ := by
  have hJ1 := (card_sup_mul_card_inf_of_normal N H₁).le
  have hJ14 := le_card_sup_inf_mul N H₁ H₄ hN
  have e3 : Nat.card ↥((H₁ ⊔ N) ⊓ H₂ ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₃) ≤
      Nat.card ↥((H₁ ⊔ N) ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₂ ⊓ H₃) := by
    have e := card_inf_mul_card_le_of_le H₂ (inf_le_inf_right H₃ (le_sup_left : H₁ ≤ H₁ ⊔ N))
    rwa [inf_right_comm (H₁ ⊔ N) H₃ H₂, inf_right_comm H₁ H₃ H₂] at e
  have e4 : Nat.card ↥((H₁ ⊔ N) ⊓ H₂ ⊓ H₄) * Nat.card ↥(H₁ ⊓ H₂) ≤
      Nat.card ↥((H₁ ⊔ N) ⊓ H₂) * Nat.card ↥(H₁ ⊓ H₂ ⊓ H₄) :=
    card_inf_mul_card_le_of_le H₄ (inf_le_inf_right H₂ (le_sup_left : H₁ ≤ H₁ ⊔ N))
  have hn : 0 < Nat.card N * Nat.card ↥((H₁ ⊔ N) ⊓ H₃) * Nat.card ↥((H₁ ⊔ N) ⊓ H₂) :=
    Nat.mul_pos (Nat.mul_pos (card_subgroup_pos _) (card_subgroup_pos _)) (card_subgroup_pos _)
  unfold Ingleton at h ⊢
  rw [Nat.not_le] at h ⊢
  have hoff : Nat.card H₁ * (Nat.card H₂ * Nat.card ↥(H₃ ⊓ H₄)) * Nat.card ↥(H₁ ⊓ H₂ ⊓ H₃) *
      Nat.card ↥(H₁ ⊓ H₂ ⊓ H₄) < Nat.card ↥(H₁ ⊓ H₄) * Nat.card ↥(H₁ ⊓ H₃) *
      Nat.card ↥(H₁ ⊓ H₂) * (Nat.card ↥(H₂ ⊓ H₃) * Nat.card ↥(H₂ ⊓ H₄)) := by
    convert h using 1 <;> ring
  have key := arith_enlarge hn hJ1 hJ14 e3 e4 hoff
  convert key using 1 <;> ring

/-- Proof of Theorem 1.3, first case with `N ≤ H₃` (by the `H₃ ↔ H₄` symmetry):
replacing `H₁` by `H₁N` keeps an Ingleton offender an offender. -/
theorem not_ingleton_sup_left_of_le_third [Finite G] (N : Subgroup G) [N.Normal]
    {H₁ H₂ H₃ H₄ : Subgroup G} (hN : N ≤ H₃) (h : ¬ Ingleton H₁ H₂ H₃ H₄) :
    ¬ Ingleton (H₁ ⊔ N) H₂ H₃ H₄ := by
  rw [ingleton_swap₃₄] at h ⊢
  exact not_ingleton_sup_left_of_le_fourth N hN h

/-- Proof of Theorem 1.3 (arXiv:2505.22565), second case: if `N` is normal with
`N ≤ H₁ ∩ H₂`, replacing `H₃` by `H₃N` keeps an Ingleton offender an offender. -/
theorem not_ingleton_sup_third [Finite G] (N : Subgroup G) [N.Normal]
    {H₁ H₂ H₃ H₄ : Subgroup G} (hN₁ : N ≤ H₁) (hN₂ : N ≤ H₂) (h : ¬ Ingleton H₁ H₂ H₃ H₄) :
    ¬ Ingleton H₁ H₂ (H₃ ⊔ N) H₄ := by
  have hc := card_sup_inf_mul_le N H₃ H₄
  have hd : Nat.card ↥(H₁ ⊓ H₂ ⊓ (H₃ ⊔ N)) * Nat.card ↥(N ⊓ H₃) ≤
      Nat.card N * Nat.card ↥(H₁ ⊓ H₂ ⊓ H₃) := by
    have e := card_sup_inf_mul_le N H₃ (H₁ ⊓ H₂)
    rwa [inf_comm (H₃ ⊔ N), inf_comm H₃] at e
  have hβ : Nat.card N * Nat.card ↥(H₁ ⊓ H₃) ≤
      Nat.card ↥(H₁ ⊓ (H₃ ⊔ N)) * Nat.card ↥(N ⊓ H₃) := by
    have e := le_card_sup_inf_mul N H₃ H₁ hN₁
    rwa [inf_comm (H₃ ⊔ N), inf_comm H₃] at e
  have hδ : Nat.card N * Nat.card ↥(H₂ ⊓ H₃) ≤
      Nat.card ↥(H₂ ⊓ (H₃ ⊔ N)) * Nat.card ↥(N ⊓ H₃) := by
    have e := le_card_sup_inf_mul N H₃ H₂ hN₂
    rwa [inf_comm (H₃ ⊔ N), inf_comm H₃] at e
  have hn : 0 < Nat.card N * Nat.card N := Nat.mul_pos (card_subgroup_pos _) (card_subgroup_pos _)
  unfold Ingleton at h ⊢
  rw [Nat.not_le] at h ⊢
  exact arith_enlarge_third hn hc hd hβ hδ h

/-- Second case of the proof of Theorem 1.3 for `H₄` (by the `H₃ ↔ H₄` symmetry):
if `N ≤ H₁ ∩ H₂`, replacing `H₄` by `H₄N` keeps an Ingleton offender an offender. -/
theorem not_ingleton_sup_fourth [Finite G] (N : Subgroup G) [N.Normal]
    {H₁ H₂ H₃ H₄ : Subgroup G} (hN₁ : N ≤ H₁) (hN₂ : N ≤ H₂) (h : ¬ Ingleton H₁ H₂ H₃ H₄) :
    ¬ Ingleton H₁ H₂ H₃ (H₄ ⊔ N) := by
  rw [ingleton_swap₃₄] at h ⊢
  exact not_ingleton_sup_third N hN₁ hN₂ h

/-- Enlargement step of Theorem 1.3 (arXiv:2505.22565): if `N` is normal and
contained in some `H_i` of an Ingleton offender, then `(H₁N, H₂N, H₃N, H₄N)` is
again an Ingleton offender. -/
theorem not_ingleton_sup_all [Finite G] (N : Subgroup G) [N.Normal]
    {H₁ H₂ H₃ H₄ : Subgroup G} (hN : N ≤ H₁ ∨ N ≤ H₂ ∨ N ≤ H₃ ∨ N ≤ H₄)
    (h : ¬ Ingleton H₁ H₂ H₃ H₄) :
    ¬ Ingleton (H₁ ⊔ N) (H₂ ⊔ N) (H₃ ⊔ N) (H₄ ⊔ N) := by
  have step₁ : ¬ Ingleton (H₁ ⊔ N) H₂ H₃ H₄ := by
    rcases hN with hN | hN | hN | hN
    · rwa [sup_eq_left.mpr hN]
    · exact not_ingleton_sup_left_of_le_second N hN h
    · exact not_ingleton_sup_left_of_le_third N hN h
    · exact not_ingleton_sup_left_of_le_fourth N hN h
  have step₂ : ¬ Ingleton (H₁ ⊔ N) (H₂ ⊔ N) H₃ H₄ := by
    rw [ingleton_swap₁₂] at step₁ ⊢
    exact not_ingleton_sup_left_of_le_second N le_sup_right step₁
  have step₃ : ¬ Ingleton (H₁ ⊔ N) (H₂ ⊔ N) (H₃ ⊔ N) H₄ :=
    not_ingleton_sup_third N le_sup_right le_sup_right step₂
  exact not_ingleton_sup_fourth N le_sup_right le_sup_right step₃

/-- The full preimage in `G` of a subgroup `K ≤ G/N` has order `|K|·|N|`. -/
theorem card_comap_mk' [Finite G] (N : Subgroup G) [N.Normal] (K : Subgroup (G ⧸ N)) :
    Nat.card ↥(K.comap (QuotientGroup.mk' N)) = Nat.card K * Nat.card N := by
  have h := card_inf_mul_relIndex (QuotientGroup.mk' N).ker (K.comap (QuotientGroup.mk' N))
  rw [inf_eq_left.mpr (MonoidHom.ker_le_comap _ K), Subgroup.relIndex_ker,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N),
    QuotientGroup.ker_mk'] at h
  rw [← h, mul_comm]

/-- If the full preimages of `K₁, …, K₄ ≤ G/N` form an Ingleton offender in `G`,
then `(K₁, …, K₄)` is an Ingleton offender in `G/N`: every order in the
inequality is multiplied by `|N|`. -/
theorem not_ingleton_of_not_ingleton_comap [Finite G] (N : Subgroup G) [N.Normal]
    {K₁ K₂ K₃ K₄ : Subgroup (G ⧸ N)}
    (h : ¬ Ingleton (K₁.comap (QuotientGroup.mk' N)) (K₂.comap (QuotientGroup.mk' N))
      (K₃.comap (QuotientGroup.mk' N)) (K₄.comap (QuotientGroup.mk' N))) :
    ¬ Ingleton K₁ K₂ K₃ K₄ := by
  intro hK
  apply h
  unfold Ingleton at hK ⊢
  simp only [← Subgroup.comap_inf, card_comap_mk']
  calc _ = (Nat.card ↥(K₁ ⊓ K₂) * Nat.card ↥(K₁ ⊓ K₃) * Nat.card ↥(K₁ ⊓ K₄) *
          Nat.card ↥(K₂ ⊓ K₃) * Nat.card ↥(K₂ ⊓ K₄)) * Nat.card N ^ 5 := by ring
    _ ≤ (Nat.card K₁ * Nat.card K₂ * Nat.card ↥(K₃ ⊓ K₄) * Nat.card ↥(K₁ ⊓ K₂ ⊓ K₃) *
          Nat.card ↥(K₁ ⊓ K₂ ⊓ K₄)) * Nat.card N ^ 5 := Nat.mul_le_mul_right _ hK
    _ = _ := by ring

/-- **Theorem 1.3** (`thm:removenormal`) of arXiv:2505.22565, in the form its proof
establishes: if `(H₁, H₂, H₃, H₄)` is an Ingleton offender in a finite group `G`
and `N` is a normal subgroup contained in some `H_i`, then the images
`(H₁N/N, H₂N/N, H₃N/N, H₄N/N)` form an Ingleton offender in `G/N`. -/
theorem not_ingleton_map_of_le [Finite G] (N : Subgroup G) [N.Normal]
    {H₁ H₂ H₃ H₄ : Subgroup G} (hN : N ≤ H₁ ∨ N ≤ H₂ ∨ N ≤ H₃ ∨ N ≤ H₄)
    (h : ¬ Ingleton H₁ H₂ H₃ H₄) :
    ¬ Ingleton (H₁.map (QuotientGroup.mk' N)) (H₂.map (QuotientGroup.mk' N))
      (H₃.map (QuotientGroup.mk' N)) (H₄.map (QuotientGroup.mk' N)) := by
  apply not_ingleton_of_not_ingleton_comap N
  simp only [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  exact not_ingleton_sup_all N hN h

/-- Distributivity of `gcd` over `lcm` (one divisibility):
`gcd(p, lcm(a, b)) ∣ lcm(gcd(p, a), gcd(p, b))` for nonzero `p, a, b`. -/
theorem gcd_lcm_dvd_lcm_gcd {p a b : ℕ} (hp : p ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.gcd p (Nat.lcm a b) ∣ Nat.lcm (Nat.gcd p a) (Nat.gcd p b) := by
  have hl : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha hb
  have hga : Nat.gcd p a ≠ 0 := Nat.gcd_ne_zero_left hp
  have hgb : Nat.gcd p b ≠ 0 := Nat.gcd_ne_zero_left hp
  rw [← Nat.factorization_le_iff_dvd (Nat.gcd_ne_zero_left hp) (Nat.lcm_ne_zero hga hgb),
    Nat.factorization_gcd hp hl, Nat.factorization_lcm ha hb, Nat.factorization_lcm hga hgb,
    Nat.factorization_gcd hp ha, Nat.factorization_gcd hp hb, Finsupp.le_def]
  intro q
  simp only [Finsupp.inf_apply, Finsupp.sup_apply]
  omega

/-- If `x ^ lcm(s, t) = 1` then `x = y z` with `y ^ s = 1` and `z ^ t = 1`
(both `y, z` are powers of `x`, obtained by Bézout). -/
theorem exists_mul_eq_of_pow_lcm_eq_one {M : Type*} [Group M] (x : M) {s t : ℕ}
    (hs : 0 < s) (hx : x ^ Nat.lcm s t = 1) :
    ∃ y z : M, y ^ s = 1 ∧ z ^ t = 1 ∧ y * z = x := by
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd s t := ⟨_, rfl⟩
  have hgpos : 0 < g := hg ▸ Nat.gcd_pos_of_pos_left t hs
  obtain ⟨s', hs'⟩ := Nat.gcd_dvd_left s t
  obtain ⟨t', ht'⟩ := Nat.gcd_dvd_right s t
  have hcop : Nat.gcd s' t' = 1 := by
    have h := Nat.gcd_mul_left (Nat.gcd s t) s' t'
    rw [← hs', ← ht', ← hg] at h
    have h2 : g * Nat.gcd s' t' = g * 1 := by rw [← h, mul_one]
    exact Nat.eq_of_mul_eq_mul_left hgpos h2
  rw [← hg] at hs' ht'
  have hlcm : Nat.lcm s t = g * s' * t' := by
    have h := Nat.gcd_mul_lcm s t
    rw [← hg] at h
    apply Nat.eq_of_mul_eq_mul_left hgpos
    rw [h, hs', ht']
    ring
  have hbez := Nat.gcd_eq_gcd_ab s' t'
  rw [hcop, Nat.cast_one] at hbez
  refine ⟨x ^ ((t' : ℤ) * Nat.gcdB s' t'), x ^ ((s' : ℤ) * Nat.gcdA s' t'), ?_, ?_, ?_⟩
  · rw [← zpow_natCast, ← zpow_mul]
    have he : (t' : ℤ) * Nat.gcdB s' t' * (s : ℤ) = ((Nat.lcm s t : ℕ) : ℤ) * Nat.gcdB s' t' := by
      rw [hlcm]; nth_rewrite 1 [hs']; push_cast; ring
    rw [he, zpow_mul, zpow_natCast, hx, one_zpow]
  · rw [← zpow_natCast, ← zpow_mul]
    have he : (s' : ℤ) * Nat.gcdA s' t' * (t : ℤ) = ((Nat.lcm s t : ℕ) : ℤ) * Nat.gcdA s' t' := by
      rw [hlcm]; nth_rewrite 1 [ht']; push_cast; ring
    rw [he, zpow_mul, zpow_natCast, hx, one_zpow]
  · rw [← zpow_add]
    have he : (t' : ℤ) * Nat.gcdB s' t' + (s' : ℤ) * Nat.gcdA s' t' = 1 := by
      rw [hbez]; ring
    rw [he, zpow_one]

section Cyclic

variable {Z : Type*} [Group Z] [IsCyclic Z] [Finite Z]

/-- In a finite cyclic group a subgroup `S` is exactly the set of `x` with
`x ^ |S| = 1`. -/
theorem mem_iff_pow_card_eq_one (S : Subgroup Z) (x : Z) : x ∈ S ↔ x ^ Nat.card S = 1 := by
  constructor
  · intro hx
    have h := congrArg Subtype.val (pow_card_eq_one' (x := (⟨x, hx⟩ : S)))
    rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
  · intro hx
    classical
    haveI : Fintype Z := Fintype.ofFinite Z
    have hT : (Finset.univ.filter (fun a : Z => a ^ Nat.card S = 1)).card ≤ Nat.card S :=
      IsCyclic.card_pow_eq_one_le Nat.card_pos
    have hsub : Finset.univ.filter (fun a : Z => a ∈ S) ⊆
        Finset.univ.filter (fun a : Z => a ^ Nat.card S = 1) := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      have h := congrArg Subtype.val (pow_card_eq_one' (x := (⟨a, ha⟩ : S)))
      rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
    have hcard : (Finset.univ.filter (fun a : Z => a ∈ S)).card = Nat.card S := by
      rw [← Nat.card_eq_finsetCard]
      exact Nat.card_congr (Equiv.subtypeEquivRight (by simp))
    have heq := Finset.eq_of_subset_of_card_le hsub (hT.trans hcard.ge)
    have hxT : x ∈ Finset.univ.filter (fun a : Z => a ^ Nat.card S = 1) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hx
    rw [← heq] at hxT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxT
    exact hxT

/-- In a finite cyclic group, every element of `A ⊔ B` satisfies
`x ^ lcm(|A|, |B|) = 1`. -/
theorem pow_lcm_eq_one_of_mem_sup {A B : Subgroup Z} {x : Z} (hx : x ∈ A ⊔ B) :
    x ^ Nat.lcm (Nat.card A) (Nat.card B) = 1 := by
  have hx' : x ∈ ((A : Set Z) * (B : Set Z)) := by rw [← Subgroup.mul_normal]; exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx'
  have hcomm : Commute a b := mul_comm' a b
  obtain ⟨k, hk⟩ := Nat.dvd_lcm_left (Nat.card A) (Nat.card B)
  obtain ⟨l, hl⟩ := Nat.dvd_lcm_right (Nat.card A) (Nat.card B)
  rw [hcomm.mul_pow]
  nth_rewrite 1 [hk]
  rw [hl, pow_mul, pow_mul, (mem_iff_pow_card_eq_one A a).mp ha,
    (mem_iff_pow_card_eq_one B b).mp hb, one_pow, one_pow, one_mul]

/-- The subgroup lattice of a finite cyclic group is distributive:
`P ∩ (A ⊔ B) ≤ (P ∩ A) ⊔ (P ∩ B)`. -/
theorem inf_sup_le_sup_inf (P A B : Subgroup Z) : P ⊓ (A ⊔ B) ≤ (P ⊓ A) ⊔ (P ⊓ B) := by
  intro x hx
  have hxP : x ^ Nat.card P = 1 := (mem_iff_pow_card_eq_one P x).mp hx.1
  have hxAB := pow_lcm_eq_one_of_mem_sup hx.2
  have hg : x ^ Nat.gcd (Nat.card P) (Nat.lcm (Nat.card A) (Nat.card B)) = 1 :=
    pow_gcd_eq_one.mpr ⟨hxP, hxAB⟩
  obtain ⟨k, hk⟩ := gcd_lcm_dvd_lcm_gcd (Nat.card_pos (α := P)).ne'
    (Nat.card_pos (α := A)).ne' (Nat.card_pos (α := B)).ne'
  have hL : x ^ Nat.lcm (Nat.gcd (Nat.card P) (Nat.card A))
      (Nat.gcd (Nat.card P) (Nat.card B)) = 1 := by
    rw [hk, pow_mul, hg, one_pow]
  obtain ⟨y, z, hy, hz, rfl⟩ := exists_mul_eq_of_pow_lcm_eq_one x
    (Nat.gcd_pos_of_pos_left _ Nat.card_pos) hL
  have hyPA : y ∈ P ⊓ A := by
    obtain ⟨u, hu⟩ := Nat.gcd_dvd_left (Nat.card P) (Nat.card A)
    obtain ⟨v, hv⟩ := Nat.gcd_dvd_right (Nat.card P) (Nat.card A)
    refine ⟨(mem_iff_pow_card_eq_one P y).mpr ?_, (mem_iff_pow_card_eq_one A y).mpr ?_⟩
    · rw [hu, pow_mul, hy, one_pow]
    · rw [hv, pow_mul, hy, one_pow]
  have hzPB : z ∈ P ⊓ B := by
    obtain ⟨u, hu⟩ := Nat.gcd_dvd_left (Nat.card P) (Nat.card B)
    obtain ⟨v, hv⟩ := Nat.gcd_dvd_right (Nat.card P) (Nat.card B)
    refine ⟨(mem_iff_pow_card_eq_one P z).mpr ?_, (mem_iff_pow_card_eq_one B z).mpr ?_⟩
    · rw [hu, pow_mul, hz, one_pow]
    · rw [hv, pow_mul, hz, one_pow]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hyPA) (Subgroup.mem_sup_right hzPB)

end Cyclic

/-- `subgroupOf` commutes with intersections. -/
theorem inf_subgroupOf_eq (H K L : Subgroup G) :
    (H ⊓ K).subgroupOf L = H.subgroupOf L ⊓ K.subgroupOf L :=
  Subgroup.comap_inf H K L.subtype

/-- If `H ≤ K` then `H.subgroupOf K` has the order of `H`. -/
theorem card_subgroupOf_of_le {H K : Subgroup G} (h : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H := by
  rw [card_subgroupOf_eq, inf_eq_left.mpr h]

/-- Product formula inside a cyclic subgroup `C`: if `X, Y ≤ C` then
`|X ⊔ Y|·|X ∩ Y| = |X|·|Y|`. -/
theorem card_sup_mul_card_inf_of_le_isCyclic [Finite G] {C X Y : Subgroup G} [IsCyclic C]
    (hX : X ≤ C) (hY : Y ≤ C) :
    Nat.card ↥(X ⊔ Y) * Nat.card ↥(X ⊓ Y) = Nat.card X * Nat.card Y := by
  have h := card_sup_mul_card_inf_of_normal (Y.subgroupOf C) (X.subgroupOf C)
  rw [← Subgroup.subgroupOf_sup hX hY, inf_comm, ← inf_subgroupOf_eq,
    card_subgroupOf_of_le (sup_le hX hY), card_subgroupOf_of_le hX, card_subgroupOf_of_le hY] at h
  rw [mul_comm (Nat.card Y)] at h
  rw [← h]
  congr 1
  exact card_subgroupOf_of_le (inf_le_left.trans hX) |>.symm

/-- Distributivity inside a cyclic subgroup `C` (used in the proof of Corollary 2.7 of
arXiv:2505.22565): if `P, A, B ≤ C` then `P ∩ (A ⊔ B) ≤ (P ∩ A) ⊔ (P ∩ B)`. -/
theorem inf_sup_le_of_le_isCyclic [Finite G] {C P A B : Subgroup G} [IsCyclic C]
    (hP : P ≤ C) (hA : A ≤ C) (hB : B ≤ C) : P ⊓ (A ⊔ B) ≤ (P ⊓ A) ⊔ (P ⊓ B) := by
  intro x hx
  have hxC : x ∈ C := hP hx.1
  have hx' : (⟨x, hxC⟩ : C) ∈ P.subgroupOf C ⊓ (A.subgroupOf C ⊔ B.subgroupOf C) := by
    rw [← Subgroup.subgroupOf_sup hA hB]
    exact ⟨hx.1, hx.2⟩
  have hy := inf_sup_le_sup_inf (P.subgroupOf C) (A.subgroupOf C) (B.subgroupOf C) hx'
  rw [← inf_subgroupOf_eq, ← inf_subgroupOf_eq,
    ← Subgroup.subgroupOf_sup (inf_le_left.trans hP) (inf_le_left.trans hP)] at hy
  exact hy

/-- **Proposition 2.6** (`prop:ingoffenderfact`) of arXiv:2505.22565, in the numeric
form its proof uses: if `|H₁₂|·|H₁₂₃ ∩ H₁₂₄| ≤ |H₁₂₃|·|H₁₂₄|` (which holds when
`H₁₂ = H₁₂₃H₁₂₄`), then the Ingleton inequality holds. -/
theorem ingleton_of_card_mul_le [Finite G] (H₁ H₂ H₃ H₄ : Subgroup G)
    (h : Nat.card ↥(H₁ ⊓ H₂) * Nat.card ↥((H₁ ⊓ H₂ ⊓ H₃) ⊓ (H₁ ⊓ H₂ ⊓ H₄)) ≤
      Nat.card ↥(H₁ ⊓ H₂ ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₂ ⊓ H₄)) :
    Ingleton H₁ H₂ H₃ H₄ := by
  set P : Subgroup G := H₁ ⊓ H₃ ⊓ H₄ with hP
  set Q : Subgroup G := H₂ ⊓ H₃ ⊓ H₄ with hQ
  set R : Subgroup G := (H₁ ⊓ H₂ ⊓ H₃) ⊓ (H₁ ⊓ H₂ ⊓ H₄) with hR
  have i1 : Nat.card ↥(H₁ ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₄) ≤ Nat.card H₁ * Nat.card P := by
    have e := card_mul_card_le_of_le (inf_le_left : H₁ ⊓ H₃ ≤ H₁) (inf_le_left : H₁ ⊓ H₄ ≤ H₁)
    have hPe : H₁ ⊓ H₃ ⊓ (H₁ ⊓ H₄) = P := by
      rw [hP, inf_assoc, inf_left_comm H₃, ← inf_assoc H₁ H₁, inf_idem, inf_assoc]
    rwa [hPe] at e
  have i2 : Nat.card ↥(H₂ ⊓ H₃) * Nat.card ↥(H₂ ⊓ H₄) ≤ Nat.card H₂ * Nat.card Q := by
    have e := card_mul_card_le_of_le (inf_le_left : H₂ ⊓ H₃ ≤ H₂) (inf_le_left : H₂ ⊓ H₄ ≤ H₂)
    have hQe : H₂ ⊓ H₃ ⊓ (H₂ ⊓ H₄) = Q := by
      rw [hQ, inf_assoc, inf_left_comm H₃, ← inf_assoc H₂ H₂, inf_idem, inf_assoc]
    rwa [hQe] at e
  have i3 : Nat.card P * Nat.card Q ≤ Nat.card ↥(H₃ ⊓ H₄) * Nat.card R := by
    have hP34 : P ≤ H₃ ⊓ H₄ := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have hQ34 : Q ≤ H₃ ⊓ H₄ := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have e := card_mul_card_le_of_le hP34 hQ34
    have hRe : P ⊓ Q ≤ R := by
      intro x hx
      simp only [hP, hQ, hR, Subgroup.mem_inf] at hx ⊢
      tauto
    exact e.trans (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hRe))
  have hpos : 0 < Nat.card P * Nat.card Q * Nat.card R :=
    Nat.mul_pos (Nat.mul_pos (card_subgroup_pos P) (card_subgroup_pos Q)) (card_subgroup_pos R)
  unfold Ingleton
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card ↥(H₁ ⊓ H₂) * Nat.card ↥(H₁ ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₄) *
          Nat.card ↥(H₂ ⊓ H₃) * Nat.card ↥(H₂ ⊓ H₄) * (Nat.card P * Nat.card Q * Nat.card R)
        = (Nat.card ↥(H₁ ⊓ H₂) * Nat.card R) *
            (Nat.card ↥(H₁ ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₄)) *
            (Nat.card ↥(H₂ ⊓ H₃) * Nat.card ↥(H₂ ⊓ H₄)) * (Nat.card P * Nat.card Q) := by
          ring
      _ ≤ (Nat.card ↥(H₁ ⊓ H₂ ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₂ ⊓ H₄)) *
            (Nat.card H₁ * Nat.card P) * (Nat.card H₂ * Nat.card Q) *
            (Nat.card ↥(H₃ ⊓ H₄) * Nat.card R) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h i1) i2) i3
      _ = Nat.card H₁ * Nat.card H₂ * Nat.card ↥(H₃ ⊓ H₄) * Nat.card ↥(H₁ ⊓ H₂ ⊓ H₃) *
            Nat.card ↥(H₁ ⊓ H₂ ⊓ H₄) * (Nat.card P * Nat.card Q * Nat.card R) := by
          ring

/-- **Lemma 2.4** (`lem:reducesizeofH1`) of arXiv:2505.22565, generalized: if
`H₁' ≤ H₁` contains `H₁₃` and `H₁₄` and `(H₁', H₂, H₃, H₄)` satisfies the Ingleton
inequality, so does `(H₁, H₂, H₃, H₄)`.  (The paper takes `H₁' = ⟨H₁₃, H₁₄⟩`.) -/
theorem ingleton_of_ingleton_of_le [Finite G] {H₁ H₁' : Subgroup G} (H₂ H₃ H₄ : Subgroup G)
    (hle : H₁' ≤ H₁) (h₃ : H₁ ⊓ H₃ ≤ H₁') (h₄ : H₁ ⊓ H₄ ≤ H₁')
    (h : Ingleton H₁' H₂ H₃ H₄) : Ingleton H₁ H₂ H₃ H₄ := by
  have e3 : H₁' ⊓ H₃ = H₁ ⊓ H₃ :=
    le_antisymm (inf_le_inf_right H₃ hle) (le_inf h₃ inf_le_right)
  have e4 : H₁' ⊓ H₄ = H₁ ⊓ H₄ :=
    le_antisymm (inf_le_inf_right H₄ hle) (le_inf h₄ inf_le_right)
  have e23 : H₁' ⊓ H₂ ⊓ H₃ = H₁ ⊓ H₂ ⊓ H₃ := by
    rw [inf_right_comm, e3, inf_right_comm]
  have e24 : H₁' ⊓ H₂ ⊓ H₄ = H₁ ⊓ H₂ ⊓ H₄ := by
    rw [inf_right_comm, e4, inf_right_comm]
  have hidx := card_inf_mul_card_le_of_le H₂ hle
  unfold Ingleton at h ⊢
  rw [e3, e4, e23, e24] at h
  refine Nat.le_of_mul_le_mul_right ?_ (card_subgroup_pos H₁')
  calc Nat.card ↥(H₁ ⊓ H₂) * Nat.card ↥(H₁ ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₄) *
          Nat.card ↥(H₂ ⊓ H₃) * Nat.card ↥(H₂ ⊓ H₄) * Nat.card H₁'
        = (Nat.card ↥(H₁ ⊓ H₂) * Nat.card H₁') * (Nat.card ↥(H₁ ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₄) *
          Nat.card ↥(H₂ ⊓ H₃) * Nat.card ↥(H₂ ⊓ H₄)) := by ring
      _ ≤ (Nat.card H₁ * Nat.card ↥(H₁' ⊓ H₂)) * (Nat.card ↥(H₁ ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₄) *
          Nat.card ↥(H₂ ⊓ H₃) * Nat.card ↥(H₂ ⊓ H₄)) := Nat.mul_le_mul_right _ hidx
      _ = Nat.card H₁ * (Nat.card ↥(H₁' ⊓ H₂) * Nat.card ↥(H₁ ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₄) *
          Nat.card ↥(H₂ ⊓ H₃) * Nat.card ↥(H₂ ⊓ H₄)) := by ring
      _ ≤ Nat.card H₁ * (Nat.card H₁' * Nat.card H₂ * Nat.card ↥(H₃ ⊓ H₄) *
          Nat.card ↥(H₁ ⊓ H₂ ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₂ ⊓ H₄)) := Nat.mul_le_mul_left _ h
      _ = _ := by ring

/-- **Corollary 2.7** (`cor:H1notcyclic`) of arXiv:2505.22565, for `H₁`: if `H₁` is
cyclic then `(H₁, H₂, H₃, H₄)` is not an Ingleton offender. -/
theorem ingleton_of_isCyclic_left [Finite G] (H₁ H₂ H₃ H₄ : Subgroup G) [IsCyclic H₁] :
    Ingleton H₁ H₂ H₃ H₄ := by
  set C : Subgroup G := H₁ ⊓ H₃ ⊔ H₁ ⊓ H₄ with hCdef
  have hC : C ≤ H₁ := sup_le inf_le_left inf_le_left
  haveI : IsCyclic C := Subgroup.isCyclic_of_le hC
  refine ingleton_of_ingleton_of_le H₂ H₃ H₄ hC le_sup_left le_sup_right ?_
  apply ingleton_of_card_mul_le
  have hX : C ⊓ H₂ ⊓ H₃ ≤ C := inf_le_left.trans inf_le_left
  have hY : C ⊓ H₂ ⊓ H₄ ≤ C := inf_le_left.trans inf_le_left
  have hdist : C ⊓ H₂ ≤ C ⊓ H₂ ⊓ H₃ ⊔ C ⊓ H₂ ⊓ H₄ := by
    have e := inf_sup_le_of_le_isCyclic (C := C) (P := C ⊓ H₂) (A := H₁ ⊓ H₃) (B := H₁ ⊓ H₄)
      inf_le_left le_sup_left le_sup_right
    refine (le_inf le_rfl inf_le_left).trans (e.trans (sup_le_sup ?_ ?_))
    · exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
    · exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
  have hprod := card_sup_mul_card_inf_of_le_isCyclic hX hY
  rw [← hprod]
  exact Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hdist)

/-- A group is **metacyclic** if it has a cyclic normal subgroup `K` with `G/K`
cyclic (arXiv:2505.22565, proof of Theorem 1.1). -/
def IsMetacyclic (G : Type*) [Group G] : Prop :=
  ∃ (K : Subgroup G) (_ : K.Normal), IsCyclic K ∧ IsCyclic (G ⧸ K)

/-- Ground truth for `IsMetacyclic`: the non-abelian dihedral group of order 6
(`S₃`) is metacyclic, with `K` the rotation subgroup of order 3. -/
theorem isMetacyclic_dihedralGroup_three : IsMetacyclic (DihedralGroup 3) := by
  let K : Subgroup (DihedralGroup 3) := Subgroup.zpowers (DihedralGroup.r 1)
  have hKcard : Nat.card K = 3 := by
    rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  have hidx : K.index = 2 := by
    have h := Subgroup.card_mul_index K
    rw [hKcard, DihedralGroup.nat_card] at h
    omega
  haveI : K.Normal := Subgroup.normal_of_index_eq_two hidx
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨K, inferInstance, Subgroup.isCyclic_zpowers _, ?_⟩
  have hq : Nat.card (DihedralGroup 3 ⧸ K) = 2 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  exact isCyclic_of_prime_card hq

/-- The dihedral group of order 6 is not commutative, so
`isMetacyclic_dihedralGroup_three` exercises `IsMetacyclic` beyond the abelian
case (where the result is Chan's 2007 theorem). -/
theorem not_isMulCommutative_dihedralGroup_three : ¬ IsMulCommutative (DihedralGroup 3) := by
  intro h
  have hc := mul_comm' (DihedralGroup.r 1 : DihedralGroup 3) (DihedralGroup.sr 0)
  revert hc
  decide

/-- Inside a finite cyclic subgroup `C`, a subgroup `S ≤ C` consists exactly of the
`x ∈ C` with `x ^ |S| = 1`. -/
theorem mem_iff_pow_card_eq_one_of_le [Finite G] {C S : Subgroup G} [IsCyclic C] (hS : S ≤ C)
    {x : G} (hx : x ∈ C) : x ∈ S ↔ x ^ Nat.card S = 1 := by
  have h := mem_iff_pow_card_eq_one (S.subgroupOf C) ⟨x, hx⟩
  rw [Subgroup.mem_subgroupOf, card_subgroupOf_of_le hS, Subtype.ext_iff,
    SubgroupClass.coe_pow, OneMemClass.coe_one] at h
  exact h

/-- Every subgroup of a cyclic normal subgroup is normal (it is characteristic in the
cyclic subgroup). -/
theorem normal_of_le_isCyclic [Finite G] {K N : Subgroup G} [hK : K.Normal] [IsCyclic K]
    (hNK : N ≤ K) : N.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hc : g * n * g⁻¹ ∈ K := hK.conj_mem n (hNK hn) g
  rw [mem_iff_pow_card_eq_one_of_le hNK hc, conj_pow,
    (mem_iff_pow_card_eq_one_of_le hNK (hNK hn)).mp hn, mul_one, mul_inv_cancel]

/-- If `G/K` is cyclic and `H ∩ K = 1`, then `H` embeds in `G/K` and is cyclic. -/
theorem isCyclic_of_inf_eq_bot {K H : Subgroup G} [K.Normal] [IsCyclic (G ⧸ K)]
    (h : H ⊓ K = ⊥) : IsCyclic H := by
  refine isCyclic_of_injective ((QuotientGroup.mk' K).comp H.subtype) ?_
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxK : (x : G) ∈ K := by
    rw [← QuotientGroup.ker_mk' K]
    exact hx
  have hxb : (x : G) ∈ H ⊓ K := ⟨x.2, hxK⟩
  rw [h, Subgroup.mem_bot] at hxb
  exact Subtype.ext hxb

/-- Quotients of metacyclic groups are metacyclic. -/
theorem isMetacyclic_quotient {K : Subgroup G} [K.Normal] [IsCyclic K] [IsCyclic (G ⧸ K)]
    (N : Subgroup G) [N.Normal] : IsMetacyclic (G ⧸ N) := by
  let K' : Subgroup (G ⧸ N) := K.map (QuotientGroup.mk' N)
  haveI hK' : K'.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
  refine ⟨K', hK', ?_, ?_⟩
  · exact isCyclic_of_surjective ((QuotientGroup.mk' N).subgroupMap K)
      ((QuotientGroup.mk' N).subgroupMap_surjective K)
  · refine isCyclic_of_surjective (QuotientGroup.map K K' (QuotientGroup.mk' N)
      (Subgroup.le_comap_map _ K)) ?_
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective K' y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
    exact ⟨QuotientGroup.mk' K x, rfl⟩

/-- Quotienting a finite group by a nontrivial normal subgroup lowers the order. -/
theorem card_quotient_lt [Finite G] {N : Subgroup G} [N.Normal] (hN : N ≠ ⊥) :
    Nat.card (G ⧸ N) < Nat.card G := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have h1 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hN
  have h2 : 0 < Nat.card (G ⧸ N) := Nat.card_pos
  calc Nat.card (G ⧸ N) = Nat.card (G ⧸ N) * 1 := (mul_one _).symm
    _ < Nat.card (G ⧸ N) * Nat.card N := Nat.mul_lt_mul_of_pos_left h1 h2
    _ = Nat.card G := h.symm

universe u

/-- Strong induction on the order for Theorem 1.1: every finite metacyclic group of
order `n` (in a fixed universe) satisfies the Ingleton inequality for every quadruple
of subgroups. -/
theorem ingleton_of_isMetacyclic_aux (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G = n → IsMetacyclic G →
      ∀ H₁ H₂ H₃ H₄ : Subgroup G, Ingleton H₁ H₂ H₃ H₄ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ hn hG H₁ H₂ H₃ H₄
    by_contra hoff
    obtain ⟨K, hK, hKc, hQc⟩ := hG
    have hH₁ : ¬ IsCyclic H₁ := fun hc => hoff (ingleton_of_isCyclic_left H₁ H₂ H₃ H₄)
    have hNbot : H₁ ⊓ K ≠ ⊥ := fun hb => hH₁ (isCyclic_of_inf_eq_bot hb)
    haveI : (H₁ ⊓ K).Normal := normal_of_le_isCyclic (K := K) inf_le_right
    have hoffQ := not_ingleton_map_of_le (H₁ ⊓ K) (Or.inl inf_le_left) hoff
    have hlt : Nat.card (G ⧸ (H₁ ⊓ K)) < n := hn ▸ card_quotient_lt hNbot
    exact hoffQ (ih _ hlt (G ⧸ (H₁ ⊓ K)) rfl (isMetacyclic_quotient (K := K) (H₁ ⊓ K)) _ _ _ _)

/-- **Theorem 1.1** (`thm:nometacyclic`) of arXiv:2505.22565: in a finite metacyclic
group every quadruple of subgroups satisfies the Ingleton inequality. -/
theorem ingleton_of_isMetacyclic {G : Type u} [Group G] [Finite G] (hG : IsMetacyclic G)
    (H₁ H₂ H₃ H₄ : Subgroup G) : Ingleton H₁ H₂ H₃ H₄ :=
  ingleton_of_isMetacyclic_aux _ G rfl hG H₁ H₂ H₃ H₄
/-- **Theorem 1.1** (`thm:nometacyclic`) of arXiv:2505.22565, verbatim form: "There
are no metacyclic Ingleton violators." -/
theorem not_isIngletonViolator_of_isMetacyclic {G : Type u} [Group G] [Finite G]
    (hG : IsMetacyclic G) : ¬ IsIngletonViolator G := by
  rintro ⟨H₁, H₂, H₃, H₄, hoff⟩
  exact hoff (ingleton_of_isMetacyclic hG H₁ H₂ H₃ H₄)

/-- **Theorem 1.1** of arXiv:2505.22565 with the metacyclic structure explicit: if
the finite group `G` has a cyclic normal subgroup `K` with `G/K` cyclic, every
quadruple of subgroups of `G` satisfies the Ingleton inequality. -/
theorem ingleton_of_metacyclic {G : Type u} [Group G] [Finite G] (K : Subgroup G)
    [K.Normal] (hK : IsCyclic K) (hQ : IsCyclic (G ⧸ K)) (H₁ H₂ H₃ H₄ : Subgroup G) :
    Ingleton H₁ H₂ H₃ H₄ :=
  ingleton_of_isMetacyclic ⟨K, inferInstance, hK, hQ⟩ H₁ H₂ H₃ H₄

/-- Satisfiability check for Theorem 1.1: its hypotheses hold jointly for the
non-abelian group `DihedralGroup 3`, which therefore has no Ingleton offender. -/
example : ¬ IsIngletonViolator (DihedralGroup 3) :=
  not_isIngletonViolator_of_isMetacyclic isMetacyclic_dihedralGroup_three

end Candidates.MetacyclicIngleton
