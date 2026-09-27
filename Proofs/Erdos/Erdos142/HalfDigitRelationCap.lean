/-
  Erdős Problem #142 — the half-digit scalar-cap obstruction for arbitrary relations.

  This file formalizes one finite, explicitly constructive obstruction.  Fix `N` and
  put `H = halfDigit N = (N + 1) / 2 = ⌈N/2⌉`.  Let `B ⊆ [0,H)` and `C ⊆ [0,N)` be
  *ordinarily* 3-AP-free finite sets of naturals (Mathlib's `ThreeAPFree (· : Set ℕ)`),
  and let `G ⊆ B × C` be an **arbitrary** finite relation.  Then the base-`N` scalar
  image `φ(G)` of `G` under

      `φ (b, c) = b + N * c`

  is 3-AP-free in `ℕ`.  The endpoint `scalarPair_image_threeAPFree` quantifies over an
  arbitrary `G`; it does not merely exhibit one relation.

  Exact carry elimination.  If `φ(p) + φ(r) = φ(q) + φ(q)` for `p, q, r ∈ G`, then in
  `ℤ`

      `(p.1 + r.1 - 2*q.1) + N * (p.2 + r.2 - 2*q.2) = 0`.

  The *low* residual `L = p.1 + r.1 - 2*q.1` satisfies `|L| < N` because every
  `b ∈ B` obeys `b < H` and `2 * H ≤ N + 1` (`abs_lowResidual_lt`); since `N ∣ L`
  by the displayed identity, `Int.eq_zero_of_abs_lt_dvd` forces `L = 0`.  Then
  `N * (p.2 + r.2 - 2*q.2) = 0`, so for `N ≥ 1` the high residual vanishes as well.
  Both residuals being zero means `p.1 + r.1 = q.1 + q.1` and `p.2 + r.2 = q.2 + q.2`,
  and `ThreeAPFree B`, `ThreeAPFree C` force `p = q`.  Hence no nontrivial progression
  survives the scalar map.  The same argument with `N = 0` is vacuous, since then
  `H = 0` and `B = ∅`; that case is discharged separately, so the theorem needs no
  positivity hypothesis on `N`.

  Also proved here:

  * `scalarPair_injective_of_lt` — `φ` is injective on pairs with low digit `< N`
    (no bound is needed on the high digit);
  * `card_image_scalarPair` — the scalar image of an arbitrary `G ⊆ B × C` has the
    same cardinality as `G`;
  * `exists_threeAPFree_card_halfDigit_mul` — the witness form of the construction:
    for every `N` there is a 3-AP-free `S ⊆ [0, N^2)` of cardinality
    `rothNumberNat ((N+1)/2) * rothNumberNat N`, namely the scalar image of
    `B₀ × C₀` for maximum 3-AP-free `B₀ ⊆ [0,(N+1)/2)` and `C₀ ⊆ [0,N)`;
  * `rothNumberNat_halfDigit_mul_le_rothNumberNat_sq` — the direct lower-product
    bound `r₃ ((N+1)/2) * r₃ N ≤ r₃ (N^2)` obtained from that witness.  The accepted
    module `Erdos.Erdos142.SquareScaleProduct` already proves this inequality by the
    scale-product route (its `rothNumberNat_mul_rothNumberNat_half_le` at `N = M`);
    the copy here is an *independent* second proof through the arbitrary-relation
    construction, and it is deliberately named differently.

  Scope.  This is a finite obstruction statement, not an asymptotic solution of
  Erdős Problem #142, and it claims no new Roth-type estimate.  No `sorry`, no
  `unsafe`, no new axioms.
-/

import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option autoImplicit false

open Finset

namespace Erdos142

/-! ## The half-digit bound and the scalar pairing -/

/-- The half-digit bound `H = (N + 1) / 2 = ⌈N/2⌉`.  It is the largest half-width for
which the carry elimination below is forced by magnitude alone: `2 * H ≤ N + 1`. -/
def halfDigit (N : ℕ) : ℕ := (N + 1) / 2

/-- The base-`N` scalar pairing `φ (b, c) = b + N * c`, read with the low digit `b`
first and the high digit `c` second.  It is the transpose of the base-`N` encoding
`Erdos142.scalarImage`, which reads `(x, y) ↦ x * N + y`. -/
def scalarPair (N : ℕ) (p : ℕ × ℕ) : ℕ := p.1 + N * p.2

/-- Ground-truth checks on `halfDigit` at the parity boundary. -/
example : halfDigit 0 = 0 := rfl
example : halfDigit 1 = 1 := rfl
example : halfDigit 2 = 1 := rfl
example : halfDigit 3 = 2 := rfl
example : halfDigit 4 = 2 := rfl
example : halfDigit 7 = 4 := rfl

/-- Ground-truth checks on `scalarPair`, including the degenerate `N = 0`. -/
example : scalarPair 10 (3, 5) = 53 := rfl
example : scalarPair 10 (0, 0) = 0 := rfl
example : scalarPair 0 (7, 9) = 7 := rfl

/-- `2 * halfDigit N ≤ N + 1` is the only arithmetic fact about the half-digit bound
that the carry elimination uses. -/
lemma two_mul_halfDigit_le (N : ℕ) : 2 * halfDigit N ≤ N + 1 :=
  Nat.mul_div_le _ _

/-- The half-digit bound never exceeds `N`, so a low digit below `halfDigit N` is a
legal base-`N` digit. -/
lemma halfDigit_le_self (N : ℕ) : halfDigit N ≤ N := by
  rw [halfDigit, Nat.div_le_iff_le_mul_add_pred (by norm_num : 0 < 2)]
  omega

/-! ## Exact carry elimination -/

/-- **Magnitude half of the carry elimination.**  If the three low digits `b₁, b₂, b₃`
are `< H` and `2 * H ≤ N + 1`, then the low residual `b₁ + b₃ - 2 * b₂` has absolute
value strictly less than `N`.  No positivity hypothesis on `N` is needed: for `N = 0`
the hypotheses `bᵢ < H = 0` are unsatisfiable, and the two linear inequalities are
still derivable from them. -/
lemma abs_lowResidual_lt {N H b₁ b₂ b₃ : ℕ} (hH : 2 * H ≤ N + 1)
    (h₁ : b₁ < H) (h₂ : b₂ < H) (h₃ : b₃ < H) :
    |((b₁ : ℤ) + (b₃ : ℤ) - 2 * (b₂ : ℤ))| < (N : ℤ) := by
  refine abs_lt.mpr ⟨?_, ?_⟩ <;> omega

/-- **Divisibility half of the carry elimination.**  From the scalar identity
`φ(p) + φ(r) = φ(q) + φ(q)` in `ℤ`, the low residual is divisible by `N`. -/
lemma dvd_lowResidual {N : ℕ} {p q r : ℕ × ℕ}
    (h : (p.1 : ℤ) + (N : ℤ) * (p.2 : ℤ) + ((r.1 : ℤ) + (N : ℤ) * (r.2 : ℤ)) =
      (q.1 : ℤ) + (N : ℤ) * (q.2 : ℤ) + ((q.1 : ℤ) + (N : ℤ) * (q.2 : ℤ))) :
    (N : ℤ) ∣ ((p.1 : ℤ) + (r.1 : ℤ) - 2 * (q.1 : ℤ)) := by
  have hsplit : ((p.1 : ℤ) + (r.1 : ℤ) - 2 * (q.1 : ℤ)) +
      (N : ℤ) * ((p.2 : ℤ) + (r.2 : ℤ) - 2 * (q.2 : ℤ)) = 0 := by linarith
  have hneg : ((p.1 : ℤ) + (r.1 : ℤ) - 2 * (q.1 : ℤ)) =
      -((N : ℤ) * ((p.2 : ℤ) + (r.2 : ℤ) - 2 * (q.2 : ℤ))) := by linarith
  rw [hneg]
  exact dvd_neg.mpr (dvd_mul_right _ _)

/-! ## Injectivity of the scalar pairing -/

/-- **Injectivity of `φ` on bounded low digits.**  If `p.1 < N` and `q.1 < N` then
`scalarPair N p = scalarPair N q` forces `p = q`; the high digits are unconstrained.
This is the same carry elimination as the main theorem, applied to the *difference*
`p - q` instead of to a three-term progression. -/
theorem scalarPair_injective_of_lt {N : ℕ} {p q : ℕ × ℕ} (hp : p.1 < N) (hq : q.1 < N)
    (h : scalarPair N p = scalarPair N q) : p = q := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact absurd hp (Nat.not_lt_zero _)
  · simp only [scalarPair] at h
    have hZ : (p.1 : ℤ) + (N : ℤ) * (p.2 : ℤ) = (q.1 : ℤ) + (N : ℤ) * (q.2 : ℤ) := by
      exact_mod_cast h
    have hsplit : ((p.1 : ℤ) - (q.1 : ℤ)) + (N : ℤ) * ((p.2 : ℤ) - (q.2 : ℤ)) = 0 := by
      linarith
    have habs : |((p.1 : ℤ) - (q.1 : ℤ))| < (N : ℤ) := by
      refine abs_lt.mpr ⟨?_, ?_⟩ <;> omega
    have hdiv : (N : ℤ) ∣ ((p.1 : ℤ) - (q.1 : ℤ)) := by
      have hneg : ((p.1 : ℤ) - (q.1 : ℤ)) = -((N : ℤ) * ((p.2 : ℤ) - (q.2 : ℤ))) := by
        linarith
      rw [hneg]
      exact dvd_neg.mpr (dvd_mul_right _ _)
    have hlow : ((p.1 : ℤ) - (q.1 : ℤ)) = 0 := Int.eq_zero_of_abs_lt_dvd hdiv habs
    have hhigh : (N : ℤ) * ((p.2 : ℤ) - (q.2 : ℤ)) = 0 := by linarith
    have h₁ : p.1 = q.1 := by omega
    have h₂ : p.2 = q.2 := by
      have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hN
      have hM : ((p.2 : ℤ) - (q.2 : ℤ)) = 0 := (mul_eq_zero.mp hhigh).resolve_left hN'
      omega
    exact Prod.ext h₁ h₂

/-! ## The arbitrary-relation endpoint -/

/-- **The half-digit scalar-cap obstruction for an arbitrary relation.**  Let `N` be any
natural, `H = halfDigit N`, and let `B ⊆ [0,H)`, `C ⊆ [0,N)` be ordinarily 3-AP-free
finite sets of naturals.  Then for *every* finite relation `G ⊆ B × C` the base-`N`
scalar image `G.image (scalarPair N)`, i.e. the set `{b + N*c : (b,c) ∈ G}`, is 3-AP-free
in `ℕ`.

The conclusion quantifies over an arbitrary `G`; nothing about `G` beyond containment in
`B × C` is assumed, and `G` may be any subrelation, not just the full product.  The bound
on `C` is used only to discharge the degenerate case `N = 0` (where it forces `C = ∅`);
the carry elimination itself needs only the half-digit bound on `B`. -/
theorem scalarPair_image_threeAPFree {N : ℕ} {B C : Finset ℕ}
    (hB : ∀ b ∈ B, b < halfDigit N) (hC : ∀ c ∈ C, c < N)
    (hBfree : ThreeAPFree (B : Set ℕ)) (hCfree : ThreeAPFree (C : Set ℕ))
    {G : Finset (ℕ × ℕ)} (hG : G ⊆ B.product C) :
    ThreeAPFree ((G.image (scalarPair N) : Finset ℕ) : Set ℕ) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · have hCempty : C = ∅ := by
      apply Finset.subset_empty.mp
      intro c hc
      have hc' := hC c hc
      simp [hN] at hc'
    have hGempty : G = ∅ := by
      apply Finset.subset_empty.mp
      intro p hp
      have hpC : p.2 ∈ C := (mem_product.mp (hG hp)).2
      rw [hCempty] at hpC
      exact absurd hpC (Finset.notMem_empty p.2)
    rw [hGempty, image_empty]
    simp
  · intro x hx y hy z hz hxyz
    obtain ⟨p, hpG, rfl⟩ := mem_image.mp hx
    obtain ⟨q, hqG, rfl⟩ := mem_image.mp hy
    obtain ⟨r, hrG, rfl⟩ := mem_image.mp hz
    have hpB : p.1 ∈ B := (mem_product.mp (hG hpG)).1
    have hpC : p.2 ∈ C := (mem_product.mp (hG hpG)).2
    have hqB : q.1 ∈ B := (mem_product.mp (hG hqG)).1
    have hqC : q.2 ∈ C := (mem_product.mp (hG hqG)).2
    have hrB : r.1 ∈ B := (mem_product.mp (hG hrG)).1
    have hrC : r.2 ∈ C := (mem_product.mp (hG hrG)).2
    have hZ : (p.1 : ℤ) + (N : ℤ) * (p.2 : ℤ) + ((r.1 : ℤ) + (N : ℤ) * (r.2 : ℤ)) =
        (q.1 : ℤ) + (N : ℤ) * (q.2 : ℤ) + ((q.1 : ℤ) + (N : ℤ) * (q.2 : ℤ)) := by
      simp only [scalarPair] at hxyz
      exact_mod_cast hxyz
    have hsplit : ((p.1 : ℤ) + (r.1 : ℤ) - 2 * (q.1 : ℤ)) +
        (N : ℤ) * ((p.2 : ℤ) + (r.2 : ℤ) - 2 * (q.2 : ℤ)) = 0 := by
      linarith
    have hlow : ((p.1 : ℤ) + (r.1 : ℤ) - 2 * (q.1 : ℤ)) = 0 :=
      Int.eq_zero_of_abs_lt_dvd (dvd_lowResidual hZ)
        (abs_lowResidual_lt (two_mul_halfDigit_le N) (hB p.1 hpB) (hB q.1 hqB) (hB r.1 hrB))
    have hhigh : ((p.2 : ℤ) + (r.2 : ℤ) - 2 * (q.2 : ℤ)) = 0 := by
      have hNM : (N : ℤ) * ((p.2 : ℤ) + (r.2 : ℤ) - 2 * (q.2 : ℤ)) = 0 := by linarith
      have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hN
      exact (mul_eq_zero.mp hNM).resolve_left hN'
    have h₁ : p.1 = q.1 := by
      refine hBfree hpB hqB hrB ?_
      omega
    have h₂ : p.2 = q.2 := by
      refine hCfree hpC hqC hrC ?_
      omega
    rw [Prod.ext h₁ h₂]

/-- Ground-truth check: the scalar image of the full relation `{0,1} × {0,1,3}` at
`N = 10` is the explicit six-element set of the low/high digit pairs. -/
example : (({0, 1} : Finset ℕ).product ({0, 1, 3} : Finset ℕ)).image (scalarPair 10) =
    {0, 1, 10, 11, 30, 31} := by decide

/-- Satisfiability: at `N = 10` the hypotheses of `scalarPair_image_threeAPFree` hold
jointly — `B = {0,1} ⊆ [0,5)`, `C = {0,1,3} ⊆ [0,10)`, both 3-AP-free — so the conclusion
is a genuine instance, not a vacuous one. -/
example : ThreeAPFree (((({0, 1} : Finset ℕ).product ({0, 1, 3} : Finset ℕ)).image
    (scalarPair 10) : Finset ℕ) : Set ℕ) :=
  scalarPair_image_threeAPFree (N := 10) (B := {0, 1}) (C := {0, 1, 3})
    (by decide) (by decide) (by decide) (by decide) subset_rfl

/-- Boundary check: the degenerate case `N = 0` of the main theorem is honest.
`halfDigit 0 = 0` forces `B = ∅`, `C = ∅`, hence `G = ∅`, and the conclusion is the
empty-set instance. -/
example : ThreeAPFree (((∅ : Finset (ℕ × ℕ)).image (scalarPair 0) : Finset ℕ) : Set ℕ) :=
  scalarPair_image_threeAPFree (N := 0) (B := ∅) (C := ∅) (by simp) (by simp) (by simp)
    (by simp) (by simp)

/-- Non-vacuity of the injectivity endpoint: at `N = 10` the pairing `φ` is injective on
the whole half-open box `{p : ℕ × ℕ | p.1 < 10}`. -/
example : Set.InjOn (scalarPair 10) {p : ℕ × ℕ | p.1 < 10} :=
  fun _ hp _ hq hpq => scalarPair_injective_of_lt hp hq hpq

/-! ## Cardinality of the scalar image -/

/-- **The scalar image is injective on a bounded relation.**  If `G ⊆ B × C` with every
low digit in `B` below `halfDigit N`, then `G.image (scalarPair N)` has the same
cardinality as `G`.  As in `scalarPair_injective_of_lt`, no bound on `C` is needed. -/
theorem card_image_scalarPair {N : ℕ} {B C : Finset ℕ}
    (hB : ∀ b ∈ B, b < halfDigit N) {G : Finset (ℕ × ℕ)} (hG : G ⊆ B.product C) :
    (G.image (scalarPair N)).card = G.card := by
  refine card_image_of_injOn fun p hp q hq hpq => ?_
  refine scalarPair_injective_of_lt ?_ ?_ hpq
  · exact (hB p.1 (mem_product.mp (hG hp)).1).trans_le (halfDigit_le_self N)
  · exact (hB q.1 (mem_product.mp (hG hq)).1).trans_le (halfDigit_le_self N)

/-- **Cardinality form for the full product.**  If every low digit in `B` is below
`H = halfDigit N` (no condition is imposed on `C`), the scalar image of the full
relation `B × C` has cardinality `B.card * C.card`. -/
theorem card_image_scalarPair_product {N : ℕ} {B C : Finset ℕ}
    (hB : ∀ b ∈ B, b < halfDigit N) :
    ((B.product C).image (scalarPair N)).card = B.card * C.card := by
  rw [card_image_scalarPair hB subset_rfl]
  exact card_product B C

/-- Non-vacuity of the cardinality endpoint at concrete data: the six-point scalar image
of `{0,1} × {0,1,3}` at `N = 10` has cardinality `2 * 3 = 6`. -/
example :
    ((({0, 1} : Finset ℕ).product ({0, 1, 3} : Finset ℕ)).image (scalarPair 10)).card = 6 :=
  card_image_scalarPair_product (N := 10) (B := {0, 1}) (C := {0, 1, 3}) (by decide)

/-! ## The witness form and the direct lower-product bound -/

/-- **Witness form of the half-digit scalar cap.**  For every `N` there is a 3-AP-free
`S ⊆ [0, N^2)` of cardinality `rothNumberNat ((N+1)/2) * rothNumberNat N`: take maximum
3-AP-free `B₀ ⊆ range (halfDigit N)` and `C₀ ⊆ range N` (Mathlib's `rothNumberNat_spec`)
and let `S` be the scalar image of the full relation `B₀ × C₀`.  Every point of `S` is
`b + N*c` with `b < N` and `c < N`, hence below `N^2`; no positivity hypothesis on `N`
is needed, and at `N = 0` both sides degenerate to the empty set. -/
theorem exists_threeAPFree_card_halfDigit_mul (N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ range (N ^ 2) ∧ ThreeAPFree (S : Set ℕ) ∧
      S.card = rothNumberNat (halfDigit N) * rothNumberNat N := by
  obtain ⟨B, hBsub, hBcard, hBfree⟩ := rothNumberNat_spec (halfDigit N)
  obtain ⟨C, hCsub, hCcard, hCfree⟩ := rothNumberNat_spec N
  have hBbound : ∀ b ∈ B, b < halfDigit N := fun b hb => mem_range.mp (hBsub hb)
  have hCbound : ∀ c ∈ C, c < N := fun c hc => mem_range.mp (hCsub hc)
  refine ⟨(B.product C).image (scalarPair N), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
    have hpB : p.1 ∈ B := (mem_product.mp hp).1
    have hpC : p.2 ∈ C := (mem_product.mp hp).2
    have hbN : p.1 < N := (hBbound p.1 hpB).trans_le (halfDigit_le_self N)
    have hcN : p.2 < N := hCbound p.2 hpC
    simp only [scalarPair, mem_range]
    calc p.1 + N * p.2 < N + N * p.2 := Nat.add_lt_add_right hbN _
      _ = N * (p.2 + 1) := by ring
      _ ≤ N * N := Nat.mul_le_mul_left N (by omega)
      _ = N ^ 2 := by rw [pow_two]
  · exact scalarPair_image_threeAPFree hBbound hCbound hBfree hCfree subset_rfl
  · rw [card_image_scalarPair_product hBbound, hBcard, hCcard]

/-- **The direct lower-product bound.**  For every `N` (with `N ^ 2 = N * N`),
`r₃ ((N+1)/2) * r₃ N ≤ r₃ (N ^ 2)`, obtained by feeding the witness set of
`exists_threeAPFree_card_halfDigit_mul` into `ThreeAPFree.le_rothNumberNat`.

The accepted module `Erdos.Erdos142.SquareScaleProduct` proves the same inequality by
the sharp scale-product route (`rothNumberNat_mul_rothNumberNat_half_le N N`); this is a
second, independent proof through the arbitrary-relation scalar-cap obstruction, named
differently to avoid a collision. -/
theorem rothNumberNat_halfDigit_mul_le_rothNumberNat_sq (N : ℕ) :
    rothNumberNat (halfDigit N) * rothNumberNat N ≤ rothNumberNat (N ^ 2) := by
  obtain ⟨S, hSsub, hSfree, hScard⟩ := exists_threeAPFree_card_halfDigit_mul N
  rw [← hScard]
  exact hSfree.le_rothNumberNat S (fun x hx => mem_range.mp (hSsub hx)) rfl

end Erdos142

