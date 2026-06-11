/-
  Ground certificate for SpreadDefect.lean §4 (Track B, B2.G3 — REFUTED).
  native_decide ground checks (trusted-compiler axioms) — experiments
  only, NOT part of the theory file.

  The G3 refutation (`spread_defect_unbounded`) is an abstract std-3
  theorem; its witnesses `productFamily b k` are astronomically large at
  the killing scale (k = 2(gb+1)²). This file certifies the SMALLEST
  instance end-to-end, P = productFamily 4 2 (16 transversals of two
  4-blocks on Fin 8), tying every abstract claim to a concrete
  computation, and — crucially — ties the theory file's IsFullShiftOf
  endpoint convention to B1's measurement convention: ONE canonical lex
  sweep of P is already fully compressed, so the single-sweep S(F) of
  the B1 report and the compressed endpoint of the theorems coincide on
  the witness class (checked here at k = 2; the Go probe confirmed the
  same at b=4, k ≤ 4 and b=5, k ≤ 3).

  Certified ground facts (P := productFamily 4 2, E := lex-sweep
  endpoint of P):
    · P = explicit 16-member literal (calibration against the Go probe)
    · IsRSpread 4 P re-checked by evaluation; ¬IsRSpread (9/2) P
      (r* = 4 exactly, matching productFamily_isRSpread /
       productFamily_not_isRSpread)
    · τ(P) = 4 — by the abstract theorem (no native_decide), plus a
      ground re-check of HasSunflower P 4
    · E is fully compressed; IsFullShiftOf E P (chain certificate)
    · τ(E) = 7: the star {0,x} (x = 1..7) up, exhaustive
      C(16,8)-scan down — ratio 7/4 at k = 2, tame at small k exactly
      as B1 measured; the theorems make it diverge along k.

  Axiom audit tail: every §4 theory theorem must report std-3 (subsets
  allowed); the ground examples here carry native_decide trust axioms
  by design (same trust model as Counterexample.lean).
-/
import Proofs.Erdos20.SpreadDefect
import Proofs.Erdos20.Counterexample

open Finset

namespace SpreadDefectWitness

open Erdos20Counterexample (franklShiftC franklShiftC_eq)

-- Pin the same decidability instances as Counterexample.lean.
attribute [local instance 2000] Finset.decidableDforallFinset
  Finset.decidableExistsAndFinset

-- ── The witness instance: two blocks of size four on Fin 8 ──────────

/-- `P = productFamily 4 2`: the 16 transversals of blocks {0,1,2,3}
    and {4,5,6,7}. -/
abbrev P : Finset (Finset (Fin 8)) := productFamily 4 2

/-- Calibration: the abstract definition evaluates to the expected
    literal (one vertex per block). -/
example : P =
    { {0,4}, {0,5}, {0,6}, {0,7}, {1,4}, {1,5}, {1,6}, {1,7},
      {2,4}, {2,5}, {2,6}, {2,7}, {3,4}, {3,5}, {3,6}, {3,7} } := by
  native_decide

-- ── Spread radius pinned at r* = 4, ground re-check ─────────────────

/-- Ground re-check of `productFamily_isRSpread` at (b,k) = (4,2). -/
example : IsRSpread 4 P := by
  unfold IsRSpread
  native_decide

/-- Ground re-check that no r > 4 works — probed strictly inside
    (4,5): `productFamily_not_isRSpread` gives every r > 4
    abstractly. -/
example : ¬ IsRSpread (9/2 : ℚ) P := by
  unfold IsRSpread
  native_decide

-- ── τ(P) = 4, abstract and ground ────────────────────────────────────

/-- τ(P) = 4 from the THEORY file (std-3, no native_decide): the
    k-independent τ of the product family. -/
example : sunflowerNumber P = 4 :=
  productFamily_sunflowerNumber 4 2 (by omega)

/-- Ground re-check of the 4-matching (the four constant transversals,
    kernel ∅). -/
example : HasSunflower P 4 :=
  ⟨{ {0,4}, {1,5}, {2,6}, {3,7} }, by native_decide, by native_decide,
    ∅, by native_decide⟩

-- ── The canonical lex sweep of P is already fully compressed ─────────

/-- All pairs (i, j) with i < j in lexicographic order on Fin 8 — the
    `sweep`/`applyChain` convention of Counterexample.lean and of the
    B1 measurement program. -/
def sweep8 : List (Fin 8 × Fin 8) :=
  (List.finRange 8).flatMap fun i =>
    ((List.finRange 8).filter fun j => decide (i < j)).map fun j => (i, j)

/-- Apply a list of shifts left-to-right. -/
def applyChain : List (Fin 8 × Fin 8) → Finset (Finset (Fin 8)) → Finset (Finset (Fin 8))
  | [], F => F
  | p :: rest, F => applyChain rest (franklShiftC p.1 p.2 F)

/-- Every chain of computable shifts is a `ReachableByShifts` witness. -/
def reachable_applyChain (L : List (Fin 8 × Fin 8)) (F : Finset (Finset (Fin 8))) :
    ReachableByShifts F (applyChain L F) := by
  induction L generalizing F with
  | nil => exact .refl F
  | cons p rest ih =>
    exact .step p.1 p.2 (franklShiftC_eq p.1 p.2 F).symm (ih (franklShiftC p.1 p.2 F))

/-- `E`: the single-lex-sweep endpoint of `P` — B1's S(F). -/
def E : Finset (Finset (Fin 8)) := applyChain sweep8 P

/-- The computed endpoint, explicitly: the colex-initial segment of
    pairs (matches the independent Go probe). -/
example : E =
    { {0,1}, {0,2}, {1,2}, {0,3}, {1,3}, {2,3}, {0,4}, {1,4}, {2,4},
      {3,4}, {0,5}, {1,5}, {2,5}, {0,6}, {1,6}, {0,7} } := by
  native_decide

/-- ONE sweep already lands on a fully compressed family: B1's
    single-sweep S(F) and the theory file's IsFullShiftOf endpoint
    coincide on the witness. -/
theorem E_compressed : IsFullyCompressed E := by
  have h : ∀ i j : Fin 8, i < j → franklShiftC i j E = E := by native_decide
  intro i j hij
  rw [← franklShiftC_eq]
  exact h i j hij

/-- The full-shift certificate `IsFullShiftOf E P`. -/
def E_isFullShiftOf : IsFullShiftOf E P :=
  ⟨E_compressed, reachable_applyChain sweep8 P⟩

-- ── τ(E) = 7: the star at 0, and nothing larger ──────────────────────

/-- The 7-sunflower in `E`: the full star {0,x}, x = 1..7, kernel {0}. -/
theorem E_hasSunflower_7 : HasSunflower E 7 :=
  ⟨{ {0,1}, {0,2}, {0,3}, {0,4}, {0,5}, {0,6}, {0,7} },
    by native_decide, by native_decide, {0}, by native_decide⟩

/-- Exhaustive scan: no 8-sunflower in `E` (bounded witness over
    `powersetCard 8` with kernels inside a member, as in
    `familyB_no_3sunflower`). -/
theorem E_no_8sunflower : ¬ HasSunflower E 8 := by
  rintro ⟨sub, hsub, hcard, K, hsf⟩
  have hne : sub.Nonempty := by
    rw [← Finset.card_pos, hcard]; norm_num
  obtain ⟨S₀, hS₀⟩ := hne
  have hwitness : ∃ sub ∈ Finset.powersetCard 8 E, ∃ S₀ ∈ sub,
      ∃ K ∈ S₀.powerset, IsSunflowerWith sub K :=
    ⟨sub, Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩, S₀, hS₀, K,
      Finset.mem_powerset.mpr (hsf.1 S₀ hS₀), hsf⟩
  exact absurd hwitness (by native_decide)

/-- τ(E) = 7: the single sweep already inflates 4 → 7 (ratio 1.75) at
    k = 2 — tame at small k exactly as the B1 table shows; the theory
    file's `spread_defect_unbounded` is the statement that this ratio
    is unbounded along k at pinned r* = 4. -/
theorem E_tau : sunflowerNumber E = 7 := by
  apply le_antisymm
  · apply sunflowerNumber_le_of_forall
    intro m hm
    by_contra hgt
    push Not at hgt
    exact E_no_8sunflower (hm.mono (by omega))
  · exact le_sunflowerNumber E E_hasSunflower_7

/-- The packaged small-k data point: r* = 4 (both directions), τ 4 → 7
    under the canonical sweep, endpoint compressed. -/
example :
    IsRSpread 4 P ∧ ¬ IsRSpread (9/2 : ℚ) P ∧
    sunflowerNumber P = 4 ∧ sunflowerNumber E = 7 ∧
    Nonempty (IsFullShiftOf E P) :=
  ⟨by unfold IsRSpread; native_decide,
   by unfold IsRSpread; native_decide,
   productFamily_sunflowerNumber 4 2 (by omega),
   E_tau,
   ⟨E_isFullShiftOf⟩⟩

-- ── Axiom audit: every §4 theory declaration must be std-3 ──────────

#print axioms block_slot_inj
#print axioms productVertex_eq_iff
#print axioms mem_productSet
#print axioms productSet_card
#print axioms productSet_injective
#print axioms mem_productFamily
#print axioms productFamily_card
#print axioms productFamily_uniform
#print axioms productFamily_nonempty
#print axioms productFamily_isRSpread
#print axioms productFamily_not_isRSpread
#print axioms productFamily_sunflowerNumber_le
#print axioms productFamily_hasSunflower
#print axioms productFamily_sunflowerNumber
#print axioms pow_two_mul_pred_lt_two_pow
#print axioms IsFullShiftOf.hasSunflower_of_isRSpread
#print axioms spread_defect_unbounded
#print axioms spread_defect_bridge_false

end SpreadDefectWitness
