/-
  Erdős Problem #20 — the shadow ladder: iterating the single-step
  shadow bound of ShiftedSunflower.lean down the shadow tower.

  Single step (v2 Lemma 4, `card_mul_le_sunflowerNumber_mul_shadow`):
      |F| · k ≤ |∂F| · τ(F)        for k-uniform F.

  Iterating k times and discharging the final 0-uniform shadow
  (|∂^[k] F| ≤ 1) yields the ladder

      |F| · k! ≤ ∏_{i < k} τ(∂^[i] F).

  NOVELTY POSTURE (per C7 §S2 / SYNTHESIS_PLAN.md §2 item 4): the
  single-step bound is a folklore double-counting mechanism; its explicit
  statement is traceable to Mishra v2 Lemma 4 (arXiv:2606.02667v2) and
  this repo's formalization. The iterated ladder was not found stated in
  the literature, but it is NOT a reformulation of the sunflower
  conjecture — the "ladder ≡ conjecture" framing is REFUTED
  (SYNTHESIS_PLAN.md §2 item 4); the inequality itself is true and is
  what is proved here.
-/

import Proofs.Erdos20.ShiftedSunflower

open Finset FinsetFamily

variable {n : ℕ}

/-- The shadow ladder: for a `k`-uniform family `F`,
    `|F| · k! ≤ ∏_{i < k} τ(∂^[i] F)`, by iterating the single-step
    shadow bound `card_mul_le_sunflowerNumber_mul_shadow`
    (`|F| · k ≤ |∂F| · τ(F)`) down the shadow tower; the `0`-uniform
    floor `∂^[k] F ⊆ {∅}` absorbs the leftover cardinality factor. -/
theorem shadow_ladder (k : ℕ) {F : Finset (Finset (Fin n))}
    (hunif : ∀ S ∈ F, S.card = k) :
    F.card * Nat.factorial k ≤
      ∏ i ∈ Finset.range k, sunflowerNumber (Finset.shadow^[i] F) := by
  induction k generalizing F with
  | zero =>
    have hsub : F ⊆ {∅} := fun S hS =>
      Finset.mem_singleton.mpr (Finset.card_eq_zero.mp (hunif S hS))
    simpa using Finset.card_le_card hsub
  | succ k ih =>
    have hshadow_unif : ∀ S ∈ ∂ F, S.card = k := by
      intro S hS
      have hsized : (F : Set (Finset (Fin n))).Sized (k + 1) :=
        fun T hT => hunif T hT
      simpa using hsized.shadow hS
    calc F.card * Nat.factorial (k + 1)
        = F.card * (k + 1) * Nat.factorial k := by
          rw [Nat.factorial_succ, ← mul_assoc]
      _ ≤ (∂ F).card * sunflowerNumber F * Nat.factorial k :=
          Nat.mul_le_mul_right _
            (card_mul_le_sunflowerNumber_mul_shadow (k + 1) F hunif)
      _ = (∂ F).card * Nat.factorial k * sunflowerNumber F := by ring
      _ ≤ (∏ i ∈ Finset.range k, sunflowerNumber (Finset.shadow^[i] (∂ F))) *
            sunflowerNumber F :=
          Nat.mul_le_mul_right _ (ih hshadow_unif)
      _ = ∏ i ∈ Finset.range (k + 1), sunflowerNumber (Finset.shadow^[i] F) := by
          rw [Finset.prod_range_succ']
          simp
