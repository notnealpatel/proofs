/-
  Scratch non-vacuity certificate for SpreadLemma.lean (Sp1 campaign,
  Sp5 acceptance gate). NOT imported by the root module — build with
  the explicit target `lake build Scratch.SpreadLemmaSanity`.

  WHAT IS CERTIFIED (option (b) of the Sp5 card): the hypotheses of the
  committed headlines are SIMULTANEOUSLY SATISFIABLE on a concrete
  family, so none of `spread_lemma_core` / `spread_lemma` /
  `sunflower_of_large_family` is vacuously true, and the consumer
  interface composes end-to-end on an instance.

  Instance (s = 1, k = 1, the card's prescription): the product family
  `productFamily (C+1) 1` of SpreadDefect.lean §4 — all C+1 singletons
  of one block on Fin (C+1) — at r := C, where C = 884736 is the
  headline constant:
    · 1-uniform                          productFamily_uniform
    · IsRSpread C: exactly (C+1)-spread  productFamily_isRSpread
      stepped down to C                  via IsRSpread.mono
    · hr:  C·1·(log₂ 1 + 1) = C ≤ C      Nat.log_one_right
    · threshold:  C^1 = C < C+1 = |F|    productFamily_card
  A second instance at s = 2 (b := 2C+1, r := 2C, same shape) certifies
  the petal-count content as well: the delivered 2-sunflower is a pair
  of disjoint members, so the conclusion is not degenerate either.

  Everything here is symbolic — no `decide`, no `native_decide`, no
  enumeration of the 884737-member family; all cardinality and spread
  facts come from the std-3 `productFamily` lemmas, so the certificate
  itself is std-3 ([propext, Classical.choice, Quot.sound]).
-/
import Erdos.Erdos20.SpreadLemma

open Finset SpreadLemma

namespace SpreadLemmaSanity

/-- The s = 1 witness: all 884737 singletons of one block of size
    `C + 1 = 884737` (so `|F| = 884737`, 1-uniform, exactly
    884737-spread). -/
abbrev familyW : Finset (Finset (Fin (884737 * 1))) := productFamily 884737 1

-- ── the four headline hypotheses, individually inhabited at r = C ──

theorem familyW_uniform : ∀ S ∈ familyW, S.card = 1 :=
  productFamily_uniform 884737 1

theorem familyW_spread : IsRSpread (884736 : ℚ) familyW :=
  (productFamily_isRSpread 884737 1).mono (by norm_num) (by norm_num)

theorem familyW_hr :
    ((884736 * 1 * (Nat.log 2 1 + 1) : ℕ) : ℚ) ≤ (884736 : ℚ) := by
  norm_num [Nat.log_one_right]

theorem familyW_threshold : (884736 : ℚ) ^ 1 < (familyW.card : ℚ) := by
  rw [productFamily_card]
  norm_num

-- ── the certificates: each headline fires on the instance ──

/-- `spread_lemma_core`'s hypotheses are non-contradictory at
    s = 1, k = 1, r = C: the lemma delivers its conclusion. -/
theorem core_nonvacuous : HasSunflower familyW 1 :=
  spread_lemma_core le_rfl le_rfl familyW_hr familyW_uniform
    familyW_spread familyW_threshold

/-- The task-shape headline `spread_lemma` composes on the same
    instance (same hypotheses, permuted interface). -/
theorem spread_lemma_nonvacuous : HasSunflower familyW 1 :=
  spread_lemma familyW_hr familyW_uniform le_rfl le_rfl
    familyW_spread familyW_threshold

/-- The unconditional headline `sunflower_of_large_family` fires on
    the same instance: `|F| = C+1 > C^1 = (C·1·(log₂ 1 + 1))^1`. -/
theorem headline_nonvacuous : HasSunflower familyW 1 :=
  sunflower_of_large_family le_rfl familyW_uniform
    (by rw [productFamily_card]; norm_num [Nat.log_one_right])

-- ── s = 2: the petal count is not degenerate either ──

/-- The s = 2 witness: 2C+1 = 1769473 singletons, exactly
    1769473-spread, instantiated at r = 2C = 1769472. The delivered
    2-sunflower is a genuine disjoint pair. -/
abbrev familyW₂ : Finset (Finset (Fin (1769473 * 1))) := productFamily 1769473 1

theorem core_nonvacuous_two_petals : HasSunflower familyW₂ 2 :=
  spread_lemma_core (s := 2) (r := (1769472 : ℚ)) one_le_two le_rfl
    (by norm_num [Nat.log_one_right])
    (productFamily_uniform 1769473 1)
    ((productFamily_isRSpread 1769473 1).mono (by norm_num) (by norm_num))
    (by rw [productFamily_card]; norm_num)

/-- The unconditional headline at s = 2 on the same witness. -/
theorem headline_nonvacuous_two_petals : HasSunflower familyW₂ 2 :=
  sunflower_of_large_family one_le_two (productFamily_uniform 1769473 1)
    (by rw [productFamily_card]; norm_num [Nat.log_one_right])

end SpreadLemmaSanity
