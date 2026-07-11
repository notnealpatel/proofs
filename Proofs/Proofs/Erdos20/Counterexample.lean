/-
  Erdős Problem #20 — machine-checked counterexample to Mishra v1 Lemma 3.

  NOTE ON NUMBERING: this file's "Lemma 3" label follows the tex \label tag,
  not the compiled auto-numbering — v1 displays the bridge τ(S(F)) ≤ 3·τ(F)²
  as Lemma 2.

  Mishra, "Erdős Rado Sunflower (Conjecture) Theorem"
  (arXiv:2606.02667v1, 2026-06-01; v1 title: "Erdős Rado Sunflower
  (Conjecture) Theorem", retitled in v2 to "Erdős Rado Sunflower Theorem
  for Shifted Families"), Lemma 3 claimed τ(S(F)) ≤ 3·τ(F)²
  for the full shift endpoint S(F) of any family F — the bridge that
  would have reduced the full Erdős–Rado conjecture to the shifted case.
  This file certifies a counterexample inside Lean, using the shift
  definitions of Sunflower.lean (franklShift, IsFullyCompressed,
  IsFullShiftOf, sunflowerNumber) and the τ-API of ShiftedSunflower.lean:

    `familyB` — 4-uniform on Fin 20, |F| = 17, τ(F) = 2 (found by
      computational search; certificate-verified by two independent
      programs before formalization) — whose full lex shift chain
      (all C_ij with i < j, 190 steps) ends at
    `starB` = {{0,1,2,x} : 3 ≤ x ≤ 19}, the full star on core {0,1,2},
      which is i<j-stable, with τ(S(F)) = 17.

  Since 3·τ² = 12 < 15 = 3·τ² + τ + 1 < 17, both the paper bound and its
  natural repair are false: the Frankl shift chain CREATES sunflowers,
  funneling a low-τ family into a star on the lex-smallest k-1 elements.
  Only empty-kernel sunflowers (matchings) are immune — they transport
  backward through chains (matchingNumber_reachable, Sunflower.lean) —
  so the creation is confined to nonempty kernels.

  Main results:
    shifting_creates_stars — ∃ F, S(F) with τ(F) = 2 and 15 < τ(S(F))
    mishra_v1_lemma3_false — no bound τ(S(F)) ≤ 3τ² + τ + 1 holds

  Method: a computable twin `franklShiftC` of `franklShift` (definitionally
  equal), the explicit 190-step lex shift chain as data, and `native_decide`
  for the ground certificate checks (no-3-sunflower scan over all C(17,3)
  triples, chain endpoint equality, i<j-stability of the star).

  Axiom audit (2026-06-10, `#print axioms` via `lake env lean`): both main
  theorems depend on exactly propext, Classical.choice, Quot.sound, and the
  per-use `native_decide` trust axioms (`*._native.native_decide.ax_*`,
  Lean ≥ 4.30's form of `Lean.ofReduceBool`). No `sorryAx`.
-/

import Proofs.Erdos20.Sunflower
import Proofs.Erdos20.ShiftedSunflower

open Finset

namespace Erdos20Counterexample

variable {n : ℕ}

/- Pin bounded-quantifier decidability to the Finset-traversal instances.
   Without this, instance search prefers `Fintype.decidableForallFintype`,
   which decides `∀ S ∈ sub, …` (sub : Finset (Finset (Fin 20))) by
   enumerating all 2^20 finsets — and the nested pairwise-intersection
   clause by enumerating (2^20)² pairs. Diagnosed via `#synth Decidable …`
   after a wedged build (100% CPU, 3.9GB RSS, 12+ min). -/
attribute [local instance 2000] Finset.decidableDforallFinset
  Finset.decidableExistsAndFinset

-- ════════════════════════════════════════════════════════════════════
-- §1 COMPUTABLE TWIN OF THE SHIFT OPERATOR
-- ════════════════════════════════════════════════════════════════════

/-- Computable twin of `franklShift` (the latter is marked `noncomputable`;
    the body is identical and fully decidable on `Fin n`). -/
def franklShiftC (i j : Fin n) (family : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  family.image fun S =>
    let S' := franklShiftSet i j S
    if S' ∈ family then S else S'

theorem franklShiftC_eq (i j : Fin n) (family : Finset (Finset (Fin n))) :
    franklShiftC i j family = franklShift i j family := rfl

/-- `IsSunflowerWith` is decidable (bounded quantifiers over finsets). -/
instance (sub : Finset (Finset (Fin n))) (K : Finset (Fin n)) :
    Decidable (IsSunflowerWith sub K) :=
  decidable_of_iff
    ((∀ S ∈ sub, K ⊆ S) ∧ (∀ S ∈ sub, S \ K ≠ ∅) ∧
      (∀ S ∈ sub, ∀ T ∈ sub, S ≠ T → S ∩ T = K))
    Iff.rfl

-- ════════════════════════════════════════════════════════════════════
-- §2 THE WITNESS FAMILY (witness (b): k=4, n=20, |F|=17, 0-indexed)
-- ════════════════════════════════════════════════════════════════════

abbrev V : Type := Fin 20

/-- Witness (b), 0-indexed: 4-uniform, 17 members, τ = 2. -/
def familyB : Finset (Finset V) :=
  { {0,1,2,15}, {0,1,3,15}, {0,1,4,5}, {0,4,14,16}, {0,4,14,18},
    {0,8,9,15}, {0,8,10,15}, {1,2,3,4}, {1,2,3,7}, {1,4,5,8},
    {1,5,6,12}, {2,9,11,12}, {2,3,12,13}, {2,3,6,12}, {3,11,12,17},
    {3,11,14,15}, {4,14,15,19} }

/-- The full star on core {0,1,2}: all 17 sets {0,1,2,x}, x ∈ {3,…,19}. -/
def starB : Finset (Finset V) :=
  { {0,1,2,3}, {0,1,2,4}, {0,1,2,5}, {0,1,2,6}, {0,1,2,7},
    {0,1,2,8}, {0,1,2,9}, {0,1,2,10}, {0,1,2,11}, {0,1,2,12},
    {0,1,2,13}, {0,1,2,14}, {0,1,2,15}, {0,1,2,16}, {0,1,2,17},
    {0,1,2,18}, {0,1,2,19} }

-- ════════════════════════════════════════════════════════════════════
-- §3 THE SHIFT CHAIN (one full lex sweep of C_ij, i < j)
-- ════════════════════════════════════════════════════════════════════

/-- All pairs (i, j) with i < j in lexicographic order — the order used by
    the certified Go verifier (i ascending outer, j ascending inner). -/
def sweep : List (V × V) :=
  (List.finRange 20).flatMap fun i =>
    ((List.finRange 20).filter fun j => decide (i < j)).map fun j => (i, j)

/-- Apply a list of shifts left-to-right. -/
def applyChain : List (V × V) → Finset (Finset V) → Finset (Finset V)
  | [], F => F
  | p :: rest, F => applyChain rest (franklShiftC p.1 p.2 F)

/-- Every chain of computable shifts is a `ReachableByShifts` witness. -/
def reachable_applyChain (L : List (V × V)) (F : Finset (Finset V)) :
    ReachableByShifts F (applyChain L F) := by
  induction L generalizing F with
  | nil => exact .refl F
  | cons p rest ih =>
    exact .step p.1 p.2 (franklShiftC_eq p.1 p.2 F).symm (ih (franklShiftC p.1 p.2 F))

/-- One lex sweep sends witness (b) to the full star. -/
theorem chain_endpoint : applyChain sweep familyB = starB := by
  native_decide

/-- The chain as a `ReachableByShifts` certificate. -/
def familyB_reaches_starB : ReachableByShifts familyB starB :=
  chain_endpoint ▸ reachable_applyChain sweep familyB

/-- The star is i<j-fully-compressed (every shift fixes it). -/
theorem starB_compressed : IsFullyCompressed starB := by
  have h : ∀ i j : V, i < j → franklShiftC i j starB = starB := by native_decide
  intro i j hij
  rw [← franklShiftC_eq]
  exact h i j hij

-- ════════════════════════════════════════════════════════════════════
-- §4 SUNFLOWER NUMBERS OF THE TWO FAMILIES
-- ════════════════════════════════════════════════════════════════════

/-- Exhaustive scan over all C(17,3) = 680 triples: no 3-sunflower in F.
    `HasSunflower` existentially quantifies over the (astronomically large)
    type of subfamilies, so it is not directly decidable; but any 3-sunflower
    ⟨sub, K⟩ yields a bounded witness with `sub ∈ powersetCard 3 familyB` and
    `K ∈ S₀.powerset` for any `S₀ ∈ sub` (kernels sit inside every member),
    and the bounded form is refuted by `native_decide`. -/
theorem familyB_no_3sunflower : ¬ HasSunflower familyB 3 := by
  rintro ⟨sub, hsub, hcard, K, hsf⟩
  have hne : sub.Nonempty := by
    rw [← Finset.card_pos, hcard]; norm_num
  obtain ⟨S₀, hS₀⟩ := hne
  have hwitness : ∃ sub ∈ Finset.powersetCard 3 familyB, ∃ S₀ ∈ sub,
      ∃ K ∈ S₀.powerset, IsSunflowerWith sub K :=
    ⟨sub, Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩, S₀, hS₀, K,
      Finset.mem_powerset.mpr (hsf.1 S₀ hS₀), hsf⟩
  exact absurd hwitness (by native_decide)

/-- A 2-sunflower in F: {0,1,2,15} and {0,1,3,15} with kernel {0,1,15}. -/
theorem familyB_hasSunflower_2 : HasSunflower familyB 2 :=
  ⟨{ {0,1,2,15}, {0,1,3,15} }, by native_decide, by native_decide,
    {0,1,15}, by native_decide⟩

theorem starB_card : starB.card = 17 := by native_decide

/-- The star itself is a 17-sunflower with kernel {0,1,2}. -/
theorem starB_hasSunflower_17 : HasSunflower starB 17 :=
  ⟨starB, Finset.Subset.refl _, starB_card, {0,1,2}, by native_decide⟩

/-- τ(F) = 2: a 2-sunflower exists, and any k-sunflower with k ≥ 3 would
    restrict to the 3-sunflower excluded by the exhaustive scan. -/
theorem familyB_tau : sunflowerNumber familyB = 2 := by
  apply le_antisymm
  · apply sunflowerNumber_le_of_forall
    intro k hk
    by_contra hgt
    push Not at hgt
    exact familyB_no_3sunflower (hk.mono (by omega))
  · exact le_sunflowerNumber familyB familyB_hasSunflower_2

/-- τ(S(F)) = 17: the star is a 17-sunflower, and τ ≤ |S(F)| = 17. -/
theorem starB_tau : sunflowerNumber starB = 17 :=
  le_antisymm (starB_card ▸ sunflowerNumber_le_card starB)
    (le_sunflowerNumber starB starB_hasSunflower_17)

-- ════════════════════════════════════════════════════════════════════
-- §5 MAIN THEOREMS
-- ════════════════════════════════════════════════════════════════════

/-- The Frankl shift chain creates stars: a family with τ = 2 whose full
    shift endpoint has τ = 17 > 15 = 3τ² + τ + 1 > 12 = 3τ². -/
theorem shifting_creates_stars :
    ∃ (family shifted : Finset (Finset (Fin 20))),
      Nonempty (IsFullShiftOf shifted family) ∧
      sunflowerNumber family = 2 ∧
      15 < sunflowerNumber shifted :=
  ⟨familyB, starB,
   ⟨⟨starB_compressed, familyB_reaches_starB⟩⟩,
   familyB_tau,
   by rw [starB_tau]; norm_num⟩

/-- Mishra v1 Lemma 3 is false, even in the repaired form
    τ(S(F)) ≤ 3·τ(F)² + τ(F) + 1 (and a fortiori in the paper form 3τ²). -/
theorem mishra_v1_lemma3_false :
    ¬ ∀ (family shifted : Finset (Finset (Fin 20))),
        Nonempty (IsFullShiftOf shifted family) →
        sunflowerNumber shifted ≤
          3 * sunflowerNumber family ^ 2 + sunflowerNumber family + 1 := by
  intro h
  have hb := h familyB starB ⟨⟨starB_compressed, familyB_reaches_starB⟩⟩
  rw [familyB_tau, starB_tau] at hb
  norm_num at hb

end Erdos20Counterexample
