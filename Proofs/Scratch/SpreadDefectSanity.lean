/-
  Scratch sanity probes for SpreadDefect.lean (Track B, B2.G1/G2).
  native_decide ground checks (trusted-compiler axioms) — experiments
  only, NOT part of the theory file.

  Probe 1 (satisfiability of G1's hypothesis, guarded form):
    F = {{0,1}} on Fin 3, k = 2, r = 2 — every Z with |Z| < 2 whose
    link is nonempty has a non-2-spread link.

  Probe 2 (the nonempty-link guard is load-bearing): Z = {2} has an
    EMPTY link, and the empty family IS vacuously 2-spread under
    IsRSpread; the unguarded quantification ∀ Z, |Z| < k → ¬spread
    would be FALSE for this family.

  Probe 3 (the |Z| < k bound is load-bearing, dispatch warning): at
    the member Z = {0,1} ∈ F the link is {∅}, which is vacuously
    r-spread for ANY r (probed at r = 100); quantifying the hypothesis
    over |Z| ≤ k would make it unsatisfiable for nonempty F.
  Tail section: #print axioms audit of every public SpreadDefect
  theorem — each must report exactly
  [propext, Classical.choice, Quot.sound] (std-3).
-/
import Proofs.Erdos20.SpreadDefect

open Finset

namespace SpreadDefectSanity

-- Pin the same decidability instances as Counterexample.lean.
attribute [local instance 2000] Finset.decidableDforallFinset
  Finset.decidableExistsAndFinset

/-- The probe family: a single pair on a ground set with a spare vertex. -/
abbrev familyP : Finset (Finset (Fin 3)) := {{0, 1}}

-- Probe 1: the guarded anti-spread hypothesis of G1 is SATISFIABLE.
example : ∀ Z : Finset (Fin 3), Z.card < 2 → (linkAt Z familyP).Nonempty →
    ¬ IsRSpread 2 (linkAt Z familyP) := by
  unfold IsRSpread
  native_decide

-- Probe 2a: the link at the uncovered vertex is empty.
example : linkAt {2} familyP = ∅ := by native_decide

-- Probe 2b: the empty link is vacuously 2-spread (guard load-bearing).
example : IsRSpread 2 (linkAt {2} familyP) := by
  unfold IsRSpread
  native_decide

-- Probe 2c: hence the UNGUARDED hypothesis fails for this family.
example : ¬ (∀ Z : Finset (Fin 3), Z.card < 2 → ¬ IsRSpread 2 (linkAt Z familyP)) := by
  unfold IsRSpread
  native_decide

-- Probe 3a: the link at a member is {∅}.
example : linkAt {0, 1} familyP = {∅} := by native_decide

-- Probe 3b: {∅} is vacuously r-spread even at r = 100 (|Z| < k load-bearing).
example : IsRSpread 100 (linkAt {0, 1} familyP) := by
  unfold IsRSpread
  native_decide

-- Probe 4: G1's conclusion |F| ≤ r^k is honest here: 1 ≤ 2^2.
example : ((familyP.card : ℚ)) ≤ 2 ^ 2 := by native_decide

-- ── Axiom audit: every public SpreadDefect theorem must be std-3 ──
#print axioms linkAt_empty
#print axioms linkAt_nonempty_iff
#print axioms linkAt_singleton_family
#print axioms not_isRSpread_singleton
#print axioms card_le_pow_of_forall_linkAt_not_isRSpread
#print axioms forall_linkAt_not_isRSpread_pair
#print axioms exists_isRSpread_linkAt_loop
#print axioms hasSunflower_of_forall_linkAt_isRSpread
#print axioms hasSunflower_of_forall_isRSpread_via_loop

end SpreadDefectSanity
