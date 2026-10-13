/-
  Erdős Problem #273 — covering systems with moduli of the form p − 1.
  Status: open.  Tier UA attack target (certificate slice on the repo's
  Covering layer).

  Verbatim statement (`goof erdos fetch 273`, pulled 2026-08-05):

    "Is there a covering system all of whose moduli are of the form
    $p-1$ for some primes $p\geq 5$?"

  DB remarks: Selfridge found an example using divisors of 360 if p = 3
  is allowed (i.e. modulus 2 allowed).  Comment (ideal_ombrer, Jul 2026,
  comment-sourced, unrefereed): any p ≥ 5 covering needs a modulus with
  p > 877 (BBMST distortion sieve applied to the 149 moduli with
  p ≤ 877), and ∑ 1/(p−1) ≥ 1 + exp(−3.36·10²¹) via Filaseta–Kalogirou.

  Repo adjacency: `Proofs/Erdos/Covering/Basic.lean` provides
  `Erdos.Covering.Covers`, `IsCoveringSystem` (Finset (ℕ × ℕ) of
  (residue, modulus) pairs, distinct moduli > 1) and the decidable
  characterization `covers_iff_forall_range` — the exact machinery for
  the Selfridge certificate.

  Mathlib inventory: finite cardinality bounds, rational arithmetic, `Nat.Prime`.
-/
import Mathlib
import Erdos.Covering.Basic

set_option autoImplicit false

namespace ErdosCandidates.E273

open Erdos.Covering

/-- `ModuliOfPrimeMinusOne P S`: every modulus of the system `S` is
    `p − 1` for some prime `p` with `P ≤ p`.  (`p − 1` is safe: `p ≥ 5`
    keeps ℕ-subtraction honest.) -/
def ModuliOfPrimeMinusOne (P : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ q ∈ S, ∃ p : ℕ, p.Prime ∧ P ≤ p ∧ q.2 = p - 1

/-- **Erdős #273 (OPEN)**: does a covering system exist with all moduli
    of the form `p − 1`, `p ≥ 5` prime?  Archived as the open boundary;
    the DB and comments suggest yes-but-hard (any example needs a
    modulus with `p > 877`).  Stated as the existence claim so that a
    future certificate closes it. -/
theorem erdos_273 :
    ∃ S : Finset (ℕ × ℕ), IsCoveringSystem S ∧ ModuliOfPrimeMinusOne 5 S := by
  sorry

/-- A computed residue table using Selfridge's modulus pool. The exact residues
    are a new certificate, not a transcription of Selfridge's historical table. -/
def selfridgeSystem : Finset (ℕ × ℕ) :=
  {(0, 2), (1, 4), (3, 6), (9, 10), (7, 12), (11, 18),
    (17, 30), (23, 36), (11, 40), (23, 60), (71, 72), (35, 180)}

example : selfridgeSystem.card = 12 := by decide
example : ((35, 180) : ℕ × ℕ) ∈ selfridgeSystem := by decide
example : selfridgeSystem.image Prod.snd = {2, 4, 6, 10, 12, 18, 30, 36, 40, 60, 72, 180} := by
  decide

set_option maxRecDepth 4096 in
/-- The computed table covers every integer with distinct moduli exceeding one,
    checked on all 360 residues by ordinary kernel reduction. -/
theorem isCoveringSystem_selfridgeSystem : IsCoveringSystem selfridgeSystem := by
  apply (isCoveringSystem_iff 360 (by decide) (by decide)).mpr
  decide

/-- Each modulus in the computed table is one less than a prime at least three. -/
theorem moduliOfPrimeMinusOne_selfridgeSystem : ModuliOfPrimeMinusOne 3 selfridgeSystem := by
  intro q hq
  refine ⟨q.2 + 1, ?_, ?_, ?_⟩
  all_goals
    simp only [selfridgeSystem, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num

/-- Allowing the prime `3` (modulus `2`), there is a covering system whose
    moduli are all one less than primes. The witness is a newly computed table
    using Selfridge's modulus pool, rather than a historical residue-table claim. -/
theorem selfridge_p3_certificate :
    ∃ S : Finset (ℕ × ℕ), IsCoveringSystem S ∧ ModuliOfPrimeMinusOne 3 S := by
  exact ⟨selfridgeSystem, isCoveringSystem_selfridgeSystem,
    moduliOfPrimeMinusOne_selfridgeSystem⟩

/-- Sanity: the modulus pool below the 877-threshold is as claimed —
    `2, 4, 6, 10, 12` are all `p − 1` for primes `3, 5, 7, 11, 13`, and
    `8` is not of the form `p − 1` for `p` prime (9 is not prime).
    Guards the `ModuliOfPrimeMinusOne` def against off-by-one. -/
theorem prime_minus_one_sanity : (∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ 12 = p - 1) ∧
    ¬(∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ 8 = p - 1) := by
  constructor
  · exact ⟨13, by decide, by decide, by decide⟩
  · rintro ⟨p, hp, hge, heq⟩
    have hp9 : p = 9 := by omega
    subst p
    exact (by decide : ¬ Nat.Prime 9) hp

/-- A residue class modulo a positive divisor of `L` has exactly `L / m`
    representatives in the natural interval `[0, L)`, even for unnormalized residues. -/
private theorem card_residue_class (L a m : ℕ) (hm : 0 < m) (hdvd : m ∣ L) :
    ((Finset.range L).filter fun r => r % m = a % m).card = L / m := by
  have hmul : m * (L / m) = L := Nat.mul_div_cancel' hdvd
  have hmod : a % m < m := Nat.mod_lt a hm
  have hbij : (Finset.range (L / m)).card =
      ((Finset.range L).filter fun r => r % m = a % m).card := by
    apply Finset.card_bij (fun t _ => a % m + m * t)
    · intro t ht
      have ht' : t + 1 ≤ L / m := Finset.mem_range.mp ht
      have hbound : a % m + m * t < L := calc
        a % m + m * t < m + m * t := Nat.add_lt_add_right hmod _
        _ = m * (t + 1) := by ring
        _ ≤ m * (L / m) := Nat.mul_le_mul_left m ht'
        _ = L := hmul
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hbound, by simp⟩
    · intro t ht u hu heq
      have hprod : m * t = m * u := Nat.add_left_cancel heq
      exact Nat.eq_of_mul_eq_mul_left hm hprod
    · intro r hr
      obtain ⟨hrange, hres⟩ := Finset.mem_filter.mp hr
      have hlt : r / m < L / m := (Nat.div_lt_iff_lt_mul hm).mpr (by
        rw [Nat.mul_comm, hmul]
        exact Finset.mem_range.mp hrange)
      refine ⟨r / m, Finset.mem_range.mpr hlt, ?_⟩
      rw [← hres]
      exact Nat.mod_add_div r m
  simpa using hbij.symm

example : ((Finset.range 12).filter fun r => r % 3 = 7 % 3).card = 4 :=
  card_residue_class 12 7 3 (by decide) (by decide)
example : IsCoveringSystem erdosSystem := isCoveringSystem_erdosSystem

/-- Density necessary condition (elementary, provable): a covering
    system's moduli satisfy `∑ 1/m ≥ 1` (each class `a (mod m)` has
    density `1/m`; the union must have density 1).  Specialized here as
    the entry point for the `p > 877` obstruction: the sum over the
    admissible pool must reach 1.  Mathlib route: count residues in
    `[0, L)` covered by each class (`covers_iff_forall_range` +
    `Finset.card_biUnion_le`). -/
theorem covering_density_lower_bound (S : Finset (ℕ × ℕ))
    (h : IsCoveringSystem S) :
    1 ≤ ∑ q ∈ S, (1 : ℚ) / q.2 := by
  classical
  let L := S.lcm Prod.snd
  have hpos : ∀ q ∈ S, 0 < q.2 := fun q hq => lt_trans Nat.zero_lt_one (h.one_lt_mod q hq)
  have hL : 0 < L := by
    apply Nat.pos_of_ne_zero
    intro hzero
    obtain ⟨q, hq, hqzero⟩ := Finset.lcm_eq_zero_iff.mp hzero
    exact (hpos q hq).ne' hqzero
  have hdvd : ∀ q ∈ S, q.2 ∣ L := fun q hq => Finset.dvd_lcm hq
  let C : ℕ × ℕ → Finset ℕ := fun q => (Finset.range L).filter fun r => r % q.2 = q.1 % q.2
  have hcover := (covers_iff_forall_range L hL hdvd).mp h.covers
  have hunion : S.biUnion C = Finset.range L := by
    ext r
    constructor
    · intro hr
      obtain ⟨q, hq, hrq⟩ := Finset.mem_biUnion.mp hr
      exact (Finset.mem_filter.mp hrq).1
    · intro hr
      obtain ⟨q, hq, hres⟩ := hcover r hr
      exact Finset.mem_biUnion.mpr ⟨q, hq, Finset.mem_filter.mpr ⟨hr, hres⟩⟩
  have hcount : L ≤ ∑ q ∈ S, L / q.2 := calc
    L = (Finset.range L).card := (Finset.card_range L).symm
    _ = (S.biUnion C).card := congrArg Finset.card hunion.symm
    _ ≤ ∑ q ∈ S, (C q).card := Finset.card_biUnion_le
    _ = ∑ q ∈ S, L / q.2 := by
      apply Finset.sum_congr rfl
      intro q hq
      exact card_residue_class L q.1 q.2 (hpos q hq) (hdvd q hq)
  have hcast : (L : ℚ) ≤ ∑ q ∈ S, ((L / q.2 : ℕ) : ℚ) := by exact_mod_cast hcount
  have hquot : ∀ q ∈ S, ((L / q.2 : ℕ) : ℚ) = (L : ℚ) * ((1 : ℚ) / q.2) := by
    intro q hq
    have hm : (q.2 : ℚ) ≠ 0 := by exact_mod_cast (hpos q hq).ne'
    have hmul : (q.2 : ℚ) * ((L / q.2 : ℕ) : ℚ) = L := by
      exact_mod_cast Nat.mul_div_cancel' (hdvd q hq)
    rw [mul_one_div]
    apply (eq_div_iff hm).mpr
    simpa only [mul_comm] using hmul
  have hsum : (L : ℚ) ≤ (L : ℚ) * ∑ q ∈ S, (1 : ℚ) / q.2 := by
    rw [Finset.mul_sum]
    calc
      (L : ℚ) ≤ ∑ q ∈ S, ((L / q.2 : ℕ) : ℚ) := hcast
      _ = ∑ q ∈ S, (L : ℚ) * ((1 : ℚ) / q.2) := Finset.sum_congr rfl hquot
  have hLQ : (0 : ℚ) < L := by exact_mod_cast hL
  exact (mul_le_mul_iff_right₀ hLQ).mp (by simpa only [mul_one] using hsum)

end ErdosCandidates.E273

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - DB statement matches file header verbatim; formalization as existence of S with
     IsCoveringSystem and ModuliOfPrimeMinusOne 5 is faithful.
   - IsCoveringSystem / Covers from Erdos.Covering.Basic confirmed: Finset (ℕ × ℕ) of
     (residue, modulus) pairs, distinct moduli > 1, coverage over ℤ.  Used consistently.
   - ModuliOfPrimeMinusOne def: P ≤ p with ℕ-subtraction p - 1 is safe since p ≥ 5 > 1.
   - Selfridge moduli verified: the 12 divisors of 360 of form p-1 (p ≥ 3 prime) are
     {2,4,6,10,12,18,30,36,40,60,72,180} for primes {3,5,7,11,13,19,31,37,41,61,73,181}.
     File listing matches exactly.
   - Example (12 = 13-1, 13 prime; 8 ≠ p-1 for prime p): verified (9 not prime).
   - Comment from ideal_ombrer correctly flagged as comment-sourced/unrefereed.
   - covering_density_lower_bound: standard folklore; correctly typed as ℚ-valued sum.
-/
