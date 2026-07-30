/-
  Covering systems of congruences — definitions and the classical Erdős
  witness. DEF-OWNER module: downstream Erdos.Covering.* files consume
  these definitions.

  A covering system (Erdős, early 1930s) is a finite collection of
  residue classes a_i (mod m_i) whose union is all of ℤ. Following the
  classical "distinct"/"incongruent" convention (Wikipedia, "Covering
  system"), the moduli are required to be pairwise distinct and every
  modulus must exceed 1: modulus 1 covers trivially, and repeated moduli
  admit cheap covers such as {0 (mod 2), 1 (mod 2)}.

  Degeneracy note: in the bare `Covers` predicate a pair with modulus 0
  contributes the singleton class {a} (`Int.ModEq 0` is equality); such
  pairs are excluded from covering systems by the `1 < m` field, and
  every theorem below guards moduli accordingly.

  Contents:
  * `Covers S` — the ∀-over-ℤ coverage predicate for a finite set `S` of
    (residue, modulus) pairs.
  * `IsCoveringSystem S` — coverage + pairwise distinct moduli + every
    modulus strictly greater than 1.
  * `covers_iff_forall_range` — PROVED equivalence of coverage with the
    finite (hence `decide`-able) check on residues 0, …, L-1, for any
    positive common multiple L of the moduli.
  * `covers_iff_forall_range_lcm` — the same with the canonical choice
    L = lcm of the moduli.
  * `isCoveringSystem_iff` — the decidable characterization of the full
    predicate.
  * `erdosSystem`, `isCoveringSystem_erdosSystem` — the classical system
    {0 (mod 2), 0 (mod 3), 1 (mod 4), 5 (mod 6), 7 (mod 12)} (Erdős
    1950, "On integers of the form 2^k + p and some related problems"),
    verified as a covering system by `decide` through the proved
    equivalence at L = 12. This is the joint-hypothesis instantiation
    mandated for the definition.

  Axiom audit (2026-07-29, Lean 4.33.0-rc1, `#print axioms`): every
  theorem in this file depends on at most
  {propext, Classical.choice, Quot.sound}. No `native_decide`, no
  `sorry`, no custom axioms.
-/

import Mathlib

set_option autoImplicit false

namespace Erdos.Covering

-- ════════════════════════════════════════════════════════════════════
-- §1 DEFINITIONS
-- ════════════════════════════════════════════════════════════════════

/-- `Covers S`: the residue classes encoded by the finite set `S` of
    pairs `(a, m)` — the class `{n : ℤ | n ≡ a (mod m)}` for each
    `(a, m) ∈ S` — jointly cover every integer. -/
def Covers (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ n : ℤ, ∃ p ∈ S, n ≡ (p.1 : ℤ) [ZMOD (p.2 : ℤ)]

/-- `IsCoveringSystem S`: the finite set `S` of (residue, modulus) pairs
    is a covering system in the classical distinct/incongruent sense of
    Erdős: every modulus exceeds `1`, the moduli are pairwise distinct,
    and the residue classes cover all of ℤ. -/
structure IsCoveringSystem (S : Finset (ℕ × ℕ)) : Prop where
  /-- Every modulus is strictly greater than `1` (modulus `1` covers
      trivially and is excluded from the classical notion). -/
  one_lt_mod : ∀ p ∈ S, 1 < p.2
  /-- The moduli are pairwise distinct: no modulus is repeated. -/
  injOn_mod : Set.InjOn Prod.snd (S : Set (ℕ × ℕ))
  /-- The residue classes cover every integer. -/
  covers : Covers S

-- ════════════════════════════════════════════════════════════════════
-- §2 DECIDABLE CHARACTERIZATION: REDUCTION MOD A COMMON MULTIPLE
-- ════════════════════════════════════════════════════════════════════

/-- Coverage of ℤ is equivalent to coverage of the residues
    `0, …, L - 1` for any positive common multiple `L` of the moduli:
    membership of `n` in the class `a (mod m)` only depends on
    `n mod L` when `m ∣ L`. The right-hand side is decidable, so this
    equivalence makes `Covers` checkable by `decide`. -/
theorem covers_iff_forall_range {S : Finset (ℕ × ℕ)} (L : ℕ) (hL : 0 < L)
    (hdvd : ∀ p ∈ S, p.2 ∣ L) :
    Covers S ↔ ∀ r ∈ Finset.range L, ∃ p ∈ S, r % p.2 = p.1 % p.2 := by
  constructor
  · -- ℤ-coverage restricts to the natural residues below `L`.
    intro hcov r _hr
    obtain ⟨p, hpS, hcong⟩ := hcov (r : ℤ)
    exact ⟨p, hpS, Int.natCast_modEq_iff.mp hcong⟩
  · -- Conversely, reduce an arbitrary `n : ℤ` modulo `L`.
    intro hfin n
    have hL0 : ((L : ℤ)) ≠ 0 := by exact_mod_cast hL.ne'
    have hnn : 0 ≤ n % (L : ℤ) := Int.emod_nonneg n hL0
    have hlt : n % (L : ℤ) < (L : ℤ) := Int.emod_lt_of_pos n (by exact_mod_cast hL)
    obtain ⟨p, hpS, hpr⟩ := hfin (n % (L : ℤ)).toNat (Finset.mem_range.mpr (by omega))
    refine ⟨p, hpS, ?_⟩
    have hmdvd : ((p.2 : ℤ)) ∣ (L : ℤ) := Int.natCast_dvd_natCast.mpr (hdvd p hpS)
    -- `n ≡ n % L (mod L)`, hence also `(mod p.2)` since `p.2 ∣ L`.
    have hLL : n % (L : ℤ) ≡ n [ZMOD (L : ℤ)] := Int.emod_emod_of_dvd n (dvd_refl _)
    have hnm : n ≡ ((n % (L : ℤ)).toNat : ℤ) [ZMOD (p.2 : ℤ)] := by
      rw [Int.toNat_of_nonneg hnn]
      exact (hLL.of_dvd hmdvd).symm
    have hnat : ((n % (L : ℤ)).toNat : ℤ) ≡ (p.1 : ℤ) [ZMOD (p.2 : ℤ)] :=
      Int.natCast_modEq_iff.mpr hpr
    exact hnm.trans hnat

/-- `covers_iff_forall_range` at the canonical common multiple: the lcm
    of the moduli. Only positivity of the moduli is required. -/
theorem covers_iff_forall_range_lcm {S : Finset (ℕ × ℕ)}
    (hpos : ∀ p ∈ S, 0 < p.2) :
    Covers S ↔
      ∀ r ∈ Finset.range (S.lcm Prod.snd), ∃ p ∈ S, r % p.2 = p.1 % p.2 := by
  have hL : 0 < S.lcm Prod.snd := by
    rcases Nat.eq_zero_or_pos (S.lcm Prod.snd) with h0 | hpos'
    · obtain ⟨p, hp, hp0⟩ := Finset.lcm_eq_zero_iff.mp h0
      exact absurd hp0 (hpos p hp).ne'
    · exact hpos'
  exact covers_iff_forall_range (S.lcm Prod.snd) hL fun p hp => Finset.dvd_lcm hp

/-- Decidable characterization of `IsCoveringSystem`, for any positive
    common multiple `L` of the moduli: all three defining conditions
    become bounded quantifications over `S` and `Finset.range L`, hence
    checkable by `decide`. -/
theorem isCoveringSystem_iff {S : Finset (ℕ × ℕ)} (L : ℕ) (hL : 0 < L)
    (hdvd : ∀ p ∈ S, p.2 ∣ L) :
    IsCoveringSystem S ↔
      (∀ p ∈ S, 1 < p.2) ∧ (∀ p ∈ S, ∀ q ∈ S, p.2 = q.2 → p = q) ∧
        ∀ r ∈ Finset.range L, ∃ p ∈ S, r % p.2 = p.1 % p.2 := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, (covers_iff_forall_range L hL hdvd).mp h3⟩
    intro p hp q hq hpq
    exact h2 (Finset.mem_coe.mpr hp) (Finset.mem_coe.mpr hq) hpq
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, (covers_iff_forall_range L hL hdvd).mpr h3⟩
    intro p hp q hq hpq
    exact h2 p (Finset.mem_coe.mp hp) q (Finset.mem_coe.mp hq) hpq

-- ════════════════════════════════════════════════════════════════════
-- §3 BASIC API
-- ════════════════════════════════════════════════════════════════════

/-- A covering system is nonempty: some class must cover `0`. -/
theorem IsCoveringSystem.nonempty {S : Finset (ℕ × ℕ)}
    (h : IsCoveringSystem S) : S.Nonempty := by
  obtain ⟨p, hpS, -⟩ := h.covers 0
  exact ⟨p, hpS⟩

/-- In a covering system the moduli are pairwise distinct, so the set of
    moduli has the same cardinality as the system itself. -/
theorem IsCoveringSystem.card_image_snd {S : Finset (ℕ × ℕ)}
    (h : IsCoveringSystem S) : (S.image Prod.snd).card = S.card :=
  Finset.card_image_iff.mpr h.injOn_mod

-- ════════════════════════════════════════════════════════════════════
-- §4 THE CLASSICAL ERDŐS WITNESS
-- ════════════════════════════════════════════════════════════════════

/-- The classical Erdős covering system
    `{0 (mod 2), 0 (mod 3), 1 (mod 4), 5 (mod 6), 7 (mod 12)}`
    (Erdős 1950): the standard example of a covering system with
    distinct moduli, all strictly greater than `1`. -/
def erdosSystem : Finset (ℕ × ℕ) := {(0, 2), (0, 3), (1, 4), (5, 6), (7, 12)}

-- Ground checks for `erdosSystem`: five classes, the expected moduli.
example : erdosSystem.card = 5 := by decide
example : ((7, 12) : ℕ × ℕ) ∈ erdosSystem := by decide
example : erdosSystem.image Prod.snd = {2, 3, 4, 6, 12} := by decide

/-- **Satisfiability witness.** The classical Erdős system is a covering
    system: distinct moduli, all exceeding `1`, covering every integer.
    Verified by kernel `decide` through `isCoveringSystem_iff` at the
    common multiple `L = 12` of the moduli `{2, 3, 4, 6, 12}`. -/
theorem isCoveringSystem_erdosSystem : IsCoveringSystem erdosSystem :=
  (isCoveringSystem_iff 12 (by decide) (by decide)).mpr (by decide)

-- ════════════════════════════════════════════════════════════════════
-- §5 GROUND CHECKS FOR THE PREDICATES
-- ════════════════════════════════════════════════════════════════════

-- `Covers` alone tolerates modulus 1 (it covers trivially) …
example : Covers ({(0, 1)} : Finset (ℕ × ℕ)) :=
  (covers_iff_forall_range 1 (by decide) (by decide)).mpr (by decide)

-- … but `IsCoveringSystem` rejects it via `one_lt_mod`.
example : ¬ IsCoveringSystem ({(0, 1)} : Finset (ℕ × ℕ)) := fun h =>
  absurd (h.one_lt_mod (0, 1) (Finset.mem_singleton_self _)) (by decide)

-- A single class mod 2 does not cover ℤ (the residue 1 is missed).
example : ¬ Covers ({(0, 2)} : Finset (ℕ × ℕ)) := fun h =>
  absurd ((covers_iff_forall_range 2 (by decide) (by decide)).mp h) (by decide)

-- Odd and even classes cover ℤ …
example : Covers ({(0, 2), (1, 2)} : Finset (ℕ × ℕ)) :=
  (covers_iff_forall_range 2 (by decide) (by decide)).mpr (by decide)

-- … but the repeated modulus disqualifies them as a covering system.
example : ¬ IsCoveringSystem ({(0, 2), (1, 2)} : Finset (ℕ × ℕ)) := fun h => by
  have heq : ((0, 2) : ℕ × ℕ) = (1, 2) := h.injOn_mod (by simp) (by simp) rfl
  exact absurd heq (by decide)

end Erdos.Covering
