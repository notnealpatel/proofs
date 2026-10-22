/-
# A distinct covering system with minimum modulus 7 and lcm 10080

Shiliang Zhang and Jiheng Zhang, “A Distinct Covering System with
Minimum Modulus 7 and Minimal Least Common Multiple 10080”,
arXiv:2607.19029, §7. The explicit 66 classes give a distinct covering
system of the integers with minimum modulus `7` and lcm `10080`,
refuting Klein's Conjecture 2 (Integers 26 (2026), #A38), which proposed
minimum lcm `15120`. Only the upper bound is formalized; the paper's
matching lower bound relies on Gurobi branch-and-bound computations.
Coverage reduces to residues `0,…,10079`, since every modulus divides
`10080`.
-/
import Mathlib

set_option autoImplicit false

namespace CoveringSystemMinModulusSeven

/-! ## Definitions mirroring Section 2 of the paper -/

/-- A finite list of congruence classes `a (mod m)`, each stored as the
pair `(a, m)`, is a *covering system*: every modulus satisfies
`2 ≤ m`, every residue satisfies `a < m`, and every integer lies in
some class. -/
def IsCoveringSystem (S : List (ℕ × ℕ)) : Prop :=
  (∀ p ∈ S, 2 ≤ p.2 ∧ p.1 < p.2) ∧ ∀ x : ℤ, ∃ p ∈ S, x ≡ (p.1 : ℤ) [ZMOD (p.2 : ℤ)]

/-- A covering system is *distinct* when its moduli are pairwise
distinct. -/
def IsDistinctCoveringSystem (S : List (ℕ × ℕ)) : Prop :=
  IsCoveringSystem S ∧ (S.map Prod.snd).Nodup

/-- The system `S` has *minimum modulus* `m`: `m` occurs as a modulus
and every modulus is at least `m`. -/
def HasMinModulus (S : List (ℕ × ℕ)) (m : ℕ) : Prop :=
  m ∈ S.map Prod.snd ∧ ∀ p ∈ S, m ≤ p.2

/-- The least common multiple of the moduli of `S`. -/
def lcmModuli (S : List (ℕ × ℕ)) : ℕ :=
  (S.map Prod.snd).foldr Nat.lcm 1

/-- The set of least common multiples of distinct covering systems with
minimum modulus `m`; `L_min(m)` of the paper is its least element. -/
def lcmSpectrum (m : ℕ) : Set ℕ :=
  {L | ∃ S : List (ℕ × ℕ), IsDistinctCoveringSystem S ∧ HasMinModulus S m ∧ lcmModuli S = L}

/-- **Klein's Conjecture 2** (Integers 26 (2026) #A38): the least
common multiple of the moduli of a distinct covering system with
minimum modulus 7 is at least 15120, and 15120 is attained, i.e.
`L_min(7) = 15120`. -/
def KleinConjectureTwo : Prop :=
  IsLeast (lcmSpectrum 7) 15120

/-- Boolean check that the classes of `S` cover `0, 1, ..., L - 1`. -/
def coversBelow (S : List (ℕ × ℕ)) (L : ℕ) : Bool :=
  (List.range L).all fun x => S.any fun p => x % p.2 == p.1

/-! ## Examples on a classical small system -/

/-- The classical distinct covering system
`0 (mod 2), 0 (mod 3), 1 (mod 4), 5 (mod 6), 7 (mod 12)`. -/
def classicalSystem : List (ℕ × ℕ) := [(0, 2), (0, 3), (1, 4), (5, 6), (7, 12)]

example : lcmModuli classicalSystem = 12 := by decide
example : lcmModuli [] = 1 := rfl
example : HasMinModulus classicalSystem 2 := by unfold HasMinModulus; decide
example : ¬ HasMinModulus classicalSystem 3 := by unfold HasMinModulus; decide
example : coversBelow classicalSystem 12 = true := by decide
-- Dropping the class `7 (mod 12)` leaves `7` uncovered.
example : coversBelow [(0, 2), (0, 3), (1, 4), (5, 6)] 12 = false := by decide
example : ¬ IsCoveringSystem [(0, 2), (0, 3)] := by
  rintro ⟨-, hcov⟩
  obtain ⟨p, hp, hx⟩ := hcov 1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> revert hx <;> decide

/-! ## Reduction of covering ℤ to a finite check -/

/-- If `m ∣ L` and the representative `(x mod L)` of `x` reduces to `a`
modulo `m`, then `x ≡ a (mod m)`. -/
theorem modEq_of_toNat_emod_mod {x : ℤ} {L m a : ℕ} (hL : 0 < L) (hm : m ∣ L)
    (h : (x % L).toNat % m = a) : x ≡ (a : ℤ) [ZMOD (m : ℤ)] := by
  have hnn : 0 ≤ x % (L : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hL.ne')
  have hr : (((x % L).toNat : ℕ) : ℤ) = x % L := Int.toNat_of_nonneg hnn
  have h1 : x ≡ x % L [ZMOD L] := (Int.mod_modEq x L).symm
  have h2 : x ≡ x % L [ZMOD m] := h1.of_dvd (Int.natCast_dvd_natCast.mpr hm)
  have h3 : (((x % L).toNat : ℕ) : ℤ) ≡ (((x % L).toNat % m : ℕ) : ℤ) [ZMOD m] := by
    rw [Int.natCast_mod]
    exact (Int.mod_modEq _ _).symm
  rw [hr, h] at h3
  exact h2.trans h3

/-- `coversBelow S L = true` provides, for each `r < L`, a class of `S`
containing `r`. -/
theorem exists_mod_eq_of_coversBelow {S : List (ℕ × ℕ)} {L r : ℕ} (hr : r < L)
    (h : coversBelow S L = true) : ∃ p ∈ S, r % p.2 = p.1 := by
  rw [coversBelow, List.all_eq_true] at h
  simpa [List.any_eq_true] using h r (List.mem_range.mpr hr)

/-- **Finite criterion.**  If every modulus of `S` divides `L > 0`, the
classes are valid (`2 ≤ m`, `a < m`), and they cover `0, ..., L - 1`,
then `S` is a covering system of ℤ. -/
theorem isCoveringSystem_of_coversBelow {S : List (ℕ × ℕ)} {L : ℕ} (hL : 0 < L)
    (hdvd : ∀ p ∈ S, p.2 ∣ L) (hvalid : ∀ p ∈ S, 2 ≤ p.2 ∧ p.1 < p.2)
    (h : coversBelow S L = true) : IsCoveringSystem S := by
  refine ⟨hvalid, fun x => ?_⟩
  have hlt : (x % L).toNat < L := by
    have hnn : 0 ≤ x % (L : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hL.ne')
    have hlt' : x % (L : ℤ) < L := Int.emod_lt_of_pos _ (by exact_mod_cast hL)
    omega
  obtain ⟨p, hp, hmod⟩ := exists_mod_eq_of_coversBelow hlt h
  exact ⟨p, hp, modEq_of_toNat_emod_mod hL (hdvd p hp) hmod⟩

/-- Satisfiability check of the finite criterion: the classical system
is a distinct covering system. -/
example : IsDistinctCoveringSystem classicalSystem :=
  ⟨isCoveringSystem_of_coversBelow (L := 12) (by decide) (by decide) (by decide) (by decide),
    by decide⟩

/-! ## The Zhang–Zhang system (Section 7) -/

/-- The 66 congruence classes `a (mod m)` of the paper's Section 7,
stored as pairs `(a, m)` in the paper's order. -/
def zhangSystem : List (ℕ × ℕ) :=
  [(6, 7), (7, 8), (8, 9), (6, 10), (9, 12), (8, 14), (12, 15), (3, 16), (14, 18), (0, 20),
   (4, 21), (13, 24), (26, 28), (24, 30), (27, 32), (33, 35), (5, 36), (11, 40), (16, 42),
   (2, 45), (1, 48), (52, 56), (30, 60), (7, 63), (28, 70), (29, 72), (59, 80), (10, 84),
   (74, 90), (43, 96), (93, 105), (73, 112), (64, 120), (112, 126), (38, 140), (65, 144),
   (43, 160), (121, 168), (110, 180), (18, 210), (169, 224), (185, 240), (154, 252),
   (248, 280), (203, 288), (128, 315), (313, 336), (209, 360), (292, 420), (75, 480),
   (217, 504), (404, 560), (578, 630), (505, 672), (281, 720), (472, 840), (553, 1008),
   (233, 1120), (532, 1260), (875, 1440), (124, 1680), (281, 2016), (2044, 2520),
   (2153, 3360), (5033, 5040), (7193, 10080)]

example : zhangSystem.length = 66 := rfl
example : zhangSystem.head? = some (6, 7) := rfl
example : zhangSystem.getLast? = some (7193, 10080) := rfl

/-- Kernel computation: the 66 classes cover every residue modulo
10080. -/
theorem coversBelow_zhangSystem : coversBelow zhangSystem 10080 = true := by
  decide +kernel

/-- Every class of the system is valid (`2 ≤ m`, `a < m`), has modulus
at least 7, and has modulus dividing 10080. -/
theorem zhangSystem_valid :
    ∀ p ∈ zhangSystem, 7 ≤ p.2 ∧ p.1 < p.2 ∧ p.2 ∣ 10080 := by
  decide +kernel

/-- The moduli of the system are pairwise distinct. -/
theorem nodup_moduli_zhangSystem : (zhangSystem.map Prod.snd).Nodup := by
  decide +kernel

/-- The least common multiple of the moduli is 10080. -/
theorem lcmModuli_zhangSystem : lcmModuli zhangSystem = 10080 := by
  decide +kernel

/-- The 66 classes of Section 7 form a covering system of ℤ. -/
theorem isCoveringSystem_zhangSystem : IsCoveringSystem zhangSystem :=
  isCoveringSystem_of_coversBelow (L := 10080) (by decide)
    (fun p hp => (zhangSystem_valid p hp).2.2)
    (fun p hp => ⟨le_trans (by decide) (zhangSystem_valid p hp).1, (zhangSystem_valid p hp).2.1⟩)
    coversBelow_zhangSystem

/-- The minimum modulus of the system is 7. -/
theorem hasMinModulus_zhangSystem : HasMinModulus zhangSystem 7 :=
  ⟨by decide, fun p hp => (zhangSystem_valid p hp).1⟩

/-- **Zhang–Zhang, Section 7 (upper bound of Theorem 1).**  There is a
distinct covering system with minimum modulus 7 whose moduli have least
common multiple 10080; hence `L_min(7) ≤ 10080`. -/
theorem exists_distinctCoveringSystem_minModulus_seven_lcm_10080 :
    ∃ S : List (ℕ × ℕ), IsDistinctCoveringSystem S ∧ HasMinModulus S 7 ∧ lcmModuli S = 10080 :=
  ⟨zhangSystem, ⟨isCoveringSystem_zhangSystem, nodup_moduli_zhangSystem⟩,
    hasMinModulus_zhangSystem, lcmModuli_zhangSystem⟩

/-- `10080` is the lcm of a distinct covering system with minimum
modulus 7. -/
theorem mem_lcmSpectrum_seven : 10080 ∈ lcmSpectrum 7 :=
  exists_distinctCoveringSystem_minModulus_seven_lcm_10080

/-- **Klein's Conjecture 2 is false** (Zhang–Zhang, arXiv:2607.19029):
the minimum least common multiple of a distinct covering system with
minimum modulus 7 is not 15120, since 10080 < 15120 is attained. -/
theorem not_kleinConjectureTwo : ¬ KleinConjectureTwo := by
  intro h
  have hle : 15120 ≤ 10080 := h.2 mem_lcmSpectrum_seven
  omega

end CoveringSystemMinModulusSeven
