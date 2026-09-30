/-
Erdős–Gyárfás problem 64 — the audited affine-family `C₁₆`/`C₃₂` certificate.

PROVENANCE.  The audited certificate for the affine family of the triangle-rooted
search: for even `m ≥ 14` and a prime `p` with `m ∣ p - 1`, let `r ∈ F_p` have
multiplicative order exactly `m`.  On the affine states `(d, k) ∈ F_p × ZMod m`
consider the three moves

* `a : (d, k) ↦ (d, k + 1)`,
* `A = a⁻¹ : (d, k) ↦ (d, k - 1)`,
* `t : (d, k) ↦ (d + rᵏ, k + m/2)`,

so that `t` translates the `d`-coordinate by the `k`-th power of `r` and shifts the
`k`-coordinate by half the order.  The audited word is

  `W = AAAAA t aaaa t aa t A t A t AAAA t aaaaa t a t A`  (32 letters),

and the audited certificate asserts that the `W`-trajectory of the origin `(0, 0)`
contains a simple cycle of length `16` or `32`, according to a dichotomy on the two
constants `D2 = D1 + D3` and `H = D1 - D3`, where `D1 = r⁻⁵ - r⁻¹` and `D3 = r - 1`:

* if `D2 = 0` the states `0, …, 15` are pairwise distinct and state `16` equals state
  `0`, giving a simple `C₁₆`;
* if `H = 0` the states `12, …, 27` are pairwise distinct and state `28` equals state
  `12`, giving a simple `C₁₆`;
* otherwise the states `0, …, 31` are pairwise distinct and state `32` equals state `0`,
  so `W` is a simple `C₃₂`.

WHAT IS FORMALIZED HERE.  The certificate is stated for an abstract *character*
`χ : ZMod m → F` (`χ 0 = 1`, `χ (x + y) = χ x * χ y`, `χ (m/2) = -1`), which is
exactly the data of `k ↦ rᵏ` needed by the moves; the specialization to
`χ k = r ^ k.val` for an element of exact order `m` is not used by the finite
verification.  The module contains:

* `Character`, `step`, `word` — the moves and the audited word;
* `trace` — the audited trajectory, the `33` states `0, …, 32` of the origin under
  `W`, with `d`-coordinates `0`, `χ(-5)`, `D1`, `D1 + χ(1)`, `D2`, `C`, `D3`, `χ(1)`
  and `k`-coordinates the canonical labels `0, -1, …, -5, m/2 - 5, …, m/2 + 1`;
* `trace_step` — all `32` transitions of the trajectory, each an identity in `F`
  combined with the single `ZMod m` fact `m/2 + m/2 = 0` (from `Even m`);
* `trace_16_eq_zero_iff`, `trace_28_eq_12_iff`, `trace_32_eq_zero` — the closure
  conditions `D2 = 0`, `H = 0`, and the unconditional `trace 32 = trace 0`;
* `dcoord_ne_of_collision` — pairwise distinctness of trajectory states that share a
  `k`-class, from `D1 ≠ 0`, `D2 ≠ 0`, `D3 ≠ 0`, `H ≠ 0`;
* `MoveCycle` — the witness type: a sequence of `n + 1` states, the `n` prescribed
  moves between consecutive states, closure, and injectivity of the first `n`;
* `cycle16_of_D2`, `cycle16_of_H`, `cycle32_of_nonzero`, `hasMoveCycle` — the three
  branches and the dichotomy, with jointly satisfiable hypotheses
  (`character29` realizes the `C₃₂` branch: `p = 29`, `m = 14`, `r = 4`).

NOT FORMALIZED HERE.  This module does not build the graph-theoretic cycle
(`SimpleGraph.Walk.IsCycle`) of the affine graph, does not prove the general
specialization `χ k = r ^ k.val` from `IsPrimitiveRoot r m`, and does not derive
`D1 ≠ 0` and `D3 ≠ 0` from `14 ≤ m` and `Even m`.  It proves the finite
prefix-state certificate itself: the audited `33`-state trajectory, its closure, and
the distinctness/dichotomy that turns it into a simple `C₁₆` or `C₃₂`.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace Erdos64

/-- A `χ : ZMod m → F` is a **character** of the cyclic `k`-coordinate when it is
multiplicative, sends `0` to `1`, and sends the half-order element `m/2` to `-1`.
For `χ k = r ^ k.val` with `r` of multiplicative order exactly `m` these are the only
properties of the power map used by the moves of the affine family. -/
structure Character (F : Type*) [CommRing F] (m : ℕ) where
  toFun : ZMod m → F
  map_zero : toFun 0 = 1
  map_add : ∀ x y, toFun (x + y) = toFun x * toFun y
  map_half : toFun ((m / 2 : ℕ) : ZMod m) = -1

namespace AffineFamily

variable {F : Type*} [CommRing F] {m : ℕ}

/-- The affine state space `F × ZMod m`. -/
abbrev St (F : Type*) (m : ℕ) := F × ZMod m

/-- The half-order shift `m / 2`, as an integer, so that the `k`-coordinates of the
trajectory can be written as explicit integer labels. -/
def halfZ (m : ℕ) : ℤ := (m / 2 : ℕ)

/-- The canonical integer label `z`, viewed in `ZMod m`.  A notation rather than a
definition, so that the standard `Int.cast` simplification lemmas apply to it. -/
local notation "kz" z:max => (((z : ℤ) : ZMod m))

/-- The half-order element `m/2` of `ZMod m`, named so that the `t`-shift arithmetic of
the trajectory is stated about a single opaque term. -/
def hhalf (m : ℕ) : ZMod m := ((m / 2 : ℕ) : ZMod m)

/-- The three letters of the affine family. -/
inductive Move where
  | a
  | A
  | t

/-- The move `a : (d, k) ↦ (d, k + 1)`. -/
def stepA (x : St F m) : St F m := (x.1, x.2 + 1)

/-- The move `A = a⁻¹ : (d, k) ↦ (d, k - 1)`. -/
def stepAinv (x : St F m) : St F m := (x.1, x.2 - 1)

/-- The move `t : (d, k) ↦ (d + χ k, k + m/2)`. -/
def stepT (χ : Character F m) (x : St F m) : St F m :=
  (x.1 + χ.toFun x.2, x.2 + hhalf m)

/-- The action of a letter on a state. -/
def step (χ : Character F m) : Move → St F m → St F m
  | .a => stepA
  | .A => stepAinv
  | .t => stepT χ

/-- The audited word `W = AAAAAtaaaataatAtAtAAAAtaaaaatatA` of length `32`. -/
def word : Fin 32 → Move :=
  ![.A, .A, .A, .A, .A, .t, .a, .a, .a, .a, .t, .a, .a, .t, .A, .t, .A, .t, .A, .A, .A, .A, .t,
    .a, .a, .a, .a, .a, .t, .a, .t, .A]

/-! ### Arithmetic of the `k`-coordinate -/

lemma kz_add (a b : ℤ) : kz (a + b) = kz a + kz b := by
  push_cast
  ring

lemma two_halfZ (hm : Even m) : 2 * halfZ m = (m : ℤ) := by
  have h : 2 * (m / 2) = m := Nat.two_mul_div_two_of_even hm
  simp only [halfZ]
  omega

/-- The single `ZMod m` arithmetic fact used by the trajectory: `m/2 + m/2 = 0`. -/
lemma two_half (hm : Even m) : hhalf m + hhalf m = 0 := by
  have h : 2 * (m / 2) = m := Nat.two_mul_div_two_of_even hm
  show ((m / 2 : ℕ) : ZMod m) + ((m / 2 : ℕ) : ZMod m) = 0
  calc ((m / 2 : ℕ) : ZMod m) + ((m / 2 : ℕ) : ZMod m)
      = ((m / 2 + m / 2 : ℕ) : ZMod m) := by push_cast; ring
    _ = ((2 * (m / 2) : ℕ) : ZMod m) := by rw [Nat.two_mul]
    _ = ((m : ℕ) : ZMod m) := by rw [h]
    _ = 0 := ZMod.natCast_self m

lemma kz_half : kz (halfZ m) = hhalf m :=
  Int.cast_natCast _

/-- The `k`-arithmetic of the two `t`-wraps, in the normal form that `simp` produces. -/
lemma half_mul_two (hm : Even m) : hhalf m * 2 = 0 := by
  rw [show hhalf m * 2 = hhalf m + hhalf m from by ring, two_half hm]

lemma kz_zero : kz 0 = 0 :=
  Int.cast_zero

/-- Shifting a `k`-label by one keeps the `d`-coordinate fixed and adds `1`. -/
lemma kz_add_one (z : ℤ) : kz (z + 1) = kz z + 1 := by
  push_cast
  ring

lemma kz_sub_one (z : ℤ) : kz (z - 1) = kz z - 1 := by
  push_cast
  ring

/-- The `t`-move without wrap: the label `z` becomes the canonical label `m/2 + z`. -/
lemma kz_add_half (z : ℤ) : kz z + hhalf m = kz (halfZ m + z) := by
  rw [← kz_half, ← kz_add]
  exact congrArg (fun w : ℤ => ((w : ℤ) : ZMod m)) (add_comm z (halfZ m))

/-- The `t`-move with wrap: the canonical label `m/2 + z` returns to `z`. -/
lemma kz_half_add (hm : Even m) (z : ℤ) : kz (halfZ m + z) + hhalf m = kz z := by
  have h : halfZ m + (halfZ m + z) = z + (m : ℤ) := by
    have := two_halfZ (m := m) hm
    omega
  rw [kz_add_half (halfZ m + z), h]
  show kz (z + (m : ℤ)) = kz z
  rw [kz_add]
  have hm0 : kz (m : ℤ) = 0 := by
    rw [show kz (m : ℤ) = ((m : ℕ) : ZMod m) from Int.cast_natCast m, ZMod.natCast_self]
  rw [hm0, add_zero]

lemma char_half (χ : Character F m) : χ.toFun (hhalf m) = -1 := by
  show χ.toFun ((m / 2 : ℕ) : ZMod m) = -1
  exact χ.map_half

/-- The `t`-move picks up `-χ z` on a shifted label. -/
lemma char_shift (χ : Character F m) (z : ℤ) :
    χ.toFun (kz (halfZ m + z)) = -χ.toFun (kz z) := by
  have hh : χ.toFun (kz (halfZ m)) = -1 := by
    rw [kz_half]
    exact char_half χ
  rw [kz_add, χ.map_add, hh]
  ring

lemma char_zero (χ : Character F m) : χ.toFun (kz 0) = 1 := by
  rw [kz_zero]
  exact χ.map_zero

/-! ### The audited trajectory -/

/-- `D1 = χ(-5) - χ(-1) = r⁻⁵ - r⁻¹`. -/
def D1 (χ : Character F m) : F := χ.toFun (kz (-5)) - χ.toFun (kz (-1))

/-- `D3 = χ(1) - 1 = r - 1`. -/
def D3 (χ : Character F m) : F := χ.toFun (kz 1) - 1

/-- `D2 = D1 + D3`. -/
def D2 (χ : Character F m) : F := D1 χ + D3 χ

/-- `H = D1 - D3`. -/
def Hc (χ : Character F m) : F := D1 χ - D3 χ

/-- The intermediate value `D1 + χ(1) = r⁻⁵ - r⁻¹ + r`. -/
def E (χ : Character F m) : F := D1 χ + χ.toFun (kz 1)

/-- The intermediate value `χ(-5) + χ(1) - 1 = r⁻⁵ + r - 1`. -/
def Cc (χ : Character F m) : F := χ.toFun (kz (-5)) + χ.toFun (kz 1) - 1

/-- The `d`-coordinates of the `33` states of the audited trajectory. -/
def dcoord (χ : Character F m) : Fin 33 → F :=
  ![0, 0, 0, 0, 0, 0, χ.toFun (kz (-5)), χ.toFun (kz (-5)), χ.toFun (kz (-5)),
    χ.toFun (kz (-5)), χ.toFun (kz (-5)), D1 χ, D1 χ, D1 χ, E χ, E χ, D2 χ, D2 χ, Cc χ, Cc χ,
    Cc χ, Cc χ, Cc χ, D3 χ, D3 χ, D3 χ, D3 χ, D3 χ, D3 χ, χ.toFun (kz 1), χ.toFun (kz 1), 0, 0]

/-- The canonical `k`-labels of the `33` states of the audited trajectory.  All labels
lie in `[-5, m/2 + 1]`, an interval of length `m/2 + 6 < m` for `m ≥ 14`. -/
def klabel (m : ℕ) : Fin 33 → ℤ :=
  ![0, -1, -2, -3, -4, -5, halfZ m + (-5), halfZ m + (-4), halfZ m + (-3), halfZ m + (-2),
    halfZ m + (-1), -1, 0, 1, halfZ m + 1, halfZ m, 0, -1, halfZ m + (-1), halfZ m + (-2),
    halfZ m + (-3), halfZ m + (-4), halfZ m + (-5), -5, -4, -3, -2, -1, 0, halfZ m, halfZ m + 1,
    1, 0]

/-- The audited trajectory: state `i` is `(dcoord i, klabel i)`, the state of the
origin `(0, 0)` after the first `i` letters of `W`. -/
def trace (χ : Character F m) : Fin 33 → St F m := fun i => (dcoord χ i, kz (klabel m i))

/-- The successor index `i ↦ i + 1` on the trajectory. -/
def idxSucc (i : Fin 32) : Fin 33 := ⟨i.1 + 1, by omega⟩

/-- The index `i ↦ i` as a trajectory index. -/
def idxCast (i : Fin 32) : Fin 33 := ⟨i.1, by omega⟩

/-- The audited transition table: the `32` steps of the trajectory, each an identity
in `F` together with the `ZMod m` arithmetic `m/2 + m/2 = 0` of `Even m`. -/
theorem trace_step (χ : Character F m) (hm : Even m) (i : Fin 32) :
    trace χ (idxSucc i) = step χ (word i) (trace χ (idxCast i)) := by
  fin_cases i <;>
    simp [trace, dcoord, klabel, word, idxSucc, idxCast, step, stepA, stepAinv, stepT,
      Prod.mk.injEq, and_true, true_and, kz_add_one, kz_sub_one, kz_zero, kz_half, kz_add_half,
      kz_half_add hm, char_shift χ, char_half χ, χ.map_add, χ.map_half, χ.map_zero, char_zero χ,
      D1, D2, D3, Hc, E, Cc]
  all_goals ring_nf
  all_goals simp only [half_mul_two hm, add_zero, and_self, true_and]

/-! ### Closure of the trajectory -/

/-- The trajectory closes at time `32`, unconditionally. -/
theorem trace_32_eq_zero (χ : Character F m) : trace χ 32 = trace χ 0 := by
  simp [trace, dcoord, klabel]

/-- The trajectory meets its start at time `16` exactly when `D2 = 0`. -/
theorem trace_16_eq_zero_iff (χ : Character F m) : trace χ 16 = trace χ 0 ↔ D2 χ = 0 := by
  simp [trace, dcoord, klabel, D2, D1, D3, Prod.mk.injEq]

/-- The trajectory meets its state at time `12` again at time `28` exactly when `H = 0`. -/
theorem trace_28_eq_12_iff (χ : Character F m) : trace χ 28 = trace χ 12 ↔ Hc χ = 0 := by
  change (D3 χ, kz 0) = (D1 χ, kz 0) ↔ Hc χ = 0
  simp only [Prod.mk.injEq, and_true, Hc, sub_eq_zero]
  exact eq_comm

/-! ### The `k`-classes of the trajectory -/

/-- The `14` canonical `k`-classes of the trajectory, in the order in which they first
occur: `0, -1, -2, -3, -4, -5, m/2 - 5, …, m/2 - 1, 1, m/2, m/2 + 1`. -/
def classVal (m : ℕ) : Fin 14 → ℤ :=
  ![0, -1, -2, -3, -4, -5, halfZ m + (-5), halfZ m + (-4), halfZ m + (-3), halfZ m + (-2),
    halfZ m + (-1), 1, halfZ m, halfZ m + 1]

/-- The class of each trajectory state. -/
def classIdx : Fin 33 → Fin 14 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 0, 11, 13, 12, 0, 1, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0,
    12, 13, 11, 0]

lemma klabel_eq_classVal (i : Fin 33) : klabel m i = classVal m (classIdx i) := by
  fin_cases i <;> simp [klabel, classVal, classIdx]

/-- For `m ≥ 14` the half-order shift is at least `7`. -/
lemma seven_le_halfZ (hm : Even m) (hm14 : 14 ≤ m) : 7 ≤ halfZ m := by
  have h := two_halfZ (m := m) hm
  omega

/-- The `14` canonical labels are pairwise distinct: any two of them lie in `[-5, m/2+1]`,
an interval of length `m/2 + 6 < m` once `m ≥ 14`. -/
theorem classVal_injective (hm : Even m) (hm14 : 14 ≤ m) :
    Function.Injective (classVal m) := by
  have h7 := seven_le_halfZ (m := m) hm hm14
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp [classVal] at hab ⊢ <;> omega

/-- Every canonical label of the trajectory lies in `[-5, m/2 + 1]`. -/
lemma klabel_bounds (hm : Even m) (hm14 : 14 ≤ m) (i : Fin 33) :
    -5 ≤ klabel m i ∧ klabel m i ≤ halfZ m + 1 := by
  have h7 := seven_le_halfZ (m := m) hm hm14
  fin_cases i <;> simp [klabel] <;> omega

/-- Two canonical labels in `[-5, m/2 + 1]` that agree in `ZMod m` agree as integers:
their difference is a multiple of `m` of absolute value `< m`. -/
lemma klabel_eq_of_kz_eq (hm : Even m) (hm14 : 14 ≤ m) {a b : ℤ} (ha : -5 ≤ a)
    (ha' : a ≤ halfZ m + 1) (hb : -5 ≤ b) (hb' : b ≤ halfZ m + 1)
    (h : kz a = kz b) : a = b := by
  have h7 := seven_le_halfZ (m := m) hm hm14
  have h2 := two_halfZ (m := m) hm
  have hdvd : (m : ℤ) ∣ b - a := (ZMod.intCast_eq_intCast_iff_dvd_sub a b m).mp h
  have hlt : |b - a| < (m : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have hz : b - a = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hlt
  omega

/-- The `d`-coordinates of the `24` colliding pairs of the trajectory: the pairs of
distinct indices that share a `k`-class. -/
def collisions : List (Fin 33 × Fin 33) :=
  [(0, 12), (0, 16), (0, 28), (12, 16), (12, 28), (16, 28), (1, 11), (1, 17), (1, 27), (11, 17),
    (11, 27), (17, 27), (2, 26), (3, 25), (4, 24), (5, 23), (6, 22), (7, 21), (8, 20), (9, 19),
    (10, 18), (13, 31), (15, 29), (14, 30)]

/-- The `d`-coordinates of the colliding pairs differ, given `D1, D2, D3, H ≠ 0`. -/
theorem dcoord_ne_of_collision (χ : Character F m) (hD1 : D1 χ ≠ 0) (hD2 : D2 χ ≠ 0)
    (hD3 : D3 χ ≠ 0) (hH : Hc χ ≠ 0) {i j : Fin 33} (h : (i, j) ∈ collisions) :
    dcoord χ i ≠ dcoord χ j := by
  have h0D1 : (0 : F) ≠ D1 χ := hD1.symm
  have h0D2 : (0 : F) ≠ D2 χ := hD2.symm
  have h0D3 : (0 : F) ≠ D3 χ := hD3.symm
  have hD1D2 : D1 χ ≠ D2 χ := by
    intro hh
    apply hD3
    simp only [D2] at hh
    exact add_left_cancel (by simpa only [add_zero] using hh.symm)
  have hD2D1 : D2 χ ≠ D1 χ := hD1D2.symm
  have hD1D3 : D1 χ ≠ D3 χ := by
    intro hh
    apply hH
    simp [Hc, hh]
  have hD3D1 : D3 χ ≠ D1 χ := hD1D3.symm
  have hD2D3 : D2 χ ≠ D3 χ := by
    intro hh
    apply hD1
    simp only [D2] at hh
    exact add_right_cancel (by simpa only [zero_add] using hh)
  have hD3D2 : D3 χ ≠ D2 χ := hD2D3.symm
  have hC5 : Cc χ ≠ χ.toFun (kz (-5)) := by
    intro hh
    apply hD3
    simp only [Cc] at hh
    simp only [D3]
    linear_combination hh
  have h5C : χ.toFun (kz (-5)) ≠ Cc χ := hC5.symm
  have hE1 : E χ ≠ χ.toFun (kz 1) := by
    intro hh
    apply hD1
    simp only [E] at hh
    linear_combination hh
  have h1E : χ.toFun (kz 1) ≠ E χ := hE1.symm
  simp only [collisions, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals (simp [dcoord]; simp_all)

/-- The `d`-coordinates of the two collisions inside the first `C₁₆` window
(states `0, …, 15`) differ, given `D1 ≠ 0`. -/
theorem dcoord_ne_of_collisionFirst (χ : Character F m) (hD1 : D1 χ ≠ 0) {i j : Fin 33}
    (h : (i, j) ∈ [(0, 12), (1, 11)]) : dcoord χ i ≠ dcoord χ j := by
  have h0D1 : (0 : F) ≠ D1 χ := hD1.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [dcoord]
    exact h0D1
  · simp [dcoord]
    exact h0D1

/-- The `d`-coordinates of the two collisions inside the second `C₁₆` window
(states `12, …, 27`) differ, given `D1 ≠ 0` and `D3 ≠ 0`. -/
theorem dcoord_ne_of_collisionSecond (χ : Character F m) (hD1 : D1 χ ≠ 0) (hD3 : D3 χ ≠ 0)
    {i j : Fin 33} (h : (i, j) ∈ [(12, 16), (17, 27)]) : dcoord χ i ≠ dcoord χ j := by
  have hD1D2 : D1 χ ≠ D2 χ := by
    intro hh
    apply hD3
    simp only [D2] at hh
    exact add_left_cancel (by simpa only [add_zero] using hh.symm)
  have hD2D3 : D2 χ ≠ D3 χ := by
    intro hh
    apply hD1
    simp only [D2] at hh
    exact add_right_cancel (by simpa only [zero_add] using hh)
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [dcoord]
    exact hD1D2
  · simp [dcoord]
    exact hD2D3

/-- **Injectivity of the trajectory along any index embedding.**  If every pair of
distinct embedded indices sharing a `k`-class is covered by a list `l` of pairs whose
`d`-coordinates differ, then the embedded trajectory is injective. -/
theorem trace_injective_on {n : ℕ} (e : Fin n → Fin 33) (l : List (Fin 33 × Fin 33))
    (χ : Character F m) (hm : Even m) (hm14 : 14 ≤ m)
    (hcover : ∀ i j : Fin n, i ≠ j → classIdx (e i) = classIdx (e j) →
      (e i, e j) ∈ l ∨ (e j, e i) ∈ l)
    (hne : ∀ p ∈ l, dcoord χ p.1 ≠ dcoord χ p.2) :
    Function.Injective (fun i : Fin n => trace χ (e i)) := by
  intro i j hij
  by_contra hne'
  have hcls : classIdx (e i) = classIdx (e j) := by
    have hk : kz (klabel m (e i)) = kz (klabel m (e j)) := by
      have := congrArg Prod.snd hij
      simpa [trace] using this
    have hlab : klabel m (e i) = klabel m (e j) :=
      klabel_eq_of_kz_eq hm hm14 (klabel_bounds hm hm14 (e i)).1 (klabel_bounds hm hm14 (e i)).2
        (klabel_bounds hm hm14 (e j)).1 (klabel_bounds hm hm14 (e j)).2 hk
    have hcv : classVal m (classIdx (e i)) = classVal m (classIdx (e j)) := by
      rw [← klabel_eq_classVal (e i), ← klabel_eq_classVal (e j), hlab]
    exact classVal_injective hm hm14 hcv
  have hd : dcoord χ (e i) = dcoord χ (e j) := by simpa [trace] using congrArg Prod.fst hij
  rcases hcover i j hne' hcls with hp | hp
  · exact hne (e i, e j) hp hd
  · exact hne (e j, e i) hp hd.symm

/-! ### The simple-cycle witness and the dichotomy -/

/-- A **move cycle**: a closed move sequence, packaging `n + 1` states whose `n`
consecutive transitions follow a prescribed letter sequence, whose first state returns
after `n` steps, and whose first `n` states are pairwise distinct.  It records the
preclosure states and the prescribed moves between them; at the intended positive
lengths this is usable as simple-cycle data once an ambient graph is supplied, but the
structure does not itself build a `SimpleGraph` cycle. -/
structure MoveCycle (χ : Character F m) (n : ℕ) (lbl : Fin n → Move) where
  vertex : Fin (n + 1) → St F m
  edge : ∀ i : Fin n, vertex ⟨i.1 + 1, by omega⟩ = step χ (lbl i) (vertex ⟨i.1, by omega⟩)
  closed : vertex 0 = vertex (Fin.last n)
  simple : Function.Injective (fun i : Fin n => vertex ⟨i.1, by omega⟩)

/-- Embed the first sixteen indices into the trajectory table. -/
def firstIndex (i : Fin 16) : Fin 33 := ⟨i.1, by omega⟩

/-- Embed the shifted sixteen indices into the trajectory table. -/
def secondIndex (i : Fin 16) : Fin 33 := ⟨i.1 + 12, by omega⟩

/-- Embed the first thirty-two indices into the trajectory table. -/
def fullIndex (i : Fin 32) : Fin 33 := ⟨i.1, by omega⟩

example : firstIndex 0 = 0 := rfl

example : secondIndex 0 = 12 := rfl

example : fullIndex 31 = 31 := rfl

/-- The complete finite collision check for the first sixteen-state window. -/
lemma coverFirst : ∀ i j : Fin 16, i ≠ j →
    classIdx (firstIndex i) = classIdx (firstIndex j) →
      (firstIndex i, firstIndex j) ∈ [(0, 12), (1, 11)] ∨
        (firstIndex j, firstIndex i) ∈ [(0, 12), (1, 11)] := by
  decide

/-- The complete finite collision check for the shifted sixteen-state window. -/
lemma coverSecond : ∀ i j : Fin 16, i ≠ j →
    classIdx (secondIndex i) = classIdx (secondIndex j) →
      (secondIndex i, secondIndex j) ∈ [(12, 16), (17, 27)] ∨
        (secondIndex j, secondIndex i) ∈ [(12, 16), (17, 27)] := by
  decide

/-- The complete finite collision check for the thirty-two-state window. -/
lemma coverFull : ∀ i j : Fin 32, i ≠ j →
    classIdx (fullIndex i) = classIdx (fullIndex j) →
      (fullIndex i, fullIndex j) ∈ collisions ∨
        (fullIndex j, fullIndex i) ∈ collisions := by
  decide

/-- If `D2 = 0` the first `16` letters of `W` close up and the states `0, …, 15` are a
simple `C₁₆`. -/
def cycle16_of_D2 (χ : Character F m) (hm : Even m) (hm14 : 14 ≤ m) (hD1 : D1 χ ≠ 0)
    (hD2 : D2 χ = 0) :
    MoveCycle χ 16 (fun i : Fin 16 => word ⟨i.1, by omega⟩) where
  vertex := fun i => trace χ ⟨i.1, by omega⟩
  edge := fun i => trace_step χ hm ⟨i.1, by omega⟩
  closed := ((trace_16_eq_zero_iff χ).mpr hD2).symm
  simple :=
    trace_injective_on firstIndex [(0, 12), (1, 11)] χ hm hm14
      coverFirst
      (fun p hp => dcoord_ne_of_collisionFirst χ hD1 hp)

/-- If `H = 0` the letters `12, …, 27` of `W` close up and the states `12, …, 27` are a
simple `C₁₆`. -/
def cycle16_of_H (χ : Character F m) (hm : Even m) (hm14 : 14 ≤ m) (hD1 : D1 χ ≠ 0)
    (hD3 : D3 χ ≠ 0) (hH : Hc χ = 0) :
    MoveCycle χ 16 (fun i : Fin 16 => word ⟨i.1 + 12, by omega⟩) where
  vertex := fun i => trace χ ⟨i.1 + 12, by omega⟩
  edge := fun i => trace_step χ hm ⟨i.1 + 12, by omega⟩
  closed := ((trace_28_eq_12_iff χ).mpr hH).symm
  simple :=
    trace_injective_on secondIndex [(12, 16), (17, 27)] χ hm hm14
      coverSecond
      (fun p hp => dcoord_ne_of_collisionSecond χ hD1 hD3 hp)

/-- If `D2 ≠ 0` and `H ≠ 0` the states `0, …, 31` are pairwise distinct, state `32`
equals state `0`, and `W` is a simple `C₃₂`. -/
def cycle32_of_nonzero (χ : Character F m) (hm : Even m) (hm14 : 14 ≤ m) (hD1 : D1 χ ≠ 0)
    (hD2 : D2 χ ≠ 0) (hD3 : D3 χ ≠ 0) (hH : Hc χ ≠ 0) : MoveCycle χ 32 word where
  vertex := trace χ
  edge := fun i => trace_step χ hm i
  closed := (trace_32_eq_zero χ).symm
  simple :=
    trace_injective_on fullIndex collisions χ hm hm14
      coverFull
      (fun _p hp => dcoord_ne_of_collision χ hD1 hD2 hD3 hH hp)

/-- **The audited dichotomy.**  For an even `m ≥ 14` and a character `χ` with
`D1 ≠ 0`, `D3 ≠ 0`, the audited word `W` exhibits a simple cycle of length `16` or
`32` in the affine move system: a `C₁₆` on the states `0, …, 15` when `D2 = 0`, a
`C₁₆` on the states `12, …, 27` when `H = 0`, and a `C₃₂` on the states `0, …, 31`
otherwise. -/
theorem hasMoveCycle (χ : Character F m) (hm : Even m) (hm14 : 14 ≤ m) (hD1 : D1 χ ≠ 0)
    (hD3 : D3 χ ≠ 0) :
    Nonempty (MoveCycle χ 16 (fun i : Fin 16 => word ⟨i.1, by omega⟩)) ∨
      Nonempty (MoveCycle χ 16 (fun i : Fin 16 => word ⟨i.1 + 12, by omega⟩)) ∨
        Nonempty (MoveCycle χ 32 word) := by
  by_cases h2 : D2 χ = 0
  · exact Or.inl ⟨cycle16_of_D2 χ hm hm14 hD1 h2⟩
  · by_cases hh : Hc χ = 0
    · exact Or.inr (Or.inl ⟨cycle16_of_H χ hm hm14 hD1 hD3 hh⟩)
    · exact Or.inr (Or.inr ⟨cycle32_of_nonzero χ hm hm14 hD1 h2 hD3 hh⟩)

/-! ### A concrete model: `p = 29`, `m = 14`, `r = 4` -/

/-- The character `k ↦ 4 ^ k.val` for `p = 29`, `m = 14`.  Since `4` has multiplicative
order `14` modulo `29`, this is the intended instantiation `χ k = r ^ k.val`. -/
def character29 : Character (ZMod 29) 14 where
  toFun k := (4 : ZMod 29) ^ k.val
  map_zero := by decide
  map_add := by decide
  map_half := by decide

example : D1 character29 = 20 := by decide

example : D2 character29 = 23 := by decide

example : Hc character29 = 17 := by decide

/-- The concrete model satisfies the nonvanishing hypotheses. -/
theorem character29_nonzero :
    D1 character29 ≠ 0 ∧ D2 character29 ≠ 0 ∧ D3 character29 ≠ 0 ∧ Hc character29 ≠ 0 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- The concrete model realizes the `C₃₂` branch of the certificate: `p = 29`,
`m = 14`, `r = 4` has `D2 = 23 ≠ 0` and `H = 17 ≠ 0`, so the audited word is a simple
`C₃₂` on the affine states. -/
def character29_cycle32 : MoveCycle character29 32 word :=
  cycle32_of_nonzero character29 (by norm_num) (by norm_num) (by decide) (by decide) (by decide)
    (by decide)

/-- The concrete model jointly realizes all hypotheses and the resulting simple
thirty-two-cycle certificate. -/
theorem character29_cycle32_exists : Nonempty (MoveCycle character29 32 word) :=
  ⟨character29_cycle32⟩

end AffineFamily

end Erdos64
