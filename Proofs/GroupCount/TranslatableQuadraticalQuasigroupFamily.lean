/-
# Self-dual quadratical quasigroups of odd square order

W. A. Dudek and R. A. R. Monzo, *Translatable quadratical quasigroups*,
arXiv:1708.08830, Section 2 and the final section, Problem 3: are there
self-dual quadratical groupoids of order greater than nine?

For each odd `r`, this file constructs a family on `ZMod r × ZMod r`:
`x · y = φ x + ψ y`, where `J(u,v) = (-v,u)`, `φ = (1+J)/2`, and
`ψ = (1-J)/2`. The operation is a quasigroup satisfying Volenec's identity
`xy · x = zx · yz`. Conjugation `(u,v) ↦ (u,-v)` is an isomorphism to its
dual. The order is `r²`, so `r = 5` gives an example of order 25 and the
family has arbitrarily large finite orders. No translatability assertion
is made here.

Both left and right equations have unique solutions, implying the source's
right-solvability requirement. Self-duality means a bijection `e` with
`e (x · y) = e y · e x`. The construction is verified directly, without
using the representation theorem. Statements requiring division by two
assume `Odd r`, making `(2 : ZMod r)⁻¹` a genuine inverse. Identification
of the order-nine member with the paper's `Q2` uses the source's uniqueness
statement, not an explicit isomorphism formalized here.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.TranslatableQuadraticalQuasigroupFamily

/-! ## Groupoid notions -/

/-- A groupoid `(G, mul)` is a *quasigroup* if for all `a b` both equations
`a · x = b` and `y · a = b` have unique solutions. -/
def IsQuasigroup {G : Type*} (mul : G → G → G) : Prop :=
  ∀ a b : G, (∃! x, mul a x = b) ∧ (∃! y, mul y a = b)

/-- Volenec's identity (A): `xy · x = zx · yz` for all `x y z`. -/
def SatisfiesA {G : Type*} (mul : G → G → G) : Prop :=
  ∀ x y z : G, mul (mul x y) x = mul (mul z x) (mul y z)

/-- A *quadratical quasigroup*: a quasigroup satisfying identity (A).  Since a
quasigroup is right solvable, this is (at least) a quadratical groupoid in
Volenec's sense. -/
def IsQuadraticalQuasigroup {G : Type*} (mul : G → G → G) : Prop :=
  IsQuasigroup mul ∧ SatisfiesA mul

/-- A groupoid is *self-dual* if it is isomorphic to its dual `a * b = b · a`,
i.e. there is a bijection `e` with `e (x · y) = e y · e x`. -/
def IsSelfDual {G : Type*} (mul : G → G → G) : Prop :=
  ∃ e : G ≃ G, ∀ x y : G, e (mul x y) = mul (e y) (e x)

/-! ## The model over a commutative ring with a half -/

section Ring

variable {R : Type*} [CommRing R]

/-- `φ = (1 + J)/2` on `R × R`, with `J (u, v) = (-v, u)` and `h` playing `1/2`. -/
def phi (h : R) (x : R × R) : R × R := (h * (x.1 - x.2), h * (x.2 + x.1))

/-- `ψ = (1 - J)/2` on `R × R`, with `J (u, v) = (-v, u)` and `h` playing `1/2`. -/
def psi (h : R) (x : R × R) : R × R := (h * (x.1 + x.2), h * (x.2 - x.1))

/-- The product `x · y = φ x + ψ y` on `R × R`. -/
def gmul (h : R) (x y : R × R) : R × R := phi h x + psi h y

/-- `1 - J`, the inverse of `φ` when `2 h = 1`. -/
def phiInv (x : R × R) : R × R := (x.1 + x.2, x.2 - x.1)

/-- `1 + J`, the inverse of `ψ` when `2 h = 1`. -/
def psiInv (x : R × R) : R × R := (x.1 - x.2, x.2 + x.1)

/-- Conjugation `(u, v) ↦ (u, -v)` as an involutive bijection of `R × R`. -/
def conj : R × R ≃ R × R where
  toFun x := (x.1, -x.2)
  invFun x := (x.1, -x.2)
  left_inv x := by simp
  right_inv x := by simp

/-- Identity (A) holds for `gmul h` whenever `2 h = 1`. -/
theorem gmul_satisfiesA (h : R) (h2 : 2 * h = 1) : SatisfiesA (gmul h) := by
  intro x y z
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  obtain ⟨z1, z2⟩ := z
  simp only [gmul, phi, psi, Prod.mk_add_mk, Prod.mk.injEq]
  constructor
  · linear_combination (-h * x1 - h * x2) * h2
  · linear_combination (h * x1 - h * x2) * h2

/-- `phi h ∘ phiInv = id` when `2 h = 1`. -/
theorem phi_phiInv (h : R) (h2 : 2 * h = 1) (x : R × R) : phi h (phiInv x) = x := by
  obtain ⟨x1, x2⟩ := x
  simp only [phi, phiInv, Prod.mk.injEq]
  constructor
  · linear_combination x1 * h2
  · linear_combination x2 * h2

/-- `phiInv ∘ phi h = id` when `2 h = 1`. -/
theorem phiInv_phi (h : R) (h2 : 2 * h = 1) (x : R × R) : phiInv (phi h x) = x := by
  obtain ⟨x1, x2⟩ := x
  simp only [phi, phiInv, Prod.mk.injEq]
  constructor
  · linear_combination x1 * h2
  · linear_combination x2 * h2

/-- `psi h ∘ psiInv = id` when `2 h = 1`. -/
theorem psi_psiInv (h : R) (h2 : 2 * h = 1) (x : R × R) : psi h (psiInv x) = x := by
  obtain ⟨x1, x2⟩ := x
  simp only [psi, psiInv, Prod.mk.injEq]
  constructor
  · linear_combination x1 * h2
  · linear_combination x2 * h2

/-- `psiInv ∘ psi h = id` when `2 h = 1`. -/
theorem psiInv_psi (h : R) (h2 : 2 * h = 1) (x : R × R) : psiInv (psi h x) = x := by
  obtain ⟨x1, x2⟩ := x
  simp only [psi, psiInv, Prod.mk.injEq]
  constructor
  · linear_combination x1 * h2
  · linear_combination x2 * h2

/-- `gmul h` is a quasigroup whenever `2 h = 1`. -/
theorem gmul_isQuasigroup (h : R) (h2 : 2 * h = 1) : IsQuasigroup (gmul h) := by
  intro a b
  constructor
  · refine ⟨psiInv (b - phi h a), ?_, ?_⟩
    · simp only [gmul, psi_psiInv h h2, add_sub_cancel]
    · intro x hx
      rw [← hx, gmul, add_sub_cancel_left, psiInv_psi h h2]
  · refine ⟨phiInv (b - psi h a), ?_, ?_⟩
    · simp only [gmul, phi_phiInv h h2, sub_add_cancel]
    · intro y hy
      rw [← hy, gmul, add_sub_cancel_right, phiInv_phi h h2]

/-- Conjugation is an isomorphism from `gmul h` onto its dual (no hypothesis on `h`). -/
theorem conj_gmul (h : R) (x y : R × R) :
    conj (gmul h x y) = gmul h (conj y) (conj x) := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  simp only [conj, Equiv.coe_fn_mk, gmul, phi, psi, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> ring

/-- `gmul h` is self-dual, via conjugation. -/
theorem gmul_isSelfDual (h : R) : IsSelfDual (gmul h) := ⟨conj, conj_gmul h⟩

end Ring

/-! ## The `ZMod r × ZMod r` family -/

/-- The product `x · y = φ x + ψ y` on `ZMod r × ZMod r`, with `φ = (1 + J)/2`,
`ψ = (1 - J)/2`, `J (u, v) = (-v, u)`; `1/2` is `(2 : ZMod r)⁻¹`, a genuine
inverse exactly when `r` is odd. -/
def qmul (r : ℕ) (x y : ZMod r × ZMod r) : ZMod r × ZMod r :=
  gmul ((2 : ZMod r)⁻¹) x y

/-- For odd `r`, `2 · 2⁻¹ = 1` in `ZMod r`. -/
theorem two_mul_inv_two (r : ℕ) (hr : Odd r) : (2 : ZMod r) * (2 : ZMod r)⁻¹ = 1 := by
  have hc : Nat.Coprime 2 r := Nat.coprime_two_left.2 hr
  exact_mod_cast ZMod.coe_mul_inv_eq_one 2 hc

/-- The groupoid `(ZMod r × ZMod r, qmul r)` has order `r²`. -/
theorem card_qmul_carrier (r : ℕ) : Nat.card (ZMod r × ZMod r) = r ^ 2 := by
  simp [Nat.card_prod, sq]

/-- **Family theorem.** For every odd `r`, `(ZMod r × ZMod r, x · y = φ x + ψ y)`
is a quadratical quasigroup (quasigroup satisfying Volenec's identity (A)) of
order `r²` that is isomorphic to its dual. -/
theorem qmul_quadratical_selfDual (r : ℕ) (hr : Odd r) :
    IsQuadraticalQuasigroup (qmul r) ∧ IsSelfDual (qmul r) := by
  have h2 := two_mul_inv_two r hr
  exact ⟨⟨gmul_isQuasigroup _ h2, gmul_satisfiesA _ h2⟩, gmul_isSelfDual _⟩

/-! ## Examples -/

/-- In `ZMod 3`, `2⁻¹ = 2`, so `qmul 3 = gmul 2`. -/
theorem qmul_three : qmul 3 = gmul (2 : ZMod 3) := by
  have hinv : (2 : ZMod 3)⁻¹ = 2 := ZMod.inv_eq_of_mul_eq_one 3 2 2 (by decide)
  funext x y
  rw [qmul, hinv]

/-- In `ZMod 5`, `2⁻¹ = 3`, so `qmul 5 = gmul 3`. -/
theorem qmul_five : qmul 5 = gmul (3 : ZMod 5) := by
  have hinv : (2 : ZMod 5)⁻¹ = 3 := ZMod.inv_eq_of_mul_eq_one 5 2 3 (by decide)
  funext x y
  rw [qmul, hinv]

/-- A sample product in the order-9 case: `(1,0) · (0,0) = (2,2)` in `ZMod 3`. -/
example : qmul 3 (1, 0) (0, 0) = (2, 2) := by rw [qmul_three]; decide

/-- In `ZMod 5`: `(1,0) · (0,0) = (3,3)` and `(0,0) · (1,0) = (3,2)`. -/
example : qmul 5 (1, 0) (0, 0) = (3, 3) ∧ qmul 5 (0, 0) (1, 0) = (3, 2) := by
  rw [qmul_five]; decide

/-- The order-9 member (`r = 3`, the paper's `Q2`) is idempotent. -/
example : ∀ x : ZMod 3 × ZMod 3, qmul 3 x x = x := by rw [qmul_three]; decide

/-- The order-9 member satisfies identity (A), checked exhaustively. -/
example : SatisfiesA (qmul 3) := by rw [qmul_three]; unfold SatisfiesA; decide

/-- The order-9 member is not commutative, so self-duality is not the identity map. -/
example : qmul 3 (1, 0) (0, 0) ≠ qmul 3 (0, 0) (1, 0) := by rw [qmul_three]; decide

/-- The paper's `Q1 ≅ (ZMod 5, 4x + 2y)` satisfies identity (A) (sanity check of
the transcription of (A)). -/
example : SatisfiesA (fun x y : ZMod 5 => 4 * x + 2 * y) := by unfold SatisfiesA; decide

/-- Identity (A) is not vacuous: it fails for `(ZMod 5, x + y)`. -/
example : ¬ SatisfiesA (fun x y : ZMod 5 => x + y) := by unfold SatisfiesA; decide

/-! ## Answer to Problem 3 -/

/-- **Problem 3 (Dudek–Monzo, arXiv:1708.08830, §"Open questions and problems").**
There are self-dual quadratical quasigroups of order greater than 9; indeed of
arbitrarily large finite order: for every `N` there is an odd `r` with
`N < r²` such that `(ZMod r × ZMod r, qmul r)` (finite, of order `r²`) is a
self-dual quadratical quasigroup. -/
theorem problem3 (N : ℕ) :
    ∃ r : ℕ, Odd r ∧ N < Nat.card (ZMod r × ZMod r) ∧
      IsQuadraticalQuasigroup (qmul r) ∧ IsSelfDual (qmul r) := by
  refine ⟨2 * N + 1, odd_two_mul_add_one N, ?_, qmul_quadratical_selfDual _ (odd_two_mul_add_one N)⟩
  rw [card_qmul_carrier]
  nlinarith

/-- **Problem 3, order 25.** The case `r = 5`: a self-dual quadratical
quasigroup of order 25 > 9. -/
theorem problem3_order25 :
    Nat.card (ZMod 5 × ZMod 5) = 25 ∧ 9 < Nat.card (ZMod 5 × ZMod 5) ∧
      IsQuadraticalQuasigroup (qmul 5) ∧ IsSelfDual (qmul 5) := by
  have hcard : Nat.card (ZMod 5 × ZMod 5) = 25 := card_qmul_carrier 5
  exact ⟨hcard, by omega, qmul_quadratical_selfDual 5 (by decide)⟩

end Candidates.TranslatableQuadraticalQuasigroupFamily
