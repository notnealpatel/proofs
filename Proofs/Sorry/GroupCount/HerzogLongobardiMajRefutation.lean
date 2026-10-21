/-
# Herzog–Longobardi–Maj Conjecture 7 is false: `ψ(G) ≤ ψ(H)|G:H|²` fails

## Source

M. Baniasad Azad, B. Khosravi, *On two conjectures about the sum of element
orders*, arXiv:1905.00815, final section "Counterexample for [HLM]-Conjecture".
The conjecture is Conjecture 7 of M. Herzog, P. Longobardi, M. Maj, *Two new
criteria for solvability of finite groups*, J. Algebra (2018).

* Notation (arXiv abstract / introduction): `ψ(G) = ∑_{g ∈ G} o(g)`, where
  `o(g)` is the order of `g`.
* [HLM]-Conjecture, verbatim: "If `H ≤ G`, then `ψ(G) ⩽ ψ(H) |G:H|^2`."
* Refutation, verbatim (final section): "Using the notation in GAP, let
  `G = SmallGroup(32,7) × C_m ≅ ((C_8 : C_2) : C_2) × C_m`, where `(m,2)=1`.
  We know that `SmallGroup(32,7)` has a maximal subgroup `M ≅ C_2 × D_8`.
  [...] Using GAP we have `ψ(SmallGroup(32,7)) = 167` and `ψ(M) = 39` and so
  `ψ(M)|G:M|^2 = 39·4 = 156`."

The paper's refutation is a GAP computation (case `m = 1` suffices).

## Claim formalized here (date: 2026-10-21)

The case `m = 1`, kernel-checked.  `G = SmallGroup(32,7)` is realized as the
iterated semidirect product `M₁₆ ⋊ C₂`, where
`M₁₆ = C₈ ⋊ C₂ = ⟨x, y | x⁸ = y² = 1, y x y⁻¹ = x⁵⟩` (the modular group) and
the outer generator `t` acts by `x ↦ x y`, `y ↦ y`.  A GAP search
(`IdGroup` of `⟨x, y, t | x⁸, y², t², y x y⁻¹ x⁻⁵, t x t⁻¹ (x y)⁻¹,
t y t⁻¹ y⁻¹⟩` equals `[32, 7]`) identifies this presentation with
`SmallGroup(32,7)`; that identification is computational evidence and is not
needed for the refutation, which only uses the concrete group below.
`H = {x^a y^b t^c : a even}` has index 2, `ψ(G) = 167`, `ψ(H) = 39`, and
`167 > 39 · 2² = 156`.

Status: the paper's own counterexample; proved here with no unfinished goals.
-/
import Mathlib

set_option autoImplicit false

namespace HerzogLongobardiMajRefutation

/-! ## The sum of element orders -/

/-- `ψ(G) = ∑_{g ∈ G} o(g)`, the sum of the element orders of a finite group
(Amiri–Jafarian Amiri–Isaacs; notation of arXiv:1905.00815). -/
noncomputable def psi (G : Type*) [Group G] [Fintype G] : ℕ :=
  ∑ g : G, orderOf g

/-- Computable candidate for the order of an element `g` with `g⁸ = 1`:
`1`, `2`, `4` or `8` according to the least of `g, g², g⁴` equal to `1`. -/
def twoPowOrd {M : Type*} [Monoid M] [DecidableEq M] (g : M) : ℕ :=
  if g = 1 then 1 else if g ^ 2 = 1 then 2 else if g ^ 4 = 1 then 4 else 8

/-- If `g⁸ = 1` then `orderOf g = twoPowOrd g`. -/
theorem orderOf_eq_twoPowOrd {M : Type*} [Monoid M] [DecidableEq M] (g : M)
    (h8 : g ^ 8 = 1) : orderOf g = twoPowOrd g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold twoPowOrd
  split_ifs with h1 h2 h4
  · exact orderOf_eq_one_iff.mpr h1
  · exact orderOf_eq_prime_pow (p := 2) (n := 0) (by simpa using h1) (by simpa using h2)
  · exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using h2) (by simpa using h4)
  · exact orderOf_eq_prime_pow (p := 2) (n := 2) (by simpa using h4) (by simpa using h8)

/-- `ψ` as a sum of `twoPowOrd`, for a group of exponent dividing 8. -/
theorem psi_eq_sum_twoPowOrd (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (h8 : ∀ g : G, g ^ 8 = 1) : psi G = ∑ g : G, twoPowOrd g :=
  Finset.sum_congr rfl fun g _ => orderOf_eq_twoPowOrd g (h8 g)

/-- Ground truth: `ψ(C₄) = 1 + 4 + 2 + 4 = 11`. -/
example : psi (Multiplicative (ZMod 4)) = 11 := by
  rw [psi_eq_sum_twoPowOrd _ (by decide)]
  decide

/-- Ground truth: `ψ(C₂ × C₂) = 1 + 2 + 2 + 2 = 7`. -/
example : psi (Multiplicative (ZMod 2 × ZMod 2)) = 7 := by
  rw [psi_eq_sum_twoPowOrd _ (by decide)]
  decide

/-! ## The modular group `M₁₆ = C₈ ⋊ C₂` -/

/-- The cyclic group `C₈ = ⟨x⟩`, written multiplicatively. -/
abbrev C8 := Multiplicative (ZMod 8)

/-- The cyclic group `C₂`, written multiplicatively. -/
abbrev C2 := Multiplicative (ZMod 2)

/-- The automorphism `x ↦ x⁵` of `C₈` (an involution). -/
def pow5 : MulAut C8 where
  toFun x := x ^ 5
  invFun x := x ^ 5
  left_inv x := by revert x; decide
  right_inv x := by revert x; decide
  map_mul' x y := by revert x y; decide

/-- The action `C₂ → Aut(C₈)` sending the generator to `x ↦ x⁵`. -/
def phi : C2 →* MulAut C8 where
  toFun b := pow5 ^ (Multiplicative.toAdd b).val
  map_one' := rfl
  map_mul' a b := by
    ext x
    revert a b x
    decide

/-- The modular group `M₁₆ = C₈ ⋊ C₂`; `⟨x^a, y^b⟩` stands for `x^a y^b`. -/
abbrev M16 := C8 ⋊[phi] C2

instance : Fintype M16 := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

/-- The map `x^a y^b ↦ (x y)^a y^b`, written in normal form: `(x y)^a` equals
`x^{3a} y^0` for even `a` and `x^{3a-2} y` for odd `a`. -/
def sigmaFun (m : M16) : M16 :=
  let a := Multiplicative.toAdd m.left
  let b := Multiplicative.toAdd m.right
  ⟨Multiplicative.ofAdd (if a.val % 2 = 0 then 3 * a else 3 * a - 2),
    Multiplicative.ofAdd ((a.val : ZMod 2) + b)⟩

/-- Ground truth for `sigmaFun`: `x ↦ x y` and `y ↦ y`. -/
example :
    sigmaFun ⟨Multiplicative.ofAdd 1, 1⟩ = ⟨Multiplicative.ofAdd 1, Multiplicative.ofAdd 1⟩ ∧
    sigmaFun ⟨1, Multiplicative.ofAdd 1⟩ = ⟨1, Multiplicative.ofAdd 1⟩ := by
  decide

/-- The involutive automorphism `σ : x ↦ x y, y ↦ y` of `M₁₆`. -/
def sigma : MulAut M16 where
  toFun := sigmaFun
  invFun := sigmaFun
  left_inv m := by revert m; decide
  right_inv m := by revert m; decide
  map_mul' m n := by revert m n; decide

/-- The action `C₂ → Aut(M₁₆)` sending the generator `t` to `σ`. -/
def rho : C2 →* MulAut M16 where
  toFun c := sigma ^ (Multiplicative.toAdd c).val
  map_one' := rfl
  map_mul' a b := by
    refine MulEquiv.ext fun m => ?_
    revert a b m
    decide

/-! ## The group `G = SmallGroup(32,7) = M₁₆ ⋊ C₂` and its subgroup `H ≅ C₂ × D₈` -/

/-- The witness group `G = M₁₆ ⋊ C₂ = ⟨x, y, t⟩` of order 32; `⟨⟨x^a, y^b⟩, t^c⟩`
stands for `x^a y^b t^c`. -/
abbrev G := M16 ⋊[rho] C2

instance : Fintype G := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

/-- The index-2 subgroup `H = {x^a y^b t^c : a even}` of `G` (isomorphic to
`C₂ × D₈`). -/
def H : Subgroup G where
  carrier := {g | (Multiplicative.toAdd g.left.left).val % 2 = 0}
  mul_mem' {g h} hg hh := by
    revert g h
    decide
  one_mem' := rfl
  inv_mem' {g} hg := by
    revert g
    decide

instance : DecidablePred (· ∈ H) := fun g =>
  inferInstanceAs (Decidable ((Multiplicative.toAdd g.left.left).val % 2 = 0))

/-- `|G| = 32`. -/
theorem card_G : Fintype.card G = 32 := by decide

/-- `|H| = 16`. -/
theorem card_H : Fintype.card H = 16 := by decide

/-- `[G : H] = 2`. -/
theorem index_H : H.index = 2 := by
  have h := H.card_mul_index
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_H, card_G] at h
  omega

/-- Every element of `G` satisfies `g⁸ = 1`. -/
theorem pow_eight_G : ∀ g : G, g ^ 8 = 1 := by decide

/-- Every element of `H` satisfies `h⁸ = 1`. -/
theorem pow_eight_H : ∀ h : H, h ^ 8 = 1 := by decide

/-- `ψ(G) = 167` (arXiv:1905.00815, final section: `ψ(SmallGroup(32,7)) = 167`). -/
theorem psi_G : psi G = 167 := by
  rw [psi_eq_sum_twoPowOrd G pow_eight_G]
  decide

/-- `ψ(H) = 39` (arXiv:1905.00815, final section: `ψ(M) = 39` for
`M ≅ C₂ × D₈`). -/
theorem psi_H : psi H = 39 := by
  rw [psi_eq_sum_twoPowOrd H pow_eight_H]
  decide

/-- Ground truth for the presentation: in `M₁₆`, `y x y⁻¹ = x⁵`, with
`x = ⟨x, 1⟩` and `y = ⟨1, y⟩`. -/
example :
    (⟨1, Multiplicative.ofAdd 1⟩ : M16) * ⟨Multiplicative.ofAdd 1, 1⟩ *
        (⟨1, Multiplicative.ofAdd 1⟩ : M16)⁻¹ = ⟨Multiplicative.ofAdd 5, 1⟩ := by
  decide

/-- Ground truth for the presentation: in `G`, `t x t⁻¹ = x y`. -/
example :
    (⟨1, Multiplicative.ofAdd 1⟩ : G) * ⟨⟨Multiplicative.ofAdd 1, 1⟩, 1⟩ *
        (⟨1, Multiplicative.ofAdd 1⟩ : G)⁻¹ =
      ⟨⟨Multiplicative.ofAdd 1, Multiplicative.ofAdd 1⟩, 1⟩ := by
  decide

/-- `G` is not abelian (sanity check on the witness). -/
example : ¬ ∀ a b : G, a * b = b * a := by decide

/-- Ground truth: `G` has exactly 16 elements of order 8 (GAP order statistics
of `SmallGroup(32,7)`: `{1:1, 2:11, 4:4, 8:16}`). -/
example : (Finset.univ.filter fun g : G => twoPowOrd g = 8).card = 16 := by decide

/-- **The concrete counterexample** (arXiv:1905.00815, final section):
`H ≤ G` with `[G : H] = 2`, `ψ(G) = 167`, `ψ(H) = 39`, and
`ψ(H) · |G:H|² = 156 < 167 = ψ(G)`. -/
theorem psi_H_mul_index_sq_lt_psi_G : psi H * H.index ^ 2 < psi G := by
  rw [psi_H, psi_G, index_H]
  norm_num

/-- **The Herzog–Longobardi–Maj Conjecture 7 is false** (J. Algebra 2018,
Conjecture 7; refuted in arXiv:1905.00815, final section).  The conjecture
asserts `ψ(G) ≤ ψ(H) |G:H|²` for every subgroup `H` of every finite group `G`,
where `ψ(G) = ∑_{g ∈ G} o(g)`; it fails for `G = SmallGroup(32,7)` and its
maximal subgroup `H ≅ C₂ × D₈`. -/
theorem hlm_conjecture_false :
    ¬ ∀ (G : Type) [Group G] [Fintype G] (H : Subgroup G) [Fintype H],
      psi G ≤ psi H * H.index ^ 2 := by
  intro hconj
  have hle := hconj G H
  have hlt := psi_H_mul_index_sq_lt_psi_G
  omega

/-- Explicit form of the refutation: there is a group `G` of order 32 with a
subgroup `H` of index 2 such that `ψ(G) = 167`, `ψ(H) = 39`, hence
`ψ(H) |G:H|² < ψ(G)`. -/
theorem exists_counterexample :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G) (H : Subgroup G) (_ : Fintype H),
      Fintype.card G = 32 ∧ H.index = 2 ∧ psi G = 167 ∧ psi H = 39 ∧
        psi H * H.index ^ 2 < psi G :=
  ⟨G, inferInstance, inferInstance, H, inferInstance, card_G, index_H, psi_G, psi_H,
    psi_H_mul_index_sq_lt_psi_G⟩

end HerzogLongobardiMajRefutation
