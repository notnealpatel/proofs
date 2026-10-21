/-
# Idempotents of the integral quandle ring of an odd dihedral quandle

## Source

Dilpreet Kaur and Pushpendra Singh, *A note on idempotents in quandle rings*,
arXiv:2609.09183. Recorded 2026-10-21.

* Section 1, Conjecture 1.1 (= Elhamdadi–Nelson–Swain–Ditzler, Conjecture
  3.10): "The integral quandle ring of a semi-latin quandle has only trivial
  idempotents. In particular, the integral quandle ring of a finite latin
  quandle has only trivial idempotents." (False in general: Jabłonowski's
  counterexample over `Aff(ℤ_37, 18x)`, Section 4 of the paper.)
* Section 2, setup: "The quandle operation on $\mathbb Z_n$ is
  $x\triangleright y=2y-x$. The quandle ring $\mathbb Z[\mathcal R_n]$ is a
  free $\mathbb Z$-module with basis $\{e_x\}$ with the multiplication on basis
  elements given as $e_xe_y=e_{x\triangleright y}=e_{2y-x}$."
* Section 2, Theorem (unnumbered, Theorem 2.5 in the numbering of the
  section): "The set of idempotents of $\mathbb Z[\mathcal R_n]$ for $n$ odd is
  $\{0,e_x\;; x\in \mathcal R_n\}$."

Status: proved in the paper (by a discrete Fourier transform argument).
Every statement below is kernel-checked here.

## Formalization notes

* An element $u=\sum_x a_xe_x$ of $\mathbb Z[\mathcal R_n]$ is modelled by its
  coefficient function `ZMod n → ℤ` (the quandle is finite). The product is the
  bilinear extension of $e_xe_y=e_{x\triangleright y}$, where
  $x\triangleright y = 2y-x$ is Mathlib's `Quandle.dihedralAct n y x`
  (Mathlib writes the dihedral quandle with the left action
  `a ◃ b = 2 * a - b`, so the paper's $x\triangleright y$ is `y ◃ x`).
* The proof avoids complex Fourier analysis. In the commutative group ring
  `ℤ[ZMod n]` let `A = ∑ a_x X^x`, `A* = A(X⁻¹)`, `σ A = A(X²)`. Idempotency is
  `A = A* · σ A`. Then `B = A · A*` satisfies `B = B · σ B`, and since `σ` has
  finite order (2 is a unit mod odd `n`), `B² = B`. As `B* = B`, the constant
  coefficient `S = B₀ = ∑ a_x²` equals `(B · B*)₀ = ∑_g B_g² ≥ S²`, so
  `S ∈ {0, 1}`; the case `a = -e_x` is excluded by the idempotency equation.
  This replaces the paper's Lemmas 2.2–2.4 and the Parseval count.
-/
import Mathlib

set_option autoImplicit false

namespace DihedralQuandleIdempotents

open AddMonoidAlgebra

variable {n : ℕ}

/-! ## The quandle ring `ℤ[R_n]` on coefficient vectors -/

/-- The product of the integral quandle ring `ℤ[R_n]` of the dihedral quandle
`R_n = (ZMod n, x ▷ y = 2y - x)`, on coefficient functions: the bilinear
extension of `e_x e_y = e_{x ▷ y}`, so that
`(u v)_z = ∑_{x, y : x ▷ y = z} u_x v_y`. Here `x ▷ y` is
`Quandle.dihedralAct n y x = 2 * y - x`. -/
def quandleRingMul [NeZero n] (u v : ZMod n → ℤ) : ZMod n → ℤ :=
  fun z => ∑ x, ∑ y, if Quandle.dihedralAct n y x = z then u x * v y else 0

/-- Mathlib's dihedral action, read in the paper's convention: `x ▷ y = 2y - x`. -/
theorem dihedralAct_eq (x y : ZMod n) : Quandle.dihedralAct n y x = 2 * y - x := rfl

/-- On basis elements the product is `e_x e_y = e_{2y - x}` (paper, Section 2). -/
theorem quandleRingMul_single [NeZero n] (x y : ZMod n) :
    quandleRingMul (Pi.single x 1) (Pi.single y 1) = Pi.single (2 * y - x) 1 := by
  funext z
  rw [quandleRingMul, Finset.sum_eq_single x, Finset.sum_eq_single y]
  · simp only [dihedralAct_eq, Pi.single_eq_same, mul_one, Pi.single_apply, eq_comm]
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ y) h
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- Ground truth in `ℤ[R_3]`: `e_0 e_1 = e_2`. -/
example : quandleRingMul (n := 3) (Pi.single 0 1) (Pi.single 1 1) = Pi.single 2 1 := by
  rw [quandleRingMul_single]; rfl

/-- Ground truth in `ℤ[R_5]`: `e_4 e_1 = e_3` (`2·1 - 4 = -2 = 3` in `ZMod 5`). -/
example : quandleRingMul (n := 5) (Pi.single 4 1) (Pi.single 1 1) = Pi.single 3 1 := by
  rw [quandleRingMul_single]; rfl

/-- The coefficient of `e_z` in `u²` is `∑_y u_{2y - z} u_y` (paper, Section 2). -/
theorem quandleRingMul_self_apply [NeZero n] (u : ZMod n → ℤ) (z : ZMod n) :
    quandleRingMul u u z = ∑ y, u (2 * y - z) * u y := by
  rw [quandleRingMul, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hiff : ∀ x : ZMod n, (Quandle.dihedralAct n y x = z) ↔ 2 * y - z = x := by
    intro x
    rw [dihedralAct_eq]
    constructor <;> intro hx
    · rw [← hx]; ring
    · rw [← hx]; ring
  simp only [hiff, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Every `e_x` is idempotent in `ℤ[R_n]` (the quandle is idempotent: `x ▷ x = x`). -/
theorem quandleRingMul_single_self [NeZero n] (x : ZMod n) :
    quandleRingMul (Pi.single x 1) (Pi.single x 1) = Pi.single x 1 := by
  rw [quandleRingMul_single, two_mul, add_sub_cancel_right]

/-- Oddness is needed: in `ℤ[R_2]` (where `x ▷ y = x`) the element `2e_0 - e_1`
is a nonzero idempotent different from every `e_x`. -/
example : quandleRingMul (n := 2) (fun x => if x = 0 then 2 else -1)
    (fun x => if x = 0 then 2 else -1) = fun x => if x = 0 then 2 else -1 := by
  decide

/-! ## The group ring `ℤ[ZMod n]` and the scaling homomorphisms -/

/-- The ring endomorphism `X^x ↦ X^{c x}` of the group ring `ℤ[ZMod n]`. -/
noncomputable def scale (c : ZMod n) :
    AddMonoidAlgebra ℤ (ZMod n) →+* AddMonoidAlgebra ℤ (ZMod n) :=
  AddMonoidAlgebra.mapDomainRingHom ℤ (AddMonoidHom.mulLeft c)

/-- `scale c` on a monomial. -/
theorem scale_single (c x : ZMod n) (r : ℤ) : scale c (single x r) = single (c * x) r := by
  simp [scale, mapDomain_single]

/-- Scaling is multiplicative in the scale factor. -/
theorem scale_scale (c d : ZMod n) (X : AddMonoidAlgebra ℤ (ZMod n)) :
    scale c (scale d X) = scale (c * d) X := by
  have hhom : (AddMonoidHom.mulLeft c).comp (AddMonoidHom.mulLeft d) =
      AddMonoidHom.mulLeft (c * d) := by
    ext x; simp [mul_assoc]
  have hcomp := congrArg (fun φ => φ X) (AddMonoidAlgebra.mapDomainRingHom_comp (R := ℤ)
    (AddMonoidHom.mulLeft c) (AddMonoidHom.mulLeft d))
  simp only [RingHom.comp_apply] at hcomp
  rw [scale, scale, ← hcomp, hhom]
  rfl

/-- Scaling by `1` is the identity. -/
theorem scale_one (X : AddMonoidAlgebra ℤ (ZMod n)) : scale 1 X = X := by
  have hid : AddMonoidHom.mulLeft (1 : ZMod n) = AddMonoidHom.id _ := by ext x; simp
  rw [scale, hid, AddMonoidAlgebra.mapDomainRingHom_id]
  rfl

/-- If `X = X · σX` for the scaling `σ = scale c`, then
`X · σX · σ²X ⋯ σ^m X = X` for every `m`. -/
theorem prod_scale_pow_eq_self (c : ZMod n) (m : ℕ) : ∀ X : AddMonoidAlgebra ℤ (ZMod n),
    X * scale c X = X → ∏ j ∈ Finset.range (m + 1), scale (c ^ j) X = X := by
  induction m with
  | zero => intro X _; simp [scale_one]
  | succ m ih =>
    intro X hX
    have hY : scale c X * scale c (scale c X) = scale c X := by rw [← map_mul, hX]
    have hkey := ih (scale c X) hY
    rw [Finset.prod_range_succ']
    simp only [pow_zero, scale_one]
    have hprod : ∏ j ∈ Finset.range (m + 1), scale (c ^ (j + 1)) X =
        ∏ j ∈ Finset.range (m + 1), scale (c ^ j) (scale c X) := by
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [scale_scale, pow_succ]
    rw [hprod, hkey, mul_comm, hX]

/-- If `c` has finite multiplicative order and `X = X · (scale c X)`, then `X` is
idempotent. -/
theorem mul_self_eq_of_mul_scale (c : ZMod n) (k : ℕ) (hk : 0 < k) (hc : c ^ k = 1)
    (X : AddMonoidAlgebra ℤ (ZMod n)) (hX : X * scale c X = X) : X * X = X := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hshort := prod_scale_pow_eq_self c k' X hX
  have hlong := prod_scale_pow_eq_self c (k' + 1) X hX
  rw [Finset.prod_range_succ, hshort, hc, scale_one] at hlong
  exact hlong

/-! ## Coefficient computations -/

section Coeff

variable [NeZero n]

/-- The group-ring element `∑_x a_x X^x` with coefficient function `a`. -/
noncomputable def embed (a : ZMod n → ℤ) : AddMonoidAlgebra ℤ (ZMod n) := ∑ x, single x (a x)

/-- The coefficients of `embed a` are `a`. -/
theorem coeff_embed (a : ZMod n → ℤ) (z : ZMod n) : (embed a).coeff z = a z := by
  simp [embed, coeff_sum, coeff_single, Finsupp.single_apply]

/-- Every group-ring element is the `embed` of its coefficient function. -/
theorem embed_coeff (F : AddMonoidAlgebra ℤ (ZMod n)) : embed (fun g => F.coeff g) = F := by
  ext z; simp [coeff_embed]

/-- Coefficients of a product of two scaled elements. -/
theorem coeff_scale_mul_scale (a b : ZMod n → ℤ) (c d z : ZMod n) :
    (scale c (embed a) * scale d (embed b)).coeff z =
      ∑ x, ∑ y, if c * x + d * y = z then a x * b y else 0 := by
  simp only [embed, map_sum, scale_single, Finset.sum_mul_sum, single_mul_single, coeff_sum,
    coeff_single, Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- The constant coefficient of `A · A*` is `∑_x a_x²`. -/
theorem coeff_zero_mul_scale_neg_one (a : ZMod n → ℤ) :
    (embed a * scale (-1) (embed a)).coeff 0 = ∑ x, a x ^ 2 := by
  have hone : embed a = scale 1 (embed a) := (scale_one _).symm
  rw [show embed a * scale (-1) (embed a) = scale 1 (embed a) * scale (-1) (embed a) by
    rw [← hone], coeff_scale_mul_scale]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hiff : ∀ y : ZMod n, (1 * x + -1 * y = 0) ↔ x = y := by
    intro y; constructor <;> intro hy
    · linear_combination hy
    · rw [hy]; ring
  simp only [hiff, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

/-- The coefficients of `A* · σA` are the coefficients of `u²` in `ℤ[R_n]`. -/
theorem coeff_scale_neg_one_mul_scale_two (a : ZMod n → ℤ) (z : ZMod n) :
    (scale (-1) (embed a) * scale 2 (embed a)).coeff z = quandleRingMul a a z := by
  rw [coeff_scale_mul_scale, quandleRingMul_self_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hiff : ∀ x : ZMod n, (-1 * x + 2 * y = z) ↔ 2 * y - z = x := by
    intro x; constructor <;> intro hx
    · linear_combination hx
    · rw [← hx]; ring
  simp only [hiff, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end Coeff

/-! ## The main theorem -/

/-- Idempotents of `ℤ[R_n]`, `n` odd, have `∑_x a_x² ∈ {0, 1}`. -/
theorem sum_sq_le_one_of_idempotent [NeZero n] (hn : Odd n) (a : ZMod n → ℤ)
    (h : quandleRingMul a a = a) : ∑ x, a x ^ 2 ≤ 1 := by
  set A := embed a with hAdef
  -- idempotency in the group ring: `A = A* · σA`
  have hA : A = scale (-1) A * scale 2 A := by
    ext z
    rw [coeff_scale_neg_one_mul_scale_two, h, coeff_embed]
  -- apply `*` to it: `A* = A · σA*`
  have hA' : scale (-1) A = A * scale (-2) A := by
    conv_lhs => rw [hA]
    rw [map_mul, scale_scale, scale_scale]
    norm_num [scale_one]
  set B := A * scale (-1) A with hBdef
  have hBstar : scale (-1) B = B := by
    rw [hBdef, map_mul, scale_scale]
    norm_num [scale_one, mul_comm]
  have hBsigma : B * scale 2 B = B := by
    have hsB : scale 2 B = scale 2 A * scale (-2) A := by
      rw [hBdef, map_mul, scale_scale]
      norm_num
    calc B * scale 2 B = (scale (-1) A * scale 2 A) * (A * scale (-2) A) := by
          rw [hsB, hBdef]; ring
      _ = B := by rw [← hA, ← hA']
  -- `2` has finite multiplicative order modulo the odd number `n`
  have hcop : Nat.Coprime 2 n := Nat.coprime_two_left.mpr hn
  set u : (ZMod n)ˣ := ZMod.unitOfCoprime 2 hcop
  have hu : (u : ZMod n) = 2 := by simp [u, ZMod.coe_unitOfCoprime]
  have hpow : (2 : ZMod n) ^ orderOf u = 1 := by
    rw [← hu, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  have hBB : B * B = B :=
    mul_self_eq_of_mul_scale 2 (orderOf u) (orderOf_pos u) hpow B hBsigma
  -- the trace inequality `S² ≤ S`
  have hS : B.coeff 0 = ∑ x, a x ^ 2 := by
    rw [hBdef, hAdef, coeff_zero_mul_scale_neg_one]
  have hSsq : B.coeff 0 = ∑ g, B.coeff g ^ 2 := by
    calc B.coeff 0 = (B * scale (-1) B).coeff 0 := by rw [hBstar, hBB]
      _ = ∑ g, B.coeff g ^ 2 := by
          rw [← embed_coeff B, coeff_zero_mul_scale_neg_one]
          simp only [coeff_embed]
  have hle : B.coeff 0 ^ 2 ≤ B.coeff 0 := by
    conv_rhs => rw [hSsq]
    exact Finset.single_le_sum (f := fun g => B.coeff g ^ 2) (fun g _ => sq_nonneg _)
      (Finset.mem_univ 0)
  rw [← hS]
  nlinarith

/-- **Kaur–Singh, arXiv:2609.09183, Section 2, Theorem.** "The set of
idempotents of `ℤ[R_n]` for `n` odd is `{0, e_x ; x ∈ R_n}`."

For odd `n`, an element `u` of the integral quandle ring of the dihedral quandle
`R_n` (coefficient function `ZMod n → ℤ`, product `e_x e_y = e_{2y - x}`)
satisfies `u² = u` if and only if `u = 0` or `u = e_x` for some `x`. -/
theorem idempotent_iff [NeZero n] (hn : Odd n) (u : ZMod n → ℤ) :
    quandleRingMul u u = u ↔ u = 0 ∨ ∃ x, u = Pi.single x 1 := by
  constructor
  · intro h
    have hsum := sum_sq_le_one_of_idempotent hn u h
    by_cases hzero : ∀ x, u x = 0
    · exact Or.inl (funext hzero)
    · push Not at hzero
      obtain ⟨x, hx⟩ := hzero
      have hsplit : ∑ y, u y ^ 2 = u x ^ 2 + ∑ y ∈ Finset.univ.erase x, u y ^ 2 :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ x)).symm
      have hxsq : 1 ≤ u x ^ 2 := by
        have hpos : 0 < u x ^ 2 := by positivity
        omega
      have hrest_nonneg : 0 ≤ ∑ y ∈ Finset.univ.erase x, u y ^ 2 :=
        Finset.sum_nonneg fun y _ => sq_nonneg _
      have hrest : ∑ y ∈ Finset.univ.erase x, u y ^ 2 = 0 := by omega
      have hother : ∀ y, y ≠ x → u y = 0 := by
        intro y hy
        have hy0 := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => sq_nonneg (u y))).mp hrest y
          (Finset.mem_erase.mpr ⟨hy, Finset.mem_univ y⟩)
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hy0
      -- the idempotency equation at `z = x` forces `u x = 1`
      have hux : u x = u x * u x := by
        have hz := congrFun h x
        rw [quandleRingMul_self_apply, Finset.sum_eq_single x] at hz
        · rw [two_mul, add_sub_cancel_right] at hz
          exact hz.symm
        · intro y _ hy
          rw [hother y hy, mul_zero]
        · intro hxmem; exact absurd (Finset.mem_univ x) hxmem
      have hx1 : u x = 1 := by
        have hmul : u x * (u x - 1) = 0 := by linear_combination -hux
        rcases mul_eq_zero.mp hmul with h0 | h1
        · exact absurd h0 hx
        · linear_combination h1
      refine Or.inr ⟨x, funext fun y => ?_⟩
      by_cases hyx : y = x
      · rw [hyx, hx1, Pi.single_eq_same]
      · rw [hother y hyx, Pi.single_eq_of_ne hyx]
  · rintro (rfl | ⟨x, rfl⟩)
    · funext z; simp [quandleRingMul]
    · exact quandleRingMul_single_self x

/-- The coefficient form used in the paper and in the target specification: for
odd `n`, an integer solution `a : ZMod n → ℤ` of the system
`a_z = ∑_y a_{2y - z} a_y` (all `z`) is `0` or a basis vector `e_x`. -/
theorem eq_zero_or_eq_single_of_forall_eq_sum [NeZero n] (hn : Odd n) (a : ZMod n → ℤ)
    (h : ∀ z, a z = ∑ y, a (2 * y - z) * a y) : a = 0 ∨ ∃ x, a = Pi.single x 1 := by
  refine (idempotent_iff hn a).mp (funext fun z => ?_)
  rw [quandleRingMul_self_apply, h z]

/-- Non-vacuity: in `ℤ[R_3]` the idempotent `e_1` is a nonzero solution. -/
example : quandleRingMul (n := 3) (Pi.single 1 1) (Pi.single 1 1) = Pi.single 1 1 :=
  quandleRingMul_single_self 1

end DihedralQuandleIdempotents
