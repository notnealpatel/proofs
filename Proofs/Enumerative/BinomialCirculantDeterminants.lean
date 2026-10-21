/-
# Determinants of binomial-related circulant matrices

## Source

arXiv:1804.01196, T. Jantaramas, S. Jitman, P. Kaewsaard,
"Determinants of Binomial-Related Circulant Matrices".
Recorded 2026-10-21.

* Section 2.1 defines the right circulant `rcir(a)` (row `i` is `a` rotated
  `i` places to the right, so entry `(i, j)` is `a_{j - i mod n}`) and the
  left circulant `lcir(a)` (entry `(i, j)` is `a_{i + j mod n}`).
* Lemma 1.3 (cited, classical): the eigenvalues of `rcir(a)` are
  `λ_m = ∑_{k=0}^{n-1} a_k e^{2kmπi/n}`, `m = 0, …, n-1`; with Lemma 2.5
  (`det = ∏ eigenvalues`) this gives `det rcir(a) = ∏_m λ_m`.
* Corollary cor-left: `det lcir(a) = (-1)^{⌊(n-1)/2⌋} det rcir(a)`.
* Section 2.2: `c_n(z) = (C(n-1,0) z^0, …, C(n-1,n-1) z^{n-1})`, the
  coefficients of `(x + z y)^{n-1}`. Lemma Eigen: the eigenvalues of
  `rcir(c_n(z))` are `(1 + z e^{2mπi/n})^{n-1}`.
* Sections 3-4 compute `det rcir(c_n(z))`, `det lcir(c_n(z))` only for
  `z ∈ {1, -1, i, -i}`.
* Section 5, verbatim: "It is of natural interest to investigate the
  eigenvalues and the determinants of such matrices for other forms of `z`.
  This issue is remained as an open problem."

## Status

The circulant determinant formula (Lemma 1.3 + 2.5) is classical and cited,
not proved, in the paper; Mathlib (at the pinned version) has `circulant`
but no determinant formula, so it is formalized here
(`det_rcir_eq_prod`, `det_rcir_eq_prod_exp`, `det_circulant_eq_prod`).

The printed open problem is closed here for every `z` in every commutative
ring: `det rcir(c_n(z)) = (1 - (-z)^n)^{n-1}` (`det_rcir_binomVec`) and
`det lcir(c_n(z)) = (-1)^{⌊(n-1)/2⌋} (1 - (-z)^n)^{n-1}`
(`det_lcir_binomVec`).  This is a short consequence of the classical
eigenvalue formula together with `∏_m (1 + z ω^m) = 1 - (-z)^n`; it is not
stated in the paper.  The general-ring statement is obtained by proving the
identity for the indeterminate `X` in `ℤ[X]` (inside `ℂ[X]`, where a
primitive root of unity exists) and specializing.
-/
import Mathlib

set_option autoImplicit false

namespace Enumerative.BinomialCirculantDeterminants

open Matrix

/-! ## Definitions mirroring the paper -/

/-- The paper's right circulant matrix `rcir(a)`: row `i` is the first row
`(a_0, …, a_{n-1})` rotated `i` places to the right, i.e. the `(i, j)` entry
is `a_{(j - i) mod n}`. Mathlib's `Matrix.circulant a` is its transpose. -/
def rcir {R : Type*} {n : ℕ} (a : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => a (j - i)

/-- The paper's left circulant matrix `lcir(a)`: row `i` is the first row
rotated `i` places to the left, i.e. the `(i, j)` entry is `a_{(i + j) mod n}`. -/
def lcir {R : Type*} {n : ℕ} (a : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => a (i + j)

/-- The paper's vector `c_n(z) = (C(n-1,k) z^k)_{k=0}^{n-1}` of coefficients
of `(x + z y)^{n-1}`. -/
def binomVec {R : Type*} [CommRing R] (n : ℕ) (z : R) : Fin n → R :=
  fun k => ((n - 1).choose (k : ℕ) : R) * z ^ (k : ℕ)

/-! ### Ground truth on small instances -/

example (a b c : ℤ) : rcir ![a, b, c] = !![a, b, c; c, a, b; b, c, a] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

example (a b c : ℤ) : lcir ![a, b, c] = !![a, b, c; b, c, a; c, a, b] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The paper's Example: `(x + iy)^4 = x^4 + 4i x^3 y - 6 x^2 y^2 - 4i x y^3 + y^4`. -/
example : binomVec 5 Complex.I = ![1, 4 * Complex.I, -6, -4 * Complex.I, 1] := by
  ext k
  fin_cases k <;> simp [binomVec, pow_succ, Nat.choose]

/-- `det rcir(c_3(2)) = det [[1,4,4],[4,1,4],[4,4,1]] = 81 = (1 - (-2)^3)^2`,
computed directly from the 3×3 cofactor formula. -/
example : (rcir (binomVec 3 (2 : ℤ))).det = 81 := by
  have hM : rcir (binomVec 3 (2 : ℤ)) = !![1, 4, 4; 4, 1, 4; 4, 4, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hM, det_fin_three]
  decide

/-- `det lcir(c_3(2)) = det [[1,4,4],[4,4,1],[4,1,4]] = -81`. -/
example : (lcir (binomVec 3 (2 : ℤ))).det = -81 := by
  have hM : lcir (binomVec 3 (2 : ℤ)) = !![1, 4, 4; 4, 4, 1; 4, 1, 4] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hM, det_fin_three]
  decide

/-! ## Eigenvectors of right circulants -/

/-- For `μ^n = 1`, `μ^((a + b) mod n) = μ^a μ^b`. -/
theorem pow_val_add {R : Type*} [CommRing R] {n : ℕ} {μ : R} (hμ : μ ^ n = 1)
    (a b : Fin n) : μ ^ ((a + b : Fin n) : ℕ) = μ ^ (a : ℕ) * μ ^ (b : ℕ) := by
  rw [Fin.val_add, ← pow_eq_pow_mod _ hμ, pow_add]

/-- Paper Lemma 1.3 (eigenvector form, any commutative ring): if `μ^n = 1`
then `(μ^j)_j` satisfies `rcir(v) (μ^j)_j = (∑_k v_k μ^k) (μ^j)_j`. -/
theorem rcir_mulVec_pow {R : Type*} [CommRing R] {n : ℕ} [NeZero n] (v : Fin n → R)
    {μ : R} (hμ : μ ^ n = 1) :
    rcir v *ᵥ (fun j : Fin n => μ ^ (j : ℕ)) =
      (∑ k : Fin n, v k * μ ^ (k : ℕ)) • fun j : Fin n => μ ^ (j : ℕ) := by
  ext i
  simp only [mulVec, dotProduct, rcir, of_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  refine Fintype.sum_equiv (Equiv.addRight i) _ _ (fun k => ?_) |>.symm
  simp only [Equiv.coe_addRight, add_sub_cancel_right, pow_val_add hμ, mul_assoc]

/-- Paper Lemma 1.3 (eigenvalue form): over a nontrivial commutative ring,
for every `μ` with `μ^n = 1`, `∑_k v_k μ^k` is an eigenvalue of `rcir(v)`. -/
theorem rcir_hasEigenvalue {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ} [NeZero n]
    (v : Fin n → R) {μ : R} (hμ : μ ^ n = 1) :
    Module.End.HasEigenvalue (toLin' (rcir v)) (∑ k : Fin n, v k * μ ^ (k : ℕ)) := by
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := fun j : Fin n => μ ^ (j : ℕ)) ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, toLin'_apply, rcir_mulVec_pow v hμ]
  · intro h
    have h0 := congrFun h 0
    simp at h0

/-! ## The classical circulant determinant formula -/

/-- Paper Lemmas 1.3 + 2.5 (classical): over an integral domain with a
primitive `n`-th root of unity `ω`,
`det rcir(v) = ∏_{j<n} ∑_{k<n} v_k ω^{jk}`. -/
theorem det_rcir_eq_prod {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} [NeZero n]
    (v : Fin n → R) {ω : R} (hω : IsPrimitiveRoot ω n) :
    (rcir v).det = ∏ j : Fin n, ∑ k : Fin n, v k * ω ^ ((j : ℕ) * k) := by
  set W : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => (ω ^ (j : ℕ)) ^ (i : ℕ) with hW
  have hWt : W = (vandermonde fun j : Fin n => ω ^ (j : ℕ))ᵀ := by
    ext i j
    simp [hW, vandermonde_apply]
  have hWdet : W.det ≠ 0 := by
    rw [hWt, det_transpose, det_vandermonde_ne_zero_iff]
    intro a b hab
    exact Fin.ext (hω.pow_inj a.isLt b.isLt hab)
  have hmul : rcir v * W =
      W * diagonal fun j : Fin n => ∑ k : Fin n, v k * ω ^ ((j : ℕ) * k) := by
    ext i j
    have hroot : (ω ^ (j : ℕ)) ^ n = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    have hcol := congrFun (rcir_mulVec_pow v hroot) i
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hcol
    rw [mul_diagonal, mul_apply]
    simp only [hW, of_apply, hcol]
    simp only [← pow_mul, mul_comm]
  have hdet := congrArg det hmul
  rw [det_mul, det_mul, det_diagonal, mul_comm] at hdet
  exact mul_left_cancel₀ hWdet hdet

/-- Paper Lemmas 1.3 + 2.5 over `ℂ`, in the paper's notation:
`det rcir(a) = ∏_{m=0}^{n-1} ∑_{k=0}^{n-1} a_k e^{2kmπi/n}`. -/
theorem det_rcir_eq_prod_exp {n : ℕ} [NeZero n] (a : Fin n → ℂ) :
    (rcir a).det = ∏ m : Fin n, ∑ k : Fin n,
      a k * Complex.exp (2 * (k : ℂ) * (m : ℂ) * Real.pi * Complex.I / n) := by
  rw [det_rcir_eq_prod a (Complex.isPrimitiveRoot_exp n (NeZero.ne n))]
  refine Finset.prod_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- Mathlib's `Matrix.circulant v` (entry `(i, j)` is `v (i - j)`) is the
transpose of the paper's `rcir v`. -/
theorem circulant_eq_transpose_rcir {R : Type*} {n : ℕ} (v : Fin n → R) :
    circulant v = (rcir v)ᵀ := rfl

/-- The circulant determinant formula for Mathlib's `Matrix.circulant`:
`det (circulant v) = ∏_{j<n} ∑_{k<n} v_k ω^{jk}` for a primitive `n`-th root
of unity `ω` in an integral domain. -/
theorem det_circulant_eq_prod {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} [NeZero n]
    (v : Fin n → R) {ω : R} (hω : IsPrimitiveRoot ω n) :
    (circulant v).det = ∏ j : Fin n, ∑ k : Fin n, v k * ω ^ ((j : ℕ) * k) := by
  rw [circulant_eq_transpose_rcir, det_transpose, det_rcir_eq_prod v hω]

/-- Satisfiability of the primitive-root hypothesis in an integral domain. -/
example : IsPrimitiveRoot (-1 : ℤ) 2 := IsPrimitiveRoot.neg_one 0 (by decide)

/-! ## Binomial-related circulants -/

/-- The binomial theorem in the paper's indexing:
`∑_{k<n} C(n-1,k) z^k μ^k = (1 + z μ)^{n-1}`. -/
theorem sum_binomVec_mul_pow {R : Type*} [CommRing R] {n : ℕ} [NeZero n] (z μ : R) :
    ∑ k : Fin n, binomVec n z k * μ ^ (k : ℕ) = (1 + z * μ) ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne n)
  calc ∑ k : Fin (m + 1), binomVec (m + 1) z k * μ ^ (k : ℕ)
      = ∑ k : Fin (m + 1), (fun k : ℕ => (z * μ) ^ k * 1 ^ (m - k) * (m.choose k : R)) k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [binomVec, Nat.add_sub_cancel, one_pow, mul_one, mul_pow]
        ring
    _ = ∑ k ∈ Finset.range (m + 1), (z * μ) ^ k * 1 ^ (m - k) * (m.choose k : R) :=
        Fin.sum_univ_eq_sum_range
          (fun k : ℕ => (z * μ) ^ k * 1 ^ (m - k) * (m.choose k : R)) _
    _ = (1 + z * μ) ^ (m + 1 - 1) := by rw [← add_pow, Nat.add_sub_cancel, add_comm]

/-- Paper Lemma Eigen (eigenvector form, any commutative ring and any `z`):
for `μ^n = 1`, `rcir(c_n(z)) (μ^j)_j = (1 + z μ)^{n-1} (μ^j)_j`. -/
theorem rcir_binomVec_mulVec {R : Type*} [CommRing R] {n : ℕ} [NeZero n] (z : R) {μ : R}
    (hμ : μ ^ n = 1) :
    rcir (binomVec n z) *ᵥ (fun j : Fin n => μ ^ (j : ℕ)) =
      (1 + z * μ) ^ (n - 1) • fun j : Fin n => μ ^ (j : ℕ) := by
  rw [rcir_mulVec_pow _ hμ, sum_binomVec_mul_pow]

/-- Paper Lemma Eigen over `ℂ`, for every `z` (the paper assumes `z ≠ 0`,
`n ≥ 2`): `(1 + z e^{2mπi/n})^{n-1}` is an eigenvalue of `rcir(c_n(z))`. -/
theorem rcir_binomVec_hasEigenvalue {n : ℕ} [NeZero n] (z : ℂ) (m : ℕ) :
    Module.End.HasEigenvalue (toLin' (rcir (binomVec n z)))
      ((1 + z * Complex.exp (2 * (m : ℂ) * Real.pi * Complex.I / n)) ^ (n - 1)) := by
  have hμ : Complex.exp (2 * (m : ℂ) * Real.pi * Complex.I / n) ^ n = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨m, ?_⟩
    have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    field_simp
    norm_cast
  rw [← sum_binomVec_mul_pow]
  exact rcir_hasEigenvalue _ hμ

/-- `∏_{j<n} (1 + x ω^j) = 1 - (-x)^n` for a primitive `n`-th root of unity
`ω` in an integral domain. -/
theorem prod_one_add_mul_pow {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} [NeZero n]
    {ω : R} (hω : IsPrimitiveRoot ω n) (x : R) :
    ∏ j : Fin n, (1 + x * ω ^ (j : ℕ)) = 1 - (-x) ^ n := by
  have hpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [← one_pow n, hω.pow_sub_pow_eq_prod_sub_mul 1 (-x) hpos, one_pow]
  refine Finset.prod_bij (fun j _ => ω ^ (j : ℕ)) (fun j _ => ?_) (fun a _ b _ hab => ?_)
    (fun ζ hζ => ?_) (fun j _ => by ring)
  · rw [Polynomial.mem_nthRootsFinset hpos, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one,
      one_pow]
  · exact Fin.ext (hω.pow_inj a.isLt b.isLt hab)
  · rw [Polynomial.mem_nthRootsFinset hpos] at hζ
    obtain ⟨i, hi, hiζ⟩ := hω.eq_pow_of_pow_eq_one hζ
    exact ⟨⟨i, hi⟩, Finset.mem_univ _, hiζ⟩

/-- The determinant identity in an integral domain with a primitive `n`-th
root of unity: `det rcir(c_n(z)) = (1 - (-z)^n)^{n-1}`. -/
theorem det_rcir_binomVec_of_isPrimitiveRoot {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    [NeZero n] {ω : R} (hω : IsPrimitiveRoot ω n) (z : R) :
    (rcir (binomVec n z)).det = (1 - (-z) ^ n) ^ (n - 1) := by
  rw [det_rcir_eq_prod _ hω, ← prod_one_add_mul_pow hω z, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [pow_mul]
  exact sum_binomVec_mul_pow z (ω ^ (j : ℕ))

/-- `rcir` commutes with applying a ring hom entrywise. -/
theorem rcir_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S)
    (a : Fin n → R) : f.mapMatrix (rcir a) = rcir fun k => f (a k) := rfl

/-- `c_n(z)` commutes with ring homs: `f (c_n(z)) = c_n(f z)`. -/
theorem binomVec_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S) (z : R) :
    (fun k => f (binomVec n z k)) = binomVec n (f z) := by
  ext k
  simp [binomVec]

/-- The universal case: in `ℤ[X]`, `det rcir(c_n(X)) = (1 - (-X)^n)^{n-1}`. -/
theorem det_rcir_binomVec_X (n : ℕ) [NeZero n] :
    (rcir (binomVec n (Polynomial.X : Polynomial ℤ))).det =
      (1 - (-Polynomial.X) ^ n) ^ (n - 1) := by
  let f : Polynomial ℤ →+* Polynomial ℂ := Polynomial.mapRingHom (Int.castRingHom ℂ)
  have hf : Function.Injective f := Polynomial.map_injective _ Int.cast_injective
  have hω : IsPrimitiveRoot (Polynomial.C (Complex.exp (2 * Real.pi * Complex.I / n))) n :=
    (Complex.isPrimitiveRoot_exp n (NeZero.ne n)).map_of_injective Polynomial.C_injective
  apply hf
  rw [RingHom.map_det, rcir_map, binomVec_map, det_rcir_binomVec_of_isPrimitiveRoot hω]
  simp [f]

/-- **Answer to the open problem of Section 5 (right circulants).**
For every commutative ring `R`, every `n ≥ 1` and every `z ∈ R`,
`det rcir(c_n(z)) = (1 - (-z)^n)^{n-1}`.  The paper proves only the cases
`z ∈ {1, -1, i, -i}` over `ℂ`. -/
theorem det_rcir_binomVec {R : Type*} [CommRing R] (n : ℕ) [NeZero n] (z : R) :
    (rcir (binomVec n z)).det = (1 - (-z) ^ n) ^ (n - 1) := by
  let g : Polynomial ℤ →+* R := Polynomial.eval₂RingHom (Int.castRingHom R) z
  have hgX : g Polynomial.X = z := Polynomial.eval₂_X _ _
  have h := congrArg g (det_rcir_binomVec_X n)
  rw [RingHom.map_det, rcir_map, binomVec_map, hgX] at h
  rw [h, map_pow, map_sub, map_one, map_pow, map_neg, hgX]

/-! ## Left circulants -/

/-- Paper Lemma col:1: `lcir(a)` is `rcir(a)` with its rows permuted by
`i ↦ -i` (the matrix `H` of the paper). -/
theorem lcir_eq_submatrix {R : Type*} {n : ℕ} [NeZero n] (a : Fin n → R) :
    lcir a = (rcir a).submatrix (Equiv.neg (Fin n)) id := by
  ext i j
  simp [lcir, rcir, add_comm]

/-- `finRotate (m+1) ∘ rev = (rev on Fin m, extended by fixing 0)`. -/
theorem finRotate_mul_revPerm (m : ℕ) :
    finRotate (m + 1) * Fin.revPerm = Equiv.Perm.decomposeFin.symm (0, Fin.revPerm) := by
  ext k
  induction k using Fin.cases with
  | zero =>
    simp [Equiv.Perm.decomposeFin_symm_apply_zero]
  | succ x =>
    rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply,
      Equiv.Perm.mul_apply, finRotate_apply]
    have hx : (x : ℕ) < m := x.isLt
    have h1 : 1 % (m + 1) = 1 := Nat.mod_eq_of_lt (by omega)
    simp only [Fin.revPerm_apply, Fin.val_add, Fin.val_rev, Fin.val_succ, Fin.val_one', h1]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- Negation on `Fin (m+1)` fixes `0` and acts as reversal on `1, …, m`. -/
theorem neg_eq_decomposeFin_symm (m : ℕ) :
    Equiv.neg (Fin (m + 1)) = Equiv.Perm.decomposeFin.symm (0, Fin.revPerm) := by
  ext k
  induction k using Fin.cases with
  | zero =>
    simp [Equiv.Perm.decomposeFin_symm_apply_zero]
  | succ x =>
    rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
    have hx : (x : ℕ) < m := x.isLt
    simp only [Equiv.neg_apply, Fin.val_neg', Fin.revPerm_apply, Fin.val_rev, Fin.val_succ]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- The sign of the reversal `i ↦ m - 1 - i` of `Fin m` is `(-1)^{C(m,2)}`. -/
theorem sign_revPerm (m : ℕ) : Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m)) =
    (-1) ^ m.choose 2 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h := congrArg Equiv.Perm.sign (finRotate_mul_revPerm m)
    rw [Equiv.Perm.decomposeFin.symm_sign, if_pos rfl, one_mul, ih, Equiv.Perm.sign_mul,
      sign_finRotate, Nat.succ_sub_one] at h
    have hsq : ((-1 : ℤˣ) ^ m) * (-1) ^ m = 1 := by
      rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    rw [Nat.choose_succ_succ', Nat.choose_one_right, pow_add, ← h, ← mul_assoc, hsq, one_mul]

/-- Parity: `C(m,2) ≡ ⌊m/2⌋ (mod 2)`. -/
theorem choose_two_mod_two (m : ℕ) : m.choose 2 % 2 = m / 2 % 2 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | k + 4, ih =>
      have hk := ih k (by omega)
      have hstep : ∀ j : ℕ, (j + 1).choose 2 = j.choose 2 + j := fun j => by
        rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
      have h4 : (k + 4).choose 2 = k.choose 2 + 4 * k + 6 := by
        rw [hstep (k + 3), hstep (k + 2), hstep (k + 1), hstep k]
        ring
      have hdiv : (k + 4) / 2 = k / 2 + 2 := by omega
      rw [h4, hdiv, Nat.add_mod, Nat.add_mod (k.choose 2), hk, Nat.add_mod (k / 2)]
      omega

/-- The sign of `i ↦ -i` on `Fin n` is `(-1)^{⌊(n-1)/2⌋}` (the paper's
`det H`). -/
theorem sign_neg (n : ℕ) [NeZero n] :
    Equiv.Perm.sign (Equiv.neg (Fin n)) = (-1) ^ ((n - 1) / 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne n)
  rw [neg_eq_decomposeFin_symm, Equiv.Perm.decomposeFin.symm_sign, if_pos rfl, one_mul,
    sign_revPerm, Nat.add_sub_cancel, Int.units_pow_eq_pow_mod_two, choose_two_mod_two,
    ← Int.units_pow_eq_pow_mod_two]

/-- Paper Corollary cor-left, over any commutative ring:
`det lcir(a) = (-1)^{⌊(n-1)/2⌋} det rcir(a)`. -/
theorem det_lcir {R : Type*} [CommRing R] {n : ℕ} [NeZero n] (a : Fin n → R) :
    (lcir a).det = (-1) ^ ((n - 1) / 2) * (rcir a).det := by
  rw [lcir_eq_submatrix, det_permute, sign_neg]
  simp

/-- **Answer to the open problem of Section 5 (left circulants).**
For every commutative ring `R`, every `n ≥ 1` and every `z ∈ R`,
`det lcir(c_n(z)) = (-1)^{⌊(n-1)/2⌋} (1 - (-z)^n)^{n-1}`. -/
theorem det_lcir_binomVec {R : Type*} [CommRing R] (n : ℕ) [NeZero n] (z : R) :
    (lcir (binomVec n z)).det = (-1) ^ ((n - 1) / 2) * (1 - (-z) ^ n) ^ (n - 1) := by
  rw [det_lcir, det_rcir_binomVec]

/-- Consistency with the paper's Theorem thm_i for `n = 5`, `z = i`:
`det rcir(c_5(i)) = (2i)^2 = -4`. -/
example : (rcir (binomVec 5 Complex.I)).det = -4 := by
  rw [det_rcir_binomVec]
  norm_num [pow_succ, Complex.ext_iff]

end Enumerative.BinomialCirculantDeterminants
