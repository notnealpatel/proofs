/-
# A228885 — Sun: sign of the coprimality determinant for squarefree `n`

Zhi-Wei Sun's sign conjecture in OEIS A228885 concerns the determinant
`a(n)` of the matrix `[gcd(i+j,n)=1]`, indexed by `1 ≤ i,j ≤ n`.
For squarefree `n`, the stronger formula proved here is
`a(n) = (-1)^(n(n-1)/2) ∏_{p ∣ n} (p-1)^(n/p)`; it implies the sign claim.
Ridouane Oudra's closed forms in the entry specialize to this formula on
squarefree `n`.

Proof outline.
1. Index rows and columns by `ZMod n` via `i ↦ i + 1` on both sides, so the
   matrix becomes the Hankel matrix `H_n(x, y) = [x + y is a unit]` with the
   same determinant (`sunDet_eq_det_unitHankel`).
2. For coprime `m, k`, the Chinese remainder ring isomorphism
   `ZMod (m k) ≃+* ZMod m × ZMod k` turns `H_{mk}` into the Kronecker product
   `H_m ⊗ H_k`, so `det H_{mk} = (det H_m)^k (det H_k)^m`
   (`det_unitHankel_mul`).
3. For a prime `p`, permuting columns by `x ↦ -x` turns `H_p` into `J - 1`,
   whose determinant is `(-1)^p (1 - p)` by the matrix determinant lemma;
   the sign of negation on `ZMod p` is `(-1)^((p-1)/2)` for odd `p`
   (`sign_neg_zmod`), giving `det H_p = (-1)^(p(p-1)/2) (p - 1)`
   (`det_unitHankel_prime`).
4. The sign `(-1)^(n(n-1)/2)` depends only on `n mod 4`, which yields
   multiplicativity of the sign for factors that are not both even
   (`negOnePow_tri_mul`); induction over coprime factorizations closes it.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A228885MatrixEntryGcd

open Matrix
open scoped Kronecker

/-! ## Definitions -/

/-- The `n × n` integer matrix of A228885: rows and columns are indexed by
`i, j ∈ {1, …, n}` (stored as `Fin n` with offset `+1`), and the
`(i, j)`-entry is `1` if `gcd(i + j, n) = 1` and `0` otherwise. -/
def sunMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => if Nat.Coprime (i.val + 1 + (j.val + 1)) n then 1 else 0

/-- `a(n)` of A228885: the determinant of `sunMatrix n`. -/
def sunDet (n : ℕ) : ℤ := (sunMatrix n).det

/-- `a(1) = 1`. -/
example : sunDet 1 = 1 := by
  rw [sunDet, det_unique]
  decide

/-- `a(2) = -1`. -/
example : sunDet 2 = -1 := by
  rw [sunDet, det_fin_two]
  decide

/-- `a(3) = -2`. -/
example : sunDet 3 = -2 := by
  rw [sunDet, det_fin_three]
  decide

/-- the matrix for `n = 4` is the checkerboard pattern
`[[0,1,0,1],[1,0,1,0],[0,1,0,1],[1,0,1,0]]`. -/
example : sunMatrix 4 = !![0, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-! ## Reindexing by `ZMod n` -/

open Classical in
/-- The Hankel matrix on `ZMod n` whose `(x, y)`-entry is `1` if `x + y` is a
unit of `ZMod n` and `0` otherwise. -/
noncomputable def unitHankel (n : ℕ) : Matrix (ZMod n) (ZMod n) ℤ :=
  Matrix.of fun x y => if IsUnit (x + y) then 1 else 0

/-- For `n ≠ 0`, `a(n)` equals the determinant of `unitHankel n`: the
reindexing `i ↦ i + 1` of `Fin n` onto `ZMod n`, applied to rows and columns
alike, carries `sunMatrix n` to `unitHankel n`. -/
theorem sunDet_eq_det_unitHankel (n : ℕ) [NeZero n] :
    sunDet n = (unitHankel n).det := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  let e : Fin (k + 1) ≃ ZMod (k + 1) := Equiv.addRight (1 : Fin (k + 1))
  have hM : sunMatrix (k + 1) = (unitHankel (k + 1)).submatrix e e := by
    ext i j
    simp only [sunMatrix, unitHankel, submatrix_apply, of_apply]
    have hcast : (((i.val + 1 + (j.val + 1) : ℕ)) : ZMod (k + 1)) = e i + e j := by
      have hi : ((i.val : ℕ) : ZMod (k + 1)) = (i : ZMod (k + 1)) :=
        ZMod.natCast_zmod_val (n := k + 1) i
      have hj : ((j.val : ℕ) : ZMod (k + 1)) = (j : ZMod (k + 1)) :=
        ZMod.natCast_zmod_val (n := k + 1) j
      simp only [e]
      push_cast
      rw [hi, hj]
      rfl
    simp only [← hcast, ZMod.isUnit_iff_coprime]
  rw [sunDet, hM, det_submatrix_equiv_self]

/-! ## Multiplicativity via the Chinese remainder theorem -/

/-- For coprime `m, k`, `det H_{mk} = (det H_m)^k * (det H_k)^m`: the Chinese
remainder isomorphism identifies `H_{mk}` with the Kronecker product
`H_m ⊗ H_k`. -/
theorem det_unitHankel_mul {m k : ℕ} [NeZero m] [NeZero k] (h : Nat.Coprime m k) :
    haveI : NeZero (m * k) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne k)⟩
    (unitHankel (m * k)).det = (unitHankel m).det ^ k * (unitHankel k).det ^ m := by
  haveI : NeZero (m * k) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne k)⟩
  let c : ZMod (m * k) ≃+* ZMod m × ZMod k := ZMod.chineseRemainder h
  have hK : reindex c.toEquiv c.toEquiv (unitHankel (m * k)) =
      unitHankel m ⊗ₖ unitHankel k := by
    ext ⟨a1, a2⟩ ⟨b1, b2⟩
    simp only [reindex_apply, submatrix_apply, unitHankel, of_apply]
    have hu : IsUnit (c.symm (a1, a2) + c.symm (b1, b2)) ↔
        IsUnit (a1 + b1) ∧ IsUnit (a2 + b2) := by
      rw [← map_add, isUnit_map_iff, Prod.isUnit_iff]
      rfl
    by_cases h1 : IsUnit (a1 + b1) <;> by_cases h2 : IsUnit (a2 + b2) <;> simp [hu, h1, h2]
  rw [← det_reindex_self c.toEquiv, hK, det_kronecker, ZMod.card, ZMod.card]

/-! ## The prime case -/

/-- For an odd prime `p`, the negation permutation `x ↦ -x` of `ZMod p` has
sign `(-1)^((p-1)/2)`: it is an involution whose support is `ZMod p \ {0}`. -/
theorem sign_neg_zmod {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    Equiv.Perm.sign (Equiv.neg (ZMod p)) = (-1) ^ ((p - 1) / 2) := by
  set σ : Equiv.Perm (ZMod p) := Equiv.neg (ZMod p) with hσ
  have hsq : σ ^ 2 = 1 := by
    ext x; simp [hσ, sq]
  have hne : σ ≠ 1 := by
    intro h
    have h1 : σ 1 = (1 : Equiv.Perm (ZMod p)) 1 := by rw [h]
    simp only [hσ, Equiv.neg_apply, Equiv.Perm.coe_one, id_eq] at h1
    haveI : Fact (2 < p) := ⟨lt_of_le_of_ne hp.out.two_le (Ne.symm hp2)⟩
    exact ZMod.neg_one_ne_one h1
  have hord : orderOf σ = 2 := orderOf_eq_prime hsq hne
  have hsupp : σ.support = Finset.univ.erase 0 := by
    ext x
    simp only [Equiv.Perm.mem_support, hσ, Equiv.neg_apply, Finset.mem_erase,
      Finset.mem_univ, and_true]
    rw [Ne, ZMod.neg_eq_self_iff]
    constructor
    · intro h h0; exact h (Or.inl h0)
    · rintro h0 (h | h)
      · exact h0 h
      · have hodd : Odd p := hp.out.odd_of_ne_two hp2
        rw [← h] at hodd
        exact (Nat.not_odd_iff_even.mpr (even_two_mul _)) hodd
  have hcard : σ.support.card = p - 1 := by
    rw [hsupp, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  obtain ⟨k, hk⟩ := Equiv.Perm.cycleType_prime_order (σ := σ) (by rw [hord]; exact Nat.prime_two)
  have hsum : σ.cycleType.sum = p - 1 := by rw [Equiv.Perm.sum_cycleType, hcard]
  rw [hk, hord, Multiset.sum_replicate, smul_eq_mul] at hsum
  rw [Equiv.Perm.sign_of_cycleType, hk, hord, Multiset.sum_replicate, Multiset.card_replicate,
    smul_eq_mul, hsum]
  have hk2 : (p - 1) / 2 = k + 1 := by omega
  rw [hk2, ← hsum, pow_add, pow_mul]
  simp

/-- The all-ones matrix minus the identity, indexed by a finite type of
cardinality `N`, has determinant `(-1)^N * (1 - N)`. -/
theorem det_allOnes_sub_one (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (Matrix.of (fun _ _ => (1 : ℤ)) - (1 : Matrix ι ι ℤ)).det =
      (-1) ^ Fintype.card ι * (1 - (Fintype.card ι : ℤ)) := by
  have h : Matrix.of (fun _ _ => (1 : ℤ)) - (1 : Matrix ι ι ℤ) =
      -(1 + replicateCol Unit (fun _ : ι => (-1 : ℤ)) *
        replicateRow Unit (fun _ : ι => (1 : ℤ))) := by
    ext x y
    simp only [Matrix.sub_apply, of_apply, replicateCol, replicateRow, Matrix.neg_apply,
      Matrix.add_apply, Matrix.mul_apply, Finset.univ_unique, PUnit.default_eq_unit, mul_one,
      Finset.sum_neg_distrib, Finset.sum_const, Finset.card_singleton, Int.nsmul_eq_mul,
      Nat.cast_one, neg_add_rev, neg_neg]
    ring
  rw [h, det_neg, det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct, mul_neg, mul_one, Finset.sum_neg_distrib, Finset.sum_const,
    Finset.card_univ, Int.nsmul_eq_mul, mul_eq_mul_left_iff, pow_eq_zero_iff', neg_eq_zero,
    one_ne_zero, ne_eq, false_and, or_false]
  ring

/-- For a prime `p`, `det H_p = (-1)^(p(p-1)/2) * (p - 1)`. -/
theorem det_unitHankel_prime {p : ℕ} (hp : p.Prime) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    (unitHankel p).det = (-1) ^ (p * (p - 1) / 2) * ((p : ℤ) - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set σ : Equiv.Perm (ZMod p) := Equiv.neg (ZMod p) with hσ
  have hsub : (unitHankel p).submatrix id σ = Matrix.of (fun _ _ => (1 : ℤ)) - 1 := by
    ext x y
    simp only [unitHankel, submatrix_apply, id_eq, hσ, Equiv.neg_apply, of_apply,
      Matrix.sub_apply, one_apply, isUnit_iff_ne_zero, ← sub_eq_add_neg, sub_ne_zero]
    by_cases hxy : x = y <;> simp [hxy]
  have hdet := det_permute' σ (unitHankel p)
  rw [hsub, det_allOnes_sub_one, ZMod.card, Int.cast_id] at hdet
  have hsq : ((Equiv.Perm.sign σ : ℤˣ) : ℤ) * (Equiv.Perm.sign σ : ℤˣ) = 1 := by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  have hH : (unitHankel p).det = (Equiv.Perm.sign σ : ℤ) * ((-1) ^ p * (1 - (p : ℤ))) := by
    rw [hdet, ← mul_assoc, hsq, one_mul]
  rw [hH]
  rcases hp.eq_two_or_odd' with rfl | hodd
  · have hσ1 : σ = 1 := by
      ext x; fin_cases x <;> rfl
    rw [hσ1]
    norm_num
  · have hp2 : p ≠ 2 := by rintro rfl; exact absurd hodd (by decide)
    rw [hσ, sign_neg_zmod hp2]
    obtain ⟨t, rfl⟩ := hodd
    have h1 : (2 * t + 1) * (2 * t + 1 - 1) / 2 = (2 * t + 1) * t := by
      rw [Nat.add_sub_cancel, mul_comm 2 t, ← mul_assoc, Nat.mul_div_cancel _ two_pos]
    have h2 : (2 * t + 1 - 1) / 2 = t := by omega
    rw [h1, h2, pow_mul]
    push_cast
    rw [pow_succ, pow_mul]
    rcases neg_one_pow_eq_or ℤ t with h | h <;> simp [h]

/-! ## The sign `(-1)^(n(n-1)/2)` -/

/-- `(n + 4)(n + 3)/2 = n(n - 1)/2 + 2(2n + 3)`. -/
theorem tri_add_four (n : ℕ) :
    (n + 4) * (n + 4 - 1) / 2 = n * (n - 1) / 2 + 2 * (2 * n + 3) := by
  have h : (n + 4) * (n + 4 - 1) = n * (n - 1) + 2 * (2 * (2 * n + 3)) := by
    rcases n with _ | s
    · rfl
    · simp only [Nat.add_sub_cancel, show s + 1 + 4 - 1 = s + 4 by omega]
      ring
  rw [h, Nat.add_mul_div_left _ _ two_pos]

/-- The sign `(-1)^(n(n-1)/2)` depends only on `n mod 4`. -/
theorem negOnePow_tri_mod_four (n : ℕ) :
    (-1 : ℤ) ^ (n * (n - 1) / 2) = (-1) ^ ((n % 4) * (n % 4 - 1) / 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < 4
    · rw [Nat.mod_eq_of_lt hn]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      rw [tri_add_four, pow_add, pow_mul, show ((-1 : ℤ) ^ 2) = 1 by norm_num, one_pow,
        mul_one, ih m (by omega), Nat.add_mod_right]

/-- If `x² = 1` then `x^k = x^(k mod 2)`. -/
theorem pow_eq_pow_mod_two_of_sq {x : ℤ} (hx : x ^ 2 = 1) (k : ℕ) : x ^ k = x ^ (k % 2) := by
  conv_lhs => rw [← Nat.div_add_mod k 2, pow_add, pow_mul, hx, one_pow, one_mul]

/-- Multiplicativity of the sign: if `m` and `k` are not both even, then
`(-1)^(mk(mk-1)/2) = ((-1)^(m(m-1)/2))^k * ((-1)^(k(k-1)/2))^m`. -/
theorem negOnePow_tri_mul {m k : ℕ} (h : ¬ (2 ∣ m ∧ 2 ∣ k)) :
    (-1 : ℤ) ^ (m * k * (m * k - 1) / 2) =
      ((-1 : ℤ) ^ (m * (m - 1) / 2)) ^ k * ((-1 : ℤ) ^ (k * (k - 1) / 2)) ^ m := by
  have hsq : ∀ e : ℕ, ((-1 : ℤ) ^ e) ^ 2 = 1 := fun e => by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [pow_eq_pow_mod_two_of_sq (hsq _) k, pow_eq_pow_mod_two_of_sq (hsq _) m,
    negOnePow_tri_mod_four (m * k), negOnePow_tri_mod_four m, negOnePow_tri_mod_four k,
    Nat.mul_mod, ← Nat.mod_mod_of_dvd k (by norm_num : 2 ∣ 4),
    ← Nat.mod_mod_of_dvd m (by norm_num : 2 ∣ 4)]
  have hm4 : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hk4 : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have h' : ¬ ((m % 4) % 2 = 0 ∧ (k % 4) % 2 = 0) := by
    rw [Nat.mod_mod_of_dvd m (by norm_num : 2 ∣ 4), Nat.mod_mod_of_dvd k (by norm_num : 2 ∣ 4)]
    omega
  generalize m % 4 = a at hm4 h'
  generalize k % 4 = b at hk4 h'
  revert a b
  decide

/-! ## The closed form and Sun's conjecture -/

/-- The closed form for squarefree `n` in `ZMod`-indexed form:
`det H_n = (-1)^(n(n-1)/2) * ∏_{p ∣ n} (p - 1)^(n/p)`. -/
theorem det_unitHankel_of_squarefree :
    ∀ n : ℕ, ∀ (_ : NeZero n), Squarefree n →
      (unitHankel n).det =
        (-1) ^ (n * (n - 1) / 2) * ∏ p ∈ n.primeFactors, ((p : ℤ) - 1) ^ (n / p) := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p e hp he =>
    intro hne hsq
    have he1 : e = 1 := ((Nat.squarefree_pow_iff hp.ne_one he.ne').mp hsq).2
    subst he1
    revert hne hsq
    rw [pow_one]
    intro _ _
    rw [det_unitHankel_prime hp, hp.primeFactors, Finset.prod_singleton,
      Nat.div_self hp.pos, pow_one]
  | zero =>
    intro _ hsq
    exact absurd hsq not_squarefree_zero
  | one =>
    intro _ _
    rw [det_unique]
    simp only [unitHankel, of_apply, if_pos (isUnit_of_subsingleton _)]
    simp
  | coprime a b ha hb hab iha ihb =>
    intro _ hsq
    haveI : NeZero a := ⟨by omega⟩
    haveI : NeZero b := ⟨by omega⟩
    have hdet := det_unitHankel_mul hab
    rw [hdet, iha inferInstance hsq.of_mul_left, ihb inferInstance hsq.of_mul_right]
    have hnot : ¬ (2 ∣ a ∧ 2 ∣ b) := fun ⟨h2a, h2b⟩ =>
      Nat.not_coprime_of_dvd_of_dvd one_lt_two h2a h2b hab
    rw [negOnePow_tri_mul hnot, hab.primeFactors_mul,
      Finset.prod_union hab.disjoint_primeFactors, mul_pow, mul_pow, ← Finset.prod_pow,
      ← Finset.prod_pow]
    have hpa : ∏ p ∈ a.primeFactors, (((p : ℤ) - 1) ^ (a / p)) ^ b =
        ∏ p ∈ a.primeFactors, ((p : ℤ) - 1) ^ (a * b / p) := by
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [← pow_mul, Nat.div_mul_right_comm (Nat.dvd_of_mem_primeFactors hp)]
    have hpb : ∏ p ∈ b.primeFactors, (((p : ℤ) - 1) ^ (b / p)) ^ a =
        ∏ p ∈ b.primeFactors, ((p : ℤ) - 1) ^ (a * b / p) := by
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [← pow_mul, Nat.div_mul_right_comm (Nat.dvd_of_mem_primeFactors hp), mul_comm b a]
    rw [hpa, hpb]
    ring

/-- **Closed form (strong form of Sun's conjecture, A228885).** For every
squarefree `n`, `a(n) = (-1)^(n(n-1)/2) * ∏_{p ∣ n prime} (p - 1)^(n/p)`.
Oudra's conjectural closed forms in the entry specialize to this on
squarefree `n`. -/
theorem sunDet_of_squarefree {n : ℕ} (hn : Squarefree n) :
    sunDet n = (-1) ^ (n * (n - 1) / 2) * ∏ p ∈ n.primeFactors, ((p : ℤ) - 1) ^ (n / p) := by
  haveI : NeZero n := ⟨hn.ne_zero⟩
  rw [sunDet_eq_det_unitHankel, det_unitHankel_of_squarefree n inferInstance hn]

/-- **Sun's conjecture (A228885, Zhi-Wei Sun).**

Here `a(n) = sunDet n` is the determinant of the `n × n` matrix with
`(i, j)`-entry `1` if `gcd(i + j, n) = 1` and `0` otherwise.  `Squarefree n`
excludes `n = 0` (`not_squarefree_zero`), so the statement ranges over
`n ≥ 1` as in the source; `n * (n - 1)` is even, so the `ℕ` division is exact. -/
theorem sun_conjecture {n : ℕ} (hn : Squarefree n) :
    0 < (-1 : ℤ) ^ (n * (n - 1) / 2) * sunDet n := by
  rw [sunDet_of_squarefree hn, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow,
    one_mul]
  refine Finset.prod_pos fun p hp => pow_pos ?_ _
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  have hp2' : (2 : ℤ) ≤ p := by exact_mod_cast hp2
  linarith

/-- Non-vacuity: `6` is squarefree, so the hypotheses of `sunDet_of_squarefree`
and `sun_conjecture` are satisfiable at a composite `n`. -/
theorem squarefree_six : Squarefree 6 := by
  rw [show (6 : ℕ) = 2 * 3 by rfl, Nat.squarefree_mul_iff]
  exact ⟨by norm_num, Nat.prime_two.prime.squarefree, Nat.prime_three.prime.squarefree⟩

/-- Consistency with the listed term `a(6) = -4`, obtained from the closed form. -/
example : sunDet 6 = -4 := by
  have hpf : Nat.primeFactors 6 = {2, 3} := by
    rw [show (6 : ℕ) = 2 * 3 by rfl, Nat.Coprime.primeFactors_mul (by norm_num),
      Nat.prime_two.primeFactors, Nat.prime_three.primeFactors]
    rfl
  rw [sunDet_of_squarefree squarefree_six, hpf]
  decide

end Candidates.A228885MatrixEntryGcd
