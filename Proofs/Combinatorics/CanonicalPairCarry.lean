import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace CanonicalPairCarry

/-- Ordinary base-`r` evaluation of a fixed-length vector of digits. -/
def value (r k : ℕ) (w : Fin k → Fin r) : ℕ :=
  ∑ i : Fin k, (w i).val * r ^ i.val

example : value 3 2 ![⟨1, by decide⟩, ⟨2, by decide⟩] = 7 := by decide
example (r : ℕ) : value r 0 Fin.elim0 = 0 := rfl

/-- Fixed-length positional encoding, including the empty vector and base one. -/
def digitsEquiv (r k : ℕ) : (Fin k → Fin r) ≃ Fin (r ^ k) :=
  finFunctionFinEquiv

/-- The positional equivalence is the usual sum of digit times base powers. -/
theorem digitsEquiv_val (r k : ℕ) (w : Fin k → Fin r) :
    (digitsEquiv r k w).val = value r k w :=
  finFunctionFinEquiv_apply w

example : (digitsEquiv 3 2 ![⟨1, by decide⟩, ⟨2, by decide⟩]).val = 7 :=
  digitsEquiv_val 3 2 _

/-- One pair of base-`a` digits becomes one base-`a*a` digit by reversing
its second coordinate and using quotient/remainder positional encoding. -/
def pairDigitEquiv (a : ℕ) : (Fin a × Fin a) ≃ Fin (a * a) :=
  ((Equiv.prodComm _ _).trans
    (Equiv.prodCongr Fin.revPerm (Equiv.refl _))).trans finProdFinEquiv

/-- The encoded pair digit is the signed coefficient plus its fixed offset. -/
theorem pairDigitEquiv_val (a : ℕ) (p : Fin a × Fin a) :
    ((pairDigitEquiv a p).val : ℤ) =
      (p.1.val : ℤ) - (a : ℤ) * p.2.val + (a : ℤ) * ((a : ℤ) - 1) := by
  change ((p.1.val + a * p.2.rev.val : ℕ) : ℤ) = _
  rw [Nat.cast_add, Nat.cast_mul, Fin.val_rev]
  have hv : p.2.val + 1 ≤ a := p.2.isLt
  rw [Nat.cast_sub hv, Nat.cast_add, Nat.cast_one]
  ring

example : (pairDigitEquiv 3 (⟨1, by decide⟩, ⟨2, by decide⟩)).val = 1 := rfl

/-- All low pairs encode exactly the full ordinary digit interval. -/
def pairVectorEquiv (a k : ℕ) : (Fin k → Fin a × Fin a) ≃ Fin ((a * a) ^ k) :=
  (Equiv.piCongrRight fun _ => pairDigitEquiv a).trans (digitsEquiv (a * a) k)

/-- The signed low block `A - a A′`, with both vectors represented together. -/
def block (a k : ℕ) (x : Fin k → Fin a × Fin a) : ℤ :=
  ∑ i : Fin k, ((x i).1.val - (a : ℤ) * (x i).2.val) * (a * a : ℕ) ^ i.val

/-- Fixed translation converting signed low coefficients to ordinary digits. -/
def shift (a k : ℕ) : ℤ :=
  (a : ℤ) * ((a : ℤ) - 1) * ∑ i : Fin k, ((a * a : ℕ) : ℤ) ^ i.val

example : block 2 1 (fun _ => (⟨0, by decide⟩, ⟨1, by decide⟩)) = -2 := by decide
example : shift 2 2 = 10 := by decide
example (a : ℕ) : block a 0 Fin.elim0 = 0 := rfl
example (a : ℕ) : shift a 0 = 0 := by simp [shift]

/-- Translating the signed block gives precisely its ordinary positional encoding. -/
theorem block_add_shift (a k : ℕ) (x : Fin k → Fin a × Fin a) :
    block a k x + shift a k = ((pairVectorEquiv a k x).val : ℤ) := by
  rw [pairVectorEquiv, Equiv.trans_apply, digitsEquiv_val]
  simp only [value, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow,
    Equiv.piCongrRight]
  rw [block, shift, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  change _ = ((pairDigitEquiv a (x i)).val : ℤ) * ((a : ℤ) * a) ^ i.val
  rw [pairDigitEquiv_val, Nat.cast_mul]
  ring

example : (pairVectorEquiv 2 0 Fin.elim0).val = 0 := rfl

/-- There are exactly `(a*a)^k` low pair vectors. -/
theorem card_pairVectors (a k : ℕ) :
    Fintype.card (Fin k → Fin a × Fin a) = (a * a) ^ k := by
  exact (Fintype.card_congr (pairVectorEquiv a k)).trans (Fintype.card_fin _)

/-- Exact translated consecutive interval range of the signed block. -/
theorem block_range (a k : ℕ) (y : ℤ) :
    (∃ x : Fin k → Fin a × Fin a, block a k x = y) ↔
      -shift a k ≤ y ∧ y < ((a * a) ^ k : ℕ) - shift a k := by
  constructor
  · rintro ⟨x, rfl⟩
    have he := block_add_shift a k x
    have hlo : (0 : ℤ) ≤ (pairVectorEquiv a k x).val := Int.natCast_nonneg _
    have hhi : ((pairVectorEquiv a k x).val : ℤ) < ((a * a) ^ k : ℕ) := by
      exact_mod_cast (pairVectorEquiv a k x).isLt
    omega
  · rintro ⟨hlo, hhi⟩
    have hn : 0 ≤ y + shift a k := by omega
    have ht : (y + shift a k).toNat < (a * a) ^ k := by
      apply Int.ofNat_lt.mp
      rw [Int.toNat_of_nonneg hn]
      omega
    let z : Fin ((a * a) ^ k) := ⟨(y + shift a k).toNat, ht⟩
    refine ⟨(pairVectorEquiv a k).symm z, ?_⟩
    have he := block_add_shift a k ((pairVectorEquiv a k).symm z)
    rw [Equiv.apply_symm_apply] at he
    change block a k ((pairVectorEquiv a k).symm z) + shift a k =
      ((y + shift a k).toNat : ℤ) at he
    rw [Int.toNat_of_nonneg hn] at he
    omega

/-- The modulus is positive for all allowed bases, including `a=1` and `k=0`. -/
theorem modulus_pos (a k : ℕ) (ha : 1 ≤ a) : 0 < (a * a) ^ k :=
  pow_pos (Nat.mul_pos (by omega) (by omega)) k

/-- The nonnegative remainder of the signed low block, as a finite residue. -/
def residue (a k : ℕ) (ha : 1 ≤ a) (x : Fin k → Fin a × Fin a) :
    Fin ((a * a) ^ k) :=
  ⟨(block a k x % ((a * a) ^ k : ℕ)).toNat, by
    have hp : (0 : ℤ) < ((a * a) ^ k : ℕ) := by exact_mod_cast modulus_pos a k ha
    have hn := Int.emod_nonneg (block a k x) (ne_of_gt hp)
    have ht := Int.emod_lt_of_pos (block a k x) hp
    apply Int.ofNat_lt.mp
    rw [Int.toNat_of_nonneg hn]
    exact ht⟩

/-- The finite residue really is integer Euclidean remainder, also for negative blocks. -/
theorem residue_val (a k : ℕ) (ha : 1 ≤ a) (x : Fin k → Fin a × Fin a) :
    ((residue a k ha x).val : ℤ) = block a k x % ((a * a) ^ k : ℕ) := by
  have hp : (0 : ℤ) < ((a * a) ^ k : ℕ) := by exact_mod_cast modulus_pos a k ha
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hp))

example : (residue 2 1 (by decide)
    (fun _ => (⟨0, by decide⟩, ⟨1, by decide⟩))).val = 2 := by decide
example (a : ℕ) (ha : 1 ≤ a) : (residue a 0 ha Fin.elim0).val = 0 := rfl
example (k : ℕ) : (residue 1 k (by decide) (fun _ => (0, 0))).val = 0 := by
  simp [residue]

/-- The low pair is determined by its remainder, even when the signed block is negative. -/
theorem emod_injective (a k : ℕ) (ha : 1 ≤ a) :
    Function.Injective (fun x : Fin k → Fin a × Fin a =>
      block a k x % ((a * a) ^ k : ℕ)) := by
  intro x y hxy
  change block a k x % ((a * a) ^ k : ℕ) =
    block a k y % ((a * a) ^ k : ℕ) at hxy
  have hp : (0 : ℤ) < ((a * a) ^ k : ℕ) := by exact_mod_cast modulus_pos a k ha
  have hx := block_add_shift a k x
  have hy := block_add_shift a k y
  have hxlo : (0 : ℤ) ≤ (pairVectorEquiv a k x).val := Int.natCast_nonneg _
  have hylo : (0 : ℤ) ≤ (pairVectorEquiv a k y).val := Int.natCast_nonneg _
  have hxhi : ((pairVectorEquiv a k x).val : ℤ) < ((a * a) ^ k : ℕ) := by
    exact_mod_cast (pairVectorEquiv a k x).isLt
  have hyhi : ((pairVectorEquiv a k y).val : ℤ) < ((a * a) ^ k : ℕ) := by
    exact_mod_cast (pairVectorEquiv a k y).isLt
  have he : (block a k x + shift a k) % ((a * a) ^ k : ℕ) =
      (block a k y + shift a k) % ((a * a) ^ k : ℕ) := by
    rw [Int.add_emod (block a k x) (shift a k),
      Int.add_emod (block a k y) (shift a k), hxy]
  rw [hx, hy, Int.emod_eq_of_lt hxlo hxhi, Int.emod_eq_of_lt hylo hyhi] at he
  apply (pairVectorEquiv a k).injective
  apply Fin.ext
  exact_mod_cast he

/-- The low-pair remainder map is a bijection onto all `(a*a)^k` residues. -/
theorem residue_bijective (a k : ℕ) (ha : 1 ≤ a) :
    Function.Bijective (residue a k ha) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro x y hxy
    apply emod_injective a k ha
    have hv := congrArg (fun z : Fin ((a * a) ^ k) => (z.val : ℤ)) hxy
    simpa only [residue_val] using hv
  · simpa only [Fintype.card_fin] using card_pairVectors a k

/-- The residue decoder is an equivalence, ready for uniform finite pushforward. -/
noncomputable def residueEquiv (a k : ℕ) (ha : 1 ≤ a) :
    (Fin k → Fin a × Fin a) ≃ Fin ((a * a) ^ k) :=
  Equiv.ofBijective (residue a k ha) (residue_bijective a k ha)

example (a k : ℕ) (ha : 1 ≤ a) (x : Fin k → Fin a × Fin a) :
    residueEquiv a k ha x = residue a k ha x := rfl

/-- In separate-vector notation the block is exactly `A - a A′`. -/
theorem block_eq_sub (a k : ℕ) (u v : Fin k → Fin a) :
    block a k (fun i => (u i, v i)) =
      (∑ i : Fin k, (u i).val * ((a * a : ℕ) : ℤ) ^ i.val) -
      (a : ℤ) * ∑ i : Fin k, (v i).val * ((a * a : ℕ) : ℤ) ^ i.val := by
  rw [block, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The SC low-block consumer: equality of remainders determines both low vectors. -/
theorem low_pair_determined_by_residue (a k : ℕ) (ha : 1 ≤ a)
    (u v u' v' : Fin k → Fin a)
    (h : block a k (fun i => (u i, v i)) % ((a * a) ^ k : ℕ) =
      block a k (fun i => (u' i, v' i)) % ((a * a) ^ k : ℕ)) :
    u = u' ∧ v = v' := by
  have he := emod_injective a k ha h
  constructor
  · exact congrArg (fun x : Fin k → Fin a × Fin a => fun i => (x i).1) he
  · exact congrArg (fun x : Fin k → Fin a × Fin a => fun i => (x i).2) he

example (a k : ℕ) (ha : 1 ≤ a) : Nonempty (Fin k → Fin a × Fin a) :=
  ⟨fun _ => (⟨0, by omega⟩, ⟨0, by omega⟩)⟩

example : 1 ≤ 2 ∧ Nonempty (Fin 1 → Fin 2 × Fin 2) ∧
    Function.Bijective (residue 2 1 (by decide)) :=
  ⟨by decide, ⟨fun _ => (0, 1)⟩, residue_bijective 2 1 (by decide)⟩

end CanonicalPairCarry
