/-
  Scratch/RouteCGaugeStab — Route C (concrete track): AES gauge stabilizer
  triviality and gauge-table injectivity, as exhaustively checked
  computational certificates.

  Setting.  GF(2^8) = GF(2)[x]/(x^8 + x^4 + x^3 + x + 1) (the AES field,
  reduction mask 0x11B); a byte b encodes the field element with bit i =
  coefficient of x^i (LSB-first).  An 8×8 matrix over GF(2) is represented
  by its column function `Nat → Nat`: column j is a byte whose bit i is the
  (i, j) entry.  For a byte a, `Mcol a` is the matrix M_a of field
  multiplication by a (column j = a·x^j mod the polynomial), and `Acol` is
  the AES S-box output linear layer A, defined entrywise by
  A[i][j] = 1 iff (j − i) mod 8 ∈ {0, 4, 5, 6, 7}.

  MAIN  (`gauge_stab`):  for all nonzero bytes c, d:
        M_d · A · M_c = A  →  c = 1 ∧ d = 1.
  255² = 65025 8×8 GF(2) matrix identities, discharged by `native_decide`;
  independently cross-checked in SageMath (the only stabilizing pair is
  (c, d) = (1, 1) — in particular no nontrivial stabilizer exists).

  COROLLARY  (`gauge_inj`):  (a, a') ↦ M_{a'} · A · M_a is injective on
  (F*)², derived from `gauge_stab` via the group structure of F*: matrix
  glue by the pure GF(2)-linearity lemmas below, scalar group facts by
  small exhaustive `native_decide` certificates.

  Sanity anchors (FIPS-197 conventions, pin the bit ordering):
  gmul 0x57 0x83 = 0xC1, ginv 0x53 = 0xCA, aff 0x01 = 0x1F (column 0 of A
  has ones in rows 0..4), sbox 0x53 = 0xED, sbox 0x01 = 0x7C,
  sbox 0x00 = 0x63.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib

namespace RouteCGaugeStab

/-! ### The field GF(2^8) and the matrices M_a and A -/

/-- Multiplication by x in GF(2^8) modulo x^8+x^4+x^3+x+1 (0x11B).
    Field-correct for inputs < 256. -/
def xtime (b : Nat) : Nat :=
  if b < 0x80 then b <<< 1 else (b <<< 1) ^^^ 0x11B

/-- `a · x^j` in the field: `j`-fold `xtime`. -/
def xtimePow (a : Nat) : Nat → Nat
  | 0 => a
  | j + 1 => xtime (xtimePow a j)

/-- Column `j` of `M_a`, the 8×8 GF(2) matrix of multiplication by the byte
    `a`: column j = a·x^j (a byte; bit i = entry (i, j)). -/
def Mcol (a : Nat) : Nat → Nat := xtimePow a

/-- Column `j` of the AES output linear layer `A`, built entrywise from the
    defining condition `A[i][j] = 1 ↔ (j − i) mod 8 ∈ {0,4,5,6,7}`
    (for i, j < 8 the integer `(j − i) mod 8` equals `(j + 8 − i) % 8` in ℕ). -/
def Acol (j : Nat) : Nat :=
  (List.range 8).foldl
    (fun acc i =>
      if (j + 8 - i) % 8 ∈ ([0, 4, 5, 6, 7] : List Nat) then acc ^^^ (1 <<< i) else acc)
    0

/-- Matrix–vector product over GF(2): xor of the columns of `M` selected by
    the low 8 bits of `v`. -/
def mulVec (M : Nat → Nat) (v : Nat) : Nat :=
  (if v.testBit 0 then M 0 else 0) ^^^ (if v.testBit 1 then M 1 else 0) ^^^
  (if v.testBit 2 then M 2 else 0) ^^^ (if v.testBit 3 then M 3 else 0) ^^^
  (if v.testBit 4 then M 4 else 0) ^^^ (if v.testBit 5 then M 5 else 0) ^^^
  (if v.testBit 6 then M 6 else 0) ^^^ (if v.testBit 7 then M 7 else 0)

/-- 8×8 GF(2) matrix product in column representation:
    column j of `M·N` is `M` applied to column j of `N`. -/
def matMul (M N : Nat → Nat) : Nat → Nat := fun j => mulVec M (N j)

/-- Field multiplication in GF(2^8): `a·b = M_a · b`. -/
def gmul (a b : Nat) : Nat := mulVec (Mcol a) b

/-- The linear layer as a byte map: `A · v`. -/
def aff (v : Nat) : Nat := mulVec Acol v

/-- `b^254` (= `b⁻¹` for `b ≠ 0`, and `0 ↦ 0`), by the addition chain
    254 = 2 + 4 + 8 + 16 + 32 + 64 + 128. -/
def ginv (b : Nat) : Nat :=
  let b2 := gmul b b
  let b4 := gmul b2 b2
  let b8 := gmul b4 b4
  let b16 := gmul b8 b8
  let b32 := gmul b16 b16
  let b64 := gmul b32 b32
  let b128 := gmul b64 b64
  gmul b2 (gmul b4 (gmul b8 (gmul b16 (gmul b32 (gmul b64 b128)))))

/-- The AES S-box: affine layer on the field inverse, then xor 0x63. -/
def sbox (b : Nat) : Nat := aff (ginv b) ^^^ 0x63

/-! ### Sanity anchors pinning the bit conventions (FIPS-197) -/

/-- Entrywise: bit i of column j of `A` is exactly the defining condition
    `A[i][j] = 1 ↔ (j − i) mod 8 ∈ {0,4,5,6,7}`. -/
theorem Acol_entry : ∀ i < 8, ∀ j < 8,
    ((Acol j).testBit i ↔ (j + 8 - i) % 8 ∈ ([0, 4, 5, 6, 7] : List Nat)) := by decide

/-- Column 0 of `A` has ones exactly in rows 0..4. -/
theorem Acol_zero : Acol 0 = 0x1F := by decide

theorem gmul_57_83 : gmul 0x57 0x83 = 0xC1 := by native_decide
theorem gmul_57_13 : gmul 0x57 0x13 = 0xFE := by native_decide
theorem ginv_53 : ginv 0x53 = 0xCA := by native_decide
theorem aff_01 : aff 0x01 = 0x1F := by native_decide
theorem sbox_53 : sbox 0x53 = 0xED := by native_decide
theorem sbox_01 : sbox 0x01 = 0x7C := by native_decide
theorem sbox_00 : sbox 0x00 = 0x63 := by native_decide

/-! ### Main theorem: the gauge stabilizer of A is trivial -/

/-- **Route C gauge stabilizer (main theorem).**  For all nonzero bytes
    `c, d`: if `M_d · A · M_c = A` as 8×8 matrices over GF(2) (equality of
    all 8 columns), then `c = 1` and `d = 1`.  65025 exhaustive 8×8 GF(2)
    matrix identities, discharged by `native_decide`. -/
theorem gauge_stab :
    ∀ c d : Fin 256, c ≠ 0 → d ≠ 0 →
      (∀ j : Fin 8, matMul (matMul (Mcol d.val) Acol) (Mcol c.val) j.val = Acol j.val) →
      c = 1 ∧ d = 1 := by
  native_decide

/-! ### GF(2)-linearity of the column representation (pure lemmas) -/

private instance : Std.Associative (α := Nat) (· ^^^ ·) := ⟨Nat.xor_assoc⟩
private instance : Std.Commutative (α := Nat) (· ^^^ ·) := ⟨Nat.xor_comm⟩

private theorem if_xor (p q : Bool) (m : Nat) :
    (if p ^^ q then m else 0) = (if p then m else 0) ^^^ (if q then m else 0) := by
  cases p <;> cases q <;> simp

theorem mulVec_zero (M : Nat → Nat) : mulVec M 0 = 0 := by
  simp [mulVec]

/-- `mulVec M` is additive (GF(2)-linear). -/
theorem mulVec_xor (M : Nat → Nat) (u w : Nat) :
    mulVec M (u ^^^ w) = mulVec M u ^^^ mulVec M w := by
  unfold mulVec
  simp only [Nat.testBit_xor, if_xor]
  ac_rfl

private theorem if_mulVec (M : Nat → Nat) (p : Bool) (w : Nat) :
    mulVec M (if p then w else 0) = if p then mulVec M w else 0 := by
  cases p <;> simp [mulVec_zero]

/-- The column representation is compositional: `(M·N)·v = M·(N·v)`. -/
theorem mulVec_matMul (M N : Nat → Nat) (v : Nat) :
    mulVec (matMul M N) v = mulVec M (mulVec N v) := by
  show _ = mulVec M
      ((if v.testBit 0 then N 0 else 0) ^^^ (if v.testBit 1 then N 1 else 0) ^^^
       (if v.testBit 2 then N 2 else 0) ^^^ (if v.testBit 3 then N 3 else 0) ^^^
       (if v.testBit 4 then N 4 else 0) ^^^ (if v.testBit 5 then N 5 else 0) ^^^
       (if v.testBit 6 then N 6 else 0) ^^^ (if v.testBit 7 then N 7 else 0))
  rw [mulVec_xor, mulVec_xor, mulVec_xor, mulVec_xor, mulVec_xor, mulVec_xor, mulVec_xor,
    if_mulVec, if_mulVec, if_mulVec, if_mulVec, if_mulVec, if_mulVec, if_mulVec, if_mulVec]
  rfl

/-- Matrix product associativity, columnwise. -/
theorem matMul_assoc (M N P : Nat → Nat) (j : Nat) :
    matMul (matMul M N) P j = matMul M (matMul N P) j :=
  mulVec_matMul M N (P j)

/-- Matrices agreeing on all 8 columns act identically on every vector. -/
theorem mulVec_congr {M N : Nat → Nat} (h : ∀ j, j < 8 → M j = N j) (v : Nat) :
    mulVec M v = mulVec N v := by
  unfold mulVec
  rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega),
    h 5 (by omega), h 6 (by omega), h 7 (by omega)]

/-! ### Group-structure facts about GF(2^8)^* (exhaustive certificates) -/

theorem gmul_lt : ∀ x < 256, ∀ y < 256, gmul x y < 256 := by native_decide

theorem gmul_ne_zero : ∀ x < 256, ∀ y < 256, x ≠ 0 → y ≠ 0 → gmul x y ≠ 0 := by native_decide

/-- `ginv` is a two-sided inverse on nonzero bytes. -/
theorem ginv_facts : ∀ b < 256, b ≠ 0 →
    gmul b (ginv b) = 1 ∧ gmul (ginv b) b = 1 ∧ ginv b < 256 ∧ ginv b ≠ 0 := by native_decide

/-- Multiplicativity of `a ↦ M_a`, columnwise: `M_{x·y} = M_x · M_y`. -/
theorem Mcol_gmul : ∀ x < 256, ∀ y < 256, ∀ j < 8,
    Mcol (gmul x y) j = mulVec (Mcol x) (Mcol y j) := by native_decide

/-- `M_1` is the identity on bytes. -/
theorem mulVec_Mcol_one : ∀ v < 256, mulVec (Mcol 1) v = v := by native_decide

/-- Uniqueness of inverses, right version. -/
theorem eq_ginv_of_gmul_right : ∀ x < 256, ∀ e < 256, gmul x e = 1 → x = ginv e := by
  native_decide

/-- Uniqueness of inverses, left version. -/
theorem eq_ginv_of_gmul_left : ∀ e < 256, ∀ y < 256, gmul e y = 1 → y = ginv e := by
  native_decide

/-- `A · M_1 = A`, columnwise. -/
theorem mulVec_Acol_Mcol_one : ∀ j < 8, mulVec Acol (Mcol 1 j) = Acol j := by decide

theorem Acol_lt : ∀ j < 8, Acol j < 256 := by decide

/-- Scalars slide through the column representation:
    `M_{x·y}` acts as `M_x` after `M_y`. -/
theorem gmul_mulVec (x y : Nat) (hx : x < 256) (hy : y < 256) (w : Nat) :
    mulVec (Mcol (gmul x y)) w = mulVec (Mcol x) (mulVec (Mcol y) w) :=
  (mulVec_congr (N := matMul (Mcol x) (Mcol y)) (fun j hj => Mcol_gmul x hx y hy j hj) w).trans
    (mulVec_matMul _ _ w)

/-! ### Corollary: gauge-table injectivity -/

/-- **Injectivity of the gauge table (corollary of `gauge_stab`).**
    On pairs of nonzero bytes, the map `(a, a') ↦ M_{a'} · A · M_a` is
    injective: if `M_{a'} · A · M_a = M_{b'} · A · M_b` (all 8 columns),
    then `a = b` and `a' = b'`. -/
theorem gauge_inj :
    ∀ a a' b b' : Fin 256, a ≠ 0 → a' ≠ 0 → b ≠ 0 → b' ≠ 0 →
      (∀ j : Fin 8,
        matMul (matMul (Mcol a'.val) Acol) (Mcol a.val) j.val
          = matMul (matMul (Mcol b'.val) Acol) (Mcol b.val) j.val) →
      a = b ∧ a' = b' := by
  intro a a' b b' ha ha' hb hb' H
  have hav : a.val ≠ 0 := fun h => ha (Fin.ext h)
  have ha'v : a'.val ≠ 0 := fun h => ha' (Fin.ext h)
  have hbv : b.val ≠ 0 := fun h => hb (Fin.ext h)
  have hb'v : b'.val ≠ 0 := fun h => hb' (Fin.ext h)
  obtain ⟨hbe, -, helt, hene⟩ := ginv_facts b.val b.isLt hbv
  obtain ⟨-, he'b', he'lt, he'ne⟩ := ginv_facts b'.val b'.isLt hb'v
  -- both gauge tables act identically on every byte (linearity upgrade of H)
  have Hv : ∀ w : Nat,
      mulVec (Mcol a'.val) (mulVec Acol (mulVec (Mcol a.val) w))
        = mulVec (Mcol b'.val) (mulVec Acol (mulVec (Mcol b.val) w)) := by
    intro w
    have h8 : ∀ j, j < 8 →
        matMul (Mcol a'.val) (matMul Acol (Mcol a.val)) j
          = matMul (Mcol b'.val) (matMul Acol (Mcol b.val)) j := fun j hj =>
      ((matMul_assoc _ _ _ j).symm.trans (H ⟨j, hj⟩)).trans (matMul_assoc _ _ _ j)
    have h := mulVec_congr h8 w
    rwa [mulVec_matMul, mulVec_matMul, mulVec_matMul, mulVec_matMul] at h
  -- the composite pair (c, d) = (a·b⁻¹, b'⁻¹·a') stabilizes A ...
  have K : ∀ j, j < 8 →
      matMul (matMul (Mcol (gmul (ginv b'.val) a'.val)) Acol)
          (Mcol (gmul a.val (ginv b.val))) j
        = Acol j := by
    intro j hj
    rw [matMul_assoc]
    show mulVec (Mcol (gmul (ginv b'.val) a'.val))
        (mulVec Acol (Mcol (gmul a.val (ginv b.val)) j)) = Acol j
    rw [Mcol_gmul a.val a.isLt (ginv b.val) helt j hj,
      gmul_mulVec (ginv b'.val) a'.val he'lt a'.isLt,
      Hv (Mcol (ginv b.val) j),
      ← Mcol_gmul b.val b.isLt (ginv b.val) helt j hj,
      hbe, mulVec_Acol_Mcol_one j hj,
      ← gmul_mulVec (ginv b'.val) b'.val he'lt b'.isLt,
      he'b']
    exact mulVec_Mcol_one (Acol j) (Acol_lt j hj)
  -- ... hence is the trivial pair, by the main theorem
  have hc256 : gmul a.val (ginv b.val) < 256 := gmul_lt a.val a.isLt (ginv b.val) helt
  have hd256 : gmul (ginv b'.val) a'.val < 256 := gmul_lt (ginv b'.val) he'lt a'.val a'.isLt
  have hc0 : gmul a.val (ginv b.val) ≠ 0 :=
    gmul_ne_zero a.val a.isLt (ginv b.val) helt hav hene
  have hd0 : gmul (ginv b'.val) a'.val ≠ 0 :=
    gmul_ne_zero (ginv b'.val) he'lt a'.val a'.isLt he'ne ha'v
  have main := gauge_stab ⟨_, hc256⟩ ⟨_, hd256⟩
    (fun h => hc0 (congrArg Fin.val h)) (fun h => hd0 (congrArg Fin.val h))
    (fun j => K j.val j.isLt)
  have hC1 : gmul a.val (ginv b.val) = 1 := congrArg Fin.val main.1
  have hD1 : gmul (ginv b'.val) a'.val = 1 := congrArg Fin.val main.2
  refine ⟨Fin.ext ?_, Fin.ext ?_⟩
  · exact (eq_ginv_of_gmul_right a.val a.isLt (ginv b.val) helt hC1).trans
      (eq_ginv_of_gmul_right b.val b.isLt (ginv b.val) helt hbe).symm
  · exact (eq_ginv_of_gmul_left (ginv b'.val) he'lt a'.val a'.isLt hD1).trans
      (eq_ginv_of_gmul_left (ginv b'.val) he'lt b'.val b'.isLt he'b').symm

end RouteCGaugeStab
