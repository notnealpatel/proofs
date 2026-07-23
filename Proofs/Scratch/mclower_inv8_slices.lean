/-
  Scratch/mclower_inv8_slices — MCLOWER campaign computational spine, in Lean.

  Setting.  GF(2^8) = GF(2)[x]/(x^8 + x^4 + x^3 + x + 1) (the AES field,
  reduction mask 0x11B); a byte b encodes the field element with bit i =
  coefficient of x^i (LSB-first).  Field multiplication `gmul`, inverse
  `ginv b = b^254` (0 ↦ 0), and absolute trace `gtr` are the standard
  computable maps.  Conventions and the addition-chain inverse are copied
  verbatim from Scratch/RouteCGaugeStab.lean, whose FIPS-197 anchors
  (`ginv 0x53 = 0xCA`, etc.) pin the bit ordering.

  What this file certifies (all `native_decide`, sorry-free):

  * `ginv_53`, `gmul_57_83` : FIPS-197 sanity anchors pinning the field/bit
    order (so the ANF computation below is over the right function).
  * `inv_correct` : gmul x (ginv x) = 1 for every nonzero byte x — ginv is
    genuine field inversion.
  * `coord_degrees_all_7` : all 8 coordinate functions of x ↦ x^254 have
    algebraic degree exactly 7 (ANF via Möbius over all 256 points).
  * `rank_D7_eq_8` : the 8×8 GF(2) matrix of degree-7 ANF slices of the
    coordinates has rank 8.  This is `k = 8`, the SOLE functional hypothesis
    of the Boyar–Find transfer giving MC(inv₈) ≥ 13, and by the
    trace-form bijection it is equivalent to "all 255 components have degree
    7".  Step-3 saturation (k ≤ dim Λ⁷ = 8) is met with equality.
  * `rank_D6_eq_8` : the 8×28 GF(2) matrix of degree-6 ANF slices of the
    coordinates also has rank 8.  Hence inversion's forced slice-coupling map
    φ : Λ⁷ → Λ⁶ is INJECTIVE (rank 8).  This is the level-6 maximality that
    makes the MCLOWER "defect ladder" dimensionally graceful — the precise
    reason the linear slice weapon (W1) cannot force MC ≥ 14 (see
    .tasks/f5exp/docs/mclower-campaign.md §S1.2).
  * `components_all_degree_7` : all 255 nonzero components Tr(b·x^254) have
    algebraic degree exactly 7 (independent trace-based recheck of `k = 8`).

  These are the finite inputs; the reduction "no 13-AND circuit ⇒ MC ≥ 14"
  is the structural (★★) argument in the campaign notes, not a finite check.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib

namespace MCLowerInv8

/-! ### The AES field, inversion, and trace (computable) -/

/-- Multiplication by x in GF(2^8) modulo x^8+x^4+x^3+x+1 (0x11B). -/
def xtime (b : Nat) : Nat :=
  if b < 0x80 then b <<< 1 else (b <<< 1) ^^^ 0x11B

/-- `a · x^j` in the field: `j`-fold `xtime`. -/
def xtimePow (a : Nat) : Nat → Nat
  | 0 => a
  | j + 1 => xtime (xtimePow a j)

/-- Matrix–vector product over GF(2): xor of the columns `M 0..M 7` selected
    by the low 8 bits of `v`. -/
def mulVec (M : Nat → Nat) (v : Nat) : Nat :=
  (if v.testBit 0 then M 0 else 0) ^^^ (if v.testBit 1 then M 1 else 0) ^^^
  (if v.testBit 2 then M 2 else 0) ^^^ (if v.testBit 3 then M 3 else 0) ^^^
  (if v.testBit 4 then M 4 else 0) ^^^ (if v.testBit 5 then M 5 else 0) ^^^
  (if v.testBit 6 then M 6 else 0) ^^^ (if v.testBit 7 then M 7 else 0)

/-- Field multiplication in GF(2^8): `a·b = M_a · b`. -/
def gmul (a b : Nat) : Nat := mulVec (xtimePow a) b

/-- `b^254` (= `b⁻¹` for `b ≠ 0`, and `0 ↦ 0`), addition chain
    254 = 2+4+8+16+32+64+128. -/
def ginv (b : Nat) : Nat :=
  let b2 := gmul b b
  let b4 := gmul b2 b2
  let b8 := gmul b4 b4
  let b16 := gmul b8 b8
  let b32 := gmul b16 b16
  let b64 := gmul b32 b32
  let b128 := gmul b64 b64
  gmul b2 (gmul b4 (gmul b8 (gmul b16 (gmul b32 (gmul b64 b128)))))

/-- Absolute trace GF(2^8) → GF(2): `y + y² + y⁴ + … + y^128`, a byte in
    {0,1}. -/
def gtr (y : Nat) : Nat := Id.run do
  let mut acc := 0
  let mut cur := y
  for _ in [0:8] do
    acc := acc ^^^ cur
    cur := gmul cur cur
  return acc &&& 1

/-! ### FIPS-197 anchors + inversion correctness -/

theorem gmul_57_83 : gmul 0x57 0x83 = 0xC1 := by native_decide
theorem ginv_53 : ginv 0x53 = 0xCA := by native_decide

/-- `ginv` is genuine field inversion: `x · x⁻¹ = 1` for every nonzero byte. -/
theorem inv_correct :
    (List.range 255).all (fun k => gmul (k + 1) (ginv (k + 1)) == 1) = true := by
  native_decide

/-! ### ANF via the Möbius transform, and algebraic degree -/

/-- Möbius transform on a length-256 truth table: ANF coefficients over GF(2).
    Eight rank-passes `k = 1,2,…,128`, each xoring `a[i] ^= a[i xor k]` for
    `i` with bit set. -/
def mobius (tt : Array Nat) : Array Nat := Id.run do
  let mut a := tt
  for kb in [0:8] do
    let k := 1 <<< kb
    for i in [0:256] do
      if i &&& k ≠ 0 then
        a := a.set! i (a[i]! ^^^ a[i ^^^ k]!)
  return a

/-- Hamming weight of a monomial index (over 8 bits). -/
def popcount (i : Nat) : Nat :=
  (List.range 8).foldl (fun acc b => if i.testBit b then acc + 1 else acc) 0

/-- Algebraic degree of a function given its 256-entry ANF coefficient array. -/
def anfDegree (anf : Array Nat) : Nat :=
  (List.range 256).foldl
    (fun d i => if anf[i]! = 1 then max d (popcount i) else d) 0

/-- Truth table of coordinate `i` of `x ↦ x^254` (bit `i` of `ginv x`). -/
def coordTT (i : Nat) : Array Nat :=
  (Array.range 256).map (fun x => (ginv x >>> i) &&& 1)

/-- ANF of coordinate `i`. -/
def coordANF (i : Nat) : Array Nat := mobius (coordTT i)

/-- All eight coordinate functions of `x ↦ x^254` have degree exactly 7. -/
theorem coord_degrees_all_7 :
    (List.range 8).all (fun i => anfDegree (coordANF i) == 7) = true := by
  native_decide

/-! ### GF(2) rank of the degree-7 and degree-6 slice matrices -/

/-- Position of the most significant set bit of `n` (0 if `n = 0`). -/
def highBit (n : Nat) : Nat :=
  (List.range 32).foldl (fun acc b => if n.testBit b then b else acc) 0

/-- Rank over GF(2) of a list of bitmask row-vectors, via XOR linear basis. -/
def rankGF2 (rows : List Nat) : Nat := Id.run do
  let mut basis : Array Nat := #[]
  for v0 in rows do
    let mut v := v0
    for b in basis do
      if v.testBit (highBit b) then
        v := v ^^^ b
    if v ≠ 0 then
      basis := basis.push v
  return basis.size

/-- Slice row of coordinate `i` at weight `w`, packed as a bitmask: iterate
    monomial masks `m = 0..255` in order, and for each of weight `w` append
    the ANF coefficient as the next bit.  (The packing order is irrelevant to
    the GF(2) rank.) -/
def sliceRow (w i : Nat) : Nat :=
  let anf := coordANF i
  Id.run do
    let mut acc := 0
    let mut k := 0
    for m in [0:256] do
      if popcount m = w then
        if anf[m]! = 1 then acc := acc ||| (1 <<< k)
        k := k + 1
    return acc

/-- Degree-7 slice row of coordinate `i` (8-bit). -/
def d7row (i : Nat) : Nat := sliceRow 7 i

/-- Degree-6 slice row of coordinate `i` (28-bit). -/
def d6row (i : Nat) : Nat := sliceRow 6 i

/-- The 8×8 degree-7 slice matrix of the coordinates has full rank 8:
    this is `k = 8`, the sole functional hypothesis behind MC(inv₈) ≥ 13,
    with Step-3 cap `k ≤ dim Λ⁷ = 8` met at equality. -/
theorem rank_D7_eq_8 :
    rankGF2 ((List.range 8).map d7row) = 8 := by native_decide

/-- The 8×28 degree-6 slice matrix of the coordinates also has rank 8:
    inversion's slice-coupling map φ : Λ⁷ → Λ⁶ is injective (level-6
    maximality). -/
theorem rank_D6_eq_8 :
    rankGF2 ((List.range 8).map d6row) = 8 := by native_decide

/-! ### Independent trace-based recheck of `k = 8` -/

/-- Truth table of the component `x ↦ Tr(b · x^254)`. -/
def compTT (b : Nat) : Array Nat :=
  (Array.range 256).map (fun x => gtr (gmul b (ginv x)))

/-- All 255 nonzero components `Tr(b·x^254)` have algebraic degree exactly 7. -/
theorem components_all_degree_7 :
    (List.range 255).all (fun k => anfDegree (mobius (compTT (k + 1))) == 7) = true := by
  native_decide

end MCLowerInv8
