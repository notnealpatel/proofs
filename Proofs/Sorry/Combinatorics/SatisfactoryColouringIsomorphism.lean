/-
# n-satisfactory colourings from partial group isomorphisms

## Source

* MathOverflow question 26358, posted by Dömötör Pálvölgyi on 2010-05-29
  (https://mathoverflow.net/questions/26358).  Quoted as Question 1.1 of
  Caicedo–Chartier–Pach, "Coloring the n-smooth numbers with n colors",
  arXiv:1902.00446, Electron. J. Combin. 28 (2021) P1.34:

  > Given any positive integer $n$, is there a coloring of the positive integers
  > using $n$ colors such that for any positive integer $a$, the numbers
  > $a,2a,\dots,na$ all have different colors?

* The case `n + 1 = p` prime is KöMaL problem A.506 (Pálvölgyi, April 2010):
  "Prove that for every prime $p$, there exists a colouring of the positive
  integers with $p-1$ colours such that the colours of the numbers
  $\{a,2a,3a,\dots,(p-1)a\}$ are pairwise different for every positive integer $a$."

* CCP Theorem 1.4 (verbatim, items (1), (2), (4)):
  "Question 1.1 has a positive answer for $n$, that is, there is an
  $n$-satisfactory coloring, in any of the following cases: (1) $n+1$ is prime.
  (2) $2n+1$ is prime. … (4) Yet more generally, $n$ admits a partial
  $G$-isomorphism for some abelian group $(G,\oplus)$ of order $n$, i.e., there is
  a bijection $h\colon[n]\to G$ such that whenever $a,b\in[n]$, if $ab\in[n]$,
  then $h(ab)=h(a)\oplus h(b)$."
  Item (4) is CCP Theorem 5.3 ("If $h\colon [n]\to G$ is a partial
  $G$-isomorphism, then $h$ can be uniquely extended to a multiplicative map
  $\hat h\colon K_n \to G$. Moreover, $h^{-1}\circ\hat h$ … is a $G$-coloring").

Recorded 2026-10-21.

## Status

The three statements formalized here are proved in the literature (CCP 2021,
KöMaL A.506).  The general question (every `n`) is open; CCP report the least
open case `n = 195`, the least `n` with no partial `G`-isomorphism.  This module
does not address the open question.

## Formalization choices

* Colourings are maps `ℕ → C`; only their values at positive integers matter.
  "Using `n` colours" is `C = Fin n`.
* A partial `G`-isomorphism is a map `h : ℕ → G` that is a bijection
  `Set.Icc 1 n → G` (`Set.BijOn … Set.univ`), additive on products inside `[n]`.
  The order of `G` is then `n` (`card_eq_of_isPartialIso`); it is not assumed.
* The colouring is the completely additive extension
  `extend h m = ∑ₚ vₚ(m) • h p` over all primes `p ∣ m` (CCP use primes `≤ n`
  on the `n`-smooth numbers; values at larger primes are irrelevant).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.SatisfactoryColouringIsomorphism

/-- `c` is `n`-satisfactory: for every positive `a`, the numbers `a, 2a, …, na` receive
pairwise distinct colours. -/
def IsSatisfactory (n : ℕ) {C : Type*} (c : ℕ → C) : Prop :=
  ∀ a : ℕ, 0 < a → Set.InjOn (fun i => c (i * a)) (Set.Icc 1 n)

/-- `h` is a partial `G`-isomorphism on `[n] = {1, …, n}`: a bijection `[n] → G` with
`h (a * b) = h a + h b` whenever `a, b, a * b ∈ [n]`. -/
def IsPartialIso (n : ℕ) {G : Type*} [AddCommGroup G] (h : ℕ → G) : Prop :=
  Set.BijOn h (Set.Icc 1 n) Set.univ ∧
    ∀ a b : ℕ, a ∈ Set.Icc 1 n → b ∈ Set.Icc 1 n → a * b ∈ Set.Icc 1 n →
      h (a * b) = h a + h b

/-! ### Ground truth for the definitions -/

/-- The constant colouring is not `2`-satisfactory: `1` and `2` share a colour. -/
example : ¬ IsSatisfactory 2 fun _ => (0 : Fin 2) := by
  intro hc
  have h12 := hc 1 one_pos (show (1 : ℕ) ∈ Set.Icc 1 2 by simp)
    (show (2 : ℕ) ∈ Set.Icc 1 2 by simp) rfl
  omega

/-- With one colour, every colouring is `1`-satisfactory (only `i = 1` is in play). -/
example : IsSatisfactory 1 fun _ => (0 : Fin 1) := by
  intro a _ i hi j hj _
  simp only [Set.mem_Icc] at hi hj
  omega

/-- `1 ↦ 0, 2 ↦ 1` is a partial `ZMod 2`-isomorphism on `[2]`. -/
example : IsPartialIso 2 fun i => if i = 2 then (1 : ZMod 2) else 0 := by
  refine ⟨⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩, ?_⟩
  · intro i hi j hj hij
    simp only [Set.mem_Icc] at hi hj
    obtain ⟨hi1, hi2⟩ := hi
    obtain ⟨hj1, hj2⟩ := hj
    interval_cases i <;> interval_cases j <;> simp_all
  · intro g _
    fin_cases g
    · exact ⟨1, by simp, rfl⟩
    · exact ⟨2, by simp, rfl⟩
  · intro a b ha hb hab
    simp only [Set.mem_Icc] at ha hb hab
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    interval_cases a <;> interval_cases b <;> simp_all

/-- The reduction map is not a partial isomorphism on `[2]` into `ZMod 2`:
`h 1 = 1 ≠ 0`, violating `h (1 * 1) = h 1 + h 1`. -/
example : ¬ IsPartialIso 2 fun i => (i : ZMod 2) := by
  intro hh
  have h11 := hh.2 1 1 (by simp) (by simp) (by simp)
  revert h11
  decide

/-- The completely additive extension `m ↦ ∑ₚ vₚ(m) • h p` of `h` along prime factorizations. -/
noncomputable def extend {G : Type*} [AddCommGroup G] (h : ℕ → G) (m : ℕ) : G :=
  m.factorization.sum fun p k => k • h p

/-- The extension is additive on products of positive integers. -/
theorem extend_mul {G : Type*} [AddCommGroup G] (h : ℕ → G) {a b : ℕ} (ha : a ≠ 0)
    (hb : b ≠ 0) : extend h (a * b) = extend h a + extend h b := by
  unfold extend
  rw [Nat.factorization_mul ha hb, Finsupp.sum_add_index']
  · intro p
    simp
  · intro p k₁ k₂
    exact add_nsmul (h p) k₁ k₂

/-- The extension agrees with `h` at primes. -/
theorem extend_prime {G : Type*} [AddCommGroup G] (h : ℕ → G) {p : ℕ} (hp : p.Prime) :
    extend h p = h p := by
  simp [extend, hp.factorization, Finsupp.sum_single_index]

/-- A partial homomorphism on `[n]` coincides with its completely additive extension on `[n]`. -/
theorem extend_eq_of_mul {n : ℕ} {G : Type*} [AddCommGroup G] (h : ℕ → G)
    (hmul : ∀ a b : ℕ, a ∈ Set.Icc 1 n → b ∈ Set.Icc 1 n → a * b ∈ Set.Icc 1 n →
      h (a * b) = h a + h b) :
    ∀ i ∈ Set.Icc 1 n, extend h i = h i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    obtain ⟨hi1, hin⟩ := hi
    rcases Nat.eq_or_lt_of_le hi1 with rfl | hi2
    · have h11 := hmul 1 1 ⟨le_rfl, hin⟩ ⟨le_rfl, hin⟩ ⟨le_rfl, hin⟩
      rw [mul_one, left_eq_add] at h11
      simp [extend, h11]
    · set p := i.minFac with hp_def
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have hpi : p ∣ i := Nat.minFac_dvd i
      have hpos : 0 < i := by omega
      have hple : p ≤ i := Nat.minFac_le hpos
      have hq1 : 1 ≤ i / p := Nat.div_pos hple hp.pos
      have hqlt : i / p < i := Nat.div_lt_self hpos hp.one_lt
      have hqle : i / p ≤ i := Nat.div_le_self i p
      have hdecomp : p * (i / p) = i := Nat.mul_div_cancel' hpi
      have hpmem : p ∈ Set.Icc 1 n := ⟨hp.one_lt.le, hple.trans hin⟩
      have hqmem : i / p ∈ Set.Icc 1 n := ⟨hq1, hqle.trans hin⟩
      have himem : p * (i / p) ∈ Set.Icc 1 n := by rw [hdecomp]; exact ⟨hi1, hin⟩
      calc extend h i = extend h (p * (i / p)) := by rw [hdecomp]
        _ = extend h p + extend h (i / p) := extend_mul h hp.ne_zero (by omega)
        _ = h p + h (i / p) := by rw [extend_prime h hp, ih (i / p) hqlt hqmem]
        _ = h (p * (i / p)) := (hmul p (i / p) hpmem hqmem himem).symm
        _ = h i := by rw [hdecomp]

/-- The completely additive extension of a partial `G`-isomorphism is an `n`-satisfactory
`G`-valued colouring: `extend h (i * a) = h i + extend h a` and `h` is injective on `[n]`. -/
theorem isSatisfactory_extend {n : ℕ} {G : Type*} [AddCommGroup G] {h : ℕ → G}
    (hh : IsPartialIso n h) : IsSatisfactory n (extend h) := by
  intro a ha i hi j hj hij
  have hi0 : i ≠ 0 := by have := hi.1; omega
  have hj0 : j ≠ 0 := by have := hj.1; omega
  have hsplit : h i + extend h a = h j + extend h a := by
    rw [← extend_eq_of_mul h hh.2 i hi, ← extend_eq_of_mul h hh.2 j hj,
      ← extend_mul h hi0 ha.ne', ← extend_mul h hj0 ha.ne']
    exact hij
  exact hh.1.injOn hi hj (add_right_cancel hsplit)

/-- The number of elements of a group admitting a partial isomorphism on `[n]` is `n`. -/
theorem card_eq_of_isPartialIso {n : ℕ} {G : Type*} [AddCommGroup G] {h : ℕ → G}
    (hh : IsPartialIso n h) : Nat.card G = n := by
  rw [← Nat.card_univ, ← Nat.card_congr (hh.1.equiv h), ← Finset.coe_Icc,
    Nat.card_coe_set_eq, Set.ncard_coe_finset]
  simp

/-- **Caicedo–Chartier–Pach, Theorem 1.4(4) / Theorem 5.3.**  If `n` admits a partial
`G`-isomorphism for some abelian group `G` (necessarily of order `n`), then there is an
`n`-satisfactory colouring of the positive integers with `n` colours. -/
theorem exists_isSatisfactory_of_isPartialIso {n : ℕ} {G : Type*} [AddCommGroup G]
    {h : ℕ → G} (hh : IsPartialIso n h) : ∃ c : ℕ → Fin n, IsSatisfactory n c := by
  have hfin : Finite G :=
    Finite.of_equiv _ ((hh.1.equiv h).trans (Equiv.Set.univ G))
  let e : G ≃ Fin n := Finite.equivFinOfCardEq (card_eq_of_isPartialIso hh)
  refine ⟨fun m => e (extend h m), ?_⟩
  intro a ha
  exact e.injective.comp_injOn (isSatisfactory_extend hh a ha)

/-! ## Units of `ZMod p` indexed by natural numbers -/

/-- The unit of `ZMod p` represented by the natural number `i`, or `1` when `p ∣ i`. -/
noncomputable def unitOf (p : ℕ) [Fact p.Prime] (i : ℕ) : (ZMod p)ˣ :=
  if hi : (i : ZMod p) = 0 then 1 else Units.mk0 (i : ZMod p) hi

/-- Away from multiples of `p`, `unitOf p i` is the residue of `i`. -/
theorem coe_unitOf {p : ℕ} [Fact p.Prime] {i : ℕ} (hi : (i : ZMod p) ≠ 0) :
    (unitOf p i : ZMod p) = i := by
  simp [unitOf, hi]

/-- A natural number `1 ≤ i < p` has nonzero residue modulo `p`. -/
theorem natCast_ne_zero_of_lt {p i : ℕ} (hi : 1 ≤ i) (hip : i < p) : (i : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)

/-- `unitOf p` is multiplicative away from multiples of `p`. -/
theorem unitOf_mul {p : ℕ} [Fact p.Prime] {a b : ℕ} (ha : (a : ZMod p) ≠ 0)
    (hb : (b : ZMod p) ≠ 0) : unitOf p (a * b) = unitOf p a * unitOf p b := by
  have hab : ((a * b : ℕ) : ZMod p) ≠ 0 := by
    rw [Nat.cast_mul]
    exact mul_ne_zero ha hb
  ext
  rw [Units.val_mul, coe_unitOf hab, coe_unitOf ha, coe_unitOf hb, Nat.cast_mul]

/-- Every unit of `ZMod p` is `unitOf p k` for its canonical representative `1 ≤ k < p`. -/
theorem exists_unitOf_eq {p : ℕ} [Fact p.Prime] (u : (ZMod p)ˣ) :
    ∃ k : ℕ, 1 ≤ k ∧ k < p ∧ unitOf p k = u := by
  have hu : (u : ZMod p) ≠ 0 := u.ne_zero
  refine ⟨(u : ZMod p).val, ?_, ZMod.val_lt _, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr ((ZMod.val_ne_zero _).mpr hu)
  · ext
    rw [coe_unitOf (by rwa [ZMod.natCast_zmod_val]), ZMod.natCast_zmod_val]

/-- Distinct naturals in `[1, p)` give distinct units. -/
theorem unitOf_injOn {p : ℕ} [Fact p.Prime] {i j : ℕ} (hi : 1 ≤ i) (hip : i < p) (hj : 1 ≤ j)
    (hjp : j < p) (hij : unitOf p i = unitOf p j) : i = j := by
  have hcast : (i : ZMod p) = j := by
    rw [← coe_unitOf (natCast_ne_zero_of_lt hi hip), ← coe_unitOf (natCast_ne_zero_of_lt hj hjp),
      hij]
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hip, Nat.mod_eq_of_lt hjp] at hcast
  exact hcast

/-- Ground truth for `unitOf`: `unitOf 3 2` is the residue `2`, and `unitOf 3 6 = 1`. -/
example : ((unitOf 3 2 : (ZMod 3)ˣ) : ZMod 3) = 2 ∧ unitOf 3 6 = 1 := by
  refine ⟨coe_unitOf (by decide), ?_⟩
  simp only [unitOf]
  rw [dif_pos (by decide)]

/-! ## Case `n + 1` prime -/

/-- For `p = n + 1` prime, `i ↦ (i mod p)` is a partial isomorphism from `[n]` onto the
multiplicative group `(ZMod p)ˣ` (written additively). -/
theorem isPartialIso_unitOf {n : ℕ} [Fact (n + 1).Prime] :
    IsPartialIso n fun i => Additive.ofMul (unitOf (n + 1) i) := by
  refine ⟨⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩, ?_⟩
  · intro i hi j hj hij
    exact unitOf_injOn hi.1 (by have := hi.2; omega) hj.1 (by have := hj.2; omega)
      (Additive.ofMul.injective hij)
  · intro g _
    obtain ⟨k, hk1, hkp, hk⟩ := exists_unitOf_eq (Additive.toMul g)
    exact ⟨k, ⟨hk1, by omega⟩, by simp [hk]⟩
  · intro a b ha hb _
    simp only
    rw [unitOf_mul (natCast_ne_zero_of_lt ha.1 (by have := ha.2; omega))
      (natCast_ne_zero_of_lt hb.1 (by have := hb.2; omega)), ofMul_mul]

/-- Non-vacuity: the hypothesis of `exists_isSatisfactory_of_isPartialIso` holds at
`n = 4`, `G = (ZMod 5)ˣ`. -/
example : ∃ h : ℕ → Additive (ZMod 5)ˣ, IsPartialIso 4 h := by
  haveI : Fact (Nat.Prime (4 + 1)) := ⟨by norm_num⟩
  exact ⟨_, isPartialIso_unitOf⟩

/-- **KöMaL A.506 (Pálvölgyi); CCP Theorem 1.4(1).**  If `n + 1` is prime, there is an
`n`-satisfactory colouring of the positive integers with `n` colours. -/
theorem exists_isSatisfactory_of_prime_succ {n : ℕ} (hp : (n + 1).Prime) :
    ∃ c : ℕ → Fin n, IsSatisfactory n c := by
  haveI : Fact (n + 1).Prime := ⟨hp⟩
  exact exists_isSatisfactory_of_isPartialIso isPartialIso_unitOf

/-! ## Case `2 n + 1` prime -/

/-- The subgroup of squares of `(ZMod p)ˣ`, the range of the squaring homomorphism. -/
abbrev squares (p : ℕ) : Subgroup (ZMod p)ˣ :=
  (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range

/-- The squaring map `(ZMod p)ˣ → (ZMod p)ˣ` corestricted to the subgroup of squares. -/
abbrev sqToSquares (p : ℕ) : (ZMod p)ˣ →* squares p :=
  (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).rangeRestrict

/-- For `p = 2 n + 1` prime, `i ↦ i ^ 2 mod p` is a partial isomorphism from `[n]` onto the
subgroup of squares of `(ZMod p)ˣ` (written additively). -/
theorem isPartialIso_sqUnitOf {n p : ℕ} [Fact p.Prime] (hp_def : p = 2 * n + 1) :
    IsPartialIso n fun i => Additive.ofMul (sqToSquares p (unitOf p i)) := by
  refine ⟨⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩, ?_⟩
  · intro i hi j hj hij
    obtain ⟨hi1, hin⟩ := hi
    obtain ⟨hj1, hjn⟩ := hj
    have hsq : (unitOf p i : ZMod p) ^ 2 = (unitOf p j : ZMod p) ^ 2 := by
      have hij' : sqToSquares p (unitOf p i) = sqToSquares p (unitOf p j) :=
        Additive.ofMul.injective hij
      have h1 := congrArg (fun x : squares p => ((x : (ZMod p)ˣ) : ZMod p)) hij'
      simpa using h1
    rw [coe_unitOf (natCast_ne_zero_of_lt hi1 (by omega)),
      coe_unitOf (natCast_ne_zero_of_lt hj1 (by omega)), sq_eq_sq_iff_eq_or_eq_neg] at hsq
    rcases hsq with heq | hneg
    · rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega : i < p),
        Nat.mod_eq_of_lt (by omega : j < p)] at heq
      exact heq
    · have hsum : ((i + j : ℕ) : ZMod p) = 0 := by
        rw [Nat.cast_add, hneg, neg_add_cancel]
      exact absurd hsum (natCast_ne_zero_of_lt (by omega) (by omega))
  · intro g _
    obtain ⟨x, hx⟩ := (Additive.toMul g : squares p).2
    obtain ⟨k, hk1, hkp, hk⟩ := exists_unitOf_eq x
    by_cases hkn : k ≤ n
    · refine ⟨k, ⟨hk1, hkn⟩, ?_⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [← hx, ← hk]
      rfl
    · refine ⟨p - k, ⟨by omega, by omega⟩, ?_⟩
      have hneg : unitOf p (p - k) = -x := by
        ext
        rw [coe_unitOf (natCast_ne_zero_of_lt (by omega) (by omega)), Nat.cast_sub hkp.le,
          ZMod.natCast_self, zero_sub, Units.val_neg, ← hk,
          coe_unitOf (natCast_ne_zero_of_lt hk1 hkp)]
      apply Additive.toMul.injective
      apply Subtype.ext
      show unitOf p (p - k) ^ 2 = _
      rw [← hx, hneg, powMonoidHom_apply, neg_sq]
  · intro a b ha hb _
    simp only
    rw [unitOf_mul (natCast_ne_zero_of_lt ha.1 (by have := ha.2; omega))
      (natCast_ne_zero_of_lt hb.1 (by have := hb.2; omega)), map_mul, ofMul_mul]

/-- **CCP Theorem 1.4(2) / Corollary 5.6.**  If `2 n + 1` is prime, there is an
`n`-satisfactory colouring of the positive integers with `n` colours. -/
theorem exists_isSatisfactory_of_prime_two_mul_add_one {n : ℕ} (hp : (2 * n + 1).Prime) :
    ∃ c : ℕ → Fin n, IsSatisfactory n c := by
  haveI : Fact (2 * n + 1).Prime := ⟨hp⟩
  exact exists_isSatisfactory_of_isPartialIso (isPartialIso_sqUnitOf rfl)

end Candidates.SatisfactoryColouringIsomorphism
