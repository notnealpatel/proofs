/-
# Braun–Etzion–Vardy bound for binary linear subspace codes

Srikanth B. Pai, *A proof of the Braun–Etzion–Vardy bound for binary
subspace codes*, arXiv:2609.33719, Theorem `thm:main` (Section 3).
The bound was posed by Braun–Etzion–Vardy, LAA 438 (2013), Section 5,
Problem 1.

A binary linear subspace code `C ⊆ P_2(n)` contains the zero subspace and
carries an abelian group operation `⊞` with identity zero, `X ⊞ X = 0`,
and translation-invariant subspace distance
`d_S(X,Y) = dim X + dim Y - 2 dim(X ∩ Y)`. The bound is `|C| ≤ 2^n`.

## Formal rendering

The code `C` with its operation `⊞` is presented as an abstract finite
abelian group `G` together with an injective labelling
`f : G → Submodule (ZMod 2) (Fin n → ZMod 2)` sending the identity to the
zero subspace `⊥`; condition (ii) is `∀ g, g + g = 0` and condition (iii)
is translation invariance of `sdist ∘ f`.  The paper's own form, with the
group structure placed directly on a set `C` of subspaces, is the
corollary `natCard_le_two_pow_of_set`.

## Proof (following the paper, in its orthogonal-family form)

For each complex additive character `χ` of `G` put
`w_χ = ∑_X χ(X) 2^{-dim X/2} 1_X ∈ ℂ^{F_2^n}`.
* Gram entries: `⟨2^{-dim X/2} 1_X, 2^{-dim Y/2} 1_Y⟩ = 2^{-d_S(X,Y)/2}`,
  and `d_S(f x, f y) = dim f (x - y)` (BEV Lemma 6, from translation
  invariance with `z = -y`).
* Orthogonality: `⟨w_χ, w_ψ⟩ = (∑_x conj(χ x) ψ x) · (∑_z ψ(-z) 2^{-dim f z/2})`,
  and the first factor vanishes for `χ ≠ ψ`.
* Nonvanishing: the coordinate sum of `w_χ` is `∑_x χ(x) √2^{dim f x}`,
  with `χ(x) = ±1`.  Writing it as `A + √2 B` with `A, B ∈ ℤ`,
  vanishing forces `A² = 2B²`, but `A` is odd (the zero codeword gives
  `1`, every other even-dimensional codeword has dimension `≥ 2`).
* Hence `|G| = #characters ≤ dim ℂ^{F_2^n} = 2^n`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.BraunEtzionVardySubspaceCodes

open Module Finset

/-! ## Definitions -/

/-- The subspace distance `d_S(X,Y) = dim X + dim Y - 2 dim (X ∩ Y)` on subspaces of
`F_2^n`.  The natural-number subtraction never truncates, because
`dim (X ∩ Y) ≤ dim X` and `dim (X ∩ Y) ≤ dim Y`; see `sdist_add_two_mul_finrank_inf`. -/
noncomputable def sdist {n : ℕ} (X Y : Submodule (ZMod 2) (Fin n → ZMod 2)) : ℕ :=
  finrank (ZMod 2) X + finrank (ZMod 2) Y - 2 * finrank (ZMod 2) ↥(X ⊓ Y)

/-- The normalizing weight `2^{-k/2} = (√2)⁻¹ ^ k`. -/
noncomputable def wt (k : ℕ) : ℝ := (Real.sqrt 2)⁻¹ ^ k

/-! ## Basic facts about `sdist` -/

section Sdist

variable {n : ℕ}

/-- `d_S(X, 0) = dim X`. -/
lemma sdist_bot_right (X : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    sdist X ⊥ = finrank (ZMod 2) X := by
  unfold sdist
  rw [inf_bot_eq, finrank_bot]
  omega

/-- `d_S(X, X) = 0`. -/
lemma sdist_self (X : Submodule (ZMod 2) (Fin n → ZMod 2)) : sdist X X = 0 := by
  unfold sdist
  rw [inf_idem]
  omega

/-- `d_S` is symmetric. -/
lemma sdist_comm (X Y : Submodule (ZMod 2) (Fin n → ZMod 2)) : sdist X Y = sdist Y X := by
  unfold sdist
  rw [inf_comm, Nat.add_comm (finrank (ZMod 2) X)]

/-- The subtraction in `sdist` does not truncate:
`d_S(X,Y) + 2 dim (X ∩ Y) = dim X + dim Y`. -/
lemma sdist_add_two_mul_finrank_inf (X Y : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    sdist X Y + 2 * finrank (ZMod 2) ↥(X ⊓ Y) = finrank (ZMod 2) X + finrank (ZMod 2) Y := by
  have hX := Submodule.finrank_mono (inf_le_left : X ⊓ Y ≤ X)
  have hY := Submodule.finrank_mono (inf_le_right : X ⊓ Y ≤ Y)
  unfold sdist
  omega

open scoped Classical in
/-- A subspace `X` of `F_2^n` has `2 ^ dim X` points. -/
lemma sum_indicator_eq_two_pow (X : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    (∑ v : Fin n → ZMod 2, if v ∈ X then (1 : ℝ) else 0) = 2 ^ finrank (ZMod 2) X := by
  rw [Finset.sum_boole]
  have hc : Fintype.card ↥X = 2 ^ finrank (ZMod 2) X := by
    rw [card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  have hfilter : (Finset.univ.filter (fun v : Fin n → ZMod 2 => v ∈ X)).card =
      Fintype.card ↥X := by
    rw [Fintype.card_subtype]
  rw [hfilter, hc]
  push_cast
  rfl

end Sdist

/-! ## Examples for `sdist` -/

/-- `d_S(0, F_2^3) = 3`. -/
example : sdist (⊥ : Submodule (ZMod 2) (Fin 3 → ZMod 2)) ⊤ = 3 := by
  rw [sdist_comm, sdist_bot_right, finrank_top, Module.finrank_fin_fun]

/-- `d_S(F_2^3, F_2^3) = 0`. -/
example : sdist (⊤ : Submodule (ZMod 2) (Fin 3 → ZMod 2)) ⊤ = 0 := sdist_self _

/-! ## Arithmetic of the weights -/

/-- If `a + b = d + 2k` then `2^{-a/2} 2^{-b/2} 2^k = 2^{-d/2}`. -/
lemma wt_mul_wt_mul_two_pow {a b d k : ℕ} (h : a + b = d + 2 * k) :
    wt a * wt b * 2 ^ k = wt d := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold wt
  rw [← pow_add, h, pow_add, pow_mul, inv_pow (Real.sqrt 2) 2, hs2, mul_assoc,
    ← mul_pow, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow, mul_one]

/-- `2^{-d/2} · 2^d = √2^d`. -/
lemma wt_mul_two_pow (d : ℕ) : wt d * 2 ^ d = Real.sqrt 2 ^ d := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have h2d : (2 : ℝ) ^ d = Real.sqrt 2 ^ d * Real.sqrt 2 ^ d := by
    rw [← mul_pow, Real.mul_self_sqrt (by norm_num)]
  unfold wt
  rw [h2d, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hs, one_pow, one_mul]

/-- The parity step of the paper (eq. `parity`): if `ε i = ±1`, `d i₀ = 0` and `d i ≠ 0`
for `i ≠ i₀`, then `∑ ε i √2^{d i} ≠ 0`.  Writing the sum as `A + √2 B` with
`A, B ∈ ℤ`, vanishing gives `A² = 2 B²`, while `A` is odd. -/
lemma sum_sign_mul_sqrt_two_pow_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι)
    (ε : ι → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) (d : ι → ℕ) (hd0 : d i0 = 0)
    (hd : ∀ i, i ≠ i0 → d i ≠ 0) :
    ∑ i, (ε i : ℝ) * Real.sqrt 2 ^ d i ≠ 0 := by
  set A : ℤ := ∑ i, if d i % 2 = 0 then ε i * 2 ^ (d i / 2) else 0 with hA
  set B : ℤ := ∑ i, if d i % 2 = 0 then 0 else ε i * 2 ^ (d i / 2) with hB
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hterm : ∀ i, (ε i : ℝ) * Real.sqrt 2 ^ d i =
      ((if d i % 2 = 0 then ε i * 2 ^ (d i / 2) else 0 : ℤ) : ℝ) +
        Real.sqrt 2 * ((if d i % 2 = 0 then 0 else ε i * 2 ^ (d i / 2) : ℤ) : ℝ) := by
    intro i
    have hdecomp : Real.sqrt 2 ^ d i = (2 : ℝ) ^ (d i / 2) * Real.sqrt 2 ^ (d i % 2) := by
      conv_lhs => rw [← Nat.div_add_mod (d i) 2]
      rw [pow_add, pow_mul, hs2]
    rcases Nat.mod_two_eq_zero_or_one (d i) with h | h
    · simp [h, hdecomp]
    · simp only [hdecomp, h, pow_one, one_ne_zero, ↓reduceIte, Int.cast_zero, Int.cast_mul,
        Int.cast_pow, Int.cast_ofNat, zero_add]
      ring
  have hsum : ∑ i, (ε i : ℝ) * Real.sqrt 2 ^ d i = (A : ℝ) + Real.sqrt 2 * (B : ℝ) := by
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, ← Finset.mul_sum]
    push_cast [hA, hB]
    rfl
  have h20 : (2 : ZMod 2) = 0 := by decide
  have hAmod : (A : ZMod 2) = 1 := by
    rw [hA]
    push_cast
    rw [Finset.sum_eq_single i0]
    · rcases hε i0 with h | h <;> simp [h, hd0]
    · intro i _ hi
      split_ifs with hmod
      · have hpos : d i / 2 ≠ 0 := by
          have hdi := hd i hi
          omega
        rw [h20, zero_pow hpos, mul_zero]
      · rfl
    · intro h
      exact absurd (Finset.mem_univ i0) h
  intro hzero
  rw [hsum] at hzero
  have hAB : (A : ℝ) ^ 2 = 2 * (B : ℝ) ^ 2 := by
    have hA' : (A : ℝ) = -(Real.sqrt 2 * B) := by linarith
    rw [hA', neg_sq, mul_pow, hs2]
  have hABz : A ^ 2 = 2 * B ^ 2 := by exact_mod_cast hAB
  have hmod := congrArg (fun z : ℤ => (z : ZMod 2)) hABz
  push_cast at hmod
  rw [hAmod, h20, zero_mul] at hmod
  exact one_ne_zero hmod

/-! ## Normalized indicators and character vectors -/

section Vectors

variable {n : ℕ} {G : Type*} [AddCommGroup G]

/-- BEV Lemma 6 (paper eq. `dim-identity`): translation invariance gives
`dim f (x - y) = d_S(f x, f y)`. -/
lemma finrank_sub_eq_sdist (f : G → Submodule (ZMod 2) (Fin n → ZMod 2)) (hf0 : f 0 = ⊥)
    (htrans : ∀ x y z : G, sdist (f (x + z)) (f (y + z)) = sdist (f x) (f y)) (x y : G) :
    finrank (ZMod 2) (f (x - y)) = sdist (f x) (f y) := by
  have h := htrans x y (-y)
  rwa [← sub_eq_add_neg, add_neg_cancel, hf0, sdist_bot_right] at h

open scoped Classical in
/-- The normalized indicator `2^{-dim X/2} 1_X` of the codeword `X = f x`, as a real
function on `F_2^n`. -/
noncomputable def nvec (f : G → Submodule (ZMod 2) (Fin n → ZMod 2)) (x : G)
    (v : Fin n → ZMod 2) : ℝ :=
  wt (finrank (ZMod 2) (f x)) * if v ∈ f x then 1 else 0

/-- Gram entries (paper eq. `gram-entry`): the inner product of two normalized indicators
is `2^{-d_S/2} = 2^{-dim f (x - y)/2}`. -/
lemma sum_nvec_mul_nvec (f : G → Submodule (ZMod 2) (Fin n → ZMod 2)) (hf0 : f 0 = ⊥)
    (htrans : ∀ x y z : G, sdist (f (x + z)) (f (y + z)) = sdist (f x) (f y)) (x y : G) :
    ∑ v, nvec f x v * nvec f y v = wt (finrank (ZMod 2) (f (x - y))) := by
  classical
  have hind : ∀ v, nvec f x v * nvec f y v =
      wt (finrank (ZMod 2) (f x)) * wt (finrank (ZMod 2) (f y)) *
        (if v ∈ f x ⊓ f y then 1 else 0) := by
    intro v
    unfold nvec
    by_cases hx : v ∈ f x <;> by_cases hy : v ∈ f y <;> simp [hx, hy, Submodule.mem_inf]
  rw [Finset.sum_congr rfl (fun v _ => hind v), ← Finset.mul_sum, sum_indicator_eq_two_pow]
  apply wt_mul_wt_mul_two_pow
  rw [finrank_sub_eq_sdist f hf0 htrans, sdist_add_two_mul_finrank_inf]

omit [AddCommGroup G] in
/-- The coordinate sum of a normalized indicator is `2^{-dim X/2} · 2^{dim X} = √2^{dim X}`. -/
lemma sum_nvec (f : G → Submodule (ZMod 2) (Fin n → ZMod 2)) (x : G) :
    ∑ v, nvec f x v = Real.sqrt 2 ^ finrank (ZMod 2) (f x) := by
  classical
  unfold nvec
  rw [← Finset.mul_sum, sum_indicator_eq_two_pow, wt_mul_two_pow]

variable [Fintype G]

/-- The character vector `w_χ = ∑_x χ(x) 2^{-dim f x/2} 1_{f x}` in `ℂ^{F_2^n}`. -/
noncomputable def charVec (f : G → Submodule (ZMod 2) (Fin n → ZMod 2)) (χ : AddChar G ℂ) :
    EuclideanSpace ℂ (Fin n → ZMod 2) :=
  WithLp.toLp 2 (fun v => ∑ x, χ x * (nvec f x v : ℂ))

/-- Expansion of `⟨w_χ, w_ψ⟩` through the Gram entries. -/
lemma inner_charVec (f : G → Submodule (ZMod 2) (Fin n → ZMod 2)) (hf0 : f 0 = ⊥)
    (htrans : ∀ x y z : G, sdist (f (x + z)) (f (y + z)) = sdist (f x) (f y))
    (χ ψ : AddChar G ℂ) :
    inner ℂ (charVec f χ) (charVec f ψ) =
      ∑ x, ∑ y, (starRingEnd ℂ) (χ x) * ψ y * (wt (finrank (ZMod 2) (f (x - y))) : ℂ) := by
  simp only [charVec, PiLp.inner_apply, RCLike.inner_apply, map_sum, map_mul,
    Complex.conj_ofReal, Finset.sum_mul_sum]
  have hv : ∀ v, ∑ i, ∑ j, ψ i * (nvec f i v : ℂ) * ((starRingEnd ℂ) (χ j) * (nvec f j v : ℂ)) =
      ∑ j, ∑ i, (starRingEnd ℂ) (χ j) * ψ i * ((nvec f j v * nvec f i v : ℝ) : ℂ) := by
    intro v
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun v _ => hv v), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [← Finset.mul_sum, ← Complex.ofReal_sum, sum_nvec_mul_nvec f hf0 htrans]

/-- Orthogonality (paper Proposition `prop:eigen`): the Gram kernel depends only on
`x - y`, so distinct characters give orthogonal vectors. -/
lemma inner_charVec_eq_zero (f : G → Submodule (ZMod 2) (Fin n → ZMod 2)) (hf0 : f 0 = ⊥)
    (htrans : ∀ x y z : G, sdist (f (x + z)) (f (y + z)) = sdist (f x) (f y))
    {χ ψ : AddChar G ℂ} (hne : χ ≠ ψ) :
    inner ℂ (charVec f χ) (charVec f ψ) = 0 := by
  rw [inner_charVec f hf0 htrans]
  have hre : ∀ x, ∑ y, (starRingEnd ℂ) (χ x) * ψ y * (wt (finrank (ZMod 2) (f (x - y))) : ℂ) =
      ((starRingEnd ℂ) (χ x) * ψ x) *
        ∑ z, ψ (-z) * (wt (finrank (ZMod 2) (f z)) : ℂ) := by
    intro x
    rw [← Fintype.sum_equiv (Equiv.subLeft x) (fun z => (starRingEnd ℂ) (χ x) * ψ (x - z) *
      (wt (finrank (ZMod 2) (f (x - (x - z)))) : ℂ)) _ (fun z => rfl), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [sub_sub_cancel, sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun x _ => hre x), ← Finset.sum_mul]
  have horth : ∑ x, (starRingEnd ℂ) (χ x) * ψ x = 0 := by
    have h := (AddChar.sum_eq_zero_iff_ne_zero (ψ := ψ - χ)).mpr (sub_ne_zero.mpr hne.symm)
    rw [← h]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [AddChar.sub_apply, AddChar.map_neg_eq_conj, mul_comm]
  rw [horth, zero_mul]

/-- Nonvanishing (paper Theorem `thm:main`, eqs. `coord`–`parity`): for an elementary
abelian `2`-group, every character vector is nonzero. -/
lemma charVec_ne_zero (h2 : ∀ g : G, g + g = 0)
    (f : G → Submodule (ZMod 2) (Fin n → ZMod 2)) (hf : Function.Injective f)
    (hf0 : f 0 = ⊥) (χ : AddChar G ℂ) :
    charVec f χ ≠ 0 := by
  classical
  intro hzero
  have hsign : ∀ x, χ x = 1 ∨ χ x = -1 := by
    intro x
    have hsq : χ x * χ x = 1 := by
      rw [← AddChar.map_add_eq_mul, h2, AddChar.map_zero_eq_one]
    exact mul_self_eq_one_iff.mp hsq
  let ε : G → ℤ := fun x => if χ x = 1 then 1 else -1
  have hε : ∀ x, ((ε x : ℤ) : ℂ) = χ x := by
    intro x
    rcases hsign x with h | h
    · simp [ε, h]
    · have hne : χ x ≠ 1 := by
        rw [h]
        norm_num
      simp only [ε, hne, if_false]
      push_cast
      rw [h]
  have hsum : ∑ v, (charVec f χ).ofLp v = 0 := by
    rw [hzero]
    simp
  have hcomp : ∑ v, (charVec f χ).ofLp v =
      ((∑ x, (ε x : ℝ) * Real.sqrt 2 ^ finrank (ZMod 2) (f x) : ℝ) : ℂ) := by
    simp only [charVec, WithLp.ofLp_toLp]
    rw [Finset.sum_comm]
    push_cast
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Finset.mul_sum, ← Complex.ofReal_sum, sum_nvec, hε]
    push_cast
    rfl
  have hreal : ∑ x, (ε x : ℝ) * Real.sqrt 2 ^ finrank (ZMod 2) (f x) = 0 := by
    have hc := hcomp.symm.trans hsum
    exact_mod_cast hc
  refine sum_sign_mul_sqrt_two_pow_ne_zero 0 ε (fun x => ?_) (fun x => finrank (ZMod 2) (f x))
    ?_ (fun x hx => ?_) hreal
  · by_cases h : χ x = 1 <;> simp [ε, h]
  · simp [hf0]
  · intro hdim
    exact hx (hf ((Submodule.finrank_eq_zero.mp hdim).trans hf0.symm))

end Vectors

/-! ## Main theorem -/

/-- **Braun–Etzion–Vardy bound** (arXiv:2609.33719, Theorem `thm:main`; conjectured by
Braun, Etzion and Vardy 2013, Section 5, Problem 1).  Let `G` be a finite abelian group
with `g + g = 0` for all `g` (an elementary abelian `2`-group), and let
`f : G → P_2(n)` be an injective labelling of `G` by subspaces of `F_2^n` with
`f 0 = 0` such that the subspace distance is translation invariant:
`d_S(f (x + z), f (y + z)) = d_S(f x, f y)`.  Then `|G| ≤ 2^n`.  Equivalently, every
binary linear subspace code `C ⊆ P_2(n)` (with `C = f(G)` and `⊞` transported from `G`)
has `|C| ≤ 2^n`. -/
theorem card_le_two_pow {n : ℕ} {G : Type*} [AddCommGroup G] [Fintype G]
    (h2 : ∀ g : G, g + g = 0)
    (f : G → Submodule (ZMod 2) (Fin n → ZMod 2)) (hf : Function.Injective f)
    (hf0 : f 0 = ⊥)
    (htrans : ∀ x y z : G, sdist (f (x + z)) (f (y + z)) = sdist (f x) (f y)) :
    Fintype.card G ≤ 2 ^ n := by
  classical
  have hli : LinearIndependent ℂ (charVec f) :=
    linearIndependent_of_ne_zero_of_inner_eq_zero (fun χ => charVec_ne_zero h2 f hf hf0 χ)
      (fun _ _ hne => inner_charVec_eq_zero f hf0 htrans hne)
  have hcard := hli.fintype_card_le_finrank
  rw [AddChar.card_eq, finrank_euclideanSpace] at hcard
  simpa using hcard

/-- **Braun–Etzion–Vardy bound, paper form** (arXiv:2609.33719, Definition
`def:linear-code` and Theorem `thm:main`).  Let `C` be a set of subspaces of `F_2^n`
carrying an abelian group structure `⊞` whose identity is the zero subspace, with
`X ⊞ X = 0` for all `X ∈ C`, under which the subspace distance is translation invariant.
Then `|C| ≤ 2^n`. -/
theorem natCard_le_two_pow_of_set {n : ℕ} (C : Set (Submodule (ZMod 2) (Fin n → ZMod 2)))
    [AddCommGroup C] (h0 : ((0 : C) : Submodule (ZMod 2) (Fin n → ZMod 2)) = ⊥)
    (h2 : ∀ X : C, X + X = 0)
    (htrans : ∀ X Y Z : C, sdist ((X + Z : C) : Submodule (ZMod 2) (Fin n → ZMod 2))
      ((Y + Z : C) : Submodule (ZMod 2) (Fin n → ZMod 2)) = sdist (X : Submodule (ZMod 2) (Fin n → ZMod 2)) (Y : Submodule (ZMod 2) (Fin n → ZMod 2))) :
    Nat.card C ≤ 2 ^ n := by
  classical
  let _ : Fintype C := Fintype.ofFinite C
  rw [Nat.card_eq_fintype_card]
  exact card_le_two_pow h2 Subtype.val Subtype.val_injective h0 htrans

/-! ## Non-vacuity: a two-word linear subspace code in `P_2(1)` -/

/-- The code `{0, F_2^1}` indexed by `ZMod 2`. -/
noncomputable def codeTwo (g : ZMod 2) : Submodule (ZMod 2) (Fin 1 → ZMod 2) :=
  if g = 0 then ⊥ else ⊤

/-- The hypotheses of `card_le_two_pow` hold jointly for `codeTwo`, and the bound is
attained: `|ZMod 2| = 2 = 2^1`. -/
example : Fintype.card (ZMod 2) ≤ 2 ^ 1 := by
  have hval : ∀ g : ZMod 2, g = 0 ∨ g = 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have hc0 : codeTwo 0 = ⊥ := by simp [codeTwo]
  have hc1 : codeTwo 1 = ⊤ := by simp [codeTwo, h10]
  have hbt : (⊥ : Submodule (ZMod 2) (Fin 1 → ZMod 2)) ≠ ⊤ := by
    intro h
    have hmem : (fun _ => 1 : Fin 1 → ZMod 2) ∈ (⊥ : Submodule (ZMod 2) (Fin 1 → ZMod 2)) := by
      rw [h]
      exact Submodule.mem_top
    rw [Submodule.mem_bot] at hmem
    exact h10 (congrFun hmem 0)
  have hinj : Function.Injective codeTwo := by
    intro a b hab
    rcases hval a with rfl | rfl <;> rcases hval b with rfl | rfl
    · rfl
    · rw [hc0, hc1] at hab
      exact absurd hab hbt
    · rw [hc0, hc1] at hab
      exact absurd hab.symm hbt
    · rfl
  have htrans : ∀ x y z : ZMod 2,
      sdist (codeTwo (x + z)) (codeTwo (y + z)) = sdist (codeTwo x) (codeTwo y) := by
    intro x y z
    rcases hval x with rfl | rfl <;> rcases hval y with rfl | rfl <;>
      rcases hval z with rfl | rfl <;>
      simp only [h11, add_zero, zero_add, hc0, hc1, sdist_self] <;>
      exact sdist_comm _ _
  have h2 : ∀ g : ZMod 2, g + g = 0 := by decide
  exact card_le_two_pow h2 codeTwo hinj hc0 htrans

end Candidates.BraunEtzionVardySubspaceCodes
