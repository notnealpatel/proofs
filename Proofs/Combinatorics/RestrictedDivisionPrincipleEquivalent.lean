/-
# Restricted and full Euclidean division are equivalent over PA⁻

## Source

Naoya Kato, *Equivalence of Restricted and Full Division*,
arXiv:2610.24976 (recorded 2026-10-21).  The axioms pa1–pa13, pa15 are in
Section 2.1, the "standard consequences" in Lemma 2 (Section 2.2, asserted
without proof in the paper), the quotient-preserving transformation is
Theorem 3, the transfer to a co-prime pair is Corollary 4, and the main
equivalence is Corollary 5.  The result answers Visser's Open Question 8.29
(A. Visser, *From Numbers to Container Strings*, arXiv:2411.15873).

## Verbatim informal claim (Corollary 5)

  PA⁻ ⊢ (pa17⁻ ↔ pa17),

where `euc(a,b) :⟺ ∃q ∃r (b = aq + r ∧ r < a)`,
`cop(a,b) :⟺ ∃c ∃d (ad = bc + 1)`,
`pa17⁻ : ∀a ∀b (cop(a,b) → euc(a,b))` and
`pa17 : ∀a ∀b (a ≠ 0 → euc(a,b))`.

## Status

Proved in the paper.

## Formalization choices

* The theory PA⁻ is the class `PAMinus` whose fields are exactly the
  paper's fourteen axioms pa1–pa13 and pa15, with the paper's numbering.
  There is deliberately no antisymmetry, cancellation, `x * 0 = 0` or
  `0 ≤ x` axiom: these are derived below (Lemma 2 of the paper).
* As in the paper, `x < y` abbreviates `x ≤ y ∧ x ≠ y`; we spell this out
  inside `euc` and in hypotheses, since `PAMinus` carries only `≤`.
* `x²` is written `x * x` (the paper's definition `x² := x · x`).
* The statement is semantic: the equivalence holds in every structure
  satisfying the axioms.  By the completeness theorem this is equivalent to
  the paper's provability claim; syntactic derivations are not formalized.
* Non-vacuity: `ℕ` is an instance of `PAMinus`.
-/
import Mathlib

set_option autoImplicit false

namespace RestrictedDivisionPrincipleEquivalent

/-- The theory PA⁻ in Visser's numbering (Kato, arXiv:2610.24976, §2.1):
the axioms pa1–pa13 and pa15 over the language `{0, 1, +, ·, ≤}`. -/
class PAMinus (M : Type*) extends Zero M, One M, Add M, Mul M, LE M where
  /-- pa1: `x + 0 = x`. -/
  pa1 : ∀ x : M, x + 0 = x
  /-- pa2: `x + y = y + x`. -/
  pa2 : ∀ x y : M, x + y = y + x
  /-- pa3: `(x + y) + z = x + (y + z)`. -/
  pa3 : ∀ x y z : M, (x + y) + z = x + (y + z)
  /-- pa4: `x · 1 = x`. -/
  pa4 : ∀ x : M, x * 1 = x
  /-- pa5: `x · y = y · x`. -/
  pa5 : ∀ x y : M, x * y = y * x
  /-- pa6: `(x · y) · z = x · (y · z)`. -/
  pa6 : ∀ x y z : M, (x * y) * z = x * (y * z)
  /-- pa7: `x · (y + z) = x · y + x · z`. -/
  pa7 : ∀ x y z : M, x * (y + z) = x * y + x * z
  /-- pa8: `x ≤ y ∨ y ≤ x`. -/
  pa8 : ∀ x y : M, x ≤ y ∨ y ≤ x
  /-- pa9: `x ≤ y ∧ y ≤ z → x ≤ z`. -/
  pa9 : ∀ x y z : M, x ≤ y → y ≤ z → x ≤ z
  /-- pa10: `x + 1 ≰ x`. -/
  pa10 : ∀ x : M, ¬ x + 1 ≤ x
  /-- pa11: `y ≤ x → (y = x ∨ y + 1 ≤ x)`. -/
  pa11 : ∀ x y : M, y ≤ x → y = x ∨ y + 1 ≤ x
  /-- pa12: `y ≤ x → y + z ≤ x + z`. -/
  pa12 : ∀ x y z : M, y ≤ x → y + z ≤ x + z
  /-- pa13: `y ≤ x → y · z ≤ x · z`. -/
  pa13 : ∀ x y z : M, y ≤ x → y * z ≤ x * z
  /-- pa15: `y ≤ x → ∃ z, x = y + z`. -/
  pa15 : ∀ x y : M, y ≤ x → ∃ z, x = y + z

section Defs

variable {M : Type*} [PAMinus M]

/-- `euc(a, b)`: `b` can be divided by `a` with remainder,
`∃ q r, b = a q + r ∧ r < a`, where `r < a` abbreviates `r ≤ a ∧ r ≠ a`. -/
def euc (a b : M) : Prop := ∃ q r : M, b = a * q + r ∧ r ≤ a ∧ r ≠ a

/-- `cop(a, b)`: `(a, b)` is a co-prime pair, `∃ c d, a d = b c + 1`. -/
def cop (a b : M) : Prop := ∃ c d : M, a * d = b * c + 1

end Defs

/-- The restricted Euclidean division principle pa17⁻:
`∀ a b, cop(a, b) → euc(a, b)`. -/
def Pa17Minus (M : Type*) [PAMinus M] : Prop := ∀ a b : M, cop a b → euc a b

/-- The full Euclidean division principle pa17: `∀ a b, a ≠ 0 → euc(a, b)`. -/
def Pa17 (M : Type*) [PAMinus M] : Prop := ∀ a b : M, a ≠ 0 → euc a b

/-- The standard model: `ℕ` satisfies the axioms of PA⁻. -/
instance instPAMinusNat : PAMinus ℕ where
  pa1 := Nat.add_zero
  pa2 := Nat.add_comm
  pa3 := Nat.add_assoc
  pa4 := Nat.mul_one
  pa5 := Nat.mul_comm
  pa6 := Nat.mul_assoc
  pa7 := Nat.mul_add
  pa8 := Nat.le_total
  pa9 := fun _ _ _ => Nat.le_trans
  pa10 := fun x => by omega
  pa11 := fun x y h => by omega
  pa12 := fun _ _ z h => Nat.add_le_add_right h z
  pa13 := fun _ _ z h => Nat.mul_le_mul_right z h
  pa15 := fun x y h => ⟨x - y, by omega⟩

/-! ## Lemma 2: elementary consequences of the axioms -/

namespace PAMinus

variable {M : Type*} [PAMinus M]

/-- Reflexivity of `≤`, from pa8. -/
theorem le_refl' (x : M) : x ≤ x := (pa8 x x).elim id id

/-- Antisymmetry of `≤`, from pa10 and pa11. -/
theorem le_antisymm' {x y : M} (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  rcases pa11 x y hyx with h | h
  · exact h.symm
  · exact absurd (pa9 _ _ _ h hxy) (pa10 y)

/-- `x ≤ x + 1`, from pa8 and pa10. -/
theorem le_add_one' (x : M) : x ≤ x + 1 :=
  (pa8 x (x + 1)).resolve_right (pa10 x)

/-- `a + 1 ≤ b ↔ a < b`, with `a < b` spelled `a ≤ b ∧ a ≠ b`. -/
theorem add_one_le_iff' {a b : M} : a + 1 ≤ b ↔ a ≤ b ∧ a ≠ b := by
  constructor
  · intro h
    refine ⟨pa9 _ _ _ (le_add_one' a) h, ?_⟩
    rintro rfl
    exact pa10 a h
  · rintro ⟨h, hne⟩
    exact (pa11 b a h).resolve_left hne

/-- Additive order cancellation: `a + c ≤ b + c → a ≤ b`. -/
theorem le_of_add_le_add_right' {a b c : M} (h : a + c ≤ b + c) : a ≤ b := by
  rcases pa8 a b with hab | hba
  · exact hab
  · rcases pa11 a b hba with heq | hlt
    · rw [heq]; exact le_refl' a
    · have h1 : b + 1 + c ≤ a + c := pa12 _ _ c hlt
      have h2 : b + c + 1 ≤ b + c := by
        rw [pa3, pa2 c 1, ← pa3]
        exact pa9 _ _ _ h1 h
      exact absurd h2 (pa10 _)

/-- Additive cancellation: `a + c = b + c → a = b`. -/
theorem add_right_cancel' {a b c : M} (h : a + c = b + c) : a = b :=
  le_antisymm' (le_of_add_le_add_right' (by rw [h]; exact le_refl' _))
    (le_of_add_le_add_right' (by rw [h]; exact le_refl' _))

/-- `0 + a = a`. -/
theorem zero_add' (a : M) : 0 + a = a := by rw [pa2, pa1]

/-- `1 · a = a`. -/
theorem one_mul' (a : M) : 1 * a = a := by rw [pa5, pa4]

/-- `a · 0 = 0`, from distributivity and cancellation. -/
theorem mul_zero' (a : M) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = 0 + a * 0 := by
    rw [← pa7, pa1, zero_add']
  exact add_right_cancel' h

/-- `0 · a = 0`. -/
theorem zero_mul' (a : M) : 0 * a = 0 := by rw [pa5, mul_zero']

/-- `0 ≤ 1`: otherwise `1 ≤ 0` gives `1 + 1 ≤ 1` by pa12. -/
theorem zero_le_one' : (0 : M) ≤ 1 := by
  refine (pa8 (0 : M) 1).resolve_right ?_
  intro h
  have h1 : (1 : M) + 1 ≤ 0 + 1 := pa12 _ _ 1 h
  rw [zero_add'] at h1
  exact pa10 1 h1

/-- `0 ≤ a`, from `0 ≤ 1` and pa13. -/
theorem zero_le' (a : M) : 0 ≤ a := by
  have h := pa13 _ _ a (zero_le_one' (M := M))
  rwa [zero_mul', one_mul'] at h

/-- `0 ≠ 1`, from pa10. -/
theorem zero_ne_one' : (0 : M) ≠ 1 := by
  intro h
  have h1 : (0 : M) + 1 ≤ 0 := by rw [zero_add', ← h]; exact le_refl' 0
  exact pa10 0 h1

/-- `a ≠ 0 → 1 ≤ a`. -/
theorem one_le_of_ne_zero' {a : M} (h : a ≠ 0) : 1 ≤ a := by
  have h1 := (add_one_le_iff' (a := (0 : M)) (b := a)).2 ⟨zero_le' a, Ne.symm h⟩
  rwa [zero_add'] at h1

/-- `a ≤ a + b`. -/
theorem le_add_right' (a b : M) : a ≤ a + b := by
  have h := pa12 _ _ a (zero_le' b)
  rwa [zero_add', pa2 b] at h

/-- `(a + b) · c = a · c + b · c`. -/
theorem add_mul' (a b c : M) : (a + b) * c = a * c + b * c := by
  rw [pa5, pa7, pa5 c a, pa5 c b]

/-- The commutative semiring structure carried by any model of PA⁻, built on
the model's own `0, 1, +, ·`; used only to run `ring` inside proofs. -/
abbrev toCommSemiring : CommSemiring M where
  add_assoc := pa3
  zero_add := zero_add'
  add_zero := pa1
  nsmul := nsmulRec
  add_comm := pa2
  left_distrib := pa7
  right_distrib := add_mul'
  zero_mul := zero_mul'
  mul_zero := mul_zero'
  mul_assoc := pa6
  one_mul := one_mul'
  mul_one := pa4
  mul_comm := pa5

end PAMinus

/-! ## Theorem 3, Corollaries 4 and 5 -/

open PAMinus

section Main

variable {M : Type*} [PAMinus M]

/-- Forward half of Theorem 3: if `y = x q + r` with `r < x` and `s < t`, then
`t y + s = (t x) q + (t r + s)` with `t r + s < t x`. -/
theorem euc_mul_add_of_euc {x y s t : M} (hst : s ≤ t ∧ s ≠ t) (h : euc x y) :
    euc (t * x) (t * y + s) := by
  letI := toCommSemiring (M := M)
  obtain ⟨q, r, hy, hrx, hrne⟩ := h
  refine ⟨q, t * r + s, ?_, ?_⟩
  · rw [hy]; ring
  · -- `t r + s + 1 ≤ t r + t = t (r + 1) ≤ t x`
    have hs1 : s + 1 ≤ t := add_one_le_iff'.2 hst
    have hr1 : r + 1 ≤ x := add_one_le_iff'.2 ⟨hrx, hrne⟩
    have h1 : s + 1 + t * r ≤ t + t * r := pa12 _ _ _ hs1
    have h2 : (r + 1) * t ≤ x * t := pa13 _ _ _ hr1
    have h3 : t * r + s + 1 ≤ t * x := by
      have e1 : t * r + s + 1 = s + 1 + t * r := by ring
      have e2 : t + t * r = (r + 1) * t := by ring
      have e3 : x * t = t * x := pa5 x t
      rw [e1]
      rw [e2] at h1
      rw [e3] at h2
      exact pa9 _ _ _ h1 h2
    exact add_one_le_iff'.1 h3

/-- Backward half of Theorem 3: if `t y + s = (t x) q + u` with `u < t x` and
`s < t`, then `y = x q + r` for some `r < x`. -/
theorem euc_of_euc_mul_add {x y s t : M} (hst : s ≤ t ∧ s ≠ t)
    (h : euc (t * x) (t * y + s)) : euc x y := by
  letI := toCommSemiring (M := M)
  obtain ⟨q, u, hu, hux, hune⟩ := h
  -- Step 1: `x q ≤ y`.
  have hxq : x * q ≤ y := by
    rcases pa8 (x * q) y with hle | hge
    · exact hle
    · rcases pa11 _ _ hge with heq | hlt
      · rw [heq]; exact le_refl' _
      · exfalso
        have h1 : (y + 1) * t ≤ x * q * t := pa13 _ _ _ hlt
        have h2 : t * y + t ≤ t * y + s := by
          have e1 : (y + 1) * t = t * y + t := by ring
          have e2 : x * q * t = t * x * q := by ring
          rw [e1, e2] at h1
          refine pa9 _ _ _ h1 ?_
          rw [hu]
          exact le_add_right' _ _
        have h3 : t ≤ s := by
          rw [pa2 _ t, pa2 _ s] at h2
          exact le_of_add_le_add_right' h2
        exact hst.2 (le_antisymm' hst.1 h3)
  -- Step 2: `y = x q + r`.
  obtain ⟨r, hr⟩ := pa15 _ _ hxq
  refine ⟨q, r, hr, ?_⟩
  -- Step 3: `r < x`, since `x ≤ r` would force `t x ≤ u`.
  have hu' : t * r + s = u := by
    have e : t * x * q + (t * r + s) = t * x * q + u := by
      rw [← hu, hr]; ring
    rw [pa2 _ (t * r + s), pa2 _ u] at e
    exact add_right_cancel' e
  by_contra hcon
  have hxr : x ≤ r := by
    rcases pa8 r x with hrx | hxr
    · rcases pa11 _ _ hrx with heq | hlt
      · rw [heq]; exact le_refl' _
      · exact absurd ⟨hrx, fun heq => pa10 x (heq ▸ hlt)⟩ hcon
    · exact hxr
  have h1 : x * t ≤ r * t := pa13 _ _ _ hxr
  rw [pa5 x, pa5 r] at h1
  have h2 : t * x ≤ u := by
    rw [← hu']
    exact pa9 _ _ _ h1 (le_add_right' _ _)
  exact hune (le_antisymm' hux h2)

/-- **Theorem 3** (Kato, arXiv:2610.24976, quotient-preserving division
transformation): in every model of PA⁻, for `x ≠ 0` and `s < t`,
`euc(x, y) ↔ euc(t x, t y + s)`.  (The hypothesis `x ≠ 0` of the paper is
not needed for this direction-by-direction argument and is kept only to
mirror the paper's statement.) -/
theorem euc_iff_euc_mul_add {x y s t : M} (_hx : x ≠ 0) (hst : s ≤ t ∧ s ≠ t) :
    euc x y ↔ euc (t * x) (t * y + s) :=
  ⟨euc_mul_add_of_euc hst, euc_of_euc_mul_add hst⟩

/-- Co-prime half of Corollary 4: if `1 < x` and `0 < y` then
`cop(x², x y + 1)`, witnessed by `c = z`, `d = y²` where `z + 1 = x y`. -/
theorem cop_mul_self_mul_add_one {x y : M} (hx : 1 ≤ x ∧ 1 ≠ x) (hy : 0 ≤ y ∧ 0 ≠ y) :
    cop (x * x) (x * y + 1) := by
  letI := toCommSemiring (M := M)
  have hy1 : 1 ≤ y := one_le_of_ne_zero' (Ne.symm hy.2)
  have hyxy : 1 * y ≤ x * y := pa13 _ _ _ hx.1
  rw [one_mul'] at hyxy
  obtain ⟨z, hz⟩ := pa15 _ _ (pa9 _ _ _ hy1 hyxy)
  refine ⟨z, y * y, ?_⟩
  have e : x * x * (y * y) = (x * y) * (x * y) := by ring
  rw [e, hz]
  ring

/-- **Corollary 4** (Kato, arXiv:2610.24976, transfer to a co-prime pair): in
every model of PA⁻, if `1 < x` and `0 < y` then `cop(x², x y + 1)` and
`euc(x, y) ↔ euc(x², x y + 1)`. -/
theorem cop_and_euc_iff {x y : M} (hx : 1 ≤ x ∧ 1 ≠ x) (hy : 0 ≤ y ∧ 0 ≠ y) :
    cop (x * x) (x * y + 1) ∧ (euc x y ↔ euc (x * x) (x * y + 1)) := by
  refine ⟨cop_mul_self_mul_add_one hx hy, ?_⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact zero_ne_one' (le_antisymm' (zero_le_one') hx.1)
  exact euc_iff_euc_mul_add hx0 hx

/-- In a co-prime pair `a d = b c + 1`, the first entry is nonzero. -/
theorem ne_zero_of_cop {a b : M} (h : cop a b) : a ≠ 0 := by
  obtain ⟨c, d, hcd⟩ := h
  rintro rfl
  rw [zero_mul'] at hcd
  have h1 : 0 + 1 ≤ b * c + 1 := pa12 _ _ _ (zero_le' _)
  rw [zero_add', ← hcd] at h1
  exact zero_ne_one' (le_antisymm' zero_le_one' h1)

/-- **Corollary 5** (Kato, arXiv:2610.24976; answers Visser's Open Question
8.29): in every model of PA⁻ (axioms pa1–pa13 and pa15), the restricted
Euclidean division principle pa17⁻ (`cop(a, b) → euc(a, b)`) holds if and
only if the full Euclidean division principle pa17 (`a ≠ 0 → euc(a, b)`)
holds. -/
theorem pa17Minus_iff_pa17 : Pa17Minus M ↔ Pa17 M := by
  constructor
  · intro h x y hx
    by_cases hy : y = 0
    · -- `0 = x · 0 + 0`, `0 < x`
      exact ⟨0, 0, by rw [hy, mul_zero', pa1], zero_le' x, Ne.symm hx⟩
    by_cases hx1 : x = 1
    · -- `y = 1 · y + 0`, `0 < 1`
      exact ⟨y, 0, by rw [hx1, one_mul', pa1], zero_le' x,
        fun h0 => hx (h0.symm)⟩
    have hx' : 1 ≤ x ∧ 1 ≠ x := ⟨one_le_of_ne_zero' hx, Ne.symm hx1⟩
    have hy' : 0 ≤ y ∧ 0 ≠ y := ⟨zero_le' y, Ne.symm hy⟩
    obtain ⟨hcop, hiff⟩ := cop_and_euc_iff hx' hy'
    exact hiff.2 (h _ _ hcop)
  · intro h a b hab
    exact h a b (ne_zero_of_cop hab)

end Main

/-- Non-vacuity: pa17 holds in the standard model `ℕ`. -/
theorem pa17_nat : Pa17 ℕ := by
  intro a b ha
  refine ⟨b / a, b % a, ?_, ?_, ?_⟩
  · exact (Nat.div_add_mod b a).symm
  · exact (Nat.mod_lt b (Nat.pos_of_ne_zero ha)).le
  · exact (Nat.mod_lt b (Nat.pos_of_ne_zero ha)).ne

/-- Non-vacuity: pa17⁻ holds in `ℕ`, via the main equivalence. -/
theorem pa17Minus_nat : Pa17Minus ℕ := pa17Minus_iff_pa17.2 pa17_nat

/-- Ground truth: `7 = 3 · 2 + 1` with `1 < 3`, so `euc(3, 7)` in `ℕ`. -/
example : euc (3 : ℕ) 7 := ⟨2, 1, by decide, by decide, by decide⟩

/-- Ground truth: `2 · 2 = 3 · 1 + 1`, so `cop(2, 3)` in `ℕ`. -/
example : cop (2 : ℕ) 3 := ⟨1, 2, by decide⟩

/-- Ground truth: `euc(0, 5)` fails in `ℕ` (no remainder `r < 0`). -/
example : ¬ euc (0 : ℕ) 5 := by
  rintro ⟨q, r, -, hr, hr0⟩
  omega

/-- Non-vacuity of Corollary 4's hypotheses: `x = 2`, `y = 1` in `ℕ`. -/
example : cop (2 * 2 : ℕ) (2 * 1 + 1) ∧ (euc (2 : ℕ) 1 ↔ euc (2 * 2 : ℕ) (2 * 1 + 1)) :=
  cop_and_euc_iff ⟨by decide, by decide⟩ ⟨by decide, by decide⟩

/-- Non-vacuity of Theorem 3's hypotheses: `x = 3`, `s = 1`, `t = 2` in `ℕ`. -/
example (y : ℕ) : euc (3 : ℕ) y ↔ euc (2 * 3 : ℕ) (2 * y + 1) :=
  euc_iff_euc_mul_add (by decide) ⟨by decide, by decide⟩

end RestrictedDivisionPrincipleEquivalent
