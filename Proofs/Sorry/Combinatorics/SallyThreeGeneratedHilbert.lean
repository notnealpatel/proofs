/-
# Sally's conjecture for 3-generated numerical semigroups

## Source

T. Cortadellas Benítez, R. Jafari, S. Zarzuela Armengou,
"On the Apéry sets of monomial curves", arXiv:1205.4118.
Section 4 ("Non-decreasing Hilbert functions"): Remark `Hi`, Lemma `land`
and the Proposition for `b = 3` ("Let `b = 3`. Then the numerical semigroup
ring `k[[S]]` has non-decreasing Hilbert function."), whose proof builds an
injective map `D_k → C_k`.  The order of an element is defined in Section 2:
"For `s ∈ S` we consider the order of `s` ... the integer `k` such that
`s ∈ kM \ (k+1)M`.  In particular `s` may be represented as
`s = r_1 n_1 + ⋯ + r_b n_b` with `∑ r_i = k` maximum over all
representations of `s` in `S`."  The Hilbert function of `k[[S]]` is
`H(k) = #(kM \ (k+1)M) = #{s ∈ S : ord(s) = k}`.

## Informal claim (as triaged, recorded 2026-10-21)

For positive integers `n1 < n2 < n3`, let `ord(x)` be the maximum of
`r1 + r2 + r3` over `r ∈ ℕ³` with `r1 n1 + r2 n2 + r3 n3 = x`, and let
`H(k) = #{x : x representable, ord(x) = k}`.  Then `H` is monotone.

## Status

Proved in the paper (Proposition for `b = 3` in Section 4, similar to
Şerban's proof); the general embedding-dimension-3 ring case is Elias (1993).
Here the statement does not assume `gcd(n1, n2, n3) = 1` or minimality of
the generators: the injection argument uses neither.  Formalized below with
no remaining `sorry`.
-/
import Mathlib

set_option autoImplicit false

namespace SallyThreeGeneratedHilbert

/-! ## Definitions -/

/-- `IsRep n₁ n₂ n₃ x k`: the natural number `x` is a sum of exactly `k`
generators from `{n₁, n₂, n₃}` (with repetition), i.e. there are
`r₁ r₂ r₃ : ℕ` with `r₁ + r₂ + r₃ = k` and `r₁ n₁ + r₂ n₂ + r₃ n₃ = x`. -/
def IsRep (n₁ n₂ n₃ x k : ℕ) : Prop :=
  ∃ r₁ r₂ r₃ : ℕ, r₁ + r₂ + r₃ = k ∧ r₁ * n₁ + r₂ * n₂ + r₃ * n₃ = x

/-- Bounded reformulation of `IsRep`, used only to decide it. -/
theorem isRep_iff_bounded (n₁ n₂ n₃ x k : ℕ) :
    IsRep n₁ n₂ n₃ x k ↔ ∃ r₁ < k + 1, ∃ r₂ < k + 1 - r₁,
      r₁ * n₁ + r₂ * n₂ + (k - r₁ - r₂) * n₃ = x := by
  constructor
  · rintro ⟨r₁, r₂, r₃, hk, hx⟩
    refine ⟨r₁, by omega, r₂, by omega, ?_⟩
    have h3 : k - r₁ - r₂ = r₃ := by omega
    rw [h3]
    exact hx
  · rintro ⟨r₁, h₁, r₂, h₂, hx⟩
    exact ⟨r₁, r₂, k - r₁ - r₂, by omega, hx⟩

instance (n₁ n₂ n₃ x k : ℕ) : Decidable (IsRep n₁ n₂ n₃ x k) :=
  decidable_of_iff _ (isRep_iff_bounded n₁ n₂ n₃ x k).symm

/-- The order `ord(x)` of `x` in the semigroup `⟨n₁, n₂, n₃⟩`: the largest
`k ≤ x` such that `x` is a sum of `k` generators.  When all generators are
positive every representation of `x` uses at most `x` generators, so for
representable `x` this is the maximum of `r₁ + r₂ + r₃` over all
representations (see `isRep_ord` and `le_ord`). -/
def ord (n₁ n₂ n₃ x : ℕ) : ℕ := Nat.findGreatest (IsRep n₁ n₂ n₃ x) x

/-- The Hilbert function `H(k) = #{x ∈ S : ord(x) = k}` of the semigroup ring
of `S = ⟨n₁, n₂, n₃⟩`.  The search range `x ≤ k (n₁ + n₂ + n₃)` contains every
sum of `k` generators (see `mem_levelSet_iff`), and the condition
`IsRep x k` encodes that `x` lies in `S`. -/
def hilb (n₁ n₂ n₃ k : ℕ) : ℕ :=
  ((Finset.range (k * (n₁ + n₂ + n₃) + 1)).filter
    (fun x => IsRep n₁ n₂ n₃ x k ∧ ord n₁ n₂ n₃ x = k)).card

/-! ## Ground truth -/

section GroundTruth

set_option maxRecDepth 10000

example : ord 3 5 7 10 = 2 := by decide
example : ord 4 11 29 33 = 3 := by decide
example : ord 4 11 29 26 = 3 := by decide
example : hilb 3 5 7 0 = 1 := by decide
example : hilb 3 5 7 1 = 3 := by decide
example : hilb 3 5 7 2 = 3 := by decide

-- Example `s=<4,11,29>` of the paper: `H = 1, 3, 3, 4, ...`.
example : hilb 4 11 29 1 = 3 := by decide
example : hilb 4 11 29 2 = 3 := by decide

end GroundTruth

/-! ## Basic lemmas -/

section Lemmas

variable {n₁ n₂ n₃ : ℕ}

/-- Representations add: a sum of `a` generators plus a sum of `b`
generators is a sum of `a + b` generators. -/
theorem IsRep.add {x y a b : ℕ} (hx : IsRep n₁ n₂ n₃ x a) (hy : IsRep n₁ n₂ n₃ y b) :
    IsRep n₁ n₂ n₃ (x + y) (a + b) := by
  obtain ⟨r₁, r₂, r₃, hr, rfl⟩ := hx
  obtain ⟨s₁, s₂, s₃, hs, rfl⟩ := hy
  refine ⟨r₁ + s₁, r₂ + s₂, r₃ + s₃, by omega, ?_⟩
  ring

/-- `n₁` is a sum of one generator. -/
theorem isRep_n₁ : IsRep n₁ n₂ n₃ n₁ 1 := ⟨1, 0, 0, rfl, by ring⟩

/-- `l n₂` is a sum of `l` generators. -/
theorem isRep_mul_n₂ (l : ℕ) : IsRep n₁ n₂ n₃ (l * n₂) l := ⟨0, l, 0, by ring, by ring⟩

/-- With positive generators, a sum of `j` generators equal to `x` has
`j ≤ x`. -/
theorem le_of_isRep (h₁ : 0 < n₁) (h₂ : 0 < n₂) (h₃ : 0 < n₃) {x j : ℕ}
    (h : IsRep n₁ n₂ n₃ x j) : j ≤ x := by
  obtain ⟨r₁, r₂, r₃, rfl, rfl⟩ := h
  have e₁ : r₁ ≤ r₁ * n₁ := Nat.le_mul_of_pos_right r₁ h₁
  have e₂ : r₂ ≤ r₂ * n₂ := Nat.le_mul_of_pos_right r₂ h₂
  have e₃ : r₃ ≤ r₃ * n₃ := Nat.le_mul_of_pos_right r₃ h₃
  omega

/-- A sum of `j` generators is at most `j` times the largest generator. -/
theorem le_mul_of_isRep (h₁₃ : n₁ ≤ n₃) (h₂₃ : n₂ ≤ n₃) {x j : ℕ}
    (h : IsRep n₁ n₂ n₃ x j) : x ≤ j * n₃ := by
  obtain ⟨r₁, r₂, r₃, rfl, rfl⟩ := h
  have e₁ : r₁ * n₁ ≤ r₁ * n₃ := Nat.mul_le_mul_left r₁ h₁₃
  have e₂ : r₂ * n₂ ≤ r₂ * n₃ := Nat.mul_le_mul_left r₂ h₂₃
  have e : (r₁ + r₂ + r₃) * n₃ = r₁ * n₃ + r₂ * n₃ + r₃ * n₃ := by ring
  omega

/-- A sum of `j` generators is at most `j (n₁ + n₂ + n₃)`. -/
theorem le_mul_sum_of_isRep {x j : ℕ} (h : IsRep n₁ n₂ n₃ x j) :
    x ≤ j * (n₁ + n₂ + n₃) := by
  obtain ⟨r₁, r₂, r₃, rfl, rfl⟩ := h
  nlinarith [Nat.zero_le (r₁ * n₂), Nat.zero_le (r₁ * n₃), Nat.zero_le (r₂ * n₁),
    Nat.zero_le (r₂ * n₃), Nat.zero_le (r₃ * n₁), Nat.zero_le (r₃ * n₂)]

/-- For representable `x`, `ord x` is itself attained by a representation. -/
theorem isRep_ord (h₁ : 0 < n₁) (h₂ : 0 < n₂) (h₃ : 0 < n₃) {x j : ℕ}
    (h : IsRep n₁ n₂ n₃ x j) : IsRep n₁ n₂ n₃ x (ord n₁ n₂ n₃ x) :=
  Nat.findGreatest_spec (le_of_isRep h₁ h₂ h₃ h) h

/-- `ord x` bounds the length of every representation of `x`. -/
theorem le_ord (h₁ : 0 < n₁) (h₂ : 0 < n₂) (h₃ : 0 < n₃) {x j : ℕ}
    (h : IsRep n₁ n₂ n₃ x j) : j ≤ ord n₁ n₂ n₃ x :=
  Nat.le_findGreatest (le_of_isRep h₁ h₂ h₃ h) h

/-- Membership in the level set counted by `hilb`: exactly the `x ∈ S` of
order `k`. -/
theorem mem_levelSet_iff (k x : ℕ) :
    x ∈ (Finset.range (k * (n₁ + n₂ + n₃) + 1)).filter
      (fun x => IsRep n₁ n₂ n₃ x k ∧ ord n₁ n₂ n₃ x = k) ↔
      IsRep n₁ n₂ n₃ x k ∧ ord n₁ n₂ n₃ x = k := by
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨Nat.lt_succ_of_le (le_mul_sum_of_isRep h.1), h⟩

end Lemmas

/-! ## The injection `{ord = k} → {ord = k + 1}` -/

section Injection

variable {n₁ n₂ n₃ : ℕ}

/-- Lemma `land` of the paper, specialised to `b = 3`.  Let `x` have order
`k` and put `l = ord(x + n₁) - (k + 1)`.  Then `x + n₁ - l n₂` is a sum of
`k + 1` generators: a maximal expression of `x + n₁` cannot use `n₁` when
`l > 0`, it uses `n₃` at most `k` times, and so at least `l + 1` copies of
`n₂`, of which `l` are removed. -/
theorem exists_landing (h₁ : 0 < n₁) (h₁₂ : n₁ < n₂) (h₂₃ : n₂ < n₃) {x k : ℕ}
    (hx : IsRep n₁ n₂ n₃ x k) (hord : ord n₁ n₂ n₃ x = k) :
    ∃ y, IsRep n₁ n₂ n₃ y (k + 1) ∧
      y + (ord n₁ n₂ n₃ (x + n₁) - (k + 1)) * n₂ = x + n₁ := by
  have h₂ : 0 < n₂ := by omega
  have h₃ : 0 < n₃ := by omega
  have hx₁ : IsRep n₁ n₂ n₃ (x + n₁) (k + 1) := hx.add isRep_n₁
  have hm : k + 1 ≤ ord n₁ n₂ n₃ (x + n₁) := le_ord h₁ h₂ h₃ hx₁
  set m := ord n₁ n₂ n₃ (x + n₁) with hm_def
  rcases Nat.eq_zero_or_pos (m - (k + 1)) with hl | hl
  · exact ⟨x + n₁, hx₁, by rw [hl, zero_mul, add_zero]⟩
  obtain ⟨r₁, r₂, r₃, hr, hrx⟩ := isRep_ord h₁ h₂ h₃ hx₁
  rw [← hm_def] at hr
  -- a maximal expression of `x + n₁` does not use `n₁`
  have hr₁ : r₁ = 0 := by
    by_contra hne
    have hrep : IsRep n₁ n₂ n₃ x (r₁ - 1 + r₂ + r₃) := by
      refine ⟨r₁ - 1, r₂, r₃, rfl, ?_⟩
      have hsplit : r₁ * n₁ = (r₁ - 1) * n₁ + n₁ := by
        conv_lhs => rw [show r₁ = r₁ - 1 + 1 by omega]
        ring
      omega
    have hle : r₁ - 1 + r₂ + r₃ ≤ k := hord ▸ le_ord h₁ h₂ h₃ hrep
    omega
  -- it uses `n₃` at most `k` times
  have hr₃ : r₃ ≤ k := by
    have hxle : x ≤ k * n₃ := le_mul_of_isRep (by omega) (by omega) hx
    have hlt : r₃ * n₃ < (k + 1) * n₃ := by
      have e : (k + 1) * n₃ = k * n₃ + n₃ := by ring
      have e₂ : r₃ * n₃ ≤ x + n₁ := by rw [← hrx]; omega
      omega
    exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_right hlt)
  set l := m - (k + 1) with hl_def
  have hlr₂ : l ≤ r₂ := by omega
  refine ⟨(r₂ - l) * n₂ + r₃ * n₃, ⟨0, r₂ - l, r₃, by omega, by ring⟩, ?_⟩
  have hsplit : (r₂ - l) * n₂ + l * n₂ = r₂ * n₂ := by
    rw [← add_mul, Nat.sub_add_cancel hlr₂]
  subst hr₁
  omega

/-- The landing element is of order exactly `k + 1`: a longer expression of
`y` would extend, by the `l` copies of `n₂`, to an expression of `x + n₁`
longer than `ord(x + n₁)` (Remark `rem1` of the paper). -/
theorem ord_landing (h₁ : 0 < n₁) (h₂ : 0 < n₂) (h₃ : 0 < n₃) {x y k : ℕ}
    (hy : IsRep n₁ n₂ n₃ y (k + 1))
    (hyx : y + (ord n₁ n₂ n₃ (x + n₁) - (k + 1)) * n₂ = x + n₁) :
    ord n₁ n₂ n₃ y = k + 1 := by
  set l := ord n₁ n₂ n₃ (x + n₁) - (k + 1) with hl_def
  have hm : k + 1 ≤ ord n₁ n₂ n₃ (x + n₁) := by
    have hrep := hy.add (isRep_mul_n₂ (n₁ := n₁) (n₃ := n₃) l)
    rw [hyx] at hrep
    have hle₀ := le_ord h₁ h₂ h₃ hrep
    omega
  refine le_antisymm ?_ (le_ord h₁ h₂ h₃ hy)
  have hrep := (isRep_ord h₁ h₂ h₃ hy).add (isRep_mul_n₂ (n₁ := n₁) (n₃ := n₃) l)
  rw [hyx] at hrep
  have hle := le_ord h₁ h₂ h₃ hrep
  omega

/-- The map `x ↦ y_x = x + n₁ - (ord(x + n₁) - (k + 1)) n₂` of the paper
(on `{ord = k}` it is `x + n₁` when `ord(x + n₁) = k + 1`, and the landing
element `y_x` of Lemma `land` otherwise). -/
def landing (n₁ n₂ n₃ k x : ℕ) : ℕ :=
  x + n₁ - (ord n₁ n₂ n₃ (x + n₁) - (k + 1)) * n₂

/-- Half of injectivity: if `y + l n₂ = x + n₁` and `y + l' n₂ = x' + n₁`
with `l ≤ l'`, both `x` and `x'` of order `k`, then `x = x'`, since otherwise
`x' = x + (l' - l) n₂` would have order larger than `k`. -/
theorem eq_of_add_mul_eq (h₁ : 0 < n₁) (h₂ : 0 < n₂) (h₃ : 0 < n₃)
    {x x' y k l l' : ℕ} (hx : IsRep n₁ n₂ n₃ x k) (hx' : ord n₁ n₂ n₃ x' = k)
    (hll : l ≤ l') (hy : y + l * n₂ = x + n₁) (hy' : y + l' * n₂ = x' + n₁) :
    x = x' := by
  have hsplit : l' * n₂ = l * n₂ + (l' - l) * n₂ := by
    rw [← add_mul, Nat.add_sub_cancel' hll]
  have hxx : x' = x + (l' - l) * n₂ := by omega
  have hrep : IsRep n₁ n₂ n₃ x' (k + (l' - l)) := by
    rw [hxx]
    exact hx.add (isRep_mul_n₂ _)
  have hle := le_ord h₁ h₂ h₃ hrep
  have hl : l' - l = 0 := by omega
  rw [hl, zero_mul] at hsplit
  omega

end Injection

/-! ## Main theorem -/

/-- **Sally's conjecture for 3-generated numerical semigroups** (arXiv
1205.4118, Section 4, Proposition for `b = 3`; Elias 1993 for general
embedding-dimension-3 rings).  For positive integers `n₁ < n₂ < n₃`, the
Hilbert function `H(k) = #{x ∈ ⟨n₁, n₂, n₃⟩ : ord(x) = k}` satisfies
`H(k) ≤ H(k + 1)`.  The map `x ↦ landing x` injects the elements of order `k`
into the elements of order `k + 1`. -/
theorem hilb_le_hilb_succ (n₁ n₂ n₃ : ℕ) (h₁ : 0 < n₁) (h₁₂ : n₁ < n₂) (h₂₃ : n₂ < n₃)
    (k : ℕ) : hilb n₁ n₂ n₃ k ≤ hilb n₁ n₂ n₃ (k + 1) := by
  have h₂ : 0 < n₂ := by omega
  have h₃ : 0 < n₃ := by omega
  unfold hilb
  apply Finset.card_le_card_of_injOn (landing n₁ n₂ n₃ k)
  · intro x hx
    rw [Finset.mem_coe, mem_levelSet_iff] at hx ⊢
    obtain ⟨y, hy, hyx⟩ := exists_landing h₁ h₁₂ h₂₃ hx.1 hx.2
    have hyl : landing n₁ n₂ n₃ k x = y := by
      unfold landing
      omega
    rw [hyl]
    exact ⟨hy, ord_landing h₁ h₂ h₃ hy hyx⟩
  · intro x hx x' hx' hxx'
    rw [Finset.mem_coe, mem_levelSet_iff] at hx hx'
    obtain ⟨y, -, hyx⟩ := exists_landing h₁ h₁₂ h₂₃ hx.1 hx.2
    obtain ⟨y', -, hyx'⟩ := exists_landing h₁ h₁₂ h₂₃ hx'.1 hx'.2
    have hyl : landing n₁ n₂ n₃ k x = y := by
      unfold landing
      omega
    have hyl' : landing n₁ n₂ n₃ k x' = y' := by
      unfold landing
      omega
    have hyy : y = y' := by rw [← hyl, ← hyl', hxx']
    subst hyy
    rcases le_total (ord n₁ n₂ n₃ (x + n₁) - (k + 1)) (ord n₁ n₂ n₃ (x' + n₁) - (k + 1))
      with hll | hll
    · exact eq_of_add_mul_eq h₁ h₂ h₃ hx.1 hx'.2 hll hyx hyx'
    · exact (eq_of_add_mul_eq h₁ h₂ h₃ hx'.1 hx.2 hll hyx' hyx).symm

/-- **Sally's conjecture for 3-generated numerical semigroups**, monotone
form: for positive integers `n₁ < n₂ < n₃` the Hilbert function
`k ↦ #{x ∈ ⟨n₁, n₂, n₃⟩ : ord(x) = k}` is nondecreasing (arXiv 1205.4118,
Section 4, Proposition for `b = 3`). -/
theorem hilb_monotone (n₁ n₂ n₃ : ℕ) (h₁ : 0 < n₁) (h₁₂ : n₁ < n₂) (h₂₃ : n₂ < n₃) :
    Monotone (hilb n₁ n₂ n₃) :=
  monotone_nat_of_le_succ (hilb_le_hilb_succ n₁ n₂ n₃ h₁ h₁₂ h₂₃)

/-- The hypotheses of `hilb_monotone` are jointly satisfiable, at the
paper's example `S = ⟨4, 11, 29⟩`. -/
example : Monotone (hilb 4 11 29) :=
  hilb_monotone 4 11 29 (by decide) (by decide) (by decide)

end SallyThreeGeneratedHilbert

