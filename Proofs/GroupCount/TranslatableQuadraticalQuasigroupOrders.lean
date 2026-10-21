/-
# Translatable quadratical quasigroups: which `Qn` arise from `ℤ_p` (a5-28)

## Source

arXiv:1708.08830, W. A. Dudek and R. A. R. Monzo, "Translatable quadratical
quasigroups".  Theorem 2.3 (Dudek's representation) and Theorem 2.5
(source label `T2.4`): a
quadratical quasigroup induced by `ℤ_m` has the form `x · y = a x + (1 - a) y`
with `2a² - 2a + 1 = 0` in `ℤ_m`.  Definition 3.1: for `a ≠ b` put
`11 = a, 12 = ab, 13 = ba, 14 = b` and recursively
`n1 = (n-1)1 · (n-1)2`, `n2 = (n-1)2 · (n-1)4`, `n3 = (n-1)3 · (n-1)1`,
`n4 = (n-1)4 · (n-1)3`, `Hn = {n1, n2, n3, n4}`.  Definition 3.12: `Q` is
*of the form `Qn`* if `Q = {aba} ∪ H1 ∪ ⋯ ∪ Hn` for some `a ≠ b` in `Q`.
Section 10 ("Open questions and problems"), verbatim:

  **Problem 1.** *For which values of `n` are there quadratical quasigroups of
  form `Qn`?*  Note that `n ∉ {5,6,8,14,17,19,33,26,32,…}`.  Moreover, from
  Theorem 4.11 in [DM] it follows that there are no such quasigroups if there
  is a prime `p | 4n+1` such that `p ≡ 3 (mod 4)`.

## Claim formalized here (recorded 2026-10-21)

A Gaussian-unit criterion for the affine (`ℤ_p`-induced) models; this
reduction is *not* stated in the paper.  Let `F` be a finite field and
`α ∈ F` with `2α² - 2α + 1 = 0`; put `i = 2α - 1` (so `i² = -1`) and
`1 + i = 2α`.  Then `(F, x · y = α x + (1 - α) y)` is of the form `Qn` iff
`0 < n`, `|F| = 4n + 1`, and `⟨i, 1 + i⟩ = Fˣ`.  In particular, for a prime
`p ≡ 1 (mod 4)`, the `ℤ_p`-induced quadratical quasigroup with parameter `α`
is of the form `Q((p-1)/4)` iff `Subgroup.closure {i, 1 + i} = ⊤` in
`(ZMod p)ˣ` (`zmod_isFormQ_iff`).

Mechanism (`H_eq`): with `w = aba` and `d = a - w`,
`H(t+1) = w + (1+i)^t · {d, i d, -i d, -d}`, so the union in Definition 3.12
is `w + d · ({0} ∪ {(1+i)^t i^k : t < n, k < 4})`.

Decidable corollaries: a `Q7` exists (`p = 29`, `α = 21`: the paper's
order-29 quasigroup `21x + 9y (mod 29)`, row `k = 17` of the Section 9 table
of translatable `ℤ_m`-quasigroups), and **no** `ℤ_41`-induced quadratical
quasigroup is of the form `Q10` (`not_isFormQ_ten_zmod41`); `n = 10` is not
in the paper's exclusion list.  Turning the latter into a full negative answer
for `n = 10` would need Dudek's representation theorem (every quadratical
quasigroup of order 41 is `ℤ_41`-induced), which is not formalized here.

## Status

Problem 1 is open in the paper.  The criterion above is an own reduction
(proved here for the affine models over finite fields); computationally it was
checked against the raw recursion for all primes `p ≡ 1 (mod 4)` below 3000
with several base pairs each.  Drápal–Griggs–Kozlík (IJAC 32 (2022)) classify
finite quadratical quasigroups and may already imply it; not verified.

## Fidelity notes

* `H op a b t` is the paper's `H(t+1)` as an ordered 4-tuple (index shifted
  by one: `H op a b 0 = (11, 12, 13, 14)`), and `aba` is `(a · b) · a`.
* `IsFormQ op n` adds `Nat.card G = 4n + 1` to the covering condition of
  Definition 3.12, i.e. the union `{aba} ∪ H1 ∪ ⋯ ∪ Hn` is disjoint.  Without
  it "form `Qn`" would be upward closed in `n` (the `Ht` are periodic), whereas
  the paper (e.g. Theorem 7.1, "no `Q6`", about order 25) means `|Q| = 4n+1`.
* `IsQuasigroup`/`SatisfiesA` record that the affine models are quadratical
  quasigroups (quasigroups satisfying Volenec's identity `xy · x = zx · yz`).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.TranslatableQuadraticalQuasigroupOrders

/-! ## Quadratical quasigroups -/

/-- A groupoid `(G, op)` is a *quasigroup* if for all `a b` both equations
`a · x = b` and `y · a = b` have unique solutions. -/
def IsQuasigroup {G : Type*} (op : G → G → G) : Prop :=
  ∀ a b : G, (∃! x, op a x = b) ∧ (∃! y, op y a = b)

/-- Volenec's identity (A): `xy · x = zx · yz` for all `x y z`. -/
def SatisfiesA {G : Type*} (op : G → G → G) : Prop :=
  ∀ x y z : G, op (op x y) x = op (op z x) (op y z)

/-! ## Definition 3.1 and Definition 3.12 -/

/-- Definition 3.1 (index shifted by one): `H op a b t` is the ordered 4-tuple
`((t+1)1, (t+1)2, (t+1)3, (t+1)4)`; `H op a b 0 = (a, ab, ba, b)` and
`(n1, n2, n3, n4) = ((n-1)1·(n-1)2, (n-1)2·(n-1)4, (n-1)3·(n-1)1, (n-1)4·(n-1)3)`. -/
def H {G : Type*} (op : G → G → G) (a b : G) : ℕ → Fin 4 → G
  | 0 => ![a, op a b, op b a, b]
  | t + 1 =>
      ![op (H op a b t 0) (H op a b t 1), op (H op a b t 1) (H op a b t 3),
        op (H op a b t 2) (H op a b t 0), op (H op a b t 3) (H op a b t 2)]

/-- The affine groupoid `x · y = α x + (1 - α) y` (Theorem 2.5: the `ℤ_m`-induced
quadratical quasigroups are exactly these with `2α² - 2α + 1 = 0`). -/
def affOp {R : Type*} [CommRing R] (α : R) (x y : R) : R := α * x + (1 - α) * y

/-- The coefficients `(1, i, -i, -1)` of a 4-cycle `{d, i d, -i d, -d}` based at `0`. -/
def cycleCoeff {R : Type*} [CommRing R] (i : R) : Fin 4 → R := ![1, i, -i, -1]

/-- **Load-bearing computation.** In the affine model with `2α² - 2α + 1 = 0`,
writing `i = 2α - 1`, `w = aba` and `d = a - w`, the `k`-th entry of `H(t+1)` is
`w + (1 + i)^t · c_k · d` with `c = (1, i, -i, -1)`. -/
theorem H_eq {R : Type*} [CommRing R] (α : R) (hα : 2 * α ^ 2 - 2 * α + 1 = 0)
    (a b : R) (t : ℕ) (k : Fin 4) :
    H (affOp α) a b t k = affOp α (affOp α a b) a
      + (1 + (2 * α - 1)) ^ t * cycleCoeff (2 * α - 1) k * (a - affOp α (affOp α a b) a) := by
  induction t generalizing k with
  | zero =>
    fin_cases k <;> simp only [H, affOp, cycleCoeff, pow_zero, Fin.zero_eta, Fin.mk_one,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk] <;>
      [ring; linear_combination (α * a - α * b - a + b) * hα;
       linear_combination (-α * a + α * b) * hα; linear_combination (-a + b) * hα]
  | succ t ih =>
    simp only [H, ih, pow_succ]
    generalize a - affOp α (affOp α a b) a = d
    generalize affOp α (affOp α a b) a = w
    generalize (1 + (2 * α - 1)) ^ t = s
    fin_cases k <;> simp only [affOp, cycleCoeff, Fin.zero_eta, Fin.mk_one,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk]
    · linear_combination (-s * d) * hα
    · linear_combination (-s * d) * hα
    · linear_combination (s * d) * hα
    · linear_combination (s * d) * hα


/-- Definition 3.12 with the intended size condition: `(G, op)` is *of the form
`Qn`* if `0 < n`, `|G| = 4n + 1`, and for some `a ≠ b` every element is `aba` or
lies in one of `H1, …, Hn`. -/
def IsFormQ {G : Type*} (op : G → G → G) (n : ℕ) : Prop :=
  0 < n ∧ Nat.card G = 4 * n + 1 ∧
    ∃ a b : G, a ≠ b ∧ ∀ x : G, x = op (op a b) a ∨ ∃ t < n, ∃ k : Fin 4, H op a b t k = x

/-- `Covers i n`: every nonzero `y` is `(1 + i)^t · c_k` for some `t < n` and
`c_k ∈ {1, i, -i, -1}`. -/
def Covers {R : Type*} [CommRing R] (i : R) (n : ℕ) : Prop :=
  ∀ y : R, y ≠ 0 → ∃ t < n, ∃ k : Fin 4, (1 + i) ^ t * cycleCoeff i k = y

/-- For `a ≠ b` in the affine model, `d = a - aba ≠ 0` (indeed `2d = a - b`). -/
theorem two_mul_sub_ne_zero {F : Type*} [Field F] (α : F) (hα : 2 * α ^ 2 - 2 * α + 1 = 0)
    (a b : F) (hab : a ≠ b) : a - affOp α (affOp α a b) a ≠ 0 := by
  intro hd
  apply hab
  have h2 : 2 * (a - affOp α (affOp α a b) a) = a - b := by
    simp only [affOp]
    linear_combination (b - a) * hα
  rw [hd, mul_zero] at h2
  exact (sub_eq_zero.mp h2.symm)

/-- For any base pair `a ≠ b`, the union `{aba} ∪ H1 ∪ ⋯ ∪ Hn` is all of `F`
iff `Covers (2α - 1) n`; in particular the condition does not depend on `(a, b)`. -/
theorem covers_iff_of_ne {F : Type*} [Field F] (α : F) (hα : 2 * α ^ 2 - 2 * α + 1 = 0)
    (a b : F) (hab : a ≠ b) (n : ℕ) :
    (∀ x : F, x = affOp α (affOp α a b) a ∨
        ∃ t < n, ∃ k : Fin 4, H (affOp α) a b t k = x) ↔ Covers (2 * α - 1) n := by
  have hd := two_mul_sub_ne_zero α hα a b hab
  simp only [H_eq α hα]
  generalize a - affOp α (affOp α a b) a = d at hd ⊢
  generalize affOp α (affOp α a b) a = w
  constructor
  · intro hcov y hy
    rcases hcov (w + y * d) with hx | ⟨t, ht, k, hk⟩
    · exact absurd (by linear_combination hx) (mul_ne_zero hy hd)
    · refine ⟨t, ht, k, mul_right_cancel₀ hd ?_⟩
      linear_combination hk
  · intro hcov x
    by_cases hxw : x = w
    · exact Or.inl hxw
    · right
      have hy : (x - w) / d ≠ 0 := div_ne_zero (sub_ne_zero.mpr hxw) hd
      obtain ⟨t, ht, k, hk⟩ := hcov _ hy
      refine ⟨t, ht, k, ?_⟩
      rw [hk, div_mul_cancel₀ _ hd]
      ring

/-- The affine model over a field is of the form `Qn` iff `0 < n`,
`|F| = 4n + 1`, and `Covers (2α - 1) n`. -/
theorem isFormQ_affOp_iff {F : Type*} [Field F] (α : F) (hα : 2 * α ^ 2 - 2 * α + 1 = 0)
    (n : ℕ) :
    IsFormQ (affOp α) n ↔ 0 < n ∧ Nat.card F = 4 * n + 1 ∧ Covers (2 * α - 1) n := by
  constructor
  · rintro ⟨hn, hcard, a, b, hab, hcov⟩
    exact ⟨hn, hcard, (covers_iff_of_ne α hα a b hab n).mp hcov⟩
  · rintro ⟨hn, hcard, hcov⟩
    exact ⟨hn, hcard, 1, 0, one_ne_zero, (covers_iff_of_ne α hα 1 0 one_ne_zero n).mpr hcov⟩

/-- Each 4-cycle coefficient is a power of `i` when `i² = -1`. -/
theorem exists_pow_eq_cycleCoeff {R : Type*} [CommRing R] (i : R) (hi : i ^ 2 = -1)
    (k : Fin 4) : ∃ m : ℕ, i ^ m = cycleCoeff i k := by
  fin_cases k
  · exact ⟨0, by simp [cycleCoeff]⟩
  · exact ⟨1, by simp [cycleCoeff]⟩
  · exact ⟨3, by simp [cycleCoeff, pow_succ, hi]⟩
  · exact ⟨2, by simp [cycleCoeff, hi]⟩

/-- Every power of `i` is a 4-cycle coefficient when `i² = -1`. -/
theorem exists_cycleCoeff_eq_pow {R : Type*} [CommRing R] (i : R) (hi : i ^ 2 = -1) (m : ℕ) :
    ∃ k : Fin 4, cycleCoeff i k = i ^ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases lt_or_ge m 4 with hm | hm
    · interval_cases m
      · exact ⟨0, by simp [cycleCoeff]⟩
      · exact ⟨1, by simp [cycleCoeff]⟩
      · exact ⟨3, by simp [cycleCoeff, hi]⟩
      · exact ⟨2, by simp [cycleCoeff, pow_succ, hi]⟩
    · obtain ⟨k, hk⟩ := ih (m - 4) (by omega)
      refine ⟨k, ?_⟩
      have h4 : i ^ 4 = 1 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hi]; norm_num
      rw [hk, ← one_mul (i ^ (m - 4)), ← h4, ← pow_add]
      congr 1
      omega

/-- **Group-theoretic step.** In a finite field with `|F| = 4n + 1`, `2 ≠ 0`,
`i² = -1` and `u = 1 + i`, `Covers i n` holds iff `i` and `u` generate `Fˣ`.
(`⇐` uses that `⟨i⟩` has order 4, so `Fˣ ⧸ ⟨i⟩` has order `n` and is generated
by the class of `u`.) -/
theorem covers_iff_closure_eq_top {F : Type*} [Field F] [Finite F] (n : ℕ)
    (hcard : Nat.card F = 4 * n + 1) (h2 : (2 : F) ≠ 0) (i u : Fˣ) (hi : (i : F) ^ 2 = -1)
    (hu : (u : F) = 1 + i) :
    Covers (i : F) n ↔ Subgroup.closure ({i, u} : Set Fˣ) = ⊤ := by
  constructor
  · intro hcov
    rw [eq_top_iff]
    intro g _
    obtain ⟨t, -, k, hk⟩ := hcov g g.ne_zero
    obtain ⟨m, hm⟩ := exists_pow_eq_cycleCoeff (i : F) hi k
    have hg : g = u ^ t * i ^ m := by
      ext
      push_cast
      rw [hu, hm, hk]
    rw [hg]
    exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
      (pow_mem (Subgroup.subset_closure (by simp)) _)
  · intro htop y hy
    set g : Fˣ := Units.mk0 y hy with hg
    set K : Subgroup Fˣ := Subgroup.zpowers i with hK
    have hi2 : ¬ i ^ 2 ^ 1 = 1 := by
      intro h
      have h' : (i : F) ^ 2 = 1 := by simpa using congrArg Units.val h
      apply h2
      linear_combination hi - h'
    have hi4 : i ^ 2 ^ (1 + 1) = 1 := by
      ext
      push_cast
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hi]
      norm_num
    have hord : orderOf i = 4 := orderOf_eq_prime_pow hi2 hi4
    have hKcard : Nat.card K = 4 := by rw [hK, Nat.card_zpowers, hord]
    have hFu : Nat.card Fˣ = 4 * n := by rw [Nat.card_units, hcard]; omega
    have hidx : K.index = n := by
      have hmul := K.index_mul_card
      rw [hKcard, hFu] at hmul
      omega
    have hi1 : ((i : Fˣ) : Fˣ ⧸ K) = 1 := (QuotientGroup.eq_one_iff i).mpr (Subgroup.mem_zpowers i)
    have hmem : (g : Fˣ ⧸ K) ∈ Subgroup.zpowers (u : Fˣ ⧸ K) := by
      have hgc : g ∈ Subgroup.closure ({i, u} : Set Fˣ) := htop ▸ Subgroup.mem_top g
      obtain ⟨a, b, hab⟩ := Subgroup.mem_closure_pair.mp hgc
      refine ⟨b, ?_⟩
      rw [← hab, QuotientGroup.mk_mul, QuotientGroup.mk_zpow, QuotientGroup.mk_zpow, hi1,
        one_zpow, one_mul]
    classical
    obtain ⟨t, ht, hteq⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hmem)
    have htn : t < n := by
      have hle : orderOf (u : Fˣ ⧸ K) ≤ Nat.card (Fˣ ⧸ K) := orderOf_le_card
      have hq : Nat.card (Fˣ ⧸ K) = n := hidx
      exact lt_of_lt_of_le (Finset.mem_range.mp ht) (hq ▸ hle)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq] at hteq
    obtain ⟨m, hm⟩ := Submonoid.mem_powers_iff _ _ |>.mp (mem_powers_iff_mem_zpowers.mpr hteq)
    obtain ⟨k, hk⟩ := exists_cycleCoeff_eq_pow (i : F) hi m
    refine ⟨t, htn, k, ?_⟩
    have hgu : u ^ t * i ^ m = g := by rw [hm]; group
    have hval := congrArg Units.val hgu
    push_cast at hval
    rw [hk, ← hu, hval, hg, Units.val_mk0]

/-- `2α² - 2α + 1 = 0` forces characteristic `≠ 2`. -/
theorem two_ne_zero_of_rel {F : Type*} [Field F] (α : F) (hα : 2 * α ^ 2 - 2 * α + 1 = 0) :
    (2 : F) ≠ 0 := by
  intro h
  apply one_ne_zero (α := F)
  linear_combination hα - (α ^ 2 - α) * h

/-- **Gaussian-unit criterion over finite fields.** For `2α² - 2α + 1 = 0`, units
`i = 2α - 1` and `u = 2α = 1 + i`, the groupoid `(F, α x + (1 - α) y)` is of the
form `Qn` iff `0 < n`, `|F| = 4n + 1` and `⟨i, u⟩ = Fˣ`. -/
theorem isFormQ_affOp_iff_closure {F : Type*} [Field F] [Finite F] (α : F)
    (hα : 2 * α ^ 2 - 2 * α + 1 = 0) (i u : Fˣ) (hi : (i : F) = 2 * α - 1)
    (hu : (u : F) = 2 * α) (n : ℕ) :
    IsFormQ (affOp α) n ↔
      0 < n ∧ Nat.card F = 4 * n + 1 ∧ Subgroup.closure ({i, u} : Set Fˣ) = ⊤ := by
  have h2 := two_ne_zero_of_rel α hα
  have hi2 : (i : F) ^ 2 = -1 := by rw [hi]; linear_combination 2 * hα
  have hu' : (u : F) = 1 + i := by rw [hu, hi]; ring
  rw [isFormQ_affOp_iff α hα, ← hi]
  constructor
  · rintro ⟨hn, hcard, hcov⟩
    exact ⟨hn, hcard, (covers_iff_closure_eq_top n hcard h2 i u hi2 hu').mp hcov⟩
  · rintro ⟨hn, hcard, htop⟩
    exact ⟨hn, hcard, (covers_iff_closure_eq_top n hcard h2 i u hi2 hu').mpr htop⟩

/-- **Main theorem (own reduction for Problem 1 of arXiv:1708.08830).** For a
prime `p ≡ 1 (mod 4)` and `α ∈ ℤ_p` with `2α² - 2α + 1 = 0`, the
`ℤ_p`-induced quadratical quasigroup `x · y = α x + (1 - α) y` is of the form
`Q((p-1)/4)` iff the units `i = 2α - 1` and `1 + i = 2α` generate `(ℤ_p)ˣ`. -/
theorem zmod_isFormQ_iff (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) (α : ZMod p)
    (hα : 2 * α ^ 2 - 2 * α + 1 = 0) (i u : (ZMod p)ˣ) (hi : (i : ZMod p) = 2 * α - 1)
    (hu : (u : ZMod p) = 2 * α) :
    IsFormQ (affOp α) ((p - 1) / 4) ↔ Subgroup.closure ({i, u} : Set (ZMod p)ˣ) = ⊤ := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hn : 0 < (p - 1) / 4 := by omega
  have hcard : Nat.card (ZMod p) = 4 * ((p - 1) / 4) + 1 := by rw [Nat.card_zmod]; omega
  rw [isFormQ_affOp_iff_closure α hα i u hi hu]
  exact ⟨fun h => h.2.2, fun h => ⟨hn, hcard, h⟩⟩

/-- `α = 21` satisfies `2α² - 2α + 1 = 0` in `ℤ_29`. -/
theorem rel_zmod29 : 2 * (21 : ZMod 29) ^ 2 - 2 * 21 + 1 = 0 := by decide

/-- The covering condition for `n = 7` in `ℤ_29` with `i = 2·21 - 1 = 12`. -/
theorem covers_zmod29 : Covers (2 * (21 : ZMod 29) - 1) 7 := by
  unfold Covers cycleCoeff
  decide

/-- For both roots `α` of `2α² - 2α + 1` in `ℤ_41`, the covering condition for
`n = 10` fails. -/
theorem not_covers_zmod41 :
    ∀ α : ZMod 41, 2 * α ^ 2 - 2 * α + 1 = 0 → ¬ Covers (2 * α - 1) 10 := by
  unfold Covers cycleCoeff
  decide

/-- A quadratical quasigroup of the form `Q7` exists: `(ℤ_29, 21x + 9y)`, one of
the paper's order-29 examples (Section 9 table). -/
theorem q7_exists : IsFormQ (affOp (21 : ZMod 29)) 7 := by
  haveI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  rw [isFormQ_affOp_iff (21 : ZMod 29) rel_zmod29]
  exact ⟨by norm_num, by rw [Nat.card_zmod], covers_zmod29⟩

/-- **New exclusion.** No `ℤ_41`-induced quadratical quasigroup
`x · y = α x + (1 - α) y` (`2α² - 2α + 1 = 0`) is of the form `Q10`. -/
theorem not_isFormQ_ten_zmod41 (α : ZMod 41) (hα : 2 * α ^ 2 - 2 * α + 1 = 0) :
    ¬ IsFormQ (affOp α) 10 := by
  haveI : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  rw [isFormQ_affOp_iff α hα]
  rintro ⟨-, -, hcov⟩
  exact not_covers_zmod41 α hα hcov

/-! ## The affine models are quadratical quasigroups -/

/-- For `2α² - 2α + 1 = 0` over a field, `x · y = α x + (1 - α) y` is a quasigroup
satisfying identity (A), i.e. a quadratical quasigroup. -/
theorem affOp_isQuasigroup_satisfiesA {F : Type*} [Field F] (α : F)
    (hα : 2 * α ^ 2 - 2 * α + 1 = 0) : IsQuasigroup (affOp α) ∧ SatisfiesA (affOp α) := by
  have hα0 : α ≠ 0 := by
    intro h
    rw [h] at hα
    norm_num at hα
  have hα1 : 1 - α ≠ 0 := by
    intro h
    have h' : α = 1 := by linear_combination -h
    subst h'
    exact one_ne_zero (by linear_combination hα)
  refine ⟨fun a b => ⟨⟨(b - α * a) / (1 - α), ?_, ?_⟩, ⟨(b - (1 - α) * a) / α, ?_, ?_⟩⟩, ?_⟩
  · simp only [affOp]
    rw [mul_div_cancel₀ _ hα1]
    ring
  · intro x hx
    rw [← hx, affOp, eq_div_iff hα1]
    ring
  · simp only [affOp]
    rw [mul_div_cancel₀ _ hα0]
    ring
  · intro y hy
    rw [← hy, affOp, eq_div_iff hα0]
    ring
  · intro x y z
    simp only [affOp]
    linear_combination (x - z) * hα

/-! ## Ground truth -/

/-- `H1` for `(ℤ_5, 4x + 2y)` (the paper's `Q1`) with `a = 1`, `b = 0`:
`(a, ab, ba, b) = (1, 4, 2, 0)`. -/
example : H (affOp (4 : ZMod 5)) 1 0 0 = ![1, 4, 2, 0] := by decide

/-- `aba = 3` there, so `{aba} ∪ H1 = ℤ_5`. -/
example : affOp (4 : ZMod 5) (affOp 4 1 0) 1 = 3 := by decide

/-- `affOp 4` on `ℤ_5` is the paper's `4x + 2y`. -/
example : ∀ x y : ZMod 5, affOp 4 x y = 4 * x + 2 * y := by decide

/-- The paper's `Q1` exists: `(ℤ_5, 4x + 2y)` is of the form `Q1`. -/
example : IsFormQ (affOp (4 : ZMod 5)) 1 := by
  have hrel : 2 * (4 : ZMod 5) ^ 2 - 2 * 4 + 1 = 0 := by decide
  have hcov : Covers (2 * (4 : ZMod 5) - 1) 1 := by unfold Covers cycleCoeff; decide
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [isFormQ_affOp_iff (4 : ZMod 5) hrel]
  exact ⟨by norm_num, by rw [Nat.card_zmod], hcov⟩

/-- The paper's `Q3 ≅ (ℤ_13, 11x + 3y)` (Section 6) is of the form `Q3`. -/
example : IsFormQ (affOp (11 : ZMod 13)) 3 := by
  have hrel : 2 * (11 : ZMod 13) ^ 2 - 2 * 11 + 1 = 0 := by decide
  have hcov : Covers (2 * (11 : ZMod 13) - 1) 3 := by unfold Covers cycleCoeff; decide
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  rw [isFormQ_affOp_iff (11 : ZMod 13) hrel]
  exact ⟨by norm_num, by rw [Nat.card_zmod], hcov⟩

/-- The paper's `Q4 ≅ (ℤ_17, 11x + 7y)` (Section 6) is of the form `Q4`. -/
example : IsFormQ (affOp (11 : ZMod 17)) 4 := by
  have hrel : 2 * (11 : ZMod 17) ^ 2 - 2 * 11 + 1 = 0 := by decide
  have hcov : Covers (2 * (11 : ZMod 17) - 1) 4 := by unfold Covers cycleCoeff; decide
  haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  rw [isFormQ_affOp_iff (11 : ZMod 17) hrel]
  exact ⟨by norm_num, by rw [Nat.card_zmod], hcov⟩

/-- `IsFormQ` is not trivially true: `(ℤ_29, 21x + 9y)` is not of the form `Q6`
(wrong cardinality). -/
example : ¬ IsFormQ (affOp (21 : ZMod 29)) 6 := by
  rintro ⟨-, hcard, -⟩
  rw [Nat.card_zmod] at hcard
  omega

/-- The units `i = 12` and `1 + i = 13` of `ℤ_29` (for `α = 21`). -/
def i29 : (ZMod 29)ˣ := ZMod.unitOfCoprime 12 (by norm_num)

/-- `u = 1 + i = 13 ∈ (ℤ_29)ˣ`. -/
def u29 : (ZMod 29)ˣ := ZMod.unitOfCoprime 13 (by norm_num)

/-- Non-vacuity of `zmod_isFormQ_iff` at `p = 29`: all hypotheses hold, and the
criterion gives `⟨12, 13⟩ = (ℤ_29)ˣ` from `q7_exists`. -/
theorem closure_zmod29_eq_top : Subgroup.closure ({i29, u29} : Set (ZMod 29)ˣ) = ⊤ := by
  have hi : (i29 : ZMod 29) = 2 * 21 - 1 := by decide
  have hu : (u29 : ZMod 29) = 2 * 21 := by decide
  haveI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  exact (zmod_isFormQ_iff 29 (by norm_num) 21 rel_zmod29 i29 u29 hi hu).mp q7_exists

/-- The units `i = 9` and `1 + i = 10` of `ℤ_41`. -/
def i41 : (ZMod 41)ˣ := ZMod.unitOfCoprime 9 (by norm_num)

/-- `u = 1 + i = 10 ∈ (ℤ_41)ˣ`. -/
def u41 : (ZMod 41)ˣ := ZMod.unitOfCoprime 10 (by norm_num)

/-- At `p = 41` (`α = 5`, `i = 9`) the criterion fails: `⟨9, 10⟩ ≠ (ℤ_41)ˣ`. -/
theorem closure_zmod41_ne_top : Subgroup.closure ({i41, u41} : Set (ZMod 41)ˣ) ≠ ⊤ := by
  have hrel : 2 * (5 : ZMod 41) ^ 2 - 2 * 5 + 1 = 0 := by decide
  have hi : (i41 : ZMod 41) = 2 * 5 - 1 := by decide
  have hu : (u41 : ZMod 41) = 2 * 5 := by decide
  haveI : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  intro htop
  exact not_isFormQ_ten_zmod41 5 hrel
    ((zmod_isFormQ_iff 41 (by norm_num) 5 hrel i41 u41 hi hu).mpr htop)

end Candidates.TranslatableQuadraticalQuasigroupOrders
