import Mathlib
import Xlib.ShearCircuit

/-!
# Quadratic rank: `s` shears give a quadratic part of rank at most `s`

The second lower-bound tool for the shear-circuit model (the first is the
degree-doubling engine `Circuit.totalDegree_polys_le`), a Strassen-style
multiplicative-complexity base case:

> After a circuit with `s` multiply-add shears, the **degree-2 homogeneous
> component** of every register polynomial is a sum of at most `s` products
> of two linear forms (`homogeneousComponent_two_polys`).

Consequently a target whose quadratic part is *not* expressible as `s` such
products needs more than `s` shears (`lt_shearCount_of_not_sumOfProducts`) —
even though `s` shears can produce total degree as high as `2 ^ s`. Each
shear contributes exactly one fresh product of linear forms to the quadratic
layer; everything else it creates lives in degree `≥ 3` or is a scalar
recombination of older products.

Two supplements make the tool usable end to end:

* **Functional form** (`lt_shearCount_of_not_sumOfProducts_run`): over a
  finite field `K` the syntactic hypothesis `polys Ci t = P` is replaced by
  functional agreement `∀ x, run Ci x t = eval x P`, provided
  `2 ^ shearCount Ci < |K|` and `P.totalDegree < |K|` — representatives of
  total degree `< |K|` of a function on `K^n` are unique (a Schwartz–Zippel
  consequence, `eq_of_eval_eq_of_totalDegree_lt`), so the register polynomial
  *is* `P`. Without the degree side condition a circuit could compute `P`'s
  function via a different representative — but only by paying
  `2 ^ shearCount Ci ≥ |K|`, i.e. `shearCount Ci ≥ log₂ |K|` shears
  (`lt_shearCount_or_card_le_two_pow_of_run` packages the dichotomy).
* **Separation witness** (`not_isSumOfProducts_one_quad`,
  `two_le_shearCount_of_quad`): `X₀X₁ + X₂X₃` is not a single product of two
  linear forms over any field, so any circuit placing it in a register needs
  `≥ 2` shears — the first concrete client of the tool.

Scope note for the elliptic-curve regime that motivates the shear model
(`Xlib.ShearAddition`): the post-slope EC addition step
`(c, λ) ↦ (a - c, c·λ - b)` has quadratic part `c·λ` — a *single* product of
two linear forms, product-rank `1` — so this tool can never give a
`≥ 2`-shear bound for the EC step itself, consistent with
`Xlib.ShearAddition.singleShear` achieving it in one shear. Separations
require product-rank `≥ 2`, as in the witness above.

The proof tracks the invariant (`Decomp`): every register is

  `C a + L + ∑ r, c r • (ℓ r * ℓ' r) + h`

with `L` homogeneous linear, `ℓ, ℓ'` a *shared* list of linear forms (one
pair per shear so far), and `h` of order `≥ 3` (`AboveDeg 3`). Affine layers
act linearly on all four pieces; a shear `x t ← x t + x i * x j` adds the
single new product `(linear part of x i) * (linear part of x j)` and garbage
of order `≥ 3`.

This machinery (multiplicative complexity of quadratic forms) has no
counterpart in Mathlib, and we know of no prior mechanization in any proof
assistant. The literature works over fields with homogeneous multiplication
sequences; the proof here needs only a commutative semiring and arbitrary
(not necessarily invertible) affine layers.

## References

* V. Strassen, *Vermeidung von Divisionen*, J. Reine Angew. Math. 264 (1973),
  184–202 — the multiplicative-complexity framework (Korollar 5: nonscalar
  multiplications vs. rank).
* P. Bürgisser, M. Clausen, M. A. Shokrollahi, *Algebraic Complexity Theory*,
  Springer 1997, §14.1 — textbook treatment of the multiplicative complexity
  of quadratic maps.
* C. Brand, P. Kaski, J. Wang, *Partition Rank and Algebraic Circuit Lower
  Bounds*, arXiv:2607.02241 (2026) — their Lemma 3 (two-slice decomposition
  of homogeneous multiplication sequences) generalizes the degree-2 statement
  here to all degrees `d ≥ 2`, over a field.
-/

namespace Xlib.ShearQuadraticRank

open MvPolynomial Xlib.ShearCircuit Xlib.ShearCircuit.Circuit

variable {k : Type*} [CommSemiring k] {n : ℕ}

/-! ## Order-≥ d polynomials -/

/-- Every monomial of `p` has degree at least `d` (`p` has order `≥ d`). -/
def AboveDeg (d : ℕ) (p : MvPolynomial (Fin n) k) : Prop :=
  ∀ m ∈ p.support, d ≤ m.degree

lemma AboveDeg.zero (d : ℕ) : AboveDeg d (0 : MvPolynomial (Fin n) k) := by
  intro m hm
  simp at hm

lemma AboveDeg.add {d : ℕ} {p q : MvPolynomial (Fin n) k}
    (hp : AboveDeg d p) (hq : AboveDeg d q) : AboveDeg d (p + q) := by
  intro m hm
  rcases Finset.mem_union.mp (support_add hm) with h | h
  exacts [hp m h, hq m h]

lemma AboveDeg.smul {d : ℕ} {p : MvPolynomial (Fin n) k} (c : k)
    (hp : AboveDeg d p) : AboveDeg d (c • p) :=
  fun m hm => hp m (support_smul hm)

lemma AboveDeg.sum {d : ℕ} {ι : Type*} {s : Finset ι}
    {f : ι → MvPolynomial (Fin n) k} (hf : ∀ i ∈ s, AboveDeg d (f i)) :
    AboveDeg d (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using AboveDeg.zero d
  | cons a s ha ih =>
      rw [Finset.sum_cons]
      exact (hf a (by simp)).add (ih fun i hi => hf i (by simp [hi]))

lemma AboveDeg.mul {d₁ d₂ : ℕ} {p q : MvPolynomial (Fin n) k}
    (hp : AboveDeg d₁ p) (hq : AboveDeg d₂ q) : AboveDeg (d₁ + d₂) (p * q) := by
  intro m hm
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul p q hm)
  rw [map_add]
  exact Nat.add_le_add (hp m₁ hm₁) (hq m₂ hm₂)

lemma AboveDeg.mono {d d' : ℕ} {p : MvPolynomial (Fin n) k} (h : d' ≤ d)
    (hp : AboveDeg d p) : AboveDeg d' p :=
  fun m hm => h.trans (hp m hm)

/-- A homogeneous polynomial of degree `d` has order `≥ d`. -/
lemma _root_.MvPolynomial.IsHomogeneous.aboveDeg {p : MvPolynomial (Fin n) k}
    {d : ℕ} (hp : p.IsHomogeneous d) : AboveDeg d p := by
  intro m hm
  by_contra h
  exact mem_support_iff.mp hm (hp.coeff_eq_zero (by omega))

lemma homogeneousComponent_eq_zero_of_aboveDeg {p : MvPolynomial (Fin n) k}
    {d e : ℕ} (hp : AboveDeg d p) (he : e < d) :
    homogeneousComponent e p = 0 :=
  homogeneousComponent_eq_zero' _ _ fun m hm => by
    have := hp m hm
    omega

/-! ## The register decomposition invariant -/

/-- Register decomposition relative to a shared list of quadratic products:
constant + homogeneous-linear + combination of the products `ℓ r * ℓ' r` +
order-≥3 remainder. -/
def Decomp {m : ℕ} (ℓ ℓ' : Fin m → MvPolynomial (Fin n) k)
    (p : MvPolynomial (Fin n) k) : Prop :=
  ∃ (a : k) (L h : MvPolynomial (Fin n) k) (c : Fin m → k),
    L.IsHomogeneous 1 ∧ AboveDeg 3 h ∧
    p = C a + L + (∑ r, c r • (ℓ r * ℓ' r)) + h

variable {m : ℕ} {ℓ ℓ' : Fin m → MvPolynomial (Fin n) k}

lemma Decomp.of_C (a : k) : Decomp ℓ ℓ' (C a : MvPolynomial (Fin n) k) :=
  ⟨a, 0, 0, 0, isHomogeneous_zero _ _ _, AboveDeg.zero 3, by simp⟩

lemma Decomp.zero : Decomp ℓ ℓ' (0 : MvPolynomial (Fin n) k) :=
  ⟨0, 0, 0, 0, isHomogeneous_zero _ _ _, AboveDeg.zero 3, by simp⟩

lemma Decomp.of_isHomogeneous_one {L : MvPolynomial (Fin n) k}
    (hL : L.IsHomogeneous 1) : Decomp ℓ ℓ' L :=
  ⟨0, L, 0, 0, hL, AboveDeg.zero 3, by simp⟩

lemma Decomp.of_aboveDeg {h : MvPolynomial (Fin n) k} (hh : AboveDeg 3 h) :
    Decomp ℓ ℓ' h :=
  ⟨0, 0, h, 0, isHomogeneous_zero _ _ _, hh, by simp⟩

lemma Decomp.add {p q : MvPolynomial (Fin n) k}
    (hp : Decomp ℓ ℓ' p) (hq : Decomp ℓ ℓ' q) : Decomp ℓ ℓ' (p + q) := by
  obtain ⟨a₁, L₁, h₁, c₁, hL₁, hh₁, rfl⟩ := hp
  obtain ⟨a₂, L₂, h₂, c₂, hL₂, hh₂, rfl⟩ := hq
  refine ⟨a₁ + a₂, L₁ + L₂, h₁ + h₂, c₁ + c₂, hL₁.add hL₂, hh₁.add hh₂, ?_⟩
  rw [map_add]
  rw [show (∑ r, (c₁ + c₂) r • (ℓ r * ℓ' r))
      = (∑ r, c₁ r • (ℓ r * ℓ' r)) + ∑ r, c₂ r • (ℓ r * ℓ' r) by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => by rw [Pi.add_apply, add_smul]]
  abel

lemma Decomp.smul {p : MvPolynomial (Fin n) k} (x : k)
    (hp : Decomp ℓ ℓ' p) : Decomp ℓ ℓ' (x • p) := by
  obtain ⟨a, L, h, c, hL, hh, rfl⟩ := hp
  refine ⟨x * a, x • L, x • h, x • c, ?_, hh.smul x, ?_⟩
  · rw [← mem_homogeneousSubmodule] at hL ⊢
    exact Submodule.smul_mem _ x hL
  · have hCa : x • (C a : MvPolynomial (Fin n) k) = C (x * a) := by
      rw [← C_mul', ← map_mul]
    rw [smul_add, smul_add, smul_add, Finset.smul_sum, hCa]
    congr 1
    congr 1
    exact Finset.sum_congr rfl fun r _ => by
      rw [smul_smul, Pi.smul_apply, smul_eq_mul]

lemma Decomp.sum {ι : Type*} {s : Finset ι} {f : ι → MvPolynomial (Fin n) k}
    (hf : ∀ i ∈ s, Decomp ℓ ℓ' (f i)) : Decomp ℓ ℓ' (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using Decomp.zero (ℓ := ℓ) (ℓ' := ℓ')
  | cons a s ha ih =>
      rw [Finset.sum_cons]
      exact (hf a (by simp)).add (ih fun i hi => hf i (by simp [hi]))

/-- A decomposition survives appending a new product pair (with coefficient
zero). -/
lemma Decomp.extend {p : MvPolynomial (Fin n) k} (hp : Decomp ℓ ℓ' p)
    (Lnew L'new : MvPolynomial (Fin n) k) :
    Decomp (Fin.snoc ℓ Lnew) (Fin.snoc ℓ' L'new) p := by
  obtain ⟨a, L, h, c, hL, hh, rfl⟩ := hp
  refine ⟨a, L, h, Fin.snoc c 0, hL, hh, ?_⟩
  congr 1
  congr 1
  rw [Fin.sum_univ_castSucc]
  simp

/-! ## Gate steps -/

/-- Affine layers preserve the decomposition (same product list). -/
lemma decomp_affine (M : Fin n → Fin n → k) (cst : Fin n → k)
    {p : Fin n → MvPolynomial (Fin n) k} (hp : ∀ t, Decomp ℓ ℓ' (p t))
    (t : Fin n) : Decomp ℓ ℓ' (((Gate.affine M cst).polyApp p) t) := by
  show Decomp ℓ ℓ' ((∑ j, C (M t j) * p j) + C (cst t))
  refine Decomp.add (Decomp.sum fun j _ => ?_) (Decomp.of_C _)
  rw [C_mul']
  exact (hp j).smul _

/-- The product of two decomposed registers, relative to the product list
extended by the pair of their linear parts: the only genuinely new quadratic
contribution of a shear is `Li * Lj`. -/
lemma decomp_mul (hℓ : ∀ r, (ℓ r).IsHomogeneous 1)
    (hℓ' : ∀ r, (ℓ' r).IsHomogeneous 1)
    {pi pj : MvPolynomial (Fin n) k} {ai aj : k}
    {Li Lj hi hj : MvPolynomial (Fin n) k} {ci cj : Fin m → k}
    (hLi : Li.IsHomogeneous 1) (hLj : Lj.IsHomogeneous 1)
    (hhi : AboveDeg 3 hi) (hhj : AboveDeg 3 hj)
    (hpi : pi = C ai + Li + (∑ r, ci r • (ℓ r * ℓ' r)) + hi)
    (hpj : pj = C aj + Lj + (∑ r, cj r • (ℓ r * ℓ' r)) + hj) :
    Decomp (Fin.snoc ℓ Li) (Fin.snoc ℓ' Lj) (pi * pj) := by
  set Qi : MvPolynomial (Fin n) k := ∑ r, ci r • (ℓ r * ℓ' r) with hQi
  set Qj : MvPolynomial (Fin n) k := ∑ r, cj r • (ℓ r * ℓ' r) with hQj
  have hQi2 : Qi.IsHomogeneous 2 := by
    rw [← mem_homogeneousSubmodule]
    exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _
      ((mem_homogeneousSubmodule _ _).mpr ((hℓ r).mul (hℓ' r)))
  have hQj2 : Qj.IsHomogeneous 2 := by
    rw [← mem_homogeneousSubmodule]
    exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _
      ((mem_homogeneousSubmodule _ _).mpr ((hℓ r).mul (hℓ' r)))
  have hgarbage : AboveDeg 3
      ((ai • hj + aj • hi)
        + ((Li * Qj + Li * hj) + (Qi * Lj + hi * Lj))
        + (Qi + hi) * (Qj + hj)) := by
    refine AboveDeg.add (AboveDeg.add ((hhj.smul ai).add (hhi.smul aj)) ?_) ?_
    · refine AboveDeg.add (AboveDeg.add ?_ ?_) (AboveDeg.add ?_ ?_)
      · exact hLi.aboveDeg.mul hQj2.aboveDeg
      · exact (hLi.aboveDeg.mul hhj).mono (by omega)
      · exact hQi2.aboveDeg.mul hLj.aboveDeg
      · exact (hhi.mul hLj.aboveDeg).mono (by omega)
    · refine (AboveDeg.mul (d₁ := 2) (d₂ := 2) ?_ ?_).mono (by omega)
      · exact hQi2.aboveDeg.add (hhi.mono (by omega))
      · exact hQj2.aboveDeg.add (hhj.mono (by omega))
  refine ⟨ai * aj, ai • Lj + aj • Li,
    (ai • hj + aj • hi) + ((Li * Qj + Li * hj) + (Qi * Lj + hi * Lj))
      + (Qi + hi) * (Qj + hj),
    Fin.snoc (fun r => ai * cj r + aj * ci r) 1, ?_, hgarbage, ?_⟩
  · rw [← mem_homogeneousSubmodule]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ ((mem_homogeneousSubmodule _ _).mpr hLj))
      (Submodule.smul_mem _ _ ((mem_homogeneousSubmodule _ _).mpr hLi))
  have hsum : (∑ r : Fin (m + 1),
        (Fin.snoc (fun r => ai * cj r + aj * ci r) 1 : Fin (m + 1) → k) r
          • (Fin.snoc ℓ Li r * Fin.snoc ℓ' Lj r))
      = ai • Qj + aj • Qi + Li * Lj := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, one_smul]
    congr 1
    rw [hQi, hQj, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => by
      rw [add_smul, smul_smul, smul_smul]
  rw [hsum, hpi, hpj]
  simp only [smul_eq_C_mul, map_mul]
  ring

/-- The shear step: the register file stays decomposed after extending the
product list by the linear parts of the two multiplied registers. -/
lemma decomp_shear (hℓ : ∀ r, (ℓ r).IsHomogeneous 1)
    (hℓ' : ∀ r, (ℓ' r).IsHomogeneous 1) (i j t₀ : Fin n)
    {p : Fin n → MvPolynomial (Fin n) k} (hp : ∀ t, Decomp ℓ ℓ' (p t)) :
    ∃ Li Lj : MvPolynomial (Fin n) k, Li.IsHomogeneous 1 ∧ Lj.IsHomogeneous 1 ∧
      ∀ t, Decomp (Fin.snoc ℓ Li) (Fin.snoc ℓ' Lj)
        (((Gate.shear i j t₀).polyApp p) t) := by
  obtain ⟨ai, Li, hi, ci, hLi, hhi, hpi⟩ := hp i
  obtain ⟨aj, Lj, hj, cj, hLj, hhj, hpj⟩ := hp j
  refine ⟨Li, Lj, hLi, hLj, fun t => ?_⟩
  show Decomp _ _ (if t = t₀ then p t₀ + p i * p j else p t)
  by_cases ht : t = t₀
  · rw [if_pos ht]
    exact ((hp t₀).extend Li Lj).add
      (decomp_mul hℓ hℓ' hLi hLj hhi hhj hpi hpj)
  · rw [if_neg ht]
    exact (hp t).extend Li Lj

/-! ## The invariant along a circuit -/

/-- Running a circuit from a decomposed register file yields a decomposed
file over the product list extended by one pair per shear gate. -/
lemma polysFrom_decomp (Ci : Circuit n k) :
    ∀ (p : Fin n → MvPolynomial (Fin n) k) (m : ℕ)
      (ℓ ℓ' : Fin m → MvPolynomial (Fin n) k),
      (∀ r, (ℓ r).IsHomogeneous 1) → (∀ r, (ℓ' r).IsHomogeneous 1) →
      (∀ t, Decomp ℓ ℓ' (p t)) →
      ∃ u v : Fin (m + shearCount Ci) → MvPolynomial (Fin n) k,
        (∀ r, (u r).IsHomogeneous 1) ∧ (∀ r, (v r).IsHomogeneous 1) ∧
        ∀ t, Decomp u v (polysFrom Ci p t) := by
  induction Ci with
  | nil =>
      intro p m ℓ ℓ' h1 h2 hp
      exact ⟨ℓ, ℓ', h1, h2, hp⟩
  | cons g C ih =>
      intro p m ℓ ℓ' h1 h2 hp
      cases g with
      | affine M cst =>
          exact ih ((Gate.affine M cst).polyApp p) m ℓ ℓ' h1 h2
            (decomp_affine M cst hp)
      | shear i j t₀ =>
          obtain ⟨Li, Lj, hLi, hLj, hstep⟩ := decomp_shear h1 h2 i j t₀ hp
          have hsnoc : ∀ r, ((Fin.snoc ℓ Li : Fin (m + 1) → _) r).IsHomogeneous 1 := by
            intro r
            induction r using Fin.lastCases with
            | last => simpa using hLi
            | cast r => simpa using h1 r
          have hsnoc' : ∀ r, ((Fin.snoc ℓ' Lj : Fin (m + 1) → _) r).IsHomogeneous 1 := by
            intro r
            induction r using Fin.lastCases with
            | last => simpa using hLj
            | cast r => simpa using h2 r
          obtain ⟨u, v, H1, H2, Hp⟩ :=
            ih ((Gate.shear i j t₀).polyApp p) (m + 1)
              (Fin.snoc ℓ Li) (Fin.snoc ℓ' Lj) hsnoc hsnoc' hstep
          rw [show m + shearCount (Gate.shear i j t₀ :: C) = m + 1 + shearCount C
            from by rw [shearCount_shear_cons]; omega]
          exact ⟨u, v, H1, H2, Hp⟩

/-! ## Main theorem and the lower-bound tool -/

/-- **Quadratic rank of a shear circuit.** The degree-2 homogeneous component
of every register of a circuit with `s` shear gates is a sum of at most `s`
products of two linear forms. (Compare: the total degree can reach `2 ^ s`.) -/
theorem homogeneousComponent_two_polys (Ci : Circuit n k) (t : Fin n) :
    ∃ ℓ ℓ' : Fin (shearCount Ci) → MvPolynomial (Fin n) k,
      (∀ r, (ℓ r).IsHomogeneous 1) ∧ (∀ r, (ℓ' r).IsHomogeneous 1) ∧
      homogeneousComponent 2 (polys Ci t) = ∑ r, ℓ r * ℓ' r := by
  suffices h : ∃ ℓ ℓ' : Fin (0 + shearCount Ci) → MvPolynomial (Fin n) k,
      (∀ r, (ℓ r).IsHomogeneous 1) ∧ (∀ r, (ℓ' r).IsHomogeneous 1) ∧
      homogeneousComponent 2 (polys Ci t) = ∑ r, ℓ r * ℓ' r by
    rwa [Nat.zero_add] at h
  obtain ⟨ℓ, ℓ', h1, h2, hp⟩ :=
    polysFrom_decomp Ci X 0 (fun _ => 0) (fun _ => 0)
      (fun r => isHomogeneous_zero _ _ _) (fun r => isHomogeneous_zero _ _ _)
      (fun t => Decomp.of_isHomogeneous_one (isHomogeneous_X _ _))
  obtain ⟨a, L, h, c, hL, hh, hEq⟩ := hp t
  refine ⟨fun r => c r • ℓ r, ℓ', ?_, h2, ?_⟩
  · intro r
    rw [← mem_homogeneousSubmodule]
    exact Submodule.smul_mem _ _ ((mem_homogeneousSubmodule _ _).mpr (h1 r))
  show homogeneousComponent 2 (polysFrom Ci X t) = _
  rw [hEq, map_add, map_add, map_add]
  have e1 : homogeneousComponent 2 (C a : MvPolynomial (Fin n) k) = 0 := by
    rw [homogeneousComponent_of_mem
      ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C _ a))]
    simp
  have e2 : homogeneousComponent 2 L = 0 := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hL)]
    simp
  have e3 : homogeneousComponent 2 (∑ r, c r • (ℓ r * ℓ' r)) =
      ∑ r, c r • (ℓ r * ℓ' r) := by
    rw [homogeneousComponent_of_mem
      (Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _
        ((mem_homogeneousSubmodule _ _).mpr ((h1 r).mul (h2 r))))]
    simp
  have e4 : homogeneousComponent 2 h = 0 :=
    homogeneousComponent_eq_zero_of_aboveDeg hh (by omega)
  rw [e1, e2, e3, e4, zero_add, add_zero, zero_add]
  exact Finset.sum_congr rfl fun r _ => (smul_mul_assoc (c r) (ℓ r) (ℓ' r)).symm

/-- `Q` is a sum of at most `s` products of two linear forms. -/
def IsSumOfProducts (s : ℕ) (Q : MvPolynomial (Fin n) k) : Prop :=
  ∃ ℓ ℓ' : Fin s → MvPolynomial (Fin n) k,
    (∀ r, (ℓ r).IsHomogeneous 1) ∧ (∀ r, (ℓ' r).IsHomogeneous 1) ∧
    Q = ∑ r, ℓ r * ℓ' r

/-- Padding with zero products: monotonicity of `IsSumOfProducts`. -/
lemma IsSumOfProducts.mono {s s' : ℕ} (hss' : s ≤ s')
    {Q : MvPolynomial (Fin n) k} (hQ : IsSumOfProducts s Q) :
    IsSumOfProducts s' Q := by
  obtain ⟨d, rfl⟩ : ∃ d, s' = s + d := ⟨s' - s, by omega⟩
  obtain ⟨ℓ, ℓ', h1, h2, hQ⟩ := hQ
  refine ⟨Fin.append ℓ (fun _ => 0), Fin.append ℓ' (fun _ => 0), ?_, ?_, ?_⟩
  · intro r
    refine Fin.addCases (fun i => ?_) (fun i => ?_) r
    · rw [Fin.append_left]
      exact h1 i
    · rw [Fin.append_right]
      exact isHomogeneous_zero _ _ _
  · intro r
    refine Fin.addCases (fun i => ?_) (fun i => ?_) r
    · rw [Fin.append_left]
      exact h2 i
    · rw [Fin.append_right]
      exact isHomogeneous_zero _ _ _
  · rw [hQ, Fin.sum_univ_add]
    simp

/-- **The lower-bound tool.** If the quadratic part of a target polynomial
`P` is not a sum of `s` products of linear forms, then no circuit with at
most `s` shears places `P` in a register.

The hypothesis `polys Ci t = P` is a *syntactic* identity of register
polynomials. Over a finite field, `lt_shearCount_of_not_sumOfProducts_run`
below replaces it with functional agreement `∀ x, run Ci x t = eval x P`
(under the degree side conditions that make representatives unique). -/
theorem lt_shearCount_of_not_sumOfProducts {P : MvPolynomial (Fin n) k}
    {s : ℕ} (hP : ¬ IsSumOfProducts s (homogeneousComponent 2 P))
    (Ci : Circuit n k) (t : Fin n) (hCi : polys Ci t = P) :
    s < shearCount Ci := by
  by_contra hle
  rw [not_lt] at hle
  obtain ⟨ℓ, ℓ', h1, h2, hEq⟩ := homogeneousComponent_two_polys Ci t
  exact hP (IsSumOfProducts.mono hle ⟨ℓ, ℓ', h1, h2, by rw [← hCi, hEq]⟩)

/-! ## The functional form over a finite field

`lt_shearCount_of_not_sumOfProducts` pins down the register *polynomial*.
Over a finite field a circuit could conceivably compute the same *function*
via a different representative and escape the bound; the results below close
that gap. The enabling fact is uniqueness of representatives of total degree
`< |K|` — a corollary of the Schwartz–Zippel lemma
(`MvPolynomial.schwartz_zippel_totalDegree`); the analogous uniqueness
statement is otherwise absent from Mathlib in this total-degree form (the
`restrictDegree`-based `MvPolynomial.eq_zero_of_eval_eq_zero` bounds each
*individual* degree instead, and is incomparable). -/

section Functional

variable {K : Type*} [Field K] [Fintype K]

/-- A polynomial over a finite field `K` of total degree `< |K|` that
vanishes at every point of `K^n` is zero. Schwartz–Zippel: a nonzero `p`
vanishes on at most a `totalDegree p / |K| < 1` fraction of `K^n`. -/
theorem eq_zero_of_eval_eq_zero_of_totalDegree_lt {p : MvPolynomial (Fin n) K}
    (h : ∀ x : Fin n → K, eval x p = 0)
    (hdeg : p.totalDegree < Fintype.card K) : p = 0 := by
  classical
  by_contra hp
  have hSZ := schwartz_zippel_totalDegree hp (Finset.univ : Finset K)
  have hfull : {f ∈ Fintype.piFinset fun _ : Fin n => (Finset.univ : Finset K) |
      eval f p = 0} = Fintype.piFinset fun _ : Fin n => (Finset.univ : Finset K) :=
    Finset.filter_true_of_mem fun f _ => h f
  rw [hfull, Fintype.piFinset_univ] at hSZ
  rw [show ((Finset.univ : Finset (Fin n → K)).card : ℚ≥0)
      = ((Finset.univ : Finset K).card : ℚ≥0) ^ n from by
    rw [Finset.card_univ, Finset.card_univ, Fintype.card_pi]
    push_cast
    simp [Fintype.card_fin]] at hSZ
  rw [div_self (by positivity)] at hSZ
  rw [one_le_div (by positivity)] at hSZ
  have : Fintype.card K ≤ p.totalDegree := by
    rw [Finset.card_univ] at hSZ
    exact_mod_cast hSZ
  omega

/-- **Uniqueness of low-degree representatives.** Two polynomials of total
degree `< |K|` that agree as functions on `K^n` are equal. -/
theorem eq_of_eval_eq_of_totalDegree_lt {p q : MvPolynomial (Fin n) K}
    (hp : p.totalDegree < Fintype.card K) (hq : q.totalDegree < Fintype.card K)
    (h : ∀ x, eval x p = eval x q) : p = q := by
  rw [← sub_eq_zero]
  refine eq_zero_of_eval_eq_zero_of_totalDegree_lt (fun x => ?_) ?_
  · rw [map_sub, h x, sub_self]
  · refine lt_of_le_of_lt ?_ (max_lt hp hq)
    rw [sub_eq_add_neg]
    exact (totalDegree_add _ _).trans (by rw [totalDegree_neg])

/-- **Representation rigidity.** A circuit whose degree budget
`2 ^ shearCount` is below `|K|` and which computes the function of a
polynomial `P` of total degree `< |K|` holds `P` itself in the register:
functional agreement upgrades to the syntactic identity that
`lt_shearCount_of_not_sumOfProducts` consumes. -/
theorem polys_eq_of_run_eq (Ci : Circuit n K) (t : Fin n)
    {P : MvPolynomial (Fin n) K}
    (hC : 2 ^ shearCount Ci < Fintype.card K)
    (hP : P.totalDegree < Fintype.card K)
    (hrun : ∀ x, run Ci x t = eval x P) : polys Ci t = P :=
  eq_of_eval_eq_of_totalDegree_lt
    (lt_of_le_of_lt (totalDegree_polys_le Ci t) hC) hP
    (fun x => by rw [← run_eq_eval_polys]; exact hrun x)

/-- **The lower-bound tool, functional form.** If the quadratic part of `P`
is not a sum of `s` products of linear forms, then no shear circuit with
degree budget below `|K|` computes the *function* of `P` (on all of `K^n`)
with at most `s` shears. -/
theorem lt_shearCount_of_not_sumOfProducts_run {P : MvPolynomial (Fin n) K}
    {s : ℕ} (hP : ¬ IsSumOfProducts s (homogeneousComponent 2 P))
    (hPdeg : P.totalDegree < Fintype.card K)
    (Ci : Circuit n K) (t : Fin n)
    (hC : 2 ^ shearCount Ci < Fintype.card K)
    (hrun : ∀ x, run Ci x t = eval x P) :
    s < shearCount Ci :=
  lt_shearCount_of_not_sumOfProducts hP Ci t
    (polys_eq_of_run_eq Ci t hC hPdeg hrun)

/-- The unconditional dichotomy: a circuit computing the function of `P`
either exceeds the quadratic-rank bound `s` or already pays the full degree
budget `2 ^ shearCount ≥ |K|` (that is, `shearCount ≥ log₂ |K|`). -/
theorem lt_shearCount_or_card_le_two_pow_of_run {P : MvPolynomial (Fin n) K}
    {s : ℕ} (hP : ¬ IsSumOfProducts s (homogeneousComponent 2 P))
    (hPdeg : P.totalDegree < Fintype.card K)
    (Ci : Circuit n K) (t : Fin n)
    (hrun : ∀ x, run Ci x t = eval x P) :
    s < shearCount Ci ∨ Fintype.card K ≤ 2 ^ shearCount Ci := by
  rcases lt_or_ge (2 ^ shearCount Ci) (Fintype.card K) with h2 | h2
  · exact Or.inl (lt_shearCount_of_not_sumOfProducts_run hP hPdeg Ci t h2 hrun)
  · exact Or.inr h2

end Functional

/-! ## A separation witness: `X₀X₁ + X₂X₃` needs two shears

The first concrete client of the lower-bound tool. Note that the
elliptic-curve addition step that motivates the shear model has quadratic
part `c·λ`, a single product of two linear forms (product-rank `1`), so it
can never separate — `Xlib.ShearAddition.singleShear` realises it in one
shear. Genuine separations start at product-rank `2`, and `X₀X₁ + X₂X₃` is
the smallest example. -/

section Separation

/-- A monomial of degree `1` is `single i 1`. -/
lemma exists_single_of_degree_eq_one {m : Fin n →₀ ℕ} (hm : m.degree = 1) :
    ∃ i, m = Finsupp.single i 1 := by
  obtain ⟨i, hi⟩ : m.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    rintro rfl
    simp at hm
  have hile : m i ≤ 1 := hm ▸ Finsupp.le_degree i m
  have hige : 1 ≤ m i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  refine ⟨i, Finsupp.ext fun j => ?_⟩
  rcases eq_or_ne j i with rfl | hj
  · simp only [Finsupp.single_eq_same]
    omega
  · rw [Finsupp.single_eq_of_ne hj]
    by_contra hjne
    have hjmem : j ∈ m.support := Finsupp.mem_support_iff.mpr hjne
    have h2 : 2 ≤ m.degree := by
      calc 2 ≤ m i + m j := by omega
        _ = ∑ x ∈ ({i, j} : Finset (Fin n)), m x := (Finset.sum_pair (Ne.symm hj)).symm
        _ ≤ ∑ x ∈ m.support, m x := Finset.sum_le_sum_of_subset (by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            exacts [hi, hjmem])
        _ = m.degree := rfl
    omega

/-- Canonical form of a linear form: a homogeneous polynomial of degree `1`
is the linear combination of the variables given by its coefficients. -/
lemma _root_.MvPolynomial.IsHomogeneous.eq_sum_C_mul_X
    {L : MvPolynomial (Fin n) k} (hL : L.IsHomogeneous 1) :
    L = ∑ i, C (L.coeff (Finsupp.single i 1)) * X i := by
  ext m
  rw [coeff_sum]
  simp only [coeff_C_mul, coeff_X']
  by_cases hm : m.degree = 1
  · obtain ⟨i, rfl⟩ := exists_single_of_degree_eq_one hm
    rw [Finset.sum_eq_single i
      (fun j _ hj => by
        rw [if_neg (fun hEq => hj
          (Finsupp.single_left_injective (α := Fin n) one_ne_zero hEq)), mul_zero])
      (fun h => absurd (Finset.mem_univ i) h)]
    rw [if_pos rfl, mul_one]
  · rw [hL.coeff_eq_zero hm]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    rw [if_neg, mul_zero]
    intro hEq
    exact hm (by rw [← hEq, Finsupp.degree_single])

/-- The scalar core of the witness: the bilinear form of `x₀x₁ + x₂x₃`
cannot factor through two linear functionals, over any field. Probing at the
standard basis vectors and their pairwise sums yields ten scalar equations
whose case analysis is contradictory. -/
lemma no_rank_one_factorization {K : Type*} [Field K] (a b : Fin 4 → K)
    (heval : ∀ x : Fin 4 → K,
      x 0 * x 1 + x 2 * x 3 = (∑ i, a i * x i) * (∑ i, b i * x i)) : False := by
  have d0 : a 0 * b 0 = 0 := by
    have h := (heval (Pi.single 0 1 : Fin 4 → K)).symm
    simpa only [Fin.sum_univ_four, Pi.add_apply, Pi.single_apply, Fin.reduceEq,
      reduceIte, mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add] using h
  have d1 : a 1 * b 1 = 0 := by
    have h := (heval (Pi.single 1 1 : Fin 4 → K)).symm
    simpa only [Fin.sum_univ_four, Pi.add_apply, Pi.single_apply, Fin.reduceEq,
      reduceIte, mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add] using h
  have d2 : a 2 * b 2 = 0 := by
    have h := (heval (Pi.single 2 1 : Fin 4 → K)).symm
    simpa only [Fin.sum_univ_four, Pi.add_apply, Pi.single_apply, Fin.reduceEq,
      reduceIte, mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add] using h
  have d3 : a 3 * b 3 = 0 := by
    have h := (heval (Pi.single 3 1 : Fin 4 → K)).symm
    simpa only [Fin.sum_univ_four, Pi.add_apply, Pi.single_apply, Fin.reduceEq,
      reduceIte, mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add] using h
  have p01 : (a 0 + a 1) * (b 0 + b 1) = 1 := by
    have h := (heval (Pi.single 0 1 + Pi.single 1 1 : Fin 4 → K)).symm
    simpa only [Fin.sum_univ_four, Pi.add_apply, Pi.single_apply, Fin.reduceEq,
      reduceIte, mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add] using h
  have p23 : (a 2 + a 3) * (b 2 + b 3) = 1 := by
    have h := (heval (Pi.single 2 1 + Pi.single 3 1 : Fin 4 → K)).symm
    simpa only [Fin.sum_univ_four, Pi.add_apply, Pi.single_apply, Fin.reduceEq,
      reduceIte, mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add] using h
  have p02 : (a 0 + a 2) * (b 0 + b 2) = 0 := by
    have h := (heval (Pi.single 0 1 + Pi.single 2 1 : Fin 4 → K)).symm
    simpa only [Fin.sum_univ_four, Pi.add_apply, Pi.single_apply, Fin.reduceEq,
      reduceIte, mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add] using h
  have p03 : (a 0 + a 3) * (b 0 + b 3) = 0 := by
    have h := (heval (Pi.single 0 1 + Pi.single 3 1 : Fin 4 → K)).symm
    simpa only [Fin.sum_univ_four, Pi.add_apply, Pi.single_apply, Fin.reduceEq,
      reduceIte, mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add] using h
  have p12 : (a 1 + a 2) * (b 1 + b 2) = 0 := by
    have h := (heval (Pi.single 1 1 + Pi.single 2 1 : Fin 4 → K)).symm
    simpa only [Fin.sum_univ_four, Pi.add_apply, Pi.single_apply, Fin.reduceEq,
      reduceIte, mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add] using h
  have p13 : (a 1 + a 3) * (b 1 + b 3) = 0 := by
    have h := (heval (Pi.single 1 1 + Pi.single 3 1 : Fin 4 → K)).symm
    simpa only [Fin.sum_univ_four, Pi.add_apply, Pi.single_apply, Fin.reduceEq,
      reduceIte, mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add] using h
  have h01 : a 0 * b 1 + a 1 * b 0 = 1 := by linear_combination p01 - d0 - d1
  have h23 : a 2 * b 3 + a 3 * b 2 = 1 := by linear_combination p23 - d2 - d3
  have h02 : a 0 * b 2 + a 2 * b 0 = 0 := by linear_combination p02 - d0 - d2
  have h03 : a 0 * b 3 + a 3 * b 0 = 0 := by linear_combination p03 - d0 - d3
  have h12 : a 1 * b 2 + a 2 * b 1 = 0 := by linear_combination p12 - d1 - d2
  have h13 : a 1 * b 3 + a 3 * b 1 = 0 := by linear_combination p13 - d1 - d3
  rcases eq_or_ne (a 0) 0 with ha0 | ha0
  · have ha1b0 : a 1 * b 0 = 1 := by linear_combination h01 - b 1 * ha0
    have ha1 : a 1 ≠ 0 := left_ne_zero_of_mul_eq_one ha1b0
    have hb1 : b 1 = 0 := (mul_eq_zero.mp d1).resolve_left ha1
    have hb2 : b 2 = 0 := by
      have h : a 1 * b 2 = 0 := by linear_combination h12 - a 2 * hb1
      exact (mul_eq_zero.mp h).resolve_left ha1
    have hb3 : b 3 = 0 := by
      have h : a 1 * b 3 = 0 := by linear_combination h13 - a 3 * hb1
      exact (mul_eq_zero.mp h).resolve_left ha1
    rw [hb2, hb3] at h23
    simp at h23
  · have hb0 : b 0 = 0 := (mul_eq_zero.mp d0).resolve_left ha0
    have ha0b1 : a 0 * b 1 = 1 := by linear_combination h01 - a 1 * hb0
    have hb1 : b 1 ≠ 0 := right_ne_zero_of_mul_eq_one ha0b1
    have hb2 : b 2 = 0 := by
      have h : a 0 * b 2 = 0 := by linear_combination h02 - a 2 * hb0
      exact (mul_eq_zero.mp h).resolve_left ha0
    have hb3 : b 3 = 0 := by
      have h : a 0 * b 3 = 0 := by linear_combination h03 - a 3 * hb0
      exact (mul_eq_zero.mp h).resolve_left ha0
    rw [hb2, hb3] at h23
    simp at h23

/-- **The separation witness.** Over any field, `X₀X₁ + X₂X₃` is not a
single product of two linear forms: the rank-`4` split quadratic form is not
product-rank `1`. -/
theorem not_isSumOfProducts_one_quad {K : Type*} [Field K] :
    ¬ IsSumOfProducts 1 (X 0 * X 1 + X 2 * X 3 : MvPolynomial (Fin 4) K) := by
  rintro ⟨ℓ, ℓ', h1, h2, hQ⟩
  rw [Fin.sum_univ_one] at hQ
  rw [(h1 0).eq_sum_C_mul_X, (h2 0).eq_sum_C_mul_X] at hQ
  refine no_rank_one_factorization
    (fun i => (ℓ 0).coeff (Finsupp.single i 1))
    (fun i => (ℓ' 0).coeff (Finsupp.single i 1)) fun x => ?_
  have h := congrArg (eval x) hQ
  simpa using h

/-- **First client of the lower-bound tool**: any shear circuit placing
`X₀X₁ + X₂X₃` in a register uses at least `2` shears — while the
degree-doubling engine alone (`Circuit.totalDegree_polys_le`) would only
give `≥ 1`. -/
theorem two_le_shearCount_of_quad {K : Type*} [Field K]
    (Ci : Circuit 4 K) (t : Fin 4)
    (hCi : polys Ci t = X 0 * X 1 + X 2 * X 3) : 2 ≤ shearCount Ci := by
  have hcomp : homogeneousComponent 2 (X 0 * X 1 + X 2 * X 3 : MvPolynomial (Fin 4) K)
      = X 0 * X 1 + X 2 * X 3 := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr
      (((isHomogeneous_X _ _).mul (isHomogeneous_X _ _)).add
        ((isHomogeneous_X _ _).mul (isHomogeneous_X _ _))))]
    simp
  have h := lt_shearCount_of_not_sumOfProducts (s := 1)
    (by rw [hcomp]; exact not_isSumOfProducts_one_quad) Ci t hCi
  omega

end Separation

end Xlib.ShearQuadraticRank
