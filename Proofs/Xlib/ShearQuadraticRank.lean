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
most `s` shears places `P` in a register. -/
theorem lt_shearCount_of_not_sumOfProducts {P : MvPolynomial (Fin n) k}
    {s : ℕ} (hP : ¬ IsSumOfProducts s (homogeneousComponent 2 P))
    (Ci : Circuit n k) (t : Fin n) (hCi : polys Ci t = P) :
    s < shearCount Ci := by
  by_contra hle
  rw [not_lt] at hle
  obtain ⟨ℓ, ℓ', h1, h2, hEq⟩ := homogeneousComponent_two_polys Ci t
  exact hP (IsSumOfProducts.mono hle ⟨ℓ, ℓ', h1, h2, by rw [← hCi, hEq]⟩)

end Xlib.ShearQuadraticRank
