/-
  Erdős Problem #857 (weak sunflower problem) — the Naslund–Sawin slice-rank
  bound on m(n,3).

  GROUND TRUTH PINNING (fetched live 2026-07-31 via `erdos fetch 857`).

    "Let m = m(n,k) be minimal such that in any collection of sets
     A_1,…,A_m ⊆ {1,…,n} there must exist a sunflower of size k — that is,
     some collection of k of the A_i which pairwise have the same
     intersection.  Estimate m(n,k) […]  When k=3 this is strongly connected
     to the cap set problem […] as observed by Alon, Shpilka, and Umans
     [ASU13].  Naslund and Sawin [NaSa17] have proved that
        m(n,3) ≤ (3/2^{2/3})^{(1+o(1))n}."

  This file formalizes the finite form of that Naslund–Sawin bound.  Source:
  References/arXiv-1606-09575/paper.tex (Naslund–Sawin, *Upper Bounds for
  Sunflower-Free sets*, Forum Math. Sigma 5 (2017) e15), Theorem 1:

      |F| ≤ 3(n+1) Σ_{k ≤ n/3} C(n,k)   for F ⊆ 2^{[n]} sunflower-free.

  STATE OF THE ART — WHAT THIS FILE IS NOT.  Erdős #857 asks for an *estimate*
  of m(n,k); it is open, and nothing here closes it.  Nor is the bound above the
  sharpest known.  Since Σ_{k ≤ n/3} C(n,k) = Θ(2^{H(1/3)n}/√n) and
  2^{H(1/3)} = 3/2^{2/3}, Theorem 1 reads O(n^{1/2}·(3/2^{2/3})^n); the
  polynomial factor has since been improved to O(n^{1/6}), at the same
  exponential base, by Ahmadi–Norouzi, *A Polynomial Improvement of
  Naslund–Sawin Bound for Sunflower-Free Families Using Triangular Tensors*
  (References/arXiv-2606-30593/main.tex, arXiv:2606.30593, June 2026),
  Theorem 1.2 — same non-uniform setting as #857.  The exponential base
  (3/2^{2/3})^n = 1.8899…^n is untouched by that work and remains the barrier.
  This file formalizes the Naslund–Sawin form only.

  NOTE ON #857's NORMALIZATION.  `m(n,3)` is the minimal FORCING size, one
  more than the largest sunflower-free family.  Exact values, computed here
  by exhaustive ILP (GLPK) and cross-checked against the independent Lean
  development github.com/SproutSeeds/sunflower-lean:
      max |F| = 2, 3, 5, 8, 12   and   m(n,3) = 3, 4, 6, 9, 13   for n = 1..5.

  DEFINITIONAL FIDELITY (§ 1 is entirely about this).  Upstream
  formal-conjectures spells the sunflower as
      `IsSunflower F := ∃ S, F.Pairwise (fun A B => A ∩ B = S)`
  (FormalConjecturesForMathlib/Combinatorics/SetFamily/Sunflower.lean, tree
  85f8637): distinct pairs, existential kernel, **no petal condition**.  The
  project's own Erdős–Rado notion `IsSunflowerWith` (Erdos/Erdos20/Sunflower.lean:76)
  additionally demands `∀ S ∈ sub, S \ K ≠ ∅`.  That extra clause is harmless
  for #20 (uniform families cannot have an empty petal) but is WRONG for #857,
  and `erdos857_petal_mismatch` below is the machine-checked witness.

  RETRACTION.  BilinearComplexity/CapsetSliceRank.lean § 6
  (`not_hasSunflower_image_vecSupport`) is therefore NOT an anchor to #857;
  its header has been annotated accordingly.  This file supplies the correct
  anchor.

  WHAT THE PIECES ARE.

    § 1  Definitional fidelity: the #857 sunflower notion (`WeakSunflower3`,
         `Erdos857Free`), the petal-mismatch witness, and the two bridges to
         the project's `BilinearComplexity.SunflowerFree` — which is, verbatim,
         Naslund–Sawin's per-layer condition (paper.tex line 262: "for any
         x,y,z ∈ S *not all equal*, there exists i such that {xᵢ,yᵢ,zᵢ} =
         {0,1,1}").
    § 2  `nsMonomialCount n` = #{multilinear monomials of degree ≤ n/3},
         spelled multiplicatively (`3 * card ≤ n`) to avoid ℕ-division junk.
    § 3  The Naslund–Sawin tensor `T(x,y,z) = ∏_c (2 − xᵢ − yᵢ − zᵢ)` over ℚ,
         its collapse to a diagonal tensor on a sunflower-free family, and
         `sliceRank_nsTensor` (= the family size) via Tao's diagonal lemma
         `BilinearComplexity.sliceRank_diag`.
    § 4  The slice-rank upper bound `sliceRank_nsTensor_le`, by explicit
         expansion of the product and regrouping by the lowest-degree block.
    § 5  Assembly: the layer bound and `erdos857Free_card_le`.
    § 6  The `m(n,3)` spelling matching upstream `ErdosProblems/857.lean`,
         with the `sInf` nonemptiness guard.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import BilinearComplexity.CapsetSliceRank

set_option autoImplicit false

namespace Erdos857

open BilinearComplexity

variable {n : ℕ}

/-! ## 1. The #857 sunflower notion, and its bridge to `SunflowerFree` -/

/-- The #857 sunflower notion at `k = 3`: three sets whose three pairwise
intersections coincide.  This is upstream `IsSunflower {A, B, C}` unfolded at
a three-element family — an existential kernel and no petal condition. -/
def WeakSunflower3 (A B C : Finset (Fin n)) : Prop :=
  A ∩ B = A ∩ C ∧ A ∩ B = B ∩ C

/-- `WeakSunflower3` is a conjunction of `Finset` equalities, hence decidable;
this is what lets the ground checks below run by `decide`. -/
instance (A B C : Finset (Fin n)) : Decidable (WeakSunflower3 A B C) := by
  unfold WeakSunflower3; infer_instance

/-- `WeakSunflower3` really is "some kernel is the common pairwise
intersection": the kernel is forced to be `A ∩ B`. -/
theorem weakSunflower3_iff_exists_kernel (A B C : Finset (Fin n)) :
    WeakSunflower3 A B C ↔ ∃ K, A ∩ B = K ∧ A ∩ C = K ∧ B ∩ C = K :=
  ⟨fun ⟨h₁, h₂⟩ => ⟨A ∩ B, rfl, h₁.symm, h₂.symm⟩,
   fun ⟨_, hAB, hAC, hBC⟩ => ⟨hAB.trans hAC.symm, hAB.trans hBC.symm⟩⟩

/-- A family of subsets of `Fin n` is #857-sunflower-free at `k = 3` when no
three *distinct* members have pairwise equal intersections.  `m(n,3)` is one
more than the largest cardinality of such a family (§ 6). -/
def Erdos857Free (F : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, ∀ C ∈ F, A ≠ B → A ≠ C → B ≠ C → ¬ WeakSunflower3 A B C

/-- `Erdos857Free` is a bounded quantification over a `Finset`, hence decidable.
Note the cost is exponential in `2 ^ n`: deciding it over *all* families of
subsets of `Fin n` enumerates `2 ^ (2 ^ n)` families, which is why the ground
checks below stop at `n = 2`. -/
instance (F : Finset (Finset (Fin n))) : Decidable (Erdos857Free F) := by
  unfold Erdos857Free; infer_instance

/-- Satisfiability of `Erdos857Free` at a nondegenerate model: the size-3
family `{{0}, {0,1}, {1}}` on `Fin 2` is #857-sunflower-free (`{0} ∩ {0,1} =
{0}` but `{0} ∩ {1} = ∅`), so the predicate is not vacuous. -/
example : Erdos857Free ({{0}, {0, 1}, {1}} : Finset (Finset (Fin 2))) := by decide

/-- **The petal mismatch.**  `{{0}, {0,1}, {0,2}} ⊆ 2^(Fin 3)` is a #857
3-sunflower — all three pairwise intersections are `{0}` — yet carries no
in-tree `HasSunflower … 3`, because the kernel-attaining member `{0}` has an
empty petal and `IsSunflowerWith` demands `S \ K ≠ ∅`.  Hence
`¬ HasSunflower F 3` is strictly weaker than `Erdos857Free F`, and the
Erdős–Rado bridge of CapsetSliceRank § 6 is not a #857 statement. -/
theorem erdos857_petal_mismatch :
    WeakSunflower3 ({0} : Finset (Fin 3)) {0, 1} {0, 2} ∧
      ¬ HasSunflower ({{0}, {0, 1}, {0, 2}} : Finset (Finset (Fin 3))) 3 := by
  refine ⟨by decide, ?_⟩
  rintro ⟨sub, hsub, hcard, K, hK⟩
  have hfam : sub = ({{0}, {0, 1}, {0, 2}} : Finset (Finset (Fin 3))) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; decide)
  subst hfam
  obtain ⟨-, hpetal, hinter⟩ := hK
  have hK0 : K = ({0} : Finset (Fin 3)) := by
    rw [← hinter {0, 1} (by decide) {0, 2} (by decide) (by decide)]
    decide
  have hbad := hpetal ({0} : Finset (Fin 3)) (by decide)
  rw [hK0] at hbad
  exact hbad (by decide)

/-- **`SunflowerFree` ⟹ #857-free supports.**  The project's `F_2^n`
condition implies #857-sunflower-freeness of the support family. -/
theorem sunflowerFree_erdos857Free {S : Finset (Fin n → ZMod 2)}
    (hS : SunflowerFree S) : Erdos857Free (S.image vecSupport) := by
  intro A hA B hB C hC hAB _ _ hw
  obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨y, hyS, rfl⟩ := Finset.mem_image.mp hB
  obtain ⟨z, hzS, rfl⟩ := Finset.mem_image.mp hC
  have hne : ¬(x = y ∧ y = z) := by
    rintro ⟨rfl, rfl⟩
    exact hAB rfl
  obtain ⟨i, hi⟩ := hS x hxS y hyS z hzS hne
  exact (forall_not_exactlyTwoOnes_iff x y z).mpr hw i hi

/-- Equal-cardinality finsets are incomparable unless equal.  This is the whole
content of the layering step: a layer of a set family is an antichain. -/
theorem eq_of_subset_of_card_eq {A C : Finset (Fin n)} (hsub : A ⊆ C)
    (hcard : A.card = C.card) : A = C :=
  Finset.eq_of_subset_of_card_le hsub hcard.ge

/-- **The layering converse** (Naslund–Sawin, References/arXiv-1606-09575
line 262).  On a layer — all supports of one fixed size — #857-freeness
upgrades to the "not all equal" condition `SunflowerFree`.  The extra triples
that `SunflowerFree` constrains, those with a repeated entry, are exactly the
ones a layer rules out for free. -/
theorem erdos857Free_layer {S : Finset (Fin n → ZMod 2)} {l : ℕ}
    (hlayer : ∀ x ∈ S, (vecSupport x).card = l)
    (hfree : Erdos857Free (S.image vecSupport)) : SunflowerFree S := by
  intro x hx y hy z hz hne
  by_contra hcon
  rw [not_exists] at hcon
  have hw : WeakSunflower3 (vecSupport x) (vecSupport y) (vecSupport z) :=
    (forall_not_exactlyTwoOnes_iff x y z).mp hcon
  obtain ⟨hw₁, hw₂⟩ := hw
  have hlayer_ne : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ vecSupport u ⊆ vecSupport v := by
    intro u hu v hv huv hsub
    exact huv (vecSupport_injective
      (eq_of_subset_of_card_eq hsub ((hlayer u hu).trans (hlayer v hv).symm)))
  by_cases hxy : x = y
  · subst hxy
    have hxz : x ≠ z := fun h => hne ⟨rfl, h⟩
    rw [Finset.inter_self] at hw₁
    exact hlayer_ne x hx z hz hxz (Finset.inter_eq_left.mp hw₁.symm)
  · by_cases hxz : x = z
    · subst hxz
      rw [Finset.inter_self] at hw₁
      exact hlayer_ne x hx y hy hxy (Finset.inter_eq_left.mp hw₁)
    · by_cases hyz : y = z
      · subst hyz
        rw [Finset.inter_self] at hw₂
        exact hlayer_ne y hy x hx (Ne.symm hxy) (Finset.inter_eq_right.mp hw₂)
      · exact hfree _ (Finset.mem_image_of_mem _ hx) _ (Finset.mem_image_of_mem _ hy)
          _ (Finset.mem_image_of_mem _ hz)
          (fun h => hxy (vecSupport_injective h))
          (fun h => hxz (vecSupport_injective h))
          (fun h => hyz (vecSupport_injective h))
          ⟨hw₁, hw₂⟩

/-! ## 2. The Naslund–Sawin monomial count -/

/-- The index set of the Naslund–Sawin slice decomposition: subsets of
`Fin n` of size at most `n/3`, spelled multiplicatively (`3 * card ≤ n`) so
that no `ℕ`-division junk enters the statement.  These index the multilinear
monomials `∏_{c ∈ A} x_c` of total degree at most `n/3`. -/
def nsSmallSets (n : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun A : Finset (Fin n) => 3 * A.card ≤ n

/-- `Σ_{k ≤ n/3} C(n,k)`, the number of multilinear monomials in `n`
variables of total degree at most `n/3` (References/arXiv-1606-09575,
Theorem 1).  Asymptotically `(2^{H(1/3)})^n = 1.8899…^n`. -/
def nsMonomialCount (n : ℕ) : ℕ := (nsSmallSets n).card

/-- Ground checks: 1, 1, 1, 4, 5, 6, 22 monomials for n = 0,…,6 (degree
thresholds ⌊n/3⌋ = 0,0,0,1,1,1,2).  `n = 6` is the discriminating case, the
first threshold that reaches degree-2 monomials, so the count is
`22 = 1 + 6 + 15` rather than the `1 + n` of every smaller `n`. -/
example : nsMonomialCount 0 = 1 ∧ nsMonomialCount 1 = 1 ∧ nsMonomialCount 2 = 1 ∧
    nsMonomialCount 3 = 4 ∧ nsMonomialCount 4 = 5 ∧ nsMonomialCount 5 = 6 ∧
    nsMonomialCount 6 = 22 := by decide

/-- Membership in `nsSmallSets`. -/
@[simp] theorem mem_nsSmallSets {A : Finset (Fin n)} :
    A ∈ nsSmallSets n ↔ 3 * A.card ≤ n := by
  simp [nsSmallSets]

/-! ## 3. The Naslund–Sawin tensor and its diagonal collapse -/

/-- The `0/1` lift of a bit into `ℚ`.  Naslund–Sawin work in characteristic
zero (paper.tex line 244: "Our work uses functions valued in a field of
characteristic zero"), so `ℚ` — not `ZMod 2` — is the right target. -/
def bit (a : ZMod 2) : ℚ := if a = 1 then 1 else 0

@[simp] theorem bit_zero : bit 0 = 0 := by decide
@[simp] theorem bit_one : bit 1 = 1 := by decide

/-- Two-valuedness of `ZMod 2`, as a case-split tool. -/
theorem zmod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

/-- **The pointwise vanishing criterion.**  A coordinate factor
`2 − (xᵢ + yᵢ + zᵢ)` vanishes exactly when exactly two of the three bits are
`1` — Naslund–Sawin's "{xᵢ,yᵢ,zᵢ} = {0,1,1}" (paper.tex line 273). -/
theorem bit_factor_eq_zero_iff (a b c : ZMod 2) :
    2 - (bit a + bit b + bit c) = 0 ↔ ExactlyTwoOnes a b c := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    rcases zmod2_cases c with rfl | rfl <;>
      simp only [bit_zero, bit_one, ExactlyTwoOnes] <;> norm_num

/-- **The Naslund–Sawin tensor** of an `m`-tuple of points of `F_2^n`
(paper.tex line 271): `T(x,y,z) = ∏_c (2 − (x_c + y_c + z_c))` over `ℚ`.  It is
nonvanishing exactly on triples with no exactly-two-ones coordinate, i.e. on
Δ-systems of supports. -/
def nsTensor {n m : ℕ} (v : Fin m → Fin n → ZMod 2) : Tensor ℚ m m m :=
  fun i j l => ∏ c, (2 - (bit (v i c) + bit (v j c) + bit (v l c)))

/-- Ground check: on the single point `0 ∈ F_2^1` the tensor is `2`. -/
example : nsTensor (![![0]] : Fin 1 → Fin 1 → ZMod 2) 0 0 0 = 2 := by
  norm_num [nsTensor, bit, Fin.prod_univ_one]

/-- Ground check, discriminating: the antichain `{01, 10} ⊆ F_2^2` has a
vanishing off-diagonal entry at the repeated-index triple `(0,0,1)`, because
`x = 01, y = 01, z = 10` has an exactly-two-ones coordinate. -/
example : nsTensor (![![0, 1], ![1, 0]] : Fin 2 → Fin 2 → ZMod 2) 0 0 1 = 0 := by
  norm_num [nsTensor, bit, Fin.prod_univ_two]

/-- Nonvanishing of the tensor is exactly the Δ-system condition. -/
theorem nsTensor_ne_zero_iff {m : ℕ} (v : Fin m → Fin n → ZMod 2) (i j l : Fin m) :
    nsTensor v i j l ≠ 0 ↔ ∀ c, ¬ ExactlyTwoOnes (v i c) (v j c) (v l c) := by
  rw [nsTensor, Finset.prod_ne_zero_iff]
  exact forall_congr' fun c =>
    ⟨fun h hc => h (Finset.mem_univ c) ((bit_factor_eq_zero_iff _ _ _).mpr hc),
     fun h _ hz => h ((bit_factor_eq_zero_iff _ _ _).mp hz)⟩

/-- Diagonal entries never vanish: each factor is `2 − 3·bit ∈ {2, −1}`. -/
theorem nsTensor_diag_ne_zero {m : ℕ} (v : Fin m → Fin n → ZMod 2) (i : Fin m) :
    nsTensor v i i i ≠ 0 := by
  rw [nsTensor_ne_zero_iff]
  intro c hc
  rcases zmod2_cases (v i c) with h | h <;> rw [h] at hc <;> exact absurd hc (by decide)

/-- **Diagonal collapse.**  On an injective enumeration of a `SunflowerFree`
family the tensor is supported on the diagonal, so Tao's diagonal lemma
applies. -/
theorem nsTensor_eq_diag {m : ℕ} {v : Fin m → Fin n → ZMod 2}
    (hv : Function.Injective v) (hfree : SunflowerFree (Finset.image v Finset.univ)) :
    nsTensor v = diag (fun i => nsTensor v i i i) := by
  funext i j l
  by_cases hall : i = j ∧ j = l
  · obtain ⟨rfl, rfl⟩ := hall
    simp only [diag, and_self, if_true]
  · show nsTensor v i j l = if i = j ∧ j = l then _ else 0
    rw [if_neg hall]
    by_contra hne
    obtain ⟨c, hc⟩ :=
      hfree (v i) (Finset.mem_image_of_mem v (Finset.mem_univ i))
        (v j) (Finset.mem_image_of_mem v (Finset.mem_univ j))
        (v l) (Finset.mem_image_of_mem v (Finset.mem_univ l))
        (fun h => hall ⟨hv h.1, hv h.2⟩)
    exact (nsTensor_ne_zero_iff v i j l).mp hne c hc

/-- **The family size is a slice rank** (Naslund–Sawin Lemma 1, i.e. Tao's
diagonal lemma `BilinearComplexity.sliceRank_diag`): the slice rank of the
tensor of a sunflower-free tuple is the number of points. -/
theorem sliceRank_nsTensor {m : ℕ} {v : Fin m → Fin n → ZMod 2}
    (hv : Function.Injective v) (hfree : SunflowerFree (Finset.image v Finset.univ)) :
    sliceRank (nsTensor v) = m := by
  rw [nsTensor_eq_diag hv hfree, sliceRank_diag]
  simp only [ne_eq, nsTensor_diag_ne_zero v, not_false_eq_true, Finset.filter_true_of_mem,
    Finset.card_univ, Fintype.card_fin, implies_true]

/-! ## 4. The slice-rank upper bound -/

section Decomposition

/-! The Naslund–Sawin expansion works over three arbitrary `ℚ`-vectors; only
at the very end are they specialized to the bit vectors of a tuple. -/

/-- The product form of the Naslund–Sawin tensor at three `ℚ`-vectors. -/
def nsProd (x y z : Fin n → ℚ) : ℚ := ∏ c, (2 - (x c + y c + z c))

/-- The `ℚ`-valued bit vector of one point of a tuple: the `{0,1}` indicator
of its support, which is what the Naslund–Sawin product consumes. -/
def nsBits {m : ℕ} (v : Fin m → Fin n → ZMod 2) (i : Fin m) : Fin n → ℚ :=
  fun c => bit (v i c)

/-- The tensor is the product form evaluated at the three points' bit vectors.
Definitional, but it is the hinge that lets § 4 argue about `nsProd` at three
arbitrary `ℚ`-vectors and only specialize to bit vectors at the end. -/
theorem nsTensor_eq_nsProd {m : ℕ} (v : Fin m → Fin n → ZMod 2) (i j l : Fin m) :
    nsTensor v i j l = nsProd (nsBits v i) (nsBits v j) (nsBits v l) := rfl

/-- The four terms of one coordinate factor: the constant `2` and the three
negated variables, labelled by `Fin 4`. -/
def nsFactor (x y z : Fin n → ℚ) (a : Fin 4) (c : Fin n) : ℚ :=
  if a = 0 then 2 else if a = 1 then -(x c) else if a = 2 then -(y c) else -(z c)

section Factors
variable (x y z : Fin n → ℚ) (c : Fin n)

@[simp] theorem nsFactor_zero : nsFactor x y z 0 c = 2 := rfl
@[simp] theorem nsFactor_one : nsFactor x y z 1 c = -(x c) := rfl
@[simp] theorem nsFactor_two : nsFactor x y z 2 c = -(y c) := rfl
@[simp] theorem nsFactor_three : nsFactor x y z 3 c = -(z c) := rfl

/-- The four labelled summands reassemble one coordinate factor. -/
theorem sum_nsFactor : ∑ a : Fin 4, nsFactor x y z a c = 2 - (x c + y c + z c) := by
  rw [Fin.sum_univ_four, nsFactor_zero, nsFactor_one, nsFactor_two, nsFactor_three]
  ring

end Factors

/-- One term of the expansion: a choice `w` of which of the four summands to
take at each coordinate. -/
def nsTerm (x y z : Fin n → ℚ) (w : Fin n → Fin 4) : ℚ := ∏ c, nsFactor x y z (w c) c

/-- The multilinear monomial `∏_{c ∈ A} (−x_c)`. -/
def nsMon (x : Fin n → ℚ) (A : Finset (Fin n)) : ℚ := ∏ c ∈ A, -(x c)

/-- The block of coordinates where `w` selects label `a`. -/
def nsPre (a : Fin 4) (w : Fin n → Fin 4) : Finset (Fin n) :=
  Finset.univ.filter fun c => w c = a

/-- Membership in `nsPre`. -/
@[simp] theorem mem_nsPre {a : Fin 4} {w : Fin n → Fin 4} {c : Fin n} :
    c ∈ nsPre a w ↔ w c = a := by
  simp [nsPre]

/-- The four blocks partition the `n` coordinates. -/
theorem sum_card_nsPre (w : Fin n → Fin 4) : ∑ a : Fin 4, (nsPre a w).card = n := by
  have h := Finset.card_eq_sum_card_fiberwise
    (f := w) (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Fin 4)))
    fun c _ => Finset.mem_univ (w c)
  simpa only [nsPre, Finset.card_univ, Fintype.card_fin] using h.symm

/-- The three variable blocks have at most `n` coordinates between them. -/
theorem card_nsPre_add_le (w : Fin n → Fin 4) :
    (nsPre 1 w).card + (nsPre 2 w).card + (nsPre 3 w).card ≤ n := by
  have h := sum_card_nsPre w
  rw [Fin.sum_univ_four] at h
  omega

/-- The label of a smallest variable block: the mode carrying the low-degree
monomial in the Naslund–Sawin regrouping.  Values in `{1, 2, 3}`. -/
def nsMode (w : Fin n → Fin 4) : Fin 4 :=
  if 3 * (nsPre 1 w).card ≤ n then 1
  else if 3 * (nsPre 2 w).card ≤ n then 2
  else 3

/-- `nsMode` never selects the constant block `0`: it names one of the three
variable blocks, which is what makes the three-slice decomposition of § 4
exhaustive. -/
theorem nsMode_cases (w : Fin n → Fin 4) :
    nsMode w = 1 ∨ nsMode w = 2 ∨ nsMode w = 3 := by
  unfold nsMode
  split_ifs <;> simp

/-- **The pigeonhole step.**  The block selected by `nsMode` always has degree
at most `n/3`: if neither of the first two blocks is small then the third is,
because the three block sizes sum to at most `n`. -/
theorem nsPre_nsMode_mem_smallSets (w : Fin n → Fin 4) :
    nsPre (nsMode w) w ∈ nsSmallSets n := by
  have hsum := card_nsPre_add_le w
  rw [mem_nsSmallSets]
  unfold nsMode
  split_ifs with h1 h2
  · exact h1
  · exact h2
  · omega

/-! ### Expanding the product -/

/-- **The expansion** (References/arXiv-1606-09575, line 274: "Expanding the
product form for T(x,y,z), we may write T(x,y,z) as a linear combination of
products of three monomials").  Choosing one of the four summands at each of
the `n` coordinates enumerates the expansion. -/
theorem nsProd_eq_sum_nsTerm (x y z : Fin n → ℚ) :
    nsProd x y z = ∑ w : Fin n → Fin 4, nsTerm x y z w := by
  unfold nsProd nsTerm
  simp_rw [← sum_nsFactor x y z]
  rw [Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin 4)))
    (fun c a => nsFactor x y z a c), Fintype.piFinset_univ]

/-- Inside the fibre of `w` over `a`, the chosen summand is the constant `a`
one. -/
theorem prod_nsFactor_fiber (x y z : Fin n → ℚ) (w : Fin n → Fin 4) (a : Fin 4) :
    ∏ c ∈ nsPre a w, nsFactor x y z (w c) c = ∏ c ∈ nsPre a w, nsFactor x y z a c :=
  Finset.prod_congr rfl fun _ hc => by rw [mem_nsPre.mp hc]

/-- **Each term is a product of three monomials.**  Grouping the coordinates
by which summand was chosen splits one term of the expansion into a scalar
`2^{#constant coordinates}` and one multilinear monomial in each of the three
variable blocks. -/
theorem nsTerm_factor (x y z : Fin n → ℚ) (w : Fin n → Fin 4) :
    nsTerm x y z w =
      2 ^ (nsPre 0 w).card *
        (nsMon x (nsPre 1 w) * (nsMon y (nsPre 2 w) * nsMon z (nsPre 3 w))) := by
  have hfib := Finset.prod_fiberwise (Finset.univ : Finset (Fin n)) w
    (fun c => nsFactor x y z (w c) c)
  rw [nsTerm, ← hfib, Fin.prod_univ_four]
  rw [show (Finset.univ.filter fun c => w c = (0 : Fin 4)) = nsPre 0 w from rfl,
    show (Finset.univ.filter fun c => w c = (1 : Fin 4)) = nsPre 1 w from rfl,
    show (Finset.univ.filter fun c => w c = (2 : Fin 4)) = nsPre 2 w from rfl,
    show (Finset.univ.filter fun c => w c = (3 : Fin 4)) = nsPre 3 w from rfl]
  rw [prod_nsFactor_fiber, prod_nsFactor_fiber, prod_nsFactor_fiber, prod_nsFactor_fiber]
  simp only [nsFactor_zero, nsFactor_one, nsFactor_two, nsFactor_three, Finset.prod_const, nsMon]
  ring

/-! ### Indexing the low-degree monomials -/

/-- The `s`-th small set, i.e. the `s`-th multilinear monomial of degree at
most `n/3`.  Indexing `nsSmallSets n` by `Fin (nsMonomialCount n)` is what the
`SliceRankLE` primitive requires of a slice family. -/
noncomputable def nsMono (n : ℕ) (s : Fin (nsMonomialCount n)) : Finset (Fin n) :=
  ((nsSmallSets n).equivFin.symm s : Finset (Fin n))

/-- `nsMono` lands in the low-degree monomials it indexes. -/
theorem nsMono_mem (s : Fin (nsMonomialCount n)) : nsMono n s ∈ nsSmallSets n :=
  ((nsSmallSets n).equivFin.symm s).2

/-- `nsMono` names each low-degree monomial at most once — no slice is
double-counted against the `3 * nsMonomialCount n` budget. -/
theorem nsMono_injective : Function.Injective (nsMono n) := fun _s _t hst =>
  (nsSmallSets n).equivFin.symm.injective (Subtype.ext hst)

/-- `nsMono` names each low-degree monomial at least once.  With
`nsMono_injective` this makes the indexing a bijection onto `nsSmallSets n`,
which is exactly what the regrouping of `sum_smallSets_collapse` needs. -/
theorem exists_nsMono {A : Finset (Fin n)} (hA : A ∈ nsSmallSets n) :
    ∃ s : Fin (nsMonomialCount n), nsMono n s = A :=
  ⟨(nsSmallSets n).equivFin ⟨A, hA⟩, by
    simp only [nsMono, Equiv.symm_apply_apply]⟩

/-! ### The regrouping -/

/-- **The regrouping step.**  Summing over the low-degree monomials of the
grouped remainder reproduces the mode-`lab` part of the expansion: each `w`
with `nsMode w = lab` is picked up by exactly one index `s`, namely the one
naming its selected block.  This is the only place the `Fin r`-indexing of
`SliceRankLE` meets the `Finset`-indexed monomials, and it is mode-agnostic —
`D` is the singled-out one-variable monomial, `G` everything else. -/
theorem sum_smallSets_collapse (lab : Fin 4)
    (hsmall : ∀ w : Fin n → Fin 4, nsMode w = lab → nsPre lab w ∈ nsSmallSets n)
    (D : Finset (Fin n) → ℚ) (G : (Fin n → Fin 4) → ℚ) :
    (∑ s : Fin (nsMonomialCount n),
        D (nsMono n s) * ∑ w : Fin n → Fin 4,
          if nsMode w = lab ∧ nsPre lab w = nsMono n s then G w else 0)
      = ∑ w : Fin n → Fin 4, if nsMode w = lab then D (nsPre lab w) * G w else 0 := by
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hm : nsMode w = lab
  · -- exactly one index names the selected block
    rw [if_pos hm]
    obtain ⟨s₀, hs₀⟩ := exists_nsMono (hsmall w hm)
    rw [Finset.sum_eq_single s₀ ?_ ?_]
    · rw [if_pos ⟨hm, hs₀.symm⟩, hs₀]
    · intro s _ hne
      refine if_neg fun hc => hne ?_
      exact (nsMono_injective (hs₀.trans hc.2)).symm
    · intro hnm
      exact absurd (Finset.mem_univ s₀) hnm
  · -- no index contributes
    rw [if_neg hm]
    exact Finset.sum_eq_zero fun s _ => if_neg fun hc => hm hc.1

end Decomposition


/-- **The Naslund–Sawin decomposition bound** (References/arXiv-1606-09575,
Theorem 1, the display after line 286).  Expanding
`∏_c (2 − x_c − y_c − z_c)` gives a linear combination of products of three
multilinear monomials of joint degree at most `n`; in each term at least one
of the three blocks has degree at most `n/3`, and grouping the terms by that
block exhibits the tensor as a sum of at most `3 · nsMonomialCount n`
slices. -/
theorem sliceRank_nsTensor_le {m : ℕ} (v : Fin m → Fin n → ZMod 2) :
    sliceRank (nsTensor v) ≤ 3 * nsMonomialCount n := by
  refine sliceRank_le_of_sliceRankLE ?_
  -- the block selected by `nsMode` is always one of the indexed low-degree monomials
  have hsm : ∀ (lab : Fin 4) (w : Fin n → Fin 4),
      nsMode w = lab → nsPre lab w ∈ nsSmallSets n := by
    intro lab w h
    rw [← h]
    exact nsPre_nsMode_mem_smallSets w
  refine sliceRankLE_of_parts (r₁ := nsMonomialCount n) (r₂ := nsMonomialCount n)
      (r₃ := nsMonomialCount n) (by omega)
      (fun s i => nsMon (nsBits v i) (nsMono n s))
      (fun s j l => ∑ w : Fin n → Fin 4,
        if nsMode w = 1 ∧ nsPre 1 w = nsMono n s then
          2 ^ (nsPre 0 w).card *
            (nsMon (nsBits v j) (nsPre 2 w) * nsMon (nsBits v l) (nsPre 3 w)) else 0)
      (fun s j => nsMon (nsBits v j) (nsMono n s))
      (fun s i l => ∑ w : Fin n → Fin 4,
        if nsMode w = 2 ∧ nsPre 2 w = nsMono n s then
          2 ^ (nsPre 0 w).card *
            (nsMon (nsBits v i) (nsPre 1 w) * nsMon (nsBits v l) (nsPre 3 w)) else 0)
      (fun s l => nsMon (nsBits v l) (nsMono n s))
      (fun s i j => ∑ w : Fin n → Fin 4,
        if nsMode w = 3 ∧ nsPre 3 w = nsMono n s then
          2 ^ (nsPre 0 w).card *
            (nsMon (nsBits v i) (nsPre 1 w) * nsMon (nsBits v j) (nsPre 2 w)) else 0)
      ?_
  intro i j l
  rw [sum_smallSets_collapse 1 (hsm 1), sum_smallSets_collapse 2 (hsm 2),
    sum_smallSets_collapse 3 (hsm 3), nsTensor_eq_nsProd, nsProd_eq_sum_nsTerm,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [nsTerm_factor]
  rcases nsMode_cases w with h | h | h <;> simp only [h, Fin.reduceEq, reduceIte] <;> ring

/-! ## 5. Assembly -/

/-- **Naslund–Sawin, layer form.**  A `SunflowerFree` family of `F_2^n`
vectors has at most `3 · nsMonomialCount n` members. -/
theorem card_le_of_sunflowerFree {S : Finset (Fin n → ZMod 2)} (hS : SunflowerFree S) :
    S.card ≤ 3 * nsMonomialCount n := by
  -- enumerate `S` as an injective tuple, exactly as `Capset.lean` does for cap sets
  set v : Fin S.card → Fin n → ZMod 2 := fun i => (S.equivFin.symm i : Fin n → ZMod 2)
    with hvdef
  have hinj : Function.Injective v := fun i j hij =>
    S.equivFin.symm.injective (Subtype.ext hij)
  have himg : Finset.image v Finset.univ = S := by
    ext a
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (S.equivFin.symm i).2
    · intro ha
      exact ⟨S.equivFin ⟨a, ha⟩, by simp only [hvdef, Equiv.symm_apply_apply]⟩
  have hfree : SunflowerFree (Finset.image v Finset.univ) := by rw [himg]; exact hS
  calc S.card = sliceRank (nsTensor v) := (sliceRank_nsTensor hinj hfree).symm
    _ ≤ 3 * nsMonomialCount n := sliceRank_nsTensor_le v

/-- The `0/1` vector of a finset, inverse to `vecSupport`. -/
def vecOf (A : Finset (Fin n)) : Fin n → ZMod 2 := fun i => if i ∈ A then 1 else 0

/-- `vecOf` is a section of `vecSupport`. -/
@[simp] theorem vecSupport_vecOf (A : Finset (Fin n)) : vecSupport (vecOf A) = A := by
  ext i
  simp [vecSupport, vecOf]

/-- `vecOf` is injective, so passing a set family through it preserves
cardinality — the step that transfers the `F_2^n` bound back to set families. -/
theorem vecOf_injective : Function.Injective (vecOf (n := n)) := by
  intro A B h
  rw [← vecSupport_vecOf A, ← vecSupport_vecOf B, h]

/-- **Naslund–Sawin, single layer of a set family.** -/
theorem erdos857Free_layer_card_le {F : Finset (Finset (Fin n))} {l : ℕ}
    (hF : Erdos857Free F) (hlayer : ∀ A ∈ F, A.card = l) :
    F.card ≤ 3 * nsMonomialCount n := by
  set S : Finset (Fin n → ZMod 2) := F.image vecOf with hSdef
  have hSF : S.image vecSupport = F := by
    rw [hSdef, Finset.image_image]
    exact Finset.image_congr (fun A _ => vecSupport_vecOf A) |>.trans Finset.image_id
  have hlayer' : ∀ x ∈ S, (vecSupport x).card = l := by
    intro x hx
    exact hlayer _ (hSF ▸ Finset.mem_image_of_mem vecSupport hx)
  have hfree' : Erdos857Free (S.image vecSupport) := hSF ▸ hF
  have hcard : S.card = F.card := Finset.card_image_of_injective F vecOf_injective
  calc F.card = S.card := hcard.symm
    _ ≤ 3 * nsMonomialCount n := card_le_of_sunflowerFree (erdos857Free_layer hlayer' hfree')

/-- #857-sunflower-freeness passes to subfamilies: every triple of distinct
members of a subfamily is a triple of distinct members of the parent. -/
theorem Erdos857Free.subset {F G : Finset (Finset (Fin n))} (hF : Erdos857Free F)
    (h : G ⊆ F) : Erdos857Free G :=
  fun A hA B hB C hC => hF A (h hA) B (h hB) C (h hC)

/-- **Naslund–Sawin Theorem 1, finite form.**  Any #857-sunflower-free family
of subsets of `Fin n` has at most `(n+1) · 3 · nsMonomialCount n` members.

This is one upper bound, not a solution: Erdős #857 asks for the order of
`m(n,k)` and is open.  See the module header for what has since superseded
this bound. -/
theorem erdos857Free_card_le {F : Finset (Finset (Fin n))} (hF : Erdos857Free F) :
    F.card ≤ (n + 1) * (3 * nsMonomialCount n) := by
  -- split `F` into its `n+1` cardinality layers; each is an antichain, hence `SunflowerFree`
  have hmaps : ∀ A ∈ F, A.card ∈ Finset.range (n + 1) := by
    intro A _
    rw [Finset.mem_range, Nat.lt_succ_iff]
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ A
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc ∑ l ∈ Finset.range (n + 1), (F.filter fun A => A.card = l).card
      ≤ ∑ _l ∈ Finset.range (n + 1), 3 * nsMonomialCount n := by
        refine Finset.sum_le_sum fun l _ => ?_
        exact erdos857Free_layer_card_le (l := l) (hF.subset (Finset.filter_subset _ _))
          fun A hA => (Finset.mem_filter.mp hA).2
    _ = (n + 1) * (3 * nsMonomialCount n) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-! ## 6. `m(n,3)` in the upstream spelling -/

/-- `m(n,k)` of Erdős #857: the least `t` such that every family of at least
`t` subsets of `Fin n` contains a `k`-sunflower.  This is the `Finset`
transcription of upstream `Erdos857.m` (FormalConjectures/ErdosProblems/857.lean),
whose `sInf` is guarded by `erdos857M_defining_set_nonempty` below. -/
noncomputable def erdos857M (n : ℕ) : ℕ :=
  sInf {t : ℕ | ∀ F : Finset (Finset (Fin n)), t ≤ F.card → ¬ Erdos857Free F}

/-- The `sInf` guard: the defining set is nonempty, so `erdos857M` is not the
junk value `0`.  Witness: `2 ^ n + 1` exceeds every family's cardinality. -/
theorem erdos857M_defining_set_nonempty (n : ℕ) :
    {t : ℕ | ∀ F : Finset (Finset (Fin n)), t ≤ F.card → ¬ Erdos857Free F}.Nonempty := by
  refine ⟨2 ^ n + 1, ?_⟩
  intro F hF _
  have hle : F.card ≤ 2 ^ n := by
    calc F.card ≤ (Finset.univ : Finset (Finset (Fin n))).card := Finset.card_le_univ F
      _ = 2 ^ n := by
          simp only [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
  omega

/-- **The bound on `m(n,3)`** — Naslund–Sawin Theorem 1 in the normalization
of Erdős #857.  Unwinding `nsMonomialCount`, this is
`m(n,3) ≤ 3(n+1) Σ_{k ≤ n/3} C(n,k) + 1`, whose growth rate is the
`(3/2^{2/3})^{(1+o(1))n} = 1.8899…^n` quoted on the problem page. -/
theorem erdos857M_le (n : ℕ) : erdos857M n ≤ (n + 1) * (3 * nsMonomialCount n) + 1 := by
  refine Nat.sInf_le ?_
  intro F hF hfree
  have hbound := erdos857Free_card_le hfree
  omega

/-! ### Ground checks pinning the normalization

`m(1,3) = 3`: the two subsets of `{1}` contain no 3-sunflower for want of
three distinct sets, so three sets are needed to force one.  Equivalently the
largest sunflower-free family has size 2 — the value independently computed
here by exhaustive ILP and reported as `M(1,3) = 2` by the Lean development
github.com/SproutSeeds/sunflower-lean.  This check is what distinguishes the
"minimal forcing size" normalization of `erdos857M` from the "maximum
sunflower-free family" normalization; they differ by exactly one.

`n = 1` alone would be a weak pin, because it is the *only* `n` at which
`Erdos857Free` holds vacuously — there are no three distinct subsets of
`Fin 1` to violate it.  `erdos857M_two` therefore re-pins the normalization at
the first `n` where the sunflower condition has content. -/
theorem erdos857M_one : erdos857M 1 = 3 := by
  refine le_antisymm ?_ ?_
  · -- no family of three distinct subsets of `Fin 1` exists at all
    refine Nat.sInf_le ?_
    intro F hF _
    have hle : F.card ≤ 2 := by
      calc F.card ≤ (Finset.univ : Finset (Finset (Fin 1))).card := Finset.card_le_univ F
        _ = 2 := by
            simp only [Finset.card_univ, Fintype.card_finset, Fintype.card_fin, pow_one]
    omega
  · -- `{∅, {0}}` is a sunflower-free family of size 2, so 2 does not force
    refine le_csInf (erdos857M_defining_set_nonempty 1) fun t ht => ?_
    by_contra hlt
    exact ht ({∅, {0}} : Finset (Finset (Fin 1))) (by rw [show (({∅, {0}} :
      Finset (Finset (Fin 1)))).card = 2 from by decide]; omega) (by decide)

/-- `m(2,3) = 4` — the first *nondegenerate* pin on the normalization.  Here
`Erdos857Free` has real content, unlike at `n = 1`: among the four subsets of
`{1,2}` the triple `{∅, {0}, {1}}` **is** a 3-sunflower, all three pairwise
intersections being `∅`, so the full power set is not free; whereas
`{∅, {0}, {0,1}}` **is** free, its three pairwise intersections being `∅`, `∅`
and `{0}`.  So the largest sunflower-free family has size 3 — the `max |F| = 3`
of the header table — and four sets are needed to force a sunflower. -/
theorem erdos857M_two : erdos857M 2 = 4 := by
  refine le_antisymm ?_ ?_
  · -- every family of four subsets of `Fin 2` is the whole power set, which
    -- contains the 3-sunflower `{∅, {0}, {1}}`; only 2 ^ 4 = 16 families to scan
    refine Nat.sInf_le ?_
    show ∀ F : Finset (Finset (Fin 2)), 4 ≤ F.card → ¬ Erdos857Free F
    decide
  · -- `{∅, {0}, {0,1}}` is sunflower-free of size 3, so 3 does not force
    refine le_csInf (erdos857M_defining_set_nonempty 2) fun t ht => ?_
    by_contra hlt
    have hcard : ({∅, {0}, {0, 1}} : Finset (Finset (Fin 2))).card = 3 := by decide
    have hfree : Erdos857Free ({∅, {0}, {0, 1}} : Finset (Finset (Fin 2))) := by decide
    exact ht ({∅, {0}, {0, 1}} : Finset (Finset (Fin 2))) (by omega) hfree

/-! ### Joint satisfiability of the hypotheses (STYLE: no vacuous theorems) -/

/-- Joint witness for `erdos857Free_layer_card_le`: the layer `{{0}, {1}}` of
`Fin 2` is #857-sunflower-free and uniform of size 1, and the bound it lands
is `2 ≤ 3 * nsMonomialCount 2 = 3`. -/
example : Erdos857Free ({{0}, {1}} : Finset (Finset (Fin 2))) ∧
    (∀ A ∈ ({{0}, {1}} : Finset (Finset (Fin 2))), A.card = 1) ∧
    ({{0}, {1}} : Finset (Finset (Fin 2))).card ≤ 3 * nsMonomialCount 2 := by
  refine ⟨by decide, by decide, ?_⟩
  exact erdos857Free_layer_card_le (l := 1) (by decide) (by decide)

/-- Joint witness for `card_le_of_sunflowerFree`: the size-3 antichain of
doubletons in `F_2^3` is `SunflowerFree`, and the theorem bounds it by
`3 * nsMonomialCount 3 = 12`. -/
example : SunflowerFree ({![1, 1, 0], ![1, 0, 1], ![0, 1, 1]} : Finset (Fin 3 → ZMod 2)) ∧
    ({![1, 1, 0], ![1, 0, 1], ![0, 1, 1]} : Finset (Fin 3 → ZMod 2)).card
      ≤ 3 * nsMonomialCount 3 :=
  ⟨by decide, card_le_of_sunflowerFree (by decide)⟩

end Erdos857
