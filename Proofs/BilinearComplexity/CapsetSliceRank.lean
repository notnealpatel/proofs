/-
  BilinearComplexity/CapsetSliceRank — the A236397 Peebles sunflower-free
  weight functional, its bridge to the cap-set numbers of Capset.lean, and
  the cap-set ↔ slice-rank bridge toward Croot–Lev–Pach / Ellenberg–Gijswijt.

  GROUND TRUTH PINNING (fetched live 2026-07-30).

  OEIS A236397 (offset 0): "Weight of the largest-weight sunflower-free set
  of width n." Terms: 1, 2, 4, 8, 20, 40, 96, 224. Comment: "Peebles
  conjectures that if n is even, a(n+1) = 2*A090245(n)." Sole link:
  J. Peebles, "Cap Set Bounds and Matrix Multiplication", Senior Thesis,
  Harvey Mudd College, 2013 (poster; archived copy in References/Peebles2013/,
  fetched from the entry's web.archive.org link).

  The weight/width convention, verbatim from the poster (the OEIS entry name
  alone does not define it):

    Definition 3. "A sunflower free set of width n is a subset S of F_2^n
    such that for any x, y, z ∈ S (not all equal), there exists an i such
    that exactly two of x_i, y_i, z_i are equal to 1."

    Definition 4. "Define the weight of a vector in F_2^n as 2^k where k is
    the number of 0's in it. Let the weight of a subset of F_2^n be the sum
    of the weights of its elements. Let c_n denote the weight of the
    largest-weight sunflower free set of width n."

  Note the "not all equal" quantification: it also constrains triples with a
  repeated element, so x, x, z with x ≠ z demands a coordinate where exactly
  two of x, x, z are 1, i.e. x_i = 1 ∧ z_i = 0 — a sunflower-free family is
  in particular an antichain of supports. This is load-bearing for the terms
  (c_1 = 2 comes from {0}, since {0, 1} fails on the triple (0, 0, 1)); the
  discriminating examples below pin it. The convention was verified by brute
  force against the pinned terms: max weight = 1, 2, 4, 8, 20 for n = 0..4.

  OEIS A090245 (offset 0): 1, 2, 4, 9, 20, 45, 112 — capsetNumber of
  Capset.lean. Peebles' Conjecture 5 on known terms: n = 0: 2 = 2·1,
  n = 2: 8 = 2·4, n = 4: 40 = 2·20, n = 6: 224 = 2·112 — all match. The
  evenness hypothesis is load-bearing: the identity happens to hold at the
  odd n = 1 (4 = 2·2, kernel-checked below) but fails at n = 3
  (A236397(4) = 20 ≠ 18 = 2·A090245(3)) and n = 5 (96 ≠ 90).

  CLP/EG PINNING (papers fetched; verified 2026-08-05). From
  References/GroupTPP/arXiv-1605-09223 (Ellenberg–Gijswijt, "On large
  subsets of F_q^n with no three-term arithmetic progression"), verbatim:
  Proposition \label{pr:clp}: "Suppose P ∈ S_n^d satisfies
  P(\alpha a+\beta b) = 0 for every pair a,b of distinct elements of A.
  Then the number of a ∈ A for which P(-\gamma a) \neq 0 is at most
  2 m_{d/2}."; Theorem \label{th:main}: "Then |A| \leq 3m_{(q-1)n/3}.";
  Corollary: "Let A be a subset of (\Z/3\Z)^n containing no three-term
  arithmetic progression.  Then |A| = o(2.756^n)."  Proof-structure model
  (per lane brief): lean-forward/cap_set_problem, the Dahmen–Hölzl–Lewis
  ITP 2019 formalization (paper in
  References/BilinearComplexity/arXiv-1907-01449; Lean 3.4.2), chain
  `theorem_12_1` ("A.card ≤ 3*(m (1/3*((q-1)*n)))") → `theorem_13_14` →
  `cap_set_problem`. DHL follow the EG asymmetric vanishing-space
  argument; § 5 here instead follows Tao's symmetric slice-rank
  formulation ("A symmetric formulation of the
  Croot–Lev–Pach–Ellenberg–Gijswijt capset bound", terrytao.wordpress.com,
  May 2016), the form the § 4 schema and Tao's diagonal lemma consume:
  over F_3 the line indicator factors as ∏_t (1 − (x_t+y_t+z_t)²), a
  polynomial of total degree ≤ 2n in whose monomials x^a y^b z^c some
  mode has degree ≤ 2n/3; grouping by that mode gives ≤ 3·m_{2n/3}
  slices.

  CONTENTS.

    § 1 Peebles weight functional: `ExactlyTwoOnes`, `SunflowerFree`,
        `vecWeight`, `setWeight`, `sunflowerFreeWeight` (= A236397), order
        API, and kernel ground values 1, 2, 4, 8 at n = 0, 1, 2, 3.
    § 2 Poster Theorem 4, sorry-free: `sunflowerFreeWeight_le_capsetNumber`
        (A236397(n) ≤ A090245(n)) via the block construction `capBlock`
        sending x ∈ F_2^n to its 2^{#zeros} lift block in F_3^n.
    § 3 ARCHIVED (intended `sorry`): `peebles_conjecture` — for even n,
        A236397(n+1) = 2·A090245(n). Open; source: the pinned OEIS comment.
    § 4 Cap-set ↔ slice-rank bridge, sorry-free: `lineTensor` (the line
        indicator tensor of a tuple of points of F_3^n),
        `lineTensor_eq_diag_one_iff` (diagonal collapse ⟺ injective cap
        tuple), `sliceRank_lineTensor` (via Tao's diagonal lemma, its slice
        rank is the number of points), and the method schema
        `capsetNumber_le_of_forall_sliceRank_lineTensor_le` (any uniform
        slice-rank bound on cap tuples bounds the cap-set numbers).
    § 5 Croot–Lev–Pach / Ellenberg–Gijswijt, sorry-free (since
        2026-08-05; previously the archived second sorry): `clpCoeff` (the
        coefficient table of 1 − (x+y+z)² over F_3, kernel-decided
        expansion `clpCoeff_expand` and degree bound
        `clpCoeff_ne_zero_deg`), `lineTensor_apply_expand` (the line
        tensor of ANY tuple as a sum of monomials),
        `sliceRankLE_of_expansion` (Tao's partition step: a
        low-degree-per-mode monomial expansion is a slice decomposition),
        `sliceRankLE_lineTensor_clp` (the CLP bound, unconditioned — no
        injectivity or 3AP-freeness needed),
        `croot_lev_pach_sliceRank_lineTensor` (the pinned conditional
        form the § 4 schema consumes), and `ellenberg_gijswijt`
        (capsetNumber n ≤ 3·clpMonomialCount n, the o(2.756^n) bound's
        exact finite form), now machine-checked end to end.
    § 6 Bridge to the project's Erdős–Rado sunflower layer
        (Erdos/Erdos20/Sunflower.lean, first cross-library import —
        justified here as the name-grounding bridge; that file is
        self-contained shift-theory infrastructure): a Peebles sunflower is
        exactly a Δ-system of supports (`forall_not_exactlyTwoOnes_iff`),
        and a `SunflowerFree` family has no classical 3-sunflower among its
        supports (`not_hasSunflower_image_vecSupport`). The containment is
        one-way, and the gap is not confined to degenerate data (a chain
        family separates the two notions — see the § 6 discriminator), so
        the defs are bridged, not shared.

        RETRACTION (2026-07-31). § 6 is NOT an anchor to Erdős problem #857
        (the weak sunflower problem), and must not be cited as one. #857 and
        upstream formal-conjectures both spell the sunflower as
        `∃ K, F.Pairwise (fun A B => A ∩ B = K)` — distinct pairs, existential
        kernel, and NO petal condition — whereas `IsSunflowerWith` of
        Erdos/Erdos20/Sunflower.lean additionally demands `S \ K ≠ ∅`. So
        `HasSunflower _ 3` is STRICTLY STRONGER than the #857 notion and
        `¬ HasSunflower _ 3` strictly weaker than #857-sunflower-freeness:
        `{{0}, {0,1}, {0,2}}` is a #857 3-sunflower carrying no
        `HasSunflower … 3`, machine-checked as
        `Erdos857.erdos857_petal_mismatch` in Erdos/Erdos857/NaslundSawin.lean.
        The extra clause is harmless for #20 itself (a uniform family cannot
        have an empty petal), so nothing in this file or in Erdos20 is wrong —
        only the #857 reading of § 6 would be. The correct #857 anchor, and
        the Naslund–Sawin bound on m(n,3), live in that file.

  Intended sorries (1, disclosed in its docstring): `peebles_conjecture`.
  Everything else — `croot_lev_pach_sliceRank_lineTensor` and
  `ellenberg_gijswijt` included since 2026-08-05 — no sorry, axioms ⊆
  {propext, Classical.choice, Quot.sound} (see the closing audit block).

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Module.Pi
import BilinearComplexity.Capset
import BilinearComplexity.SliceRank
import Erdos.Erdos20.Sunflower

set_option autoImplicit false

namespace BilinearComplexity

/-! ## 1. The Peebles sunflower-free weight functional (OEIS A236397) -/

section PeeblesWeight

/-- Poster Definition 3, pointwise core: exactly two of `a`, `b`, `c` are `1`
(in `ZMod 2`, spelled as the three explicit patterns). -/
def ExactlyTwoOnes (a b c : ZMod 2) : Prop :=
  (a = 1 ∧ b = 1 ∧ c = 0) ∨ (a = 1 ∧ b = 0 ∧ c = 1) ∨ (a = 0 ∧ b = 1 ∧ c = 1)

/-- `ExactlyTwoOnes` is decidable (finite case split on `ZMod 2` values). -/
instance (a b c : ZMod 2) : Decidable (ExactlyTwoOnes a b c) := by
  unfold ExactlyTwoOnes; infer_instance

/-- Poster Definition 3: `S ⊆ F_2^n` is sunflower free iff every triple of
its elements that is *not all equal* has a coordinate where exactly two of
the three entries are `1`. The "not all equal" form also constrains triples
with one repeated element — see the discriminating examples below. -/
def SunflowerFree {n : ℕ} (S : Finset (Fin n → ZMod 2)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, ¬(x = y ∧ y = z) → ∃ i, ExactlyTwoOnes (x i) (y i) (z i)

/-- `SunflowerFree` is decidable (bounded quantification over `S³` and `Fin n`). -/
instance {n : ℕ} (S : Finset (Fin n → ZMod 2)) : Decidable (SunflowerFree S) := by
  unfold SunflowerFree; infer_instance

/-- Poster Definition 4, vector part: the weight of `x ∈ F_2^n` is `2^k`
where `k` is the number of `0`'s in `x`. -/
def vecWeight {n : ℕ} (x : Fin n → ZMod 2) : ℕ :=
  2 ^ (Finset.univ.filter fun i => x i = 0).card

/-- Poster Definition 4, set part: the weight of `S ⊆ F_2^n` is the sum of
the weights of its elements. -/
def setWeight {n : ℕ} (S : Finset (Fin n → ZMod 2)) : ℕ :=
  ∑ x ∈ S, vecWeight x

/-- OEIS A236397: the weight of the largest-weight sunflower-free set of
width `n` (poster Definition 4), as a `Finset.sup` over all sunflower-free
subsets of `F_2^n`. Terms: 1, 2, 4, 8, 20, 40, 96, 224. -/
def sunflowerFreeWeight (n : ℕ) : ℕ :=
  (Finset.univ.filter fun S : Finset (Fin n → ZMod 2) => SunflowerFree S).sup setWeight

/-! Ground checks for the § 1 defs. -/

example : ExactlyTwoOnes 1 1 0 ∧ ExactlyTwoOnes 1 0 1 ∧ ExactlyTwoOnes 0 1 1 := by decide
example : ¬ ExactlyTwoOnes 1 1 1 ∧ ¬ ExactlyTwoOnes 1 0 0 ∧ ¬ ExactlyTwoOnes 0 0 0 := by decide

example : vecWeight (![0, 1, 0] : Fin 3 → ZMod 2) = 4 := by decide
example : vecWeight (![1, 1] : Fin 2 → ZMod 2) = 1 := by decide
example : setWeight ({![0], ![1]} : Finset (Fin 1 → ZMod 2)) = 3 := by decide

/-- The attaining family for c_2 = 4: the antichain `{01, 10}`. -/
example : SunflowerFree ({![0, 1], ![1, 0]} : Finset (Fin 2 → ZMod 2)) ∧
    setWeight ({![0, 1], ![1, 0]} : Finset (Fin 2 → ZMod 2)) = 4 := by decide

/-- DISCRIMINATOR for the "not all equal" convention: `{0, 1} ⊆ F_2^1` is NOT
sunflower free, because the repeated-element triple `(0, 0, 1)` has no
coordinate with exactly two `1`s. Under a "pairwise distinct" reading it
would be sunflower free (no 3 distinct elements exist) with weight 3 > 2,
contradicting the pinned c_1 = 2. -/
example : ¬ SunflowerFree ({![0], ![1]} : Finset (Fin 1 → ZMod 2)) := by decide

/-- Discriminator, positive side: a genuinely 3-element sunflower-free
family (the size-3 antichain of doubletons in `F_2^3`). -/
example : SunflowerFree ({![1, 1, 0], ![1, 0, 1], ![0, 1, 1]} : Finset (Fin 3 → ZMod 2)) := by
  decide

/-- Discriminator, negative side: three pairwise disjoint supports form a
classical (empty-core) sunflower, and Peebles' condition indeed rejects
them: no coordinate of `(100, 010, 001)` has exactly two `1`s. -/
example : ¬ SunflowerFree ({![1, 0, 0], ![0, 1, 0], ![0, 0, 1]} : Finset (Fin 3 → ZMod 2)) := by
  decide

/-- The empty family is sunflower free (so the defining `sup` ranges over a
nonempty family of sets and is attained). -/
theorem sunflowerFree_empty {n : ℕ} : SunflowerFree (∅ : Finset (Fin n → ZMod 2)) :=
  fun x hx => absurd hx (Finset.notMem_empty x)

/-- Singletons are sunflower free: every triple from `{x}` is all-equal. -/
theorem sunflowerFree_singleton {n : ℕ} (x : Fin n → ZMod 2) :
    SunflowerFree ({x} : Finset (Fin n → ZMod 2)) := by
  intro a ha b hb c hc h
  rw [Finset.mem_singleton] at ha hb hc
  exact absurd ⟨ha.trans hb.symm, hb.trans hc.symm⟩ h

/-- Order API: every sunflower-free family's weight is at most A236397(n). -/
theorem setWeight_le_sunflowerFreeWeight {n : ℕ} {S : Finset (Fin n → ZMod 2)}
    (hS : SunflowerFree S) : setWeight S ≤ sunflowerFreeWeight n :=
  Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS⟩)

/-- Order API: A236397(n) is attained by some sunflower-free family. -/
theorem exists_sunflowerFree_setWeight_eq (n : ℕ) :
    ∃ S : Finset (Fin n → ZMod 2), SunflowerFree S ∧ setWeight S = sunflowerFreeWeight n := by
  obtain ⟨S, hmem, hval⟩ :=
    (Finset.univ.filter fun S : Finset (Fin n → ZMod 2) => SunflowerFree S).exists_mem_eq_sup
      ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ ∅, sunflowerFree_empty⟩⟩ setWeight
  exact ⟨S, (Finset.mem_filter.mp hmem).2, hval.symm⟩

/-! Ground values, checked against the pinned A236397 terms 1, 2, 4, 8. -/

/-- A236397(0) = 1: `F_2^0` is a point of weight `2^0 = 1`. -/
theorem sunflowerFreeWeight_zero : sunflowerFreeWeight 0 = 1 := by decide

/-- A236397(1) = 2: the singleton `{0}` (weight 2) wins; `{0, 1}` is not
sunflower free (see the discriminator example above). -/
theorem sunflowerFreeWeight_one : sunflowerFreeWeight 1 = 2 := by decide

/-- A236397(2) = 4: exhaustive kernel decision over all 16 subsets. -/
theorem sunflowerFreeWeight_two : sunflowerFreeWeight 2 = 4 := by decide

set_option maxRecDepth 16000 in
/-- A236397(3) = 8: exhaustive kernel decision over all 256 subsets of
`F_2^3` (attained by the singleton `{000}` of weight `2^3 = 8`).
A236397(4) = 20 is beyond cheap kernel search (65536 subsets with up to
`16^3` triples each) and is recorded as pinned evidence only.

This check is load-bearing for definition fidelity: `n = 3` is the first
index separating the pinned convention from the "exactly two zeros" and
"weight `2^#ones`" misreadings — do not drop it for build cost. -/
theorem sunflowerFreeWeight_three : sunflowerFreeWeight 3 = 8 := by decide

end PeeblesWeight

/-! ## 2. Poster Theorem 4: A236397(n) ≤ A090245(n) -/

section BlockConstruction

variable {n : ℕ}

/-- The lift block of `x ∈ F_2^n`: all `y ∈ F_3^n` with `y i = 1` where
`x i = 1` and `y i ∈ {0, 2}` where `x i = 0`. It has `vecWeight x = 2^{#zeros}`
elements, and blocks of distinct vectors are disjoint; the union of the
blocks of a sunflower-free family is a cap set (the ASU-style correspondence
behind poster Theorem 4). -/
def capBlock (x : Fin n → ZMod 2) : Finset (Fin n → ZMod 3) :=
  Fintype.piFinset fun i => if x i = 1 then ({1} : Finset (ZMod 3)) else {0, 2}

/-- `ZMod 2` is two-valued: not-`1` is `0`. Kernel-decided. -/
private theorem zmod2_ne_one_iff : ∀ a : ZMod 2, a ≠ 1 ↔ a = 0 := by decide

/-- The zero-sum kill at an exactly-two-ones coordinate: in `ZMod 3`, two
`1`s and a non-`1` (in any of the three positions) never sum to `0`
(`1 + 1 + 0 = 2`, `1 + 1 + 2 = 1`). Kernel-decided. -/
private theorem zmod3_sum_ne_zero_of_two_ones :
    ∀ u v w : ZMod 3, ((u = 1 ∧ v = 1 ∧ w ≠ 1) ∨ (u = 1 ∧ v ≠ 1 ∧ w = 1) ∨
      (u ≠ 1 ∧ v = 1 ∧ w = 1)) → u + v + w ≠ 0 := by decide

/-- Zero-sum triples from `{0, 2} ⊆ ZMod 3` are constant (`0+0+0` and
`2+2+2` are the only zero sums). Kernel-decided. -/
private theorem zmod3_eq_of_sum_eq_zero_of_ne_one :
    ∀ u v w : ZMod 3, u ≠ 1 → v ≠ 1 → w ≠ 1 → u + v + w = 0 → u = v := by decide

/-- Ground check: the block of `10 ∈ F_2^2` is `{10, 12} ⊆ F_3^2`. -/
example : capBlock (![1, 0] : Fin 2 → ZMod 2) =
    ({![1, 0], ![1, 2]} : Finset (Fin 2 → ZMod 3)) := by decide

/-- On one-coordinates of the owner, block members are `1`. -/
theorem capBlock_apply_eq_one {x : Fin n → ZMod 2} {y : Fin n → ZMod 3}
    (hy : y ∈ capBlock x) {i : Fin n} (hi : x i = 1) : y i = 1 := by
  have h := Fintype.mem_piFinset.mp hy i
  rw [if_pos hi] at h
  exact Finset.mem_singleton.mp h

/-- On zero-coordinates of the owner, block members avoid `1`. -/
theorem capBlock_apply_ne_one {x : Fin n → ZMod 2} {y : Fin n → ZMod 3}
    (hy : y ∈ capBlock x) {i : Fin n} (hi : x i ≠ 1) : y i ≠ 1 := by
  have h := Fintype.mem_piFinset.mp hy i
  rw [if_neg hi] at h
  intro h1
  rw [h1] at h
  exact absurd h (by decide)

/-- A block member determines its owner: blocks of distinct vectors are
disjoint. -/
theorem capBlock_owner_unique {x x' : Fin n → ZMod 2} {y : Fin n → ZMod 3}
    (hy : y ∈ capBlock x) (hy' : y ∈ capBlock x') : x = x' := by
  funext i
  by_cases hxi : x i = 1 <;> by_cases hxi' : x' i = 1
  · rw [hxi, hxi']
  · exact absurd (capBlock_apply_eq_one hy hxi) (capBlock_apply_ne_one hy' hxi')
  · exact absurd (capBlock_apply_eq_one hy' hxi') (capBlock_apply_ne_one hy hxi)
  · rw [(zmod2_ne_one_iff (x i)).mp hxi, (zmod2_ne_one_iff (x' i)).mp hxi']

/-- The block of `x` has exactly `vecWeight x = 2^{#zeros(x)}` elements. -/
theorem card_capBlock (x : Fin n → ZMod 2) : (capBlock x).card = vecWeight x := by
  rw [capBlock, Fintype.card_piFinset]
  have hcard : ∀ i ∈ Finset.univ,
      ((if x i = 1 then ({1} : Finset (ZMod 3)) else {0, 2}).card : ℕ)
        = if x i = 1 then 1 else 2 := by
    intro i _
    by_cases hxi : x i = 1
    · rw [if_pos hxi, if_pos hxi]
      rfl
    · rw [if_neg hxi, if_neg hxi]
      rfl
  have hfilt : (Finset.univ.filter fun i => ¬ x i = 1) = Finset.univ.filter fun i => x i = 0 :=
    Finset.filter_congr fun i _ => zmod2_ne_one_iff (x i)
  rw [Finset.prod_congr rfl hcard, Finset.prod_ite (fun _ => (1 : ℕ)) fun _ => (2 : ℕ),
    Finset.prod_const_one, Finset.prod_const, one_mul, vecWeight, hfilt]

/-- The block union of a family has cardinality its Peebles weight. -/
theorem card_biUnion_capBlock (S : Finset (Fin n → ZMod 2)) :
    (S.biUnion capBlock).card = setWeight S := by
  have hdisj : (↑S : Set (Fin n → ZMod 2)).PairwiseDisjoint capBlock := by
    intro x _ x' _ hne
    exact Finset.disjoint_left.mpr fun y hy hy' => hne (capBlock_owner_unique hy hy')
  rw [Finset.card_biUnion hdisj, setWeight]
  exact Finset.sum_congr rfl fun x _ => card_capBlock x

/-- **Sunflower-free lifts to cap.** The block union of a sunflower-free
family is 3AP-free: a zero-sum triple of lifts with not-all-equal owners is
killed at a coordinate where exactly two owners are `1` (there the sum is
`1 + 1 + {0,2} ∈ {2, 1}` ≠ 0), and a zero-sum triple within one block is
forced equal coordinatewise (`{0,2}`-triples summing to 0 are constant). -/
theorem threeAPFree_biUnion_capBlock {S : Finset (Fin n → ZMod 2)}
    (hS : SunflowerFree S) :
    ThreeAPFree ((S.biUnion capBlock : Finset (Fin n → ZMod 3)) : Set (Fin n → ZMod 3)) := by
  rw [threeAPFree_iff_forall_add_add_eq_zero_imp]
  intro a ha b hb c hc habc
  obtain ⟨x, hxS, hax⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp ha)
  obtain ⟨y, hyS, hby⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hb)
  obtain ⟨z, hzS, hcz⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hc)
  have hsum : ∀ i, a i + b i + c i = 0 := fun i => by
    have h := congrFun habc i
    simpa only [Pi.add_apply, Pi.zero_apply] using h
  by_cases hall : x = y ∧ y = z
  · -- degenerate owners: all three lifts live in the block of `x`
    obtain ⟨rfl, rfl⟩ := hall
    funext i
    by_cases hxi : x i = 1
    · rw [capBlock_apply_eq_one hax hxi, capBlock_apply_eq_one hby hxi]
    · exact zmod3_eq_of_sum_eq_zero_of_ne_one (a i) (b i) (c i)
        (capBlock_apply_ne_one hax hxi) (capBlock_apply_ne_one hby hxi)
        (capBlock_apply_ne_one hcz hxi) (hsum i)
  · -- not-all-equal owners: kill the sum at an exactly-two-ones coordinate
    obtain ⟨i, hex⟩ := hS x hxS y hyS z hzS hall
    refine absurd (hsum i) (zmod3_sum_ne_zero_of_two_ones (a i) (b i) (c i) ?_)
    rcases hex with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨capBlock_apply_eq_one hax h1, capBlock_apply_eq_one hby h2,
        capBlock_apply_ne_one hcz (by rw [h3]; decide)⟩
    · exact Or.inr (Or.inl ⟨capBlock_apply_eq_one hax h1,
        capBlock_apply_ne_one hby (by rw [h2]; decide), capBlock_apply_eq_one hcz h3⟩)
    · exact Or.inr (Or.inr ⟨capBlock_apply_ne_one hax (by rw [h1]; decide),
        capBlock_apply_eq_one hby h2, capBlock_apply_eq_one hcz h3⟩)

/-- **Poster Theorem 4** (Peebles 2013): A236397(n) ≤ A090245(n) — the
largest Peebles weight is at most the cap-set number, via the block
construction. Sorry-free bridge between the two OEIS sequences. -/
theorem sunflowerFreeWeight_le_capsetNumber (n : ℕ) :
    sunflowerFreeWeight n ≤ capsetNumber n := by
  refine Finset.sup_le fun S hS => ?_
  have hfree : SunflowerFree S := (Finset.mem_filter.mp hS).2
  calc setWeight S = (S.biUnion capBlock).card := (card_biUnion_capBlock S).symm
    _ ≤ capsetNumber n := card_le_capsetNumber (threeAPFree_biUnion_capBlock hfree)

end BlockConstruction

/-! ## 3. The Peebles conjecture (ARCHIVED, intended sorry) -/

/-- **Peebles' conjecture** (OEIS A236397 comment, pinned 2026-07-30:
"Peebles conjectures that if n is even, a(n+1) = 2*A090245(n)"; poster
Conjecture 5: "For all even n, 2a_n = c_{n+1}").

OPEN. INTENDED SORRY — archived conjecture, disclosed in the module header.
Evidence: matches all pinned terms — n = 0: 2 = 2·1, n = 2: 8 = 2·4,
n = 4: 40 = 2·20, n = 6: 224 = 2·112. The n = 0 and n = 2 instances are
kernel-verified below. Evenness is load-bearing (n = 3: 20 ≠ 18, n = 5:
96 ≠ 90 on pinned terms), though the identity coincidentally holds at
n = 1 (kernel-verified below). Only 8 terms of A236397 and 7 of A090245
are known; one new term of either sequence tests the conjecture. -/
theorem peebles_conjecture (n : ℕ) (hn : Even n) :
    sunflowerFreeWeight (n + 1) = 2 * capsetNumber n := by
  sorry

/-- Kernel-verified instance of `peebles_conjecture` at n = 0 (its
hypothesis' joint witness: `Even 0`): A236397(1) = 2 = 2·A090245(0). -/
example : Even 0 ∧ sunflowerFreeWeight 1 = 2 * capsetNumber 0 := by decide

/-- Kernel-verified instance of `peebles_conjecture` at n = 2:
A236397(3) = 8 = 2·4 = 2·A090245(2). -/
example : sunflowerFreeWeight 3 = 2 * capsetNumber 2 := by
  rw [sunflowerFreeWeight_three, capsetNumber_two]

/-- The identity of `peebles_conjecture` coincidentally holds at the ODD
n = 1 — A236397(2) = 4 = 2·A090245(1) — while failing at n = 3 and n = 5 on
the pinned terms (20 ≠ 2·9, 96 ≠ 2·45; both sides beyond kernel search).
So evenness is necessary for the general claim but not for small n. -/
example : sunflowerFreeWeight 2 = 2 * capsetNumber 1 := by decide

/-! ## 4. The cap-set ↔ slice-rank bridge -/

section LineTensor

variable {k : Type*} [CommSemiring k] {n m : ℕ}

/-- The line indicator tensor of an `m`-tuple `v` of points of `F_3^n`:
`T i j l = 1` if `v i + v j + v l = 0` (the three points form a line of
`AG(n, 3)`, degenerate triples included) and `0` otherwise. For a cap tuple
it collapses to the identity diagonal tensor (`lineTensor_eq_diag_one_iff`),
which is the pivot of the Croot–Lev–Pach / Ellenberg–Gijswijt method. -/
def lineTensor (k : Type*) [CommSemiring k] {n m : ℕ}
    (v : Fin m → Fin n → ZMod 3) : Tensor k m m m :=
  fun i j l => if v i + v j + v l = 0 then 1 else 0

/-- Ground check: the line tensor of the cap tuple `(0, 1) ⊆ F_3^1` is the
`2×2×2` identity diagonal (diagonal entries `x+x+x = 0` fire, off-diagonal
sums `0+0+1, 0+1+1, …` do not). -/
example : lineTensor ℕ ![![0], ![1]] = diag (fun _ => 1) := by decide

/-- Discriminator: the full line `(0, 1, 2) ⊆ F_3^1` is not a cap, and its
line tensor is NOT diagonal (`0 + 1 + 2 = 0` fires off-diagonal). -/
example : lineTensor ℕ ![![0], ![1], ![2]] ≠ diag (fun _ => 1) := by decide

/-- Discriminator: repeated points also break diagonality (`v 0 + v 1 + v 0
= 0` fires at `(0,1,0)`), so injectivity in
`lineTensor_eq_diag_one_iff` is load-bearing. -/
example : lineTensor ℕ ![![0], ![0]] ≠ diag (fun _ => 1) := by decide

/-- Cap tuples have identity line tensors: if `v` is injective with 3AP-free
range, every zero-sum triple `v i + v j + v l = 0` is degenerate
(`i = j = l`), so the line tensor is the all-ones diagonal. -/
theorem lineTensor_eq_diag_one {v : Fin m → Fin n → ZMod 3}
    (hv : Function.Injective v) (hfree : ThreeAPFree (Set.range v)) :
    lineTensor k v = diag (fun _ => (1 : k)) := by
  funext i j l
  show (if v i + v j + v l = 0 then (1 : k) else 0) = if i = j ∧ j = l then (1 : k) else 0
  refine if_congr ?_ rfl rfl
  constructor
  · intro hsum
    have himp := threeAPFree_iff_forall_add_add_eq_zero_imp.mp hfree
    have hij : v i = v j :=
      himp (Set.mem_range_self i) (Set.mem_range_self j) (Set.mem_range_self l) hsum
    have hjl : v l = v j := by
      rw [hij] at hsum
      exact eq_of_add_self_add_eq_zero hsum
    exact ⟨hv hij, hv hjl.symm⟩
  · rintro ⟨rfl, rfl⟩
    exact add_add_self_eq_zero (v i)

/-- **Diagonal collapse characterizes cap tuples.** Over a nontrivial
semiring, the line tensor of `v` is the identity diagonal iff `v` is an
injective enumeration of a cap set (3AP-free set) of `F_3^n`. -/
theorem lineTensor_eq_diag_one_iff [Nontrivial k] {v : Fin m → Fin n → ZMod 3} :
    lineTensor k v = diag (fun _ => (1 : k)) ↔
      Function.Injective v ∧ ThreeAPFree (Set.range v) := by
  constructor
  · intro h
    -- from the tensor identity, every zero-sum triple of points is degenerate
    have key : ∀ i j l, v i + v j + v l = 0 → i = j ∧ j = l := by
      intro i j l hsum
      have hentry := congrFun (congrFun (congrFun h i) j) l
      simp only [lineTensor, diag] at hentry
      rw [if_pos hsum] at hentry
      by_contra hne
      rw [if_neg hne] at hentry
      exact one_ne_zero hentry
    constructor
    · intro i j hij
      have hsum : v i + v j + v i = 0 := by
        rw [hij]
        exact add_add_self_eq_zero (v j)
      exact (key i j i hsum).1
    · rw [threeAPFree_iff_forall_add_add_eq_zero_imp]
      rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩ c ⟨l, rfl⟩ hsum
      exact congrArg v (key i j l hsum).1
  · rintro ⟨hv, hfree⟩
    exact lineTensor_eq_diag_one hv hfree

/-- Joint satisfiability of the `sliceRank_lineTensor` hypotheses at a
concrete instance, harvested backward through the iff from the
kernel-checked tensor identity: `(0, 1) ⊆ F_3^1` is an injective cap
tuple. -/
example : Function.Injective (![![0], ![1]] : Fin 2 → Fin 1 → ZMod 3) ∧
    ThreeAPFree (Set.range (![![0], ![1]] : Fin 2 → Fin 1 → ZMod 3)) :=
  (lineTensor_eq_diag_one_iff (k := ℕ)).mp (by decide)

/-- **The slice rank of a cap tuple's line tensor is the number of points.**
Combines the diagonal collapse with Tao's diagonal lemma (`sliceRank_diag`).
This is the lower-bound half of the Croot–Lev–Pach / Ellenberg–Gijswijt
method: cap sets realize their size as a slice rank. (The upper-bound
half is § 5's `croot_lev_pach_sliceRank_lineTensor`.) -/
theorem sliceRank_lineTensor {k : Type*} [Field k] [DecidableEq k]
    {n m : ℕ} {v : Fin m → Fin n → ZMod 3}
    (hv : Function.Injective v) (hfree : ThreeAPFree (Set.range v)) :
    sliceRank (lineTensor k v) = m := by
  rw [lineTensor_eq_diag_one hv hfree, sliceRank_diag]
  simp

/-- The cap-set number is realized as a slice rank: some injective cap tuple
of length `capsetNumber n` has line tensor of slice rank exactly
`capsetNumber n` (enumerate an extremal cap set of `Capset.lean`). -/
theorem exists_sliceRank_lineTensor_eq_capsetNumber
    (k : Type*) [Field k] [DecidableEq k] (n : ℕ) :
    ∃ v : Fin (capsetNumber n) → Fin n → ZMod 3,
      Function.Injective v ∧ ThreeAPFree (Set.range v) ∧
        sliceRank (lineTensor k v) = capsetNumber n := by
  obtain ⟨A, hcard, hfree⟩ := exists_threeAPFree_card_capsetNumber n
  set v : Fin (capsetNumber n) → Fin n → ZMod 3 :=
    fun i => (A.equivFin.symm ((finCongr hcard).symm i) : Fin n → ZMod 3) with hv_def
  have hinj : Function.Injective v := fun i j hij =>
    (finCongr hcard).symm.injective (A.equivFin.symm.injective (Subtype.ext hij))
  have hrange : Set.range v = (A : Set (Fin n → ZMod 3)) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact Finset.mem_coe.mpr (A.equivFin.symm ((finCongr hcard).symm i)).2
    · intro ha
      refine ⟨finCongr hcard (A.equivFin ⟨a, Finset.mem_coe.mp ha⟩), ?_⟩
      simp only [hv_def, Equiv.symm_apply_apply]
  have hfree' : ThreeAPFree (Set.range v) := by
    rw [hrange]
    exact hfree
  exact ⟨v, hinj, hfree', sliceRank_lineTensor hinj hfree'⟩

/-- **Method schema: slice-rank bounds bound cap sets.** Any uniform upper
bound on the slice rank of line tensors of cap tuples is an upper bound on
the cap-set numbers. This is the machine-checked reduction through which
`ellenberg_gijswijt` follows from the § 5 Croot–Lev–Pach bound. -/
theorem capsetNumber_le_of_forall_sliceRank_lineTensor_le
    {k : Type*} [Field k] [DecidableEq k] {n B : ℕ}
    (h : ∀ (m : ℕ) (v : Fin m → Fin n → ZMod 3), Function.Injective v →
      ThreeAPFree (Set.range v) → sliceRank (lineTensor k v) ≤ B) :
    capsetNumber n ≤ B := by
  obtain ⟨v, hinj, hfree, hrank⟩ := exists_sliceRank_lineTensor_eq_capsetNumber k n
  calc capsetNumber n = sliceRank (lineTensor k v) := hrank.symm
    _ ≤ B := h _ v hinj hfree

/-- Satisfiability of the schema hypothesis at `B = 3^n` (joint witness for
`capsetNumber_le_of_forall_sliceRank_lineTensor_le`): the mode-1 totality
bound gives `sliceRank ≤ m ≤ 3^n` for any injective tuple, reproving
`capsetNumber_le_pow` through the tensor route. -/
example (n : ℕ) : capsetNumber n ≤ 3 ^ n := by
  refine capsetNumber_le_of_forall_sliceRank_lineTensor_le (k := ZMod 3) ?_
  intro m v hv _
  refine le_trans (sliceRank_le_left _) ?_
  calc m = Fintype.card (Fin m) := (Fintype.card_fin m).symm
    _ ≤ Fintype.card (Fin n → ZMod 3) := Fintype.card_le_of_injective v hv
    _ = 3 ^ n := by rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

end LineTensor

/-! ## 5. Croot–Lev–Pach / Ellenberg–Gijswijt (sorry-free) -/

section CLP

/-- The Croot–Lev–Pach monomial count for `F_3`: the number of monomials in
`n` variables with each exponent at most `2` and total degree at most
`2n/3`, spelled multiplicatively (`3·Σ ≤ 2n`) to avoid ℕ-division junk.
This is `m_{(q-1)n/3}` of References/arXiv-1605-09223 at `q = 3`;
asymptotically `o(2.756^n)`. -/
def clpMonomialCount (n : ℕ) : ℕ :=
  (Finset.univ.filter fun a : Fin n → Fin 3 => 3 * ∑ i, (a i : ℕ) ≤ 2 * n).card

/-- Ground checks: 1, 1, 3, 10, 15 monomials for n = 0, …, 4 (degree
thresholds 0, 0, 1, 2, 2). -/
example : clpMonomialCount 0 = 1 ∧ clpMonomialCount 1 = 1 ∧ clpMonomialCount 2 = 3 ∧
    clpMonomialCount 3 = 10 ∧ clpMonomialCount 4 = 15 := by decide

/-- The coefficient table of the CLP kill polynomial over `F_3`: in
`ZMod 3` the line indicator `δ₀(x+y+z)` equals `1 − (x+y+z)²` (`0 ↦ 1`,
`1 ↦ 0`, `2 ↦ 0`), which expands to
`1 − x² − y² − z² − 2xy − 2xz − 2yz`, i.e. (mod 3) coefficient `1` on the
constant monomial, `2` on `x², y², z²`, `1` on `xy, xz, yz`, `0`
elsewhere. `clpCoeff p q r` is the coefficient of `x^p y^q z^r`. Every
nonzero entry has `p + q + r ≤ 2` (`clpCoeff_ne_zero_deg`) — the degree
bound that powers the slice count. -/
def clpCoeff (p q r : Fin 3) : ZMod 3 :=
  if (p : ℕ) + (q : ℕ) + (r : ℕ) = 0 then 1
  else if (p : ℕ) + (q : ℕ) + (r : ℕ) = 2 then
    (if p = 1 ∨ q = 1 ∨ r = 1 then 1 else 2)
  else 0

/-! Ground checks for `clpCoeff`: the constant, square, cross, and
vanishing entries of `1 − (x+y+z)²` over `F_3`. -/

example : clpCoeff 0 0 0 = 1 := rfl
example : clpCoeff 2 0 0 = 2 := rfl
example : clpCoeff 0 2 0 = 2 := rfl
example : clpCoeff 1 1 0 = 1 := rfl
example : clpCoeff 1 0 1 = 1 := rfl
example : clpCoeff 1 0 0 = 0 := rfl
example : clpCoeff 2 2 2 = 0 := rfl

/-- **The char-3 indicator identity, expanded.** In `ZMod 3`,
`δ₀(x+y+z) = 1 − (x+y+z)² = ∑_{(p,q,r)} clpCoeff p q r · x^p y^q z^r`
(sum over `(Fin 3)³`, exponents read through `Fin.val`). Kernel-decided
over all 27 inputs. This is the engine of the Croot–Lev–Pach polynomial
method at `q = 3`. -/
theorem clpCoeff_expand :
    ∀ x y z : ZMod 3,
      (if x + y + z = 0 then (1 : ZMod 3) else 0)
        = ∑ w : Fin 3 × Fin 3 × Fin 3,
            clpCoeff w.1 w.2.1 w.2.2 * x ^ (w.1 : ℕ) * y ^ (w.2.1 : ℕ)
              * z ^ (w.2.2 : ℕ) := by
  decide

/-- Nonzero CLP coefficients have total degree at most 2 (27 cases,
kernel-decided): `1 − (x+y+z)²` is a polynomial of degree 2. -/
theorem clpCoeff_ne_zero_deg :
    ∀ p q r : Fin 3, clpCoeff p q r ≠ 0 → (p : ℕ) + (q : ℕ) + (r : ℕ) ≤ 2 := by
  decide

/-- **Monomial expansion of the line tensor.** Entrywise, the line tensor
of ANY tuple `v` (injectivity and 3AP-freeness not needed) is the
polynomial `∏ t, (1 − (v i t + v j t + v l t)²)` written out in the
monomial basis: a sum over exponent triples `(a, b, c)` of
`(∏ t, clpCoeff (a t) (b t) (c t)) · x^a(i) · x^b(j) · x^c(l)` with
`x^a(i) = ∏ t, v i t ^ (a t)`. The indicator factorizes coordinatewise,
each factor expands by `clpCoeff_expand`, and `Finset.prod_univ_sum`
distributes the product over the sums. -/
theorem lineTensor_apply_expand {n m : ℕ} (v : Fin m → Fin n → ZMod 3)
    (i j l : Fin m) :
    lineTensor (ZMod 3) v i j l
      = ∑ a : Fin n → Fin 3, ∑ b : Fin n → Fin 3, ∑ c : Fin n → Fin 3,
          (∏ t, clpCoeff (a t) (b t) (c t)) * (∏ t, v i t ^ (a t : ℕ))
            * (∏ t, v j t ^ (b t : ℕ)) * (∏ t, v l t ^ (c t : ℕ)) := by
  have h1 : lineTensor (ZMod 3) v i j l
      = ∏ t, (if v i t + v j t + v l t = 0 then (1 : ZMod 3) else 0) := by
    simp only [lineTensor]
    by_cases hz : v i + v j + v l = 0
    · rw [if_pos hz]
      refine (Finset.prod_eq_one fun t _ => ?_).symm
      have ht : v i t + v j t + v l t = 0 := by
        have hc := congrFun hz t
        simpa using hc
      rw [if_pos ht]
    · rw [if_neg hz]
      have hex : ∃ t, ¬ (v i t + v j t + v l t = 0) := by
        by_contra hall
        push Not at hall
        refine hz (funext fun t => ?_)
        simpa using hall t
      obtain ⟨t, ht⟩ := hex
      exact (Finset.prod_eq_zero (Finset.mem_univ t) (if_neg ht)).symm
  calc lineTensor (ZMod 3) v i j l
      = ∏ t, (if v i t + v j t + v l t = 0 then (1 : ZMod 3) else 0) := h1
    _ = ∏ t, ∑ w : Fin 3 × Fin 3 × Fin 3,
          clpCoeff w.1 w.2.1 w.2.2 * v i t ^ (w.1 : ℕ) * v j t ^ (w.2.1 : ℕ)
            * v l t ^ (w.2.2 : ℕ) :=
        Finset.prod_congr rfl fun t _ => clpCoeff_expand (v i t) (v j t) (v l t)
    _ = ∑ x ∈ Fintype.piFinset
          (fun _ : Fin n => (Finset.univ : Finset (Fin 3 × Fin 3 × Fin 3))),
          ∏ t, clpCoeff (x t).1 (x t).2.1 (x t).2.2 * v i t ^ ((x t).1 : ℕ)
            * v j t ^ ((x t).2.1 : ℕ) * v l t ^ ((x t).2.2 : ℕ) :=
        Finset.prod_univ_sum _ _
    _ = ∑ x : Fin n → Fin 3 × Fin 3 × Fin 3,
          ∏ t, clpCoeff (x t).1 (x t).2.1 (x t).2.2 * v i t ^ ((x t).1 : ℕ)
            * v j t ^ ((x t).2.1 : ℕ) * v l t ^ ((x t).2.2 : ℕ) := by
        rw [Fintype.piFinset_univ]
    _ = ∑ p : (Fin n → Fin 3) × (Fin n → Fin 3) × (Fin n → Fin 3),
          (∏ t, clpCoeff (p.1 t) (p.2.1 t) (p.2.2 t))
            * (∏ t, v i t ^ (p.1 t : ℕ)) * (∏ t, v j t ^ (p.2.1 t : ℕ))
            * (∏ t, v l t ^ (p.2.2 t : ℕ)) := by
        refine (Fintype.sum_equiv
          ⟨fun p => fun t => (p.1 t, p.2.1 t, p.2.2 t),
           fun x => (fun t => (x t).1, fun t => (x t).2.1, fun t => (x t).2.2),
           fun p => rfl, fun x => rfl⟩
          _ _ fun p => ?_).symm
        simp only [Equiv.coe_fn_mk, Finset.prod_mul_distrib]
    _ = ∑ a : Fin n → Fin 3, ∑ b : Fin n → Fin 3, ∑ c : Fin n → Fin 3,
          (∏ t, clpCoeff (a t) (b t) (c t)) * (∏ t, v i t ^ (a t : ℕ))
            * (∏ t, v j t ^ (b t : ℕ)) * (∏ t, v l t ^ (c t : ℕ)) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Fintype.sum_prod_type]

/-- **Tao's partition step, abstractly.** If a cubical tensor `T` expands
as `T i j l = ∑ a, ∑ b, ∑ c, C a b c · X a i · Y b j · Z c l` over a
finite monomial index `ι`, and every nonzero coefficient satisfies
`P₁ a ∨ P₂ b ∨ P₃ c` ("some mode is low-degree"), then grouping each
monomial by its first low mode — mode 1 on `P₁ a`, mode 2 on
`P₂ b ∧ ¬ P₁ a`, mode 3 on the rest — exhibits `T` as a sum of
`|P₁| + |P₂| + |P₃|` slices. This is the symmetrized Croot–Lev–Pach
mechanism (Tao 2016), the analogue of "at least one of `m`, `m′` has
degree at most `d/2`" in Proposition 2 of
References/GroupTPP/arXiv-1605-09223. Hypotheses jointly instantiated by
`sliceRankLE_lineTensor_clp` below. -/
theorem sliceRankLE_of_expansion {k : Type*} [CommSemiring k] {m : ℕ}
    {ι : Type*} [Fintype ι]
    {T : Tensor k m m m} {C : ι → ι → ι → k} {X Y Z : ι → Fin m → k}
    {P₁ P₂ P₃ : ι → Prop} [DecidablePred P₁] [DecidablePred P₂] [DecidablePred P₃]
    (hT : ∀ i j l, T i j l = ∑ a, ∑ b, ∑ c, C a b c * X a i * Y b j * Z c l)
    (hC : ∀ a b c, C a b c ≠ 0 → P₁ a ∨ P₂ b ∨ P₃ c) :
    SliceRankLE T ((Finset.univ.filter P₁).card + (Finset.univ.filter P₂).card
      + (Finset.univ.filter P₃).card) := by
  set D₁ : Finset ι := Finset.univ.filter P₁ with hD₁
  set D₂ : Finset ι := Finset.univ.filter P₂ with hD₂
  set D₃ : Finset ι := Finset.univ.filter P₃ with hD₃
  refine sliceRankLE_of_parts le_rfl
    (fun s i => X (D₁.equivFin.symm s : ι) i)
    (fun s j l => ∑ b, ∑ c, C (D₁.equivFin.symm s : ι) b c * Y b j * Z c l)
    (fun s j => Y (D₂.equivFin.symm s : ι) j)
    (fun s i l => ∑ a, ∑ c,
      if P₁ a then 0 else C a (D₂.equivFin.symm s : ι) c * X a i * Z c l)
    (fun s l => Z (D₃.equivFin.symm s : ι) l)
    (fun s i j => ∑ a, ∑ b,
      if P₁ a ∨ P₂ b then 0 else C a b (D₃.equivFin.symm s : ι) * X a i * Y b j)
    ?_
  intro i j l
  rw [hT i j l]
  -- mode-1 sum as a triple sum with indicator `P₁ a`
  have hm1 : (∑ s : Fin D₁.card, X (D₁.equivFin.symm s : ι) i *
        ∑ b, ∑ c, C (D₁.equivFin.symm s : ι) b c * Y b j * Z c l)
      = ∑ a, ∑ b, ∑ c,
          (if P₁ a then C a b c * X a i * Y b j * Z c l else 0) := by
    rw [Equiv.sum_comp (D₁.equivFin.symm)
      (fun x : ↥D₁ => X (x : ι) i * ∑ b, ∑ c, C (x : ι) b c * Y b j * Z c l)]
    rw [Finset.sum_coe_sort D₁
      (fun a => X a i * ∑ b, ∑ c, C a b c * Y b j * Z c l)]
    rw [hD₁, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h₁ : P₁ a
    · simp only [if_pos h₁]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    · simp only [if_neg h₁, Finset.sum_const_zero]
  -- mode-2 sum as a triple sum with indicator `P₂ b ∧ ¬ P₁ a`
  have hm2 : (∑ s : Fin D₂.card, Y (D₂.equivFin.symm s : ι) j *
        ∑ a, ∑ c,
          if P₁ a then 0 else C a (D₂.equivFin.symm s : ι) c * X a i * Z c l)
      = ∑ a, ∑ b, ∑ c,
          (if P₂ b ∧ ¬ P₁ a then C a b c * X a i * Y b j * Z c l else 0) := by
    rw [Equiv.sum_comp (D₂.equivFin.symm)
      (fun x : ↥D₂ => Y (x : ι) j * ∑ a, ∑ c,
        if P₁ a then 0 else C a (x : ι) c * X a i * Z c l)]
    rw [Finset.sum_coe_sort D₂
      (fun b => Y b j * ∑ a, ∑ c,
        if P₁ a then 0 else C a b c * X a i * Z c l)]
    rw [hD₂, Finset.sum_filter]
    have hpt : ∀ b : ι,
        (if P₂ b then Y b j * ∑ a, ∑ c,
          (if P₁ a then 0 else C a b c * X a i * Z c l) else 0)
        = ∑ a, ∑ c,
            (if P₂ b ∧ ¬ P₁ a then C a b c * X a i * Y b j * Z c l else 0) := by
      intro b
      by_cases h₂ : P₂ b
      · simp only [if_pos h₂]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        by_cases h₁ : P₁ a
        · rw [if_pos h₁, mul_zero,
            if_neg (fun hcon : P₂ b ∧ ¬ P₁ a => hcon.2 h₁)]
        · rw [if_neg h₁, if_pos ⟨h₂, h₁⟩]
          ring
      · simp [h₂]
    exact (Finset.sum_congr rfl fun b _ => hpt b).trans Finset.sum_comm
  -- mode-3 sum as a triple sum with indicator `P₃ c ∧ ¬ P₁ a ∧ ¬ P₂ b`
  have hm3 : (∑ s : Fin D₃.card, Z (D₃.equivFin.symm s : ι) l *
        ∑ a, ∑ b,
          if P₁ a ∨ P₂ b then 0
          else C a b (D₃.equivFin.symm s : ι) * X a i * Y b j)
      = ∑ a, ∑ b, ∑ c,
          (if P₃ c ∧ ¬ P₁ a ∧ ¬ P₂ b then C a b c * X a i * Y b j * Z c l
           else 0) := by
    rw [Equiv.sum_comp (D₃.equivFin.symm)
      (fun x : ↥D₃ => Z (x : ι) l * ∑ a, ∑ b,
        if P₁ a ∨ P₂ b then 0 else C a b (x : ι) * X a i * Y b j)]
    rw [Finset.sum_coe_sort D₃
      (fun c => Z c l * ∑ a, ∑ b,
        if P₁ a ∨ P₂ b then 0 else C a b c * X a i * Y b j)]
    rw [hD₃, Finset.sum_filter]
    have hpt : ∀ c : ι,
        (if P₃ c then Z c l * ∑ a, ∑ b,
          (if P₁ a ∨ P₂ b then 0 else C a b c * X a i * Y b j) else 0)
        = ∑ a, ∑ b,
            (if P₃ c ∧ ¬ P₁ a ∧ ¬ P₂ b then C a b c * X a i * Y b j * Z c l
             else 0) := by
      intro c
      by_cases h₃ : P₃ c
      · simp only [if_pos h₃]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases h₁ : P₁ a
        · rw [if_pos (Or.inl h₁), mul_zero,
            if_neg (fun hcon : P₃ c ∧ ¬ P₁ a ∧ ¬ P₂ b => hcon.2.1 h₁)]
        · by_cases h₂ : P₂ b
          · rw [if_pos (Or.inr h₂), mul_zero,
              if_neg (fun hcon : P₃ c ∧ ¬ P₁ a ∧ ¬ P₂ b => hcon.2.2 h₂)]
          · rw [if_neg (fun hor : P₁ a ∨ P₂ b => hor.elim h₁ h₂),
              if_pos ⟨h₃, h₁, h₂⟩]
            ring
      · simp [h₃]
    exact (Finset.sum_congr rfl fun c _ => hpt c).trans
      (Finset.sum_comm.trans (Finset.sum_congr rfl fun a _ => Finset.sum_comm))
  rw [hm1, hm2, hm3]
  calc ∑ a, ∑ b, ∑ c, C a b c * X a i * Y b j * Z c l
      = ∑ a, ∑ b, ∑ c,
          ((if P₁ a then C a b c * X a i * Y b j * Z c l else 0)
            + (if P₂ b ∧ ¬ P₁ a then C a b c * X a i * Y b j * Z c l else 0)
            + (if P₃ c ∧ ¬ P₁ a ∧ ¬ P₂ b then C a b c * X a i * Y b j * Z c l
               else 0)) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun c _ => ?_
        by_cases h₁ : P₁ a
        · simp [h₁]
        · by_cases h₂ : P₂ b
          · simp [h₁, h₂]
          · by_cases h₃ : P₃ c
            · simp [h₁, h₂, h₃]
            · have hzero : C a b c = 0 := by
                by_contra hne
                rcases hC a b c hne with h | h | h
                · exact h₁ h
                · exact h₂ h
                · exact h₃ h
              simp [h₁, h₂, h₃, hzero]
    _ = (∑ a, ∑ b, ∑ c,
          (if P₁ a then C a b c * X a i * Y b j * Z c l else 0))
        + (∑ a, ∑ b, ∑ c,
          (if P₂ b ∧ ¬ P₁ a then C a b c * X a i * Y b j * Z c l else 0))
        + (∑ a, ∑ b, ∑ c,
          (if P₃ c ∧ ¬ P₁ a ∧ ¬ P₂ b then C a b c * X a i * Y b j * Z c l
           else 0)) := by
        simp only [Finset.sum_add_distrib]

/-- **The Croot–Lev–Pach slice-rank bound, unconditioned.** Over `F_3`,
the line tensor of ANY tuple of points of `F_3^n` — no injectivity, no
3AP-freeness — is a sum of at most `3·clpMonomialCount n` slices: in the
monomial expansion `lineTensor_apply_expand` every exponent triple with
nonzero coefficient has per-coordinate degree at most 2
(`clpCoeff_ne_zero_deg`), hence total degree at most `2n`, hence some
mode of degree at most `2n/3` (spelled `3·Σ ≤ 2n`), and
`sliceRankLE_of_expansion` groups the monomials accordingly. This is the
unconditioned "full-tensor form" this file's § 5 previously archived. -/
theorem sliceRankLE_lineTensor_clp (n m : ℕ) (v : Fin m → Fin n → ZMod 3) :
    SliceRankLE (lineTensor (ZMod 3) v) (3 * clpMonomialCount n) := by
  have hdeg : ∀ a b c : Fin n → Fin 3,
      (∏ t, clpCoeff (a t) (b t) (c t)) ≠ 0 →
        (3 * ∑ i, (a i : ℕ) ≤ 2 * n) ∨ (3 * ∑ i, (b i : ℕ) ≤ 2 * n)
          ∨ (3 * ∑ i, (c i : ℕ) ≤ 2 * n) := by
    intro a b c hprod
    have hpt : ∀ t, (a t : ℕ) + (b t : ℕ) + (c t : ℕ) ≤ 2 := by
      intro t
      refine clpCoeff_ne_zero_deg (a t) (b t) (c t) fun h0 => ?_
      exact hprod (Finset.prod_eq_zero (Finset.mem_univ t) h0)
    have hsum : ∑ t, ((a t : ℕ) + (b t : ℕ) + (c t : ℕ)) ≤ 2 * n := by
      calc ∑ t, ((a t : ℕ) + (b t : ℕ) + (c t : ℕ))
          ≤ ∑ _t : Fin n, 2 := Finset.sum_le_sum fun t _ => hpt t
        _ = 2 * n := by simp [mul_comm]
    have hsplit : ∑ t, ((a t : ℕ) + (b t : ℕ) + (c t : ℕ))
        = (∑ t, (a t : ℕ)) + (∑ t, (b t : ℕ)) + (∑ t, (c t : ℕ)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    by_contra hcon
    push Not at hcon
    omega
  -- `C`, `X`, `Y`, `Z` are deliberately left to unification: pinning them
  -- with named arguments forces the unifier to compare the summands under
  -- mismatched instance paths and it times out evaluating finsets.
  have h := sliceRankLE_of_expansion
    (T := lineTensor (ZMod 3) v)
    (P₁ := fun a : Fin n → Fin 3 => 3 * ∑ i, (a i : ℕ) ≤ 2 * n)
    (P₂ := fun a : Fin n → Fin 3 => 3 * ∑ i, (a i : ℕ) ≤ 2 * n)
    (P₃ := fun a : Fin n → Fin 3 => 3 * ∑ i, (a i : ℕ) ≤ 2 * n)
    (lineTensor_apply_expand v) hdeg
  refine h.mono ?_
  have hN : (Finset.univ.filter
      fun a : Fin n → Fin 3 => 3 * ∑ i, (a i : ℕ) ≤ 2 * n).card
      = clpMonomialCount n := rfl
  omega

set_option linter.unusedVariables false in
/-- **Croot–Lev–Pach slice-rank bound**
(References/GroupTPP/arXiv-1605-09223, Proposition 2 — "essentially Lemma
1 of Croot–Lev–Pach" — feeding Theorem 4 at `q = 3`, in Tao's symmetric
slice-rank formulation): over `F_3`, the line tensor of an injective
3AP-free tuple of points of `F_3^n` has slice rank at most
`3·clpMonomialCount n` — exactly the instance the § 4 method schema
consumes.

Sorry-free since 2026-08-05 (previously this file's archived second
sorry). The hypotheses `hv`, `hfree` are retained for interface stability
with the § 4 schema but are NOT needed: the bound holds for every tuple
(`sliceRankLE_lineTensor_clp`), so no slice-rank pullback-monotonicity is
required here either — `SliceRank.lean` now carries that lemma anyway as
`SliceRankLE.comp` / `sliceRank_comp_le`. Joint satisfiability of the
hypotheses: the § 4 example at `(0, 1) ⊆ F_3^1`. Model formalization
(proof structure only; different route — they use the EG vanishing-space
argument): Dahmen–Hölzl–Lewis, ITP 2019, `theorem_12_1` of
lean-forward/cap_set_problem (References/BilinearComplexity/
arXiv-1907-01449). -/
theorem croot_lev_pach_sliceRank_lineTensor (n m : ℕ) (v : Fin m → Fin n → ZMod 3)
    (hv : Function.Injective v) (hfree : ThreeAPFree (Set.range v)) :
    sliceRank (lineTensor (ZMod 3) v) ≤ 3 * clpMonomialCount n :=
  sliceRank_le_of_sliceRankLE (sliceRankLE_lineTensor_clp n m v)

/-- **Ellenberg–Gijswijt cap-set bound** (References/GroupTPP/
arXiv-1605-09223, Theorem 4 at `q = 3`, `α = β = γ = 1`):
A090245(n) ≤ 3·m_{2n/3}, the exact finite form of the `o(2.756^n)` bound
— the § 4 method schema applied to the Croot–Lev–Pach bound. Sorry-free
end to end since 2026-08-05 (see the closing axiom audit). -/
theorem ellenberg_gijswijt (n : ℕ) : capsetNumber n ≤ 3 * clpMonomialCount n :=
  capsetNumber_le_of_forall_sliceRank_lineTensor_le fun m v hv hfree =>
    croot_lev_pach_sliceRank_lineTensor n m v hv hfree

/-- Kernel-verified instances of `ellenberg_gijswijt` at n = 0, 1: 1 ≤ 3,
2 ≤ 3. -/
example : capsetNumber 0 ≤ 3 * clpMonomialCount 0 ∧
    capsetNumber 1 ≤ 3 * clpMonomialCount 1 := by decide

/-- Kernel-verified instance of `ellenberg_gijswijt` at n = 2: 4 ≤ 9. -/
example : capsetNumber 2 ≤ 3 * clpMonomialCount 2 := by
  rw [capsetNumber_two]; decide

end CLP

/-! ## 6. Bridge to the Erdős–Rado sunflower layer (Erdos/Erdos20) -/

section ErdosRadoBridge

variable {n : ℕ}

/-- The support of `x ∈ F_2^n` as a `Finset (Fin n)`: the coordinates equal
to `1`. Injective, so families of vectors correspond to set families. -/
def vecSupport (x : Fin n → ZMod 2) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i = 1

/-- Membership in `vecSupport x`: coordinate `i` is in the support iff `x i = 1`. -/
@[simp] theorem mem_vecSupport {x : Fin n → ZMod 2} {i : Fin n} :
    i ∈ vecSupport x ↔ x i = 1 := by
  simp [vecSupport]

example : vecSupport (![0, 1, 1] : Fin 3 → ZMod 2) = {1, 2} := by decide

/-- `ZMod 2` vectors agreeing on one-hood agree. Kernel-decided. -/
private theorem zmod2_eq_of_one_iff : ∀ a b : ZMod 2, (a = 1 ↔ b = 1) → a = b := by decide

/-- The pointwise Δ-system dictionary: no exactly-two-ones pattern at a
coordinate iff the three pairwise one-hood conjunctions coincide there.
Kernel-decided (8 cases). -/
private theorem zmod2_not_exactlyTwoOnes_iff :
    ∀ a b c : ZMod 2, ¬ ExactlyTwoOnes a b c ↔
      ((a = 1 ∧ b = 1 ↔ a = 1 ∧ c = 1) ∧ (a = 1 ∧ b = 1 ↔ b = 1 ∧ c = 1)) := by decide

/-- `vecSupport` is injective (`ZMod 2` is two-valued). -/
theorem vecSupport_injective : Function.Injective (vecSupport (n := n)) := by
  intro x y h
  funext i
  have hi := Finset.ext_iff.mp h i
  simp only [mem_vecSupport] at hi
  exact zmod2_eq_of_one_iff (x i) (y i) hi

/-- **A Peebles sunflower is a Δ-system of supports**: a triple of vectors
has no exactly-two-ones coordinate iff the three pairwise intersections of
their supports coincide (the classical Erdős–Rado sunflower condition —
an element in exactly two of three sets is precisely a witness that two
pairwise intersections differ). No distinctness hypotheses: the equivalence
is exact even for degenerate triples. -/
theorem forall_not_exactlyTwoOnes_iff (x y z : Fin n → ZMod 2) :
    (∀ i, ¬ ExactlyTwoOnes (x i) (y i) (z i)) ↔
      vecSupport x ∩ vecSupport y = vecSupport x ∩ vecSupport z ∧
        vecSupport x ∩ vecSupport y = vecSupport y ∩ vecSupport z := by
  rw [Finset.ext_iff, Finset.ext_iff, ← forall_and]
  refine forall_congr' fun i => ?_
  simp only [Finset.mem_inter, mem_vecSupport]
  exact zmod2_not_exactlyTwoOnes_iff (x i) (y i) (z i)

/-- **A sunflower-free family has sunflower-free supports**: the support
family of a Peebles `SunflowerFree` family contains no classical 3-sunflower
in the sense of the project's Erdős–Rado layer
(`Erdos/Erdos20/Sunflower.lean`). One-way containment: the gap between the
two notions is not confined to degenerate data — the chain family
`{100, 110, 111}` has three distinct nonempty supports and is not Peebles
sunflower-free, yet its supports carry no classical 3-sunflower (see the
discriminator below). -/
theorem not_hasSunflower_image_vecSupport {S : Finset (Fin n → ZMod 2)}
    (hS : SunflowerFree S) : ¬ HasSunflower (S.image vecSupport) 3 := by
  rintro ⟨sub, hsub, hcard, K, hK⟩
  obtain ⟨A, B, C, hAB, hAC, hBC, rfl⟩ := Finset.card_eq_three.mp hcard
  obtain ⟨x, hxS, hxA⟩ := Finset.mem_image.mp (hsub (by simp : A ∈ ({A, B, C} : Finset _)))
  obtain ⟨y, hyS, hyB⟩ := Finset.mem_image.mp (hsub (by simp : B ∈ ({A, B, C} : Finset _)))
  obtain ⟨z, hzS, hzC⟩ := Finset.mem_image.mp (hsub (by simp : C ∈ ({A, B, C} : Finset _)))
  have hne : ¬(x = y ∧ y = z) := by
    rintro ⟨rfl, rfl⟩
    exact hAB (hxA.symm.trans hyB)
  obtain ⟨i, hex⟩ := hS x hxS y hyS z hzS hne
  obtain ⟨hsubK, -, hinter⟩ := hK
  rcases hex with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · -- x, y are 1 at i: i ∈ A ∩ B = K ⊆ C, yet z i = 0
    have hiK : i ∈ K := by
      rw [← hinter A (by simp) B (by simp) hAB]
      exact Finset.mem_inter.mpr ⟨hxA ▸ mem_vecSupport.mpr h1, hyB ▸ mem_vecSupport.mpr h2⟩
    have hiC : i ∈ C := hsubK C (by simp) hiK
    rw [← hzC, mem_vecSupport, h3] at hiC
    exact absurd hiC (by decide)
  · -- x, z are 1 at i: i ∈ A ∩ C = K ⊆ B, yet y i = 0
    have hiK : i ∈ K := by
      rw [← hinter A (by simp) C (by simp) hAC]
      exact Finset.mem_inter.mpr ⟨hxA ▸ mem_vecSupport.mpr h1, hzC ▸ mem_vecSupport.mpr h3⟩
    have hiB : i ∈ B := hsubK B (by simp) hiK
    rw [← hyB, mem_vecSupport, h2] at hiB
    exact absurd hiB (by decide)
  · -- y, z are 1 at i: i ∈ B ∩ C = K ⊆ A, yet x i = 0
    have hiK : i ∈ K := by
      rw [← hinter B (by simp) C (by simp) hBC]
      exact Finset.mem_inter.mpr ⟨hyB ▸ mem_vecSupport.mpr h2, hzC ▸ mem_vecSupport.mpr h3⟩
    have hiA : i ∈ A := hsubK A (by simp) hiK
    rw [← hxA, mem_vecSupport, h1] at hiA
    exact absurd hiA (by decide)

/-- Satisfiability: the 3-element sunflower-free family of § 1 has
3-sunflower-free supports; and the rejected disjoint-support family's
supports DO form a classical sunflower with empty core (nonempty petals),
witnessing that the § 6 bridge is discriminating. -/
example : IsSunflowerWith ({{0}, {1}, {2}} : Finset (Finset (Fin 3))) (∅ : Finset (Fin 3)) :=
  ⟨by decide, by decide, by decide⟩

-- Discriminator for the one-way containment: the chain family has three
-- distinct nonempty supports (nondegenerate data), fails Peebles
-- `SunflowerFree`, and still has no classical 3-sunflower among its
-- supports — so the gap between the two notions is real, not degenerate.
example :
    (({![1, 0, 0], ![1, 1, 0], ![1, 1, 1]} : Finset (Fin 3 → ZMod 2)).card = 3) ∧
    ¬ SunflowerFree ({![1, 0, 0], ![1, 1, 0], ![1, 1, 1]} : Finset (Fin 3 → ZMod 2)) ∧
    ¬ HasSunflower
      ((({![1, 0, 0], ![1, 1, 0], ![1, 1, 1]} : Finset (Fin 3 → ZMod 2)).image vecSupport)) 3 := by
  refine ⟨by decide, by decide, ?_⟩
  rintro ⟨sub, hsub, hcard, K, hK⟩
  have hfam : (({![1, 0, 0], ![1, 1, 0], ![1, 1, 1]} : Finset (Fin 3 → ZMod 2)).image vecSupport)
      = ({{0}, {0, 1}, {0, 1, 2}} : Finset (Finset (Fin 3))) := by decide
  rw [hfam] at hsub
  have hsubeq : sub = ({{0}, {0, 1}, {0, 1, 2}} : Finset (Finset (Fin 3))) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; decide)
  subst hsubeq
  obtain ⟨-, -, hinter⟩ := hK
  have h1 := hinter {0} (by decide) {0, 1} (by decide) (by decide)
  have h2 := hinter {0, 1} (by decide) {0, 1, 2} (by decide) (by decide)
  rw [← h1] at h2
  revert h2
  decide

end ErdosRadoBridge

/-! Axiom audit for the main declarations. `peebles_conjecture` is this
file's single intended sorry (archived open conjecture, § 3) and reports
`sorryAx`; everything else stays within the base axioms. -/

#print axioms sunflowerFreeWeight_le_capsetNumber
#print axioms peebles_conjecture
#print axioms sliceRank_lineTensor
#print axioms sliceRankLE_lineTensor_clp
#print axioms croot_lev_pach_sliceRank_lineTensor
#print axioms ellenberg_gijswijt

end BilinearComplexity
