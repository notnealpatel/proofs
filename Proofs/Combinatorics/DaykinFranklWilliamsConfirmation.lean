/-
# The Daykin–Frankl inequality for convex subsets of a cube

Kada Kalman Williams, *Confirmation of the Daykin-Frankl Conjecture*,
arXiv:2609.03087, Theorem 2 and Lemma 3 (Sections 2–3). The author credits
the proof content to ChatGPT 5.6 Sol Pro. The conjecture is due to
D. E. Daykin and P. Frankl, *Inequalities for subsets of a set and KLYM
posets*, SIAM J. Alg. Disc. Meth. 4 (1983), 67–69.

For convex `P ⊆ Q_n`, the width inequality is
`|P| w(Q_n) ≤ 2^n w(P)`. Below, Lemma 3 gives the two-level inequality;
induction proves Theorem 2 and a strengthening with an arbitrary finite
poset in place of `Q_k`.

## Formalization notes

* `w(P)` is `width P` for a `Finset` in a partial order: the largest
  cardinality of an antichain (for `≤`) contained in `P`.
* `Q_n` is `Fin n → Bool` (pointwise order) in the induction and
  `Finset (Fin n)` (inclusion) in the final statements; `Q_1 = Bool` with
  `false = 0 < true = 1`.  Convexity is `Set.OrdConnected`.
* The paper's proof of Lemma 3 leaves the set `C` undefined in its sorting
  rule; it must be read as `C = B = P_0 ∩ P_1`.  We use an equivalent,
  symmetric presentation: with `L_0 × {0} ∪ H_0 × {1}` and
  `L_1 × {0} ∪ H_1 × {1}` maximum antichains of `P_0 × Q_1` and `P_1 × Q_1`,
  put `p x := ∃ z ∈ L_0 ∪ H_0, z ≤ x`, `q y := ∃ z ∈ H_1 ∪ L_1, y ≤ z`,
  `X := {x ∈ L_1 | ¬ p x} ∪ {y ∈ H_0 | q y}` and
  `Y := {y ∈ H_0 | ¬ q y} ∪ {x ∈ L_1 | p x}`.  Then `L_0 × {0} ∪ X × {1}` and
  `Y × {0} ∪ H_1 × {1}` are antichains of `P`, and `|X| + |Y| = |L_1| + |H_0|`.
  This coincides with the paper's sets `(L_1 \ B) ∪ L` and `(H_0 \ B) ∪ H`.
  The paper's argument also omits the case `x < y` with `x ∈ L_1 ∩ L`,
  `y ∈ H_0 ∩ L`; it is covered in `key_lemma_twoLevel`.
* Convexity enters Lemma 3 only through property (*): `x ∈ P_0`, `y ∈ P_1`,
  `x ≤ y` imply `x ∈ P_1` and `y ∈ P_0`.
* The binomial form needs only the middle slice as a witness antichain;
  Sperner's theorem (`IsAntichain.sperner`) is used only to record
  `w(Q_n) = C(n, ⌊n/2⌋)` (`width_univ_finset`).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.DaykinFranklWilliamsConfirmation

open Finset

section Width
variable {α : Type*} [PartialOrder α]

/-- The width `w(P)` of a finite subset `P` of a partial order: the largest
cardinality of an antichain contained in `P`. -/
noncomputable def width (P : Finset α) : ℕ := by
  classical exact ((P.powerset.filter fun (A : Finset α) => IsAntichain (· ≤ ·) (A : Set α))).sup Finset.card

/-- Every antichain contained in `P` has at most `width P` elements. -/
theorem le_width {P A : Finset α} (hA : A ⊆ P) (hac : IsAntichain (· ≤ ·) (A : Set α)) :
    A.card ≤ width P := by
  classical
  unfold width
  exact Finset.le_sup (f := Finset.card) (by simp [hA, hac])

/-- The width is attained: `P` contains an antichain with exactly `width P`
elements. -/
theorem exists_antichain_card_eq_width (P : Finset α) :
    ∃ A ⊆ P, IsAntichain (· ≤ ·) (A : Set α) ∧ A.card = width P := by
  classical
  unfold width
  obtain ⟨A, hA, hcard⟩ := Finset.exists_mem_eq_sup
    (P.powerset.filter fun (A : Finset α) => IsAntichain (· ≤ ·) (A : Set α))
    ⟨∅, by simp⟩ Finset.card
  simp only [Finset.mem_filter, Finset.mem_powerset] at hA
  exact ⟨A, hA.1, hA.2, hcard.symm⟩

end Width

section TwoLevelDef
variable {R : Type*}

/-- The subset `L × {0} ∪ H × {1}` of `R × Q_1`, with `Q_1 = Bool` and
`0 = false`, `1 = true` (a disjoint union, so no decidable equality is needed). -/
def twoLevel (L H : Finset R) : Finset (R × Bool) :=
  (L ×ˢ {false}).disjUnion (H ×ˢ {true}) (by
    rw [Finset.disjoint_left]
    rintro ⟨x, b⟩ h1 h2
    simp only [Finset.mem_product, Finset.mem_singleton] at h1 h2
    rw [h1.2] at h2
    exact Bool.false_ne_true h2.2)

/-- `(x, 0) ∈ L × {0} ∪ H × {1}` iff `x ∈ L`. -/
@[simp] theorem mem_twoLevel_false {L H : Finset R} {x : R} :
    (x, false) ∈ twoLevel L H ↔ x ∈ L := by
  simp [twoLevel]

/-- `(x, 1) ∈ L × {0} ∪ H × {1}` iff `x ∈ H`. -/
@[simp] theorem mem_twoLevel_true {L H : Finset R} {x : R} :
    (x, true) ∈ twoLevel L H ↔ x ∈ H := by
  simp [twoLevel]

/-- `|L × {0} ∪ H × {1}| = |L| + |H|`. -/
theorem card_twoLevel (L H : Finset R) : (twoLevel L H).card = L.card + H.card := by
  simp [twoLevel, Finset.card_disjUnion]

/-- `L × {0} ∪ H × {1} ⊆ P_0 × {0} ∪ P_1 × {1}` iff `L ⊆ P_0` and `H ⊆ P_1`. -/
theorem twoLevel_subset_twoLevel_iff {L H P0 P1 : Finset R} :
    twoLevel L H ⊆ twoLevel P0 P1 ↔ L ⊆ P0 ∧ H ⊆ P1 := by
  constructor
  · intro h
    exact ⟨fun x hx => mem_twoLevel_false.1 (h (mem_twoLevel_false.2 hx)),
      fun x hx => mem_twoLevel_true.1 (h (mem_twoLevel_true.2 hx))⟩
  · rintro ⟨hL, hH⟩ ⟨x, b⟩ hx
    cases b
    · exact mem_twoLevel_false.2 (hL (mem_twoLevel_false.1 hx))
    · exact mem_twoLevel_true.2 (hH (mem_twoLevel_true.1 hx))

/-- Every finite subset of `R × Q_1` has the form `L × {0} ∪ H × {1}`. -/
theorem exists_twoLevel_eq (A : Finset (R × Bool)) : ∃ L H : Finset R, A = twoLevel L H := by
  classical
  refine ⟨(A.filter (fun p => p.2 = false)).image Prod.fst,
    (A.filter (fun p => p.2 = true)).image Prod.fst, ?_⟩
  ext ⟨x, b⟩
  cases b <;> simp

/-- `P × {0} ∪ P × {1} = P × Q_1`. -/
theorem twoLevel_self (P : Finset R) : twoLevel P P = P ×ˢ (Finset.univ : Finset Bool) := by
  ext ⟨x, b⟩
  cases b <;> simp

end TwoLevelDef

section TwoLevel
variable {R : Type*} [PartialOrder R]

/-- `L × {0} ∪ H × {1}` is an antichain of `R × Q_1` iff `L` and `H` are
antichains of `R` and no element of `L` lies below an element of `H`. -/
theorem isAntichain_twoLevel_iff {L H : Finset R} :
    IsAntichain (· ≤ ·) (twoLevel L H : Set (R × Bool)) ↔
      IsAntichain (· ≤ ·) (L : Set R) ∧ IsAntichain (· ≤ ·) (H : Set R) ∧
        ∀ x ∈ L, ∀ y ∈ H, ¬ x ≤ y := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro a ha b hb hne hle
      exact h (mem_twoLevel_false.2 ha) (mem_twoLevel_false.2 hb)
        (by simpa using hne) (Prod.mk_le_mk.2 ⟨hle, le_rfl⟩)
    · intro a ha b hb hne hle
      exact h (mem_twoLevel_true.2 ha) (mem_twoLevel_true.2 hb)
        (by simpa using hne) (Prod.mk_le_mk.2 ⟨hle, le_rfl⟩)
    · intro x hx y hy hle
      exact h (mem_twoLevel_false.2 hx) (mem_twoLevel_true.2 hy)
        (by simp) (Prod.mk_le_mk.2 ⟨hle, by decide⟩)
  · rintro ⟨hL, hH, hcross⟩ ⟨a, b⟩ ha ⟨c, d⟩ hc hne hle
    rw [Prod.mk_le_mk] at hle
    have hne' : (a, b) ≠ (c, d) := hne
    cases b <;> cases d
    · exact hL (mem_twoLevel_false.1 ha) (mem_twoLevel_false.1 hc)
        (fun h => hne' (by rw [h])) hle.1
    · exact hcross a (mem_twoLevel_false.1 ha) c (mem_twoLevel_true.1 hc) hle.1
    · exact absurd hle.2 (by decide)
    · exact hH (mem_twoLevel_true.1 ha) (mem_twoLevel_true.1 hc)
        (fun h => hne' (by rw [h])) hle.1


/-- **Key Lemma (Lemma 3 of arXiv:2609.03087), property-(*) form.**  For any
partial order `R` and finite `P_0, P_1 ⊆ R` satisfying (*): `x ∈ P_0`,
`y ∈ P_1`, `x ≤ y` imply `x ∈ P_1` and `y ∈ P_0`, we have
`w(P_0 × Q_1) + w(P_1 × Q_1) ≤ 2 w(P_0 × {0} ∪ P_1 × {1})`. -/
theorem key_lemma_twoLevel (P0 P1 : Finset R)
    (hstar : ∀ x ∈ P0, ∀ y ∈ P1, x ≤ y → x ∈ P1 ∧ y ∈ P0) :
    width (twoLevel P0 P0) + width (twoLevel P1 P1) ≤ 2 * width (twoLevel P0 P1) := by
  classical
  obtain ⟨A0, hA0P, hA0, hA0c⟩ := exists_antichain_card_eq_width (twoLevel P0 P0)
  obtain ⟨L0, H0, rfl⟩ := exists_twoLevel_eq A0
  obtain ⟨A1, hA1P, hA1, hA1c⟩ := exists_antichain_card_eq_width (twoLevel P1 P1)
  obtain ⟨L1, H1, rfl⟩ := exists_twoLevel_eq A1
  rw [twoLevel_subset_twoLevel_iff] at hA0P hA1P
  rw [isAntichain_twoLevel_iff] at hA0 hA1
  obtain ⟨hL0P, hH0P⟩ := hA0P
  obtain ⟨hL1P, hH1P⟩ := hA1P
  obtain ⟨acL0, acH0, crs0⟩ := hA0
  obtain ⟨acL1, acH1, crs1⟩ := hA1
  rw [← hA0c, ← hA1c, card_twoLevel, card_twoLevel]
  -- `p x`: some element of the first antichain lies below `x`;
  -- `q y`: some element of the second antichain lies above `y`.
  let p : R → Prop := fun x => ∃ z ∈ L0 ∪ H0, z ≤ x
  let q : R → Prop := fun y => ∃ z ∈ H1 ∪ L1, y ≤ z
  let X : Finset R := L1.filter (fun x => ¬ p x) ∪ H0.filter q
  let Y : Finset R := H0.filter (fun y => ¬ q y) ∪ L1.filter p
  have hXdisj : Disjoint (L1.filter (fun x => ¬ p x)) (H0.filter q) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_filter] at ha hb
    exact ha.2 ⟨a, Finset.mem_union_right _ hb.1, le_rfl⟩
  have hYdisj : Disjoint (H0.filter (fun y => ¬ q y)) (L1.filter p) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_filter] at ha hb
    exact ha.2 ⟨a, Finset.mem_union_right _ hb.1, le_rfl⟩
  have hXc : X.card = (L1.filter (fun x => ¬ p x)).card + (H0.filter q).card :=
    Finset.card_union_of_disjoint hXdisj
  have hYc : Y.card = (H0.filter (fun y => ¬ q y)).card + (L1.filter p).card :=
    Finset.card_union_of_disjoint hYdisj
  -- the first antichain `L0 × {0} ∪ X × {1}` of `P`
  have hXsub : X ⊆ P1 := by
    intro a ha
    rcases Finset.mem_union.1 ha with ha | ha
    · exact hL1P (Finset.mem_filter.1 ha).1
    · obtain ⟨haH0, z, hz, haz⟩ := Finset.mem_filter.1 ha
      have hzP1 : z ∈ P1 := by
        rcases Finset.mem_union.1 hz with hz | hz
        · exact hH1P hz
        · exact hL1P hz
      exact (hstar a (hH0P haH0) z hzP1 haz).1
  have hXac : IsAntichain (· ≤ ·) (X : Set R) := by
    intro a ha b hb hne hle
    rcases Finset.mem_union.1 ha with ha | ha <;>
      rcases Finset.mem_union.1 hb with hb | hb <;>
      rw [Finset.mem_filter] at ha hb
    · exact acL1 ha.1 hb.1 hne hle
    · -- `a ∈ L1`, `b ∈ H0` with some `z ∈ H1 ∪ L1` above `b`
      obtain ⟨z, hz, hbz⟩ := hb.2
      have haz : a ≤ z := hle.trans hbz
      rcases Finset.mem_union.1 hz with hz | hz
      · exact crs1 a ha.1 z hz haz
      · by_cases hza : a = z
        · subst hza
          exact hne (le_antisymm hle hbz)
        · exact acL1 ha.1 hz hza haz
    · exact hb.2 ⟨a, Finset.mem_union_right _ ha.1, hle⟩
    · exact acH0 ha.1 hb.1 hne hle
  have hXcross : ∀ x ∈ L0, ∀ y ∈ X, ¬ x ≤ y := by
    intro x hx y hy hle
    rcases Finset.mem_union.1 hy with hy | hy <;> rw [Finset.mem_filter] at hy
    · exact hy.2 ⟨x, Finset.mem_union_left _ hx, hle⟩
    · exact crs0 x hx y hy.1 hle
  have h1 : L0.card + X.card ≤ width (twoLevel P0 P1) := by
    rw [← card_twoLevel]
    exact le_width (twoLevel_subset_twoLevel_iff.2 ⟨hL0P, hXsub⟩)
      (isAntichain_twoLevel_iff.2 ⟨acL0, hXac, hXcross⟩)
  -- the second antichain `Y × {0} ∪ H1 × {1}` of `P`
  have hYsub : Y ⊆ P0 := by
    intro a ha
    rcases Finset.mem_union.1 ha with ha | ha
    · exact hH0P (Finset.mem_filter.1 ha).1
    · obtain ⟨haL1, z, hz, hza⟩ := Finset.mem_filter.1 ha
      have hzP0 : z ∈ P0 := by
        rcases Finset.mem_union.1 hz with hz | hz
        · exact hL0P hz
        · exact hH0P hz
      exact (hstar z hzP0 a (hL1P haL1) hza).2
  have hYac : IsAntichain (· ≤ ·) (Y : Set R) := by
    intro a ha b hb hne hle
    rcases Finset.mem_union.1 ha with ha | ha <;>
      rcases Finset.mem_union.1 hb with hb | hb <;>
      rw [Finset.mem_filter] at ha hb
    · exact acH0 ha.1 hb.1 hne hle
    · exact ha.2 ⟨b, Finset.mem_union_right _ hb.1, hle⟩
    · -- `a ∈ L1` with some `z ∈ L0 ∪ H0` below `a`, `b ∈ H0`
      obtain ⟨z, hz, hza⟩ := ha.2
      have hzb : z ≤ b := hza.trans hle
      rcases Finset.mem_union.1 hz with hz | hz
      · exact crs0 z hz b hb.1 hzb
      · by_cases hzb' : z = b
        · subst hzb'
          exact hne (le_antisymm hle hza)
        · exact acH0 hz hb.1 hzb' hzb
    · exact acL1 ha.1 hb.1 hne hle
  have hYcross : ∀ x ∈ Y, ∀ y ∈ H1, ¬ x ≤ y := by
    intro x hx y hy hle
    rcases Finset.mem_union.1 hx with hx | hx <;> rw [Finset.mem_filter] at hx
    · exact hx.2 ⟨y, Finset.mem_union_left _ hy, hle⟩
    · exact crs1 x hx.1 y hy hle
  have h2 : Y.card + H1.card ≤ width (twoLevel P0 P1) := by
    rw [← card_twoLevel]
    exact le_width (twoLevel_subset_twoLevel_iff.2 ⟨hYsub, hH1P⟩)
      (isAntichain_twoLevel_iff.2 ⟨hYac, acH1, hYcross⟩)
  have hsplitL1 := Finset.card_filter_add_card_filter_not (s := L1) p
  have hsplitH0 := Finset.card_filter_add_card_filter_not (s := H0) q
  omega

end TwoLevel

section Iso
variable {α β : Type*} [PartialOrder α] [PartialOrder β]

/-- Width does not decrease along an order embedding. -/
theorem width_le_width_map (f : α ↪o β) (P : Finset α) :
    width P ≤ width (P.map f.toEmbedding) := by
  obtain ⟨A, hAP, hA, hAc⟩ := exists_antichain_card_eq_width P
  rw [← hAc, ← Finset.card_map f.toEmbedding]
  refine le_width (Finset.map_subset_map.2 hAP) ?_
  rw [Finset.coe_map]
  exact hA.image_embedding f

/-- Width is invariant under order isomorphisms. -/
theorem width_map_orderIso (e : α ≃o β) (P : Finset α) :
    width (P.map e.toEquiv.toEmbedding) = width P := by
  apply le_antisymm
  · have h := width_le_width_map e.symm.toOrderEmbedding (P.map e.toEquiv.toEmbedding)
    have hmap : (P.map e.toEquiv.toEmbedding).map e.symm.toOrderEmbedding.toEmbedding = P := by
      ext x
      rw [Finset.mem_map]
      constructor
      · rintro ⟨a, ha, rfl⟩
        rw [Finset.mem_map_equiv] at ha
        exact ha
      · intro hx
        refine ⟨e x, Finset.mem_map_equiv.2 ?_, e.symm_apply_apply x⟩
        simpa using hx
    rwa [hmap] at h
  · exact width_le_width_map e.toOrderEmbedding P

/-- If an order isomorphism `e` carries `P` onto `Q`, then `w(Q) = w(P)`. -/
theorem width_congr_orderIso (e : α ≃o β) {P : Finset α} {Q : Finset β}
    (h : ∀ x, e x ∈ Q ↔ x ∈ P) : width Q = width P := by
  have hQ : Q = P.map e.toEquiv.toEmbedding := by
    ext y
    rw [Finset.mem_map_equiv, ← h (e.toEquiv.symm y)]
    simp
  rw [hQ, width_map_orderIso]

end Iso

/-- The order isomorphism `(Q_n × S) × Q_1 ≃o Q_{n+1} × S`, ((g, s), b) ↦
(cons b g, s), which peels the first cube coordinate into the second factor. -/
def peel (n : ℕ) (S : Type*) [PartialOrder S] :
    ((Fin n → Bool) × S) × Bool ≃o (Fin (n + 1) → Bool) × S where
  toFun x := (Fin.cons x.2 x.1.1, x.1.2)
  invFun y := ((Fin.tail y.1, y.2), y.1 0)
  left_inv x := by simp
  right_inv y := by simp
  map_rel_iff' := by
    rintro ⟨⟨g, s⟩, b⟩ ⟨⟨g', s'⟩, b'⟩
    simp only [Equiv.coe_fn_mk, Prod.mk_le_mk, Fin.cons_le_cons]
    tauto

/-- The order isomorphism `α ≃o α × Unit`. -/
def toProdUnit (α : Type*) [PartialOrder α] : α ≃o α × Unit where
  toFun a := (a, ())
  invFun x := x.1
  left_inv a := rfl
  right_inv x := rfl
  map_rel_iff' := by
    intro a b
    simp [Prod.mk_le_mk]

/-- **Theorem 2 of arXiv:2609.03087, generalised.**  For every finite partial
order `S` and every convex `P ⊆ Q_n = (Fin n → Bool)`,
`|P| · w(Q_n × S) ≤ 2^n · w(P × S)`.  The paper's Theorem 2 is the case
`S = Q_k` (see `theorem_2`); the induction on `n` peels one cube coordinate
into `S` and applies the Key Lemma with `R = Q_n × S`. -/
theorem general (n : ℕ) : ∀ (S : Type*) [PartialOrder S] [Fintype S]
    (P : Finset (Fin n → Bool)), (P : Set (Fin n → Bool)).OrdConnected →
    P.card * width (Finset.univ : Finset ((Fin n → Bool) × S)) ≤
      2 ^ n * width (P ×ˢ (Finset.univ : Finset S)) := by
  classical
  induction n with
  | zero =>
    intro S _ _ P _
    rcases P.eq_empty_or_nonempty with hP | ⟨y, hy⟩
    · simp [hP]
    · have hPu : P = Finset.univ := by
        ext x
        simp only [Finset.mem_univ, iff_true]
        rwa [Subsingleton.elim x y]
      have hone : Fintype.card (Fin 0 → Bool) = 1 := by simp
      rw [hPu, Finset.univ_product_univ, Finset.card_univ, hone, pow_zero]
  | succ n ih =>
    intro S _ _ P hP
    let P0 : Finset (Fin n → Bool) := Finset.univ.filter fun g => Fin.cons false g ∈ P
    let P1 : Finset (Fin n → Bool) := Finset.univ.filter fun g => Fin.cons true g ∈ P
    have hmem0 : ∀ g, g ∈ P0 ↔ Fin.cons false g ∈ P := by simp [P0]
    have hmem1 : ∀ g, g ∈ P1 ↔ Fin.cons true g ∈ P := by simp [P1]
    -- sections of a convex set are convex
    have hconv : ∀ b : Bool, (({g | Fin.cons b g ∈ P} : Set (Fin n → Bool))).OrdConnected := by
      intro b
      refine ⟨fun x hx y hy z hz => ?_⟩
      exact hP.out hx hy ⟨Fin.cons_le_cons.2 ⟨le_rfl, hz.1⟩, Fin.cons_le_cons.2 ⟨le_rfl, hz.2⟩⟩
    have hP0 : (P0 : Set (Fin n → Bool)).OrdConnected := by
      have : (P0 : Set (Fin n → Bool)) = {g | Fin.cons false g ∈ P} := by
        ext g; simp [hmem0]
      rw [this]; exact hconv false
    have hP1 : (P1 : Set (Fin n → Bool)).OrdConnected := by
      have : (P1 : Set (Fin n → Bool)) = {g | Fin.cons true g ∈ P} := by
        ext g; simp [hmem1]
      rw [this]; exact hconv true
    -- the cardinality splits along the first coordinate
    have hcard : P.card = P0.card + P1.card := by
      let e : (Fin n → Bool) × Bool ≃o (Fin (n + 1) → Bool) :=
        OrderIso.prodComm.trans (Fin.consOrderIso fun _ => Bool)
      have hPe : P = (twoLevel P0 P1).map e.toEquiv.toEmbedding := by
        ext f
        rw [Finset.mem_map_equiv]
        obtain ⟨b, g, rfl⟩ : ∃ b g, f = Fin.cons b g := ⟨f 0, Fin.tail f, (Fin.cons_self_tail f).symm⟩
        have he : e.toEquiv.symm (Fin.cons b g) = (g, b) := e.toEquiv.symm_apply_eq.2 rfl
        rw [he]
        cases b <;> simp [hmem0, hmem1]
      rw [hPe, Finset.card_map, card_twoLevel]
    -- the convexity property (*) for the sections, thickened by `S`
    have hstar : ∀ x ∈ P0 ×ˢ (Finset.univ : Finset S), ∀ y ∈ P1 ×ˢ (Finset.univ : Finset S),
        x ≤ y → x ∈ P1 ×ˢ (Finset.univ : Finset S) ∧ y ∈ P0 ×ˢ (Finset.univ : Finset S) := by
      rintro ⟨g, s⟩ hx ⟨g', s'⟩ hy hle
      simp only [Finset.mem_product, Finset.mem_univ, and_true, hmem0, hmem1] at hx hy ⊢
      have hgg : g ≤ g' := (Prod.mk_le_mk.1 hle).1
      refine ⟨hP.out hx hy ⟨Fin.cons_le_cons.2 ⟨by decide, le_rfl⟩,
        Fin.cons_le_cons.2 ⟨le_rfl, hgg⟩⟩, hP.out hx hy ⟨Fin.cons_le_cons.2 ⟨le_rfl, hgg⟩,
        Fin.cons_le_cons.2 ⟨by decide, le_rfl⟩⟩⟩
    have hkey := key_lemma_twoLevel _ _ hstar
    -- identify the three widths
    have hwP : width (twoLevel (P0 ×ˢ (Finset.univ : Finset S)) (P1 ×ˢ Finset.univ)) =
        width (P ×ˢ (Finset.univ : Finset S)) := by
      symm
      apply width_congr_orderIso (peel n S)
      rintro ⟨⟨g, s⟩, b⟩
      cases b <;> simp [peel, hmem0, hmem1]
    have hw : ∀ Pi : Finset (Fin n → Bool),
        width (twoLevel (Pi ×ˢ (Finset.univ : Finset S)) (Pi ×ˢ Finset.univ)) =
          width (Pi ×ˢ (Finset.univ : Finset (S × Bool))) := by
      intro Pi
      rw [twoLevel_self]
      apply width_congr_orderIso (OrderIso.prodAssoc _ _ _).symm
      rintro ⟨g, s, b⟩
      simp only [Finset.mem_product, Finset.mem_univ, and_true]
      exact Iff.rfl
    have hW : width (Finset.univ : Finset ((Fin n → Bool) × (S × Bool))) =
        width (Finset.univ : Finset ((Fin (n + 1) → Bool) × S)) := by
      symm
      apply width_congr_orderIso ((OrderIso.prodAssoc _ _ _).symm.trans (peel n S))
      intro x
      simp
    have ih0 := ih (S × Bool) P0 hP0
    have ih1 := ih (S × Bool) P1 hP1
    rw [hW, ← hw] at ih0 ih1
    rw [hwP] at hkey
    rw [hcard, Nat.add_mul, pow_succ]
    calc P0.card * width (Finset.univ : Finset ((Fin (n + 1) → Bool) × S)) +
          P1.card * width (Finset.univ : Finset ((Fin (n + 1) → Bool) × S))
        ≤ 2 ^ n * width (twoLevel (P0 ×ˢ (Finset.univ : Finset S)) (P0 ×ˢ Finset.univ)) +
          2 ^ n * width (twoLevel (P1 ×ˢ (Finset.univ : Finset S)) (P1 ×ˢ Finset.univ)) :=
          Nat.add_le_add ih0 ih1
      _ ≤ 2 ^ n * 2 * width (P ×ˢ (Finset.univ : Finset S)) := by
          rw [← Nat.mul_add, Nat.mul_assoc]
          exact Nat.mul_le_mul_left _ hkey


/-- The order isomorphism `Q_n × Q_k ≃o Q_{n+k}` given by `Fin.append`. -/
def cubeAppend (n k : ℕ) : (Fin n → Bool) × (Fin k → Bool) ≃o (Fin (n + k) → Bool) where
  toFun x := Fin.append x.1 x.2
  invFun f := (fun i => f (Fin.castAdd k i), fun j => f (Fin.natAdd n j))
  left_inv x := by
    ext i <;> simp
  right_inv f := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp
  map_rel_iff' := by
    rintro ⟨a, b⟩ ⟨c, d⟩
    simp only [Equiv.coe_fn_mk, Prod.mk_le_mk, Pi.le_def]
    constructor
    · intro h
      exact ⟨fun i => by simpa using h (Fin.castAdd k i),
        fun j => by simpa using h (Fin.natAdd n j)⟩
    · rintro ⟨h1, h2⟩ i
      exact Fin.addCases (fun i => by simpa using h1 i) (fun j => by simpa using h2 j) i

/-- **Theorem 2 of arXiv:2609.03087.**  For integers `n, k ≥ 0` and convex
`P ⊆ Q_n`, `w(P × Q_k) ≥ w(Q_{n+k}) |P| 2^{-n}`, stated without division as
`|P| · w(Q_{n+k}) ≤ 2^n · w(P × Q_k)`. -/
theorem theorem_2 (n k : ℕ) (P : Finset (Fin n → Bool))
    (hP : (P : Set (Fin n → Bool)).OrdConnected) :
    P.card * width (Finset.univ : Finset (Fin (n + k) → Bool)) ≤
      2 ^ n * width (P ×ˢ (Finset.univ : Finset (Fin k → Bool))) := by
  have h := general n (Fin k → Bool) P hP
  have hW : width (Finset.univ : Finset (Fin (n + k) → Bool)) =
      width (Finset.univ : Finset ((Fin n → Bool) × (Fin k → Bool))) :=
    width_congr_orderIso (cubeAppend n k) (fun x => by simp)
  rwa [hW]

/-- The order isomorphism between `Q_n` as the power set `Finset (Fin n)`
(inclusion) and `Q_n` as `Fin n → Bool` (pointwise order). -/
def finsetOrderIsoCube (n : ℕ) : Finset (Fin n) ≃o (Fin n → Bool) where
  toFun s i := decide (i ∈ s)
  invFun f := Finset.univ.filter fun i => f i = true
  left_inv s := by
    ext i
    simp
  right_inv f := by
    funext i
    simp
  map_rel_iff' := by
    intro s t
    simp only [Equiv.coe_fn_mk, Pi.le_def, Bool.le_iff_imp, decide_eq_true_eq]
    exact Iff.rfl

/-- **Daykin-Frankl conjecture, width form.**  For every convex
`P ⊆ Q_n = Finset (Fin n)`, `|P| · w(Q_n) ≤ 2^n · w(P)`, i.e.
`w(P)/|P| ≥ w(Q_n)/|Q_n|` (arXiv:2609.03087, Section 1). -/
theorem daykin_frankl_width (n : ℕ) (P : Finset (Finset (Fin n)))
    (hP : (P : Set (Finset (Fin n))).OrdConnected) :
    P.card * width (Finset.univ : Finset (Finset (Fin n))) ≤ 2 ^ n * width P := by
  let e := finsetOrderIsoCube n
  let P' : Finset (Fin n → Bool) := P.map e.toEquiv.toEmbedding
  have hmem : ∀ f, f ∈ P' ↔ e.symm f ∈ P := fun f => Finset.mem_map_equiv
  have hP' : (P' : Set (Fin n → Bool)).OrdConnected := by
    refine ⟨fun x hx y hy z hz => ?_⟩
    rw [Finset.mem_coe, hmem] at hx hy ⊢
    exact hP.out hx hy ⟨e.symm.monotone hz.1, e.symm.monotone hz.2⟩
  have h := general n Unit P' hP'
  have hc : P'.card = P.card := Finset.card_map _
  have hw1 : width (Finset.univ : Finset ((Fin n → Bool) × Unit)) =
      width (Finset.univ : Finset (Finset (Fin n))) :=
    width_congr_orderIso (e.trans (toProdUnit _)) (fun x => by simp)
  have hw2 : width (P' ×ˢ (Finset.univ : Finset Unit)) = width P := by
    apply width_congr_orderIso (e.trans (toProdUnit _))
    intro x
    simp [toProdUnit, hmem]
  rwa [hc, hw1, hw2] at h

/-- The width of `Q_n` is `C(n, ⌊n/2⌋)` (Sperner's theorem plus the middle
slice). -/
theorem width_univ_finset (n : ℕ) :
    width (Finset.univ : Finset (Finset (Fin n))) = n.choose (n / 2) := by
  apply le_antisymm
  · obtain ⟨A, -, hA, hAc⟩ := exists_antichain_card_eq_width (Finset.univ : Finset (Finset (Fin n)))
    rw [← hAc]
    simpa using hA.sperner
  · have hslice := le_width (Finset.subset_univ (Finset.powersetCard (n / 2) (Finset.univ : Finset (Fin n))))
      (Set.Sized.isAntichain (Set.sized_powersetCard _ _))
    simpa using hslice

/-- **Daykin-Frankl conjecture, binomial form** (Daykin-Frankl 1983; proof of
arXiv:2609.03087).  Every convex `P ⊆ Q_n` contains an antichain `A` with
`|A| ≥ |P| C(n, ⌊n/2⌋) 2^{-n}`, stated without division as
`|P| · C(n, ⌊n/2⌋) ≤ |A| · 2^n`. -/
theorem daykin_frankl (n : ℕ) (P : Finset (Finset (Fin n)))
    (hP : (P : Set (Finset (Fin n))).OrdConnected) :
    ∃ A ⊆ P, IsAntichain (· ⊆ ·) (A : Set (Finset (Fin n))) ∧
      P.card * n.choose (n / 2) ≤ A.card * 2 ^ n := by
  obtain ⟨A, hAP, hA, hAc⟩ := exists_antichain_card_eq_width P
  refine ⟨A, hAP, hA, ?_⟩
  have h := daykin_frankl_width n P hP
  rw [width_univ_finset, ← hAc] at h
  rwa [Nat.mul_comm A.card]


/-- The width of `P` is at most `|P|`. -/
theorem width_le_card {α : Type*} [PartialOrder α] (P : Finset α) : width P ≤ P.card := by
  obtain ⟨A, hAP, -, hAc⟩ := exists_antichain_card_eq_width P
  rw [← hAc]
  exact Finset.card_le_card hAP

/-- **Key Lemma (Lemma 3 of arXiv:2609.03087).**  Let `R` be a partial order
and `P = P_0 × {0} ∪ P_1 × {1} ⊆ R × Q_1` convex.  Then
`w(P_0 × Q_1) + w(P_1 × Q_1) ≤ 2 w(P)`. -/
theorem key_lemma {R : Type*} [PartialOrder R] [DecidableEq R] (P0 P1 : Finset R)
    (hP : ((P0 ×ˢ {false} ∪ P1 ×ˢ {true} : Finset (R × Bool)) : Set (R × Bool)).OrdConnected) :
    width (P0 ×ˢ (Finset.univ : Finset Bool)) + width (P1 ×ˢ (Finset.univ : Finset Bool)) ≤
      2 * width (P0 ×ˢ {false} ∪ P1 ×ˢ {true}) := by
  have hP' : (P0 ×ˢ {false} ∪ P1 ×ˢ {true} : Finset (R × Bool)) = twoLevel P0 P1 := by
    ext ⟨x, b⟩
    cases b <;> simp
  rw [hP'] at hP ⊢
  rw [← twoLevel_self, ← twoLevel_self]
  apply key_lemma_twoLevel
  intro x hx y hy hxy
  have hx' : ((x, false) : R × Bool) ∈ (twoLevel P0 P1 : Set (R × Bool)) :=
    mem_twoLevel_false.2 hx
  have hy' : ((y, true) : R × Bool) ∈ (twoLevel P0 P1 : Set (R × Bool)) :=
    mem_twoLevel_true.2 hy
  refine ⟨mem_twoLevel_true.1 (hP.out hx' hy' ⟨Prod.mk_le_mk.2 ⟨le_rfl, by decide⟩,
    Prod.mk_le_mk.2 ⟨hxy, le_rfl⟩⟩), mem_twoLevel_false.1 (hP.out hx' hy'
    ⟨Prod.mk_le_mk.2 ⟨hxy, le_rfl⟩, Prod.mk_le_mk.2 ⟨le_rfl, by decide⟩⟩)⟩

/-- **Daykin-Frankl conjecture, ratio form** as printed in arXiv:2609.03087:
for every nonempty convex `P ⊆ Q_n`, `w(Q_n)/|Q_n| ≤ w(P)/|P|` in `ℚ`. -/
theorem daykin_frankl_ratio (n : ℕ) (P : Finset (Finset (Fin n)))
    (hP : (P : Set (Finset (Fin n))).OrdConnected) (hne : P.Nonempty) :
    (width (Finset.univ : Finset (Finset (Fin n))) : ℚ) /
        (Finset.univ : Finset (Finset (Fin n))).card ≤ (width P : ℚ) / P.card := by
  have h := daykin_frankl_width n P hP
  have hU : (Finset.univ : Finset (Finset (Fin n))).card = 2 ^ n := by simp
  have hPpos : (0 : ℚ) < P.card := by exact_mod_cast hne.card_pos
  have hUpos : (0 : ℚ) < (Finset.univ : Finset (Finset (Fin n))).card := by
    rw [hU]; positivity
  rw [div_le_div_iff₀ hUpos hPpos, hU]
  have hq : ((P.card * width (Finset.univ : Finset (Finset (Fin n))) : ℕ) : ℚ) ≤
      ((2 ^ n * width P : ℕ) : ℚ) := by exact_mod_cast h
  push_cast at hq ⊢
  linarith

/-! ## Examples -/

example : twoLevel ({1} : Finset ℕ) {2} = {(1, false), (2, true)} := by decide
example : finsetOrderIsoCube 3 {0, 2} = ![true, false, true] := by decide
example : peel 1 Unit ((![false], ()), true) = (![true, false], ()) := by decide
example : cubeAppend 1 2 (![true], ![false, true]) = ![true, false, true] := by decide
example : width (Finset.univ : Finset Bool) = 1 := by
  apply le_antisymm
  · obtain ⟨A, -, hA, hAc⟩ := exists_antichain_card_eq_width (Finset.univ : Finset Bool)
    rw [← hAc, Finset.card_le_one]
    intro a ha b hb
    by_contra hne
    rcases le_total a b with hab | hba
    · exact hA ha hb hne hab
    · exact hA hb ha (Ne.symm hne) hba
  · simpa using le_width (Finset.subset_univ {false})
      (by simp : IsAntichain (· ≤ ·) (({false} : Finset Bool) : Set Bool))
example : width ({(false, true), (true, false)} : Finset (Bool × Bool)) = 2 := by
  apply le_antisymm (width_le_card _)
  refine le_width (A := {(false, true), (true, false)}) subset_rfl ?_
  intro a ha b hb hne hle
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all [Prod.mk_le_mk, Bool.le_iff_imp]
example : width (Finset.univ : Finset (Finset (Fin 4))) = 6 := width_univ_finset 4
example : ∃ A ⊆ Finset.Icc ({0} : Finset (Fin 3)) Finset.univ,
    IsAntichain (· ⊆ ·) (A : Set (Finset (Fin 3))) ∧
      (Finset.Icc ({0} : Finset (Fin 3)) Finset.univ).card * Nat.choose 3 (3 / 2) ≤ A.card * 2 ^ 3 :=
  daykin_frankl 3 _ (by rw [Finset.coe_Icc]; exact Set.ordConnected_Icc)
example : width (({()} : Finset Unit) ×ˢ (Finset.univ : Finset Bool)) +
    width (({()} : Finset Unit) ×ˢ (Finset.univ : Finset Bool)) ≤
      2 * width (({()} : Finset Unit) ×ˢ {false} ∪ ({()} : Finset Unit) ×ˢ {true}) :=
  key_lemma _ _ (by
    rw [show (({()} : Finset Unit) ×ˢ {false} ∪ ({()} : Finset Unit) ×ˢ {true}) = Finset.univ by
      decide, Finset.coe_univ]
    exact Set.ordConnected_univ)

end Candidates.DaykinFranklWilliamsConfirmation
