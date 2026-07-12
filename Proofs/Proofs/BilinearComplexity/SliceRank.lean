/-
  BilinearComplexity/SliceRank — slice rank of rectangular 3-tensors:
  the definition layer and the elementary structural results.

  Slice rank is the hinge invariant of the barrier literature
  (BCCGU Cor 2.11, `Formalize/arXiv-1712-02302.md`): it is how that
  literature formally rules out group families as routes to ω = 2, and
  it is the prototype "leave the degree-2 paradigm" invariant. A slice
  is a tensor of the form (a vector in one mode) ⊗ (a matrix in the
  other two); the slice rank is the least number of slices summing to
  `T`. This file mirrors `Basic.lean`'s rank layer exactly (same `sInf`
  pattern, same order API), building on the `Tensor`/`RankLE`/`rank`
  API defined there.

    · `IsSlice1/2/3 T`    — `T` is a single slice supported on mode 1,
                            2, or 3 (`T i j l = f i * M j l`, and cyclic
                            variants).
    · `SliceRankLE T r`   — `T` is a sum of at most `r` slices, in the
                            "three parts" shape `r₁ + r₂ + r₃ ≤ r`
                            (`SliceRankLE.exists_parts` /
                            `sliceRankLE_of_parts` are the binding
                            destructor/constructor pair). Comes with
                            `SliceRankLE.mono` and the three mode
                            totalities `sliceRankLE_left/mid/right`.
    · `sliceRank T`       — the least such `r` (`sInf`; total by
                            `sliceRankLE_left`), with the order API
                            `sliceRankLE_sliceRank`,
                            `sliceRank_le_of_sliceRankLE`,
                            `sliceRankLE_of_sliceRank_le`,
                            `sliceRank_le_iff`, the min-over-modes bound
                            `sliceRank_le_left/mid/right`, and
                            `sliceRank_zero`/`sliceRank_eq_zero_iff`.
    · `RankLE.sliceRankLE` / `sliceRank_le_rank` — a triad is a mode-1
                            slice, so `sliceRank T ≤ rank T`.
    · `diag w`            — the diagonal tensor `⟨w⟩`, with the upper
                            bound `sliceRank_diag_le`: its slice rank is
                            at most the number of nonzero diagonal
                            entries. (The matching lower bound — Tao's
                            diagonal lemma over a field — is card Sr2.)

  Everything is over `CommSemiring k`; the diagonal-support lemmas take
  `[DecidableEq k]` so the support finset is genuinely decidable.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Lattice
import Proofs.BilinearComplexity.Basic
import Proofs.BilinearComplexity.RankCalculus

namespace BilinearComplexity

section SliceRank

variable {k : Type*} [CommSemiring k] {a b c : ℕ}

/-! ## 1. Slice predicates -/

/-- `IsSlice1 T` : `T` is a single slice supported on mode 1, i.e. a
vector `f` in mode 1 times a matrix `M` in modes 2, 3. -/
def IsSlice1 (T : Tensor k a b c) : Prop :=
  ∃ (f : Fin a → k) (M : Fin b → Fin c → k), ∀ i j l, T i j l = f i * M j l

/-- `IsSlice2 T` : `T` is a single slice supported on mode 2. -/
def IsSlice2 (T : Tensor k a b c) : Prop :=
  ∃ (g : Fin b → k) (N : Fin a → Fin c → k), ∀ i j l, T i j l = g j * N i l

/-- `IsSlice3 T` : `T` is a single slice supported on mode 3. -/
def IsSlice3 (T : Tensor k a b c) : Prop :=
  ∃ (e : Fin c → k) (P : Fin a → Fin b → k), ∀ i j l, T i j l = e l * P i j

/-! ## 2. The slice-rank-≤ r predicate -/

/-- `SliceRankLE T r` : the tensor `T` is a sum of at most `r` slices —
`r₁` mode-1 slices, `r₂` mode-2 slices, `r₃` mode-3 slices, with
`r₁ + r₂ + r₃ ≤ r`. This "three parts" primitive is the shape of the
binding destructor `SliceRankLE.exists_parts`; monotonicity is
immediate from it. -/
def SliceRankLE (T : Tensor k a b c) (r : ℕ) : Prop :=
  ∃ (r₁ r₂ r₃ : ℕ), r₁ + r₂ + r₃ ≤ r ∧
    ∃ (f : Fin r₁ → Fin a → k) (M : Fin r₁ → Fin b → Fin c → k)
      (g : Fin r₂ → Fin b → k) (N : Fin r₂ → Fin a → Fin c → k)
      (e : Fin r₃ → Fin c → k) (P : Fin r₃ → Fin a → Fin b → k),
      ∀ i j l, T i j l =
        (∑ s, f s i * M s j l) + (∑ s, g s j * N s i l) + (∑ s, e s l * P s i j)

/-- Binding destructor (Sr2's interface): a slice-rank-≤ r decomposition
splits into `r₁` mode-1, `r₂` mode-2, `r₃` mode-3 slice families with
`r₁ + r₂ + r₃ ≤ r`. Definitional for the "three parts" primitive. -/
theorem SliceRankLE.exists_parts {T : Tensor k a b c} {r : ℕ}
    (h : SliceRankLE T r) :
    ∃ (r₁ r₂ r₃ : ℕ), r₁ + r₂ + r₃ ≤ r ∧
      ∃ (f : Fin r₁ → Fin a → k) (M : Fin r₁ → Fin b → Fin c → k)
        (g : Fin r₂ → Fin b → k) (N : Fin r₂ → Fin a → Fin c → k)
        (e : Fin r₃ → Fin c → k) (P : Fin r₃ → Fin a → Fin b → k),
        ∀ i j l, T i j l =
          (∑ s, f s i * M s j l) + (∑ s, g s j * N s i l) + (∑ s, e s l * P s i j) :=
  h

/-- Binding constructor (Sr2's interface): three slice families with
`r₁ + r₂ + r₃ ≤ r` assemble into a slice-rank-≤ r decomposition. -/
theorem sliceRankLE_of_parts {T : Tensor k a b c} {r r₁ r₂ r₃ : ℕ}
    (hr : r₁ + r₂ + r₃ ≤ r)
    (f : Fin r₁ → Fin a → k) (M : Fin r₁ → Fin b → Fin c → k)
    (g : Fin r₂ → Fin b → k) (N : Fin r₂ → Fin a → Fin c → k)
    (e : Fin r₃ → Fin c → k) (P : Fin r₃ → Fin a → Fin b → k)
    (hT : ∀ i j l, T i j l =
      (∑ s, f s i * M s j l) + (∑ s, g s j * N s i l) + (∑ s, e s l * P s i j)) :
    SliceRankLE T r :=
  ⟨r₁, r₂, r₃, hr, f, M, g, N, e, P, hT⟩

/-- Slice rank is monotone in `r`: the same parts still fit under a
larger budget. -/
theorem SliceRankLE.mono {T : Tensor k a b c} {r r' : ℕ} (h : SliceRankLE T r)
    (hrr' : r ≤ r') : SliceRankLE T r' := by
  obtain ⟨r₁, r₂, r₃, hr, rest⟩ := h
  exact ⟨r₁, r₂, r₃, le_trans hr hrr', rest⟩

/-- Mode-1 totality: every tensor is a sum of `a` mode-1 slices
`e_i ⊗ (T i · ·)`. -/
theorem sliceRankLE_left (T : Tensor k a b c) : SliceRankLE T a := by
  refine ⟨a, 0, 0, by omega, fun s i => if s = i then 1 else 0, fun s j l => T s j l,
    Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, ?_⟩
  intro i j l
  simp [ite_mul]

/-- Mode-2 totality: every tensor is a sum of `b` mode-2 slices. -/
theorem sliceRankLE_mid (T : Tensor k a b c) : SliceRankLE T b := by
  refine ⟨0, b, 0, by omega, Fin.elim0, Fin.elim0, fun s j => if s = j then 1 else 0,
    fun s i l => T i s l, Fin.elim0, Fin.elim0, ?_⟩
  intro i j l
  simp [ite_mul]

/-- Mode-3 totality: every tensor is a sum of `c` mode-3 slices. -/
theorem sliceRankLE_right (T : Tensor k a b c) : SliceRankLE T c := by
  refine ⟨0, 0, c, by omega, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0,
    fun s l => if s = l then 1 else 0, fun s i j => T i j s, ?_⟩
  intro i j l
  simp [ite_mul]

/-! ## 3. Slice rank -/

/-- The slice rank of a tensor: the least `r` admitting a slice-rank-≤ r
decomposition. The defining set is nonempty by `sliceRankLE_left`, so
the `sInf` is attained (`sliceRankLE_sliceRank`). -/
noncomputable def sliceRank (T : Tensor k a b c) : ℕ :=
  sInf {r | SliceRankLE T r}

/-- The slice rank is attained. -/
theorem sliceRankLE_sliceRank (T : Tensor k a b c) : SliceRankLE T (sliceRank T) :=
  Nat.sInf_mem (s := {r | SliceRankLE T r}) ⟨a, sliceRankLE_left T⟩

theorem sliceRank_le_of_sliceRankLE {T : Tensor k a b c} {r : ℕ}
    (h : SliceRankLE T r) : sliceRank T ≤ r :=
  Nat.sInf_le h

theorem sliceRankLE_of_sliceRank_le {T : Tensor k a b c} {r : ℕ}
    (h : sliceRank T ≤ r) : SliceRankLE T r :=
  (sliceRankLE_sliceRank T).mono h

theorem sliceRank_le_iff {T : Tensor k a b c} {r : ℕ} :
    sliceRank T ≤ r ↔ SliceRankLE T r :=
  ⟨sliceRankLE_of_sliceRank_le, sliceRank_le_of_sliceRankLE⟩

/-- Min-over-modes bound (mode 1): `sliceRank T ≤ a`. -/
theorem sliceRank_le_left (T : Tensor k a b c) : sliceRank T ≤ a :=
  sliceRank_le_of_sliceRankLE (sliceRankLE_left T)

/-- Min-over-modes bound (mode 2): `sliceRank T ≤ b`. -/
theorem sliceRank_le_mid (T : Tensor k a b c) : sliceRank T ≤ b :=
  sliceRank_le_of_sliceRankLE (sliceRankLE_mid T)

/-- Min-over-modes bound (mode 3): `sliceRank T ≤ c`. -/
theorem sliceRank_le_right (T : Tensor k a b c) : sliceRank T ≤ c :=
  sliceRank_le_of_sliceRankLE (sliceRankLE_right T)

/-- Slice rank ≤ 0 means the tensor is zero (the empty sum of slices). -/
theorem sliceRankLE_zero_iff {T : Tensor k a b c} : SliceRankLE T 0 ↔ T = 0 := by
  constructor
  · rintro ⟨r₁, r₂, r₃, hr, f, M, g, N, e, P, hT⟩
    obtain ⟨rfl, rfl, rfl⟩ : r₁ = 0 ∧ r₂ = 0 ∧ r₃ = 0 := by omega
    funext i j l
    simpa using hT i j l
  · rintro rfl
    exact ⟨0, 0, 0, by omega, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0,
      Fin.elim0, by intro i j l; simp⟩

theorem sliceRank_zero : sliceRank (0 : Tensor k a b c) = 0 :=
  Nat.le_zero.mp (sliceRank_le_of_sliceRankLE (sliceRankLE_zero_iff.mpr rfl))

theorem sliceRank_eq_zero_iff {T : Tensor k a b c} : sliceRank T = 0 ↔ T = 0 := by
  rw [← Nat.le_zero, sliceRank_le_iff, sliceRankLE_zero_iff]

/-! ## 4. Slice rank ≤ rank -/

/-- A rank-one triad `u ⊗ v ⊗ w` is a mode-1 slice (`f := u`,
`M := v ⊗ w`), so any `r`-triad decomposition is a slice-rank-≤ r
decomposition. -/
theorem RankLE.sliceRankLE {T : Tensor k a b c} {r : ℕ} (h : RankLE T r) :
    SliceRankLE T r := by
  obtain ⟨u, v, w, hT⟩ := h
  refine ⟨r, 0, 0, by omega, u, fun s j l => v s j * w s l,
    Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, ?_⟩
  intro i j l
  simp only [hT, Fin.sum_univ_zero, add_zero, mul_assoc]

/-- Renamed form of `RankLE.sliceRankLE`. -/
theorem sliceRankLE_of_rankLE {T : Tensor k a b c} {r : ℕ} (h : RankLE T r) :
    SliceRankLE T r :=
  h.sliceRankLE

/-- Slice rank never exceeds rank. -/
theorem sliceRank_le_rank (T : Tensor k a b c) : sliceRank T ≤ rank T :=
  sliceRank_le_of_sliceRankLE (rankLE_rank T).sliceRankLE

/-! ## 5. The diagonal tensor and its slice-rank upper bound -/

/-- The diagonal tensor `⟨w⟩` of shape `n × n × n`: `w i` on the main
diagonal `i = j = l`, zero elsewhere. -/
def diag {n : ℕ} (w : Fin n → k) : Tensor k n n n :=
  fun i j l => if i = j ∧ j = l then w i else 0

/-- Slice-rank upper bound for the diagonal tensor: `⟨w⟩` is a sum of
one mode-1 slice per nonzero diagonal entry, indexed by the support of
`w` reindexed through `Finset.equivFin`. Off-support diagonal entries
are zero, so the sum reproduces `⟨w⟩`. -/
theorem sliceRankLE_diag [DecidableEq k] {n : ℕ} (w : Fin n → k) :
    SliceRankLE (diag w) ((Finset.univ.filter fun i => w i ≠ 0).card) := by
  set s : Finset (Fin n) := Finset.univ.filter (fun i => w i ≠ 0) with hs
  refine ⟨s.card, 0, 0, by omega,
    fun t i => if (s.equivFin.symm t : Fin n) = i then (1 : k) else 0,
    fun t j l =>
      if (s.equivFin.symm t : Fin n) = j ∧ j = l then w (s.equivFin.symm t) else 0,
    Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, ?_⟩
  intro i j l
  rw [Fin.sum_univ_zero, Fin.sum_univ_zero, add_zero, add_zero]
  -- reindex the sum over `Fin s.card` back to a sum over the support `s`
  have ereindex :
      (∑ t : Fin s.card,
        (if (s.equivFin.symm t : Fin n) = i then (1 : k) else 0) *
          (if (s.equivFin.symm t : Fin n) = j ∧ j = l then w (s.equivFin.symm t) else 0))
        = ∑ x : {x // x ∈ s},
          (if (x : Fin n) = i then (1 : k) else 0) *
            (if (x : Fin n) = j ∧ j = l then w (x : Fin n) else 0) :=
    Equiv.sum_comp s.equivFin.symm
      (fun x : {x // x ∈ s} =>
        (if (x : Fin n) = i then (1 : k) else 0) *
          (if (x : Fin n) = j ∧ j = l then w (x : Fin n) else 0))
  rw [ereindex, Finset.sum_coe_sort s
    (fun x => (if x = i then (1 : k) else 0) * (if x = j ∧ j = l then w x else 0))]
  -- off-support terms vanish, so extend the sum to all of `Fin n`
  rw [Finset.sum_subset (Finset.subset_univ s)]
  · -- compute the diagonal sum over `Fin n`
    simp only [diag, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · intro x _ hx
    have hwx : w x = 0 := by
      by_contra hne
      exact hx (by rw [hs]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hne⟩)
    simp [hwx]

/-- Slice-rank upper bound for the diagonal tensor: `sliceRank ⟨w⟩` is
at most the number of nonzero diagonal entries. -/
theorem sliceRank_diag_le [DecidableEq k] {n : ℕ} (w : Fin n → k) :
    sliceRank (diag w) ≤ (Finset.univ.filter fun i => w i ≠ 0).card :=
  sliceRank_le_of_sliceRankLE (sliceRankLE_diag w)

/-! ## 6. Cyclic rotation -/

/-- Slice rank does not increase under cyclic rotation: a mode-1 slice
of `T` is a mode-3 slice of `cyc T`, a mode-2 slice a mode-1 slice, a
mode-3 slice a mode-2 slice — the three parts rotate. -/
theorem SliceRankLE.cyc {T : Tensor k a b c} {r : ℕ} (h : SliceRankLE T r) :
    SliceRankLE (cyc T) r := by
  obtain ⟨r₁, r₂, r₃, hr, f, M, g, N, e, P, hT⟩ := h
  refine ⟨r₂, r₃, r₁, by omega, g, fun s L I => N s I L, e, fun s J I => P s I J,
    f, fun s J L => M s J L, ?_⟩
  intro J L I
  dsimp only [cyc_apply]
  rw [hT I J L]
  ring

/-- Slice rank-≤ is invariant under cyclic rotation (rotate twice more
to come back around, using `cyc³ = id`). -/
theorem sliceRankLE_cyc_iff {T : Tensor k a b c} {r : ℕ} :
    SliceRankLE (cyc T) r ↔ SliceRankLE T r :=
  ⟨fun h => h.cyc.cyc, SliceRankLE.cyc⟩

/-- Slice rank is invariant under cyclic rotation. -/
@[simp] theorem sliceRank_cyc (T : Tensor k a b c) : sliceRank (cyc T) = sliceRank T :=
  le_antisymm (sliceRank_le_of_sliceRankLE (sliceRankLE_sliceRank T).cyc)
    (sliceRank_le_of_sliceRankLE ((sliceRankLE_sliceRank (cyc T)).cyc.cyc))

end SliceRank

end BilinearComplexity
