/-
# A175287: perimeter-magic triangles modulo rotation

OEIS A175287, R. J. Mathar (Mar 08 2025); closed form by Bruno Berselli
(Dec 03 2010).
For every natural `n`, `Σ_{i=0}^n ceil(i²/4)` counts the rotation orbits
of six positive entries on a hollow order-three triangle of magic sum `n+2`.
Entries need not be distinct. Rotations, but not reflections, are identified.
Orbit counting reduces the count to corner triples and fixed triangles.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A175287SumCeilPerimeter

/-! ## The sequence -/

/-- OEIS A175287: `a(n) = ∑_{i=0}^{n} ⌈i²/4⌉`. -/
noncomputable def a175287 (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), ⌈((i : ℚ) ^ 2 / 4)⌉₊

/-! ## Triangles, rotation, orbits, and the proof -/

/-- `⌈k/4⌉ = (k + 3) / 4` (natural division) for natural `k`. -/
theorem ceil_div_four (k : ℕ) : ⌈((k : ℚ) / 4)⌉₊ = (k + 3) / 4 := by
  apply le_antisymm
  · rw [Nat.ceil_le]
    rw [div_le_iff₀ (by norm_num)]
    exact_mod_cast (by omega : k ≤ (k + 3) / 4 * 4)
  · have h := Nat.le_ceil ((k : ℚ) / 4)
    rw [div_le_iff₀ (by norm_num)] at h
    have h' : k ≤ ⌈((k : ℚ) / 4)⌉₊ * 4 := by exact_mod_cast h
    omega

/-- `IsMagic s t`: the six entries `t 0, …, t 5` of an order-3 hollow triangle,
read counterclockwise with corners at positions `0, 2, 4` and edge-middles at
`1, 3, 5`, are all `≥ 1`, and each of the three edges sums to the magic sum `s`. -/
def IsMagic (s : ℕ) (t : Fin 6 → ℕ) : Prop :=
  (∀ i, 1 ≤ t i) ∧ t 0 + t 1 + t 2 = s ∧ t 2 + t 3 + t 4 = s ∧ t 4 + t 5 + t 0 = s

/-- `IsMagic s` is decidable (a finite conjunction of `ℕ` comparisons). -/
instance (s : ℕ) : DecidablePred (IsMagic s) := fun t => by unfold IsMagic; infer_instance

/-- The finite set of perimeter-magic order-3 triangles with magic sum `s`.
The box `[1, s]^6` loses nothing (`mem_triangles`). -/
def triangles (s : ℕ) : Finset (Fin 6 → ℕ) :=
  (Fintype.piFinset fun _ => Finset.Icc 1 s).filter (IsMagic s)

/-- Rotation of a triangle by one corner: every entry moves two positions. -/
def rot (t : Fin 6 → ℕ) : Fin 6 → ℕ := fun i => t (i + 2)

/-- The rotation orbit `{t, rot t, rot² t}` of a triangle (`rot³ = id`). -/
def orbit (t : Fin 6 → ℕ) : Finset (Fin 6 → ℕ) := {t, rot t, rot (rot t)}

/-- The number of perimeter-magic order-3 triangles with magic sum `s`,
counted up to rotation: the number of distinct rotation orbits. -/
def numTriangles (s : ℕ) : ℕ := ((triangles s).image orbit).card

/-- A statement about all of `Fin 6` is the conjunction of its six instances. -/
theorem forall_fin_six {p : Fin 6 → Prop} :
    (∀ i, p i) ↔ p 0 ∧ p 1 ∧ p 2 ∧ p 3 ∧ p 4 ∧ p 5 := by
  constructor
  · intro h; exact ⟨h 0, h 1, h 2, h 3, h 4, h 5⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩ i
    fin_cases i
    exacts [h0, h1, h2, h3, h4, h5]

/-- Membership in `triangles s` is exactly `IsMagic s`: the bounding box is harmless. -/
theorem mem_triangles {s : ℕ} {t : Fin 6 → ℕ} : t ∈ triangles s ↔ IsMagic s t := by
  unfold triangles
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun i => ?_, h⟩
    obtain ⟨hpos, h1, h2, h3⟩ := h
    rw [forall_fin_six] at hpos
    rw [Finset.mem_Icc]
    fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;> omega

/-- Rotating three times is the identity. -/
theorem rot_rot_rot (t : Fin 6 → ℕ) : rot (rot (rot t)) = t := by
  funext i
  simp only [rot]
  congr 1
  fin_cases i <;> rfl

/-- Rotation preserves perimeter-magic triangles. -/
theorem isMagic_rot {s : ℕ} {t : Fin 6 → ℕ} (h : IsMagic s t) : IsMagic s (rot t) := by
  obtain ⟨hpos, h1, h2, h3⟩ := h
  refine ⟨fun i => hpos _, ?_, ?_, ?_⟩ <;>
    simp only [rot, Fin.isValue, zero_add, Fin.reduceAdd] <;> omega

/-- A rotated triangle has the same orbit. -/
theorem orbit_rot (t : Fin 6 → ℕ) : orbit (rot t) = orbit t := by
  ext u
  simp only [orbit, Finset.mem_insert, Finset.mem_singleton, rot_rot_rot]
  tauto

/-- Two triangles have the same orbit iff one is a rotation of the other. -/
theorem orbit_eq_orbit_iff {t u : Fin 6 → ℕ} : orbit u = orbit t ↔ u ∈ orbit t := by
  constructor
  · intro h
    rw [← h]
    simp [orbit]
  · intro h
    simp only [orbit, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl
    · rfl
    · exact orbit_rot t
    · rw [orbit_rot, orbit_rot]

/-- Being rotation-invariant is constant along an orbit. -/
theorem rot_eq_self_iff_of_mem_orbit {t u : Fin 6 → ℕ} (h : u ∈ orbit t) :
    rot u = u ↔ rot t = t := by
  simp only [orbit, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl
  · rfl
  · constructor
    · intro hu
      have hu' := congrArg (fun v => rot (rot v)) hu
      simpa only [rot_rot_rot] using hu'
    · intro ht; rw [ht, ht]
  · constructor
    · intro hu
      rw [rot_rot_rot] at hu
      calc rot t = rot (rot (rot t)) := by rw [← hu]
        _ = t := rot_rot_rot t
    · intro ht; rw [ht, ht, ht]

/-- Weighting fixed triangles by `3` and the others by `1`, every orbit has
total weight `3` (it has one fixed element or three non-fixed ones). -/
theorem sum_orbit (t : Fin 6 → ℕ) :
    ∑ u ∈ orbit t, (if rot u = u then 3 else 1) = 3 := by
  by_cases ht : rot t = t
  · have ho : orbit t = {t} := by simp [orbit, ht]
    simp [ho, ht]
  · have h1 : rot (rot t) ≠ t := by
      intro h
      apply ht
      have h' := congrArg rot h
      rwa [rot_rot_rot, eq_comm] at h'
    have h2 : rot (rot t) ≠ rot t := by
      intro h
      apply h1
      have h' := congrArg rot h
      rw [rot_rot_rot] at h'
      exact h'.symm
    rw [Finset.sum_congr rfl (g := fun _ => 1)
      (fun u hu => by rw [if_neg ((rot_eq_self_iff_of_mem_orbit hu).not.mpr ht)])]
    have hne : t ≠ rot t := fun h => ht h.symm
    simp [orbit, hne, h1.symm, h2.symm]

/-- Orbit counting for the rotation: `3 · #orbits = #triangles + 2 · #fixed`. -/
theorem three_mul_numTriangles (s : ℕ) :
    3 * numTriangles s =
      (triangles s).card + 2 * ((triangles s).filter fun t => rot t = t).card := by
  have hclosed : ∀ t ∈ triangles s, orbit t ⊆ triangles s := by
    intro t ht u hu
    rw [mem_triangles] at ht ⊢
    simp only [orbit, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact ht
    · exact isMagic_rot ht
    · exact isMagic_rot (isMagic_rot ht)
  have hsum : ∑ b ∈ (triangles s).image orbit, (3 : ℕ) =
      ∑ t ∈ triangles s, (if rot t = t then 3 else 1) := by
    apply Finset.sum_image'
    intro t ht
    have hfib : (triangles s).filter (fun u => orbit u = orbit t) = orbit t := by
      ext u
      rw [Finset.mem_filter, orbit_eq_orbit_iff]
      exact ⟨fun h => h.2, fun h => ⟨hclosed t ht h, h⟩⟩
    rw [hfib, sum_orbit]
  rw [Finset.sum_const, smul_eq_mul] at hsum
  have hite : ∀ t : Fin 6 → ℕ,
      (if rot t = t then 3 else 1) = 1 + 2 * (if rot t = t then 1 else 0) := by
    intro t; split_ifs <;> rfl
  rw [Finset.sum_congr rfl (fun t _ => hite t), Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.card_filter, ← Finset.card_eq_sum_ones] at hsum
  unfold numTriangles
  omega

/-- Corner triples `(A, B, C)`, all in `[1, m]`, with pairwise sums `≤ m`. -/
def cornerTriples (m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc 1 m ×ˢ Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter
    fun p => p.1 + p.2.1 ≤ m ∧ p.2.1 + p.2.2 ≤ m ∧ p.2.2 + p.1 ≤ m

/-- Triangles with magic sum `m + 1` correspond to their corner triples. -/
theorem card_triangles (m : ℕ) : (triangles (m + 1)).card = (cornerTriples m).card := by
  apply Finset.card_nbij' (fun t => (t 0, t 2, t 4))
    (fun p => ![p.1, m + 1 - p.1 - p.2.1, p.2.1, m + 1 - p.2.1 - p.2.2, p.2.2,
      m + 1 - p.2.2 - p.1])
  · intro t ht
    rw [Finset.mem_coe, mem_triangles] at ht
    obtain ⟨hpos, h1, h2, h3⟩ := ht
    rw [forall_fin_six] at hpos
    simp only [cornerTriples, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc]
    omega
  · rintro ⟨a, b, c⟩ hp
    simp only [cornerTriples, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc] at hp
    rw [Finset.mem_coe, mem_triangles]
    refine ⟨forall_fin_six.mpr ?_, ?_, ?_, ?_⟩ <;>
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;>
      omega
  · intro t ht
    rw [Finset.mem_coe, mem_triangles] at ht
    obtain ⟨hpos, h1, h2, h3⟩ := ht
    funext k
    fin_cases k <;>
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;>
      omega
  · rintro ⟨a, b, c⟩ _
    simp

/-- A triangle is rotation-invariant iff its corners agree and its
edge-middles agree. -/
theorem rot_eq_self_iff (t : Fin 6 → ℕ) :
    rot t = t ↔ t 0 = t 2 ∧ t 2 = t 4 ∧ t 1 = t 3 ∧ t 3 = t 5 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    simp only [rot] at h0 h1 h2 h3
    exact ⟨h0.symm, h2.symm, h1.symm, h3.symm⟩
  · rintro ⟨h02, h24, h13, h35⟩
    funext i
    fin_cases i <;>
      simp only [rot, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
        zero_add, Fin.reduceAdd] <;>
      omega

/-- There are `⌊m/2⌋` rotation-invariant triangles with magic sum `m + 1`. -/
theorem card_fixed_triangles (m : ℕ) :
    ((triangles (m + 1)).filter fun t => rot t = t).card = m / 2 := by
  rw [show m / 2 = (Finset.Icc 1 (m / 2)).card by simp]
  apply Finset.card_nbij' (fun t => t 0)
    (fun a => ![a, m + 1 - 2 * a, a, m + 1 - 2 * a, a, m + 1 - 2 * a])
  · intro t ht
    rw [Finset.mem_coe, Finset.mem_filter, mem_triangles, rot_eq_self_iff] at ht
    obtain ⟨⟨hpos, h1, h2, h3⟩, h02, h24, h13, h35⟩ := ht
    rw [forall_fin_six] at hpos
    rw [Finset.mem_coe, Finset.mem_Icc]
    dsimp only
    omega
  · intro a ha
    rw [Finset.mem_coe, Finset.mem_Icc] at ha
    rw [Finset.mem_coe, Finset.mem_filter, mem_triangles, rot_eq_self_iff]
    refine ⟨⟨forall_fin_six.mpr ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, and_self] <;>
      omega
  · intro t ht
    rw [Finset.mem_coe, Finset.mem_filter, mem_triangles, rot_eq_self_iff] at ht
    obtain ⟨⟨hpos, h1, h2, h3⟩, h02, h24, h13, h35⟩ := ht
    funext k
    fin_cases k <;>
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;>
      omega
  · intro a _
    simp

/-- Pairs of naturals with sum `≤ m`. -/
def pairsLE (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter fun p => p.1 + p.2 ≤ m

/-- Triples of naturals with pairwise sums `≤ m`. -/
def triplesLE (m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (m + 1) ×ˢ Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter
    fun p => p.1 + p.2.1 ≤ m ∧ p.2.1 + p.2.2 ≤ m ∧ p.2.2 + p.1 ≤ m

/-- `2 · #{(a, b) : a + b ≤ m} = (m + 1)(m + 2)`. -/
theorem two_mul_card_pairsLE (m : ℕ) : 2 * (pairsLE m).card = (m + 1) * (m + 2) := by
  induction m with
  | zero => decide
  | succ m ih =>
    have hsplit := Finset.card_filter_add_card_filter_not (s := pairsLE (m + 1))
      (fun p : ℕ × ℕ => p.1 + p.2 ≤ m)
    have hlow : (pairsLE (m + 1)).filter (fun p : ℕ × ℕ => p.1 + p.2 ≤ m) = pairsLE m := by
      ext ⟨a, b⟩
      simp only [pairsLE, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    have htop : (pairsLE (m + 1)).filter (fun p : ℕ × ℕ => ¬ p.1 + p.2 ≤ m) =
        Finset.HasAntidiagonal.antidiagonal (m + 1) := by
      ext ⟨a, b⟩
      simp only [pairsLE, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        Finset.HasAntidiagonal.mem_antidiagonal]
      omega
    rw [hlow, htop, Finset.Nat.card_antidiagonal] at hsplit
    rw [← hsplit]
    linarith

/-- Subtracting one from each corner: positive triples with pairwise sums
`≤ m + 2` correspond to natural triples with pairwise sums `≤ m`. -/
theorem card_cornerTriples_add_two (m : ℕ) :
    (cornerTriples (m + 2)).card = (triplesLE m).card := by
  apply Finset.card_nbij' (fun p => (p.1 - 1, p.2.1 - 1, p.2.2 - 1))
    (fun p => (p.1 + 1, p.2.1 + 1, p.2.2 + 1))
  · rintro ⟨a, b, c⟩ hp
    simp only [cornerTriples, triplesLE, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc, Finset.mem_range] at hp ⊢
    omega
  · rintro ⟨a, b, c⟩ hp
    simp only [cornerTriples, triplesLE, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc, Finset.mem_range] at hp ⊢
    omega
  · rintro ⟨a, b, c⟩ hp
    simp only [cornerTriples, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc] at hp
    simp only [Prod.mk.injEq]
    omega
  · rintro ⟨a, b, c⟩ _
    simp

/-- Splitting natural triples by their first vanishing coordinate. -/
theorem card_triplesLE (k : ℕ) :
    (triplesLE (k + 2)).card = (cornerTriples (k + 2)).card + (pairsLE (k + 2)).card +
      (pairsLE (k + 1)).card + (pairsLE k).card := by
  have e1 : ((triplesLE (k + 2)).filter (fun p : ℕ × ℕ × ℕ => p.1 = 0)).card =
      (pairsLE (k + 2)).card := by
    apply Finset.card_nbij' (fun p => (p.2.1, p.2.2)) (fun p => (0, p.1, p.2))
    · rintro ⟨a, b, c⟩ hp
      simp only [triplesLE, pairsLE, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range] at hp ⊢
      omega
    · rintro ⟨b, c⟩ hp
      simp only [triplesLE, pairsLE, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range, and_true] at hp ⊢
      omega
    · rintro ⟨a, b, c⟩ hp
      simp only [triplesLE, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range] at hp
      simp only [Prod.mk.injEq, and_true]
      omega
    · rintro ⟨b, c⟩ _
      simp
  have e2 : (((triplesLE (k + 2)).filter (fun p : ℕ × ℕ × ℕ => ¬ p.1 = 0)).filter
      (fun p : ℕ × ℕ × ℕ => p.2.1 = 0)).card = (pairsLE (k + 1)).card := by
    apply Finset.card_nbij' (fun p => (p.1 - 1, p.2.2)) (fun p => (p.1 + 1, 0, p.2))
    · rintro ⟨a, b, c⟩ hp
      simp only [triplesLE, pairsLE, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range] at hp ⊢
      omega
    · rintro ⟨b, c⟩ hp
      simp only [triplesLE, pairsLE, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range, and_true] at hp ⊢
      omega
    · rintro ⟨a, b, c⟩ hp
      simp only [triplesLE, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range] at hp
      simp only [Prod.mk.injEq, and_true]
      omega
    · rintro ⟨b, c⟩ _
      simp
  have e3 : ((((triplesLE (k + 2)).filter (fun p : ℕ × ℕ × ℕ => ¬ p.1 = 0)).filter
      (fun p : ℕ × ℕ × ℕ => ¬ p.2.1 = 0)).filter (fun p : ℕ × ℕ × ℕ => p.2.2 = 0)).card =
      (pairsLE k).card := by
    apply Finset.card_nbij' (fun p => (p.1 - 1, p.2.1 - 1)) (fun p => (p.1 + 1, p.2 + 1, 0))
    · rintro ⟨a, b, c⟩ hp
      simp only [triplesLE, pairsLE, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range] at hp ⊢
      omega
    · rintro ⟨b, c⟩ hp
      simp only [triplesLE, pairsLE, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range, and_true] at hp ⊢
      omega
    · rintro ⟨a, b, c⟩ hp
      simp only [triplesLE, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range] at hp
      simp only [Prod.mk.injEq]
      omega
    · rintro ⟨b, c⟩ _
      simp
  have e4 : ((((triplesLE (k + 2)).filter (fun p : ℕ × ℕ × ℕ => ¬ p.1 = 0)).filter
      (fun p : ℕ × ℕ × ℕ => ¬ p.2.1 = 0)).filter (fun p : ℕ × ℕ × ℕ => ¬ p.2.2 = 0)) =
      cornerTriples (k + 2) := by
    ext ⟨a, b, c⟩
    simp only [triplesLE, cornerTriples, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range, Finset.mem_Icc]
    omega
  have h1 := Finset.card_filter_add_card_filter_not (s := triplesLE (k + 2))
    (fun p : ℕ × ℕ × ℕ => p.1 = 0)
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (triplesLE (k + 2)).filter (fun p : ℕ × ℕ × ℕ => ¬ p.1 = 0))
    (fun p : ℕ × ℕ × ℕ => p.2.1 = 0)
  have h3 := Finset.card_filter_add_card_filter_not
    (s := ((triplesLE (k + 2)).filter (fun p : ℕ × ℕ × ℕ => ¬ p.1 = 0)).filter
      (fun p : ℕ × ℕ × ℕ => ¬ p.2.1 = 0))
    (fun p : ℕ × ℕ × ℕ => p.2.2 = 0)
  rw [e1] at h1
  rw [e2] at h2
  rw [e3, e4] at h3
  omega

/-- The arithmetic step:
`6 (⌈(n+2)²/4⌉ + ⌈(n+3)²/4⌉) = (n+3)(n+4) + (n+2)(n+3) + (n+1)(n+2) + 4`. -/
theorem ceil_step_identity (n : ℕ) :
    2 * (3 * (((n + 2) ^ 2 + 3) / 4 + ((n + 3) ^ 2 + 3) / 4)) =
      (n + 3) * (n + 4) + (n + 2) * (n + 3) + (n + 1) * (n + 2) + 4 := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
  · have e1 : (2 * j + 2) ^ 2 + 3 = 4 * (j * j + 2 * j + 1) + 3 := by ring
    have e2 : (2 * j + 3) ^ 2 + 3 = 4 * (j * j + 3 * j + 3) := by ring
    rw [e1, e2]
    ring_nf
    omega
  · have e1 : (2 * j + 1 + 2) ^ 2 + 3 = 4 * (j * j + 3 * j + 3) := by ring
    have e2 : (2 * j + 1 + 3) ^ 2 + 3 = 4 * (j * j + 4 * j + 4) + 3 := by ring
    rw [e1, e2]
    ring_nf
    omega

/-- Two consecutive instances of
`#cornerTriples (n + 1) + 2⌊(n + 1)/2⌋ = 3 ∑_{i ≤ n} ⌈i²/4⌉`, by two-step induction. -/
theorem card_cornerTriples_formula_aux (n : ℕ) :
    (cornerTriples (n + 2)).card + 2 * ((n + 2) / 2) =
        3 * ∑ i ∈ Finset.range (n + 2), (i ^ 2 + 3) / 4 ∧
      (cornerTriples (n + 3)).card + 2 * ((n + 3) / 2) =
        3 * ∑ i ∈ Finset.range (n + 3), (i ^ 2 + 3) / 4 := by
  induction n with
  | zero => decide
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have hrec : (cornerTriples (n + 4)).card = (cornerTriples (n + 2)).card +
        (pairsLE (n + 2)).card + (pairsLE (n + 1)).card + (pairsLE n).card := by
      rw [card_cornerTriples_add_two, card_triplesLE]
    have hp2 := two_mul_card_pairsLE (n + 2)
    have hp1 := two_mul_card_pairsLE (n + 1)
    have hp0 := two_mul_card_pairsLE n
    have harith := ceil_step_identity n
    have hold := ih.1
    rw [show n + 1 + 3 = n + 4 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      hrec]
    have hdiv : (n + 4) / 2 = (n + 2) / 2 + 1 := by omega
    rw [hdiv]
    nlinarith

/-- `#cornerTriples (n + 1) + 2⌊(n + 1)/2⌋ = 3 ∑_{i ≤ n} ⌈i²/4⌉` for every `n`. -/
theorem card_cornerTriples_formula (n : ℕ) :
    (cornerTriples (n + 1)).card + 2 * ((n + 1) / 2) =
      3 * ∑ i ∈ Finset.range (n + 1), (i ^ 2 + 3) / 4 := by
  cases n with
  | zero => decide
  | succ n => exact (card_cornerTriples_formula_aux n).1

/-- The A175287 terms in natural-number form: `⌈i²/4⌉ = (i² + 3) / 4`. -/
theorem a175287_eq (n : ℕ) :
    a175287 n = ∑ i ∈ Finset.range (n + 1), (i ^ 2 + 3) / 4 := by
  unfold a175287
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← ceil_div_four]
  push_cast
  rfl

/-! ## Examples -/

-- The definition of `a175287` against the DATA line `0, 1, 2, 5, 9, 16, 25, 38`.
example : (List.range 8).map a175287 = [0, 1, 2, 5, 9, 16, 25, 38] := by
  rw [show a175287 = fun n => ∑ i ∈ Finset.range (n + 1), (i ^ 2 + 3) / 4 from
    funext a175287_eq]
  decide

-- Mathar's examples: magic sum 3 has the triangle `1 1 1 1 1 1`; magic sum 4 has
-- `1 1 2 1 1 2` and `1 2 1 2 1 2`, which lie in different rotation orbits.
example : IsMagic 3 ![1, 1, 1, 1, 1, 1] := by decide
example : IsMagic 4 ![1, 1, 2, 1, 1, 2] ∧ IsMagic 4 ![1, 2, 1, 2, 1, 2] := by decide
example : orbit ![1, 1, 2, 1, 1, 2] ≠ orbit ![1, 2, 1, 2, 1, 2] := by decide

-- The orbit count against the first terms: magic sums 2, 3, 4 give 0, 1, 2.
example : numTriangles 2 = 0 := by decide +kernel
example : numTriangles 3 = 1 := by decide +kernel
example : numTriangles 4 = 2 := by decide +kernel

/-! ## The conjecture -/

/-- Mathar's A175287 identity: the rotation orbits of positive six-tuples
`(A,x,B,y,C,z)` with `A+x+B = B+y+C = C+z+A = n+2` are counted by
`Σ_{i=0}^n ceil(i²/4)`. Corners are `A,B,C`; repeated entries are allowed
and reflections are not identified. -/
theorem perimeterMagic_count_eq_a175287 (n : ℕ) :
    numTriangles (n + 2) = a175287 n := by
  have h3 := three_mul_numTriangles (n + 2)
  rw [card_triangles (n + 1), card_fixed_triangles (n + 1),
    card_cornerTriples_formula n] at h3
  rw [a175287_eq]
  omega

end Candidates.A175287SumCeilPerimeter
