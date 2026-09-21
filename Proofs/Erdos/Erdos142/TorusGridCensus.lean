/-
  Erdős Problem #142 — discrete census of the torus grid.

  The torus grid `torusGrid ε q` is the set of residues of `ZMod q × ZMod q`
  whose canonical lift lies in `torusT ε`.  This module transports that finset
  to the pair grid `Fin q × Fin q` (via the least-nonnegative representatives),
  identifies the three discrete pieces `T1`, `T2`, `T3` as explicit filtered
  finsets, and proves their pairwise disjointness and containment in the grid.

  The discrete conditions are obtained by clearing denominators, e.g. for
  `x = i/q`, `y = j/q`:
  `2/3 < x + y ↔ 2*q < 3*(i+j)` and `x + y ≤ 7/6 ↔ 6*(i+j) ≤ 7*q`.
  No `ε` enters the `T1` piece.

  No sorry, no new axioms.

  **Scope actually delivered.**  This module provides the pair-grid transport
  `(torusGrid ε q).card = (pairGood ε q).card`, the three exact discrete pieces
  `censusT1`/`censusT2`/`censusT3` together with their containment in `pairGood`
  and pairwise disjointness, and hence the lower bound
  `#T1 + #T2 + #T3 ≤ (torusGrid ε q).card`.

  **Scope delivered.**  Pair-grid transport `(torusGrid ε q).card = (pairGood ε q).card`;
  the three exact discrete pieces `censusT1`/`censusT2`/`censusT3` with containment in
  `pairGood` and pairwise disjointness, hence `#T1 + #T2 + #T3 ≤ (torusGrid ε q).card`;
  a natural lattice-triangle count (`tri`/`triNum`/`Pr`, `card_tri_ge`) with the
  half-triangle rectangle bound `halfTri_card_le_sq`; and the three census ledgers
  with explicit coefficients `C₁ = C₂ = C₃ = 1`,
  `#T1 ≥ q^2*(7/36) - q` (`censusT1_card_lower`),
  `#T2 ≥ q^2*(5/96 - 7*ε/24 + 3*ε^2/8) - q` (`censusT2_card_lower`),
  `q^2*(13/288 - 5*ε/24 + ε^2/8) - q ≤ #T3` (`censusT3_card_lower`).
  Summing them gives the assembled bound
  `q^2*(7/24 - ε/2 + ε^2/2) - 3q ≤ #torusGrid` (`torusGrid_card_lower_eps`), with
  the reciprocal form `torusGrid_card_lower_inv` for `ε = e⁻¹`, `e ≥ 6`.

  **Still open.**  Nothing in this module; the `T1`/`T2`/`T3`/assembly target is complete. -/

import Erdos.Erdos142.TorusGrid
import Erdos.Erdos142.TorusProductSlicing

set_option autoImplicit false

namespace Erdos142

/-- The least-nonnegative representative of a residue, packaged as an element of
`Fin q`. -/
def valFin {q : ℕ} [NeZero q] (a : ZMod q) : Fin q := ⟨a.val, ZMod.val_lt a⟩

@[simp]
theorem valFin_val {q : ℕ} [NeZero q] (a : ZMod q) : (valFin a : ℕ) = a.val := rfl

@[simp]
theorem natCast_valFin {q : ℕ} [NeZero q] (a : ZMod q) :
    ((valFin a : ℕ) : ZMod q) = a := ZMod.natCast_zmod_val a

theorem valFin_injective {q : ℕ} [NeZero q] :
    Function.Injective (fun a : ZMod q => valFin a) := by
  intro a b h
  have : a.val = b.val := congrArg Fin.val h
  exact ZMod.val_injective q this

@[simp]
theorem valFin_natCast {q : ℕ} [NeZero q] (i : Fin q) :
    valFin ((i : ℕ) : ZMod q) = i := by
  apply Fin.ext
  simp [valFin, ZMod.val_natCast_of_lt i.isLt]

/-- The **pair grid** representing `torusGrid ε q` as lattice points
`(i, j) ∈ Fin q × Fin q` with `x = i/q`, `y = j/q`. -/
noncomputable def pairGood (ε : ℝ) (q : ℕ) : Finset (Fin q × Fin q) := by
  classical
  exact Finset.univ.filter fun p =>
    torusT ε (((p.1 : ℕ) : ℝ) / q, ((p.2 : ℕ) : ℝ) / q)

/-- **Pair-grid transport.**  The torus grid has the same cardinality as the
pair grid of lifted lattice points. -/
theorem torusGrid_card_eq_pairGood (ε : ℝ) (q : ℕ) [NeZero q] :
    (torusGrid ε q).card = (pairGood ε q).card := by
  classical
  refine Finset.card_bij (fun x _ => (valFin x.1, valFin x.2)) ?_ ?_ ?_
  · intro x hx
    simp only [pairGood, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    simpa [torusLift, cyclicLift, valFin] using hx
  · intro x1 _ x2 _ h
    have h1 : valFin x1.1 = valFin x2.1 := congrArg Prod.fst h
    have h2 : valFin x1.2 = valFin x2.2 := congrArg Prod.snd h
    exact Prod.ext (valFin_injective h1) (valFin_injective h2)
  · intro p hp
    refine ⟨(((p.1 : ℕ) : ZMod q), ((p.2 : ℕ) : ZMod q)), ?_, ?_⟩
    · simp only [torusGrid, Finset.mem_filter, Finset.mem_univ, true_and]
      have hp' : torusT ε (((p.1 : ℕ) : ℝ) / q, ((p.2 : ℕ) : ℝ) / q) := by
        simpa only [pairGood, Finset.mem_filter, Finset.mem_univ, true_and] using hp
      have h1 : (((p.1 : ℕ) : ZMod q).val) = (p.1 : ℕ) := ZMod.val_natCast_of_lt p.1.isLt
      have h2 : (((p.2 : ℕ) : ZMod q).val) = (p.2 : ℕ) := ZMod.val_natCast_of_lt p.2.isLt
      simpa [torusLift, cyclicLift, valFin, h1, h2] using hp'
    · ext <;> simp

/-- **Discrete low-sum piece `T1`.**  The `ε`-free conditions
`x ≥ 1/2`, `2/3 < x + y ≤ 7/6`. -/
noncomputable def censusT1 (q : ℕ) : Finset (Fin q × Fin q) := by
  classical
  exact Finset.univ.filter fun p =>
    q ≤ 2 * (p.1 : ℕ) ∧
      2 * q < 3 * ((p.1 : ℕ) + (p.2 : ℕ)) ∧
        6 * ((p.1 : ℕ) + (p.2 : ℕ)) ≤ 7 * q

/-- **Discrete high-sum piece `T2`.**  `x ≥ 1/2`, `y < 1/2`, and
`7/6 + ε ≤ x + y ≤ 17/12 + ε/2`. -/
noncomputable def censusT2 (ε : ℝ) (q : ℕ) : Finset (Fin q × Fin q) := by
  classical
  exact Finset.univ.filter fun p =>
    q ≤ 2 * (p.1 : ℕ) ∧
      2 * (p.2 : ℕ) < q ∧
        (7 / 6 + ε) * q ≤ (((p.1 : ℕ) + (p.2 : ℕ) : ℕ) : ℝ) ∧
          (((p.1 : ℕ) + (p.2 : ℕ) : ℕ) : ℝ) ≤ (17 / 12 + ε / 2) * q

/-- **Discrete high-sum piece `T3`.**  `x < 1/2 ≤ y`, the same sum band, and
`2x + y ≥ 3/2 + ε`. -/
noncomputable def censusT3 (ε : ℝ) (q : ℕ) : Finset (Fin q × Fin q) := by
  classical
  exact Finset.univ.filter fun p =>
    2 * (p.1 : ℕ) < q ∧
      q ≤ 2 * (p.2 : ℕ) ∧
        (7 / 6 + ε) * q ≤ (((p.1 : ℕ) + (p.2 : ℕ) : ℕ) : ℝ) ∧
          (((p.1 : ℕ) + (p.2 : ℕ) : ℕ) : ℝ) ≤ (17 / 12 + ε / 2) * q ∧
            (3 / 2 + ε) * q ≤ (((2 * (p.1 : ℕ) + (p.2 : ℕ) : ℕ)) : ℝ)

theorem censusT1_subset_pairGood (ε : ℝ) (q : ℕ) [NeZero q] :
    censusT1 q ⊆ pairGood ε q := by
  intro p hp
  simp only [censusT1, pairGood, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  obtain ⟨h1, h2, h3⟩ := hp
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have h1R : (q : ℝ) ≤ 2 * (p.1 : ℝ) := by exact_mod_cast h1
  have h2R : 2 * (q : ℝ) < 3 * ((p.1 : ℝ) + (p.2 : ℝ)) := by exact_mod_cast h2
  have h3R : 6 * ((p.1 : ℝ) + (p.2 : ℝ)) ≤ 7 * (q : ℝ) := by exact_mod_cast h3
  refine Or.inl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hq]; linarith
  · rw [div_lt_one hq]; exact_mod_cast p.1.isLt
  · exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hq)
  · rw [div_lt_one hq]; exact_mod_cast p.2.isLt
  · show 2 / 3 < (p.1 : ℝ) / q + (p.2 : ℝ) / q
    have hsplit : (p.1 : ℝ) / q + (p.2 : ℝ) / q = ((p.1 : ℝ) + (p.2 : ℝ)) / q := by ring
    rw [hsplit, lt_div_iff₀ hq]; linarith
  · show (p.1 : ℝ) / q + (p.2 : ℝ) / q ≤ 7 / 6
    have hsplit : (p.1 : ℝ) / q + (p.2 : ℝ) / q = ((p.1 : ℝ) + (p.2 : ℝ)) / q := by ring
    rw [hsplit, div_le_iff₀ hq]; linarith

theorem censusT2_subset_pairGood {ε : ℝ} (q : ℕ) [NeZero q] :
    censusT2 ε q ⊆ pairGood ε q := by
  intro p hp
  simp only [censusT2, pairGood, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have h1R : (q : ℝ) ≤ 2 * (p.1 : ℝ) := by exact_mod_cast h1
  have h2R : 2 * (p.2 : ℝ) < (q : ℝ) := by exact_mod_cast h2
  have hsplit : (p.1 : ℝ) / q + (p.2 : ℝ) / q =
      (((p.1 : ℕ) + (p.2 : ℕ) : ℕ) : ℝ) / q := by
    push_cast
    ring
  refine Or.inr (Or.inl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩)
  · rw [le_div_iff₀ hq]; linarith
  · rw [div_lt_one hq]; exact_mod_cast p.1.isLt
  · exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hq)
  · rw [div_lt_iff₀ hq]; linarith
  · show 7 / 6 + ε ≤ (p.1 : ℝ) / q + (p.2 : ℝ) / q
    rw [hsplit, le_div_iff₀ hq]; linarith
  · show (p.1 : ℝ) / q + (p.2 : ℝ) / q ≤ 17 / 12 + ε / 2
    rw [hsplit, div_le_iff₀ hq]; linarith

theorem censusT3_subset_pairGood {ε : ℝ} (q : ℕ) [NeZero q] :
    censusT3 ε q ⊆ pairGood ε q := by
  intro p hp
  simp only [censusT3, pairGood, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := hp
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have h1R : 2 * (p.1 : ℝ) < (q : ℝ) := by exact_mod_cast h1
  have h2R : (q : ℝ) ≤ 2 * (p.2 : ℝ) := by exact_mod_cast h2
  have h5R : (3 / 2 + ε) * q ≤ (((2 * (p.1 : ℕ) + (p.2 : ℕ) : ℕ)) : ℝ) :=
    by exact_mod_cast h5
  have hsplit : (p.1 : ℝ) / q + (p.2 : ℝ) / q =
      (((p.1 : ℕ) + (p.2 : ℕ) : ℕ) : ℝ) / q := by
    push_cast
    ring
  have hsplit2 : 2 * ((p.1 : ℝ) / q) + (p.2 : ℝ) / q =
      (((2 * (p.1 : ℕ) + (p.2 : ℕ) : ℕ)) : ℝ) / q := by
    push_cast
    ring
  refine Or.inr (Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  · exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hq)
  · rw [div_lt_iff₀ hq]; linarith
  · rw [le_div_iff₀ hq]; linarith
  · rw [div_lt_one hq]; exact_mod_cast p.2.isLt
  · show 7 / 6 + ε ≤ (p.1 : ℝ) / q + (p.2 : ℝ) / q
    rw [hsplit, le_div_iff₀ hq]; linarith
  · show (p.1 : ℝ) / q + (p.2 : ℝ) / q ≤ 17 / 12 + ε / 2
    rw [hsplit, div_le_iff₀ hq]; linarith
  · show 3 / 2 + ε ≤ 2 * ((p.1 : ℝ) / q) + (p.2 : ℝ) / q
    rw [hsplit2, le_div_iff₀ hq]; linarith

theorem disjoint_censusT1_censusT2 {ε : ℝ} (hε : 0 < ε) (q : ℕ) [NeZero q] :
    Disjoint (censusT1 q) (censusT2 ε q) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  simp only [censusT1, censusT2, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  set S : ℝ := (((p.1 : ℕ) + (p.2 : ℕ) : ℕ) : ℝ) with hS
  have hlo : 6 * S ≤ 7 * (q : ℝ) := by
    rw [hS]; exact_mod_cast hp1.2.2
  have hhi : (7 / 6 + ε) * q ≤ S := hp2.2.2.1
  nlinarith [hlo, hhi, hq, hε]

theorem disjoint_censusT1_censusT3 (ε : ℝ) (q : ℕ) :
    Disjoint (censusT1 q) (censusT3 ε q) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp3
  simp only [censusT1, censusT3, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp3
  omega

theorem disjoint_censusT2_censusT3 (ε : ℝ) (q : ℕ) [NeZero q] :
    Disjoint (censusT2 ε q) (censusT3 ε q) := by
  rw [Finset.disjoint_left]
  intro p hp2 hp3
  simp only [censusT2, censusT3, Finset.mem_filter, Finset.mem_univ, true_and] at hp2 hp3
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have h2R : (q : ℝ) ≤ 2 * (p.1 : ℝ) := by exact_mod_cast hp2.1
  have h3R : 2 * (p.1 : ℝ) < (q : ℝ) := by exact_mod_cast hp3.1
  linarith

/-- **Census lower bound.**  The three discrete pieces are contained in the pair
grid and pairwise disjoint, so their cardinalities add:
`#T1 + #T2 + #T3 ≤ (torusGrid ε q).card`. -/
theorem census_card_add_le_torusGrid {ε : ℝ} (hε : 0 < ε) (q : ℕ) [NeZero q] :
    (censusT1 q).card + (censusT2 ε q).card + (censusT3 ε q).card ≤
      (torusGrid ε q).card := by
  classical
  have hsub : censusT1 q ∪ censusT2 ε q ∪ censusT3 ε q ⊆ pairGood ε q :=
    Finset.union_subset
      (Finset.union_subset (censusT1_subset_pairGood ε q) (censusT2_subset_pairGood q))
      (censusT3_subset_pairGood q)
  have hd12 : Disjoint (censusT1 q) (censusT2 ε q) := disjoint_censusT1_censusT2 hε q
  have hd13 : Disjoint (censusT1 q) (censusT3 ε q) := disjoint_censusT1_censusT3 ε q
  have hd23 : Disjoint (censusT2 ε q) (censusT3 ε q) := disjoint_censusT2_censusT3 ε q
  have hcard : (censusT1 q ∪ censusT2 ε q ∪ censusT3 ε q).card =
      (censusT1 q).card + (censusT2 ε q).card + (censusT3 ε q).card := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hd13, hd23⟩),
      Finset.card_union_of_disjoint hd12]
  calc (censusT1 q).card + (censusT2 ε q).card + (censusT3 ε q).card
      = (censusT1 q ∪ censusT2 ε q ∪ censusT3 ε q).card := hcard.symm
    _ ≤ (pairGood ε q).card := Finset.card_le_card hsub
    _ = (torusGrid ε q).card := (torusGrid_card_eq_pairGood ε q).symm

/-! ### The natural lattice triangle -/

/-- `#{(u,v) : ℕ × ℕ | u + v ≤ n} = (n+1)(n+2)/2`. -/
def triNum (n : ℕ) : ℕ := (n + 1) * (n + 2) / 2

/-- The same number as a real. -/
noncomputable def Pr (n : ℕ) : ℝ := ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2

/-- The antidiagonal `{(u,v) | u + v = m}`, as an injective image of `range (m+1)`. -/
def diag (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (m + 1)).image fun u => (u, m - u)

theorem mem_diag {m : ℕ} {p : ℕ × ℕ} : p ∈ diag m ↔ p.1 + p.2 = m := by
  rw [diag, Finset.mem_image]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [Finset.mem_range] at hu
    omega
  · intro h
    exact ⟨p.1, by rw [Finset.mem_range]; omega, Prod.ext rfl (by omega)⟩

theorem diag_card (m : ℕ) : (diag m).card = m + 1 := by
  rw [diag, Finset.card_image_of_injective _ (fun u v huv => congrArg Prod.fst huv),
    Finset.card_range]

/-- The natural lattice triangle `{(u,v) | u + v ≤ n}`. -/
def tri (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n + 1)).biUnion diag

theorem mem_tri {n : ℕ} {p : ℕ × ℕ} : p ∈ tri n ↔ p.1 + p.2 ≤ n := by
  rw [tri, Finset.mem_biUnion]
  constructor
  · rintro ⟨m, hm, hpm⟩
    rw [Finset.mem_range] at hm
    rw [mem_diag] at hpm
    omega
  · intro h
    exact ⟨p.1 + p.2, by rw [Finset.mem_range]; omega, by rw [mem_diag]⟩

theorem tri_card_choose (n : ℕ) : (tri n).card = (n + 2).choose 2 := by
  have h : (∑ m ∈ Finset.range (n + 1), (m + 1)) = (n + 2).choose 2 := by
    have h2 := Nat.sum_range_add_choose n 1
    simp only [Nat.choose_one_right] at h2
    exact h2
  rw [tri, Finset.card_biUnion]
  · simpa only [diag_card] using h
  · intro m _ m' _ hmm'
    show Disjoint (diag m) (diag m')
    rw [Finset.disjoint_left]
    intro p hpm hpm'
    rw [mem_diag] at hpm hpm'
    exact hmm' (by omega)

theorem tri_card (n : ℕ) : (tri n).card = triNum n := by
  rw [tri_card_choose, triNum, Nat.choose_two_right,
    show (n + 2) - 1 = n + 1 from by omega, Nat.mul_comm (n + 2) (n + 1)]

theorem triNum_mono {n m : ℕ} (h : n ≤ m) : triNum n ≤ triNum m := by
  simp only [triNum]
  exact Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))

theorem triNum_cast (n : ℕ) : (triNum n : ℝ) = Pr n := by
  rw [triNum, Pr]
  have hd : 2 ∣ (n + 1) * (n + 2) := by
    have h := Nat.even_mul_succ_self (n + 1)
    rw [even_iff_two_dvd] at h
    simpa using h
  rw [Nat.cast_div hd (by norm_num)]
  push_cast
  ring

/-- `#{(u,v) | u < A, u + v ≤ n}` for `A ≤ n`. -/
theorem card_tri_ge (A n : ℕ) (h : A ≤ n) :
    ((tri n).filter fun p => A ≤ p.1).card = triNum (n - A) := by
  have hbij : ((tri n).filter fun p => A ≤ p.1).card = (tri (n - A)).card := by
    refine Finset.card_bij (fun (p : ℕ × ℕ) _ => (p.1 - A, p.2)) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter] at hp
      rw [mem_tri] at hp ⊢
      omega
    · intro p1 h1 p2 h2 heq
      simp only [Finset.mem_filter] at h1 h2
      have e1 : p1.1 - A = p2.1 - A := by
        simpa using congrArg (fun r : ℕ × ℕ => r.1) heq
      exact Prod.ext (by omega) (by simpa using congrArg (fun r : ℕ × ℕ => r.2) heq)
    · intro (p : ℕ × ℕ) hp
      rw [mem_tri] at hp
      refine ⟨((p.1 + A, p.2) : ℕ × ℕ), ?_, ?_⟩
      · simp only [Finset.mem_filter]
        exact ⟨by rw [mem_tri]; omega, by omega⟩
      · refine Prod.ext ?_ rfl
        show (p.1 + A) - A = p.1
        omega
  rw [hbij, tri_card]

/-! ### Exact `T1` census -/

/-- `⌈q/2⌉`. -/
def t1c (q : ℕ) : ℕ := (q + 1) / 2
/-- `⌊2q/3⌋`. -/
def t1lo (q : ℕ) : ℕ := 2 * q / 3
/-- `⌊7q/6⌋`. -/
def t1hi (q : ℕ) : ℕ := 7 * q / 6

/-- The `ε`-free `T1` piece with the exact floor/ceil thresholds.  The strict
condition `2q < 3(i+j)` becomes the strict `t1lo q < i+j`. -/
theorem censusT1_eq_filter (q : ℕ) :
    censusT1 q = Finset.univ.filter (fun p : Fin q × Fin q =>
      t1c q ≤ (p.1 : ℕ) ∧ t1lo q < (p.1 : ℕ) + (p.2 : ℕ) ∧
        (p.1 : ℕ) + (p.2 : ℕ) ≤ t1hi q) := by
  unfold censusT1
  apply Finset.filter_congr
  intro p _
  simp only [t1c, t1lo, t1hi]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, by omega, by omega⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, by omega, by omega⟩

/-- The `(u,v)`-coefficient set of the `T1` piece, a clipped diagonal band. -/
def boxBand (q : ℕ) : Finset (ℕ × ℕ) :=
  (tri (t1hi q - t1c q) \ tri (t1lo q - t1c q)).filter (fun p => p.1 < q - t1c q)

theorem tri_sdiff_subset (q : ℕ) :
    tri (t1lo q - t1c q) ⊆ tri (t1hi q - t1c q) := by
  have hle : t1lo q - t1c q ≤ t1hi q - t1c q := by
    simp only [t1lo, t1hi]; omega
  intro p hp
  rw [mem_tri] at hp ⊢
  omega

theorem t1hi_sub_c_le (q : ℕ) : t1hi q - t1c q ≤ q - 1 := by
  simp only [t1hi, t1c]; omega

/-- The `T1` piece is bijective to its `(u,v)`-coefficient band `boxBand`. -/
theorem censusT1_card_eq_boxBand (q : ℕ) (h4 : 4 ≤ q) :
    (censusT1 q).card = (boxBand q).card := by
  rw [censusT1_eq_filter]
  have hcq : t1c q ≤ q := by simp only [t1c]; omega
  have hcl : t1c q ≤ t1lo q := by simp only [t1c, t1lo]; omega
  have hch : t1c q ≤ t1hi q := by simp only [t1c, t1hi]; omega
  refine Finset.card_bij (fun p _ => ((p.1 : ℕ) - t1c q, (p.2 : ℕ))) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨h1, h2, h3⟩ := hp
    have hp1 : (p.1 : ℕ) < q := p.1.isLt
    rw [boxBand, Finset.mem_filter, Finset.mem_sdiff, mem_tri, mem_tri]
    exact ⟨⟨by omega, by omega⟩, by omega⟩
  · intro p1 h1 p2 h2 heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    have e1 : (p1.1 : ℕ) - t1c q = (p2.1 : ℕ) - t1c q := congrArg Prod.fst heq
    have e2 : (p1.2 : ℕ) = (p2.2 : ℕ) := congrArg Prod.snd heq
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext e2)
  · intro p hp
    rw [boxBand, Finset.mem_filter, Finset.mem_sdiff, mem_tri, mem_tri] at hp
    obtain ⟨⟨hpA, hpB⟩, hplt⟩ := hp
    have hp2 : p.2 < q := by
      have := t1hi_sub_c_le q
      omega
    refine ⟨(⟨t1c q + p.1, by omega⟩, ⟨p.2, hp2⟩), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by omega, by omega, by omega⟩
    · refine Prod.ext ?_ rfl
      show (t1c q + p.1) - t1c q = (p.1 : ℕ)
      omega

/-- **Exact `T1` census.** `(censusT1 q).card = P(hi-c) - P(lo-c) - P(hi-q)` with
`P(n) = (n+1)(n+2)/2`, encoded additively to avoid truncated subtraction. -/
theorem boxBand_card_add (q : ℕ) (h4 : 4 ≤ q) :
    (boxBand q).card + triNum (t1lo q - t1c q) + triNum (t1hi q - q)
      = triNum (t1hi q - t1c q) := by
  have hsub := tri_sdiff_subset q
  have hle : triNum (t1lo q - t1c q) ≤ triNum (t1hi q - t1c q) :=
    triNum_mono (by simp only [t1lo, t1hi]; omega)
  have hsdiff : (tri (t1hi q - t1c q) \ tri (t1lo q - t1c q)).card
      = triNum (t1hi q - t1c q) - triNum (t1lo q - t1c q) := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, tri_card, tri_card]
  have hsplit : (boxBand q).card
      + ((tri (t1hi q - t1c q) \ tri (t1lo q - t1c q)).filter (fun p => ¬ p.1 < q - t1c q)).card
      = (tri (t1hi q - t1c q) \ tri (t1lo q - t1c q)).card := by
    rw [boxBand]
    exact Finset.card_filter_add_card_filter_not (fun p : ℕ × ℕ => p.1 < q - t1c q)
  have hneg : ((tri (t1hi q - t1c q) \ tri (t1lo q - t1c q)).filter
        (fun p => ¬ p.1 < q - t1c q)).card = triNum (t1hi q - q) := by
    have hfilter : (tri (t1hi q - t1c q) \ tri (t1lo q - t1c q)).filter
          (fun p => ¬ p.1 < q - t1c q)
        = (tri (t1hi q - t1c q)).filter (fun p => q - t1c q ≤ p.1) := by
      ext p
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_sdiff]
      constructor
      · rintro ⟨⟨hpA, _⟩, hge⟩
        exact ⟨hpA, by omega⟩
      · rintro ⟨hpA, hge⟩
        refine ⟨⟨hpA, ?_⟩, by omega⟩
        intro hpB
        rw [mem_tri] at hpB
        simp only [t1lo, t1c, t1hi] at hpA hge hpB
        omega
    rw [hfilter, card_tri_ge (q - t1c q) (t1hi q - t1c q)
        (by simp only [t1hi, t1c]; omega),
      show t1hi q - t1c q - (q - t1c q) = t1hi q - q from by
        simp only [t1hi, t1c]; omega]
  omega

/-- **Exact `T1` cardinality, real form.** -/
theorem censusT1_card_eq (q : ℕ) (h4 : 4 ≤ q) :
    ((censusT1 q).card : ℝ)
      = Pr (t1hi q - t1c q) - Pr (t1lo q - t1c q) - Pr (t1hi q - q) := by
  rw [censusT1_card_eq_boxBand q h4]
  have hadd := boxBand_card_add q h4
  have hcast := congrArg (fun n : ℕ => (n : ℝ)) hadd
  push_cast at hcast
  simp only [triNum_cast] at hcast
  linarith

/-- **`T1` census lower bound.**  With the explicit floor/ceil ledger the `T1`
piece carries an error of at most one `q`. -/
theorem censusT1_card_lower (q : ℕ) [NeZero q] :
    ((censusT1 q).card : ℝ) ≥ (q : ℝ) ^ 2 * (7 / 36) - (q : ℝ) := by
  by_cases h5 : q ≤ 5
  · have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    have hq5 : (q : ℝ) ≤ 5 := by exact_mod_cast h5
    have hcard : (0 : ℝ) ≤ (censusT1 q).card := Nat.cast_nonneg _
    nlinarith [hq0, hq5, hcard]
  · have h4 : 4 ≤ q := by omega
    have hq6 : (6 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 6 ≤ q)
    have hA : 3 * (t1hi q - t1c q) + 4 ≥ 2 * q := by simp only [t1hi, t1c]; omega
    have hB : 6 * (t1lo q - t1c q) ≤ q := by simp only [t1lo, t1c]; omega
    have hC : 6 * (t1hi q - q) ≤ q := by simp only [t1hi]; omega
    have hU : ((t1hi q - t1c q : ℕ) : ℝ) ≥ (2 * (q : ℝ) - 4) / 3 := by
      have hA' : (3 : ℝ) * ((t1hi q - t1c q : ℕ) : ℝ) + 4 ≥ 2 * (q : ℝ) := by
        exact_mod_cast hA
      linarith
    have hV : ((t1lo q - t1c q : ℕ) : ℝ) ≤ (q : ℝ) / 6 := by
      have hB' : (6 : ℝ) * ((t1lo q - t1c q : ℕ) : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast hB
      linarith
    have hW : ((t1hi q - q : ℕ) : ℝ) ≤ (q : ℝ) / 6 := by
      have hC' : (6 : ℝ) * ((t1hi q - q : ℕ) : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast hC
      linarith
    have hPrA : Pr (t1hi q - t1c q) ≥ (2 * (q : ℝ) - 1) * (2 * (q : ℝ) + 2) / 18 := by
      simp only [Pr]
      nlinarith [hU]
    have hPrB : Pr (t1lo q - t1c q) ≤ ((q : ℝ) + 6) * ((q : ℝ) + 12) / 72 := by
      have h0 : (0 : ℝ) ≤ ((t1lo q - t1c q : ℕ) : ℝ) := Nat.cast_nonneg _
      simp only [Pr]
      nlinarith [hV, h0]
    have hPrC : Pr (t1hi q - q) ≤ ((q : ℝ) + 6) * ((q : ℝ) + 12) / 72 := by
      have h0 : (0 : ℝ) ≤ ((t1hi q - q : ℕ) : ℝ) := Nat.cast_nonneg _
      simp only [Pr]
      nlinarith [hW, h0]
    rw [censusT1_card_eq q h4]
    nlinarith [hPrA, hPrB, hPrC, hq6]

/-! ### Ground-truth checks for the new counting definitions -/

example : (tri 0).card = 1 := by decide
example : (diag 4).card = 5 := by decide
example : (tri 5).card = 21 := by decide
example : triNum 6 = 28 := by decide
example : ((censusT1 6).card : ℝ) = Erdos142.Pr 4 - Erdos142.Pr 1 - Erdos142.Pr 1 := by
  have h := censusT1_card_eq 6 (by norm_num)
  simpa only [t1hi, t1c, t1lo] using h

/-! ### `T2` census lower bound

The `T2` band is transported to the annulus `{L ≤ U + V ≤ A}` in the deficit
coordinates `U = 1 - x`, `V = 1/2 - y`.  We take an outer lattice triangle of
radius `t2n` and delete an inner triangle of radius `t2m`, map it back, and
bound the two triangle counts against `q*A` and `q*L`. -/

/-- `⌊(q-1)/2⌋`, the vertical half-range of `T2`. -/
def t2d (q : ℕ) : ℕ := (q - 1) / 2

theorem t2d_lt (q : ℕ) [NeZero q] : t2d q < q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  simp only [t2d]; omega

/-- `q - 1 + ⌊(q-1)/2⌋`, the constant of the deficit sum. -/
def t2H (q : ℕ) : ℕ := q - 1 + t2d q

/-- Outer radius `⌊H - (7/6+ε)q⌋`, clipped at zero. -/
noncomputable def t2n (ε : ℝ) (q : ℕ) : ℕ :=
  Nat.floor ((t2H q : ℝ) - (7 / 6 + ε) * (q : ℝ))

/-- Inner radius `⌈H - (17/12+ε/2)q⌉ - 1`, clipped at zero. -/
noncomputable def t2m (ε : ℝ) (q : ℕ) : ℕ :=
  Nat.ceil ((t2H q : ℝ) - (17 / 12 + ε / 2) * (q : ℝ)) - 1

/-- The deficit-to-coordinate map `(u,v) ↦ (q-1-u, t2d q - v)`, clamped so that
it is a total map `ℕ × ℕ → Fin q × Fin q`. -/
noncomputable def t2g (q : ℕ) [NeZero q] (p : ℕ × ℕ) : Fin q × Fin q :=
  (⟨q - 1 - min p.1 (q - 1),
      lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_one_lt (NeZero.ne q))⟩,
    ⟨t2d q - min p.2 (t2d q),
      lt_of_le_of_lt (Nat.sub_le _ _) (t2d_lt q)⟩)

/-- Membership in the discrete `T2` piece, in cleared-denominator form. -/
theorem mem_censusT2_iff {ε : ℝ} {q : ℕ} {r : Fin q × Fin q} :
    r ∈ censusT2 ε q ↔
      q ≤ 2 * (r.1 : ℕ) ∧ 2 * (r.2 : ℕ) < q ∧
        (7 / 6 + ε) * (q : ℝ) ≤ (((r.1 : ℕ) + (r.2 : ℕ) : ℕ) : ℝ) ∧
          (((r.1 : ℕ) + (r.2 : ℕ) : ℕ) : ℝ) ≤ (17 / 12 + ε / 2) * (q : ℝ) := by
  rw [censusT2]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The deficit triangle maps injectively into the discrete `T2` piece. -/
theorem triad_mono {m n : ℕ} (h : m ≤ n) : tri m ⊆ tri n := by
  intro p hp
  rw [mem_tri] at hp ⊢
  omega

set_option maxHeartbeats 1000000 in
theorem censusT2_card_lower {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1 / 6) (q : ℕ) [NeZero q] :
    ((censusT2 ε q).card : ℝ) ≥
      (q : ℝ) ^ 2 * (5 / 96 - 7 * ε / 24 + 3 * ε ^ 2 / 8) - (q : ℝ) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  by_cases hq19 : q ≤ 19
  · have hcard : (0 : ℝ) ≤ (censusT2 ε q).card := Nat.cast_nonneg _
    have hcoef : 5 / 96 - 7 * ε / 24 + 3 * ε ^ 2 / 8 ≤ 5 / 96 := by nlinarith [hε, hεle]
    have hq19R : (q : ℝ) ≤ 19 := by exact_mod_cast hq19
    nlinarith [hcard, hcoef, hq0, hq19R]
  · have h20 : 20 ≤ q := by omega
    have hq20 : (20 : ℝ) ≤ (q : ℝ) := by exact_mod_cast h20
    have hHlo_nat : 3 * q ≤ 2 * t2H q + 4 := by simp only [t2H, t2d]; omega
    have hHhi_nat : 2 * t2H q + 3 ≤ 3 * q := by simp only [t2H, t2d]; omega
    have hdhi_nat : 2 * t2d q ≤ q - 1 := by simp only [t2d]; omega
    have hdlo_nat : q ≤ 2 * t2d q + 2 := by simp only [t2d]; omega
    have hHlo : (3 * (q : ℝ) - 4) / 2 ≤ (t2H q : ℝ) := by
      have h : (3 : ℝ) * (q : ℝ) ≤ 2 * (t2H q : ℝ) + 4 := by exact_mod_cast hHlo_nat
      linarith
    have hHhi : (t2H q : ℝ) ≤ (3 * (q : ℝ) - 3) / 2 := by
      have h : 2 * (t2H q : ℝ) + 3 ≤ (3 : ℝ) * (q : ℝ) := by exact_mod_cast hHhi_nat
      linarith
    have hdlo : (q : ℝ) / 2 - 1 ≤ (t2d q : ℝ) := by
      have h : (q : ℝ) ≤ 2 * (t2d q : ℝ) + 2 := by exact_mod_cast hdlo_nat
      linarith
    have hRr_pos : 0 ≤ (t2H q : ℝ) - (7 / 6 + ε) * (q : ℝ) := by
      nlinarith [hHlo, hq20, hε]
    have hn_hi : (t2n ε q : ℝ) ≤ (t2H q : ℝ) - (7 / 6 + ε) * (q : ℝ) :=
      Nat.floor_le hRr_pos
    have hn_ge : (t2H q : ℝ) - (7 / 6 + ε) * (q : ℝ) - 1 ≤ (t2n ε q : ℝ) := by
      have h := Nat.lt_floor_add_one ((t2H q : ℝ) - (7 / 6 + ε) * (q : ℝ))
      simp only [t2n]
      linarith
    have hεq : 0 ≤ ε * (q : ℝ) := mul_nonneg (le_of_lt hε) (le_of_lt hq0)
    have hn_d : t2n ε q ≤ t2d q := by
      show Nat.floor ((t2H q : ℝ) - (7 / 6 + ε) * (q : ℝ)) ≤ t2d q
      apply Nat.floor_le_of_le
      have h1 : (t2H q : ℝ) - (7 / 6 + ε) * (q : ℝ)
          ≤ (3 * (q : ℝ) - 3) / 2 - (7 / 6) * (q : ℝ) := by nlinarith [hHhi, hεq]
      have h2 : (3 * (q : ℝ) - 3) / 2 - (7 / 6) * (q : ℝ) ≤ (t2d q : ℝ) := by
        nlinarith [hdlo, hq20]
      linarith
    have hn_q1 : t2n ε q ≤ q - 1 := by
      show Nat.floor ((t2H q : ℝ) - (7 / 6 + ε) * (q : ℝ)) ≤ q - 1
      apply Nat.floor_le_of_le
      have h1 : (t2H q : ℝ) - (7 / 6 + ε) * (q : ℝ)
          ≤ (3 * (q : ℝ) - 3) / 2 - (7 / 6) * (q : ℝ) := by nlinarith [hHhi, hεq]
      have h2 : (3 * (q : ℝ) - 3) / 2 - (7 / 6) * (q : ℝ) ≤ (q : ℝ) - 1 := by
        nlinarith [hq20]
      have hqm : (((q - 1 : ℕ)) : ℝ) = (q : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ q)]; push_cast; ring
      linarith
    have hce_le : (q + 1) / 2 ≤ q - 1 := by omega
    have hce_hi : (((q + 1) / 2 : ℕ) : ℝ) ≤ ((q : ℝ) + 1) / 2 := by
      have h : 2 * ((q + 1) / 2) ≤ q + 1 := by omega
      have := (Nat.cast_le (α := ℝ)).mpr h
      push_cast at this; linarith
    have hn_ce : t2n ε q ≤ q - 1 - (q + 1) / 2 := by
      show Nat.floor ((t2H q : ℝ) - (7 / 6 + ε) * (q : ℝ)) ≤ q - 1 - (q + 1) / 2
      apply Nat.floor_le_of_le
      have hcast : (((q - 1 - (q + 1) / 2 : ℕ)) : ℝ) = (q : ℝ) - 1 - (((q + 1) / 2 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hce_le, Nat.cast_sub (by omega : 1 ≤ q)]
        push_cast; ring
      rw [hcast]
      have h1 : (t2H q : ℝ) - (7 / 6 + ε) * (q : ℝ)
          ≤ (3 * (q : ℝ) - 3) / 2 - (7 / 6) * (q : ℝ) := by nlinarith [hHhi, hεq]
      have h2 : (3 * (q : ℝ) - 3) / 2 - (7 / 6) * (q : ℝ)
          ≤ (q : ℝ) - 1 - (((q + 1) / 2 : ℕ) : ℝ) := by
        nlinarith [hce_hi, hq20]
      linarith
    have hm_ge : (t2H q : ℝ) - (17 / 12 + ε / 2) * (q : ℝ) - 1 ≤ (t2m ε q : ℝ) := by
      have h1 : Nat.ceil ((t2H q : ℝ) - (17 / 12 + ε / 2) * (q : ℝ)) ≤ t2m ε q + 1 := by
        simp only [t2m]; omega
      have h2 := Nat.le_ceil ((t2H q : ℝ) - (17 / 12 + ε / 2) * (q : ℝ))
      have h3 : ((t2m ε q + 1 : ℕ) : ℝ) = (t2m ε q : ℝ) + 1 := by push_cast; ring
      have h4 : ((Nat.ceil ((t2H q : ℝ) - (17 / 12 + ε / 2) * (q : ℝ)) : ℕ) : ℝ)
          ≤ (t2m ε q : ℝ) + 1 := by rw [← h3]; exact_mod_cast h1
      linarith
    have hm_le : (t2m ε q : ℝ) ≤ (1 / 12 - ε / 2) * (q : ℝ) := by
      rcases eq_or_lt_of_le (Nat.zero_le (Nat.ceil ((t2H q : ℝ) - (17 / 12 + ε / 2) * (q : ℝ)))) with
        hc | hc
      · rw [t2m, ← hc]
        simp only [Nat.zero_sub, Nat.cast_zero]
        nlinarith [hq20, hεle]
      · have hXr_pos : 0 < (t2H q : ℝ) - (17 / 12 + ε / 2) * (q : ℝ) := by
          by_contra hle
          have hc0 : Nat.ceil ((t2H q : ℝ) - (17 / 12 + ε / 2) * (q : ℝ)) = 0 := by
            apply Nat.le_zero.mp
            rw [Nat.ceil_le]
            simpa using (not_lt.mp hle : (t2H q : ℝ) - (17 / 12 + ε / 2) * (q : ℝ) ≤ 0)
          omega
        have hlt := Nat.ceil_lt_add_one (le_of_lt hXr_pos)
            (a := (t2H q : ℝ) - (17 / 12 + ε / 2) * (q : ℝ))
        have hmval : (t2m ε q : ℝ)
            = (Nat.ceil ((t2H q : ℝ) - (17 / 12 + ε / 2) * (q : ℝ)) : ℝ) - 1 := by
          rw [t2m, Nat.cast_sub (by omega : 1 ≤ Nat.ceil _), Nat.cast_one]
        have hXr_le : (t2H q : ℝ) - (17 / 12 + ε / 2) * (q : ℝ)
            ≤ (1 / 12 - ε / 2) * (q : ℝ) - 3 / 2 := by
          nlinarith [hHhi]
        rw [hmval]
        linarith
    have hm_n : t2m ε q ≤ t2n ε q := by
      have hL_Rr : (1 / 12 - ε / 2) * (q : ℝ) ≤ (t2H q : ℝ) - (7 / 6 + ε) * (q : ℝ) := by
        nlinarith [hHlo, hq20, hε, hεle]
      have hmRr : ((t2m ε q : ℕ) : ℝ) ≤ (t2H q : ℝ) - (7 / 6 + ε) * (q : ℝ) :=
        le_trans hm_le hL_Rr
      calc t2m ε q = Nat.floor ((t2m ε q : ℕ) : ℝ) := (Nat.floor_natCast _).symm
        _ ≤ Nat.floor ((t2H q : ℝ) - (7 / 6 + ε) * (q : ℝ)) := Nat.floor_mono hmRr
        _ = t2n ε q := rfl
    -- Injection into censusT2
    have hmem : ∀ p ∈ tri (t2n ε q) \ tri (t2m ε q), t2g q p ∈ censusT2 ε q := by
      intro p hp
      rw [Finset.mem_sdiff, mem_tri, mem_tri] at hp
      obtain ⟨hpn, hpm⟩ := hp
      have hp1d : p.1 ≤ t2d q := le_trans (le_trans (Nat.le_add_right _ _) hpn) hn_d
      have hp2d : p.2 ≤ t2d q := le_trans (le_trans (Nat.le_add_left _ _) hpn) hn_d
      have hp1q : p.1 ≤ q - 1 := le_trans (le_trans (Nat.le_add_right _ _) hpn) hn_q1
      have hp1ce : p.1 ≤ q - 1 - (q + 1) / 2 :=
        le_trans (le_trans (Nat.le_add_right _ _) hpn) hn_ce
      have hmin1 : min p.1 (q - 1) = p.1 := min_eq_left hp1q
      have hmin2 : min p.2 (t2d q) = p.2 := min_eq_left hp2d
      have hleH : p.1 + p.2 ≤ t2H q := by
        have hnon : 0 ≤ (7 / 6 + ε) * (q : ℝ) := by positivity
        have h2 : (t2n ε q : ℝ) ≤ (t2H q : ℝ) := by linarith [hn_hi, hnon]
        exact le_trans hpn (Nat.cast_le.mp h2)
      have hid : (q - 1 - p.1) + (t2d q - p.2) = t2H q - (p.1 + p.2) := by
        simp only [t2H]; omega
      have hcastid : ((t2H q - (p.1 + p.2) : ℕ) : ℝ) = (t2H q : ℝ) - (p.1 + p.2 : ℕ) :=
        Nat.cast_sub hleH
      have hpnc : ((p.1 + p.2 : ℕ) : ℝ) ≤ (t2n ε q : ℝ) := Nat.cast_le.mpr hpn
      have hg1 : ((t2g q p).1 : ℕ) = q - 1 - min p.1 (q - 1) := rfl
      have hg2 : ((t2g q p).2 : ℕ) = t2d q - min p.2 (t2d q) := rfl
      rw [mem_censusT2_iff, hg1, hg2]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hmin1]; omega
      · rw [hmin2]
        have := hdhi_nat; omega
      · rw [hmin1, hmin2, hid, hcastid]
        linarith [hn_hi, hpnc]
      · rw [hmin1, hmin2, hid, hcastid]
        have hm1 : ((t2m ε q + 1 : ℕ) : ℝ) ≥ (t2H q : ℝ) - (17 / 12 + ε / 2) * (q : ℝ) := by
          have h := hm_ge
          push_cast at h ⊢
          linarith
        have hpv : p.1 + p.2 ≥ t2m ε q + 1 := by omega
        have hpvR : ((t2m ε q + 1 : ℕ) : ℝ) ≤ ((p.1 + p.2 : ℕ) : ℝ) := Nat.cast_le.mpr hpv
        linarith [hm1, hpvR]
    have hinj : Set.InjOn (t2g q) ↑(tri (t2n ε q) \ tri (t2m ε q)) := by
      intro p1 h1 p2 h2 heq
      simp only [Finset.mem_coe] at h1 h2
      rw [Finset.mem_sdiff, mem_tri] at h1 h2
      obtain ⟨h1n, _⟩ := h1
      obtain ⟨h2n, _⟩ := h2
      have hp1q : p1.1 ≤ q - 1 := le_trans (le_trans (Nat.le_add_right _ _) h1n) hn_q1
      have hp2q : p2.1 ≤ q - 1 := le_trans (le_trans (Nat.le_add_right _ _) h2n) hn_q1
      have hq1d : p1.2 ≤ t2d q := le_trans (le_trans (Nat.le_add_left _ _) h1n) hn_d
      have hq2d : p2.2 ≤ t2d q := le_trans (le_trans (Nat.le_add_left _ _) h2n) hn_d
      have e1 : min p1.1 (q - 1) = min p2.1 (q - 1) := by
        have hh := congrArg (fun r : Fin q × Fin q => ((r.1 : Fin q) : ℕ)) heq
        simp only [t2g, Fin.val_mk] at hh
        omega
      have e2 : min p1.2 (t2d q) = min p2.2 (t2d q) := by
        have hh := congrArg (fun r : Fin q × Fin q => ((r.2 : Fin q) : ℕ)) heq
        simp only [t2g, Fin.val_mk] at hh
        omega
      rw [min_eq_left hp1q, min_eq_left hp2q] at e1
      rw [min_eq_left hq1d, min_eq_left hq2d] at e2
      exact Prod.ext e1 e2
    have hcard_le : (tri (t2n ε q) \ tri (t2m ε q)).card ≤ (censusT2 ε q).card := by
      have hsub : (tri (t2n ε q) \ tri (t2m ε q)).image (t2g q) ⊆ censusT2 ε q :=
        Finset.image_subset_iff.mpr hmem
      have himg : ((tri (t2n ε q) \ tri (t2m ε q)).image (t2g q)).card
          = (tri (t2n ε q) \ tri (t2m ε q)).card :=
        Finset.card_image_of_injOn hinj
      calc (tri (t2n ε q) \ tri (t2m ε q)).card
          = ((tri (t2n ε q) \ tri (t2m ε q)).image (t2g q)).card := himg.symm
        _ ≤ (censusT2 ε q).card := Finset.card_le_card hsub
    have htri_card : (tri (t2n ε q) \ tri (t2m ε q)).card =
        triNum (t2n ε q) - triNum (t2m ε q) := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (triad_mono hm_n), tri_card, tri_card]
    have hmain : ((triNum (t2n ε q) - triNum (t2m ε q) : ℕ) : ℝ) ≤ (censusT2 ε q).card := by
      have := hcard_le
      rw [htri_card] at this
      exact_mod_cast this
    have htriR : ((triNum (t2n ε q) - triNum (t2m ε q) : ℕ) : ℝ)
        = Pr (t2n ε q) - Pr (t2m ε q) := by
      rw [Nat.cast_sub (triNum_mono hm_n), triNum_cast, triNum_cast]
    have hn_lo : (t2n ε q : ℝ) ≥ (q : ℝ) * (1 / 3 - ε) - 3 := by
      nlinarith [hn_ge, hHlo, hq20, hε]
    have hPrn : Pr (t2n ε q)
        ≥ ((q : ℝ) * (1 / 3 - ε) - 2) * ((q : ℝ) * (1 / 3 - ε) - 1) / 2 := by
      simp only [Pr]
      nlinarith [hn_lo, hq20, hε, hεle]
    have hPrm : Pr (t2m ε q)
        ≤ ((q : ℝ) * (1 / 12 - ε / 2) + 1) * ((q : ℝ) * (1 / 12 - ε / 2) + 2) / 2 := by
      have h0 : (0 : ℝ) ≤ (t2m ε q : ℝ) := Nat.cast_nonneg _
      simp only [Pr]
      nlinarith [hm_le, h0]
    have hfinal : ((q : ℝ) * (1 / 3 - ε) - 2) * ((q : ℝ) * (1 / 3 - ε) - 1) / 2
        - ((q : ℝ) * (1 / 12 - ε / 2) + 1) * ((q : ℝ) * (1 / 12 - ε / 2) + 2) / 2
        ≥ (q : ℝ) ^ 2 * (5 / 96 - 7 * ε / 24 + 3 * ε ^ 2 / 8) - (q : ℝ) := by
      nlinarith [hq0, hε, hεle]
    linarith [hmain, htriR, hPrn, hPrm, hfinal]

/-! ### Ground-truth checks for the new `T2` counting definitions -/

example : t2d 20 = 9 := by decide
example : t2H 20 = 28 := by decide
example : t2d 21 = 10 := by decide
example : t2H 21 = 30 := by decide

/-! ### `T3` census lower bound

The `T3` band is transported to the region `{a q ≤ U+V ≤ b q}` cut by the weight
`2U+V ≤ c q` in the deficit coordinates `U = 1-x`, `V = 1-y` of the map
`(u,v) ↦ (t3d q - u, q-1-v)`.  The admissible set is the lattice annulus
`{m < u+v ≤ n}` filtered by `2u+v ≤ K`; the discarded wedge `{u+v ≤ n, 2u+v > K}`
is bounded by the upper half of a lattice triangle. -/

/-- `⌊(q-1)/2⌋`, the horizontal half-range of `T3`. -/
def t3d (q : ℕ) : ℕ := (q - 1) / 2

theorem t3d_lt (q : ℕ) [NeZero q] : t3d q < q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  simp only [t3d]; omega

/-- `q - 1 + ⌊(q-1)/2⌋`, the constant of the deficit sum. -/
def t3H (q : ℕ) : ℕ := q - 1 + t3d q

/-- `q - 1 + 2⌊(q-1)/2⌋`, the constant of the deficit weight. -/
def t3J (q : ℕ) : ℕ := q - 1 + 2 * t3d q

/-- Outer radius `⌊H - (7/6+ε)q⌋`, clipped at zero. -/
noncomputable def t3n (ε : ℝ) (q : ℕ) : ℕ :=
  Nat.floor ((t3H q : ℝ) - (7 / 6 + ε) * (q : ℝ))

/-- Inner radius `⌈H - (17/12+ε/2)q⌉ - 1`, clipped at zero. -/
noncomputable def t3m (ε : ℝ) (q : ℕ) : ℕ :=
  Nat.ceil ((t3H q : ℝ) - (17 / 12 + ε / 2) * (q : ℝ)) - 1

/-- Weight cut `⌊J - (3/2+ε)q⌋`, clipped at zero. -/
noncomputable def t3K (ε : ℝ) (q : ℕ) : ℕ :=
  Nat.floor ((t3J q : ℝ) - (3 / 2 + ε) * (q : ℝ))

/-- `2⌊H-aq⌋ - ⌊J-cq⌋ - 1`, the truncated wedge depth. -/
noncomputable def t3D (ε : ℝ) (q : ℕ) : ℕ := 2 * t3n ε q - t3K ε q - 1

/-- The deficit-to-coordinate map `(u,v) ↦ (t3d q - u, q-1-v)`, clamped so that
it is a total map `ℕ × ℕ → Fin q × Fin q`. -/
noncomputable def t3g (q : ℕ) [NeZero q] (p : ℕ × ℕ) : Fin q × Fin q :=
  (⟨t3d q - min p.1 (t3d q),
      lt_of_le_of_lt (Nat.sub_le _ _) (t3d_lt q)⟩,
    ⟨q - 1 - min p.2 (q - 1),
      lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_one_lt (NeZero.ne q))⟩)

/-- The upper half `{w ≤ r}` of the lattice triangle of radius `D`. -/
def halfTri (D : ℕ) : Finset (ℕ × ℕ) := (tri D).filter (fun p => p.2 ≤ p.1)

/-- The half-triangle injection into `range (D/2+1) × range (D - D/2 + 1)`. -/
def halfG (D : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  if p.1 ≤ D / 2 then p else (p.2, D - p.1 + 1)

/-- Membership in the discrete `T3` piece, in cleared-denominator form. -/
theorem mem_censusT3_iff {ε : ℝ} {q : ℕ} {r : Fin q × Fin q} :
    r ∈ censusT3 ε q ↔
      2 * (r.1 : ℕ) < q ∧ q ≤ 2 * (r.2 : ℕ) ∧
        (7 / 6 + ε) * (q : ℝ) ≤ (((r.1 : ℕ) + (r.2 : ℕ) : ℕ) : ℝ) ∧
          (((r.1 : ℕ) + (r.2 : ℕ) : ℕ) : ℝ) ≤ (17 / 12 + ε / 2) * (q : ℝ) ∧
            (3 / 2 + ε) * (q : ℝ) ≤ (((2 * (r.1 : ℕ) + (r.2 : ℕ) : ℕ)) : ℝ) := by
  rw [censusT3]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Casting a truncated double subtraction to `ℝ` costs at most the honest value. -/
theorem cast_sub_sub_one_le (a b : ℕ) :
    ((a - b - 1 : ℕ) : ℝ) ≤ max 0 ((a : ℝ) - (b : ℝ) - 1) := by
  by_cases h : b ≤ a
  · by_cases h1 : 1 ≤ a - b
    · rw [Nat.cast_sub h1, Nat.cast_sub h, Nat.cast_one]
      exact le_max_right _ _
    · have h0 : a - b = 0 := by omega
      rw [h0]
      simp only [Nat.zero_sub, Nat.cast_zero]
      exact le_max_left _ _
  · have h0 : a - b = 0 := by omega
    rw [h0]
    simp only [Nat.zero_sub, Nat.cast_zero]
    exact le_max_left _ _

/-- The upper half of a lattice triangle of radius `D` fits in the rectangle
`(D/2+1) × (D - D/2 + 1)`. -/
theorem halfTri_card_le (D : ℕ) :
    (halfTri D).card ≤ (D / 2 + 1) * (D - D / 2 + 1) := by
  have hinj : Set.InjOn (halfG D) ↑(halfTri D) := by
    intro p1 h1 p2 h2 heq
    simp only [Finset.mem_coe] at h1 h2
    rw [halfTri, Finset.mem_filter, mem_tri] at h1 h2
    obtain ⟨h1t, h1w⟩ := h1
    obtain ⟨h2t, h2w⟩ := h2
    by_cases c1 : p1.1 ≤ D / 2 <;> by_cases c2 : p2.1 ≤ D / 2
    · simpa only [halfG, if_pos c1, if_pos c2] using heq
    · exfalso
      have hb : p1 = (p2.2, D - p2.1 + 1) :=
        by simpa only [halfG, if_pos c1, if_neg c2] using heq
      have h1 : p1.1 = p2.2 := congrArg Prod.fst hb
      have h2 : p1.2 = D - p2.1 + 1 := congrArg Prod.snd hb
      have hle : p1.2 ≤ p1.1 := h1w
      have hlt : p2.2 < D - p2.1 + 1 := by omega
      omega
    · exfalso
      have hb : p2 = (p1.2, D - p1.1 + 1) :=
        by simpa only [halfG, if_neg c1, if_pos c2] using heq.symm
      have h1 : p2.1 = p1.2 := congrArg Prod.fst hb
      have h2 : p2.2 = D - p1.1 + 1 := congrArg Prod.snd hb
      have hle : p2.2 ≤ p2.1 := h2w
      have hlt : p1.2 < D - p1.1 + 1 := by omega
      omega
    · have he : (p1.2, D - p1.1 + 1) = (p2.2, D - p2.1 + 1) :=
        by simpa only [halfG, if_neg c1, if_neg c2] using heq
      have e1 : p1.2 = p2.2 := congrArg Prod.fst he
      have e2 : D - p1.1 + 1 = D - p2.1 + 1 := congrArg Prod.snd he
      have e3 : p1.1 = p2.1 := by omega
      exact Prod.ext e3 e1
  have hmem : ∀ p ∈ halfTri D,
      halfG D p ∈ (Finset.range (D / 2 + 1)) ×ˢ (Finset.range (D - D / 2 + 1)) := by
    intro p hp
    rw [halfTri, Finset.mem_filter, mem_tri] at hp
    obtain ⟨hpt, hpw⟩ := hp
    by_cases c : p.1 ≤ D / 2
    · simp only [halfG, if_pos c, Finset.mem_product, Finset.mem_range]
      constructor <;> omega
    · simp only [halfG, if_neg c, Finset.mem_product, Finset.mem_range]
      constructor <;> omega
  calc (halfTri D).card
      ≤ ((Finset.range (D / 2 + 1)) ×ˢ (Finset.range (D - D / 2 + 1))).card :=
        Finset.card_le_card_of_injOn (halfG D) hmem hinj
    _ = (D / 2 + 1) * (D - D / 2 + 1) := by
        rw [Finset.card_product, Finset.card_range, Finset.card_range]

/-- The half-triangle count is at most `(D+2)^2/4`. -/
theorem halfTri_card_le_sq (D : ℕ) :
    ((halfTri D).card : ℝ) ≤ ((D : ℝ) + 2) ^ 2 / 4 := by
  have h1 : ((halfTri D).card : ℝ) ≤ (((D / 2 + 1) * (D - D / 2 + 1) : ℕ) : ℝ) := by
    exact_mod_cast halfTri_card_le D
  have h2 : (((D / 2 + 1) * (D - D / 2 + 1) : ℕ) : ℝ) ≤ ((D : ℝ) + 2) ^ 2 / 4 := by
    have hcast : (((D / 2 + 1) * (D - D / 2 + 1) : ℕ) : ℝ)
        = (((D / 2 + 1 : ℕ)) : ℝ) * (((D - D / 2 + 1 : ℕ)) : ℝ) := by push_cast; ring
    rw [hcast]
    have hsum : (D / 2 + 1) + (D - D / 2 + 1) = D + 2 := by omega
    have hx : (((D / 2 + 1 : ℕ)) : ℝ) + (((D - D / 2 + 1 : ℕ)) : ℝ) = (D : ℝ) + 2 :=
      by exact_mod_cast hsum
    nlinarith [sq_nonneg ((((D / 2 + 1 : ℕ)) : ℝ) - (((D - D / 2 + 1 : ℕ)) : ℝ)), hx]
  linarith

set_option maxHeartbeats 1600000 in
/-- **`T3` census ledger.**  For `0 < ε ≤ 1/6` the discrete piece `T3` has at
least `q^2*(13/288 - 5ε/24 + ε²/8) - q` points (coefficient `C₃ = 1`). -/
theorem censusT3_card_lower {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1 / 6) (q : ℕ) [NeZero q] :
    (q : ℝ) ^ 2 * (13 / 288 - 5 * ε / 24 + ε ^ 2 / 8) - (q : ℝ) ≤
      ((censusT3 ε q).card : ℝ) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  by_cases hq22 : q ≤ 22
  · have hcard : (0 : ℝ) ≤ (censusT3 ε q).card := Nat.cast_nonneg _
    have hcoef : 13 / 288 - 5 * ε / 24 + ε ^ 2 / 8 ≤ 13 / 288 := by nlinarith [hε, hεle]
    have hq22R : (q : ℝ) ≤ 22 := by exact_mod_cast hq22
    nlinarith [hcard, hcoef, hq0, hq22R]
  · have h23 : 23 ≤ q := by omega
    have hq23 : (23 : ℝ) ≤ (q : ℝ) := by exact_mod_cast h23
    have hdhi_nat : 2 * t3d q ≤ q - 1 := by simp only [t3d]; omega
    have hdlo_nat : q ≤ 2 * t3d q + 2 := by simp only [t3d]; omega
    have hce_le : (q + 1) / 2 ≤ q - 1 := by omega
    have hHlo_nat : 3 * q ≤ 2 * t3H q + 4 := by simp only [t3H, t3d]; omega
    have hHhi_nat : 2 * t3H q + 3 ≤ 3 * q := by simp only [t3H, t3d]; omega
    have hJlo_nat : 2 * q ≤ t3J q + 3 := by simp only [t3J, t3d]; omega
    have hdlo : (q : ℝ) / 2 - 1 ≤ (t3d q : ℝ) := by
      have h : (q : ℝ) ≤ 2 * (t3d q : ℝ) + 2 := by exact_mod_cast hdlo_nat
      linarith
    have hHlo : (3 * (q : ℝ) - 4) / 2 ≤ (t3H q : ℝ) := by
      have h : (3 : ℝ) * (q : ℝ) ≤ 2 * (t3H q : ℝ) + 4 := by exact_mod_cast hHlo_nat
      linarith
    have hHhi : (t3H q : ℝ) ≤ (3 * (q : ℝ) - 3) / 2 := by
      have h : 2 * (t3H q : ℝ) + 3 ≤ (3 : ℝ) * (q : ℝ) := by exact_mod_cast hHhi_nat
      linarith
    have hJlo : 2 * (q : ℝ) - 3 ≤ (t3J q : ℝ) := by
      have h : 2 * (q : ℝ) ≤ (t3J q : ℝ) + 3 := by exact_mod_cast hJlo_nat
      linarith
    have hεq : 0 ≤ ε * (q : ℝ) := mul_nonneg (le_of_lt hε) (le_of_lt hq0)
    -- outer radius `n`
    have hRr_pos : 0 ≤ (t3H q : ℝ) - (7 / 6 + ε) * (q : ℝ) := by nlinarith [hHlo, hq23, hε]
    have hn_hi : (t3n ε q : ℝ) ≤ (t3H q : ℝ) - (7 / 6 + ε) * (q : ℝ) := Nat.floor_le hRr_pos
    have hn_ge : (t3H q : ℝ) - (7 / 6 + ε) * (q : ℝ) - 1 ≤ (t3n ε q : ℝ) := by
      have h := Nat.lt_floor_add_one ((t3H q : ℝ) - (7 / 6 + ε) * (q : ℝ))
      simp only [t3n]; linarith
    have hn_lo : (t3n ε q : ℝ) ≥ (q : ℝ) * (1 / 3 - ε) - 3 := by
      nlinarith [hn_ge, hHlo, hq23, hε]
    have hn_d : t3n ε q ≤ t3d q := by
      show Nat.floor ((t3H q : ℝ) - (7 / 6 + ε) * (q : ℝ)) ≤ t3d q
      apply Nat.floor_le_of_le
      have h1 : (t3H q : ℝ) - (7 / 6 + ε) * (q : ℝ)
          ≤ (3 * (q : ℝ) - 3) / 2 - (7 / 6) * (q : ℝ) := by nlinarith [hHhi, hεq]
      have h2 : (3 * (q : ℝ) - 3) / 2 - (7 / 6) * (q : ℝ) ≤ (t3d q : ℝ) := by
        nlinarith [hdlo, hq23]
      linarith
    have hn_q1 : t3n ε q ≤ q - 1 := by
      show Nat.floor ((t3H q : ℝ) - (7 / 6 + ε) * (q : ℝ)) ≤ q - 1
      apply Nat.floor_le_of_le
      have h1 : (t3H q : ℝ) - (7 / 6 + ε) * (q : ℝ)
          ≤ (3 * (q : ℝ) - 3) / 2 - (7 / 6) * (q : ℝ) := by nlinarith [hHhi, hεq]
      have h2 : (3 * (q : ℝ) - 3) / 2 - (7 / 6) * (q : ℝ) ≤ (q : ℝ) - 1 := by nlinarith [hq23]
      have hqm : (((q - 1 : ℕ)) : ℝ) = (q : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ q)]; push_cast; ring
      linarith
    have hce_hi : (((q + 1) / 2 : ℕ) : ℝ) ≤ ((q : ℝ) + 1) / 2 := by
      have h : 2 * ((q + 1) / 2) ≤ q + 1 := by omega
      have := (Nat.cast_le (α := ℝ)).mpr h
      push_cast at this; linarith
    have hn_ce : t3n ε q ≤ q - 1 - (q + 1) / 2 := by
      show Nat.floor ((t3H q : ℝ) - (7 / 6 + ε) * (q : ℝ)) ≤ q - 1 - (q + 1) / 2
      apply Nat.floor_le_of_le
      have hcast : (((q - 1 - (q + 1) / 2 : ℕ)) : ℝ) = (q : ℝ) - 1 - (((q + 1) / 2 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hce_le, Nat.cast_sub (by omega : 1 ≤ q)]
        push_cast; ring
      rw [hcast]
      have h1 : (t3H q : ℝ) - (7 / 6 + ε) * (q : ℝ)
          ≤ (3 * (q : ℝ) - 3) / 2 - (7 / 6) * (q : ℝ) := by nlinarith [hHhi, hεq]
      have h2 : (3 * (q : ℝ) - 3) / 2 - (7 / 6) * (q : ℝ)
          ≤ (q : ℝ) - 1 - (((q + 1) / 2 : ℕ) : ℝ) := by nlinarith [hce_hi, hq23]
      linarith
    -- inner radius `m`
    have hm_ge : (t3H q : ℝ) - (17 / 12 + ε / 2) * (q : ℝ) - 1 ≤ (t3m ε q : ℝ) := by
      have h1 : Nat.ceil ((t3H q : ℝ) - (17 / 12 + ε / 2) * (q : ℝ)) ≤ t3m ε q + 1 := by
        simp only [t3m]; omega
      have h2 := Nat.le_ceil ((t3H q : ℝ) - (17 / 12 + ε / 2) * (q : ℝ))
      have h3 : ((t3m ε q + 1 : ℕ) : ℝ) = (t3m ε q : ℝ) + 1 := by push_cast; ring
      have h4 : ((Nat.ceil ((t3H q : ℝ) - (17 / 12 + ε / 2) * (q : ℝ)) : ℕ) : ℝ)
          ≤ (t3m ε q : ℝ) + 1 := by rw [← h3]; exact_mod_cast h1
      linarith
    have hm_le : (t3m ε q : ℝ) ≤ (1 / 12 - ε / 2) * (q : ℝ) := by
      rcases eq_or_lt_of_le (Nat.zero_le (Nat.ceil ((t3H q : ℝ) - (17 / 12 + ε / 2) * (q : ℝ)))) with
        hc | hc
      · rw [t3m, ← hc]
        simp only [Nat.zero_sub, Nat.cast_zero]
        nlinarith [hq23, hεle]
      · have hXr_pos : 0 < (t3H q : ℝ) - (17 / 12 + ε / 2) * (q : ℝ) := by
          by_contra hle
          have hc0 : Nat.ceil ((t3H q : ℝ) - (17 / 12 + ε / 2) * (q : ℝ)) = 0 := by
            apply Nat.le_zero.mp
            rw [Nat.ceil_le]
            simpa using (not_lt.mp hle : (t3H q : ℝ) - (17 / 12 + ε / 2) * (q : ℝ) ≤ 0)
          omega
        have hlt := Nat.ceil_lt_add_one (le_of_lt hXr_pos)
            (a := (t3H q : ℝ) - (17 / 12 + ε / 2) * (q : ℝ))
        have hmval : (t3m ε q : ℝ)
            = (Nat.ceil ((t3H q : ℝ) - (17 / 12 + ε / 2) * (q : ℝ)) : ℝ) - 1 := by
          rw [t3m, Nat.cast_sub (by omega : 1 ≤ Nat.ceil _), Nat.cast_one]
        have hXr_le : (t3H q : ℝ) - (17 / 12 + ε / 2) * (q : ℝ)
            ≤ (1 / 12 - ε / 2) * (q : ℝ) - 3 / 2 := by nlinarith [hHhi]
        rw [hmval]
        linarith
    have hm_n : t3m ε q ≤ t3n ε q := by
      have hL_Rr : (1 / 12 - ε / 2) * (q : ℝ) ≤ (t3H q : ℝ) - (7 / 6 + ε) * (q : ℝ) := by
        nlinarith [hHlo, hq23, hε, hεle]
      have hmRr : ((t3m ε q : ℕ) : ℝ) ≤ (t3H q : ℝ) - (7 / 6 + ε) * (q : ℝ) :=
        le_trans hm_le hL_Rr
      calc t3m ε q = Nat.floor ((t3m ε q : ℕ) : ℝ) := (Nat.floor_natCast _).symm
        _ ≤ Nat.floor ((t3H q : ℝ) - (7 / 6 + ε) * (q : ℝ)) := Nat.floor_mono hmRr
        _ = t3n ε q := rfl
    -- weight cut `K`
    have hK_pos : 0 ≤ (t3J q : ℝ) - (3 / 2 + ε) * (q : ℝ) := by nlinarith [hJlo, hq23, hεle]
    have hK_le : (t3K ε q : ℝ) ≤ (t3J q : ℝ) - (3 / 2 + ε) * (q : ℝ) := Nat.floor_le hK_pos
    have hK_ge : (t3J q : ℝ) - (3 / 2 + ε) * (q : ℝ) - 1 ≤ (t3K ε q : ℝ) := by
      have h := Nat.lt_floor_add_one ((t3J q : ℝ) - (3 / 2 + ε) * (q : ℝ))
      simp only [t3K]; linarith
    -- wedge depth `D`
    have hD_le : ((t3D ε q : ℕ) : ℝ) ≤ 2 * ((1 / 12 - ε / 2) * (q : ℝ)) := by
      have hmax := cast_sub_sub_one_le (2 * t3n ε q) (t3K ε q)
      have h2qL : 0 ≤ 2 * ((1 / 12 - ε / 2) * (q : ℝ)) := by nlinarith [hq0, hεle]
      have hreal : ((2 * t3n ε q : ℕ) : ℝ) - (t3K ε q : ℝ) - 1
          ≤ 2 * ((1 / 12 - ε / 2) * (q : ℝ)) := by
        have h2n : ((2 * t3n ε q : ℕ) : ℝ) = 2 * (t3n ε q : ℝ) := by push_cast; ring
        rw [h2n]
        nlinarith [hn_hi, hK_ge, hHhi, hJlo, hεq]
      have hsimp : t3D ε q = 2 * t3n ε q - t3K ε q - 1 := rfl
      rw [hsimp]
      exact le_trans hmax (max_le h2qL hreal)
    -- injection of the admissible set into `censusT3`
    have hsrc_mem : ∀ p ∈ (tri (t3n ε q) \ tri (t3m ε q)).filter
        (fun p => 2 * p.1 + p.2 ≤ t3K ε q), t3g q p ∈ censusT3 ε q := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_sdiff, mem_tri, mem_tri] at hp
      obtain ⟨⟨hpn, hpm⟩, hpK⟩ := hp
      have hp1d : p.1 ≤ t3d q := le_trans (le_trans (Nat.le_add_right _ _) hpn) hn_d
      have hp2d : p.2 ≤ t3d q := le_trans (le_trans (Nat.le_add_left _ _) hpn) hn_d
      have hp2q : p.2 ≤ q - 1 := le_trans (le_trans (Nat.le_add_left _ _) hpn) hn_q1
      have hp2ce : p.2 ≤ q - 1 - (q + 1) / 2 :=
        le_trans (le_trans (Nat.le_add_left _ _) hpn) hn_ce
      have hmin1 : min p.1 (t3d q) = p.1 := min_eq_left hp1d
      have hmin2 : min p.2 (q - 1) = p.2 := min_eq_left hp2q
      have hleH : p.1 + p.2 ≤ t3H q := by
        have hnon : 0 ≤ (7 / 6 + ε) * (q : ℝ) := by positivity
        have h2 : (t3n ε q : ℝ) ≤ (t3H q : ℝ) := by linarith [hn_hi, hnon]
        exact le_trans hpn (Nat.cast_le.mp h2)
      have hKJ : (t3K ε q : ℝ) ≤ (t3J q : ℝ) := by
        have hc : 0 ≤ (3 / 2 + ε) * (q : ℝ) := by positivity
        linarith [hK_le, hc]
      have hleJ : 2 * p.1 + p.2 ≤ t3J q := le_trans hpK (Nat.cast_le.mp hKJ)
      have hid : (t3d q - p.1) + (q - 1 - p.2) = t3H q - (p.1 + p.2) := by
        simp only [t3H]; omega
      have hid2 : 2 * (t3d q - p.1) + (q - 1 - p.2) = t3J q - (2 * p.1 + p.2) := by
        simp only [t3J]; omega
      have hcastid : ((t3H q - (p.1 + p.2) : ℕ) : ℝ) = (t3H q : ℝ) - (p.1 + p.2 : ℕ) :=
        Nat.cast_sub hleH
      have hcastid2 : ((t3J q - (2 * p.1 + p.2) : ℕ) : ℝ)
          = (t3J q : ℝ) - ((2 * p.1 + p.2 : ℕ) : ℝ) := Nat.cast_sub hleJ
      have hpnc : ((p.1 + p.2 : ℕ) : ℝ) ≤ (t3n ε q : ℝ) := Nat.cast_le.mpr hpn
      have hpKc : ((2 * p.1 + p.2 : ℕ) : ℝ) ≤ (t3K ε q : ℝ) := Nat.cast_le.mpr hpK
      have hg1 : ((t3g q p).1 : ℕ) = t3d q - min p.1 (t3d q) := rfl
      have hg2 : ((t3g q p).2 : ℕ) = q - 1 - min p.2 (q - 1) := rfl
      rw [mem_censusT3_iff, hg1, hg2]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hmin1]
        have := hdhi_nat; omega
      · rw [hmin2]; omega
      · rw [hmin1, hmin2, hid, hcastid]
        linarith [hn_hi, hpnc]
      · rw [hmin1, hmin2, hid, hcastid]
        have hm1 : ((t3m ε q + 1 : ℕ) : ℝ) ≥ (t3H q : ℝ) - (17 / 12 + ε / 2) * (q : ℝ) := by
          have h := hm_ge; push_cast at h ⊢; linarith
        have hpv : p.1 + p.2 ≥ t3m ε q + 1 := by omega
        have hpvR : ((t3m ε q + 1 : ℕ) : ℝ) ≤ ((p.1 + p.2 : ℕ) : ℝ) := Nat.cast_le.mpr hpv
        linarith [hm1, hpvR]
      · rw [hmin1, hmin2, hid2, hcastid2]
        linarith [hK_le, hpKc]
    have hsrc_inj : Set.InjOn (t3g q)
        ↑((tri (t3n ε q) \ tri (t3m ε q)).filter (fun p => 2 * p.1 + p.2 ≤ t3K ε q)) := by
      intro p1 h1 p2 h2 heq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_sdiff, mem_tri] at h1 h2
      obtain ⟨⟨h1n, _⟩, _⟩ := h1
      obtain ⟨⟨h2n, _⟩, _⟩ := h2
      have hp1d : p1.1 ≤ t3d q := le_trans (le_trans (Nat.le_add_right _ _) h1n) hn_d
      have hp2d : p2.1 ≤ t3d q := le_trans (le_trans (Nat.le_add_right _ _) h2n) hn_d
      have hq1d : p1.2 ≤ q - 1 := le_trans (le_trans (Nat.le_add_left _ _) h1n) hn_q1
      have hq2d : p2.2 ≤ q - 1 := le_trans (le_trans (Nat.le_add_left _ _) h2n) hn_q1
      have e1 : min p1.1 (t3d q) = min p2.1 (t3d q) := by
        have hh := congrArg (fun r : Fin q × Fin q => ((r.1 : Fin q) : ℕ)) heq
        simp only [t3g, Fin.val_mk] at hh
        omega
      have e2 : min p1.2 (q - 1) = min p2.2 (q - 1) := by
        have hh := congrArg (fun r : Fin q × Fin q => ((r.2 : Fin q) : ℕ)) heq
        simp only [t3g, Fin.val_mk] at hh
        omega
      rw [min_eq_left hp1d, min_eq_left hp2d] at e1
      rw [min_eq_left hq1d, min_eq_left hq2d] at e2
      exact Prod.ext e1 e2
    have hsrc_le : (((tri (t3n ε q) \ tri (t3m ε q)).filter
        (fun p => 2 * p.1 + p.2 ≤ t3K ε q)).card : ℝ) ≤ (censusT3 ε q).card := by
      have hsub : ((tri (t3n ε q) \ tri (t3m ε q)).filter
          (fun p => 2 * p.1 + p.2 ≤ t3K ε q)).image (t3g q) ⊆ censusT3 ε q :=
        Finset.image_subset_iff.mpr hsrc_mem
      have himg : (((tri (t3n ε q) \ tri (t3m ε q)).filter
          (fun p => 2 * p.1 + p.2 ≤ t3K ε q)).image (t3g q)).card
          = ((tri (t3n ε q) \ tri (t3m ε q)).filter
              (fun p => 2 * p.1 + p.2 ≤ t3K ε q)).card :=
        Finset.card_image_of_injOn hsrc_inj
      have := Finset.card_le_card hsub
      rw [himg] at this
      exact_mod_cast this
    -- the discarded wedge
    have hbad_le : (((tri (t3n ε q)).filter
        (fun p => ¬ (2 * p.1 + p.2 ≤ t3K ε q))).card : ℝ) ≤ ((halfTri (t3D ε q)).card : ℝ) := by
      have hinj : Set.InjOn (fun p : ℕ × ℕ => (t3n ε q - p.1, t3n ε q - p.1 - p.2))
          ↑((tri (t3n ε q)).filter (fun p => ¬ (2 * p.1 + p.2 ≤ t3K ε q))) := by
        intro p1 h1 p2 h2 heq
        simp only [Finset.mem_coe, Finset.mem_filter, mem_tri] at h1 h2
        obtain ⟨h1n, _⟩ := h1
        obtain ⟨h2n, _⟩ := h2
        have e1 : t3n ε q - p1.1 = t3n ε q - p2.1 := congrArg Prod.fst heq
        have e2 : t3n ε q - p1.1 - p1.2 = t3n ε q - p2.1 - p2.2 := congrArg Prod.snd heq
        have h1' : p1.1 = p2.1 := by omega
        have h2' : p1.2 = p2.2 := by omega
        exact Prod.ext h1' h2'
      have hmem : ∀ p ∈ (tri (t3n ε q)).filter (fun p => ¬ (2 * p.1 + p.2 ≤ t3K ε q)),
          (t3n ε q - p.1, t3n ε q - p.1 - p.2) ∈ halfTri (t3D ε q) := by
        intro p hp
        rw [Finset.mem_filter, mem_tri] at hp
        obtain ⟨hpn, hpK⟩ := hp
        rw [halfTri, Finset.mem_filter, mem_tri]
        refine ⟨?_, ?_⟩
        · simp only [t3D]; omega
        · exact Nat.sub_le _ _
      have := Finset.card_le_card_of_injOn
        (fun p : ℕ × ℕ => (t3n ε q - p.1, t3n ε q - p.1 - p.2)) hmem hinj
      exact_mod_cast this
    -- assembly
    have hsrc_eq : (tri (t3n ε q) \ tri (t3m ε q)).filter (fun p => 2 * p.1 + p.2 ≤ t3K ε q)
        = ((tri (t3n ε q)).filter (fun p => 2 * p.1 + p.2 ≤ t3K ε q)) \ tri (t3m ε q) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      tauto
    have hB_card : (((tri (t3n ε q)).filter (fun p => 2 * p.1 + p.2 ≤ t3K ε q)).card : ℝ)
        = (triNum (t3n ε q) : ℝ)
          - (((tri (t3n ε q)).filter (fun p => ¬ (2 * p.1 + p.2 ≤ t3K ε q))).card : ℝ) := by
      have h := Finset.card_filter_add_card_filter_not (s := tri (t3n ε q))
        (p := fun p => 2 * p.1 + p.2 ≤ t3K ε q)
      rw [tri_card] at h
      have hle : ((tri (t3n ε q)).filter (fun p => ¬ (2 * p.1 + p.2 ≤ t3K ε q))).card
          ≤ triNum (t3n ε q) := by omega
      have hBeq : ((tri (t3n ε q)).filter (fun p => 2 * p.1 + p.2 ≤ t3K ε q)).card
          = triNum (t3n ε q)
            - ((tri (t3n ε q)).filter (fun p => ¬ (2 * p.1 + p.2 ≤ t3K ε q))).card := by omega
      rw [hBeq, Nat.cast_sub hle]
    have hC : ((((tri (t3n ε q)).filter (fun p => 2 * p.1 + p.2 ≤ t3K ε q)) \ tri (t3m ε q)).card : ℝ)
        ≥ (((tri (t3n ε q)).filter (fun p => 2 * p.1 + p.2 ≤ t3K ε q)).card : ℝ)
          - (triNum (t3m ε q) : ℝ) := by
      have hcd : ((((tri (t3n ε q)).filter (fun p => 2 * p.1 + p.2 ≤ t3K ε q)) \ tri (t3m ε q)).card : ℝ)
          = (((tri (t3n ε q)).filter (fun p => 2 * p.1 + p.2 ≤ t3K ε q)).card : ℝ)
            - (((tri (t3m ε q)) ∩ ((tri (t3n ε q)).filter
                (fun p => 2 * p.1 + p.2 ≤ t3K ε q))).card : ℝ) := by
        rw [Finset.card_sdiff,
          Nat.cast_sub (Finset.card_le_card Finset.inter_subset_right)]
      have hle : ((((tri (t3m ε q)) ∩ ((tri (t3n ε q)).filter
          (fun p => 2 * p.1 + p.2 ≤ t3K ε q))).card : ℕ) : ℝ) ≤ (triNum (t3m ε q) : ℝ) := by
        have h' : ((tri (t3m ε q)) ∩ ((tri (t3n ε q)).filter
            (fun p => 2 * p.1 + p.2 ≤ t3K ε q))).card ≤ (tri (t3m ε q)).card :=
          Finset.card_le_card Finset.inter_subset_left
        rw [tri_card] at h'
        exact_mod_cast h'
      linarith
    have hsplit : (triNum (t3n ε q) : ℝ)
        - (((tri (t3n ε q)).filter (fun p => ¬ (2 * p.1 + p.2 ≤ t3K ε q))).card : ℝ)
        - (triNum (t3m ε q) : ℝ)
        ≤ (((tri (t3n ε q) \ tri (t3m ε q)).filter
            (fun p => 2 * p.1 + p.2 ≤ t3K ε q)).card : ℝ) := by
      rw [hsrc_eq]
      linarith [hC, hB_card]
    have hfin : ((censusT3 ε q).card : ℝ)
        ≥ (triNum (t3n ε q) : ℝ) - (triNum (t3m ε q) : ℝ)
          - (((halfTri (t3D ε q)).card : ℕ) : ℝ) := by
      linarith [hsrc_le, hsplit, hbad_le]
    -- final arithmetic
    have hPrn : (triNum (t3n ε q) : ℝ)
        ≥ ((q : ℝ) * (1 / 3 - ε) - 2) * ((q : ℝ) * (1 / 3 - ε) - 1) / 2 := by
      rw [triNum_cast]
      simp only [Pr]
      nlinarith [hn_lo, hq23, hε, hεle]
    have hPrm : (triNum (t3m ε q) : ℝ)
        ≤ ((q : ℝ) * (1 / 12 - ε / 2) + 1) * ((q : ℝ) * (1 / 12 - ε / 2) + 2) / 2 := by
      rw [triNum_cast]
      simp only [Pr]
      have h0 : (0 : ℝ) ≤ (t3m ε q : ℝ) := Nat.cast_nonneg _
      nlinarith [hm_le, h0]
    have hhalf2 : (((halfTri (t3D ε q)).card : ℕ) : ℝ)
        ≤ (2 * ((1 / 12 - ε / 2) * (q : ℝ)) + 2) ^ 2 / 4 := by
      have h0 : (0 : ℝ) ≤ (t3D ε q : ℝ) + 2 := by positivity
      have h1 : (0 : ℝ) ≤ 2 * ((1 / 12 - ε / 2) * (q : ℝ)) + 2 := by
        have hL : 0 ≤ (1 / 12 - ε / 2) * (q : ℝ) :=
          mul_nonneg (by linarith [hεle]) (le_of_lt hq0)
        linarith
      have hle2 : (t3D ε q : ℝ) + 2 ≤ 2 * ((1 / 12 - ε / 2) * (q : ℝ)) + 2 := by linarith
      have hsq : ((t3D ε q : ℝ) + 2) ^ 2 ≤ (2 * ((1 / 12 - ε / 2) * (q : ℝ)) + 2) ^ 2 := by
        have := mul_self_le_mul_self h0 hle2
        simpa only [pow_two] using this
      linarith [halfTri_card_le_sq (t3D ε q), hsq]
    have hfinal : ((q : ℝ) * (1 / 3 - ε) - 2) * ((q : ℝ) * (1 / 3 - ε) - 1) / 2
        - ((q : ℝ) * (1 / 12 - ε / 2) + 1) * ((q : ℝ) * (1 / 12 - ε / 2) + 2) / 2
        - (2 * ((1 / 12 - ε / 2) * (q : ℝ)) + 2) ^ 2 / 4
        ≥ (q : ℝ) ^ 2 * (13 / 288 - 5 * ε / 24 + ε ^ 2 / 8) - (q : ℝ) := by
      nlinarith [hq23, hε, hεle]
    have hfinal2 : (triNum (t3n ε q) : ℝ) - (triNum (t3m ε q) : ℝ)
        - (((halfTri (t3D ε q)).card : ℕ) : ℝ)
        ≥ (q : ℝ) ^ 2 * (13 / 288 - 5 * ε / 24 + ε ^ 2 / 8) - (q : ℝ) :=
      by linarith only [hPrn, hPrm, hhalf2, hfinal]
    exact le_trans hfinal2 hfin

/-! ### Ground-truth checks for the new `T3` counting definitions -/

example : t3d 23 = 11 := by decide
example : t3H 23 = 33 := by decide
example : t3J 23 = 44 := by decide
example : halfTri 4 = {(0, 0), (1, 0), (1, 1), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (4, 0)} :=
  by decide
example : (halfTri 4).card = 9 := by decide
example : (halfTri 5).card = 12 := by decide

/-! ### Assembled torus-grid lower bound -/

/-- **Assembled torus-grid lower bound.**  Adding the three census ledgers to the
disjointness bound gives `q²(7/24 - ε/2 + ε²/2) - 3q ≤ #torusGrid`. -/
theorem torusGrid_card_lower_eps {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1 / 6) (q : ℕ) [NeZero q] :
    (q : ℝ) ^ 2 * (7 / 24 - ε / 2 + ε ^ 2 / 2) - 3 * (q : ℝ) ≤
      ((torusGrid ε q).card : ℝ) := by
  have h1 := censusT1_card_lower q
  have h2 := censusT2_card_lower hε hεle q
  have h3 := censusT3_card_lower hε hεle q
  have hsum : ((censusT1 q).card : ℝ) + ((censusT2 ε q).card : ℝ)
      + ((censusT3 ε q).card : ℝ) ≤ ((torusGrid ε q).card : ℝ) := by
    have h := census_card_add_le_torusGrid hε q
    exact_mod_cast h
  nlinarith [h1, h2, h3, hsum]

/-- Reciprocal form: for `e ≥ 6` the same bound holds with `ε = e⁻¹`. -/
theorem torusGrid_card_lower_inv {e : ℝ} (he : 6 ≤ e) (q : ℕ) [NeZero q] :
    (q : ℝ) ^ 2 * (7 / 24 - e⁻¹ / 2 + e⁻¹ ^ 2 / 2) - 3 * (q : ℝ) ≤
      ((torusGrid e⁻¹ q).card : ℝ) := by
  have he0 : 0 < e := by linarith
  have hε : 0 < e⁻¹ := inv_pos.mpr he0
  have hεle : e⁻¹ ≤ 1 / 6 := by
    have h := (inv_le_inv₀ he0 (by norm_num : (0 : ℝ) < 6)).mpr he
    simpa using h
  exact torusGrid_card_lower_eps hε hεle q

end Erdos142

