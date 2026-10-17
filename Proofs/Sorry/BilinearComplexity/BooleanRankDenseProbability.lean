import Sorry.BilinearComplexity.BooleanRankDenseDefect
import BilinearComplexity.BooleanRankProbability
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators Classical

namespace BilinearComplexity
open BooleanRankProbability

/-- Row `i` has its unique zero at `a`, with a one everywhere else. -/
def singletonZero {n : ℕ} (A : BoolMatrix n n) (i a : Fin n) : Prop :=
  ∀ c, A i c = if c = a then 0 else 1

example : singletonZero (boolId 2) 0 1 := by unfold singletonZero; decide
example : ¬ singletonZero (boolId 3) 0 1 := by unfold singletonZero; decide

/-- The singleton-row predicate agrees with the standard zero-coordinate set. -/
theorem singletonZero_iff_zeroCoordinates {n : ℕ} (A : BoolMatrix n n) (i a : Fin n) :
    singletonZero A i a ↔ zeroCoordinates A i = {a} := by
  classical
  constructor
  · intro h
    ext c
    have hv : ∀ c, A i c = if c = a then 0 else 1 := h
    by_cases hc : c = a <;> simp [zeroCoordinates, hv, hc]
  · intro h c
    have hc : A i c = 0 ↔ c = a := by
      have hm := congrArg (fun s => c ∈ s) h
      simpa [zeroCoordinates] using hm
    by_cases he : c = a
    · simpa [he] using hc.mpr he
    · simpa [he] using (BoolSemiring.eq_zero_or_eq_one (A i c)).resolve_left
        (fun hz => he (hc.mp hz))

/-- A one-zero row has a coordinate witnessing the explicit singleton pattern. -/
theorem mem_oneZeroRows_iff_singletonZero {n : ℕ} (A : BoolMatrix n n) (i : Fin n) :
    i ∈ oneZeroRows A ↔ ∃ a, singletonZero A i a := by
  classical
  simp only [oneZeroRows, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Finset.card_eq_one]
  exact exists_congr (fun a => (singletonZero_iff_zeroCoordinates A i a).symm)

/-- The canonical witness uses all other rows zero at the target's zero coordinate.
If every other coordinate is covered, its OR is exactly the target row. -/
theorem singletonZero_canonical_witness {n : ℕ} (A : BoolMatrix n n) (i a : Fin n)
    (hi : singletonZero A i a)
    (hcover : ∀ b, b ≠ a → ∃ j, j ≠ i ∧ A j a = 0 ∧ A j b = 1) :
    let W := Finset.univ.filter (fun j => j ≠ i ∧ A j a = 0)
    i ∉ W ∧ rowsSum A W = A i := by
  classical
  dsimp only
  constructor
  · simp
  · funext b
    by_cases hb : b = a
    · subst b
      rw [hi a]
      simp only [ite_true, rowsSum]
      exact Finset.sum_eq_zero (fun j hj => (Finset.mem_filter.mp hj).2.2)
    · obtain ⟨j, hji, hja, hjb⟩ := hcover b hb
      rw [hi b, if_neg hb]
      exact (BoolSemiring.sum_eq_one_iff _ _).mpr
        ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hji, hja⟩, hjb⟩

/-- A failed singleton generation cylinder: no other row covers coordinate `b`
while staying zero at `a`. Distinctness of `a,b` is imposed by its callers. -/
def singletonCoverFailure {n : ℕ} (A : BoolMatrix n n) (i a b : Fin n) : Prop :=
  singletonZero A i a ∧ ∀ j, j ≠ i → ¬ (A j a = 0 ∧ A j b = 1)

example : singletonCoverFailure (boolId 2) 0 1 0 := by
  unfold singletonCoverFailure singletonZero
  decide
example : ¬ singletonCoverFailure (boolId 2) 0 0 1 := by
  unfold singletonCoverFailure singletonZero
  decide

/-- The complement of the dense event is covered by the four concrete bad-event
families: constant rows, dominated multi-zero rows, failed canonical generation,
and unordered singleton collisions. The order on row indices avoids double counting. -/
theorem not_denseGoodEvent_cover {n : ℕ} (A : BoolMatrix n n) (hn : 2 ≤ n)
    (hbad : ¬ denseGoodEvent A) :
    (∃ i, (∀ c, A i c = 0) ∨ (∀ c, A i c = 1)) ∨
    (∃ i j, j ≠ i ∧ i ∈ multiZeroRows A ∧ RowLE (A j) (A i)) ∨
    (∃ i a b, b ≠ a ∧ singletonCoverFailure A i a b) ∨
    (∃ i j a, i < j ∧ singletonZero A i a ∧ singletonZero A j a) := by
  classical
  by_contra h
  push Not at h
  obtain ⟨hconst, hdom, hfail, hcoll⟩ := h
  apply hbad
  refine ⟨hn, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨c, hc⟩ := (hconst i).1
    exact ⟨c, (BoolSemiring.eq_zero_or_eq_one (A i c)).resolve_left hc⟩
  · intro i
    obtain ⟨c, hc⟩ := (hconst i).2
    exact ⟨c, (BoolSemiring.eq_zero_or_eq_one (A i c)).resolve_right hc⟩
  · intro i hi j hji hle
    exact hdom i j hji hi hle
  · intro i hi
    obtain ⟨a, hia⟩ := (mem_oneZeroRows_iff_singletonZero A i).mp hi
    refine ⟨Finset.univ.filter (fun j => j ≠ i ∧ A j a = 0), ?_⟩
    apply singletonZero_canonical_witness A i a hia
    intro b hba
    by_contra hc
    apply hfail i a b hba
    refine ⟨hia, ?_⟩
    intro j hji hj
    exact hc ⟨j, hji, hj⟩
  · intro i hi j hj heq
    obtain ⟨a, hia⟩ := (mem_oneZeroRows_iff_singletonZero A i).mp hi
    have hja : singletonZero A j a :=
      (singletonZero_iff_zeroCoordinates A j a).mpr
        (heq.symm.trans ((singletonZero_iff_zeroCoordinates A i a).mp hia))
    rcases lt_trichotomy i j with hij | hij | hji
    · exact False.elim (hcoll i j a hij hia hja)
    · exact hij
    · exact False.elim (hcoll j i a hji hja hia)

private theorem row_singleton_mass {n : ℕ} (p : ℝ) (a : Fin n) :
    (∑ x : Fin n → BoolSemiring,
      if ∀ c, x c = if c = a then 0 else 1 then ∏ c, entryWeight p (x c) else 0) =
      (1-p) * p^(n-1) := by
  classical
  trans ∏ c : Fin n, ∑ v : BoolSemiring,
    if v = (if c = a then 0 else 1) then entryWeight p v else 0
  · convert cylinder_factor (fun (_ : Fin n) v => entryWeight p v)
      (fun c v => v = if c = a then 0 else 1) using 1
    apply Finset.sum_congr rfl
    intro x hx
    split_ifs <;> rfl
  ·
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
    simp only [ite_true, entryWeight, show (0 : BoolSemiring) ≠ 1 by decide, if_false]
    have he : (∏ c ∈ Finset.univ.erase a,
        entryWeight p (if c = a then 0 else 1)) = p^(n-1) := by
      calc
        _ = ∏ _c ∈ (Finset.univ.erase a : Finset (Fin n)), p := by
          apply Finset.prod_congr rfl
          intro c hc
          simp [Finset.ne_of_mem_erase hc, entryWeight]
        _ = _ := by simp
    exact congrArg (fun t : ℝ => (1-p) * t) he

private theorem row_pair_mass {n : ℕ} (p : ℝ) (a b : Fin n) (hab : a ≠ b) :
    (∑ x : Fin n → BoolSemiring,
      if x a = 0 ∧ x b = 1 then ∏ c, entryWeight p (x c) else 0) = (1-p)*p := by
  classical
  let P := fun c (v : BoolSemiring) => if c = a then v = 0 else if c = b then v = 1 else True
  have hP (x : Fin n → BoolSemiring) : (∀ c, P c (x c)) ↔ x a = 0 ∧ x b = 1 := by
    constructor
    · intro h
      exact ⟨by simpa [P] using h a, by simpa [P, hab.symm] using h b⟩
    · rintro ⟨ha, hb⟩ c
      by_cases hca : c = a <;> by_cases hcb : c = b <;> simp_all [P]
  simp_rw [← hP]
  have hf : (∑ x : Fin n → BoolSemiring,
      if ∀ c, P c (x c) then ∏ c, entryWeight p (x c) else 0) =
      ∏ c : Fin n, ∑ v : BoolSemiring, if P c v then entryWeight p v else 0 := by
    convert cylinder_factor (fun (_ : Fin n) v => entryWeight p v) P using 1
    apply Finset.sum_congr rfl
    intro x hx
    split_ifs <;> rfl
  rw [hf]
  have hs (c : Fin n) : (∑ v : BoolSemiring, if P c v then entryWeight p v else 0) =
      if c = a then 1-p else if c = b then p else 1 := by
    by_cases hca : c = a
    · subst c
      simp [P, entryWeight]
    · by_cases hcb : c = b
      · subst c
        simp [P, hab.symm, entryWeight]
      · simp only [P, if_neg hca, if_neg hcb, if_true]
        exact sum_entryWeight p
  simp_rw [hs]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
  simp only [ite_true]
  congr 1
  calc
    _ = ∏ c ∈ (Finset.univ.erase a : Finset (Fin n)), if c = b then p else 1 := by
      apply Finset.prod_congr rfl
      intro c hc
      simp [Finset.ne_of_mem_erase hc]
    _ = p := by simp [Finset.prod_ite_eq', hab.symm]

private theorem row_not_pair_mass {n : ℕ} (p : ℝ) (a b : Fin n) (hab : a ≠ b) :
    (∑ x : Fin n → BoolSemiring,
      if ¬ (x a = 0 ∧ x b = 1) then ∏ c, entryWeight p (x c) else 0) = 1-(1-p)*p := by
  classical
  have he (x : Fin n → BoolSemiring) :
      (if ¬ (x a = 0 ∧ x b = 1) then ∏ c, entryWeight p (x c) else 0) =
      (∏ c, entryWeight p (x c)) -
        (if x a = 0 ∧ x b = 1 then ∏ c, entryWeight p (x c) else 0) := by
    split_ifs <;> simp_all
  simp_rw [he]
  rw [Finset.sum_sub_distrib, row_pair_mass p a b hab, ← Fintype.prod_sum]
  simp [sum_entryWeight]

/-- The actual iid mass of each distinct-coordinate failed-generation cylinder.
The target row contributes its singleton pattern; every other row independently
avoids the zero-at-`a`, one-at-`b` pair. -/
theorem singletonCoverFailure_mass {n : ℕ} (p : ℝ) (i a b : Fin n) (hab : a ≠ b) :
    (∑ A : BoolMatrix n n,
      if singletonCoverFailure A i a b then matrixWeight p A else 0) =
      (1-p)*p^(n-1)*(1-(1-p)*p)^(n-1) := by
  classical
  let P := fun j (x : Fin n → BoolSemiring) =>
    if j = i then (∀ c, x c = if c = a then 0 else 1) else ¬ (x a = 0 ∧ x b = 1)
  have he (A : BoolMatrix n n) : singletonCoverFailure A i a b ↔ ∀ j, P j (A j) := by
    constructor
    · rintro ⟨hi, ho⟩ j
      by_cases hj : j = i
      · simpa [P, hj, singletonZero] using hi
      · simpa [P, hj] using ho j hj
    · intro h
      refine ⟨by simpa [P, singletonZero] using h i, ?_⟩
      intro j hj
      simpa [P, hj] using h j
  simp_rw [he]
  change (∑ A : BoolMatrix n n, if ∀ j, P j (A j) then
    ∏ j, ∏ c, entryWeight p (A j c) else 0) = _
  have hf : (∑ A : BoolMatrix n n, if ∀ j, P j (A j) then
      ∏ j, ∏ c, entryWeight p (A j c) else 0) =
      ∏ j : Fin n, ∑ x : Fin n → BoolSemiring,
        if P j x then ∏ c, entryWeight p (x c) else 0 := by
    convert cylinder_factor (fun (_ : Fin n) x => ∏ c, entryWeight p (x c)) P using 1
    apply Finset.sum_congr rfl
    intro A hA
    split_ifs <;> rfl
  rw [hf]
  have hs (j : Fin n) :
      (∑ x : Fin n → BoolSemiring, if P j x then ∏ c, entryWeight p (x c) else 0) =
        if j = i then (1-p)*p^(n-1) else 1-(1-p)*p := by
    by_cases hj : j = i
    · simpa [P, hj] using row_singleton_mass p a
    · simpa [P, hj] using row_not_pair_mass p a b hab
  simp_rw [hs]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [ite_true]
  congr 1
  calc
    _ = ∏ _j ∈ (Finset.univ.erase i : Finset (Fin n)), (1-(1-p)*p) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [Finset.ne_of_mem_erase hj]
    _ = _ := by simp

private theorem mass_cover {α β : Type*} [Fintype α] (w : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (E : α → Prop) (s : Finset β) (F : β → α → Prop)
    [DecidablePred E] [∀ b, DecidablePred (F b)]
    (hc : ∀ a, E a → ∃ b ∈ s, F b a) :
    (∑ a, if E a then w a else 0) ≤ ∑ b ∈ s, ∑ a, if F b a then w a else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a ha
  by_cases he : E a
  · obtain ⟨b, hb, hF⟩ := hc a he
    rw [if_pos he]
    have hsingle := Finset.single_le_sum
      (f := fun b => if F b a then w a else 0)
      (fun b _ => by split_ifs; exact hw a; exact le_refl 0) hb
    simpa only [if_pos hF] using hsingle
  · rw [if_neg he]
    exact Finset.sum_nonneg (fun b _ => by split_ifs; exact hw a; exact le_refl 0)

/-- Summing the failed canonical-generation cylinders gives exactly the third
term of the requested finite bound, without assumptions on the rank. -/
theorem singletonCoverFailure_union_mass_le {n : ℕ} (p : ℝ)
    (hn : 2 ≤ n) (hp : 0 < p) (hp1 : p < 1) :
    (∑ A : BoolMatrix n n, if ∃ i a b, b ≠ a ∧ singletonCoverFailure A i a b
      then matrixWeight p A else 0) ≤
      (n : ℝ)^2 * ((n : ℝ)-1) * (1-p)*p^(n-1)*(1-(1-p)*p)^(n-1) := by
  classical
  let t := (1-p)*p^(n-1)*(1-(1-p)*p)^(n-1)
  have hw := matrixWeight_nonneg (m := n) (n := n) p hp hp1
  have hinner (i a : Fin n) :
      (∑ A : BoolMatrix n n, if ∃ b, b ≠ a ∧ singletonCoverFailure A i a b
        then matrixWeight p A else 0) ≤ ((n : ℝ)-1) * t := by
    refine (mass_cover _ hw _ (Finset.univ.erase a)
      (fun b A => singletonCoverFailure A i a b) ?_).trans_eq ?_
    · rintro A ⟨b, hba, hF⟩
      exact ⟨b, Finset.mem_erase.mpr ⟨hba, Finset.mem_univ b⟩, hF⟩
    · have he (b : Fin n) (hb : b ∈ Finset.univ.erase a) :
          (∑ A : BoolMatrix n n, if singletonCoverFailure A i a b
            then matrixWeight p A else 0) = t := by
        exact singletonCoverFailure_mass p i a b (Finset.ne_of_mem_erase hb).symm
      rw [Finset.sum_congr rfl he]
      simp [Nat.cast_sub (by omega : 1 ≤ n)]
  have hmiddle (i : Fin n) :
      (∑ A : BoolMatrix n n, if ∃ a b, b ≠ a ∧ singletonCoverFailure A i a b
        then matrixWeight p A else 0) ≤ (n : ℝ) * ((n : ℝ)-1) * t := by
    refine (mass_cover _ hw _ Finset.univ
      (fun a A => ∃ b, b ≠ a ∧ singletonCoverFailure A i a b) ?_).trans ?_
    · rintro A ⟨a, ha⟩
      exact ⟨a, Finset.mem_univ a, ha⟩
    · calc
        _ ≤ ∑ _a : Fin n, ((n : ℝ)-1) * t :=
          Finset.sum_le_sum (fun a _ => hinner i a)
        _ = _ := by simp [mul_assoc]
  refine (mass_cover _ hw _ Finset.univ
    (fun i A => ∃ a b, b ≠ a ∧ singletonCoverFailure A i a b) ?_).trans ?_
  · rintro A ⟨i, hi⟩
    exact ⟨i, Finset.mem_univ i, hi⟩
  · calc
      _ ≤ ∑ _i : Fin n, (n : ℝ) * ((n : ℝ)-1) * t :=
        Finset.sum_le_sum (fun i _ => hmiddle i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]; dsimp [t]; ring

/-- Fixing any collection of rows to the same singleton-zero pattern has the
product mass prescribed by the iid law. -/
theorem singletonZero_rows_mass {n : ℕ} (p : ℝ) (S : Finset (Fin n)) (a : Fin n) :
    (∑ A : BoolMatrix n n, if ∀ i ∈ S, singletonZero A i a
      then matrixWeight p A else 0) = ((1-p)*p^(n-1))^S.card := by
  classical
  let P := fun i (x : Fin n → BoolSemiring) => i ∈ S →
    ∀ c, x c = if c = a then 0 else 1
  have hf : (∑ A : BoolMatrix n n, if ∀ i ∈ S, singletonZero A i a
      then matrixWeight p A else 0) =
      ∏ i : Fin n, ∑ x : Fin n → BoolSemiring,
        if P i x then ∏ c, entryWeight p (x c) else 0 := by
    convert cylinder_factor (fun (_ : Fin n) x => ∏ c, entryWeight p (x c)) P using 1
    apply Finset.sum_congr rfl
    intro A hA
    split_ifs <;> simp_all [P, singletonZero, matrixWeight]
    rename_i h₁ h₂
    obtain ⟨i, hi, c, hc⟩ := h₁
    exact False.elim (hc (h₂ i hi c))
  rw [hf]
  have hrow : (∑ x : Fin n → BoolSemiring, ∏ c, entryWeight p (x c)) = 1 := by
    rw [← Fintype.prod_sum]
    simp [sum_entryWeight]
  have hs (i : Fin n) : (∑ x : Fin n → BoolSemiring,
      if P i x then ∏ c, entryWeight p (x c) else 0) =
      if i ∈ S then (1-p)*p^(n-1) else 1 := by
    by_cases hi : i ∈ S
    · simpa [P, hi] using row_singleton_mass p a
    · simpa [P, hi] using hrow
  simp_rw [hs]
  rw [Finset.prod_ite_mem]
  simp

/-- Two distinct displayed rows have the same specified singleton zero with
mass equal to the square of a single row's mass. -/
theorem singletonZero_collision_mass {n : ℕ} (p : ℝ) (i j a : Fin n) (hij : i ≠ j) :
    (∑ A : BoolMatrix n n, if singletonZero A i a ∧ singletonZero A j a
      then matrixWeight p A else 0) = ((1-p)*p^(n-1))^2 := by
  simpa [hij] using singletonZero_rows_mass p {i, j} a

example : (2 ≤ 3) ∧ 0 < (1/2 : ℝ) ∧ (1/2 : ℝ) < 1 ∧
    Nonempty (Fin 3) ∧ Nonempty (BoolMatrix 3 3) := by
  exact ⟨by decide, by norm_num, by norm_num, ⟨0⟩, ⟨0⟩⟩

example :
    let A : BoolMatrix 3 3 := fun i c =>
      if c = 0 then 0 else if i = 0 ∨ i = c then 1 else 0
    singletonZero A 0 0 ∧
      (∀ b, b ≠ 0 → ∃ j, j ≠ 0 ∧ A j 0 = 0 ∧ A j b = 1) := by
  dsimp only
  unfold singletonZero
  decide

private theorem constant_row_mass {n : ℕ} (p : ℝ) (i : Fin n) (v : BoolSemiring) :
    (∑ A : BoolMatrix n n, if ∀ c, A i c = v then matrixWeight p A else 0) =
      (entryWeight p v)^n := by
  classical
  have hf := matrix_column_cylinder p
    (fun (_ : Fin n) (x : Fin n → BoolSemiring) => x i = v)
  rw [hf]
  have hs : (∑ x : Fin n → BoolSemiring,
      if x i = v then ∏ k, entryWeight p (x k) else 0) = entryWeight p v := by
    simpa using fixed_entries_mass p {i} v
  simp [hs]

private theorem singletonZero_dominated_mass {n : ℕ} (p : ℝ) (i j a : Fin n)
    (hji : j ≠ i) :
    (∑ A : BoolMatrix n n, if singletonZero A i a ∧ RowLE (A j) (A i)
      then matrixWeight p A else 0) = (1-p)^2*p^(n-1) := by
  classical
  let P := fun c (x : Fin n → BoolSemiring) =>
    if c = a then x i = 0 ∧ x j = 0 else x i = 1
  have he (A : BoolMatrix n n) :
      (singletonZero A i a ∧ RowLE (A j) (A i)) ↔
        ∀ c, P c (fun k => A k c) := by
    constructor
    · rintro ⟨hi, hd⟩ c
      by_cases hc : c = a
      · subst c
        have hia : A i a = 0 := by simpa using hi a
        have hja : A j a = 0 :=
          (BoolSemiring.eq_zero_or_eq_one (A j a)).resolve_right (by
            intro hj
            have hz := hd a hj
            rw [hia] at hz
            exact (by decide : (0 : BoolSemiring) ≠ 1) hz)
        simpa [P] using And.intro hia hja
      · simpa [P, hc] using hi c
    · intro h
      have ha : A i a = 0 ∧ A j a = 0 := by simpa [P] using h a
      refine ⟨?_, ?_⟩
      · intro c
        by_cases hc : c = a
        · simpa [hc] using ha.1
        · simpa [P, hc] using h c
      · intro c hj
        by_cases hc : c = a
        · subst c
          exact False.elim ((by decide : (0 : BoolSemiring) ≠ 1) (ha.2.symm.trans hj))
        · simpa [P, hc] using h c
  simp_rw [he]
  have hf : (∑ A : BoolMatrix n n,
      if ∀ c, P c (fun k => A k c) then matrixWeight p A else 0) =
      ∏ c, ∑ x : Fin n → BoolSemiring,
        if P c x then ∏ k, entryWeight p (x k) else 0 := by
    convert matrix_column_cylinder p P using 1
  rw [hf]
  have hs (c : Fin n) :
      (∑ x : Fin n → BoolSemiring, if P c x then ∏ k, entryWeight p (x k) else 0) =
        if c = a then (1-p)^2 else p := by
    by_cases hc : c = a
    · simpa [P, hc, hji, hji.symm, entryWeight] using fixed_entries_mass p {i, j} 0
    · simpa [P, hc, entryWeight] using fixed_entries_mass p {i} 1
  simp_rw [hs]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
  simp only [ite_true]
  congr 1
  calc
    _ = ∏ _c ∈ (Finset.univ.erase a : Finset (Fin n)), p := by
      apply Finset.prod_congr rfl
      intro c hc
      simp [Finset.ne_of_mem_erase hc]
    _ = _ := by simp

example : (1 : Fin 2) ≠ 0 ∧
    (0 : Fin 2) ∈ multiZeroRows (0 : BoolMatrix 2 2) ∧
    RowLE ((0 : BoolMatrix 2 2) 1) ((0 : BoolMatrix 2 2) 0) := by
  decide

/-- Exact mass of a dominated ordered pair whose target has at least two
zeros. Target `i` dominates `j`; subtracting target zero counts zero and one from
the full dominated-pair cylinder gives the displayed polynomial. -/
theorem dominated_multiZero_mass {n : ℕ} (p : ℝ) (i j : Fin n) (hji : j ≠ i) :
    (∑ A : BoolMatrix n n, if i ∈ multiZeroRows A ∧ RowLE (A j) (A i)
      then matrixWeight p A else 0) =
      (p+(1-p)^2)^n-p^n-(n : ℝ)*(1-p)^2*p^(n-1) := by
  classical
  have htotal : (∑ A : BoolMatrix n n, if RowLE (A j) (A i)
      then matrixWeight p A else 0) = (p+(1-p)^2)^n := by
    have ht := dominated_rows_mass (n := n) p i {j} (by simp [hji.symm])
    calc
      _ = ∑ A : BoolMatrix n n,
          if ∀ k ∈ ({j} : Finset (Fin n)), ∀ c, A k c = 1 → A i c = 1
          then matrixWeight p A else 0 := by
        apply Finset.sum_congr rfl
        intro A hA
        split_ifs <;> simp_all [RowLE]
      _ = _ := by simpa using ht
  have hzero : (∑ A : BoolMatrix n n,
      if (∀ c, A i c = 1) ∧ RowLE (A j) (A i) then matrixWeight p A else 0) = p^n := by
    have he (A : BoolMatrix n n) :
        ((∀ c, A i c = 1) ∧ RowLE (A j) (A i)) ↔ (∀ c, A i c = 1) :=
      ⟨And.left, fun h => ⟨h, fun c _ => h c⟩⟩
    simp_rw [he]
    simpa [entryWeight] using constant_row_mass p i 1
  have hone : (∑ A : BoolMatrix n n,
      if i ∈ oneZeroRows A ∧ RowLE (A j) (A i) then matrixWeight p A else 0) =
        (n : ℝ)*(1-p)^2*p^(n-1) := by
    have he (A : BoolMatrix n n) :
        (if i ∈ oneZeroRows A ∧ RowLE (A j) (A i) then matrixWeight p A else 0) =
        ∑ a : Fin n, if singletonZero A i a ∧ RowLE (A j) (A i)
          then matrixWeight p A else 0 := by
      by_cases hi : i ∈ oneZeroRows A
      · obtain ⟨a, ha⟩ := (mem_oneZeroRows_iff_singletonZero A i).mp hi
        have hu : ∀ b, singletonZero A i b → b = a := by
          intro b hb
          have hs := (singletonZero_iff_zeroCoordinates A i b).mp hb
          rw [(singletonZero_iff_zeroCoordinates A i a).mp ha] at hs
          simpa using hs.symm
        rw [Finset.sum_eq_single a]
        · simp [hi, ha]
        · intro b _ hba
          have hb : ¬ singletonZero A i b := fun hb => hba (hu b hb)
          simp [hb]
        · simp
      · have hnone : ∀ a, ¬ singletonZero A i a :=
          fun a ha => hi ((mem_oneZeroRows_iff_singletonZero A i).mpr ⟨a, ha⟩)
        simp [hi, hnone]
    simp_rw [he]
    rw [Finset.sum_comm]
    simp_rw [singletonZero_dominated_mass p i j _ hji]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hsplit (A : BoolMatrix n n) :
      (if RowLE (A j) (A i) then matrixWeight p A else 0) =
        (if i ∈ multiZeroRows A ∧ RowLE (A j) (A i) then matrixWeight p A else 0) +
        (if (∀ c, A i c = 1) ∧ RowLE (A j) (A i) then matrixWeight p A else 0) +
        (if i ∈ oneZeroRows A ∧ RowLE (A j) (A i) then matrixWeight p A else 0) := by
    have hz : (zeroCoordinates A i).card = 0 ↔ ∀ c, A i c = 1 := by
      rw [Finset.card_eq_zero]
      constructor
      · intro h c
        apply (BoolSemiring.eq_zero_or_eq_one (A i c)).resolve_left
        intro hc
        have hm : c ∈ zeroCoordinates A i := by simp [zeroCoordinates, hc]
        rw [h] at hm
        exact Finset.notMem_empty c hm
      · intro h
        simp [zeroCoordinates, h]
    have hm : i ∈ multiZeroRows A ↔ 2 ≤ (zeroCoordinates A i).card := by
      simp [multiZeroRows]
    have ho : i ∈ oneZeroRows A ↔ (zeroCoordinates A i).card = 1 := by
      simp [oneZeroRows]
    rcases Nat.eq_zero_or_pos (zeroCoordinates A i).card with hc | hc
    · simp [hm, ho, hc, hz.mp hc]
    · by_cases hc1 : (zeroCoordinates A i).card = 1
      · have hnz : ¬ ∀ c, A i c = 1 := fun h => by have := hz.mpr h; omega
        simp [hm, ho, hc1, hnz]
      · have hc2 : 2 ≤ (zeroCoordinates A i).card := by omega
        have hnz : ¬ ∀ c, A i c = 1 := fun h => by have := hz.mpr h; omega
        have hn1 : ¬ i ∈ oneZeroRows A := by simpa [ho] using hc1
        simp [hm.mpr hc2, hnz, hn1]
  have hsum := congrArg (fun f : BoolMatrix n n → ℝ => ∑ A, f A) (funext hsplit)
  simp only [Finset.sum_add_distrib] at hsum
  rw [htotal, hzero, hone] at hsum
  linarith

private theorem mass_or_le {α : Type*} [Fintype α] (w : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] :
    (∑ a, if P a ∨ Q a then w a else 0) ≤
      (∑ a, if P a then w a else 0) + (∑ a, if Q a then w a else 0) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a ha
  have hn := hw a
  by_cases hp : P a <;> by_cases hq : Q a <;> simp [hp, hq, hn]

/-- The four-term finite Bernoulli bound for the actual dense-good-event
complement, obtained from the four concrete bad-event families. -/
theorem denseGoodEvent_complement_mass_le (n : ℕ) (p : ℝ)
    (hn : 2 ≤ n) (hp : 0 < p) (hp1 : p < 1) :
    (∑ A : BoolMatrix n n, if ¬ denseGoodEvent A then matrixWeight p A else 0) ≤
      (n : ℝ)*(p^n+(1-p)^n) +
      (n : ℝ)*((n : ℝ)-1)*((p+(1-p)^2)^n-p^n-(n : ℝ)*(1-p)^2*p^(n-1)) +
      (n : ℝ)^2*((n : ℝ)-1)*(1-p)*p^(n-1)*(1-(1-p)*p)^(n-1) +
      (Nat.choose n 2 : ℝ)*(n : ℝ)*((1-p)*p^(n-1))^2 := by
  classical
  let C := fun A : BoolMatrix n n => ∃ i, (∀ c, A i c = 0) ∨ (∀ c, A i c = 1)
  let D := fun A : BoolMatrix n n =>
    ∃ i j, j ≠ i ∧ i ∈ multiZeroRows A ∧ RowLE (A j) (A i)
  let F := fun A : BoolMatrix n n => ∃ i a b, b ≠ a ∧ singletonCoverFailure A i a b
  let K := fun A : BoolMatrix n n =>
    ∃ i j a, i < j ∧ singletonZero A i a ∧ singletonZero A j a
  let mass := fun E : BoolMatrix n n → Prop =>
    ∑ A : BoolMatrix n n, if E A then matrixWeight p A else 0
  have mass_eq (E : BoolMatrix n n → Prop) [DecidablePred E] :
      mass E = ∑ A : BoolMatrix n n, if E A then matrixWeight p A else 0 := by
    apply Finset.sum_congr rfl
    intro A hA
    split_ifs <;> rfl
  let d := (p+(1-p)^2)^n-p^n-(n : ℝ)*(1-p)^2*p^(n-1)
  let s := ((1-p)*p^(n-1))^2
  have hw := matrixWeight_nonneg (m := n) (n := n) p hp hp1
  have hC : mass C ≤ (n : ℝ)*(p^n+(1-p)^n) := by
    rw [mass_eq C]
    refine (mass_cover _ hw C Finset.univ
      (fun i A => (∀ c, A i c = 0) ∨ (∀ c, A i c = 1)) ?_).trans ?_
    · rintro A ⟨i, hi⟩
      exact ⟨i, Finset.mem_univ i, hi⟩
    · have hrow (i : Fin n) :
          (∑ A : BoolMatrix n n, if (∀ c, A i c = 0) ∨ (∀ c, A i c = 1)
            then matrixWeight p A else 0) ≤ p^n+(1-p)^n := by
        have h := mass_or_le _ hw (fun A => ∀ c, A i c = 0) (fun A => ∀ c, A i c = 1)
        rw [constant_row_mass, constant_row_mass] at h
        simpa [entryWeight, add_comm] using h
      calc
        _ ≤ ∑ _i : Fin n, (p^n+(1-p)^n) := Finset.sum_le_sum (fun i _ => hrow i)
        _ = _ := by simp [mul_add]
  have hD : mass D ≤ (n : ℝ)*((n : ℝ)-1)*d := by
    have hinner (i : Fin n) :
        (∑ A : BoolMatrix n n,
          if ∃ j, j ≠ i ∧ i ∈ multiZeroRows A ∧ RowLE (A j) (A i)
            then matrixWeight p A else 0) ≤ ((n : ℝ)-1)*d := by
      refine (mass_cover _ hw _ (Finset.univ.erase i)
        (fun j A => i ∈ multiZeroRows A ∧ RowLE (A j) (A i)) ?_).trans_eq ?_
      · rintro A ⟨j, hji, hj⟩
        exact ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩, hj⟩
      · have he (j : Fin n) (hj : j ∈ Finset.univ.erase i) :
            (∑ A : BoolMatrix n n, if i ∈ multiZeroRows A ∧ RowLE (A j) (A i)
              then matrixWeight p A else 0) = d :=
          dominated_multiZero_mass p i j (Finset.ne_of_mem_erase hj)
        rw [Finset.sum_congr rfl he]
        simp [Nat.cast_sub (by omega : 1 ≤ n)]
    rw [mass_eq D]
    refine (mass_cover _ hw D Finset.univ
      (fun i A => ∃ j, j ≠ i ∧ i ∈ multiZeroRows A ∧ RowLE (A j) (A i)) ?_).trans ?_
    · rintro A ⟨i, hi⟩
      exact ⟨i, Finset.mem_univ i, hi⟩
    · calc
        _ ≤ ∑ _i : Fin n, ((n : ℝ)-1)*d := Finset.sum_le_sum (fun i _ => hinner i)
        _ = _ := by simp [mul_assoc]
  have hF : mass F ≤ (n : ℝ)^2*((n : ℝ)-1)*(1-p)*p^(n-1)*
      (1-(1-p)*p)^(n-1) := by
    rw [mass_eq F]
    exact singletonCoverFailure_union_mass_le p hn hp hp1
  have hK : mass K ≤ (Nat.choose n 2 : ℝ)*(n : ℝ)*s := by
    let T := (Finset.univ : Finset (Fin n × Fin n)).filter (fun ij => ij.1 < ij.2)
    have hcard : T.card = Nat.choose n 2 := by
      simpa [T] using (Fintype.card_product_filter_lt (α := Fin n))
    have hpair (ij : Fin n × Fin n) (hij : ij ∈ T) :
        (∑ A : BoolMatrix n n,
          if ∃ a, singletonZero A ij.1 a ∧ singletonZero A ij.2 a
            then matrixWeight p A else 0) ≤ (n : ℝ)*s := by
      have hlt : ij.1 < ij.2 := (Finset.mem_filter.mp hij).2
      refine (mass_cover _ hw _ Finset.univ
        (fun a A => singletonZero A ij.1 a ∧ singletonZero A ij.2 a) ?_).trans_eq ?_
      · rintro A ⟨a, ha⟩
        exact ⟨a, Finset.mem_univ a, ha⟩
      · simp_rw [singletonZero_collision_mass p ij.1 ij.2 _ (ne_of_lt hlt)]
        simp [s]
    rw [mass_eq K]
    refine (mass_cover _ hw K T
      (fun ij A => ∃ a, singletonZero A ij.1 a ∧ singletonZero A ij.2 a) ?_).trans ?_
    · rintro A ⟨i, j, a, hij, hi, hj⟩
      exact ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, a, hi, hj⟩
    · calc
        _ ≤ ∑ _ij ∈ T, (n : ℝ)*s := Finset.sum_le_sum (fun ij hij => hpair ij hij)
        _ = _ := by simp [hcard, mul_assoc]
  have hcover : (∑ A : BoolMatrix n n,
      if ¬ denseGoodEvent A then matrixWeight p A else 0) ≤
        mass (fun A => C A ∨ D A ∨ F A ∨ K A) := by
    apply Finset.sum_le_sum
    intro A hA
    by_cases hbad : ¬ denseGoodEvent A
    · have hc : C A ∨ D A ∨ F A ∨ K A := not_denseGoodEvent_cover A hn hbad
      simp only [if_pos hbad, if_pos hc]
      exact le_refl _
    · rw [if_neg hbad]
      split_ifs
      · exact hw A
      · exact le_refl 0
  have hCD : mass (fun A => C A ∨ D A ∨ F A ∨ K A) ≤
      mass C + mass (fun A => D A ∨ F A ∨ K A) := by
    rw [mass_eq, mass_eq, mass_eq]
    exact mass_or_le _ hw C (fun A => D A ∨ F A ∨ K A)
  have hDF : mass (fun A => D A ∨ F A ∨ K A) ≤
      mass D + mass (fun A => F A ∨ K A) := by
    rw [mass_eq, mass_eq, mass_eq]
    exact mass_or_le _ hw D (fun A => F A ∨ K A)
  have hFK : mass (fun A => F A ∨ K A) ≤ mass F + mass K := by
    rw [mass_eq, mass_eq, mass_eq]
    exact mass_or_le _ hw F K
  change _ ≤ (n : ℝ)*(p^n+(1-p)^n) + (n : ℝ)*((n : ℝ)-1)*d +
    (n : ℝ)^2*((n : ℝ)-1)*(1-p)*p^(n-1)*(1-(1-p)*p)^(n-1) +
    (Nat.choose n 2 : ℝ)*(n : ℝ)*s
  linarith

end BilinearComplexity
