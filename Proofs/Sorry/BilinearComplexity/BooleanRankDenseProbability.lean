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

/-- Unpaid exact mass of a dominated ordered pair whose target has at least two
zeros. Target `i` dominates `j`; subtracting target zero counts zero and one from
the full dominated-pair cylinder gives the displayed polynomial. -/
theorem dominated_multiZero_mass {n : ℕ} (p : ℝ) (i j : Fin n) (hji : j ≠ i) :
    (∑ A : BoolMatrix n n, if i ∈ multiZeroRows A ∧ RowLE (A j) (A i)
      then matrixWeight p A else 0) =
      (p+(1-p)^2)^n-p^n-(n : ℝ)*(1-p)^2*p^(n-1) := by
  sorry

/-- Requested four-term finite Bernoulli bound for the actual dense-good-event
complement. This remains unpaid: the dominated-multi-zero mass lemma above,
constant-row cylinder masses, and final four-family union/counting assembly
(including the `choose n 2` unordered row-pair count) are not discharged here.
The canonical cover, singleton failure mass and its entire union bound, and
singleton collision mass are proved independently of this placeholder. -/
theorem denseGoodEvent_complement_mass_le (n : ℕ) (p : ℝ)
    (hn : 2 ≤ n) (hp : 0 < p) (hp1 : p < 1) :
    (∑ A : BoolMatrix n n, if ¬ denseGoodEvent A then matrixWeight p A else 0) ≤
      (n : ℝ)*(p^n+(1-p)^n) +
      (n : ℝ)*((n : ℝ)-1)*((p+(1-p)^2)^n-p^n-(n : ℝ)*(1-p)^2*p^(n-1)) +
      (n : ℝ)^2*((n : ℝ)-1)*(1-p)*p^(n-1)*(1-(1-p)*p)^(n-1) +
      (Nat.choose n 2 : ℝ)*(n : ℝ)*((1-p)*p^(n-1))^2 := by
  sorry

end BilinearComplexity
