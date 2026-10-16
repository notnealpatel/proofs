import Enumerative.HalfZumkeller

set_option autoImplicit false
open Finset

private theorem reservoir_missing {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (R : ι → Finset ℕ) (w : ι → ℕ) (A : Finset ℕ)
    (hdis : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (R i) (R j))
    (hw : ∀ i ∈ F, ∀ r ∈ R i, w i ≤ r)
    (hlt : (∑ a ∈ A, a) < ∑ i ∈ F, w i) :
    ∃ i ∈ F, Disjoint A (R i) := by
  classical
  by_contra h
  have hit : ∀ i ∈ F, ∃ r, r ∈ R i ∧ r ∈ A := by
    intro i hi
    have hn : ¬ Disjoint A (R i) := by
      intro hd
      exact h ⟨i, hi, hd⟩
    obtain ⟨r, hrA, hrR⟩ := (not_disjoint_iff.mp hn)
    exact ⟨r, hrR, hrA⟩
  choose x hxR hxA using hit
  let f : ι → ℕ := fun i => if hi : i ∈ F then x i hi else 0
  have hfR : ∀ i ∈ F, f i ∈ R i := by
    intro i hi
    simpa only [f, dif_pos hi] using hxR i hi
  have hfA : ∀ i ∈ F, f i ∈ A := by
    intro i hi
    simpa only [f, dif_pos hi] using hxA i hi
  have hinj : Set.InjOn f F := by
    intro i hi j hj hij
    by_contra hne
    exact (disjoint_left.mp (hdis i hi j hj hne)) (hfR i hi) (hij ▸ hfR j hj)
  have hsub : F.image f ⊆ A := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hr
    exact hfA i hi
  have hle : (∑ i ∈ F, w i) ≤ ∑ a ∈ A, a := calc
    _ ≤ ∑ i ∈ F, f i := sum_le_sum (fun i hi => hw i hi (f i) (hfR i hi))
    _ = ∑ r ∈ F.image f, r := (sum_image (f := fun r : ℕ => r) hinj).symm
    _ ≤ ∑ a ∈ A, a := sum_le_sum_of_subset hsub
  omega

/-- Disjoint half-sized reservoirs with a combined lower-weight bound force an
 even Zumkeller number to be half-Zumkeller. The index set may be empty. -/
theorem IsZumkeller.isHalfZumkeller_of_reservoirs {n : ℕ} (hz : IsZumkeller n)
    (he : Even n) {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (R : ι → Finset ℕ) (w : ι → ℕ)
    (hR : ∀ i ∈ F, R i ⊆ (n.divisors.erase n).erase (n / 2))
    (hsumR : ∀ i ∈ F, 2 * ∑ r ∈ R i, r = n)
    (hdis : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (R i) (R j))
    (hw : ∀ i ∈ F, ∀ r ∈ R i, w i ≤ r)
    (hbound : (∑ d ∈ n.divisors, d) < 3 * n + 2 * ∑ i ∈ F, w i) :
    IsHalfZumkeller n := by
  classical
  have hn := hz.pos
  have hnd : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_refl n, hn.ne'⟩
  have htwo : 2 * (n / 2) = n := Nat.mul_div_cancel' (even_iff_two_dvd.mp he)
  have hne : n / 2 ≠ n := by omega
  obtain ⟨T, hT, hbal⟩ := (isZumkeller_iff_two_mul_sum_eq_sum_divisors hn).mp hz
  have hTsub := mem_powerset.mp hT
  have horient : ∃ S ⊆ n.divisors, n ∈ S ∧
      2 * ∑ a ∈ S, a = ∑ d ∈ n.divisors, d := by
    by_cases ht : n ∈ T
    · exact ⟨T, hTsub, ht, hbal⟩
    · refine ⟨n.divisors \ T, sdiff_subset, mem_sdiff.mpr ⟨hnd, ht⟩, ?_⟩
      have hs := sum_sdiff (f := fun a : ℕ => a) hTsub
      omega
  obtain ⟨S, hS, hnS, hsumS⟩ := horient
  apply (isHalfZumkeller_iff_endpoint_partition hn he).mpr
  by_cases hhS : n / 2 ∈ S
  · let A := (S.erase n).erase (n / 2)
    have hhalf : n / 2 ∈ S.erase n := mem_erase.mpr ⟨hne, hhS⟩
    have he1 := sum_erase_add (f := fun a : ℕ => a) S hnS
    have he2 := sum_erase_add (f := fun a : ℕ => a) (S.erase n) hhalf
    have hsumA : 2 * ∑ a ∈ A, a + 3 * n = ∑ d ∈ n.divisors, d := by
      dsimp [A]
      omega
    have hlt : (∑ a ∈ A, a) < ∑ i ∈ F, w i := by omega
    obtain ⟨i, hi, hd⟩ := reservoir_missing F R w A hdis hw hlt
    let C := A ∪ R i
    have hsub : C ⊆ n.divisors := by
      intro x hx
      rcases mem_union.mp hx with hx | hx
      · exact hS (mem_of_mem_erase (mem_of_mem_erase hx))
      · exact mem_of_mem_erase (mem_of_mem_erase (hR i hi hx))
    have hnC : n ∉ C := by
      intro hx
      rcases mem_union.mp hx with hx | hx
      · exact (mem_erase.mp (mem_of_mem_erase hx)).1 rfl
      · exact (mem_erase.mp (mem_of_mem_erase (hR i hi hx))).1 rfl
    have hhC : n / 2 ∉ C := by
      intro hx
      rcases mem_union.mp hx with hx | hx
      · exact (mem_erase.mp hx).1 rfl
      · exact (mem_erase.mp (hR i hi hx)).1 rfl
    have hsumC : 2 * ∑ c ∈ C, c + 2 * n = ∑ d ∈ n.divisors, d := by
      dsimp [C]
      rw [sum_union hd]
      have hr := hsumR i hi
      omega
    have hB : insert n C ⊆ n.divisors := insert_subset hnd hsub
    refine ⟨insert n C, hB, mem_insert_self _ _, ?_, ?_⟩
    · simpa only [mem_insert, not_or] using And.intro hne hhC
    · have hiC := sum_insert (f := fun a : ℕ => a) hnC
      have hs := sum_sdiff (f := fun a : ℕ => a) hB
      omega
  · refine ⟨S, hS, hnS, hhS, ?_⟩
    have hs := sum_sdiff (f := fun a : ℕ => a) hS
    omega

/-- A Zumkeller multiple of `280` satisfying `20 σ(n) < 63 n` is half-Zumkeller.
The two reservoirs have weights `14 k` and `7 k`, where `n = 280 k`. -/
theorem IsZumkeller.isHalfZumkeller_of_two_hundred_eighty_dvd {n : ℕ}
    (hz : IsZumkeller n) (h280 : 280 ∣ n)
    (hbound : 20 * (∑ d ∈ n.divisors, d) < 63 * n) : IsHalfZumkeller n := by
  obtain ⟨k, rfl⟩ := h280
  have hk : 0 < k := by have hp := hz.pos; omega
  let R : Bool → Finset ℕ := fun b =>
    if b then {70 * k, 56 * k, 14 * k}
    else {40 * k, 35 * k, 28 * k, 20 * k, 10 * k, 7 * k}
  let w : Bool → ℕ := fun b => if b then 14 * k else 7 * k
  have hsub : ∀ b ∈ (univ : Finset Bool),
      R b ⊆ ((280 * k).divisors.erase (280 * k)).erase (280 * k / 2) := by
    intro b _ r hr
    have hd : r ∣ 280 * k := by
      cases b <;> simp only [R, Bool.false_eq_true, if_false, if_true,
        mem_insert, mem_singleton] at hr
      · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨7, by omega⟩
        · exact ⟨8, by omega⟩
        · exact ⟨10, by omega⟩
        · exact ⟨14, by omega⟩
        · exact ⟨28, by omega⟩
        · exact ⟨40, by omega⟩
      · rcases hr with rfl | rfl | rfl
        · exact ⟨4, by omega⟩
        · exact ⟨5, by omega⟩
        · exact ⟨20, by omega⟩
    have hends : r ≠ 280 * k / 2 ∧ r ≠ 280 * k := by
      cases b <;> simp only [R, Bool.false_eq_true, if_false, if_true,
        mem_insert, mem_singleton] at hr <;> omega
    exact mem_erase.mpr ⟨hends.1, mem_erase.mpr
      ⟨hends.2, Nat.mem_divisors.mpr ⟨hd, by omega⟩⟩⟩
  have hsum : ∀ b ∈ (univ : Finset Bool), 2 * ∑ r ∈ R b, r = 280 * k := by
    intro b _
    cases b <;> dsimp [R]
    all_goals
      simp (disch := (simp only [mem_insert, mem_singleton]; omega)) only
        [sum_insert, sum_singleton]
      omega
  have hdis : ∀ i ∈ (univ : Finset Bool), ∀ j ∈ (univ : Finset Bool),
      i ≠ j → Disjoint (R i) (R j) := by
    intro i _ j _ hne
    apply disjoint_left.mpr
    intro r hi hj
    cases i <;> cases j
    all_goals try exact (hne rfl).elim
    all_goals
      simp only [R, Bool.false_eq_true, if_false, if_true, mem_insert, mem_singleton] at hi hj
      omega
  have hw : ∀ b ∈ (univ : Finset Bool), ∀ r ∈ R b, w b ≤ r := by
    intro b _ r hr
    cases b <;>
      simp only [R, w, Bool.false_eq_true, if_false, if_true, mem_insert, mem_singleton] at *
    all_goals omega
  apply hz.isHalfZumkeller_of_reservoirs (show Even (280 * k) from ⟨140 * k, by omega⟩)
    univ R w hsub hsum hdis hw
  have hweights : (∑ b : Bool, w b) = 21 * k := by
    simp only [Fintype.sum_bool, w, if_true, Bool.false_eq_true, if_false]
    omega
  rw [hweights]
  omega

example : IsZumkeller 12 ∧ Even 12 ∧
    (∀ i ∈ (∅ : Finset Unit), (∅ : Finset ℕ) ⊆ ((12 : ℕ).divisors.erase 12).erase (12 / 2)) ∧
    (∀ i ∈ (∅ : Finset Unit), 2 * ∑ r ∈ (∅ : Finset ℕ), r = 12) ∧
    (∀ i ∈ (∅ : Finset Unit), ∀ j ∈ (∅ : Finset Unit), i ≠ j →
      Disjoint (∅ : Finset ℕ) ∅) ∧
    (∀ i ∈ (∅ : Finset Unit), ∀ r ∈ (∅ : Finset ℕ), 0 ≤ r) ∧
    (∑ d ∈ (12 : ℕ).divisors, d) < 3 * 12 + 2 * ∑ _i ∈ (∅ : Finset Unit), (0 : ℕ) := by
  decide

example : IsHalfZumkeller 12 :=
  (show IsZumkeller 12 by decide).isHalfZumkeller_of_reservoirs (by decide)
    (∅ : Finset Unit) (fun _ => ∅) (fun _ => 0)
    (by simp) (by simp) (by simp) (by simp) (by decide)

example : IsZumkeller 280 ∧ 280 ∣ 280 ∧
    20 * (∑ d ∈ (280 : ℕ).divisors, d) < 63 * 280 := by
  refine ⟨?_, dvd_refl 280, ?_⟩
  · have h40 : IsZumkeller 40 := by
      refine (isZumkeller_iff_exists_subset 40).mpr ⟨by decide, {40, 5}, ?_, ?_⟩ <;> decide
    simpa using (IsZumkeller.mul_of_coprime (m := 40) (n := 7) h40 (by decide))
  · decide

/-- A Zumkeller multiple of `140` with `70 σ(n) < 223 n` is half-Zumkeller.
Three overlapping reservoirs give the transversal lower bound `13 k` for `n = 140 k`. -/
theorem IsZumkeller.isHalfZumkeller_of_one_hundred_forty_dvd {n : ℕ}
    (hz : IsZumkeller n) (h140 : 140 ∣ n)
    (hbound : 70 * (∑ d ∈ n.divisors, d) < 223 * n) : IsHalfZumkeller n := by
  obtain ⟨k, rfl⟩ := h140
  have hn := hz.pos
  have hk : 0 < k := by omega
  have he : Even (140 * k) := ⟨70 * k, by omega⟩
  have hnd : 140 * k ∈ (140 * k).divisors :=
    Nat.mem_divisors.mpr ⟨dvd_refl _, hn.ne'⟩
  have htwo : 2 * (140 * k / 2) = 140 * k := by omega
  have hne : 140 * k / 2 ≠ 140 * k := by omega
  obtain ⟨T, hT, hbal⟩ := (isZumkeller_iff_two_mul_sum_eq_sum_divisors hn).mp hz
  have hTsub := mem_powerset.mp hT
  have horient : ∃ S ⊆ (140 * k).divisors, 140 * k ∈ S ∧
      2 * ∑ a ∈ S, a = ∑ d ∈ (140 * k).divisors, d := by
    by_cases ht : 140 * k ∈ T
    · exact ⟨T, hTsub, ht, hbal⟩
    · refine ⟨(140 * k).divisors \ T, sdiff_subset, mem_sdiff.mpr ⟨hnd, ht⟩, ?_⟩
      have hs := sum_sdiff (f := fun a : ℕ => a) hTsub
      omega
  obtain ⟨S, hS, hnS, hsumS⟩ := horient
  apply (isHalfZumkeller_iff_endpoint_partition hn he).mpr
  by_cases hhS : 140 * k / 2 ∈ S
  · let A := (S.erase (140 * k)).erase (140 * k / 2)
    have hhalf : 140 * k / 2 ∈ S.erase (140 * k) := mem_erase.mpr ⟨hne, hhS⟩
    have he1 := sum_erase_add (f := fun a : ℕ => a) S hnS
    have he2 := sum_erase_add (f := fun a : ℕ => a) (S.erase (140 * k)) hhalf
    have hsumA : 2 * ∑ a ∈ A, a + 420 * k = ∑ d ∈ (140 * k).divisors, d := by
      dsimp [A]
      omega
    have hlt : (∑ a ∈ A, a) < 13 * k := by omega
    let R1 : Finset ℕ := {7 * k, 28 * k, 35 * k}
    let R2 : Finset ℕ := {5 * k, 10 * k, 20 * k, 35 * k}
    let R3 : Finset ℕ := {k, 14 * k, 20 * k, 35 * k}
    have hsmall : ∀ r ∈ A, r < 13 * k := by
      intro r hr
      have hle : r ≤ ∑ a ∈ A, a := single_le_sum (fun x _ => Nat.zero_le x) hr
      omega
    have hmissing : ∃ R ∈ ({R1, R2, R3} : Finset (Finset ℕ)), Disjoint A R := by
      by_cases hd1 : Disjoint A R1
      · exact ⟨R1, by simp, hd1⟩
      by_cases hd2 : Disjoint A R2
      · exact ⟨R2, by simp, hd2⟩
      by_cases hd3 : Disjoint A R3
      · exact ⟨R3, by simp, hd3⟩
      obtain ⟨x, hxA, hxR⟩ := not_disjoint_iff.mp hd1
      have hxlt := hsmall x hxA
      have h7 : 7 * k ∈ A := by
        simp only [R1, mem_insert, mem_singleton] at hxR
        rcases hxR with rfl | rfl | rfl <;> first | exact hxA | omega
      obtain ⟨y, hyA, hyR⟩ := not_disjoint_iff.mp hd2
      have hylt := hsmall y hyA
      have h10 : 10 * k ∉ A := by
        intro h10A
        have hsub : ({7 * k, 10 * k} : Finset ℕ) ⊆ A := by
          intro r hr
          simp only [mem_insert, mem_singleton] at hr
          rcases hr with rfl | rfl
          · exact h7
          · exact h10A
        have hle := sum_le_sum_of_subset (f := fun r : ℕ => r) hsub
        have hs : (∑ r ∈ ({7 * k, 10 * k} : Finset ℕ), r) = 17 * k := by
          simp (disch := (simp only [mem_singleton]; omega)) only [sum_insert, sum_singleton]
          omega
        omega
      have h5 : 5 * k ∈ A := by
        simp only [R2, mem_insert, mem_singleton] at hyR
        rcases hyR with rfl | rfl | rfl | rfl
        · exact hyA
        · exact False.elim (h10 hyA)
        · omega
        · omega
      obtain ⟨z, hzA, hzR⟩ := not_disjoint_iff.mp hd3
      have hzlt := hsmall z hzA
      have h1 : k ∈ A := by
        simp only [R3, mem_insert, mem_singleton] at hzR
        rcases hzR with rfl | rfl | rfl | rfl <;> first | exact hzA | omega
      have hsub : ({k, 5 * k, 7 * k} : Finset ℕ) ⊆ A := by
        intro r hr
        simp only [mem_insert, mem_singleton] at hr
        rcases hr with rfl | rfl | rfl
        · exact h1
        · exact h5
        · exact h7
      have hle := sum_le_sum_of_subset (f := fun r : ℕ => r) hsub
      have hs : (∑ r ∈ ({k, 5 * k, 7 * k} : Finset ℕ), r) = 13 * k := by
        simp (disch := (simp only [mem_insert, mem_singleton]; omega)) only
          [sum_insert, sum_singleton]
        omega
      omega
    obtain ⟨R, hRmem, hd⟩ := hmissing
    have hcases : R = R1 ∨ R = R2 ∨ R = R3 := by simpa using hRmem
    have helig : ∀ r ∈ R, r ∣ 140 * k ∧ r ≠ 140 * k ∧ r ≠ 140 * k / 2 := by
      intro r hr
      have hvalues : r = k ∨ r = 5 * k ∨ r = 7 * k ∨ r = 10 * k ∨
          r = 14 * k ∨ r = 20 * k ∨ r = 28 * k ∨ r = 35 * k := by
        rcases hcases with rfl | rfl | rfl <;>
          simp only [R1, R2, R3, mem_insert, mem_singleton] at hr <;> omega
      rcases hvalues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals refine ⟨?_, by omega, by omega⟩
      · exact ⟨140, by omega⟩
      · exact ⟨28, by omega⟩
      · exact ⟨20, by omega⟩
      · exact ⟨14, by omega⟩
      · exact ⟨10, by omega⟩
      · exact ⟨7, by omega⟩
      · exact ⟨5, by omega⟩
      · exact ⟨4, by omega⟩
    have hsumR : 2 * ∑ r ∈ R, r = 140 * k := by
      rcases hcases with rfl | rfl | rfl <;> dsimp [R1, R2, R3]
      all_goals
        simp (disch := (simp only [mem_insert, mem_singleton]; omega)) only
          [sum_insert, sum_singleton]
        omega
    let C := A ∪ R
    have hsub : C ⊆ (140 * k).divisors := by
      intro x hx
      rcases mem_union.mp hx with hx | hx
      · exact hS (mem_of_mem_erase (mem_of_mem_erase hx))
      · exact Nat.mem_divisors.mpr ⟨(helig x hx).1, hn.ne'⟩
    have hnC : 140 * k ∉ C := by
      intro hx
      rcases mem_union.mp hx with hx | hx
      · exact (mem_erase.mp (mem_of_mem_erase hx)).1 rfl
      · exact (helig _ hx).2.1 rfl
    have hhC : 140 * k / 2 ∉ C := by
      intro hx
      rcases mem_union.mp hx with hx | hx
      · exact (mem_erase.mp hx).1 rfl
      · exact (helig _ hx).2.2 rfl
    have hsumC : 2 * ∑ c ∈ C, c + 2 * (140 * k) = ∑ d ∈ (140 * k).divisors, d := by
      dsimp [C]
      rw [sum_union hd]
      omega
    have hB : insert (140 * k) C ⊆ (140 * k).divisors := insert_subset hnd hsub
    refine ⟨insert (140 * k) C, hB, mem_insert_self _ _, ?_, ?_⟩
    · simpa only [mem_insert, not_or] using And.intro hne hhC
    · have hiC := sum_insert (f := fun a : ℕ => a) hnC
      have hs := sum_sdiff (f := fun a : ℕ => a) hB
      omega
  · refine ⟨S, hS, hnS, hhS, ?_⟩
    have hs := sum_sdiff (f := fun a : ℕ => a) hS
    omega
