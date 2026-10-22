import Enumerative.IsZumkeller

/-!
# Half-Zumkeller numbers and endpoint exchange

Proper-divisor partitions, the endpoint criterion of Rao–Peng (Remark h4),
and a sufficient exchange criterion. No novelty claim is made for the latter.
-/

set_option autoImplicit false
open Finset

/-- A positive number is half-Zumkeller when its proper divisors have an
 equal-sum partition. -/
def IsHalfZumkeller (n : ℕ) : Prop :=
  0 < n ∧ ∃ A ⊆ n.divisors.erase n,
    ∑ a ∈ A, a = ∑ d ∈ n.divisors.erase n \ A, d

example : IsHalfZumkeller 12 := by
  have hd : (12 : ℕ).divisors = {1, 2, 3, 4, 6, 12} := by decide
  refine ⟨by decide, {2, 6}, ?_, ?_⟩ <;> rw [hd] <;> decide

example : ¬ IsHalfZumkeller 0 := by
  rintro ⟨h, -⟩
  omega

private theorem orient (D : Finset ℕ) (x : ℕ) (hx : x ∈ D)
    (hex : ∃ S ⊆ D, 2 * ∑ a ∈ S, a = ∑ d ∈ D, d) :
    ∃ S ⊆ D, x ∈ S ∧ 2 * ∑ a ∈ S, a = ∑ d ∈ D, d := by
  obtain ⟨S, hS, heq⟩ := hex
  by_cases h : x ∈ S
  · exact ⟨S, hS, h, heq⟩
  · refine ⟨D \ S, sdiff_subset, mem_sdiff.mpr ⟨hx, h⟩, ?_⟩
    have hs := sum_sdiff (f := fun a : ℕ => a) hS
    omega

private theorem half_data {n : ℕ} (hn : 0 < n) (he : Even n) :
    n ∈ n.divisors ∧ n / 2 ∈ n.divisors ∧ n / 2 ≠ n ∧ 2 * (n / 2) = n := by
  have hd : 2 ∣ n := even_iff_two_dvd.mp he
  have hmul := Nat.mul_div_cancel' hd
  refine ⟨Nat.mem_divisors.mpr ⟨dvd_refl n, hn.ne'⟩,
    Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hd, hn.ne'⟩, ?_, hmul⟩
  omega

private theorem half_core {n : ℕ} (hn : 0 < n) (he : Even n) :
    IsHalfZumkeller n ↔ ∃ C ⊆ n.divisors, n ∉ C ∧ n / 2 ∉ C ∧
      2 * ∑ c ∈ C, c + 2 * n = ∑ d ∈ n.divisors, d := by
  obtain ⟨hnd, hhd, hne, htwo⟩ := half_data hn he
  have hp : ∑ d ∈ n.divisors.erase n, d + n = ∑ d ∈ n.divisors, d :=
    sum_erase_add _ _ hnd
  constructor
  · rintro ⟨-, A, hA, hsum⟩
    have hs := sum_sdiff (f := fun a : ℕ => a) hA
    obtain ⟨S, hS, hhS, hbal⟩ := orient (n.divisors.erase n) (n / 2)
      (mem_erase.mpr ⟨hne, hhd⟩) ⟨A, hA, by omega⟩
    refine ⟨S.erase (n / 2), fun x hx => mem_of_mem_erase (hS (mem_of_mem_erase hx)),
      ?_, notMem_erase _ _, ?_⟩
    · intro hx
      exact (mem_erase.mp (hS (mem_of_mem_erase hx))).1 rfl
    · have hs' := sum_erase_add (f := fun a : ℕ => a) S hhS
      omega
  · rintro ⟨C, hC, hnC, hhC, hsum⟩
    have hsub : insert (n / 2) C ⊆ n.divisors.erase n := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact mem_erase.mpr ⟨hne, hhd⟩
      · exact mem_erase.mpr ⟨fun heq => hnC (heq ▸ hx), hC hx⟩
    refine ⟨hn, insert (n / 2) C, hsub, ?_⟩
    have hi : ∑ a ∈ insert (n / 2) C, a = n / 2 + ∑ c ∈ C, c :=
      sum_insert hhC
    have hs := sum_sdiff (f := fun a : ℕ => a) hsub
    omega

/-- For a positive even number, half-Zumkeller is equivalent to an equal-sum
 divisor partition oriented to contain `n` and exclude `n / 2`. -/
theorem isHalfZumkeller_iff_endpoint_partition {n : ℕ} (hn : 0 < n) (he : Even n) :
    IsHalfZumkeller n ↔ ∃ B ⊆ n.divisors, n ∈ B ∧ n / 2 ∉ B ∧
      ∑ b ∈ B, b = ∑ d ∈ n.divisors \ B, d := by
  obtain ⟨hnd, -, hne, -⟩ := half_data hn he
  rw [half_core hn he]
  constructor
  · rintro ⟨C, hC, hnC, hhC, hsum⟩
    have hsub : insert n C ⊆ n.divisors := insert_subset hnd hC
    refine ⟨insert n C, hsub, mem_insert_self _ _, ?_, ?_⟩
    · simpa only [mem_insert, not_or] using And.intro hne hhC
    · have hi := sum_insert (f := fun a : ℕ => a) hnC
      have hs := sum_sdiff (f := fun a : ℕ => a) hsub
      omega
  · rintro ⟨B, hB, hnB, hhB, hsum⟩
    refine ⟨B.erase n, fun x hx => hB (mem_of_mem_erase hx), notMem_erase _ _,
      fun hx => hhB (mem_of_mem_erase hx), ?_⟩
    have hi := sum_erase_add (f := fun a : ℕ => a) B hnB
    have hs := sum_sdiff (f := fun a : ℕ => a) hB
    omega

/-- Exchange criterion: a half-sized reservoir of proper divisors, excluding
 `n / 2`, and the stated strict bounds force a Zumkeller number to be half-Zumkeller. -/
theorem IsZumkeller.isHalfZumkeller_of_exchange {n : ℕ} (hz : IsZumkeller n)
    (he : Even n) (R : Finset ℕ) (hR : R ⊆ (n.divisors.erase n).erase (n / 2))
    (hsumR : 2 * ∑ r ∈ R, r = n)
    (hbound : ∀ r ∈ R, (∑ d ∈ n.divisors, d) < 3 * n + 2 * r) :
    IsHalfZumkeller n := by
  obtain ⟨hnd, -, hne, htwo⟩ := half_data hz.pos he
  obtain ⟨T, hT, hbal⟩ :=
    (isZumkeller_iff_two_mul_sum_eq_sum_divisors hz.pos).mp hz
  obtain ⟨S, hS, hnS, hsumS⟩ := orient n.divisors n hnd
    ⟨T, mem_powerset.mp hT, hbal⟩
  by_cases hhS : n / 2 ∈ S
  · let A := (S.erase n).erase (n / 2)
    have hhalf : n / 2 ∈ S.erase n := mem_erase.mpr ⟨hne, hhS⟩
    have he1 := sum_erase_add (f := fun a : ℕ => a) S hnS
    have he2 := sum_erase_add (f := fun a : ℕ => a) (S.erase n) hhalf
    have hsumA : 2 * ∑ a ∈ A, a + 3 * n = ∑ d ∈ n.divisors, d := by
      dsimp [A]
      omega
    have hdis : Disjoint A R := by
      apply disjoint_left.mpr
      intro r hrA hrR
      have hle : r ≤ ∑ a ∈ A, a := single_le_sum (fun x _ => Nat.zero_le x) hrA
      have hb := hbound r hrR
      omega
    have hsub : A ∪ R ⊆ n.divisors := by
      intro x hx
      rcases mem_union.mp hx with hx | hx
      · exact hS (mem_of_mem_erase (mem_of_mem_erase hx))
      · exact mem_of_mem_erase (mem_of_mem_erase (hR hx))
    apply (half_core hz.pos he).mpr
    refine ⟨A ∪ R, hsub, ?_, ?_, ?_⟩
    · intro hx
      rcases mem_union.mp hx with hx | hx
      · exact (mem_erase.mp (mem_of_mem_erase hx)).1 rfl
      · exact (mem_erase.mp (mem_of_mem_erase (hR hx))).1 rfl
    · intro hx
      rcases mem_union.mp hx with hx | hx
      · exact (mem_erase.mp hx).1 rfl
      · exact (mem_erase.mp (hR hx)).1 rfl
    · rw [sum_union hdis]
      omega
  · apply (isHalfZumkeller_iff_endpoint_partition hz.pos he).mpr
    refine ⟨S, hS, hnS, hhS, ?_⟩
    have hs := sum_sdiff (f := fun a : ℕ => a) hS
    omega

/-- A Zumkeller multiple of `20` with `10 σ(n) < 31 n` is half-Zumkeller.
The exchange reservoir is `{n / 4, n / 5, n / 20}`. -/
theorem IsZumkeller.isHalfZumkeller_of_twenty_dvd {n : ℕ} (hz : IsZumkeller n)
    (h20 : 20 ∣ n) (hbound : 10 * (∑ d ∈ n.divisors, d) < 31 * n) :
    IsHalfZumkeller n := by
  obtain ⟨k, rfl⟩ := h20
  have hk : 0 < k := by have hp := hz.pos; omega
  have he : Even (20 * k) := ⟨10 * k, by omega⟩
  have hne54 : 5 * k ≠ 4 * k := by omega
  have hne51 : 5 * k ≠ k := by omega
  have hne41 : 4 * k ≠ k := by omega
  have hd5 : 5 * k ∣ 20 * k := ⟨4, by omega⟩
  have hd4 : 4 * k ∣ 20 * k := ⟨5, by omega⟩
  have hd1 : k ∣ 20 * k := ⟨20, by omega⟩
  have hsub : ({5 * k, 4 * k, k} : Finset ℕ) ⊆
      ((20 * k).divisors.erase (20 * k)).erase (20 * k / 2) := by
    intro r hr
    have hcases : r = 5 * k ∨ r = 4 * k ∨ r = k := by simpa using hr
    rcases hcases with rfl | rfl | rfl
    all_goals
      apply mem_erase.mpr
      constructor
      · omega
      · apply mem_erase.mpr
        constructor
        · omega
        · apply Nat.mem_divisors.mpr
          constructor
          · assumption
          · omega
  have hsum : 2 * ∑ r ∈ ({5 * k, 4 * k, k} : Finset ℕ), r = 20 * k := by
    simp only [sum_insert, mem_insert, mem_singleton, hne54, hne51, hne41,
      or_self, not_false_eq_true, sum_singleton]
    omega
  apply hz.isHalfZumkeller_of_exchange he {5 * k, 4 * k, k} hsub hsum
  intro r hr
  have hcases : r = 5 * k ∨ r = 4 * k ∨ r = k := by simpa using hr
  rcases hcases with rfl | rfl | rfl <;> omega
