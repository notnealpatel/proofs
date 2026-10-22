import Sorry.Enumerative.HalfZumkeller

set_option autoImplicit false

open Finset

private theorem mem_blocks {m a x : ℕ} :
    x ∈ (m * 2 ^ a).divisors ↔
      ∃ d ∈ m.divisors, ∃ i ≤ a, x = d * 2 ^ i := by
  rw [Nat.divisors_mul, Finset.mem_mul]
  constructor
  · rintro ⟨d, hd, q, hq, rfl⟩
    obtain ⟨i, hi, rfl⟩ := (Nat.mem_divisors_prime_pow Nat.prime_two a).mp hq
    exact ⟨d, hd, i, hi, rfl⟩
  · rintro ⟨d, hd, i, hi, rfl⟩
    exact ⟨d, hd, 2 ^ i,
      (Nat.mem_divisors_prime_pow Nat.prime_two a).mpr ⟨i, hi, rfl⟩, rfl⟩

private theorem blocks_split (m a : ℕ) :
    (m * 2 ^ (a + 1)).divisors = (m * 2 ^ a).divisors ∪
      (m.divisors.image (fun d => d * 2 ^ a)).image (fun d => d * 2) := by
  ext x
  simp only [Finset.mem_union, Finset.mem_image]
  constructor
  · intro hx
    obtain ⟨d, hd, i, hi, rfl⟩ := mem_blocks.mp hx
    by_cases hia : i ≤ a
    · exact Or.inl (mem_blocks.mpr ⟨d, hd, i, hia, rfl⟩)
    · have hie : i = a + 1 := by omega
      right
      exact ⟨d * 2 ^ a, ⟨d, hd, rfl⟩, by rw [hie, pow_succ, mul_assoc]⟩
  · rintro (hx | ⟨y, ⟨d, hd, rfl⟩, rfl⟩)
    · obtain ⟨d, hd, i, hi, rfl⟩ := mem_blocks.mp hx
      exact mem_blocks.mpr ⟨d, hd, i, by omega, rfl⟩
    · exact mem_blocks.mpr ⟨d, hd, a + 1, le_rfl, by rw [pow_succ, mul_assoc]⟩

private theorem blocks_disjoint {m a : ℕ} (hcop : m.Coprime 2) :
    Disjoint (m * 2 ^ a).divisors
      ((m.divisors.image (fun d => d * 2 ^ a)).image (fun d => d * 2)) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨d, hd, i, hi, hxi⟩ := mem_blocks.mp hx
  obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hy
  obtain ⟨q, hq, hqy⟩ := Finset.mem_image.mp hy
  have heq : d * 2 ^ i = q * 2 ^ (a + 1) := by
    rw [← hxi, ← hyx, ← hqy, pow_succ, mul_assoc]
  have hpi : 2 ^ i ∈ (2 ^ (a + 1)).divisors :=
    (Nat.mem_divisors_prime_pow Nat.prime_two _).mpr ⟨i, by omega, rfl⟩
  have hpj : 2 ^ (a + 1) ∈ (2 ^ (a + 1)).divisors :=
    (Nat.mem_divisors_prime_pow Nat.prime_two _).mpr ⟨a + 1, le_rfl, rfl⟩
  have hpairs : (d, 2 ^ i) = (q, 2 ^ (a + 1)) :=
    (hcop.pow_right _).mul_injOn_divisors (Finset.mem_product.mpr ⟨hd, hpi⟩)
      (Finset.mem_product.mpr ⟨hq, hpj⟩) heq
  have hexp : i = a + 1 :=
    Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) (congrArg Prod.snd hpairs)
  omega

private theorem flip_top {D T A : Finset ℕ} (hA : A ⊆ D) (hT : T ⊆ D)
    (hdisj : Disjoint D (T.image (fun d => d * 2)))
    (hhalf : 2 * ∑ x ∈ A, x = ∑ x ∈ D, x) :
    ∃ B ⊆ D ∪ T.image (fun d => d * 2),
      2 * ∑ x ∈ B, x = ∑ x ∈ D ∪ T.image (fun d => d * 2), x := by
  let B := (A \ T) ∪ (T \ A) ∪ ((A ∩ T).image (fun d => d * 2))
  have hlow : (A \ T) ∪ (T \ A) ⊆ D :=
    Finset.union_subset (Finset.sdiff_subset.trans hA) (Finset.sdiff_subset.trans hT)
  have himage : (A ∩ T).image (fun d => d * 2) ⊆ T.image (fun d => d * 2) :=
    Finset.image_subset_image Finset.inter_subset_right
  have hsmall : Disjoint ((A \ T) ∪ (T \ A))
      ((A ∩ T).image (fun d => d * 2)) := hdisj.mono hlow himage
  have hdiff : Disjoint (A \ T) (T \ A) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  have hsum (S : Finset ℕ) :
      ∑ x ∈ S.image (fun d => d * 2), x = 2 * ∑ x ∈ S, x := by
    rw [Finset.sum_image]
    · simp_rw [mul_comm _ 2]
      exact (Finset.mul_sum S (fun x => x) 2).symm
    · intro x hx y hy hxy
      dsimp only at hxy
      omega
  have hsplitA : (∑ x ∈ A \ T, x) + (∑ x ∈ A ∩ T, x) = ∑ x ∈ A, x := by
    have hs := Finset.sum_sdiff (f := fun x : ℕ => x)
      (Finset.inter_subset_left : A ∩ T ⊆ A)
    have he : A \ (A ∩ T) = A \ T := by ext x; simp
    rwa [he] at hs
  have hsplitT : (∑ x ∈ T \ A, x) + (∑ x ∈ A ∩ T, x) = ∑ x ∈ T, x := by
    have hs := Finset.sum_sdiff (f := fun x : ℕ => x)
      (Finset.inter_subset_right : A ∩ T ⊆ T)
    have he : T \ (A ∩ T) = T \ A := by ext x; simp
    rwa [he] at hs
  refine ⟨B, Finset.union_subset_union hlow himage, ?_⟩
  dsimp only [B]
  rw [Finset.sum_union hsmall, Finset.sum_union hdiff, hsum,
    Finset.sum_union hdisj, hsum]
  omega

/-- Doubling a Zumkeller number preserves its equal-sum divisor partition, with no
parity assumption on the original number. -/
theorem IsZumkeller.mul_two {n : ℕ} (hn : IsZumkeller n) : IsZumkeller (n * 2) := by
  obtain ⟨a, m, hm, hfactor⟩ := Nat.exists_eq_two_pow_mul_odd hn.pos.ne'
  have hn_eq : n = m * 2 ^ a := by rw [hfactor, mul_comm]
  have hcop : m.Coprime 2 :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr hm.not_two_dvd_nat).symm
  obtain ⟨A, hApow, hhalf⟩ :=
    (isZumkeller_iff_two_mul_sum_eq_sum_divisors hn.pos).mp hn
  have hA : A ⊆ (m * 2 ^ a).divisors := by
    simpa only [← hn_eq] using Finset.mem_powerset.mp hApow
  have hT : m.divisors.image (fun d => d * 2 ^ a) ⊆ (m * 2 ^ a).divisors := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    exact mem_blocks.mpr ⟨d, hd, a, le_rfl, rfl⟩
  obtain ⟨B, hBsub, hBhalf⟩ := flip_top hA hT (blocks_disjoint hcop)
    (by simpa only [← hn_eq] using hhalf)
  have hnext : n * 2 = m * 2 ^ (a + 1) := by rw [hn_eq, pow_succ, mul_assoc]
  apply (isZumkeller_iff_two_mul_sum_eq_sum_divisors (Nat.mul_pos hn.pos (by decide))).mpr
  rw [hnext, blocks_split]
  exact ⟨B, Finset.mem_powerset.mpr hBsub, hBhalf⟩

/-- A Zumkeller number remains Zumkeller after multiplication by any nonnegative
power of two, including exponent zero. -/
theorem IsZumkeller.mul_two_pow {n : ℕ} (hn : IsZumkeller n) (k : ℕ) :
    IsZumkeller (n * 2 ^ k) := by
  induction k with
  | zero => simpa using hn
  | succ k ih => simpa only [pow_succ, ← mul_assoc] using ih.mul_two

/-- In particular, multiplication by four preserves the Zumkeller property. -/
theorem IsZumkeller.mul_four {n : ℕ} (hn : IsZumkeller n) : IsZumkeller (n * 4) := by
  simpa only [mul_assoc, show (2 : ℕ) * 2 = 4 from rfl] using hn.mul_two.mul_two

/-- Doubling a Zumkeller number gives a half-Zumkeller number: the partition
uses all positive proper divisors of `2 * n`, including `n`. -/
theorem IsZumkeller.isHalfZumkeller_mul_two {n : ℕ} (hz : IsZumkeller n) :
    IsHalfZumkeller (n * 2) := by
  obtain ⟨a, m, hm, hfactor⟩ := Nat.exists_eq_two_pow_mul_odd hz.pos.ne'
  have hn_eq : n = m * 2 ^ a := by rw [hfactor, mul_comm]
  have hcop : m.Coprime 2 :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr hm.not_two_dvd_nat).symm
  let D := n.divisors
  let U := m.divisors.image (fun d => d * 2 ^ a)
  let T := U.erase n
  have hU : U ⊆ D := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    rw [show D = (m * 2 ^ a).divisors from congrArg Nat.divisors hn_eq]
    exact mem_blocks.mpr ⟨d, hd, a, le_rfl, rfl⟩
  have hdisj : Disjoint D (U.image (fun d => d * 2)) := by
    simpa only [D, U, hn_eq] using blocks_disjoint (a := a) hcop
  have hT : T ⊆ D := (Finset.erase_subset n U).trans hU
  have hdisjT : Disjoint D (T.image (fun d => d * 2)) :=
    hdisj.mono_right (Finset.image_subset_image (Finset.erase_subset n U))
  have hsplit : (n * 2).divisors = D ∪ U.image (fun d => d * 2) := by
    have hnext : n * 2 = m * 2 ^ (a + 1) := by rw [hn_eq, pow_succ, mul_assoc]
    rw [hnext]
    simpa only [D, U, hn_eq] using blocks_split m a
  have hnot : n * 2 ∉ D := by
    intro hx
    have hle : n * 2 ≤ n := Nat.le_of_dvd hz.pos (Nat.mem_divisors.mp hx).1
    have hp := hz.pos
    omega
  have hproper : (n * 2).divisors.erase (n * 2) =
      D ∪ T.image (fun d => d * 2) := by
    rw [hsplit, Finset.erase_union_distrib, Finset.erase_eq_of_notMem hnot]
    rw [show T.image (fun d => d * 2) =
      (U.image (fun d => d * 2)).erase (n * 2) from
      Finset.image_erase (fun x y hxy => by omega) U n]
  obtain ⟨A, hApow, hhalf⟩ :=
    (isZumkeller_iff_two_mul_sum_eq_sum_divisors hz.pos).mp hz
  obtain ⟨B, hB, hbal⟩ := flip_top (D := D) (T := T)
    (Finset.mem_powerset.mp hApow) hT hdisjT hhalf
  have hBproper : B ⊆ (n * 2).divisors.erase (n * 2) := by
    rw [hproper]
    exact hB
  refine ⟨Nat.mul_pos hz.pos (by decide), B, hBproper, ?_⟩
  have hsum := Finset.sum_sdiff (f := fun x : ℕ => x) hBproper
  rw [hproper] at hsum ⊢
  omega

/-- Multiplication of a Zumkeller number by a positive power of two gives a
half-Zumkeller number. -/
theorem IsZumkeller.isHalfZumkeller_mul_two_pow_succ {n : ℕ}
    (hz : IsZumkeller n) (k : ℕ) : IsHalfZumkeller (n * 2 ^ (k + 1)) := by
  simpa only [pow_succ, ← mul_assoc] using (hz.mul_two_pow k).isHalfZumkeller_mul_two

example : IsHalfZumkeller 12 := IsZumkeller.isHalfZumkeller_mul_two (n := 6) (by decide)

example : IsZumkeller 6 := by decide
example : IsZumkeller (6 * 2 ^ 0) := IsZumkeller.mul_two_pow (by decide) 0
example : IsZumkeller 24 := IsZumkeller.mul_four (n := 6) (by decide)
example : IsZumkeller 12 := IsZumkeller.mul_two (n := 6) (by decide)
example : IsZumkeller 48 := IsZumkeller.mul_two_pow (n := 6) (by decide) 3
