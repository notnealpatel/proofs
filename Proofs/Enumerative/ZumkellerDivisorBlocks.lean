import Enumerative.IsZumkeller

set_option autoImplicit false

open Finset

private theorem mem_prime_blocks {p m e x : ℕ} (hp : p.Prime) :
    x ∈ (m * p ^ e).divisors ↔
      ∃ d ∈ m.divisors, ∃ i ≤ e, x = d * p ^ i := by
  rw [Nat.divisors_mul, Finset.mem_mul]
  constructor
  · rintro ⟨d, hd, q, hq, rfl⟩
    obtain ⟨i, hi, rfl⟩ := (Nat.mem_divisors_prime_pow hp e).mp hq
    exact ⟨d, hd, i, hi, rfl⟩
  · rintro ⟨d, hd, i, hi, rfl⟩
    exact ⟨d, hd, p ^ i, (Nat.mem_divisors_prime_pow hp e).mpr ⟨i, hi, rfl⟩, rfl⟩

private theorem prime_blocks_split {p m a b : ℕ} (hp : p.Prime) :
    (m * p ^ (a + 1 + b)).divisors =
      (m * p ^ a).divisors ∪
        (m * p ^ b).divisors.image (fun d => p ^ (a + 1) * d) := by
  ext x
  simp only [Finset.mem_union, Finset.mem_image]
  constructor
  · intro hx
    obtain ⟨d, hd, i, hi, rfl⟩ := (mem_prime_blocks hp).mp hx
    by_cases hia : i ≤ a
    · exact Or.inl ((mem_prime_blocks hp).mpr ⟨d, hd, i, hia, rfl⟩)
    · right
      have hik : a + 1 ≤ i := by omega
      refine ⟨d * p ^ (i - (a + 1)),
        (mem_prime_blocks hp).mpr ⟨d, hd, i - (a + 1), by omega, rfl⟩, ?_⟩
      calc
        p ^ (a + 1) * (d * p ^ (i - (a + 1))) =
            d * p ^ ((a + 1) + (i - (a + 1))) := by rw [pow_add]; ring
        _ = d * p ^ i := by rw [Nat.add_sub_of_le hik]
  · rintro (hx | ⟨y, hy, rfl⟩)
    · obtain ⟨d, hd, i, hi, rfl⟩ := (mem_prime_blocks hp).mp hx
      exact (mem_prime_blocks hp).mpr ⟨d, hd, i, by omega, rfl⟩
    · obtain ⟨d, hd, i, hi, rfl⟩ := (mem_prime_blocks hp).mp hy
      refine (mem_prime_blocks hp).mpr ⟨d, hd, a + 1 + i, by omega, ?_⟩
      rw [pow_add]
      ring

private theorem prime_blocks_disjoint {p m a b : ℕ} (hp : p.Prime)
    (hpm : ¬p ∣ m) :
    Disjoint (m * p ^ a).divisors
      ((m * p ^ b).divisors.image (fun d => p ^ (a + 1) * d)) := by
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  obtain ⟨d, hd, i, hi, hxi⟩ := (mem_prime_blocks hp).mp hx
  obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx'
  obtain ⟨q, hq, j, hj, hyj⟩ := (mem_prime_blocks hp).mp hy
  have hpowi : p ^ i ∈ (p ^ (a + 1 + b)).divisors :=
    (Nat.mem_divisors_prime_pow hp _).mpr ⟨i, by omega, rfl⟩
  have hpowj : p ^ (a + 1 + j) ∈ (p ^ (a + 1 + b)).divisors :=
    (Nat.mem_divisors_prime_pow hp _).mpr ⟨a + 1 + j, by omega, rfl⟩
  have heq : d * p ^ i = q * p ^ (a + 1 + j) := by
    calc
      d * p ^ i = x := hxi.symm
      _ = p ^ (a + 1) * (q * p ^ j) := by rw [← hxy, hyj]
      _ = q * p ^ (a + 1 + j) := by rw [pow_add]; ring
  have hcop : m.Coprime (p ^ (a + 1 + b)) :=
    ((hp.coprime_iff_not_dvd.mpr hpm).symm).pow_right _
  have hpairs : (d, p ^ i) = (q, p ^ (a + 1 + j)) :=
    hcop.mul_injOn_divisors (Finset.mem_product.mpr ⟨hd, hpowi⟩)
      (Finset.mem_product.mpr ⟨hq, hpowj⟩) heq
  have hexp : i = a + 1 + j :=
    Nat.pow_right_injective hp.two_le (congrArg Prod.snd hpairs)
  omega

/-- Two balanced prime-power divisor blocks concatenate: the second block is
scaled by `p^(a+1)`, beyond all exponents occurring in the first block. -/
theorem IsZumkeller.prime_power_concat {p m a b : ℕ} (hp : p.Prime)
    (hpm : ¬p ∣ m) (ha : IsZumkeller (m * p ^ a))
    (hb : IsZumkeller (m * p ^ b)) : IsZumkeller (m * p ^ (a + 1 + b)) := by
  have hm : 0 < m := by
    by_contra h
    have hm0 : m = 0 := by omega
    have hz : IsZumkeller 0 := by simpa [hm0] using ha
    exact not_isZumkeller_zero hz
  have hpos : 0 < m * p ^ (a + 1 + b) := Nat.mul_pos hm (pow_pos hp.pos _)
  obtain ⟨A, hA, hAsum⟩ :=
    (isZumkeller_iff_two_mul_sum_eq_sum_divisors ha.pos).mp ha
  obtain ⟨B, hB, hBsum⟩ :=
    (isZumkeller_iff_two_mul_sum_eq_sum_divisors hb.pos).mp hb
  have hAsub : A ⊆ (m * p ^ a).divisors := Finset.mem_powerset.mp hA
  have hBsub : B ⊆ (m * p ^ b).divisors := Finset.mem_powerset.mp hB
  let c := p ^ (a + 1)
  have hc : 0 < c := pow_pos hp.pos _
  have hinj : Function.Injective (fun d : ℕ => c * d) :=
    fun _ _ h => Nat.eq_of_mul_eq_mul_left hc h
  have hsum (S : Finset ℕ) :
      ∑ x ∈ S.image (fun d => c * d), x = c * ∑ d ∈ S, d := by
    rw [Finset.sum_image (fun _ _ _ _ h => hinj h), Finset.mul_sum]
  have hdisj : Disjoint (m * p ^ a).divisors
      ((m * p ^ b).divisors.image (fun d => c * d)) :=
    prime_blocks_disjoint hp hpm
  have hsmall : Disjoint A (B.image (fun d => c * d)) :=
    hdisj.mono hAsub (Finset.image_subset_image hBsub)
  apply (isZumkeller_iff_two_mul_sum_eq_sum_divisors hpos).mpr
  refine ⟨A ∪ B.image (fun d => c * d), Finset.mem_powerset.mpr ?_, ?_⟩
  · rw [prime_blocks_split hp]
    exact Finset.union_subset_union hAsub (Finset.image_subset_image hBsub)
  · rw [prime_blocks_split hp, Finset.sum_union hsmall, Finset.sum_union hdisj,
      hsum B, hsum (m * p ^ b).divisors]
    calc
      2 * ((∑ x ∈ A, x) + c * ∑ x ∈ B, x) =
          2 * (∑ x ∈ A, x) + c * (2 * ∑ x ∈ B, x) := by ring
      _ = (∑ x ∈ (m * p ^ a).divisors, x) +
          c * ∑ x ∈ (m * p ^ b).divisors, x := by rw [hAsum, hBsum]

/-- Repeating a balanced divisor block `t` times preserves the Zumkeller property.
Coprimality to the prime ensures that the exponent intervals are disjoint. -/
theorem IsZumkeller.prime_power_blocks {p m a t : ℕ} (hp : p.Prime)
    (hpm : ¬p ∣ m) (ht : 0 < t) (ha : IsZumkeller (m * p ^ a)) :
    IsZumkeller (m * p ^ (t * (a + 1) - 1)) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  induction s with
  | zero => simpa using ha
  | succ s ih =>
    have he : (s + 1 + 1) * (a + 1) - 1 =
        ((s + 1) * (a + 1) - 1) + 1 + a := by
      have hpos : 1 ≤ (s + 1) * (a + 1) := Nat.mul_pos (by omega) (by omega)
      rw [Nat.add_mul]
      simp only [one_mul]
      omega
    rw [show s.succ.succ = s + 1 + 1 from rfl, he]
    exact IsZumkeller.prime_power_concat hp hpm (ih (by omega)) ha

example : Nat.Prime 2 ∧ ¬2 ∣ 3 ∧ 0 < (2 : ℕ) ∧ IsZumkeller (3 * 2 ^ 1) := by
  decide

example : IsZumkeller 24 := by
  exact IsZumkeller.prime_power_blocks (p := 2) (m := 3) (a := 1) (t := 2)
    (by decide) (by decide) (by decide) (by decide)
