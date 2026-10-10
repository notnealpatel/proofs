import Erdos.Unitary1052A12Support

set_option autoImplicit false

namespace Erdos1052

/-- A prime component in the odd-exponent slot cannot be 61 when its base
is congruent to 1 modulo 24. -/
theorem a12_not_sixty_one_dvd_odd_component (p e : ℕ)
    (hp : p.Prime) (hp24 : p % 24 = 1) : ¬ 61 ∣ p ^ e := by
  intro hd
  have h61 : Nat.Prime 61 := by decide
  have heq : 61 = p :=
    (Nat.prime_dvd_prime_iff_eq h61 hp).mp (h61.dvd_of_dvd_pow hd)
  rw [← heq] at hp24
  norm_num at hp24

example : Nat.Prime 73 ∧ (73 : ℕ) % 24 = 1 := by decide

/-- In the source-gated a=12 branch with the 11-square seed and four other
square components, the full canceled identity forces one of those four bases
to be 61. This does not establish applicability of the seed or of the branch. -/
theorem a12_eleven_seed_forces_sixty_one
    (p e r1 r2 r3 r4 d1 d2 d3 d4 : ℕ)
    (hp : p.Prime) (_hp13 : 13 < p) (hp24 : p % 24 = 1)
    (_he : 0 < e) (_heodd : Odd e)
    (_hd1 : 0 < d1) (_hd2 : 0 < d2) (_hd3 : 0 < d3) (_hd4 : 0 < d4)
    (hcomponents : ∀ r ∈ ({r1, r2, r3, r4} : Finset ℕ),
      r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13)
    (_hdistinct : List.Pairwise (· ≠ ·) [p, 11, r1, r2, r3, r4])
    (hid : (2 ^ 12 + 1) * (p ^ e + 1) * (11 ^ 2 + 1) *
        (r1 ^ (2 * d1) + 1) * (r2 ^ (2 * d2) + 1) *
        (r3 ^ (2 * d3) + 1) * (r4 ^ (2 * d4) + 1) =
      2 ^ 6 * 65 * p ^ e * 11 ^ 2 * r1 ^ (2 * d1) *
        r2 ^ (2 * d2) * r3 ^ (2 * d3) * r4 ^ (2 * d4)) :
    r1 = 61 ∨ r2 = 61 ∨ r3 = 61 ∨ r4 = 61 := by
  have h61 : Nat.Prime 61 := by decide
  have hleft : 61 ∣ (2 ^ 12 + 1) * (p ^ e + 1) * (11 ^ 2 + 1) *
      (r1 ^ (2 * d1) + 1) * (r2 ^ (2 * d2) + 1) *
      (r3 ^ (2 * d3) + 1) * (r4 ^ (2 * d4) + 1) := by
    refine ⟨(2 ^ 12 + 1) * (p ^ e + 1) * 2 *
      (r1 ^ (2 * d1) + 1) * (r2 ^ (2 * d2) + 1) *
      (r3 ^ (2 * d3) + 1) * (r4 ^ (2 * d4) + 1), ?_⟩
    ring
  rw [hid] at hleft
  have hpnot := a12_not_sixty_one_dvd_odd_component p e hp hp24
  have heq_of_pow {r k : ℕ} (hr : r.Prime) (hd : 61 ∣ r ^ k) : r = 61 :=
    ((Nat.prime_dvd_prime_iff_eq h61 hr).mp (h61.dvd_of_dvd_pow hd)).symm
  simp only [h61.dvd_mul] at hleft
  rcases hleft with ((((((h2 | h65) | hpdiv) | h11) | hr1div) | hr2div) | hr3div) | hr4div
  · norm_num at h2
  · norm_num at h65
  · exact False.elim (hpnot hpdiv)
  · norm_num at h11
  · exact Or.inl (heq_of_pow (hcomponents r1 (by simp)).1 hr1div)
  · exact Or.inr (Or.inl (heq_of_pow (hcomponents r2 (by simp)).1 hr2div))
  · exact Or.inr (Or.inr (Or.inl (heq_of_pow (hcomponents r3 (by simp)).1 hr3div)))
  · exact Or.inr (Or.inr (Or.inr (heq_of_pow (hcomponents r4 (by simp)).1 hr4div)))

/-- The forced 61 slot inherits the adopted five-slot support obstruction:
its positive exponent parameter is not divisible by 81. Each branch transports
the full identity and distinct component list without changing the other slots. -/
theorem a12_eleven_seed_forces_sixty_one_not_dvd_eighty_one
    (p e r1 r2 r3 r4 d1 d2 d3 d4 : ℕ)
    (hp : p.Prime) (hp13 : 13 < p) (hp24 : p % 24 = 1)
    (he : 0 < e) (heodd : Odd e)
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hd3 : 0 < d3) (hd4 : 0 < d4)
    (hcomponents : ∀ r ∈ ({r1, r2, r3, r4} : Finset ℕ),
      r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13)
    (hdistinct : List.Pairwise (· ≠ ·) [p, 11, r1, r2, r3, r4])
    (hid : (2 ^ 12 + 1) * (p ^ e + 1) * (11 ^ 2 + 1) *
        (r1 ^ (2 * d1) + 1) * (r2 ^ (2 * d2) + 1) *
        (r3 ^ (2 * d3) + 1) * (r4 ^ (2 * d4) + 1) =
      2 ^ 6 * 65 * p ^ e * 11 ^ 2 * r1 ^ (2 * d1) *
        r2 ^ (2 * d2) * r3 ^ (2 * d3) * r4 ^ (2 * d4)) :
    (r1 = 61 ∧ ¬ 81 ∣ d1) ∨ (r2 = 61 ∧ ¬ 81 ∣ d2) ∨
      (r3 = 61 ∧ ¬ 81 ∣ d3) ∨ (r4 = 61 ∧ ¬ 81 ∣ d4) := by
  have hforced := a12_eleven_seed_forces_sixty_one p e r1 r2 r3 r4 d1 d2 d3 d4
    hp hp13 hp24 he heodd hd1 hd2 hd3 hd4 hcomponents hdistinct hid
  rcases hforced with h1 | h2 | h3 | h4
  · subst r1
    refine Or.inl ⟨rfl, ?_⟩
    have hcomponents' : ∀ q ∈ ({r2, r3, r4} : Finset ℕ),
        q.Prime ∧ Odd q ∧ q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≠ 13 := by
      intro q hq
      apply hcomponents q
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq ⊢
      tauto
    apply a12_five_slot_not_dvd_eighty_one p e d1 r2 r3 r4 d2 d3 d4
      hp hp13 hp24 he heodd hd1 hd2 hd3 hd4 hcomponents' hdistinct
    exact hid
  · subst r2
    refine Or.inr (Or.inl ⟨rfl, ?_⟩)
    have hcomponents' : ∀ q ∈ ({r1, r3, r4} : Finset ℕ),
        q.Prime ∧ Odd q ∧ q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≠ 13 := by
      intro q hq
      apply hcomponents q
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq ⊢
      tauto
    have hperm : List.Perm [p, 11, r1, 61, r3, r4] [p, 11, 61, r1, r3, r4] :=
      (((List.Perm.swap 61 r1 [r3, r4]).cons 11).cons p)
    have hdistinct' : List.Pairwise (· ≠ ·) [p, 11, 61, r1, r3, r4] :=
      (hperm.pairwise_iff (fun hne => Ne.symm hne)).mp hdistinct
    apply a12_five_slot_not_dvd_eighty_one p e d2 r1 r3 r4 d1 d3 d4
      hp hp13 hp24 he heodd hd2 hd1 hd3 hd4 hcomponents' hdistinct'
    convert hid using 1 <;> ring
  · subst r3
    refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
    have hcomponents' : ∀ q ∈ ({r1, r2, r4} : Finset ℕ),
        q.Prime ∧ Odd q ∧ q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≠ 13 := by
      intro q hq
      apply hcomponents q
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq ⊢
      tauto
    have hperm : List.Perm [p, 11, r1, r2, 61, r4] [p, 11, 61, r1, r2, r4] :=
      ((((List.Perm.swap 61 r2 [r4]).cons r1).trans
        (List.Perm.swap 61 r1 [r2, r4])).cons 11).cons p
    have hdistinct' : List.Pairwise (· ≠ ·) [p, 11, 61, r1, r2, r4] :=
      (hperm.pairwise_iff (fun hne => Ne.symm hne)).mp hdistinct
    apply a12_five_slot_not_dvd_eighty_one p e d3 r1 r2 r4 d1 d2 d4
      hp hp13 hp24 he heodd hd3 hd1 hd2 hd4 hcomponents' hdistinct'
    convert hid using 1 <;> ring
  · subst r4
    refine Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩))
    have hcomponents' : ∀ q ∈ ({r1, r2, r3} : Finset ℕ),
        q.Prime ∧ Odd q ∧ q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≠ 13 := by
      intro q hq
      apply hcomponents q
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq ⊢
      tauto
    have hperm : List.Perm [p, 11, r1, r2, r3, 61] [p, 11, 61, r1, r2, r3] :=
      ((((((List.Perm.swap 61 r3 []).cons r2).cons r1).trans
        ((List.Perm.swap 61 r2 [r3]).cons r1)).trans
        (List.Perm.swap 61 r1 [r2, r3])).cons 11).cons p
    have hdistinct' : List.Pairwise (· ≠ ·) [p, 11, 61, r1, r2, r3] :=
      (hperm.pairwise_iff (fun hne => Ne.symm hne)).mp hdistinct
    apply a12_five_slot_not_dvd_eighty_one p e d4 r1 r2 r3 d1 d2 d3
      hp hp13 hp24 he heodd hd4 hd1 hd2 hd3 hcomponents' hdistinct'
    convert hid using 1 <;> ring

example : Nat.Prime 73 ∧ 13 < (73 : ℕ) ∧ (73 : ℕ) % 24 = 1 ∧
    0 < (3 : ℕ) ∧ Odd (3 : ℕ) ∧
    0 < (1 : ℕ) ∧ 0 < (1 : ℕ) ∧ 0 < (1 : ℕ) ∧ 0 < (1 : ℕ) ∧
    (∀ r ∈ ({17, 19, 23, 61} : Finset ℕ),
      r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13) ∧
    List.Pairwise (· ≠ ·) ([73, 11, 17, 19, 23, 61] : List ℕ) := by decide

end Erdos1052
