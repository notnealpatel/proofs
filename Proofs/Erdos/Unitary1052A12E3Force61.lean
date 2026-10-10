import Erdos.Unitary1052A12E3Seed
import Erdos.Unitary1052A12Force61

set_option autoImplicit false

namespace Erdos1052

/-- In the full five-unspecified-square-slot a=12 identity with e at least three,
the derived 11-square seed makes the paid Force61 consumer applicable: an actual
61 slot has exponent parameter not divisible by 81. -/
theorem a12_e3_forces_sixty_one_not_dvd_eighty_one
    (p e q1 q2 q3 q4 q5 d1 d2 d3 d4 d5 : ℕ)
    (hp : p.Prime) (hp13 : 13 < p) (hp24 : p % 24 = 1)
    (he : 0 < e) (heodd : Odd e) (he3 : 3 ≤ e)
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hd3 : 0 < d3) (hd4 : 0 < d4) (hd5 : 0 < d5)
    (hcomponents : ∀ q ∈ ({q1, q2, q3, q4, q5} : Finset ℕ),
      q.Prime ∧ Odd q ∧ q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≠ 13)
    (hdistinct : List.Pairwise (· ≠ ·) [p, q1, q2, q3, q4, q5])
    (hid : (2 ^ 12 + 1) * (p ^ e + 1) *
      (q1 ^ (2 * d1) + 1) * (q2 ^ (2 * d2) + 1) *
      (q3 ^ (2 * d3) + 1) * (q4 ^ (2 * d4) + 1) * (q5 ^ (2 * d5) + 1) =
      2 ^ 6 * 65 * p ^ e * q1 ^ (2 * d1) * q2 ^ (2 * d2) *
        q3 ^ (2 * d3) * q4 ^ (2 * d4) * q5 ^ (2 * d5)) :
    (q1 = 61 ∧ ¬ 81 ∣ d1) ∨ (q2 = 61 ∧ ¬ 81 ∣ d2) ∨ (q3 = 61 ∧ ¬ 81 ∣ d3) ∨
      (q4 = 61 ∧ ¬ 81 ∣ d4) ∨ (q5 = 61 ∧ ¬ 81 ∣ d5) := by
  have hseed := a12_e3_forces_eleven_square p e q1 q2 q3 q4 q5 d1 d2 d3 d4 d5
    hp hp13 hp24 he heodd he3 hd1 hd2 hd3 hd4 hd5 hcomponents hdistinct hid
  rcases hseed with h1 | h2 | h3 | h4 | h5
  · rcases h1 with ⟨hq, hd⟩
    subst q1
    subst d1
    have hc : ∀ q ∈ ({q2, q3, q4, q5} : Finset ℕ),
        q.Prime ∧ Odd q ∧ q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≠ 13 := by
      intro q hq
      apply hcomponents q
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq ⊢
      tauto
    have hdist : List.Pairwise (· ≠ ·) [p, 11, q2, q3, q4, q5] := hdistinct
    have hid' : (2 ^ 12 + 1) * (p ^ e + 1) * (11 ^ 2 + 1) *
      (q2 ^ (2 * d2) + 1) * (q3 ^ (2 * d3) + 1) * (q4 ^ (2 * d4) + 1) * (q5 ^ (2 * d5) + 1) =
      2 ^ 6 * 65 * p ^ e * 11 ^ 2 * q2 ^ (2 * d2) * q3 ^ (2 * d3) * q4 ^ (2 * d4) * q5 ^ (2 * d5) := by
      exact hid
    have hforced := a12_eleven_seed_forces_sixty_one_not_dvd_eighty_one
      p e q2 q3 q4 q5 d2 d3 d4 d5
      hp hp13 hp24 he heodd hd2 hd3 hd4 hd5 hc hdist hid'
    rcases hforced with h2 | h3 | h4 | h5
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (h5))))
  · rcases h2 with ⟨hq, hd⟩
    subst q2
    subst d2
    have hc : ∀ q ∈ ({q1, q3, q4, q5} : Finset ℕ),
        q.Prime ∧ Odd q ∧ q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≠ 13 := by
      intro q hq
      apply hcomponents q
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq ⊢
      tauto
    have hperm : List.Perm [p, q1, 11, q3, q4, q5] [p, 11, q1, q3, q4, q5] :=
      (List.Perm.swap 11 q1 [q3, q4, q5]).cons p
    have hdist : List.Pairwise (· ≠ ·) [p, 11, q1, q3, q4, q5] :=
      (hperm.pairwise_iff (fun hne => Ne.symm hne)).mp hdistinct
    have hid' : (2 ^ 12 + 1) * (p ^ e + 1) * (11 ^ 2 + 1) *
      (q1 ^ (2 * d1) + 1) * (q3 ^ (2 * d3) + 1) * (q4 ^ (2 * d4) + 1) * (q5 ^ (2 * d5) + 1) =
      2 ^ 6 * 65 * p ^ e * 11 ^ 2 * q1 ^ (2 * d1) * q3 ^ (2 * d3) * q4 ^ (2 * d4) * q5 ^ (2 * d5) := by
      convert hid using 1 <;> ring
    have hforced := a12_eleven_seed_forces_sixty_one_not_dvd_eighty_one
      p e q1 q3 q4 q5 d1 d3 d4 d5
      hp hp13 hp24 he heodd hd1 hd3 hd4 hd5 hc hdist hid'
    rcases hforced with h1 | h3 | h4 | h5
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (h5))))
  · rcases h3 with ⟨hq, hd⟩
    subst q3
    subst d3
    have hc : ∀ q ∈ ({q1, q2, q4, q5} : Finset ℕ),
        q.Prime ∧ Odd q ∧ q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≠ 13 := by
      intro q hq
      apply hcomponents q
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq ⊢
      tauto
    have hperm : List.Perm [p, q1, q2, 11, q4, q5] [p, 11, q1, q2, q4, q5] :=
      (((List.Perm.swap 11 q2 [q4, q5]).cons q1).trans (List.Perm.swap 11 q1 [q2, q4, q5])).cons p
    have hdist : List.Pairwise (· ≠ ·) [p, 11, q1, q2, q4, q5] :=
      (hperm.pairwise_iff (fun hne => Ne.symm hne)).mp hdistinct
    have hid' : (2 ^ 12 + 1) * (p ^ e + 1) * (11 ^ 2 + 1) *
      (q1 ^ (2 * d1) + 1) * (q2 ^ (2 * d2) + 1) * (q4 ^ (2 * d4) + 1) * (q5 ^ (2 * d5) + 1) =
      2 ^ 6 * 65 * p ^ e * 11 ^ 2 * q1 ^ (2 * d1) * q2 ^ (2 * d2) * q4 ^ (2 * d4) * q5 ^ (2 * d5) := by
      convert hid using 1 <;> ring
    have hforced := a12_eleven_seed_forces_sixty_one_not_dvd_eighty_one
      p e q1 q2 q4 q5 d1 d2 d4 d5
      hp hp13 hp24 he heodd hd1 hd2 hd4 hd5 hc hdist hid'
    rcases hforced with h1 | h2 | h4 | h5
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (h5))))
  · rcases h4 with ⟨hq, hd⟩
    subst q4
    subst d4
    have hc : ∀ q ∈ ({q1, q2, q3, q5} : Finset ℕ),
        q.Prime ∧ Odd q ∧ q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≠ 13 := by
      intro q hq
      apply hcomponents q
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq ⊢
      tauto
    have hperm : List.Perm [p, q1, q2, q3, 11, q5] [p, 11, q1, q2, q3, q5] :=
      (((((List.Perm.swap 11 q3 [q5]).cons q2).cons q1).trans ((List.Perm.swap 11 q2 [q3, q5]).cons q1)).trans (List.Perm.swap 11 q1 [q2, q3, q5])).cons p
    have hdist : List.Pairwise (· ≠ ·) [p, 11, q1, q2, q3, q5] :=
      (hperm.pairwise_iff (fun hne => Ne.symm hne)).mp hdistinct
    have hid' : (2 ^ 12 + 1) * (p ^ e + 1) * (11 ^ 2 + 1) *
      (q1 ^ (2 * d1) + 1) * (q2 ^ (2 * d2) + 1) * (q3 ^ (2 * d3) + 1) * (q5 ^ (2 * d5) + 1) =
      2 ^ 6 * 65 * p ^ e * 11 ^ 2 * q1 ^ (2 * d1) * q2 ^ (2 * d2) * q3 ^ (2 * d3) * q5 ^ (2 * d5) := by
      convert hid using 1 <;> ring
    have hforced := a12_eleven_seed_forces_sixty_one_not_dvd_eighty_one
      p e q1 q2 q3 q5 d1 d2 d3 d5
      hp hp13 hp24 he heodd hd1 hd2 hd3 hd5 hc hdist hid'
    rcases hforced with h1 | h2 | h3 | h5
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (h5))))
  · rcases h5 with ⟨hq, hd⟩
    subst q5
    subst d5
    have hc : ∀ q ∈ ({q1, q2, q3, q4} : Finset ℕ),
        q.Prime ∧ Odd q ∧ q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≠ 13 := by
      intro q hq
      apply hcomponents q
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq ⊢
      tauto
    have hperm : List.Perm [p, q1, q2, q3, q4, 11] [p, 11, q1, q2, q3, q4] :=
      (((((((List.Perm.swap 11 q4 []).cons q3).cons q2).cons q1).trans (((List.Perm.swap 11 q3 [q4]).cons q2).cons q1)).trans ((List.Perm.swap 11 q2 [q3, q4]).cons q1)).trans (List.Perm.swap 11 q1 [q2, q3, q4])).cons p
    have hdist : List.Pairwise (· ≠ ·) [p, 11, q1, q2, q3, q4] :=
      (hperm.pairwise_iff (fun hne => Ne.symm hne)).mp hdistinct
    have hid' : (2 ^ 12 + 1) * (p ^ e + 1) * (11 ^ 2 + 1) *
      (q1 ^ (2 * d1) + 1) * (q2 ^ (2 * d2) + 1) * (q3 ^ (2 * d3) + 1) * (q4 ^ (2 * d4) + 1) =
      2 ^ 6 * 65 * p ^ e * 11 ^ 2 * q1 ^ (2 * d1) * q2 ^ (2 * d2) * q3 ^ (2 * d3) * q4 ^ (2 * d4) := by
      convert hid using 1 <;> ring
    have hforced := a12_eleven_seed_forces_sixty_one_not_dvd_eighty_one
      p e q1 q2 q3 q4 d1 d2 d3 d4
      hp hp13 hp24 he heodd hd1 hd2 hd3 hd4 hc hdist hid'
    rcases hforced with h1 | h2 | h3 | h4
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))

end Erdos1052
