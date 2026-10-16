import Enumerative.GreedyQuasiBarrycadeSixData

set_option autoImplicit false

namespace GreedyQuasiBarrycade

private theorem sixth_gap_ne (i x k j : ℕ) (hi : i < 5)
    (hlo : triangular j < x + rowShift i)
    (hhi : x + rowShift i < triangular (j + 1))
    (hcut : (rowPrefix i).length ≤ k) :
    partialSum (explicitTable i) k ≠ x := by
  intro heq
  let l := if i = 0 then k else k + 1
  have hsum : partialSum (explicitTable i) k + rowShift i = triangular l := by
    by_cases hi0 : i = 0
    · subst i
      simpa [l, rowShift] using explicit_first_sum k
    · simpa [l, hi0] using explicit_shifted_sum i k hi hi0 hcut
  by_cases hl : l ≤ j
  · have hmono := triangular_monotone hl
    omega
  · have hmono := triangular_monotone (show j + 1 ≤ l by omega)
    omega

private theorem sixth_finite_greedy (n : ℕ) (hc : SixthCertificate n) :
    Admissible sixTable 5 n (sixTable 5 n) ∧
    ∀ b, Admissible sixTable 5 n b → sixTable 5 n ≤ b := by
  rcases hc with ⟨hpos, hunused, havoid, hreject⟩
  constructor
  · refine ⟨hpos, ?_, ?_⟩
    · intro m hm
      exact hunused m (Finset.mem_range.mpr hm)
    · intro i hi k hk
      rw [sixTable_earlier i hi]
      have hcert := havoid i (Finset.mem_range.mpr hi)
      by_cases hcut : (rowPrefix i).length ≤ k
      · rcases hcert.2 with hbelow | ⟨j, hj, hlo, hhi⟩
        · exact tailAvoid_ne i _ k hi hk hcut (Or.inl hbelow)
        · exact sixth_gap_ne i _ k j hi hlo hhi hcut
      · exact hcert.1 k (Finset.mem_range.mpr (by omega)) hk
  · intro b hb
    by_contra hnot
    rcases hreject b (Finset.mem_range.mpr (show b < sixTable 5 n by omega)) hb.1 with
      ⟨m, hm, heq⟩ | ⟨i, hi, k, hk, hkpos, heq⟩
    · exact hb.2.1 m (Finset.mem_range.mp hm) heq
    · have hr := hb.2.2 i (Finset.mem_range.mp hi) k hkpos
      rw [sixTable_earlier i (Finset.mem_range.mp hi)] at hr
      exact hr heq

private theorem sixth_tail_greedy (n : ℕ) (hn : 29 ≤ n) :
    Admissible sixTable 5 n (sixTable 5 n) ∧
    ∀ b, Admissible sixTable 5 n b → sixTable 5 n ≤ b := by
  let x := partialSum (sixTable 5) n + (n + 2)
  have hentry := explicit_sixth_tail n hn
  have hsum := sixth_shifted_sum (n + 1) (by omega)
  have hx : x + 29 = triangular (n + 2) := by
    rw [sum_succ, hentry] at hsum
    exact hsum
  constructor
  · rw [hentry]
    refine ⟨by omega, ?_, ?_⟩
    · intro m hm heq
      have hused := (sixth_used n (n + 2) hn).mp ⟨m, hm, heq⟩
      omega
    · intro i hi k hk
      rw [sixTable_earlier i hi]
      have hd : rowShift i ≤ 16 := by interval_cases i <;> decide
      have hlo : triangular (n + 1) < x + rowShift i := by
        have hrec : triangular (n + 2) = triangular (n + 1) + (n + 2) := by
          simpa only [Nat.add_assoc] using triangular_succ (n + 1)
        omega
      have hhi : x + rowShift i < triangular (n + 2) := by omega
      by_cases hcut : (rowPrefix i).length ≤ k
      · exact sixth_gap_ne i x k (n + 1) hi hlo hhi hcut
      · have hbound := sixth_earlier_sum_bound i (Finset.mem_range.mpr hi)
          k (Finset.mem_range.mpr (show k < (rowPrefix i).length by omega))
        have hmono := triangular_monotone (show 31 ≤ n + 2 by omega)
        have hval : triangular 31 = 496 := by decide
        change partialSum (explicitTable i) k ≠ x
        omega
  · intro b hb
    rw [hentry]
    by_contra hnot
    have hbmiss : b = 29 := by
      by_contra hne
      have hused := (sixth_used n b hn).mpr ⟨hb.1, by omega, hne⟩
      rcases hused with ⟨m, hm, heq⟩
      exact hb.2.1 m hm heq
    have hreject := hb.2.2 0 (by decide) (n + 1) (by omega)
    rw [sixTable_earlier 0 (by decide), explicit_first_sum, hbmiss] at hreject
    exact hreject (sixth_shifted_sum n hn).symm

/-- The explicit table satisfies the exact greedy rule on six complete rows. -/
theorem explicit_six_greedy : GreedyPrefix 6 sixTable := by
  intro r hr n
  by_cases hr5 : r = 5
  · subst r
    by_cases hn : 29 ≤ n
    · exact sixth_tail_greedy n hn
    · exact sixth_finite_greedy n (sixth_certificates n (Finset.mem_range.mpr (by omega)))
  · have hrlt : r < 5 := by omega
    have hagree (a : ℕ) : Admissible sixTable r n a ↔ Admissible explicitTable r n a :=
      admissible_iff_of_agree sixTable explicitTable r n a
        (fun i hi => sixTable_earlier i (by omega))
        (fun m _ => congrFun (sixTable_earlier r hrlt) m)
    have h := explicit_five_greedy r hrlt n
    rw [congrFun (sixTable_earlier r hrlt) n]
    exact ⟨(hagree _).mpr h.1, fun b hb => h.2 b ((hagree b).mp hb)⟩

/-- Any greedy six-row prefix agrees with the explicit certificate. -/
theorem six_greedy_eq_explicit (table : Table) (h : GreedyPrefix 6 table) :
    ∀ r, r < 6 → table r = sixTable r :=
  greedyPrefix_unique 6 table sixTable h explicit_six_greedy

/-- The sixth row's first 29 entries are exactly the reviewed exceptional prefix. -/
theorem sixth_row_prefix (table : Table) (h : GreedyPrefix 6 table) :
    List.ofFn (fun n : Fin 29 => table 5 n) = sixthPrefix := by
  rw [six_greedy_eq_explicit table h 5 (by decide)]
  decide

/-- The sixth row's entries at zero-based indices at least 29 equal `n+2`. -/
theorem sixth_row_tail (table : Table) (h : GreedyPrefix 6 table)
    (n : ℕ) (hn : 29 ≤ n) : table 5 n = n + 2 := by
  rw [six_greedy_eq_explicit table h 5 (by decide)]
  exact explicit_sixth_tail n hn

/-- The explicit sixth row contains exactly the positive integers other than 29. -/
theorem explicit_sixth_range (a : ℕ) (ha : 0 < a) :
    (∃ n, sixTable 5 n = a) ↔ a ≠ 29 := by
  constructor
  · rintro ⟨n, heq⟩
    let N := max 29 (n + 1)
    have hN : 29 ≤ N := Nat.le_max_left _ _
    have hn : n < N := by
      have hmax := Nat.le_max_right 29 (n + 1)
      omega
    exact ((sixth_used N a hN).mp ⟨n, hn, heq⟩).2.2
  · intro hne
    let N := max 29 a
    have hN : 29 ≤ N := Nat.le_max_left _ _
    have haN : a ≤ N + 1 := by
      have hmax := Nat.le_max_right 29 a
      omega
    rcases (sixth_used N a hN).mpr ⟨ha, haN, hne⟩ with ⟨n, hn, heq⟩
    exact ⟨n, heq⟩

/-- In any greedy six-row prefix, the sixth row omits exactly 29 among positives. -/
theorem sixth_row_range (table : Table) (h : GreedyPrefix 6 table)
    (a : ℕ) (ha : 0 < a) : (∃ n, table 5 n = a) ↔ a ≠ 29 := by
  rw [six_greedy_eq_explicit table h 5 (by decide)]
  exact explicit_sixth_range a ha

example : ∃ table : Table, GreedyPrefix 6 table := ⟨sixTable, explicit_six_greedy⟩
example : GreedyPrefix 6 sixTable ∧ 29 ≤ (29 : ℕ) ∧ 0 < (30 : ℕ) :=
  ⟨explicit_six_greedy, by decide, by decide⟩
example : ∃ n, sixTable 5 n = 30 := (explicit_sixth_range 30 (by decide)).mpr (by decide)

end GreedyQuasiBarrycade
