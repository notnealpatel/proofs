import Enumerative.GreedyQuasiBarrycadeCertificates

/-!
# Infinite greedy certificate and the fifth-row omission

The finite certificates are imported from a stable computation module.
The tail proof below excludes earlier sums at every positive length, not only
at the witness-search bound of those certificates. Combined with uniqueness
of the reviewed greedy model, it applies to any table satisfying that model.
-/

set_option autoImplicit false

namespace GreedyQuasiBarrycade

private theorem shifted_gap_ne (i x k j : ℕ) (hi : i < 5)
    (_hk : 0 < k) (hcut : (rowPrefix i).length ≤ k)
    (hlo : triangular j < x + rowShift i)
    (hhi : x + rowShift i < triangular (j + 1)) :
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

private theorem finite_earlier_sum_bound :
    ∀ i ∈ Finset.range 4, ∀ k ∈ Finset.range (rowPrefix i).length,
      partialSum (explicitTable i) k ≤ 47 := by decide

private theorem tail_greedy (r n : ℕ) (hr : r < 5) (hr0 : r ≠ 0)
    (hn : (rowPrefix r).length ≤ n) :
    Admissible explicitTable r n (explicitTable r n) ∧
    ∀ b, Admissible explicitTable r n b → explicitTable r n ≤ b := by
  let x := partialSum (explicitTable r) n + (n + 2)
  have hentry := explicit_tail r n hr0 hn
  have hsum := explicit_shifted_sum r (n + 1) hr hr0 (by omega)
  have hx : x + rowShift r = triangular (n + 2) := by
    rw [sum_succ, hentry] at hsum
    exact hsum
  have hd : rowShift r < n + 2 := by
    interval_cases r <;> simp_all [rowShift, rowPrefix]
    all_goals omega
  have hdmax : rowShift r ≤ 16 := by interval_cases r <;> decide
  have hshifts : ∀ i, i < r → rowShift i < rowShift r := by
    intro i hi
    interval_cases r <;> interval_cases i <;> first | omega | decide
  constructor
  · rw [hentry]
    refine ⟨by omega, ?_, ?_⟩
    · intro m hm heq
      have hused := (explicit_used r n (n + 2) hr hr0 hn).mp ⟨m, hm, heq⟩
      omega
    · intro i hi k hk
      have hshift := hshifts i hi
      have hlo : triangular (n + 1) < x + rowShift i := by
        have hrec : triangular (n + 2) = triangular (n + 1) + (n + 2) := by
          simpa only [Nat.add_assoc] using triangular_succ (n + 1)
        omega
      have hhi : x + rowShift i < triangular (n + 2) := by omega
      by_cases hcut : (rowPrefix i).length ≤ k
      · exact shifted_gap_ne i x k (n + 1) (by omega) hk hcut hlo hhi
      · have hkcut : k < (rowPrefix i).length := by omega
        have hrlarge : 3 ≤ r := by
          by_contra hnot
          have hi2 : i < 2 := by omega
          interval_cases i <;> simp [rowPrefix] at hkcut
        have hnlarge : 10 ≤ n := by
          interval_cases r <;>
            (simp only [rowPrefix, List.length_cons, List.length_nil] at hn; omega)
        have hbound := finite_earlier_sum_bound i (Finset.mem_range.mpr (by omega))
          k (Finset.mem_range.mpr hkcut)
        have hmono := triangular_monotone (show 12 ≤ n + 2 by omega)
        have hval : triangular 12 = 78 := by decide
        change partialSum (explicitTable i) k ≠ x
        omega
  · intro b hb
    rw [hentry]
    by_contra hnot
    have hsmall : b ≤ n + 1 := by omega
    have hbmiss : b = rowShift r := by
      by_contra hne
      have hused := (explicit_used r n b hr hr0 hn).mpr ⟨hb.1, hsmall, hne⟩
      rcases hused with ⟨m, hm, heq⟩
      exact hb.2.1 m hm heq
    have hreject := hb.2.2 0 (by omega) (n + 1) (by omega)
    rw [explicit_first_sum, hbmiss] at hreject
    exact hreject (explicit_shifted_sum r n hr hr0 hn).symm

/-- The displayed five infinite rows satisfy the exact least-positive-unused
rule, avoiding all positive-length partial sums of every earlier row. -/
theorem explicit_five_greedy : GreedyPrefix 5 explicitTable := by
  intro r hr n
  by_cases hr0 : r = 0
  · subst r
    have hfirst := increasing_first_row 0 (by decide) n
    simpa [Admissible, explicitTable] using hfirst
  · by_cases hn : (rowPrefix r).length ≤ n
    · exact tail_greedy r n hr hr0 hn
    · exact finiteCertificate_greedy r n hr
        (finite_certificates r (Finset.mem_range.mpr hr) n
          (Finset.mem_range.mpr (by omega)))

/-- The fifth explicit row has linear tail from zero-based entry index 16. -/
theorem explicit_fifth_tail (n : ℕ) (hn : 16 ≤ n) :
    explicitTable 4 n = n + 2 :=
  explicit_tail 4 n (by decide) hn

/-- The fifth explicit row contains every positive integer except 16,
and does not contain 16 at any index. -/
theorem explicit_fifth_range (a : ℕ) (ha : 0 < a) :
    (∃ n, explicitTable 4 n = a) ↔ a ≠ 16 := by
  constructor
  · rintro ⟨n, heq⟩
    let N := max 16 (n + 1)
    have hcut : (rowPrefix 4).length ≤ N := by
      change 16 ≤ max 16 (n + 1)
      exact Nat.le_max_left _ _
    have hn : n < N := by
      have hmax := Nat.le_max_right 16 (n + 1)
      omega
    exact ((explicit_used 4 N a (by decide) (by decide) hcut).mp
      ⟨n, hn, heq⟩).2.2
  · intro hne
    let N := max 16 a
    have hcut : (rowPrefix 4).length ≤ N := Nat.le_max_left _ _
    have haN : a ≤ N + 1 := by
      have hmax := Nat.le_max_right 16 a
      omega
    rcases (explicit_used 4 N a (by decide) (by decide) hcut).mpr
      ⟨ha, haN, hne⟩ with ⟨n, hn, heq⟩
    exact ⟨n, heq⟩

/-- Any table satisfying the five-row greedy contract equals the explicit
certificate in each of its first five rows. -/
theorem five_greedy_eq_explicit (table : Table) (h : GreedyPrefix 5 table) :
    ∀ r, r < 5 → table r = explicitTable r :=
  greedyPrefix_unique 5 table explicitTable h explicit_five_greedy

/-- In any table satisfying the greedy rule for its first five rows,
the fifth row's entry at zero-based index `n ≥ 16` is `n+2`. -/
theorem fifth_row_tail (table : Table) (h : GreedyPrefix 5 table)
    (n : ℕ) (hn : 16 ≤ n) : table 4 n = n + 2 := by
  rw [five_greedy_eq_explicit table h 4 (by decide)]
  exact explicit_fifth_tail n hn

/-- For any table satisfying the five-row greedy rule, its fifth row's
positive range consists exactly of the positive integers other than 16. -/
theorem fifth_row_range (table : Table) (h : GreedyPrefix 5 table)
    (a : ℕ) (ha : 0 < a) : (∃ n, table 4 n = a) ↔ a ≠ 16 := by
  rw [five_greedy_eq_explicit table h 4 (by decide)]
  exact explicit_fifth_range a ha

/-- The paper's one-based seventeenth and subsequent entries of row five
are `k+1`; the guard ensures the natural subtraction is not truncated. -/
theorem fifth_row_tail_one_based (table : Table) (h : GreedyPrefix 5 table)
    (k : ℕ) (hk : 17 ≤ k) : table 4 (k - 1) = k + 1 := by
  rw [fifth_row_tail table h (k - 1) (by omega)]
  omega

example : GreedyPrefix 5 explicitTable ∧ 16 ≤ (16 : ℕ) ∧ 0 < (17 : ℕ) :=
  ⟨explicit_five_greedy, by decide, by decide⟩

example : explicitTable 4 16 = 18 := explicit_fifth_tail 16 (by decide)
example : ∃ n, explicitTable 4 n = 17 :=
  (explicit_fifth_range 17 (by decide)).mpr (by decide)

end GreedyQuasiBarrycade
