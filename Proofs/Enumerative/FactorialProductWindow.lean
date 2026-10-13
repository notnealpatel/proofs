import Enumerative.FactorialProducts

set_option autoImplicit false

namespace FactorialProducts

open Nat

private theorem two_le_factorial {m : ℕ} (hm : 2 ≤ m) : 2 ≤ m ! :=
  Nat.factorial_le hm

/-- Exact factorial-product search, permitting repeated factors and the empty product.
Zero is rejected; one is accepted. The two recursive branches skip the largest
allowed argument or use one copy of it. -/
def factorialSearch (m q : ℕ) : Bool :=
  if q = 0 then false
  else if q = 1 then true
  else if _hm : 2 ≤ m then
    factorialSearch (m - 1) q ||
      (if m ! ∣ q then factorialSearch m (q / m !) else false)
  else false
termination_by (m, q)
decreasing_by
  · have : 2 ≤ m := _hm
    exact Prod.Lex.left _ _ (by omega)
  · apply Prod.Lex.right
    exact Nat.div_lt_self (by omega) (by have := two_le_factorial _hm; omega)

example (m : ℕ) : factorialSearch m 0 = false := by
  rw [factorialSearch]
  simp

example (m : ℕ) : factorialSearch m 1 = true := by
  rw [factorialSearch]
  simp

example : factorialSearch 0 2 = false := by simp [factorialSearch]
example : factorialSearch 1 2 = false := by simp [factorialSearch]

private theorem factorial_prod_pos (L : Multiset ℕ) :
    0 < (L.map Nat.factorial).prod := by
  induction L using Multiset.induction_on with
  | empty => simp
  | cons a L ih =>
    simpa only [Multiset.map_cons, Multiset.prod_cons] using
      Nat.mul_pos (Nat.factorial_pos a) ih

/-- For every positive target, the search accepts exactly the products of
factorials of a multiset of arguments in the inclusive interval from two to `m`.
The empty multiset is allowed, and repetitions are retained. -/
theorem factorialSearch_eq_true_iff (m q : ℕ) (hq : 0 < q) :
    factorialSearch m q = true ↔
      ∃ L : Multiset ℕ, (∀ x ∈ L, 2 ≤ x ∧ x ≤ m) ∧
        (L.map Nat.factorial).prod = q := by
  induction q using Nat.strong_induction_on generalizing m with
  | h q ihq =>
    induction m using Nat.strong_induction_on with
    | h m ihm =>
      by_cases hq1 : q = 1
      · subst q
        rw [factorialSearch]
        simp only [show ¬ (1 : ℕ) = 0 by decide, if_false, if_true]
        exact ⟨fun _ => ⟨0, by simp, by simp⟩, fun _ => True.intro⟩
      by_cases hm : 2 ≤ m
      · have hmdec : m - 1 < m := by omega
        have hqdec : q / m ! < q :=
          Nat.div_lt_self hq (by have := two_le_factorial hm; omega)
        rw [factorialSearch]
        simp only [show q ≠ 0 by omega, hq1, hm, if_false, dif_pos,
          Bool.or_eq_true]
        constructor
        · rintro (hskip | huse)
          · obtain ⟨L, hL, hprod⟩ := (ihm (m - 1) hmdec).mp hskip
            exact ⟨L, fun x hx => ⟨(hL x hx).1, by have := (hL x hx).2; omega⟩,
              hprod⟩
          · by_cases hd : m ! ∣ q
            · simp only [hd, if_true] at huse
              have hqp : 0 < q / m ! :=
                Nat.div_pos (Nat.le_of_dvd hq hd) (Nat.factorial_pos m)
              obtain ⟨L, hL, hprod⟩ := (ihq (q / m !) hqdec m hqp).mp huse
              refine ⟨m ::ₘ L, ?_, ?_⟩
              · intro x hx
                rcases Multiset.mem_cons.mp hx with rfl | hx
                · exact ⟨hm, le_rfl⟩
                · exact hL x hx
              · simp only [Multiset.map_cons, Multiset.prod_cons, hprod]
                exact Nat.mul_div_cancel' hd
            · simp [hd] at huse
        · rintro ⟨L, hL, hprod⟩
          by_cases hmem : m ∈ L
          · right
            let R := L.erase m
            have hR : ∀ x ∈ R, 2 ≤ x ∧ x ≤ m :=
              fun x hx => hL x (Multiset.mem_of_mem_erase hx)
            have heq : m ! * (R.map Nat.factorial).prod = q := by
              rw [← hprod, ← Multiset.cons_erase hmem]
              simp only [Multiset.map_cons, Multiset.prod_cons, R]
            have hd : m ! ∣ q := ⟨(R.map Nat.factorial).prod, heq.symm⟩
            simp only [hd, if_true]
            have hdiv : q / m ! = (R.map Nat.factorial).prod := by
              rw [← heq, Nat.mul_div_cancel_left _ (Nat.factorial_pos m)]
            have hqp : 0 < q / m ! := by rw [hdiv]; exact factorial_prod_pos R
            exact (ihq (q / m !) hqdec m hqp).mpr ⟨R, hR, hdiv.symm⟩
          · left
            apply (ihm (m - 1) hmdec).mpr
            refine ⟨L, ?_, hprod⟩
            intro x hx
            have hb := hL x hx
            have hne : x ≠ m := by intro he; subst x; exact hmem hx
            exact ⟨hb.1, by omega⟩
      · have hempty : ∀ L : Multiset ℕ,
            (∀ x ∈ L, 2 ≤ x ∧ x ≤ m) → L = 0 := by
          intro L hL
          apply Multiset.eq_zero_of_forall_notMem
          intro x hx
          have := hL x hx
          omega
        rw [factorialSearch]
        simp only [show q ≠ 0 by omega, hq1, hm, if_false, dite_false,
          Bool.false_eq_true, false_iff]
        rintro ⟨L, hL, hprod⟩
        have hzero := hempty L hL
        subst L
        simp only [Multiset.map_zero, Multiset.prod_zero] at hprod
        exact hq1 hprod.symm

/-- For `n ≥ 2`, the exact nontrivial factorial-product predicate is equivalent
to the complete search at largest allowed argument `n - 2` and target `n!`. -/
theorem isNontrivialFactorialProduct_iff_search {n : ℕ} (hn : 2 ≤ n) :
    IsNontrivialFactorialProduct n ↔ factorialSearch (n - 2) (n !) = true := by
  rw [factorialSearch_eq_true_iff _ _ (Nat.factorial_pos n)]
  constructor
  · rintro ⟨L, hne, h2, hsmall, hprod⟩
    exact ⟨L, fun x hx => ⟨h2 x hx, by have := hsmall x hx; omega⟩, hprod⟩
  · rintro ⟨L, hL, hprod⟩
    have hne : L ≠ 0 := by
      intro hz
      have hf := two_le_factorial hn
      subst L
      simp only [Multiset.map_zero, Multiset.prod_zero] at hprod
      omega
    exact ⟨L, hne, fun x hx => (hL x hx).1,
      fun x hx => by have := (hL x hx).2; omega, hprod⟩

private theorem search_accept_9 : factorialSearch 7 (9 !) = true :=
  (isNontrivialFactorialProduct_iff_search (by decide)).mp
    isNontrivialFactorialProduct_nine

private theorem search_accept_10 : factorialSearch 8 (10 !) = true :=
  (isNontrivialFactorialProduct_iff_search (by decide)).mp
    isNontrivialFactorialProduct_ten

private theorem search_accept_16 : factorialSearch 14 (16 !) = true :=
  (isNontrivialFactorialProduct_iff_search (by decide)).mp
    isNontrivialFactorialProduct_sixteen

private theorem factorialSearch_false_of_prime {m q p : ℕ}
    (hq : 0 < q) (hp : p.Prime) (hpm : m < p) (hd : p ∣ q) :
    factorialSearch m q = false := by
  cases hs : factorialSearch m q with
  | false => rfl
  | true =>
    obtain ⟨L, hL, hprod⟩ := (factorialSearch_eq_true_iff m q hq).mp hs
    have hdL : p ∣ (L.map Nat.factorial).prod := by rw [hprod]; exact hd
    obtain ⟨x, hx, hpx⟩ := exists_le_of_prime_dvd_prod_factorial hp L hdL
    have hxm := (hL x hx).2
    omega

private theorem factorialSearch_false_step {m q : ℕ}
    (hq : 1 < q) (hm : 2 ≤ m)
    (hs : factorialSearch (m - 1) q = false)
    (hu : m ! ∣ q → factorialSearch m (q / m !) = false) :
    factorialSearch m q = false := by
  rw [factorialSearch]
  simp only [show q ≠ 0 by omega, show q ≠ 1 by omega, hm, if_false, dif_pos, hs,
    Bool.false_or]
  split_ifs with hd
  · exact hu hd
  · rfl

/-- Complete search rejects the target factorial at 2. -/
private theorem search_reject_2 : factorialSearch 0 (2 !) = false := by
  have h0 : factorialSearch 0 2 = false :=
    factorialSearch_false_of_prime (p := 2) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 3. -/
private theorem search_reject_3 : factorialSearch 1 (3 !) = false := by
  have h0 : factorialSearch 1 6 = false :=
    factorialSearch_false_of_prime (p := 3) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 4. -/
private theorem search_reject_4 : factorialSearch 2 (4 !) = false := by
  have h0 : factorialSearch 2 24 = false :=
    factorialSearch_false_of_prime (p := 3) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 5. -/
private theorem search_reject_5 : factorialSearch 3 (5 !) = false := by
  have h0 : factorialSearch 3 120 = false :=
    factorialSearch_false_of_prime (p := 5) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 6. -/
private theorem search_reject_6 : factorialSearch 4 (6 !) = false := by
  have h0 : factorialSearch 4 720 = false :=
    factorialSearch_false_of_prime (p := 5) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 7. -/
private theorem search_reject_7 : factorialSearch 5 (7 !) = false := by
  have h0 : factorialSearch 5 5040 = false :=
    factorialSearch_false_of_prime (p := 7) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 8. -/
private theorem search_reject_8 : factorialSearch 6 (8 !) = false := by
  have h0 : factorialSearch 6 40320 = false :=
    factorialSearch_false_of_prime (p := 7) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 11. -/
private theorem search_reject_11 : factorialSearch 9 (11 !) = false := by
  have h0 : factorialSearch 9 39916800 = false :=
    factorialSearch_false_of_prime (p := 11) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 12. -/
private theorem search_reject_12 : factorialSearch 10 (12 !) = false := by
  have h0 : factorialSearch 10 479001600 = false :=
    factorialSearch_false_of_prime (p := 11) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 13. -/
private theorem search_reject_13 : factorialSearch 11 (13 !) = false := by
  have h0 : factorialSearch 11 6227020800 = false :=
    factorialSearch_false_of_prime (p := 13) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 14. -/
private theorem search_reject_14 : factorialSearch 12 (14 !) = false := by
  have h0 : factorialSearch 12 87178291200 = false :=
    factorialSearch_false_of_prime (p := 13) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 15. -/
private theorem search_reject_15 : factorialSearch 13 (15 !) = false := by
  have h0 : factorialSearch 12 1307674368000 = false :=
    factorialSearch_false_of_prime (p := 13) (by decide) (by decide) (by decide) (by norm_num)
  have h1 : factorialSearch 6 210 = false :=
    factorialSearch_false_of_prime (p := 7) (by decide) (by decide) (by decide) (by norm_num)
  have h2 : factorialSearch 7 210 = false :=
    factorialSearch_false_step (by decide) (by decide) h1 (by intro hd; norm_num [Nat.factorial] at hd)
  have h3 : factorialSearch 8 210 = false :=
    factorialSearch_false_step (by decide) (by decide) h2 (by intro hd; norm_num [Nat.factorial] at hd)
  have h4 : factorialSearch 9 210 = false :=
    factorialSearch_false_step (by decide) (by decide) h3 (by intro hd; norm_num [Nat.factorial] at hd)
  have h5 : factorialSearch 10 210 = false :=
    factorialSearch_false_step (by decide) (by decide) h4 (by intro hd; norm_num [Nat.factorial] at hd)
  have h6 : factorialSearch 11 210 = false :=
    factorialSearch_false_step (by decide) (by decide) h5 (by intro hd; norm_num [Nat.factorial] at hd)
  have h7 : factorialSearch 12 210 = false :=
    factorialSearch_false_step (by decide) (by decide) h6 (by intro hd; norm_num [Nat.factorial] at hd)
  have h8 : factorialSearch 13 210 = false :=
    factorialSearch_false_step (by decide) (by decide) h7 (by intro hd; norm_num [Nat.factorial] at hd)
  have h9 : factorialSearch 13 1307674368000 = false :=
    factorialSearch_false_step (by decide) (by decide) h0 (by intro _; norm_num only [Nat.factorial]; exact h8)
  norm_num only [Nat.factorial]
  exact h9

/-- Complete search rejects the target factorial at 17. -/
private theorem search_reject_17 : factorialSearch 15 (17 !) = false := by
  have h0 : factorialSearch 15 355687428096000 = false :=
    factorialSearch_false_of_prime (p := 17) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 18. -/
private theorem search_reject_18 : factorialSearch 16 (18 !) = false := by
  have h0 : factorialSearch 16 6402373705728000 = false :=
    factorialSearch_false_of_prime (p := 17) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 19. -/
private theorem search_reject_19 : factorialSearch 17 (19 !) = false := by
  have h0 : factorialSearch 17 121645100408832000 = false :=
    factorialSearch_false_of_prime (p := 19) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 20. -/
private theorem search_reject_20 : factorialSearch 18 (20 !) = false := by
  have h0 : factorialSearch 18 2432902008176640000 = false :=
    factorialSearch_false_of_prime (p := 19) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 21. -/
private theorem search_reject_21 : factorialSearch 19 (21 !) = false := by
  have h0 : factorialSearch 18 51090942171709440000 = false :=
    factorialSearch_false_of_prime (p := 19) (by decide) (by decide) (by decide) (by norm_num)
  have h1 : factorialSearch 6 420 = false :=
    factorialSearch_false_of_prime (p := 7) (by decide) (by decide) (by decide) (by norm_num)
  have h2 : factorialSearch 7 420 = false :=
    factorialSearch_false_step (by decide) (by decide) h1 (by intro hd; norm_num [Nat.factorial] at hd)
  have h3 : factorialSearch 8 420 = false :=
    factorialSearch_false_step (by decide) (by decide) h2 (by intro hd; norm_num [Nat.factorial] at hd)
  have h4 : factorialSearch 9 420 = false :=
    factorialSearch_false_step (by decide) (by decide) h3 (by intro hd; norm_num [Nat.factorial] at hd)
  have h5 : factorialSearch 10 420 = false :=
    factorialSearch_false_step (by decide) (by decide) h4 (by intro hd; norm_num [Nat.factorial] at hd)
  have h6 : factorialSearch 11 420 = false :=
    factorialSearch_false_step (by decide) (by decide) h5 (by intro hd; norm_num [Nat.factorial] at hd)
  have h7 : factorialSearch 12 420 = false :=
    factorialSearch_false_step (by decide) (by decide) h6 (by intro hd; norm_num [Nat.factorial] at hd)
  have h8 : factorialSearch 13 420 = false :=
    factorialSearch_false_step (by decide) (by decide) h7 (by intro hd; norm_num [Nat.factorial] at hd)
  have h9 : factorialSearch 14 420 = false :=
    factorialSearch_false_step (by decide) (by decide) h8 (by intro hd; norm_num [Nat.factorial] at hd)
  have h10 : factorialSearch 15 420 = false :=
    factorialSearch_false_step (by decide) (by decide) h9 (by intro hd; norm_num [Nat.factorial] at hd)
  have h11 : factorialSearch 16 420 = false :=
    factorialSearch_false_step (by decide) (by decide) h10 (by intro hd; norm_num [Nat.factorial] at hd)
  have h12 : factorialSearch 17 420 = false :=
    factorialSearch_false_step (by decide) (by decide) h11 (by intro hd; norm_num [Nat.factorial] at hd)
  have h13 : factorialSearch 18 420 = false :=
    factorialSearch_false_step (by decide) (by decide) h12 (by intro hd; norm_num [Nat.factorial] at hd)
  have h14 : factorialSearch 19 420 = false :=
    factorialSearch_false_step (by decide) (by decide) h13 (by intro hd; norm_num [Nat.factorial] at hd)
  have h15 : factorialSearch 19 51090942171709440000 = false :=
    factorialSearch_false_step (by decide) (by decide) h0 (by intro _; norm_num only [Nat.factorial]; exact h14)
  norm_num only [Nat.factorial]
  exact h15

/-- Complete search rejects the target factorial at 22. -/
private theorem search_reject_22 : factorialSearch 20 (22 !) = false := by
  have h0 : factorialSearch 18 1124000727777607680000 = false :=
    factorialSearch_false_of_prime (p := 19) (by decide) (by decide) (by decide) (by norm_num)
  have h1 : factorialSearch 10 9240 = false :=
    factorialSearch_false_of_prime (p := 11) (by decide) (by decide) (by decide) (by norm_num)
  have h2 : factorialSearch 11 9240 = false :=
    factorialSearch_false_step (by decide) (by decide) h1 (by intro hd; norm_num [Nat.factorial] at hd)
  have h3 : factorialSearch 12 9240 = false :=
    factorialSearch_false_step (by decide) (by decide) h2 (by intro hd; norm_num [Nat.factorial] at hd)
  have h4 : factorialSearch 13 9240 = false :=
    factorialSearch_false_step (by decide) (by decide) h3 (by intro hd; norm_num [Nat.factorial] at hd)
  have h5 : factorialSearch 14 9240 = false :=
    factorialSearch_false_step (by decide) (by decide) h4 (by intro hd; norm_num [Nat.factorial] at hd)
  have h6 : factorialSearch 15 9240 = false :=
    factorialSearch_false_step (by decide) (by decide) h5 (by intro hd; norm_num [Nat.factorial] at hd)
  have h7 : factorialSearch 16 9240 = false :=
    factorialSearch_false_step (by decide) (by decide) h6 (by intro hd; norm_num [Nat.factorial] at hd)
  have h8 : factorialSearch 17 9240 = false :=
    factorialSearch_false_step (by decide) (by decide) h7 (by intro hd; norm_num [Nat.factorial] at hd)
  have h9 : factorialSearch 18 9240 = false :=
    factorialSearch_false_step (by decide) (by decide) h8 (by intro hd; norm_num [Nat.factorial] at hd)
  have h10 : factorialSearch 19 9240 = false :=
    factorialSearch_false_step (by decide) (by decide) h9 (by intro hd; norm_num [Nat.factorial] at hd)
  have h11 : factorialSearch 19 1124000727777607680000 = false :=
    factorialSearch_false_step (by decide) (by decide) h0 (by intro _; norm_num only [Nat.factorial]; exact h10)
  have h12 : factorialSearch 10 462 = false :=
    factorialSearch_false_of_prime (p := 11) (by decide) (by decide) (by decide) (by norm_num)
  have h13 : factorialSearch 11 462 = false :=
    factorialSearch_false_step (by decide) (by decide) h12 (by intro hd; norm_num [Nat.factorial] at hd)
  have h14 : factorialSearch 12 462 = false :=
    factorialSearch_false_step (by decide) (by decide) h13 (by intro hd; norm_num [Nat.factorial] at hd)
  have h15 : factorialSearch 13 462 = false :=
    factorialSearch_false_step (by decide) (by decide) h14 (by intro hd; norm_num [Nat.factorial] at hd)
  have h16 : factorialSearch 14 462 = false :=
    factorialSearch_false_step (by decide) (by decide) h15 (by intro hd; norm_num [Nat.factorial] at hd)
  have h17 : factorialSearch 15 462 = false :=
    factorialSearch_false_step (by decide) (by decide) h16 (by intro hd; norm_num [Nat.factorial] at hd)
  have h18 : factorialSearch 16 462 = false :=
    factorialSearch_false_step (by decide) (by decide) h17 (by intro hd; norm_num [Nat.factorial] at hd)
  have h19 : factorialSearch 17 462 = false :=
    factorialSearch_false_step (by decide) (by decide) h18 (by intro hd; norm_num [Nat.factorial] at hd)
  have h20 : factorialSearch 18 462 = false :=
    factorialSearch_false_step (by decide) (by decide) h19 (by intro hd; norm_num [Nat.factorial] at hd)
  have h21 : factorialSearch 19 462 = false :=
    factorialSearch_false_step (by decide) (by decide) h20 (by intro hd; norm_num [Nat.factorial] at hd)
  have h22 : factorialSearch 20 462 = false :=
    factorialSearch_false_step (by decide) (by decide) h21 (by intro hd; norm_num [Nat.factorial] at hd)
  have h23 : factorialSearch 20 1124000727777607680000 = false :=
    factorialSearch_false_step (by decide) (by decide) h11 (by intro _; norm_num only [Nat.factorial]; exact h22)
  norm_num only [Nat.factorial]
  exact h23

/-- Complete search rejects the target factorial at 23. -/
private theorem search_reject_23 : factorialSearch 21 (23 !) = false := by
  have h0 : factorialSearch 21 25852016738884976640000 = false :=
    factorialSearch_false_of_prime (p := 23) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 24. -/
private theorem search_reject_24 : factorialSearch 22 (24 !) = false := by
  have h0 : factorialSearch 22 620448401733239439360000 = false :=
    factorialSearch_false_of_prime (p := 23) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 25. -/
private theorem search_reject_25 : factorialSearch 23 (25 !) = false := by
  have h0 : factorialSearch 22 15511210043330985984000000 = false :=
    factorialSearch_false_of_prime (p := 23) (by decide) (by decide) (by decide) (by norm_num)
  have h1 : factorialSearch 4 600 = false :=
    factorialSearch_false_of_prime (p := 5) (by decide) (by decide) (by decide) (by norm_num)
  have h2 : factorialSearch 4 5 = false :=
    factorialSearch_false_of_prime (p := 5) (by decide) (by decide) (by decide) (by norm_num)
  have h3 : factorialSearch 5 5 = false :=
    factorialSearch_false_step (by decide) (by decide) h2 (by intro hd; norm_num [Nat.factorial] at hd)
  have h4 : factorialSearch 5 600 = false :=
    factorialSearch_false_step (by decide) (by decide) h1 (by intro _; norm_num only [Nat.factorial]; exact h3)
  have h5 : factorialSearch 6 600 = false :=
    factorialSearch_false_step (by decide) (by decide) h4 (by intro hd; norm_num [Nat.factorial] at hd)
  have h6 : factorialSearch 7 600 = false :=
    factorialSearch_false_step (by decide) (by decide) h5 (by intro hd; norm_num [Nat.factorial] at hd)
  have h7 : factorialSearch 8 600 = false :=
    factorialSearch_false_step (by decide) (by decide) h6 (by intro hd; norm_num [Nat.factorial] at hd)
  have h8 : factorialSearch 9 600 = false :=
    factorialSearch_false_step (by decide) (by decide) h7 (by intro hd; norm_num [Nat.factorial] at hd)
  have h9 : factorialSearch 10 600 = false :=
    factorialSearch_false_step (by decide) (by decide) h8 (by intro hd; norm_num [Nat.factorial] at hd)
  have h10 : factorialSearch 11 600 = false :=
    factorialSearch_false_step (by decide) (by decide) h9 (by intro hd; norm_num [Nat.factorial] at hd)
  have h11 : factorialSearch 12 600 = false :=
    factorialSearch_false_step (by decide) (by decide) h10 (by intro hd; norm_num [Nat.factorial] at hd)
  have h12 : factorialSearch 13 600 = false :=
    factorialSearch_false_step (by decide) (by decide) h11 (by intro hd; norm_num [Nat.factorial] at hd)
  have h13 : factorialSearch 14 600 = false :=
    factorialSearch_false_step (by decide) (by decide) h12 (by intro hd; norm_num [Nat.factorial] at hd)
  have h14 : factorialSearch 15 600 = false :=
    factorialSearch_false_step (by decide) (by decide) h13 (by intro hd; norm_num [Nat.factorial] at hd)
  have h15 : factorialSearch 16 600 = false :=
    factorialSearch_false_step (by decide) (by decide) h14 (by intro hd; norm_num [Nat.factorial] at hd)
  have h16 : factorialSearch 17 600 = false :=
    factorialSearch_false_step (by decide) (by decide) h15 (by intro hd; norm_num [Nat.factorial] at hd)
  have h17 : factorialSearch 18 600 = false :=
    factorialSearch_false_step (by decide) (by decide) h16 (by intro hd; norm_num [Nat.factorial] at hd)
  have h18 : factorialSearch 19 600 = false :=
    factorialSearch_false_step (by decide) (by decide) h17 (by intro hd; norm_num [Nat.factorial] at hd)
  have h19 : factorialSearch 20 600 = false :=
    factorialSearch_false_step (by decide) (by decide) h18 (by intro hd; norm_num [Nat.factorial] at hd)
  have h20 : factorialSearch 21 600 = false :=
    factorialSearch_false_step (by decide) (by decide) h19 (by intro hd; norm_num [Nat.factorial] at hd)
  have h21 : factorialSearch 22 600 = false :=
    factorialSearch_false_step (by decide) (by decide) h20 (by intro hd; norm_num [Nat.factorial] at hd)
  have h22 : factorialSearch 23 600 = false :=
    factorialSearch_false_step (by decide) (by decide) h21 (by intro hd; norm_num [Nat.factorial] at hd)
  have h23 : factorialSearch 23 15511210043330985984000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h0 (by intro _; norm_num only [Nat.factorial]; exact h22)
  norm_num only [Nat.factorial]
  exact h23

/-- Complete search rejects the target factorial at 26. -/
private theorem search_reject_26 : factorialSearch 24 (26 !) = false := by
  have h0 : factorialSearch 22 403291461126605635584000000 = false :=
    factorialSearch_false_of_prime (p := 23) (by decide) (by decide) (by decide) (by norm_num)
  have h1 : factorialSearch 12 15600 = false :=
    factorialSearch_false_of_prime (p := 13) (by decide) (by decide) (by decide) (by norm_num)
  have h2 : factorialSearch 13 15600 = false :=
    factorialSearch_false_step (by decide) (by decide) h1 (by intro hd; norm_num [Nat.factorial] at hd)
  have h3 : factorialSearch 14 15600 = false :=
    factorialSearch_false_step (by decide) (by decide) h2 (by intro hd; norm_num [Nat.factorial] at hd)
  have h4 : factorialSearch 15 15600 = false :=
    factorialSearch_false_step (by decide) (by decide) h3 (by intro hd; norm_num [Nat.factorial] at hd)
  have h5 : factorialSearch 16 15600 = false :=
    factorialSearch_false_step (by decide) (by decide) h4 (by intro hd; norm_num [Nat.factorial] at hd)
  have h6 : factorialSearch 17 15600 = false :=
    factorialSearch_false_step (by decide) (by decide) h5 (by intro hd; norm_num [Nat.factorial] at hd)
  have h7 : factorialSearch 18 15600 = false :=
    factorialSearch_false_step (by decide) (by decide) h6 (by intro hd; norm_num [Nat.factorial] at hd)
  have h8 : factorialSearch 19 15600 = false :=
    factorialSearch_false_step (by decide) (by decide) h7 (by intro hd; norm_num [Nat.factorial] at hd)
  have h9 : factorialSearch 20 15600 = false :=
    factorialSearch_false_step (by decide) (by decide) h8 (by intro hd; norm_num [Nat.factorial] at hd)
  have h10 : factorialSearch 21 15600 = false :=
    factorialSearch_false_step (by decide) (by decide) h9 (by intro hd; norm_num [Nat.factorial] at hd)
  have h11 : factorialSearch 22 15600 = false :=
    factorialSearch_false_step (by decide) (by decide) h10 (by intro hd; norm_num [Nat.factorial] at hd)
  have h12 : factorialSearch 23 15600 = false :=
    factorialSearch_false_step (by decide) (by decide) h11 (by intro hd; norm_num [Nat.factorial] at hd)
  have h13 : factorialSearch 23 403291461126605635584000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h0 (by intro _; norm_num only [Nat.factorial]; exact h12)
  have h14 : factorialSearch 12 650 = false :=
    factorialSearch_false_of_prime (p := 13) (by decide) (by decide) (by decide) (by norm_num)
  have h15 : factorialSearch 13 650 = false :=
    factorialSearch_false_step (by decide) (by decide) h14 (by intro hd; norm_num [Nat.factorial] at hd)
  have h16 : factorialSearch 14 650 = false :=
    factorialSearch_false_step (by decide) (by decide) h15 (by intro hd; norm_num [Nat.factorial] at hd)
  have h17 : factorialSearch 15 650 = false :=
    factorialSearch_false_step (by decide) (by decide) h16 (by intro hd; norm_num [Nat.factorial] at hd)
  have h18 : factorialSearch 16 650 = false :=
    factorialSearch_false_step (by decide) (by decide) h17 (by intro hd; norm_num [Nat.factorial] at hd)
  have h19 : factorialSearch 17 650 = false :=
    factorialSearch_false_step (by decide) (by decide) h18 (by intro hd; norm_num [Nat.factorial] at hd)
  have h20 : factorialSearch 18 650 = false :=
    factorialSearch_false_step (by decide) (by decide) h19 (by intro hd; norm_num [Nat.factorial] at hd)
  have h21 : factorialSearch 19 650 = false :=
    factorialSearch_false_step (by decide) (by decide) h20 (by intro hd; norm_num [Nat.factorial] at hd)
  have h22 : factorialSearch 20 650 = false :=
    factorialSearch_false_step (by decide) (by decide) h21 (by intro hd; norm_num [Nat.factorial] at hd)
  have h23 : factorialSearch 21 650 = false :=
    factorialSearch_false_step (by decide) (by decide) h22 (by intro hd; norm_num [Nat.factorial] at hd)
  have h24 : factorialSearch 22 650 = false :=
    factorialSearch_false_step (by decide) (by decide) h23 (by intro hd; norm_num [Nat.factorial] at hd)
  have h25 : factorialSearch 23 650 = false :=
    factorialSearch_false_step (by decide) (by decide) h24 (by intro hd; norm_num [Nat.factorial] at hd)
  have h26 : factorialSearch 24 650 = false :=
    factorialSearch_false_step (by decide) (by decide) h25 (by intro hd; norm_num [Nat.factorial] at hd)
  have h27 : factorialSearch 24 403291461126605635584000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h13 (by intro _; norm_num only [Nat.factorial]; exact h26)
  norm_num only [Nat.factorial]
  exact h27

/-- Complete search rejects the target factorial at 27. -/
private theorem search_reject_27 : factorialSearch 25 (27 !) = false := by
  have h0 : factorialSearch 22 10888869450418352160768000000 = false :=
    factorialSearch_false_of_prime (p := 23) (by decide) (by decide) (by decide) (by norm_num)
  have h1 : factorialSearch 12 421200 = false :=
    factorialSearch_false_of_prime (p := 13) (by decide) (by decide) (by decide) (by norm_num)
  have h2 : factorialSearch 13 421200 = false :=
    factorialSearch_false_step (by decide) (by decide) h1 (by intro hd; norm_num [Nat.factorial] at hd)
  have h3 : factorialSearch 14 421200 = false :=
    factorialSearch_false_step (by decide) (by decide) h2 (by intro hd; norm_num [Nat.factorial] at hd)
  have h4 : factorialSearch 15 421200 = false :=
    factorialSearch_false_step (by decide) (by decide) h3 (by intro hd; norm_num [Nat.factorial] at hd)
  have h5 : factorialSearch 16 421200 = false :=
    factorialSearch_false_step (by decide) (by decide) h4 (by intro hd; norm_num [Nat.factorial] at hd)
  have h6 : factorialSearch 17 421200 = false :=
    factorialSearch_false_step (by decide) (by decide) h5 (by intro hd; norm_num [Nat.factorial] at hd)
  have h7 : factorialSearch 18 421200 = false :=
    factorialSearch_false_step (by decide) (by decide) h6 (by intro hd; norm_num [Nat.factorial] at hd)
  have h8 : factorialSearch 19 421200 = false :=
    factorialSearch_false_step (by decide) (by decide) h7 (by intro hd; norm_num [Nat.factorial] at hd)
  have h9 : factorialSearch 20 421200 = false :=
    factorialSearch_false_step (by decide) (by decide) h8 (by intro hd; norm_num [Nat.factorial] at hd)
  have h10 : factorialSearch 21 421200 = false :=
    factorialSearch_false_step (by decide) (by decide) h9 (by intro hd; norm_num [Nat.factorial] at hd)
  have h11 : factorialSearch 22 421200 = false :=
    factorialSearch_false_step (by decide) (by decide) h10 (by intro hd; norm_num [Nat.factorial] at hd)
  have h12 : factorialSearch 23 421200 = false :=
    factorialSearch_false_step (by decide) (by decide) h11 (by intro hd; norm_num [Nat.factorial] at hd)
  have h13 : factorialSearch 23 10888869450418352160768000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h0 (by intro _; norm_num only [Nat.factorial]; exact h12)
  have h14 : factorialSearch 12 17550 = false :=
    factorialSearch_false_of_prime (p := 13) (by decide) (by decide) (by decide) (by norm_num)
  have h15 : factorialSearch 13 17550 = false :=
    factorialSearch_false_step (by decide) (by decide) h14 (by intro hd; norm_num [Nat.factorial] at hd)
  have h16 : factorialSearch 14 17550 = false :=
    factorialSearch_false_step (by decide) (by decide) h15 (by intro hd; norm_num [Nat.factorial] at hd)
  have h17 : factorialSearch 15 17550 = false :=
    factorialSearch_false_step (by decide) (by decide) h16 (by intro hd; norm_num [Nat.factorial] at hd)
  have h18 : factorialSearch 16 17550 = false :=
    factorialSearch_false_step (by decide) (by decide) h17 (by intro hd; norm_num [Nat.factorial] at hd)
  have h19 : factorialSearch 17 17550 = false :=
    factorialSearch_false_step (by decide) (by decide) h18 (by intro hd; norm_num [Nat.factorial] at hd)
  have h20 : factorialSearch 18 17550 = false :=
    factorialSearch_false_step (by decide) (by decide) h19 (by intro hd; norm_num [Nat.factorial] at hd)
  have h21 : factorialSearch 19 17550 = false :=
    factorialSearch_false_step (by decide) (by decide) h20 (by intro hd; norm_num [Nat.factorial] at hd)
  have h22 : factorialSearch 20 17550 = false :=
    factorialSearch_false_step (by decide) (by decide) h21 (by intro hd; norm_num [Nat.factorial] at hd)
  have h23 : factorialSearch 21 17550 = false :=
    factorialSearch_false_step (by decide) (by decide) h22 (by intro hd; norm_num [Nat.factorial] at hd)
  have h24 : factorialSearch 22 17550 = false :=
    factorialSearch_false_step (by decide) (by decide) h23 (by intro hd; norm_num [Nat.factorial] at hd)
  have h25 : factorialSearch 23 17550 = false :=
    factorialSearch_false_step (by decide) (by decide) h24 (by intro hd; norm_num [Nat.factorial] at hd)
  have h26 : factorialSearch 24 17550 = false :=
    factorialSearch_false_step (by decide) (by decide) h25 (by intro hd; norm_num [Nat.factorial] at hd)
  have h27 : factorialSearch 24 10888869450418352160768000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h13 (by intro _; norm_num only [Nat.factorial]; exact h26)
  have h28 : factorialSearch 12 702 = false :=
    factorialSearch_false_of_prime (p := 13) (by decide) (by decide) (by decide) (by norm_num)
  have h29 : factorialSearch 13 702 = false :=
    factorialSearch_false_step (by decide) (by decide) h28 (by intro hd; norm_num [Nat.factorial] at hd)
  have h30 : factorialSearch 14 702 = false :=
    factorialSearch_false_step (by decide) (by decide) h29 (by intro hd; norm_num [Nat.factorial] at hd)
  have h31 : factorialSearch 15 702 = false :=
    factorialSearch_false_step (by decide) (by decide) h30 (by intro hd; norm_num [Nat.factorial] at hd)
  have h32 : factorialSearch 16 702 = false :=
    factorialSearch_false_step (by decide) (by decide) h31 (by intro hd; norm_num [Nat.factorial] at hd)
  have h33 : factorialSearch 17 702 = false :=
    factorialSearch_false_step (by decide) (by decide) h32 (by intro hd; norm_num [Nat.factorial] at hd)
  have h34 : factorialSearch 18 702 = false :=
    factorialSearch_false_step (by decide) (by decide) h33 (by intro hd; norm_num [Nat.factorial] at hd)
  have h35 : factorialSearch 19 702 = false :=
    factorialSearch_false_step (by decide) (by decide) h34 (by intro hd; norm_num [Nat.factorial] at hd)
  have h36 : factorialSearch 20 702 = false :=
    factorialSearch_false_step (by decide) (by decide) h35 (by intro hd; norm_num [Nat.factorial] at hd)
  have h37 : factorialSearch 21 702 = false :=
    factorialSearch_false_step (by decide) (by decide) h36 (by intro hd; norm_num [Nat.factorial] at hd)
  have h38 : factorialSearch 22 702 = false :=
    factorialSearch_false_step (by decide) (by decide) h37 (by intro hd; norm_num [Nat.factorial] at hd)
  have h39 : factorialSearch 23 702 = false :=
    factorialSearch_false_step (by decide) (by decide) h38 (by intro hd; norm_num [Nat.factorial] at hd)
  have h40 : factorialSearch 24 702 = false :=
    factorialSearch_false_step (by decide) (by decide) h39 (by intro hd; norm_num [Nat.factorial] at hd)
  have h41 : factorialSearch 25 702 = false :=
    factorialSearch_false_step (by decide) (by decide) h40 (by intro hd; norm_num [Nat.factorial] at hd)
  have h42 : factorialSearch 25 10888869450418352160768000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h27 (by intro _; norm_num only [Nat.factorial]; exact h41)
  norm_num only [Nat.factorial]
  exact h42

/-- Complete search rejects the target factorial at 28. -/
private theorem search_reject_28 : factorialSearch 26 (28 !) = false := by
  have h0 : factorialSearch 22 304888344611713860501504000000 = false :=
    factorialSearch_false_of_prime (p := 23) (by decide) (by decide) (by decide) (by norm_num)
  have h1 : factorialSearch 12 11793600 = false :=
    factorialSearch_false_of_prime (p := 13) (by decide) (by decide) (by decide) (by norm_num)
  have h2 : factorialSearch 13 11793600 = false :=
    factorialSearch_false_step (by decide) (by decide) h1 (by intro hd; norm_num [Nat.factorial] at hd)
  have h3 : factorialSearch 14 11793600 = false :=
    factorialSearch_false_step (by decide) (by decide) h2 (by intro hd; norm_num [Nat.factorial] at hd)
  have h4 : factorialSearch 15 11793600 = false :=
    factorialSearch_false_step (by decide) (by decide) h3 (by intro hd; norm_num [Nat.factorial] at hd)
  have h5 : factorialSearch 16 11793600 = false :=
    factorialSearch_false_step (by decide) (by decide) h4 (by intro hd; norm_num [Nat.factorial] at hd)
  have h6 : factorialSearch 17 11793600 = false :=
    factorialSearch_false_step (by decide) (by decide) h5 (by intro hd; norm_num [Nat.factorial] at hd)
  have h7 : factorialSearch 18 11793600 = false :=
    factorialSearch_false_step (by decide) (by decide) h6 (by intro hd; norm_num [Nat.factorial] at hd)
  have h8 : factorialSearch 19 11793600 = false :=
    factorialSearch_false_step (by decide) (by decide) h7 (by intro hd; norm_num [Nat.factorial] at hd)
  have h9 : factorialSearch 20 11793600 = false :=
    factorialSearch_false_step (by decide) (by decide) h8 (by intro hd; norm_num [Nat.factorial] at hd)
  have h10 : factorialSearch 21 11793600 = false :=
    factorialSearch_false_step (by decide) (by decide) h9 (by intro hd; norm_num [Nat.factorial] at hd)
  have h11 : factorialSearch 22 11793600 = false :=
    factorialSearch_false_step (by decide) (by decide) h10 (by intro hd; norm_num [Nat.factorial] at hd)
  have h12 : factorialSearch 23 11793600 = false :=
    factorialSearch_false_step (by decide) (by decide) h11 (by intro hd; norm_num [Nat.factorial] at hd)
  have h13 : factorialSearch 23 304888344611713860501504000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h0 (by intro _; norm_num only [Nat.factorial]; exact h12)
  have h14 : factorialSearch 12 491400 = false :=
    factorialSearch_false_of_prime (p := 13) (by decide) (by decide) (by decide) (by norm_num)
  have h15 : factorialSearch 13 491400 = false :=
    factorialSearch_false_step (by decide) (by decide) h14 (by intro hd; norm_num [Nat.factorial] at hd)
  have h16 : factorialSearch 14 491400 = false :=
    factorialSearch_false_step (by decide) (by decide) h15 (by intro hd; norm_num [Nat.factorial] at hd)
  have h17 : factorialSearch 15 491400 = false :=
    factorialSearch_false_step (by decide) (by decide) h16 (by intro hd; norm_num [Nat.factorial] at hd)
  have h18 : factorialSearch 16 491400 = false :=
    factorialSearch_false_step (by decide) (by decide) h17 (by intro hd; norm_num [Nat.factorial] at hd)
  have h19 : factorialSearch 17 491400 = false :=
    factorialSearch_false_step (by decide) (by decide) h18 (by intro hd; norm_num [Nat.factorial] at hd)
  have h20 : factorialSearch 18 491400 = false :=
    factorialSearch_false_step (by decide) (by decide) h19 (by intro hd; norm_num [Nat.factorial] at hd)
  have h21 : factorialSearch 19 491400 = false :=
    factorialSearch_false_step (by decide) (by decide) h20 (by intro hd; norm_num [Nat.factorial] at hd)
  have h22 : factorialSearch 20 491400 = false :=
    factorialSearch_false_step (by decide) (by decide) h21 (by intro hd; norm_num [Nat.factorial] at hd)
  have h23 : factorialSearch 21 491400 = false :=
    factorialSearch_false_step (by decide) (by decide) h22 (by intro hd; norm_num [Nat.factorial] at hd)
  have h24 : factorialSearch 22 491400 = false :=
    factorialSearch_false_step (by decide) (by decide) h23 (by intro hd; norm_num [Nat.factorial] at hd)
  have h25 : factorialSearch 23 491400 = false :=
    factorialSearch_false_step (by decide) (by decide) h24 (by intro hd; norm_num [Nat.factorial] at hd)
  have h26 : factorialSearch 24 491400 = false :=
    factorialSearch_false_step (by decide) (by decide) h25 (by intro hd; norm_num [Nat.factorial] at hd)
  have h27 : factorialSearch 24 304888344611713860501504000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h13 (by intro _; norm_num only [Nat.factorial]; exact h26)
  have h28 : factorialSearch 12 19656 = false :=
    factorialSearch_false_of_prime (p := 13) (by decide) (by decide) (by decide) (by norm_num)
  have h29 : factorialSearch 13 19656 = false :=
    factorialSearch_false_step (by decide) (by decide) h28 (by intro hd; norm_num [Nat.factorial] at hd)
  have h30 : factorialSearch 14 19656 = false :=
    factorialSearch_false_step (by decide) (by decide) h29 (by intro hd; norm_num [Nat.factorial] at hd)
  have h31 : factorialSearch 15 19656 = false :=
    factorialSearch_false_step (by decide) (by decide) h30 (by intro hd; norm_num [Nat.factorial] at hd)
  have h32 : factorialSearch 16 19656 = false :=
    factorialSearch_false_step (by decide) (by decide) h31 (by intro hd; norm_num [Nat.factorial] at hd)
  have h33 : factorialSearch 17 19656 = false :=
    factorialSearch_false_step (by decide) (by decide) h32 (by intro hd; norm_num [Nat.factorial] at hd)
  have h34 : factorialSearch 18 19656 = false :=
    factorialSearch_false_step (by decide) (by decide) h33 (by intro hd; norm_num [Nat.factorial] at hd)
  have h35 : factorialSearch 19 19656 = false :=
    factorialSearch_false_step (by decide) (by decide) h34 (by intro hd; norm_num [Nat.factorial] at hd)
  have h36 : factorialSearch 20 19656 = false :=
    factorialSearch_false_step (by decide) (by decide) h35 (by intro hd; norm_num [Nat.factorial] at hd)
  have h37 : factorialSearch 21 19656 = false :=
    factorialSearch_false_step (by decide) (by decide) h36 (by intro hd; norm_num [Nat.factorial] at hd)
  have h38 : factorialSearch 22 19656 = false :=
    factorialSearch_false_step (by decide) (by decide) h37 (by intro hd; norm_num [Nat.factorial] at hd)
  have h39 : factorialSearch 23 19656 = false :=
    factorialSearch_false_step (by decide) (by decide) h38 (by intro hd; norm_num [Nat.factorial] at hd)
  have h40 : factorialSearch 24 19656 = false :=
    factorialSearch_false_step (by decide) (by decide) h39 (by intro hd; norm_num [Nat.factorial] at hd)
  have h41 : factorialSearch 25 19656 = false :=
    factorialSearch_false_step (by decide) (by decide) h40 (by intro hd; norm_num [Nat.factorial] at hd)
  have h42 : factorialSearch 25 304888344611713860501504000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h27 (by intro _; norm_num only [Nat.factorial]; exact h41)
  have h43 : factorialSearch 6 756 = false :=
    factorialSearch_false_of_prime (p := 7) (by decide) (by decide) (by decide) (by norm_num)
  have h44 : factorialSearch 7 756 = false :=
    factorialSearch_false_step (by decide) (by decide) h43 (by intro hd; norm_num [Nat.factorial] at hd)
  have h45 : factorialSearch 8 756 = false :=
    factorialSearch_false_step (by decide) (by decide) h44 (by intro hd; norm_num [Nat.factorial] at hd)
  have h46 : factorialSearch 9 756 = false :=
    factorialSearch_false_step (by decide) (by decide) h45 (by intro hd; norm_num [Nat.factorial] at hd)
  have h47 : factorialSearch 10 756 = false :=
    factorialSearch_false_step (by decide) (by decide) h46 (by intro hd; norm_num [Nat.factorial] at hd)
  have h48 : factorialSearch 11 756 = false :=
    factorialSearch_false_step (by decide) (by decide) h47 (by intro hd; norm_num [Nat.factorial] at hd)
  have h49 : factorialSearch 12 756 = false :=
    factorialSearch_false_step (by decide) (by decide) h48 (by intro hd; norm_num [Nat.factorial] at hd)
  have h50 : factorialSearch 13 756 = false :=
    factorialSearch_false_step (by decide) (by decide) h49 (by intro hd; norm_num [Nat.factorial] at hd)
  have h51 : factorialSearch 14 756 = false :=
    factorialSearch_false_step (by decide) (by decide) h50 (by intro hd; norm_num [Nat.factorial] at hd)
  have h52 : factorialSearch 15 756 = false :=
    factorialSearch_false_step (by decide) (by decide) h51 (by intro hd; norm_num [Nat.factorial] at hd)
  have h53 : factorialSearch 16 756 = false :=
    factorialSearch_false_step (by decide) (by decide) h52 (by intro hd; norm_num [Nat.factorial] at hd)
  have h54 : factorialSearch 17 756 = false :=
    factorialSearch_false_step (by decide) (by decide) h53 (by intro hd; norm_num [Nat.factorial] at hd)
  have h55 : factorialSearch 18 756 = false :=
    factorialSearch_false_step (by decide) (by decide) h54 (by intro hd; norm_num [Nat.factorial] at hd)
  have h56 : factorialSearch 19 756 = false :=
    factorialSearch_false_step (by decide) (by decide) h55 (by intro hd; norm_num [Nat.factorial] at hd)
  have h57 : factorialSearch 20 756 = false :=
    factorialSearch_false_step (by decide) (by decide) h56 (by intro hd; norm_num [Nat.factorial] at hd)
  have h58 : factorialSearch 21 756 = false :=
    factorialSearch_false_step (by decide) (by decide) h57 (by intro hd; norm_num [Nat.factorial] at hd)
  have h59 : factorialSearch 22 756 = false :=
    factorialSearch_false_step (by decide) (by decide) h58 (by intro hd; norm_num [Nat.factorial] at hd)
  have h60 : factorialSearch 23 756 = false :=
    factorialSearch_false_step (by decide) (by decide) h59 (by intro hd; norm_num [Nat.factorial] at hd)
  have h61 : factorialSearch 24 756 = false :=
    factorialSearch_false_step (by decide) (by decide) h60 (by intro hd; norm_num [Nat.factorial] at hd)
  have h62 : factorialSearch 25 756 = false :=
    factorialSearch_false_step (by decide) (by decide) h61 (by intro hd; norm_num [Nat.factorial] at hd)
  have h63 : factorialSearch 26 756 = false :=
    factorialSearch_false_step (by decide) (by decide) h62 (by intro hd; norm_num [Nat.factorial] at hd)
  have h64 : factorialSearch 26 304888344611713860501504000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h42 (by intro _; norm_num only [Nat.factorial]; exact h63)
  norm_num only [Nat.factorial]
  exact h64

/-- Complete search rejects the target factorial at 29. -/
private theorem search_reject_29 : factorialSearch 27 (29 !) = false := by
  have h0 : factorialSearch 27 8841761993739701954543616000000 = false :=
    factorialSearch_false_of_prime (p := 29) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 30. -/
private theorem search_reject_30 : factorialSearch 28 (30 !) = false := by
  have h0 : factorialSearch 28 265252859812191058636308480000000 = false :=
    factorialSearch_false_of_prime (p := 29) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 31. -/
private theorem search_reject_31 : factorialSearch 29 (31 !) = false := by
  have h0 : factorialSearch 29 8222838654177922817725562880000000 = false :=
    factorialSearch_false_of_prime (p := 31) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 32. -/
private theorem search_reject_32 : factorialSearch 30 (32 !) = false := by
  have h0 : factorialSearch 30 263130836933693530167218012160000000 = false :=
    factorialSearch_false_of_prime (p := 31) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 33. -/
private theorem search_reject_33 : factorialSearch 31 (33 !) = false := by
  have h0 : factorialSearch 30 8683317618811886495518194401280000000 = false :=
    factorialSearch_false_of_prime (p := 31) (by decide) (by decide) (by decide) (by norm_num)
  have h1 : factorialSearch 10 1056 = false :=
    factorialSearch_false_of_prime (p := 11) (by decide) (by decide) (by decide) (by norm_num)
  have h2 : factorialSearch 11 1056 = false :=
    factorialSearch_false_step (by decide) (by decide) h1 (by intro hd; norm_num [Nat.factorial] at hd)
  have h3 : factorialSearch 12 1056 = false :=
    factorialSearch_false_step (by decide) (by decide) h2 (by intro hd; norm_num [Nat.factorial] at hd)
  have h4 : factorialSearch 13 1056 = false :=
    factorialSearch_false_step (by decide) (by decide) h3 (by intro hd; norm_num [Nat.factorial] at hd)
  have h5 : factorialSearch 14 1056 = false :=
    factorialSearch_false_step (by decide) (by decide) h4 (by intro hd; norm_num [Nat.factorial] at hd)
  have h6 : factorialSearch 15 1056 = false :=
    factorialSearch_false_step (by decide) (by decide) h5 (by intro hd; norm_num [Nat.factorial] at hd)
  have h7 : factorialSearch 16 1056 = false :=
    factorialSearch_false_step (by decide) (by decide) h6 (by intro hd; norm_num [Nat.factorial] at hd)
  have h8 : factorialSearch 17 1056 = false :=
    factorialSearch_false_step (by decide) (by decide) h7 (by intro hd; norm_num [Nat.factorial] at hd)
  have h9 : factorialSearch 18 1056 = false :=
    factorialSearch_false_step (by decide) (by decide) h8 (by intro hd; norm_num [Nat.factorial] at hd)
  have h10 : factorialSearch 19 1056 = false :=
    factorialSearch_false_step (by decide) (by decide) h9 (by intro hd; norm_num [Nat.factorial] at hd)
  have h11 : factorialSearch 20 1056 = false :=
    factorialSearch_false_step (by decide) (by decide) h10 (by intro hd; norm_num [Nat.factorial] at hd)
  have h12 : factorialSearch 21 1056 = false :=
    factorialSearch_false_step (by decide) (by decide) h11 (by intro hd; norm_num [Nat.factorial] at hd)
  have h13 : factorialSearch 22 1056 = false :=
    factorialSearch_false_step (by decide) (by decide) h12 (by intro hd; norm_num [Nat.factorial] at hd)
  have h14 : factorialSearch 23 1056 = false :=
    factorialSearch_false_step (by decide) (by decide) h13 (by intro hd; norm_num [Nat.factorial] at hd)
  have h15 : factorialSearch 24 1056 = false :=
    factorialSearch_false_step (by decide) (by decide) h14 (by intro hd; norm_num [Nat.factorial] at hd)
  have h16 : factorialSearch 25 1056 = false :=
    factorialSearch_false_step (by decide) (by decide) h15 (by intro hd; norm_num [Nat.factorial] at hd)
  have h17 : factorialSearch 26 1056 = false :=
    factorialSearch_false_step (by decide) (by decide) h16 (by intro hd; norm_num [Nat.factorial] at hd)
  have h18 : factorialSearch 27 1056 = false :=
    factorialSearch_false_step (by decide) (by decide) h17 (by intro hd; norm_num [Nat.factorial] at hd)
  have h19 : factorialSearch 28 1056 = false :=
    factorialSearch_false_step (by decide) (by decide) h18 (by intro hd; norm_num [Nat.factorial] at hd)
  have h20 : factorialSearch 29 1056 = false :=
    factorialSearch_false_step (by decide) (by decide) h19 (by intro hd; norm_num [Nat.factorial] at hd)
  have h21 : factorialSearch 30 1056 = false :=
    factorialSearch_false_step (by decide) (by decide) h20 (by intro hd; norm_num [Nat.factorial] at hd)
  have h22 : factorialSearch 31 1056 = false :=
    factorialSearch_false_step (by decide) (by decide) h21 (by intro hd; norm_num [Nat.factorial] at hd)
  have h23 : factorialSearch 31 8683317618811886495518194401280000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h0 (by intro _; norm_num only [Nat.factorial]; exact h22)
  norm_num only [Nat.factorial]
  exact h23

/-- Complete search rejects the target factorial at 34. -/
private theorem search_reject_34 : factorialSearch 32 (34 !) = false := by
  have h0 : factorialSearch 30 295232799039604140847618609643520000000 = false :=
    factorialSearch_false_of_prime (p := 31) (by decide) (by decide) (by decide) (by norm_num)
  have h1 : factorialSearch 16 35904 = false :=
    factorialSearch_false_of_prime (p := 17) (by decide) (by decide) (by decide) (by norm_num)
  have h2 : factorialSearch 17 35904 = false :=
    factorialSearch_false_step (by decide) (by decide) h1 (by intro hd; norm_num [Nat.factorial] at hd)
  have h3 : factorialSearch 18 35904 = false :=
    factorialSearch_false_step (by decide) (by decide) h2 (by intro hd; norm_num [Nat.factorial] at hd)
  have h4 : factorialSearch 19 35904 = false :=
    factorialSearch_false_step (by decide) (by decide) h3 (by intro hd; norm_num [Nat.factorial] at hd)
  have h5 : factorialSearch 20 35904 = false :=
    factorialSearch_false_step (by decide) (by decide) h4 (by intro hd; norm_num [Nat.factorial] at hd)
  have h6 : factorialSearch 21 35904 = false :=
    factorialSearch_false_step (by decide) (by decide) h5 (by intro hd; norm_num [Nat.factorial] at hd)
  have h7 : factorialSearch 22 35904 = false :=
    factorialSearch_false_step (by decide) (by decide) h6 (by intro hd; norm_num [Nat.factorial] at hd)
  have h8 : factorialSearch 23 35904 = false :=
    factorialSearch_false_step (by decide) (by decide) h7 (by intro hd; norm_num [Nat.factorial] at hd)
  have h9 : factorialSearch 24 35904 = false :=
    factorialSearch_false_step (by decide) (by decide) h8 (by intro hd; norm_num [Nat.factorial] at hd)
  have h10 : factorialSearch 25 35904 = false :=
    factorialSearch_false_step (by decide) (by decide) h9 (by intro hd; norm_num [Nat.factorial] at hd)
  have h11 : factorialSearch 26 35904 = false :=
    factorialSearch_false_step (by decide) (by decide) h10 (by intro hd; norm_num [Nat.factorial] at hd)
  have h12 : factorialSearch 27 35904 = false :=
    factorialSearch_false_step (by decide) (by decide) h11 (by intro hd; norm_num [Nat.factorial] at hd)
  have h13 : factorialSearch 28 35904 = false :=
    factorialSearch_false_step (by decide) (by decide) h12 (by intro hd; norm_num [Nat.factorial] at hd)
  have h14 : factorialSearch 29 35904 = false :=
    factorialSearch_false_step (by decide) (by decide) h13 (by intro hd; norm_num [Nat.factorial] at hd)
  have h15 : factorialSearch 30 35904 = false :=
    factorialSearch_false_step (by decide) (by decide) h14 (by intro hd; norm_num [Nat.factorial] at hd)
  have h16 : factorialSearch 31 35904 = false :=
    factorialSearch_false_step (by decide) (by decide) h15 (by intro hd; norm_num [Nat.factorial] at hd)
  have h17 : factorialSearch 31 295232799039604140847618609643520000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h0 (by intro _; norm_num only [Nat.factorial]; exact h16)
  have h18 : factorialSearch 16 1122 = false :=
    factorialSearch_false_of_prime (p := 17) (by decide) (by decide) (by decide) (by norm_num)
  have h19 : factorialSearch 17 1122 = false :=
    factorialSearch_false_step (by decide) (by decide) h18 (by intro hd; norm_num [Nat.factorial] at hd)
  have h20 : factorialSearch 18 1122 = false :=
    factorialSearch_false_step (by decide) (by decide) h19 (by intro hd; norm_num [Nat.factorial] at hd)
  have h21 : factorialSearch 19 1122 = false :=
    factorialSearch_false_step (by decide) (by decide) h20 (by intro hd; norm_num [Nat.factorial] at hd)
  have h22 : factorialSearch 20 1122 = false :=
    factorialSearch_false_step (by decide) (by decide) h21 (by intro hd; norm_num [Nat.factorial] at hd)
  have h23 : factorialSearch 21 1122 = false :=
    factorialSearch_false_step (by decide) (by decide) h22 (by intro hd; norm_num [Nat.factorial] at hd)
  have h24 : factorialSearch 22 1122 = false :=
    factorialSearch_false_step (by decide) (by decide) h23 (by intro hd; norm_num [Nat.factorial] at hd)
  have h25 : factorialSearch 23 1122 = false :=
    factorialSearch_false_step (by decide) (by decide) h24 (by intro hd; norm_num [Nat.factorial] at hd)
  have h26 : factorialSearch 24 1122 = false :=
    factorialSearch_false_step (by decide) (by decide) h25 (by intro hd; norm_num [Nat.factorial] at hd)
  have h27 : factorialSearch 25 1122 = false :=
    factorialSearch_false_step (by decide) (by decide) h26 (by intro hd; norm_num [Nat.factorial] at hd)
  have h28 : factorialSearch 26 1122 = false :=
    factorialSearch_false_step (by decide) (by decide) h27 (by intro hd; norm_num [Nat.factorial] at hd)
  have h29 : factorialSearch 27 1122 = false :=
    factorialSearch_false_step (by decide) (by decide) h28 (by intro hd; norm_num [Nat.factorial] at hd)
  have h30 : factorialSearch 28 1122 = false :=
    factorialSearch_false_step (by decide) (by decide) h29 (by intro hd; norm_num [Nat.factorial] at hd)
  have h31 : factorialSearch 29 1122 = false :=
    factorialSearch_false_step (by decide) (by decide) h30 (by intro hd; norm_num [Nat.factorial] at hd)
  have h32 : factorialSearch 30 1122 = false :=
    factorialSearch_false_step (by decide) (by decide) h31 (by intro hd; norm_num [Nat.factorial] at hd)
  have h33 : factorialSearch 31 1122 = false :=
    factorialSearch_false_step (by decide) (by decide) h32 (by intro hd; norm_num [Nat.factorial] at hd)
  have h34 : factorialSearch 32 1122 = false :=
    factorialSearch_false_step (by decide) (by decide) h33 (by intro hd; norm_num [Nat.factorial] at hd)
  have h35 : factorialSearch 32 295232799039604140847618609643520000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h17 (by intro _; norm_num only [Nat.factorial]; exact h34)
  norm_num only [Nat.factorial]
  exact h35

/-- Complete search rejects the target factorial at 35. -/
private theorem search_reject_35 : factorialSearch 33 (35 !) = false := by
  have h0 : factorialSearch 30 10333147966386144929666651337523200000000 = false :=
    factorialSearch_false_of_prime (p := 31) (by decide) (by decide) (by decide) (by norm_num)
  have h1 : factorialSearch 16 1256640 = false :=
    factorialSearch_false_of_prime (p := 17) (by decide) (by decide) (by decide) (by norm_num)
  have h2 : factorialSearch 17 1256640 = false :=
    factorialSearch_false_step (by decide) (by decide) h1 (by intro hd; norm_num [Nat.factorial] at hd)
  have h3 : factorialSearch 18 1256640 = false :=
    factorialSearch_false_step (by decide) (by decide) h2 (by intro hd; norm_num [Nat.factorial] at hd)
  have h4 : factorialSearch 19 1256640 = false :=
    factorialSearch_false_step (by decide) (by decide) h3 (by intro hd; norm_num [Nat.factorial] at hd)
  have h5 : factorialSearch 20 1256640 = false :=
    factorialSearch_false_step (by decide) (by decide) h4 (by intro hd; norm_num [Nat.factorial] at hd)
  have h6 : factorialSearch 21 1256640 = false :=
    factorialSearch_false_step (by decide) (by decide) h5 (by intro hd; norm_num [Nat.factorial] at hd)
  have h7 : factorialSearch 22 1256640 = false :=
    factorialSearch_false_step (by decide) (by decide) h6 (by intro hd; norm_num [Nat.factorial] at hd)
  have h8 : factorialSearch 23 1256640 = false :=
    factorialSearch_false_step (by decide) (by decide) h7 (by intro hd; norm_num [Nat.factorial] at hd)
  have h9 : factorialSearch 24 1256640 = false :=
    factorialSearch_false_step (by decide) (by decide) h8 (by intro hd; norm_num [Nat.factorial] at hd)
  have h10 : factorialSearch 25 1256640 = false :=
    factorialSearch_false_step (by decide) (by decide) h9 (by intro hd; norm_num [Nat.factorial] at hd)
  have h11 : factorialSearch 26 1256640 = false :=
    factorialSearch_false_step (by decide) (by decide) h10 (by intro hd; norm_num [Nat.factorial] at hd)
  have h12 : factorialSearch 27 1256640 = false :=
    factorialSearch_false_step (by decide) (by decide) h11 (by intro hd; norm_num [Nat.factorial] at hd)
  have h13 : factorialSearch 28 1256640 = false :=
    factorialSearch_false_step (by decide) (by decide) h12 (by intro hd; norm_num [Nat.factorial] at hd)
  have h14 : factorialSearch 29 1256640 = false :=
    factorialSearch_false_step (by decide) (by decide) h13 (by intro hd; norm_num [Nat.factorial] at hd)
  have h15 : factorialSearch 30 1256640 = false :=
    factorialSearch_false_step (by decide) (by decide) h14 (by intro hd; norm_num [Nat.factorial] at hd)
  have h16 : factorialSearch 31 1256640 = false :=
    factorialSearch_false_step (by decide) (by decide) h15 (by intro hd; norm_num [Nat.factorial] at hd)
  have h17 : factorialSearch 31 10333147966386144929666651337523200000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h0 (by intro _; norm_num only [Nat.factorial]; exact h16)
  have h18 : factorialSearch 16 39270 = false :=
    factorialSearch_false_of_prime (p := 17) (by decide) (by decide) (by decide) (by norm_num)
  have h19 : factorialSearch 17 39270 = false :=
    factorialSearch_false_step (by decide) (by decide) h18 (by intro hd; norm_num [Nat.factorial] at hd)
  have h20 : factorialSearch 18 39270 = false :=
    factorialSearch_false_step (by decide) (by decide) h19 (by intro hd; norm_num [Nat.factorial] at hd)
  have h21 : factorialSearch 19 39270 = false :=
    factorialSearch_false_step (by decide) (by decide) h20 (by intro hd; norm_num [Nat.factorial] at hd)
  have h22 : factorialSearch 20 39270 = false :=
    factorialSearch_false_step (by decide) (by decide) h21 (by intro hd; norm_num [Nat.factorial] at hd)
  have h23 : factorialSearch 21 39270 = false :=
    factorialSearch_false_step (by decide) (by decide) h22 (by intro hd; norm_num [Nat.factorial] at hd)
  have h24 : factorialSearch 22 39270 = false :=
    factorialSearch_false_step (by decide) (by decide) h23 (by intro hd; norm_num [Nat.factorial] at hd)
  have h25 : factorialSearch 23 39270 = false :=
    factorialSearch_false_step (by decide) (by decide) h24 (by intro hd; norm_num [Nat.factorial] at hd)
  have h26 : factorialSearch 24 39270 = false :=
    factorialSearch_false_step (by decide) (by decide) h25 (by intro hd; norm_num [Nat.factorial] at hd)
  have h27 : factorialSearch 25 39270 = false :=
    factorialSearch_false_step (by decide) (by decide) h26 (by intro hd; norm_num [Nat.factorial] at hd)
  have h28 : factorialSearch 26 39270 = false :=
    factorialSearch_false_step (by decide) (by decide) h27 (by intro hd; norm_num [Nat.factorial] at hd)
  have h29 : factorialSearch 27 39270 = false :=
    factorialSearch_false_step (by decide) (by decide) h28 (by intro hd; norm_num [Nat.factorial] at hd)
  have h30 : factorialSearch 28 39270 = false :=
    factorialSearch_false_step (by decide) (by decide) h29 (by intro hd; norm_num [Nat.factorial] at hd)
  have h31 : factorialSearch 29 39270 = false :=
    factorialSearch_false_step (by decide) (by decide) h30 (by intro hd; norm_num [Nat.factorial] at hd)
  have h32 : factorialSearch 30 39270 = false :=
    factorialSearch_false_step (by decide) (by decide) h31 (by intro hd; norm_num [Nat.factorial] at hd)
  have h33 : factorialSearch 31 39270 = false :=
    factorialSearch_false_step (by decide) (by decide) h32 (by intro hd; norm_num [Nat.factorial] at hd)
  have h34 : factorialSearch 32 39270 = false :=
    factorialSearch_false_step (by decide) (by decide) h33 (by intro hd; norm_num [Nat.factorial] at hd)
  have h35 : factorialSearch 32 10333147966386144929666651337523200000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h17 (by intro _; norm_num only [Nat.factorial]; exact h34)
  have h36 : factorialSearch 16 1190 = false :=
    factorialSearch_false_of_prime (p := 17) (by decide) (by decide) (by decide) (by norm_num)
  have h37 : factorialSearch 17 1190 = false :=
    factorialSearch_false_step (by decide) (by decide) h36 (by intro hd; norm_num [Nat.factorial] at hd)
  have h38 : factorialSearch 18 1190 = false :=
    factorialSearch_false_step (by decide) (by decide) h37 (by intro hd; norm_num [Nat.factorial] at hd)
  have h39 : factorialSearch 19 1190 = false :=
    factorialSearch_false_step (by decide) (by decide) h38 (by intro hd; norm_num [Nat.factorial] at hd)
  have h40 : factorialSearch 20 1190 = false :=
    factorialSearch_false_step (by decide) (by decide) h39 (by intro hd; norm_num [Nat.factorial] at hd)
  have h41 : factorialSearch 21 1190 = false :=
    factorialSearch_false_step (by decide) (by decide) h40 (by intro hd; norm_num [Nat.factorial] at hd)
  have h42 : factorialSearch 22 1190 = false :=
    factorialSearch_false_step (by decide) (by decide) h41 (by intro hd; norm_num [Nat.factorial] at hd)
  have h43 : factorialSearch 23 1190 = false :=
    factorialSearch_false_step (by decide) (by decide) h42 (by intro hd; norm_num [Nat.factorial] at hd)
  have h44 : factorialSearch 24 1190 = false :=
    factorialSearch_false_step (by decide) (by decide) h43 (by intro hd; norm_num [Nat.factorial] at hd)
  have h45 : factorialSearch 25 1190 = false :=
    factorialSearch_false_step (by decide) (by decide) h44 (by intro hd; norm_num [Nat.factorial] at hd)
  have h46 : factorialSearch 26 1190 = false :=
    factorialSearch_false_step (by decide) (by decide) h45 (by intro hd; norm_num [Nat.factorial] at hd)
  have h47 : factorialSearch 27 1190 = false :=
    factorialSearch_false_step (by decide) (by decide) h46 (by intro hd; norm_num [Nat.factorial] at hd)
  have h48 : factorialSearch 28 1190 = false :=
    factorialSearch_false_step (by decide) (by decide) h47 (by intro hd; norm_num [Nat.factorial] at hd)
  have h49 : factorialSearch 29 1190 = false :=
    factorialSearch_false_step (by decide) (by decide) h48 (by intro hd; norm_num [Nat.factorial] at hd)
  have h50 : factorialSearch 30 1190 = false :=
    factorialSearch_false_step (by decide) (by decide) h49 (by intro hd; norm_num [Nat.factorial] at hd)
  have h51 : factorialSearch 31 1190 = false :=
    factorialSearch_false_step (by decide) (by decide) h50 (by intro hd; norm_num [Nat.factorial] at hd)
  have h52 : factorialSearch 32 1190 = false :=
    factorialSearch_false_step (by decide) (by decide) h51 (by intro hd; norm_num [Nat.factorial] at hd)
  have h53 : factorialSearch 33 1190 = false :=
    factorialSearch_false_step (by decide) (by decide) h52 (by intro hd; norm_num [Nat.factorial] at hd)
  have h54 : factorialSearch 33 10333147966386144929666651337523200000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h35 (by intro _; norm_num only [Nat.factorial]; exact h53)
  norm_num only [Nat.factorial]
  exact h54

/-- Complete search rejects the target factorial at 36. -/
private theorem search_reject_36 : factorialSearch 34 (36 !) = false := by
  have h0 : factorialSearch 30 371993326789901217467999448150835200000000 = false :=
    factorialSearch_false_of_prime (p := 31) (by decide) (by decide) (by decide) (by norm_num)
  have h1 : factorialSearch 16 45239040 = false :=
    factorialSearch_false_of_prime (p := 17) (by decide) (by decide) (by decide) (by norm_num)
  have h2 : factorialSearch 17 45239040 = false :=
    factorialSearch_false_step (by decide) (by decide) h1 (by intro hd; norm_num [Nat.factorial] at hd)
  have h3 : factorialSearch 18 45239040 = false :=
    factorialSearch_false_step (by decide) (by decide) h2 (by intro hd; norm_num [Nat.factorial] at hd)
  have h4 : factorialSearch 19 45239040 = false :=
    factorialSearch_false_step (by decide) (by decide) h3 (by intro hd; norm_num [Nat.factorial] at hd)
  have h5 : factorialSearch 20 45239040 = false :=
    factorialSearch_false_step (by decide) (by decide) h4 (by intro hd; norm_num [Nat.factorial] at hd)
  have h6 : factorialSearch 21 45239040 = false :=
    factorialSearch_false_step (by decide) (by decide) h5 (by intro hd; norm_num [Nat.factorial] at hd)
  have h7 : factorialSearch 22 45239040 = false :=
    factorialSearch_false_step (by decide) (by decide) h6 (by intro hd; norm_num [Nat.factorial] at hd)
  have h8 : factorialSearch 23 45239040 = false :=
    factorialSearch_false_step (by decide) (by decide) h7 (by intro hd; norm_num [Nat.factorial] at hd)
  have h9 : factorialSearch 24 45239040 = false :=
    factorialSearch_false_step (by decide) (by decide) h8 (by intro hd; norm_num [Nat.factorial] at hd)
  have h10 : factorialSearch 25 45239040 = false :=
    factorialSearch_false_step (by decide) (by decide) h9 (by intro hd; norm_num [Nat.factorial] at hd)
  have h11 : factorialSearch 26 45239040 = false :=
    factorialSearch_false_step (by decide) (by decide) h10 (by intro hd; norm_num [Nat.factorial] at hd)
  have h12 : factorialSearch 27 45239040 = false :=
    factorialSearch_false_step (by decide) (by decide) h11 (by intro hd; norm_num [Nat.factorial] at hd)
  have h13 : factorialSearch 28 45239040 = false :=
    factorialSearch_false_step (by decide) (by decide) h12 (by intro hd; norm_num [Nat.factorial] at hd)
  have h14 : factorialSearch 29 45239040 = false :=
    factorialSearch_false_step (by decide) (by decide) h13 (by intro hd; norm_num [Nat.factorial] at hd)
  have h15 : factorialSearch 30 45239040 = false :=
    factorialSearch_false_step (by decide) (by decide) h14 (by intro hd; norm_num [Nat.factorial] at hd)
  have h16 : factorialSearch 31 45239040 = false :=
    factorialSearch_false_step (by decide) (by decide) h15 (by intro hd; norm_num [Nat.factorial] at hd)
  have h17 : factorialSearch 31 371993326789901217467999448150835200000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h0 (by intro _; norm_num only [Nat.factorial]; exact h16)
  have h18 : factorialSearch 16 1413720 = false :=
    factorialSearch_false_of_prime (p := 17) (by decide) (by decide) (by decide) (by norm_num)
  have h19 : factorialSearch 17 1413720 = false :=
    factorialSearch_false_step (by decide) (by decide) h18 (by intro hd; norm_num [Nat.factorial] at hd)
  have h20 : factorialSearch 18 1413720 = false :=
    factorialSearch_false_step (by decide) (by decide) h19 (by intro hd; norm_num [Nat.factorial] at hd)
  have h21 : factorialSearch 19 1413720 = false :=
    factorialSearch_false_step (by decide) (by decide) h20 (by intro hd; norm_num [Nat.factorial] at hd)
  have h22 : factorialSearch 20 1413720 = false :=
    factorialSearch_false_step (by decide) (by decide) h21 (by intro hd; norm_num [Nat.factorial] at hd)
  have h23 : factorialSearch 21 1413720 = false :=
    factorialSearch_false_step (by decide) (by decide) h22 (by intro hd; norm_num [Nat.factorial] at hd)
  have h24 : factorialSearch 22 1413720 = false :=
    factorialSearch_false_step (by decide) (by decide) h23 (by intro hd; norm_num [Nat.factorial] at hd)
  have h25 : factorialSearch 23 1413720 = false :=
    factorialSearch_false_step (by decide) (by decide) h24 (by intro hd; norm_num [Nat.factorial] at hd)
  have h26 : factorialSearch 24 1413720 = false :=
    factorialSearch_false_step (by decide) (by decide) h25 (by intro hd; norm_num [Nat.factorial] at hd)
  have h27 : factorialSearch 25 1413720 = false :=
    factorialSearch_false_step (by decide) (by decide) h26 (by intro hd; norm_num [Nat.factorial] at hd)
  have h28 : factorialSearch 26 1413720 = false :=
    factorialSearch_false_step (by decide) (by decide) h27 (by intro hd; norm_num [Nat.factorial] at hd)
  have h29 : factorialSearch 27 1413720 = false :=
    factorialSearch_false_step (by decide) (by decide) h28 (by intro hd; norm_num [Nat.factorial] at hd)
  have h30 : factorialSearch 28 1413720 = false :=
    factorialSearch_false_step (by decide) (by decide) h29 (by intro hd; norm_num [Nat.factorial] at hd)
  have h31 : factorialSearch 29 1413720 = false :=
    factorialSearch_false_step (by decide) (by decide) h30 (by intro hd; norm_num [Nat.factorial] at hd)
  have h32 : factorialSearch 30 1413720 = false :=
    factorialSearch_false_step (by decide) (by decide) h31 (by intro hd; norm_num [Nat.factorial] at hd)
  have h33 : factorialSearch 31 1413720 = false :=
    factorialSearch_false_step (by decide) (by decide) h32 (by intro hd; norm_num [Nat.factorial] at hd)
  have h34 : factorialSearch 32 1413720 = false :=
    factorialSearch_false_step (by decide) (by decide) h33 (by intro hd; norm_num [Nat.factorial] at hd)
  have h35 : factorialSearch 32 371993326789901217467999448150835200000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h17 (by intro _; norm_num only [Nat.factorial]; exact h34)
  have h36 : factorialSearch 16 42840 = false :=
    factorialSearch_false_of_prime (p := 17) (by decide) (by decide) (by decide) (by norm_num)
  have h37 : factorialSearch 17 42840 = false :=
    factorialSearch_false_step (by decide) (by decide) h36 (by intro hd; norm_num [Nat.factorial] at hd)
  have h38 : factorialSearch 18 42840 = false :=
    factorialSearch_false_step (by decide) (by decide) h37 (by intro hd; norm_num [Nat.factorial] at hd)
  have h39 : factorialSearch 19 42840 = false :=
    factorialSearch_false_step (by decide) (by decide) h38 (by intro hd; norm_num [Nat.factorial] at hd)
  have h40 : factorialSearch 20 42840 = false :=
    factorialSearch_false_step (by decide) (by decide) h39 (by intro hd; norm_num [Nat.factorial] at hd)
  have h41 : factorialSearch 21 42840 = false :=
    factorialSearch_false_step (by decide) (by decide) h40 (by intro hd; norm_num [Nat.factorial] at hd)
  have h42 : factorialSearch 22 42840 = false :=
    factorialSearch_false_step (by decide) (by decide) h41 (by intro hd; norm_num [Nat.factorial] at hd)
  have h43 : factorialSearch 23 42840 = false :=
    factorialSearch_false_step (by decide) (by decide) h42 (by intro hd; norm_num [Nat.factorial] at hd)
  have h44 : factorialSearch 24 42840 = false :=
    factorialSearch_false_step (by decide) (by decide) h43 (by intro hd; norm_num [Nat.factorial] at hd)
  have h45 : factorialSearch 25 42840 = false :=
    factorialSearch_false_step (by decide) (by decide) h44 (by intro hd; norm_num [Nat.factorial] at hd)
  have h46 : factorialSearch 26 42840 = false :=
    factorialSearch_false_step (by decide) (by decide) h45 (by intro hd; norm_num [Nat.factorial] at hd)
  have h47 : factorialSearch 27 42840 = false :=
    factorialSearch_false_step (by decide) (by decide) h46 (by intro hd; norm_num [Nat.factorial] at hd)
  have h48 : factorialSearch 28 42840 = false :=
    factorialSearch_false_step (by decide) (by decide) h47 (by intro hd; norm_num [Nat.factorial] at hd)
  have h49 : factorialSearch 29 42840 = false :=
    factorialSearch_false_step (by decide) (by decide) h48 (by intro hd; norm_num [Nat.factorial] at hd)
  have h50 : factorialSearch 30 42840 = false :=
    factorialSearch_false_step (by decide) (by decide) h49 (by intro hd; norm_num [Nat.factorial] at hd)
  have h51 : factorialSearch 31 42840 = false :=
    factorialSearch_false_step (by decide) (by decide) h50 (by intro hd; norm_num [Nat.factorial] at hd)
  have h52 : factorialSearch 32 42840 = false :=
    factorialSearch_false_step (by decide) (by decide) h51 (by intro hd; norm_num [Nat.factorial] at hd)
  have h53 : factorialSearch 33 42840 = false :=
    factorialSearch_false_step (by decide) (by decide) h52 (by intro hd; norm_num [Nat.factorial] at hd)
  have h54 : factorialSearch 33 371993326789901217467999448150835200000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h35 (by intro _; norm_num only [Nat.factorial]; exact h53)
  have h55 : factorialSearch 6 1260 = false :=
    factorialSearch_false_of_prime (p := 7) (by decide) (by decide) (by decide) (by norm_num)
  have h56 : factorialSearch 7 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h55 (by intro hd; norm_num [Nat.factorial] at hd)
  have h57 : factorialSearch 8 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h56 (by intro hd; norm_num [Nat.factorial] at hd)
  have h58 : factorialSearch 9 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h57 (by intro hd; norm_num [Nat.factorial] at hd)
  have h59 : factorialSearch 10 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h58 (by intro hd; norm_num [Nat.factorial] at hd)
  have h60 : factorialSearch 11 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h59 (by intro hd; norm_num [Nat.factorial] at hd)
  have h61 : factorialSearch 12 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h60 (by intro hd; norm_num [Nat.factorial] at hd)
  have h62 : factorialSearch 13 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h61 (by intro hd; norm_num [Nat.factorial] at hd)
  have h63 : factorialSearch 14 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h62 (by intro hd; norm_num [Nat.factorial] at hd)
  have h64 : factorialSearch 15 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h63 (by intro hd; norm_num [Nat.factorial] at hd)
  have h65 : factorialSearch 16 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h64 (by intro hd; norm_num [Nat.factorial] at hd)
  have h66 : factorialSearch 17 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h65 (by intro hd; norm_num [Nat.factorial] at hd)
  have h67 : factorialSearch 18 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h66 (by intro hd; norm_num [Nat.factorial] at hd)
  have h68 : factorialSearch 19 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h67 (by intro hd; norm_num [Nat.factorial] at hd)
  have h69 : factorialSearch 20 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h68 (by intro hd; norm_num [Nat.factorial] at hd)
  have h70 : factorialSearch 21 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h69 (by intro hd; norm_num [Nat.factorial] at hd)
  have h71 : factorialSearch 22 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h70 (by intro hd; norm_num [Nat.factorial] at hd)
  have h72 : factorialSearch 23 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h71 (by intro hd; norm_num [Nat.factorial] at hd)
  have h73 : factorialSearch 24 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h72 (by intro hd; norm_num [Nat.factorial] at hd)
  have h74 : factorialSearch 25 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h73 (by intro hd; norm_num [Nat.factorial] at hd)
  have h75 : factorialSearch 26 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h74 (by intro hd; norm_num [Nat.factorial] at hd)
  have h76 : factorialSearch 27 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h75 (by intro hd; norm_num [Nat.factorial] at hd)
  have h77 : factorialSearch 28 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h76 (by intro hd; norm_num [Nat.factorial] at hd)
  have h78 : factorialSearch 29 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h77 (by intro hd; norm_num [Nat.factorial] at hd)
  have h79 : factorialSearch 30 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h78 (by intro hd; norm_num [Nat.factorial] at hd)
  have h80 : factorialSearch 31 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h79 (by intro hd; norm_num [Nat.factorial] at hd)
  have h81 : factorialSearch 32 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h80 (by intro hd; norm_num [Nat.factorial] at hd)
  have h82 : factorialSearch 33 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h81 (by intro hd; norm_num [Nat.factorial] at hd)
  have h83 : factorialSearch 34 1260 = false :=
    factorialSearch_false_step (by decide) (by decide) h82 (by intro hd; norm_num [Nat.factorial] at hd)
  have h84 : factorialSearch 34 371993326789901217467999448150835200000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h54 (by intro _; norm_num only [Nat.factorial]; exact h83)
  norm_num only [Nat.factorial]
  exact h84

/-- Complete search rejects the target factorial at 37. -/
private theorem search_reject_37 : factorialSearch 35 (37 !) = false := by
  have h0 : factorialSearch 35 13763753091226345046315979581580902400000000 = false :=
    factorialSearch_false_of_prime (p := 37) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 38. -/
private theorem search_reject_38 : factorialSearch 36 (38 !) = false := by
  have h0 : factorialSearch 36 523022617466601111760007224100074291200000000 = false :=
    factorialSearch_false_of_prime (p := 37) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 39. -/
private theorem search_reject_39 : factorialSearch 37 (39 !) = false := by
  have h0 : factorialSearch 36 20397882081197443358640281739902897356800000000 = false :=
    factorialSearch_false_of_prime (p := 37) (by decide) (by decide) (by decide) (by norm_num)
  have h1 : factorialSearch 18 1482 = false :=
    factorialSearch_false_of_prime (p := 19) (by decide) (by decide) (by decide) (by norm_num)
  have h2 : factorialSearch 19 1482 = false :=
    factorialSearch_false_step (by decide) (by decide) h1 (by intro hd; norm_num [Nat.factorial] at hd)
  have h3 : factorialSearch 20 1482 = false :=
    factorialSearch_false_step (by decide) (by decide) h2 (by intro hd; norm_num [Nat.factorial] at hd)
  have h4 : factorialSearch 21 1482 = false :=
    factorialSearch_false_step (by decide) (by decide) h3 (by intro hd; norm_num [Nat.factorial] at hd)
  have h5 : factorialSearch 22 1482 = false :=
    factorialSearch_false_step (by decide) (by decide) h4 (by intro hd; norm_num [Nat.factorial] at hd)
  have h6 : factorialSearch 23 1482 = false :=
    factorialSearch_false_step (by decide) (by decide) h5 (by intro hd; norm_num [Nat.factorial] at hd)
  have h7 : factorialSearch 24 1482 = false :=
    factorialSearch_false_step (by decide) (by decide) h6 (by intro hd; norm_num [Nat.factorial] at hd)
  have h8 : factorialSearch 25 1482 = false :=
    factorialSearch_false_step (by decide) (by decide) h7 (by intro hd; norm_num [Nat.factorial] at hd)
  have h9 : factorialSearch 26 1482 = false :=
    factorialSearch_false_step (by decide) (by decide) h8 (by intro hd; norm_num [Nat.factorial] at hd)
  have h10 : factorialSearch 27 1482 = false :=
    factorialSearch_false_step (by decide) (by decide) h9 (by intro hd; norm_num [Nat.factorial] at hd)
  have h11 : factorialSearch 28 1482 = false :=
    factorialSearch_false_step (by decide) (by decide) h10 (by intro hd; norm_num [Nat.factorial] at hd)
  have h12 : factorialSearch 29 1482 = false :=
    factorialSearch_false_step (by decide) (by decide) h11 (by intro hd; norm_num [Nat.factorial] at hd)
  have h13 : factorialSearch 30 1482 = false :=
    factorialSearch_false_step (by decide) (by decide) h12 (by intro hd; norm_num [Nat.factorial] at hd)
  have h14 : factorialSearch 31 1482 = false :=
    factorialSearch_false_step (by decide) (by decide) h13 (by intro hd; norm_num [Nat.factorial] at hd)
  have h15 : factorialSearch 32 1482 = false :=
    factorialSearch_false_step (by decide) (by decide) h14 (by intro hd; norm_num [Nat.factorial] at hd)
  have h16 : factorialSearch 33 1482 = false :=
    factorialSearch_false_step (by decide) (by decide) h15 (by intro hd; norm_num [Nat.factorial] at hd)
  have h17 : factorialSearch 34 1482 = false :=
    factorialSearch_false_step (by decide) (by decide) h16 (by intro hd; norm_num [Nat.factorial] at hd)
  have h18 : factorialSearch 35 1482 = false :=
    factorialSearch_false_step (by decide) (by decide) h17 (by intro hd; norm_num [Nat.factorial] at hd)
  have h19 : factorialSearch 36 1482 = false :=
    factorialSearch_false_step (by decide) (by decide) h18 (by intro hd; norm_num [Nat.factorial] at hd)
  have h20 : factorialSearch 37 1482 = false :=
    factorialSearch_false_step (by decide) (by decide) h19 (by intro hd; norm_num [Nat.factorial] at hd)
  have h21 : factorialSearch 37 20397882081197443358640281739902897356800000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h0 (by intro _; norm_num only [Nat.factorial]; exact h20)
  norm_num only [Nat.factorial]
  exact h21

/-- Complete search rejects the target factorial at 40. -/
private theorem search_reject_40 : factorialSearch 38 (40 !) = false := by
  have h0 : factorialSearch 36 815915283247897734345611269596115894272000000000 = false :=
    factorialSearch_false_of_prime (p := 37) (by decide) (by decide) (by decide) (by norm_num)
  have h1 : factorialSearch 18 59280 = false :=
    factorialSearch_false_of_prime (p := 19) (by decide) (by decide) (by decide) (by norm_num)
  have h2 : factorialSearch 19 59280 = false :=
    factorialSearch_false_step (by decide) (by decide) h1 (by intro hd; norm_num [Nat.factorial] at hd)
  have h3 : factorialSearch 20 59280 = false :=
    factorialSearch_false_step (by decide) (by decide) h2 (by intro hd; norm_num [Nat.factorial] at hd)
  have h4 : factorialSearch 21 59280 = false :=
    factorialSearch_false_step (by decide) (by decide) h3 (by intro hd; norm_num [Nat.factorial] at hd)
  have h5 : factorialSearch 22 59280 = false :=
    factorialSearch_false_step (by decide) (by decide) h4 (by intro hd; norm_num [Nat.factorial] at hd)
  have h6 : factorialSearch 23 59280 = false :=
    factorialSearch_false_step (by decide) (by decide) h5 (by intro hd; norm_num [Nat.factorial] at hd)
  have h7 : factorialSearch 24 59280 = false :=
    factorialSearch_false_step (by decide) (by decide) h6 (by intro hd; norm_num [Nat.factorial] at hd)
  have h8 : factorialSearch 25 59280 = false :=
    factorialSearch_false_step (by decide) (by decide) h7 (by intro hd; norm_num [Nat.factorial] at hd)
  have h9 : factorialSearch 26 59280 = false :=
    factorialSearch_false_step (by decide) (by decide) h8 (by intro hd; norm_num [Nat.factorial] at hd)
  have h10 : factorialSearch 27 59280 = false :=
    factorialSearch_false_step (by decide) (by decide) h9 (by intro hd; norm_num [Nat.factorial] at hd)
  have h11 : factorialSearch 28 59280 = false :=
    factorialSearch_false_step (by decide) (by decide) h10 (by intro hd; norm_num [Nat.factorial] at hd)
  have h12 : factorialSearch 29 59280 = false :=
    factorialSearch_false_step (by decide) (by decide) h11 (by intro hd; norm_num [Nat.factorial] at hd)
  have h13 : factorialSearch 30 59280 = false :=
    factorialSearch_false_step (by decide) (by decide) h12 (by intro hd; norm_num [Nat.factorial] at hd)
  have h14 : factorialSearch 31 59280 = false :=
    factorialSearch_false_step (by decide) (by decide) h13 (by intro hd; norm_num [Nat.factorial] at hd)
  have h15 : factorialSearch 32 59280 = false :=
    factorialSearch_false_step (by decide) (by decide) h14 (by intro hd; norm_num [Nat.factorial] at hd)
  have h16 : factorialSearch 33 59280 = false :=
    factorialSearch_false_step (by decide) (by decide) h15 (by intro hd; norm_num [Nat.factorial] at hd)
  have h17 : factorialSearch 34 59280 = false :=
    factorialSearch_false_step (by decide) (by decide) h16 (by intro hd; norm_num [Nat.factorial] at hd)
  have h18 : factorialSearch 35 59280 = false :=
    factorialSearch_false_step (by decide) (by decide) h17 (by intro hd; norm_num [Nat.factorial] at hd)
  have h19 : factorialSearch 36 59280 = false :=
    factorialSearch_false_step (by decide) (by decide) h18 (by intro hd; norm_num [Nat.factorial] at hd)
  have h20 : factorialSearch 37 59280 = false :=
    factorialSearch_false_step (by decide) (by decide) h19 (by intro hd; norm_num [Nat.factorial] at hd)
  have h21 : factorialSearch 37 815915283247897734345611269596115894272000000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h0 (by intro _; norm_num only [Nat.factorial]; exact h20)
  have h22 : factorialSearch 12 1560 = false :=
    factorialSearch_false_of_prime (p := 13) (by decide) (by decide) (by decide) (by norm_num)
  have h23 : factorialSearch 13 1560 = false :=
    factorialSearch_false_step (by decide) (by decide) h22 (by intro hd; norm_num [Nat.factorial] at hd)
  have h24 : factorialSearch 14 1560 = false :=
    factorialSearch_false_step (by decide) (by decide) h23 (by intro hd; norm_num [Nat.factorial] at hd)
  have h25 : factorialSearch 15 1560 = false :=
    factorialSearch_false_step (by decide) (by decide) h24 (by intro hd; norm_num [Nat.factorial] at hd)
  have h26 : factorialSearch 16 1560 = false :=
    factorialSearch_false_step (by decide) (by decide) h25 (by intro hd; norm_num [Nat.factorial] at hd)
  have h27 : factorialSearch 17 1560 = false :=
    factorialSearch_false_step (by decide) (by decide) h26 (by intro hd; norm_num [Nat.factorial] at hd)
  have h28 : factorialSearch 18 1560 = false :=
    factorialSearch_false_step (by decide) (by decide) h27 (by intro hd; norm_num [Nat.factorial] at hd)
  have h29 : factorialSearch 19 1560 = false :=
    factorialSearch_false_step (by decide) (by decide) h28 (by intro hd; norm_num [Nat.factorial] at hd)
  have h30 : factorialSearch 20 1560 = false :=
    factorialSearch_false_step (by decide) (by decide) h29 (by intro hd; norm_num [Nat.factorial] at hd)
  have h31 : factorialSearch 21 1560 = false :=
    factorialSearch_false_step (by decide) (by decide) h30 (by intro hd; norm_num [Nat.factorial] at hd)
  have h32 : factorialSearch 22 1560 = false :=
    factorialSearch_false_step (by decide) (by decide) h31 (by intro hd; norm_num [Nat.factorial] at hd)
  have h33 : factorialSearch 23 1560 = false :=
    factorialSearch_false_step (by decide) (by decide) h32 (by intro hd; norm_num [Nat.factorial] at hd)
  have h34 : factorialSearch 24 1560 = false :=
    factorialSearch_false_step (by decide) (by decide) h33 (by intro hd; norm_num [Nat.factorial] at hd)
  have h35 : factorialSearch 25 1560 = false :=
    factorialSearch_false_step (by decide) (by decide) h34 (by intro hd; norm_num [Nat.factorial] at hd)
  have h36 : factorialSearch 26 1560 = false :=
    factorialSearch_false_step (by decide) (by decide) h35 (by intro hd; norm_num [Nat.factorial] at hd)
  have h37 : factorialSearch 27 1560 = false :=
    factorialSearch_false_step (by decide) (by decide) h36 (by intro hd; norm_num [Nat.factorial] at hd)
  have h38 : factorialSearch 28 1560 = false :=
    factorialSearch_false_step (by decide) (by decide) h37 (by intro hd; norm_num [Nat.factorial] at hd)
  have h39 : factorialSearch 29 1560 = false :=
    factorialSearch_false_step (by decide) (by decide) h38 (by intro hd; norm_num [Nat.factorial] at hd)
  have h40 : factorialSearch 30 1560 = false :=
    factorialSearch_false_step (by decide) (by decide) h39 (by intro hd; norm_num [Nat.factorial] at hd)
  have h41 : factorialSearch 31 1560 = false :=
    factorialSearch_false_step (by decide) (by decide) h40 (by intro hd; norm_num [Nat.factorial] at hd)
  have h42 : factorialSearch 32 1560 = false :=
    factorialSearch_false_step (by decide) (by decide) h41 (by intro hd; norm_num [Nat.factorial] at hd)
  have h43 : factorialSearch 33 1560 = false :=
    factorialSearch_false_step (by decide) (by decide) h42 (by intro hd; norm_num [Nat.factorial] at hd)
  have h44 : factorialSearch 34 1560 = false :=
    factorialSearch_false_step (by decide) (by decide) h43 (by intro hd; norm_num [Nat.factorial] at hd)
  have h45 : factorialSearch 35 1560 = false :=
    factorialSearch_false_step (by decide) (by decide) h44 (by intro hd; norm_num [Nat.factorial] at hd)
  have h46 : factorialSearch 36 1560 = false :=
    factorialSearch_false_step (by decide) (by decide) h45 (by intro hd; norm_num [Nat.factorial] at hd)
  have h47 : factorialSearch 37 1560 = false :=
    factorialSearch_false_step (by decide) (by decide) h46 (by intro hd; norm_num [Nat.factorial] at hd)
  have h48 : factorialSearch 38 1560 = false :=
    factorialSearch_false_step (by decide) (by decide) h47 (by intro hd; norm_num [Nat.factorial] at hd)
  have h49 : factorialSearch 38 815915283247897734345611269596115894272000000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h21 (by intro _; norm_num only [Nat.factorial]; exact h48)
  norm_num only [Nat.factorial]
  exact h49

/-- Complete search rejects the target factorial at 41. -/
private theorem search_reject_41 : factorialSearch 39 (41 !) = false := by
  have h0 : factorialSearch 39 33452526613163807108170062053440751665152000000000 = false :=
    factorialSearch_false_of_prime (p := 41) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 42. -/
private theorem search_reject_42 : factorialSearch 40 (42 !) = false := by
  have h0 : factorialSearch 40 1405006117752879898543142606244511569936384000000000 = false :=
    factorialSearch_false_of_prime (p := 41) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 43. -/
private theorem search_reject_43 : factorialSearch 41 (43 !) = false := by
  have h0 : factorialSearch 41 60415263063373835637355132068513997507264512000000000 = false :=
    factorialSearch_false_of_prime (p := 43) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 44. -/
private theorem search_reject_44 : factorialSearch 42 (44 !) = false := by
  have h0 : factorialSearch 42 2658271574788448768043625811014615890319638528000000000 = false :=
    factorialSearch_false_of_prime (p := 43) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 45. -/
private theorem search_reject_45 : factorialSearch 43 (45 !) = false := by
  have h0 : factorialSearch 42 119622220865480194561963161495657715064383733760000000000 = false :=
    factorialSearch_false_of_prime (p := 43) (by decide) (by decide) (by decide) (by norm_num)
  have h1 : factorialSearch 10 1980 = false :=
    factorialSearch_false_of_prime (p := 11) (by decide) (by decide) (by decide) (by norm_num)
  have h2 : factorialSearch 11 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h1 (by intro hd; norm_num [Nat.factorial] at hd)
  have h3 : factorialSearch 12 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h2 (by intro hd; norm_num [Nat.factorial] at hd)
  have h4 : factorialSearch 13 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h3 (by intro hd; norm_num [Nat.factorial] at hd)
  have h5 : factorialSearch 14 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h4 (by intro hd; norm_num [Nat.factorial] at hd)
  have h6 : factorialSearch 15 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h5 (by intro hd; norm_num [Nat.factorial] at hd)
  have h7 : factorialSearch 16 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h6 (by intro hd; norm_num [Nat.factorial] at hd)
  have h8 : factorialSearch 17 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h7 (by intro hd; norm_num [Nat.factorial] at hd)
  have h9 : factorialSearch 18 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h8 (by intro hd; norm_num [Nat.factorial] at hd)
  have h10 : factorialSearch 19 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h9 (by intro hd; norm_num [Nat.factorial] at hd)
  have h11 : factorialSearch 20 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h10 (by intro hd; norm_num [Nat.factorial] at hd)
  have h12 : factorialSearch 21 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h11 (by intro hd; norm_num [Nat.factorial] at hd)
  have h13 : factorialSearch 22 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h12 (by intro hd; norm_num [Nat.factorial] at hd)
  have h14 : factorialSearch 23 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h13 (by intro hd; norm_num [Nat.factorial] at hd)
  have h15 : factorialSearch 24 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h14 (by intro hd; norm_num [Nat.factorial] at hd)
  have h16 : factorialSearch 25 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h15 (by intro hd; norm_num [Nat.factorial] at hd)
  have h17 : factorialSearch 26 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h16 (by intro hd; norm_num [Nat.factorial] at hd)
  have h18 : factorialSearch 27 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h17 (by intro hd; norm_num [Nat.factorial] at hd)
  have h19 : factorialSearch 28 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h18 (by intro hd; norm_num [Nat.factorial] at hd)
  have h20 : factorialSearch 29 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h19 (by intro hd; norm_num [Nat.factorial] at hd)
  have h21 : factorialSearch 30 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h20 (by intro hd; norm_num [Nat.factorial] at hd)
  have h22 : factorialSearch 31 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h21 (by intro hd; norm_num [Nat.factorial] at hd)
  have h23 : factorialSearch 32 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h22 (by intro hd; norm_num [Nat.factorial] at hd)
  have h24 : factorialSearch 33 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h23 (by intro hd; norm_num [Nat.factorial] at hd)
  have h25 : factorialSearch 34 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h24 (by intro hd; norm_num [Nat.factorial] at hd)
  have h26 : factorialSearch 35 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h25 (by intro hd; norm_num [Nat.factorial] at hd)
  have h27 : factorialSearch 36 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h26 (by intro hd; norm_num [Nat.factorial] at hd)
  have h28 : factorialSearch 37 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h27 (by intro hd; norm_num [Nat.factorial] at hd)
  have h29 : factorialSearch 38 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h28 (by intro hd; norm_num [Nat.factorial] at hd)
  have h30 : factorialSearch 39 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h29 (by intro hd; norm_num [Nat.factorial] at hd)
  have h31 : factorialSearch 40 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h30 (by intro hd; norm_num [Nat.factorial] at hd)
  have h32 : factorialSearch 41 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h31 (by intro hd; norm_num [Nat.factorial] at hd)
  have h33 : factorialSearch 42 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h32 (by intro hd; norm_num [Nat.factorial] at hd)
  have h34 : factorialSearch 43 1980 = false :=
    factorialSearch_false_step (by decide) (by decide) h33 (by intro hd; norm_num [Nat.factorial] at hd)
  have h35 : factorialSearch 43 119622220865480194561963161495657715064383733760000000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h0 (by intro _; norm_num only [Nat.factorial]; exact h34)
  norm_num only [Nat.factorial]
  exact h35

/-- Complete search rejects the target factorial at 46. -/
private theorem search_reject_46 : factorialSearch 44 (46 !) = false := by
  have h0 : factorialSearch 42 5502622159812088949850305428800254892961651752960000000000 = false :=
    factorialSearch_false_of_prime (p := 43) (by decide) (by decide) (by decide) (by norm_num)
  have h1 : factorialSearch 22 91080 = false :=
    factorialSearch_false_of_prime (p := 23) (by decide) (by decide) (by decide) (by norm_num)
  have h2 : factorialSearch 23 91080 = false :=
    factorialSearch_false_step (by decide) (by decide) h1 (by intro hd; norm_num [Nat.factorial] at hd)
  have h3 : factorialSearch 24 91080 = false :=
    factorialSearch_false_step (by decide) (by decide) h2 (by intro hd; norm_num [Nat.factorial] at hd)
  have h4 : factorialSearch 25 91080 = false :=
    factorialSearch_false_step (by decide) (by decide) h3 (by intro hd; norm_num [Nat.factorial] at hd)
  have h5 : factorialSearch 26 91080 = false :=
    factorialSearch_false_step (by decide) (by decide) h4 (by intro hd; norm_num [Nat.factorial] at hd)
  have h6 : factorialSearch 27 91080 = false :=
    factorialSearch_false_step (by decide) (by decide) h5 (by intro hd; norm_num [Nat.factorial] at hd)
  have h7 : factorialSearch 28 91080 = false :=
    factorialSearch_false_step (by decide) (by decide) h6 (by intro hd; norm_num [Nat.factorial] at hd)
  have h8 : factorialSearch 29 91080 = false :=
    factorialSearch_false_step (by decide) (by decide) h7 (by intro hd; norm_num [Nat.factorial] at hd)
  have h9 : factorialSearch 30 91080 = false :=
    factorialSearch_false_step (by decide) (by decide) h8 (by intro hd; norm_num [Nat.factorial] at hd)
  have h10 : factorialSearch 31 91080 = false :=
    factorialSearch_false_step (by decide) (by decide) h9 (by intro hd; norm_num [Nat.factorial] at hd)
  have h11 : factorialSearch 32 91080 = false :=
    factorialSearch_false_step (by decide) (by decide) h10 (by intro hd; norm_num [Nat.factorial] at hd)
  have h12 : factorialSearch 33 91080 = false :=
    factorialSearch_false_step (by decide) (by decide) h11 (by intro hd; norm_num [Nat.factorial] at hd)
  have h13 : factorialSearch 34 91080 = false :=
    factorialSearch_false_step (by decide) (by decide) h12 (by intro hd; norm_num [Nat.factorial] at hd)
  have h14 : factorialSearch 35 91080 = false :=
    factorialSearch_false_step (by decide) (by decide) h13 (by intro hd; norm_num [Nat.factorial] at hd)
  have h15 : factorialSearch 36 91080 = false :=
    factorialSearch_false_step (by decide) (by decide) h14 (by intro hd; norm_num [Nat.factorial] at hd)
  have h16 : factorialSearch 37 91080 = false :=
    factorialSearch_false_step (by decide) (by decide) h15 (by intro hd; norm_num [Nat.factorial] at hd)
  have h17 : factorialSearch 38 91080 = false :=
    factorialSearch_false_step (by decide) (by decide) h16 (by intro hd; norm_num [Nat.factorial] at hd)
  have h18 : factorialSearch 39 91080 = false :=
    factorialSearch_false_step (by decide) (by decide) h17 (by intro hd; norm_num [Nat.factorial] at hd)
  have h19 : factorialSearch 40 91080 = false :=
    factorialSearch_false_step (by decide) (by decide) h18 (by intro hd; norm_num [Nat.factorial] at hd)
  have h20 : factorialSearch 41 91080 = false :=
    factorialSearch_false_step (by decide) (by decide) h19 (by intro hd; norm_num [Nat.factorial] at hd)
  have h21 : factorialSearch 42 91080 = false :=
    factorialSearch_false_step (by decide) (by decide) h20 (by intro hd; norm_num [Nat.factorial] at hd)
  have h22 : factorialSearch 43 91080 = false :=
    factorialSearch_false_step (by decide) (by decide) h21 (by intro hd; norm_num [Nat.factorial] at hd)
  have h23 : factorialSearch 43 5502622159812088949850305428800254892961651752960000000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h0 (by intro _; norm_num only [Nat.factorial]; exact h22)
  have h24 : factorialSearch 22 2070 = false :=
    factorialSearch_false_of_prime (p := 23) (by decide) (by decide) (by decide) (by norm_num)
  have h25 : factorialSearch 23 2070 = false :=
    factorialSearch_false_step (by decide) (by decide) h24 (by intro hd; norm_num [Nat.factorial] at hd)
  have h26 : factorialSearch 24 2070 = false :=
    factorialSearch_false_step (by decide) (by decide) h25 (by intro hd; norm_num [Nat.factorial] at hd)
  have h27 : factorialSearch 25 2070 = false :=
    factorialSearch_false_step (by decide) (by decide) h26 (by intro hd; norm_num [Nat.factorial] at hd)
  have h28 : factorialSearch 26 2070 = false :=
    factorialSearch_false_step (by decide) (by decide) h27 (by intro hd; norm_num [Nat.factorial] at hd)
  have h29 : factorialSearch 27 2070 = false :=
    factorialSearch_false_step (by decide) (by decide) h28 (by intro hd; norm_num [Nat.factorial] at hd)
  have h30 : factorialSearch 28 2070 = false :=
    factorialSearch_false_step (by decide) (by decide) h29 (by intro hd; norm_num [Nat.factorial] at hd)
  have h31 : factorialSearch 29 2070 = false :=
    factorialSearch_false_step (by decide) (by decide) h30 (by intro hd; norm_num [Nat.factorial] at hd)
  have h32 : factorialSearch 30 2070 = false :=
    factorialSearch_false_step (by decide) (by decide) h31 (by intro hd; norm_num [Nat.factorial] at hd)
  have h33 : factorialSearch 31 2070 = false :=
    factorialSearch_false_step (by decide) (by decide) h32 (by intro hd; norm_num [Nat.factorial] at hd)
  have h34 : factorialSearch 32 2070 = false :=
    factorialSearch_false_step (by decide) (by decide) h33 (by intro hd; norm_num [Nat.factorial] at hd)
  have h35 : factorialSearch 33 2070 = false :=
    factorialSearch_false_step (by decide) (by decide) h34 (by intro hd; norm_num [Nat.factorial] at hd)
  have h36 : factorialSearch 34 2070 = false :=
    factorialSearch_false_step (by decide) (by decide) h35 (by intro hd; norm_num [Nat.factorial] at hd)
  have h37 : factorialSearch 35 2070 = false :=
    factorialSearch_false_step (by decide) (by decide) h36 (by intro hd; norm_num [Nat.factorial] at hd)
  have h38 : factorialSearch 36 2070 = false :=
    factorialSearch_false_step (by decide) (by decide) h37 (by intro hd; norm_num [Nat.factorial] at hd)
  have h39 : factorialSearch 37 2070 = false :=
    factorialSearch_false_step (by decide) (by decide) h38 (by intro hd; norm_num [Nat.factorial] at hd)
  have h40 : factorialSearch 38 2070 = false :=
    factorialSearch_false_step (by decide) (by decide) h39 (by intro hd; norm_num [Nat.factorial] at hd)
  have h41 : factorialSearch 39 2070 = false :=
    factorialSearch_false_step (by decide) (by decide) h40 (by intro hd; norm_num [Nat.factorial] at hd)
  have h42 : factorialSearch 40 2070 = false :=
    factorialSearch_false_step (by decide) (by decide) h41 (by intro hd; norm_num [Nat.factorial] at hd)
  have h43 : factorialSearch 41 2070 = false :=
    factorialSearch_false_step (by decide) (by decide) h42 (by intro hd; norm_num [Nat.factorial] at hd)
  have h44 : factorialSearch 42 2070 = false :=
    factorialSearch_false_step (by decide) (by decide) h43 (by intro hd; norm_num [Nat.factorial] at hd)
  have h45 : factorialSearch 43 2070 = false :=
    factorialSearch_false_step (by decide) (by decide) h44 (by intro hd; norm_num [Nat.factorial] at hd)
  have h46 : factorialSearch 44 2070 = false :=
    factorialSearch_false_step (by decide) (by decide) h45 (by intro hd; norm_num [Nat.factorial] at hd)
  have h47 : factorialSearch 44 5502622159812088949850305428800254892961651752960000000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h23 (by intro _; norm_num only [Nat.factorial]; exact h46)
  norm_num only [Nat.factorial]
  exact h47

/-- Complete search rejects the target factorial at 47. -/
private theorem search_reject_47 : factorialSearch 45 (47 !) = false := by
  have h0 : factorialSearch 45 258623241511168180642964355153611979969197632389120000000000 = false :=
    factorialSearch_false_of_prime (p := 47) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 48. -/
private theorem search_reject_48 : factorialSearch 46 (48 !) = false := by
  have h0 : factorialSearch 46 12413915592536072670862289047373375038521486354677760000000000 = false :=
    factorialSearch_false_of_prime (p := 47) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 49. -/
private theorem search_reject_49 : factorialSearch 47 (49 !) = false := by
  have h0 : factorialSearch 46 608281864034267560872252163321295376887552831379210240000000000 = false :=
    factorialSearch_false_of_prime (p := 47) (by decide) (by decide) (by decide) (by norm_num)
  have h1 : factorialSearch 6 2352 = false :=
    factorialSearch_false_of_prime (p := 7) (by decide) (by decide) (by decide) (by norm_num)
  have h2 : factorialSearch 7 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h1 (by intro hd; norm_num [Nat.factorial] at hd)
  have h3 : factorialSearch 8 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h2 (by intro hd; norm_num [Nat.factorial] at hd)
  have h4 : factorialSearch 9 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h3 (by intro hd; norm_num [Nat.factorial] at hd)
  have h5 : factorialSearch 10 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h4 (by intro hd; norm_num [Nat.factorial] at hd)
  have h6 : factorialSearch 11 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h5 (by intro hd; norm_num [Nat.factorial] at hd)
  have h7 : factorialSearch 12 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h6 (by intro hd; norm_num [Nat.factorial] at hd)
  have h8 : factorialSearch 13 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h7 (by intro hd; norm_num [Nat.factorial] at hd)
  have h9 : factorialSearch 14 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h8 (by intro hd; norm_num [Nat.factorial] at hd)
  have h10 : factorialSearch 15 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h9 (by intro hd; norm_num [Nat.factorial] at hd)
  have h11 : factorialSearch 16 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h10 (by intro hd; norm_num [Nat.factorial] at hd)
  have h12 : factorialSearch 17 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h11 (by intro hd; norm_num [Nat.factorial] at hd)
  have h13 : factorialSearch 18 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h12 (by intro hd; norm_num [Nat.factorial] at hd)
  have h14 : factorialSearch 19 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h13 (by intro hd; norm_num [Nat.factorial] at hd)
  have h15 : factorialSearch 20 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h14 (by intro hd; norm_num [Nat.factorial] at hd)
  have h16 : factorialSearch 21 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h15 (by intro hd; norm_num [Nat.factorial] at hd)
  have h17 : factorialSearch 22 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h16 (by intro hd; norm_num [Nat.factorial] at hd)
  have h18 : factorialSearch 23 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h17 (by intro hd; norm_num [Nat.factorial] at hd)
  have h19 : factorialSearch 24 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h18 (by intro hd; norm_num [Nat.factorial] at hd)
  have h20 : factorialSearch 25 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h19 (by intro hd; norm_num [Nat.factorial] at hd)
  have h21 : factorialSearch 26 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h20 (by intro hd; norm_num [Nat.factorial] at hd)
  have h22 : factorialSearch 27 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h21 (by intro hd; norm_num [Nat.factorial] at hd)
  have h23 : factorialSearch 28 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h22 (by intro hd; norm_num [Nat.factorial] at hd)
  have h24 : factorialSearch 29 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h23 (by intro hd; norm_num [Nat.factorial] at hd)
  have h25 : factorialSearch 30 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h24 (by intro hd; norm_num [Nat.factorial] at hd)
  have h26 : factorialSearch 31 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h25 (by intro hd; norm_num [Nat.factorial] at hd)
  have h27 : factorialSearch 32 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h26 (by intro hd; norm_num [Nat.factorial] at hd)
  have h28 : factorialSearch 33 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h27 (by intro hd; norm_num [Nat.factorial] at hd)
  have h29 : factorialSearch 34 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h28 (by intro hd; norm_num [Nat.factorial] at hd)
  have h30 : factorialSearch 35 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h29 (by intro hd; norm_num [Nat.factorial] at hd)
  have h31 : factorialSearch 36 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h30 (by intro hd; norm_num [Nat.factorial] at hd)
  have h32 : factorialSearch 37 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h31 (by intro hd; norm_num [Nat.factorial] at hd)
  have h33 : factorialSearch 38 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h32 (by intro hd; norm_num [Nat.factorial] at hd)
  have h34 : factorialSearch 39 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h33 (by intro hd; norm_num [Nat.factorial] at hd)
  have h35 : factorialSearch 40 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h34 (by intro hd; norm_num [Nat.factorial] at hd)
  have h36 : factorialSearch 41 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h35 (by intro hd; norm_num [Nat.factorial] at hd)
  have h37 : factorialSearch 42 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h36 (by intro hd; norm_num [Nat.factorial] at hd)
  have h38 : factorialSearch 43 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h37 (by intro hd; norm_num [Nat.factorial] at hd)
  have h39 : factorialSearch 44 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h38 (by intro hd; norm_num [Nat.factorial] at hd)
  have h40 : factorialSearch 45 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h39 (by intro hd; norm_num [Nat.factorial] at hd)
  have h41 : factorialSearch 46 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h40 (by intro hd; norm_num [Nat.factorial] at hd)
  have h42 : factorialSearch 47 2352 = false :=
    factorialSearch_false_step (by decide) (by decide) h41 (by intro hd; norm_num [Nat.factorial] at hd)
  have h43 : factorialSearch 47 608281864034267560872252163321295376887552831379210240000000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h0 (by intro _; norm_num only [Nat.factorial]; exact h42)
  norm_num only [Nat.factorial]
  exact h43

/-- Complete search rejects the target factorial at 50. -/
private theorem search_reject_50 : factorialSearch 48 (50 !) = false := by
  have h0 : factorialSearch 46 30414093201713378043612608166064768844377641568960512000000000000 = false :=
    factorialSearch_false_of_prime (p := 47) (by decide) (by decide) (by decide) (by norm_num)
  have h1 : factorialSearch 6 117600 = false :=
    factorialSearch_false_of_prime (p := 7) (by decide) (by decide) (by decide) (by norm_num)
  have h2 : factorialSearch 7 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h1 (by intro hd; norm_num [Nat.factorial] at hd)
  have h3 : factorialSearch 8 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h2 (by intro hd; norm_num [Nat.factorial] at hd)
  have h4 : factorialSearch 9 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h3 (by intro hd; norm_num [Nat.factorial] at hd)
  have h5 : factorialSearch 10 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h4 (by intro hd; norm_num [Nat.factorial] at hd)
  have h6 : factorialSearch 11 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h5 (by intro hd; norm_num [Nat.factorial] at hd)
  have h7 : factorialSearch 12 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h6 (by intro hd; norm_num [Nat.factorial] at hd)
  have h8 : factorialSearch 13 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h7 (by intro hd; norm_num [Nat.factorial] at hd)
  have h9 : factorialSearch 14 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h8 (by intro hd; norm_num [Nat.factorial] at hd)
  have h10 : factorialSearch 15 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h9 (by intro hd; norm_num [Nat.factorial] at hd)
  have h11 : factorialSearch 16 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h10 (by intro hd; norm_num [Nat.factorial] at hd)
  have h12 : factorialSearch 17 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h11 (by intro hd; norm_num [Nat.factorial] at hd)
  have h13 : factorialSearch 18 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h12 (by intro hd; norm_num [Nat.factorial] at hd)
  have h14 : factorialSearch 19 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h13 (by intro hd; norm_num [Nat.factorial] at hd)
  have h15 : factorialSearch 20 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h14 (by intro hd; norm_num [Nat.factorial] at hd)
  have h16 : factorialSearch 21 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h15 (by intro hd; norm_num [Nat.factorial] at hd)
  have h17 : factorialSearch 22 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h16 (by intro hd; norm_num [Nat.factorial] at hd)
  have h18 : factorialSearch 23 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h17 (by intro hd; norm_num [Nat.factorial] at hd)
  have h19 : factorialSearch 24 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h18 (by intro hd; norm_num [Nat.factorial] at hd)
  have h20 : factorialSearch 25 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h19 (by intro hd; norm_num [Nat.factorial] at hd)
  have h21 : factorialSearch 26 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h20 (by intro hd; norm_num [Nat.factorial] at hd)
  have h22 : factorialSearch 27 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h21 (by intro hd; norm_num [Nat.factorial] at hd)
  have h23 : factorialSearch 28 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h22 (by intro hd; norm_num [Nat.factorial] at hd)
  have h24 : factorialSearch 29 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h23 (by intro hd; norm_num [Nat.factorial] at hd)
  have h25 : factorialSearch 30 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h24 (by intro hd; norm_num [Nat.factorial] at hd)
  have h26 : factorialSearch 31 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h25 (by intro hd; norm_num [Nat.factorial] at hd)
  have h27 : factorialSearch 32 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h26 (by intro hd; norm_num [Nat.factorial] at hd)
  have h28 : factorialSearch 33 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h27 (by intro hd; norm_num [Nat.factorial] at hd)
  have h29 : factorialSearch 34 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h28 (by intro hd; norm_num [Nat.factorial] at hd)
  have h30 : factorialSearch 35 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h29 (by intro hd; norm_num [Nat.factorial] at hd)
  have h31 : factorialSearch 36 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h30 (by intro hd; norm_num [Nat.factorial] at hd)
  have h32 : factorialSearch 37 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h31 (by intro hd; norm_num [Nat.factorial] at hd)
  have h33 : factorialSearch 38 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h32 (by intro hd; norm_num [Nat.factorial] at hd)
  have h34 : factorialSearch 39 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h33 (by intro hd; norm_num [Nat.factorial] at hd)
  have h35 : factorialSearch 40 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h34 (by intro hd; norm_num [Nat.factorial] at hd)
  have h36 : factorialSearch 41 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h35 (by intro hd; norm_num [Nat.factorial] at hd)
  have h37 : factorialSearch 42 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h36 (by intro hd; norm_num [Nat.factorial] at hd)
  have h38 : factorialSearch 43 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h37 (by intro hd; norm_num [Nat.factorial] at hd)
  have h39 : factorialSearch 44 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h38 (by intro hd; norm_num [Nat.factorial] at hd)
  have h40 : factorialSearch 45 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h39 (by intro hd; norm_num [Nat.factorial] at hd)
  have h41 : factorialSearch 46 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h40 (by intro hd; norm_num [Nat.factorial] at hd)
  have h42 : factorialSearch 47 117600 = false :=
    factorialSearch_false_step (by decide) (by decide) h41 (by intro hd; norm_num [Nat.factorial] at hd)
  have h43 : factorialSearch 47 30414093201713378043612608166064768844377641568960512000000000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h0 (by intro _; norm_num only [Nat.factorial]; exact h42)
  have h44 : factorialSearch 6 2450 = false :=
    factorialSearch_false_of_prime (p := 7) (by decide) (by decide) (by decide) (by norm_num)
  have h45 : factorialSearch 7 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h44 (by intro hd; norm_num [Nat.factorial] at hd)
  have h46 : factorialSearch 8 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h45 (by intro hd; norm_num [Nat.factorial] at hd)
  have h47 : factorialSearch 9 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h46 (by intro hd; norm_num [Nat.factorial] at hd)
  have h48 : factorialSearch 10 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h47 (by intro hd; norm_num [Nat.factorial] at hd)
  have h49 : factorialSearch 11 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h48 (by intro hd; norm_num [Nat.factorial] at hd)
  have h50 : factorialSearch 12 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h49 (by intro hd; norm_num [Nat.factorial] at hd)
  have h51 : factorialSearch 13 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h50 (by intro hd; norm_num [Nat.factorial] at hd)
  have h52 : factorialSearch 14 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h51 (by intro hd; norm_num [Nat.factorial] at hd)
  have h53 : factorialSearch 15 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h52 (by intro hd; norm_num [Nat.factorial] at hd)
  have h54 : factorialSearch 16 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h53 (by intro hd; norm_num [Nat.factorial] at hd)
  have h55 : factorialSearch 17 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h54 (by intro hd; norm_num [Nat.factorial] at hd)
  have h56 : factorialSearch 18 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h55 (by intro hd; norm_num [Nat.factorial] at hd)
  have h57 : factorialSearch 19 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h56 (by intro hd; norm_num [Nat.factorial] at hd)
  have h58 : factorialSearch 20 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h57 (by intro hd; norm_num [Nat.factorial] at hd)
  have h59 : factorialSearch 21 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h58 (by intro hd; norm_num [Nat.factorial] at hd)
  have h60 : factorialSearch 22 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h59 (by intro hd; norm_num [Nat.factorial] at hd)
  have h61 : factorialSearch 23 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h60 (by intro hd; norm_num [Nat.factorial] at hd)
  have h62 : factorialSearch 24 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h61 (by intro hd; norm_num [Nat.factorial] at hd)
  have h63 : factorialSearch 25 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h62 (by intro hd; norm_num [Nat.factorial] at hd)
  have h64 : factorialSearch 26 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h63 (by intro hd; norm_num [Nat.factorial] at hd)
  have h65 : factorialSearch 27 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h64 (by intro hd; norm_num [Nat.factorial] at hd)
  have h66 : factorialSearch 28 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h65 (by intro hd; norm_num [Nat.factorial] at hd)
  have h67 : factorialSearch 29 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h66 (by intro hd; norm_num [Nat.factorial] at hd)
  have h68 : factorialSearch 30 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h67 (by intro hd; norm_num [Nat.factorial] at hd)
  have h69 : factorialSearch 31 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h68 (by intro hd; norm_num [Nat.factorial] at hd)
  have h70 : factorialSearch 32 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h69 (by intro hd; norm_num [Nat.factorial] at hd)
  have h71 : factorialSearch 33 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h70 (by intro hd; norm_num [Nat.factorial] at hd)
  have h72 : factorialSearch 34 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h71 (by intro hd; norm_num [Nat.factorial] at hd)
  have h73 : factorialSearch 35 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h72 (by intro hd; norm_num [Nat.factorial] at hd)
  have h74 : factorialSearch 36 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h73 (by intro hd; norm_num [Nat.factorial] at hd)
  have h75 : factorialSearch 37 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h74 (by intro hd; norm_num [Nat.factorial] at hd)
  have h76 : factorialSearch 38 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h75 (by intro hd; norm_num [Nat.factorial] at hd)
  have h77 : factorialSearch 39 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h76 (by intro hd; norm_num [Nat.factorial] at hd)
  have h78 : factorialSearch 40 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h77 (by intro hd; norm_num [Nat.factorial] at hd)
  have h79 : factorialSearch 41 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h78 (by intro hd; norm_num [Nat.factorial] at hd)
  have h80 : factorialSearch 42 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h79 (by intro hd; norm_num [Nat.factorial] at hd)
  have h81 : factorialSearch 43 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h80 (by intro hd; norm_num [Nat.factorial] at hd)
  have h82 : factorialSearch 44 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h81 (by intro hd; norm_num [Nat.factorial] at hd)
  have h83 : factorialSearch 45 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h82 (by intro hd; norm_num [Nat.factorial] at hd)
  have h84 : factorialSearch 46 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h83 (by intro hd; norm_num [Nat.factorial] at hd)
  have h85 : factorialSearch 47 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h84 (by intro hd; norm_num [Nat.factorial] at hd)
  have h86 : factorialSearch 48 2450 = false :=
    factorialSearch_false_step (by decide) (by decide) h85 (by intro hd; norm_num [Nat.factorial] at hd)
  have h87 : factorialSearch 48 30414093201713378043612608166064768844377641568960512000000000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h43 (by intro _; norm_num only [Nat.factorial]; exact h86)
  norm_num only [Nat.factorial]
  exact h87

/-- Complete search rejects the target factorial at 51. -/
private theorem search_reject_51 : factorialSearch 49 (51 !) = false := by
  have h0 : factorialSearch 46 1551118753287382280224243016469303211063259720016986112000000000000 = false :=
    factorialSearch_false_of_prime (p := 47) (by decide) (by decide) (by decide) (by norm_num)
  have h1 : factorialSearch 16 5997600 = false :=
    factorialSearch_false_of_prime (p := 17) (by decide) (by decide) (by decide) (by norm_num)
  have h2 : factorialSearch 17 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h1 (by intro hd; norm_num [Nat.factorial] at hd)
  have h3 : factorialSearch 18 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h2 (by intro hd; norm_num [Nat.factorial] at hd)
  have h4 : factorialSearch 19 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h3 (by intro hd; norm_num [Nat.factorial] at hd)
  have h5 : factorialSearch 20 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h4 (by intro hd; norm_num [Nat.factorial] at hd)
  have h6 : factorialSearch 21 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h5 (by intro hd; norm_num [Nat.factorial] at hd)
  have h7 : factorialSearch 22 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h6 (by intro hd; norm_num [Nat.factorial] at hd)
  have h8 : factorialSearch 23 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h7 (by intro hd; norm_num [Nat.factorial] at hd)
  have h9 : factorialSearch 24 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h8 (by intro hd; norm_num [Nat.factorial] at hd)
  have h10 : factorialSearch 25 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h9 (by intro hd; norm_num [Nat.factorial] at hd)
  have h11 : factorialSearch 26 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h10 (by intro hd; norm_num [Nat.factorial] at hd)
  have h12 : factorialSearch 27 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h11 (by intro hd; norm_num [Nat.factorial] at hd)
  have h13 : factorialSearch 28 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h12 (by intro hd; norm_num [Nat.factorial] at hd)
  have h14 : factorialSearch 29 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h13 (by intro hd; norm_num [Nat.factorial] at hd)
  have h15 : factorialSearch 30 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h14 (by intro hd; norm_num [Nat.factorial] at hd)
  have h16 : factorialSearch 31 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h15 (by intro hd; norm_num [Nat.factorial] at hd)
  have h17 : factorialSearch 32 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h16 (by intro hd; norm_num [Nat.factorial] at hd)
  have h18 : factorialSearch 33 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h17 (by intro hd; norm_num [Nat.factorial] at hd)
  have h19 : factorialSearch 34 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h18 (by intro hd; norm_num [Nat.factorial] at hd)
  have h20 : factorialSearch 35 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h19 (by intro hd; norm_num [Nat.factorial] at hd)
  have h21 : factorialSearch 36 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h20 (by intro hd; norm_num [Nat.factorial] at hd)
  have h22 : factorialSearch 37 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h21 (by intro hd; norm_num [Nat.factorial] at hd)
  have h23 : factorialSearch 38 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h22 (by intro hd; norm_num [Nat.factorial] at hd)
  have h24 : factorialSearch 39 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h23 (by intro hd; norm_num [Nat.factorial] at hd)
  have h25 : factorialSearch 40 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h24 (by intro hd; norm_num [Nat.factorial] at hd)
  have h26 : factorialSearch 41 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h25 (by intro hd; norm_num [Nat.factorial] at hd)
  have h27 : factorialSearch 42 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h26 (by intro hd; norm_num [Nat.factorial] at hd)
  have h28 : factorialSearch 43 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h27 (by intro hd; norm_num [Nat.factorial] at hd)
  have h29 : factorialSearch 44 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h28 (by intro hd; norm_num [Nat.factorial] at hd)
  have h30 : factorialSearch 45 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h29 (by intro hd; norm_num [Nat.factorial] at hd)
  have h31 : factorialSearch 46 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h30 (by intro hd; norm_num [Nat.factorial] at hd)
  have h32 : factorialSearch 47 5997600 = false :=
    factorialSearch_false_step (by decide) (by decide) h31 (by intro hd; norm_num [Nat.factorial] at hd)
  have h33 : factorialSearch 47 1551118753287382280224243016469303211063259720016986112000000000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h0 (by intro _; norm_num only [Nat.factorial]; exact h32)
  have h34 : factorialSearch 16 124950 = false :=
    factorialSearch_false_of_prime (p := 17) (by decide) (by decide) (by decide) (by norm_num)
  have h35 : factorialSearch 17 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h34 (by intro hd; norm_num [Nat.factorial] at hd)
  have h36 : factorialSearch 18 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h35 (by intro hd; norm_num [Nat.factorial] at hd)
  have h37 : factorialSearch 19 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h36 (by intro hd; norm_num [Nat.factorial] at hd)
  have h38 : factorialSearch 20 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h37 (by intro hd; norm_num [Nat.factorial] at hd)
  have h39 : factorialSearch 21 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h38 (by intro hd; norm_num [Nat.factorial] at hd)
  have h40 : factorialSearch 22 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h39 (by intro hd; norm_num [Nat.factorial] at hd)
  have h41 : factorialSearch 23 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h40 (by intro hd; norm_num [Nat.factorial] at hd)
  have h42 : factorialSearch 24 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h41 (by intro hd; norm_num [Nat.factorial] at hd)
  have h43 : factorialSearch 25 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h42 (by intro hd; norm_num [Nat.factorial] at hd)
  have h44 : factorialSearch 26 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h43 (by intro hd; norm_num [Nat.factorial] at hd)
  have h45 : factorialSearch 27 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h44 (by intro hd; norm_num [Nat.factorial] at hd)
  have h46 : factorialSearch 28 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h45 (by intro hd; norm_num [Nat.factorial] at hd)
  have h47 : factorialSearch 29 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h46 (by intro hd; norm_num [Nat.factorial] at hd)
  have h48 : factorialSearch 30 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h47 (by intro hd; norm_num [Nat.factorial] at hd)
  have h49 : factorialSearch 31 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h48 (by intro hd; norm_num [Nat.factorial] at hd)
  have h50 : factorialSearch 32 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h49 (by intro hd; norm_num [Nat.factorial] at hd)
  have h51 : factorialSearch 33 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h50 (by intro hd; norm_num [Nat.factorial] at hd)
  have h52 : factorialSearch 34 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h51 (by intro hd; norm_num [Nat.factorial] at hd)
  have h53 : factorialSearch 35 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h52 (by intro hd; norm_num [Nat.factorial] at hd)
  have h54 : factorialSearch 36 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h53 (by intro hd; norm_num [Nat.factorial] at hd)
  have h55 : factorialSearch 37 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h54 (by intro hd; norm_num [Nat.factorial] at hd)
  have h56 : factorialSearch 38 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h55 (by intro hd; norm_num [Nat.factorial] at hd)
  have h57 : factorialSearch 39 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h56 (by intro hd; norm_num [Nat.factorial] at hd)
  have h58 : factorialSearch 40 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h57 (by intro hd; norm_num [Nat.factorial] at hd)
  have h59 : factorialSearch 41 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h58 (by intro hd; norm_num [Nat.factorial] at hd)
  have h60 : factorialSearch 42 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h59 (by intro hd; norm_num [Nat.factorial] at hd)
  have h61 : factorialSearch 43 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h60 (by intro hd; norm_num [Nat.factorial] at hd)
  have h62 : factorialSearch 44 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h61 (by intro hd; norm_num [Nat.factorial] at hd)
  have h63 : factorialSearch 45 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h62 (by intro hd; norm_num [Nat.factorial] at hd)
  have h64 : factorialSearch 46 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h63 (by intro hd; norm_num [Nat.factorial] at hd)
  have h65 : factorialSearch 47 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h64 (by intro hd; norm_num [Nat.factorial] at hd)
  have h66 : factorialSearch 48 124950 = false :=
    factorialSearch_false_step (by decide) (by decide) h65 (by intro hd; norm_num [Nat.factorial] at hd)
  have h67 : factorialSearch 48 1551118753287382280224243016469303211063259720016986112000000000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h33 (by intro _; norm_num only [Nat.factorial]; exact h66)
  have h68 : factorialSearch 16 2550 = false :=
    factorialSearch_false_of_prime (p := 17) (by decide) (by decide) (by decide) (by norm_num)
  have h69 : factorialSearch 17 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h68 (by intro hd; norm_num [Nat.factorial] at hd)
  have h70 : factorialSearch 18 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h69 (by intro hd; norm_num [Nat.factorial] at hd)
  have h71 : factorialSearch 19 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h70 (by intro hd; norm_num [Nat.factorial] at hd)
  have h72 : factorialSearch 20 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h71 (by intro hd; norm_num [Nat.factorial] at hd)
  have h73 : factorialSearch 21 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h72 (by intro hd; norm_num [Nat.factorial] at hd)
  have h74 : factorialSearch 22 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h73 (by intro hd; norm_num [Nat.factorial] at hd)
  have h75 : factorialSearch 23 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h74 (by intro hd; norm_num [Nat.factorial] at hd)
  have h76 : factorialSearch 24 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h75 (by intro hd; norm_num [Nat.factorial] at hd)
  have h77 : factorialSearch 25 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h76 (by intro hd; norm_num [Nat.factorial] at hd)
  have h78 : factorialSearch 26 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h77 (by intro hd; norm_num [Nat.factorial] at hd)
  have h79 : factorialSearch 27 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h78 (by intro hd; norm_num [Nat.factorial] at hd)
  have h80 : factorialSearch 28 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h79 (by intro hd; norm_num [Nat.factorial] at hd)
  have h81 : factorialSearch 29 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h80 (by intro hd; norm_num [Nat.factorial] at hd)
  have h82 : factorialSearch 30 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h81 (by intro hd; norm_num [Nat.factorial] at hd)
  have h83 : factorialSearch 31 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h82 (by intro hd; norm_num [Nat.factorial] at hd)
  have h84 : factorialSearch 32 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h83 (by intro hd; norm_num [Nat.factorial] at hd)
  have h85 : factorialSearch 33 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h84 (by intro hd; norm_num [Nat.factorial] at hd)
  have h86 : factorialSearch 34 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h85 (by intro hd; norm_num [Nat.factorial] at hd)
  have h87 : factorialSearch 35 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h86 (by intro hd; norm_num [Nat.factorial] at hd)
  have h88 : factorialSearch 36 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h87 (by intro hd; norm_num [Nat.factorial] at hd)
  have h89 : factorialSearch 37 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h88 (by intro hd; norm_num [Nat.factorial] at hd)
  have h90 : factorialSearch 38 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h89 (by intro hd; norm_num [Nat.factorial] at hd)
  have h91 : factorialSearch 39 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h90 (by intro hd; norm_num [Nat.factorial] at hd)
  have h92 : factorialSearch 40 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h91 (by intro hd; norm_num [Nat.factorial] at hd)
  have h93 : factorialSearch 41 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h92 (by intro hd; norm_num [Nat.factorial] at hd)
  have h94 : factorialSearch 42 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h93 (by intro hd; norm_num [Nat.factorial] at hd)
  have h95 : factorialSearch 43 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h94 (by intro hd; norm_num [Nat.factorial] at hd)
  have h96 : factorialSearch 44 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h95 (by intro hd; norm_num [Nat.factorial] at hd)
  have h97 : factorialSearch 45 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h96 (by intro hd; norm_num [Nat.factorial] at hd)
  have h98 : factorialSearch 46 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h97 (by intro hd; norm_num [Nat.factorial] at hd)
  have h99 : factorialSearch 47 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h98 (by intro hd; norm_num [Nat.factorial] at hd)
  have h100 : factorialSearch 48 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h99 (by intro hd; norm_num [Nat.factorial] at hd)
  have h101 : factorialSearch 49 2550 = false :=
    factorialSearch_false_step (by decide) (by decide) h100 (by intro hd; norm_num [Nat.factorial] at hd)
  have h102 : factorialSearch 49 1551118753287382280224243016469303211063259720016986112000000000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h67 (by intro _; norm_num only [Nat.factorial]; exact h101)
  norm_num only [Nat.factorial]
  exact h102

/-- Complete search rejects the target factorial at 52. -/
private theorem search_reject_52 : factorialSearch 50 (52 !) = false := by
  have h0 : factorialSearch 46 80658175170943878571660636856403766975289505440883277824000000000000 = false :=
    factorialSearch_false_of_prime (p := 47) (by decide) (by decide) (by decide) (by norm_num)
  have h1 : factorialSearch 16 311875200 = false :=
    factorialSearch_false_of_prime (p := 17) (by decide) (by decide) (by decide) (by norm_num)
  have h2 : factorialSearch 17 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h1 (by intro hd; norm_num [Nat.factorial] at hd)
  have h3 : factorialSearch 18 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h2 (by intro hd; norm_num [Nat.factorial] at hd)
  have h4 : factorialSearch 19 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h3 (by intro hd; norm_num [Nat.factorial] at hd)
  have h5 : factorialSearch 20 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h4 (by intro hd; norm_num [Nat.factorial] at hd)
  have h6 : factorialSearch 21 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h5 (by intro hd; norm_num [Nat.factorial] at hd)
  have h7 : factorialSearch 22 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h6 (by intro hd; norm_num [Nat.factorial] at hd)
  have h8 : factorialSearch 23 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h7 (by intro hd; norm_num [Nat.factorial] at hd)
  have h9 : factorialSearch 24 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h8 (by intro hd; norm_num [Nat.factorial] at hd)
  have h10 : factorialSearch 25 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h9 (by intro hd; norm_num [Nat.factorial] at hd)
  have h11 : factorialSearch 26 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h10 (by intro hd; norm_num [Nat.factorial] at hd)
  have h12 : factorialSearch 27 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h11 (by intro hd; norm_num [Nat.factorial] at hd)
  have h13 : factorialSearch 28 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h12 (by intro hd; norm_num [Nat.factorial] at hd)
  have h14 : factorialSearch 29 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h13 (by intro hd; norm_num [Nat.factorial] at hd)
  have h15 : factorialSearch 30 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h14 (by intro hd; norm_num [Nat.factorial] at hd)
  have h16 : factorialSearch 31 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h15 (by intro hd; norm_num [Nat.factorial] at hd)
  have h17 : factorialSearch 32 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h16 (by intro hd; norm_num [Nat.factorial] at hd)
  have h18 : factorialSearch 33 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h17 (by intro hd; norm_num [Nat.factorial] at hd)
  have h19 : factorialSearch 34 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h18 (by intro hd; norm_num [Nat.factorial] at hd)
  have h20 : factorialSearch 35 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h19 (by intro hd; norm_num [Nat.factorial] at hd)
  have h21 : factorialSearch 36 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h20 (by intro hd; norm_num [Nat.factorial] at hd)
  have h22 : factorialSearch 37 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h21 (by intro hd; norm_num [Nat.factorial] at hd)
  have h23 : factorialSearch 38 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h22 (by intro hd; norm_num [Nat.factorial] at hd)
  have h24 : factorialSearch 39 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h23 (by intro hd; norm_num [Nat.factorial] at hd)
  have h25 : factorialSearch 40 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h24 (by intro hd; norm_num [Nat.factorial] at hd)
  have h26 : factorialSearch 41 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h25 (by intro hd; norm_num [Nat.factorial] at hd)
  have h27 : factorialSearch 42 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h26 (by intro hd; norm_num [Nat.factorial] at hd)
  have h28 : factorialSearch 43 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h27 (by intro hd; norm_num [Nat.factorial] at hd)
  have h29 : factorialSearch 44 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h28 (by intro hd; norm_num [Nat.factorial] at hd)
  have h30 : factorialSearch 45 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h29 (by intro hd; norm_num [Nat.factorial] at hd)
  have h31 : factorialSearch 46 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h30 (by intro hd; norm_num [Nat.factorial] at hd)
  have h32 : factorialSearch 47 311875200 = false :=
    factorialSearch_false_step (by decide) (by decide) h31 (by intro hd; norm_num [Nat.factorial] at hd)
  have h33 : factorialSearch 47 80658175170943878571660636856403766975289505440883277824000000000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h0 (by intro _; norm_num only [Nat.factorial]; exact h32)
  have h34 : factorialSearch 16 6497400 = false :=
    factorialSearch_false_of_prime (p := 17) (by decide) (by decide) (by decide) (by norm_num)
  have h35 : factorialSearch 17 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h34 (by intro hd; norm_num [Nat.factorial] at hd)
  have h36 : factorialSearch 18 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h35 (by intro hd; norm_num [Nat.factorial] at hd)
  have h37 : factorialSearch 19 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h36 (by intro hd; norm_num [Nat.factorial] at hd)
  have h38 : factorialSearch 20 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h37 (by intro hd; norm_num [Nat.factorial] at hd)
  have h39 : factorialSearch 21 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h38 (by intro hd; norm_num [Nat.factorial] at hd)
  have h40 : factorialSearch 22 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h39 (by intro hd; norm_num [Nat.factorial] at hd)
  have h41 : factorialSearch 23 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h40 (by intro hd; norm_num [Nat.factorial] at hd)
  have h42 : factorialSearch 24 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h41 (by intro hd; norm_num [Nat.factorial] at hd)
  have h43 : factorialSearch 25 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h42 (by intro hd; norm_num [Nat.factorial] at hd)
  have h44 : factorialSearch 26 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h43 (by intro hd; norm_num [Nat.factorial] at hd)
  have h45 : factorialSearch 27 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h44 (by intro hd; norm_num [Nat.factorial] at hd)
  have h46 : factorialSearch 28 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h45 (by intro hd; norm_num [Nat.factorial] at hd)
  have h47 : factorialSearch 29 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h46 (by intro hd; norm_num [Nat.factorial] at hd)
  have h48 : factorialSearch 30 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h47 (by intro hd; norm_num [Nat.factorial] at hd)
  have h49 : factorialSearch 31 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h48 (by intro hd; norm_num [Nat.factorial] at hd)
  have h50 : factorialSearch 32 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h49 (by intro hd; norm_num [Nat.factorial] at hd)
  have h51 : factorialSearch 33 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h50 (by intro hd; norm_num [Nat.factorial] at hd)
  have h52 : factorialSearch 34 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h51 (by intro hd; norm_num [Nat.factorial] at hd)
  have h53 : factorialSearch 35 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h52 (by intro hd; norm_num [Nat.factorial] at hd)
  have h54 : factorialSearch 36 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h53 (by intro hd; norm_num [Nat.factorial] at hd)
  have h55 : factorialSearch 37 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h54 (by intro hd; norm_num [Nat.factorial] at hd)
  have h56 : factorialSearch 38 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h55 (by intro hd; norm_num [Nat.factorial] at hd)
  have h57 : factorialSearch 39 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h56 (by intro hd; norm_num [Nat.factorial] at hd)
  have h58 : factorialSearch 40 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h57 (by intro hd; norm_num [Nat.factorial] at hd)
  have h59 : factorialSearch 41 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h58 (by intro hd; norm_num [Nat.factorial] at hd)
  have h60 : factorialSearch 42 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h59 (by intro hd; norm_num [Nat.factorial] at hd)
  have h61 : factorialSearch 43 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h60 (by intro hd; norm_num [Nat.factorial] at hd)
  have h62 : factorialSearch 44 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h61 (by intro hd; norm_num [Nat.factorial] at hd)
  have h63 : factorialSearch 45 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h62 (by intro hd; norm_num [Nat.factorial] at hd)
  have h64 : factorialSearch 46 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h63 (by intro hd; norm_num [Nat.factorial] at hd)
  have h65 : factorialSearch 47 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h64 (by intro hd; norm_num [Nat.factorial] at hd)
  have h66 : factorialSearch 48 6497400 = false :=
    factorialSearch_false_step (by decide) (by decide) h65 (by intro hd; norm_num [Nat.factorial] at hd)
  have h67 : factorialSearch 48 80658175170943878571660636856403766975289505440883277824000000000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h33 (by intro _; norm_num only [Nat.factorial]; exact h66)
  have h68 : factorialSearch 16 132600 = false :=
    factorialSearch_false_of_prime (p := 17) (by decide) (by decide) (by decide) (by norm_num)
  have h69 : factorialSearch 17 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h68 (by intro hd; norm_num [Nat.factorial] at hd)
  have h70 : factorialSearch 18 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h69 (by intro hd; norm_num [Nat.factorial] at hd)
  have h71 : factorialSearch 19 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h70 (by intro hd; norm_num [Nat.factorial] at hd)
  have h72 : factorialSearch 20 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h71 (by intro hd; norm_num [Nat.factorial] at hd)
  have h73 : factorialSearch 21 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h72 (by intro hd; norm_num [Nat.factorial] at hd)
  have h74 : factorialSearch 22 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h73 (by intro hd; norm_num [Nat.factorial] at hd)
  have h75 : factorialSearch 23 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h74 (by intro hd; norm_num [Nat.factorial] at hd)
  have h76 : factorialSearch 24 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h75 (by intro hd; norm_num [Nat.factorial] at hd)
  have h77 : factorialSearch 25 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h76 (by intro hd; norm_num [Nat.factorial] at hd)
  have h78 : factorialSearch 26 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h77 (by intro hd; norm_num [Nat.factorial] at hd)
  have h79 : factorialSearch 27 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h78 (by intro hd; norm_num [Nat.factorial] at hd)
  have h80 : factorialSearch 28 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h79 (by intro hd; norm_num [Nat.factorial] at hd)
  have h81 : factorialSearch 29 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h80 (by intro hd; norm_num [Nat.factorial] at hd)
  have h82 : factorialSearch 30 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h81 (by intro hd; norm_num [Nat.factorial] at hd)
  have h83 : factorialSearch 31 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h82 (by intro hd; norm_num [Nat.factorial] at hd)
  have h84 : factorialSearch 32 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h83 (by intro hd; norm_num [Nat.factorial] at hd)
  have h85 : factorialSearch 33 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h84 (by intro hd; norm_num [Nat.factorial] at hd)
  have h86 : factorialSearch 34 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h85 (by intro hd; norm_num [Nat.factorial] at hd)
  have h87 : factorialSearch 35 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h86 (by intro hd; norm_num [Nat.factorial] at hd)
  have h88 : factorialSearch 36 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h87 (by intro hd; norm_num [Nat.factorial] at hd)
  have h89 : factorialSearch 37 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h88 (by intro hd; norm_num [Nat.factorial] at hd)
  have h90 : factorialSearch 38 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h89 (by intro hd; norm_num [Nat.factorial] at hd)
  have h91 : factorialSearch 39 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h90 (by intro hd; norm_num [Nat.factorial] at hd)
  have h92 : factorialSearch 40 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h91 (by intro hd; norm_num [Nat.factorial] at hd)
  have h93 : factorialSearch 41 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h92 (by intro hd; norm_num [Nat.factorial] at hd)
  have h94 : factorialSearch 42 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h93 (by intro hd; norm_num [Nat.factorial] at hd)
  have h95 : factorialSearch 43 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h94 (by intro hd; norm_num [Nat.factorial] at hd)
  have h96 : factorialSearch 44 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h95 (by intro hd; norm_num [Nat.factorial] at hd)
  have h97 : factorialSearch 45 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h96 (by intro hd; norm_num [Nat.factorial] at hd)
  have h98 : factorialSearch 46 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h97 (by intro hd; norm_num [Nat.factorial] at hd)
  have h99 : factorialSearch 47 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h98 (by intro hd; norm_num [Nat.factorial] at hd)
  have h100 : factorialSearch 48 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h99 (by intro hd; norm_num [Nat.factorial] at hd)
  have h101 : factorialSearch 49 132600 = false :=
    factorialSearch_false_step (by decide) (by decide) h100 (by intro hd; norm_num [Nat.factorial] at hd)
  have h102 : factorialSearch 49 80658175170943878571660636856403766975289505440883277824000000000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h67 (by intro _; norm_num only [Nat.factorial]; exact h101)
  have h103 : factorialSearch 16 2652 = false :=
    factorialSearch_false_of_prime (p := 17) (by decide) (by decide) (by decide) (by norm_num)
  have h104 : factorialSearch 17 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h103 (by intro hd; norm_num [Nat.factorial] at hd)
  have h105 : factorialSearch 18 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h104 (by intro hd; norm_num [Nat.factorial] at hd)
  have h106 : factorialSearch 19 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h105 (by intro hd; norm_num [Nat.factorial] at hd)
  have h107 : factorialSearch 20 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h106 (by intro hd; norm_num [Nat.factorial] at hd)
  have h108 : factorialSearch 21 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h107 (by intro hd; norm_num [Nat.factorial] at hd)
  have h109 : factorialSearch 22 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h108 (by intro hd; norm_num [Nat.factorial] at hd)
  have h110 : factorialSearch 23 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h109 (by intro hd; norm_num [Nat.factorial] at hd)
  have h111 : factorialSearch 24 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h110 (by intro hd; norm_num [Nat.factorial] at hd)
  have h112 : factorialSearch 25 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h111 (by intro hd; norm_num [Nat.factorial] at hd)
  have h113 : factorialSearch 26 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h112 (by intro hd; norm_num [Nat.factorial] at hd)
  have h114 : factorialSearch 27 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h113 (by intro hd; norm_num [Nat.factorial] at hd)
  have h115 : factorialSearch 28 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h114 (by intro hd; norm_num [Nat.factorial] at hd)
  have h116 : factorialSearch 29 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h115 (by intro hd; norm_num [Nat.factorial] at hd)
  have h117 : factorialSearch 30 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h116 (by intro hd; norm_num [Nat.factorial] at hd)
  have h118 : factorialSearch 31 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h117 (by intro hd; norm_num [Nat.factorial] at hd)
  have h119 : factorialSearch 32 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h118 (by intro hd; norm_num [Nat.factorial] at hd)
  have h120 : factorialSearch 33 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h119 (by intro hd; norm_num [Nat.factorial] at hd)
  have h121 : factorialSearch 34 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h120 (by intro hd; norm_num [Nat.factorial] at hd)
  have h122 : factorialSearch 35 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h121 (by intro hd; norm_num [Nat.factorial] at hd)
  have h123 : factorialSearch 36 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h122 (by intro hd; norm_num [Nat.factorial] at hd)
  have h124 : factorialSearch 37 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h123 (by intro hd; norm_num [Nat.factorial] at hd)
  have h125 : factorialSearch 38 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h124 (by intro hd; norm_num [Nat.factorial] at hd)
  have h126 : factorialSearch 39 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h125 (by intro hd; norm_num [Nat.factorial] at hd)
  have h127 : factorialSearch 40 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h126 (by intro hd; norm_num [Nat.factorial] at hd)
  have h128 : factorialSearch 41 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h127 (by intro hd; norm_num [Nat.factorial] at hd)
  have h129 : factorialSearch 42 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h128 (by intro hd; norm_num [Nat.factorial] at hd)
  have h130 : factorialSearch 43 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h129 (by intro hd; norm_num [Nat.factorial] at hd)
  have h131 : factorialSearch 44 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h130 (by intro hd; norm_num [Nat.factorial] at hd)
  have h132 : factorialSearch 45 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h131 (by intro hd; norm_num [Nat.factorial] at hd)
  have h133 : factorialSearch 46 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h132 (by intro hd; norm_num [Nat.factorial] at hd)
  have h134 : factorialSearch 47 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h133 (by intro hd; norm_num [Nat.factorial] at hd)
  have h135 : factorialSearch 48 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h134 (by intro hd; norm_num [Nat.factorial] at hd)
  have h136 : factorialSearch 49 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h135 (by intro hd; norm_num [Nat.factorial] at hd)
  have h137 : factorialSearch 50 2652 = false :=
    factorialSearch_false_step (by decide) (by decide) h136 (by intro hd; norm_num [Nat.factorial] at hd)
  have h138 : factorialSearch 50 80658175170943878571660636856403766975289505440883277824000000000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h102 (by intro _; norm_num only [Nat.factorial]; exact h137)
  norm_num only [Nat.factorial]
  exact h138

/-- Complete search rejects the target factorial at 53. -/
private theorem search_reject_53 : factorialSearch 51 (53 !) = false := by
  have h0 : factorialSearch 51 4274883284060025564298013753389399649690343788366813724672000000000000 = false :=
    factorialSearch_false_of_prime (p := 53) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 54. -/
private theorem search_reject_54 : factorialSearch 52 (54 !) = false := by
  have h0 : factorialSearch 52 230843697339241380472092742683027581083278564571807941132288000000000000 = false :=
    factorialSearch_false_of_prime (p := 53) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 55. -/
private theorem search_reject_55 : factorialSearch 53 (55 !) = false := by
  have h0 : factorialSearch 52 12696403353658275925965100847566516959580321051449436762275840000000000000 = false :=
    factorialSearch_false_of_prime (p := 53) (by decide) (by decide) (by decide) (by norm_num)
  have h1 : factorialSearch 10 2970 = false :=
    factorialSearch_false_of_prime (p := 11) (by decide) (by decide) (by decide) (by norm_num)
  have h2 : factorialSearch 11 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h1 (by intro hd; norm_num [Nat.factorial] at hd)
  have h3 : factorialSearch 12 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h2 (by intro hd; norm_num [Nat.factorial] at hd)
  have h4 : factorialSearch 13 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h3 (by intro hd; norm_num [Nat.factorial] at hd)
  have h5 : factorialSearch 14 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h4 (by intro hd; norm_num [Nat.factorial] at hd)
  have h6 : factorialSearch 15 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h5 (by intro hd; norm_num [Nat.factorial] at hd)
  have h7 : factorialSearch 16 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h6 (by intro hd; norm_num [Nat.factorial] at hd)
  have h8 : factorialSearch 17 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h7 (by intro hd; norm_num [Nat.factorial] at hd)
  have h9 : factorialSearch 18 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h8 (by intro hd; norm_num [Nat.factorial] at hd)
  have h10 : factorialSearch 19 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h9 (by intro hd; norm_num [Nat.factorial] at hd)
  have h11 : factorialSearch 20 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h10 (by intro hd; norm_num [Nat.factorial] at hd)
  have h12 : factorialSearch 21 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h11 (by intro hd; norm_num [Nat.factorial] at hd)
  have h13 : factorialSearch 22 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h12 (by intro hd; norm_num [Nat.factorial] at hd)
  have h14 : factorialSearch 23 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h13 (by intro hd; norm_num [Nat.factorial] at hd)
  have h15 : factorialSearch 24 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h14 (by intro hd; norm_num [Nat.factorial] at hd)
  have h16 : factorialSearch 25 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h15 (by intro hd; norm_num [Nat.factorial] at hd)
  have h17 : factorialSearch 26 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h16 (by intro hd; norm_num [Nat.factorial] at hd)
  have h18 : factorialSearch 27 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h17 (by intro hd; norm_num [Nat.factorial] at hd)
  have h19 : factorialSearch 28 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h18 (by intro hd; norm_num [Nat.factorial] at hd)
  have h20 : factorialSearch 29 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h19 (by intro hd; norm_num [Nat.factorial] at hd)
  have h21 : factorialSearch 30 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h20 (by intro hd; norm_num [Nat.factorial] at hd)
  have h22 : factorialSearch 31 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h21 (by intro hd; norm_num [Nat.factorial] at hd)
  have h23 : factorialSearch 32 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h22 (by intro hd; norm_num [Nat.factorial] at hd)
  have h24 : factorialSearch 33 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h23 (by intro hd; norm_num [Nat.factorial] at hd)
  have h25 : factorialSearch 34 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h24 (by intro hd; norm_num [Nat.factorial] at hd)
  have h26 : factorialSearch 35 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h25 (by intro hd; norm_num [Nat.factorial] at hd)
  have h27 : factorialSearch 36 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h26 (by intro hd; norm_num [Nat.factorial] at hd)
  have h28 : factorialSearch 37 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h27 (by intro hd; norm_num [Nat.factorial] at hd)
  have h29 : factorialSearch 38 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h28 (by intro hd; norm_num [Nat.factorial] at hd)
  have h30 : factorialSearch 39 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h29 (by intro hd; norm_num [Nat.factorial] at hd)
  have h31 : factorialSearch 40 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h30 (by intro hd; norm_num [Nat.factorial] at hd)
  have h32 : factorialSearch 41 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h31 (by intro hd; norm_num [Nat.factorial] at hd)
  have h33 : factorialSearch 42 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h32 (by intro hd; norm_num [Nat.factorial] at hd)
  have h34 : factorialSearch 43 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h33 (by intro hd; norm_num [Nat.factorial] at hd)
  have h35 : factorialSearch 44 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h34 (by intro hd; norm_num [Nat.factorial] at hd)
  have h36 : factorialSearch 45 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h35 (by intro hd; norm_num [Nat.factorial] at hd)
  have h37 : factorialSearch 46 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h36 (by intro hd; norm_num [Nat.factorial] at hd)
  have h38 : factorialSearch 47 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h37 (by intro hd; norm_num [Nat.factorial] at hd)
  have h39 : factorialSearch 48 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h38 (by intro hd; norm_num [Nat.factorial] at hd)
  have h40 : factorialSearch 49 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h39 (by intro hd; norm_num [Nat.factorial] at hd)
  have h41 : factorialSearch 50 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h40 (by intro hd; norm_num [Nat.factorial] at hd)
  have h42 : factorialSearch 51 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h41 (by intro hd; norm_num [Nat.factorial] at hd)
  have h43 : factorialSearch 52 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h42 (by intro hd; norm_num [Nat.factorial] at hd)
  have h44 : factorialSearch 53 2970 = false :=
    factorialSearch_false_step (by decide) (by decide) h43 (by intro hd; norm_num [Nat.factorial] at hd)
  have h45 : factorialSearch 53 12696403353658275925965100847566516959580321051449436762275840000000000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h0 (by intro _; norm_num only [Nat.factorial]; exact h44)
  norm_num only [Nat.factorial]
  exact h45

/-- Complete search rejects the target factorial at 56. -/
private theorem search_reject_56 : factorialSearch 54 (56 !) = false := by
  have h0 : factorialSearch 52 710998587804863451854045647463724949736497978881168458687447040000000000000 = false :=
    factorialSearch_false_of_prime (p := 53) (by decide) (by decide) (by decide) (by norm_num)
  have h1 : factorialSearch 10 166320 = false :=
    factorialSearch_false_of_prime (p := 11) (by decide) (by decide) (by decide) (by norm_num)
  have h2 : factorialSearch 11 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h1 (by intro hd; norm_num [Nat.factorial] at hd)
  have h3 : factorialSearch 12 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h2 (by intro hd; norm_num [Nat.factorial] at hd)
  have h4 : factorialSearch 13 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h3 (by intro hd; norm_num [Nat.factorial] at hd)
  have h5 : factorialSearch 14 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h4 (by intro hd; norm_num [Nat.factorial] at hd)
  have h6 : factorialSearch 15 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h5 (by intro hd; norm_num [Nat.factorial] at hd)
  have h7 : factorialSearch 16 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h6 (by intro hd; norm_num [Nat.factorial] at hd)
  have h8 : factorialSearch 17 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h7 (by intro hd; norm_num [Nat.factorial] at hd)
  have h9 : factorialSearch 18 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h8 (by intro hd; norm_num [Nat.factorial] at hd)
  have h10 : factorialSearch 19 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h9 (by intro hd; norm_num [Nat.factorial] at hd)
  have h11 : factorialSearch 20 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h10 (by intro hd; norm_num [Nat.factorial] at hd)
  have h12 : factorialSearch 21 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h11 (by intro hd; norm_num [Nat.factorial] at hd)
  have h13 : factorialSearch 22 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h12 (by intro hd; norm_num [Nat.factorial] at hd)
  have h14 : factorialSearch 23 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h13 (by intro hd; norm_num [Nat.factorial] at hd)
  have h15 : factorialSearch 24 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h14 (by intro hd; norm_num [Nat.factorial] at hd)
  have h16 : factorialSearch 25 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h15 (by intro hd; norm_num [Nat.factorial] at hd)
  have h17 : factorialSearch 26 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h16 (by intro hd; norm_num [Nat.factorial] at hd)
  have h18 : factorialSearch 27 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h17 (by intro hd; norm_num [Nat.factorial] at hd)
  have h19 : factorialSearch 28 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h18 (by intro hd; norm_num [Nat.factorial] at hd)
  have h20 : factorialSearch 29 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h19 (by intro hd; norm_num [Nat.factorial] at hd)
  have h21 : factorialSearch 30 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h20 (by intro hd; norm_num [Nat.factorial] at hd)
  have h22 : factorialSearch 31 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h21 (by intro hd; norm_num [Nat.factorial] at hd)
  have h23 : factorialSearch 32 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h22 (by intro hd; norm_num [Nat.factorial] at hd)
  have h24 : factorialSearch 33 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h23 (by intro hd; norm_num [Nat.factorial] at hd)
  have h25 : factorialSearch 34 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h24 (by intro hd; norm_num [Nat.factorial] at hd)
  have h26 : factorialSearch 35 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h25 (by intro hd; norm_num [Nat.factorial] at hd)
  have h27 : factorialSearch 36 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h26 (by intro hd; norm_num [Nat.factorial] at hd)
  have h28 : factorialSearch 37 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h27 (by intro hd; norm_num [Nat.factorial] at hd)
  have h29 : factorialSearch 38 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h28 (by intro hd; norm_num [Nat.factorial] at hd)
  have h30 : factorialSearch 39 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h29 (by intro hd; norm_num [Nat.factorial] at hd)
  have h31 : factorialSearch 40 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h30 (by intro hd; norm_num [Nat.factorial] at hd)
  have h32 : factorialSearch 41 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h31 (by intro hd; norm_num [Nat.factorial] at hd)
  have h33 : factorialSearch 42 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h32 (by intro hd; norm_num [Nat.factorial] at hd)
  have h34 : factorialSearch 43 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h33 (by intro hd; norm_num [Nat.factorial] at hd)
  have h35 : factorialSearch 44 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h34 (by intro hd; norm_num [Nat.factorial] at hd)
  have h36 : factorialSearch 45 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h35 (by intro hd; norm_num [Nat.factorial] at hd)
  have h37 : factorialSearch 46 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h36 (by intro hd; norm_num [Nat.factorial] at hd)
  have h38 : factorialSearch 47 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h37 (by intro hd; norm_num [Nat.factorial] at hd)
  have h39 : factorialSearch 48 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h38 (by intro hd; norm_num [Nat.factorial] at hd)
  have h40 : factorialSearch 49 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h39 (by intro hd; norm_num [Nat.factorial] at hd)
  have h41 : factorialSearch 50 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h40 (by intro hd; norm_num [Nat.factorial] at hd)
  have h42 : factorialSearch 51 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h41 (by intro hd; norm_num [Nat.factorial] at hd)
  have h43 : factorialSearch 52 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h42 (by intro hd; norm_num [Nat.factorial] at hd)
  have h44 : factorialSearch 53 166320 = false :=
    factorialSearch_false_step (by decide) (by decide) h43 (by intro hd; norm_num [Nat.factorial] at hd)
  have h45 : factorialSearch 53 710998587804863451854045647463724949736497978881168458687447040000000000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h0 (by intro _; norm_num only [Nat.factorial]; exact h44)
  have h46 : factorialSearch 10 3080 = false :=
    factorialSearch_false_of_prime (p := 11) (by decide) (by decide) (by decide) (by norm_num)
  have h47 : factorialSearch 11 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h46 (by intro hd; norm_num [Nat.factorial] at hd)
  have h48 : factorialSearch 12 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h47 (by intro hd; norm_num [Nat.factorial] at hd)
  have h49 : factorialSearch 13 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h48 (by intro hd; norm_num [Nat.factorial] at hd)
  have h50 : factorialSearch 14 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h49 (by intro hd; norm_num [Nat.factorial] at hd)
  have h51 : factorialSearch 15 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h50 (by intro hd; norm_num [Nat.factorial] at hd)
  have h52 : factorialSearch 16 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h51 (by intro hd; norm_num [Nat.factorial] at hd)
  have h53 : factorialSearch 17 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h52 (by intro hd; norm_num [Nat.factorial] at hd)
  have h54 : factorialSearch 18 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h53 (by intro hd; norm_num [Nat.factorial] at hd)
  have h55 : factorialSearch 19 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h54 (by intro hd; norm_num [Nat.factorial] at hd)
  have h56 : factorialSearch 20 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h55 (by intro hd; norm_num [Nat.factorial] at hd)
  have h57 : factorialSearch 21 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h56 (by intro hd; norm_num [Nat.factorial] at hd)
  have h58 : factorialSearch 22 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h57 (by intro hd; norm_num [Nat.factorial] at hd)
  have h59 : factorialSearch 23 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h58 (by intro hd; norm_num [Nat.factorial] at hd)
  have h60 : factorialSearch 24 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h59 (by intro hd; norm_num [Nat.factorial] at hd)
  have h61 : factorialSearch 25 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h60 (by intro hd; norm_num [Nat.factorial] at hd)
  have h62 : factorialSearch 26 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h61 (by intro hd; norm_num [Nat.factorial] at hd)
  have h63 : factorialSearch 27 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h62 (by intro hd; norm_num [Nat.factorial] at hd)
  have h64 : factorialSearch 28 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h63 (by intro hd; norm_num [Nat.factorial] at hd)
  have h65 : factorialSearch 29 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h64 (by intro hd; norm_num [Nat.factorial] at hd)
  have h66 : factorialSearch 30 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h65 (by intro hd; norm_num [Nat.factorial] at hd)
  have h67 : factorialSearch 31 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h66 (by intro hd; norm_num [Nat.factorial] at hd)
  have h68 : factorialSearch 32 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h67 (by intro hd; norm_num [Nat.factorial] at hd)
  have h69 : factorialSearch 33 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h68 (by intro hd; norm_num [Nat.factorial] at hd)
  have h70 : factorialSearch 34 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h69 (by intro hd; norm_num [Nat.factorial] at hd)
  have h71 : factorialSearch 35 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h70 (by intro hd; norm_num [Nat.factorial] at hd)
  have h72 : factorialSearch 36 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h71 (by intro hd; norm_num [Nat.factorial] at hd)
  have h73 : factorialSearch 37 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h72 (by intro hd; norm_num [Nat.factorial] at hd)
  have h74 : factorialSearch 38 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h73 (by intro hd; norm_num [Nat.factorial] at hd)
  have h75 : factorialSearch 39 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h74 (by intro hd; norm_num [Nat.factorial] at hd)
  have h76 : factorialSearch 40 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h75 (by intro hd; norm_num [Nat.factorial] at hd)
  have h77 : factorialSearch 41 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h76 (by intro hd; norm_num [Nat.factorial] at hd)
  have h78 : factorialSearch 42 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h77 (by intro hd; norm_num [Nat.factorial] at hd)
  have h79 : factorialSearch 43 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h78 (by intro hd; norm_num [Nat.factorial] at hd)
  have h80 : factorialSearch 44 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h79 (by intro hd; norm_num [Nat.factorial] at hd)
  have h81 : factorialSearch 45 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h80 (by intro hd; norm_num [Nat.factorial] at hd)
  have h82 : factorialSearch 46 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h81 (by intro hd; norm_num [Nat.factorial] at hd)
  have h83 : factorialSearch 47 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h82 (by intro hd; norm_num [Nat.factorial] at hd)
  have h84 : factorialSearch 48 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h83 (by intro hd; norm_num [Nat.factorial] at hd)
  have h85 : factorialSearch 49 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h84 (by intro hd; norm_num [Nat.factorial] at hd)
  have h86 : factorialSearch 50 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h85 (by intro hd; norm_num [Nat.factorial] at hd)
  have h87 : factorialSearch 51 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h86 (by intro hd; norm_num [Nat.factorial] at hd)
  have h88 : factorialSearch 52 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h87 (by intro hd; norm_num [Nat.factorial] at hd)
  have h89 : factorialSearch 53 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h88 (by intro hd; norm_num [Nat.factorial] at hd)
  have h90 : factorialSearch 54 3080 = false :=
    factorialSearch_false_step (by decide) (by decide) h89 (by intro hd; norm_num [Nat.factorial] at hd)
  have h91 : factorialSearch 54 710998587804863451854045647463724949736497978881168458687447040000000000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h45 (by intro _; norm_num only [Nat.factorial]; exact h90)
  norm_num only [Nat.factorial]
  exact h91

/-- Complete search rejects the target factorial at 57. -/
private theorem search_reject_57 : factorialSearch 55 (57 !) = false := by
  have h0 : factorialSearch 52 40526919504877216755680601905432322134980384796226602145184481280000000000000 = false :=
    factorialSearch_false_of_prime (p := 53) (by decide) (by decide) (by decide) (by norm_num)
  have h1 : factorialSearch 18 9480240 = false :=
    factorialSearch_false_of_prime (p := 19) (by decide) (by decide) (by decide) (by norm_num)
  have h2 : factorialSearch 19 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h1 (by intro hd; norm_num [Nat.factorial] at hd)
  have h3 : factorialSearch 20 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h2 (by intro hd; norm_num [Nat.factorial] at hd)
  have h4 : factorialSearch 21 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h3 (by intro hd; norm_num [Nat.factorial] at hd)
  have h5 : factorialSearch 22 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h4 (by intro hd; norm_num [Nat.factorial] at hd)
  have h6 : factorialSearch 23 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h5 (by intro hd; norm_num [Nat.factorial] at hd)
  have h7 : factorialSearch 24 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h6 (by intro hd; norm_num [Nat.factorial] at hd)
  have h8 : factorialSearch 25 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h7 (by intro hd; norm_num [Nat.factorial] at hd)
  have h9 : factorialSearch 26 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h8 (by intro hd; norm_num [Nat.factorial] at hd)
  have h10 : factorialSearch 27 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h9 (by intro hd; norm_num [Nat.factorial] at hd)
  have h11 : factorialSearch 28 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h10 (by intro hd; norm_num [Nat.factorial] at hd)
  have h12 : factorialSearch 29 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h11 (by intro hd; norm_num [Nat.factorial] at hd)
  have h13 : factorialSearch 30 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h12 (by intro hd; norm_num [Nat.factorial] at hd)
  have h14 : factorialSearch 31 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h13 (by intro hd; norm_num [Nat.factorial] at hd)
  have h15 : factorialSearch 32 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h14 (by intro hd; norm_num [Nat.factorial] at hd)
  have h16 : factorialSearch 33 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h15 (by intro hd; norm_num [Nat.factorial] at hd)
  have h17 : factorialSearch 34 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h16 (by intro hd; norm_num [Nat.factorial] at hd)
  have h18 : factorialSearch 35 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h17 (by intro hd; norm_num [Nat.factorial] at hd)
  have h19 : factorialSearch 36 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h18 (by intro hd; norm_num [Nat.factorial] at hd)
  have h20 : factorialSearch 37 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h19 (by intro hd; norm_num [Nat.factorial] at hd)
  have h21 : factorialSearch 38 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h20 (by intro hd; norm_num [Nat.factorial] at hd)
  have h22 : factorialSearch 39 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h21 (by intro hd; norm_num [Nat.factorial] at hd)
  have h23 : factorialSearch 40 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h22 (by intro hd; norm_num [Nat.factorial] at hd)
  have h24 : factorialSearch 41 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h23 (by intro hd; norm_num [Nat.factorial] at hd)
  have h25 : factorialSearch 42 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h24 (by intro hd; norm_num [Nat.factorial] at hd)
  have h26 : factorialSearch 43 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h25 (by intro hd; norm_num [Nat.factorial] at hd)
  have h27 : factorialSearch 44 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h26 (by intro hd; norm_num [Nat.factorial] at hd)
  have h28 : factorialSearch 45 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h27 (by intro hd; norm_num [Nat.factorial] at hd)
  have h29 : factorialSearch 46 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h28 (by intro hd; norm_num [Nat.factorial] at hd)
  have h30 : factorialSearch 47 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h29 (by intro hd; norm_num [Nat.factorial] at hd)
  have h31 : factorialSearch 48 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h30 (by intro hd; norm_num [Nat.factorial] at hd)
  have h32 : factorialSearch 49 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h31 (by intro hd; norm_num [Nat.factorial] at hd)
  have h33 : factorialSearch 50 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h32 (by intro hd; norm_num [Nat.factorial] at hd)
  have h34 : factorialSearch 51 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h33 (by intro hd; norm_num [Nat.factorial] at hd)
  have h35 : factorialSearch 52 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h34 (by intro hd; norm_num [Nat.factorial] at hd)
  have h36 : factorialSearch 53 9480240 = false :=
    factorialSearch_false_step (by decide) (by decide) h35 (by intro hd; norm_num [Nat.factorial] at hd)
  have h37 : factorialSearch 53 40526919504877216755680601905432322134980384796226602145184481280000000000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h0 (by intro _; norm_num only [Nat.factorial]; exact h36)
  have h38 : factorialSearch 18 175560 = false :=
    factorialSearch_false_of_prime (p := 19) (by decide) (by decide) (by decide) (by norm_num)
  have h39 : factorialSearch 19 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h38 (by intro hd; norm_num [Nat.factorial] at hd)
  have h40 : factorialSearch 20 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h39 (by intro hd; norm_num [Nat.factorial] at hd)
  have h41 : factorialSearch 21 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h40 (by intro hd; norm_num [Nat.factorial] at hd)
  have h42 : factorialSearch 22 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h41 (by intro hd; norm_num [Nat.factorial] at hd)
  have h43 : factorialSearch 23 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h42 (by intro hd; norm_num [Nat.factorial] at hd)
  have h44 : factorialSearch 24 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h43 (by intro hd; norm_num [Nat.factorial] at hd)
  have h45 : factorialSearch 25 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h44 (by intro hd; norm_num [Nat.factorial] at hd)
  have h46 : factorialSearch 26 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h45 (by intro hd; norm_num [Nat.factorial] at hd)
  have h47 : factorialSearch 27 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h46 (by intro hd; norm_num [Nat.factorial] at hd)
  have h48 : factorialSearch 28 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h47 (by intro hd; norm_num [Nat.factorial] at hd)
  have h49 : factorialSearch 29 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h48 (by intro hd; norm_num [Nat.factorial] at hd)
  have h50 : factorialSearch 30 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h49 (by intro hd; norm_num [Nat.factorial] at hd)
  have h51 : factorialSearch 31 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h50 (by intro hd; norm_num [Nat.factorial] at hd)
  have h52 : factorialSearch 32 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h51 (by intro hd; norm_num [Nat.factorial] at hd)
  have h53 : factorialSearch 33 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h52 (by intro hd; norm_num [Nat.factorial] at hd)
  have h54 : factorialSearch 34 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h53 (by intro hd; norm_num [Nat.factorial] at hd)
  have h55 : factorialSearch 35 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h54 (by intro hd; norm_num [Nat.factorial] at hd)
  have h56 : factorialSearch 36 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h55 (by intro hd; norm_num [Nat.factorial] at hd)
  have h57 : factorialSearch 37 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h56 (by intro hd; norm_num [Nat.factorial] at hd)
  have h58 : factorialSearch 38 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h57 (by intro hd; norm_num [Nat.factorial] at hd)
  have h59 : factorialSearch 39 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h58 (by intro hd; norm_num [Nat.factorial] at hd)
  have h60 : factorialSearch 40 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h59 (by intro hd; norm_num [Nat.factorial] at hd)
  have h61 : factorialSearch 41 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h60 (by intro hd; norm_num [Nat.factorial] at hd)
  have h62 : factorialSearch 42 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h61 (by intro hd; norm_num [Nat.factorial] at hd)
  have h63 : factorialSearch 43 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h62 (by intro hd; norm_num [Nat.factorial] at hd)
  have h64 : factorialSearch 44 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h63 (by intro hd; norm_num [Nat.factorial] at hd)
  have h65 : factorialSearch 45 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h64 (by intro hd; norm_num [Nat.factorial] at hd)
  have h66 : factorialSearch 46 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h65 (by intro hd; norm_num [Nat.factorial] at hd)
  have h67 : factorialSearch 47 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h66 (by intro hd; norm_num [Nat.factorial] at hd)
  have h68 : factorialSearch 48 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h67 (by intro hd; norm_num [Nat.factorial] at hd)
  have h69 : factorialSearch 49 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h68 (by intro hd; norm_num [Nat.factorial] at hd)
  have h70 : factorialSearch 50 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h69 (by intro hd; norm_num [Nat.factorial] at hd)
  have h71 : factorialSearch 51 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h70 (by intro hd; norm_num [Nat.factorial] at hd)
  have h72 : factorialSearch 52 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h71 (by intro hd; norm_num [Nat.factorial] at hd)
  have h73 : factorialSearch 53 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h72 (by intro hd; norm_num [Nat.factorial] at hd)
  have h74 : factorialSearch 54 175560 = false :=
    factorialSearch_false_step (by decide) (by decide) h73 (by intro hd; norm_num [Nat.factorial] at hd)
  have h75 : factorialSearch 54 40526919504877216755680601905432322134980384796226602145184481280000000000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h37 (by intro _; norm_num only [Nat.factorial]; exact h74)
  have h76 : factorialSearch 18 3192 = false :=
    factorialSearch_false_of_prime (p := 19) (by decide) (by decide) (by decide) (by norm_num)
  have h77 : factorialSearch 19 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h76 (by intro hd; norm_num [Nat.factorial] at hd)
  have h78 : factorialSearch 20 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h77 (by intro hd; norm_num [Nat.factorial] at hd)
  have h79 : factorialSearch 21 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h78 (by intro hd; norm_num [Nat.factorial] at hd)
  have h80 : factorialSearch 22 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h79 (by intro hd; norm_num [Nat.factorial] at hd)
  have h81 : factorialSearch 23 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h80 (by intro hd; norm_num [Nat.factorial] at hd)
  have h82 : factorialSearch 24 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h81 (by intro hd; norm_num [Nat.factorial] at hd)
  have h83 : factorialSearch 25 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h82 (by intro hd; norm_num [Nat.factorial] at hd)
  have h84 : factorialSearch 26 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h83 (by intro hd; norm_num [Nat.factorial] at hd)
  have h85 : factorialSearch 27 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h84 (by intro hd; norm_num [Nat.factorial] at hd)
  have h86 : factorialSearch 28 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h85 (by intro hd; norm_num [Nat.factorial] at hd)
  have h87 : factorialSearch 29 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h86 (by intro hd; norm_num [Nat.factorial] at hd)
  have h88 : factorialSearch 30 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h87 (by intro hd; norm_num [Nat.factorial] at hd)
  have h89 : factorialSearch 31 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h88 (by intro hd; norm_num [Nat.factorial] at hd)
  have h90 : factorialSearch 32 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h89 (by intro hd; norm_num [Nat.factorial] at hd)
  have h91 : factorialSearch 33 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h90 (by intro hd; norm_num [Nat.factorial] at hd)
  have h92 : factorialSearch 34 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h91 (by intro hd; norm_num [Nat.factorial] at hd)
  have h93 : factorialSearch 35 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h92 (by intro hd; norm_num [Nat.factorial] at hd)
  have h94 : factorialSearch 36 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h93 (by intro hd; norm_num [Nat.factorial] at hd)
  have h95 : factorialSearch 37 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h94 (by intro hd; norm_num [Nat.factorial] at hd)
  have h96 : factorialSearch 38 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h95 (by intro hd; norm_num [Nat.factorial] at hd)
  have h97 : factorialSearch 39 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h96 (by intro hd; norm_num [Nat.factorial] at hd)
  have h98 : factorialSearch 40 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h97 (by intro hd; norm_num [Nat.factorial] at hd)
  have h99 : factorialSearch 41 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h98 (by intro hd; norm_num [Nat.factorial] at hd)
  have h100 : factorialSearch 42 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h99 (by intro hd; norm_num [Nat.factorial] at hd)
  have h101 : factorialSearch 43 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h100 (by intro hd; norm_num [Nat.factorial] at hd)
  have h102 : factorialSearch 44 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h101 (by intro hd; norm_num [Nat.factorial] at hd)
  have h103 : factorialSearch 45 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h102 (by intro hd; norm_num [Nat.factorial] at hd)
  have h104 : factorialSearch 46 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h103 (by intro hd; norm_num [Nat.factorial] at hd)
  have h105 : factorialSearch 47 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h104 (by intro hd; norm_num [Nat.factorial] at hd)
  have h106 : factorialSearch 48 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h105 (by intro hd; norm_num [Nat.factorial] at hd)
  have h107 : factorialSearch 49 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h106 (by intro hd; norm_num [Nat.factorial] at hd)
  have h108 : factorialSearch 50 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h107 (by intro hd; norm_num [Nat.factorial] at hd)
  have h109 : factorialSearch 51 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h108 (by intro hd; norm_num [Nat.factorial] at hd)
  have h110 : factorialSearch 52 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h109 (by intro hd; norm_num [Nat.factorial] at hd)
  have h111 : factorialSearch 53 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h110 (by intro hd; norm_num [Nat.factorial] at hd)
  have h112 : factorialSearch 54 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h111 (by intro hd; norm_num [Nat.factorial] at hd)
  have h113 : factorialSearch 55 3192 = false :=
    factorialSearch_false_step (by decide) (by decide) h112 (by intro hd; norm_num [Nat.factorial] at hd)
  have h114 : factorialSearch 55 40526919504877216755680601905432322134980384796226602145184481280000000000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h75 (by intro _; norm_num only [Nat.factorial]; exact h113)
  norm_num only [Nat.factorial]
  exact h114

/-- Complete search rejects the target factorial at 58. -/
private theorem search_reject_58 : factorialSearch 56 (58 !) = false := by
  have h0 : factorialSearch 52 2350561331282878571829474910515074683828862318181142924420699914240000000000000 = false :=
    factorialSearch_false_of_prime (p := 53) (by decide) (by decide) (by decide) (by norm_num)
  have h1 : factorialSearch 28 549853920 = false :=
    factorialSearch_false_of_prime (p := 29) (by decide) (by decide) (by decide) (by norm_num)
  have h2 : factorialSearch 29 549853920 = false :=
    factorialSearch_false_step (by decide) (by decide) h1 (by intro hd; norm_num [Nat.factorial] at hd)
  have h3 : factorialSearch 30 549853920 = false :=
    factorialSearch_false_step (by decide) (by decide) h2 (by intro hd; norm_num [Nat.factorial] at hd)
  have h4 : factorialSearch 31 549853920 = false :=
    factorialSearch_false_step (by decide) (by decide) h3 (by intro hd; norm_num [Nat.factorial] at hd)
  have h5 : factorialSearch 32 549853920 = false :=
    factorialSearch_false_step (by decide) (by decide) h4 (by intro hd; norm_num [Nat.factorial] at hd)
  have h6 : factorialSearch 33 549853920 = false :=
    factorialSearch_false_step (by decide) (by decide) h5 (by intro hd; norm_num [Nat.factorial] at hd)
  have h7 : factorialSearch 34 549853920 = false :=
    factorialSearch_false_step (by decide) (by decide) h6 (by intro hd; norm_num [Nat.factorial] at hd)
  have h8 : factorialSearch 35 549853920 = false :=
    factorialSearch_false_step (by decide) (by decide) h7 (by intro hd; norm_num [Nat.factorial] at hd)
  have h9 : factorialSearch 36 549853920 = false :=
    factorialSearch_false_step (by decide) (by decide) h8 (by intro hd; norm_num [Nat.factorial] at hd)
  have h10 : factorialSearch 37 549853920 = false :=
    factorialSearch_false_step (by decide) (by decide) h9 (by intro hd; norm_num [Nat.factorial] at hd)
  have h11 : factorialSearch 38 549853920 = false :=
    factorialSearch_false_step (by decide) (by decide) h10 (by intro hd; norm_num [Nat.factorial] at hd)
  have h12 : factorialSearch 39 549853920 = false :=
    factorialSearch_false_step (by decide) (by decide) h11 (by intro hd; norm_num [Nat.factorial] at hd)
  have h13 : factorialSearch 40 549853920 = false :=
    factorialSearch_false_step (by decide) (by decide) h12 (by intro hd; norm_num [Nat.factorial] at hd)
  have h14 : factorialSearch 41 549853920 = false :=
    factorialSearch_false_step (by decide) (by decide) h13 (by intro hd; norm_num [Nat.factorial] at hd)
  have h15 : factorialSearch 42 549853920 = false :=
    factorialSearch_false_step (by decide) (by decide) h14 (by intro hd; norm_num [Nat.factorial] at hd)
  have h16 : factorialSearch 43 549853920 = false :=
    factorialSearch_false_step (by decide) (by decide) h15 (by intro hd; norm_num [Nat.factorial] at hd)
  have h17 : factorialSearch 44 549853920 = false :=
    factorialSearch_false_step (by decide) (by decide) h16 (by intro hd; norm_num [Nat.factorial] at hd)
  have h18 : factorialSearch 45 549853920 = false :=
    factorialSearch_false_step (by decide) (by decide) h17 (by intro hd; norm_num [Nat.factorial] at hd)
  have h19 : factorialSearch 46 549853920 = false :=
    factorialSearch_false_step (by decide) (by decide) h18 (by intro hd; norm_num [Nat.factorial] at hd)
  have h20 : factorialSearch 47 549853920 = false :=
    factorialSearch_false_step (by decide) (by decide) h19 (by intro hd; norm_num [Nat.factorial] at hd)
  have h21 : factorialSearch 48 549853920 = false :=
    factorialSearch_false_step (by decide) (by decide) h20 (by intro hd; norm_num [Nat.factorial] at hd)
  have h22 : factorialSearch 49 549853920 = false :=
    factorialSearch_false_step (by decide) (by decide) h21 (by intro hd; norm_num [Nat.factorial] at hd)
  have h23 : factorialSearch 50 549853920 = false :=
    factorialSearch_false_step (by decide) (by decide) h22 (by intro hd; norm_num [Nat.factorial] at hd)
  have h24 : factorialSearch 51 549853920 = false :=
    factorialSearch_false_step (by decide) (by decide) h23 (by intro hd; norm_num [Nat.factorial] at hd)
  have h25 : factorialSearch 52 549853920 = false :=
    factorialSearch_false_step (by decide) (by decide) h24 (by intro hd; norm_num [Nat.factorial] at hd)
  have h26 : factorialSearch 53 549853920 = false :=
    factorialSearch_false_step (by decide) (by decide) h25 (by intro hd; norm_num [Nat.factorial] at hd)
  have h27 : factorialSearch 53 2350561331282878571829474910515074683828862318181142924420699914240000000000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h0 (by intro _; norm_num only [Nat.factorial]; exact h26)
  have h28 : factorialSearch 28 10182480 = false :=
    factorialSearch_false_of_prime (p := 29) (by decide) (by decide) (by decide) (by norm_num)
  have h29 : factorialSearch 29 10182480 = false :=
    factorialSearch_false_step (by decide) (by decide) h28 (by intro hd; norm_num [Nat.factorial] at hd)
  have h30 : factorialSearch 30 10182480 = false :=
    factorialSearch_false_step (by decide) (by decide) h29 (by intro hd; norm_num [Nat.factorial] at hd)
  have h31 : factorialSearch 31 10182480 = false :=
    factorialSearch_false_step (by decide) (by decide) h30 (by intro hd; norm_num [Nat.factorial] at hd)
  have h32 : factorialSearch 32 10182480 = false :=
    factorialSearch_false_step (by decide) (by decide) h31 (by intro hd; norm_num [Nat.factorial] at hd)
  have h33 : factorialSearch 33 10182480 = false :=
    factorialSearch_false_step (by decide) (by decide) h32 (by intro hd; norm_num [Nat.factorial] at hd)
  have h34 : factorialSearch 34 10182480 = false :=
    factorialSearch_false_step (by decide) (by decide) h33 (by intro hd; norm_num [Nat.factorial] at hd)
  have h35 : factorialSearch 35 10182480 = false :=
    factorialSearch_false_step (by decide) (by decide) h34 (by intro hd; norm_num [Nat.factorial] at hd)
  have h36 : factorialSearch 36 10182480 = false :=
    factorialSearch_false_step (by decide) (by decide) h35 (by intro hd; norm_num [Nat.factorial] at hd)
  have h37 : factorialSearch 37 10182480 = false :=
    factorialSearch_false_step (by decide) (by decide) h36 (by intro hd; norm_num [Nat.factorial] at hd)
  have h38 : factorialSearch 38 10182480 = false :=
    factorialSearch_false_step (by decide) (by decide) h37 (by intro hd; norm_num [Nat.factorial] at hd)
  have h39 : factorialSearch 39 10182480 = false :=
    factorialSearch_false_step (by decide) (by decide) h38 (by intro hd; norm_num [Nat.factorial] at hd)
  have h40 : factorialSearch 40 10182480 = false :=
    factorialSearch_false_step (by decide) (by decide) h39 (by intro hd; norm_num [Nat.factorial] at hd)
  have h41 : factorialSearch 41 10182480 = false :=
    factorialSearch_false_step (by decide) (by decide) h40 (by intro hd; norm_num [Nat.factorial] at hd)
  have h42 : factorialSearch 42 10182480 = false :=
    factorialSearch_false_step (by decide) (by decide) h41 (by intro hd; norm_num [Nat.factorial] at hd)
  have h43 : factorialSearch 43 10182480 = false :=
    factorialSearch_false_step (by decide) (by decide) h42 (by intro hd; norm_num [Nat.factorial] at hd)
  have h44 : factorialSearch 44 10182480 = false :=
    factorialSearch_false_step (by decide) (by decide) h43 (by intro hd; norm_num [Nat.factorial] at hd)
  have h45 : factorialSearch 45 10182480 = false :=
    factorialSearch_false_step (by decide) (by decide) h44 (by intro hd; norm_num [Nat.factorial] at hd)
  have h46 : factorialSearch 46 10182480 = false :=
    factorialSearch_false_step (by decide) (by decide) h45 (by intro hd; norm_num [Nat.factorial] at hd)
  have h47 : factorialSearch 47 10182480 = false :=
    factorialSearch_false_step (by decide) (by decide) h46 (by intro hd; norm_num [Nat.factorial] at hd)
  have h48 : factorialSearch 48 10182480 = false :=
    factorialSearch_false_step (by decide) (by decide) h47 (by intro hd; norm_num [Nat.factorial] at hd)
  have h49 : factorialSearch 49 10182480 = false :=
    factorialSearch_false_step (by decide) (by decide) h48 (by intro hd; norm_num [Nat.factorial] at hd)
  have h50 : factorialSearch 50 10182480 = false :=
    factorialSearch_false_step (by decide) (by decide) h49 (by intro hd; norm_num [Nat.factorial] at hd)
  have h51 : factorialSearch 51 10182480 = false :=
    factorialSearch_false_step (by decide) (by decide) h50 (by intro hd; norm_num [Nat.factorial] at hd)
  have h52 : factorialSearch 52 10182480 = false :=
    factorialSearch_false_step (by decide) (by decide) h51 (by intro hd; norm_num [Nat.factorial] at hd)
  have h53 : factorialSearch 53 10182480 = false :=
    factorialSearch_false_step (by decide) (by decide) h52 (by intro hd; norm_num [Nat.factorial] at hd)
  have h54 : factorialSearch 54 10182480 = false :=
    factorialSearch_false_step (by decide) (by decide) h53 (by intro hd; norm_num [Nat.factorial] at hd)
  have h55 : factorialSearch 54 2350561331282878571829474910515074683828862318181142924420699914240000000000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h27 (by intro _; norm_num only [Nat.factorial]; exact h54)
  have h56 : factorialSearch 28 185136 = false :=
    factorialSearch_false_of_prime (p := 29) (by decide) (by decide) (by decide) (by norm_num)
  have h57 : factorialSearch 29 185136 = false :=
    factorialSearch_false_step (by decide) (by decide) h56 (by intro hd; norm_num [Nat.factorial] at hd)
  have h58 : factorialSearch 30 185136 = false :=
    factorialSearch_false_step (by decide) (by decide) h57 (by intro hd; norm_num [Nat.factorial] at hd)
  have h59 : factorialSearch 31 185136 = false :=
    factorialSearch_false_step (by decide) (by decide) h58 (by intro hd; norm_num [Nat.factorial] at hd)
  have h60 : factorialSearch 32 185136 = false :=
    factorialSearch_false_step (by decide) (by decide) h59 (by intro hd; norm_num [Nat.factorial] at hd)
  have h61 : factorialSearch 33 185136 = false :=
    factorialSearch_false_step (by decide) (by decide) h60 (by intro hd; norm_num [Nat.factorial] at hd)
  have h62 : factorialSearch 34 185136 = false :=
    factorialSearch_false_step (by decide) (by decide) h61 (by intro hd; norm_num [Nat.factorial] at hd)
  have h63 : factorialSearch 35 185136 = false :=
    factorialSearch_false_step (by decide) (by decide) h62 (by intro hd; norm_num [Nat.factorial] at hd)
  have h64 : factorialSearch 36 185136 = false :=
    factorialSearch_false_step (by decide) (by decide) h63 (by intro hd; norm_num [Nat.factorial] at hd)
  have h65 : factorialSearch 37 185136 = false :=
    factorialSearch_false_step (by decide) (by decide) h64 (by intro hd; norm_num [Nat.factorial] at hd)
  have h66 : factorialSearch 38 185136 = false :=
    factorialSearch_false_step (by decide) (by decide) h65 (by intro hd; norm_num [Nat.factorial] at hd)
  have h67 : factorialSearch 39 185136 = false :=
    factorialSearch_false_step (by decide) (by decide) h66 (by intro hd; norm_num [Nat.factorial] at hd)
  have h68 : factorialSearch 40 185136 = false :=
    factorialSearch_false_step (by decide) (by decide) h67 (by intro hd; norm_num [Nat.factorial] at hd)
  have h69 : factorialSearch 41 185136 = false :=
    factorialSearch_false_step (by decide) (by decide) h68 (by intro hd; norm_num [Nat.factorial] at hd)
  have h70 : factorialSearch 42 185136 = false :=
    factorialSearch_false_step (by decide) (by decide) h69 (by intro hd; norm_num [Nat.factorial] at hd)
  have h71 : factorialSearch 43 185136 = false :=
    factorialSearch_false_step (by decide) (by decide) h70 (by intro hd; norm_num [Nat.factorial] at hd)
  have h72 : factorialSearch 44 185136 = false :=
    factorialSearch_false_step (by decide) (by decide) h71 (by intro hd; norm_num [Nat.factorial] at hd)
  have h73 : factorialSearch 45 185136 = false :=
    factorialSearch_false_step (by decide) (by decide) h72 (by intro hd; norm_num [Nat.factorial] at hd)
  have h74 : factorialSearch 46 185136 = false :=
    factorialSearch_false_step (by decide) (by decide) h73 (by intro hd; norm_num [Nat.factorial] at hd)
  have h75 : factorialSearch 47 185136 = false :=
    factorialSearch_false_step (by decide) (by decide) h74 (by intro hd; norm_num [Nat.factorial] at hd)
  have h76 : factorialSearch 48 185136 = false :=
    factorialSearch_false_step (by decide) (by decide) h75 (by intro hd; norm_num [Nat.factorial] at hd)
  have h77 : factorialSearch 49 185136 = false :=
    factorialSearch_false_step (by decide) (by decide) h76 (by intro hd; norm_num [Nat.factorial] at hd)
  have h78 : factorialSearch 50 185136 = false :=
    factorialSearch_false_step (by decide) (by decide) h77 (by intro hd; norm_num [Nat.factorial] at hd)
  have h79 : factorialSearch 51 185136 = false :=
    factorialSearch_false_step (by decide) (by decide) h78 (by intro hd; norm_num [Nat.factorial] at hd)
  have h80 : factorialSearch 52 185136 = false :=
    factorialSearch_false_step (by decide) (by decide) h79 (by intro hd; norm_num [Nat.factorial] at hd)
  have h81 : factorialSearch 53 185136 = false :=
    factorialSearch_false_step (by decide) (by decide) h80 (by intro hd; norm_num [Nat.factorial] at hd)
  have h82 : factorialSearch 54 185136 = false :=
    factorialSearch_false_step (by decide) (by decide) h81 (by intro hd; norm_num [Nat.factorial] at hd)
  have h83 : factorialSearch 55 185136 = false :=
    factorialSearch_false_step (by decide) (by decide) h82 (by intro hd; norm_num [Nat.factorial] at hd)
  have h84 : factorialSearch 55 2350561331282878571829474910515074683828862318181142924420699914240000000000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h55 (by intro _; norm_num only [Nat.factorial]; exact h83)
  have h85 : factorialSearch 28 3306 = false :=
    factorialSearch_false_of_prime (p := 29) (by decide) (by decide) (by decide) (by norm_num)
  have h86 : factorialSearch 29 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h85 (by intro hd; norm_num [Nat.factorial] at hd)
  have h87 : factorialSearch 30 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h86 (by intro hd; norm_num [Nat.factorial] at hd)
  have h88 : factorialSearch 31 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h87 (by intro hd; norm_num [Nat.factorial] at hd)
  have h89 : factorialSearch 32 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h88 (by intro hd; norm_num [Nat.factorial] at hd)
  have h90 : factorialSearch 33 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h89 (by intro hd; norm_num [Nat.factorial] at hd)
  have h91 : factorialSearch 34 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h90 (by intro hd; norm_num [Nat.factorial] at hd)
  have h92 : factorialSearch 35 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h91 (by intro hd; norm_num [Nat.factorial] at hd)
  have h93 : factorialSearch 36 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h92 (by intro hd; norm_num [Nat.factorial] at hd)
  have h94 : factorialSearch 37 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h93 (by intro hd; norm_num [Nat.factorial] at hd)
  have h95 : factorialSearch 38 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h94 (by intro hd; norm_num [Nat.factorial] at hd)
  have h96 : factorialSearch 39 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h95 (by intro hd; norm_num [Nat.factorial] at hd)
  have h97 : factorialSearch 40 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h96 (by intro hd; norm_num [Nat.factorial] at hd)
  have h98 : factorialSearch 41 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h97 (by intro hd; norm_num [Nat.factorial] at hd)
  have h99 : factorialSearch 42 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h98 (by intro hd; norm_num [Nat.factorial] at hd)
  have h100 : factorialSearch 43 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h99 (by intro hd; norm_num [Nat.factorial] at hd)
  have h101 : factorialSearch 44 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h100 (by intro hd; norm_num [Nat.factorial] at hd)
  have h102 : factorialSearch 45 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h101 (by intro hd; norm_num [Nat.factorial] at hd)
  have h103 : factorialSearch 46 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h102 (by intro hd; norm_num [Nat.factorial] at hd)
  have h104 : factorialSearch 47 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h103 (by intro hd; norm_num [Nat.factorial] at hd)
  have h105 : factorialSearch 48 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h104 (by intro hd; norm_num [Nat.factorial] at hd)
  have h106 : factorialSearch 49 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h105 (by intro hd; norm_num [Nat.factorial] at hd)
  have h107 : factorialSearch 50 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h106 (by intro hd; norm_num [Nat.factorial] at hd)
  have h108 : factorialSearch 51 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h107 (by intro hd; norm_num [Nat.factorial] at hd)
  have h109 : factorialSearch 52 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h108 (by intro hd; norm_num [Nat.factorial] at hd)
  have h110 : factorialSearch 53 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h109 (by intro hd; norm_num [Nat.factorial] at hd)
  have h111 : factorialSearch 54 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h110 (by intro hd; norm_num [Nat.factorial] at hd)
  have h112 : factorialSearch 55 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h111 (by intro hd; norm_num [Nat.factorial] at hd)
  have h113 : factorialSearch 56 3306 = false :=
    factorialSearch_false_step (by decide) (by decide) h112 (by intro hd; norm_num [Nat.factorial] at hd)
  have h114 : factorialSearch 56 2350561331282878571829474910515074683828862318181142924420699914240000000000000 = false :=
    factorialSearch_false_step (by decide) (by decide) h84 (by intro _; norm_num only [Nat.factorial]; exact h113)
  norm_num only [Nat.factorial]
  exact h114

/-- Complete search rejects the target factorial at 59. -/
private theorem search_reject_59 : factorialSearch 57 (59 !) = false := by
  have h0 : factorialSearch 57 138683118545689835737939019720389406345902876772687432540821294940160000000000000 = false :=
    factorialSearch_false_of_prime (p := 59) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- Complete search rejects the target factorial at 60. -/
private theorem search_reject_60 : factorialSearch 58 (60 !) = false := by
  have h0 : factorialSearch 58 8320987112741390144276341183223364380754172606361245952449277696409600000000000000 = false :=
    factorialSearch_false_of_prime (p := 59) (by decide) (by decide) (by decide) (by norm_num)
  norm_num only [Nat.factorial]
  exact h0

/-- The exact search on the initial window accepts precisely the three known terms. -/
theorem factorialSearch_small_window :
    ∀ n ∈ Finset.Icc 2 16, factorialSearch (n - 2) (n !) = true ↔ n ∈ knownTerms := by
  intro n hn
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
  have htwo : factorialSearch 0 2 = false := search_reject_2
  interval_cases n <;>
    simp [htwo, search_reject_3, search_reject_4, search_reject_5,
      search_reject_6, search_reject_7, search_reject_8, search_reject_11,
      search_reject_12, search_reject_13, search_reject_14, search_reject_15,
      search_accept_9, search_accept_10, search_accept_16, knownTerms]

/-- The complete search on arguments two through sixty accepts exactly the known terms. -/
theorem factorialSearch_window :
    ∀ n ∈ Finset.Icc 2 60, factorialSearch (n - 2) (n !) = true ↔ n ∈ knownTerms := by
  intro n hn
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
  by_cases hsmall : n ≤ 16
  · exact factorialSearch_small_window n (Finset.mem_Icc.mpr ⟨hlo, hsmall⟩)
  have hlarge : 17 ≤ n := by omega
  interval_cases n <;>
    simp [search_reject_17, search_reject_18, search_reject_19, search_reject_20,
      search_reject_21, search_reject_22, search_reject_23, search_reject_24,
      search_reject_25, search_reject_26, search_reject_27, search_reject_28,
      search_reject_29, search_reject_30, search_reject_31, search_reject_32,
      search_reject_33, search_reject_34, search_reject_35, search_reject_36,
      search_reject_37, search_reject_38, search_reject_39, search_reject_40,
      search_reject_41, search_reject_42, search_reject_43, search_reject_44,
      search_reject_45, search_reject_46, search_reject_47, search_reject_48,
      search_reject_49, search_reject_50, search_reject_51, search_reject_52,
      search_reject_53, search_reject_54, search_reject_55, search_reject_56,
      search_reject_57, search_reject_58, search_reject_59, search_reject_60, knownTerms]

/-- In the inclusive window from two through sixty, every exact nontrivial
factorial-product representation has a known term as its target. -/
theorem isNontrivialFactorialProduct_mem_knownTerms_window :
    ∀ n ∈ Finset.Icc 2 60, IsNontrivialFactorialProduct n → n ∈ knownTerms := by
  intro n hn hp
  have hn2 := (Finset.mem_Icc.mp hn).1
  exact (factorialSearch_window n hn).mp
    ((isNontrivialFactorialProduct_iff_search hn2).mp hp)

example : 9 ∈ Finset.Icc 2 60 ∧ IsNontrivialFactorialProduct 9 :=
  ⟨by decide, isNontrivialFactorialProduct_nine⟩

end FactorialProducts
