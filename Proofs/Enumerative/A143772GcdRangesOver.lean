/-
# A143772: the range of a divisor gcd

OEIS A143772, Robert G. Wilson v (Sep 08 2008), with companion A143771.
For composite `m`, put `g(m) = gcd_{d∣m}(d+m/d)`. The range of the
sequence enumerating composites is exactly `{1,3}` together with all
positive even integers; `0` is excluded.
Odd values divide `3`. Each positive even value is realized using two
applications of Dirichlet's theorem to construct suitable primes.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A143772GcdRangesOver

/-! ## Definitions -/

/-- `g m = gcd_{d ∣ m} (d + m / d)`, the gcd taken over all divisors `d` of `m`
(the inner term of A143772). -/
def g (m : ℕ) : ℕ := m.divisors.gcd (fun d => d + m / d)

/-- The composite numbers: `1 < m` and `m` not prime. -/
def IsComposite (m : ℕ) : Prop := 1 < m ∧ ¬ m.Prime

instance : DecidablePred IsComposite := fun m => by
  unfold IsComposite; infer_instance

/-- A143772, shifted to offset `0`: `a n = g (c n)` where `c n` is the `n`-th
composite number counting from `c 0 = 4` (OEIS offset `1` gives `a(1) = a 0`). -/
noncomputable def a (n : ℕ) : ℕ := g (Nat.nth IsComposite n)

/-! ### Examples -/

example : g 4 = 1 := by decide
example : g 8 = 3 := by decide
example : g 9 = 2 := by decide
example : g 15 = 8 := by decide
example : g 36 = 1 := by decide

/-- The first ten listed terms `1,1,3,2,1,1,3,8,1,1` at the composites
`4, 6, 8, 9, 10, 12, 14, 15, 16, 18`. -/
example : (List.map g [4, 6, 8, 9, 10, 12, 14, 15, 16, 18]) =
    [1, 1, 3, 2, 1, 1, 3, 8, 1, 1] := by decide

/-- `a` is evaluated through `Nat.nth_count`: the composite `15` has seven
smaller composites, so `a 7 = g 15 = 8` (the eighth listed term). -/
example : a 7 = 8 := by
  have hc : Nat.count IsComposite 15 = 7 := by decide
  have h15 : IsComposite 15 := by decide
  rw [a, ← hc, Nat.nth_count h15]
  decide

/-! ## Basic lemmas -/

/-- The set of composite numbers is infinite. -/
theorem infinite_setOf_isComposite : {m | IsComposite m}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun n => ⟨2 * (n + 2), ?_, by omega⟩
  exact ⟨by omega, Nat.not_prime_mul (by omega) (by omega)⟩

/-- The terms of A143772 are exactly the values of `g` on composite numbers. -/
theorem range_a_eq_image : Set.range a = g '' {m | IsComposite m} := by
  have h := Nat.range_nth_of_infinite infinite_setOf_isComposite
  rw [show a = g ∘ Nat.nth IsComposite from rfl, Set.range_comp]
  exact congrArg (g '' ·) h

/-- `g m` divides `d + m / d` for every divisor `d` of a positive `m`. -/
theorem g_dvd {m d : ℕ} (hd : d ∣ m) (hm : m ≠ 0) : g m ∣ d + m / d :=
  Finset.gcd_dvd (f := fun d => d + m / d) (Nat.mem_divisors.mpr ⟨hd, hm⟩)

/-- `g m` is positive for positive `m`. -/
theorem g_pos {m : ℕ} (hm : m ≠ 0) : 0 < g m := by
  have h := g_dvd (one_dvd m) hm
  exact Nat.pos_of_ne_zero fun h0 => by simp [h0] at h

/-! ## Odd values -/

/-- For odd `m`, `g m` is even: every `d + m/d` is a sum of two odd numbers. -/
theorem two_dvd_g_of_odd {m : ℕ} (hm : Odd m) : 2 ∣ g m := by
  refine Finset.dvd_gcd fun d hd => ?_
  obtain ⟨hdm, -⟩ := Nat.mem_divisors.mp hd
  have hd' : Odd d := hm.of_dvd_nat hdm
  have hq : Odd (m / d) := hm.of_dvd_nat (Nat.div_dvd_of_dvd hdm)
  exact (hd'.add_odd hq).two_dvd

/-- For even `m ≠ 0`, `g m ∣ 3`, from the divisors `1` and `2`. -/
theorem g_dvd_three_of_even {m : ℕ} (hm : Even m) (hm0 : m ≠ 0) : g m ∣ 3 := by
  obtain ⟨j, rfl⟩ := hm
  have h1 : g (j + j) ∣ 1 + (j + j) := by
    simpa using g_dvd (one_dvd (j + j)) hm0
  have h2 : g (j + j) ∣ 2 + j := by
    have := g_dvd (d := 2) ⟨j, by ring⟩ hm0
    rwa [show (j + j) / 2 = j by omega] at this
  have h3 : g (j + j) ∣ (1 + (j + j)) + 3 := by
    rw [show 1 + (j + j) + 3 = 2 * (2 + j) by ring]
    exact Dvd.dvd.mul_left h2 2
  exact (Nat.dvd_add_right h1).mp h3

/-- **Part (ii).** If `g m` is odd for some `m ≠ 0`, then `g m = 1` or `g m = 3`. -/
theorem g_eq_one_or_three_of_odd {m : ℕ} (hm0 : m ≠ 0) (ho : Odd (g m)) :
    g m = 1 ∨ g m = 3 := by
  rcases Nat.even_or_odd m with he | hodd
  · exact (Nat.dvd_prime Nat.prime_three).mp (g_dvd_three_of_even he hm0)
  · exact absurd (two_dvd_g_of_odd hodd) (Nat.not_even_iff_odd.mpr ho ∘ even_iff_two_dvd.mpr)

/-! ## Even values -/

/-- An integer coprime to `n` is a unit in `ZMod n`. -/
theorem isUnit_intCast_of_isCoprime {x : ℤ} {n : ℕ} (h : IsCoprime x (n : ℤ)) :
    IsUnit (x : ZMod n) := by
  obtain ⟨u, v, huv⟩ := h
  refine IsUnit.of_mul_eq_one (u : ZMod n) ?_
  have h' := congrArg (fun z : ℤ => (z : ZMod n)) huv
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero,
    add_zero, Int.cast_one] at h'
  rw [mul_comm]
  exact h'

/-- For primes `p, q`, `g (p * q) = gcd (p * q + 1, p + q)`: the divisors of
`p * q` are `1, p, q, p * q`. -/
theorem g_prime_mul {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    g (p * q) = Nat.gcd (p * q + 1) (p + q) := by
  have hpq0 : p * q ≠ 0 := Nat.mul_ne_zero hp.ne_zero hq.ne_zero
  apply Nat.dvd_antisymm
  · refine Nat.dvd_gcd ?_ ?_
    · simpa [add_comm] using g_dvd (one_dvd (p * q)) hpq0
    · have h := g_dvd (dvd_mul_right p q) hpq0
      rwa [Nat.mul_div_cancel_left q hp.pos] at h
  · refine Finset.dvd_gcd fun d hd => ?_
    obtain ⟨hdm, -⟩ := Nat.mem_divisors.mp hd
    obtain ⟨d₁, d₂, h₁, h₂, rfl⟩ := Nat.dvd_mul.mp hdm
    have hG1 := Nat.gcd_dvd_left (p * q + 1) (p + q)
    have hG2 := Nat.gcd_dvd_right (p * q + 1) (p + q)
    rcases (Nat.dvd_prime hp).mp h₁ with h₁ | h₁ <;>
      rcases (Nat.dvd_prime hq).mp h₂ with h₂ | h₂ <;> rw [h₁, h₂]
    · simpa [add_comm] using hG1
    · simpa [Nat.mul_div_cancel p hq.pos, add_comm] using hG2
    · simpa [Nat.mul_div_cancel_left q hp.pos] using hG2
    · simpa [Nat.div_self (Nat.mul_pos hp.pos hq.pos)] using hG1

/-- If `e ∣ p - 1` and `p + q ≡ e (mod p² - 1)` then `gcd (p q + 1, p + q) = e`. -/
theorem gcd_eq_of_dvd {p q e : ℕ} (hep : (e : ℤ) ∣ (p : ℤ) - 1)
    (hpq : ((p : ℤ) ^ 2 - 1) ∣ (e : ℤ) - (p + q)) :
    Nat.gcd (p * q + 1) (p + q) = e := by
  have heM : (e : ℤ) ∣ (p : ℤ) ^ 2 - 1 :=
    hep.trans ⟨(p : ℤ) + 1, by ring⟩
  apply Nat.dvd_antisymm
  · set G := Nat.gcd (p * q + 1) (p + q) with hG
    have hG1 : (G : ℤ) ∣ (p : ℤ) * q + 1 := by
      exact_mod_cast Nat.gcd_dvd_left (p * q + 1) (p + q)
    have hG2 : (G : ℤ) ∣ (p : ℤ) + q := by
      exact_mod_cast Nat.gcd_dvd_right (p * q + 1) (p + q)
    have hGM : (G : ℤ) ∣ (p : ℤ) ^ 2 - 1 := by
      have h := (hG2.mul_left (p : ℤ)).sub hG1
      rwa [show (p : ℤ) * (p + q) - (p * q + 1) = (p : ℤ) ^ 2 - 1 by ring] at h
    have hGe : (G : ℤ) ∣ (e : ℤ) := by
      have h := hG2.add (hGM.trans hpq)
      rwa [show (p : ℤ) + q + (e - (p + q)) = e by ring] at h
    exact_mod_cast hGe
  · have h2 : (e : ℤ) ∣ (p : ℤ) + q := by
      have h := (dvd_refl (e : ℤ)).sub (heM.trans hpq)
      rwa [show (e : ℤ) - (e - (p + q)) = p + q by ring] at h
    have h1 : (e : ℤ) ∣ (p : ℤ) * q + 1 := by
      have h := (h2.mul_left (p : ℤ)).sub heM
      rwa [show (p : ℤ) * (p + q) - (p ^ 2 - 1) = p * q + 1 by ring] at h
    exact Nat.dvd_gcd (by exact_mod_cast h1) (by exact_mod_cast h2)

/-- For even `e ≥ 2`, the residue `A = 1 + 2e - e²` is coprime to `e (e - 1) (e + 1)`:
`A ≡ 1 (mod e)`, `A ≡ 2 (mod e - 1)`, `A ≡ -2 (mod e + 1)`, and `e ± 1` are odd. -/
theorem isCoprime_residue {e : ℕ} (he : Even e) :
    IsCoprime (1 + 2 * (e : ℤ) - (e : ℤ) ^ 2) ((e : ℤ) * ((e : ℤ) - 1) * ((e : ℤ) + 1)) := by
  obtain ⟨k, hk⟩ := he
  have hk' : (e : ℤ) = 2 * k := by rw [hk]; push_cast; ring
  refine IsCoprime.mul_right (IsCoprime.mul_right ?_ ?_) ?_
  · exact ⟨1, (e : ℤ) - 2, by ring⟩
  · exact ⟨k, k * ((e : ℤ) - 1) - 1, by linear_combination (-1 : ℤ) * hk'⟩
  · exact ⟨k, 1 + k * ((e : ℤ) - 3), by linear_combination hk'⟩

/-- **First prime (Dirichlet).** For even `e ≥ 2` there is a prime `p` with `e ∣ p - 1`
and `e - p` coprime to `p² - 1`. -/
theorem exists_prime_first {e : ℕ} (he : Even e) (h2 : 2 ≤ e) :
    ∃ p : ℕ, p.Prime ∧ (e : ℤ) ∣ (p : ℤ) - 1 ∧
      IsCoprime ((e : ℤ) - p) ((p : ℤ) ^ 2 - 1) := by
  set N : ℕ := e * (e - 1) * (e + 1) with hN
  have hNz : ((N : ℕ) : ℤ) = (e : ℤ) * ((e : ℤ) - 1) * ((e : ℤ) + 1) := by
    rw [hN]; push_cast [Nat.cast_sub (by omega : 1 ≤ e)]; ring
  haveI : NeZero N := ⟨by
    rw [hN]; exact Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (by omega)) (by omega)⟩
  set A : ℤ := 1 + 2 * (e : ℤ) - (e : ℤ) ^ 2 with hA
  have hcop : IsCoprime A (N : ℤ) := by rw [hNz]; exact isCoprime_residue he
  obtain ⟨p, -, hp, hpA⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (isUnit_intCast_of_isCoprime hcop) 0
  have hdiv : (N : ℤ) ∣ A - p := by
    rw [← Int.cast_natCast (R := ZMod N) p] at hpA
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hpA
  rw [hNz] at hdiv
  obtain ⟨r, hr⟩ : (e : ℤ) ∣ A - p := (Dvd.intro (((e : ℤ) - 1) * ((e : ℤ) + 1)) (by ring)).trans hdiv
  obtain ⟨s, hs⟩ : ((e : ℤ) - 1) ∣ A - p :=
    (Dvd.intro_left ((e : ℤ) * ((e : ℤ) + 1)) (by ring)).trans hdiv
  obtain ⟨t, ht⟩ : ((e : ℤ) + 1) ∣ A - p := Dvd.intro_left _ rfl |>.trans hdiv
  refine ⟨p, hp, ⟨2 - e - r, by linear_combination (-1 : ℤ) * hr⟩, ?_⟩
  have h1 : IsCoprime ((e : ℤ) - p) ((p : ℤ) - 1) :=
    ⟨(e : ℤ) - 1 + s, e + s, by linear_combination (-1 : ℤ) * hs⟩
  have h2 : IsCoprime ((e : ℤ) - p) ((p : ℤ) + 1) :=
    ⟨3 - e - t, 2 - e - t, by linear_combination ht⟩
  rw [show (p : ℤ) ^ 2 - 1 = ((p : ℤ) - 1) * ((p : ℤ) + 1) by ring]
  exact h1.mul_right h2

/-- **Part (i).** Every positive even `e` is `g m` for some composite `m`
(namely `m = p q` for the primes of `exists_prime_first` and Dirichlet). -/
theorem exists_isComposite_g_eq_of_even {e : ℕ} (he : Even e) (hpos : 0 < e) :
    ∃ m, IsComposite m ∧ g m = e := by
  have h2 : 2 ≤ e := by obtain ⟨k, rfl⟩ := he; omega
  obtain ⟨p, hp, hep, hcop⟩ := exists_prime_first he h2
  have hp2 := hp.two_le
  set N : ℕ := p ^ 2 - 1 with hN
  have hNz : ((N : ℕ) : ℤ) = (p : ℤ) ^ 2 - 1 := by
    rw [hN]; push_cast [Nat.cast_sub (Nat.one_le_pow _ _ hp.pos)]; ring
  haveI : NeZero N := ⟨by
    rw [hN]; have : 4 ≤ p ^ 2 := by nlinarith
    omega⟩
  rw [← hNz] at hcop
  obtain ⟨q, -, hq, hqA⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (isUnit_intCast_of_isCoprime hcop) 0
  have hdiv : (N : ℤ) ∣ ((e : ℤ) - p) - q := by
    rw [← Int.cast_natCast (R := ZMod N) q] at hqA
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hqA
  rw [hNz, sub_sub] at hdiv
  refine ⟨p * q, ⟨?_, Nat.not_prime_mul hp.ne_one hq.ne_one⟩, ?_⟩
  · have := hq.two_le; nlinarith
  · rw [g_prime_mul hp hq]
    exact gcd_eq_of_dvd hep hdiv

/-! ## The conjecture -/

/-- **Wilson's conjecture, part (ii) (A143772, Robert G. Wilson v, Sep 08 2008).**
The only odd terms are `1` and `3`: if `m` is composite and `g m` is odd then
`g m ∈ {1, 3}`. -/
theorem odd_term_eq_one_or_three {n : ℕ} (ho : Odd (a n)) : a n = 1 ∨ a n = 3 := by
  have hc : IsComposite (Nat.nth IsComposite n) :=
    Nat.nth_mem_of_infinite infinite_setOf_isComposite n
  exact g_eq_one_or_three_of_odd (by have := hc.1; omega) ho

/-- **Wilson's conjecture, part (i) (A143772, Robert G. Wilson v, Sep 08 2008).**
Every positive even number is a term of A143772. -/
theorem even_mem_range_a {e : ℕ} (he : Even e) (hpos : 0 < e) : e ∈ Set.range a := by
  rw [range_a_eq_image]
  obtain ⟨m, hm, hg⟩ := exists_isComposite_g_eq_of_even he hpos
  exact ⟨m, hm, hg⟩

/-- The range of A143772 is `{1,3}` together with the positive even integers
(Wilson's conjecture). Zero never occurs; `1 = a(0)` and `3 = a(2)`. -/
theorem range_a_eq : Set.range a = {1, 3} ∪ {e | Even e ∧ 0 < e} := by
  rw [range_a_eq_image]
  ext v
  constructor
  · rintro ⟨m, hm, rfl⟩
    have hm0 : m ≠ 0 := by have := hm.1; omega
    rcases Nat.even_or_odd (g m) with he | ho
    · exact Or.inr ⟨he, g_pos hm0⟩
    · rcases g_eq_one_or_three_of_odd hm0 ho with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
  · rintro ((rfl | rfl) | ⟨he, hpos⟩)
    · exact ⟨4, by decide, by decide⟩
    · exact ⟨8, by decide, by decide⟩
    · exact exists_isComposite_g_eq_of_even he hpos

end Candidates.A143772GcdRangesOver
