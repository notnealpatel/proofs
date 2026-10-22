/-
Squarefree members of OEIS A068991 and Bernoulli denominators.
The entry (Benoit Cloitre, Apr 06 2002) asks whether a squarefree k with
∑_{d∣k} σ(d)/φ(d) integral divides the denominator of B_{2k}.
Here “contains k” means divisibility, as in the entry's example.

The proof writes the sum as ∏_{p∣k} 2p/(p-1), obtains
∏_{p∣k}(p-1) ∣ 2^ω(k) k, and derives p-1 ∣ 2k for every prime p∣k.
The exceptional 2-adic configuration forces primes 7 and 43 and hence 9∣k,
contrary to squarefreeness. Von Staudt–Clausen then gives the denominator result.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A068991SquarefreeSuchSum

/-! ## Definition layer -/

/-- `S k = ∑_{d ∣ k} σ(d)/φ(d)`, the sum in the name of OEIS A068991,
computed in `ℚ`. -/
def S (k : ℕ) : ℚ :=
  ∑ d ∈ k.divisors, (ArithmeticFunction.sigma 1 d : ℚ) / (Nat.totient d : ℚ)

/-- Membership in OEIS A068991: `k` is a positive integer and `S k` is an
integer.  The sequence lists positive integers only, so `0` is excluded
explicitly (otherwise `S 0 = 0` would admit it). -/
def IsA068991 (k : ℕ) : Prop :=
  0 < k ∧ ∃ z : ℤ, S k = z

/-- Being an integer is the same as having denominator `1`.  This makes
membership decidable for examples. -/
theorem exists_intCast_eq_iff_den_eq_one (q : ℚ) : (∃ z : ℤ, q = z) ↔ q.den = 1 := by
  constructor
  · rintro ⟨z, rfl⟩
    exact Rat.den_intCast z
  · intro h
    exact ⟨q.num, (Rat.coe_int_num_of_den_eq_one h).symm⟩

/-! ### Examples -/

example : S 1 = 1 := by decide +kernel
example : S 2 = 4 := by decide +kernel
example : S 6 = 12 := by decide +kernel
example : S 4 = 15 / 2 := by decide +kernel

/-- The members below `31` are exactly the listed terms `1, 2, 3, 6, 10, 21, 30`
(and `0`, which `IsA068991` excludes by its positivity clause). -/
example : (List.range 31).filter (fun k => (S k).den = 1) = [0, 1, 2, 3, 6, 10, 21, 30] := by
  decide +kernel

example : IsA068991 30 :=
  ⟨by norm_num, (exists_intCast_eq_iff_den_eq_one _).mpr (by decide +kernel)⟩

example : ¬ IsA068991 4 := fun h =>
  absurd ((exists_intCast_eq_iff_den_eq_one _).mp h.2) (by decide +kernel)

example : ¬ IsA068991 0 := fun h => absurd h.1 (lt_irrefl 0)

/-- The hypotheses of the conjecture hold jointly at `k = 30`. -/
example : Squarefree 30 ∧ IsA068991 30 :=
  ⟨by decide +kernel, ⟨by norm_num, (exists_intCast_eq_iff_den_eq_one _).mpr (by decide +kernel)⟩⟩

/-! ## Step 1: the product formula -/

/-- The arithmetic function `d ↦ σ(d)/φ(d)` over `ℚ`. -/
noncomputable def sigmaDivTotient : ArithmeticFunction ℚ :=
  ⟨fun d => (ArithmeticFunction.sigma 1 d : ℚ) / (Nat.totient d : ℚ), by simp⟩

/-- `σ/φ` is multiplicative, since both `σ` and `φ` are. -/
theorem isMultiplicative_sigmaDivTotient : sigmaDivTotient.IsMultiplicative := by
  refine ⟨by simp [sigmaDivTotient], fun {m n} hmn => ?_⟩
  simp only [sigmaDivTotient, ArithmeticFunction.coe_mk]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hmn, Nat.totient_mul hmn]
  push_cast
  rw [mul_div_mul_comm]

/-- For a prime `p`, `1 + σ(p)/φ(p) = 2p/(p-1)`. -/
theorem one_add_sigmaDivTotient_prime {p : ℕ} (hp : p.Prime) :
    1 + sigmaDivTotient p = 2 * p / ((p : ℚ) - 1) := by
  have h1 : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hne : (p : ℚ) - 1 ≠ 0 := by linarith
  have hs : ArithmeticFunction.sigma 1 p = p + 1 := by
    have hpow := ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) hp
    rw [pow_one] at hpow
    rw [hpow, Finset.sum_range_succ, Finset.sum_range_one]
    ring
  simp only [sigmaDivTotient, ArithmeticFunction.coe_mk]
  rw [Nat.totient_prime hp, hs, Nat.cast_sub hp.one_le]
  push_cast
  rw [eq_div_iff hne, add_mul, div_mul_cancel₀ _ hne]
  ring

/-- For squarefree `k`, `S k = ∏_{p ∣ k} 2p/(p-1)`. -/
theorem S_eq_prod_primeFactors {k : ℕ} (hk : Squarefree k) :
    S k = ∏ p ∈ k.primeFactors, 2 * (p : ℚ) / ((p : ℚ) - 1) := by
  rw [← Finset.prod_congr rfl fun p hp =>
      one_add_sigmaDivTotient_prime (Nat.prime_of_mem_primeFactors hp),
    isMultiplicative_sigmaDivTotient.prodPrimeFactors_one_add_of_squarefree hk]
  rfl

/-! ## Step 2: integrality as a divisibility -/

/-- If `k` is a squarefree member of A068991, then `∏_{p ∣ k} (p - 1)` divides
`2^ω(k) · k`.  (`p - 1` is natural subtraction at a prime `p ≥ 2`, so it is
the true value.) -/
theorem prod_sub_one_dvd_of_isA068991 {k : ℕ} (hk : Squarefree k) (hmem : IsA068991 k) :
    ∏ p ∈ k.primeFactors, (p - 1) ∣ 2 ^ k.primeFactors.card * k := by
  obtain ⟨-, z, hz⟩ := hmem
  rw [S_eq_prod_primeFactors hk, Finset.prod_div_distrib, Finset.prod_mul_distrib,
    Finset.prod_const] at hz
  have hD : (∏ p ∈ k.primeFactors, ((p : ℚ) - 1)) =
      ((∏ p ∈ k.primeFactors, (p - 1) : ℕ) : ℚ) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
  have hprod : (∏ p ∈ k.primeFactors, (p : ℚ)) = k := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hk]
  have hDne : ((∏ p ∈ k.primeFactors, (p - 1) : ℕ) : ℚ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Finset.prod_ne_zero_iff]
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  rw [hD, hprod, div_eq_iff hDne] at hz
  have hzZ : ((2 ^ k.primeFactors.card * k : ℕ) : ℤ) =
      z * ((∏ p ∈ k.primeFactors, (p - 1) : ℕ) : ℤ) := by
    exact_mod_cast hz
  exact Int.natCast_dvd_natCast.mp ⟨z, by rw [hzZ, mul_comm]⟩

/-! ## Step 3: the arithmetic core -/

/-- Each factor `p - 1` of `D = ∏_{q ∣ k} (q - 1)` divides `2^ω(k) · k` when `D` does. -/
theorem sub_one_dvd_of_mem {k p : ℕ}
    (hD : ∏ q ∈ k.primeFactors, (q - 1) ∣ 2 ^ k.primeFactors.card * k)
    (hp : p ∈ k.primeFactors) : p - 1 ∣ 2 ^ k.primeFactors.card * k :=
  (Finset.dvd_prod_of_mem _ hp).trans hD

/-- An odd divisor of `2^w · k` divides `k`. -/
theorem dvd_of_odd_of_dvd_two_pow_mul {m w k : ℕ} (hm : Odd m) (h : m ∣ 2 ^ w * k) :
    m ∣ k :=
  (Nat.Coprime.pow_right w hm.coprime_two_right).dvd_of_dvd_mul_left h

/-- The 2-adic valuation of `2^a · m` with `m` odd is `a`. -/
theorem factorization_two_two_pow_mul_odd {a m : ℕ} (hm : Odd m) :
    (2 ^ a * m).factorization 2 = a := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two, smul_eq_mul, mul_one,
    Nat.factorization_eq_zero_of_not_dvd (by rw [Nat.odd_iff] at hm; omega), add_zero]

/-- The divisors of `21` are `1, 3, 7, 21`. -/
theorem eq_of_dvd_twentyOne {m : ℕ} (h : m ∣ 21) : m = 1 ∨ m = 3 ∨ m = 7 ∨ m = 21 := by
  have hle : m ≤ 21 := Nat.le_of_dvd (by norm_num) h
  interval_cases m <;> omega

/-- Finite check: a prime `t ∉ {3, 7}` with `t - 1 = 2^a · m`, `a ∈ {1, 3}`,
`m ∣ 21`, is `43` with `m = 21`. -/
theorem eq_fortyThree {t a m : ℕ} (ht : t.Prime) (ht3 : t ≠ 3) (ht7 : t ≠ 7)
    (ha : a = 1 ∨ a = 3) (hm : m = 1 ∨ m = 3 ∨ m = 7 ∨ m = 21) (htm : t - 1 = 2 ^ a * m) :
    t = 43 ∧ m = 21 := by
  rw [Nat.sub_eq_iff_eq_add ht.one_le] at htm
  subst htm
  rcases ha with rfl | rfl <;> rcases hm with rfl | rfl | rfl | rfl <;>
    first
    | exact ⟨rfl, rfl⟩
    | exact absurd rfl ht3
    | exact absurd rfl ht7
    | (exfalso; norm_num at ht)

/-- **The delicate case is impossible.** Let `k` be squarefree with
`∏_{p ∣ k} (p - 1) ∣ 2^ω(k) · k`.  There is no prime `p0 ∣ k` with
`v₂(p0 - 1) = 3` such that every other odd prime `r ∣ k` has `v₂(r - 1) ≤ 1`.

Proof: let `t` be the least odd prime factor of `k` outside `{3, 7}` (`p0` is
one).  The odd part `m` of `t - 1` divides `k`, and its prime factors are
smaller odd prime factors of `k`, so they lie in `{3, 7}` and `m ∣ 21`.  Since
`v₂(t - 1) ∈ {1, 3}`, the finite check forces `t = 43`.  Then `7 ∣ k` and
`9 ∣ (7 - 1)(43 - 1) ∣ 2^ω(k) · k`, contradicting squarefreeness. -/
theorem false_of_bad_config (k : ℕ) (hk : Squarefree k)
    (hD : ∏ p ∈ k.primeFactors, (p - 1) ∣ 2 ^ k.primeFactors.card * k)
    {p0 : ℕ} (hp0 : p0 ∈ k.primeFactors) (hv0 : (p0 - 1).factorization 2 = 3)
    (hothers : ∀ r ∈ k.primeFactors, r ≠ 2 → r ≠ p0 → (r - 1).factorization 2 ≤ 1) :
    False := by
  have hk0 : k ≠ 0 := hk.ne_zero
  set P := k.primeFactors.filter (fun q => q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 7)
  have hp0P : p0 ∈ P := by
    refine Finset.mem_filter.mpr ⟨hp0, ?_, ?_, ?_⟩ <;> rintro rfl
    · rw [show 2 - 1 = 2 ^ 0 * 1 from rfl, factorization_two_two_pow_mul_odd (by decide)] at hv0
      omega
    · rw [show 3 - 1 = 2 ^ 1 * 1 from rfl, factorization_two_two_pow_mul_odd (by decide)] at hv0
      omega
    · rw [show 7 - 1 = 2 ^ 1 * 3 from rfl, factorization_two_two_pow_mul_odd (by decide)] at hv0
      omega
  set t := P.min' ⟨p0, hp0P⟩
  have htP : t ∈ P := Finset.min'_mem _ _
  have htmin : ∀ q ∈ P, t ≤ q := fun q hq => Finset.min'_le _ _ hq
  obtain ⟨htk, ht2, ht3, ht7⟩ := Finset.mem_filter.mp htP
  have htprime : t.Prime := Nat.prime_of_mem_primeFactors htk
  have htodd : Odd t := htprime.odd_of_ne_two ht2
  obtain ⟨a, m, hm, htm⟩ := Nat.exists_eq_two_pow_mul_odd (n := t - 1)
    (by have := htprime.two_le; omega)
  have ha : (t - 1).factorization 2 = a := by rw [htm, factorization_two_two_pow_mul_odd hm]
  have ha13 : a = 1 ∨ a = 3 := by
    by_cases htp0 : t = p0
    · right; rw [← ha, htp0, hv0]
    · left
      have hle := hothers t htk ht2 htp0
      rw [ha] at hle
      rcases Nat.lt_or_ge a 1 with ha0 | ha1
      · have ha0' : a = 0 := by omega
        rw [ha0', pow_zero, one_mul] at htm
        rw [Nat.odd_iff] at htodd hm
        omega
      · omega
  have hmt : m ∣ t - 1 := Dvd.intro_left _ htm.symm
  have hmk : m ∣ k := dvd_of_odd_of_dvd_two_pow_mul hm (hmt.trans (sub_one_dvd_of_mem hD htk))
  have hmle : m ≤ t - 1 := by
    rw [htm]; exact Nat.le_mul_of_pos_left m (by positivity)
  have hm21 : m ∣ 21 := by
    have hmsq : Squarefree m := hk.squarefree_of_dvd hmk
    rw [← Nat.prod_primeFactors_of_squarefree hmsq]
    have hsub : m.primeFactors ⊆ {3, 7} := by
      intro q hq
      have hqprime := Nat.prime_of_mem_primeFactors hq
      have hqm := Nat.dvd_of_mem_primeFactors hq
      have hqk : q ∈ k.primeFactors := Nat.mem_primeFactors.mpr ⟨hqprime, hqm.trans hmk, hk0⟩
      have hq2 : q ≠ 2 := by
        rintro rfl
        rw [Nat.odd_iff] at hm
        omega
      have hqlt : q < t := by
        have hqle : q ≤ m := Nat.le_of_dvd hm.pos hqm
        have ht1 : 2 ≤ t := htprime.two_le
        omega
      by_contra hq37
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq37
      have hqP : q ∈ P := Finset.mem_filter.mpr ⟨hqk, hq2, hq37.1, hq37.2⟩
      have := htmin q hqP
      omega
    calc ∏ q ∈ m.primeFactors, q ∣ ∏ q ∈ ({3, 7} : Finset ℕ), q :=
          Finset.prod_dvd_prod_of_subset _ _ _ hsub
      _ = 21 := by decide
  obtain ⟨ht43, hm21'⟩ := eq_fortyThree htprime ht3 ht7 ha13 (eq_of_dvd_twentyOne hm21) htm
  have h7k : 7 ∈ k.primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨by norm_num, ?_, hk0⟩
    refine dvd_of_odd_of_dvd_two_pow_mul (w := k.primeFactors.card) (by decide) ?_
    refine Dvd.dvd.trans ?_ (sub_one_dvd_of_mem hD htk)
    rw [ht43]
    norm_num
  have h252 : (7 - 1) * (43 - 1) ∣ 2 ^ k.primeFactors.card * k := by
    have hsub : ({7, 43} : Finset ℕ) ⊆ k.primeFactors := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact h7k
      · rw [← ht43]; exact htk
    have hdvd := Finset.prod_dvd_prod_of_subset _ _ (fun q => q - 1) hsub
    rw [Finset.prod_pair (by norm_num)] at hdvd
    exact hdvd.trans hD
  have h9 : 3 * 3 ∣ k :=
    dvd_of_odd_of_dvd_two_pow_mul (by decide) ((by norm_num : 3 * 3 ∣ (7 - 1) * (43 - 1)).trans h252)
  have hunit := hk 3 h9
  norm_num at hunit

/-- If `f ≥ 1` on `s \ t` and `t ⊆ s`, then
`∑_{t} f + (|s| - |t|) ≤ ∑_{s} f`. -/
theorem sum_sub_card_le {s t : Finset ℕ} (f : ℕ → ℕ) (hts : t ⊆ s)
    (h1 : ∀ x ∈ s, x ∉ t → 1 ≤ f x) :
    ∑ x ∈ t, f x + (s.card - t.card) ≤ ∑ x ∈ s, f x := by
  rw [← Finset.sum_sdiff hts, ← Finset.card_sdiff_of_subset hts, add_comm]
  gcongr
  calc (s \ t).card = ∑ x ∈ s \ t, 1 := by simp
    _ ≤ ∑ x ∈ s \ t, f x := Finset.sum_le_sum fun x hx => by
        rw [Finset.mem_sdiff] at hx
        exact h1 x hx.1 hx.2

/-- 2-adic form of `D ∣ 2^ω(k) · k`:
`∑_{p ∣ k} v₂(p - 1) ≤ ω(k) + v₂(k)`. -/
theorem sum_factorization_two_le (k : ℕ) (hk0 : k ≠ 0)
    (hD : ∏ p ∈ k.primeFactors, (p - 1) ∣ 2 ^ k.primeFactors.card * k) :
    ∑ p ∈ k.primeFactors, (p - 1).factorization 2 ≤ k.primeFactors.card + k.factorization 2 := by
  have hne : ∀ p ∈ k.primeFactors, p - 1 ≠ 0 := fun p hp => by
    have := (Nat.prime_of_mem_primeFactors hp).two_le; omega
  have hpos : 2 ^ k.primeFactors.card * k ≠ 0 := by positivity
  have hle := (Nat.factorization_le_iff_dvd (Finset.prod_ne_zero_iff.mpr hne) hpos).mpr hD 2
  rw [Nat.factorization_prod hne, Finset.sum_apply', Nat.factorization_mul (by positivity) hk0,
    Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply,
    Nat.Prime.factorization_self Nat.prime_two, smul_eq_mul, mul_one] at hle
  exact hle

/-- For an odd prime `p`, `v₂(p - 1) ≥ 1`. -/
theorem one_le_factorization_two_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    1 ≤ (p - 1).factorization 2 := by
  have hodd := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have h2 := hp.two_le
  rw [← Nat.prime_two.pow_dvd_iff_le_factorization (by omega), pow_one]
  omega

/-- For `q ≠ 2`, `v_q(2^w · k) = v_q(k)`. -/
theorem factorization_two_pow_mul_of_ne {w k q : ℕ} (hk0 : k ≠ 0) (hq : q ≠ 2) :
    (2 ^ w * k).factorization q = k.factorization q := by
  rw [Nat.factorization_mul (by positivity) hk0, Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.Prime.factorization Nat.prime_two]
  simp [Ne.symm hq]

/-- **2-adic bound.** If `k` is squarefree and `∏_{p ∣ k} (p - 1) ∣ 2^ω(k) · k`,
then `v₂(p - 1) ≤ v₂(2k)` for every prime `p ∣ k`. -/
theorem factorization_two_sub_one_le (k : ℕ) (hk : Squarefree k)
    (hD : ∏ p ∈ k.primeFactors, (p - 1) ∣ 2 ^ k.primeFactors.card * k) :
    ∀ p ∈ k.primeFactors, (p - 1).factorization 2 ≤ (2 * k).factorization 2 := by
  intro p hp
  have hk0 : k ≠ 0 := hk.ne_zero
  have h2k : (2 * k).factorization 2 = 1 + k.factorization 2 := by
    rw [Nat.factorization_mul two_ne_zero hk0, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two]
  rw [h2k]
  set v : ℕ → ℕ := fun q => (q - 1).factorization 2 with hv
  have hsum : ∑ x ∈ k.primeFactors, v x ≤ k.primeFactors.card + k.factorization 2 :=
    sum_factorization_two_le k hk0 hD
  show v p ≤ _
  have hv1 : ∀ x ∈ k.primeFactors, x ≠ 2 → 1 ≤ v x := fun x hx hx2 =>
    one_le_factorization_two_sub_one (Nat.prime_of_mem_primeFactors hx) hx2
  have hv2 : v 2 = 0 := by simp [hv]
  by_cases h2 : 2 ∈ k.primeFactors
  · -- `k` even: `k.factorization 2 = 1`
    have hk2 : k.factorization 2 = 1 :=
      Nat.factorization_eq_one_of_squarefree hk Nat.prime_two (Nat.dvd_of_mem_primeFactors h2)
    rw [hk2]
    by_cases hp2 : p = 2
    · subst hp2; show v 2 ≤ _; omega
    by_contra hbig
    have hbig' : 3 ≤ v p := by omega
    have hsub2 : ({2, p} : Finset ℕ) ⊆ k.primeFactors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      exacts [h2, hp]
    have hcard2 : ({2, p} : Finset ℕ).card = 2 := Finset.card_pair (Ne.symm hp2)
    have hw2 := Finset.card_le_card hsub2
    have hle2 := sum_sub_card_le v hsub2 (fun x hx hxt => hv1 x hx (by
      rintro rfl; simp at hxt))
    rw [Finset.sum_pair (Ne.symm hp2), hcard2] at hle2
    refine false_of_bad_config k hk hD hp (p0 := p) ?_ ?_
    · show v p = 3
      omega
    · intro r hr hr2 hrp
      show v r ≤ 1
      have hsub3 : ({2, p, r} : Finset ℕ) ⊆ k.primeFactors := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        exacts [h2, hp, hr]
      have hcard3 : ({2, p, r} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [Ne.symm hp2, Ne.symm hr2]),
          Finset.card_pair (Ne.symm hrp)]
      have hw3 := Finset.card_le_card hsub3
      have hle3 := sum_sub_card_le v hsub3 (fun x hx hxt => hv1 x hx (by
        rintro rfl; simp at hxt))
      rw [Finset.sum_insert (by simp [Ne.symm hp2, Ne.symm hr2]),
        Finset.sum_pair (Ne.symm hrp), hcard3] at hle3
      omega
  · -- `k` odd: every prime factor is odd
    have hk2 : k.factorization 2 = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      right; left
      intro h
      exact h2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h, hk0⟩)
    have hp2 : p ≠ 2 := by rintro rfl; exact h2 hp
    have hsub1 : ({p} : Finset ℕ) ⊆ k.primeFactors := Finset.singleton_subset_iff.mpr hp
    have hw1 := Finset.card_le_card hsub1
    have hle1 := sum_sub_card_le v hsub1 (fun x hx _ => hv1 x hx (by
      rintro rfl; exact h2 hx))
    rw [Finset.sum_singleton, Finset.card_singleton] at hle1
    rw [Finset.card_singleton] at hw1
    show v p ≤ _
    omega

/-- **Arithmetic core.** If `k` is squarefree and `∏_{p ∣ k} (p - 1) ∣ 2^ω(k) · k`,
then `p - 1 ∣ 2k` for every prime `p ∣ k`.  Odd primes are handled by the
divisibility directly; the prime `2` by `factorization_two_sub_one_le`. -/
theorem sub_one_dvd_two_mul_of_dvd (k : ℕ) (hk : Squarefree k)
    (hD : ∏ p ∈ k.primeFactors, (p - 1) ∣ 2 ^ k.primeFactors.card * k) :
    ∀ p ∈ k.primeFactors, p - 1 ∣ 2 * k := by
  intro p hp
  have hk0 : k ≠ 0 := hk.ne_zero
  have hp1 : p - 1 ≠ 0 := by
    have := (Nat.prime_of_mem_primeFactors hp).two_le; omega
  rw [← Nat.factorization_le_iff_dvd hp1 (by positivity)]
  intro q
  by_cases hq : q = 2
  · subst hq
    exact factorization_two_sub_one_le k hk hD p hp
  · have h := (Nat.factorization_le_iff_dvd hp1 (by positivity)).mpr (sub_one_dvd_of_mem hD hp) q
    rw [factorization_two_pow_mul_of_ne hk0 hq] at h
    rw [show 2 * k = 2 ^ 1 * k by ring, factorization_two_pow_mul_of_ne hk0 hq]
    exact h

/-! ## Step 4: von Staudt–Clausen -/

/-- **From von Staudt–Clausen.** If `p` is prime, `p - 1 ∣ 2k`, and `0 < k`,
then `p` divides the denominator of `B_{2k}`. -/
theorem prime_dvd_den_bernoulli {k p : ℕ} (hp : p.Prime) (hpk : p - 1 ∣ 2 * k) (hk : 0 < k) :
    p ∣ (bernoulli (2 * k)).den := by
  obtain ⟨N, hN⟩ := Bernoulli.vonStaudt_clausen k
  set T := (Finset.range (2 * k + 2)).filter (fun q => q.Prime ∧ q - 1 ∣ 2 * k) with hT
  have hpT : p ∈ T := by
    have hle : p - 1 ≤ 2 * k := Nat.le_of_dvd (by omega) hpk
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp, hpk⟩
  rw [← Finset.add_sum_erase T _ hpT] at hN
  set R := ∑ q ∈ T.erase p, (1 : ℚ) / q with hR
  have h1p : (1 : ℚ) / p = N + (-bernoulli (2 * k) + -R) := by rw [hN]; ring
  have hpden : ((1 : ℚ) / p).den = p := by simp [hp.ne_zero]
  have hdvd : p ∣ (bernoulli (2 * k)).den * R.den := by
    have h := Rat.add_den_dvd (-bernoulli (2 * k)) (-R)
    rw [← Rat.intCast_add_den N, ← h1p, hpden, Rat.neg_den, Rat.neg_den] at h
    exact h
  have hRden : R.den ∣ ∏ q ∈ T.erase p, q := by
    refine (Finset.Rat.den_sum_dvd_prod_den _ _).trans (dvd_of_eq (Finset.prod_congr rfl fun q hq => ?_))
    have hq := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hq)).2.1
    simp [hq.ne_zero]
  rcases (Nat.Prime.dvd_mul hp).mp (hdvd.trans (mul_dvd_mul_left _ hRden)) with h | h
  · exact h
  · obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp h
    have hqT := Finset.mem_erase.mp hq
    have hqprime := (Finset.mem_filter.mp hqT.2).2.1
    exact absurd ((Nat.prime_dvd_prime_iff_eq hp hqprime).mp hpq).symm hqT.1

/-! ## The conjecture -/

/-- **Prime-divisor consequence.** If `k` is a squarefree member of A068991,
then `p - 1 ∣ 2k` for every prime `p ∣ k`. -/
theorem sub_one_dvd_two_mul_of_isA068991 {k : ℕ} (hmem : IsA068991 k) (hk : Squarefree k) :
    ∀ p ∈ k.primeFactors, p - 1 ∣ 2 * k :=
  sub_one_dvd_two_mul_of_dvd k hk (prod_sub_one_dvd_of_isA068991 hk hmem)

/-- A squarefree positive member `k` of A068991 divides the denominator
of `B_{2k}`. At this even index the two Bernoulli sign conventions agree. -/
theorem a068991_conjecture (k : ℕ) (hmem : IsA068991 k) (hk : Squarefree k) :
    k ∣ (bernoulli (2 * k)).den := by
  have hdvd := sub_one_dvd_two_mul_of_isA068991 hmem hk
  have hprod : ∏ p ∈ k.primeFactors, p ∣ (bernoulli (2 * k)).den :=
    Finset.prod_primes_dvd _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime)
      fun p hp => prime_dvd_den_bernoulli (Nat.prime_of_mem_primeFactors hp) (hdvd p hp) hmem.1
  rwa [Nat.prod_primeFactors_of_squarefree hk] at hprod

end Candidates.A068991SquarefreeSuchSum
