/-
# McCranie / Stephan jump conditions at shift 12: one-sided semiprime case

## Source

arXiv 2606.10331, Himaghna Roy Choudhury and Shicheng Wei, "Prime Quadruplets and
Jump Conditions on Arithmetic Functions" (OEIS A056777, McCranie and Stephan).

* Conjecture 1.1 (McCranie), verbatim: "Every composite integer $n$ satisfying both
  $\varphi(n+12) = \varphi(n) + 12$ and $\sigma(n+12) = \sigma(n) + 12$ is of the form
  $n=p(p+8)$, where $(p,p+2,p+6,p+8)$ is a prime quadruplet with $p\ge5$."  Open.
* Theorem 2.2, verbatim: "Suppose $n = pq$ and $n+12 = p'q'$ are both products of two
  distinct primes (with $p < q$ and $p' < q'$). Then both jump conditions
  $\varphi(n+12) - \varphi(n) = 12, \sigma(n+12) - \sigma(n) = 12$ hold if and only if
  $p \ge 5$, $q = p+8$, and $\{p', q'\} = \{p+2, p+6\}$."  Proved in the paper.
* Theorem 3.1: no prime power $p^k$, $k \ge 2$, satisfies both jump conditions.  Proved
  in the paper; it uses $T(m) = (\sigma(m) - m) - (m - \varphi(m))$.

## Target (a4-1), recorded 2026-10-21

A one-sided strengthening of Theorem 2.2: "If n is a solution and EITHER n OR n+12 is a
squarefree semiprime, then n = p(p+8) for a prime quadruplet. Also, no solution has n or
n+12 equal to a prime square."  The paper requires both sides to be semiprimes; this
one-sided form is not stated there (status at triage: open).  Here it is proved.

## Mechanism

`defect m := ∑_{e ∣ m, e < m} (e - φ e)` equals the paper's `T(m) = σ(m) + φ(m) - 2m`
(`sigma_add_totient_eq`, from `∑_{e ∣ m} φ e = m`).  Each summand is `0` at `e = 1`, `1`
at a prime and at least `2` at a composite, which gives `defect m = 2 ↔ m` is a
squarefree semiprime and `defect m = 1 ↔ m` is a prime square (Cloitre's remark in OEIS
A006881).  The jump conditions say exactly `defect (n + 12) = defect n`, so one
semiprime side forces the other and Theorem 2.2 applies; `q² + 12 = r²` has no
solution in primes.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.McCranieQuadrupletJumpSemiprime

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- The two jump conditions of arXiv 2606.10331 at shift `12`:
`φ(n+12) = φ(n) + 12` and `σ(n+12) = σ(n) + 12`. -/
def JumpCondition12 (n : ℕ) : Prop :=
  Nat.totient (n + 12) = Nat.totient n + 12 ∧ σ 1 (n + 12) = σ 1 n + 12

/-- `m` is a squarefree semiprime: a product of two distinct primes. -/
def IsSqfreeSemiprime (m : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ m = p * q

/-- `(p, p+2, p+6, p+8)` is a prime quadruplet (all four entries prime). -/
def IsPrimeQuadruplet (p : ℕ) : Prop :=
  p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧ (p + 8).Prime

/-- The defect `∑_{e ∣ m, e < m} (e - φ e)`.  The truncated subtraction is harmless since
`φ e ≤ e` (`Nat.totient_le`); by `sigma_add_totient_eq` this is the paper's
`T(m) = σ(m) + φ(m) - 2m`. -/
def defect (m : ℕ) : ℕ :=
  ∑ e ∈ m.properDivisors, (e - Nat.totient e)

/-- `σ(m) + φ(m) = 2m + defect m` for every `m` (both sides vanish at `m = 0`). -/
theorem sigma_add_totient_eq (m : ℕ) :
    σ 1 m + Nat.totient m = 2 * m + defect m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [defect]
  have hsig : σ 1 m = (∑ e ∈ m.properDivisors, e) + m := by
    rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  have htot : (∑ e ∈ m.properDivisors, Nat.totient e) + Nat.totient m = m := by
    have hsum := Nat.sum_totient m
    rw [← Nat.insert_self_properDivisors hm.ne',
      Finset.sum_insert Nat.self_notMem_properDivisors] at hsum
    omega
  have hsplit : (∑ e ∈ m.properDivisors, e) =
      (∑ e ∈ m.properDivisors, Nat.totient e) + defect m := by
    rw [defect, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    have := Nat.totient_le e
    omega
  omega

/-- A prime `e` contributes `e - φ e = 1` to the defect. -/
theorem term_eq_one_of_prime {e : ℕ} (he : e.Prime) : e - Nat.totient e = 1 := by
  rw [Nat.totient_prime he]
  have := he.two_le
  omega

/-- A composite `e ≥ 2` contributes `e - φ e ≥ 2` to the defect. -/
theorem two_le_term {e : ℕ} (he : 2 ≤ e) (hnp : ¬ e.Prime) : 2 ≤ e - Nat.totient e := by
  have hlt := Nat.totient_lt e (by omega)
  have hne : Nat.totient e ≠ e - 1 := fun h => hnp ((Nat.totient_eq_iff_prime (by omega)).1 h)
  omega

/-- A prime has defect `0` (its only proper divisor is `1`). -/
theorem defect_of_prime {p : ℕ} (hp : p.Prime) : defect p = 0 := by
  simp [defect, hp.properDivisors]

/-- `defect 0 = 0`. -/
theorem defect_zero : defect 0 = 0 := by simp [defect]

/-- `defect 1 = 0`. -/
theorem defect_one : defect 1 = 0 := by simp [defect]

/-- Two distinct proper divisors contribute at most the whole defect. -/
theorem pair_le_defect {m a b : ℕ} (ha : a ∈ m.properDivisors) (hb : b ∈ m.properDivisors)
    (hab : a ≠ b) : (a - Nat.totient a) + (b - Nat.totient b) ≤ defect m := by
  rw [← Finset.sum_pair (f := fun e => e - Nat.totient e) hab, defect]
  refine Finset.sum_le_sum_of_subset ?_
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  exacts [ha, hb]

/-- `σ(p) = p + 1` for a prime `p`. -/
theorem sigma_one_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  have := sigma_one_apply_prime_pow (i := 1) hp
  simp only [pow_one] at this
  rw [this]
  simp [Finset.sum_range_succ, add_comm]

/-- A squarefree semiprime `p q` has defect `2`. -/
theorem defect_mul_of_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    defect (p * q) = 2 := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  have hs : σ 1 (p * q) = (p + 1) * (q + 1) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_prime hp, sigma_one_prime hq]
  have ht : Nat.totient (p * q) = (p - 1) * (q - 1) := by
    rw [Nat.totient_mul hcop, Nat.totient_prime hp, Nat.totient_prime hq]
  have hid := sigma_add_totient_eq (p * q)
  rw [hs, ht] at hid
  obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, q = b + 1 := ⟨q - 1, by have := hq.one_lt; omega⟩
  simp only [Nat.add_sub_cancel] at hid
  nlinarith

/-- A prime square `p ^ 2` has defect `1`. -/
theorem defect_sq {p : ℕ} (hp : p.Prime) : defect (p ^ 2) = 1 := by
  have hs : σ 1 (p ^ 2) = 1 + p + p ^ 2 := by
    rw [sigma_one_apply_prime_pow hp]
    simp [Finset.sum_range_succ]
  have ht : Nat.totient (p ^ 2) = p * (p - 1) := by
    rw [Nat.totient_prime_pow hp (by norm_num)]
    simp
  have hid := sigma_add_totient_eq (p ^ 2)
  rw [hs, ht] at hid
  obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
  simp only [Nat.add_sub_cancel] at hid
  nlinarith

/-- If `defect m ≤ 2`, every proper divisor of `m` is `1` or prime (a composite proper
divisor and its least prime factor would contribute at least `3`). -/
theorem properDivisor_eq_one_or_prime {m e : ℕ} (hd : defect m ≤ 2)
    (he : e ∈ m.properDivisors) : e = 1 ∨ e.Prime := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨he1, hnp⟩ := hcon
  obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.1 he
  have hm : m ≠ 0 := by omega
  have he0 : e ≠ 0 := by rintro rfl; exact hm (Nat.eq_zero_of_zero_dvd hdvd)
  have he2 : 2 ≤ e := by omega
  have hr : e.minFac < e := (Nat.not_prime_iff_minFac_lt he2).1 hnp
  have hrp : e.minFac.Prime := Nat.minFac_prime (by omega)
  have hrmem : e.minFac ∈ m.properDivisors :=
    Nat.mem_properDivisors.2 ⟨(Nat.minFac_dvd e).trans hdvd, hr.trans hlt⟩
  have hpair := pair_le_defect hrmem he hr.ne
  have h1 := term_eq_one_of_prime hrp
  have h2 := two_le_term he2 hnp
  omega

/-- If `0 < defect m ≤ 2`, then `m` is a product of two (not necessarily distinct) primes. -/
theorem exists_prime_mul_of_defect {m : ℕ} (hd0 : defect m ≠ 0) (hd : defect m ≤ 2) :
    ∃ r k : ℕ, r.Prime ∧ k.Prime ∧ m = r * k := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hd0 defect_zero
  have hm1 : m ≠ 1 := by rintro rfl; exact hd0 defect_one
  have hnp : ¬ m.Prime := fun hp => hd0 (defect_of_prime hp)
  have hm2 : 2 ≤ m := by omega
  set r := m.minFac with hr_def
  have hrp : r.Prime := Nat.minFac_prime hm1
  have hrlt : r < m := (Nat.not_prime_iff_minFac_lt hm2).1 hnp
  have hrdvd : r ∣ m := Nat.minFac_dvd m
  have hmk : m = r * (m / r) := (Nat.mul_div_cancel' hrdvd).symm
  have hk1 : m / r ≠ 1 := by
    intro h
    rw [h, mul_one] at hmk
    omega
  have hklt : m / r < m := Nat.div_lt_self (by omega) hrp.one_lt
  have hkmem : m / r ∈ m.properDivisors :=
    Nat.mem_properDivisors.2 ⟨Nat.div_dvd_of_dvd hrdvd, hklt⟩
  rcases properDivisor_eq_one_or_prime hd hkmem with hk | hk
  · exact absurd hk hk1
  · exact ⟨r, m / r, hrp, hk, hmk⟩

/-- **Defect-two characterization** (Cloitre's remark in OEIS A006881, here proved):
`σ(m) + φ(m) = 2m + 2` exactly for the squarefree semiprimes. -/
theorem defect_eq_two_iff (m : ℕ) : defect m = 2 ↔ IsSqfreeSemiprime m := by
  constructor
  · intro hd
    obtain ⟨r, k, hr, hk, rfl⟩ := exists_prime_mul_of_defect (m := m) (by omega) (by omega)
    by_cases hrk : r = k
    · subst hrk
      have := defect_sq hr
      rw [sq] at this
      omega
    · exact ⟨r, k, hr, hk, hrk, rfl⟩
  · rintro ⟨p, q, hp, hq, hpq, rfl⟩
    exact defect_mul_of_ne hp hq hpq

/-- **Defect-one characterization**: `σ(m) + φ(m) = 2m + 1` exactly for the prime
squares. -/
theorem defect_eq_one_iff (m : ℕ) : defect m = 1 ↔ ∃ p : ℕ, p.Prime ∧ m = p ^ 2 := by
  constructor
  · intro hd
    obtain ⟨r, k, hr, hk, rfl⟩ := exists_prime_mul_of_defect (m := m) (by omega) (by omega)
    by_cases hrk : r = k
    · subst hrk
      exact ⟨r, hr, (sq r).symm⟩
    · have := defect_mul_of_ne hr hk hrk
      omega
  · rintro ⟨p, hp, rfl⟩
    exact defect_sq hp

/-- The two jump conditions at shift `12` force equal defects at `n` and `n + 12`. -/
theorem defect_add_twelve_of_jump {n : ℕ} (h : JumpCondition12 n) :
    defect (n + 12) = defect n := by
  obtain ⟨hφ, hσ⟩ := h
  have h1 := sigma_add_totient_eq n
  have h2 := sigma_add_totient_eq (n + 12)
  omega

/-- If `p` and `p + k` are both prime and `k` is odd, then `p = 2`. -/
theorem eq_two_of_prime_add_odd {p k : ℕ} (hp : p.Prime) (hpk : (p + k).Prime)
    (hk : k % 2 = 1) :
    p = 2 := by
  rcases hp.eq_two_or_odd with h | h
  · exact h
  · rcases hpk.eq_two_or_odd with h' | h'
    · have := hp.two_le
      omega
    · omega

/-- Paper's Theorem 2.2 core: primes `p < q`, `p', q'` with `p' + q' = p + q` and
`p' q' = p q + 12` force `(p, p+2, p+6, p+8)` to be a prime quadruplet and `q = p + 8`. -/
theorem quadruplet_of_sum_prod {p q p' q' : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp' : p'.Prime) (hq' : q'.Prime) (hpq : p < q)
    (hsum : p' + q' = p + q) (hprod : p' * q' = p * q + 12) :
    IsPrimeQuadruplet p ∧ q = p + 8 := by
  rcases le_or_gt p' p with hle | hlt
  · exfalso
    obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le hle
    have hq'x : q' = q + x := by omega
    subst hq'x
    have hkey : p' * x = x * q + 12 := by
      ring_nf at hprod
      linarith
    have : x * p' ≤ x * q := Nat.mul_le_mul_left x (by omega)
    linarith
  · obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    -- `p' = p + x + 1`
    have hqx : q = q' + (x + 1) := by omega
    subst hqx
    have hkey : (x + 1) * q' = (x + 1) * p + 12 := by
      ring_nf at hprod ⊢
      linarith
    have hq'p : p < q' := by
      by_contra hcon
      have : (x + 1) * q' ≤ (x + 1) * p := Nat.mul_le_mul_left _ (by omega)
      omega
    obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_lt hq'p
    have hxy : (x + 1) * (y + 1) = 12 := by
      ring_nf at hkey ⊢
      linarith
    have hx : x + 1 ∣ 12 := ⟨y + 1, hxy.symm⟩
    have hxle : x ≤ 11 := by have := Nat.le_of_dvd (by norm_num) hx; omega
    interval_cases x <;> (try omega)
    · -- x + 1 = 1, y + 1 = 12
      have hy : y = 11 := by omega
      subst hy
      have h2 := eq_two_of_prime_add_odd hp (k := 1) (by simpa using hp') (by norm_num)
      subst h2
      norm_num at hq
    · -- x + 1 = 2, y + 1 = 6
      have hy : y = 5 := by omega
      subst hy
      exact ⟨⟨hp, by simpa using hp', by simpa using hq', by simpa [add_assoc] using hq⟩,
        by omega⟩
    · -- x + 1 = 3, y + 1 = 4
      have hy : y = 3 := by omega
      subst hy
      have h2 := eq_two_of_prime_add_odd hp (k := 3) (by simpa using hp') (by norm_num)
      subst h2
      norm_num at hq
    · -- x + 1 = 4, y + 1 = 3
      have hy : y = 2 := by omega
      subst hy
      have h2 := eq_two_of_prime_add_odd hp (k := 3) (by simpa using hq') (by norm_num)
      subst h2
      norm_num at hq
    · -- x + 1 = 6, y + 1 = 2
      have hy : y = 1 := by omega
      subst hy
      exact ⟨⟨hp, by simpa using hq', by simpa using hp', by simpa [add_assoc] using hq⟩,
        by omega⟩
    · -- x + 1 = 12, y + 1 = 1
      have hy : y = 0 := by omega
      subst hy
      have h2 := eq_two_of_prime_add_odd hp (k := 1) (by simpa using hq') (by norm_num)
      subst h2
      norm_num at hq

/-- `φ(p q) = (p - 1)(q - 1)` for distinct primes. -/
theorem totient_mul_of_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Nat.totient (p * q) = (p - 1) * (q - 1) := by
  rw [Nat.totient_mul ((Nat.coprime_primes hp hq).2 hpq), Nat.totient_prime hp,
    Nat.totient_prime hq]

/-- `σ(p q) = (p + 1)(q + 1)` for distinct primes. -/
theorem sigma_mul_of_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    σ 1 (p * q) = (p + 1) * (q + 1) := by
  rw [isMultiplicative_sigma.map_mul_of_coprime ((Nat.coprime_primes hp hq).2 hpq),
    sigma_one_prime hp, sigma_one_prime hq]

/-- **Theorem 2.2 (⇒), both-sides case** of arXiv 2606.10331, in the form used here:
if `n = p q` and `n + 12 = p' q'` are squarefree semiprimes and `φ(n+12) = φ(n) + 12`,
then `n = r (r + 8)` for a prime quadruplet `(r, r+2, r+6, r+8)`. -/
theorem quadruplet_of_semiprime_pair {n : ℕ} (h : JumpCondition12 n)
    (hn : IsSqfreeSemiprime n) (hn12 : IsSqfreeSemiprime (n + 12)) :
    ∃ r : ℕ, IsPrimeQuadruplet r ∧ n = r * (r + 8) := by
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hn
  obtain ⟨p', q', hp', hq', hpq', hn12⟩ := hn12
  have hφ := h.1
  rw [hn12, totient_mul_of_ne hp' hq' hpq', totient_mul_of_ne hp hq hpq] at hφ
  have hsum : p' + q' = p + q := by
    obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = b + 1 := ⟨q - 1, by have := hq.one_lt; omega⟩
    obtain ⟨c, rfl⟩ : ∃ c, p' = c + 1 := ⟨p' - 1, by have := hp'.one_lt; omega⟩
    obtain ⟨d, rfl⟩ : ∃ d, q' = d + 1 := ⟨q' - 1, by have := hq'.one_lt; omega⟩
    simp only [Nat.add_sub_cancel] at hφ
    ring_nf at hφ hn12
    linarith
  rcases lt_or_gt_of_ne hpq with hlt | hgt
  · obtain ⟨hquad, hq8⟩ := quadruplet_of_sum_prod hp hq hp' hq' hlt hsum (by omega)
    exact ⟨p, hquad, by rw [hq8]⟩
  · obtain ⟨hquad, hp8⟩ := quadruplet_of_sum_prod hq hp hp' hq' hgt (by omega)
      (by rw [mul_comm q p]; omega)
    exact ⟨q, hquad, by rw [hp8, mul_comm]⟩

/-- **One-sided strengthening of Theorem 2.2** (arXiv 2606.10331; target a4-1).
If `n` satisfies both jump conditions `φ(n+12) = φ(n) + 12`, `σ(n+12) = σ(n) + 12` and
*either* `n` *or* `n + 12` is a squarefree semiprime, then `n = p (p + 8)` where
`(p, p+2, p+6, p+8)` is a prime quadruplet with `5 ≤ p`. -/
theorem exists_quadruplet_of_jump_of_semiprime {n : ℕ} (h : JumpCondition12 n)
    (hs : IsSqfreeSemiprime n ∨ IsSqfreeSemiprime (n + 12)) :
    ∃ p : ℕ, 5 ≤ p ∧ IsPrimeQuadruplet p ∧ n = p * (p + 8) := by
  have hdef := defect_add_twelve_of_jump h
  have hboth : IsSqfreeSemiprime n ∧ IsSqfreeSemiprime (n + 12) := by
    rcases hs with hs | hs
    · refine ⟨hs, ?_⟩
      rw [← defect_eq_two_iff, hdef, defect_eq_two_iff]
      exact hs
    · refine ⟨?_, hs⟩
      rw [← defect_eq_two_iff, ← hdef, defect_eq_two_iff]
      exact hs
  obtain ⟨p, hquad, rfl⟩ := quadruplet_of_semiprime_pair h hboth.1 hboth.2
  refine ⟨p, ?_, hquad, rfl⟩
  obtain ⟨hp, hp2, hp6, _⟩ := hquad
  by_contra hlt
  have h2 := hp.two_le
  interval_cases p
  · norm_num at hp2
  · norm_num at hp6
  · norm_num at hp

/-- `r² = p² + 12` has no solution in primes `p, r`. -/
theorem sq_ne_sq_add_twelve {p r : ℕ} (hp : p.Prime) (hr : r.Prime) : r ^ 2 ≠ p ^ 2 + 12 := by
  intro h
  have hpr : p < r := by nlinarith
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hpr
  have ht : t ≤ 2 := by nlinarith
  interval_cases t
  · ring_nf at h
    omega
  · have hp2 : p = 2 := by
      ring_nf at h
      omega
    subst hp2
    norm_num at hr
  · ring_nf at h
    omega

/-- **No prime squares** (target a4-1, second part): no `n` satisfying both jump conditions
has `n` or `n + 12` equal to the square of a prime. -/
theorem jump_ne_prime_sq {n : ℕ} (h : JumpCondition12 n) {p : ℕ} (hp : p.Prime) :
    n ≠ p ^ 2 ∧ n + 12 ≠ p ^ 2 := by
  have hdef := defect_add_twelve_of_jump h
  constructor
  · rintro rfl
    obtain ⟨r, hr, hr2⟩ := (defect_eq_one_iff (p ^ 2 + 12)).1 (by rw [hdef, defect_sq hp])
    exact sq_ne_sq_add_twelve hp hr hr2.symm
  · intro h12
    obtain ⟨r, hr, hr2⟩ := (defect_eq_one_iff n).1 (by rw [← hdef, h12, defect_sq hp])
    subst hr2
    exact sq_ne_sq_add_twelve hr hp h12.symm

/-- **Theorem 2.2 (⇐)** of arXiv 2606.10331: every prime quadruplet `(p, p+2, p+6, p+8)`
yields a solution `n = p (p + 8)` of both jump conditions. -/
theorem jump_of_isPrimeQuadruplet {p : ℕ} (hq : IsPrimeQuadruplet p) :
    JumpCondition12 (p * (p + 8)) := by
  obtain ⟨hp, hp2, hp6, hp8⟩ := hq
  have hsplit : p * (p + 8) + 12 = (p + 2) * (p + 6) := by ring
  have hne1 : p ≠ p + 8 := by omega
  have hne2 : p + 2 ≠ p + 6 := by omega
  have h1 := hp.one_lt
  refine ⟨?_, ?_⟩
  · rw [hsplit, totient_mul_of_ne hp2 hp6 hne2, totient_mul_of_ne hp hp8 hne1]
    have e1 : p + 2 - 1 = p + 1 := by omega
    have e2 : p + 6 - 1 = p + 5 := by omega
    have e3 : p + 8 - 1 = p + 7 := by omega
    rw [e1, e2, e3]
    obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  · rw [hsplit, sigma_mul_of_ne hp2 hp6 hne2, sigma_mul_of_ne hp hp8 hne1]
    ring

/-! ## Ground truth -/

example : IsPrimeQuadruplet 5 := by unfold IsPrimeQuadruplet; norm_num

/-- `n = 65 = 5 · 13` is the paper's worked example. -/
example : JumpCondition12 65 :=
  jump_of_isPrimeQuadruplet (p := 5) (by unfold IsPrimeQuadruplet; norm_num)

example : IsSqfreeSemiprime 65 := ⟨5, 13, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `defect 12 = 0 + 1 + 1 + 2 + 4`; indeed `σ 12 + φ 12 = 28 + 4 = 2 · 12 + 8`. -/
example : defect 12 = 8 := by decide

example : defect 6 = 2 := by decide

example : defect 9 = 1 := by decide

/-- The hypotheses of the main theorem are jointly satisfiable, at `n = 65`. -/
example : ∃ p : ℕ, 5 ≤ p ∧ IsPrimeQuadruplet p ∧ 65 = p * (p + 8) :=
  exists_quadruplet_of_jump_of_semiprime
    (jump_of_isPrimeQuadruplet (p := 5) (by unfold IsPrimeQuadruplet; norm_num))
    (Or.inl ⟨5, 13, by norm_num, by norm_num, by norm_num, by norm_num⟩)

end Candidates.McCranieQuadrupletJumpSemiprime
