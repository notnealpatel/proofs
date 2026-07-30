import Mathlib

/-!
# OEIS A064097: a quasi-logarithm and its logarithmic bounds

`quasilog` is OEIS A064097, the completely additive quasi-logarithm defined
inductively by `a 1 = 0`, `a p = 1 + a (p - 1)` for `p` prime, and
`a (m * n) = a m + a n` for `1 < m`, `1 < n`.

Main declarations:

* `NumberComplexity.quasilog` — the sequence, by recursion on the least prime factor;
* `NumberComplexity.quasilog_mul` — complete additivity (the defining property), proved;
* `NumberComplexity.log_two_le_quasilog` — Wilson's lower bound `⌊log₂ n⌋ ≤ a n`, proved
  via the sharper `NumberComplexity.le_two_pow_quasilog` (`n ≤ 2 ^ a n`);
* `NumberComplexity.quasilog_le_two_point_five_mul_log` — Cloitre's conjectured upper
  bound `a n ≤ 2.5 * Real.log n` for `1 < n`: OPEN, carried as an intended `sorry` over
  a proved ground-truth instance at `n = 2`.

Ground truth: `oeis show A064097`, pulled live 2026-07-29; first terms
`0, 1, 2, 2, 3, 3, 4, 3, 4, 4, 5, 4, 5, 5, 5, 4, …` (offset 1), checked below.

Source: OEIS A064097 formulas — Benoit Cloitre (2002-10-30), Robert G. Wilson v
(2013-08-10). Card: `Formalize/A064097-quasilog-bounds.md`.
-/

set_option autoImplicit false

namespace NumberComplexity

/-- OEIS A064097, the quasi-logarithm: `quasilog 1 = 0`; for a prime `p`,
`quasilog p = 1 + quasilog (p - 1)`; for a composite `n`, `quasilog` splits off the
least prime factor, `quasilog n = quasilog n.minFac + quasilog (n / n.minFac)`.
The input `0` is junk and is mapped to `0`. Complete additivity
`quasilog (m * n) = quasilog m + quasilog n` (the defining clause in the OEIS entry)
is recovered in `quasilog_mul`. -/
def quasilog (n : ℕ) : ℕ :=
  if _h1 : n ≤ 1 then 0
  else if h2 : n.Prime then 1 + quasilog (n - 1)
  else quasilog n.minFac + quasilog (n / n.minFac)
termination_by n
decreasing_by
  · omega
  · have hle : n.minFac ≤ n := Nat.minFac_le (by omega)
    have hne : n.minFac ≠ n := fun h => h2 (h ▸ Nat.minFac_prime (by omega : n ≠ 1))
    omega
  · exact Nat.div_lt_self (by omega) (Nat.minFac_prime (by omega : n ≠ 1)).one_lt

/-! ## Defining equations

`quasilog` is defined by well-founded recursion, so it does not reduce by `rfl` or
`decide`; ground evaluation goes through the conditional equations below, whose
side conditions (`Nat.Prime` and `Nat.minFac` at numerals) `norm_num` discharges.
`simp [quasilog]` must NOT be used for evaluation: simp rewrites inside the dead
branch of the `dite` (e.g. `quasilog 2.minFac = quasilog 2`) and loops.
-/

/-- `quasilog 0 = 0` (junk input, junk value). -/
@[simp] theorem quasilog_zero : quasilog 0 = 0 := by
  rw [quasilog, dif_pos (by norm_num : (0 : ℕ) ≤ 1)]

/-- `quasilog 1 = 0`, the base case of OEIS A064097. -/
@[simp] theorem quasilog_one : quasilog 1 = 0 := by
  rw [quasilog, dif_pos (by norm_num : (1 : ℕ) ≤ 1)]

/-- Defining equation of A064097 at a prime: `quasilog p = 1 + quasilog (p - 1)`. -/
theorem quasilog_of_prime {p : ℕ} (hp : p.Prime) : quasilog p = 1 + quasilog (p - 1) := by
  have h2 : 2 ≤ p := hp.two_le
  rw [quasilog, dif_neg (by omega : ¬p ≤ 1), dif_pos hp]

/-- Defining equation of `quasilog` at a non-prime `2 ≤ n`: split off the least
prime factor. -/
theorem quasilog_of_not_prime {n : ℕ} (h2 : 2 ≤ n) (hn : ¬n.Prime) :
    quasilog n = quasilog n.minFac + quasilog (n / n.minFac) := by
  rw [quasilog, dif_neg (by omega : ¬n ≤ 1), dif_neg hn]

/-- Least-prime-factor splitting holds for every `2 ≤ n`, primes included (there the
cofactor is `1` and contributes `0`). -/
theorem quasilog_eq_minFac_add_div {n : ℕ} (h2 : 2 ≤ n) :
    quasilog n = quasilog n.minFac + quasilog (n / n.minFac) := by
  by_cases hp : n.Prime
  · rw [hp.minFac_eq, Nat.div_self (by omega : 0 < n), quasilog_one, Nat.add_zero]
  · exact quasilog_of_not_prime h2 hp

/-!
## Ground checks against `oeis show A064097` (pulled live 2026-07-29)

Terms `a(1)..a(16)` are `0,1,2,2,3,3,4,3,4,4,5,4,5,5,5,4`; further spot checks
at `23, 24, 32, 47, 48, 64, 94, 96, 100` against the in-entry data
(`a(23) = 7` and `a(47) = 9` exercise long prime chains, `a(64) = 6` a pure
power of `2`, `a(100) = 8` a mixed composite).
-/

example : quasilog 0 = 0 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
example : quasilog 1 = 0 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
example : quasilog 2 = 1 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
example : quasilog 3 = 2 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
example : quasilog 4 = 2 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
example : quasilog 5 = 3 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
example : quasilog 6 = 3 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
example : quasilog 7 = 4 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
example : quasilog 8 = 3 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
example : quasilog 9 = 4 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
example : quasilog 10 = 4 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
example : quasilog 11 = 5 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
example : quasilog 12 = 4 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
example : quasilog 13 = 5 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
example : quasilog 14 = 5 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
example : quasilog 15 = 5 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
example : quasilog 16 = 4 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
example : quasilog 23 = 7 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
example : quasilog 24 = 5 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
example : quasilog 32 = 5 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
example : quasilog 47 = 9 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
example : quasilog 48 = 6 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
example : quasilog 64 = 6 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
example : quasilog 94 = 10 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
example : quasilog 96 = 7 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]
example : quasilog 100 = 8 := by norm_num [quasilog_of_prime, quasilog_of_not_prime]

/-! ## Complete additivity -/

/-- **Complete additivity** of OEIS A064097 (the defining clause
`a(n*m) = a(n) + a(m)` of the entry): for `0 < m` and `0 < n`,
`quasilog (m * n) = quasilog m + quasilog n`. The guards are necessary:
`quasilog 0 = 0` is junk. -/
theorem quasilog_mul (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    quasilog (m * n) = quasilog m + quasilog n := by
  -- strong induction on the product, phrased as plain induction on an upper bound `N`
  suffices H : ∀ N m n : ℕ, m * n ≤ N → 0 < m → 0 < n →
      quasilog (m * n) = quasilog m + quasilog n by
    exact H (m * n) m n le_rfl hm hn
  intro N
  induction N with
  | zero =>
    intro m n hmn hm hn
    exact absurd hmn (Nat.not_le.mpr (Nat.mul_pos hm hn))
  | succ N ih =>
    intro m n hmn hm hn
    by_cases hm1 : m = 1
    · subst hm1
      rw [one_mul, quasilog_one, Nat.zero_add]
    by_cases hn1 : n = 1
    · subst hn1
      rw [mul_one, quasilog_one, Nat.add_zero]
    -- now `2 ≤ m` and `2 ≤ n`, so `m * n` is composite
    have hm2 : 2 ≤ m := by omega
    have hn2 : 2 ≤ n := by omega
    have hmn4 : 2 * 2 ≤ m * n := Nat.mul_le_mul hm2 hn2
    set p := (m * n).minFac with hp_def
    have hpp : p.Prime := by
      rw [hp_def]
      exact Nat.minFac_prime (by omega : m * n ≠ 1)
    have hp2 : 2 ≤ p := hpp.two_le
    have hsplit : quasilog (m * n) = quasilog p + quasilog (m * n / p) := by
      rw [hp_def]
      exact quasilog_eq_minFac_add_div (by omega : 2 ≤ m * n)
    have hpd : p ∣ m * n := by
      rw [hp_def]
      exact Nat.minFac_dvd (m * n)
    rcases hpp.dvd_mul.mp hpd with hpm | hpn
    · -- the least prime factor divides `m`
      obtain ⟨k, hk⟩ := hpm
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · rw [h, Nat.mul_zero] at hk
          omega
        · exact h
      have hdiv : m * n / p = k * n := by
        rw [hk, mul_assoc, Nat.mul_div_cancel_left _ hpp.pos]
      have hkn_le : k * n ≤ N := by
        have ha : 2 * (k * n) ≤ p * (k * n) := Nat.mul_le_mul hp2 le_rfl
        have hb : p * (k * n) = m * n := by rw [hk, mul_assoc]
        have hc : 0 < k * n := Nat.mul_pos hk0 hn
        omega
      have hm_le : m ≤ N := by
        have ha : m * 2 ≤ m * n := Nat.mul_le_mul le_rfl hn2
        omega
      have hIH1 : quasilog (k * n) = quasilog k + quasilog n := ih k n hkn_le hk0 hn
      have hIH2 : quasilog (p * k) = quasilog p + quasilog k :=
        ih p k (by omega : p * k ≤ N) hpp.pos hk0
      calc quasilog (m * n)
          = quasilog p + quasilog (m * n / p) := hsplit
        _ = quasilog p + quasilog (k * n) := by rw [hdiv]
        _ = quasilog p + (quasilog k + quasilog n) := by rw [hIH1]
        _ = quasilog p + quasilog k + quasilog n := by rw [Nat.add_assoc]
        _ = quasilog (p * k) + quasilog n := by rw [hIH2]
        _ = quasilog m + quasilog n := by rw [← hk]
    · -- the least prime factor divides `n`
      obtain ⟨k, hk⟩ := hpn
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · rw [h, Nat.mul_zero] at hk
          omega
        · exact h
      have hdiv : m * n / p = m * k := by
        rw [hk, show m * (p * k) = p * (m * k) by ring, Nat.mul_div_cancel_left _ hpp.pos]
      have hmk_le : m * k ≤ N := by
        have ha : 2 * (m * k) ≤ p * (m * k) := Nat.mul_le_mul hp2 le_rfl
        have hb : p * (m * k) = m * n := by rw [hk]; ring
        have hc : 0 < m * k := Nat.mul_pos hm hk0
        omega
      have hn_le : n ≤ N := by
        have ha : 2 * n ≤ m * n := Nat.mul_le_mul hm2 le_rfl
        omega
      have hIH1 : quasilog (m * k) = quasilog m + quasilog k := ih m k hmk_le hm hk0
      have hIH2 : quasilog (p * k) = quasilog p + quasilog k :=
        ih p k (by omega : p * k ≤ N) hpp.pos hk0
      calc quasilog (m * n)
          = quasilog p + quasilog (m * n / p) := hsplit
        _ = quasilog p + quasilog (m * k) := by rw [hdiv]
        _ = quasilog p + (quasilog m + quasilog k) := by rw [hIH1]
        _ = quasilog m + (quasilog p + quasilog k) := by rw [Nat.add_left_comm]
        _ = quasilog m + quasilog (p * k) := by rw [hIH2]
        _ = quasilog m + quasilog n := by rw [← hk]

-- satisfiability of `quasilog_mul` hypotheses at a concrete model: `m = 2`, `n = 3`
example : quasilog (2 * 3) = quasilog 2 + quasilog 3 :=
  quasilog_mul 2 3 (by norm_num) (by norm_num)

/-! ## Lower bound (Wilson): proved -/

/-- The exponential form of Wilson's lower bound: `n ≤ 2 ^ quasilog n` for `0 < n`.
Prime step: `2 ^ (1 + a (p-1)) = 2 * 2 ^ a (p-1) ≤ 2 * (p-1)` reversed gives
`p ≤ 2 * (p - 1) ≤ 2 ^ a p`; composite step is multiplicativity of both sides. -/
theorem le_two_pow_quasilog (n : ℕ) (hn : 0 < n) : n ≤ 2 ^ quasilog n := by
  -- strong induction, phrased as plain induction on an upper bound `N`
  suffices H : ∀ N n : ℕ, n ≤ N → 0 < n → n ≤ 2 ^ quasilog n by
    exact H n n le_rfl hn
  intro N
  induction N with
  | zero =>
    intro n hle hn
    exact absurd hle (Nat.not_le.mpr hn)
  | succ N ih =>
    intro n hle hn
    by_cases h1 : n = 1
    · subst h1
      norm_num [quasilog_one]
    have h2 : 2 ≤ n := by omega
    by_cases hp : n.Prime
    · -- prime step
      have hIH : n - 1 ≤ 2 ^ quasilog (n - 1) := ih (n - 1) (by omega) (by omega)
      calc n ≤ 2 * (n - 1) := by omega
        _ ≤ 2 * 2 ^ quasilog (n - 1) := Nat.mul_le_mul le_rfl hIH
        _ = 2 ^ (1 + quasilog (n - 1)) := by rw [pow_add, pow_one]
        _ = 2 ^ quasilog n := by rw [quasilog_of_prime hp]
    · -- composite step: split off the least prime factor
      have hpp : (n.minFac).Prime := Nat.minFac_prime (by omega : n ≠ 1)
      have hpdvd : n.minFac ∣ n := Nat.minFac_dvd n
      have hple : n.minFac ≤ n := Nat.minFac_le (by omega)
      have hplt : n.minFac < n :=
        lt_of_le_of_ne hple (fun h => hp (h ▸ hpp))
      have hqpos : 0 < n / n.minFac := Nat.div_pos hple hpp.pos
      have hqlt : n / n.minFac < n := Nat.div_lt_self (by omega) hpp.one_lt
      have hIH1 : n.minFac ≤ 2 ^ quasilog n.minFac := ih n.minFac (by omega) hpp.pos
      have hIH2 : n / n.minFac ≤ 2 ^ quasilog (n / n.minFac) :=
        ih (n / n.minFac) (by omega) hqpos
      calc n = n.minFac * (n / n.minFac) := (Nat.mul_div_cancel' hpdvd).symm
        _ ≤ 2 ^ quasilog n.minFac * 2 ^ quasilog (n / n.minFac) := Nat.mul_le_mul hIH1 hIH2
        _ = 2 ^ (quasilog n.minFac + quasilog (n / n.minFac)) := (pow_add 2 _ _).symm
        _ = 2 ^ quasilog n := by rw [← quasilog_of_not_prime h2 hp]

/-- **Wilson's lower bound** (OEIS A064097, Robert G. Wilson v, 2013-08-10):
`⌊log₂ n⌋ ≤ a n` for `0 < n`. The guard keeps both `Nat.log` and `quasilog`
off their junk value at `0`. -/
theorem log_two_le_quasilog (n : ℕ) (hn : 0 < n) : Nat.log 2 n ≤ quasilog n :=
  calc Nat.log 2 n ≤ Nat.log 2 (2 ^ quasilog n) :=
        Nat.log_mono_right (le_two_pow_quasilog n hn)
    _ = quasilog n := Nat.log_pow Nat.one_lt_two _

-- satisfiability of `log_two_le_quasilog` at a concrete model, and its sharpness:
-- at `n = 16` both sides equal `4`
example : Nat.log 2 16 ≤ quasilog 16 := log_two_le_quasilog 16 (by norm_num)
example : Nat.log 2 16 = 4 :=
  Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
example : 5 ≤ 2 ^ quasilog 5 := le_two_pow_quasilog 5 (by norm_num)

/-! ## Upper bound (Cloitre): open, intended `sorry`

The OEIS entry conjectures `a n < 2.5 * log n` for `1 < n` (Cloitre, 2002-10-30;
verified computationally far into the entry, unproven in the literature as far as
the campaign sweep found). Naive strong induction FAILS at `c = 2.5`: the prime
step needs `2 ≤ c * Real.log 2`, but `2.5 * Real.log 2 ≈ 1.733 < 2`. A proof must
exploit that `p - 1` is even for odd primes (cheap factor-`2` steps cannot repeat
immediately) or track worst-case prime chains. HOLD tier: stated, not attempted.
-/

/-- **Cloitre's upper bound** (OEIS A064097, Benoit Cloitre, 2002-10-30) — OPEN:
`a n ≤ 2.5 * Real.log n` for `1 < n` (the entry conjectures the strict form
`a n < 2.5 * log n`). The guard `1 < n` keeps `Real.log` off `Real.log 1 = 0`
(and off the junk value `Real.log 0 = 0`); at `n = 1` even the strict form would
be false since `a 1 = 0 = 2.5 * log 1`. -/
theorem quasilog_le_two_point_five_mul_log (n : ℕ) (hn : 1 < n) :
    (quasilog n : ℝ) ≤ 2.5 * Real.log n := by
  -- intended sorry: open conjecture (card A064097-quasilog-bounds, ROUTE (ii));
  -- naive induction fails at c = 2.5 because 2.5 * log 2 < 2 at prime steps.
  sorry

-- ground-truth/satisfiability layer for the sorried statement: the hypothesis
-- `1 < n` and the conclusion are jointly satisfied at `n = 2`, proved outright
-- (`quasilog 2 = 1 ≤ 2.5 * Real.log 2 ≈ 1.733`).
example : ∃ n : ℕ, 1 < n ∧ (quasilog n : ℝ) ≤ 2.5 * Real.log n := by
  refine ⟨2, one_lt_two, ?_⟩
  have h2 : quasilog 2 = 1 := by norm_num [quasilog_of_prime]
  rw [h2]
  have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  push_cast
  linarith

/-! ## Axiom audit (sorry-free declarations only) -/

#print axioms quasilog
#print axioms quasilog_zero
#print axioms quasilog_one
#print axioms quasilog_of_prime
#print axioms quasilog_of_not_prime
#print axioms quasilog_eq_minFac_add_div
#print axioms quasilog_mul
#print axioms le_two_pow_quasilog
#print axioms log_two_le_quasilog

end NumberComplexity
