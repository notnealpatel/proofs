/-
# Dice relabeling with square-sided dice: the odd-`p` direction of Conjecture con:q01

## Source

arXiv:2606.20311, Evelyn Fiore, George D. Nasr, Cooper Stone,
"Dice Relabeling using Square-Sided Dice".  Section 4 ("Square-sided dice for
pairs of `p²q`-sided dice"), Conjecture `con:q01`, stated just before
Theorem `thm:q01_coeffs`.  The paper defines, for distinct primes `p, q`,

  `Q_{a,b}(x) := x Φ_q² Φ_{pq}^a Φ_{p²q}^b`,   so   `Q_{01}(x) = x Φ_q(x)² Φ_{p²q}(x)`.

Verbatim informal claim (Conjecture con:q01):

  "`Q_{01}` has nonnegative coefficients if and only if `p=2` and `q≡1 mod 4`."

followed by "We have ample numerical evidence to justify the case where
`p≠2`, but were not able to fully classify this case.  However, we can prove
this conjecture in the case of `p=2`."  Theorem thm:q01_coeffs proves the
`p = 2` case.

## Target recorded here (2026-10-21)

The direction the paper leaves open: for all primes `p ≠ q` with `p` odd,
`Q_{01}` has a negative coefficient.  Literature status: open in the source
(only numerical evidence there).  Together with the paper's Theorem
thm:q01_coeffs this settles Conjecture con:q01.

## Proof outline (checked below, no `sorry`)

With `t_k = [x^k] Φ_q² Φ_{p²q}`:

* `Φ_{p²q} Φ_{p²} = Φ_{p²}(x^q) = Σ_{i<p} x^{pqi}` (because `q ∤ p²`), whence
  `Φ_q² Φ_{p²q} (1 - x)(1 - x^{p²}) = (1 - x^q)² Φ_p(x) Σ_{i<p} x^{pqi}`.
* Hence for `k < pq`, `t_k = Σ_{j<p} (s(k,j) - 2 s(k,q+j) + s(k,2q+j))`, where
  `s(k,a) = ⌊(k-a)/p²⌋ + 1` for `a ≤ k` and `0` otherwise.
* Witnesses: `k = p` (`2q-1 ≤ p`, value `-1`); `k = 2q-2` (`q < p ≤ 2q-3`,
  value `p+2-2q`; or `p < q`, `2q-2 < p²`, value `-p`); in the periodic regime
  `2q+p+p²-1 ≤ pq`, `k = q+p-1+(⌊q/p²⌋+1)p²`, where every summand is `≤ 0`
  and the `j = p-1` summand is `-1`; finally `(p,q) = (3,7)` with `k = 8`.
  For `p ≥ 5` and for `p = 3, q ≠ 7` these regimes cover every `q`.
-/
import Mathlib

set_option autoImplicit false

open Polynomial Finset

namespace DiceRelabelingSquareSided

/-- The paper's `Q_{01}(x) = x Φ_q(x)² Φ_{p²q}(x)` over `ℤ` (Section 4, the case
`a = 0`, `b = 1` of `Q_{a,b}(x) = x Φ_q² Φ_{pq}^a Φ_{p²q}^b`). -/
noncomputable def Q01 (p q : ℕ) : ℤ[X] := X * cyclotomic q ℤ ^ 2 * cyclotomic (p ^ 2 * q) ℤ

/-- `Q_{01}/x = Φ_q(x)² Φ_{p²q}(x)` over `ℤ`. -/
noncomputable def q01Core (p q : ℕ) : ℤ[X] := cyclotomic q ℤ ^ 2 * cyclotomic (p ^ 2 * q) ℤ

/-- `Q_{01} = x · (Φ_q² Φ_{p²q})`. -/
theorem Q01_eq_X_mul (p q : ℕ) : Q01 p q = X * q01Core p q := by
  rw [Q01, q01Core, mul_assoc]

/-- Coefficients of `Q_{01}` are those of `Φ_q² Φ_{p²q}` shifted by one. -/
theorem coeff_Q01_succ (p q k : ℕ) : (Q01 p q).coeff (k + 1) = (q01Core p q).coeff k := by
  rw [Q01_eq_X_mul, coeff_X_mul]

/-- **Key identity.**  For distinct primes `p, q`,
`Φ_q² Φ_{p²q} · (1 - X) · (1 - X^{p²}) = (1 - X^q)² · (Σ_{j<p} X^j) · (Σ_{i<p} X^{pqi})`.
It combines `Φ_{p²q} Φ_{p²} = Φ_{p²}(X^q) = Σ_{i<p} X^{pqi}` (since `q ∤ p²`) with the
geometric-sum forms of `Φ_q`, `Φ_p`, `Φ_{p²}`. -/
theorem key_identity (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    q01Core p q * (1 - X) * (1 - X ^ (p ^ 2)) =
      (1 - X ^ q) ^ 2 * (∑ j ∈ range p, (X : ℤ[X]) ^ j) *
        ∑ i ∈ range p, (X ^ (p * q) : ℤ[X]) ^ i := by
  haveI := Fact.mk hp
  haveI := Fact.mk hq
  have hΦq : cyclotomic q ℤ * (1 - X) = 1 - X ^ q := by
    rw [cyclotomic_prime]; exact geom_sum_mul_neg _ _
  have hΦp : cyclotomic p ℤ * (1 - X) = 1 - X ^ p := by
    rw [cyclotomic_prime]; exact geom_sum_mul_neg _ _
  have hΦp2eq : cyclotomic (p ^ 2) ℤ = ∑ i ∈ range p, ((X : ℤ[X]) ^ p) ^ i := by
    have := cyclotomic_prime_pow_eq_geom_sum (R := ℤ) (n := 1) hp
    simpa using this
  have hΦp2 : cyclotomic (p ^ 2) ℤ * (1 - X ^ p) = 1 - X ^ (p ^ 2) := by
    rw [hΦp2eq, geom_sum_mul_neg, ← pow_mul, sq]
  have hndvd : ¬ q ∣ p ^ 2 := by
    intro h
    have h1 : q ∣ p := hq.dvd_of_dvd_pow h
    rcases (Nat.prime_dvd_prime_iff_eq hq hp).1 h1 with rfl
    exact hpq rfl
  have hexp : cyclotomic (p ^ 2 * q) ℤ * cyclotomic (p ^ 2) ℤ =
      ∑ i ∈ range p, (X ^ (p * q) : ℤ[X]) ^ i := by
    rw [← cyclotomic_expand_eq_cyclotomic_mul hq hndvd, hΦp2eq]
    simp only [map_sum, map_pow, expand_X, ← pow_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring_nf
  rw [← hΦq, ← hexp, ← hΦp2, ← hΦp, q01Core, cyclotomic_prime ℤ p]
  ring


/-- Two integer polynomials whose difference is divisible by `X^N` agree below degree `N`. -/
theorem coeff_eq_of_X_pow_dvd_sub {f g : ℤ[X]} {N k : ℕ} (h : X ^ N ∣ f - g) (hk : k < N) :
    f.coeff k = g.coeff k := by
  have := (X_pow_dvd_iff.1 h) k hk
  rw [coeff_sub, sub_eq_zero] at this
  exact this

/-- Below degree `N`, the coefficient of `(Σ_{i<N} X^i)(Σ_{i<N} X^{m i})` at `n` is
`⌊n/m⌋ + 1`, the number of `i` with `m i ≤ n`. -/
theorem coeff_S1_S2 (m N n : ℕ) (hm : 0 < m) (hn : n < N) :
    ((∑ i ∈ range N, (X : ℤ[X]) ^ i) * ∑ i ∈ range N, ((X : ℤ[X]) ^ m) ^ i).coeff n =
      ((n / m + 1 : ℕ) : ℤ) := by
  have hS1 : ∀ d, (∑ i ∈ range N, (X : ℤ[X]) ^ i).coeff d = if d < N then 1 else 0 := by
    intro d
    simp [finsetSum_coeff, coeff_X_pow]
  rw [mul_sum, finsetSum_coeff]
  simp_rw [← pow_mul, coeff_mul_X_pow', hS1]
  have hfilt : ∀ i ∈ range N, (if m * i ≤ n then (if n - m * i < N then (1:ℤ) else 0) else 0)
      = if m * i ≤ n then 1 else 0 := by
    intro i _
    split_ifs <;> omega
  rw [Finset.sum_congr rfl hfilt, Finset.sum_boole]
  congr 1
  rw [← card_range (n / m + 1)]
  congr 1
  ext i
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨_, hi⟩
    rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hm]
    linarith
  · intro hi
    rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hm] at hi
    refine ⟨?_, by linarith⟩
    have : i ≤ i * m := Nat.le_mul_of_pos_right i hm
    omega


/-- `shiftCount m k a` is the number of `i : ℕ` with `a + m i ≤ k`, namely `⌊(k - a)/m⌋ + 1`
when `a ≤ k` and `0` otherwise (the `ℕ` subtraction is guarded by the test `a ≤ k`). -/
def shiftCount (m k a : ℕ) : ℤ := if a ≤ k then ((k - a) / m + 1 : ℕ) else 0

/-- **Coefficient formula.**  For distinct primes `p, q` and `k < pq`,
`[X^k] Φ_q² Φ_{p²q} = Σ_{j<p} (s(k, j) - 2 s(k, q + j) + s(k, 2q + j))` with
`s = shiftCount (p²)`.  This is the coefficient of `X^k` in
`(1 - X^q)² Φ_p(X) / ((1 - X)(1 - X^{p²}))`, to which `Φ_q² Φ_{p²q}` is congruent
modulo `X^{pq}` by `key_identity`. -/
theorem coeff_q01Core_eq (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (k : ℕ)
    (hk : k < p * q) :
    (q01Core p q).coeff k = ∑ j ∈ range p,
      (shiftCount (p ^ 2) k j - 2 * shiftCount (p ^ 2) k (q + j)
        + shiftCount (p ^ 2) k (2 * q + j)) := by
  set N := p * q with hN
  set m := p ^ 2 with hm
  have hm0 : 0 < m := pow_pos hp.pos 2
  set S1 : ℤ[X] := ∑ i ∈ range N, X ^ i with hS1
  set S2 : ℤ[X] := ∑ i ∈ range N, (X ^ m) ^ i with hS2
  set S : ℤ[X] := ∑ i ∈ range p, (X ^ (p * q) : ℤ[X]) ^ i with hS
  set E : ℤ[X] := (1 - X ^ q) ^ 2 * ∑ j ∈ range p, (X : ℤ[X]) ^ j with hE
  have hkey := key_identity p q hp hq hpq
  have hfull : q01Core p q * ((1 - X ^ N) * (1 - (X ^ m) ^ N)) = E * S * (S1 * S2) := by
    rw [← geom_sum_mul_neg (X : ℤ[X]) N, ← geom_sum_mul_neg ((X : ℤ[X]) ^ m) N]
    linear_combination (S1 * S2) * hkey
  -- left side agrees with `T` below degree `N`
  have hL : (q01Core p q * ((1 - X ^ N) * (1 - (X ^ m) ^ N))).coeff k = (q01Core p q).coeff k := by
    apply coeff_eq_of_X_pow_dvd_sub _ hk
    have hdN : (X : ℤ[X]) ^ N ∣ (X ^ m) ^ N := by
      rw [← pow_mul]; exact pow_dvd_pow _ (Nat.le_mul_of_pos_left N hm0)
    have hrw : q01Core p q * ((1 - X ^ N) * (1 - (X ^ m) ^ N)) - q01Core p q
        = -(q01Core p q * X ^ N) - q01Core p q * (X ^ m) ^ N + q01Core p q * X ^ N * (X ^ m) ^ N := by ring
    rw [hrw]
    exact dvd_add (dvd_sub (dvd_neg.2 (dvd_mul_left _ _)) (hdN.mul_left _))
      (hdN.mul_left _)
  -- right side: `S ≡ 1` below degree `N`
  have hR : (E * S * (S1 * S2)).coeff k = (E * (S1 * S2)).coeff k := by
    apply coeff_eq_of_X_pow_dvd_sub _ hk
    have hS1' : (X : ℤ[X]) ^ N ∣ S - 1 := by
      obtain ⟨r, hr⟩ : ∃ r, p = r + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
      have hrange : range p = range (r + 1) := by rw [hr]
      rw [hS, hrange, sum_range_succ', pow_zero, add_sub_cancel_right]
      exact dvd_sum fun i _ => by rw [pow_succ]; exact dvd_mul_left (X ^ N) _
    have hrw : E * S * (S1 * S2) - E * (S1 * S2) = (S - 1) * (E * (S1 * S2)) := by ring
    rw [hrw]
    exact hS1'.mul_right _
  rw [← hL, hfull, hR]
  have hEexp : E = ∑ j ∈ range p, (X ^ j - 2 * X ^ (q + j) + X ^ (2 * q + j)) := by
    rw [hE, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    ring
  rw [hEexp, sum_mul, finsetSum_coeff]
  refine sum_congr rfl fun j _ => ?_
  have hc : ∀ a : ℕ, (X ^ a * (S1 * S2)).coeff k = shiftCount m k a := by
    intro a
    rw [coeff_X_pow_mul', shiftCount]
    split_ifs with h
    · exact coeff_S1_S2 m N (k - a) hm0 (by omega)
    · rfl
  rw [add_mul, sub_mul, coeff_add, coeff_sub, mul_assoc, coeff_ofNat_mul, hc, hc, hc]


/-- For `k < m`, `shiftCount m k a` is the indicator of `a ≤ k`. -/
theorem shiftCount_of_lt {m k : ℕ} (a : ℕ) (hk : k < m) :
    shiftCount m k a = if a ≤ k then 1 else 0 := by
  unfold shiftCount
  split_ifs
  · rw [Nat.div_eq_of_lt (by omega)]; rfl
  · rfl

/-- The number of `j < n` with `a + j ≤ k` is `min n (k + 1 - a)`. -/
theorem sum_indicator (n a k : ℕ) :
    ∑ j ∈ range n, (if a + j ≤ k then (1 : ℤ) else 0) = ((min n (k + 1 - a) : ℕ) : ℤ) := by
  rw [Finset.sum_boole]
  congr 1
  rw [← card_range (min n (k + 1 - a))]
  congr 1
  ext j
  simp only [mem_filter, mem_range]
  omega

/-- For `k < m` the coefficient formula collapses to three interval counts:
`min p (k+1) - 2 min p (k+1-q) + min p (k+1-2q)`. -/
theorem sum_formula_of_lt (m k p q : ℕ) (hk : k < m) :
    ∑ j ∈ range p, (shiftCount m k j - 2 * shiftCount m k (q + j)
        + shiftCount m k (2 * q + j)) =
      ((min p (k + 1) : ℕ) : ℤ) - 2 * ((min p (k + 1 - q) : ℕ) : ℤ)
        + ((min p (k + 1 - 2 * q) : ℕ) : ℤ) := by
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum]
  simp only [shiftCount_of_lt _ hk]
  have h0 := sum_indicator p 0 k
  simp only [zero_add, Nat.sub_zero] at h0
  rw [h0, sum_indicator p q k, sum_indicator p (2 * q) k]

/-- If `y < 2m` then `y / m` is `0` (when `y < m`) or `1` (when `m ≤ y`). -/
theorem div_cases {y m : ℕ} (hy : y < 2 * m) :
    (y / m = 0 ∧ y < m) ∨ (y / m = 1 ∧ m ≤ y) := by
  rcases Nat.lt_or_ge y m with h | h
  · exact Or.inl ⟨Nat.div_eq_of_lt h, h⟩
  · exact Or.inr ⟨Nat.div_eq_of_lt_le (by omega) (by omega), h⟩

/-- Periodic regime: write `q = u m + v` and `k = q + p - 1 + (u + 1) m`.  Then the `j`-th
summand of the coefficient formula equals `⌊(v + x)/m⌋ + ⌊(m - v + x)/m⌋ - 1` with
`x = p - 1 - j`. -/
theorem case4_term (m u v p q k j : ℕ) (hm : 0 < m) (hv0 : 0 < v) (hvm : v < m)
    (h2p : 2 * p ≤ m) (hq : q = u * m + v) (hk : k = q + p - 1 + (u + 1) * m) (hj : j < p) :
    shiftCount m k j - 2 * shiftCount m k (q + j) + shiftCount m k (2 * q + j)
      = ((v + (p - 1 - j)) / m : ℕ) + ((m - v + (p - 1 - j)) / m : ℕ) - 1 := by
  have hum : (u + 1) * m = u * m + m := by ring
  have h2um : (2 * u + 1) * m = u * m + u * m + m := by ring
  have e1 : k - j = (v + (p - 1 - j)) + (2 * u + 1) * m := by subst hq hk; omega
  have e2 : k - (q + j) = (p - 1 - j) + (u + 1) * m := by subst hq hk; omega
  have e3 : k - (2 * q + j) = m - v + (p - 1 - j) := by subst hq hk; omega
  unfold shiftCount
  rw [if_pos (by subst hq hk; omega), if_pos (by subst hq hk; omega),
    if_pos (by subst hq hk; omega), e1, e2, e3, Nat.add_mul_div_right _ _ hm,
    Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt (a := p - 1 - j) (by omega)]
  push_cast
  ring

/-- For `v < m` and `2x < m`, `⌊(v + x)/m⌋ + ⌊(m - v + x)/m⌋ - 1 ≤ 0`: the two floors
cannot both equal `1`. -/
theorem case4_le (m v x : ℕ) (hm : 0 < m) (hvm : v < m) (h2x : 2 * x < m) :
    (((v + x) / m : ℕ) : ℤ) + ((m - v + x) / m : ℕ) - 1 ≤ 0 := by
  rcases div_cases (y := v + x) (m := m) (by omega) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
  rcases div_cases (y := m - v + x) (m := m) (by omega) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
  omega


/-- **Open direction of Conjecture con:q01, core form.**  For primes `p ≠ q` with `p` odd,
`Φ_q(x)² Φ_{p²q}(x)` has a negative coefficient.  Witnesses: `k = p` if `2q - 1 ≤ p`;
`k = 2q - 2` if `q < p ≤ 2q - 3` or if `p < q` with `2q - 2 < p²`; `k = q + p - 1 + (u + 1)p²`
(`u = ⌊q/p²⌋`) in the periodic regime `2q + p + p² - 1 ≤ pq`; and `k = 8` for `(p, q) = (3, 7)`. -/
theorem exists_coeff_q01Core_neg (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp2 : p ≠ 2) :
    ∃ k, (q01Core p q).coeff k < 0 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
  have hq2 : 2 ≤ q := hq.two_le
  set m := p ^ 2 with hm
  have hmp : 3 * p ≤ m := by rw [hm, sq]; exact Nat.mul_le_mul_right p hp3
  have hpq2 : 2 * q ≤ p * q := Nat.mul_le_mul_right q (by omega)
  have hpq3 : p * 2 ≤ p * q := Nat.mul_le_mul_left p hq2
  rcases Nat.lt_or_gt_of_ne hpq with hlt | hgt
  · -- `p < q`
    by_cases h3 : 2 * q - 2 < m
    · -- small `q`: the witness `k = 2q - 2`
      refine ⟨2 * q - 2, ?_⟩
      rw [coeff_q01Core_eq p q hp hq hpq _ (by omega), sum_formula_of_lt m _ p q h3]
      have e1 : min p (2 * q - 2 + 1) = p := by omega
      have e2 : min p (2 * q - 2 + 1 - q) = p := by omega
      have e3 : min p (2 * q - 2 + 1 - 2 * q) = 0 := by omega
      rw [e1, e2, e3]
      push_cast
      omega
    · by_cases h4 : 2 * q + p + m - 1 ≤ p * q
      · -- periodic regime: `q = u m + v`, witness `k = q + p - 1 + (u + 1) m`
        set u := q / m with hu
        set v := q % m with hv
        have hm0 : 0 < m := by omega
        have hqv : q = u * m + v := by rw [hu, hv, mul_comm]; exact (Nat.div_add_mod q m).symm
        have hvm : v < m := Nat.mod_lt q hm0
        have hv0 : 0 < v := by
          rcases Nat.eq_zero_or_pos v with h0 | h0
          · exfalso
            have hdvd : p ∣ q := by
              have hmq : m ∣ q := Nat.dvd_of_mod_eq_zero h0
              exact Nat.dvd_trans (dvd_pow_self p two_ne_zero) hmq
            exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 hdvd)
          · exact h0
        have hum : (u + 1) * m = u * m + m := by ring
        refine ⟨q + p - 1 + (u + 1) * m, ?_⟩
        rw [coeff_q01Core_eq p q hp hq hpq _ (by omega)]
        have hlast : p - 1 ∈ range p := mem_range.2 (by omega)
        calc ∑ j ∈ range p, (shiftCount m (q + p - 1 + (u + 1) * m) j
                - 2 * shiftCount m (q + p - 1 + (u + 1) * m) (q + j)
                + shiftCount m (q + p - 1 + (u + 1) * m) (2 * q + j))
            < ∑ _j ∈ range p, (0 : ℤ) := by
              apply Finset.sum_lt_sum
              · intro j hj
                rw [case4_term m u v p q _ j hm0 hv0 hvm (by omega) hqv rfl (mem_range.1 hj)]
                exact case4_le m v (p - 1 - j) hm0 hvm (by omega)
              · refine ⟨p - 1, hlast, ?_⟩
                rw [case4_term m u v p q _ (p - 1) hm0 hv0 hvm (by omega) hqv rfl (by omega),
                  Nat.sub_self, add_zero, add_zero, Nat.div_eq_of_lt hvm,
                  Nat.div_eq_of_lt (by omega)]
                norm_num
          _ = 0 := sum_const_zero
      · -- only `p = 3`, `q = 7` escapes both regimes
        have hp5 : p < 5 := by
          by_contra hcon
          have hcon' : 5 ≤ p := by omega
          have hmm : m = p * p := by rw [hm, sq]
          have hA : p * p + 2 ≤ 2 * q := by omega
          have hB : p * q + 2 ≤ 2 * q + p + p * p := by omega
          have h1 : p * (p * p + 2) ≤ p * (2 * q) := Nat.mul_le_mul_left p hA
          have h2 : 5 * q ≤ p * q := Nat.mul_le_mul_right q hcon'
          have h3 : 5 * (p * p) ≤ p * (p * p) := Nat.mul_le_mul_right (p * p) hcon'
          have h4 : 5 * p ≤ p * p := Nat.mul_le_mul_right p hcon'
          nlinarith
        have hp3' : p = 3 := by omega
        subst hp3'
        have hq7 : q = 7 := by
          have hlo : 6 ≤ q := by omega
          have hhi : q < 11 := by omega
          interval_cases q <;> first | rfl | norm_num at hq
        subst hq7
        refine ⟨8, ?_⟩
        rw [coeff_q01Core_eq 3 7 hp hq hpq 8 (by norm_num), sum_formula_of_lt (3 ^ 2) 8 3 7 (by norm_num)]
        norm_num
  · -- `q < p`
    have hpm : p < m := by omega
    by_cases h2 : 2 * q - 1 ≤ p
    · refine ⟨p, ?_⟩
      rw [coeff_q01Core_eq p q hp hq hpq _ (by omega), sum_formula_of_lt m _ p q hpm]
      have e1 : min p (p + 1) = p := by omega
      have e2 : min p (p + 1 - q) = p + 1 - q := by omega
      have e3 : min p (p + 1 - 2 * q) = p + 1 - 2 * q := by omega
      rw [e1, e2, e3]
      push_cast [Nat.cast_sub (show q ≤ p + 1 by omega),
        Nat.cast_sub (show 2 * q ≤ p + 1 by omega)]
      omega
    · refine ⟨2 * q - 2, ?_⟩
      rw [coeff_q01Core_eq p q hp hq hpq _ (by omega), sum_formula_of_lt m _ p q (by omega)]
      have e1 : min p (2 * q - 2 + 1) = p := by omega
      have e2 : min p (2 * q - 2 + 1 - q) = q - 1 := by omega
      have e3 : min p (2 * q - 2 + 1 - 2 * q) = 0 := by omega
      rw [e1, e2, e3]
      push_cast [Nat.cast_sub (show 1 ≤ q by omega)]
      omega


/-! ## Ground truth -/

example : shiftCount 9 8 0 = 1 := by decide
example : shiftCount 9 8 7 = 1 := by decide
example : shiftCount 9 8 9 = 0 := by decide
example : shiftCount 4 9 1 = 3 := by decide

/-- `Φ_2² Φ_18 = (1 + x)² (1 - x³ + x⁶)` has `[x³] = -1`. -/
example : (q01Core 3 2).coeff 3 = -1 := by
  rw [coeff_q01Core_eq 3 2 Nat.prime_three Nat.prime_two (by norm_num) 3 (by norm_num),
    sum_formula_of_lt (3 ^ 2) 3 3 2 (by norm_num)]
  norm_num

/-- `[x^0] Φ_2² Φ_18 = 1` and `[x^1] Φ_2² Φ_18 = 2`. -/
example : (q01Core 3 2).coeff 0 = 1 ∧ (q01Core 3 2).coeff 1 = 2 := by
  constructor
  · rw [coeff_q01Core_eq 3 2 Nat.prime_three Nat.prime_two (by norm_num) 0 (by norm_num),
      sum_formula_of_lt (3 ^ 2) 0 3 2 (by norm_num)]
    norm_num
  · rw [coeff_q01Core_eq 3 2 Nat.prime_three Nat.prime_two (by norm_num) 1 (by norm_num),
      sum_formula_of_lt (3 ^ 2) 1 3 2 (by norm_num)]
    norm_num

/-- The hypotheses of the main theorem are jointly satisfiable (`p = 3`, `q = 2`). -/
example : Nat.Prime 3 ∧ Nat.Prime 2 ∧ (3 : ℕ) ≠ 2 ∧ (3 : ℕ) ≠ 2 := by norm_num

/-! ## Main theorem -/

/-- **Conjecture con:q01 of arXiv:2606.20311, the direction left open there.**
For all primes `p ≠ q` with `p` odd, `Q_{01}(x) = x Φ_q(x)² Φ_{p²q}(x)` has a negative
coefficient over `ℤ`.  (The paper proves the `p = 2` case as Theorem thm:q01_coeffs and offers
only numerical evidence for odd `p`.) -/
theorem con_q01_odd (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hp2 : p ≠ 2) :
    ∃ k, (Q01 p q).coeff k < 0 := by
  obtain ⟨k, hk⟩ := exists_coeff_q01Core_neg p q hp hq hpq hp2
  exact ⟨k + 1, by rw [coeff_Q01_succ]; exact hk⟩

end DiceRelabelingSquareSided
