/-
# Prime circles on `{1, …, 2n}` from four primes (Chen–Fu–Guo)

## Source

* MathOverflow question 100265, "Not especially famous, long-open problems
  which anyone can understand" (asked by David Feldman),
  answer https://mathoverflow.net/a/130466 by Santi Spadaro (2013-05-13),
  quoted verbatim:

  > Let $G_n$ be the graph with vertex set $\{1, 2, \dots, 2n\}$ such that
  > $\{i,j\}$ is an edge if and only if $i+j$ is a prime number. Is it true
  > that $G_n$ is Hamiltonian for every $n \geq 2$?

  (The prime circle problem, Filz 1982, J. Recreational Math. problem #1046;
  OEIS A051252: "There is no known proof that a(n) > 0 for all n.")
* H.-B. Chen, H.-L. Fu, J.-Y. Guo, "From a Consequence of Bertrand's
  Postulate to Hamilton Cycles", arXiv:1804.07104, Theorem 1.2 (verbatim):

  > $G_{2n}$, $n\geq 2$, contains a Hamilton cycle if there exist two primes
  > $p_1<p_2$ in $[1,2n]$ ($p_1$ can be 1) such that $2n+p_1$ and $2n+p_2$
  > are primes and $\gcd\left(\frac{p_2-p_1}{2},n\right)=1$.

  and Corollary 1.3: "if $2n+1$ and $2n+3$ are twin primes, then $G_{2n}$ has
  a Hamilton cycle" (OEIS A072618 comment (a), due to Mike Hennebry).

Date recorded: 2026-10-21.

## Status

The general prime circle conjecture is open. The four-prime sufficient
condition (Theorem 1.2) and its twin-prime corollary are proved in the
literature (arXiv:1804.07104); this module kernel-checks both, using the
paper's explicit cycle. The infinitude result of the paper (via
Maynard–Polymath bounded gaps) is out of scope.

## Construction

With `s = (p₁ - 1)/2`, `t = (p₂ - 1)/2`, `d = t - s`, position `2m` of the
circle holds the odd number `2 (m d mod n) + 1` and position `2m + 1` holds
the even number `2n - 2 ((m d + n - s) mod n)`. Adjacent sums are among
`p₁, 2n + p₁, p₂, 2n + p₂`; `gcd(d, n) = 1` makes the arrangement injective.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.PrimeCircleFourPrimes

/-! ## Definitions -/

/-- A *prime circle* on `{1, …, 2n}`: a cyclic arrangement `c` of the positions
`Fin (2n)` that is a bijection onto `{1, …, 2n}` (injective with image exactly
`Finset.Icc 1 (2n)`) such that every pair of cyclically adjacent entries
`c i, c (i + 1 mod 2n)` has prime sum. Equivalently, a Hamilton cycle in the
prime sum graph `G_{2n}` of Chen–Fu–Guo. -/
def IsPrimeCircle (n : ℕ) (c : Fin (2 * n) → ℕ) : Prop :=
  Function.Injective c ∧ Finset.univ.image c = Finset.Icc 1 (2 * n) ∧
    ∀ i, (c i + c (finRotate (2 * n) i)).Prime

/-- The Chen–Fu–Guo arrangement, as a function of the position `i : ℕ`, with
parameters `n` (half the length), `s = (p₁ - 1)/2` and `d = (p₂ - p₁)/2`.
Even position `2m` holds the odd number `x_j = 2j + 1` with `j = m d mod n`;
odd position `2m + 1` holds the even number `y_k = 2n - 2k` with
`k = (m d + (n - s)) mod n`, i.e. `j - k ≡ s (mod n)`. -/
def circ (n s d i : ℕ) : ℕ :=
  if i % 2 = 0 then 2 * (i / 2 * d % n) + 1 else 2 * n - 2 * ((i / 2 * d + (n - s)) % n)

/-! ## Ground truth -/

/-- Twin-prime case `n = 2` (`5, 7` prime, `s = 0`, `d = 1`): the circle `1, 4, 3, 2`. -/
example : (List.range 4).map (circ 2 0 1) = [1, 4, 3, 2] := by decide

/-- Case `n = 4`, `p₁ = 3`, `p₂ = 5` (`s = 1`, `d = 1`): the circle
`1, 2, 3, 8, 5, 6, 7, 4`, with adjacent sums `3, 5, 11, 13, 11, 13, 11, 5`. -/
example : (List.range 8).map (circ 4 1 1) = [1, 2, 3, 8, 5, 6, 7, 4] := by decide

/-- `1, 4, 3, 2` is a prime circle on `{1, 2, 3, 4}`. -/
example : IsPrimeCircle 2 ![1, 4, 3, 2] := by
  refine ⟨by decide, by decide, ?_⟩
  decide

/-- `1, 3, 2, 4` is not a prime circle: the adjacent sum `1 + 3 = 4` is not prime. -/
example : ¬ IsPrimeCircle 2 ![1, 3, 2, 4] := by
  rintro ⟨-, -, h⟩
  exact absurd (h 0) (by decide)

/-- The hypotheses of the main theorem are jointly satisfiable with `p₁` an
actual prime: `n = 4`, `p₁ = 3`, `p₂ = 5`. -/
example : (2 ≤ 4) ∧ (3 = 1 ∨ Nat.Prime 3) ∧ Nat.Prime 5 ∧ 3 < 5 ∧ 5 ≤ 2 * 4 ∧
    (2 * 4 + 3).Prime ∧ (2 * 4 + 5).Prime ∧ Nat.Coprime ((5 - 3) / 2) 4 := by
  refine ⟨by norm_num, Or.inr Nat.prime_three, Nat.prime_five, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩

/-! ## Helper lemmas -/

/-- The value of `finRotate N i` is `(i + 1) mod N`. -/
theorem val_finRotate (N : ℕ) (i : Fin N) : (finRotate N i).val = (i.val + 1) % N := by
  haveI := i.neZero
  rw [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]

/-- The arrangement `circ` is periodic with period `2n`. -/
theorem circ_add_period (n s d i : ℕ) : circ n s d (i + 2 * n) = circ n s d i := by
  have h2 : (i + 2 * n) % 2 = i % 2 := by omega
  have hdiv : (i + 2 * n) / 2 = i / 2 + n := by omega
  have hA : (i / 2 + n) * d % n = i / 2 * d % n := by
    rw [add_mul, Nat.add_mul_mod_self_left]
  have hB : ((i / 2 + n) * d + (n - s)) % n = (i / 2 * d + (n - s)) % n := by
    rw [add_mul, add_right_comm, Nat.add_mul_mod_self_left]
  unfold circ
  rw [h2, hdiv, hA, hB]

/-- Core arithmetic: if `k + s ≡ j (mod n)` with `j, k, s < n`, then
`x_j + y_k = (2j + 1) + (2n - 2k)` equals `2n + (2s + 1)` (no wrap) or
`2s + 1` (wrap, `j + n = k + s`). -/
theorem sum_cases (n s j k : ℕ) (hk : k < n) (hs : s < n) (h : (k + s) % n = j) :
    (2 * j + 1) + (2 * n - 2 * k) = 2 * n + (2 * s + 1) ∨
      ((2 * j + 1) + (2 * n - 2 * k) = 2 * s + 1 ∧ j + n = k + s) := by
  rcases Nat.lt_or_ge (k + s) n with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h
    left
    omega
  · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at h
    right
    omega

/-- Every adjacent sum of the arrangement is one of `2n + (2s+1)`, `2s+1` (only
when `0 < s`), `2n + (2t+1)`, `2t+1`, where `t = s + d < n`. -/
theorem circ_adj (n s d i : ℕ) (hst : s + d < n) :
    (circ n s d i + circ n s d (i + 1) = 2 * n + (2 * s + 1) ∨
      (circ n s d i + circ n s d (i + 1) = 2 * s + 1 ∧ 0 < s)) ∨
    (circ n s d i + circ n s d (i + 1) = 2 * n + (2 * (s + d) + 1) ∨
      circ n s d i + circ n s d (i + 1) = 2 * (s + d) + 1) := by
  have hn : 0 < n := by omega
  rcases Nat.even_or_odd' i with ⟨m, rfl | rfl⟩
  · left
    have he : 2 * m % 2 = 0 := by omega
    have ho : (2 * m + 1) % 2 = 1 := by omega
    have hq1 : 2 * m / 2 = m := by omega
    have hq2 : (2 * m + 1) / 2 = m := by omega
    have hkey : ((m * d + (n - s)) % n + s) % n = m * d % n := by
      rw [Nat.mod_add_mod, add_assoc, Nat.sub_add_cancel (by omega), Nat.add_mod_right]
    have h := sum_cases n s (m * d % n) ((m * d + (n - s)) % n)
      (Nat.mod_lt _ hn) (by omega) hkey
    simp only [circ, he, ho, hq1, hq2, if_true, one_ne_zero, if_false]
    rcases h with h | ⟨h, hwrap⟩
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      have hj := Nat.mod_lt (m * d + (n - s)) hn
      omega
  · right
    have he : (2 * m + 1 + 1) % 2 = 0 := by omega
    have ho : (2 * m + 1) % 2 = 1 := by omega
    have hq1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    have hq2 : (2 * m + 1) / 2 = m := by omega
    have hkey : ((m * d + (n - s)) % n + (s + d)) % n = (m + 1) * d % n := by
      rw [Nat.mod_add_mod, add_mul, one_mul,
        show m * d + (n - s) + (s + d) = m * d + d + n by omega, Nat.add_mod_right]
    have h := sum_cases n (s + d) ((m + 1) * d % n) ((m * d + (n - s)) % n)
      (Nat.mod_lt _ hn) hst hkey
    simp only [circ, he, ho, hq1, hq2, if_true, one_ne_zero, if_false]
    rcases h with h | ⟨h, -⟩
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

/-- Every entry of the arrangement lies in `{1, …, 2n}`. -/
theorem circ_mem (n s d i : ℕ) (hn : 0 < n) : circ n s d i ∈ Finset.Icc 1 (2 * n) := by
  have h1 := Nat.mod_lt (i / 2 * d) hn
  have h2 := Nat.mod_lt (i / 2 * d + (n - s)) hn
  rw [Finset.mem_Icc]
  unfold circ
  split_ifs <;> omega

/-- Cancellation of a unit: if `gcd(d, n) = 1`, `m, m' < n` and
`m d ≡ m' d (mod n)`, then `m = m'`. -/
theorem eq_of_mul_modEq (n d m m' : ℕ) (hcop : Nat.Coprime d n) (hm : m < n) (hm' : m' < n)
    (h : m * d ≡ m' * d [MOD n]) : m = m' := by
  have h' := Nat.ModEq.cancel_right_of_coprime (Nat.Coprime.symm hcop) h
  unfold Nat.ModEq at h'
  rwa [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hm'] at h'

/-- On the positions `0, …, 2n - 1` the arrangement is injective when
`gcd(d, n) = 1`. -/
theorem circ_inj (n s d i i' : ℕ) (hcop : Nat.Coprime d n) (hi : i < 2 * n) (hi' : i' < 2 * n)
    (h : circ n s d i = circ n s d i') : i = i' := by
  have hn : 0 < n := by omega
  have a1 := Nat.mod_lt (i / 2 * d + (n - s)) hn
  have a2 := Nat.mod_lt (i' / 2 * d + (n - s)) hn
  have hm : i / 2 < n := by omega
  have hm' : i' / 2 < n := by omega
  unfold circ at h
  split_ifs at h with hp hp'
  · have hmod : i / 2 * d ≡ i' / 2 * d [MOD n] := by
      unfold Nat.ModEq
      omega
    have heq := eq_of_mul_modEq n d _ _ hcop hm hm' hmod
    omega
  · omega
  · omega
  · have hmod : i / 2 * d + (n - s) ≡ i' / 2 * d + (n - s) [MOD n] := by
      unfold Nat.ModEq
      omega
    have heq := eq_of_mul_modEq n d _ _ hcop hm hm' (Nat.ModEq.add_right_cancel' _ hmod)
    omega

/-- If `2n + p` is prime (`0 < n`) and `p` is `1` or prime, then `p` is odd. -/
theorem odd_of_prime_add (n p : ℕ) (hn : 0 < n) (hp : p = 1 ∨ p.Prime)
    (hq : (2 * n + p).Prime) : Odd p := by
  rcases hp with rfl | hp
  · exact odd_one
  · rcases hp.eq_two_or_odd' with rfl | ho
    · have he : Even (2 * n + 2) := ⟨n + 1, by ring⟩
      have h2 := hq.even_iff.mp he
      omega
    · exact ho

/-- Reading the arrangement at the cyclic successor position is reading it at
`i + 1`, thanks to `2n`-periodicity. -/
theorem circ_finRotate (n s d : ℕ) (i : Fin (2 * n)) :
    circ n s d (finRotate (2 * n) i).val = circ n s d (i.val + 1) := by
  rw [val_finRotate]
  rcases Nat.lt_or_ge (i.val + 1) (2 * n) with h | h
  · rw [Nat.mod_eq_of_lt h]
  · have he : i.val + 1 = 0 + 2 * n := by omega
    rw [he, Nat.add_mod_right, circ_add_period, Nat.zero_mod]

/-! ## Main results -/

/-- **Chen–Fu–Guo, Theorem 1.2** (arXiv:1804.07104), on the prime circle
problem of MathOverflow answer 130466: let `n ≥ 2` and let `p₁ < p₂ ≤ 2n`,
where `p₁` is `1` or a prime and `p₂` is a prime, such that `2n + p₁` and
`2n + p₂` are prime and `gcd((p₂ - p₁)/2, n) = 1`. Then `{1, …, 2n}` admits a
prime circle: a cyclic arrangement in which every two adjacent numbers have
prime sum (a Hamilton cycle of the prime sum graph `G_{2n}`). -/
theorem prime_circle_of_four_primes (n p₁ p₂ : ℕ) (hn : 2 ≤ n) (h₁ : p₁ = 1 ∨ p₁.Prime)
    (h₂ : p₂.Prime) (hlt : p₁ < p₂) (hle : p₂ ≤ 2 * n) (hq₁ : (2 * n + p₁).Prime)
    (hq₂ : (2 * n + p₂).Prime) (hg : Nat.Coprime ((p₂ - p₁) / 2) n) :
    ∃ c : Fin (2 * n) → ℕ, IsPrimeCircle n c := by
  have hn0 : 0 < n := by omega
  have ho₁ := Nat.odd_iff.mp (odd_of_prime_add n p₁ hn0 h₁ hq₁)
  have ho₂ := Nat.odd_iff.mp (odd_of_prime_add n p₂ hn0 (Or.inr h₂) hq₂)
  set s := p₁ / 2 with hs
  set d := p₂ / 2 - p₁ / 2 with hd
  have hp₁ : p₁ = 2 * s + 1 := by omega
  have hp₂ : p₂ = 2 * (s + d) + 1 := by omega
  have hst : s + d < n := by omega
  have hcop : Nat.Coprime d n := by
    have hdeq : (p₂ - p₁) / 2 = d := by omega
    rwa [hdeq] at hg
  have hinj : Function.Injective (fun i : Fin (2 * n) => circ n s d i.val) :=
    fun i i' h => Fin.ext (circ_inj n s d i i' hcop i.isLt i'.isLt h)
  refine ⟨fun i => circ n s d i.val, hinj, ?_, ?_⟩
  · apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact circ_mem n s d i hn0
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin,
        Nat.card_Icc]
      omega
  · intro i
    show (circ n s d i.val + circ n s d (finRotate (2 * n) i).val).Prime
    rw [circ_finRotate]
    rcases circ_adj n s d i hst with (h | ⟨h, hpos⟩) | (h | h) <;> rw [h]
    · rwa [← hp₁]
    · rcases h₁ with h₁ | h₁
      · omega
      · rwa [← hp₁]
    · rwa [← hp₂]
    · rwa [← hp₂]

/-- **Chen–Fu–Guo, Corollary 1.3** (OEIS A072618 comment (a), due to Mike
Hennebry): if `n ≥ 2` and `2n + 1`, `2n + 3` are twin primes, then
`{1, …, 2n}` admits a prime circle. This is Theorem 1.2 with `p₁ = 1`,
`p₂ = 3`. -/
theorem prime_circle_of_twin_primes (n : ℕ) (hn : 2 ≤ n) (h₁ : (2 * n + 1).Prime)
    (h₃ : (2 * n + 3).Prime) : ∃ c : Fin (2 * n) → ℕ, IsPrimeCircle n c :=
  prime_circle_of_four_primes n 1 3 hn (Or.inl rfl) Nat.prime_three (by norm_num) (by omega)
    h₁ h₃ (by norm_num)

end Candidates.PrimeCircleFourPrimes
