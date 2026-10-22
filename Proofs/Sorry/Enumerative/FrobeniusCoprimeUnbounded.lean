/-
# Coprime-coefficient Frobenius number: `g(a,b)/(ab)` is unbounded

## Source

arXiv:2610.17267, Grace Natalie Jaffe, "Denominators in the Farey Sequence,
the Stern Sequence, and the Frobenius Problem with Relatively Prime
Multipliers".  Retrieved 2026-10-21.

* Section "The Frobenius Connection": for positive coprime `a, b`,
  `g(a,b)` is "the largest integer that cannot be expressed as `ax+by` for
  *relatively prime*, non-negative integers `x,y`; if no such integer
  exists, we will say `g(a,b)=∞`".
* Theorem `thm:fareyub` bounds `g(a,b)` above by `ab · j(N(a,b))` with `j`
  Jacobsthal's function, and Section "Future Directions" asks
  (`conj:frob`) only whether `g(a,b) ≥ 4 f(a,b)`, `f(a,b) = ab - a - b`.

## Claim (not in the paper)

> `g(a,b)/(ab)` is unbounded: `g(a,b) ≥ (2r-2)ab` when
> `min(a,b) ≥ p_1 ⋯ p_r` (the product of the first `r` primes).

## Status

Not stated in Jaffe's paper (its lower-bound discussion stops at the
conjecture `g ≥ 4f`).  Unboundedness of `g(a,b)/(ab)` itself is not new:
Ding, Wang and Zhang, "The Diophantine Frobenius Problem revisited",
arXiv:2509.08599 (September 2025, not cited by Jaffe), study the same
quantity `G_{a_1,a_2}` and prove `a_1 a_2 ≤ G ≪ a_1 a_2 (log a_1 a_2)^2`,
`G_{2,a} = 4a - 2`, and, for fixed `a_1 > 2`, `limsup G/(a_2 log a_2) > 0`,
which already implies that `G/(a_1 a_2)` is unbounded.  The contribution of
this module is the uniform explicit lower bound `g(a,b) ≥ (2r-2)ab` for
every coprime pair with `min(a,b) ≥ p_1 ⋯ p_r` (so `g ≥ 4ab` once
`min(a,b) ≥ 30`), which implies `conj:frob` in that range; no source for
this uniform bound was found (search coverage: arXiv and web, no
MathSciNet).

## Formal reading

`g(a,b) ≥ (2r-2)ab` (with `g = ∞` allowed) is the existence of an integer
`n ≥ (2r-2)ab` with no representation `n = ax+by`, `x,y ≥ 0`,
`gcd(x,y) = 1`.  The main theorem `exists_not_coprimeRep_of_primeProd_le`
uses the product `primeProd r = p₁ ⋯ p_{r+1}` of the first `r+1` primes and
the bound `2r · ab`; `exists_not_coprimeRep_of_prod_first_primes_le` is the
paper-indexed form (`r ≥ 1` primes, bound `(2r-2)ab`), and
`exists_not_coprimeRep_of_primorial_le` the form with Mathlib's `primorial`.
`coprimeRep_ratio_unbounded` is the unboundedness of `g(a,b)/(ab)`.

## Proof outline

*Covering lemma.*  If `gcd(a,b) = 1` and `x₀ < b`, every non-negative
solution of `ax+by = ax₀+by₀` is `(x₀+bk, y₀-ak)` with `ak ≤ y₀`.

*Modular witnesses.*  With `x₀ = λb mod M` and `M ∣ y₀ + λa`, the number
`gcd(M, λ+k)` divides both `x₀+bk` and `y₀-ak`.

*Covering of `λ, …, λ+2r` by the first `r+1` primes.*  By the Chinese
remainder theorem choose `λ` even with `p_i ∣ λ + (2i-1)` for the odd primes
`p_i = nth Prime i`, `1 ≤ i ≤ r`.  Then every `λ+k`, `0 ≤ k ≤ 2r`, shares a
prime with `M = primeProd r`.  Take `y₀ ∈ [2ra, 2ra + M)` with
`M ∣ y₀ + λa`; since `M ≤ a`, `ak ≤ y₀` forces `k ≤ 2r`, and since `M ≤ b`,
`x₀ < b`.  The witness is `a x₀ + b y₀ ≥ 2r · ab`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.FrobeniusCoprimeUnbounded

open Finset

/-! ## Definitions -/

/-- `CoprimeRep a b n`: the paper's "`n` can be expressed as `ax+by` for relatively
prime, non-negative integers `x, y`". -/
def CoprimeRep (a b n : ℕ) : Prop :=
  ∃ x y : ℕ, a * x + b * y = n ∧ Nat.Coprime x y

/-- The coprime-coefficient Frobenius number `g(a,b)`: the supremum of the integers with no
coprime representation.  It is the paper's `g(a,b)` whenever that set is bounded above
(the paper's existence theorem); otherwise `sSup` takes its junk value `0`, so every
statement about it below carries the boundedness hypothesis explicitly. -/
noncomputable def coprimeFrobenius (a b : ℕ) : ℕ :=
  sSup {n : ℕ | ¬ CoprimeRep a b n}

/-- `primeProd r = p₁ p₂ ⋯ p_{r+1}`: the product of the first `r + 1` primes
(`Nat.nth Nat.Prime 0 = 2`). -/
noncomputable def primeProd (r : ℕ) : ℕ :=
  ∏ i ∈ range (r + 1), Nat.nth Nat.Prime i

/-! ## Ground truth -/

/-- `primeProd 2 = 2 · 3 · 5 = 30`. -/
theorem primeProd_two : primeProd 2 = 30 := by
  simp [primeProd, Finset.prod_range_succ, Nat.nth_prime_zero_eq_two,
    Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]

/-- Mathlib's `primorial 5 = 2 · 3 · 5 = 30`. -/
theorem primorial_five : primorial 5 = 30 := by
  decide

example : CoprimeRep 5 7 12 := ⟨1, 1, by norm_num, by decide⟩

/-! ## The covering lemma -/

/-- For coprime `a, b` and `x₀ < b`, every non-negative solution of
`a x + b y = a x₀ + b y₀` is `x = x₀ + b k`, `y = y₀ - a k` for some `k` with `a k ≤ y₀`. -/
theorem eq_of_mul_add_mul_eq {a b x0 y0 x y : ℕ} (hab : Nat.Coprime a b) (hx0 : x0 < b)
    (h : a * x + b * y = a * x0 + b * y0) :
    ∃ k : ℕ, x = x0 + b * k ∧ a * k + y = y0 := by
  have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le x0) hx0
  have hmod : a * x ≡ a * x0 [MOD b] := by
    have h' := congrArg (· % b) h
    simpa [Nat.ModEq, Nat.add_mul_mod_self_left] using h'
  have hx : x ≡ x0 [MOD b] := Nat.ModEq.cancel_left_of_coprime hab.symm hmod
  have hxmod : x % b = x0 := by
    rw [hx]
    exact Nat.mod_eq_of_lt hx0
  have hxk : x = x0 + b * (x / b) := by
    have hdiv := Nat.mod_add_div x b
    omega
  refine ⟨x / b, hxk, ?_⟩
  rw [hxk] at h
  have hbb : b * (a * (x / b) + y) = b * y0 := by
    rw [← Nat.add_left_cancel_iff (n := a * x0), ← h]
    ring
  exact Nat.eq_of_mul_eq_mul_left hb hbb

/-- Covering lemma: if `gcd(a,b) = 1`, `x₀ < b`, and no pair `(x₀ + b k, y₀ - a k)` with
`a k ≤ y₀` is coprime, then `a x₀ + b y₀` has no coprime representation. -/
theorem not_coprimeRep_of_cover {a b x0 y0 : ℕ} (hab : Nat.Coprime a b) (hx0 : x0 < b)
    (hcov : ∀ k : ℕ, a * k ≤ y0 → ¬ Nat.Coprime (x0 + b * k) (y0 - a * k)) :
    ¬ CoprimeRep a b (a * x0 + b * y0) := by
  rintro ⟨x, y, hxy, hco⟩
  obtain ⟨k, hxk, hyk⟩ := eq_of_mul_add_mul_eq hab hx0 hxy
  have hle : a * k ≤ y0 := by omega
  have hy : y = y0 - a * k := by omega
  subst hxk hy
  exact hcov k hle hco

/-- Modular witnesses: with `x₀ = λ b mod M` and `M ∣ y₀ + λ a`, the number `gcd(M, λ+k)`
divides both `x₀ + b k` and `y₀ - a k`; so if it differs from `1` whenever `a k ≤ y₀`,
then `a x₀ + b y₀` has no coprime representation. -/
theorem not_coprimeRep_of_modular {a b M lam y0 : ℕ} (hab : Nat.Coprime a b)
    (hx0 : lam * b % M < b) (hM : M ∣ y0 + lam * a)
    (hcov : ∀ k : ℕ, a * k ≤ y0 → Nat.gcd M (lam + k) ≠ 1) :
    ¬ CoprimeRep a b (a * (lam * b % M) + b * y0) := by
  refine not_coprimeRep_of_cover hab hx0 fun k hk hco => hcov k hk ?_
  set d := Nat.gcd M (lam + k) with hd
  have hdM : d ∣ M := Nat.gcd_dvd_left M (lam + k)
  have hdl : d ∣ lam + k := Nat.gcd_dvd_right M (lam + k)
  have hdx : d ∣ lam * b % M + b * k := by
    have hsplit : lam * b % M + b * k + M * (lam * b / M) = b * (lam + k) := by
      have hdiv := Nat.mod_add_div (lam * b) M
      have hc : b * lam = lam * b := mul_comm b lam
      rw [mul_add]
      omega
    have h2 : d ∣ lam * b % M + b * k + M * (lam * b / M) := by
      rw [hsplit]
      exact Dvd.dvd.mul_left hdl b
    exact (Nat.dvd_add_left (Dvd.dvd.mul_right hdM _)).mp h2
  have hdy : d ∣ y0 - a * k := by
    have hsplit : y0 - a * k + a * (lam + k) = y0 + lam * a := by
      have hc : a * lam = lam * a := mul_comm a lam
      rw [mul_add]
      omega
    have h2 : d ∣ y0 - a * k + a * (lam + k) := by
      rw [hsplit]
      exact hdM.trans hM
    exact (Nat.dvd_add_left (Dvd.dvd.mul_left hdl a)).mp h2
  have hdd : Nat.Coprime d d :=
    Nat.Coprime.coprime_dvd_left hdx (Nat.Coprime.coprime_dvd_right hdy hco)
  exact Nat.Coprime.eq_one_of_dvd hdd (dvd_refl d)

/-- The paper's running example: `5x + 7y = 156` has the solutions `(6,18), (13,13), (20,8),
(27,3)`, none coprime, so `156` has no coprime representation by `5, 7`. -/
theorem not_coprimeRep_five_seven : ¬ CoprimeRep 5 7 156 := by
  have hcov : ∀ k : ℕ, 5 * k ≤ 18 → ¬ Nat.Coprime (6 + 7 * k) (18 - 5 * k) := by
    intro k hk
    have hk3 : k ≤ 3 := by omega
    interval_cases k <;> decide
  exact not_coprimeRep_of_cover (x0 := 6) (y0 := 18) (by norm_num) (by norm_num) hcov

/-! ## The first primes and the Jacobsthal-type covering -/

/-- `n ↦ p_{n+1}` is injective. -/
theorem nth_prime_injective : Function.Injective (Nat.nth Nat.Prime) :=
  Nat.nth_injective Nat.infinite_setOfPred_prime

/-- Each of the first `r + 1` primes divides `primeProd r`. -/
theorem nth_prime_dvd_primeProd {i r : ℕ} (hi : i ≤ r) : Nat.nth Nat.Prime i ∣ primeProd r :=
  Finset.dvd_prod_of_mem _ (mem_range.mpr (Nat.lt_succ_of_le hi))

/-- `primeProd r` is positive. -/
theorem primeProd_pos (r : ℕ) : 0 < primeProd r :=
  Finset.prod_pos fun i _ => (Nat.prime_nth_prime i).pos

/-- The product of the first `r + 1` primes divides Mathlib's `primorial (p_{r+1})`
(they are equal; divisibility is all that is used). -/
theorem primeProd_dvd_primorial (r : ℕ) : primeProd r ∣ primorial (Nat.nth Nat.Prime r) := by
  unfold primeProd primorial
  have himg : ∏ i ∈ range (r + 1), Nat.nth Nat.Prime i
      = ∏ p ∈ (range (r + 1)).image (Nat.nth Nat.Prime), p :=
    (Finset.prod_image (f := fun p => p) fun i _ j _ h => nth_prime_injective h).symm
  rw [himg]
  refine Finset.prod_dvd_prod_of_subset _ _ _ ?_
  intro p hp
  simp only [mem_image, mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  simp only [mem_filter, mem_range]
  refine ⟨?_, Nat.prime_nth_prime i⟩
  have hle : Nat.nth Nat.Prime i ≤ Nat.nth Nat.Prime r :=
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone (show i ≤ r by omega)
  omega

/-- Chinese remainder step: there is an even `λ` with `p_{i+1} ∣ λ + (2i - 1)` for every
`1 ≤ i ≤ r` (here `p_{i+1} = Nat.nth Nat.Prime i` is the `i`-th odd prime). -/
theorem exists_lambda (r : ℕ) :
    ∃ lam : ℕ, 2 ∣ lam ∧ ∀ i, 1 ≤ i → i ≤ r → Nat.nth Nat.Prime i ∣ lam + (2 * i - 1) := by
  let c : ℕ → ℕ := fun i => (2 * i - 1) * (Nat.nth Nat.Prime i - 1)
  have hs : ∀ i ∈ range (r + 1), Nat.nth Nat.Prime i ≠ 0 :=
    fun i _ => (Nat.prime_nth_prime i).ne_zero
  have pp : Set.Pairwise (range (r + 1) : Set ℕ)
      (Function.onFun Nat.Coprime (Nat.nth Nat.Prime)) :=
    fun i _ j _ hij => (Nat.coprime_primes (Nat.prime_nth_prime i) (Nat.prime_nth_prime j)).mpr
      (fun h => hij (nth_prime_injective h))
  obtain ⟨lam, hlam⟩ := Nat.chineseRemainderOfFinset c (Nat.nth Nat.Prime) (range (r + 1)) hs pp
  refine ⟨lam, ?_, fun i hi1 hir => ?_⟩
  · have h0 := hlam 0 (by simp)
    simp only [c, Nat.nth_prime_zero_eq_two] at h0
    exact (Nat.modEq_zero_iff_dvd).mp (by simpa using h0)
  · have hi := hlam i (mem_range.mpr (by omega))
    have hp := (Nat.prime_nth_prime i).one_le
    refine (Nat.modEq_zero_iff_dvd).mp ?_
    have h2 := hi.add_right (2 * i - 1)
    refine h2.trans ?_
    simp only [c]
    have hsplit : (2 * i - 1) * (Nat.nth Nat.Prime i - 1) + (2 * i - 1)
        = (2 * i - 1) * Nat.nth Nat.Prime i := by
      rw [Nat.mul_sub_one]
      have hle : 2 * i - 1 ≤ (2 * i - 1) * Nat.nth Nat.Prime i := Nat.le_mul_of_pos_right _ hp
      omega
    rw [hsplit]
    exact (Nat.modEq_zero_iff_dvd).mpr (dvd_mul_left _ _)

/-- Jacobsthal-type covering: for the `λ` of `exists_lambda`, each of the `2r + 1`
consecutive integers `λ, λ+1, …, λ+2r` shares a prime factor with `primeProd r`. -/
theorem gcd_primeProd_ne_one {r lam k : ℕ} (h2 : 2 ∣ lam)
    (hodd : ∀ i, 1 ≤ i → i ≤ r → Nat.nth Nat.Prime i ∣ lam + (2 * i - 1)) (hk : k ≤ 2 * r) :
    Nat.gcd (primeProd r) (lam + k) ≠ 1 := by
  have key : ∃ p, p.Prime ∧ p ∣ primeProd r ∧ p ∣ lam + k := by
    rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · refine ⟨2, Nat.prime_two, ?_, ?_⟩
      · have h0 := nth_prime_dvd_primeProd (Nat.zero_le r)
        rwa [Nat.nth_prime_zero_eq_two] at h0
      · exact Nat.dvd_add h2 ⟨m, by omega⟩
    · refine ⟨Nat.nth Nat.Prime (m + 1), Nat.prime_nth_prime _,
        nth_prime_dvd_primeProd (by omega), ?_⟩
      have hd := hodd (m + 1) (by omega) (by omega)
      have hk' : 2 * (m + 1) - 1 = k := by omega
      rwa [hk'] at hd
  obtain ⟨p, hp, hpM, hpk⟩ := key
  intro hg
  have hp1 : p ∣ 1 := hg ▸ Nat.dvd_gcd hpM hpk
  exact hp.one_lt.ne' (Nat.dvd_one.mp hp1)

/-- Every residue class modulo `M > 0` has a representative offset: `∃ t < M, M ∣ c + t`. -/
theorem exists_offset_dvd {M : ℕ} (hM : 0 < M) (c : ℕ) : ∃ t < M, M ∣ c + t := by
  have hdiv := Nat.mod_add_div c M
  have hlt := Nat.mod_lt c hM
  by_cases h0 : c % M = 0
  · exact ⟨0, hM, ⟨c / M, by omega⟩⟩
  · exact ⟨M - c % M, by omega, ⟨c / M + 1, by rw [Nat.mul_add_one]; omega⟩⟩

/-! ## Main theorems -/

/-- **Lower bound `g(a,b) ≥ 2r · ab` (first `r + 1` primes).**  If `a, b` are coprime and
both at least `primeProd r = p₁ ⋯ p_{r+1}`, there is an integer `n ≥ 2r · ab` that is not of
the form `a x + b y` with `x, y ≥ 0`, `gcd(x, y) = 1`.  For `r ≥ 2` (so `min(a,b) ≥ 30`)
this implies `conj:frob` of arXiv:2610.17267 (Jaffe) in that range; not stated in the
paper. -/
theorem exists_not_coprimeRep_of_primeProd_le (r : ℕ) {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : primeProd r ≤ a) (hb : primeProd r ≤ b) :
    ∃ n : ℕ, 2 * r * (a * b) ≤ n ∧ ¬ CoprimeRep a b n := by
  set M := primeProd r with hMdef
  have hM0 : 0 < M := primeProd_pos r
  obtain ⟨lam, h2, hodd⟩ := exists_lambda r
  obtain ⟨t, htM, hdvd⟩ := exists_offset_dvd hM0 ((2 * r + lam) * a)
  set y0 := 2 * r * a + t with hy0
  have hMy : M ∣ y0 + lam * a := by
    have heq : y0 + lam * a = (2 * r + lam) * a + t := by
      rw [hy0]
      ring
    rw [heq]
    exact hdvd
  have hx0 : lam * b % M < b := lt_of_lt_of_le (Nat.mod_lt _ hM0) hb
  have hcov : ∀ k : ℕ, a * k ≤ y0 → Nat.gcd M (lam + k) ≠ 1 := by
    intro k hk
    have hlt : a * k < a * (2 * r + 1) := by
      have hexp : a * (2 * r + 1) = 2 * r * a + a := by ring
      omega
    exact gcd_primeProd_ne_one h2 hodd (Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_left hlt))
  refine ⟨a * (lam * b % M) + b * y0, ?_, not_coprimeRep_of_modular hab hx0 hMy hcov⟩
  calc 2 * r * (a * b) = b * (2 * r * a) := by ring
    _ ≤ b * y0 := Nat.mul_le_mul_left b (Nat.le_add_right _ _)
    _ ≤ a * (lam * b % M) + b * y0 := Nat.le_add_left _ _

/-- **The claim in the paper's indexing.**  For `r ≥ 1`, if coprime `a, b` are both at least
`p₁ p₂ ⋯ p_r` (the product of the first `r` primes) then some `n ≥ (2r - 2) · ab` has no
representation `a x + b y` with `x, y ≥ 0`, `gcd(x, y) = 1`; i.e. `g(a,b) ≥ (2r-2)ab`. -/
theorem exists_not_coprimeRep_of_prod_first_primes_le {r : ℕ} (hr : 1 ≤ r) {a b : ℕ}
    (hab : Nat.Coprime a b) (ha : ∏ i ∈ range r, Nat.nth Nat.Prime i ≤ a)
    (hb : ∏ i ∈ range r, Nat.nth Nat.Prime i ≤ b) :
    ∃ n : ℕ, (2 * r - 2) * (a * b) ≤ n ∧ ¬ CoprimeRep a b n := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hcoef : 2 * (s + 1) - 2 = 2 * s := by omega
  rw [hcoef]
  exact exists_not_coprimeRep_of_primeProd_le s hab ha hb

/-- **Primorial form.**  If coprime `a, b` are both at least `primorial (p_{r+1})` (Mathlib's
product of all primes `≤ p_{r+1}`), then some `n ≥ 2r · ab` has no coprime representation. -/
theorem exists_not_coprimeRep_of_primorial_le (r : ℕ) {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : primorial (Nat.nth Nat.Prime r) ≤ a) (hb : primorial (Nat.nth Nat.Prime r) ≤ b) :
    ∃ n : ℕ, 2 * r * (a * b) ≤ n ∧ ¬ CoprimeRep a b n := by
  have hle : primeProd r ≤ primorial (Nat.nth Nat.Prime r) :=
    Nat.le_of_dvd (primorial_pos _) (primeProd_dvd_primorial r)
  exact exists_not_coprimeRep_of_primeProd_le r hab (hle.trans ha) (hle.trans hb)

/-- **`g(a,b)/(ab)` is unbounded.**  For every `C` there is a threshold `N` such that all
coprime `a, b ≥ N` admit an integer `n ≥ C · ab` with no coprime representation. -/
theorem coprimeRep_ratio_unbounded (C : ℕ) :
    ∃ N : ℕ, ∀ a b : ℕ, N ≤ a → N ≤ b → Nat.Coprime a b →
      ∃ n : ℕ, C * (a * b) ≤ n ∧ ¬ CoprimeRep a b n := by
  refine ⟨primeProd C, fun a b ha hb hab => ?_⟩
  obtain ⟨n, hn, hrep⟩ := exists_not_coprimeRep_of_primeProd_le C hab ha hb
  refine ⟨n, le_trans ?_ hn, hrep⟩
  exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left C (by norm_num))

/-- **Supremum form.**  When the non-representable set is bounded above (the paper's
existence theorem, not reproved here), `coprimeFrobenius a b ≥ 2r · ab` for coprime
`a, b ≥ primeProd r`. -/
theorem le_coprimeFrobenius_of_primeProd_le (r : ℕ) {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : primeProd r ≤ a) (hb : primeProd r ≤ b)
    (hbdd : BddAbove {n : ℕ | ¬ CoprimeRep a b n}) :
    2 * r * (a * b) ≤ coprimeFrobenius a b := by
  obtain ⟨n, hn, hrep⟩ := exists_not_coprimeRep_of_primeProd_le r hab ha hb
  exact hn.trans (le_csSup hbdd hrep)

/-- Non-vacuity: the hypotheses of the main theorem hold jointly at `r = 2`, `a = 30`,
`b = 31`, giving a non-representable `n ≥ 4 · 930`. -/
example : ∃ n : ℕ, 2 * 2 * (30 * 31) ≤ n ∧ ¬ CoprimeRep 30 31 n :=
  exists_not_coprimeRep_of_primeProd_le 2 (by norm_num) (by rw [primeProd_two])
    (by rw [primeProd_two]; norm_num)

end Candidates.FrobeniusCoprimeUnbounded
