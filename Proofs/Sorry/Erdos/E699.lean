/-
  Erdős Problem #699 — a common prime factor of two binomial
  coefficients in the same row.
  Status: falsifiable (open).  Tier UA attack target.

  Verbatim statement (`goof erdos fetch 699`, pulled 2026-08-05):

    "Is it true that for every $1\leq i<j\leq n/2$ there exists some
    prime $p\geq i$ such that
    \[p\mid \textrm{gcd}\left(\binom{n}{i}, \binom{n}{j}\right)?\]"

  DB remarks (Erdős–Szekeres): Sylvester–Schur gives a prime > i
  dividing C(n,i) alone.  GPT 5.6/Price proved the claim for j ≤ (3/2)i
  and for n = 2j.  For fixed i < j only finitely many n can fail (easy;
  Bloom's argument via the identity
  C(n,i)·C(n−i,j−i) = C(n,j)·C(j,i): if V_i(n) — the part of C(n,i)
  supported on primes ≥ i — is coprime to C(n,j) then V_i(n) ∣ C(j,i),
  bounding n).  The strict variant (p > i) fails at explicit exceptional
  pairs; the only known exception with i ≥ 4 is
  gcd(C(28,5), C(28,14)) = 2³·3³·5.  Verified up to n = 10⁷ (Cong,
  Jan 2026, comment-sourced).

  Mathlib inventory (leandoc 2026-08-05): `Nat.choose`, `Nat.gcd`,
  `Nat.primeFactors`, `Nat.Prime.dvd_choose`, `Nat.choose_mul_choose_le`?
  — the key identity C(n,i)·C(n−i,j−i) = C(n,j)·C(j,i) is
  `Nat.choose_mul_choose_eq`-shaped; `Nat.succ_mul_choose_eq` family in
  Data/Nat/Choose.  Kummer machinery adjacent to
  `Proofs/Erdos/Erdos175/NotSquarefree.lean`.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E699

/-- `SharedLargePrime n i j`: some prime `p ≥ i` divides both `C(n,i)`
    and `C(n,j)`. -/
def SharedLargePrime (n i j : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.gcd (n.choose i) (n.choose j)

/-- Satisfiability at a small model: `n = 10, i = 2, j = 5`:
    `C(10,2) = 45`, `C(10,5) = 252`, `gcd = 9`, and `p = 3 ≥ 2` works.
    -- PROVABLE (decide). -/
example : SharedLargePrime 10 2 5 := by
  refine ⟨3, by norm_num, by norm_num, ?_⟩
  rw [Nat.choose_eq_descFactorial_div_factorial, Nat.choose_eq_descFactorial_div_factorial]
  norm_num [Nat.descFactorial, Nat.factorial, Nat.gcd]

/-- **Erdős #699, headline (OPEN)**: for all `1 ≤ i < j` with `2j ≤ n`,
    some prime `p ≥ i` divides `gcd(C(n,i), C(n,j))`.

    Source text: "Is it true that for every $1\leq i<j\leq n/2$ there
    exists some prime $p\geq i$ such that
    $p \mid \gcd(\binom{n}{i},\binom{n}{j})$?"

    `j ≤ n/2` is encoded multiplicatively as `2*j ≤ n` (STYLE.md: no
    ℕ-division in hypotheses).  Status: open/falsifiable; verified to
    n = 10⁷.  Archived; the provable slices are below. -/
theorem erdos_699 (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : 2 * j ≤ n) :
    SharedLargePrime n i j := by
  sorry

/-- **Proved slice 1 — the balanced case** `n = 2j` (GPT 5.6/Price via
    Bloom's identity; comment-sourced 2026, re-derive before trusting).
    Attack: from C(2j,i)·C(2j−i,j−i) = C(2j,j)·C(j,i), the part of
    C(2j,i) supported on primes ≥ i cannot be coprime to C(2j,j) unless
    it divides C(j,i); but the EEES 1978 bound V_i(n)² > C(n,i) (12
    exceptions) gives V_i(2j) > C(j,i).  Lemma chain: (a) the identity
    (`Nat.choose_mul_choose_eq`-family or direct factorial proof);
    (b) the smooth/rough split of C(n,i) (shared def with #684/#1093);
    (c) EEES lower bound — the deep input, sorry-able separately. -/
theorem erdos_699_balanced (j i : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    SharedLargePrime (2 * j) i j := by
  sorry

open Finset in
/-- If no prime `p ≥ i` divides both `C(n,i)` and `C(n,j)` (with `i < j ≤ n`), then
    `C(n,i) ≤ n ^ (i - 1) * C(j,i)`. -/
private lemma choose_le_of_not_shared (n i j : ℕ) (hij : i < j) (hjn : j ≤ n)
    (hbad : ¬ SharedLargePrime n i j) :
    n.choose i ≤ n ^ (i - 1) * j.choose i := by
  set m := n.choose i with hm_def
  have hn : 0 < n := by omega
  have hm0 : m ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hji0 : 0 < j.choose i := Nat.choose_pos hij.le
  -- smooth/rough split of `m`
  have hsplit : (∏ p ∈ m.primeFactors with p < i, p ^ m.factorization p) *
      (∏ p ∈ m.primeFactors with ¬ p < i, p ^ m.factorization p) = m := by
    rw [prod_filter_mul_prod_filter_not]
    exact Nat.prod_factorization_pow_eq_self hm0
  set S := ∏ p ∈ m.primeFactors with p < i, p ^ m.factorization p with hS_def
  set R := ∏ p ∈ m.primeFactors with ¬ p < i, p ^ m.factorization p with hR_def
  -- the rough part is coprime to `C(n,j)`
  have hRcop : R.Coprime (n.choose j) := by
    refine Nat.Coprime.prod_left fun p hp => ?_
    rw [mem_filter] at hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp.1
    refine Nat.Coprime.pow_left _ ((hpp.coprime_iff_not_dvd).2 fun hdvd => hbad ?_)
    exact ⟨p, hpp, not_lt.1 hp.2, Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp.1) hdvd⟩
  -- Bloom's identity: `m ∣ C(n,j) * C(j,i)`
  have hmdvd : m ∣ n.choose j * j.choose i := by
    rw [Nat.choose_mul hij.le]
    exact Dvd.intro _ rfl
  have hRdvd : R ∣ j.choose i :=
    hRcop.dvd_of_dvd_mul_left ((Dvd.intro_left S hsplit).trans hmdvd)
  have hRle : R ≤ j.choose i := Nat.le_of_dvd hji0 hRdvd
  -- the smooth part is at most `n ^ (i - 1)`
  have hSle : S ≤ n ^ (i - 1) := by
    have hcard : (m.primeFactors.filter (· < i)).card ≤ i - 1 := by
      have hsub : m.primeFactors.filter (· < i) ⊆ Ico 1 i := by
        intro p hp
        rw [mem_filter] at hp
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp.1
        rw [mem_Ico]
        exact ⟨hpp.one_lt.le, hp.2⟩
      simpa using card_le_card hsub
    calc S ≤ n ^ (m.primeFactors.filter (· < i)).card :=
          prod_le_pow_card _ _ _ fun p _ => Nat.pow_factorization_choose_le hn
      _ ≤ n ^ (i - 1) := Nat.pow_le_pow_right hn hcard
  calc m = S * R := hsplit.symm
    _ ≤ n ^ (i - 1) * j.choose i := Nat.mul_le_mul hSle hRle

/-- **Proved slice 2 — finiteness of bad `n` for fixed `i < j`**
    (easy per DB; Bloom's argument).  For fixed `1 ≤ i < j` the set of
    `n ≥ 2j` violating the conclusion is finite: coprimality forces
    `V_i(n) ∣ C(j,i)` while `V_i(n) → ∞` with `n`.
    The natural first sorry-free target of this file. -/
theorem erdos_699_finitely_many_bad (i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    {n : ℕ | 2 * j ≤ n ∧ ¬ SharedLargePrime n i j}.Finite := by
  refine (Set.finite_Iic (2 ^ i * i.factorial * j.choose i)).subset ?_
  rintro n ⟨hjn, hbad⟩
  rw [Set.mem_Iic]
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hn : 0 < n := by omega
  have hup := choose_le_of_not_shared n (k + 1) j hij (by omega) hbad
  rw [Nat.add_sub_cancel] at hup
  -- lower bound: `n ^ (k+1) ≤ 2 ^ (k+1) * (k+1)! * C(n,k+1)`
  have hlow : n ^ (k + 1) ≤ 2 ^ (k + 1) * (k + 1).factorial * n.choose (k + 1) := by
    have h1 : n ≤ 2 * (n + 1 - (k + 1)) := by omega
    calc n ^ (k + 1) ≤ (2 * (n + 1 - (k + 1))) ^ (k + 1) := Nat.pow_le_pow_left h1 _
      _ = 2 ^ (k + 1) * (n + 1 - (k + 1)) ^ (k + 1) := by rw [mul_pow]
      _ ≤ 2 ^ (k + 1) * n.descFactorial (k + 1) :=
          Nat.mul_le_mul_left _ (Nat.pow_sub_le_descFactorial n (k + 1))
      _ = 2 ^ (k + 1) * (k + 1).factorial * n.choose (k + 1) := by
          rw [Nat.descFactorial_eq_factorial_mul_choose, mul_assoc]
  have hkey : n * n ^ k ≤ (2 ^ (k + 1) * (k + 1).factorial * j.choose (k + 1)) * n ^ k := by
    calc n * n ^ k = n ^ (k + 1) := by ring
      _ ≤ 2 ^ (k + 1) * (k + 1).factorial * n.choose (k + 1) := hlow
      _ ≤ 2 ^ (k + 1) * (k + 1).factorial * (n ^ k * j.choose (k + 1)) :=
          Nat.mul_le_mul_left _ hup
      _ = (2 ^ (k + 1) * (k + 1).factorial * j.choose (k + 1)) * n ^ k := by ring
  exact Nat.le_of_mul_le_mul_right hkey (pow_pos hn k)

/-- The Erdős–Szekeres *strict* variant `p > i` fails: at
    `(n, i, j) = (28, 5, 14)`, `gcd(C(28,5), C(28,14)) = 2³·3³·5 = 1080`
    and no prime `> 5` divides it (but `p = 5 ≥ 5` does — the weak form
    holds).  The only known exception with `i ≥ 4`.
    -- PROVABLE (decide; C(28,14) = 40116600). -/
theorem strict_variant_fails_28_5_14 :
    Nat.gcd (Nat.choose 28 5) (Nat.choose 28 14) = 1080 ∧
    (∀ p : ℕ, p.Prime → 5 < p → ¬ p ∣ 1080) ∧
    SharedLargePrime 28 5 14 := by
  have hgcd : Nat.gcd (Nat.choose 28 5) (Nat.choose 28 14) = 1080 := by
    rw [Nat.choose_eq_descFactorial_div_factorial, Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial, Nat.factorial, Nat.gcd]
  refine ⟨hgcd, ?_, ?_⟩
  · intro p hp hgt hdvd
    have hfactor : 1080 = 2 ^ 3 * 3 ^ 3 * 5 := by norm_num
    rw [hfactor] at hdvd
    rcases hp.dvd_mul.mp hdvd with h23 | h5
    · rcases hp.dvd_mul.mp h23 with h2 | h3
      · have heq : 2 = p := (Nat.prime_two.dvd_iff_eq hp.ne_one).mp
          (hp.dvd_of_dvd_pow h2)
        omega
      · have hprime3 : Nat.Prime 3 := by norm_num
        have heq : 3 = p := (hprime3.dvd_iff_eq hp.ne_one).mp
          (hp.dvd_of_dvd_pow h3)
        omega
    · have hprime5 : Nat.Prime 5 := by norm_num
      have heq : 5 = p := (hprime5.dvd_iff_eq hp.ne_one).mp h5
      omega
  · refine ⟨5, by norm_num, le_rfl, ?_⟩
    rw [hgcd]
    norm_num

/-- Bounded computational form of the window check. -/
private lemma window_60_compute :
    ∀ n ∈ List.range 61, ∀ i ∈ List.range 31, ∀ j ∈ List.range 31,
      1 ≤ i → i < j → 2 * j ≤ n →
      ∃ p ∈ [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59],
        i ≤ p ∧ n.descFactorial i / i.factorial % p = 0 ∧
          n.descFactorial j / j.factorial % p = 0 := by
  decide +kernel

/-- Sanity window: the headline verified for all `n ≤ 60` and all
    admissible `(i, j)`.  -- PROVABLE (decide; small search space). -/
theorem erdos_699_window_60 :
    ∀ n ∈ Finset.range 61, ∀ i ∈ Finset.range 31, ∀ j ∈ Finset.range 31,
      1 ≤ i → i < j → 2 * j ≤ n → SharedLargePrime n i j := by
  intro n hn i hi j hj h1 h2 h3
  obtain ⟨p, hp, hip, hpi, hpj⟩ := window_60_compute n (List.mem_range.2 (Finset.mem_range.1 hn))
    i (List.mem_range.2 (Finset.mem_range.1 hi)) j (List.mem_range.2 (Finset.mem_range.1 hj))
    h1 h2 h3
  have hprime : p.Prime := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> norm_num
  rw [← Nat.choose_eq_descFactorial_div_factorial] at hpi hpj
  exact ⟨p, hprime, hip, Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hpi) (Nat.dvd_of_mod_eq_zero hpj)⟩

/-- **Sylvester–Schur** (input lemma, also the prize of #683): for
    `1 ≤ k` and `2k ≤ n`, `C(n,k)` has a prime factor `> k`.  Not in
    Mathlib (leandoc miss "sylvester schur" re-verified 2026-08-05).
    Load-bearing for this problem, #683, #1094, #1095. -/
theorem sylvester_schur (n k : ℕ) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ n.choose k := by
  sorry

end ErdosCandidates.E699

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB pull exactly.
   - SharedLargePrime uses p >= i (not p > i), matching the weak form; strict variant
     correctly separated into strict_variant_fails_28_5_14.
   - gcd(C(28,5), C(28,14)) = 1080 = 2^3 * 3^3 * 5 verified by computation.
   - C(10,2) = 45, C(10,5) = 252, gcd = 9, prime 3 >= 2 verified.
   - C(28,14) = 40116600 verified.
   - j <= n/2 encoded as 2*j <= n: correct ℕ-division avoidance per STYLE.md.
   - Attribution: DB says "GPT 5.6 (prompted by Price)" for balanced/3-2 cases; file
     says "GPT 5.6/Price" — faithful. Bloom's finiteness argument from comments
     correctly attributed. Cong verification to 10^7 correctly flagged comment-sourced.
   - Sylvester-Schur correctly noted as not in Mathlib.
   - Types: all ℕ, no ℤ/ℝ issues. No ℕ-subtraction or ℕ-division in hypotheses.
-/
