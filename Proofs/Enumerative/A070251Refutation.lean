/-
Powerful terms of OEIS A070251 (Michael De Vlieger, Jan 15 2025).

The unrelated-factorial product uses 0<k<n, gcd(k,n)>1 and k∤n.
The claim that a(6)=4 is its only powerful value exceeding 1 is refuted by
 a(35)=18522000000=2^7*3^3*5^6*7^3.
More generally, a(pq) is powerful and exceeds 1 for consecutive primes 5≤p<q,
yielding an unbounded family of indices.
The source's squarefree-value, A055932, n=2p and n∣a(n) sub-conjectures
are not addressed.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A070251Refutation

/-! ## Definitions -/

/-- The numbers unrelated to `n`: those `k` with `0 < k < n` that share a
common divisor `> 1` with `n` but do not divide `n`.  The lower bound `0 < k`
is key: `k = 0` satisfies `1 < gcd 0 n` and `¬ 0 ∣ n` for `n ≥ 2`,
and would make every product `0`. -/
def unrelSet (n : ℕ) : Finset ℕ :=
  (Finset.Ioo 0 n).filter (fun k => 1 < Nat.gcd k n ∧ ¬ k ∣ n)

/-- OEIS A070251: `a(n)` is the product of the numbers unrelated to `n`
(empty product `1`). -/
def unrelProd (n : ℕ) : ℕ := ∏ k ∈ unrelSet n, k

/-- A natural number `m` is powerful (OEIS A001694) if every prime dividing it
divides it at least squared.  With this convention `1` is powerful and so is
`0`; the conjecture concerns terms `> 1`, so `0` never enters. -/
def IsPowerful (m : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m

/-! ## Examples -/

-- The definition reproduces all 33 listed terms a(1), ..., a(33).
example : (List.range 33).map (fun i => unrelProd (i + 1)) =
    [1, 1, 1, 1, 1, 4, 1, 6, 6, 192, 1, 720, 1, 23040, 6480, 10080, 1,
      12902400, 1, 34836480, 2449440, 1857945600, 1, 50295168000, 3000,
      980995276800, 9797760, 9564703948800, 1, 1518492398911488000, 1,
      41845579776000, 1571364748800] := by
  decide

-- The unrelated set of `10` is `{4, 6, 8}`, whose product is `a(10) = 192`.
example : unrelSet 10 = {4, 6, 8} := by decide

-- `IsPowerful` examples: `4 = a(6)` is powerful, `6 = a(8)` is not.
example : IsPowerful 4 := by
  intro p hp hdvd
  have hp2 : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using hdvd))
  subst hp2
  norm_num

example : ¬ IsPowerful 6 := by
  intro h
  have h4 : 2 ^ 2 ∣ 6 := h 2 Nat.prime_two (by norm_num)
  norm_num at h4

/-! ## The counterexample `n = 35` -/

/-- `a(35) = 18522000000`, checked by kernel evaluation. -/
theorem unrelProd_35 : unrelProd 35 = 18522000000 := by decide

/-- The factorization `18522000000 = 2^7 * 3^3 * 5^6 * 7^3`. -/
theorem factorization_18522000000 : (18522000000 : ℕ) = 2 ^ 7 * 3 ^ 3 * 5 ^ 6 * 7 ^ 3 := by
  norm_num

/-- `a(35) = 2^7 * 3^3 * 5^6 * 7^3` is powerful: its only prime divisors are
`2, 3, 5, 7`, each occurring at least squared. -/
theorem isPowerful_unrelProd_35 : IsPowerful (unrelProd 35) := by
  intro p hp hdvd
  rw [unrelProd_35, factorization_18522000000] at hdvd ⊢
  have hcases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h7
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h5
      · rcases (Nat.Prime.dvd_mul hp).1 h with h2 | h3
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
            (hp.dvd_of_dvd_pow h2))
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
            (hp.dvd_of_dvd_pow h3)))
      · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1
          (hp.dvd_of_dvd_pow h5))))
    · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1
        (hp.dvd_of_dvd_pow h7))))
  rcases hcases with rfl | rfl | rfl | rfl <;> norm_num

/-- De Vlieger's unique-index reading is false: `n=35`, not `6`, gives
a powerful term exceeding `1`. -/
theorem a070251_powerful_conjecture_false :
    ¬ ∀ n : ℕ, 1 < unrelProd n → IsPowerful (unrelProd n) → n = 6 := by
  intro h
  have h35 : (35 : ℕ) = 6 := h 35 (by rw [unrelProd_35]; norm_num) isPowerful_unrelProd_35
  omega

/-- The value form of the refutation: the term `a(35) > 1` is powerful and
differs from `4`, so `4` is not the only powerful value exceeding `1`. -/
theorem a070251_powerful_value_conjecture_false :
    ¬ ∀ n : ℕ, 1 < unrelProd n → IsPowerful (unrelProd n) → unrelProd n = 4 := by
  intro h
  have h35 := h 35 (by rw [unrelProd_35]; norm_num) isPowerful_unrelProd_35
  rw [unrelProd_35] at h35
  norm_num at h35

/-! ## The infinite family `n = p q`, `p < q` consecutive primes, `p ≥ 5` -/

/-- Membership in the unrelated set, unfolded. -/
theorem mem_unrelSet {n k : ℕ} :
    k ∈ unrelSet n ↔ 0 < k ∧ k < n ∧ 1 < Nat.gcd k n ∧ ¬ k ∣ n := by
  simp [unrelSet, and_assoc]

/-- If two distinct members of a finite set of naturals are both divisible by
`r`, then `r ^ 2` divides the product of the set. -/
theorem sq_dvd_prod_of_two_mem {s : Finset ℕ} {r a b : ℕ} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) (hra : r ∣ a) (hrb : r ∣ b) : r ^ 2 ∣ ∏ k ∈ s, k := by
  have hsub : ({a, b} : Finset ℕ) ⊆ s := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact ha
    · rw [Finset.mem_singleton.1 hx]
      exact hb
  have hpair : a * b ∣ ∏ k ∈ s, k := by
    have hab' : ∏ k ∈ ({a, b} : Finset ℕ), k = a * b := Finset.prod_pair hab
    rw [← hab']
    exact Finset.prod_dvd_prod_of_subset _ _ _ hsub
  exact (pow_two r ▸ mul_dvd_mul hra hrb).trans hpair

/-- For a prime `b`, `1 < a` and `2 ≤ m < b`, the multiple `m * a` is unrelated
to `a * b`. -/
theorem mul_mem_unrelSet {a b m : ℕ} (ha : 1 < a) (hb : b.Prime) (hm2 : 2 ≤ m)
    (hmb : m < b) : m * a ∈ unrelSet (a * b) := by
  rw [mem_unrelSet]
  have ha0 : 0 < a := by omega
  refine ⟨Nat.mul_pos (by omega) ha0, ?_, ?_, ?_⟩
  · rw [mul_comm a b]
    exact Nat.mul_lt_mul_of_pos_right hmb ha0
  · have hdvd : a ∣ Nat.gcd (m * a) (a * b) :=
      Nat.dvd_gcd (dvd_mul_left a m) (dvd_mul_right a b)
    have hpos : 0 < Nat.gcd (m * a) (a * b) :=
      Nat.gcd_pos_of_pos_left _ (Nat.mul_pos (by omega) ha0)
    have hle : a ≤ Nat.gcd (m * a) (a * b) := Nat.le_of_dvd hpos hdvd
    omega
  · intro hdvd
    rw [mul_comm a b] at hdvd
    have hmdvd : m ∣ b := Nat.dvd_of_mul_dvd_mul_right ha0 hdvd
    rcases (Nat.dvd_prime hb).1 hmdvd with h | h <;> omega

/-- Every member of `unrelSet (p * q)`, for primes `p, q`, is a multiple of `p`
or of `q`. -/
theorem dvd_or_dvd_of_mem_unrelSet {p q k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hk : k ∈ unrelSet (p * q)) : p ∣ k ∨ q ∣ k := by
  obtain ⟨_, _, hgcd, _⟩ := mem_unrelSet.1 hk
  obtain ⟨s, hs, hsg⟩ := Nat.exists_prime_and_dvd (show Nat.gcd k (p * q) ≠ 1 by omega)
  have hsk : s ∣ k := hsg.trans (Nat.gcd_dvd_left k (p * q))
  have hspq : s ∣ p * q := hsg.trans (Nat.gcd_dvd_right k (p * q))
  rcases (Nat.Prime.dvd_mul hs).1 hspq with h | h
  · rw [(Nat.prime_dvd_prime_iff_eq hs hp).1 h] at hsk
    exact Or.inl hsk
  · rw [(Nat.prime_dvd_prime_iff_eq hs hq).1 h] at hsk
    exact Or.inr hsk

/-- A prime `r ∉ {p, q}` dividing a member of `unrelSet (p * q)` satisfies
`r < p`, when `p < q` are consecutive primes. -/
theorem lt_of_prime_dvd_mem_unrelSet {p q r k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hcons : ∀ r : ℕ, r.Prime → p < r → q ≤ r) (hr : r.Prime)
    (hrp : r ≠ p) (hrq : r ≠ q) (hk : k ∈ unrelSet (p * q)) (hrk : r ∣ k) : r < p := by
  obtain ⟨hk0, hkn, _, _⟩ := mem_unrelSet.1 hk
  -- `r` divides a cofactor `j` with `j < q` (resp. `j < p`).
  have hrq' : r < q := by
    rcases dvd_or_dvd_of_mem_unrelSet hp hq hk with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · have hjq : j < q := Nat.lt_of_mul_lt_mul_left hkn
      have hrj : r ∣ j := by
        rcases (Nat.Prime.dvd_mul hr).1 hrk with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hr hp).1 h) hrp
        · exact h
      have hj0 : 0 < j := Nat.pos_of_mul_pos_left hk0
      exact lt_of_le_of_lt (Nat.le_of_dvd hj0 hrj) hjq
    · have hjp : j < p := by
        rw [mul_comm p q] at hkn
        exact Nat.lt_of_mul_lt_mul_left hkn
      have hrj : r ∣ j := by
        rcases (Nat.Prime.dvd_mul hr).1 hrk with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hr hq).1 h) hrq
        · exact h
      have hj0 : 0 < j := Nat.pos_of_mul_pos_left hk0
      exact lt_of_le_of_lt (Nat.le_of_dvd hj0 hrj) (hjp.trans hpq)
  rcases lt_trichotomy r p with h | h | h
  · exact h
  · exact absurd h hrp
  · exact absurd (hcons r hr h) (by omega)

/-- **The infinite family of counterexamples.**  For consecutive primes
`5 ≤ p < q` (no prime strictly between them), `a(p q)` exceeds `1` and is
powerful.  `(p, q) = (5, 7)` gives `n = 35`; the next cases are
`77, 143, 221, 323, 437`.

Proof: every prime `r ∣ a(p q)` divides two distinct members of the unrelated
set: `2p, 3p` if `r = p`; `2q, 3q` if `r = q`; and `r p, r q` otherwise, since
then `r < p` (`r` divides a cofactor `< q`, and no prime lies in `(p, q)`). -/
theorem one_lt_unrelProd_mul_and_isPowerful (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (h5 : 5 ≤ p) (hpq : p < q) (hcons : ∀ r : ℕ, r.Prime → p < r → q ≤ r) :
    1 < unrelProd (p * q) ∧ IsPowerful (unrelProd (p * q)) := by
  have hp1 : 1 < p := hp.one_lt
  have hq1 : 1 < q := hq.one_lt
  -- The members `m * p` (`2 ≤ m < q`) and `m * q` (`2 ≤ m < p`)
  have hmemp : ∀ m, 2 ≤ m → m < q → m * p ∈ unrelSet (p * q) :=
    fun m hm2 hmq => mul_mem_unrelSet hp1 hq hm2 hmq
  have hmemq : ∀ m, 2 ≤ m → m < p → m * q ∈ unrelSet (p * q) := by
    intro m hm2 hmp
    rw [mul_comm p q]
    exact mul_mem_unrelSet hq1 hp hm2 hmp
  constructor
  · have hpos : 0 < unrelProd (p * q) :=
      Finset.prod_pos (fun k hk => (mem_unrelSet.1 hk).1)
    have hdvd : 2 * p ∣ unrelProd (p * q) :=
      Finset.dvd_prod_of_mem _ (hmemp 2 le_rfl (by omega))
    have hle : 2 * p ≤ unrelProd (p * q) := Nat.le_of_dvd hpos hdvd
    omega
  · intro r hr hdvd
    obtain ⟨k, hk, hrk⟩ := (Prime.dvd_finsetProd_iff hr.prime _).1 hdvd
    by_cases hrp : r = p
    · subst hrp
      exact sq_dvd_prod_of_two_mem (hmemp 2 le_rfl (by omega)) (hmemp 3 (by omega) (by omega))
        (by omega) (dvd_mul_left r 2) (dvd_mul_left r 3)
    by_cases hrq : r = q
    · subst hrq
      exact sq_dvd_prod_of_two_mem (hmemq 2 le_rfl (by omega)) (hmemq 3 (by omega) (by omega))
        (by omega) (dvd_mul_left r 2) (dvd_mul_left r 3)
    have hrlt : r < p := lt_of_prime_dvd_mem_unrelSet hp hq hpq hcons hr hrp hrq hk hrk
    have hr2 : 2 ≤ r := hr.two_le
    have hne : r * p ≠ r * q := fun h =>
      absurd (Nat.eq_of_mul_eq_mul_left (by omega) h) (by omega)
    exact sq_dvd_prod_of_two_mem (hmemp r hr2 (by omega)) (hmemq r hr2 hrlt) hne
      (dvd_mul_right r p) (dvd_mul_right r q)

-- Satisfiability of the family hypotheses at `(p, q) = (5, 7)`, recovering `n = 35`.
example : 1 < unrelProd 35 ∧ IsPowerful (unrelProd 35) := by
  have hcons : ∀ r : ℕ, r.Prime → 5 < r → 7 ≤ r := by
    intro r hr h5
    by_contra h7
    have hr6 : r = 6 := by omega
    subst hr6
    norm_num at hr
  exact one_lt_unrelProd_mul_and_isPowerful 5 7 Nat.prime_five (by norm_num) le_rfl
    (by norm_num) hcons

/-- **Infinitely many counterexamples.**  For every `N` there is an index
`n > N` with `a(n) > 1` powerful: take a prime `p ≥ N + 5` and the next prime
`q` after it, and apply `one_lt_unrelProd_mul_and_isPowerful` to `n = p q`. -/
theorem exists_lt_one_lt_unrelProd_isPowerful (N : ℕ) :
    ∃ n : ℕ, N < n ∧ 1 < unrelProd n ∧ IsPowerful (unrelProd n) := by
  obtain ⟨p, hNp, hp⟩ := Nat.exists_infinite_primes (N + 5)
  have hex : ∃ r : ℕ, r.Prime ∧ p < r := by
    obtain ⟨r, hpr, hr⟩ := Nat.exists_infinite_primes (p + 1)
    exact ⟨r, hr, by omega⟩
  classical
  let q := Nat.find hex
  have hq : q.Prime ∧ p < q := Nat.find_spec hex
  have hcons : ∀ r : ℕ, r.Prime → p < r → q ≤ r := fun r hr hpr =>
    Nat.find_min' hex ⟨hr, hpr⟩
  obtain ⟨h1, hpow⟩ :=
    one_lt_unrelProd_mul_and_isPowerful p q hp hq.1 (by omega) hq.2 hcons
  have hq1 : 1 ≤ q := hq.1.one_lt.le
  have hpq : p ≤ p * q := Nat.le_mul_of_pos_right p hq1
  exact ⟨p * q, by omega, h1, hpow⟩

end Candidates.A070251Refutation
