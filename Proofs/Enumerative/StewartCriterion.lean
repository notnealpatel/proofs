import Enumerative.Practical

/-!
# Stewart's structure theorem for practical numbers

Stewart (1954) and Sierpiński (1955) completed Srinivasan's partial classification of
the practical numbers (OEIS A005153) into a criterion readable off the prime
factorisation.  In the phrasing of the A005153 comment of Franklin T. Adams-Watters
(Nov 09 2006, pulled live 2026-07-30):

> An integer `m ≥ 2` with factorization `∏_{i=1..k} p_i^e_i` with the `p_i` in
> ascending order is practical if and only if `p_1 = 2` and, for `1 < i ≤ k`,
> `p_i ≤ σ(∏_{j < i} p_j^e_j) + 1`.

This file formalises that criterion as a full `↔`, in the *index-free* shape

`n.Practical ↔ ∀ p ∈ n.primeFactors, p ≤ 1 + σ(stewartPrefix n p)`

where `Nat.stewartPrefix n p = ∏ q ∈ n.primeFactors with q < p, q ^ n.factorization q` is
the part of `n` supported on the primes *below* `p` — exactly `∏_{j < i} p_j^{e_j}`
when `p = p_i`, since `n.primeFactors` carries no order data of its own and "the
primes below `p_i`" is precisely "`p_1, …, p_{i-1}`" for an ascending enumeration.

Merging Stewart's two clauses into one quantifier is not a re-statement: it is the
A005153 comment of Hal M. Switkay (Dec 22 2022, pulled live 2026-07-30),

> the first condition in Stewart's characterization (`p_1 = 2`) is equivalent to the
> second condition with index `i = 1`, given that an empty product is equal to 1.

Indeed at the least prime factor `p_1` the prefix is the empty product `1`, and
`p_1 ≤ 1 + σ(1) = 2` forces `p_1 = 2`.  The two-clause form is recovered verbatim as
`Nat.practical_iff_two_dvd_and_stewart`.

## Main results

* `Nat.stewartPrefix` — the prefix product, with `Nat.factorization_stewartPrefix`
  identifying its factorisation as `n.factorization.filter (· < p)`;
* `Nat.Practical.le_one_add_sum_divisors_stewartPrefix` — **necessity**: every prime
  factor obeys the bound.  Divisors of `n` below `p` all divide the prefix, so
  `Nat.Practical.divisor_le_one_add_sum` at `p` caps `p` by `1 + σ(prefix)`;
* `Nat.practical_of_forall_le_one_add_sum_divisors_stewartPrefix` — **sufficiency**,
  by strong induction: peel the largest prime factor `p` as `n = m * p ^ k`, the
  remainder `m` is the prefix at `p`, and `Nat.Practical.mul_prime_pow` re-attaches
  `p ^ k`;
* `Nat.practical_iff_stewart` — the two directions combined;
* `Nat.practical_iff_two_dvd_and_stewart` — Stewart's own two-clause phrasing;
* `Nat.Practical.minFac_eq_two` — Stewart's clause `p_1 = 2` in `Nat.minFac` form;
* `Nat.practical_mul_prime_pow_iff` — the criterion in recursive form: for `p` prime
  exceeding every prime factor of `m`, `m * p ^ k` is practical iff `m` is practical
  and `p ≤ 1 + σ(m)`.  This is the *ordered* Stewart step promoted to an `↔`; the
  unordered sufficiency step `Nat.Practical.mul_prime_pow` has no converse, witnessed
  at the end of this file by `3 * 2² = 12` (practical, with `3` not practical).

## Guards

The `↔` needs `0 < n`: `Nat.primeFactors 0 = ∅` makes the right-hand side vacuously
true while `0` is not practical.  At `n = 1` both sides hold — `1` is practical and
has no prime factors — so the criterion covers the whole of A005153, not just `n ≥ 2`.

## Axiom audit

Every declaration in this file reports a subset of
`{propext, Classical.choice, Quot.sound}`; the `#print axioms` sweep is at the end.
There is no `native_decide` and no `sorry`.
-/

set_option autoImplicit false

namespace Nat

/-! ## The prefix product -/

/-- `Nat.stewartPrefix n p` is the product `∏ q ^ (n.factorization q)` over the prime
factors `q < p` of `n` — the `p`-smooth part of `n`.  For `p = p_i` the `i`-th smallest
prime factor of `n`, this is Stewart's prefix `p_1^{e_1} ⋯ p_{i-1}^{e_{i-1}}`; at the
least prime factor it is the empty product `1`.

For `n ≠ 0` it is the largest divisor of `n` all of whose prime factors lie below `p`
(`Nat.stewartPrefix_dvd` and `Nat.dvd_stewartPrefix`, both of which carry that guard).
The `n ≠ 0` scope is needed for *that* description only: `stewartPrefix 0 p = 1`, while
`0 ∣ 0` and `Nat.primeFactors 0 = ∅` make `0` itself the largest such divisor of `0`.
The product above is unconditional, and `Nat.stewartPrefix_pos` holds for every `n`. -/
def stewartPrefix (n p : ℕ) : ℕ :=
  ∏ q ∈ n.primeFactors.filter (fun q => q < p), q ^ n.factorization q

/-- The prefix product is positive: every factor `q ^ e` has prime base. -/
theorem stewartPrefix_pos (n p : ℕ) : 0 < stewartPrefix n p :=
  Finset.prod_pos fun _q hq =>
    pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).pos _

/-- The prefix product is nonzero. -/
theorem stewartPrefix_ne_zero (n p : ℕ) : stewartPrefix n p ≠ 0 :=
  (stewartPrefix_pos n p).ne'

/-- **Factorisation of the prefix**: `stewartPrefix n p` is the number whose
factorisation is `n`'s restricted to the primes below `p`.  No positivity guard is
needed: at `n = 0` both sides are the zero finitely-supported function. -/
theorem factorization_stewartPrefix (n p : ℕ) :
    (stewartPrefix n p).factorization = n.factorization.filter (fun q => q < p) := by
  have hsupp : (n.factorization.filter (fun q => q < p)).support
      = n.primeFactors.filter (fun q => q < p) := by
    rw [Finsupp.support_filter, Nat.support_factorization]
  have hprod : stewartPrefix n p
      = (n.factorization.filter (fun q => q < p)).prod (· ^ ·) := by
    rw [Finsupp.prod, hsupp, stewartPrefix]
    exact Finset.prod_congr rfl fun q hq => by
      rw [Finsupp.filter_apply_pos (fun q => q < p) _ (Finset.mem_filter.mp hq).2]
  rw [hprod]
  refine Nat.prod_pow_factorization_eq_self fun q hq => ?_
  rw [hsupp] at hq
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1

/-- The prime factors of the prefix are exactly the prime factors of `n` below `p`. -/
theorem primeFactors_stewartPrefix (n p : ℕ) :
    (stewartPrefix n p).primeFactors = n.primeFactors.filter (fun q => q < p) := by
  rw [← Nat.support_factorization, factorization_stewartPrefix, Finsupp.support_filter,
    Nat.support_factorization]

/-- Every prime factor of the prefix lies below `p`. -/
theorem lt_of_mem_primeFactors_stewartPrefix {n p q : ℕ}
    (hq : q ∈ (stewartPrefix n p).primeFactors) : q < p := by
  rw [primeFactors_stewartPrefix] at hq
  exact (Finset.mem_filter.mp hq).2

/-- The prefix divides `n`. -/
theorem stewartPrefix_dvd {n : ℕ} (hn : n ≠ 0) (p : ℕ) : stewartPrefix n p ∣ n := by
  refine (Nat.factorization_le_iff_dvd (stewartPrefix_ne_zero n p) hn).mp ?_
  rw [factorization_stewartPrefix, Finsupp.le_def]
  intro q
  by_cases hq : q < p
  · rw [Finsupp.filter_apply_pos (fun q => q < p) _ hq]
  · rw [Finsupp.filter_apply_neg (fun q => q < p) _ hq]
    exact Nat.zero_le _

/-- **Maximality of the prefix**: any divisor of `n` whose prime factors all lie below
`p` divides `stewartPrefix n p`. -/
theorem dvd_stewartPrefix {n p d : ℕ} (hn : n ≠ 0) (hd : d ≠ 0) (hdvd : d ∣ n)
    (hlt : ∀ q ∈ d.primeFactors, q < p) : d ∣ stewartPrefix n p := by
  refine (Nat.factorization_le_iff_dvd hd (stewartPrefix_ne_zero n p)).mp ?_
  rw [factorization_stewartPrefix, Finsupp.le_def]
  intro q
  by_cases hq : q < p
  · rw [Finsupp.filter_apply_pos (fun q => q < p) _ hq]
    exact Finsupp.le_def.mp ((Nat.factorization_le_iff_dvd hd hn).mpr hdvd) q
  · rw [Finsupp.filter_apply_neg (fun q => q < p) _ hq]
    by_contra hc
    exact hq (hlt q (Nat.support_factorization d ▸ Finsupp.mem_support_iff.mpr
      (Nat.pos_of_ne_zero (by omega)).ne'))

/-- **The prefix sees only the factorisation below `p`**: two numbers whose
factorisations agree below `p` have the same prefix at `p`. -/
theorem stewartPrefix_congr {m n p : ℕ}
    (h : ∀ r, r < p → m.factorization r = n.factorization r) :
    stewartPrefix m p = stewartPrefix n p := by
  refine Nat.factorization_inj (stewartPrefix_ne_zero m p) (stewartPrefix_ne_zero n p) ?_
  rw [factorization_stewartPrefix, factorization_stewartPrefix]
  ext r
  by_cases hr : r < p
  · rw [Finsupp.filter_apply_pos (fun q => q < p) _ hr,
      Finsupp.filter_apply_pos (fun q => q < p) _ hr]
    exact h r hr
  · rw [Finsupp.filter_apply_neg (fun q => q < p) _ hr,
      Finsupp.filter_apply_neg (fun q => q < p) _ hr]

/-- If every prime factor of `n` is below `p`, the prefix is all of `n`. -/
theorem stewartPrefix_eq_self {n p : ℕ} (hn : n ≠ 0)
    (hlt : ∀ q ∈ n.primeFactors, q < p) : stewartPrefix n p = n :=
  Nat.dvd_antisymm (stewartPrefix_dvd hn p) (dvd_stewartPrefix hn hn dvd_rfl hlt)

/-- **Empty prefix**: if no prime factor of `n` lies below `p`, the prefix is the empty
product `1`.  At the least prime factor `p_1` of `n` this gives `stewartPrefix n p_1 = 1`,
so Stewart's condition there reads `p_1 ≤ 1 + σ(1) = 2`. -/
theorem stewartPrefix_eq_one_of_forall_le {n p : ℕ}
    (hle : ∀ q ∈ n.primeFactors, p ≤ q) : stewartPrefix n p = 1 := by
  refine Finset.prod_eq_one fun q hq => ?_
  obtain ⟨hq_mem, hq_lt⟩ := Finset.mem_filter.mp hq
  have hpq : p ≤ q := hle q hq_mem
  exact absurd hq_lt (by omega)

/-- **Adjoining a top prime power leaves low prefixes alone**: for `p` prime and
`q ≤ p`, the prefix of `m * p ^ k` at `q` equals the prefix of `m` at `q`.  Multiplying
by `p ^ k` changes the factorisation only at `p`, and the prefix at `q ≤ p` reads only
the exponents strictly below `q ≤ p`. -/
theorem stewartPrefix_mul_prime_pow_of_le {m p q : ℕ} (hp : p.Prime) (hm : m ≠ 0)
    (hq : q ≤ p) (k : ℕ) : stewartPrefix (m * p ^ k) q = stewartPrefix m q := by
  refine stewartPrefix_congr fun r hr => ?_
  rw [Nat.factorization_mul hm (pow_ne_zero k hp.ne_zero), hp.factorization_pow,
    Finsupp.add_apply, Finsupp.single_apply, if_neg (by omega), Nat.add_zero]

/-- **Peeling identity**: if `p` is prime and exceeds every prime factor of `m`, then
the prefix of `m * p ^ k` at `p` is `m` — the whole of `m` survives, and `p ^ k` is
discarded. -/
theorem stewartPrefix_mul_prime_pow {m p : ℕ} (hp : p.Prime) (hm : m ≠ 0)
    (hlt : ∀ q ∈ m.primeFactors, q < p) (k : ℕ) :
    stewartPrefix (m * p ^ k) p = m := by
  rw [stewartPrefix_mul_prime_pow_of_le hp hm (le_refl p) k]
  exact stewartPrefix_eq_self hm hlt

/-! ## Necessity -/

/-- **Necessity in Stewart's criterion**: in a practical `n`, every prime factor `p`
satisfies `p ≤ 1 + σ(stewartPrefix n p)`.  Every divisor of `n` smaller than `p` has
all its prime factors below `p`, hence divides the prefix; so the divisor-gap bound
`Nat.Practical.divisor_le_one_add_sum` at `d = p` is capped by `1 + σ(prefix)`. -/
theorem Practical.le_one_add_sum_divisors_stewartPrefix {n p : ℕ} (h : n.Practical)
    (hp : p ∈ n.primeFactors) :
    p ≤ 1 + ∑ d ∈ (stewartPrefix n p).divisors, d := by
  have hn : n ≠ 0 := h.pos.ne'
  have hpmem : p ∈ n.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.dvd_of_mem_primeFactors hp, hn⟩
  -- the divisor-gap bound at `d = p`
  have hgap : p ≤ 1 + ∑ x ∈ n.divisors.filter (fun x => x < p), x :=
    h.divisor_le_one_add_sum hpmem
  -- every divisor of `n` below `p` has all its prime factors below `p`, hence divides
  -- the prefix
  have hsub : n.divisors.filter (fun x => x < p) ⊆ (stewartPrefix n p).divisors := by
    intro d hd
    obtain ⟨hd_mem, hd_lt⟩ := Finset.mem_filter.mp hd
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd_mem).ne'
    refine Nat.mem_divisors.mpr
      ⟨dvd_stewartPrefix hn hd0 (Nat.dvd_of_mem_divisors hd_mem) ?_, stewartPrefix_ne_zero n p⟩
    intro q hq
    exact lt_of_le_of_lt
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) (Nat.dvd_of_mem_primeFactors hq)) hd_lt
  have hsum : ∑ x ∈ n.divisors.filter (fun x => x < p), x
      ≤ ∑ d ∈ (stewartPrefix n p).divisors, d := Finset.sum_le_sum_of_subset hsub
  omega

/-! ## Sufficiency -/

/-- **Sufficiency in Stewart's criterion**: if every prime factor `p` of `n > 0`
satisfies `p ≤ 1 + σ(stewartPrefix n p)`, then `n` is practical.  Strong induction:
peel the largest prime factor `p`, writing `n = m * p ^ k` with `p ∤ m`.  Since `p` is
the largest prime factor, `m` is exactly `stewartPrefix n p`, and `m` inherits the
criterion because prefixes below `p` are unchanged by the peeling; the induction
hypothesis makes `m` practical and `Nat.Practical.mul_prime_pow` re-attaches `p ^ k`,
using `p ≤ 1 + σ(m)` — which is the criterion at `p`. -/
theorem practical_of_forall_le_one_add_sum_divisors_stewartPrefix :
    ∀ n : ℕ, 0 < n →
      (∀ p ∈ n.primeFactors, p ≤ 1 + ∑ d ∈ (stewartPrefix n p).divisors, d) →
      n.Practical := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hcrit
    rcases Nat.lt_or_ge n 2 with hn1 | hn1
    · -- `n = 1`: the empty factorisation, practical with no conditions to check
      have hn_one : n = 1 := by omega
      subst hn_one
      exact practical_one
    have hn0 : n ≠ 0 := hn.ne'
    -- peel the largest prime factor `p`
    have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn1
    obtain ⟨p, hpmem, hpmax⟩ := n.primeFactors.exists_max_image id hne
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    obtain ⟨k, m, hpm, hmul⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.ne_one
    have hm0 : m ≠ 0 := by rintro rfl; exact hn0 (by simpa using hmul)
    have hmul' : n = m * p ^ k := by rw [hmul, Nat.mul_comm]
    have hk0 : k ≠ 0 := by
      rintro rfl
      have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hpmem
      rw [hmul, pow_zero, Nat.one_mul] at hpn
      exact hpm hpn
    -- checkpoint: every prime factor of `m` is strictly below the peeled `p`
    have hmdvd : m ∣ n := ⟨p ^ k, by rw [hmul', Nat.mul_comm]⟩
    have hlt : ∀ q ∈ m.primeFactors, q < p := by
      intro q hq
      have hqn : q ∈ n.primeFactors := Nat.primeFactors_mono hmdvd hn0 hq
      have hqne : q ≠ p := by
        rintro rfl
        exact hpm (Nat.dvd_of_mem_primeFactors hq)
      exact lt_of_le_of_ne (hpmax q hqn) hqne
    -- checkpoint: the prefix of `n` at `p` is exactly `m`
    have hprefix : stewartPrefix n p = m := by
      rw [hmul']
      exact stewartPrefix_mul_prime_pow hp hm0 hlt k
    -- checkpoint: `m` inherits the criterion, and is smaller than `n`
    have hmcrit : ∀ q ∈ m.primeFactors, q ≤ 1 + ∑ d ∈ (stewartPrefix m q).divisors, d := by
      intro q hq
      have hqn : q ∈ n.primeFactors := Nat.primeFactors_mono hmdvd hn0 hq
      have hcongr : stewartPrefix n q = stewartPrefix m q := by
        rw [hmul']
        exact stewartPrefix_mul_prime_pow_of_le hp hm0 (hlt q hq).le k
      rw [← hcongr]
      exact hcrit q hqn
    have hmlt : m < n := by
      have h1 : 1 < p ^ k := Nat.one_lt_pow hk0 hp.one_lt
      calc m = 1 * m := (Nat.one_mul m).symm
        _ < p ^ k * m := by
            exact Nat.mul_lt_mul_of_lt_of_le h1 (le_refl m) (Nat.pos_of_ne_zero hm0)
        _ = n := hmul.symm
    have hmprac : m.Practical := ih m hmlt (Nat.pos_of_ne_zero hm0) hmcrit
    -- re-attach the peeled prime power via the unordered Stewart step
    have hple : p ≤ 1 + ∑ d ∈ m.divisors, d := hprefix ▸ hcrit p hpmem
    have hres : (m * p ^ k).Practical := hmprac.mul_prime_pow hp hpm hple k
    rw [hmul']
    exact hres

/-! ## Stewart's structure theorem -/

/-- **Stewart's structure theorem** (Stewart 1954, *Sums of distinct divisors*, Amer.
J. Math. 76, 779–785; Sierpiński 1955, Ann. Mat. Pura Appl. 39, 69–74), index-free
form: a positive `n` is practical iff every prime factor `p` of `n` is at most
`1 + σ` of the part of `n` supported on the primes below `p`.

Writing `n = p_1^{e_1} ⋯ p_k^{e_k}` with `p_1 < ⋯ < p_k`, the condition at `p = p_i`
reads `p_i ≤ 1 + σ(p_1^{e_1} ⋯ p_{i-1}^{e_{i-1}})`, and at `i = 1` the empty prefix
gives `p_1 ≤ 1 + σ(1) = 2`, i.e. `p_1 = 2` (OEIS A005153, comment of Hal M. Switkay,
Dec 22 2022).  The guard `0 < n` is required: at `n = 0` the right-hand side is
vacuously true and `0` is not practical. -/
theorem practical_iff_stewart {n : ℕ} (hn : 0 < n) :
    n.Practical ↔
      ∀ p ∈ n.primeFactors, p ≤ 1 + ∑ d ∈ (stewartPrefix n p).divisors, d :=
  ⟨fun h _ hp => h.le_one_add_sum_divisors_stewartPrefix hp,
   practical_of_forall_le_one_add_sum_divisors_stewartPrefix n hn⟩

/-- **Stewart's own two-clause phrasing** for `n ≥ 2` (OEIS A005153, comment of
Franklin T. Adams-Watters, Nov 09 2006): `n` is practical iff `p_1 = 2` — stated as
`2 ∣ n`, equivalent for `n ≥ 2` to the least prime factor being `2` — and every
*larger* prime factor obeys the prefix bound.

Stewart's first clause is logically redundant, exactly as Switkay observes: the proof
of `←` never uses `2 ∣ n`, because the second clause applied at the least prime factor
already forces it (an odd `n > 1` has least prime factor `p_1 > 2` facing the empty
prefix, so `p_1 ≤ 1 + σ(1) = 2` fails).  It is kept here because it is how Stewart,
Sierpiński and the A005153 comment state the criterion. -/
theorem practical_iff_two_dvd_and_stewart {n : ℕ} (hn : 1 < n) :
    n.Practical ↔
      2 ∣ n ∧ ∀ p ∈ n.primeFactors, 2 < p →
        p ≤ 1 + ∑ d ∈ (stewartPrefix n p).divisors, d := by
  rw [practical_iff_stewart (by omega : 0 < n)]
  constructor
  · intro h
    refine ⟨?_, fun p hp _ => h p hp⟩
    -- `p_1 = 2` is the criterion at the least prime factor, whose prefix is empty
    obtain ⟨p, hpmem, hpmin⟩ :=
      n.primeFactors.exists_min_image id (Nat.nonempty_primeFactors.mpr hn)
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hempty : stewartPrefix n p = 1 := stewartPrefix_eq_one_of_forall_le hpmin
    have hple : p ≤ 2 := by
      have hbound := h p hpmem
      rw [hempty] at hbound
      simpa using hbound
    have hp2 : p = 2 := le_antisymm hple hp.two_le
    exact hp2 ▸ Nat.dvd_of_mem_primeFactors hpmem
  · rintro ⟨-, h⟩ p hp
    rcases lt_or_ge 2 p with hp2 | hp2
    · exact h p hp hp2
    -- at `p = 2` the bound is free: `1` is always a divisor of the prefix
    have hp_eq : p = 2 := le_antisymm hp2 (Nat.prime_of_mem_primeFactors hp).two_le
    have hone : (1 : ℕ) ≤ ∑ d ∈ (stewartPrefix n p).divisors, d :=
      Finset.single_le_sum (f := fun x : ℕ => x) (fun i _ => Nat.zero_le i)
        (Nat.one_mem_divisors.mpr (stewartPrefix_ne_zero n p))
    omega

/-- The least prime factor of a practical `n > 1` is `2` — Stewart's clause `p_1 = 2`
in `Nat.minFac` form. -/
theorem Practical.minFac_eq_two {n : ℕ} (h : n.Practical) (hn : 1 < n) :
    n.minFac = 2 :=
  (Nat.minFac_eq_two_iff n).mpr (h.two_dvd hn)

/-- **Recursive form of the criterion**: for `p` prime exceeding every prime factor of
`m > 0`, the number `m * p ^ k` is practical iff `m` is practical and
`p ≤ 1 + σ(m)`.  The `←` direction is `Nat.Practical.mul_prime_pow`; the `→`
direction is the ordered necessity, which the unordered step does not provide.

The `0 < m` guard is not needed for truth — at `m = 0` both sides are `False` — but it
is kept so that every model satisfying the hypotheses is nondegenerate: at `m = 0` the
ordering hypothesis is vacuous (`Nat.primeFactors 0 = ∅`) and the `↔` is `False ↔
False`.  All four hypotheses are load-bearing or nondegenerating; `hlt` and `hk` are
witnessed sharp at the end of this file. -/
theorem practical_mul_prime_pow_iff {m p k : ℕ} (hp : p.Prime) (hm : 0 < m)
    (hlt : ∀ q ∈ m.primeFactors, q < p) (hk : k ≠ 0) :
    (m * p ^ k).Practical ↔ m.Practical ∧ p ≤ 1 + ∑ d ∈ m.divisors, d := by
  have hm0 : m ≠ 0 := hm.ne'
  have hpm : ¬ p ∣ m := fun hc =>
    absurd (hlt p (Nat.mem_primeFactors.mpr ⟨hp, hc, hm0⟩)) (lt_irrefl p)
  have hN0 : m * p ^ k ≠ 0 := Nat.mul_ne_zero hm0 (pow_ne_zero k hp.ne_zero)
  have hprefix : stewartPrefix (m * p ^ k) p = m := stewartPrefix_mul_prime_pow hp hm0 hlt k
  constructor
  · intro h
    -- `p` is a prime factor of `m * p ^ k`, and its prefix there is `m`
    have hpmem : p ∈ (m * p ^ k).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, Dvd.dvd.mul_left (dvd_pow_self p hk) m, hN0⟩
    refine ⟨practical_of_forall_le_one_add_sum_divisors_stewartPrefix m hm fun q hq => ?_,
      hprefix ▸ h.le_one_add_sum_divisors_stewartPrefix hpmem⟩
    -- every prime factor `q` of `m` is a prime factor of `m * p ^ k` with the same prefix
    have hqmem : q ∈ (m * p ^ k).primeFactors :=
      Nat.primeFactors_mono (Dvd.intro _ rfl) hN0 hq
    have hcongr : stewartPrefix (m * p ^ k) q = stewartPrefix m q :=
      stewartPrefix_mul_prime_pow_of_le hp hm0 (hlt q hq).le k
    exact hcongr ▸ h.le_one_add_sum_divisors_stewartPrefix hqmem
  · rintro ⟨hmp, hple⟩
    exact hmp.mul_prime_pow hp hpm hple k

/-- Every prime factor of `m > 0` is at most `m`, so `m < p` already forces all prime
factors of `m` below `p`.  This discharges the ordering hypothesis of
`Nat.practical_mul_prime_pow_iff` at concrete numbers without factorising `m`. -/
theorem forall_mem_primeFactors_lt_of_lt {m p : ℕ} (hm : m ≠ 0) (hmp : m < p) :
    ∀ q ∈ m.primeFactors, q < p := fun _q hq =>
  lt_of_le_of_lt
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.dvd_of_mem_primeFactors hq)) hmp

end Nat

/-!
## Ground-truth checks for `Nat.stewartPrefix`

The prefix at `p` strips exactly the primes `≥ p`.  `Nat.factorization` does not reduce
in the kernel, so these go through the peeling identity rather than `decide`; the
values are cross-checked against `#eval` and against SageMath's `prod([q^v for q,v in
factor(n) if q < p])`.
-/

-- `20 = 2² · 5`: the prefix below `5` is `2² = 4`.
example : Nat.stewartPrefix 20 5 = 4 := by
  rw [show (20 : ℕ) = 4 * 5 ^ 1 by norm_num,
    Nat.stewartPrefix_mul_prime_pow Nat.prime_five (by norm_num)
      (Nat.forall_mem_primeFactors_lt_of_lt (by norm_num) (by norm_num)) 1]

-- `10 = 2 · 5`: the prefix below `5` is only `2`.
example : Nat.stewartPrefix 10 5 = 2 := by
  rw [show (10 : ℕ) = 2 * 5 ^ 1 by norm_num,
    Nat.stewartPrefix_mul_prime_pow Nat.prime_five (by norm_num)
      (Nat.forall_mem_primeFactors_lt_of_lt (by norm_num) (by norm_num)) 1]

-- At the least prime factor the prefix is the empty product.
example : Nat.stewartPrefix 20 2 = 1 :=
  Nat.stewartPrefix_eq_one_of_forall_le fun _q hq =>
    (Nat.prime_of_mem_primeFactors hq).two_le

-- Wikipedia's worked example: `429606 = 2 · 3² · 29 · 823`, prefix below `823` is
-- `2 · 3² · 29 = 522`, and indeed `823 ≤ 1 + σ(522) = 1171`.
example : Nat.stewartPrefix 429606 823 = 522 := by
  rw [show (429606 : ℕ) = 522 * 823 ^ 1 by norm_num,
    Nat.stewartPrefix_mul_prime_pow (by norm_num) (by norm_num)
      (Nat.forall_mem_primeFactors_lt_of_lt (by norm_num) (by norm_num)) 1]

-- `Nat.stewartPrefix` is compiler-evaluable even though it is not kernel-reducible;
-- the proved values above can be read off directly.  Cross-checked via `#eval` in
-- Scratch (no active `#eval` in committed files, per house practice):
--   Nat.stewartPrefix 20 5  = 4
--   Nat.stewartPrefix 10 5  = 2
--   Nat.stewartPrefix 20 2  = 1
--   ((429606 : ℕ).primeFactors.sort (· ≤ ·)).map
--     (fun p => (p, Nat.stewartPrefix 429606 p))
--   = [(2, 1), (3, 2), (29, 18), (823, 522)]
-- — the ascending prefix chain for Wikipedia's example, `∏_{j < i} p_j^{e_j}`
-- against the primes `[2, 3, 29, 823]`.

/-!
## Satisfiability of the hypothesis-bearing statements

Every theorem above with hypotheses is instantiated jointly at a concrete model, so
that no statement is discharged by contradictory assumptions.  The recurring model is
`n = 20 = 2² · 5` with `p = 5` and prefix `4`.
-/

-- `Nat.stewartPrefix_dvd`, `Nat.dvd_stewartPrefix`: `4 ∣ stewartPrefix 20 5 ∣ 20`.
example : Nat.stewartPrefix 20 5 ∣ 20 := Nat.stewartPrefix_dvd (by norm_num) 5

example : (4 : ℕ) ∣ Nat.stewartPrefix 20 5 :=
  Nat.dvd_stewartPrefix (by norm_num) (by norm_num) (by norm_num)
    (Nat.forall_mem_primeFactors_lt_of_lt (by norm_num) (by norm_num))

-- `Nat.stewartPrefix_congr` at a nondegenerate model: `4` and `20` have the same
-- factorisation below `5`, hence the same prefix there.
example : Nat.stewartPrefix 4 5 = Nat.stewartPrefix 20 5 := by
  refine Nat.stewartPrefix_congr fun r hr => ?_
  rw [show (20 : ℕ) = 4 * 5 ^ 1 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Nat.prime_five.factorization_pow,
    Finsupp.add_apply, Finsupp.single_apply, if_neg (by omega), Nat.add_zero]

-- `Nat.stewartPrefix_eq_self`: all prime factors of `4` are below `5`.
example : Nat.stewartPrefix 4 5 = 4 :=
  Nat.stewartPrefix_eq_self (by norm_num)
    (Nat.forall_mem_primeFactors_lt_of_lt (by norm_num) (by norm_num))

-- `Nat.stewartPrefix_mul_prime_pow_of_le` below the peeled prime: `q = 3 ≤ 5 = p`.
example : Nat.stewartPrefix (4 * 5 ^ 1) 3 = Nat.stewartPrefix 4 3 :=
  Nat.stewartPrefix_mul_prime_pow_of_le Nat.prime_five (by norm_num) (by norm_num) 1

-- `Nat.lt_of_mem_primeFactors_stewartPrefix`: `2` is a prime factor of the prefix `4`.
example : (2 : ℕ) < 5 :=
  Nat.lt_of_mem_primeFactors_stewartPrefix (n := 20) (p := 5)
    (by
      rw [Nat.primeFactors_stewartPrefix, Finset.mem_filter]
      exact ⟨Nat.mem_primeFactors.mpr ⟨Nat.prime_two, by norm_num, by norm_num⟩, by norm_num⟩)

-- `Nat.Practical.le_one_add_sum_divisors_stewartPrefix`: `20` is practical and `5` is
-- one of its prime factors, giving `5 ≤ 1 + σ(4) = 8`.
example : (5 : ℕ) ≤ 1 + ∑ d ∈ (Nat.stewartPrefix 20 5).divisors, d :=
  (by decide : Nat.Practical 20).le_one_add_sum_divisors_stewartPrefix
    (Nat.mem_primeFactors.mpr ⟨Nat.prime_five, by norm_num, by norm_num⟩)

-- `Nat.practical_of_forall_le_one_add_sum_divisors_stewartPrefix` at `n = 4`: the sole
-- prime factor is `2`, whose prefix is empty.
example : Nat.Practical 4 := by
  refine Nat.practical_of_forall_le_one_add_sum_divisors_stewartPrefix 4 (by norm_num)
    fun p hp => ?_
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num,
    Nat.primeFactors_prime_pow two_ne_zero Nat.prime_two, Finset.mem_singleton] at hp
  subst hp
  rw [Nat.stewartPrefix_eq_one_of_forall_le
    (fun _q hq => (Nat.prime_of_mem_primeFactors hq).two_le)]
  decide

-- `Nat.Practical.minFac_eq_two`: `20` is practical and `1 < 20`.
example : (20 : ℕ).minFac = 2 := (by decide : Nat.Practical 20).minFac_eq_two (by norm_num)

/-!
## Discriminating checks

`20 = 2² · 5` and `10 = 2 · 5` have the same prime support and differ only in the
prefix available to `5`; the criterion separates them.

The decision procedure on `Nat.Practical` is asymmetric: refutations are cheap, since
`∀ m ≤ n, …` aborts at the first unrepresentable `m` (kernel `decide` closes
`¬ Nat.Practical 4036` in about 7 s at `maxRecDepth 100000`), while confirmations must
certify a subset of the divisors for every one of the `n + 1` values.  Stewart's
criterion replaces that search with `r` inequalities.  The confirmation at
`1372 = 2² · 7³` below is the example of record: kernel `decide` does not close it —
at default options it exhausts the `200000`-heartbeat budget after about `34` s, and at
`maxHeartbeats 2000000` with `maxRecDepth 400000` it had still not finished after
`280` s of wall clock.  The criterion closes it from `σ(4) = 7`.
-/

-- `20` is practical: `4` is practical and `5 ≤ 1 + σ(4) = 8`.
example : Nat.Practical 20 := by
  rw [show (20 : ℕ) = 4 * 5 ^ 1 by norm_num,
    Nat.practical_mul_prime_pow_iff Nat.prime_five (by norm_num)
      (Nat.forall_mem_primeFactors_lt_of_lt (by norm_num) (by norm_num)) one_ne_zero]
  exact ⟨by decide, by decide⟩

-- `10` is not: `5 > 1 + σ(2) = 4`.  Same primes, different order structure.
example : ¬ Nat.Practical 10 := by
  rw [show (10 : ℕ) = 2 * 5 ^ 1 by norm_num,
    Nat.practical_mul_prime_pow_iff Nat.prime_five (by norm_num)
      (Nat.forall_mem_primeFactors_lt_of_lt (by norm_num) (by norm_num)) one_ne_zero]
  rintro ⟨-, hbound⟩
  exact absurd hbound (by decide)

-- Cross-checks against the decision procedure of `Enumerative.Practical`.
example : Nat.Practical 20 := by decide
example : ¬ Nat.Practical 10 := by decide
example : Nat.Practical 28 := by decide

-- `28 = 2² · 7` is practical (`7 ≤ 1 + σ(4) = 8`), from the criterion this time.
example : Nat.Practical 28 := by
  rw [show (28 : ℕ) = 4 * 7 ^ 1 by norm_num,
    Nat.practical_mul_prime_pow_iff Nat.prime_seven (by norm_num)
      (Nat.forall_mem_primeFactors_lt_of_lt (by norm_num) (by norm_num)) one_ne_zero]
  exact ⟨by decide, by decide⟩

-- `15 = 3 · 5` is odd, so its least prime factor `3` faces an empty prefix and the
-- criterion fails at `3 ≤ 1 + σ(1) = 2`.
example : ¬ Nat.Practical 15 := by
  intro h
  have hmem : (3 : ℕ) ∈ (15 : ℕ).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_three, by norm_num, by norm_num⟩
  have hbound := h.le_one_add_sum_divisors_stewartPrefix hmem
  rw [Nat.stewartPrefix_eq_one_of_forall_le (n := 15) (p := 3) (fun q hq => ?_)] at hbound
  · exact absurd hbound (by decide)
  · have hq2 : 2 ≤ q := (Nat.prime_of_mem_primeFactors hq).two_le
    have hqd : q ∣ 15 := Nat.dvd_of_mem_primeFactors hq
    rcases Nat.eq_or_lt_of_le hq2 with hq_eq | hq_lt
    · exact absurd (hq_eq ▸ hqd) (by norm_num)
    · omega

-- `1372 = 2² · 7³` is practical: `7 ≤ 1 + σ(4) = 8` and `4` is practical.  Kernel
-- `decide` does not close this goal (heartbeat-exhausted at default options in ~34 s;
-- unfinished after 280 s at `maxHeartbeats 2000000`); the criterion needs one
-- inequality.
example : Nat.Practical 1372 := by
  rw [show (1372 : ℕ) = 4 * 7 ^ 3 by norm_num,
    Nat.practical_mul_prime_pow_iff Nat.prime_seven (by norm_num)
      (Nat.forall_mem_primeFactors_lt_of_lt (by norm_num) (by norm_num)) (by norm_num)]
  exact ⟨by decide, by decide⟩

-- `4036 = 2² · 1009` is not practical: `1009 > 1 + σ(4) = 8`.  Cross-checked below
-- against kernel `decide`, which refutes cheaply.
example : ¬ Nat.Practical 4036 := by
  rw [show (4036 : ℕ) = 4 * 1009 ^ 1 by norm_num,
    Nat.practical_mul_prime_pow_iff (by norm_num) (by norm_num)
      (Nat.forall_mem_primeFactors_lt_of_lt (by norm_num) (by norm_num)) one_ne_zero]
  rintro ⟨-, hbound⟩
  exact absurd hbound (by decide)

set_option maxRecDepth 100000 in
example : ¬ Nat.Practical 4036 := by decide

/-!
## Sharpness of the guards

The `0 < n` guard on `Nat.practical_iff_stewart` and the ordering hypothesis of
`Nat.practical_mul_prime_pow_iff` are both load-bearing, witnessed here.
-/

-- Without `0 < n` the criterion is vacuously satisfied at `n = 0`, which is not
-- practical: `Nat.primeFactors 0 = ∅`.
example : (∀ p ∈ (0 : ℕ).primeFactors, p ≤ 1 + ∑ d ∈ (Nat.stewartPrefix 0 p).divisors, d)
    ∧ ¬ Nat.Practical 0 :=
  ⟨fun _p hp => absurd hp (by simp), Nat.not_practical_zero⟩

-- At `n = 1` both sides hold, so the criterion covers the first term of A005153.
example : Nat.Practical 1 ∧
    ∀ p ∈ (1 : ℕ).primeFactors, p ≤ 1 + ∑ d ∈ (Nat.stewartPrefix 1 p).divisors, d :=
  ⟨Nat.practical_one, fun _p hp => absurd hp (by simp)⟩

-- Sharpness of the ordering hypothesis `∀ q ∈ m.primeFactors, q < p` in
-- `Nat.practical_mul_prime_pow_iff`: dropping it makes `→` false.  At `m = 3`, `p = 2`,
-- `k = 2` the product `3 * 2² = 12` is practical while `3` is not — which is also why
-- the unordered step `Nat.Practical.mul_prime_pow` admits no converse.  The witness
-- certifies that `hp`, `hm`, `hk` all hold and that it is exactly `hlt` that fails.
example : Nat.Prime 2 ∧ 0 < (3 : ℕ) ∧ (2 : ℕ) ≠ 0 ∧
    ¬ (∀ q ∈ (3 : ℕ).primeFactors, q < 2) ∧
    ¬ ((3 * 2 ^ 2 : ℕ).Practical ↔
        (3 : ℕ).Practical ∧ 2 ≤ 1 + ∑ d ∈ (3 : ℕ).divisors, d) := by
  refine ⟨Nat.prime_two, by norm_num, by norm_num, ?_, by decide⟩
  intro hc
  exact absurd
    (hc 3 (Nat.mem_primeFactors.mpr ⟨Nat.prime_three, by norm_num, by norm_num⟩))
    (by norm_num)

-- Sharpness of `hk : k ≠ 0` in `Nat.practical_mul_prime_pow_iff`: at `k = 0` the
-- product is just `m`, and `p` need not obey any bound.  `4 * 11⁰ = 4` is practical
-- while `11 > 1 + σ(4) = 8`.
example : Nat.Prime 11 ∧ 0 < (4 : ℕ) ∧ (∀ q ∈ (4 : ℕ).primeFactors, q < 11) ∧
    ¬ ((4 * 11 ^ 0 : ℕ).Practical ↔
        (4 : ℕ).Practical ∧ 11 ≤ 1 + ∑ d ∈ (4 : ℕ).divisors, d) :=
  ⟨by norm_num, by norm_num,
   Nat.forall_mem_primeFactors_lt_of_lt (by norm_num) (by norm_num), by decide⟩

-- Sharpness of `1 < n` in `Nat.practical_iff_two_dvd_and_stewart`: at `n = 1` the
-- practical number `1` fails the `2 ∣ n` clause, and at `n = 0` the right-hand side
-- holds while `0` is not practical.
example : ¬ ((1 : ℕ).Practical ↔ 2 ∣ (1 : ℕ) ∧
    ∀ p ∈ (1 : ℕ).primeFactors, 2 < p →
      p ≤ 1 + ∑ d ∈ (Nat.stewartPrefix 1 p).divisors, d) := fun h =>
  absurd (h.mp Nat.practical_one).1 (by norm_num)

example : ¬ ((0 : ℕ).Practical ↔ 2 ∣ (0 : ℕ) ∧
    ∀ p ∈ (0 : ℕ).primeFactors, 2 < p →
      p ≤ 1 + ∑ d ∈ (Nat.stewartPrefix 0 p).divisors, d) := fun h =>
  Nat.not_practical_zero (h.mpr ⟨dvd_zero 2, fun _p hp => absurd hp (by simp)⟩)

-- Sharpness of `1 < n` in `Nat.Practical.minFac_eq_two`: `1` is practical and odd, and
-- `Nat.minFac 1 = 1`.  (`Nat.minFac` is well-founded, so this needs `Nat.minFac_one`
-- rather than `decide`.)
example : (1 : ℕ).Practical ∧ (1 : ℕ).minFac ≠ 2 :=
  ⟨Nat.practical_one, by rw [Nat.minFac_one]; norm_num⟩

-- Exactness of the `1 +`: `78 = 2 · 3 · 13` attains equality `13 = 1 + σ(6)` and is
-- practical, so the criterion with `p ≤ σ(prefix)` would misclassify it; `102 = 2 · 3 ·
-- 17` fails the true bound at `17 > 13` and is not practical.
example : (13 : ℕ) = 1 + ∑ d ∈ (6 : ℕ).divisors, d ∧
    ¬ ((13 : ℕ) ≤ ∑ d ∈ (6 : ℕ).divisors, d) := by decide

set_option maxRecDepth 100000 in
example : (78 : ℕ).Practical ∧ ¬ (102 : ℕ).Practical := by decide

-- The quantifier really must range over `n.primeFactors` and not over all primes:
-- `4` is practical, yet the bound fails at the non-factor prime `11`.
example : (4 : ℕ).Practical ∧ Nat.Prime 11 ∧
    ¬ ((11 : ℕ) ≤ 1 + ∑ d ∈ (Nat.stewartPrefix 4 11).divisors, d) := by
  refine ⟨by decide, by norm_num, ?_⟩
  rw [Nat.stewartPrefix_eq_self (n := 4) (p := 11) (by norm_num)
    (Nat.forall_mem_primeFactors_lt_of_lt (by norm_num) (by norm_num))]
  decide

/-! ## Axiom audit

Every declaration rests on a subset of `{propext, Classical.choice, Quot.sound}`.  The
subset check is the sound `native_decide` detector on this toolchain: a use would
surface as a per-declaration `*._native.native_decide.ax_*` axiom.  There is no
`native_decide` in this file. -/

#print axioms Nat.stewartPrefix
#print axioms Nat.stewartPrefix_pos
#print axioms Nat.stewartPrefix_ne_zero
#print axioms Nat.factorization_stewartPrefix
#print axioms Nat.primeFactors_stewartPrefix
#print axioms Nat.lt_of_mem_primeFactors_stewartPrefix
#print axioms Nat.stewartPrefix_dvd
#print axioms Nat.dvd_stewartPrefix
#print axioms Nat.stewartPrefix_congr
#print axioms Nat.stewartPrefix_eq_self
#print axioms Nat.stewartPrefix_eq_one_of_forall_le
#print axioms Nat.stewartPrefix_mul_prime_pow_of_le
#print axioms Nat.stewartPrefix_mul_prime_pow
#print axioms Nat.Practical.le_one_add_sum_divisors_stewartPrefix
#print axioms Nat.practical_of_forall_le_one_add_sum_divisors_stewartPrefix
#print axioms Nat.practical_iff_stewart
#print axioms Nat.practical_iff_two_dvd_and_stewart
#print axioms Nat.Practical.minFac_eq_two
#print axioms Nat.practical_mul_prime_pow_iff
#print axioms Nat.forall_mem_primeFactors_lt_of_lt
