/-
  Erdős Problem #1063 × #175 crossover — defect-one rigidity and the
  carry-counting lower bound for `n_k`.

  ══════════════════════════════════════════════════════════════════════
  SOURCE PINS (all fetched 2026-08-05)
  ══════════════════════════════════════════════════════════════════════

  Erdős Problem #1063 (`goof erdos fetch 1063`), `statement` field, verbatim:

      Let $k\geq 2$ and define $n_k\geq 2k$ to be the least value of $n$ such
      that $n-i$ divides $\binom{n}{k}$ for all but one $0\leq i<k$.
      Estimate $n_k$.

  OEIS A389360 (`goof oeis show A389360`), `name` field, verbatim:

      Smallest m >= 2*n such that binomial(m,n) is a multiple of m-i for all
      0<=i<n, but one.

  and its `terms` field (offset 2, so the list starts at a(2) = n₂), verbatim:

      4,6,9,12,75,30,70,56,2403,280,3465,210,793,4732,3213,1456,31110,612,
      67203,145540,464646,2640,476938,21000,86550,234026,1053702,34776,
      37584001,8100,2301456,77780756,61924632,26515138,105846930,665280,
      622999377,233999782,510752034,1154440

  erdosproblems.com #1063 comment thread (same fetch).  Comment `post-7233`
  (author `rickyc`, 23:38 on 26 Jun 2026) claims, verbatim from the body
  HTML (`<br/>` tags are the source's own line breaks, kept as-is):

      We prove the following lower bound:\[<br/>n_k\ge <br/>\max\left(2k,\
      \prod_{p^a\parallel k}p^{a+\lfloor\log_p(k/2)\rfloor}\right).<br/>\]

  and ends "(Note: This was AI assisted by GPT-5.5 Thinking)".  Comment
  `post-7439` (author `rickyc`, 23:31 on 10 Jul 2026) claims, verbatim:

      The same argument gives the stronger lower bound\[<br/>n_k\ge<br/>
      \max\left(2k,\ \prod_{p^a\parallel k}p^{a+\lfloor\log_p(k-1)\rfloor}
      \right).<br/>\]

  and ends "(Note: This comment was written by GPT-5.6 Sol)".

  Both comments are explicitly AI-assisted and unrefereed, so NOTHING below
  is cited from them: this file re-derives the post-7439 bound from scratch
  and machine-checks it.  The comments are pinned only to attribute the
  statement being verified.

  ══════════════════════════════════════════════════════════════════════
  WHAT THIS FILE PROVES (sorry-free; see `#print axioms` at the end)
  ══════════════════════════════════════════════════════════════════════

  Throughout, `badSet n k` is the set of `i < k` with `(n-i) ∤ C(n,k)`, so
  `divisorDefect n k = 1` (the defining property of `n_k`) says exactly
  `badSet n k = {e}` for a unique bad index `e`.

  * `factorization_choose_add_le_of_max` — the strengthened core valuation
    inequality: if `e < k ≤ n` maximizes `v_p(n-i)` over `i < k`, then
    `v_p(C(n,k)) + v_p(k) + v_p(C(k-1,e)) ≤ v_p(n-e)`.  This sharpens
    `exists_factorization_choose_lt` (SelfridgeDefect.lean), which discarded
    both the `v_p(k)` and the `v_p(C(k-1,e))` terms.

  * `badIndex_max_factorization` — defect-one rigidity: when
    `badSet n k = {e}`, the bad index `e` simultaneously maximizes
    `v_p(n - i)` over `i < k` for EVERY prime `p ∣ k`.

  * `badIndex_eq_mod`, `badSet_eq_singleton_mod` — consequently `k ∣ n - e`,
    i.e. the unique bad index is `e = n % k` and the unique non-dividing
    term is `n - n % k = k⌊n/k⌋`.

  * `factorization_choose_eq_card_carries`, `pow_carry_card_dvd_sub_badIndex`
    — the #175 crossover, part 1: via `Erdos175.carry` (KummerDigits.lean),
    `v_p(C(n,k))` is the number of carries when adding `k` and `n-k` in base
    `p`, so `p^{v_p(k) + #carries}` divides the unique bad term `n - e`.

  * `pow_factorization_add_log_dvd_sub_badIndex` — the #175 crossover,
    part 2 (the case `u = t-1` below): `p^{v_p(k) + ⌊log_p(k-1)⌋} ∣ n - e`
    for every prime `p ∣ k`.  The proof needs `p ∣ C(k-1,e)` when both `e`
    and `k-1-e` are below `p^t ≤ k-1`; that is Kummer's criterion
    `Erdos175.prime_dvd_choose_add_iff_exists_carry` applied to the carry
    at place `t` in the base-`p` addition `e + (k-1-e)`.

  * `prod_pow_dvd_sub_badIndex`, `nk_mem`, `nk_lower_bound`,
    `nk_lower_bound_max` — multiplying over `p ∣ k` and specializing to
    `n = n_k`:

        max (2k, ∏_{p ∣ k} p^{v_p(k) + ⌊log_p(k-1)⌋}) ≤ n_k,

    the post-7439 claim, now machine-verified.

  Numerical check (2026-08-05, this session): the whole chain — defect one,
  `e = n % k`, rigidity, the per-prime bound, and the product bound — was
  verified by direct computation at all 42 known values of A389360
  (`2 ≤ k ≤ 41` plus a(43), a(47) from the OEIS comment).  The product
  bound is tight at `k = 6` (`72 ∣ 75 - 3`, bound 72, n₆ = 75) and `k = 14`
  (bound 784, n₁₄ = 793, e = 9).  The carry case `u = t - 1` genuinely
  occurs (13 times across those 42 values), so the Kummer step is
  load-bearing and not dead generality.

  ══════════════════════════════════════════════════════════════════════
  HONEST CLAIM BOUNDARY
  ══════════════════════════════════════════════════════════════════════

  The headline question of #1063 ("Estimate $n_k$") remains OPEN and is not
  advanced here: the bound proved below is exponentially far from the data
  for most `k` (at `k = 43` it gives `43` against `n₄₃ = 24458112`), and for
  prime `k` it degenerates to `max(2k, k) = 2k`, the definitional bound.
  What is new relative to SelfridgeDefect.lean is the rigidity structure of
  the defect-one configuration (`e = n % k`; `e` is the universal valuation
  maximizer) and the formal verification of the unrefereed comment-thread
  lower bound, with the Kummer carry layer of Erdos175 doing the critical
  case.  The exact identity `v_p(n-e) = v_p(C(n,k)) + v_p(k) + v_p(C(k-1,e))`
  (equality, not just `≤`) also holds and was confirmed numerically, but
  only the `≤` direction is formalized here.
-/
import Erdos.Erdos1063.SelfridgeDefect
import Erdos.Erdos175.KummerDigits

set_option autoImplicit false

open Finset

namespace Erdos1063

/-! ## The bad set -/

/-- `badSet n k` is the set of indices `0 ≤ i < k` for which `n - i` does
**not** divide `C(n,k)`; `divisorDefect n k` is its cardinality.  The
condition `divisorDefect n k = 1` defining `n_k` says `badSet n k` is a
singleton `{e}`, and this file is about the rigidity of that configuration. -/
def badSet (n k : ℕ) : Finset ℕ :=
  (Finset.range k).filter fun i => ¬ (n - i) ∣ n.choose k

/-- `divisorDefect` counts exactly the elements of `badSet`. -/
theorem divisorDefect_eq_card_badSet (n k : ℕ) :
    divisorDefect n k = (badSet n k).card := rfl

/-- Ground truth: `C(9,4) = 126`; among `9, 8, 7, 6` only `8` fails, at
index `1`. -/
example : badSet 9 4 = {1} := by decide

/-- Ground truth: `C(12,5) = 792`; among `12, …, 8` only `10` fails, at
index `2`. -/
example : badSet 12 5 = {2} := by decide

/-- Ground truth at a defect-4 point: `C(14,6) = 3003 = 3·7·11·13`, and the
even values `14, 12, 10` fail along with `9`.  So `badSet` is not always a
singleton, and theorems below assuming `badSet n k = {e}` are about a
genuinely special configuration. -/
example : badSet 14 6 = {0, 2, 4, 5} := by decide

/-- Boundary: at `k = 1` and `k = 0` the bad set is empty. -/
example : badSet 7 1 = ∅ ∧ badSet 7 0 = ∅ := by decide

/-- A defect-one point has a unique bad index. -/
theorem exists_badSet_eq_singleton (n k : ℕ) (h1 : divisorDefect n k = 1) :
    ∃ e, badSet n k = {e} :=
  Finset.card_eq_one.mp (by rw [← divisorDefect_eq_card_badSet]; exact h1)

/-- The unique bad index lies below `k`. -/
theorem badIndex_lt (n k e : ℕ) (hbad : badSet n k = {e}) : e < k := by
  have he : e ∈ badSet n k := by rw [hbad]; exact Finset.mem_singleton_self e
  exact Finset.mem_range.mp (Finset.mem_filter.mp he).1

/-- The unique bad index is bad: `(n - e) ∤ C(n,k)`. -/
theorem badIndex_not_dvd (n k e : ℕ) (hbad : badSet n k = {e}) :
    ¬ (n - e) ∣ n.choose k := by
  have he : e ∈ badSet n k := by rw [hbad]; exact Finset.mem_singleton_self e
  exact (Finset.mem_filter.mp he).2

/-- Every other index is good: `(n - i) ∣ C(n,k)` for `i < k`, `i ≠ e`. -/
theorem dvd_choose_of_ne_badIndex (n k e i : ℕ) (hbad : badSet n k = {e})
    (hik : i < k) (hne : i ≠ e) : (n - i) ∣ n.choose k := by
  by_contra hnd
  have hi : i ∈ badSet n k :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hik, hnd⟩
  rw [hbad, Finset.mem_singleton] at hi
  exact hne hi

/-! ## The strengthened core valuation inequality

`exists_factorization_choose_lt` (SelfridgeDefect.lean) proves
`v_p(C(n,k)) < v_p(n-e)` at a maximizer `e` of `v_p(n - ·)` by bounding
`e! · (k-1-e)! ∣ (k-1)!` and discarding the cofactor.  Keeping the exact
factorization `k! = k · C(k-1,e) · e! · (k-1-e)!` retains two more terms. -/

/-- **Strengthened core inequality.**  If `e < k ≤ n` maximizes
`v_p(n - i)` over `i < k`, then

    v_p(C(n,k)) + v_p(k) + v_p(C(k-1,e)) ≤ v_p(n - e).

Proof: for `i ≠ e`, `p^{v_p(n-i)}` divides `|i - e|`
(`pow_factorization_dvd_dist`), so `∑_{i ≠ e} v_p(n-i) ≤ v_p(e!·(k-1-e)!)`;
combine with the Legendre bookkeeping `∑_{i<k} v_p(n-i) = v_p(k!) + v_p(C(n,k))`
and `k! = k · C(k-1,e) · (e! · (k-1-e)!)`. -/
theorem factorization_choose_add_le_of_max (p n k e : ℕ) (hp : p.Prime)
    (hkn : k ≤ n) (hek : e < k)
    (hmax : ∀ i ∈ Finset.range k,
      (n - i).factorization p ≤ (n - e).factorization p) :
    (n.choose k).factorization p + k.factorization p
      + ((k - 1).choose e).factorization p ≤ (n - e).factorization p := by
  have he : e ∈ Finset.range k := Finset.mem_range.mpr hek
  have hdvd : p ^ (∑ i ∈ (Finset.range k).erase e, (n - i).factorization p)
      ∣ e.factorial * (k - 1 - e).factorial := by
    rw [← Finset.prod_pow_eq_pow_sum, ← prod_dist_erase_range k e hek]
    refine Finset.prod_dvd_prod_of_dvd _ _ ?_
    intro i hi
    have hi' := Finset.mem_of_mem_erase hi
    have hine : i ≠ e := Finset.ne_of_mem_erase hi
    exact pow_factorization_dvd_dist p n k e i hkn hek (Finset.mem_range.mp hi')
      (hmax i hi') hine
  have hff : e.factorial * (k - 1 - e).factorial ≠ 0 :=
    Nat.mul_ne_zero (Nat.factorial_ne_zero e) (Nat.factorial_ne_zero _)
  have hAle : (∑ i ∈ (Finset.range k).erase e, (n - i).factorization p)
      ≤ (e.factorial * (k - 1 - e).factorial).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp hff).mp hdvd
  have hsplit : (n - e).factorization p
      + (∑ i ∈ (Finset.range k).erase e, (n - i).factorization p)
      = ∑ i ∈ Finset.range k, (n - i).factorization p :=
    Finset.add_sum_erase _ (fun i => (n - i).factorization p) he
  have hsum := sum_factorization_sub_range p n k hkn
  have hchoose_ne : (k - 1).choose e ≠ 0 := Nat.choose_ne_zero (by omega)
  have hprod : k.factorial
      = k * ((k - 1).choose e * (e.factorial * (k - 1 - e).factorial)) := by
    have h1 : (k - 1).choose e * e.factorial * (k - 1 - e).factorial
        = (k - 1).factorial := Nat.choose_mul_factorial_mul_factorial (by omega)
    have h2 : k * (k - 1).factorial = k.factorial :=
      Nat.mul_factorial_pred (by omega)
    rw [← h2, ← h1]
    ring
  have hfact : (k.factorial).factorization p
      = k.factorization p + (((k - 1).choose e).factorization p
        + (e.factorial * (k - 1 - e).factorial).factorization p) := by
    rw [hprod, Nat.factorization_mul (by omega) (Nat.mul_ne_zero hchoose_ne hff),
      Nat.factorization_mul hchoose_ne hff]
    simp only [Finsupp.coe_add, Pi.add_apply]
  omega

/-! ## Defect-one rigidity -/

/-- **Rigidity.**  When `badSet n k = {e}`, the bad index `e` maximizes
`v_p(n - i)` over `i < k` for every prime `p ∣ k`: any maximizer `m` has
`v_p(n - m) ≥ v_p(C(n,k)) + v_p(k) > v_p(C(n,k))`, so `(n - m) ∤ C(n,k)`
and by uniqueness `m = e`. -/
theorem badIndex_max_factorization (n k e p : ℕ) (hkn : k ≤ n)
    (hbad : badSet n k = {e}) (hp : p.Prime) (hpk : p ∣ k) :
    ∀ i ∈ Finset.range k, (n - i).factorization p ≤ (n - e).factorization p := by
  have hek : e < k := badIndex_lt n k e hbad
  have hnem : (Finset.range k).Nonempty := ⟨e, Finset.mem_range.mpr hek⟩
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (Finset.range k)
    (fun i => (n - i).factorization p) hnem
  have hcore := factorization_choose_add_le_of_max p n k m hp hkn
    (Finset.mem_range.mp hm) hmax
  have hpos : 1 ≤ k.factorization p :=
    Nat.Prime.factorization_pos_of_dvd hp (by omega) hpk
  have hbadm : ¬ (n - m) ∣ n.choose k := by
    intro hdvd
    have h2 : p ^ ((n - m).factorization p) ∣ n.choose k :=
      dvd_trans (Nat.ordProj_dvd _ _) hdvd
    have h1 : (n - m).factorization p ≤ (n.choose k).factorization p :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp (Nat.choose_ne_zero hkn)).mp h2
    omega
  have hmem : m ∈ badSet n k := Finset.mem_filter.mpr ⟨hm, hbadm⟩
  rw [hbad, Finset.mem_singleton] at hmem
  subst hmem
  exact hmax

/-- Combining rigidity with the core inequality at `e` itself: for every
prime `p ∣ k`,

    v_p(C(n,k)) + v_p(k) + v_p(C(k-1,e)) ≤ v_p(n - e).

This is the promised "specific relationship" between the unique bad index
and the `p`-adic valuations of the block `n, n-1, …, n-k+1`. -/
theorem badIndex_factorization_add_le (n k e p : ℕ) (hkn : k ≤ n)
    (hbad : badSet n k = {e}) (hp : p.Prime) (hpk : p ∣ k) :
    (n.choose k).factorization p + k.factorization p
      + ((k - 1).choose e).factorization p ≤ (n - e).factorization p :=
  factorization_choose_add_le_of_max p n k e hp hkn (badIndex_lt n k e hbad)
    (badIndex_max_factorization n k e p hkn hbad hp hpk)

/-- **The bad index is `n % k`.**  Since `v_p(k) ≤ v_p(n - e)` for every
prime `p ∣ k`, we get `k ∣ n - e`, and `e < k` pins `e = n % k`. -/
theorem badIndex_eq_mod (n k e : ℕ) (hkn : k ≤ n) (hbad : badSet n k = {e}) :
    e = n % k := by
  have hek : e < k := badIndex_lt n k e hbad
  have hkdvd : k ∣ n - e := by
    rw [← Nat.factorization_le_iff_dvd (by omega) (by omega), Finsupp.le_iff]
    intro q hq
    rw [Nat.support_factorization] at hq
    have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hq_dvd : q ∣ k := Nat.dvd_of_mem_primeFactors hq
    have h := badIndex_factorization_add_le n k e q hkn hbad hq_prime hq_dvd
    omega
  have hmod : e % k = n % k :=
    (Nat.modEq_iff_dvd' (by omega : e ≤ n)).mpr hkdvd
  rwa [Nat.mod_eq_of_lt hek] at hmod

/-- Defect-one classification: if exactly one of `n, n-1, …, n-k+1` fails
to divide `C(n,k)`, the failure is exactly at `n - n % k = k·⌊n/k⌋`, the
unique multiple of `k` in the block. -/
theorem badSet_eq_singleton_mod (n k : ℕ) (hkn : k ≤ n)
    (h1 : divisorDefect n k = 1) : badSet n k = {n % k} := by
  obtain ⟨e, hbad⟩ := exists_badSet_eq_singleton n k h1
  rwa [badIndex_eq_mod n k e hkn hbad] at hbad

/-! ## The Kummer carry crossover (Erdős #175 layer)

`Erdos175.carry p m n i` (KummerDigits.lean) is the schoolbook carry
recursion for adding `m` and `n` in base `p`;
`Erdos175.padicValNat_choose_add_eq_card_carries` is Kummer's theorem over
it.  Writing `C(n,k) = C(k + (n-k), k)` turns `v_p(C(n,k))` into a carry
count for the addition `k + (n - k)`. -/

/-- **Kummer for `C(n,k)`, carry form.**  For `k ≤ n` and any window bound
`b > log_p n`, the valuation `v_p(C(n,k))` is the number of carries in the
base-`p` addition of `k` and `n - k`. -/
theorem factorization_choose_eq_card_carries {p n k b : ℕ} (hp : p.Prime)
    (hkn : k ≤ n) (hb : Nat.log p n < b) :
    (n.choose k).factorization p
      = ((Finset.Ico 1 b).filter
          fun i => Erdos175.carry p k (n - k) i = true).card := by
  obtain ⟨m, rfl⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
  simp only [Nat.add_sub_cancel_left]
  rw [Nat.factorization_def _ hp]
  exact Erdos175.padicValNat_choose_add_eq_card_carries hp hb

/-- **Carry-counting divisibility of the bad term.**  At a defect-one point
with bad index `e`, for every prime `p ∣ k`,

    p ^ (v_p(k) + #carries(k, n-k in base p))  ∣  n - e.

Each base-`p` carry in the addition `k + (n - k)` forces an extra factor
`p` in the unique non-dividing term. -/
theorem pow_carry_card_dvd_sub_badIndex (n k e p b : ℕ) (hkn : k ≤ n)
    (hbad : badSet n k = {e}) (hp : p.Prime) (hpk : p ∣ k)
    (hb : Nat.log p n < b) :
    p ^ (k.factorization p
        + ((Finset.Ico 1 b).filter
            fun i => Erdos175.carry p k (n - k) i = true).card)
      ∣ (n - e) := by
  have hD := badIndex_factorization_add_le n k e p hkn hbad hp hpk
  have hS := factorization_choose_eq_card_carries hp hkn hb
  refine dvd_trans (pow_dvd_pow p ?_) (Nat.ordProj_dvd (n - e) p)
  omega

/-! ## The per-prime `⌊log_p (k-1)⌋` bound -/

/-- Any block `n, n-1, …, n-k+1` contains a multiple of any `q ≤ k`
(namely `n - n % q`). -/
theorem exists_lt_dvd_sub (n k q : ℕ) (hq : 0 < q) (hqk : q ≤ k) :
    ∃ i, i < k ∧ q ∣ (n - i) := by
  refine ⟨n % q, lt_of_lt_of_le (Nat.mod_lt n hq) hqk, ?_⟩
  have hdm := Nat.div_add_mod n q
  have hsub : n - n % q = q * (n / q) := by omega
  rw [hsub]
  exact dvd_mul_right q (n / q)

/-- **Per-prime lower bound on the bad term** (the content of comment
post-7439, re-derived from scratch).  At a defect-one point with bad index
`e`, for every prime `p ∣ k`,

    p ^ (v_p(k) + ⌊log_p (k-1)⌋)  ∣  n - e.

Writing `t = ⌊log_p(k-1)⌋`, `r = max(e, k-1-e)`, `u = ⌊log_p r⌋`: the good
index at distance `p^u` from `e` gives `v_p(C(n,k)) ≥ u ≥ t-1`; if `u < t`
then `e, k-1-e < p^t ≤ k-1`, so the base-`p` addition `e + (k-1-e)` carries
at place `t` and Kummer (`Erdos175.prime_dvd_choose_add_iff_exists_carry`)
gives `v_p(C(k-1,e)) ≥ 1`.  Either way
`v_p(C(n,k)) + v_p(C(k-1,e)) ≥ t`, and `badIndex_factorization_add_le`
converts this into `v_p(n-e) ≥ v_p(k) + t`. -/
theorem pow_factorization_add_log_dvd_sub_badIndex (n k e p : ℕ) (hk : 2 ≤ k)
    (hkn : k ≤ n) (hbad : badSet n k = {e}) (hp : p.Prime) (hpk : p ∣ k) :
    p ^ (k.factorization p + Nat.log p (k - 1)) ∣ (n - e) := by
  have hp1 : 1 < p := hp.one_lt
  have hek : e < k := badIndex_lt n k e hbad
  have hmax := badIndex_max_factorization n k e p hkn hbad hp hpk
  have hD := badIndex_factorization_add_le n k e p hkn hbad hp hpk
  have hle1 : e ≤ max e (k - 1 - e) := le_max_left _ _
  have hle2 : k - 1 - e ≤ max e (k - 1 - e) := le_max_right _ _
  have hrle : max e (k - 1 - e) ≤ k - 1 := max_le (by omega) (by omega)
  have hr0 : max e (k - 1 - e) ≠ 0 := by omega
  -- Step 1: `v_p(C(n,k)) ≥ u` where `u = ⌊log_p r⌋`.
  have hSu : Nat.log p (max e (k - 1 - e)) ≤ (n.choose k).factorization p := by
    have hpu_le : p ^ Nat.log p (max e (k - 1 - e)) ≤ max e (k - 1 - e) :=
      Nat.pow_log_le_self p hr0
    have hpu_pos : 0 < p ^ Nat.log p (max e (k - 1 - e)) := pow_pos (by omega) _
    -- `p^u` divides the bad term, via the block multiple and rigidity.
    have hpu_dvd_e : p ^ Nat.log p (max e (k - 1 - e)) ∣ (n - e) := by
      obtain ⟨i₀, hi₀k, hi₀d⟩ :=
        exists_lt_dvd_sub n k (p ^ Nat.log p (max e (k - 1 - e))) hpu_pos (by omega)
      have h1 : Nat.log p (max e (k - 1 - e)) ≤ (n - i₀).factorization p :=
        (Nat.Prime.pow_dvd_iff_le_factorization hp (by omega)).mp hi₀d
      have h2 : (n - i₀).factorization p ≤ (n - e).factorization p :=
        hmax i₀ (Finset.mem_range.mpr hi₀k)
      exact dvd_trans (pow_dvd_pow p (by omega)) (Nat.ordProj_dvd _ _)
    -- A good index at distance exactly `p^u` from `e`.
    obtain ⟨i, hik, hine, hdisteq⟩ : ∃ i, i < k ∧ i ≠ e ∧
        (n - i = (n - e) + p ^ Nat.log p (max e (k - 1 - e)) ∨
         n - i = (n - e) - p ^ Nat.log p (max e (k - 1 - e))) := by
      rcases max_choice e (k - 1 - e) with hre | hre
      · exact ⟨e - p ^ Nat.log p (max e (k - 1 - e)), by omega, by omega,
          Or.inl (by omega)⟩
      · exact ⟨e + p ^ Nat.log p (max e (k - 1 - e)), by omega, by omega,
          Or.inr (by omega)⟩
    have hgood : (n - i) ∣ n.choose k :=
      dvd_choose_of_ne_badIndex n k e i hbad hik hine
    have hpu_dvd_i : p ^ Nat.log p (max e (k - 1 - e)) ∣ (n - i) := by
      rcases hdisteq with h | h
      · rw [h]; exact dvd_add hpu_dvd_e dvd_rfl
      · rw [h]; exact Nat.dvd_sub hpu_dvd_e dvd_rfl
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp
      (Nat.choose_ne_zero hkn)).mp (dvd_trans hpu_dvd_i hgood)
  -- Step 2: `v_p(C(n,k)) + v_p(C(k-1,e)) ≥ t`, splitting on `u ≥ t` vs `u = t-1`.
  have hW : Nat.log p (k - 1) ≤ (n.choose k).factorization p
      + ((k - 1).choose e).factorization p := by
    rcases Nat.lt_or_ge (Nat.log p (max e (k - 1 - e))) (Nat.log p (k - 1))
      with hcase | hcase
    swap
    · omega
    · -- `u < t`: first `u ≥ t - 1` …
      have hpt_le : p ^ Nat.log p (k - 1) ≤ k - 1 :=
        Nat.pow_log_le_self p (by omega)
      have hps : p * p ^ (Nat.log p (k - 1) - 1) = p ^ Nat.log p (k - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have hchain : p * p ^ (Nat.log p (k - 1) - 1)
          ≤ p * max e (k - 1 - e) := by
        calc p * p ^ (Nat.log p (k - 1) - 1)
            = p ^ Nat.log p (k - 1) := hps
          _ ≤ k - 1 := hpt_le
          _ ≤ 2 * max e (k - 1 - e) := by omega
          _ ≤ p * max e (k - 1 - e) :=
              Nat.mul_le_mul_right _ (by omega : 2 ≤ p)
      have hpt1_le : p ^ (Nat.log p (k - 1) - 1) ≤ max e (k - 1 - e) :=
        Nat.le_of_mul_le_mul_left hchain (by omega)
      have hu_ge : Nat.log p (k - 1) - 1 ≤ Nat.log p (max e (k - 1 - e)) :=
        Nat.le_log_of_pow_le hp1 hpt1_le
      -- … then the Kummer carry gives `p ∣ C(k-1, e)`.
      have hstep := Nat.lt_pow_succ_log_self hp1 (max e (k - 1 - e))
      have hmono : p ^ (Nat.log p (max e (k - 1 - e))).succ
          ≤ p ^ Nat.log p (k - 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have he_lt : e < p ^ Nat.log p (k - 1) := by omega
      have hke_lt : k - 1 - e < p ^ Nat.log p (k - 1) := by omega
      have hcarry : Erdos175.carry p e (k - 1 - e) (Nat.log p (k - 1)) = true := by
        rw [Erdos175.carry_eq_true_iff hp1, Nat.mod_eq_of_lt he_lt,
          Nat.mod_eq_of_lt hke_lt]
        omega
      have hpdvd : p ∣ (k - 1).choose e := by
        have h := (Erdos175.prime_dvd_choose_add_iff_exists_carry
          (p := p) (m := e) (n := k - 1 - e) hp).mpr ⟨Nat.log p (k - 1), hcarry⟩
        have heq : e + (k - 1 - e) = k - 1 := by omega
        rwa [heq] at h
      have hWpos : 0 < ((k - 1).choose e).factorization p :=
        Nat.Prime.factorization_pos_of_dvd hp (Nat.choose_ne_zero (by omega)) hpdvd
      omega
  refine dvd_trans (pow_dvd_pow p ?_) (Nat.ordProj_dvd (n - e) p)
  omega

/-! ## The product bound and the `n_k` lower bound -/

/-- Multiplying the per-prime bounds over the (pairwise coprime) prime
powers: at a defect-one point with bad index `e`,

    ∏_{p ∣ k} p ^ (v_p(k) + ⌊log_p (k-1)⌋)  ∣  n - e. -/
theorem prod_pow_dvd_sub_badIndex (n k e : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n)
    (hbad : badSet n k = {e}) :
    (∏ p ∈ k.primeFactors, p ^ (k.factorization p + Nat.log p (k - 1)))
      ∣ (n - e) := by
  have hek : e < k := badIndex_lt n k e hbad
  have hprim : ∀ p ∈ k.primeFactors, p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactors hp
  have hne0 : ∀ p ∈ k.primeFactors,
      p ^ (k.factorization p + Nat.log p (k - 1)) ≠ 0 :=
    fun p hp => pow_ne_zero _ (hprim p hp).ne_zero
  have happ : ∀ q : ℕ,
      (∏ p ∈ k.primeFactors,
        p ^ (k.factorization p + Nat.log p (k - 1))).factorization q
      = if q ∈ k.primeFactors then k.factorization q + Nat.log q (k - 1)
        else 0 := by
    intro q
    rw [Nat.factorization_prod hne0, Finset.sum_apply',
      Finset.sum_congr rfl (fun p hp => by
        rw [(hprim p hp).factorization_pow, Finsupp.single_apply])]
    exact Finset.sum_ite_eq' k.primeFactors q _
  rw [← Nat.factorization_le_iff_dvd
    (Finset.prod_ne_zero_iff.mpr hne0) (by omega), Finsupp.le_iff]
  intro q _
  rw [happ q]
  by_cases hqk : q ∈ k.primeFactors
  · rw [if_pos hqk]
    have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hqk
    have hdvd := pow_factorization_add_log_dvd_sub_badIndex n k e q hk hkn hbad
      hq_prime (Nat.dvd_of_mem_primeFactors hqk)
    exact (Nat.Prime.pow_dvd_iff_le_factorization hq_prime (by omega)).mp hdvd
  · rw [if_neg hqk]
    exact Nat.zero_le _

/-- `n_k` belongs to its defining set: `2k ≤ n_k` and
`divisorDefect (n_k) k = 1`, for every `k ≥ 2`.  (This also certifies that
the `sInf` defining `nk` is over a nonempty set — witness `4` at `k = 2`
and `k!` for `k ≥ 3` — so `nk k` is never the junk value `sInf ∅ = 0`.) -/
theorem nk_mem (k : ℕ) (hk : 2 ≤ k) :
    2 * k ≤ nk k ∧ divisorDefect (nk k) k = 1 := by
  have hne : {n : ℕ | 2 * k ≤ n ∧ divisorDefect n k = 1}.Nonempty := by
    rcases eq_or_lt_of_le hk with rfl | h3
    · exact ⟨4, by norm_num, by decide⟩
    · refine ⟨k.factorial, two_mul_le_factorial k h3, ?_⟩
      have hpos := erdos_selfridge_defect_pos k.factorial k hk
        (Nat.self_le_factorial k)
      have hle := divisorDefect_factorial_le_one k
      omega
  exact Nat.sInf_mem hne

/-- **The `n_k` lower bound** (the post-7439 comment-thread claim,
machine-verified):

    ∏_{p ∣ k} p ^ (v_p(k) + ⌊log_p (k-1)⌋)  ≤  n_k    for all k ≥ 2. -/
theorem nk_lower_bound (k : ℕ) (hk : 2 ≤ k) :
    (∏ p ∈ k.primeFactors, p ^ (k.factorization p + Nat.log p (k - 1)))
      ≤ nk k := by
  obtain ⟨h2k, h1⟩ := nk_mem k hk
  obtain ⟨e, hbad⟩ := exists_badSet_eq_singleton (nk k) k h1
  have hkn : k ≤ nk k := by omega
  have hek : e < k := badIndex_lt (nk k) k e hbad
  have hdvd := prod_pow_dvd_sub_badIndex (nk k) k e hk hkn hbad
  have hle : (∏ p ∈ k.primeFactors,
      p ^ (k.factorization p + Nat.log p (k - 1))) ≤ nk k - e :=
    Nat.le_of_dvd (by omega) hdvd
  omega

/-- The lower bound in the source's `max` form:
`max (2k, ∏_{p ∣ k} p^{v_p(k) + ⌊log_p(k-1)⌋}) ≤ n_k`. -/
theorem nk_lower_bound_max (k : ℕ) (hk : 2 ≤ k) :
    max (2 * k)
      (∏ p ∈ k.primeFactors, p ^ (k.factorization p + Nat.log p (k - 1)))
      ≤ nk k :=
  max_le (nk_mem k hk).1 (nk_lower_bound k hk)

/-! ## Satisfiability witnesses

STYLE.md requires jointly instantiating every hypothesis at concrete
models and showing the conclusions are non-degenerate. -/

/-- Joint instantiation of the hypotheses of `badSet_eq_singleton_mod`,
`badIndex_factorization_add_le`, and `pow_factorization_add_log_dvd_sub_badIndex`
at `(n, k) = (9, 4)`, `p = 2`: all hypotheses hold and the bad set is the
singleton `{1}` with `1 = 9 % 4`. -/
example : 2 ≤ 4 ∧ 4 ≤ 9 ∧ divisorDefect 9 4 = 1 ∧ badSet 9 4 = {9 % 4} ∧
    Nat.Prime 2 ∧ (2 ∣ 4) := by decide

/-- Non-degeneracy and tightness of the per-prime bound at `(9, 4, p = 2)`:
the guaranteed divisor is `2^{v_2(4) + ⌊log_2 3⌋} = 2^3 = 8`, and the bad
term is `9 - 9 % 4 = 8` itself — the bound is attained. -/
example : (2 : ℕ) ^ ((4 : ℕ).factorization 2 + Nat.log 2 3) = 9 - 9 % 4 := by
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  have hf : (4 : ℕ).factorization 2 = 2 := by
    rw [h4, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
  have hl : Nat.log 2 3 = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  rw [hf, hl]
  norm_num

/-- End-to-end evaluation of `nk_lower_bound` at `k = 4`: the product bound
evaluates to `8` and `n₄ = 9` (`nk_four`, SelfridgeDefect.lean), so the
bound is one off the true value and in particular not vacuous. -/
example : (∏ p ∈ (4 : ℕ).primeFactors,
    p ^ ((4 : ℕ).factorization p + Nat.log p (4 - 1))) = 8 ∧ nk 4 = 9 := by
  constructor
  · have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [show (4 : ℕ) - 1 = 3 by norm_num, h4,
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
      Finset.prod_singleton, Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_eq_same,
      Nat.log_eq_of_pow_le_of_lt_pow (by norm_num : 2 ^ 1 ≤ 3) (by norm_num)]
    norm_num
  · exact nk_four

/-- The carry count in `pow_carry_card_dvd_sub_badIndex` is not always `0`:
at `(n, k) = (9, 4)`, `p = 2`, adding `4 = (100)₂` and `5 = (101)₂` carries
once (into place `3`), matching `v_2(C(9,4)) = v_2(126) = 1`. -/
example : Erdos175.carry 2 4 5 3 = true ∧ Erdos175.carry 2 4 5 1 = false ∧
    Nat.choose 9 4 = 126 := by decide

/-- The rigidity conclusion is non-degenerate: at `(9, 4)`, `p = 2`, the
valuations of `9, 8, 7, 6` are `0, 3, 0, 1`, maximized exactly at the bad
term `8`. -/
example : (2 ∣ 4) ∧ ¬ (8 ∣ Nat.choose 9 4) ∧ (7 ∣ Nat.choose 9 4) ∧
    (9 ∣ Nat.choose 9 4) ∧ (6 ∣ Nat.choose 9 4) := by decide

/-! ## Axiom audit -/

#print axioms Erdos1063.badSet_eq_singleton_mod
#print axioms Erdos1063.badIndex_eq_mod
#print axioms Erdos1063.badIndex_max_factorization
#print axioms Erdos1063.badIndex_factorization_add_le
#print axioms Erdos1063.factorization_choose_add_le_of_max
#print axioms Erdos1063.factorization_choose_eq_card_carries
#print axioms Erdos1063.pow_carry_card_dvd_sub_badIndex
#print axioms Erdos1063.pow_factorization_add_log_dvd_sub_badIndex
#print axioms Erdos1063.prod_pow_dvd_sub_badIndex
#print axioms Erdos1063.nk_mem
#print axioms Erdos1063.nk_lower_bound
#print axioms Erdos1063.nk_lower_bound_max

end Erdos1063
