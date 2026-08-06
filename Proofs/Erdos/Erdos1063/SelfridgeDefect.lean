/-
  Erdős Problem #1063 — the Erdős–Selfridge defect lemma, and the
  small-value table for `n_k`.

  ## Primary source (VERBATIM, `goof erdos fetch 1063`, pulled 2026-08-05)

  Statement field:

    "Let $k\geq 2$ and define $n_k\geq 2k$ to be the least value of $n$ such
     that $n-i$ divides $\binom{n}{k}$ for all but one $0\leq i<k$.
     Estimate $n_k$."

  Body field (first paragraph, verbatim):

    "A problem of Erd\H{o}s and Selfridge posed in \cite{ErSe83}. Erd\H{o}s
     and Selfridge noted (and a proof can be found in \cite{Mo85}) that if
     $n\geq 2k$ then there must exist at least one $0\leq i<k$ such that
     $n-i$ does not divide $\binom{n}{k}$.

     We have $n_2=4$, $n_3=6$, $n_4=9$, and $n_5=12$. Monier \cite{Mo85}
     observed that $n_k\leq k!$ for $k\geq 3$, since $\binom{k!}{k}$ is
     divisible by $k!-i$ for $1\leq i<k$. Cambie observes in the comments
     that this can be improved to\[n_k\leq k[2,3,\ldots,k-1]\leq
     e^{(1+o(1))k},\]where $[\cdots]$ is the least common multiple.

     This is discussed in problem B31 of Guy's collection \cite{Gu04}."

  References field (verbatim):

    "[ErSe83] Erdos, P. and Selfridge, J. L., *Problem 6447*. Amer. Math.
     Monthly (1983), 710.

     [Gu04] Guy, Richard K., *Unsolved problems in number theory*. (2004),
     xviii+437.

     [Mo85] Monier, Jean-Marie, *Problems and Solutions: Solutions of
     {A}dvanced {P}roblems: 6447*. Amer. Math. Monthly (1985), 435--436."

  ## OEIS cross-reference (VERBATIM, `goof oeis show A389360`, 2026-08-05)

    name:  "Smallest m >= 2*n such that binomial(m,n) is a multiple of m-i
            for all 0<=i<n, but one."
    terms: "4,6,9,12,75,30,70,56,2403,280,3465,210,793,4732,3213,1456,31110,
            612,67203,145540,464646,2640,476938,21000,86550,234026,1053702,
            34776,37584001,8100,2301456,77780756,61924632,26515138,105846930,
            665280,622999377,233999782,510752034,1154440"

  (A389360's index variable `n` is the problem's `k`; offset 2.  So
  a(2) = 4 = n₂, a(3) = 6 = n₃, a(4) = 9 = n₄, a(5) = 12 = n₅, matching the
  four values quoted in the problem body.)

  ## What this file proves

  The headline question ("Estimate n_k") is OPEN and is NOT addressed here.
  What is proved, sorry-free:

  * `erdos_selfridge_defect_pos` — the Erdős–Selfridge lemma: for `2 ≤ k` and
    `k ≤ n` there is at least one `0 ≤ i < k` with `(n - i) ∤ C(n,k)`.  This
    is the statement the source attributes to Erdős–Selfridge with a proof in
    Monier [Mo85]; it is what makes "all but one" the optimal phrasing and
    what makes `n_k` well posed.  NOTE: proved under the weaker hypothesis
    `k ≤ n` rather than the source's `2*k ≤ n`; the source form is recorded
    separately as `erdos_selfridge_defect_pos_of_two_mul_le`.

  * `nk_two`, `nk_three`, `nk_four`, `nk_five` — `n₂ = 4`, `n₃ = 6`,
    `n₄ = 9`, `n₅ = 12`, the four values quoted in the source body, certified
    by `decide` against the definition of `nk` as a `sInf`.

  * `nk_six`, …, `nk_ten` — `n₆ = 75`, `n₇ = 30`, `n₈ = 70`, `n₉ = 56`,
    `n₁₀ = 2403`, the continuation of the table, matching OEIS A389360
    terms a(6)–a(10) quoted verbatim above.  These five values are NOT
    quoted in the erdosproblems.com body (which stops at `n₅`); each was
    recomputed independently from the definition (Python sweep, 2026-08-05)
    before proving, and each is certified by kernel `decide` — membership
    plus a single bounded-forall minimality sweep (`nk_eq_of_ball`).  The
    `k = 10` sweep covers all `20 ≤ n < 2403` and needs only a raised
    `maxRecDepth` (the `Nat.choose` and `Nat.decidableBallLT` recursions
    are ≈ 2403 deep); no `native_decide` anywhere.

  * `nk_le_factorial` — Monier's bound `n_k ≤ k!` for `3 ≤ k`, via the exact
    identity `C(k!, k) = ∏_{j=1}^{k-1} (k! - j)` (`choose_factorial_self_eq`).
    This also certifies that the `sInf` defining `nk` is over a NONEMPTY set
    for every `k ≥ 3` (together with `nk_two`, `nk_three`, every `k ≥ 2`), so
    `nk k` is never the `sInf ∅ = 0` junk value.

  NOT proved here (recorded for downstream work): Cambie's improvement
  `n_k ≤ k · lcm(2, …, k-1)`, and the comment-thread lower bound
  `n_k ≥ ∏_{p^a ∥ k} p^{a + ⌊log_p (k-1)⌋}` (erdosproblems.com comments
  post-7233 / post-7439 by user `rickyc`, Jun–Jul 2026; explicitly
  AI-assisted and unrefereed, so it is not taken as a source claim).

  ## Proof of the defect lemma

  Write `d_i = n - i` for `0 ≤ i < k`, let `p` be any prime dividing `k`
  (exists since `k ≥ 2`), let `a = v_p(k) ≥ 1`, let `e < k` maximize
  `v_p(d_i)`, and put `M = v_p(d_e)`, `S = v_p(C(n,k))`.  The claim is
  `S + a ≤ M`, whence `S < M` and so `d_e ∤ C(n,k)`.

  For `i ≠ e` both `d_i` and `d_e` are divisible by `p^{v_p(d_i)}` (the
  latter because `v_p(d_i) ≤ M`), hence so is their difference `±(i - e)`;
  therefore `p^{v_p(d_i)} ∣ dist i e`.  Multiplying over `i ≠ e`,

      p^{∑_{i ≠ e} v_p(d_i)} ∣ ∏_{i ≠ e} dist i e = e! · (k-1-e)! ∣ (k-1)!,

  so `∑_{i ≠ e} v_p(d_i) ≤ v_p((k-1)!)`.  On the other hand
  `∏_{i<k} d_i = k! · C(n,k)` gives `M + ∑_{i ≠ e} v_p(d_i) = v_p(k!) + S`
  and `v_p(k!) = a + v_p((k-1)!)`.  Combining the three displays yields
  `S + a ≤ M`.  (This is the `p ∣ k` specialization of the valuation
  identity in the erdosproblems.com comment thread; it is re-derived from
  scratch here and depends on no comment claim.)
-/
import Mathlib

set_option autoImplicit false

open Finset

namespace Erdos1063

/-! ## The defect -/

/-- `divisorDefect n k` is the number of indices `0 ≤ i < k` for which `n - i`
does **not** divide `C(n,k)`.  The problem's phrase "`n - i` divides
`C(n,k)` for all but one `0 ≤ i < k`" is exactly `divisorDefect n k = 1`.

The truncated subtraction `n - i` is harmless in the regime the file works
in: every hypothesis below forces `k ≤ n`, and then `i < k ≤ n` gives
`1 ≤ n - i`. -/
def divisorDefect (n k : ℕ) : ℕ :=
  ((Finset.range k).filter (fun i => ¬ (n - i) ∣ n.choose k)).card

/-- Ground truth for `divisorDefect` at `(n, k) = (4, 2)`: `C(4,2) = 6`,
`4 ∤ 6` and `3 ∣ 6`, so the defect is `1`. -/
example : divisorDefect 4 2 = 1 := by decide

/-- Ground truth at `(8, 4)`: `C(8,4) = 70`; `8 ∤ 70`, `7 ∣ 70`, `6 ∤ 70`,
`5 ∣ 70`, so the defect is `2`.  (This is the fact that rules out `n = 8`
in `nk_four`.) -/
example : divisorDefect 8 4 = 2 := by decide

/-- Ground truth at `(9, 4)`: `C(9,4) = 126`; `9 ∣ 126`, `8 ∤ 126`,
`7 ∣ 126`, `6 ∣ 126`, so the defect is `1`. -/
example : divisorDefect 9 4 = 1 := by decide

/-- Ground truth at `(11, 5)`: `C(11,5) = 462 = 2·3·7·11`; only `11` and `7`
divide it among `11, 10, 9, 8, 7`, so the defect is `3`. -/
example : divisorDefect 11 5 = 3 := by decide

/-- Boundary behaviour: at `k = 1` the defect is always `0` (`n ∣ C(n,1) = n`),
so the hypothesis `2 ≤ k` in `erdos_selfridge_defect_pos` is load-bearing and
not a vacuity guard.  Likewise `divisorDefect n 0 = 0` since `range 0 = ∅`. -/
example : divisorDefect 7 1 = 0 ∧ divisorDefect 7 0 = 0 := by decide

/-! ## Combinatorics of `∏ dist i e` over a punctured range -/

/-- Puncturing `range k` at `e < k` splits it as `range e ∪ Ico (e+1) k`. -/
theorem erase_range_eq_union (k e : ℕ) (he : e < k) :
    (Finset.range k).erase e = Finset.range e ∪ Finset.Ico (e + 1) k := by
  ext i
  simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
  omega

/-- Below the puncture point the distances run over `e, e-1, …, 1`, so their
product is `e !`. -/
theorem prod_dist_range_eq_factorial (e : ℕ) :
    ∏ i ∈ Finset.range e, Nat.dist i e = e.factorial := by
  have h : ∀ i ∈ Finset.range e, Nat.dist i e = (fun j => j + 1) (e - 1 - i) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Nat.dist]
    omega
  rw [Finset.prod_congr rfl h, Finset.prod_range_reflect (fun j => j + 1) e,
    Finset.prod_range_add_one_eq_factorial]

/-- Above the puncture point the distances run over `1, 2, …, k-1-e`, so their
product is `(k-1-e)!`. -/
theorem prod_dist_Ico_eq_factorial (k e : ℕ) (he : e < k) :
    ∏ i ∈ Finset.Ico (e + 1) k, Nat.dist i e = (k - 1 - e).factorial := by
  rw [Finset.prod_Ico_eq_prod_range]
  have h : ∀ j ∈ Finset.range (k - (e + 1)), Nat.dist (e + 1 + j) e = j + 1 := by
    intro j _
    simp only [Nat.dist]
    omega
  have hk : k - (e + 1) = k - 1 - e := by omega
  rw [Finset.prod_congr rfl h, hk, Finset.prod_range_add_one_eq_factorial]

/-- The product of the distances from `e` to the other points of `range k`
factors as `e ! · (k-1-e)!`. -/
theorem prod_dist_erase_range (k e : ℕ) (he : e < k) :
    ∏ i ∈ (Finset.range k).erase e, Nat.dist i e
      = e.factorial * (k - 1 - e).factorial := by
  have hdisj : Disjoint (Finset.range e) (Finset.Ico (e + 1) k) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_range] at ha
    simp only [Finset.mem_Ico] at hb
    omega
  rw [erase_range_eq_union k e he, Finset.prod_union hdisj,
    prod_dist_range_eq_factorial, prod_dist_Ico_eq_factorial k e he]

/-- Consequently that product divides `(k-1)!`, since
`e ! · (k-1-e)! ∣ (e + (k-1-e))! = (k-1)!`. -/
theorem prod_dist_erase_range_dvd (k e : ℕ) (he : e < k) :
    (∏ i ∈ (Finset.range k).erase e, Nat.dist i e) ∣ (k - 1).factorial := by
  have hsum : e + (k - 1 - e) = k - 1 := by omega
  rw [prod_dist_erase_range k e he]
  calc e.factorial * (k - 1 - e).factorial
      ∣ (e + (k - 1 - e)).factorial := Nat.factorial_mul_factorial_dvd_factorial_add _ _
    _ = (k - 1).factorial := by rw [hsum]

/-! ## The valuation inequality -/

/-- If `v_p(n - i) ≤ v_p(n - e)` and `i ≠ e`, then `p ^ v_p(n - i)` divides the
distance `|i - e|`: it divides both `n - i` (by definition of the valuation)
and `n - e` (through `p ^ v_p(n-i) ∣ p ^ v_p(n-e)`), hence their difference. -/
theorem pow_factorization_dvd_dist (p n k e i : ℕ) (hkn : k ≤ n) (he : e < k)
    (hi : i < k) (hmax : (n - i).factorization p ≤ (n - e).factorization p)
    (hne : i ≠ e) :
    p ^ ((n - i).factorization p) ∣ Nat.dist i e := by
  have h1 : p ^ ((n - i).factorization p) ∣ (n - i) := Nat.ordProj_dvd _ _
  have h2 : p ^ ((n - i).factorization p) ∣ (n - e) :=
    dvd_trans (pow_dvd_pow p hmax) (Nat.ordProj_dvd _ _)
  rcases lt_or_gt_of_ne hne with h | h
  · have hd : Nat.dist i e = (n - i) - (n - e) := by simp only [Nat.dist]; omega
    rw [hd]
    exact Nat.dvd_sub h1 h2
  · have hd : Nat.dist i e = (n - e) - (n - i) := by simp only [Nat.dist]; omega
    rw [hd]
    exact Nat.dvd_sub h2 h1

/-- Legendre bookkeeping for the falling factorial: for `k ≤ n`,
`∑_{i<k} v_p(n - i) = v_p(k!) + v_p(C(n,k))`, because
`∏_{i<k}(n - i) = k! · C(n,k)` and every factor is nonzero. -/
theorem sum_factorization_sub_range (p n k : ℕ) (hkn : k ≤ n) :
    ∑ i ∈ Finset.range k, (n - i).factorization p
      = (k.factorial).factorization p + (n.choose k).factorization p := by
  have hprod : ∏ i ∈ Finset.range k, (n - i) = k.factorial * n.choose k := by
    rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose]
  have hne : ∀ i ∈ Finset.range k, n - i ≠ 0 := by
    intro i hi
    simp only [Finset.mem_range] at hi
    omega
  have hL := Nat.factorization_prod (S := Finset.range k) (g := fun i => n - i) hne
  rw [hprod, Nat.factorization_mul (Nat.factorial_ne_zero k) (Nat.choose_ne_zero hkn)] at hL
  have happ := congrFun (congrArg (⇑) hL) p
  simpa only [Finsupp.add_apply, Finset.sum_apply'] using happ.symm

/-- **Core inequality.**  For a prime `p ∣ k` and `k ≤ n`, some `e < k` has
`v_p(C(n,k)) < v_p(n - e)`.  Take `e` maximizing `v_p(n - i)`; then
`v_p(C(n,k)) + v_p(k) ≤ v_p(n - e)` and `v_p(k) ≥ 1`. -/
theorem exists_factorization_choose_lt (p n k : ℕ) (hp : p.Prime) (hpk : p ∣ k)
    (hk : 2 ≤ k) (hkn : k ≤ n) :
    ∃ e ∈ Finset.range k, (n.choose k).factorization p < (n - e).factorization p := by
  have hnem : (Finset.range k).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨e, he, hmax⟩ :=
    Finset.exists_max_image (Finset.range k) (fun i => (n - i).factorization p) hnem
  refine ⟨e, he, ?_⟩
  have hek : e < k := Finset.mem_range.mp he
  have hdvd : p ^ (∑ i ∈ (Finset.range k).erase e, (n - i).factorization p)
      ∣ (k - 1).factorial := by
    rw [← Finset.prod_pow_eq_pow_sum]
    refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ _ ?_) (prod_dist_erase_range_dvd k e hek)
    intro i hi
    have hi' := Finset.mem_of_mem_erase hi
    have hine : i ≠ e := Finset.ne_of_mem_erase hi
    exact pow_factorization_dvd_dist p n k e i hkn hek (Finset.mem_range.mp hi') (hmax i hi') hine
  have hAle : (∑ i ∈ (Finset.range k).erase e, (n - i).factorization p)
      ≤ ((k - 1).factorial).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp (Nat.factorial_ne_zero _)).mp hdvd
  have hsplit : (n - e).factorization p
      + (∑ i ∈ (Finset.range k).erase e, (n - i).factorization p)
      = ∑ i ∈ Finset.range k, (n - i).factorization p :=
    Finset.add_sum_erase _ (fun i => (n - i).factorization p) he
  have hsum := sum_factorization_sub_range p n k hkn
  have hfact : (k.factorial).factorization p
      = k.factorization p + ((k - 1).factorial).factorization p := by
    rw [← Nat.mul_factorial_pred (n := k) (by omega),
      Nat.factorization_mul (by omega) (Nat.factorial_ne_zero _)]
    simp only [Finsupp.coe_add, Pi.add_apply]
  have hpos : 1 ≤ k.factorization p := Nat.Prime.factorization_pos_of_dvd hp (by omega) hpk
  omega

/-! ## The Erdős–Selfridge defect lemma -/

/-- **Erdős–Selfridge** (Problem 6447, Amer. Math. Monthly 1983; solution
Monier 1985).  For `2 ≤ k` and `k ≤ n` there is at least one `0 ≤ i < k` with
`(n - i) ∤ C(n,k)`; equivalently `1 ≤ divisorDefect n k`.

The source states this for `n ≥ 2k`; the argument only needs `k ≤ n`, and the
source form is `erdos_selfridge_defect_pos_of_two_mul_le`.

The hypothesis `2 ≤ k` cannot be dropped: `divisorDefect n 1 = 0` for every
`n` (see the boundary example above). -/
theorem erdos_selfridge_defect_pos (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    1 ≤ divisorDefect n k := by
  obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd (n := k) (by omega)
  obtain ⟨e, he, hlt⟩ := exists_factorization_choose_lt p n k hp hpk hk hkn
  have hnd : ¬ (n - e) ∣ n.choose k := by
    intro hdvd
    have h2 : p ^ ((n - e).factorization p) ∣ n.choose k :=
      dvd_trans (Nat.ordProj_dvd _ _) hdvd
    have h1 : (n - e).factorization p ≤ (n.choose k).factorization p :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp (Nat.choose_ne_zero hkn)).mp h2
    omega
  have hmem : e ∈ (Finset.range k).filter (fun i => ¬ (n - i) ∣ n.choose k) :=
    Finset.mem_filter.mpr ⟨he, hnd⟩
  exact Finset.card_pos.mpr ⟨e, hmem⟩

/-- The Erdős–Selfridge lemma in the source's own regime `2k ≤ n`. -/
theorem erdos_selfridge_defect_pos_of_two_mul_le (n k : ℕ) (hk : 2 ≤ k)
    (hn : 2 * k ≤ n) : 1 ≤ divisorDefect n k :=
  erdos_selfridge_defect_pos n k hk (by omega)

/-- Because the defect is never `0`, "at most one exceptional `i`" and
"exactly one exceptional `i`" define the same set of `n`.  This is what makes
the `= 1` in the definition of `nk` the faithful reading of the source's
"for all but one `0 ≤ i < k`". -/
theorem divisorDefect_le_one_iff_eq_one (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    divisorDefect n k ≤ 1 ↔ divisorDefect n k = 1 := by
  have h := erdos_selfridge_defect_pos n k hk hkn
  omega

/-! ## `n_k` and the small-value table -/

/-- `nk k` is the source's `n_k`: the least `n` with `2k ≤ n` such that `n - i`
divides `C(n,k)` for all but exactly one `0 ≤ i < k`.

`sInf ∅ = 0` in `ℕ`, so a nonemptiness certificate is required for the value
to be meaningful; `nk_two`, `nk_three` and `nk_le_factorial` supply one for
every `k ≥ 2`. -/
noncomputable def nk (k : ℕ) : ℕ :=
  sInf {n : ℕ | 2 * k ≤ n ∧ divisorDefect n k = 1}

/-- Extensionality principle for `nk`: a member of the defining set that is
below every other member is the infimum. -/
theorem nk_eq_of (k m : ℕ) (hmem : 2 * k ≤ m ∧ divisorDefect m k = 1)
    (hmin : ∀ n, 2 * k ≤ n → n < m → divisorDefect n k ≠ 1) : nk k = m := by
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨m, hmem⟩ ?_)
  rintro b ⟨hb1, hb2⟩
  by_contra hlt
  exact hmin b hb1 (by omega) hb2

/-- Bounded-forall variant of `nk_eq_of`: the minimality hypothesis is shaped
with `n < m` first so that `Nat.decidableBallLT` applies and one `decide` can
discharge the whole sweep, which matters for the larger certificates below. -/
theorem nk_eq_of_ball (k m : ℕ) (hmem : 2 * k ≤ m ∧ divisorDefect m k = 1)
    (hmin : ∀ n, n < m → 2 * k ≤ n → divisorDefect n k ≠ 1) : nk k = m :=
  nk_eq_of k m hmem (fun n h1 h2 => hmin n h2 h1)

/-- `n₂ = 4` (source body: "We have $n_2=4$").  `C(4,2) = 6`, `4 ∤ 6`,
`3 ∣ 6`; and `4 = 2·2` is the least admissible `n`. -/
theorem nk_two : nk 2 = 4 := by
  refine nk_eq_of 2 4 (by decide) ?_
  intro n h1 h2
  omega

/-- `n₃ = 6` (source body: "$n_3=6$").  `C(6,3) = 20`, `6 ∤ 20`, `5 ∣ 20`,
`4 ∣ 20`; and `6 = 2·3` is the least admissible `n`. -/
theorem nk_three : nk 3 = 6 := by
  refine nk_eq_of 3 6 (by decide) ?_
  intro n h1 h2
  omega

/-- `n₄ = 9` (source body: "$n_4=9$").  `C(9,4) = 126` has defect `1`, and the
only smaller admissible `n` is `8`, where `C(8,4) = 70` has defect `2`. -/
theorem nk_four : nk 4 = 9 := by
  refine nk_eq_of 4 9 (by decide) ?_
  intro n h1 h2
  interval_cases n
  decide

/-- `n₅ = 12` (source body: "and $n_5=12$").  `C(12,5) = 792` has defect `1`;
the smaller admissible `n` are `10` (`C(10,5) = 252`, defect `2`) and `11`
(`C(11,5) = 462`, defect `3`). -/
theorem nk_five : nk 5 = 12 := by
  refine nk_eq_of 5 12 (by decide) ?_
  intro n h1 h2
  interval_cases n <;> decide

/-- `n₆ = 75` (OEIS A389360, a(6) = 75; first value beyond the source body's
table).  `C(75,6) = 201359550`; the unique exceptional index is `i = 3`
(`72 ∤ C(75,6)`), and no `12 ≤ n < 75` has defect `1`. -/
theorem nk_six : nk 6 = 75 :=
  nk_eq_of_ball 6 75 (by decide) (by decide)

/-- `n₇ = 30` (OEIS A389360, a(7) = 30).  `C(30,7) = 2035800`; the unique
exceptional index is `i = 2` (`28 ∤ C(30,7)`), and no `14 ≤ n < 30` has
defect `1`.  Note `n₇ < n₆`: the sequence is not monotone in `k`. -/
theorem nk_seven : nk 7 = 30 :=
  nk_eq_of_ball 7 30 (by decide) (by decide)

/-- `n₈ = 70` (OEIS A389360, a(8) = 70).  `C(70,8) = 9440350920`; the unique
exceptional index is `i = 6` (`64 ∤ C(70,8)`), and no `16 ≤ n < 70` has
defect `1`. -/
theorem nk_eight : nk 8 = 70 :=
  nk_eq_of_ball 8 70 (by decide) (by decide)

/-- `n₉ = 56` (OEIS A389360, a(9) = 56).  `C(56,9) = 7575968400`; the unique
exceptional index is `i = 2` (`54 ∤ C(56,9)`), and no `18 ≤ n < 56` has
defect `1`. -/
theorem nk_nine : nk 9 = 56 :=
  nk_eq_of_ball 9 56 (by decide) (by decide)

set_option maxRecDepth 40000 in
/-- `n₁₀ = 2403` (OEIS A389360, a(10) = 2403).  `C(2403,10)` is the 28-digit
number `1736325250692362528802510060`; the unique exceptional index is
`i = 3` (`2400 ∤ C(2403,10)`).  The minimality sweep checks all
`20 ≤ n < 2403` in one kernel `decide` (on that range the defect is in fact
always ≥ 2; it is `3` at `n = 2402`, see the example below).  `maxRecDepth`
is raised because the `Nat.choose` and `Nat.decidableBallLT` recursions are
≈ 2403 deep; kernel reduction, not `native_decide`. -/
theorem nk_ten : nk 10 = 2403 :=
  nk_eq_of_ball 10 2403 (by decide) (by decide)

/-! ## Monier's upper bound `n_k ≤ k!` -/

/-- **Monier's identity.**  For `0 < k`, `C(k!, k) = ∏_{j=1}^{k-1} (k! - j)`.

The falling factorial `k!·(k!-1)⋯(k!-k+1)` has leading factor `k!`, which
cancels the entire denominator of `C(k!, k)`. -/
theorem choose_factorial_self_eq (k : ℕ) (hk : 0 < k) :
    (k.factorial).choose k = ∏ j ∈ Finset.Ico 1 k, (k.factorial - j) := by
  have h1 : (k.factorial).descFactorial k = k.factorial * (k.factorial).choose k :=
    Nat.descFactorial_eq_factorial_mul_choose _ _
  have h2 : (k.factorial).descFactorial k = ∏ i ∈ Finset.range k, (k.factorial - i) :=
    Nat.descFactorial_eq_prod_range _ _
  have h3 : ∏ i ∈ Finset.range k, (k.factorial - i)
      = k.factorial * ∏ j ∈ Finset.Ico 1 k, (k.factorial - j) := by
    rw [Finset.range_eq_Ico, Finset.prod_eq_prod_Ico_succ_bot hk]
    simp only [Nat.sub_zero]
  refine Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos k) ?_
  rw [← h1, h2, h3]

/-- Monier's divisibility (source body: "since $\binom{k!}{k}$ is divisible by
$k!-i$ for $1\leq i<k$"). -/
theorem sub_dvd_choose_factorial_self (k j : ℕ) (hj : 1 ≤ j) (hjk : j < k) :
    (k.factorial - j) ∣ (k.factorial).choose k := by
  rw [choose_factorial_self_eq k (by omega)]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_Ico.mpr ⟨hj, hjk⟩)

/-- At `n = k!` every index `1 ≤ i < k` is good, so the defect is at most `1`
(and by `erdos_selfridge_defect_pos` it is exactly `1` for `k ≥ 2`). -/
theorem divisorDefect_factorial_le_one (k : ℕ) :
    divisorDefect (k.factorial) k ≤ 1 := by
  have hsub : (Finset.range k).filter (fun i => ¬ (k.factorial - i) ∣ (k.factorial).choose k)
      ⊆ {0} := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_singleton]
    by_contra hne
    exact hi.2 (sub_dvd_choose_factorial_self k i (by omega) hi.1)
  calc divisorDefect (k.factorial) k
      ≤ ({0} : Finset ℕ).card := Finset.card_le_card hsub
    _ = 1 := rfl

/-- `2k ≤ k!` for `3 ≤ k`, so `k!` is admissible in the `sInf` defining `nk`. -/
theorem two_mul_le_factorial (k : ℕ) (hk : 3 ≤ k) : 2 * k ≤ k.factorial := by
  have hpred : k * (k - 1).factorial = k.factorial := Nat.mul_factorial_pred (by omega)
  have htwo : 2 ≤ (k - 1).factorial := by
    have hle : (2 : ℕ).factorial ≤ (k - 1).factorial := Nat.factorial_le (by omega)
    simpa only [Nat.factorial_two] using hle
  calc 2 * k = k * 2 := by ring
    _ ≤ k * (k - 1).factorial := Nat.mul_le_mul_left k htwo
    _ = k.factorial := hpred

/-- **Monier's bound** (source body: "Monier \cite{Mo85} observed that
$n_k\leq k!$ for $k\geq 3$"): `nk k ≤ k !` for `3 ≤ k`.

As a by-product the defining set of `nk k` is nonempty for every `k ≥ 3`, so
`nk k` is a genuine minimum and not the `sInf ∅ = 0` junk value. -/
theorem nk_le_factorial (k : ℕ) (hk : 3 ≤ k) : nk k ≤ k.factorial := by
  refine Nat.sInf_le ⟨two_mul_le_factorial k hk, ?_⟩
  have hkle : k ≤ k.factorial := Nat.self_le_factorial k
  have hpos := erdos_selfridge_defect_pos (k.factorial) k (by omega) hkle
  have hle := divisorDefect_factorial_le_one k
  omega

/-! ## Satisfiability witnesses

STYLE.md requires exhibiting a concrete joint model of every hypothesis, and
evidence that the conclusions are not degenerate. -/

/-- Joint instantiation of the hypotheses of `erdos_selfridge_defect_pos` and
of `erdos_selfridge_defect_pos_of_two_mul_le` at `(n, k) = (12, 5)`, together
with the exact defect there (so the conclusion `1 ≤ defect` is tight, not
vacuous). -/
example : 2 ≤ 5 ∧ 5 ≤ 12 ∧ 2 * 5 ≤ 12 ∧ divisorDefect 12 5 = 1 := by decide

/-- The conclusion of `erdos_selfridge_defect_pos` is not an equality in
general: at `(n, k) = (14, 6)` the defect is `4`. -/
example : 2 ≤ 6 ∧ 6 ≤ 14 ∧ divisorDefect 14 6 = 4 := by decide

/-- Joint instantiation of the hypotheses of `nk_le_factorial` at `k = 3`,
with the witness `n = 3! = 6` actually lying in the defining set. -/
example : 2 * 3 ≤ Nat.factorial 3 ∧ divisorDefect (Nat.factorial 3) 3 = 1 := by decide

/-- Joint instantiation of the hypotheses of `nk_eq_of` at `k = 4`, `m = 9`. -/
example : 2 * 4 ≤ 9 ∧ divisorDefect 9 4 = 1 ∧ divisorDefect 8 4 ≠ 1 := by decide

/-- Monier's identity is not vacuous: at `k = 4`, `C(24,4) = 10626` and
`23 · 22 · 21 = 10626`. -/
example : (Nat.factorial 4).choose 4 = 23 * 22 * 21 := by decide

/-- The `nk_six` minimality sweep has content at its top end: `n = 74` just
misses, with defect `2` (`C(74,6) = 185250786`). -/
example : divisorDefect 74 6 = 2 := by decide

set_option maxRecDepth 40000 in
/-- The `nk_ten` minimality sweep has content at its top end: `n = 2402` just
misses, with defect `3`.  So the sweep's conclusion `≠ 1` is not the vacuous
half of a degenerate range. -/
example : divisorDefect 2402 10 = 3 := by decide

/-! ## Axiom audit -/

#print axioms erdos_selfridge_defect_pos
#print axioms erdos_selfridge_defect_pos_of_two_mul_le
#print axioms divisorDefect_le_one_iff_eq_one
#print axioms exists_factorization_choose_lt
#print axioms nk_two
#print axioms nk_three
#print axioms nk_four
#print axioms nk_five
#print axioms nk_six
#print axioms nk_seven
#print axioms nk_eight
#print axioms nk_nine
#print axioms nk_ten
#print axioms choose_factorial_self_eq
#print axioms sub_dvd_choose_factorial_self
#print axioms nk_le_factorial

end Erdos1063
