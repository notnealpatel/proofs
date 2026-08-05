/-
  OEIS A046098 — "Numbers n such that central binomial coefficient
  C(n, floor(n/2)) is squarefree" — STATEMENT ARCHIVE with one intended
  `sorry`, plus a sorry-free even-index classification.

  ── SOURCE PIN (verbatim, `goof oeis show A046098`, re-pulled 2026-08-05) ──

    {"id":"A046098",
     "name":"Numbers n such that central binomial coefficient
             C(n, floor(n/2)) is squarefree.",
     "terms":"0,1,2,3,4,5,7,8,11,17,19,23,71",
     "comments":["No other n < 10^8. - _T. D. Noe_, Apr 06 2007"],
     "xrefs":["Cf. A001405.",
              "Cf. A056651 (cubefree central binomial coefficients)."],
     "keywords":"nonn,hard",
     "programs":["Select[Range[0, 100], SquareFreeQ[Binomial[#,Floor[#/2]]]&]
                  (* _Harvey P. Dale_, Mar 11 2011 *)",
                 "(PARI) is(n)=issquarefree(binomial(n,n\\2)) \\\\
                  _Charles R Greathouse IV_, Jul 16 2011"]}

  The entry carries NO finiteness conjecture. Its only strengthening beyond
  the 13 listed terms is Noe's computation: "No other n < 10^8." That is the
  claim archived here, in the honest bounded form

      ∀ n, 72 ≤ n → n < 10^8 → ¬ Squarefree (C(n, ⌊n/2⌋)),

  which is a *finite computational assertion* (Noe 2007), not a theorem with
  a published proof.

  ── LITERATURE PIN (verbatim, `goof erdos fetch 175`, 2026-08-05, from
     https://www.erdosproblems.com/175) ──

    "It is easy to see that $4\mid \binom{2n}{n}$ except when $n=2^k$, and
     hence it suffices to prove this when $n$ is a power of $2$.
     Proved by S\'{a}rk\"{o}zy \cite{Sa85} for all sufficiently large $n$,
     and independently by Granville and Ramar\'{e} \cite{GrRa96} and
     Velammal \cite{Ve95} for all $n\geq 5$."

    "Sander \cite{Sa92b} proved that, for all $0<\epsilon<1$, if $n$ is
     sufficiently large and $\lvert d\rvert\leq n^{1-\epsilon}$ then
     $\binom{2n+d}{n}$ is not squarefree."

    "[GrRa96] Granville, Andrew and Ramar\'{e}, Olivier, *Explicit bounds on
     exponential sums and the scarcity of squarefree binomial
     coefficients*. Mathematika (1996), 73--107."
    "[Sa92b] Sander, J. W., *On prime divisors of binomial coefficients*.
     Bull. London Math. Soc. (1992), 140--142."
    "[Ve95] Velammal, G., *Is the binomial coefficient {$\binom {2n}n$}
     squarefree?*. Hardy-Ramanujan J. (1995), 23--45."

  So A046098 is NOT open in the qualitative sense — it is known to be finite.
  The even indices `n = 2m` are exactly Erdős #175 (Granville–Ramaré /
  Velammal, every `m ≥ 5`; see `Proofs/Erdos/Erdos175/NotSquarefree.lean`),
  and the odd indices `n = 2k+1` are the `d = 1` case of Sander [Sa92b].
  But the odd half is stated on the problem page only for "$n$ sufficiently
  large", with no threshold given there, so nothing in the cited literature
  certifies the range `[72, 10^8)`. That range is precisely Noe's
  computation, and precisely the `sorry` below.

  Note that the odd case does NOT follow from the even case: with `n = 2k+1`
  one has `C(n, ⌊n/2⌋) = centralBinom (k+1) / 2`, and halving can *destroy*
  the square. Concretely `centralBinom 12 = C(24,12) = 2²·7·13·17·19·23` is
  not squarefree, yet `C(23,11) = 2·7·13·17·19·23` is — which is why `23` is
  a term of A046098.

  `n / 2` below is `Nat` division, which is exactly OEIS's `floor(n/2)`; the
  binomial `Nat.choose n (n / 2)` is A001405 (the xref above).

  ── WHAT IS PROVED HERE, SORRY-FREE ──

  * `choose_half_eq_centralBinom_of_even` — for even `n`,
      `C(n, n/2) = Nat.centralBinom (n/2)`.
  * `squarefree_choose_half_iff_of_even` — **full classification at even
      indices** up to `2^31`: for even `n ≤ 2^31`,
      `Squarefree (C(n, n/2)) ↔ n ∈ {0, 2, 4, 8}`. These are exactly the
      even terms of A046098 (`0,2,4,8 = 2·{0,1,2,4}`), so the even half of
      Noe's range is fully discharged, and then some (`2^31 > 2·10^9`).
  * `not_squarefree_choose_half_of_even` — the even half of the archived
      claim, `72 ≤ n < 10^8`.
  * `two_mul_choose_half_of_odd`, `padicValNat_two_choose_half_of_odd` — the
      odd bridge: for odd `n`, `2·C(n, n/2) = centralBinom ((n+1)/2)`, hence
      `v₂(C(n, n/2)) = s₂((n+1)/2) − 1` with `s₂` the binary digit sum.
  * `not_squarefree_choose_half_of_odd_of_three_le_sum_digits` — consequently
      every odd `n` with `3 ≤ s₂((n+1)/2)` has `4 ∣ C(n, n/2)`; unbounded `n`.
  * `terms_squarefree` — all 13 OEIS terms really are terms: each
      `C(n, ⌊n/2⌋)` is exhibited as a product of distinct primes. In
      particular `C(71,35) = 221256270138418389602 = 2·7·13·19·23·37·41·43
      ·47·53·59·61·67·71` is squarefree, so the archived threshold `72` is
      *tight* — it is not an off-by-one.

  ── THE ONE INTENDED `sorry` ──

  `not_squarefree_choose_half_of_odd_of_sum_digits_le_two`: odd `n` in
  `[72, 10^8)` whose half-successor `m = n/2 + 1` has binary digit sum `≤ 2`.
  Everything else in the archived range is discharged above. Implementation
  note for whoever closes it: there are exactly **331** such `m` in
  `[37, 5·10^7]` (they are the `2^a` and `2^a + 2^b`), and for each one the
  Kummer carry certificate of `Erdos175.two_le_padicValNat_centralBinom`,

      s_p(2m) + 2(p−1) ≤ 2·s_p(m)  ⟹  v_p(centralBinom m) ≥ 2,

  holds at a witness prime `p ≤ 7` — and `v_p` is unchanged by the halving
  for odd `p`. Witness distribution (computed with Python/sympy, see the
  disclosure below): `p = 3` for 312 of the 331; `p = 5` for
  `m ∈ {64, 66, 192, 264, 513, 514, 516, 576, 768, 2304, 65664, 532480}`;
  `p = 7` for `m ∈ {40, 256, 272, 1026, 1056, 16392, 81920}`. Turning that
  into Lean needs (i) `s₂(m) ≤ 2 ↔ m = 2^a ∨ m = 2^a + 2^b` and (ii) a
  331-entry certificate table; base-`p` digit sums of numbers up to `10^8`
  are behind `Nat.digits`' well-founded recursion, so the table would need
  `native_decide` or a fuel-indexed digit-sum surrogate. Out of scope here.

  ── AXIOM / TRUST DISCLOSURE ──

  No `native_decide`, `axiom`, `@[implemented_by]`, `@[extern]`, or `@[csimp]`
  is written in this file. The even-side results *inherit* one documented
  `native_decide` from `Erdos175.witness_cert` in `NotSquarefree.lean` (digit
  sums of `2^k, 2^(k+1) ≤ 2^31` in bases 3, 5, 7), because they are proved
  through `Erdos175.squarefree_centralBinom_iff` /
  `Erdos175.not_squarefree_centralBinom`. The odd-side 2-adic results
  (`two_mul_choose_half_of_odd`, `padicValNat_two_choose_half_of_odd`,
  `not_squarefree_choose_half_of_odd_of_three_le_sum_digits`) and the
  arithmetic sanity layer (`squarefree_list_prod`, `terms_squarefree`) use
  only `propext, Classical.choice, Quot.sound`. See the `#print axioms`
  block at the end of the file for the exact per-declaration report.

  Computational disclosure: `sage` is NOT installed in this environment
  (`command -v sage` empty), so all pre-proof computation — the term list,
  the factorizations pinned in `terms_squarefree`, the 331-value reduction
  and its witness primes — was done with `python3` + `sympy` 1.14.0. None of
  it enters any proof.
-/

import Erdos.Erdos175.NotSquarefree
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum.Prime

namespace Erdos175.A046098

-- ════════════════════════════════════════════════════════════════════
-- §1 THE HALVING IDENTITY C(2k+1, k) = centralBinom (k+1) / 2
-- ════════════════════════════════════════════════════════════════════

/-- `centralBinom (k+1) = C(2k+2, k+1) = 2·C(2k+1, k)`: Pascal plus the
    symmetry `C(2k+1, k+1) = C(2k+1, k)`. This is the identity behind
    Mathlib's `Nat.two_dvd_centralBinom_succ`, made explicit. -/
theorem centralBinom_succ_eq_two_mul_choose (k : ℕ) :
    Nat.centralBinom (k + 1) = 2 * ((2 * k + 1).choose k) := by
  have hk : (2 * k + 1).choose k = (k + 1 + k).choose k := by
    rw [show k + 1 + k = 2 * k + 1 by ring]
  rw [hk, Nat.centralBinom_eq_two_mul_choose,
    show 2 * (k + 1) = (k + 1 + k) + 1 by ring,
    Nat.choose_succ_succ' (k + 1 + k) k, Nat.choose_symm_add, ← two_mul]

-- ════════════════════════════════════════════════════════════════════
-- §2 EVEN INDICES: A046098 IS `Erdos175.squarefree_centralBinom_iff`
-- ════════════════════════════════════════════════════════════════════

/-- At an even index the A046098 binomial *is* the central binomial
    coefficient: `C(2k, k) = centralBinom k`. (`n / 2` is `Nat` division,
    i.e. OEIS's `floor(n/2)`.) -/
theorem choose_half_eq_centralBinom_of_even {n : ℕ} (hn : Even n) :
    n.choose (n / 2) = Nat.centralBinom (n / 2) := by
  obtain ⟨k, rfl⟩ := hn
  rw [show k + k = 2 * k by ring, Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]
  rfl

/-- **Even-index classification, sorry-free.** For every even `n ≤ 2^31`,
    the A046098 binomial `C(n, ⌊n/2⌋)` is squarefree exactly for
    `n ∈ {0, 2, 4, 8}` — precisely the even terms listed by OEIS
    (`{0,2,4,8} = 2·{0,1,2,4}`). Transported from
    `Erdos175.squarefree_centralBinom_iff`, whose range `n/2 ≤ 2^30`
    corresponds to `n ≤ 2^31 > 2·10^9`, comfortably past Noe's `10^8`. -/
theorem squarefree_choose_half_iff_of_even {n : ℕ} (hn : Even n)
    (hle : n ≤ 2 ^ 31) :
    Squarefree (n.choose (n / 2)) ↔ n = 0 ∨ n = 2 ∨ n = 4 ∨ n = 8 := by
  have hhalf : n / 2 ≤ 2 ^ 30 := by
    have h31 : (2 : ℕ) ^ 31 = 2147483648 := by norm_num
    have h30 : (2 : ℕ) ^ 30 = 1073741824 := by norm_num
    omega
  rw [choose_half_eq_centralBinom_of_even hn,
    Erdos175.squarefree_centralBinom_iff hhalf]
  obtain ⟨k, rfl⟩ := hn
  omega

/-- **Even half of Noe's claim, sorry-free.** No even `n` with
    `72 ≤ n < 10^8` has squarefree `C(n, ⌊n/2⌋)`. -/
theorem not_squarefree_choose_half_of_even {n : ℕ} (hn : Even n)
    (h72 : 72 ≤ n) (hlt : n < 10 ^ 8) : ¬ Squarefree (n.choose (n / 2)) := by
  rw [choose_half_eq_centralBinom_of_even hn]
  refine Erdos175.not_squarefree_centralBinom (by omega) ?_
  have h30 : (2 : ℕ) ^ 30 = 1073741824 := by norm_num
  have he : (10 : ℕ) ^ 8 = 100000000 := by norm_num
  omega

-- ════════════════════════════════════════════════════════════════════
-- §3 ODD INDICES: THE 2-ADIC VALUATION IS s₂((n+1)/2) − 1
-- ════════════════════════════════════════════════════════════════════

/-- At an odd index the A046098 binomial is half a central binomial
    coefficient: for odd `n`, `2·C(n, ⌊n/2⌋) = centralBinom (⌊n/2⌋ + 1)`.
    (With `n = 2k+1` this reads `2·C(2k+1, k) = C(2k+2, k+1)`.) -/
theorem two_mul_choose_half_of_odd {n : ℕ} (hn : Odd n) :
    2 * (n.choose (n / 2)) = Nat.centralBinom (n / 2 + 1) := by
  obtain ⟨k, rfl⟩ := hn
  have hd : (2 * k + 1) / 2 = k := by omega
  rw [hd, centralBinom_succ_eq_two_mul_choose k]

/-- **Kummer at `p = 2`, odd index.** For odd `n`, the `2`-adic valuation of
    `C(n, ⌊n/2⌋)` is `s₂(⌊n/2⌋ + 1) − 1`, where `s₂` is the binary digit sum
    and `⌊n/2⌋ + 1 = (n+1)/2`. Stated additively to keep `Nat` subtraction
    out of the claim. Combines `Erdos175.padicValNat_two_centralBinom`
    (`v₂(centralBinom m) = s₂(m)`) with the halving identity. -/
theorem padicValNat_two_choose_half_of_odd {n : ℕ} (hn : Odd n) :
    padicValNat 2 (n.choose (n / 2)) + 1 = (Nat.digits 2 (n / 2 + 1)).sum := by
  have hne : n.choose (n / 2) ≠ 0 := (Nat.choose_pos (Nat.div_le_self n 2)).ne'
  have hval := Erdos175.padicValNat_two_centralBinom (n / 2 + 1)
  rw [← two_mul_choose_half_of_odd hn, padicValNat.mul (by norm_num) hne,
    padicValNat.self (by norm_num)] at hval
  omega

/-- **Odd indices with three or more binary ones, sorry-free, unbounded.**
    If `n` is odd and the binary digit sum of `(n+1)/2` is at least `3`, then
    `4 ∣ C(n, ⌊n/2⌋)`, so `n` is not a term of A046098. This is the odd
    analogue of `Erdos175.not_squarefree_centralBinom_of_not_two_pow` and it
    cuts the odd part of Noe's range down to the `331` values recorded in the
    file header. (Example: `n = 13`, `(n+1)/2 = 7 = 111₂`, and indeed
    `C(13,6) = 1716 = 2²·3·11·13`.) -/
theorem not_squarefree_choose_half_of_odd_of_three_le_sum_digits {n : ℕ}
    (hn : Odd n) (hs : 3 ≤ (Nat.digits 2 (n / 2 + 1)).sum) :
    ¬ Squarefree (n.choose (n / 2)) := by
  refine Erdos175.not_squarefree_of_two_le_padicValNat Nat.prime_two ?_
  have hval := padicValNat_two_choose_half_of_odd hn
  omega

-- ════════════════════════════════════════════════════════════════════
-- §4 THE ARCHIVED CLAIM (ONE INTENDED `sorry`)
-- ════════════════════════════════════════════════════════════════════

/-- Joint satisfiability of the hypotheses of the archived statement below:
    `n = 79` is odd, lies in `[72, 10^8)`, and has
    `s₂(79/2 + 1) = s₂(40) = s₂(101000₂) = 2 ≤ 2`. So the archived theorem is
    not vacuous. (`79` is in fact the *smallest* such `n`; its witness prime
    is `7`, per the header table.) -/
example : Odd 79 ∧ 72 ≤ 79 ∧ 79 < 10 ^ 8 ∧ (Nat.digits 2 (79 / 2 + 1)).sum ≤ 2 :=
  ⟨⟨39, by norm_num⟩, by norm_num, by norm_num, by decide⟩

/-- **ARCHIVED — the one intended `sorry` of this file.** T. D. Noe's
    computation ("No other n < 10^8", A046098, Apr 06 2007), restricted to
    the part not already discharged in §2–§3: odd `n` with `72 ≤ n < 10^8`
    whose half-successor `m = ⌊n/2⌋ + 1` has binary digit sum at most `2`
    (equivalently `m = 2^a` or `m = 2^a + 2^b`). There are exactly `331`
    such `m` in `[37, 5·10^7]`, each certified by a Kummer carry witness
    prime `p ∈ {3, 5, 7}`; see the file header for the full reduction and
    the exceptional lists. Not a theorem with a published proof — a finite
    computer verification. -/
theorem not_squarefree_choose_half_of_odd_of_sum_digits_le_two {n : ℕ}
    (hn : Odd n) (h72 : 72 ≤ n) (hlt : n < 10 ^ 8)
    (hs : (Nat.digits 2 (n / 2 + 1)).sum ≤ 2) :
    ¬ Squarefree (n.choose (n / 2)) := by
  sorry

/-- Odd half of Noe's claim: no odd `n` with `72 ≤ n < 10^8` has squarefree
    `C(n, ⌊n/2⌋)`. Splits on the binary digit sum of `(n+1)/2`: at least `3`
    is §3 (sorry-free, unbounded), at most `2` is the archived residue. -/
theorem not_squarefree_choose_half_of_odd {n : ℕ} (hn : Odd n) (h72 : 72 ≤ n)
    (hlt : n < 10 ^ 8) : ¬ Squarefree (n.choose (n / 2)) := by
  rcases Nat.lt_or_ge (Nat.digits 2 (n / 2 + 1)).sum 3 with hs | hs
  · exact not_squarefree_choose_half_of_odd_of_sum_digits_le_two hn h72 hlt
      (by omega)
  · exact not_squarefree_choose_half_of_odd_of_three_le_sum_digits hn hs

/-- **ARCHIVED STATEMENT (restriction of A046098's Noe comment to n ≥ 72).**
    T. D. Noe (Apr 06 2007): "No other n < 10^8." Noe's full claim covers all
    `n < 10^8` not in the 13-term list; this theorem captures only the `72 ≤ n`
    portion. Ten odd values below 72 with `s₂((n+1)/2) ≤ 2` (n ∈ {9, 15, 31,
    33, 35, 39, 47, 63, 65, 67}) fall outside both §3's `s₂ ≥ 3` guard and
    this theorem's `72 ≤ n` guard — they are non-squarefree (verified
    computationally) but not formalized here. The even half
    and the odd `s₂ ≥ 3` half are proved above; the remaining `331` odd
    values sit behind
    `not_squarefree_choose_half_of_odd_of_sum_digits_le_two`.

    Not implied by the literature: Granville–Ramaré/Velammal cover the even
    indices for all `m ≥ 5`, and Sander [Sa92b] covers the odd indices only
    for "sufficiently large" `n` with no threshold given on the Erdős #175
    page. See the file header for the verbatim pins. -/
theorem noe_not_squarefree_choose_half {n : ℕ} (h72 : 72 ≤ n)
    (hlt : n < 10 ^ 8) : ¬ Squarefree (n.choose (n / 2)) := by
  rcases Nat.even_or_odd n with hp | hp
  · exact not_squarefree_choose_half_of_even hp h72 hlt
  · exact not_squarefree_choose_half_of_odd hp h72 hlt

-- ════════════════════════════════════════════════════════════════════
-- §5 SANITY LAYER: THE 13 LISTED TERMS ARE GENUINE, AND `72` IS TIGHT
-- ════════════════════════════════════════════════════════════════════

/-- A product of a duplicate-free list of primes is squarefree. -/
theorem squarefree_list_prod {l : List ℕ} (hp : ∀ p ∈ l, Nat.Prime p)
    (hnd : l.Nodup) : Squarefree l.prod := by
  induction l with
  | nil => simp
  | cons p t ih =>
    have hpp : Nat.Prime p := hp p List.mem_cons_self
    have hpt : ∀ q ∈ t, Nat.Prime q := fun q hq => hp q (List.mem_cons_of_mem p hq)
    have hnd' : t.Nodup := (List.nodup_cons.mp hnd).2
    have hnm : p ∉ t := (List.nodup_cons.mp hnd).1
    have hcop : Nat.Coprime p t.prod := by
      rw [Nat.Prime.coprime_iff_not_dvd hpp]
      intro hdvd
      obtain ⟨q, hq, hpq⟩ := (Nat.Prime.prime hpp).dvd_prod_iff.mp hdvd
      exact hnm (((Nat.prime_dvd_prime_iff_eq hpp (hpt q hq)).mp hpq) ▸ hq)
    rw [List.prod_cons, Nat.squarefree_mul_iff]
    exact ⟨hcop, hpp.prime.squarefree, ih hpt hnd'⟩

/-- Squarefreeness certificate: exhibit `m` as a product of distinct primes. -/
theorem squarefree_of_eq_list_prod {m : ℕ} {l : List ℕ} (h : m = l.prod)
    (hp : ∀ p ∈ l, Nat.Prime p) (hnd : l.Nodup) : Squarefree m :=
  h ▸ squarefree_list_prod hp hnd

/-- **The 13 OEIS terms are genuine.** For each `n` in A046098's `terms`
    field, `C(n, ⌊n/2⌋)` is squarefree — certified by an explicit
    factorization into distinct primes (binomials evaluated through
    `Nat.choose_eq_descFactorial_div_factorial`, which the kernel can reduce,
    unlike the Pascal recursion). Factorizations, in order:
    `1, 1, 2, 3, 2·3, 2·5, 5·7, 2·5·7, 2·3·7·11, 2·5·11·13·17,
    2·11·13·17·19, 2·7·13·17·19·23,
    2·7·13·19·23·37·41·43·47·53·59·61·67·71`. -/
theorem terms_squarefree :
    ∀ n ∈ ([0, 1, 2, 3, 4, 5, 7, 8, 11, 17, 19, 23, 71] : List ℕ),
      Squarefree (n.choose (n / 2)) := by
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact squarefree_of_eq_list_prod (l := []) rfl (by simp) (by decide)
  · exact squarefree_of_eq_list_prod (l := []) rfl (by simp) (by decide)
  · exact squarefree_of_eq_list_prod (l := [2]) rfl (by norm_num) (by decide)
  · exact squarefree_of_eq_list_prod (l := [3]) rfl (by norm_num) (by decide)
  · exact squarefree_of_eq_list_prod (l := [2, 3]) rfl (by norm_num) (by decide)
  · exact squarefree_of_eq_list_prod (l := [2, 5]) rfl (by norm_num) (by decide)
  · exact squarefree_of_eq_list_prod (l := [5, 7]) rfl (by norm_num) (by decide)
  · exact squarefree_of_eq_list_prod (l := [2, 5, 7]) rfl (by norm_num) (by decide)
  · exact squarefree_of_eq_list_prod (l := [2, 3, 7, 11]) rfl (by norm_num)
      (by decide)
  · exact squarefree_of_eq_list_prod (l := [2, 5, 11, 13, 17])
      (by rw [Nat.choose_eq_descFactorial_div_factorial]
          norm_num [Nat.descFactorial, Nat.factorial]) (by norm_num) (by decide)
  · exact squarefree_of_eq_list_prod (l := [2, 11, 13, 17, 19])
      (by rw [Nat.choose_eq_descFactorial_div_factorial]
          norm_num [Nat.descFactorial, Nat.factorial]) (by norm_num) (by decide)
  · exact squarefree_of_eq_list_prod (l := [2, 7, 13, 17, 19, 23])
      (by rw [Nat.choose_eq_descFactorial_div_factorial]
          norm_num [Nat.descFactorial, Nat.factorial]) (by norm_num) (by decide)
  · exact squarefree_of_eq_list_prod
      (l := [2, 7, 13, 19, 23, 37, 41, 43, 47, 53, 59, 61, 67, 71])
      (by rw [Nat.choose_eq_descFactorial_div_factorial]
          norm_num [Nat.descFactorial, Nat.factorial]) (by norm_num) (by decide)

/-- **The threshold `72` is tight.** `C(71, 35)` is squarefree (so `71` is a
    term, matching OEIS's last listed value) while `C(72, 36)` is not (so the
    archived range starts exactly where it should). Both halves are
    sorry-free; the second inherits `witness_cert`'s `native_decide`. -/
theorem squarefree_choose_71_and_not_choose_72 :
    Squarefree (Nat.choose 71 35) ∧ ¬ Squarefree (Nat.choose 72 36) :=
  ⟨terms_squarefree 71 (by simp),
    not_squarefree_choose_half_of_even (n := 72) ⟨36, by norm_num⟩ (by norm_num)
      (by norm_num)⟩

/-- Ground-truth check for `not_squarefree_choose_half_of_odd_of_three_le_sum_digits`
    at a concrete odd index inside the archived range: `n = 73` has
    `(73+1)/2 = 37 = 100101₂`, binary digit sum `3`, so `4 ∣ C(73, 36)`. -/
example : ¬ Squarefree (Nat.choose 73 36) :=
  not_squarefree_choose_half_of_odd_of_three_le_sum_digits (n := 73)
    ⟨36, by norm_num⟩ (by decide)

/-- Ground-truth check for `padicValNat_two_choose_half_of_odd`: at `n = 13`,
    `(13+1)/2 = 7 = 111₂` has binary digit sum `3`, and indeed
    `C(13, 6) = 1716 = 2²·3·11·13` has `v₂ = 2`. -/
example : padicValNat 2 (Nat.choose 13 6) = 2 := by
  have h := padicValNat_two_choose_half_of_odd (n := 13) ⟨6, by norm_num⟩
  norm_num at h
  omega

/-- Ground-truth check for `choose_half_eq_centralBinom_of_even` and the even
    classification: `C(8, 4) = centralBinom 4 = 70 = 2·5·7` is squarefree, so
    `8` is a term; `C(6, 3) = centralBinom 3 = 20 = 2²·5` is not. -/
example : Squarefree (Nat.choose 8 4) ∧ ¬ Squarefree (Nat.choose 6 3) :=
  ⟨(squarefree_choose_half_iff_of_even (n := 8) ⟨4, by norm_num⟩
      (by norm_num)).mpr (by norm_num),
    fun h => by
      have := (squarefree_choose_half_iff_of_even (n := 6) ⟨3, by norm_num⟩
        (by norm_num)).mp (by simpa using h)
      omega⟩

end Erdos175.A046098

-- ════════════════════════════════════════════════════════════════════
-- §6 AXIOM REPORT
-- ════════════════════════════════════════════════════════════════════

-- Sorry-free, and free of the inherited `native_decide`:
#print axioms Erdos175.A046098.centralBinom_succ_eq_two_mul_choose
#print axioms Erdos175.A046098.choose_half_eq_centralBinom_of_even
#print axioms Erdos175.A046098.two_mul_choose_half_of_odd
#print axioms Erdos175.A046098.padicValNat_two_choose_half_of_odd
#print axioms Erdos175.A046098.not_squarefree_choose_half_of_odd_of_three_le_sum_digits
#print axioms Erdos175.A046098.squarefree_list_prod
#print axioms Erdos175.A046098.squarefree_of_eq_list_prod
#print axioms Erdos175.A046098.terms_squarefree

-- Sorry-free, but inheriting `Erdos175.witness_cert`'s single `native_decide`:
#print axioms Erdos175.A046098.squarefree_choose_half_iff_of_even
#print axioms Erdos175.A046098.not_squarefree_choose_half_of_even
#print axioms Erdos175.A046098.squarefree_choose_71_and_not_choose_72

-- Carrying the one intended `sorry` (archived, not proved);
-- `noe_not_squarefree_choose_half` additionally inherits the native_decide
-- from the even branch:
#print axioms Erdos175.A046098.not_squarefree_choose_half_of_odd_of_sum_digits_le_two
#print axioms Erdos175.A046098.not_squarefree_choose_half_of_odd
#print axioms Erdos175.A046098.noe_not_squarefree_choose_half
