import Enumerative.PowerOfTwoDigits
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Erdős #406, the counting bound: the sieve has exactly `2 ^ j` classes, so `N(x) ≤ 2 x^{log₃ 2}`

## Source

The problem statement, its references ([Na80], [La09], …), and the OEIS cross-references
are pinned **verbatim in the parent file** `Enumerative.PowerOfTwoDigits` (module
docstring there, pulled with `goof erdos fetch 406` on 2026-08-05); they are cited here,
not re-pinned. The two source sentences this file is about:

> Let $N(x)$ count the number of $n\leq x$ such that $2^n$ has only the digits $0$ and $1$
> in base $3$. Narkiewicz \cite{Na80} proved\[N(x)\leq 1.62 x^{\log_32}\]

and, from the parent's own docstring, the sieve density observation: at depth `j` the
number of surviving residues is exactly `2 ^ j` against period `2 · 3 ^ (j-1)`.

### The exact bound formalised here is [La09], Theorem 1.4 at `λ = 1`

Lagarias, *Ternary expansions of powers of 2* (J. Lond. Math. Soc. 2009) — the [La09]
reference pinned in the parent — proves (paper fetched locally at
`References/arXiv-math-0512006/paper.tex`, lines ≈528–548):

> **Theorem 1.4.** For each nonzero $\lambda \in \mathbb{Z}_3$, the $3$-adic integers, and
> each $X \ge 2$,
> $\tilde{N}_{\lambda}(X) := \#\{n \le X : (\lambda 2^n)_3 \in \mathbb{Z}_3
> \text{ omits the digit } 2\} \le 2X^{\alpha_0}$, with
> $\alpha_0 = \log_3 2 \approx 0.63092$.

introduced by (ibid., lines ≈528–531):

> Our first observation is an upper bound on the number of solutions valid for all nonzero
> $\lambda \in \mathbb{Z}_3$, which extends the result of Narkiewicz [Na80] for
> $\lambda = 1$, using essentially the same proof.

So the theorem `card_erdos406_filter_le_rpow` below **is the `λ = 1` case of [La09]
Theorem 1.4** — same constant `2`, same exponent `log₃ 2` — not merely an ad-hoc
weakening of Narkiewicz's `1.62`. Terminology: Lagarias calls the surviving congruence
classes of the sieve *admissible* congruence classes (ibid., line ≈2266); the Finset
`sieveClasses` below is the exponent-side (`n mod 2·3^j`) avatar of that notion.

## What is proved

Everything in this file is `sorry`-free and kernel-checked.

* **The crux** (`two_pow_two_mul_three_pow`): `2 ^ (2·3^j) = 1 + c·3^(j+1)` with `3 ∤ c` —
  a lifting-the-exponent fact proved by a self-contained induction. Consequently the
  multiplicative order of `2` modulo `3 ^ (j+1)` divides (in fact equals, though only the
  divisibility is needed or stated) `2 · 3 ^ j`, which is the sieve period.
* **The truncated sieve** `SieveAt D n` ("the low `D` base-3 digits of `2 ^ n` are all
  `≤ 1`"), decidable, monotone in `D`, and periodic: `SieveAt (j+1) n` depends only on
  `n % (2 · 3 ^ j)` (`sieveAt_mod_period`).
* **The survivor classes** `sieveClasses j ⊆ range (2 · 3 ^ j)` with ground truths
  `{0}`, `{0, 2}`, `{0, 2, 6, 8}`, `{0, 2, 8, 18, 20, 24, 26, 42}` at `j = 0, 1, 2, 3` —
  matching the parent's `mod_six`/`mod_eighteen`/`mod_fiftyFour` survivor lists exactly.
* **The exact count** (`card_sieveClasses`): `(sieveClasses j).card = 2 ^ j`, via the
  doubling theorem `card_sieveClasses_succ`: of the three lifts `s, s + P, s + 2P`
  (`P = 2·3^j`) of a surviving class `s`, **exactly two** survive at depth `j + 2` —
  because the new digit takes the three values `q, q+u, q+2u (mod 3)` with `3 ∤ u`, which
  are `{0, 1, 2}` in some order, and exactly one of those is the forbidden digit `2`.
* **The counting bounds**: `card_erdos406_filter_le` (window form, pure ℕ:
  solutions below `N` number at most `2^j · (N/(2·3^j) + 1)` for every depth `j`),
  `card_erdos406_filter_le_log` (optimised depth `j = Nat.log 3 N`, bound `2 · 2^{log₃ N}`),
  and `card_erdos406_filter_le_rpow` (the real form `≤ 2 · N^{log₃ 2}` — [La09] Thm 1.4 at
  `λ = 1`).

### A terminology warning on "`2 ^ j` survivors"

The parent docstring counts "`2 ^ j` surviving residues at depth `j`": residues of the
*value* `2 ^ n mod 3 ^ j`, i.e. the `{0,1}`-digit strings of length `j` — all of them,
whether or not a power of `2` ever hits them. This file counts surviving *exponent*
classes `n mod 2·3^j`, at digit-depth `j + 1` (modulus `3 ^ (j+1)`, period `2 · 3 ^ j`),
and proves there are exactly `2 ^ j` of those. The numbers coincide only through this
shift of depth by one — at equal depth the string count (`2 ^ (j+1)` strings at depth
`j + 1`) is twice the class count proved here — so the two notions must not be conflated.
Every statement in this file is about exponent classes:
`sieveClasses j ⊆ Finset.range (2 · 3 ^ j)`, filtered by `SieveAt (j + 1)`.

## What is NOT proved (honest claim boundary)

* Narkiewicz's sharper constant `1.62` [Na80] is **not** formalised — only the constant
  `2` of [La09] Thm 1.4. The exponent `log₃ 2` is the same, and `card_sieveClasses` shows
  it is *exactly* the exponent this sieve produces: the survivor count is `2 ^ j` against
  period `2 · 3 ^ j`, not `O(2^{(1-ε)j})` — so no refinement of this sieve can lower the
  exponent, only the constant.
* Nothing here is progress on Erdős #406 itself. Bounding the *counting function* of
  `erdos406Set` says nothing about its *finiteness*: the bound `2 N^{0.631}` is unbounded
  in `N`. The parent's `Conjecture` remains exactly as open as before.
* Boundary convention: [La09] counts `n ≤ X` for real `X ≥ 2`; here `Finset.range N`
  counts `n < N` for `N : ℕ` (with `1 ≤ N` for the rpow form). Every bound below is
  stated in the `range N` convention and no claim is made in the other one.
-/

set_option autoImplicit false
set_option exponentiation.threshold 2000

namespace Erdos406

/-! ## §1 The crux: `2 ^ (2·3^j) = 1 + c·3^(j+1)` with `3 ∤ c`

Lifting-the-exponent by hand. The base case is `2 ^ 2 = 1 + 1·3`; cubing
`x = 1 + c·3^(j+1)` gives `x³ = 1 + c'·3^(j+2)` with `c' = c + 3c²·3^j + 3c³·(3^j)² ≡ c
(mod 3)`. -/

/-- **The crux.** `2 ^ (2 · 3 ^ j) = 1 + c · 3 ^ (j+1)` for some `c` with `3 ∤ c`. In
other words `2 ^ (2·3^j) ≡ 1 (mod 3^(j+1))` but `≢ 1 (mod 3^(j+2))`: the period of the
depth-`(j+1)` sieve is exactly `2 · 3 ^ j` (only the "period divides" direction is used
below, but `3 ∤ c` is load-bearing in `card_fiber_sieveClasses_succ`). -/
theorem two_pow_two_mul_three_pow (j : ℕ) :
    ∃ c : ℕ, 2 ^ (2 * 3 ^ j) = 1 + c * 3 ^ (j + 1) ∧ ¬ 3 ∣ c := by
  induction j with
  | zero => exact ⟨1, by norm_num, by norm_num⟩
  | succ j ih =>
    obtain ⟨c, hc, hc3⟩ := ih
    refine ⟨c + 3 * c ^ 2 * 3 ^ j + 3 * c ^ 3 * (3 ^ j * 3 ^ j), ?_, ?_⟩
    · have hstep : 2 * 3 ^ (j + 1) = 2 * 3 ^ j * 3 := by ring
      rw [hstep, pow_mul, hc]
      simp only [pow_succ]
      ring
    · intro hdvd
      refine hc3 ?_
      obtain ⟨a, ha⟩ : ∃ a, c + 3 * c ^ 2 * 3 ^ j + 3 * c ^ 3 * (3 ^ j * 3 ^ j) = c + 3 * a :=
        ⟨c ^ 2 * 3 ^ j + c ^ 3 * (3 ^ j * 3 ^ j), by ring⟩
      rw [ha] at hdvd
      omega

/-- The corollary in the form `two_pow_mod_eq_of_pow_mod_one` (parent, §6) consumes:
`2 ^ (2·3^j) % 3^(j+1) = 1 % 3^(j+1)`. -/
theorem two_pow_two_mul_three_pow_mod (j : ℕ) :
    2 ^ (2 * 3 ^ j) % 3 ^ (j + 1) = 1 % 3 ^ (j + 1) := by
  obtain ⟨c, hc, -⟩ := two_pow_two_mul_three_pow j
  rw [hc, Nat.add_mul_mod_self_right]

/-! ## §2 The truncated sieve predicate -/

/-- `SieveAt D n`: the low `D` base-3 digits of `2 ^ n` are all `≤ 1`. This is the
depth-`D` truncation of the parent's `Base3ZeroOne (2 ^ n)` (see
`base3ZeroOne_two_pow_iff_forall_sieveAt`), spelled positionally as in
`base3ZeroOne_iff_forall_index` so that it is a *bounded* — hence decidable —
quantification. At `D = 0` it is vacuously true; every use below has `D = j + 1`, which
is positive. -/
def SieveAt (D n : ℕ) : Prop := ∀ i < D, 2 ^ n / 3 ^ i % 3 ≤ 1

/-- `SieveAt D n` is a bounded quantification (`∀ i < D`) over decidable digit
comparisons, hence decidable. This instance is what lets `sieveClasses` be a
`Finset.filter` and the ground truths `sieveClasses_zero` … `sieveClasses_three` (and the
§7 window counts) be checked by `decide` in the kernel. -/
instance (D n : ℕ) : Decidable (SieveAt D n) := by
  unfold SieveAt; infer_instance

/-- `SieveAt` really is the truncation of the parent's predicate: all base-3 digits of
`2 ^ n` are `≤ 1` iff every truncated sieve passes. -/
theorem base3ZeroOne_two_pow_iff_forall_sieveAt (n : ℕ) :
    Base3ZeroOne (2 ^ n) ↔ ∀ D, SieveAt D n := by
  rw [base3ZeroOne_iff_forall_index]
  constructor
  · intro h D i _
    exact h i
  · intro h i
    exact h (i + 1) i (Nat.lt_succ_self i)

/-- Solutions pass every truncated sieve. -/
theorem sieveAt_of_base3ZeroOne {n : ℕ} (h : Base3ZeroOne (2 ^ n)) (D : ℕ) :
    SieveAt D n :=
  (base3ZeroOne_two_pow_iff_forall_sieveAt n).mp h D

/-- Truncation: a deeper sieve pass restricts to a shallower one. -/
theorem sieveAt_of_le {D' D n : ℕ} (hD : D' ≤ D) (h : SieveAt D n) : SieveAt D' n :=
  fun i hi => h i (lt_of_lt_of_le hi hD)

/-! ## §3 Digits below `D` only see the value mod `3 ^ D`, so the sieve is periodic -/

/-- Digits at positions `i < D` only depend on the value modulo `3 ^ D`. This is the
parent's `div_pow_mod_eq_mod_pow_div` + `Nat.mod_mod_of_dvd` pattern (from the proof of
`base3ZeroOne_mod_pow`), packaged as a congruence. -/
theorem digit_eq_digit_of_mod_pow_eq {m m' : ℕ} (D : ℕ) (h : m % 3 ^ D = m' % 3 ^ D)
    {i : ℕ} (hi : i < D) : m / 3 ^ i % 3 = m' / 3 ^ i % 3 := by
  have hdvd : (3 : ℕ) ^ (i + 1) ∣ 3 ^ D := pow_dvd_pow 3 (by omega)
  rw [div_pow_mod_eq_mod_pow_div, div_pow_mod_eq_mod_pow_div,
    ← Nat.mod_mod_of_dvd m hdvd, h, Nat.mod_mod_of_dvd m' hdvd]

/-- The depth-`D` sieve cannot distinguish exponents whose powers agree mod `3 ^ D`. -/
theorem sieveAt_iff_of_two_pow_mod_eq {D a b : ℕ} (h : 2 ^ a % 3 ^ D = 2 ^ b % 3 ^ D) :
    SieveAt D a ↔ SieveAt D b := by
  constructor <;> intro hs i hi
  · rw [← digit_eq_digit_of_mod_pow_eq D h hi]
    exact hs i hi
  · rw [digit_eq_digit_of_mod_pow_eq D h hi]
    exact hs i hi

/-- **Periodicity.** The depth-`(j+1)` sieve only sees `n % (2 · 3 ^ j)`: the crux gives
`2 ^ (2·3^j) ≡ 1 (mod 3^(j+1))`, and the parent's `two_pow_mod_eq_of_pow_mod_one` turns
that into periodicity of `2 ^ n mod 3^(j+1)` in `n`. -/
theorem sieveAt_mod_period (j n : ℕ) :
    SieveAt (j + 1) n ↔ SieveAt (j + 1) (n % (2 * 3 ^ j)) :=
  sieveAt_iff_of_two_pow_mod_eq
    (two_pow_mod_eq_of_pow_mod_one (two_pow_two_mul_three_pow_mod j) n)

/-! ## §4 The survivor classes -/

/-- `sieveClasses j`: the exponent classes mod the period `2 · 3 ^ j` that survive the
depth-`(j+1)` sieve. Lagarias [La09] calls the corresponding congruence classes
*admissible*. By `sieveAt_mod_period`, `n` passes the depth-`(j+1)` sieve iff
`n % (2·3^j) ∈ sieveClasses j`. -/
def sieveClasses (j : ℕ) : Finset ℕ :=
  (Finset.range (2 * 3 ^ j)).filter fun r => SieveAt (j + 1) r

/-- Membership in `sieveClasses` unfolds to the bound and the sieve condition. -/
theorem mem_sieveClasses {j r : ℕ} :
    r ∈ sieveClasses j ↔ r < 2 * 3 ^ j ∧ SieveAt (j + 1) r := by
  unfold sieveClasses
  rw [Finset.mem_filter, Finset.mem_range]

/-- Ground truth, depth 1 (mod 2): only `n ≡ 0`. (Odd `n` put the digit `2` in position
`0`; this is the parent's `even_of_base3ZeroOne_two_pow` seen through the sieve.) -/
theorem sieveClasses_zero : sieveClasses 0 = {0} := by decide

/-- Ground truth, depth 2 (mod 6): `{0, 2}` — exactly the survivor list of the parent's
`mod_six_of_base3ZeroOne_two_pow`. -/
theorem sieveClasses_one : sieveClasses 1 = {0, 2} := by decide

/-- Ground truth, depth 3 (mod 18): `{0, 2, 6, 8}` — exactly the survivor list of the
parent's `mod_eighteen_of_base3ZeroOne_two_pow`. -/
theorem sieveClasses_two : sieveClasses 2 = {0, 2, 6, 8} := by decide

set_option maxRecDepth 40000 in
/-- Ground truth, depth 4 (mod 54): `{0, 2, 8, 18, 20, 24, 26, 42}` — exactly the
survivor list of the parent's `mod_fiftyFour_of_base3ZeroOne_two_pow`. -/
theorem sieveClasses_three : sieveClasses 3 = {0, 2, 8, 18, 20, 24, 26, 42} := by decide

/-- Passing the depth-`(j+1)` sieve puts `n`'s class in `sieveClasses j`. -/
theorem mod_mem_sieveClasses_of_sieveAt {j n : ℕ} (h : SieveAt (j + 1) n) :
    n % (2 * 3 ^ j) ∈ sieveClasses j :=
  mem_sieveClasses.mpr
    ⟨Nat.mod_lt _ (by positivity), (sieveAt_mod_period j n).mp h⟩

/-- **The bridge to the parent's archived conjecture**: every element of `erdos406Set`
has its class mod `2 · 3 ^ j` in `sieveClasses j`, for every depth `j`. -/
theorem mod_mem_sieveClasses_of_mem_erdos406Set {n : ℕ} (hn : n ∈ erdos406Set) (j : ℕ) :
    n % (2 * 3 ^ j) ∈ sieveClasses j :=
  mod_mem_sieveClasses_of_sieveAt
    (sieveAt_of_base3ZeroOne (mem_erdos406Set_iff n |>.mp hn) (j + 1))

/-! ## §5 The doubling: exactly two of three lifts survive

Fix `s ∈ sieveClasses j` and `P = 2 · 3 ^ j`. The three lifts `s + t·P`, `t ∈ {0,1,2}`,
agree with `s` on digits `≤ j` (periodicity), and their digit at position `j + 1` is
`(q + t·u) % 3` where `q = 2^s / 3^(j+1) % 3` and `u = c·2^s` with `3 ∤ u` — so the three
new digits are `{0, 1, 2}` in some order and exactly one lift dies. -/

/-- Binomial congruence `(1 + u)^t ≡ 1 + t·u (mod u²)`, by induction on `t`. -/
theorem pow_one_add_modEq (u t : ℕ) : (1 + u) ^ t ≡ 1 + t * u [MOD u ^ 2] := by
  induction t with
  | zero => simpa using Nat.ModEq.refl 1
  | succ t ih =>
    calc (1 + u) ^ (t + 1) = (1 + u) ^ t * (1 + u) := pow_succ _ _
      _ ≡ (1 + t * u) * (1 + u) [MOD u ^ 2] := ih.mul_right _
      _ = 1 + (t + 1) * u + t * u ^ 2 := by ring
      _ ≡ 1 + (t + 1) * u + 0 [MOD u ^ 2] :=
          Nat.ModEq.add_left _ (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left _ _))
      _ = 1 + (t + 1) * u := by ring

/-- **Digit of a lift.** With `2 ^ (2·3^j) = 1 + c·3^(j+1)` (the crux), the digit of
`2 ^ (s + t·(2·3^j))` at position `j + 1` is `(2^s/3^(j+1) + t·(c·2^s)) % 3`: linear in
`t` with slope `c·2^s ≢ 0 (mod 3)`. -/
theorem lift_digit_eq {j c : ℕ} (hc : 2 ^ (2 * 3 ^ j) = 1 + c * 3 ^ (j + 1)) (s t : ℕ) :
    2 ^ (s + t * (2 * 3 ^ j)) / 3 ^ (j + 1) % 3
      = (2 ^ s / 3 ^ (j + 1) + t * (c * 2 ^ s)) % 3 := by
  have hpow : 2 ^ (s + t * (2 * 3 ^ j)) = 2 ^ s * (1 + c * 3 ^ (j + 1)) ^ t := by
    rw [pow_add, pow_mul', hc]
  have hdvd : (3 : ℕ) ^ (j + 2) ∣ (c * 3 ^ (j + 1)) ^ 2 := by
    rw [mul_pow, ← pow_mul]
    exact dvd_mul_of_dvd_right (pow_dvd_pow 3 (by omega)) _
  have hmodeq : 2 ^ s * (1 + c * 3 ^ (j + 1)) ^ t
      ≡ 2 ^ s + t * (c * 2 ^ s) * 3 ^ (j + 1) [MOD 3 ^ (j + 2)] := by
    have h1 : (1 + c * 3 ^ (j + 1)) ^ t ≡ 1 + t * (c * 3 ^ (j + 1)) [MOD 3 ^ (j + 2)] :=
      (pow_one_add_modEq (c * 3 ^ (j + 1)) t).of_dvd hdvd
    calc 2 ^ s * (1 + c * 3 ^ (j + 1)) ^ t
        ≡ 2 ^ s * (1 + t * (c * 3 ^ (j + 1))) [MOD 3 ^ (j + 2)] := h1.mul_left _
      _ = 2 ^ s + t * (c * 2 ^ s) * 3 ^ (j + 1) := by ring
  have hdigit : 2 ^ s * (1 + c * 3 ^ (j + 1)) ^ t / 3 ^ (j + 1) % 3
      = (2 ^ s + t * (c * 2 ^ s) * 3 ^ (j + 1)) / 3 ^ (j + 1) % 3 :=
    digit_eq_digit_of_mod_pow_eq (j + 2) hmodeq (by omega)
  rw [hpow, hdigit, Nat.add_mul_div_right _ _ (by positivity : (0:ℕ) < 3 ^ (j + 1))]

/-- **The 2-out-of-3 count.** If `3 ∤ u` then exactly two of the three values
`(q + t·u) % 3`, `t ∈ {0, 1, 2}`, are `≤ 1` — they are `{0, 1, 2}` in some order and
exactly one is the forbidden digit `2`. Reduced to a kernel-checked case bash on
`q % 3 < 3`, `u % 3 ∈ {1, 2}`. -/
theorem card_filter_digit_eq_two (q u : ℕ) (hu : ¬ 3 ∣ u) :
    ((Finset.range 3).filter (fun t => (q + t * u) % 3 ≤ 1)).card = 2 := by
  have haux : ∀ q' < 3, ∀ u' < 3, u' ≠ 0 →
      ((Finset.range 3).filter (fun t => (q' + t * u') % 3 ≤ 1)).card = 2 := by decide
  have hbridge : ((Finset.range 3).filter (fun t => (q + t * u) % 3 ≤ 1))
      = ((Finset.range 3).filter (fun t => (q % 3 + t * (u % 3)) % 3 ≤ 1)) :=
    Finset.filter_congr (fun t _ => by
      rw [show (q + t * u) % 3 = (q % 3 + t * (u % 3)) % 3 from
        (Nat.mod_modEq q 3).symm.add ((Nat.mod_modEq u 3).symm.mul_left t)])
  rw [hbridge]
  exact haux _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num))
    (fun h => hu (Nat.dvd_of_mod_eq_zero h))

/-- For `s` surviving at depth `j + 1`, a lift `s + t·(2·3^j)` survives at depth `j + 2`
iff its (new) digit at position `j + 1` is `≤ 1`; the old digits are inherited from `s`
by periodicity. -/
theorem sieveAt_succ_iff {j s : ℕ} (hs : SieveAt (j + 1) s) (hslt : s < 2 * 3 ^ j)
    (t : ℕ) :
    SieveAt (j + 2) (s + t * (2 * 3 ^ j)) ↔
      2 ^ (s + t * (2 * 3 ^ j)) / 3 ^ (j + 1) % 3 ≤ 1 := by
  constructor
  · intro h
    exact h (j + 1) (by omega)
  · intro hd i hi
    rcases (by omega : i < j + 1 ∨ i = j + 1) with hij | hij
    · have hper : SieveAt (j + 1) (s + t * (2 * 3 ^ j)) := by
        rw [sieveAt_mod_period, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hslt]
        exact hs
      exact hper i hij
    · rw [hij]
      exact hd

/-- **The fiber count.** Each surviving class `s ∈ sieveClasses j` has exactly `2` of its
`3` lifts in `sieveClasses (j + 1)`. -/
theorem card_fiber_sieveClasses_succ {j s : ℕ} (hs : s ∈ sieveClasses j) :
    ((sieveClasses (j + 1)).filter (fun r => r % (2 * 3 ^ j) = s)).card = 2 := by
  obtain ⟨hslt, hsAt⟩ := mem_sieveClasses.mp hs
  obtain ⟨c, hc, hc3⟩ := two_pow_two_mul_three_pow j
  have hu : ¬ 3 ∣ c * 2 ^ s := by
    intro hdvd
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hdvd with h | h
    · exact hc3 h
    · have h2 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      norm_num at h2
  have hcard : ((sieveClasses (j + 1)).filter (fun r => r % (2 * 3 ^ j) = s)).card
      = ((Finset.range 3).filter
          (fun t => 2 ^ (s + t * (2 * 3 ^ j)) / 3 ^ (j + 1) % 3 ≤ 1)).card := by
    refine Finset.card_bij' (fun r _ => r / (2 * 3 ^ j)) (fun t _ => s + t * (2 * 3 ^ j))
      ?_ ?_ ?_ ?_
    · -- forward map lands in the `t`-filter
      intro r hr
      obtain ⟨hrC, hrP⟩ := Finset.mem_filter.mp hr
      obtain ⟨hrlt, hrAt⟩ := mem_sieveClasses.mp hrC
      have hself : s + r / (2 * 3 ^ j) * (2 * 3 ^ j) = r := by
        rw [← hrP]
        exact Nat.mod_add_div' r (2 * 3 ^ j)
      have h3 : 2 * 3 ^ (j + 1) = 3 * (2 * 3 ^ j) := by ring
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul (by positivity)]
        omega
      · rw [hself]
        exact hrAt (j + 1) (by omega)
    · -- backward map lands in the fiber
      intro t ht
      obtain ⟨ht3, htd⟩ := Finset.mem_filter.mp ht
      rw [Finset.mem_range] at ht3
      have h3 : 2 * 3 ^ (j + 1) = 3 * (2 * 3 ^ j) := by ring
      have htP : t * (2 * 3 ^ j) ≤ 2 * (2 * 3 ^ j) := Nat.mul_le_mul (by omega) le_rfl
      refine Finset.mem_filter.mpr
        ⟨mem_sieveClasses.mpr ⟨by omega, (sieveAt_succ_iff hsAt hslt t).mpr htd⟩, ?_⟩
      rw [Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt hslt
    · -- left inverse
      intro r hr
      obtain ⟨-, hrP⟩ := Finset.mem_filter.mp hr
      rw [← hrP]
      exact Nat.mod_add_div' r (2 * 3 ^ j)
    · -- right inverse
      intro t ht
      rw [Nat.add_mul_div_right _ _ (by positivity : (0:ℕ) < 2 * 3 ^ j),
        Nat.div_eq_of_lt hslt]
      omega
  have hpred : ((Finset.range 3).filter
        (fun t => 2 ^ (s + t * (2 * 3 ^ j)) / 3 ^ (j + 1) % 3 ≤ 1))
      = ((Finset.range 3).filter
        (fun t => (2 ^ s / 3 ^ (j + 1) + t * (c * 2 ^ s)) % 3 ≤ 1)) :=
    Finset.filter_congr (fun t _ => by rw [lift_digit_eq hc s t])
  rw [hcard, hpred]
  exact card_filter_digit_eq_two _ _ hu

/-- **The doubling theorem.** The survivor count doubles with each depth increment:
`|sieveClasses (j+1)| = 2 · |sieveClasses j|`. Cover `sieveClasses (j+1)` by the fibers
of reduction mod `2 · 3 ^ j`; each fiber sits over a surviving class and has size exactly
`2`. -/
theorem card_sieveClasses_succ (j : ℕ) :
    (sieveClasses (j + 1)).card = 2 * (sieveClasses j).card := by
  have hmap : ∀ r ∈ sieveClasses (j + 1), r % (2 * 3 ^ j) ∈ sieveClasses j := by
    intro r hr
    obtain ⟨-, hrAt⟩ := mem_sieveClasses.mp hr
    exact mod_mem_sieveClasses_of_sieveAt (sieveAt_of_le (by omega) hrAt)
  have hsum : ∀ s ∈ sieveClasses j,
      ((sieveClasses (j + 1)).filter (fun r => r % (2 * 3 ^ j) = s)).card = 2 :=
    fun s hs => card_fiber_sieveClasses_succ hs
  rw [Finset.card_eq_sum_card_fiberwise (fun r hr => hmap r hr),
    Finset.sum_congr rfl hsum, Finset.sum_const, smul_eq_mul, mul_comm]

/-- **The exact survivor count**: `|sieveClasses j| = 2 ^ j`. This is the sharpness
statement for the sieve — the surviving density `2^j / (2·3^j) = (2/3)^j` is positive at
every depth, which is why this method can bound the counting function (with exponent
exactly `log₃ 2`, see `card_erdos406_filter_le_rpow`) but can never prove finiteness. -/
theorem card_sieveClasses (j : ℕ) : (sieveClasses j).card = 2 ^ j := by
  induction j with
  | zero => rw [sieveClasses_zero]; decide
  | succ j ih => rw [card_sieveClasses_succ, ih]; ring

/-! ## §6 The counting bound -/

/-- A congruence class mod `P` meets `Finset.range N` in at most `N / P + 1` numbers
(map `n ↦ n / P`; on a fixed class it is injective into `range (N/P + 1)`). No
positivity hypothesis on `P` is needed: at the degenerate `P = 0` the "class" is
`{s} ∩ range N` and the bound reads `≤ 0 + 1` (Nat convention `N / 0 = 0`), still true.
Every use below has `P = 2 · 3 ^ j`, which is positive. -/
theorem card_range_filter_mod_le {P : ℕ} (N s : ℕ) :
    ((Finset.range N).filter (fun n => n % P = s)).card ≤ N / P + 1 := by
  have hmaps : ∀ n ∈ (Finset.range N).filter (fun n => n % P = s),
      n / P ∈ Finset.range (N / P + 1) := by
    intro n hn
    have hn' : n < N := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
    have hd : n / P ≤ N / P := Nat.div_le_div_right (Nat.le_of_lt hn')
    exact Finset.mem_range.mpr (by omega)
  have hinj : ∀ a ∈ (Finset.range N).filter (fun n => n % P = s),
      ∀ b ∈ (Finset.range N).filter (fun n => n % P = s), a / P = b / P → a = b := by
    intro a ha b hb hab
    have ha2 : a % P = s := (Finset.mem_filter.mp ha).2
    have hb2 : b % P = s := (Finset.mem_filter.mp hb).2
    have h1 : a % P + a / P * P = a := Nat.mod_add_div' a P
    have h2 : b % P + b / P * P = b := Nat.mod_add_div' b P
    rw [hab] at h1
    omega
  have h := Finset.card_le_card_of_injOn (fun n => n / P)
    (fun n hn => hmaps n hn) (fun a ha b hb hab => hinj a ha b hb hab)
  rwa [Finset.card_range] at h

/-- **The window counting bound, pure ℕ (the depth-`j` sieve bound).** Solutions of
Erdős #406 below `N` number at most `2 ^ j · (N / (2·3^j) + 1)`: each solution's class
mod `2 · 3 ^ j` lies in `sieveClasses j` (which has exactly `2 ^ j` elements), and each
class meets `range N` at most `N/(2·3^j) + 1` times. -/
theorem card_erdos406_filter_le (N j : ℕ) :
    ((Finset.range N).filter fun n => Base3ZeroOne (2 ^ n)).card
      ≤ 2 ^ j * (N / (2 * 3 ^ j) + 1) := by
  have hmap : ∀ n ∈ (Finset.range N).filter (fun n => Base3ZeroOne (2 ^ n)),
      n % (2 * 3 ^ j) ∈ sieveClasses j := fun n hn =>
    mod_mem_sieveClasses_of_sieveAt
      (sieveAt_of_base3ZeroOne (Finset.mem_filter.mp hn).2 (j + 1))
  have hfiber : ∀ s ∈ sieveClasses j,
      (((Finset.range N).filter (fun n => Base3ZeroOne (2 ^ n))).filter
          (fun n => n % (2 * 3 ^ j) = s)).card
        ≤ N / (2 * 3 ^ j) + 1 := by
    intro s _
    refine le_trans (Finset.card_le_card ?_) (card_range_filter_mod_le N s)
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn1).1, hn2⟩
  rw [Finset.card_eq_sum_card_fiberwise (fun n hn => hmap n hn)]
  refine le_trans (Finset.sum_le_sum hfiber) (le_of_eq ?_)
  rw [Finset.sum_const, smul_eq_mul, card_sieveClasses]

/-- **Optimised depth.** Taking `j = Nat.log 3 N` in `card_erdos406_filter_le` (so that
`N < 3 ^ (j+1)` and the window quotient is `≤ 1`) gives the pure-ℕ form of the
`2 N^{log₃ 2}` bound: at most `2 · 2 ^ (log₃ N)` solutions below `N`. -/
theorem card_erdos406_filter_le_log (N : ℕ) :
    ((Finset.range N).filter fun n => Base3ZeroOne (2 ^ n)).card
      ≤ 2 * 2 ^ Nat.log 3 N := by
  have hbound := card_erdos406_filter_le N (Nat.log 3 N)
  have hN3 : N < 3 ^ (Nat.log 3 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hpow : (3 : ℕ) ^ (Nat.log 3 N + 1) = 3 ^ Nat.log 3 N * 3 := pow_succ 3 _
  have hdivlt : N / (2 * 3 ^ Nat.log 3 N) < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    omega
  have hmul : 2 ^ Nat.log 3 N * (N / (2 * 3 ^ Nat.log 3 N) + 1) ≤ 2 ^ Nat.log 3 N * 2 :=
    Nat.mul_le_mul le_rfl (by omega)
  omega

/-- **[La09], Theorem 1.4 at `λ = 1` (extending Narkiewicz [Na80]): the real counting
bound `N(x) ≤ 2 x^{log₃ 2}`.** The number of exponents `n < N` for which `2 ^ n` has all
base-3 digits in `{0, 1}` is at most `2 · N ^ (log₃ 2)`. Narkiewicz's own constant is
`1.62` (not formalised); the exponent `log₃ 2 ≈ 0.6309` is the same, and by
`card_sieveClasses` it is exactly the exponent the sieve produces. -/
theorem card_erdos406_filter_le_rpow (N : ℕ) (hN : 1 ≤ N) :
    (((Finset.range N).filter fun n => Base3ZeroOne (2 ^ n)).card : ℝ)
      ≤ 2 * (N : ℝ) ^ Real.logb 3 2 := by
  have hlogb : (0 : ℝ) ≤ Real.logb 3 2 := Real.logb_nonneg (by norm_num) (by norm_num)
  have hcast : (((Finset.range N).filter fun n => Base3ZeroOne (2 ^ n)).card : ℝ)
      ≤ 2 * (2 : ℝ) ^ Nat.log 3 N := by
    calc (((Finset.range N).filter fun n => Base3ZeroOne (2 ^ n)).card : ℝ)
        ≤ ((2 * 2 ^ Nat.log 3 N : ℕ) : ℝ) := Nat.cast_le.mpr (card_erdos406_filter_le_log N)
      _ = 2 * (2 : ℝ) ^ Nat.log 3 N := by push_cast; ring
  have hkey : (2 : ℝ) ^ Nat.log 3 N = ((3 : ℝ) ^ Nat.log 3 N) ^ Real.logb 3 2 := by
    rw [show ((3 : ℝ) ^ Nat.log 3 N) ^ Real.logb 3 2
          = ((3 : ℝ) ^ (Nat.log 3 N : ℝ)) ^ Real.logb 3 2 by rw [Real.rpow_natCast],
      ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_natCast, Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]
  have hpowle : ((3 : ℝ) ^ Nat.log 3 N) ≤ (N : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 3 (by omega)
  have hmono : ((3 : ℝ) ^ Nat.log 3 N) ^ Real.logb 3 2 ≤ (N : ℝ) ^ Real.logb 3 2 :=
    Real.rpow_le_rpow (by positivity) hpowle hlogb
  calc (((Finset.range N).filter fun n => Base3ZeroOne (2 ^ n)).card : ℝ)
      ≤ 2 * (2 : ℝ) ^ Nat.log 3 N := hcast
    _ = 2 * ((3 : ℝ) ^ Nat.log 3 N) ^ Real.logb 3 2 := by rw [hkey]
    _ ≤ 2 * (N : ℝ) ^ Real.logb 3 2 := by linarith

/-! ## §7 Joint satisfiability of every hypothesis, and concrete instantiations

Mirroring the parent's §9: every hypothesis-bearing declaration above is instantiated at
a concrete model, and the counting bounds are checked on an explicit window against an
independent kernel count. -/

/-- `SieveAt` ground truth: `2 ^ 0 = 1` passes depth 2; `2 ^ 1 = 2 = (2)₃` fails depth 1;
`2 ^ 8 = 256 = (100111)₃` passes depth 6. -/
example : SieveAt 2 0 ∧ ¬ SieveAt 1 1 ∧ SieveAt 6 8 := by decide

/-- `sieveAt_of_base3ZeroOne` and `base3ZeroOne_two_pow_iff_forall_sieveAt` at the
parent's witness `n = 2`. -/
example : ∀ D, SieveAt D 2 :=
  (base3ZeroOne_two_pow_iff_forall_sieveAt 2).mp witness_two_pow_two

/-- `sieveAt_of_le`: jointly satisfied at `D' = 2 ≤ 6 = D`, `n = 8`. -/
example : SieveAt 2 8 :=
  sieveAt_of_le (by norm_num) (sieveAt_of_base3ZeroOne witness_two_pow_eight 6)

/-- `digit_eq_digit_of_mod_pow_eq`: satisfied at `m = 4`, `m' = 13`, `D = 2`, `i = 0`
(`4 ≡ 13 (mod 9)`, and both have units digit `1`). -/
example : 4 / 3 ^ 0 % 3 = 13 / 3 ^ 0 % 3 :=
  digit_eq_digit_of_mod_pow_eq 2 (by norm_num) (by norm_num)

/-- The crux at `j = 1`: `2 ^ 6 = 64 = 1 + 7 · 9` with `3 ∤ 7`, so `2 ^ 6 % 9 = 1`. -/
example : 2 ^ (2 * 3 ^ 1) % 3 ^ 2 = 1 % 3 ^ 2 := two_pow_two_mul_three_pow_mod 1

/-- `sieveAt_mod_period` at `j = 1`, `n = 8`: depth-2 sieve at `8` is the depth-2 sieve
at `8 % 6 = 2`. -/
example : SieveAt 2 8 ↔ SieveAt 2 (8 % (2 * 3 ^ 1)) := sieveAt_mod_period 1 8

/-- `sieveAt_iff_of_two_pow_mod_eq` directly, at `D = 2` and the *distinct* exponents
`a = 8`, `b = 2` (`2 ^ 8 % 9 = 4 = 2 ^ 2 % 9`), so the congruence hypothesis is not
satisfied by mere reflexivity. -/
example : SieveAt 2 8 ↔ SieveAt 2 2 := sieveAt_iff_of_two_pow_mod_eq (by norm_num)

/-- `mod_mem_sieveClasses_of_mem_erdos406Set` at the parent's witness `n = 8`, depth
`j = 2`: `8 % 18 = 8 ∈ {0, 2, 6, 8}`. -/
example : (8 : ℕ) % (2 * 3 ^ 2) ∈ sieveClasses 2 :=
  mod_mem_sieveClasses_of_mem_erdos406Set witness_two_pow_eight 2

/-- `mod_mem_sieveClasses_of_sieveAt` directly, at `j = 2`, `n = 8`: its hypothesis
`SieveAt 3 8` is satisfied by kernel check (not routed through `Base3ZeroOne`). -/
example : (8 : ℕ) % (2 * 3 ^ 2) ∈ sieveClasses 2 :=
  mod_mem_sieveClasses_of_sieveAt (by decide)

/-- `pow_one_add_modEq` at `u = 3`, `t = 2`: `(1+3)² = 16 ≡ 7 = 1 + 2·3 (mod 9)`. -/
example : (1 + 3) ^ 2 ≡ 1 + 2 * 3 [MOD 3 ^ 2] := pow_one_add_modEq 3 2

/-- `lift_digit_eq` at `j = 0`, `c = 1`, `s = 2`, `t = 1`, with an independent kernel
check that both sides equal `2` (the lift `2 ^ 4 = 16 = (121)₃` has digit `2` at position
`1` — this is the dying lift of the class `s = 2`). -/
example : 2 ^ (2 + 1 * (2 * 3 ^ 0)) / 3 ^ (0 + 1) % 3
    = (2 ^ 2 / 3 ^ (0 + 1) + 1 * (1 * 2 ^ 2)) % 3 :=
  lift_digit_eq (by norm_num) 2 1

example : 2 ^ 4 / 3 % 3 = 2 ∧ (2 ^ 2 / 3 + 4) % 3 = 2 := by decide

/-- `card_filter_digit_eq_two` at `q = 1`, `u = 2`: the three values `(1 + 2t) % 3` are
`1, 0, 2` — exactly two are `≤ 1` — with an independent kernel check. -/
example : ((Finset.range 3).filter (fun t => (1 + t * 2) % 3 ≤ 1)).card = 2 :=
  card_filter_digit_eq_two 1 2 (by norm_num)

example : ((Finset.range 3).filter (fun t => (1 + t * 2) % 3 ≤ 1)) = {0, 1} := by decide

/-- `sieveAt_succ_iff`: both hypotheses jointly at `j = 0`, `s = 0`, `t = 1` (`SieveAt 1 0`
holds and `0 < 2`). -/
example : SieveAt (0 + 2) (0 + 1 * (2 * 3 ^ 0)) ↔
    2 ^ (0 + 1 * (2 * 3 ^ 0)) / 3 ^ (0 + 1) % 3 ≤ 1 :=
  sieveAt_succ_iff (by decide) (by norm_num) 1

/-- `card_fiber_sieveClasses_succ` at `j = 0`, `s = 0`: the fiber of `sieveClasses 1 =
{0, 2}` over `0` mod `2` is all of it — `2` elements — with an independent kernel check. -/
example : ((sieveClasses (0 + 1)).filter (fun r => r % (2 * 3 ^ 0) = 0)).card = 2 :=
  card_fiber_sieveClasses_succ (by decide)

example : ((sieveClasses 1).filter (fun r => r % 2 = 0)) = {0, 2} := by decide

/-- The exact count at depth 4, against the kernel: `|{0, 2, 8, 18, 20, 24, 26, 42}| = 8
= 2 ^ 3`. -/
example : (sieveClasses 3).card = 8 := by
  rw [card_sieveClasses]
  norm_num

/-- `card_range_filter_mod_le` at `P = 6`, `N = 19`, `s = 2`: the class `{2, 8, 14}` has
`3 ≤ 19/6 + 1 = 4` elements below `19`; independent kernel check of the class. -/
example : ((Finset.range 19).filter (fun n => n % 6 = 2)).card ≤ 19 / 6 + 1 :=
  card_range_filter_mod_le 19 2

example : ((Finset.range 19).filter (fun n => n % 6 = 2)) = {2, 8, 14} := by decide

set_option maxRecDepth 40000 in
/-- **The window `N = 19`, `j = 1` of `card_erdos406_filter_le`, checked exactly.** The
kernel count of solutions below `19` is `3` (they are `{0, 2, 8}`, consistent with the
parent's `mem_erdos406Set_iff_of_le`), and the sieve bound evaluates to
`2 ^ 1 · (19/6 + 1) = 8`. -/
example : ((Finset.range 19).filter fun n => Base3ZeroOne (2 ^ n)).card = 3 := by decide

example : ((Finset.range 19).filter fun n => Base3ZeroOne (2 ^ n)).card ≤ 8 := by
  have h := card_erdos406_filter_le 19 1
  norm_num at h
  exact h

/-- The optimised-depth bound on the same window: `Nat.log 3 19 = 2`, so
`card_erdos406_filter_le_log` gives `≤ 2 · 2² = 8`. -/
example : ((Finset.range 19).filter fun n => Base3ZeroOne (2 ^ n)).card ≤ 8 := by
  have hlog : Nat.log 3 19 = 2 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h := card_erdos406_filter_le_log 19
  rw [hlog] at h
  norm_num at h
  exact h

/-- `card_erdos406_filter_le_rpow` instantiated at `N = 1` (the hypothesis `1 ≤ N` is
satisfiable): one solution below `1` (namely `n = 0`), bounded by `2 · 1^{log₃ 2} = 2`. -/
example : (((Finset.range 1).filter fun n => Base3ZeroOne (2 ^ n)).card : ℝ)
    ≤ 2 * (1 : ℝ) ^ Real.logb 3 2 := by
  have h := card_erdos406_filter_le_rpow 1 le_rfl
  simpa using h

/-- `card_erdos406_filter_le_rpow` at the nontrivial window `N = 19`: the three solutions
`{0, 2, 8}` (kernel count above) against the bound `2 · 19^{log₃ 2} ≈ 12.8`. -/
example : (((Finset.range 19).filter fun n => Base3ZeroOne (2 ^ n)).card : ℝ)
    ≤ 2 * (19 : ℝ) ^ Real.logb 3 2 := by
  have h := card_erdos406_filter_le_rpow 19 (by norm_num)
  simpa using h

/-- The `N = 19` right-hand side is a nondegenerate quantity: since
`0 ≤ log₃ 2`, it is at least `2 · 19⁰ = 2` … -/
example : (2 : ℝ) ≤ 2 * (19 : ℝ) ^ Real.logb 3 2 := by
  have h1 : (1 : ℝ) ≤ (19 : ℝ) ^ Real.logb 3 2 :=
    Real.one_le_rpow (by norm_num) (Real.logb_nonneg (by norm_num) (by norm_num))
  linarith

/-- … and since `log₃ 2 ≤ 1`, it is at most `2 · 19¹ = 38`: the real bound genuinely
sits between the trivial constants. -/
example : 2 * (19 : ℝ) ^ Real.logb 3 2 ≤ 38 := by
  have hb1 : Real.logb 3 2 ≤ 1 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num), Real.rpow_one]
    norm_num
  have h19 : (19 : ℝ) ^ Real.logb 3 2 ≤ (19 : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hb1
  rw [Real.rpow_one] at h19
  linarith

end Erdos406

#print axioms Erdos406.two_pow_two_mul_three_pow
#print axioms Erdos406.two_pow_two_mul_three_pow_mod
#print axioms Erdos406.base3ZeroOne_two_pow_iff_forall_sieveAt
#print axioms Erdos406.sieveAt_of_base3ZeroOne
#print axioms Erdos406.sieveAt_of_le
#print axioms Erdos406.digit_eq_digit_of_mod_pow_eq
#print axioms Erdos406.sieveAt_iff_of_two_pow_mod_eq
#print axioms Erdos406.sieveAt_mod_period
#print axioms Erdos406.mem_sieveClasses
#print axioms Erdos406.sieveClasses_zero
#print axioms Erdos406.sieveClasses_one
#print axioms Erdos406.sieveClasses_two
#print axioms Erdos406.sieveClasses_three
#print axioms Erdos406.mod_mem_sieveClasses_of_sieveAt
#print axioms Erdos406.mod_mem_sieveClasses_of_mem_erdos406Set
#print axioms Erdos406.pow_one_add_modEq
#print axioms Erdos406.lift_digit_eq
#print axioms Erdos406.card_filter_digit_eq_two
#print axioms Erdos406.sieveAt_succ_iff
#print axioms Erdos406.card_fiber_sieveClasses_succ
#print axioms Erdos406.card_sieveClasses_succ
#print axioms Erdos406.card_sieveClasses
#print axioms Erdos406.card_range_filter_mod_le
#print axioms Erdos406.card_erdos406_filter_le
#print axioms Erdos406.card_erdos406_filter_le_log
#print axioms Erdos406.card_erdos406_filter_le_rpow
