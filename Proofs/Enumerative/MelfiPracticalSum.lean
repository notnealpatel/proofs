import Enumerative.Practical

/-!
# Melfi's theorem: every even positive integer is a sum of two practical numbers

Margenstern conjectured (Margenstern, *Results and conjectures about practical numbers*,
C.R. Acad. Sc. Paris 299 (1984) 895–898; *Les nombres pratiques: théorie, observations
et conjectures*, J. Number Theory 37 (1991) 1–36) a Goldbach analogue for the practical
numbers (OEIS A005153).  It was proved by Melfi, *On two conjectures about practical
numbers*, J. Number Theory 56 (1996) 205–210.

## Sources, quoted verbatim

OEIS A005153, comment of Hal M. Switkay (Jan 28 2023), pulled live 2026-08-05 via
`goof oeis show A005153`:

> Conjecture: every odd number, beginning with 3, is the sum of a prime number and a
> practical number.  Note that this conjecture occupies the space between the unproven
> Goldbach conjecture and the theorem that every even number, beginning with 2, is the
> sum of two practical numbers (Melfi's 1996 proof of Margenstern's conjecture).

Melfi, *A survey on practical numbers*, Rend. Sem. Mat. Univ. Pol. Torino 53,4 (1995)
347–359 — the author's own restatement of his 1996 proof, fetched to
`References/Melfi-Survey-1995/347/paper.txt` (OCR of the published scan).  Section 3,
"The Goldbach problem for practical numbers", verbatim (OCR artefacts corrected where the scan mangles subscripts,
fractions, and strictness marks (`<` normalised to `≤` where the inclusive reading
is forced by the proof); see "Deviations" below):

> LEMMA 4.  If `m` is a practical number and `n` is an integer such that
> `1 ≤ n ≤ σ(m) + 1`, then `mn` is a practical number.  In particular, for
> `1 ≤ n ≤ 2m`, `mn` is practical.

> Proof.  The first assertion easily follows from Stewart's structure theorem; see also
> [7, p. 6].  Since `m − 1` is a sum of distinct divisors of `m`, we have
> `m + (m − 1) ≤ σ(m)`, i.e. `2m ≤ σ(m) + 1`, and this proves the second assertion.

> LEMMA 5.  If `m` and `m + 2` are two practical numbers, then every even integer `2n`
> with `(1/2)m² ≤ 2n ≤ (7/2)m²` is a sum of two practical numbers.

> THEOREM 6.  Every even positive integer is a sum of two practical numbers.

Melfi's Theorem 6 is proved from Lemma 5 by exhibiting a sequence `{mₙ}` of *twin
practical* numbers (`mₙ` and `mₙ + 2` both practical) with `1 < mₙ₊₁/mₙ < √7`, so that
the Lemma-5 intervals `[½mₙ², (7/2)mₙ²]` overlap and cover `[128, ∞)`; the initial
segment `2n < 126` is covered by the twin pairs `(2,4)`, `(4,6)`, `(6,8)`.  Verbatim:

> Since (2,4), (4,6), (6,8) are pairs of twin practical numbers, by Lemma 5 every
> `2n < 126` is a sum of two practical numbers.  […]  We shall construct a sequence
> `{mₙ}` satisfying (i), (ii), (iii) and a condition slightly stronger than (iv), i.e.
> `1 < mₙ₊₁/mₙ < 2`.  Let `S₀ = {16, 30, 54, 88, 160}`.

The recursion generating `Sₖ` from `Sₖ₋₁` is mangled by the OCR of the scan.  It is
*reconstructed* (not quoted) as `Sₖ = {½r² + 2r, r² + 3r : r ∈ Sₖ₋₁}`; this reading is
consistent with the one legible instance `r₀,₅ = ½r₀,₁² + 2r₀,₁ = 160` and with the
underlying identity — if `r` and `r + 2` are practical then
`r(1 + t(r+2)/2) = (r+2)(1 + tr/2) − 2` exhibits `t = 1, 2` as twin practical pairs
`½r² + 2r` and `r² + 3r`.  **Nothing below depends on this reconstruction**; it is
recorded only to document what is being replaced.

## What is formalized here, and how it deviates from Melfi

The **statement** proved here is Melfi's Theorem 6, and the **engine** is Melfi's Lemma
4, formalized as `Nat.Practical.mul_of_le_one_add_sum_divisors`.  The **covering
argument is not Melfi's**: his Lemma 5 plus the recursive construction of a
bounded-ratio twin-practical sequence

  `S₀ = {16, 30, 54, 88, 160}`,  `Sₖ = {½r² + 2r, r² + 3r : r ∈ Sₖ₋₁}`

is replaced here by a two-modulus covering that needs no twin practical numbers at all
(`Nat.exists_practical_add_practical_of_window`).  The two moduli are

* `2 ^ k`, practical for every `k` (`Nat.practical_two_pow`), with Lemma-4 budget
  `1 + σ(2^k) = 2^(k+1)`;
* `2 * 3 ^ j`, practical for every `j` (`Nat.practical_two_mul_three_pow`), with
  Lemma-4 budget `1 + σ(2·3^j) = (3^(j+2) − 1)/2`.

They satisfy `gcd(2^k, 2·3^j) = 2`, so every *even* number in a suitable window is
`a · 2^k + b · (2 · 3^j)` with `a`, `b` inside the two budgets, and Lemma 4 makes both
summands practical.  Choosing `j = j(k)` by `3^(j+1) ≤ 2^k < 3^(j+2)` makes the windows
`[2^k (3^j + 1), 2^(2k+1)]` overlap consecutively, and they cover `[8, ∞)`; `2`, `4`,
`6` are handled by hand.

Melfi's own Lemma 5 and his twin-practical recursion are therefore **not** formalized.
The simplification is elementary and is not claimed to be new; it is recorded here only
because it is what the Lean proof actually does.  Melfi derives Lemma 4 from Stewart's
structure theorem; the proof below is direct from the strong characterisation
`Nat.practical_iff_forall_le_sum_divisors` of `Enumerative.Practical`, so
`Enumerative.StewartCriterion` is not needed as an import.

## Main results

* `Nat.Practical.mul_of_le_one_add_sum_divisors` — **Melfi's Lemma 4**, first assertion;
* `Nat.Practical.mul_of_le_two_mul` — Lemma 4, second assertion (`n ≤ 2m` suffices);
* `Nat.practical_two_mul_three_pow` — `2 · 3 ^ j` is practical;
* `Nat.exists_practical_add_practical_of_window` — the covering step;
* `Nat.even_eq_practical_add_practical` — **Melfi's Theorem 6**.

## Guards

The theorem needs `0 < n`: `0` is even and is not a sum of two practical numbers, since
practical numbers are positive.  `Even n` alone would therefore be false at `n = 0`.

## Axiom audit

Every declaration in this file reports a subset of
`{propext, Classical.choice, Quot.sound}`; the `#print axioms` sweep is at the end.
There is no `native_decide` and no `sorry`.  The import `Enumerative.Practical` carries
one intended `sorry` (`Nat.coleman_multiperfect_practical`, an open conjecture); nothing
here depends on it, as the sweep confirms.
-/

set_option autoImplicit false

namespace Nat

/-! ## Melfi's Lemma 4

`m` practical and `1 ≤ t ≤ σ(m) + 1` force `m * t` practical.  Melfi reads this off
Stewart's structure theorem; the proof here is direct.  Split `x ≤ m * t` as
`x = q * t + r` with `r < t`.  Then `r ≤ σ(m)` and `q ≤ m`, so the strong
characterisation represents `r` over `m.divisors` and the plain definition represents
`q` over `m.divisors`; scaling the second representation by `t` lands it in
`(m * t).divisors`, and the two families are disjoint because the first sums to `r < t`
while every member of the second is at least `t`.
-/

/-- **Melfi's Lemma 4** (Melfi 1996, Lemma 4; Melfi 1995 survey, Lemma 4): if `m` is
practical and `1 ≤ t ≤ 1 + σ(m)`, then `m * t` is practical.

The threshold is sharp in the sense that `t = 2 + σ(m)` can fail: `m = 2` has
`σ(2) = 3`, and `2 * 5 = 10` is not practical (witnessed after the statement). -/
theorem Practical.mul_of_le_one_add_sum_divisors {m t : ℕ} (hm : m.Practical)
    (ht : 0 < t) (hle : t ≤ 1 + ∑ d ∈ m.divisors, d) : (m * t).Practical := by
  classical
  have hm0 : 0 < m := hm.pos
  have hmt : 0 < m * t := Nat.mul_pos hm0 ht
  rw [practical_iff_exists_subset]
  refine ⟨hmt, fun x hx => ?_⟩
  -- checkpoint: base-`t` split of `x`, with quotient at most `m` and remainder at most `σ(m)`
  have hsplit : x / t * t + x % t = x := Nat.div_add_mod' x t
  have hrt : x % t < t := Nat.mod_lt x ht
  have hqm : x / t ≤ m := Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact hx)
  have hrσ : x % t ≤ ∑ d ∈ m.divisors, d := by omega
  obtain ⟨S, hS_sub, hS_sum⟩ := hm.exists_sum_eq_of_le_sum_divisors hrσ
  obtain ⟨T, hT_sub, hT_sum⟩ := hm.exists_sum_eq hqm
  -- the quotient's representation, scaled by `t`
  set T' : Finset ℕ := T.image (fun d => d * t) with hT'_def
  have hinj : ∀ a ∈ T, ∀ b ∈ T, a * t = b * t → a = b := fun _ _ _ _ h =>
    Nat.eq_of_mul_eq_mul_right ht h
  have hT'_sum : ∑ b ∈ T', b = x / t * t := by
    rw [hT'_def, Finset.sum_image hinj, ← Finset.sum_mul, hT_sum]
  -- checkpoint: members of `S` are below `t`, members of `T'` are at least `t`
  have hS_lt : ∀ s ∈ S, s < t := fun s hs => by
    have hs_le : s ≤ x % t :=
      hS_sum ▸ Finset.single_le_sum (f := fun x : ℕ => x) (fun i _ => Nat.zero_le i) hs
    omega
  have hT'_ge : ∀ b ∈ T', t ≤ b := by
    intro b hb
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hb
    have hd_pos : 0 < d := Nat.pos_of_mem_divisors (hT_sub hd)
    calc t = 1 * t := (Nat.one_mul t).symm
      _ ≤ d * t := Nat.mul_le_mul_right t hd_pos
  have hdisj : Disjoint S T' := by
    rw [Finset.disjoint_left]
    intro b hbS hbT'
    exact absurd (hT'_ge b hbT') (by have := hS_lt b hbS; omega)
  -- checkpoint: both families consist of divisors of `m * t`
  have hsub : S ∪ T' ⊆ (m * t).divisors := by
    intro b hb
    rcases Finset.mem_union.mp hb with hbS | hbT'
    · exact Nat.mem_divisors.mpr
        ⟨(Nat.mem_divisors.mp (hS_sub hbS)).1.trans (Dvd.intro t rfl), hmt.ne'⟩
    · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hbT'
      exact Nat.mem_divisors.mpr
        ⟨Nat.mul_dvd_mul_right (Nat.mem_divisors.mp (hT_sub hd)).1 t, hmt.ne'⟩
  refine ⟨S ∪ T', hsub, ?_⟩
  rw [Finset.sum_union hdisj, hS_sum, hT'_sum]
  omega

/-- **Melfi's Lemma 4**, second assertion: `1 ≤ t ≤ 2 * m` already suffices, since
Srinivasan's bound gives `2m ≤ σ(m) + 1` (`Nat.Practical.two_mul_le_one_add_sum_divisors`). -/
theorem Practical.mul_of_le_two_mul {m t : ℕ} (hm : m.Practical) (ht : 0 < t)
    (hle : t ≤ 2 * m) : (m * t).Practical :=
  hm.mul_of_le_one_add_sum_divisors ht (hle.trans hm.two_mul_le_one_add_sum_divisors)

/-! ## The two moduli and their Lemma-4 budgets

The covering below feeds Lemma 4 with the two families `2 ^ k` and `2 * 3 ^ j`.  Both
are practical for every exponent, `gcd (2 ^ k) (2 * 3 ^ j) = 2` for `1 ≤ k` and `1 ≤ j`,
and their Lemma-4 budgets `1 + σ` are `2 ^ (k + 1)` and `(3 ^ (j + 2) - 1) / 2`.  The
second budget is recorded division-free as `2 * (1 + σ) + 1 = 3 ^ (j + 2)`.
-/

/-- The Lemma-4 budget of `2 ^ k` is `1 + σ(2 ^ k) = 2 ^ (k + 1)`: the divisors of
`2 ^ k` are `2 ^ 0, …, 2 ^ k` and the geometric sum telescopes. -/
theorem one_add_sum_divisors_two_pow (k : ℕ) :
    1 + ∑ d ∈ ((2 : ℕ) ^ k).divisors, d = 2 ^ (k + 1) := by
  have hsum : ∑ d ∈ ((2 : ℕ) ^ k).divisors, d = ∑ i ∈ Finset.range (k + 1), 2 ^ i :=
    Nat.sum_divisors_prime_pow Nat.prime_two
  have hgeom : (∑ i ∈ Finset.range (k + 1), ((1 : ℕ) + 1) ^ i) * 1 + 1
      = ((1 : ℕ) + 1) ^ (k + 1) := geom_sum_mul_add 1 (k + 1)
  norm_num at hgeom
  omega

/-- `2 * 3 ^ j` is practical for every `j`.  Induction on `j` with Melfi's Lemma 4 at
`t = 3`, which is inside the budget because `3 ≤ 2 * (2 * 3 ^ j)`. -/
theorem practical_two_mul_three_pow (j : ℕ) : ((2 : ℕ) * 3 ^ j).Practical := by
  induction j with
  | zero => simpa using practical_two
  | succ j ih =>
    have hpos : (1 : ℕ) ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
    have hstep : ((2 * 3 ^ j) * 3 : ℕ).Practical :=
      ih.mul_of_le_two_mul (by norm_num) (by omega)
    have heq : (2 : ℕ) * 3 ^ (j + 1) = (2 * 3 ^ j) * 3 := by ring
    rw [heq]
    exact hstep

/-- The Lemma-4 budget of `2 * 3 ^ j`, stated division-free:
`2 * (1 + σ(2 · 3 ^ j)) + 1 = 3 ^ (j + 2)`, i.e. `1 + σ(2 · 3 ^ j) = (3 ^ (j+2) − 1)/2`.
Multiplicativity of `σ` across the coprime factors `2` and `3 ^ j`, then the geometric
sum. -/
theorem two_mul_one_add_sum_divisors_two_mul_three_pow (j : ℕ) :
    2 * (1 + ∑ d ∈ ((2 : ℕ) * 3 ^ j).divisors, d) + 1 = 3 ^ (j + 2) := by
  have hcop : Nat.Coprime 2 (3 ^ j) := Nat.Coprime.pow_right _ (by norm_num)
  have hsplit : ∑ d ∈ ((2 : ℕ) * 3 ^ j).divisors, d
      = (∑ d ∈ (2 : ℕ).divisors, d) * ∑ d ∈ ((3 : ℕ) ^ j).divisors, d :=
    Nat.Coprime.sum_divisors_mul hcop
  have h2 : ∑ d ∈ (2 : ℕ).divisors, d = 3 := by decide
  have h3 : ∑ d ∈ ((3 : ℕ) ^ j).divisors, d = ∑ i ∈ Finset.range (j + 1), 3 ^ i :=
    Nat.sum_divisors_prime_pow Nat.prime_three
  have hgeom : (∑ i ∈ Finset.range (j + 1), ((2 : ℕ) + 1) ^ i) * 2 + 1
      = ((2 : ℕ) + 1) ^ (j + 1) := geom_sum_mul_add 2 (j + 1)
  have hpow : (3 : ℕ) ^ (j + 2) = 3 * 3 ^ (j + 1) := by ring
  norm_num at hgeom
  rw [hsplit, h2, h3]
  omega

/-! ## The covering step

Fix `k ≥ 1` and `j` with `2 ^ k < 3 ^ (j + 2)`.  Every even `n` in the window
`[2 ^ k (3 ^ j + 1), 2 ^ (2k+1)]` is `a · 2 ^ k + b · (2 · 3 ^ j)` with `a` inside the
budget `2 ^ (k+1)` of `2 ^ k` and `b` inside the budget of `2 · 3 ^ j`.  Writing
`n = 2F` and `M = 2 ^ (k-1)`, the residue `b ∈ [1, M]` is pinned by
`b · 3 ^ j ≡ F (mod M)` — solvable because `3 ^ j` is invertible mod the power of two —
and then `a = (F − b · 3 ^ j)/M`.  The lower window bound makes `a ≥ 1`, the upper one
makes `a ≤ 2 ^ (k+1)`, and `2 ^ k < 3 ^ (j+2)` makes `M` fit inside the second budget.
-/

/-- **The covering step.**  If `1 ≤ k` and `2 ^ k < 3 ^ (j + 2)`, then every even `n`
with `2 ^ k * (3 ^ j + 1) ≤ n ≤ 2 ^ (2 * k + 1)` is a sum of two practical numbers.

This replaces Melfi's Lemma 5 (which covers `[½m², (7/2)m²]` from a twin practical pair
`m`, `m + 2`); the moduli here are `2 ^ k` and `2 * 3 ^ j`, whose gcd is `2`. -/
theorem exists_practical_add_practical_of_window {k j n : ℕ} (hk : 1 ≤ k)
    (hj : 2 ^ k < 3 ^ (j + 2)) (hlo : 2 ^ k * (3 ^ j + 1) ≤ n)
    (hhi : n ≤ 2 ^ (2 * k + 1)) (hn : Even n) :
    ∃ p q : ℕ, p.Practical ∧ q.Practical ∧ p + q = n := by
  obtain ⟨F, hF⟩ := hn
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  set M : ℕ := 2 ^ k' with hM_def
  have hM_pos : 0 < M := pow_pos (by norm_num) k'
  have hpow : (2 : ℕ) ^ (k' + 1) = 2 * M := by rw [hM_def]; ring
  -- checkpoint: the residue `b ∈ [1, M]` with `b * 3 ^ j ≡ F (mod M)`
  have hcop : Nat.Coprime (3 ^ j) M := Nat.Coprime.pow _ _ (by norm_num)
  obtain ⟨b₀, hb₀_lt, hb₀⟩ := Nat.exists_mul_mod_eq_of_coprime F hcop hM_pos.ne'
  set b : ℕ := if b₀ = 0 then M else b₀ with hb_def
  have hb_pos : 0 < b := by rw [hb_def]; split <;> omega
  have hb_hi : b ≤ M := by rw [hb_def]; split <;> omega
  have hbmod : 3 ^ j * b ≡ F [MOD M] := by
    rw [Nat.ModEq, hb_def]
    split
    · next h0 =>
        rw [h0, Nat.mul_zero, Nat.zero_mod] at hb₀
        rw [Nat.mul_mod_left]
        exact hb₀
    · exact hb₀
  -- checkpoint: the lower window bound, halved
  have hFlo : M * (3 ^ j + 1) ≤ F := by
    have h1 : 2 * (M * (3 ^ j + 1)) ≤ 2 * F := by
      calc 2 * (M * (3 ^ j + 1)) = 2 ^ (k' + 1) * (3 ^ j + 1) := by rw [hpow]; ring
        _ ≤ n := hlo
        _ = 2 * F := by omega
    omega
  have hcbM : 3 ^ j * b ≤ 3 ^ j * M := Nat.mul_le_mul_left _ hb_hi
  have hMc : M * (3 ^ j + 1) = 3 ^ j * M + M := by ring
  have hcb_le : 3 ^ j * b ≤ F := by omega
  -- checkpoint: the quotient `a`
  obtain ⟨a, ha⟩ := (Nat.modEq_iff_dvd' hcb_le).mp hbmod
  have hFa : F = M * a + 3 ^ j * b := by omega
  have ha_pos : 0 < a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · rw [Nat.mul_zero] at hFa; omega
    · exact h
  -- checkpoint: the upper window bound caps `a` at the budget of `2 ^ (k'+1)`
  have hF_hi : F ≤ 2 ^ (2 * k' + 2) := by
    have h1 : 2 * F ≤ 2 * 2 ^ (2 * k' + 2) := by
      calc 2 * F = n := by omega
        _ ≤ 2 ^ (2 * (k' + 1) + 1) := hhi
        _ = 2 * 2 ^ (2 * k' + 2) := by ring
    omega
  have hprod : (2 : ℕ) ^ (2 * k' + 2) = M * 2 ^ (k' + 2) := by
    rw [hM_def, ← pow_add]
    congr 1
    ring
  have ha_hi : a ≤ 2 ^ (k' + 2) := by
    refine Nat.le_of_mul_le_mul_left ?_ hM_pos
    calc M * a ≤ F := by omega
      _ ≤ 2 ^ (2 * k' + 2) := hF_hi
      _ = M * 2 ^ (k' + 2) := hprod
  have ha_budget : a ≤ 1 + ∑ d ∈ ((2 : ℕ) ^ (k' + 1)).divisors, d := by
    rw [one_add_sum_divisors_two_pow]
    exact ha_hi
  -- checkpoint: `2 ^ k < 3 ^ (j+2)` caps `M`, hence `b`, at the budget of `2 * 3 ^ j`
  have hb_budget : b ≤ 1 + ∑ d ∈ ((2 : ℕ) * 3 ^ j).divisors, d := by
    have hσ := two_mul_one_add_sum_divisors_two_mul_three_pow j
    have hMlt : 2 * M < 3 ^ (j + 2) := by rw [← hpow]; exact hj
    omega
  refine ⟨2 ^ (k' + 1) * a, 2 * 3 ^ j * b, ?_, ?_, ?_⟩
  · exact (practical_two_pow (k' + 1)).mul_of_le_one_add_sum_divisors ha_pos ha_budget
  · exact (practical_two_mul_three_pow j).mul_of_le_one_add_sum_divisors hb_pos hb_budget
  · calc 2 ^ (k' + 1) * a + 2 * 3 ^ j * b = 2 * (M * a + 3 ^ j * b) := by rw [hpow]; ring
      _ = 2 * F := by rw [← hFa]
      _ = n := by omega

/-! ## Tiling the even numbers by windows

Pairing each `k ≥ 2` with the `j = j(k)` determined by `3 ^ (j+1) ≤ 2 ^ k < 3 ^ (j+2)`,
the windows `[2 ^ k (3 ^ (j(k)) + 1), 2 ^ (2k+1)]` overlap consecutively and their union
is `[8, ∞)`.  The overlap is the inequality `2 ^ (k+1) (3 ^ (j(k+1)) + 1) ≤ 2 ^ (2k+1)`,
which reduces to `3 ≤ 2 ^ (k-1)`.
-/

/-- For `k ≥ 2` there is a `j` with `3 ^ (j+1) ≤ 2 ^ k < 3 ^ (j+2)`, namely
`j = Nat.log 3 (2 ^ k) - 1`.  The guard `2 ≤ k` is what makes `Nat.log 3 (2 ^ k)`
positive, so that subtracting `1` is not `Nat` truncation. -/
theorem exists_three_pow_bracket {k : ℕ} (hk : 2 ≤ k) :
    ∃ j : ℕ, 3 ^ (j + 1) ≤ 2 ^ k ∧ 2 ^ k < 3 ^ (j + 2) := by
  have h4 : (4 : ℕ) ≤ 2 ^ k := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hL_pos : 0 < Nat.log 3 (2 ^ k) := Nat.log_pos (by norm_num) (by omega)
  refine ⟨Nat.log 3 (2 ^ k) - 1, ?_, ?_⟩
  · have hle : 3 ^ Nat.log 3 (2 ^ k) ≤ 2 ^ k :=
      Nat.pow_log_le_self 3 (by positivity)
    rwa [Nat.sub_add_cancel hL_pos]
  · have hlt : 2 ^ k < 3 ^ (Nat.log 3 (2 ^ k) + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) _
    rwa [show Nat.log 3 (2 ^ k) - 1 + 2 = Nat.log 3 (2 ^ k) + 1 by omega]

/-- **The tiling.**  Every `n ≥ 8` lies in one of the windows: there are `k ≥ 2` and `j`
with `3 ^ (j+1) ≤ 2 ^ k < 3 ^ (j+2)` and `2 ^ k * (3 ^ j + 1) ≤ n ≤ 2 ^ (2k+1)`.

Take `k` least with `n ≤ 2 ^ (2k+1)` among `k ≥ 2`.  At `k = 2` the bracket forces
`3 ^ j = 1` and the lower bound is `8 ≤ n`.  At `k ≥ 3` minimality gives
`2 ^ (2k−1) < n`, and `3 ^ (j+1) ≤ 2 ^ k` together with `3 ≤ 2 ^ (k−1)` gives
`3 ^ j + 1 ≤ 2 ^ (k−1)`, hence `2 ^ k (3 ^ j + 1) ≤ 2 ^ (2k−1) < n`. -/
theorem exists_pow_window {n : ℕ} (hn : 8 ≤ n) :
    ∃ k j : ℕ, 2 ≤ k ∧ 2 ^ k < 3 ^ (j + 2) ∧ 2 ^ k * (3 ^ j + 1) ≤ n ∧
      n ≤ 2 ^ (2 * k + 1) := by
  classical
  have hex : ∃ i : ℕ, n ≤ 2 ^ (2 * (i + 2) + 1) := by
    refine ⟨n, ?_⟩
    calc n ≤ 2 ^ n := Nat.lt_two_pow_self.le
      _ ≤ 2 ^ (2 * (n + 2) + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨j, hj1, hj2⟩ := exists_three_pow_bracket (k := Nat.find hex + 2) (by omega)
  refine ⟨Nat.find hex + 2, j, by omega, hj2, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with hi | hi
  · -- `k = 2`: the bracket forces `3 ^ j = 1`
    rw [hi] at hj1 ⊢
    have hpos : 1 ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
    have hexp : 3 ^ (j + 1) = 3 * 3 ^ j := by ring
    have h4 : (2 : ℕ) ^ (0 + 2) = 4 := by norm_num
    rw [h4] at hj1
    have h3j : 3 ^ j = 1 := by omega
    rw [h4, h3j]
    omega
  · -- `k ≥ 3`: minimality of `Nat.find` gives the previous window's top below `n`
    obtain ⟨i, hi'⟩ : ∃ i, Nat.find hex = i + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hmin : ¬ (n ≤ 2 ^ (2 * (i + 2) + 1)) := Nat.find_min hex (by omega)
    have hA_ge : 3 ≤ 2 ^ (i + 2) := by
      calc (3 : ℕ) ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (i + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hAk : (2 : ℕ) ^ (Nat.find hex + 2) = 2 * 2 ^ (i + 2) := by
      rw [hi', show i + 1 + 2 = (i + 2) + 1 from by omega, pow_succ]
      ring
    have hAA : (2 : ℕ) ^ (2 * (i + 2) + 1) = 2 * 2 ^ (i + 2) * 2 ^ (i + 2) := by
      rw [show 2 * (i + 2) + 1 = (i + 2) + (i + 2) + 1 from by ring, pow_succ, pow_add]
      ring
    -- `3 ^ j + 1 ≤ 2 ^ (k-1)`, from `3 ^ (j+1) ≤ 2 ^ k` and `3 ≤ 2 ^ (k-1)`
    have hstep : 3 ^ j + 1 ≤ 2 ^ (i + 2) := by
      have hexp : 3 ^ (j + 1) = 3 * 3 ^ j := by ring
      rw [hAk] at hj1
      omega
    calc (2 : ℕ) ^ (Nat.find hex + 2) * (3 ^ j + 1)
        = 2 * 2 ^ (i + 2) * (3 ^ j + 1) := by rw [hAk]
      _ ≤ 2 * 2 ^ (i + 2) * 2 ^ (i + 2) := Nat.mul_le_mul_left _ hstep
      _ = 2 ^ (2 * (i + 2) + 1) := hAA.symm
      _ ≤ n := by omega

/-! ## Melfi's theorem -/

/-- **Melfi's theorem** (Melfi, *On two conjectures about practical numbers*, J. Number
Theory 56 (1996) 205–210, Theorem 1; Melfi, *A survey on practical numbers*, Rend. Sem.
Mat. Univ. Pol. Torino 53,4 (1995) 347–359, Theorem 6): every even positive integer is a
sum of two practical numbers.  This settles Margenstern's Goldbach analogue for A005153.

The guard `0 < n` is load-bearing: `0` is even, and practical numbers are positive, so
`0` is not a sum of two of them (witnessed below).  Given `Even n` it is equivalent to
`2 ≤ n`, the form in which A005153 states the theorem.

`n < 8` is settled by `2 = 1 + 1`, `4 = 2 + 2`, `6 = 2 + 4`; `8 ≤ n` goes through the
window tiling `Nat.exists_pow_window` and the covering step
`Nat.exists_practical_add_practical_of_window`. -/
theorem even_eq_practical_add_practical {n : ℕ} (heven : Even n) (hn : 0 < n) :
    ∃ q r : ℕ, q.Practical ∧ r.Practical ∧ q + r = n := by
  rcases lt_or_ge n 8 with hsmall | hbig
  · obtain ⟨F, hF⟩ := heven
    have hcases : n = 2 ∨ n = 4 ∨ n = 6 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact ⟨1, 1, practical_one, practical_one, rfl⟩
    · exact ⟨2, 2, practical_two, practical_two, rfl⟩
    · exact ⟨2, 4, practical_two, by decide, rfl⟩
  · obtain ⟨k, j, hk, hj, hlo, hhi⟩ := exists_pow_window hbig
    exact exists_practical_add_practical_of_window (by omega) hj hlo hhi heven

/-- **Melfi 1996, Theorem 1 / Melfi 1995 survey, Theorem 6** — the paper-theorem alias,
in the `2 ≤ n` phrasing of the A005153 comment: "every even number, beginning with 2, is
the sum of two practical numbers". -/
theorem melfi_thm_6 (n : ℕ) (heven : Even n) (hn : 2 ≤ n) :
    ∃ q r : ℕ, q.Practical ∧ r.Practical ∧ q + r = n :=
  even_eq_practical_add_practical heven (by omega)

end Nat

/-!
## Sharpness of the guards

`0 < n` is required, and the threshold `1 + σ(m)` in Melfi's Lemma 4 is exactly right.
-/

-- `0` is even but is not a sum of two practical numbers: practical numbers are positive.
example : Even 0 ∧ ¬ ∃ q r : ℕ, q.Practical ∧ r.Practical ∧ q + r = 0 := by
  refine ⟨by decide, ?_⟩
  rintro ⟨q, r, hq, hr, hsum⟩
  have hq0 := hq.pos
  have hr0 := hr.pos
  omega

-- Sharpness of `t ≤ 1 + σ(m)` in `Nat.Practical.mul_of_le_one_add_sum_divisors`: at
-- `m = 2`, `t = 5 = 2 + σ(2)` the conclusion fails, since `2 * 5 = 10` is not practical.
example : (2 : ℕ).Practical ∧ (5 : ℕ) = 2 + ∑ d ∈ (2 : ℕ).divisors, d ∧
    ¬ ((2 * 5 : ℕ)).Practical := by decide

/-!
## Satisfiability of the hypothesis-bearing statements

Every theorem above with hypotheses is instantiated jointly at a concrete model.
-/

-- `Nat.Practical.mul_of_le_one_add_sum_divisors` at the threshold: `m = 6`,
-- `t = 13 = 1 + σ(6)`, giving `78 ∈ A005153` without a divisor-set search.
example : (78 : ℕ).Practical := by
  have h : ((6 * 13 : ℕ)).Practical :=
    (by decide : (6 : ℕ).Practical).mul_of_le_one_add_sum_divisors (by norm_num) (by decide)
  norm_num at h
  exact h

-- `Nat.Practical.mul_of_le_two_mul` at `m = 6`, `t = 12 ≤ 2 * 6`.
example : (72 : ℕ).Practical := by
  have h : ((6 * 12 : ℕ)).Practical :=
    (by decide : (6 : ℕ).Practical).mul_of_le_two_mul (by norm_num) (by norm_num)
  norm_num at h
  exact h

-- `Nat.exists_practical_add_practical_of_window` with all five hypotheses at
-- `k = 4`, `j = 1`, `n = 100`: `2⁴ = 16 < 27 = 3³`, `16 * (3 + 1) = 64 ≤ 100 ≤ 512 = 2⁹`.
example : ∃ q r : ℕ, q.Practical ∧ r.Practical ∧ q + r = 100 :=
  Nat.exists_practical_add_practical_of_window (k := 4) (j := 1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by decide)

-- The decomposition the covering step produces at `k = 4`, `j = 1`, read off by hand:
-- `a = 4`, `b = 6`, so `100 = 4 · 2⁴ + 6 · (2 · 3) = 64 + 36`.
example : (64 : ℕ).Practical ∧ (36 : ℕ).Practical ∧ 64 + 36 = 100 := by
  refine ⟨?_, ?_, by norm_num⟩
  · have h := Nat.practical_two_pow 6
    norm_num at h
    exact h
  · have h := (Nat.practical_two_mul_three_pow 2).mul_of_le_two_mul (t := 2)
      (by norm_num) (by norm_num)
    norm_num at h
    exact h

-- `Nat.exists_pow_window` picks the *least* admissible `k`, which at `n = 100` is
-- `k = 3` (as `2 ^ 5 = 32 < 100 ≤ 128 = 2 ^ 7`) with `j = 0`; the covering step then
-- returns `a = 12`, `b = 2`, i.e. `100 = 12 · 2³ + 2 · (2 · 3⁰) = 96 + 4`.  So the two
-- examples exhibit genuinely different decompositions of the same `n`.
example : (96 : ℕ).Practical ∧ (4 : ℕ).Practical ∧ 96 + 4 = 100 := by
  refine ⟨?_, by decide, by norm_num⟩
  have h := (Nat.practical_two_pow 5).mul_of_le_two_mul (t := 3) (by norm_num) (by norm_num)
  norm_num at h
  exact h

-- `Nat.exists_three_pow_bracket` at `k = 4`: `3² = 9 ≤ 16 < 27 = 3³`, so `j = 1`.
example : ∃ j : ℕ, 3 ^ (j + 1) ≤ 2 ^ 4 ∧ 2 ^ 4 < 3 ^ (j + 2) :=
  Nat.exists_three_pow_bracket (by norm_num)

-- `Nat.exists_pow_window` at `n = 100`.
example : ∃ k j : ℕ, 2 ≤ k ∧ 2 ^ k < 3 ^ (j + 2) ∧ 2 ^ k * (3 ^ j + 1) ≤ 100 ∧
    100 ≤ 2 ^ (2 * k + 1) := Nat.exists_pow_window (by norm_num)

-- `Nat.melfi_thm_6` at the first term, `n = 2`.
example : ∃ q r : ℕ, q.Practical ∧ r.Practical ∧ q + r = 2 :=
  Nat.melfi_thm_6 2 (by decide) (by norm_num)

/-!
## Ground-truth checks

The theorem's conclusion, verified independently by the decision procedure of
`Enumerative.Practical` at the first even numbers, matching the A005153 prefix
`1, 2, 4, 6, 8, 12, …`.
-/

example : ∃ q r : ℕ, q.Practical ∧ r.Practical ∧ q + r = 2 :=
  Nat.even_eq_practical_add_practical (by decide) (by norm_num)

example : ∃ q r : ℕ, q.Practical ∧ r.Practical ∧ q + r = 4 :=
  Nat.even_eq_practical_add_practical (by decide) (by norm_num)

example : ∃ q r : ℕ, q.Practical ∧ r.Practical ∧ q + r = 6 :=
  Nat.even_eq_practical_add_practical (by decide) (by norm_num)

example : ∃ q r : ℕ, q.Practical ∧ r.Practical ∧ q + r = 14 :=
  Nat.even_eq_practical_add_practical (by decide) (by norm_num)

-- `14 = 6 + 8` is the decomposition Melfi records by hand for the interval `]3m², (7/2)m²]`
-- at `m = 2`; the decision procedure confirms both summands.
example : (6 : ℕ).Practical ∧ (8 : ℕ).Practical ∧ 6 + 8 = 14 := by decide

-- `2 * 3 ^ j` is practical: the second modulus, at the first four exponents.
example : ((2 : ℕ) * 3 ^ 0).Practical ∧ ((2 : ℕ) * 3 ^ 1).Practical ∧
    ((2 : ℕ) * 3 ^ 2).Practical :=
  ⟨Nat.practical_two_mul_three_pow 0, Nat.practical_two_mul_three_pow 1,
   Nat.practical_two_mul_three_pow 2⟩

example : (2 : ℕ) = 2 * 3 ^ 0 ∧ (6 : ℕ) = 2 * 3 ^ 1 ∧ (18 : ℕ) = 2 * 3 ^ 2 ∧
    (54 : ℕ) = 2 * 3 ^ 3 := by norm_num

-- Budget checks against the σ formulas: `1 + σ(2⁴) = 32` and `1 + σ(2·3¹) = 13`.
example : 1 + ∑ d ∈ ((2 : ℕ) ^ 4).divisors, d = 32 := Nat.one_add_sum_divisors_two_pow 4

example : 2 * (1 + ∑ d ∈ ((2 : ℕ) * 3 ^ 1).divisors, d) + 1 = 27 :=
  Nat.two_mul_one_add_sum_divisors_two_mul_three_pow 1

/-! ## Axiom audit

Every declaration rests on a subset of `{propext, Classical.choice, Quot.sound}`.  The
subset check is the sound `native_decide` detector on this toolchain: a use would
surface as a per-declaration `*._native.native_decide.ax_*` axiom.  There is no
`native_decide` in this file.  In particular nothing here depends on the intended
`sorry` of `Enumerative.Practical` (`Nat.coleman_multiperfect_practical`), which would
surface as `sorryAx`. -/

#print axioms Nat.Practical.mul_of_le_one_add_sum_divisors
#print axioms Nat.Practical.mul_of_le_two_mul
#print axioms Nat.one_add_sum_divisors_two_pow
#print axioms Nat.practical_two_mul_three_pow
#print axioms Nat.two_mul_one_add_sum_divisors_two_mul_three_pow
#print axioms Nat.exists_practical_add_practical_of_window
#print axioms Nat.exists_three_pow_bracket
#print axioms Nat.exists_pow_window
#print axioms Nat.even_eq_practical_add_practical
#print axioms Nat.melfi_thm_6
