/-
# A211417 — Bala: divisibility of (30n)! n! / ((15n)! (10n)! (6n)!) by 3n+1, 5n+1, ...

## OEIS source (retrieved with `oeis show A211417`, 2026-10-21)

```
NAME:     a(n) = (30*n)!*n!/((15*n)!*(10*n)!*(6*n)!).
TERMS:    1,77636318760,53837289804317953893960,...
COMMENT (the conjecture):
  From _Peter Bala_, Aug 28 2025: (Start)
  Conjectures: 7*a(n)/(2*n + 1), a(n)/(3*n + 1), a(n)/(5*n + 1) and
  42*a(n)/((2*n + 1)*(3*n + 1)*(5*n + 1)) are integers for all n
  (checked up to n = 1000).
COMMENT (context):
  It appears that a(n)/(30*n - 1) is integral for all n ... - the conjecture that
  (30*n-1) divides a(n) was proved by an autonomous AI agent, see the Lean file.
  - _Ralf Stephan_, Jun 30 2026
```

## Literature status (triage)

Open: no proof in the entry or in the literature as far as the triage could
tell. The entry marks only the separate claim `(30n - 1) ∣ a(n)` as proved
(AlphaProof Nexus; Adamczewski et al., arXiv:2608.11941, whose table lists only
the `30n - 1` claim for this sequence).

## Result of this module

All four conjectures are proved for every `n`, with no remaining `sorry`:
`three_mul_add_one_dvd`, `five_mul_add_one_dvd`, `two_mul_add_one_dvd` and
`prod_dvd`.

Argument. Put `J = ⌊30n/q⌋`. Legendre's formula gives
`v_p(a(n)) = ∑_{i ≥ 1} slack ⌊30n/p^i⌋`, where
`slack J = J + ⌊J/30⌋ - ⌊J/2⌋ - ⌊J/3⌋ - ⌊J/5⌋ ∈ {0, 1}`. Also
`v_p(∏ (c n + 1)) = ∑_{i ≥ 1} #{c : p^i ∣ c n + 1}`. The comparison is made
level by level.
* For `q ≥ 9`, at most one of `2n+1, 3n+1, 5n+1` is divisible by `q`. If one
  is, then `slack ⌊30n/q⌋ = 1` (`ind_le_slack`).
* For `6n < q ≤ 30n`, no factor is divisible by `q` and the slack is `1`
  (`ind_add_one_le_slack`). There are at least two such powers of `2` and at
  least one power of `3` and of `5`.
* The levels `q ∈ {2, 4, 8, 3, 5, 7}` are checked on residues. The deficit there
  is paid by these compensation levels and by the constants `7` and `42`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A211417FactorialRatio

/-- The OEIS sequence A211417: `a(n) = (30n)! n! / ((15n)! (10n)! (6n)!)`. The
truncating `Nat` division is exact; see `a211417_mul`. -/
def a211417 (n : ℕ) : ℕ :=
  (30 * n).factorial * n.factorial / ((15 * n).factorial * (10 * n).factorial * (6 * n).factorial)

example : a211417 0 = 1 := by decide
example : a211417 1 = 77636318760 := by decide
example : a211417 2 = 53837289804317953893960 := by decide

/-- Per-level Legendre slack. With `j = ⌊30n/q⌋` it equals
`⌊30n/q⌋ + ⌊n/q⌋ - ⌊15n/q⌋ - ⌊10n/q⌋ - ⌊6n/q⌋` (see `level_identity`). The
`Nat` subtraction never truncates, because `j/2 + j/3 + j/5 ≤ j + j/30`. -/
def slack (j : ℕ) : ℕ := j + j / 30 - j / 2 - j / 3 - j / 5

example : slack 0 = 0 ∧ slack 1 = 1 ∧ slack 5 = 1 ∧ slack 6 = 0 ∧ slack 9 = 1 ∧
    slack 29 = 1 ∧ slack 30 = 0 := by decide

/-- The number of `c ∈ cs` (with multiplicity) for which `q ∣ c n + 1`. -/
def ind (cs : List ℕ) (n q : ℕ) : ℕ := (cs.map fun c => if q ∣ c * n + 1 then 1 else 0).sum

example : ind [2, 3, 5] 1 2 = 2 ∧ ind [2, 3, 5] 1 3 = 2 ∧ ind [2, 3, 5] 3 2 = 2 ∧
    ind [3] 5 16 = 1 := by decide

/-- `slack` has period `30`. -/
theorem slack_add (k x : ℕ) : slack (30 * k + x) = slack x := by
  unfold slack; omega

/-- Divisibility of `c n + 1` by `q` depends only on `n mod M` when `q ∣ M`. -/
theorem ind_mod (cs : List ℕ) (n q M : ℕ) (hq : q ∣ M) : ind cs n q = ind cs (n % M) q := by
  have key : ∀ c : ℕ, (q ∣ c * n + 1 ↔ q ∣ c * (n % M) + 1) := by
    intro c
    have hn : c * n + 1 = c * (n % M) + 1 + q * (c * (M / q) * (n / M)) := by
      obtain ⟨d, rfl⟩ := hq
      rcases Nat.eq_zero_or_pos q with h0 | hpos
      · subst h0; simp
      · rw [Nat.mul_div_cancel_left _ hpos]
        conv_lhs => rw [← Nat.mod_add_div n (q * d)]
        ring
    rw [hn]
    exact Nat.dvd_add_left (Dvd.intro _ rfl)
  unfold ind
  congr 1
  apply List.map_congr_left
  intro c _
  simp only [key c]

/-- The level slack `slack (30 n / q)` depends only on `n mod M` when `q ∣ M`. -/
theorem slack_mod (n q M : ℕ) (hq : q ∣ M) :
    slack (30 * n / q) = slack (30 * (n % M) / q) := by
  obtain ⟨d, rfl⟩ := hq
  rcases Nat.eq_zero_or_pos q with h0 | hpos
  · subst h0; simp
  · have h : 30 * n = 30 * (n % (q * d)) + q * (30 * (d * (n / (q * d)))) := by
      conv_lhs => rw [← Nat.mod_add_div n (q * d)]
      ring
    rw [h, Nat.add_mul_div_left _ _ hpos, add_comm, slack_add]

/-- Per-level domination at a large level: if `q ≥ 9` divides `c r + 1` with
`c ∈ {2, 3, 5}` and `r < q`, then the slack at `30 r / q` is positive. -/
theorem one_le_slack_of_dvd (c r q : ℕ) (hc : c = 2 ∨ c = 3 ∨ c = 5) (hq : 9 ≤ q)
    (hr : r < q) (hd : q ∣ c * r + 1) : 1 ≤ slack (30 * r / q) := by
  obtain ⟨s, hs⟩ := hd
  have hq0 : 0 < q := by omega
  have hsc : s < c := by
    by_contra hcon
    have h1 : q * c ≤ q * s := Nat.mul_le_mul_left q (not_lt.mp hcon)
    rcases hc with rfl | rfl | rfl <;> omega
  have hj1 : 30 * r / q * q ≤ 30 * r := Nat.div_mul_le_self _ _
  have hj2 : 30 * r < (30 * r / q + 1) * q := by
    rw [add_mul, one_mul]; exact Nat.lt_div_mul_add hq0
  have hj3 : 30 * r / q < 30 := (Nat.div_lt_iff_lt_mul hq0).2 (by omega)
  generalize 30 * r / q = j at hj1 hj2 hj3 ⊢
  unfold slack
  rcases hc with rfl | rfl | rfl <;> interval_cases s <;> interval_cases j <;> omega

/-- Two of the numbers `2n+1, 3n+1, 5n+1` share no common divisor `q ≥ 4`. -/
theorem not_dvd_two_of_four_le (r q : ℕ) (hq : 4 ≤ q) :
    ¬ (q ∣ 2 * r + 1 ∧ q ∣ 3 * r + 1) ∧ ¬ (q ∣ 2 * r + 1 ∧ q ∣ 5 * r + 1) ∧
      ¬ (q ∣ 3 * r + 1 ∧ q ∣ 5 * r + 1) := by
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun ⟨h1, h2⟩ => ?_, fun ⟨h1, h2⟩ => ?_⟩
  · have h := Nat.dvd_sub (dvd_mul_of_dvd_right h1 3) (dvd_mul_of_dvd_right h2 2)
    rw [show 3 * (2 * r + 1) - 2 * (3 * r + 1) = 1 by omega] at h
    have := Nat.le_of_dvd one_pos h; omega
  · have h := Nat.dvd_sub (dvd_mul_of_dvd_right h1 5) (dvd_mul_of_dvd_right h2 2)
    rw [show 5 * (2 * r + 1) - 2 * (5 * r + 1) = 3 by omega] at h
    have := Nat.le_of_dvd (by norm_num) h; omega
  · have h := Nat.dvd_sub (dvd_mul_of_dvd_right h1 5) (dvd_mul_of_dvd_right h2 3)
    rw [show 5 * (3 * r + 1) - 3 * (5 * r + 1) = 2 by omega] at h
    have := Nat.le_of_dvd (by norm_num) h; omega

/-- Large-level domination: for `q ≥ 9`, the number of `c ∈ {2, 3, 5}` with
`q ∣ c n + 1` is at most the slack at level `q`. -/
theorem ind_le_slack (n q : ℕ) (hq : 9 ≤ q) : ind [2, 3, 5] n q ≤ slack (30 * n / q) := by
  rw [ind_mod _ n q q dvd_rfl, slack_mod n q q dvd_rfl]
  have hr := Nat.mod_lt n (by omega : 0 < q)
  generalize n % q = r at hr ⊢
  obtain ⟨e1, e2, e3⟩ := not_dvd_two_of_four_le r q (by omega)
  have k2 := one_le_slack_of_dvd 2 r q (by norm_num) hq hr
  have k3 := one_le_slack_of_dvd 3 r q (by norm_num) hq hr
  have k5 := one_le_slack_of_dvd 5 r q (by norm_num) hq hr
  simp only [ind, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  split_ifs <;> simp_all

/-- Compensation levels: for `n ≥ 1` and `6 n < q ≤ 30 n`, no `c n + 1` with
`c ∈ {2, 3, 5}` is divisible by `q`, while the slack equals `1`. -/
theorem ind_add_one_le_slack (n q : ℕ) (hn : 1 ≤ n) (h1 : 6 * n < q) (h2 : q ≤ 30 * n) :
    ind [2, 3, 5] n q + 1 ≤ slack (30 * n / q) := by
  have hq0 : 0 < q := by omega
  have hJ1 : 1 ≤ 30 * n / q := (Nat.le_div_iff_mul_le hq0).2 (by omega)
  have hJ2 : 30 * n / q < 5 := (Nat.div_lt_iff_lt_mul hq0).2 (by omega)
  have hnd : ∀ c, c ≤ 5 → ¬ q ∣ c * n + 1 := fun c hc hd =>
    absurd (Nat.le_of_dvd (by omega) hd) (by nlinarith)
  simp only [ind, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    if_neg (hnd 2 (by norm_num)), if_neg (hnd 3 (by norm_num)), if_neg (hnd 5 (by norm_num))]
  generalize 30 * n / q = J at hJ1 hJ2
  unfold slack; omega

/-- Rescaling a floor quotient: `⌊k n / q⌋ = ⌊⌊d k n / q⌋ / d⌋` for `d > 0`. -/
theorem div_scale (k d n q : ℕ) (hd : 0 < d) : k * n / q = d * k * n / q / d := by
  rw [Nat.div_div_eq_div_mul, mul_comm q d, mul_assoc, Nat.mul_div_mul_left _ _ hd]

/-- The Legendre level identity: at every level `q`,
`⌊30n/q⌋ + ⌊n/q⌋ = ⌊15n/q⌋ + ⌊10n/q⌋ + ⌊6n/q⌋ + slack ⌊30n/q⌋`. -/
theorem level_identity (n q : ℕ) :
    30 * n / q + n / q = 15 * n / q + 10 * n / q + 6 * n / q + slack (30 * n / q) := by
  have h15 : 15 * n / q = 30 * n / q / 2 := by
    rw [div_scale 15 2 n q (by norm_num)]
  have h10 : 10 * n / q = 30 * n / q / 3 := by
    rw [div_scale 10 3 n q (by norm_num)]
  have h6 : 6 * n / q = 30 * n / q / 5 := by
    rw [div_scale 6 5 n q (by norm_num)]
  have h1 : n / q = 30 * n / q / 30 := by
    have := div_scale 1 30 n q (by norm_num); simpa using this
  rw [h15, h10, h6, h1]
  generalize 30 * n / q = J
  unfold slack; omega

/-- Legendre-type count for a product of linear factors: if every `c n + 1`
(`c ∈ cs`) is below `p ^ b`, then `v_p(∏ (c n + 1)) = ∑_{1 ≤ i < b} ind cs n (p ^ i)`. -/
theorem factorization_prod_linear (cs : List ℕ) (n p b : ℕ) (hp : p.Prime)
    (hb : ∀ c ∈ cs, c * n + 1 < p ^ b) :
    (cs.map fun c => c * n + 1).prod.factorization p = ∑ i ∈ Finset.Ico 1 b, ind cs n (p ^ i) := by
  induction cs with
  | nil => simp [ind]
  | cons c cs ih =>
    have hne : (cs.map fun c => c * n + 1).prod ≠ 0 := by
      rw [Ne, List.prod_eq_zero_iff]; simp
    rw [List.map_cons, List.prod_cons, Nat.factorization_mul (by omega) hne, Finsupp.add_apply,
      Nat.factorization_eq_card_pow_dvd_of_lt hp (by omega) (hb c (List.mem_cons_self ..)),
      Finset.card_filter, ih fun d hd => hb d (List.mem_cons_of_mem _ hd),
      ← Finset.sum_add_distrib]
    simp [ind]

/-- The divisibility reduction. Suppose that for every prime `p` and every `b`
exceeding `30 n` and `∏ (c n + 1)`, some `e` with `p ^ e ∣ K` satisfies
`∑_{1 ≤ i < b} ind cs n (p^i) ≤ e + ∑_{1 ≤ i < b} slack ⌊30 n / p^i⌋`. Then
`∏ (c n + 1) · (15n)! (10n)! (6n)!` divides `K · (30n)! n!`. -/
theorem mul_dvd_of_sum (cs : List ℕ) (K n : ℕ) (hK : K ≠ 0)
    (h : ∀ p, p.Prime → ∀ b, 30 * n < b → (cs.map fun c => c * n + 1).prod < b →
      ∃ e, p ^ e ∣ K ∧ ∑ i ∈ Finset.Ico 1 b, ind cs n (p ^ i) ≤
        e + ∑ i ∈ Finset.Ico 1 b, slack (30 * n / p ^ i)) :
    (cs.map fun c => c * n + 1).prod *
        ((15 * n).factorial * (10 * n).factorial * (6 * n).factorial) ∣
      K * ((30 * n).factorial * n.factorial) := by
  set m := (cs.map fun c => c * n + 1).prod with hm
  have hm0 : m ≠ 0 := by rw [hm, Ne, List.prod_eq_zero_iff]; simp
  have hF : ∀ x : ℕ, x.factorial ≠ 0 := Nat.factorial_ne_zero
  rw [← Nat.factorization_le_iff_dvd (by simp [hm0, hF]) (by simp [hK, hF]), Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  swap
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  set b := 30 * n + m + 1 with hb
  have hlog : ∀ x, x ≤ 30 * n → Nat.log p x < b := fun x hx =>
    lt_of_le_of_lt (Nat.log_le_self p x) (by omega)
  have hpb : ∀ c ∈ cs, c * n + 1 < p ^ b := by
    intro c hc
    have hle : c * n + 1 ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0)
      (List.dvd_prod (List.mem_map.2 ⟨c, hc, rfl⟩))
    exact lt_of_lt_of_le (by omega : c * n + 1 < b) (Nat.lt_pow_self hp.one_lt).le
  obtain ⟨e, he, hsum⟩ := h p hp b (by omega) (by omega)
  have heK : e ≤ K.factorization p := (hp.pow_dvd_iff_le_factorization hK).1 he
  rw [Nat.factorization_mul hm0 (mul_ne_zero (mul_ne_zero (hF _) (hF _)) (hF _)),
    Nat.factorization_mul hK (mul_ne_zero (hF _) (hF _)),
    Nat.factorization_mul (mul_ne_zero (hF _) (hF _)) (hF _),
    Nat.factorization_mul (hF (15 * n)) (hF _), Nat.factorization_mul (hF (30 * n)) (hF _)]
  simp only [Finsupp.add_apply]
  rw [hm, factorization_prod_linear cs n p b hp hpb,
    Nat.factorization_factorial hp (hlog _ (by omega)),
    Nat.factorization_factorial hp (hlog _ (by omega)),
    Nat.factorization_factorial hp (hlog _ (by omega)),
    Nat.factorization_factorial hp (hlog _ le_rfl),
    Nat.factorization_factorial hp (hlog _ (by omega))]
  have hlev : ∑ i ∈ Finset.Ico 1 b, (30 * n / p ^ i + n / p ^ i) =
      ∑ i ∈ Finset.Ico 1 b, (15 * n / p ^ i + 10 * n / p ^ i + 6 * n / p ^ i) +
        ∑ i ∈ Finset.Ico 1 b, slack (30 * n / p ^ i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => level_identity n (p ^ i)
  simp only [Finset.sum_add_distrib] at hlev ⊢
  omega

/-- Integrality of A211417: `(15n)! (10n)! (6n)!` divides `(30n)! n!`. -/
theorem denom_dvd_numer (n : ℕ) :
    (15 * n).factorial * (10 * n).factorial * (6 * n).factorial ∣
      (30 * n).factorial * n.factorial := by
  have h := mul_dvd_of_sum [] 1 n one_ne_zero fun p _ b _ _ => ⟨0, by simp, by simp [ind]⟩
  simpa using h

/-- The truncating division in `a211417` is exact. -/
theorem a211417_mul (n : ℕ) :
    a211417 n * ((15 * n).factorial * (10 * n).factorial * (6 * n).factorial) =
      (30 * n).factorial * n.factorial :=
  Nat.div_mul_cancel (denom_dvd_numer n)

/-- Prime case split used in the main argument. -/
theorem prime_cases (p : ℕ) (hp : p.Prime) : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ 11 ≤ p := by
  rcases Nat.lt_or_ge p 11 with h | h
  · have := hp.two_le
    interval_cases p <;> first | omega | (exfalso; norm_num at hp)
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- The level `i₀ = ⌊log_p (6n)⌋ + 1` satisfies `6n < p^i₀ ≤ 6pn`. -/
theorem comp_level (p n : ℕ) (hp : 1 < p) (hn : 1 ≤ n) :
    6 * n < p ^ (Nat.log p (6 * n) + 1) ∧ p ^ (Nat.log p (6 * n) + 1) ≤ p * (6 * n) := by
  refine ⟨Nat.lt_pow_succ_log_self hp _, ?_⟩
  rw [pow_succ, mul_comm]
  exact Nat.mul_le_mul_left p (Nat.pow_log_le_self p (by omega))

/-- A level `p^i ≤ 30n` lies below any `b > 30n`. -/
theorem lt_of_pow_le (p i n b : ℕ) (hp : 1 < p) (h : p ^ i ≤ 30 * n) (hb : 30 * n < b) : i < b :=
  (Nat.le_log_of_pow_le hp h).trans_lt ((Nat.log_le_self _ _).trans_lt hb)

/-- Summation of the per-level bounds at a fixed prime `p`. Levels `i ≥ L` satisfy
`p ^ i ≥ 9`, where the large-level domination holds; the levels in `T` are
compensation levels with `6n < p^i ≤ 30n`; the small levels `1 ≤ i < L` are
controlled by `hsmall`. -/
theorem sum_ind_le (cs : List ℕ) (n p b L e : ℕ) (hcs : ∀ q, ind cs n q ≤ ind [2, 3, 5] n q)
    (hn : 1 ≤ n) (hL : ∀ i, L ≤ i → 9 ≤ p ^ i) (h1L : 1 ≤ L) (hLb : L ≤ b) (T : Finset ℕ)
    (hT : ∀ i ∈ T, L ≤ i ∧ i < b ∧ 6 * n < p ^ i ∧ p ^ i ≤ 30 * n)
    (hsmall : ∑ i ∈ Finset.Ico 1 L, ind cs n (p ^ i) ≤
      e + T.card + ∑ i ∈ Finset.Ico 1 L, slack (30 * n / p ^ i)) :
    ∑ i ∈ Finset.Ico 1 b, ind cs n (p ^ i) ≤ e + ∑ i ∈ Finset.Ico 1 b, slack (30 * n / p ^ i) := by
  rw [← Finset.sum_Ico_consecutive _ h1L hLb, ← Finset.sum_Ico_consecutive _ h1L hLb]
  have hTsub : T ⊆ Finset.Ico L b := fun i hi =>
    Finset.mem_Ico.2 ⟨(hT i hi).1, (hT i hi).2.1⟩
  have hcard : T.card = ∑ i ∈ Finset.Ico L b, if i ∈ T then 1 else 0 := by
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hTsub, Nat.cast_id]
  have hbig : ∑ i ∈ Finset.Ico L b, ind cs n (p ^ i) + T.card ≤
      ∑ i ∈ Finset.Ico L b, slack (30 * n / p ^ i) := by
    rw [hcard, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i hi => ?_
    split_ifs with hiT
    · obtain ⟨-, -, h1, h2⟩ := hT i hiT
      exact (Nat.add_le_add_right (hcs _) 1).trans (ind_add_one_le_slack n _ hn h1 h2)
    · simpa using (hcs _).trans (ind_le_slack n _ (hL i (Finset.mem_Ico.1 hi).1))
  omega

/-- The general divisibility criterion. Let `cs` index factors among `2n+1, 3n+1,
5n+1`, let `p ^ eₚ ∣ K` for `p ∈ {2, 3, 5, 7}`, and assume the small-level
residue bounds `s2, s3, s5, s7`. If the claim holds for `n < 2`, then
`∏_{c ∈ cs} (c n + 1)` divides `K · a(n)` for every `n`. -/
theorem prod_dvd_of_small (cs : List ℕ) (K : ℕ) (hK : K ≠ 0)
    (hcs : ∀ n q, ind cs n q ≤ ind [2, 3, 5] n q)
    (e2 e3 e5 e7 : ℕ) (h2K : 2 ^ e2 ∣ K) (h3K : 3 ^ e3 ∣ K) (h5K : 5 ^ e5 ∣ K) (h7K : 7 ^ e7 ∣ K)
    (s2 : ∀ n, ind cs n 2 + ind cs n 4 + ind cs n 8 ≤
      e2 + 2 + (slack (30 * n / 2) + slack (30 * n / 4) + slack (30 * n / 8)))
    (s3 : ∀ n, ind cs n 3 ≤ e3 + 1 + slack (30 * n / 3))
    (s5 : ∀ n, ind cs n 5 ≤ e5 + 1 + slack (30 * n / 5))
    (s7 : ∀ n, ind cs n 7 ≤ e7 + 0 + slack (30 * n / 7))
    (h01 : ∀ n < 2, (cs.map fun c => c * n + 1).prod ∣ K * a211417 n) (n : ℕ) :
    (cs.map fun c => c * n + 1).prod ∣ K * a211417 n := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · exact h01 n hn
  have hD : 0 < (15 * n).factorial * (10 * n).factorial * (6 * n).factorial := by positivity
  apply Nat.dvd_of_mul_dvd_mul_right hD
  rw [mul_assoc K (a211417 n), a211417_mul]
  apply mul_dvd_of_sum cs K n hK
  intro p hp b hb _
  have hp1 := hp.one_lt
  have hcomp := comp_level p n hp1 (by omega)
  set i₀ := Nat.log p (6 * n) + 1 with hi₀
  -- `i₀` is at least `L` whenever `p ^ (L - 1) ≤ 6 n`
  have hi₀L : ∀ L, p ^ (L - 1) ≤ 6 * n → L ≤ i₀ := fun L hL => by
    by_contra hcon
    have := Nat.pow_le_pow_right (by omega : 1 ≤ p) (by omega : i₀ ≤ L - 1)
    omega
  rcases prime_cases p hp with rfl | rfl | rfl | rfl | h11
  · refine ⟨e2, h2K, sum_ind_le cs n 2 b 4 e2 (hcs n) (by omega) (fun i hi => ?_) (by omega)
      (by omega) {i₀, i₀ + 1} ?_ ?_⟩
    · exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hi)
    · have hL := hi₀L 4 (by rw [show 2 ^ (4 - 1) = 8 by norm_num]; omega)
      intro i hi
      rw [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact ⟨hL, lt_of_pow_le 2 _ n b hp1 (by omega) hb, hcomp.1, by omega⟩
      · rw [pow_succ]
        exact ⟨by omega, lt_of_pow_le 2 _ n b hp1 (by rw [pow_succ]; omega) hb, by omega,
          by omega⟩
    · rw [Finset.card_pair (by omega)]
      simpa [Finset.sum_Ico_succ_top, add_assoc] using s2 n
  · refine ⟨e3, h3K, sum_ind_le cs n 3 b 2 e3 (hcs n) (by omega) (fun i hi => ?_) (by omega)
      (by omega) {i₀} ?_ ?_⟩
    · exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hi)
    · intro i hi
      rw [Finset.mem_singleton] at hi
      subst hi
      exact ⟨hi₀L 2 (by rw [show 3 ^ (2 - 1) = 3 by norm_num]; omega),
        lt_of_pow_le 3 _ n b hp1 (by omega) hb, hcomp.1,
        by omega⟩
    · simpa [Finset.sum_Ico_succ_top] using s3 n
  · refine ⟨e5, h5K, sum_ind_le cs n 5 b 2 e5 (hcs n) (by omega) (fun i hi => ?_) (by omega)
      (by omega) {i₀} ?_ ?_⟩
    · exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hi)
    · intro i hi
      rw [Finset.mem_singleton] at hi
      subst hi
      exact ⟨hi₀L 2 (by rw [show 5 ^ (2 - 1) = 5 by norm_num]; omega),
        lt_of_pow_le 5 _ n b hp1 (by omega) hb, hcomp.1,
        by omega⟩
    · simpa [Finset.sum_Ico_succ_top] using s5 n
  · refine ⟨e7, h7K, sum_ind_le cs n 7 b 2 e7 (hcs n) (by omega) (fun i hi => ?_) (by omega)
      (by omega) ∅ (by simp) ?_⟩
    · exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hi)
    · simpa [Finset.sum_Ico_succ_top] using s7 n
  · refine ⟨0, by simp, sum_ind_le cs n p b 1 0 (hcs n) (by omega) (fun i hi => ?_) le_rfl
      (by omega) ∅ (by simp) (by simp)⟩
    exact le_trans (by omega) (Nat.le_self_pow (by omega) p)

/-- The `p = 2` small-level bound follows from its check on residues mod `8`. -/
theorem small_two (cs : List ℕ) (e : ℕ)
    (h : ∀ r < 8, ind cs r 2 + ind cs r 4 + ind cs r 8 ≤
      e + 2 + (slack (30 * r / 2) + slack (30 * r / 4) + slack (30 * r / 8))) (n : ℕ) :
    ind cs n 2 + ind cs n 4 + ind cs n 8 ≤
      e + 2 + (slack (30 * n / 2) + slack (30 * n / 4) + slack (30 * n / 8)) := by
  rw [ind_mod _ n 2 8 (by norm_num), ind_mod _ n 4 8 (by norm_num), ind_mod _ n 8 8 (by norm_num),
    slack_mod n 2 8 (by norm_num), slack_mod n 4 8 (by norm_num), slack_mod n 8 8 (by norm_num)]
  exact h _ (Nat.mod_lt n (by norm_num))

/-- A single-level bound follows from its check on residues mod `q`. -/
theorem small_one (cs : List ℕ) (q e k : ℕ) (hq : 0 < q)
    (h : ∀ r < q, ind cs r q ≤ e + k + slack (30 * r / q)) (n : ℕ) :
    ind cs n q ≤ e + k + slack (30 * n / q) := by
  rw [ind_mod _ n q q dvd_rfl, slack_mod n q q dvd_rfl]
  exact h _ (Nat.mod_lt n hq)

/-- A single factor `c n + 1` with `c ∈ {2, 3, 5}` is counted at most as often as
in the full product. -/
theorem ind_single_le (c : ℕ) (hc : c = 2 ∨ c = 3 ∨ c = 5) (n q : ℕ) :
    ind [c] n q ≤ ind [2, 3, 5] n q := by
  simp only [ind, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rcases hc with rfl | rfl | rfl <;> split_ifs <;> omega

/-- **Bala's conjecture (i) for A211417 (Aug 28 2025).** `3n + 1` divides
`a(n) = (30n)! n! / ((15n)! (10n)! (6n)!)` for every `n`. -/
theorem three_mul_add_one_dvd (n : ℕ) : 3 * n + 1 ∣ a211417 n := by
  have h := prod_dvd_of_small [3] 1 one_ne_zero (ind_single_le 3 (by norm_num))
    0 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (small_two [3] 0 (by decide)) (small_one [3] 3 0 1 (by norm_num) (by decide))
    (small_one [3] 5 0 1 (by norm_num) (by decide)) (small_one [3] 7 0 0 (by norm_num) (by decide))
    (by decide) n
  simpa using h

/-- **Bala's conjecture (ii) for A211417 (Aug 28 2025).** `5n + 1` divides
`a(n) = (30n)! n! / ((15n)! (10n)! (6n)!)` for every `n`. -/
theorem five_mul_add_one_dvd (n : ℕ) : 5 * n + 1 ∣ a211417 n := by
  have h := prod_dvd_of_small [5] 1 one_ne_zero (ind_single_le 5 (by norm_num))
    0 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (small_two [5] 0 (by decide)) (small_one [5] 3 0 1 (by norm_num) (by decide))
    (small_one [5] 5 0 1 (by norm_num) (by decide)) (small_one [5] 7 0 0 (by norm_num) (by decide))
    (by decide) n
  simpa using h

/-- **Bala's conjecture (iii) for A211417 (Aug 28 2025).** `2n + 1` divides
`7 a(n)`, i.e. `7 a(n) / (2n + 1)` is an integer, for every `n`. -/
theorem two_mul_add_one_dvd (n : ℕ) : 2 * n + 1 ∣ 7 * a211417 n := by
  have h := prod_dvd_of_small [2] 7 (by norm_num) (ind_single_le 2 (by norm_num))
    0 0 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (small_two [2] 0 (by decide)) (small_one [2] 3 0 1 (by norm_num) (by decide))
    (small_one [2] 5 0 1 (by norm_num) (by decide)) (small_one [2] 7 1 0 (by norm_num) (by decide))
    (by decide) n
  simpa using h

/-- **Bala's conjecture (iv) for A211417 (Aug 28 2025).** `(2n + 1)(3n + 1)(5n + 1)`
divides `42 a(n)` for every `n`. -/
theorem prod_dvd (n : ℕ) : (2 * n + 1) * (3 * n + 1) * (5 * n + 1) ∣ 42 * a211417 n := by
  have h := prod_dvd_of_small [2, 3, 5] 42 (by norm_num) (fun _ _ => le_rfl)
    1 1 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (small_two [2, 3, 5] 1 (by decide)) (small_one [2, 3, 5] 3 1 1 (by norm_num) (by decide))
    (small_one [2, 3, 5] 5 0 1 (by norm_num) (by decide))
    (small_one [2, 3, 5] 7 1 0 (by norm_num) (by decide))
    (by decide) n
  simpa [mul_assoc] using h

end Candidates.A211417FactorialRatio
