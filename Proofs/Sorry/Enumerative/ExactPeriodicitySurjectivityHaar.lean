/-
# Restarting Josephus process: endpoint criteria, reflection, prime transitions,
# and the nearest-internal case of endpoint dominance

## Source

arXiv 2608.09092v1, "Exact Periodicity, Surjectivity, and a Haar Limit Law for a
Restarting Josephus Process" (retrieved 2026-10-21).

* Definition (Section 2): the restarting Josephus process on `1, …, n` with
  parameter `q` deletes, while the list has length `k ≥ 2`, its entry of rank
  `1 + (q mod k)` and restarts counting at the leftmost survivor; `F_n(q)` is the
  initial position of the last survivor.  `L_n = lcm(1, …, n)`.
* Lemma 2.1 (Fundamental recurrence): `F_1(q) = 1`,
  `F_k(q) = F_{k-1}(q) + 1_{q mod k < F_{k-1}(q)}` for `k ≥ 2`.
* Prop. 2.3: `F_n(q + L_n) = F_n(q)`, `F_n(q) + F_n(L_n - 1 - q) = n + 1`
  for `0 ≤ q < L_n`, and `F_n(q) = 1 ⟺ gcd(q, L_n) = 1`.
* Cor. 2.5: `N_{n,j} = N_{n,n+1-j}` and `N_{n,1} = N_{n,n} = φ(L_n)`, where
  `N_{n,j} = #{0 ≤ q < L_n : F_n(q) = j}`.
* Section 6, Open Problem 6.1 (verbatim): "For every `n ≥ 4` and every `1 < j < n`,
  is it true that `N_{n,j} < φ(L_n)`?"
* Prop. 6.2 (Prime transition, verbatim): "Let `p` be prime.  With the convention
  `N_{p-1,0} = N_{p-1,p} = 0`, one has
  `N_{p,j} = (p-j) N_{p-1,j} + (j-1) N_{p-1,j-1}` `(1 ≤ j ≤ p)`."
* Cor. 6.3 (verbatim): "Let `p ≥ 5` be prime.  If endpoint dominance holds at
  level `p-1`, then it holds at level `p`."
* Theorem 6.4 (verbatim): "For every `n ≥ 4`, `N_{n,2} = N_{n,n-1} < φ(L_n)`."
* Cor. 6.5 (verbatim): "If Problem 6.1 is false and `n` is the least level at
  which it fails, then `n` is composite and the offending position satisfies
  `3 ≤ j ≤ n - 2`."

## Status

The elementary results above (Lemma 2.1, Prop. 2.3 endpoint and reflection parts,
Cor. 2.5 endpoint counts and symmetry, Prop. 6.2, Cor. 6.3, Theorem 6.4,
Cor. 6.5) are PROVED in the paper and are proved here.  Problem 6.1 itself is
OPEN (the paper checks it by computer for `n ≤ 49`); it is stated below as
`endpoint_dominance` with `sorry` and is not a target.  The surjectivity theorem,
exact-period theorem and Haar limit law of Sections 3-5 are not formalized here.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.ExactPeriodicitySurjectivityHaar

open Finset

/-- The restarting Josephus survivor `F_n(q)` through the fundamental recurrence
(arXiv 2608.09092, Lemma 2.1): `F_1(q) = 1` and
`F_k(q) = F_{k-1}(q) + [q mod k < F_{k-1}(q)]` for `k ≥ 2`.  The value at `n = 0`
is a junk value `1`; every statement below assumes `1 ≤ n`.  The agreement with
the deletion process itself is `josephus_eq_F`. -/
def F (q : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | (k + 2) => if q % (k + 2) < F q (k + 1) then F q (k + 1) + 1 else F q (k + 1)

/-- `L_n = lcm(1, …, n)`, with `L_0 = L_1 = 1`. -/
def L (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm id

/-- The fiber size `N_{n,j} = #{0 ≤ q < L_n : F_n(q) = j}`. -/
def N (n j : ℕ) : ℕ := ((Finset.range (L n)).filter (fun q => F q n = j)).card

/-! ## Ground truth checks (values from arXiv 2608.09092 and a direct enumeration) -/

example : L 4 = 12 := by decide
example : L 8 = 840 := by decide
/-- The paper's table `(F_4(0), …, F_4(11))` from the proof of Theorem 6.4. -/
example : (List.range 12).map (fun q => F q 4) = [4, 1, 2, 2, 4, 1, 4, 1, 3, 3, 4, 1] := by
  decide
/-- `(N_{3,1}, N_{3,2}, N_{3,3}) = (2, 2, 2)`, showing `n ≥ 4` is needed in Problem 6.1. -/
example : (List.range' 1 3).map (N 3) = [2, 2, 2] := by decide
example : (List.range' 1 4).map (N 4) = [4, 2, 2, 4] := by decide
example : (List.range' 1 5).map (N 5) = [16, 10, 8, 10, 16] := by decide
example : (List.range' 1 7).map (N 7) = [96, 56, 40, 36, 40, 56, 96] := by decide

/-- The fundamental recurrence at every level `k + 1` with `1 ≤ k`. -/
theorem F_succ (q k : ℕ) (hk : 1 ≤ k) :
    F q (k + 1) = if q % (k + 1) < F q k then F q k + 1 else F q k := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rfl

/-- The survivor label is at least `1`. -/
theorem one_le_F (q n : ℕ) : 1 ≤ F q n := by
  induction n with
  | zero => simp [F]
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [F]
    · rw [F_succ q k hk]; split_ifs <;> omega

/-- The survivor label is at most `n` (Lemma 2.1). -/
theorem F_le (q n : ℕ) (hn : 1 ≤ n) : F q n ≤ n := by
  induction n, hn using Nat.le_induction with
  | base => simp [F]
  | succ k hk ih => rw [F_succ q k hk]; split_ifs <;> omega

/-- `F_n(q)` depends only on the residues `q mod k` for `2 ≤ k ≤ n`. -/
theorem F_congr (q q' n : ℕ) (h : ∀ k, 2 ≤ k → k ≤ n → q % k = q' % k) : F q n = F q' n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rfl
    · rw [F_succ q k hk, F_succ q' k hk, ih (fun i hi hik => h i hi (by omega)),
        h (k + 1) (by omega) le_rfl]

/-- `L_{n+1} = lcm(L_n, n + 1)`. -/
theorem L_succ (n : ℕ) : L (n + 1) = Nat.lcm (L n) (n + 1) := by
  unfold L
  have hI : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hI, Finset.lcm_insert, lcm_eq_nat_lcm, Nat.lcm_comm]
  rfl

/-- Every `1 ≤ k ≤ n` divides `L_n`. -/
theorem dvd_L {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) : k ∣ L n :=
  Finset.dvd_lcm (s := Finset.Icc 1 n) (f := id) (Finset.mem_Icc.mpr ⟨hk, hkn⟩)

/-- `L_n` divides `n!`. -/
theorem L_dvd_factorial (n : ℕ) : L n ∣ n.factorial :=
  Finset.lcm_dvd fun _ hk =>
    Nat.dvd_factorial (Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1)
      (Finset.mem_Icc.mp hk).2

/-- `L_n` is positive. -/
theorem L_pos (n : ℕ) : 0 < L n := Nat.pos_of_dvd_of_pos (L_dvd_factorial n) (Nat.factorial_pos n)

/-- `L_m ∣ L_n` whenever `m ≤ n`. -/
theorem L_dvd_L {m n : ℕ} (h : m ≤ n) : L m ∣ L n :=
  Finset.lcm_dvd fun _ hk => dvd_L (Finset.mem_Icc.mp hk).1 ((Finset.mem_Icc.mp hk).2.trans h)

/-- `gcd(q, L_n) = 1` iff no `2 ≤ k ≤ n` divides `q`. -/
theorem coprime_L_iff (q n : ℕ) :
    q.Coprime (L n) ↔ ∀ k, 2 ≤ k → k ≤ n → ¬ k ∣ q := by
  constructor
  · intro hcop k hk hkn hkq
    have h1 : k ∣ Nat.gcd q (L n) := Nat.dvd_gcd hkq (dvd_L (by omega) hkn)
    rw [hcop.gcd_eq_one, Nat.dvd_one] at h1
    omega
  · intro h
    apply Nat.coprime_of_dvd
    intro r hr hrq hrL
    have hrn : r ≤ n := (Nat.Prime.dvd_factorial hr).mp (hrL.trans (L_dvd_factorial n))
    exact h r hr.two_le hrn hrq

/-- `F_n(q) = 1` iff no `2 ≤ k ≤ n` divides `q` (no increment ever occurs). -/
theorem F_eq_one_iff_forall (q n : ℕ) (hn : 1 ≤ n) :
    F q n = 1 ↔ ∀ k, 2 ≤ k → k ≤ n → ¬ k ∣ q := by
  induction n, hn using Nat.le_induction with
  | base =>
    simp only [F, true_iff]
    intro k hk hk1 _; omega
  | succ n hn ih =>
    rw [F_succ q n hn]
    have h1 := one_le_F q n
    constructor
    · intro h k hk hkn hkq
      have hFn : F q n = 1 := by split_ifs at h <;> omega
      rcases Nat.lt_or_ge k (n + 1) with hlt | hge
      · exact ih.mp hFn k hk (by omega) hkq
      · have hk' : k = n + 1 := by omega
        subst hk'
        rw [Nat.mod_eq_zero_of_dvd hkq, hFn] at h
        simp at h
    · intro h
      have hFn : F q n = 1 := ih.mpr fun k hk hkn => h k hk (by omega)
      have hnd : ¬ (n + 1) ∣ q := h (n + 1) (by omega) le_rfl
      have hmod : q % (n + 1) ≠ 0 := fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0)
      rw [hFn, if_neg (by omega)]

/-- Left endpoint criterion (arXiv 2608.09092, Prop. 2.3, eq. (2.4)):
for `n ≥ 1`, `F_n(q) = 1 ⟺ gcd(q, L_n) = 1`. -/
theorem F_eq_one_iff (q n : ℕ) (hn : 1 ≤ n) : F q n = 1 ↔ q.Coprime (L n) := by
  rw [F_eq_one_iff_forall q n hn, coprime_L_iff]

/-- Endpoint count (Cor. 2.5): `N_{n,1} = φ(L_n)` for `n ≥ 1`. -/
theorem N_one (n : ℕ) (hn : 1 ≤ n) : N n 1 = Nat.totient (L n) := by
  unfold N
  rw [Nat.totient]
  congr 1
  apply Finset.filter_congr
  intro q _
  rw [F_eq_one_iff q n hn, Nat.coprime_comm]

/-- Periodicity: if `L_n ∣ M` then `F_n(q mod M) = F_n(q)`. -/
theorem F_mod (q n M : ℕ) (hM : L n ∣ M) : F (q % M) n = F q n :=
  F_congr _ _ n fun k hk hkn => Nat.mod_mod_of_dvd q ((dvd_L (by omega) hkn).trans hM)

/-- Counting an `M`-periodic predicate over `k` full periods. -/
theorem card_filter_range_mul (P : ℕ → Prop) [DecidablePred P] (M : ℕ)
    (hP : ∀ q, P (q + M) ↔ P q) (k : ℕ) :
    #{q ∈ range (k * M) | P q} = k * #{q ∈ range M | P q} := by
  have hshift : ∀ k x, P (k * M + x) ↔ P x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => intro x; rw [Nat.succ_mul, Nat.add_right_comm, hP, ih]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.count_eq_card_filter_range, Nat.succ_mul, Nat.count_add,
      Nat.count_eq_card_filter_range, ih, Nat.count_eq_card_filter_range, Nat.succ_mul]
    congr 1
    exact congrArg Finset.card (Finset.filter_congr fun x _ => hshift k x)

/-- Exact CRT counting: for coprime `M, p`, the map `q ↦ (q mod M, q mod p)` is a
bijection `[0, Mp) → [0, M) × [0, p)`, so counts of predicates of the two residues
split as a double sum. -/
theorem card_filter_range_crt (M p : ℕ) (hcop : M.Coprime p) (g : ℕ → ℕ → ℕ) (j : ℕ) :
    #{q ∈ range (M * p) | g (q % M) (q % p) = j} =
      ∑ a ∈ range M, #{r ∈ range p | g a r = j} := by
  have hinj : ∀ a ∈ range (M * p), ∀ b ∈ range (M * p),
      (a % M, a % p) = (b % M, b % p) → a = b := by
    intro a ha b hb hab
    simp only [Prod.mk.injEq] at hab
    have hmod : a ≡ b [MOD M * p] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp hab
    rw [Finset.mem_range] at ha hb
    unfold Nat.ModEq at hmod
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hmod
  have himage : (range (M * p)).image (fun q => (q % M, q % p)) = range M ×ˢ range p := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_range] at hq
      have hM : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
      have hp : 0 < p := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt q hM),
        Finset.mem_range.mpr (Nat.mod_lt q hp)⟩
    · rw [Finset.card_image_of_injOn (fun a ha b hb hab => hinj a ha b hb hab),
        Finset.card_product, Finset.card_range, Finset.card_range, Finset.card_range]
  have hcard : #{q ∈ range (M * p) | g (q % M) (q % p) = j} =
      #{x ∈ range M ×ˢ range p | g x.1 x.2 = j} := by
    apply Finset.card_bij (fun q _ => (q % M, q % p))
    · intro q hq
      rw [Finset.mem_filter] at hq ⊢
      refine ⟨?_, hq.2⟩
      rw [← himage]
      exact Finset.mem_image_of_mem _ hq.1
    · intro a ha b hb hab
      exact hinj a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
    · intro x hx
      rw [Finset.mem_filter, ← himage] at hx
      obtain ⟨q, hq, hqx⟩ := Finset.mem_image.mp hx.1
      refine ⟨q, Finset.mem_filter.mpr ⟨hq, ?_⟩, hqx⟩
      subst hqx
      exact hx.2
  rw [hcard, Finset.card_filter, Finset.sum_product]
  simp only [Finset.card_filter]

/-- One prime-level step: for an old state `s`, the number of residues `r < p`
whose new state `s + [r < s]` equals `j`. -/
theorem card_step (p s j : ℕ) (hj : 1 ≤ j) (hjp : j ≤ p) :
    #{r ∈ range p | (if r < s then s + 1 else s) = j} =
      (if s = j then p - j else 0) + (if s + 1 = j then j - 1 else 0) := by
  by_cases hsj : s = j
  · subst hsj
    rw [if_pos rfl, if_neg (by omega)]
    have : #{r ∈ range p | (if r < s then s + 1 else s) = s} = #(Finset.Ico s p) := by
      congr 1
      ext r
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      split_ifs <;> omega
    rw [this, Nat.card_Ico, Nat.add_zero]
  · rw [if_neg hsj]
    by_cases hsj' : s + 1 = j
    · rw [if_pos hsj', Nat.zero_add]
      have : #{r ∈ range p | (if r < s then s + 1 else s) = j} = #(Finset.range s) := by
        congr 1
        ext r
        simp only [Finset.mem_filter, Finset.mem_range]
        split_ifs <;> omega
      rw [this, Finset.card_range]
      omega
    · rw [if_neg hsj', Nat.add_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro r _
      split_ifs <;> omega

/-- A prime `p` does not divide `L_{p-1}`. -/
theorem not_dvd_L_pred {p : ℕ} (hp : p.Prime) : ¬ p ∣ L (p - 1) := by
  intro h
  have := (Nat.Prime.dvd_factorial hp).mp (h.trans (L_dvd_factorial (p - 1)))
  have := hp.two_le
  omega

/-- `L_p = L_{p-1} · p` for a prime `p`. -/
theorem L_prime {p : ℕ} (hp : p.Prime) : L p = L (p - 1) * p := by
  have hp1 : p - 1 + 1 = p := by have := hp.two_le; omega
  have hcop : (L (p - 1)).Coprime p :=
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr (not_dvd_L_pred hp)))
  conv_lhs => rw [← hp1, L_succ, hp1]
  exact hcop.lcm_eq_mul

/-- A sum of a constant over a filter, as a product with the filter's size. -/
theorem sum_ite_eq_card_mul (s : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] (c : ℕ) :
    ∑ a ∈ s, (if P a then c else 0) = c * #{a ∈ s | P a} := by
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- Prime transition (arXiv 2608.09092, Prop. 6.2): for a prime `p` and
`1 ≤ j ≤ p`, `N_{p,j} = (p - j) N_{p-1,j} + (j - 1) N_{p-1,j-1}`.  (The paper's
convention `N_{p-1,0} = N_{p-1,p} = 0` is automatic: both fibers are empty, and
their coefficients vanish anyway.) -/
theorem N_prime_transition (p : ℕ) (hp : p.Prime) (j : ℕ) (hj : 1 ≤ j) (hjp : j ≤ p) :
    N p j = (p - j) * N (p - 1) j + (j - 1) * N (p - 1) (j - 1) := by
  have hp2 := hp.two_le
  have hp1 : p - 1 + 1 = p := by omega
  have hcop : (L (p - 1)).Coprime p :=
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr (not_dvd_L_pred hp)))
  set M := L (p - 1) with hM
  have hF : ∀ q, F q p =
      if q % p < F (q % M) (p - 1) then F (q % M) (p - 1) + 1 else F (q % M) (p - 1) := by
    intro q
    rw [F_mod q (p - 1) M dvd_rfl]
    conv_lhs => rw [← hp1, F_succ q (p - 1) (by omega)]
    rw [hp1]
  unfold N
  rw [L_prime hp, ← hM]
  have hstep : #{q ∈ range (M * p) | F q p = j} =
      #{q ∈ range (M * p) | (fun a r => if r < F a (p - 1) then F a (p - 1) + 1
        else F a (p - 1)) (q % M) (q % p) = j} :=
    congrArg Finset.card (Finset.filter_congr fun q _ => by rw [hF q])
  refine hstep.trans ((card_filter_range_crt M p hcop (fun a r => if r < F a (p - 1) then
    F a (p - 1) + 1 else F a (p - 1)) j).trans ?_)
  have hinner : ∀ a ∈ range M, #{r ∈ range p | (if r < F a (p - 1) then F a (p - 1) + 1
        else F a (p - 1)) = j} =
      (if F a (p - 1) = j then p - j else 0) + (if F a (p - 1) = j - 1 then j - 1 else 0) := by
    intro a _
    rw [card_step p (F a (p - 1)) j hj hjp]
    congr 1
    exact if_congr (by omega) rfl rfl
  rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, sum_ite_eq_card_mul,
    sum_ite_eq_card_mul]

/-- Counting a level-`n` fiber over one `L_{n+1}`-block gives `ρ_{n+1} N_{n,j}`
with `ρ_{n+1} = L_{n+1} / L_n`. -/
theorem card_filter_range_L_succ (n j : ℕ) :
    #{q ∈ range (L (n + 1)) | F q n = j} = (L (n + 1) / L n) * N n j := by
  have hdiv : L (n + 1) = (L (n + 1) / L n) * L n :=
    (Nat.div_mul_cancel (L_dvd_L (Nat.le_succ n))).symm
  have hper : ∀ q, F (q + L n) n = j ↔ F q n = j := by
    intro q
    rw [← F_mod (q + L n) n (L n) dvd_rfl, Nat.add_mod_right, F_mod q n (L n) dvd_rfl]
  conv_lhs => rw [hdiv]
  exact card_filter_range_mul (fun q => F q n = j) (L n) hper _

/-- A composite `n + 1` has a divisor `2 ≤ r ≤ n`. -/
theorem exists_dvd_of_not_prime (n : ℕ) (hn : 1 ≤ n) (hnp : ¬ (n + 1).Prime) :
    ∃ r, 2 ≤ r ∧ r ≤ n ∧ r ∣ n + 1 := by
  refine ⟨(n + 1).minFac, (Nat.minFac_prime (by omega)).two_le, ?_, Nat.minFac_dvd _⟩
  have := (Nat.not_prime_iff_minFac_lt (by omega)).mp hnp
  omega

/-- At a composite level `n + 1` the state `1` is never left. -/
theorem F_succ_eq_one_iff_of_not_prime (q n : ℕ) (hn : 1 ≤ n) (hnp : ¬ (n + 1).Prime) :
    F q (n + 1) = 1 ↔ F q n = 1 := by
  rw [F_eq_one_iff_forall q (n + 1) (by omega), F_eq_one_iff_forall q n hn]
  obtain ⟨r, hr2, hrn, hrd⟩ := exists_dvd_of_not_prime n hn hnp
  constructor
  · intro h k hk hkn; exact h k hk (by omega)
  · intro h k hk hkn hkq
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · exact h k hk (by omega) hkq
    · have hk' : k = n + 1 := by omega
      subst hk'
      exact h r hr2 hrn (hrd.trans hkq)

/-- At a composite level `n + 1`, a final state `2` comes from an old state `2`. -/
theorem F_succ_eq_two_of_not_prime (q n : ℕ) (hn : 1 ≤ n) (hnp : ¬ (n + 1).Prime)
    (h : F q (n + 1) = 2) : F q n = 2 := by
  have h1 := one_le_F q n
  by_contra hne
  have hFn : F q n = 1 := by
    rw [F_succ q n hn] at h
    split_ifs at h <;> omega
  have := (F_succ_eq_one_iff_of_not_prime q n hn hnp).mpr hFn
  omega

/-- `N_{n,2} < N_{n,1}` for every `n ≥ 4` (the induction in Theorem 6.4). -/
theorem N_two_lt_N_one (n : ℕ) (hn : 4 ≤ n) : N n 2 < N n 1 := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    by_cases hp : (n + 1).Prime
    · have h1 := N_prime_transition (n + 1) hp 1 le_rfl (by omega)
      have h2 := N_prime_transition (n + 1) hp 2 (by omega) (by omega)
      simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.zero_mul, Nat.add_zero] at h1 h2
      rw [h1, h2, show 2 - 1 = 1 from rfl, Nat.one_mul]
      have hc : 0 < n + 1 - 2 := by omega
      have hlt := Nat.mul_lt_mul_of_pos_left ih hc
      have hexp : n * N n 1 = (n + 1 - 2) * N n 1 + N n 1 := by
        rw [← Nat.succ_mul]; congr 1; omega
      omega
    · have hρ : 0 < L (n + 1) / L n :=
        Nat.div_pos (Nat.le_of_dvd (L_pos _) (L_dvd_L (Nat.le_succ n))) (L_pos n)
      have hle : N (n + 1) 2 ≤ (L (n + 1) / L n) * N n 2 := by
        rw [← card_filter_range_L_succ]
        apply Finset.card_le_card
        intro q hq
        simp only [Finset.mem_filter] at hq ⊢
        exact ⟨hq.1, F_succ_eq_two_of_not_prime q n (by omega) hp hq.2⟩
      have heq : N (n + 1) 1 = (L (n + 1) / L n) * N n 1 := by
        rw [← card_filter_range_L_succ]
        exact congrArg Finset.card (Finset.filter_congr fun q _ =>
          F_succ_eq_one_iff_of_not_prime q n (by omega) hp)
      rw [heq]
      exact hle.trans_lt (Nat.mul_lt_mul_of_pos_left ih hρ)

/-- Nearest internal position (arXiv 2608.09092, Theorem 6.4, `j = 2`):
`N_{n,2} < φ(L_n)` for every `n ≥ 4`. -/
theorem N_two_lt (n : ℕ) (hn : 4 ≤ n) : N n 2 < Nat.totient (L n) := by
  rw [← N_one n (by omega)]
  exact N_two_lt_N_one n hn

/-- Reflection (Prop. 2.3, eq. (2.2)): if every `1 ≤ k ≤ n` divides `q + q' + 1`
(that is, `q' ≡ -1 - q` modulo `L_n`), then `F_n(q) + F_n(q') = n + 1`. -/
theorem F_add_F (q q' n : ℕ) (hn : 1 ≤ n) (h : ∀ k, 1 ≤ k → k ≤ n → k ∣ q + q' + 1) :
    F q n + F q' n = n + 1 := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    have ih' := ih fun k hk hkn => h k hk (by omega)
    have hdvd : n + 1 ∣ q % (n + 1) + q' % (n + 1) + 1 := by
      have hq := Nat.div_add_mod q (n + 1)
      have hq' := Nat.div_add_mod q' (n + 1)
      have hall := h (n + 1) (by omega) le_rfl
      have hsum : q + q' + 1 = (n + 1) * (q / (n + 1) + q' / (n + 1)) +
          (q % (n + 1) + q' % (n + 1) + 1) := by rw [Nat.mul_add]; omega
      rw [hsum] at hall
      exact (Nat.dvd_add_right (Nat.dvd_mul_right _ _)).mp hall
    have hr := Nat.mod_lt q (by omega : 0 < n + 1)
    have hr' := Nat.mod_lt q' (by omega : 0 < n + 1)
    have hsum : q % (n + 1) + q' % (n + 1) + 1 = n + 1 :=
      Nat.eq_of_dvd_of_lt_two_mul (by omega) hdvd (by omega)
    rw [F_succ q n hn, F_succ q' n hn]
    split_ifs <;> omega

/-- Periodicity (arXiv 2608.09092, Prop. 2.3, eq. (2.1)): `F_n(q + L_n) = F_n(q)`. -/
theorem F_add_L (q n : ℕ) : F (q + L n) n = F q n := by
  rw [← F_mod (q + L n) n (L n) dvd_rfl, Nat.add_mod_right, F_mod q n (L n) dvd_rfl]

/-- Reflection (Prop. 2.3, eq. (2.3)): `F_n(q) + F_n(L_n - 1 - q) = n + 1` for
`0 ≤ q < L_n` and `n ≥ 1`. -/
theorem F_add_F_reflect (q n : ℕ) (hn : 1 ≤ n) (hq : q < L n) :
    F q n + F (L n - 1 - q) n = n + 1 := by
  apply F_add_F q (L n - 1 - q) n hn
  intro k hk hkn
  have hsum : q + (L n - 1 - q) + 1 = L n := by omega
  rw [hsum]
  exact dvd_L hk hkn

/-- Right endpoint criterion (Prop. 2.3, eq. (2.5)): for `n ≥ 1`,
`F_n(q) = n ⟺ gcd(q + 1, L_n) = 1`. -/
theorem F_eq_self_iff (q n : ℕ) (hn : 1 ≤ n) : F q n = n ↔ (q + 1).Coprime (L n) := by
  have hL := L_pos n
  set r := q % L n with hr
  have hrL : r < L n := Nat.mod_lt q hL
  have hrefl := F_add_F_reflect r n hn hrL
  have h1 := one_le_F (L n - 1 - r) n
  rw [← F_mod q n (L n) dvd_rfl, ← hr]
  have hiff : F r n = n ↔ F (L n - 1 - r) n = 1 := by omega
  rw [hiff, F_eq_one_iff_forall _ n hn, coprime_L_iff]
  have hq : q + 1 = L n * (q / L n) + (r + 1) := by
    have := Nat.div_add_mod q (L n); omega
  have hsum : (L n - 1 - r) + (r + 1) = L n := by omega
  refine forall_congr' fun k => imp_congr_right fun hk => imp_congr_right fun hkn => ?_
  have hkL := dvd_L (by omega : 1 ≤ k) hkn
  have hkS : k ∣ (L n - 1 - r) + (r + 1) := by rw [hsum]; exact hkL
  have e1 : k ∣ q + 1 ↔ k ∣ r + 1 := by
    rw [hq]; exact Nat.dvd_add_right (Dvd.dvd.mul_right hkL _)
  have e2 : k ∣ L n - 1 - r ↔ k ∣ r + 1 :=
    ⟨fun h => (Nat.dvd_add_right h).mp hkS, fun h => (Nat.dvd_add_left h).mp hkS⟩
  rw [e1, e2]

/-- Fiber symmetry (Cor. 2.5, eq. (2.6)): `N_{n,j} = N_{n,n+1-j}` for `j ≤ n`. -/
theorem N_symm (n j : ℕ) (hn : 1 ≤ n) (hjn : j ≤ n) :
    N n j = N n (n + 1 - j) := by
  unfold N
  have hL := L_pos n
  have hrefl : ∀ q, q < L n → F q n + F (L n - 1 - q) n = n + 1 := by
    intro q hq
    apply F_add_F q (L n - 1 - q) n hn
    intro k hk hkn
    have : q + (L n - 1 - q) + 1 = L n := by omega
    rw [this]
    exact dvd_L hk hkn
  apply Finset.card_nbij' (fun q => L n - 1 - q) (fun q => L n - 1 - q)
  · intro q hq
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hq ⊢
    have := hrefl q hq.1
    omega
  · intro q hq
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hq ⊢
    have := hrefl q hq.1
    omega
  · intro q hq
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hq
    show L n - 1 - (L n - 1 - q) = q
    omega
  · intro q hq
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hq
    show L n - 1 - (L n - 1 - q) = q
    omega

/-- Right endpoint count (Cor. 2.5): `N_{n,n} = φ(L_n)` for `n ≥ 1`. -/
theorem N_self (n : ℕ) (hn : 1 ≤ n) : N n n = Nat.totient (L n) := by
  rw [N_symm n n hn le_rfl, Nat.add_sub_cancel_left, N_one n hn]

/-- Nearest internal positions (arXiv 2608.09092, Theorem 6.4): for every `n ≥ 4`,
`N_{n,2} = N_{n,n-1}` and `N_{n,2} < φ(L_n)`. -/
theorem nearest_internal (n : ℕ) (hn : 4 ≤ n) :
    N n 2 = N n (n - 1) ∧ N n 2 < Nat.totient (L n) := by
  refine ⟨?_, N_two_lt n hn⟩
  rw [N_symm n (n - 1) (by omega) (by omega), show n + 1 - (n - 1) = 2 by omega]

/-- Prime propagation (arXiv 2608.09092, Cor. 6.3): for a prime `p ≥ 5`, endpoint
dominance at level `p - 1` implies endpoint dominance at level `p`. -/
theorem prime_propagation (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (h : ∀ j, 1 < j → j < p - 1 → N (p - 1) j < Nat.totient (L (p - 1))) :
    ∀ j, 1 < j → j < p → N p j < Nat.totient (L p) := by
  intro j hj1 hjp
  set T := Nat.totient (L (p - 1)) with hT
  have hbound : ∀ i, 1 ≤ i → i ≤ p - 1 → N (p - 1) i ≤ T := by
    intro i hi1 hip
    rcases Nat.lt_or_ge 1 i with h1 | h1
    · rcases Nat.lt_or_ge i (p - 1) with h2 | h2
      · exact (h i h1 h2).le
      · have hi : i = p - 1 := by omega
        rw [hi, N_self (p - 1) (by omega)]
    · have hi : i = 1 := by omega
      rw [hi, N_one (p - 1) (by omega)]
  have htot : Nat.totient (L p) = (p - j) * T + (j - 1) * T := by
    rw [← N_one p (by omega), N_prime_transition p hp 1 le_rfl (by omega), Nat.sub_self,
      Nat.zero_mul, Nat.add_zero, N_one (p - 1) (by omega), ← hT, ← Nat.add_mul]
    congr 1
    omega
  rw [htot, N_prime_transition p hp j (by omega) hjp.le]
  rcases Nat.lt_or_ge j (p - 1) with hj2 | hj2
  · exact Nat.add_lt_add_of_lt_of_le
      (Nat.mul_lt_mul_of_pos_left (h j hj1 hj2) (by omega))
      (Nat.mul_le_mul_left _ (hbound (j - 1) (by omega) (by omega)))
  · exact Nat.add_lt_add_of_le_of_lt
      (Nat.mul_le_mul_left _ (hbound j (by omega) (by omega)))
      (Nat.mul_lt_mul_of_pos_left (h (j - 1) (by omega) (by omega)) (by omega))

/-- Minimal counterexample (arXiv 2608.09092, Cor. 6.5): if endpoint dominance
fails at `(n, j)` with `n ≥ 4`, `1 < j < n`, and holds at every level `4 ≤ m < n`,
then `n` is composite and `3 ≤ j ≤ n - 2`. -/
theorem minimal_counterexample (n j : ℕ) (hn : 4 ≤ n) (hj1 : 1 < j) (hjn : j < n)
    (hfail : Nat.totient (L n) ≤ N n j)
    (hmin : ∀ m, 4 ≤ m → m < n → ∀ i, 1 < i → i < m → N m i < Nat.totient (L m)) :
    ¬ n.Prime ∧ 3 ≤ j ∧ j + 2 ≤ n := by
  refine ⟨?_, ?_, ?_⟩
  · intro hp
    have h5 : 5 ≤ n := by
      rcases Nat.lt_or_ge n 5 with h | h
      · have h4 : n = 4 := by omega
        subst h4
        exact absurd hp (by decide)
      · exact h
    have := prime_propagation n hp h5 (hmin (n - 1) (by omega) (by omega)) j hj1 hjn
    omega
  · by_contra h3
    have hj : j = 2 := by omega
    subst hj
    have := N_two_lt n hn
    omega
  · by_contra h3
    have hj : j = n - 1 := by omega
    subst hj
    have hsym := N_symm n (n - 1) (by omega) (by omega)
    rw [show n + 1 - (n - 1) = 2 by omega] at hsym
    have := N_two_lt n hn
    omega

/-- **Open Problem 6.1 (endpoint dominance), arXiv 2608.09092.**  For every
`n ≥ 4` and `1 < j < n`, `N_{n,j} < φ(L_n)`.  This is OPEN; the paper verifies it
for `n ≤ 49` by computer and proves only the partial results above.  It is not a
target of this module and is left as `sorry`. -/
theorem endpoint_dominance (n : ℕ) (hn : 4 ≤ n) (j : ℕ) (hj1 : 1 < j) (hjn : j < n) :
    N n j < Nat.totient (L n) := by
  sorry

/-- The restarting Josephus process itself, with a step budget: while the current
list has length `k ≥ 2`, delete its entry of rank `1 + (q mod k)` (zero-based
index `q mod k`) and restart; return the last remaining entry.  A list of length
`n` needs `n - 1` deletions, so the budget `n` used in `josephus` never runs out. -/
def survivorAux (q : ℕ) : ℕ → List ℕ → ℕ
  | 0, l => l.headD 0
  | fuel + 1, l =>
    if l.length ≤ 1 then l.headD 0 else survivorAux q fuel (l.eraseIdx (q % l.length))

/-- The initial position of the last survivor of the restarting Josephus process
on `1, …, n` with parameter `q` (the paper's defining process for `F_n(q)`). -/
def josephus (q n : ℕ) : ℕ := survivorAux q n (List.range' 1 n)

/-- The process on a list of length `k + 1` returns its entry of rank
`F_{k+1}(q)` (Lemma 2.1 by reverse insertion). -/
theorem survivorAux_eq (q k : ℕ) : ∀ (l : List ℕ) (fuel : ℕ), l.length = k + 1 → k ≤ fuel →
    survivorAux q fuel l = (l[F q (k + 1) - 1]?).getD 0 := by
  induction k with
  | zero =>
    intro l fuel hl _
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hl
    cases fuel <;> rfl
  | succ k ih =>
    intro l fuel hl hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hlen : ¬ l.length ≤ 1 := by omega
    have hr : q % l.length < l.length := Nat.mod_lt _ (by omega)
    have hlen' : (l.eraseIdx (q % l.length)).length = k + 1 := by
      rw [List.length_eraseIdx_of_lt hr]; omega
    simp only [survivorAux, if_neg hlen]
    rw [ih _ f hlen' (by omega), List.getElem?_eraseIdx, F_succ q (k + 1) (by omega), hl]
    have h1 := one_le_F q (k + 1)
    split_ifs with ha hb hb <;> first | omega | (congr 2; omega)

/-- Lemma 2.1: the deletion process agrees with the recurrence, for `n ≥ 1`. -/
theorem josephus_eq_F (q n : ℕ) (hn : 1 ≤ n) : josephus q n = F q n := by
  unfold josephus
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [survivorAux_eq q k _ _ (by simp) (by omega)]
  have h1 := one_le_F q (k + 1)
  have h2 := F_le q (k + 1) (by omega)
  rw [List.getElem?_range' (by omega)]
  simp only [Option.getD_some]
  omega


/-- The process on `1, …, 4` reproduces the paper's table. -/
example : (List.range 12).map (fun q => josephus q 4) = [4, 1, 2, 2, 4, 1, 4, 1, 3, 3, 4, 1] := by
  decide

/-- Non-vacuity of `prime_propagation`: its hypothesis holds at `p = 5`
(level `4` has internal positions `j = 2, 3`), giving dominance at level 5. -/
example : ∀ j, 1 < j → j < 5 → N 5 j < Nat.totient (L 5) := by
  have h5 : Nat.Prime 5 := by norm_num
  have h4 : ∀ j, 1 < j → j < 5 - 1 → N (5 - 1) j < Nat.totient (L (5 - 1)) := by
    intro j hj1 hj2
    have hj : j = 2 ∨ j = 3 := by omega
    rcases hj with rfl | rfl <;> decide
  exact prime_propagation 5 h5 le_rfl h4

end Candidates.ExactPeriodicitySurjectivityHaar
