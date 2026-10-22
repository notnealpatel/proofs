/-
# A232656 — Kleinwaks: Fibonacci-like pairs mod n that hit zero

Logan J. Kleinwaks' conjecture in OEIS A232656 gives the number of pairs
modulo positive `n` whose Fibonacci-like sequence hits zero as
`Σ_{d ∣ n} φ(d) A001177(d)`. The formula is also recorded by Richard L.
Ollerton. Here A001177 is the rank of apparition: the least positive `k`
with `d ∣ F_k`.

The step map `T (x, y) = (y, x + y)` is a bijection of `(ZMod n)²`, so every
point is periodic and a pair whose sequence contains `0` lies on the forward
orbit of some `(0, c)`.  Since `T^[k] (0, c) = (c F_k, c F_{k+1})` and
`c F_k = 0` in `ZMod n` iff `n / gcd(n, c) ∣ F_k`, the pairs are in bijection
with `{(c, j) : c ∈ ZMod n, j < A001177(n / gcd(n, c))}` via
`(c, j) ↦ T^[j] (0, c)`.  Grouping `c` by `gcd(n, c)` with
`φ(n / g) = #{c < n : gcd(n, c) = g}` gives `Σ_{d ∣ n} φ(d) A001177(d)`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A232656PairsWhoseFibonacci

open Finset

/-! ## Definitions -/

/-- The Fibonacci step map on pairs modulo `n`: `(x₀, x₁) ↦ (x₁, x₀ + x₁)`.  The
`k`-th term of the Fibonacci-like sequence started at `(a, b)` is
`((step n)^[k] (a, b)).1`. -/
def step (n : ℕ) (p : ZMod n × ZMod n) : ZMod n × ZMod n := (p.2, p.1 + p.2)

/-- The Fibonacci-like sequence `x₀ = a, x₁ = b, x_{k+2} = x_k + x_{k+1}` modulo
`n` started at the pair `p = (a, b)` contains a zero term. -/
def HitsZero (n : ℕ) (p : ZMod n × ZMod n) : Prop := ∃ k, ((step n)^[k] p).1 = 0

/-- OEIS A232656: the number of pairs `(a, b) ∈ (ZMod n)²` whose Fibonacci-like
sequence modulo `n` contains a zero.  (For `n = 0` the type is infinite and the
value is the junk `0`; all statements below assume `0 < n`.) -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {p : ZMod n × ZMod n // HitsZero n p}

/-- OEIS A001177, the Fibonacci entry point of `d`: the least `k ≥ 1` with
`d ∣ F_k` (`0` if no such `k` exists, which never happens for `0 < d`). -/
noncomputable def entryPoint (d : ℕ) : ℕ := sInf {k | 0 < k ∧ d ∣ Nat.fib k}

/-! ## Dynamics of the step map -/

/-- The step map is injective. -/
theorem step_injective (n : ℕ) : Function.Injective (step n) := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  simp only [step, Prod.mk.injEq] at h
  obtain ⟨hy, hxy⟩ := h
  subst hy
  simp only [Prod.mk.injEq, and_true]
  exact add_right_cancel hxy

/-- For `0 < n`, every pair is a periodic point of the step map. -/
theorem exists_isPeriodicPt {n : ℕ} (hn : 0 < n) (p : ZMod n × ZMod n) :
    ∃ m, 0 < m ∧ Function.IsPeriodicPt (step n) m p := by
  haveI : NeZero n := ⟨hn.ne'⟩
  exact (step_injective n).mem_periodicPts p

/-- Closed form of the orbit of `(0, c)`: `T^[k] (0, c) = (c F_k, c F_{k+1})`. -/
theorem iterate_step_zero (n : ℕ) (c : ZMod n) (k : ℕ) :
    (step n)^[k] (0, c) = (c * (Nat.fib k : ZMod n), c * (Nat.fib (k + 1) : ZMod n)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [step, Nat.fib_add_two, Nat.cast_add, mul_add]

/-- Every positive `d` divides some Fibonacci number `F_k` with `0 < k`. -/
theorem exists_pos_dvd_fib {d : ℕ} (hd : 0 < d) : ∃ k, 0 < k ∧ d ∣ Nat.fib k := by
  obtain ⟨m, hm, hper⟩ := exists_isPeriodicPt hd ((0 : ZMod d), (1 : ZMod d))
  refine ⟨m, hm, ?_⟩
  have hfst := congrArg Prod.fst (hper.eq)
  rw [iterate_step_zero] at hfst
  simp only [one_mul] at hfst
  exact (ZMod.natCast_eq_zero_iff _ _).1 hfst

/-! ## The entry point -/

/-- For `0 < d`, the entry point is positive and `d ∣ F_{entryPoint d}`. -/
theorem entryPoint_spec {d : ℕ} (hd : 0 < d) : 0 < entryPoint d ∧ d ∣ Nat.fib (entryPoint d) :=
  Nat.sInf_mem (exists_pos_dvd_fib hd)

/-- Minimality of the entry point. -/
theorem entryPoint_le {d k : ℕ} (hk : 0 < k) (h : d ∣ Nat.fib k) : entryPoint d ≤ k :=
  Nat.sInf_le (show k ∈ {k | 0 < k ∧ d ∣ Nat.fib k} from ⟨hk, h⟩)

/-- Characterization used for examples: if `0 < k`, `d ∣ F_k` and no
`0 < j < k` has `d ∣ F_j`, then `entryPoint d = k`. -/
theorem entryPoint_eq_of {d k : ℕ} (hk : 0 < k) (h : d ∣ Nat.fib k)
    (hmin : ∀ j < k, 0 < j → ¬ d ∣ Nat.fib j) : entryPoint d = k := by
  refine le_antisymm (entryPoint_le hk h) ?_
  by_contra hlt
  have hmem : 0 < entryPoint d ∧ d ∣ Nat.fib (entryPoint d) :=
    Nat.sInf_mem (s := {k | 0 < k ∧ d ∣ Nat.fib k}) ⟨k, hk, h⟩
  exact hmin _ (not_le.1 hlt) hmem.1 hmem.2

/-! ## Arithmetic of `c F_k` modulo `n` -/

/-- `c * m = 0` in `ZMod n` iff `n / gcd(n, c) ∣ m`. -/
theorem mul_natCast_eq_zero_iff {n : ℕ} (hn : 0 < n) (c : ZMod n) (m : ℕ) :
    c * (m : ZMod n) = 0 ↔ n / n.gcd c.val ∣ m := by
  haveI : NeZero n := ⟨hn.ne'⟩
  rw [← ZMod.natCast_zmod_val c, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff,
    ZMod.val_natCast_of_lt (ZMod.val_lt c)]
  set g := n.gcd c.val with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hn
  have hcop : Nat.Coprime (n / g) (c.val / g) := Nat.coprime_div_gcd_div_gcd hgpos
  have hn' : n = g * (n / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
  have hc' : c.val = g * (c.val / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
  calc n ∣ c.val * m ↔ g * (n / g) ∣ g * (c.val / g * m) := by
        rw [← hn', ← mul_assoc, ← hc']
    _ ↔ n / g ∣ c.val / g * m := Nat.mul_dvd_mul_iff_left hgpos
    _ ↔ n / g ∣ m := hcop.dvd_mul_left

/-- The "depth" of `c`: the entry point of `n / gcd(n, c)`, i.e. the number of
pairs on the orbit of `(0, c)` before the next zero. -/
noncomputable def depth (n : ℕ) (c : ZMod n) : ℕ := entryPoint (n / n.gcd c.val)

/-- For `0 < n`, `n / gcd(n, c)` is positive. -/
theorem div_gcd_pos {n : ℕ} (hn : 0 < n) (c : ZMod n) : 0 < n / n.gcd c.val :=
  Nat.div_pos (Nat.gcd_le_left _ hn) (Nat.gcd_pos_of_pos_left _ hn)

/-- The first coordinate of `T^[k] (0, c)` vanishes iff `n / gcd(n, c) ∣ F_k`. -/
theorem iterate_fst_eq_zero_iff {n : ℕ} (hn : 0 < n) (c : ZMod n) (k : ℕ) :
    ((step n)^[k] (0, c)).1 = 0 ↔ n / n.gcd c.val ∣ Nat.fib k := by
  rw [iterate_step_zero]
  exact mul_natCast_eq_zero_iff hn c _

/-! ## The bijection `(c, j) ↦ T^[j] (0, c)` -/

/-- Every point on the forward orbit of `(0, c)` has a sequence hitting zero. -/
theorem hitsZero_iterate {n : ℕ} (hn : 0 < n) (c : ZMod n) (j : ℕ) :
    HitsZero n ((step n)^[j] (0, c)) := by
  obtain ⟨he, hdvd⟩ := entryPoint_spec (div_gcd_pos hn c)
  set e := entryPoint (n / n.gcd c.val)
  have hle : j ≤ e * (j + 1) := by nlinarith
  refine ⟨e * (j + 1) - j, ?_⟩
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle, iterate_fst_eq_zero_iff hn]
  exact hdvd.trans (Nat.fib_dvd _ _ (dvd_mul_right e (j + 1)))

/-- Every pair whose sequence hits zero is `T^[j] (0, c)` with `j < depth n c`. -/
theorem exists_of_hitsZero {n : ℕ} (hn : 0 < n) (p : ZMod n × ZMod n) (hp : HitsZero n p) :
    ∃ c : ZMod n, ∃ j < depth n c, (step n)^[j] (0, c) = p := by
  obtain ⟨k, hk⟩ := hp
  obtain ⟨m, hm, hper⟩ := exists_isPeriodicPt hn p
  have hex : ∃ t, ∃ c : ZMod n, (step n)^[t] (0, c) = p := by
    refine ⟨m * (k + 1) - k, ((step n)^[k] p).2, ?_⟩
    have hq : ((0 : ZMod n), ((step n)^[k] p).2) = (step n)^[k] p := Prod.ext hk.symm rfl
    have hle : k ≤ m * (k + 1) := by nlinarith
    rw [hq, ← Function.iterate_add_apply, Nat.sub_add_cancel hle]
    exact (hper.mul_const (k + 1)).eq
  classical
  let t₀ := Nat.find hex
  obtain ⟨c₀, hc₀⟩ : ∃ c : ZMod n, (step n)^[t₀] (0, c) = p := Nat.find_spec hex
  refine ⟨c₀, t₀, ?_, hc₀⟩
  by_contra hge
  rw [not_lt] at hge
  obtain ⟨he, hdvd⟩ := entryPoint_spec (div_gcd_pos hn c₀)
  set e := depth n c₀ with he_def
  have hzero : ((step n)^[e] (0, c₀)).1 = 0 := (iterate_fst_eq_zero_iff hn c₀ e).2 hdvd
  have hshift : (step n)^[t₀ - e] (0, ((step n)^[e] (0, c₀)).2) = p := by
    have hq : ((0 : ZMod n), ((step n)^[e] (0, c₀)).2) = (step n)^[e] (0, c₀) :=
      Prod.ext hzero.symm rfl
    rw [hq, ← Function.iterate_add_apply, Nat.sub_add_cancel hge]
    exact hc₀
  have hlt : t₀ - e < t₀ := Nat.sub_lt (lt_of_lt_of_le he hge) he
  exact Nat.find_min hex hlt ⟨_, hshift⟩

/-- Injectivity helper, ordered case: if `j ≤ j' < depth n c'` and
`T^[j] (0, c) = T^[j'] (0, c')`, then `j = j'` and `c = c'`. -/
theorem eq_of_iterate_eq_of_le {n : ℕ} (hn : 0 < n) {c c' : ZMod n} {j j' : ℕ}
    (hjj : j ≤ j') (hj' : j' < depth n c')
    (h : (step n)^[j] (0, c) = (step n)^[j'] (0, c')) : j = j' ∧ c = c' := by
  have hsplit : (step n)^[j'] (0, c') = (step n)^[j] ((step n)^[j' - j] (0, c')) := by
    rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hjj]
  rw [hsplit] at h
  have h0 : ((0 : ZMod n), c) = (step n)^[j' - j] (0, c') :=
    ((step_injective n).iterate j) h
  have hfst : ((step n)^[j' - j] (0, c')).1 = 0 := by rw [← h0]
  rw [iterate_fst_eq_zero_iff hn] at hfst
  have hdiff : j' - j = 0 := by
    by_contra hne
    have hle := entryPoint_le (Nat.pos_of_ne_zero hne) hfst
    have : j' - j ≤ j' := Nat.sub_le j' j
    exact absurd hj' (not_lt.2 (hle.trans this))
  have hjeq : j = j' := le_antisymm hjj (Nat.sub_eq_zero_iff_le.1 hdiff)
  refine ⟨hjeq, ?_⟩
  rw [hdiff, Function.iterate_zero_apply] at h0
  exact (Prod.mk.inj h0).2

/-- Injectivity of `(c, j) ↦ T^[j] (0, c)` on `j < depth n c`. -/
theorem eq_of_iterate_eq {n : ℕ} (hn : 0 < n) {c c' : ZMod n} {j j' : ℕ}
    (hj : j < depth n c) (hj' : j' < depth n c')
    (h : (step n)^[j] (0, c) = (step n)^[j'] (0, c')) : j = j' ∧ c = c' := by
  rcases le_total j j' with hjj | hjj
  · exact eq_of_iterate_eq_of_le hn hjj hj' h
  · obtain ⟨h1, h2⟩ := eq_of_iterate_eq_of_le hn hjj hj h.symm
    exact ⟨h1.symm, h2.symm⟩

/-- `a n` is the sum of the depths over `c ∈ ZMod n`. -/
theorem a_eq_sum_depth (n : ℕ) [NeZero n] : a n = ∑ c : ZMod n, depth n c := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  classical
  rw [a, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcard : (univ.sigma fun c : ZMod n => range (depth n c)).card =
      (univ.filter (HitsZero n)).card := by
    refine Finset.card_bij (fun x _ => (step n)^[x.2] (0, x.1)) ?_ ?_ ?_
    · intro x _
      exact mem_filter.2 ⟨mem_univ _, hitsZero_iterate hn x.1 x.2⟩
    · rintro ⟨c, j⟩ hx ⟨c', j'⟩ hx' h
      simp only [mem_sigma, mem_univ, mem_range, true_and] at hx hx'
      obtain ⟨rfl, rfl⟩ := eq_of_iterate_eq hn hx hx' h
      rfl
    · intro p hp
      obtain ⟨c, j, hj, hcj⟩ := exists_of_hitsZero hn p (mem_filter.1 hp).2
      exact ⟨⟨c, j⟩, by simp [hj], hcj⟩
  rw [← hcard, card_sigma]
  simp

/-! ## Regrouping by `gcd` -/

/-- `Σ_{c ∈ ZMod n} entryPoint (n / gcd(n, c)) = Σ_{d ∣ n} φ(d) entryPoint(d)`. -/
theorem sum_depth_eq (n : ℕ) [NeZero n] :
    ∑ c : ZMod n, depth n c = ∑ d ∈ n.divisors, Nat.totient d * entryPoint d := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have h1 : ∑ c : ZMod n, depth n c = ∑ i ∈ range n, entryPoint (n / n.gcd i) := by
    refine Finset.sum_nbij' (fun c : ZMod n => c.val) (fun i => (i : ZMod n)) ?_ ?_ ?_ ?_ ?_
    · intro c _
      exact mem_range.2 (ZMod.val_lt c)
    · intro i _
      exact mem_univ _
    · intro c _
      exact ZMod.natCast_zmod_val c
    · intro i hi
      exact ZMod.val_cast_of_lt (mem_range.1 hi)
    · intro c _
      rfl
  have hmaps : ∀ i ∈ range n, n.gcd i ∈ n.divisors := fun i _ =>
    Nat.mem_divisors.2 ⟨Nat.gcd_dvd_left _ _, hn.ne'⟩
  rw [h1, ← Finset.sum_fiberwise_of_maps_to hmaps]
  have h2 : ∀ g ∈ n.divisors,
      ∑ i ∈ range n with n.gcd i = g, entryPoint (n / n.gcd i) =
        Nat.totient (n / g) * entryPoint (n / g) := by
    intro g hg
    rw [Finset.sum_congr rfl (g := fun _ => entryPoint (n / g)) (fun i hi => by
      rw [(mem_filter.1 hi).2]), sum_const, smul_eq_mul,
      Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hg)]
  rw [Finset.sum_congr rfl h2]
  exact Nat.sum_div_divisors n (fun d => Nat.totient d * entryPoint d)

/-! ## Examples

`a` is checked independently of the main theorem: when `T^[m] = id`
(`m` a multiple of the Pisano period), zero-hitting is a bounded search, which
`decide` evaluates. -/

/-- If `T^[m] = id` with `0 < m`, a sequence hits zero iff it does so at some
`k < m`. -/
theorem hitsZero_iff_exists_lt {n m : ℕ} (hm : 0 < m) (hper : ∀ p, (step n)^[m] p = p)
    (p : ZMod n × ZMod n) : HitsZero n p ↔ ∃ k < m, ((step n)^[k] p).1 = 0 := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k % m, Nat.mod_lt _ hm, ?_⟩
    rw [Function.IsPeriodicPt.iterate_mod_apply (hper p)]
    exact hk
  · rintro ⟨k, -, hk⟩
    exact ⟨k, hk⟩

/-- `a n` as a bounded count, given `T^[m] = id` with `0 < m`. -/
theorem a_eq_card_filter_lt (n m : ℕ) [NeZero n] (hm : 0 < m)
    (hper : ∀ p, (step n)^[m] p = p) :
    a n = #{p : ZMod n × ZMod n | ∃ k < m, ((step n)^[k] p).1 = 0} := by
  classical
  rw [a, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext p
  simp only [mem_filter, mem_univ, true_and]
  exact hitsZero_iff_exists_lt hm hper p

example : a 1 = 1 := by
  rw [a_eq_card_filter_lt 1 1 one_pos (by decide)]
  decide

example : a 2 = 4 := by
  rw [a_eq_card_filter_lt 2 3 (by norm_num) (by decide)]
  decide

example : a 5 = 21 := by
  rw [a_eq_card_filter_lt 5 20 (by norm_num) (by decide)]
  decide

example : a 8 = 40 := by
  rw [a_eq_card_filter_lt 8 12 (by norm_num) (by decide)]
  decide

example : entryPoint 1 = 1 := entryPoint_eq_of one_pos (by decide) (by decide)

example : entryPoint 2 = 3 := entryPoint_eq_of (by norm_num) (by decide) (by decide)

example : entryPoint 4 = 6 := entryPoint_eq_of (by norm_num) (by decide) (by decide)

example : entryPoint 5 = 5 := entryPoint_eq_of (by norm_num) (by decide) (by decide)

example : entryPoint 8 = 6 := entryPoint_eq_of (by norm_num) (by decide) (by decide)

/-! ## The conjecture -/

/-- **Kleinwaks' conjecture (A232656, Logan J. Kleinwaks).**

For every `n ≥ 1`, the number of pairs `(a, b) ∈ (ZMod n)²` whose Fibonacci-like
sequence `x₀ = a, x₁ = b, x_{k+2} = x_k + x_{k+1}` (mod `n`) contains a zero
equals `Σ_{d ∣ n} φ(d) · A001177(d)`, where `A001177(d)` is the least `k ≥ 1`
with `d ∣ F_k`.  The guard `0 < n` is needed: `ZMod 0 = ℤ` is infinite. -/
theorem a232656 {n : ℕ} (hn : 0 < n) :
    a n = ∑ d ∈ n.divisors, Nat.totient d * entryPoint d := by
  haveI : NeZero n := ⟨hn.ne'⟩
  rw [a_eq_sum_depth n, sum_depth_eq n]

/-- Non-vacuity: the hypothesis `0 < n` is satisfiable and the conclusion at
`n = 5` reads `21 = Σ_{d ∣ 5} φ(d) A001177(d) = 1·1 + 4·5`. -/
example : a 5 = ∑ d ∈ (5 : ℕ).divisors, Nat.totient d * entryPoint d := a232656 (by norm_num)

end Candidates.A232656PairsWhoseFibonacci
