/-
  Erdős Problem #856 — harmonic weight of sets with no k elements of
  equal pairwise lcm.
  Status: open.  Tier UA attack target (second client of the Erdos857
  sunflower layer).

  Verbatim statement (`goof erdos fetch 856`, pulled 2026-08-05):

    "Let $k\geq 3$ and $f_k(N)$ be the maximum value of
    $\sum_{n\in A}\frac{1}{n}$, where $A$ ranges over all subsets of
    $\{1,\ldots,N\}$ which contain no subset of size $k$ with the same
    pairwise least common multiple.

    Estimate $f_k(N)$."

  DB remarks: Erdős [Er70]: f_k(N) ≪ (log N)/(log log N), via: for every
  t there are < k solutions to t = a·p with a ∈ A, p prime, whence
  (∑ 1/n)(∑_{p<N} 1/p) < k ∑_{t<N²} 1/t ≪ log N.  Tang–Zhang
  [TaZh25b, arXiv:2512.20055]: (log N)^{b_k−o(1)} ≤ f_k(N) ≤
  (log N)^{c_k+o(1)}; for k = 3: (log N)^{0.438} ≤ f₃(N) ≤
  (log N)^{0.889}.  The exponents c_k are < 1 iff the Erdős–Szemerédi
  sunflower conjecture #857 holds for k-sunflowers (their capacity
  µ_k^S: f_k(N) ≪ (log N)^{µ_k^S − 1 + o(1)}; equality µ_k^S = 2 iff
  f_k(N) = (log N)^{1−o(1)}).

  Repo adjacency: `Proofs/Erdos/Erdos857/NaslundSawin.lean`
  (`SunflowerFree`, `Erdos857Free`, `erdos857M`, Naslund–Sawin capacity
  bound 3/2^{2/3}) — the k = 3 upper-bound exponent 0.889 comes from
  exactly that bound.

  Mathlib inventory (leandoc 2026-08-05): `Nat.lcm`, `Finset.sum` over
  ℚ, `Finset.powersetCard`; no lcm-pattern machinery — the defs below
  are fresh.
-/
import Mathlib
import Sorry.Erdos.MertensLowerBound

set_option autoImplicit false

namespace ErdosCandidates.E856

/-- `EqualPairwiseLcm S`: all pairs of distinct elements of `S` have the
    same lcm.  (The forbidden pattern, for `|S| = k`.) -/
def EqualPairwiseLcm (S : Finset ℕ) : Prop :=
  ∃ L : ℕ, ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.lcm a b = L

/-- `LcmPatternFree k A`: no `k`-element subset of `A` has constant
    pairwise lcm. -/
def LcmPatternFree (k : ℕ) (A : Finset ℕ) : Prop :=
  ∀ S ∈ A.powersetCard k, ¬ EqualPairwiseLcm S

/-- The harmonic weight `∑_{n ∈ A} 1/n : ℚ`.  (`1/0 = 0` junk is
    guarded in the theorems by `A ⊆ Icc 1 N`.) -/
def harmonicWeight (A : Finset ℕ) : ℚ :=
  ∑ n ∈ A, (1 : ℚ) / n

/-- Ground truth: primes have pairwise lcm p·q all distinct, so
    `{2, 3, 5}` is 3-pattern-free; harmonic weight 31/30.
    -- PROVABLE (decide). -/
example : LcmPatternFree 3 ({2, 3, 5} : Finset ℕ) ∧
    harmonicWeight {2, 3, 5} = 31 / 30 := by
  refine ⟨?_, ?_⟩
  · intro S hS hEq
    obtain ⟨L, hL⟩ := hEq
    rw [Finset.mem_powersetCard] at hS
    have hSeq : S = {2, 3, 5} :=
      Finset.eq_of_subset_of_card_le hS.1 (by rw [hS.2]; decide)
    subst hSeq
    have h23 := hL 2 (by simp) 3 (by simp) (by norm_num)
    have h25 := hL 2 (by simp) 5 (by simp) (by norm_num)
    norm_num at h23 h25
    omega
  · simp [harmonicWeight]
    norm_num

/-- Non-degeneracy: `{6, 10, 15}` has all pairwise lcms equal to 30, so
    it is NOT 3-pattern-free.  The constraint has content.
    -- PROVABLE (decide). -/
example : ¬ LcmPatternFree 3 ({6, 10, 15} : Finset ℕ) := by
  intro h
  refine h {6, 10, 15} (Finset.mem_powersetCard.mpr ⟨subset_rfl, by decide⟩) ⟨30, ?_⟩
  intro a ha b hb hab
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first | exact absurd rfl hab | norm_num

/-- If `a * p = t = b * q` with `p ≠ q` primes, then `lcm a b = t`. -/
private theorem lcm_eq_of_mul_prime_eq {a b p q t : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (ha : a * p = t) (hb : b * q = t) : Nat.lcm a b = t := by
  have hqt : q ∣ a * p := ha ▸ (Dvd.intro_left b hb)
  have hqa : q ∣ a := by
    rcases (Nat.Prime.dvd_mul hq).mp hqt with h | h
    · exact h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).mp h) (Ne.symm hpq)
  obtain ⟨m, rfl⟩ := hqa
  have hbm : b = m * p := by
    have h1 : q * b = q * (m * p) := by rw [mul_comm q b, hb, ← ha]; ring
    exact Nat.eq_of_mul_eq_mul_left hq.pos h1
  subst hbm
  have hcop : Nat.Coprime q p := (Nat.coprime_primes hq hp).mpr (Ne.symm hpq)
  rw [← ha, mul_comm q m, Nat.lcm_mul_left, hcop.lcm_eq_mul]
  ring

/-- In a `k`-pattern-free set of positive integers, each `t` has at most `k - 1`
representations `t = a * p` with `a ∈ A` and `p ∈ P` prime. -/
private theorem card_fiber_le {k : ℕ} {A P : Finset ℕ} (hA : LcmPatternFree k A)
    (hpos : ∀ a ∈ A, 0 < a) (hP : ∀ p ∈ P, p.Prime) (t : ℕ) :
    ((A ×ˢ P).filter (fun x => x.1 * x.2 = t)).card ≤ k - 1 := by
  set F := (A ×ˢ P).filter (fun x => x.1 * x.2 = t) with hF
  have hmem : ∀ x ∈ F, x.1 ∈ A ∧ x.2.Prime ∧ x.1 * x.2 = t := by
    intro x hx
    rw [hF, Finset.mem_filter, Finset.mem_product] at hx
    exact ⟨hx.1.1, hP _ hx.1.2, hx.2⟩
  have hinj : Set.InjOn Prod.fst (F : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    obtain ⟨hxA, -, hxt⟩ := hmem x hx
    obtain ⟨-, -, hyt⟩ := hmem y hy
    have h2 : x.2 = y.2 := by
      rw [hxy] at hxt
      exact Nat.eq_of_mul_eq_mul_left (hpos _ (hxy ▸ hxA)) (hxt.trans hyt.symm)
    exact Prod.ext hxy h2
  have hcardS : (F.image Prod.fst).card = F.card := Finset.card_image_of_injOn hinj
  by_contra hlt
  have hk : k ≤ (F.image Prod.fst).card := by omega
  obtain ⟨T, hTS, hTk⟩ := Finset.exists_subset_card_eq hk
  have hTA : T ⊆ A := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hTS ha)
    exact (hmem x hx).1
  refine hA T (Finset.mem_powersetCard.mpr ⟨hTA, hTk⟩) ⟨t, ?_⟩
  intro a ha b hb hab
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hTS ha)
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hTS hb)
  obtain ⟨-, hxp, hxt⟩ := hmem x hx
  obtain ⟨hyA, hyp, hyt⟩ := hmem y hy
  have hne : x.2 ≠ y.2 := by
    intro h2
    apply hab
    rw [h2] at hxt
    exact Nat.eq_of_mul_eq_mul_right hyp.pos (hxt.trans hyt.symm)
  exact lcm_eq_of_mul_prime_eq hxp hyp hne hxt hyt


/-- Double counting: `(∑_{a ∈ A} 1/a) (∑_{p ≤ N} 1/p) ≤ (k - 1) H_{N²}`. -/
private theorem weight_mul_sum_inv_primes_le {k N : ℕ} {A : Finset ℕ}
    (hk : 1 ≤ k) (hA : LcmPatternFree k A) (hsub : A ⊆ Finset.Icc 1 N) :
    (harmonicWeight A : ℝ) * ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p ≤
      ((k : ℝ) - 1) * (harmonic (N ^ 2) : ℝ) := by
  set P := Nat.primesLE N
  have hpos : ∀ a ∈ A, 0 < a := fun a ha => (Finset.mem_Icc.mp (hsub ha)).1
  have hP : ∀ p ∈ P, p.Prime := fun p hp => Nat.prime_of_mem_primesLE hp
  have hk1 : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk]; simp
  have hw : (harmonicWeight A : ℝ) = ∑ a ∈ A, (1 : ℝ) / a := by
    simp [harmonicWeight]
  have hprod : (harmonicWeight A : ℝ) * ∑ p ∈ P, (1 : ℝ) / p =
      ∑ x ∈ A ×ˢ P, (1 : ℝ) / ((x.1 * x.2 : ℕ) : ℝ) := by
    rw [hw, Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun p _ => ?_
    push_cast
    rw [one_div_mul_one_div]
  have hmaps : ∀ x ∈ A ×ˢ P, x.1 * x.2 ∈ Finset.Icc 1 (N ^ 2) := by
    intro x hx
    obtain ⟨hxA, hxP⟩ := Finset.mem_product.mp hx
    obtain ⟨ha1, haN⟩ := Finset.mem_Icc.mp (hsub hxA)
    have hp := hP _ hxP
    have hpN : x.2 ≤ N := (Nat.mem_primesLE.mp hxP).1
    refine Finset.mem_Icc.mpr ⟨Nat.mul_pos ha1 hp.pos, ?_⟩
    rw [sq]
    exact Nat.mul_le_mul haN hpN
  rw [hprod, ← Finset.sum_fiberwise_of_maps_to hmaps, harmonic_eq_sum_Icc]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  have hfib : ∑ x ∈ (A ×ˢ P).filter (fun x => x.1 * x.2 = t),
      (1 : ℝ) / ((x.1 : ℝ) * (x.2 : ℝ)) =
      (((A ×ˢ P).filter (fun x => x.1 * x.2 = t)).card : ℝ) * (t : ℝ)⁻¹ := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← Nat.cast_mul, (Finset.mem_filter.mp hx).2]
    simp
  rw [hfib]
  have hc := card_fiber_le hA hpos hP t
  have hc' : (((A ×ˢ P).filter (fun x => x.1 * x.2 = t)).card : ℝ) ≤ (k : ℝ) - 1 :=
    (Nat.cast_le.mpr hc).trans hk1
  exact mul_le_mul_of_nonneg_right hc' (by positivity)


/-- For `N ≥ 3 ^ 8`, `2 ≤ log log N`. -/
private theorem two_le_log_log {N : ℕ} (hN : 3 ^ 8 ≤ N) :
    8 ≤ Real.log N ∧ 2 ≤ Real.log (Real.log N) := by
  have hlog3 : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hNr : ((3 : ℝ) ^ 8) ≤ N := by exact_mod_cast hN
  have hlogN : 8 ≤ Real.log N := by
    have h1 : Real.log ((3 : ℝ) ^ 8) ≤ Real.log N := Real.log_le_log (by norm_num) hNr
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  refine ⟨hlogN, ?_⟩
  rw [Real.le_log_iff_exp_le (by linarith)]
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  rw [h2]
  nlinarith

/-- **Erdős #856, Er70 upper bound (the Tier-UA target)**:
    `f_k(N) ≪ log N / log log N`.  Stated with an explicit constant
    over ℝ.

    Proof sketch (attack plan, following the DB's own proof): if `A` is
    `k`-pattern-free then for every `t` there are `< k` pairs `(a, p)`
    with `a ∈ A`, `p` prime, `t = a p` — otherwise `k` products
    `a₁p₁ = ⋯ = a_kp_k = t` yield `k` elements whose pairwise lcms all
    equal `t` (needs the primes distinct and not dividing the `a_i` —
    the actual combinatorial core; handle the multiplicity bookkeeping
    with `Nat.Coprime`).  Multiply out:
    `harmonicWeight A · ∑_{p<N} 1/p < k · ∑_{t<N²} 1/t ≪ k log N`, and
    `∑_{p<N} 1/p ≫ log log N` (Mertens.  Mathlib:
    `Nat.Primes.sum_one_div_le`? — Mertens' second theorem exists as
    `mertens_second`-shaped results in Mathlib's
    `NumberTheory/MertensTheorems`; re-check name via leandoc before
    the campaign).  Effort M. -/
theorem erdos_856_upper_bound (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A ⊆ Finset.Icc 1 N, LcmPatternFree k A →
        (harmonicWeight A : ℝ) ≤ C * Real.log N / Real.log (Real.log N) := by
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  refine ⟨6 * ((k : ℝ) - 1), by linarith, 3 ^ 8, fun N hN A hsub hA => ?_⟩
  obtain ⟨hlogN, hL⟩ := two_le_log_log hN
  have hN3 : 3 ≤ N := le_trans (by norm_num) hN
  set L := Real.log (Real.log N) with hLdef
  set M := ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p with hMdef
  have hM : L - 1 ≤ M := Candidates.MertensLowerBound.log_log_sub_one_le_sum_inv_primes N hN3
  have hw0 : 0 ≤ (harmonicWeight A : ℝ) := by
    have : 0 ≤ harmonicWeight A :=
      Finset.sum_nonneg fun n _ => by positivity
    exact_mod_cast this
  have hdc := weight_mul_sum_inv_primes_le (by omega) hA hsub
  have hharm : (harmonic (N ^ 2) : ℝ) ≤ 1 + 2 * Real.log N := by
    have h := harmonic_le_one_add_log (N ^ 2)
    rw [Nat.cast_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
  have hupper : (harmonicWeight A : ℝ) * M ≤ ((k : ℝ) - 1) * (3 * Real.log N) :=
    hdc.trans (mul_le_mul_of_nonneg_left (by linarith) hk1)
  have hLpos : 0 < L := by linarith
  rw [le_div_iff₀ hLpos]
  have hLM : L ≤ 2 * M := by linarith
  calc (harmonicWeight A : ℝ) * L ≤ (harmonicWeight A : ℝ) * (2 * M) :=
        mul_le_mul_of_nonneg_left hLM hw0
    _ = 2 * ((harmonicWeight A : ℝ) * M) := by ring
    _ ≤ 2 * (((k : ℝ) - 1) * (3 * Real.log N)) := by linarith
    _ = 6 * ((k : ℝ) - 1) * Real.log N := by ring

/-- Trivial harmonic bound — the sanity floor:
    `harmonicWeight A ≤ 1 + log N` for `A ⊆ [1, N]`.
    -- PROVABLE (harmonic-sum vs log comparison; the ℚ→ℝ cast plus
    `Real.add_pow_le_pow_mul_pow_of_sq_le_sq`-free route via
    `Finset.sum_div` and integral comparison in Mathlib's
    `Real.log` API). -/
theorem harmonicWeight_le (N : ℕ) (hN : 1 ≤ N) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 N) :
    (harmonicWeight A : ℝ) ≤ 1 + Real.log N := by
  have hsub : harmonicWeight A ≤ harmonic N := by
    rw [harmonic_eq_sum_Icc, harmonicWeight]
    simp_rw [one_div]
    refine Finset.sum_le_sum_of_subset_of_nonneg hA ?_
    intro i _ _
    positivity
  have hcast : (harmonicWeight A : ℝ) ≤ (harmonic N : ℝ) := by
    exact_mod_cast hsub
  exact hcast.trans (harmonic_le_one_add_log N)

/-- **Tang–Zhang lower bound, k = 3** (TaZh25b), archived:
    `f₃(N) ≥ (log N)^{0.438}` for large `N` — realized by an explicit
    pattern-free `A`.  The exponent is `log 1.551` from the
    Deuber–Erdős–Gunderson–Kostochka–Meyer sunflower-free construction;
    the bridge to the repo's SUNFLOWER assets is the interesting part:
    a sunflower-free family of subsets of primes maps to an lcm-pattern-
    free set of squarefree integers by `S ↦ ∏_{p∈S} p`. -/
theorem tang_zhang_lower_k3 :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ A ⊆ Finset.Icc 1 N, LcmPatternFree 3 A ∧
        Real.log N ^ (0.438 : ℝ) ≤ (harmonicWeight A : ℝ) := by
  sorry

/-- **The sunflower encoding lemma** — the reusable bridge (also serves
    #535): for squarefree integers, equal pairwise lcms of
    `∏_{p∈S_i} p` correspond to the `S_i` forming a weak sunflower
    (pairwise unions equal).  Fresh def; connects to
    `Erdos.Erdos857.WeakSunflower3` for k = 3.  -- PROVABLE (elementary
    squarefree factorization; `Nat.squarefree_prod` API). -/
theorem lcm_pattern_iff_union_pattern (S T : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hT : ∀ p ∈ T, p.Prime) :
    Nat.lcm (∏ p ∈ S, p) (∏ p ∈ T, p) = ∏ p ∈ (S ∪ T), p := by
  apply Nat.dvd_antisymm
  · exact Nat.lcm_dvd (Finset.prod_dvd_prod_of_subset _ _ _ Finset.subset_union_left)
      (Finset.prod_dvd_prod_of_subset _ _ _ Finset.subset_union_right)
  · refine Finset.prod_primes_dvd _ ?_ ?_
    · intro p hp
      rcases Finset.mem_union.mp hp with h | h
      · exact (hS p h).prime
      · exact (hT p h).prime
    · intro p hp
      rcases Finset.mem_union.mp hp with h | h
      · exact (Finset.dvd_prod_of_mem _ h).trans (Nat.dvd_lcm_left _ _)
      · exact (Finset.dvd_prod_of_mem _ h).trans (Nat.dvd_lcm_right _ _)

end ErdosCandidates.E856

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS-WITH-FLAGS
   - Verbatim statement matches DB pull exactly.
   - EqualPairwiseLcm and LcmPatternFree correctly encode the forbidden pattern.
   - harmonicWeight uses (1:Q)/n; junk at n=0 is guarded by A <= Icc 1 N in theorems.
   - lcm(6,10)=lcm(6,15)=lcm(10,15)=30 verified: {6,10,15} is NOT 3-pattern-free.
   - harmonicWeight {2,3,5} = 1/2+1/3+1/5 = 31/30 verified.
   - Er70 upper bound log N / log log N: matches DB body.
   - Tang-Zhang k=3 lower exponent 0.438: log(1.551) = 0.4389, rounded. Matches DB.
   - Tang-Zhang k=3 upper exponent 0.889: 3/2^{2/3}-1 = 0.8899. Matches DB.
   - FLAG (minor, style): lcm_pattern_iff_union_pattern is stated as an equality of
     lcm(prod S, prod T) = prod (S union T) for prime sets, not as an iff about
     EqualPairwiseLcm. The docstring says "iff ... union pattern" but the theorem is
     just the lcm-product identity. The bridge to EqualPairwiseLcm/WeakSunflower3 is
     not formalized here. Not a fidelity error but the theorem name overpromises.
   - Attributions: Er70 for upper bound, TaZh25b for Tang-Zhang, Naslund-Sawin for
     the 3/2^{2/3} capacity — all match DB.
-/
