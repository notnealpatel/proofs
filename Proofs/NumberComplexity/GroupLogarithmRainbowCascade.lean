/-
# Group logarithm implies a rainbow-cascade colouring, so `χ(B_n) = n`

## Source

arXiv:2609.15081, Lujia Wang and Ruihua Wang, "Obstructions to coloring
arithmetic graphs" (dated 14 September 2026).  The statement sits in
Sec. 1 (definition of the arithmetic graph `B_n`, the rainbow cascade
condition `(cascade-conjecture)`, and the definition of cyclic / group
logarithms) and Sec. 2, Lemma 2.2 (`lem:group`, "Group logarithm
construction"), which the paper attributes to Caicedo, Chartier and Pach
[CCP, Theorem 61 and Lemma 74]; see also Bosek et al.

Verbatim informal claim (Sec. 1 and Lemma 2.2):

> The arithmetic graph `B_n` has vertex set `ℕ = {1,2,…}` and adjacency
> relation `a ∼ b ⟺ a ≠ b, max(a,b)/gcd(a,b) ≤ n`.  Every cascade `r[n]`
> is a clique of order `n`, and every edge lies in the cascade based at the
> greatest common divisor of its endpoints.  Thus `χ(B_n) ≥ n`, with
> equality precisely when there is a coloring `c : ℕ → [n]` satisfying
> `{c(r), c(2r), …, c(nr)} = [n]  (r ∈ ℕ)`.
>
> A cyclic logarithm of length `n` is a bijection `h : [n] → ℤ_n` such that
> `h(ab) = h(a) + h(b)  (ab ≤ n)`.  The same definition with a finite
> abelian group `G` of order `n` gives a group logarithm.
>
> Lemma 2.2 (Group logarithm construction).  A group logarithm
> `h : [n] → G` gives a proper `n`-coloring of `B_n`.  The resulting
> coloring is given explicitly by `c(a) = ∑_{r ≤ n, r prime} v_r(a) h(r)`.

Date: 2026-10-21.

Status: known result, proved elsewhere (CCP, Bosek et al.) and recalled
(without proof) in the paper.  The paper's own new results (the
obstructions at 205 and 211) are not formalized here.

Formalized here (sorry-free): the satisfactory-colouring form
(`exists_isSatisfactory_of_isGroupLog`), the chromatic-number form
(`chromaticNumber_arithGraph_of_isGroupLog`, using the clique `{1,…,n}`),
and `χ(B_n) = n` for `1 ≤ n ≤ 16` via explicit cyclic logarithms.
-/
import Mathlib

set_option autoImplicit false

namespace GroupLogarithmRainbowCascade

open Set

/-- The arithmetic graph `B_n` on the positive integers: distinct `a, b`
are adjacent iff `max(a,b) / gcd(a,b) ≤ n` (the division is exact since
`gcd(a,b)` divides `max(a,b)`). -/
def arithGraph (n : ℕ) : SimpleGraph ℕ+ where
  Adj a b := a ≠ b ∧ max (a : ℕ) b / Nat.gcd a b ≤ n
  symm := ⟨fun a b hab => ⟨hab.1.symm, by rw [max_comm, Nat.gcd_comm]; exact hab.2⟩⟩
  loopless := ⟨fun a haa => haa.1 rfl⟩

/-- Adjacency in `B_n` is decidable. -/
instance (n : ℕ) : DecidableRel (arithGraph n).Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ max (a : ℕ) b / Nat.gcd a b ≤ n))

/-- A group logarithm of length `n` into the additive group `G`: `h` maps
`[n] = {1,…,n}` bijectively onto `G`, and `h (a * b) = h a + h b`
whenever `a, b ∈ [n]` and `a * b ≤ n`. -/
def IsGroupLog {G : Type*} [AddCommGroup G] (n : ℕ) (h : ℕ → G) : Prop :=
  BijOn h (Icc 1 n) univ ∧
    ∀ a b, 1 ≤ a → 1 ≤ b → a * b ≤ n → h (a * b) = h a + h b

/-- An `n`-satisfactory (rainbow cascade) colouring `c : ℕ → [n]`:
for every positive `r`, `{c(r), c(2r), …, c(nr)} = [n]`. -/
def IsSatisfactory (n : ℕ) (c : ℕ → ℕ) : Prop :=
  ∀ r, 0 < r → (fun k => c (r * k)) '' Icc 1 n = Icc 1 n

/-! ### Ground truth for the definitions -/

example : (arithGraph 6).Adj 4 6 := by decide
example : ¬ (arithGraph 2).Adj 2 3 := by decide
example : (arithGraph 3).Adj 2 3 := by decide
example : ¬ (arithGraph 5).Adj 3 3 := by decide


/-! ### The completely additive extension of a group logarithm -/

section Extension

variable {G : Type*} [AddCommGroup G]

/-- The paper's colouring `c(a) = ∑_{r ≤ n, r prime} v_r(a) h(r)`: the
completely additive extension of `h` through prime factorizations (only
primes `r ≤ n` carry a weight). -/
noncomputable def logColour (n : ℕ) (h : ℕ → G) (m : ℕ) : G :=
  m.factorization.sum fun p e => e • (if p ≤ n then h p else 0)

variable {n : ℕ} {h : ℕ → G}

/-- `logColour` is completely additive on positive integers. -/
theorem logColour_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    logColour n h (a * b) = logColour n h a + logColour n h b := by
  unfold logColour
  rw [Nat.factorization_mul ha hb, Finsupp.sum_add_index']
  · intro p
    exact zero_smul ℕ _
  · intro p e₁ e₂
    exact add_smul e₁ e₂ _

/-- `logColour` vanishes at `1`. -/
theorem logColour_one : logColour n h 1 = 0 := by
  simp [logColour]

/-- `logColour` agrees with `h` at primes `p ≤ n`. -/
theorem logColour_prime {p : ℕ} (hp : p.Prime) (hpn : p ≤ n) :
    logColour n h p = h p := by
  simp [logColour, hp.factorization, hpn]

/-- A group logarithm of positive length sends `1` to `0`. -/
theorem IsGroupLog.map_one (hh : IsGroupLog n h) (hn : 1 ≤ n) : h 1 = 0 := by
  have h11 : h (1 * 1) = h 1 + h 1 := hh.2 1 1 le_rfl le_rfl (by simpa using hn)
  rw [one_mul] at h11
  exact (left_eq_add.mp h11)

/-- The completely additive extension agrees with the group logarithm on
`[n]`. -/
theorem logColour_eq_of_isGroupLog (hh : IsGroupLog n h) :
    ∀ k, 1 ≤ k → k ≤ n → logColour n h k = h k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk1 hkn
  rcases hk1.eq_or_lt with hk | hk
  · subst hk
    rw [logColour_one, hh.map_one hkn]
  · have hp : k.minFac.Prime := Nat.minFac_prime (by omega)
    obtain ⟨k', hk'⟩ := k.minFac_dvd
    have hk'pos : 1 ≤ k' := by
      rcases Nat.eq_zero_or_pos k' with h0 | h0
      · rw [h0, mul_zero] at hk'
        omega
      · exact h0
    have hk'lt : k' < k := by
      rw [hk']
      exact lt_mul_left hk'pos hp.one_lt
    have hpn : k.minFac ≤ n := (Nat.minFac_le (by omega)).trans hkn
    have hprod : k.minFac * k' ≤ n := hk' ▸ hkn
    calc logColour n h k = logColour n h (k.minFac * k') := by rw [← hk']
      _ = h k.minFac + h k' := by
        rw [logColour_mul hp.ne_zero (by omega), logColour_prime hp hpn,
          ih k' hk'lt hk'pos (by omega)]
      _ = h (k.minFac * k') := (hh.2 _ _ hp.one_lt.le hk'pos hprod).symm
      _ = h k := by rw [← hk']

/-- Along a cascade, the extension is a translate of `h`:
`c(r k) = c(r) + h(k)` for `r > 0` and `k ∈ [n]`. -/
theorem logColour_cascade (hh : IsGroupLog n h) {r k : ℕ} (hr : 0 < r)
    (hk : k ∈ Icc 1 n) : logColour n h (r * k) = logColour n h r + h k := by
  rw [logColour_mul hr.ne' (by have := hk.1; omega),
    logColour_eq_of_isGroupLog hh k hk.1 hk.2]

/-- Rainbow cascades: every cascade `{r, 2r, …, nr}` receives every
colour of `G` under the extension of a group logarithm. -/
theorem image_cascade_logColour (hh : IsGroupLog n h) {r : ℕ} (hr : 0 < r) :
    (fun k => logColour n h (r * k)) '' Icc 1 n = univ := by
  have hcongr : EqOn (fun k => logColour n h (r * k))
      ((fun g => logColour n h r + g) ∘ h) (Icc 1 n) :=
    fun k hk => logColour_cascade hh hr hk
  rw [hcongr.image_eq, image_comp, hh.1.image_eq, image_univ_of_surjective]
  exact fun g => ⟨g - logColour n h r, add_sub_cancel _ _⟩

end Extension

/-! ### Rainbow cascades and the chromatic number of `B_n` -/

section Colouring

variable {G : Type*} [AddCommGroup G] {n : ℕ} {h : ℕ → G}

/-- Lemma 2.2, satisfactory form: a group logarithm of length `n` yields an
`n`-satisfactory colouring `c : ℕ → [n]`, namely `c = h⁻¹ ∘ logColour n h`. -/
theorem exists_isSatisfactory_of_isGroupLog (hh : IsGroupLog n h) :
    ∃ c : ℕ → ℕ, IsSatisfactory n c := by
  refine ⟨fun m => Function.invFunOn h (Icc 1 n) (logColour n h m), fun r hr => ?_⟩
  have hinv : BijOn (Function.invFunOn h (Icc 1 n)) univ (Icc 1 n) :=
    BijOn.symm hh.1.invOn_invFunOn.symm hh.1
  have hcomp : (fun k => Function.invFunOn h (Icc 1 n) (logColour n h (r * k))) =
      Function.invFunOn h (Icc 1 n) ∘ fun k => logColour n h (r * k) := rfl
  rw [hcomp, image_comp, image_cascade_logColour hh hr, hinv.image_eq]

/-- Every edge of `B_n` lies in the cascade at the gcd of its endpoints:
if `a ∼ b` then `a = g a'`, `b = g b'` with `g = gcd(a,b)`, `a', b' ∈ [n]`
and `a' ≠ b'`. -/
theorem exists_cascade_of_adj {a b : ℕ+} (hab : (arithGraph n).Adj a b) :
    ∃ g a' b' : ℕ, 0 < g ∧ a' ∈ Icc 1 n ∧ b' ∈ Icc 1 n ∧ a' ≠ b' ∧
      (a : ℕ) = g * a' ∧ (b : ℕ) = g * b' := by
  obtain ⟨hne, hle⟩ := hab
  set g := Nat.gcd (a : ℕ) b with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ a.pos
  have ha : (a : ℕ) = g * ((a : ℕ) / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
  have hb : (b : ℕ) = g * ((b : ℕ) / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
  have ha1 : 1 ≤ (a : ℕ) / g :=
    (Nat.one_le_div_iff hgpos).2 (Nat.le_of_dvd a.pos (Nat.gcd_dvd_left _ _))
  have hb1 : 1 ≤ (b : ℕ) / g :=
    (Nat.one_le_div_iff hgpos).2 (Nat.le_of_dvd b.pos (Nat.gcd_dvd_right _ _))
  have han : (a : ℕ) / g ≤ n := (Nat.div_le_div_right (le_max_left _ _)).trans hle
  have hbn : (b : ℕ) / g ≤ n := (Nat.div_le_div_right (le_max_right _ _)).trans hle
  refine ⟨g, (a : ℕ) / g, (b : ℕ) / g, hgpos, ⟨ha1, han⟩, ⟨hb1, hbn⟩, ?_, ha, hb⟩
  intro hq
  apply hne
  apply PNat.coe_injective
  rw [ha, hb, hq]

/-- Lemma 2.2, colouring form: the completely additive extension of a group
logarithm is a proper `G`-colouring of `B_n`. -/
noncomputable def logColouring (hh : IsGroupLog n h) : (arithGraph n).Coloring G :=
  SimpleGraph.Coloring.mk (fun a => logColour n h a) fun {a b} hab heq => by
    obtain ⟨g, a', b', hg, ha', hb', hne, ha, hb⟩ := exists_cascade_of_adj hab
    have hcol : logColour n h g + h a' = logColour n h g + h b' := by
      rw [← logColour_cascade hh hg ha', ← logColour_cascade hh hg hb', ← ha, ← hb]
      exact heq
    exact hne (hh.1.injOn ha' hb' (add_left_cancel hcol))

/-- The `n` vertices `1, …, n` form a clique of `B_n`, so `n ≤ χ(B_n)`. -/
theorem le_chromaticNumber_arithGraph (n : ℕ) : (n : ℕ∞) ≤ (arithGraph n).chromaticNumber := by
  refine SimpleGraph.le_chromaticNumber_of_pairwise_adj (ι := Fin n) (by simp)
    (fun i => ⟨(i : ℕ) + 1, Nat.succ_pos _⟩) fun i j hij => ⟨?_, ?_⟩
  · intro heq
    apply hij
    have hv : (i : ℕ) + 1 = (j : ℕ) + 1 := congrArg PNat.val heq
    exact Fin.ext (by omega)
  · have hi := i.isLt
    have hj := j.isLt
    calc max ((i : ℕ) + 1) ((j : ℕ) + 1) / Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1)
        ≤ max ((i : ℕ) + 1) ((j : ℕ) + 1) := Nat.div_le_self _ _
      _ ≤ n := max_le (by omega) (by omega)

/-- **Lemma 2.2 with the clique bound** (Caicedo–Chartier–Pach; recalled in
arXiv:2609.15081, Sec. 1–2): if there is a group logarithm of length `n` into a
finite abelian group `G`, then `χ(B_n) = n`. -/
theorem chromaticNumber_arithGraph_of_isGroupLog [Finite G] (hh : IsGroupLog n h) :
    (arithGraph n).chromaticNumber = n := by
  have : Fintype G := Fintype.ofFinite G
  have hcard : Fintype.card G = n := by
    have hnat : Nat.card (Icc 1 n) = Nat.card (univ : Set G) := Nat.card_congr hh.1.equiv
    have hIcc : Nat.card (Icc 1 n) = n := by simp
    rw [Nat.card_univ, hIcc, Nat.card_eq_fintype_card] at hnat
    exact hnat.symm
  refine le_antisymm ?_ (le_chromaticNumber_arithGraph n)
  calc (arithGraph n).chromaticNumber ≤ (Fintype.card G : ℕ∞) :=
        (logColouring hh).colorable.chromaticNumber_le
    _ = n := by rw [hcard]

/-- A decidable criterion for a group logarithm: if `|G| = n`, `h` is
injective on `[n]` and `h (a b) = h a + h b` for `a, b ∈ [n]`, `a b ≤ n`, then
`h` is a group logarithm of length `n`. -/
theorem isGroupLog_of_check [Fintype G] (hcard : Fintype.card G = n)
    (hinj : ∀ a ∈ Finset.Icc 1 n, ∀ b ∈ Finset.Icc 1 n, h a = h b → a = b)
    (hmul : ∀ a ∈ Finset.Icc 1 n, ∀ b ∈ Finset.Icc 1 n, a * b ≤ n →
      h (a * b) = h a + h b) :
    IsGroupLog n h := by
  have hinjOn : InjOn h (Icc 1 n) := fun a ha b hb hab =>
    hinj a (Finset.mem_Icc.2 ha) b (Finset.mem_Icc.2 hb) hab
  classical
  have himage : (Finset.Icc 1 n).image h = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn (by simpa using hinjOn), Nat.card_Icc, hcard]
    omega
  refine ⟨⟨fun _ _ => mem_univ _, hinjOn, fun g _ => ?_⟩, fun a b ha hb hab => ?_⟩
  · have hg : g ∈ (Finset.Icc 1 n).image h := himage ▸ Finset.mem_univ g
    obtain ⟨k, hk, hkg⟩ := Finset.mem_image.1 hg
    exact ⟨k, Finset.mem_Icc.1 hk, hkg⟩
  · have han : a ≤ n := (Nat.le_mul_of_pos_right a hb).trans hab
    have hbn : b ≤ n := (Nat.le_mul_of_pos_left b ha).trans hab
    exact hmul a (Finset.mem_Icc.2 ⟨ha, han⟩) b (Finset.mem_Icc.2 ⟨hb, hbn⟩) hab

end Colouring

/-! ### Explicit cyclic logarithms for `n ≤ 16` -/

/-- The cyclic candidate logarithm read off a table: `k ↦ l[k-1] mod n`
(entries outside `[n]` are irrelevant). -/
def tableLog (n : ℕ) (l : List ℕ) : ℕ → ZMod n := fun k => (l.getD (k - 1) 0 : ZMod n)

/-- The cyclic logarithm of length 6 from Sec. 1 of the paper:
`h(1)=0, h(2)=1, h(4)=2, h(3)=3, h(6)=4, h(5)=5` in `ℤ/6`. -/
theorem isGroupLog_six : IsGroupLog 6 (tableLog 6 [0, 1, 3, 2, 5, 4]) :=
  isGroupLog_of_check (ZMod.card 6) (by decide) (by decide)

/-- Ground truth: the identity table `k ↦ k - 1` is not a logarithm of
length 6, since `h(4) = 3 ≠ 2 = h(2) + h(2)`. -/
example : ¬ IsGroupLog 6 (tableLog 6 [0, 1, 2, 3, 4, 5]) := fun hh =>
  absurd (hh.2 2 2 (by norm_num) (by norm_num) (by norm_num)) (by decide)

/-- Non-vacuity of `IsSatisfactory`: a 6-satisfactory colouring exists. -/
example : ∃ c : ℕ → ℕ, IsSatisfactory 6 c :=
  exists_isSatisfactory_of_isGroupLog isGroupLog_six

/-- `B_n` has chromatic number exactly `n` for `1 ≤ n ≤ 16`, witnessed by explicit
cyclic logarithms (found by exhaustive search over the values at primes). -/
theorem chromaticNumber_arithGraph_of_le_sixteen (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 16) :
    (arithGraph n).chromaticNumber = n := by
  interval_cases n
  · exact chromaticNumber_arithGraph_of_isGroupLog
      (isGroupLog_of_check (h := tableLog 1 [0]) (ZMod.card 1) (by decide) (by decide))
  · exact chromaticNumber_arithGraph_of_isGroupLog
      (isGroupLog_of_check (h := tableLog 2 [0, 1]) (ZMod.card 2) (by decide) (by decide))
  · exact chromaticNumber_arithGraph_of_isGroupLog
      (isGroupLog_of_check (h := tableLog 3 [0, 1, 2]) (ZMod.card 3) (by decide) (by decide))
  · exact chromaticNumber_arithGraph_of_isGroupLog
      (isGroupLog_of_check (h := tableLog 4 [0, 1, 3, 2]) (ZMod.card 4) (by decide) (by decide))
  · exact chromaticNumber_arithGraph_of_isGroupLog
      (isGroupLog_of_check (h := tableLog 5 [0, 1, 3, 2, 4]) (ZMod.card 5) (by decide) (by decide))
  · exact chromaticNumber_arithGraph_of_isGroupLog
      (isGroupLog_of_check (h := tableLog 6 [0, 1, 3, 2, 5, 4]) (ZMod.card 6) (by decide) (by decide))
  · exact chromaticNumber_arithGraph_of_isGroupLog
      (isGroupLog_of_check (h := tableLog 7 [0, 1, 3, 2, 5, 4, 6]) (ZMod.card 7) (by decide) (by decide))
  · exact chromaticNumber_arithGraph_of_isGroupLog
      (isGroupLog_of_check (h := tableLog 8 [0, 1, 4, 2, 6, 5, 7, 3]) (ZMod.card 8) (by decide) (by decide))
  · exact chromaticNumber_arithGraph_of_isGroupLog
      (isGroupLog_of_check (h := tableLog 9 [0, 1, 4, 2, 6, 5, 7, 3, 8]) (ZMod.card 9) (by decide) (by decide))
  · exact chromaticNumber_arithGraph_of_isGroupLog
      (isGroupLog_of_check (h := tableLog 10 [0, 1, 4, 2, 6, 5, 9, 3, 8, 7]) (ZMod.card 10) (by decide) (by decide))
  · exact chromaticNumber_arithGraph_of_isGroupLog
      (isGroupLog_of_check (h := tableLog 11 [0, 1, 4, 2, 6, 5, 9, 3, 8, 7, 10]) (ZMod.card 11) (by decide) (by decide))
  · exact chromaticNumber_arithGraph_of_isGroupLog
      (isGroupLog_of_check (h := tableLog 12 [0, 1, 4, 2, 9, 5, 7, 3, 8, 10, 11, 6]) (ZMod.card 12) (by decide) (by decide))
  · exact chromaticNumber_arithGraph_of_isGroupLog
      (isGroupLog_of_check (h := tableLog 13 [0, 1, 4, 2, 9, 5, 7, 3, 8, 10, 11, 6, 12]) (ZMod.card 13) (by decide) (by decide))
  · exact chromaticNumber_arithGraph_of_isGroupLog
      (isGroupLog_of_check (h := tableLog 14 [0, 1, 4, 2, 9, 5, 11, 3, 8, 10, 7, 6, 13, 12]) (ZMod.card 14) (by decide) (by decide))
  · exact chromaticNumber_arithGraph_of_isGroupLog
      (isGroupLog_of_check (h := tableLog 15 [0, 1, 4, 2, 9, 5, 11, 3, 8, 10, 7, 6, 14, 12, 13]) (ZMod.card 15) (by decide) (by decide))
  · exact chromaticNumber_arithGraph_of_isGroupLog
      (isGroupLog_of_check (h := tableLog 16 [0, 1, 5, 2, 8, 6, 11, 3, 10, 9, 14, 7, 15, 12, 13, 4]) (ZMod.card 16) (by decide) (by decide))


end GroupLogarithmRainbowCascade
