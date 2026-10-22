import Mathlib.Data.Finset.Sort
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic

set_option autoImplicit false

namespace Erdos1052.NineOdd

/-- Distinct prime bases with positive exponents give distinct component values. -/
theorem component_injOn (P : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime) (he : ∀ p ∈ P, 0 < e p) :
    Set.InjOn (fun p => p ^ e p) (↑P : Set ℕ) := by
  intro p hpm q hqm hpq
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (he p hpm))
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (he q hqm))
  change p ^ e p = q ^ e q at hpq
  rw [hm, hn] at hpq
  exact ((hp p hpm).pow_inj (hp q hqm) hpq).1

/-- The actual-component image has the same cardinality as the prime support. -/
theorem component_card (P : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime) (he : ∀ p ∈ P, 0 < e p) :
    (P.image (fun p => p ^ e p)).card = P.card :=
  Finset.card_image_iff.mpr (component_injOn P e hp he)

/-- A positive natural component contributes its exact unitary abundance ratio. -/
def componentRatio (x : ℕ) : ℚ := ((x : ℚ) + 1) / x

example : componentRatio 3 = 4 / 3 := by norm_num [componentRatio]
example : componentRatio 32769 = 32770 / 32769 := by norm_num [componentRatio]

/-- Increasing a positive component can only decrease its abundance ratio. -/
theorem componentRatio_antitone {x y : ℕ} (hx : 0 < x) (hxy : x ≤ y) :
    componentRatio y ≤ componentRatio x := by
  have hxq : (0 : ℚ) < x := by exact_mod_cast hx
  have hyq : (0 : ℚ) < y := by exact_mod_cast (hx.trans_le hxy)
  have hxyq : (x : ℚ) ≤ y := by exact_mod_cast hxy
  unfold componentRatio
  apply (div_le_div_iff₀ hyq hxq).mpr
  nlinarith

/-- Every positive component has a positive abundance ratio. -/
theorem componentRatio_pos {x : ℕ} (hx : 0 < x) : 0 < componentRatio x := by
  unfold componentRatio
  positivity

/-- The ordinary factorized unitary identity gives the exact rational ratio equation,
without any bounds on the prime bases or exponents. -/
theorem factorized_ratio (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p)) :
    componentRatio (2 ^ a) * (∏ p ∈ P, componentRatio (p ^ e p)) = 2 := by
  have hpos : ∀ p ∈ P, (p : ℚ) ^ e p ≠ 0 := by
    intro p hpm
    exact pow_ne_zero _ (by exact_mod_cast (hp p hpm).ne_zero)
  have hprod : (∏ p ∈ P, (p : ℚ) ^ e p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hpos
  have hcast := congrArg (fun n : ℕ => (n : ℚ)) hid
  push_cast at hcast
  simp only [componentRatio, Nat.cast_pow, Finset.prod_div_distrib]
  rw [div_mul_div_comm]
  apply (div_eq_iff (mul_ne_zero (pow_ne_zero a (by norm_num)) hprod)).mpr
  exact hcast

/-- Prime uniqueness transports the ratio equation to the actual-component finset. -/
theorem actual_component_ratio (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime) (he : ∀ p ∈ P, 0 < e p)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p)) :
    componentRatio (2 ^ a) *
      (∏ x ∈ P.image (fun p => p ^ e p), componentRatio x) = 2 := by
  rw [Finset.prod_image (component_injOn P e hp he)]
  exact factorized_ratio a P e hp hid

/-- Any odd prime dividing a component successor must belong to the actual support.
This is derived from the full identity, not a closure premise. -/
theorem successor_prime_mem (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p))
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (p : ℕ) (hpm : p ∈ P) (hd : q ∣ p ^ e p + 1) : q ∈ P := by
  have hsucc : q ∣ ∏ p ∈ P, (p ^ e p + 1) :=
    hd.trans (Finset.dvd_prod_of_mem _ hpm)
  have hrhs : q ∣ 2 * (2 ^ a * ∏ p ∈ P, p ^ e p) := by
    rw [← hid]
    exact dvd_mul_of_dvd_right hsucc _
  have hn2 : ¬ q ∣ 2 := by
    intro h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq (by decide)).mp h)
  have hn2pow : ¬ q ∣ 2 ^ a := fun h => hn2 (hq.dvd_of_dvd_pow h)
  have hprod := (hq.dvd_mul.mp ((hq.dvd_mul.mp hrhs).resolve_left hn2)).resolve_left hn2pow
  obtain ⟨r, hrm, hr⟩ := (hq.prime.dvd_finsetProd_iff _).mp hprod
  have hqr : q = r :=
    (Nat.prime_dvd_prime_iff_eq hq (hp r hrm)).mp (hq.dvd_of_dvd_pow hr)
  exact hqr ▸ hrm

/-- Joint nonempty positive-exponent model for the ratio and closure infrastructure:
60 is an ordinary unitary-perfect number with odd components 3 and 5. -/
theorem sixty_model :
    let P : Finset ℕ := {3, 5}
    let e : ℕ → ℕ := fun _ => 1
    (∀ p ∈ P, p.Prime) ∧ (∀ p ∈ P, Odd p) ∧ (∀ p ∈ P, 0 < e p) ∧
      (2 ^ 2 + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
        2 * (2 ^ 2 * ∏ p ∈ P, p ^ e p) := by
  decide

/-- A count bound below a threshold bounds the corresponding sorted component,
regardless of how large the other components are. -/
theorem sorted_component_lower (X : Finset ℕ) {n : ℕ} (hc : X.card = n)
    (i : Fin n) (b : ℕ) (hcount : (X.filter (fun x => x < b)).card ≤ i.val) :
    b ≤ X.orderEmbOfFin hc i := by
  by_contra h
  have hlt : X.orderEmbOfFin hc i < b := by omega
  have hmap : Set.MapsTo (X.orderEmbOfFin hc)
      (↑(Finset.Iic i) : Set (Fin n)) (↑(X.filter (fun x => x < b)) : Set ℕ) := by
    intro j hj
    have hji : j ≤ i := Finset.mem_Iic.mp hj
    exact Finset.mem_filter.mpr ⟨X.orderEmbOfFin_mem hc j,
      lt_of_le_of_lt ((X.orderEmbOfFin hc).monotone hji) hlt⟩
  have hcard := Finset.card_le_card_of_injOn (X.orderEmbOfFin hc) hmap
    (X.orderEmbOfFin hc).injective.injOn
  rw [Fin.card_Iic] at hcard
  omega

/-- The largest component bound transfers to the final sorted entry. -/
theorem sorted_last_lower (X : Finset ℕ) {n : ℕ} (hc : X.card = n)
    (hn : 0 < n) (b : ℕ) (hlarge : ∃ x ∈ X, b ≤ x) :
    b ≤ X.orderEmbOfFin hc ⟨n - 1, Nat.sub_lt hn (by omega)⟩ := by
  obtain ⟨x, hxm, hbx⟩ := hlarge
  rw [Finset.orderEmbOfFin_last hc hn]
  exact hbx.trans (X.le_max' x hxm)

/-- Pointwise lower bounds on sorted actual components give an unbounded product
upper bound. Repeated envelope entries are permitted; actual entries remain distinct. -/
theorem sorted_ratio_le (X : Finset ℕ) {n : ℕ} (hc : X.card = n)
    (b : Fin n → ℕ) (hb : ∀ i, 0 < b i)
    (hdom : ∀ i, b i ≤ X.orderEmbOfFin hc i) :
    (∏ x ∈ X, componentRatio x) ≤ ∏ i : Fin n, componentRatio (b i) := by
  have hprod : (∏ i : Fin n, componentRatio (X.orderEmbOfFin hc i)) =
      ∏ x ∈ X, componentRatio x := by
    rw [← Finset.prod_image (X.orderEmbOfFin hc).injective.injOn]
    rw [Finset.image_orderEmbOfFin_univ]
  rw [← hprod]
  apply Finset.prod_le_prod
  · intro i _
    exact (componentRatio_pos ((hb i).trans_le (hdom i))).le
  · intro i _
    exact componentRatio_antitone (hb i) (hdom i)

/-- A sorted envelope with abundance strictly below two contradicts perfection.
The envelope is conditional infrastructure, not the nine-odd reduction theorem. -/
theorem not_perfect_of_sorted_envelope (a : ℕ) (X : Finset ℕ) {n : ℕ}
    (hc : X.card = n) (b : Fin n → ℕ) (A : ℕ) (hA : A ≤ a)
    (hb : ∀ i, 0 < b i) (hdom : ∀ i, b i ≤ X.orderEmbOfFin hc i)
    (hgap : componentRatio (2 ^ A) * (∏ i : Fin n, componentRatio (b i)) < 2) :
    componentRatio (2 ^ a) * (∏ x ∈ X, componentRatio x) ≠ 2 := by
  have htwo : 0 < (2 : ℕ) ^ a := by positivity
  have htwoA : 0 < (2 : ℕ) ^ A := by positivity
  have hpow : 2 ^ A ≤ (2 : ℕ) ^ a := Nat.pow_le_pow_right (by omega) hA
  have hratio := componentRatio_antitone htwoA hpow
  have hprod := sorted_ratio_le X hc b hb hdom
  have hnonneg : 0 ≤ ∏ i : Fin n, componentRatio (b i) :=
    Finset.prod_nonneg (fun i _ => (componentRatio_pos (hb i)).le)
  have hbound : componentRatio (2 ^ a) * (∏ x ∈ X, componentRatio x) ≤
      componentRatio (2 ^ A) * (∏ i : Fin n, componentRatio (b i)) :=
    mul_le_mul hratio hprod
      (Finset.prod_nonneg (fun x hx => by
        obtain ⟨i, hi⟩ := (show ∃ i, X.orderEmbOfFin hc i = x from by
          have hm : x ∈ Set.range (X.orderEmbOfFin hc) := by simpa using hx
          exact hm)
        exact (componentRatio_pos (hi ▸ (hb i).trans_le (hdom i))).le))
      (componentRatio_pos htwoA).le
  exact ne_of_lt (hbound.trans_lt hgap)

/-- The valuation of a nonzero finite product is the sum of its valuations. -/
theorem valuation_prod (q : ℕ) [Fact q.Prime] (P : Finset ℕ) (f : ℕ → ℕ)
    (hf : ∀ p ∈ P, f p ≠ 0) :
    padicValNat q (∏ p ∈ P, f p) = ∑ p ∈ P, padicValNat q (f p) := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hpm ih =>
    have hfp : f p ≠ 0 := hf p (Finset.mem_insert_self p P)
    have hfP : ∀ r ∈ P, f r ≠ 0 := fun r hr => hf r (Finset.mem_insert_of_mem hr)
    rw [Finset.prod_insert hpm, Finset.sum_insert hpm,
      padicValNat.mul hfp (Finset.prod_ne_zero_iff.mpr hfP), ih hfP]

/-- For an odd prime, the full ordinary identity gives the exact successor
valuation budget, with zero budget when that prime is not an actual base. -/
theorem ordinary_valuation_budget (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p))
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    padicValNat q (2 ^ a + 1) + (∑ p ∈ P, padicValNat q (p ^ e p + 1)) =
      if q ∈ P then e q else 0 := by
  letI : Fact q.Prime := ⟨hq⟩
  have hpow : ∀ p ∈ P, p ^ e p ≠ 0 :=
    fun p hpm => pow_ne_zero _ (hp p hpm).ne_zero
  have hsucc : ∀ p ∈ P, p ^ e p + 1 ≠ 0 := fun p _ => by omega
  have htwo : ¬ q ∣ 2 := by
    intro hd
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq (by decide)).mp hd)
  have hv2 : padicValNat q 2 = 0 := padicValNat.eq_zero_of_not_dvd htwo
  have hval := congrArg (padicValNat q) hid
  rw [padicValNat.mul (p := q) (a := 2 ^ a + 1) (by positivity) (Finset.prod_ne_zero_iff.mpr hsucc),
    padicValNat.mul (p := q) (a := 2) (by decide)
      (mul_ne_zero (pow_ne_zero a (by omega)) (Finset.prod_ne_zero_iff.mpr hpow)),
    padicValNat.mul (p := q) (a := 2 ^ a) (pow_ne_zero a (by omega)) (Finset.prod_ne_zero_iff.mpr hpow),
    valuation_prod q P _ hsucc, valuation_prod q P _ hpow,
    padicValNat.pow, hv2, mul_zero, zero_add, zero_add] at hval
  have hterms : ∀ p ∈ P, padicValNat q (p ^ e p) = if p = q then e q else 0 := by
    intro p hpm
    by_cases hpq : p = q
    · subst p
      simp
    · have hn : ¬ q ∣ p := by
        intro hd
        exact hpq ((Nat.prime_dvd_prime_iff_eq hq (hp p hpm)).mp hd).symm
      rw [padicValNat.pow, padicValNat.eq_zero_of_not_dvd hn, mul_zero]
      simp [hpq]
  rw [Finset.sum_congr rfl hterms] at hval
  simpa using hval

/-- Joint nonempty model for a sorted envelope with intentionally repeated entries. -/
theorem repeated_envelope_model :
    let X : Finset ℕ := {7, 13, 19}
    let b : Fin 3 → ℕ := fun _ => 7
    X.card = 3 ∧ (∀ i, 0 < b i) ∧
      (∀ i, b i ≤ X.orderEmbOfFin (by decide) i) := by
  dsimp
  refine ⟨by decide, by decide, ?_⟩
  intro i
  have hm := ({7, 13, 19} : Finset ℕ).orderEmbOfFin_mem (by decide :
    ({7, 13, 19} : Finset ℕ).card = 3) i
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h <;> omega

/-- The complete list of odd prime-power values below 37. This is an interval
classification only; neither the prime nor exponent is globally bounded. -/
theorem odd_prime_power_lt_thirty_seven (p k : ℕ) (hp : p.Prime)
    (ho : Odd p) (hk : 0 < k) (hlt : p ^ k < 37) :
    p ^ k ∈ ({3, 5, 7, 9, 11, 13, 17, 19, 23, 25, 27, 29, 31} : Finset ℕ) := by
  have hp3 : 3 ≤ p := by
    have hp2 := hp.two_le
    have hm := Nat.odd_iff.mp ho
    omega
  have hp37 : p < 37 := (Nat.le_pow hk).trans_lt hlt
  have hk4 : k < 4 := by
    by_contra h
    have h4 : 4 ≤ k := by omega
    have hbound : 3 ^ 4 ≤ p ^ k :=
      (Nat.pow_le_pow_left hp3 4).trans (Nat.pow_le_pow_right (by omega) h4)
    norm_num at hbound
    omega
  have hfinite : ∀ p : Fin 37, ∀ k : Fin 4,
      p.val.Prime → Odd p.val → 0 < k.val → p.val ^ k.val < 37 →
      p.val ^ k.val ∈ ({3, 5, 7, 9, 11, 13, 17, 19, 23, 25, 27, 29, 31} : Finset ℕ) := by
    decide
  exact hfinite ⟨p, hp37⟩ ⟨k, hk4⟩ hp ho hk hlt

/-- A finite exhaustive interval list bounds counts below every smaller threshold. -/
theorem count_lt_le_of_small_list (X L : Finset ℕ) (c b : ℕ) (hbc : b ≤ c)
    (hsmall : ∀ x ∈ X, x < c → x ∈ L) :
    (X.filter (fun x => x < b)).card ≤ (L.filter (fun x => x < b)).card := by
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hxm, hxb⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hsmall x hxm (hxb.trans_le hbc), hxb⟩

/-- If base three is absent, every actual odd component is one modulo three.
Successor coprimality and component coprimality both follow from the full identity. -/
theorem component_mod_three_of_base_absent (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p))
    (h3 : 3 ∉ P) (p : ℕ) (hpm : p ∈ P) : p ^ e p % 3 = 1 := by
  have hn : ¬ 3 ∣ p ^ e p := by
    intro hd
    have hbase := (by decide : Nat.Prime 3).dvd_of_dvd_pow hd
    have hp3 : 3 = p :=
      (Nat.prime_dvd_prime_iff_eq (by decide) (hp p hpm)).mp hbase
    exact h3 (hp3 ▸ hpm)
  have hsucc : ¬ 3 ∣ p ^ e p + 1 := by
    intro hd
    exact h3 (successor_prime_mem a P e hp hid 3 (by decide) (by decide) p hpm hd)
  rw [Nat.dvd_iff_mod_eq_zero] at hn hsucc
  omega

/-- The first load-bearing branch reduction: with nine distinct odd bases and
`11 ≤ a`, the full ordinary identity forces base three. No largest-component
bound is needed in this branch. This does not yet force exponent one. -/
theorem three_mem_of_nine_odd (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hc : P.card = 9) (hp : ∀ p ∈ P, p.Prime) (ho : ∀ p ∈ P, Odd p)
    (he : ∀ p ∈ P, 0 < e p) (ha : 11 ≤ a)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p)) : 3 ∈ P := by
  by_contra h3
  let X := P.image (fun p => p ^ e p)
  have hcX : X.card = 9 := (component_card P e hp he).trans hc
  have hsmall : ∀ x ∈ X, x < 25 → x ∈ ({7, 13, 19} : Finset ℕ) := by
    intro x hxm hx25
    obtain ⟨p, hpm, rfl⟩ := Finset.mem_image.mp hxm
    have hl := odd_prime_power_lt_thirty_seven p (e p) (hp p hpm) (ho p hpm)
      (he p hpm) (by omega)
    have hm := component_mod_three_of_base_absent a P e hp hid h3 p hpm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl ⊢
    omega
  let b : Fin 9 → ℕ := ![7, 13, 19, 25, 25, 25, 25, 25, 25]
  have hb : ∀ i, 0 < b i := by decide
  have hdom : ∀ i, b i ≤ X.orderEmbOfFin hcX i := by
    intro i
    apply sorted_component_lower
    have hb25 : b i ≤ 25 := by fin_cases i <;> decide
    have hcL := count_lt_le_of_small_list X {7, 13, 19} 25 (b i) hb25 hsmall
    have hcnum : (({7, 13, 19} : Finset ℕ).filter (fun x => x < b i)).card ≤ i.val := by
      fin_cases i <;> decide
    exact hcL.trans hcnum
  have hgap : componentRatio (2 ^ 11) * (∏ i : Fin 9, componentRatio (b i)) < 2 := by
    norm_num [b, componentRatio, Fin.prod_univ_succ]
  exact not_perfect_of_sorted_envelope a X hcX b 11 ha hb hdom hgap
    (actual_component_ratio a P e hp he hid)

/-- Equality of an actual component with a positive prime power recovers both
its actual base and its exponent. -/
theorem mem_component_prime_power_iff (P : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime) (he : ∀ p ∈ P, 0 < e p)
    (q k : ℕ) (hq : q.Prime) (hk : 0 < k) :
    q ^ k ∈ P.image (fun p => p ^ e p) ↔ q ∈ P ∧ e q = k := by
  constructor
  · intro hm
    obtain ⟨p, hpm, hpk⟩ := Finset.mem_image.mp hm
    obtain ⟨m, hem⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (he p hpm))
    obtain ⟨n, hkn⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
    rw [hem, hkn] at hpk
    obtain ⟨hpq, hmn⟩ := (hp p hpm).pow_inj hq hpk
    subst p
    exact ⟨hpm, by omega⟩
  · rintro ⟨hqm, hek⟩
    exact Finset.mem_image.mpr ⟨q, hqm, by rw [hek]⟩

/-- For nine components, eight finite count bounds and one large component
suffice to exclude perfection by an exact rational envelope. -/
theorem not_perfect_of_interval_envelope (a : ℕ) (X L : Finset ℕ)
    (hc : X.card = 9) (c : ℕ) (b : Fin 9 → ℕ) (ha : 11 ≤ a)
    (hb : ∀ i, 0 < b i) (hlast : b 8 = 32769)
    (hcut : ∀ i : Fin 9, i.val < 8 → b i ≤ c)
    (hcounts : ∀ i : Fin 9, i.val < 8 → (L.filter (fun x => x < b i)).card ≤ i.val)
    (hsmall : ∀ x ∈ X, x < c → x ∈ L)
    (hlarge : ∃ x ∈ X, 32768 < x)
    (hgap : componentRatio (2 ^ 11) * (∏ i : Fin 9, componentRatio (b i)) < 2) :
    componentRatio (2 ^ a) * (∏ x ∈ X, componentRatio x) ≠ 2 := by
  apply not_perfect_of_sorted_envelope a X hc b 11 ha hb _ hgap
  intro i
  by_cases hi : i.val < 8
  · apply sorted_component_lower
    exact (count_lt_le_of_small_list X L c (b i) (hcut i hi) hsmall).trans (hcounts i hi)
  · have hi8 : i = 8 := by apply Fin.ext; omega
    subst i
    rw [hlast]
    exact sorted_last_lower X hc (by omega) 32769 (by
      obtain ⟨x, hxm, hx⟩ := hlarge
      exact ⟨x, hxm, by omega⟩)

/-- Any nine actual odd prime powers obeying the two Wall bounds and the full
identity include either component three or component nine. -/
theorem three_or_nine_component (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hc : P.card = 9) (hp : ∀ p ∈ P, p.Prime) (ho : ∀ p ∈ P, Odd p)
    (he : ∀ p ∈ P, 0 < e p) (ha : 11 ≤ a)
    (hlarge : ∃ p ∈ P, 32768 < p ^ e p)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p)) :
    3 ∈ P.image (fun p => p ^ e p) ∨ 9 ∈ P.image (fun p => p ^ e p) := by
  by_contra h
  push Not at h
  let X := P.image (fun p => p ^ e p)
  have hcX : X.card = 9 := (component_card P e hp he).trans hc
  have hsmall : ∀ x ∈ X, x < 26 → x ∈ ({5, 7, 11, 13, 17, 19, 23, 25} : Finset ℕ) := by
    intro x hxm hx26
    obtain ⟨p, hpm, hpx⟩ := Finset.mem_image.mp hxm
    have hl := odd_prime_power_lt_thirty_seven p (e p) (hp p hpm) (ho p hpm)
      (he p hpm) (by omega)
    rw [hpx] at hl
    have hn3 : x ≠ 3 := by intro hx; exact h.1 (hx ▸ hxm)
    have hn9 : x ≠ 9 := by intro hx; exact h.2 (hx ▸ hxm)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl ⊢
    omega
  let b : Fin 9 → ℕ := ![5, 7, 11, 13, 17, 19, 23, 25, 32769]
  have hb : ∀ i, 0 < b i := by decide
  have hcut : ∀ i : Fin 9, i.val < 8 → b i ≤ 26 := by decide
  have hcounts : ∀ i : Fin 9, i.val < 8 →
      (({5, 7, 11, 13, 17, 19, 23, 25} : Finset ℕ).filter (fun x => x < b i)).card ≤ i.val := by
    decide
  have hlargeX : ∃ x ∈ X, 32768 < x := by
    obtain ⟨p, hpm, hpl⟩ := hlarge
    exact ⟨p ^ e p, Finset.mem_image.mpr ⟨p, hpm, rfl⟩, hpl⟩
  have hgap : componentRatio (2 ^ 11) * (∏ i : Fin 9, componentRatio (b i)) < 2 := by
    norm_num [b, componentRatio, Fin.prod_univ_succ]
  exact not_perfect_of_interval_envelope a X {5, 7, 11, 13, 17, 19, 23, 25}
    hcX 26 b ha hb (by rfl) hcut hcounts hsmall hlargeX hgap
    (actual_component_ratio a P e hp he hid)

/-- The first two branch exclusions reduce the actual base-three exponent to
one or two, uniformly over all bases and exponents. The exponent-two branch
is still unpaid here. -/
theorem three_exponent_one_or_two (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hc : P.card = 9) (hp : ∀ p ∈ P, p.Prime) (ho : ∀ p ∈ P, Odd p)
    (he : ∀ p ∈ P, 0 < e p) (ha : 11 ≤ a)
    (hlarge : ∃ p ∈ P, 32768 < p ^ e p)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p)) :
    3 ∈ P ∧ (e 3 = 1 ∨ e 3 = 2) := by
  have h3 := three_mem_of_nine_odd a P e hc hp ho he ha hid
  have hm := three_or_nine_component a P e hc hp ho he ha hlarge hid
  refine ⟨h3, ?_⟩
  rcases hm with hm3 | hm9
  · have hm3' : 3 ^ 1 ∈ P.image (fun p => p ^ e p) := by simpa using hm3
    exact Or.inl ((mem_component_prime_power_iff P e hp he 3 1 (by decide) (by omega)).mp hm3').2
  · have hm9' : 3 ^ 2 ∈ P.image (fun p => p ^ e p) := hm9
    exact Or.inr ((mem_component_prime_power_iff P e hp he 3 2 (by decide) (by omega)).mp hm9').2

/-- In the exponent-two branch, omission of actual component five or seven
contradicts the corresponding exact nine-component envelope. -/
theorem five_seven_component_of_three_exponent_two (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hc : P.card = 9) (hp : ∀ p ∈ P, p.Prime) (ho : ∀ p ∈ P, Odd p)
    (he : ∀ p ∈ P, 0 < e p) (ha : 11 ≤ a)
    (hlarge : ∃ p ∈ P, 32768 < p ^ e p)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p)) (he3 : e 3 = 2)
    (q : ℕ) (hq : q = 5 ∨ q = 7) :
    q ∈ P.image (fun p => p ^ e p) := by
  by_contra hqX
  let X := P.image (fun p => p ^ e p)
  let L : Finset ℕ := ({5, 7, 9, 11, 13, 17, 19, 23, 25} : Finset ℕ).erase q
  have hcX : X.card = 9 := (component_card P e hp he).trans hc
  have hn3 : 3 ∉ X := by
    intro hm3
    have hm3' : 3 ^ 1 ∈ P.image (fun p => p ^ e p) := hm3
    have hexp := ((mem_component_prime_power_iff P e hp he 3 1 (by decide) (by omega)).mp hm3').2
    omega
  have hsmall : ∀ x ∈ X, x < 26 → x ∈ L := by
    intro x hxm hx26
    obtain ⟨p, hpm, hpx⟩ := Finset.mem_image.mp hxm
    have hl := odd_prime_power_lt_thirty_seven p (e p) (hp p hpm) (ho p hpm)
      (he p hpm) (by omega)
    rw [hpx] at hl
    have hx3 : x ≠ 3 := by intro hx; exact hn3 (hx ▸ hxm)
    have hxq : x ≠ q := by intro hx; exact hqX (hx ▸ hxm)
    simp only [L, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hl ⊢
    omega
  let b : Fin 9 → ℕ := if q = 5 then ![7, 9, 11, 13, 17, 19, 23, 25, 32769]
    else ![5, 9, 11, 13, 17, 19, 23, 25, 32769]
  have hb : ∀ i, 0 < b i := by rcases hq with rfl | rfl <;> decide
  have hlast : b 8 = 32769 := by rcases hq with rfl | rfl <;> decide
  have hcut : ∀ i : Fin 9, i.val < 8 → b i ≤ 26 := by rcases hq with rfl | rfl <;> decide
  have hcounts : ∀ i : Fin 9, i.val < 8 → (L.filter (fun x => x < b i)).card ≤ i.val := by
    rcases hq with rfl | rfl <;> decide
  have hlargeX : ∃ x ∈ X, 32768 < x := by
    obtain ⟨p, hpm, hpl⟩ := hlarge
    exact ⟨p ^ e p, Finset.mem_image.mpr ⟨p, hpm, rfl⟩, hpl⟩
  have hgap : componentRatio (2 ^ 11) * (∏ i : Fin 9, componentRatio (b i)) < 2 := by
    rcases hq with rfl | rfl <;> norm_num [b, componentRatio, Fin.prod_univ_succ]
  exact not_perfect_of_interval_envelope a X L hcX 26 b ha hb hlast hcut hcounts
    hsmall hlargeX hgap (actual_component_ratio a P e hp he hid)

/-- In the only remaining higher-exponent branch, five and seven occur as
actual exponent-one components, not merely as prime bases. -/
theorem five_seven_exponent_one_of_three_exponent_two (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hc : P.card = 9) (hp : ∀ p ∈ P, p.Prime) (ho : ∀ p ∈ P, Odd p)
    (he : ∀ p ∈ P, 0 < e p) (ha : 11 ≤ a)
    (hlarge : ∃ p ∈ P, 32768 < p ^ e p)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p)) (he3 : e 3 = 2) :
    (5 ∈ P ∧ e 5 = 1) ∧ (7 ∈ P ∧ e 7 = 1) := by
  have h5 := five_seven_component_of_three_exponent_two a P e hc hp ho he ha hlarge hid he3 5
    (Or.inl rfl)
  have h7 := five_seven_component_of_three_exponent_two a P e hc hp ho he ha hlarge hid he3 7
    (Or.inr rfl)
  have h5' : 5 ^ 1 ∈ P.image (fun p => p ^ e p) := by simpa using h5
  have h7' : 7 ^ 1 ∈ P.image (fun p => p ^ e p) := by simpa using h7
  exact ⟨(mem_component_prime_power_iff P e hp he 5 1 (by decide) (by omega)).mp h5',
    (mem_component_prime_power_iff P e hp he 7 1 (by decide) (by omega)).mp h7'⟩

/-- The successor valuation budget transported to actual component values. -/
theorem actual_valuation_budget (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime) (he : ∀ p ∈ P, 0 < e p)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p)) (h3 : 3 ∈ P) :
    padicValNat 3 (2 ^ a + 1) +
      (∑ x ∈ P.image (fun p => p ^ e p), padicValNat 3 (x + 1)) = e 3 := by
  rw [Finset.sum_image (component_injOn P e hp he)]
  simpa only [if_pos h3] using ordinary_valuation_budget a P e hp hid 3 (by decide) (by decide)

/-- Divisibility by a prime power and nondivisibility by its successor power
certify a natural valuation, with both totalization guards explicit. -/
theorem valuation_eq_of_pow_dvd (q n k : ℕ) (hq : q ≠ 1) (hn : n ≠ 0)
    (hd : q ^ k ∣ n) (hnd : ¬ q ^ (k + 1) ∣ n) : padicValNat q n = k := by
  have hlo := (Nat.pow_dvd_iff_le_padicValNat hq hn).mp hd
  have hhi : ¬ k + 1 ≤ padicValNat q n := by
    intro h
    exact hnd ((Nat.pow_dvd_iff_le_padicValNat hq hn).mpr h)
  omega

/-- In a two-unit budget containing actual five, actual seventeen is impossible
and actual twenty-three and twenty-nine cannot both occur. -/
theorem two_budget_small_exclusions (X : Finset ℕ) (t : ℕ) (h5 : 5 ∈ X)
    (hbudget : t + (∑ x ∈ X, padicValNat 3 (x + 1)) = 2) :
    17 ∉ X ∧ (23 ∉ X ∨ 29 ∉ X) := by
  have hv5 : padicValNat 3 (5 + 1) = 1 := valuation_eq_of_pow_dvd 3 6 1 (by decide) (by decide) (by decide) (by decide)
  have hv17 : padicValNat 3 (17 + 1) = 2 := valuation_eq_of_pow_dvd 3 18 2 (by decide) (by decide) (by decide) (by decide)
  have hv23 : padicValNat 3 (23 + 1) = 1 := valuation_eq_of_pow_dvd 3 24 1 (by decide) (by decide) (by decide) (by decide)
  have hv29 : padicValNat 3 (29 + 1) = 1 := valuation_eq_of_pow_dvd 3 30 1 (by decide) (by decide) (by decide) (by decide)
  constructor
  · intro h17
    have hsub : ({5, 17} : Finset ℕ) ⊆ X := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h5
      · exact h17
    have hsum := Finset.sum_le_sum_of_subset hsub (f := fun x => padicValNat 3 (x + 1))
    norm_num [hv5, hv17] at hsum
    omega
  · by_contra h
    push Not at h
    have hsub : ({5, 23, 29} : Finset ℕ) ⊆ X := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact h5
      · exact h.1
      · exact h.2
    have hsum := Finset.sum_le_sum_of_subset hsub (f := fun x => padicValNat 3 (x + 1))
    norm_num [hv5, hv23, hv29] at hsum
    omega

/-- With actual five and eleven present, their successors exhaust a two-unit
three-adic budget. The binary successor and every other successor are coprime to three. -/
theorem two_budget_exhausted (X : Finset ℕ) (u : ℕ) (h5 : 5 ∈ X) (h11 : 11 ∈ X)
    (hbudget : padicValNat 3 (u + 1) + (∑ x ∈ X, padicValNat 3 (x + 1)) = 2) :
    ¬ 3 ∣ u + 1 ∧ ∀ x ∈ X, x ≠ 5 → x ≠ 11 → ¬ 3 ∣ x + 1 := by
  have hsub : ({5, 11} : Finset ℕ) ⊆ X := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h5
    · exact h11
  have hsum := Finset.sum_le_sum_of_subset hsub (f := fun x => padicValNat 3 (x + 1))
  have hv5 : padicValNat 3 6 = 1 := valuation_eq_of_pow_dvd 3 6 1 (by decide) (by decide) (by decide) (by decide)
  have hv11 : padicValNat 3 12 = 1 := valuation_eq_of_pow_dvd 3 12 1 (by decide) (by decide) (by decide) (by decide)
  norm_num [hv5, hv11] at hsum
  have huval : padicValNat 3 (u + 1) = 0 := by omega
  have hu : ¬ 3 ∣ u + 1 := by
    simpa using padicValNat.eq_zero_iff.mp huval
  refine ⟨hu, ?_⟩
  intro x hxm hx5 hx11
  have hsubx : ({5, 11, x} : Finset ℕ) ⊆ X := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact h5
    · exact h11
    · exact hxm
  have hsumx := Finset.sum_le_sum_of_subset hsubx (f := fun x => padicValNat 3 (x + 1))
  have h5x : (5 : ℕ) ≠ x := Ne.symm hx5
  have h11x : (11 : ℕ) ≠ x := Ne.symm hx11
  simp only [Finset.sum_insert (by simp [h5x] : (5 : ℕ) ∉ {11, x}),
    Finset.sum_insert (by simp [h11x] : (11 : ℕ) ∉ {x}), Finset.sum_singleton] at hsumx
  norm_num [hv5, hv11] at hsumx
  have hxval : padicValNat 3 (x + 1) = 0 := by omega
  simpa using padicValNat.eq_zero_iff.mp hxval

/-- A binary power successor coprime to three has even exponent. -/
theorem even_of_binary_successor_not_dvd_three (a : ℕ) (h : ¬ 3 ∣ 2 ^ a + 1) : Even a := by
  rcases Nat.even_or_odd a with ha | ha
  · exact ha
  · have hz : (2 : ZMod 3) = -1 := by decide
    have heq : (2 : ZMod 3) ^ a + 1 = 0 := by rw [hz, ha.neg_one_pow]; ring
    have hd : 3 ∣ 2 ^ a + 1 := by
      apply (ZMod.natCast_eq_zero_iff (2 ^ a + 1) 3).mp
      simpa using heq
    exact (h hd).elim

/-- Joint satisfiable two-unit budget model used by the valuation helpers. -/
theorem two_budget_model :
    let X : Finset ℕ := {5, 7, 9, 11}
    5 ∈ X ∧ 11 ∈ X ∧
      padicValNat 3 (2 ^ 12 + 1) + (∑ x ∈ X, padicValNat 3 (x + 1)) = 2 := by
  have h6 : padicValNat 3 6 = 1 := valuation_eq_of_pow_dvd 3 6 1 (by decide) (by decide) (by decide) (by decide)
  have h12 : padicValNat 3 12 = 1 := valuation_eq_of_pow_dvd 3 12 1 (by decide) (by decide) (by decide) (by decide)
  have h8 : padicValNat 3 8 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
  have h10 : padicValNat 3 10 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
  have h4097 : padicValNat 3 4097 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
  norm_num [h6, h12, h8, h10, h4097]

/-- Under the derived exponent-two small-component constraints, the last
absent-eleven envelope forces actual eleven. -/
theorem eleven_mem_of_two_budget (a : ℕ) (X : Finset ℕ) (hc : X.card = 9)
    (ha : 11 ≤ a) (hlarge : ∃ x ∈ X, 32768 < x)
    (hratio : componentRatio (2 ^ a) * (∏ x ∈ X, componentRatio x) = 2)
    (h5 : 5 ∈ X) (hbudget : padicValNat 3 (2 ^ a + 1) +
      (∑ x ∈ X, padicValNat 3 (x + 1)) = 2)
    (hn3 : 3 ∉ X) (hn25 : 25 ∉ X) (hn27 : 27 ∉ X)
    (hclass : ∀ x ∈ X, x < 37 →
      x ∈ ({3, 5, 7, 9, 11, 13, 17, 19, 23, 25, 27, 29, 31} : Finset ℕ)) : 11 ∈ X := by
  by_contra hn11
  obtain ⟨hn17, hdisj⟩ := two_budget_small_exclusions X _ h5 hbudget
  obtain ⟨q, hq, hnq⟩ : ∃ q, (q = 23 ∨ q = 29) ∧ q ∉ X := by
    rcases hdisj with h23 | h29
    · exact ⟨23, Or.inl rfl, h23⟩
    · exact ⟨29, Or.inr rfl, h29⟩
  let L : Finset ℕ := ({5, 7, 9, 13, 19, 23, 29, 31} : Finset ℕ).erase q
  have hsmall : ∀ x ∈ X, x < 37 → x ∈ L := by
    intro x hxm hx37
    have hl := hclass x hxm hx37
    have hx3 : x ≠ 3 := by intro hx; exact hn3 (hx ▸ hxm)
    have hx11 : x ≠ 11 := by intro hx; exact hn11 (hx ▸ hxm)
    have hx17 : x ≠ 17 := by intro hx; exact hn17 (hx ▸ hxm)
    have hx25 : x ≠ 25 := by intro hx; exact hn25 (hx ▸ hxm)
    have hx27 : x ≠ 27 := by intro hx; exact hn27 (hx ▸ hxm)
    have hxq : x ≠ q := by intro hx; exact hnq (hx ▸ hxm)
    simp only [L, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hl ⊢
    omega
  let b : Fin 9 → ℕ := ![5, 7, 9, 13, 19, 23, 31, 37, 32769]
  have hb : ∀ i, 0 < b i := by decide
  have hcut : ∀ i : Fin 9, i.val < 8 → b i ≤ 37 := by decide
  have hcounts : ∀ i : Fin 9, i.val < 8 → (L.filter (fun x => x < b i)).card ≤ i.val := by
    rcases hq with rfl | rfl <;> decide
  have hgap : componentRatio (2 ^ 11) * (∏ i : Fin 9, componentRatio (b i)) < 2 := by
    norm_num [b, componentRatio, Fin.prod_univ_succ]
  exact not_perfect_of_interval_envelope a X L hc 37 b ha hb (by rfl) hcut hcounts
    hsmall hlarge hgap hratio

/-- The final present-eleven envelope contradicts perfection once the three-adic
budget is exhausted and every non-nine component is coprime to three. -/
theorem not_perfect_of_two_budget_eleven (a : ℕ) (X : Finset ℕ) (hc : X.card = 9)
    (ha : 11 ≤ a) (hlarge : ∃ x ∈ X, 32768 < x)
    (h5 : 5 ∈ X) (h11 : 11 ∈ X)
    (hbudget : padicValNat 3 (2 ^ a + 1) + (∑ x ∈ X, padicValNat 3 (x + 1)) = 2)
    (hn25 : 25 ∉ X)
    (hcop : ∀ x ∈ X, x ≠ 9 → ¬ 3 ∣ x)
    (hclass : ∀ x ∈ X, x < 37 →
      x ∈ ({3, 5, 7, 9, 11, 13, 17, 19, 23, 25, 27, 29, 31} : Finset ℕ)) :
    componentRatio (2 ^ a) * (∏ x ∈ X, componentRatio x) ≠ 2 := by
  obtain ⟨ha3, hsucc⟩ := two_budget_exhausted X (2 ^ a) h5 h11 hbudget
  have heven := even_of_binary_successor_not_dvd_three a ha3
  have ha12 : 12 ≤ a := by
    obtain ⟨k, hk⟩ := heven
    omega
  have hsmall : ∀ x ∈ X, x < 37 → x ∈ ({5, 7, 9, 11, 13, 19, 31} : Finset ℕ) := by
    intro x hxm hx37
    have hl := hclass x hxm hx37
    by_cases hx5 : x = 5
    · simp [hx5]
    by_cases hx9 : x = 9
    · simp [hx9]
    by_cases hx11 : x = 11
    · simp [hx11]
    have hnc := hcop x hxm hx9
    have hns := hsucc x hxm hx5 hx11
    rw [Nat.dvd_iff_mod_eq_zero] at hnc hns
    have hxmod : x % 3 = 1 := by omega
    have hx25 : x ≠ 25 := by intro hx; exact hn25 (hx ▸ hxm)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl ⊢
    omega
  let b : Fin 9 → ℕ := ![5, 7, 9, 11, 13, 19, 31, 37, 32769]
  have hb : ∀ i, 0 < b i := by decide
  have hdom : ∀ i, b i ≤ X.orderEmbOfFin hc i := by
    intro i
    by_cases hi : i.val < 8
    · apply sorted_component_lower
      have hcut : b i ≤ 37 := by fin_cases i <;> simp_all [b]
      have hcounts : (({5, 7, 9, 11, 13, 19, 31} : Finset ℕ).filter (fun x => x < b i)).card ≤ i.val := by
        fin_cases i <;> decide
      exact (count_lt_le_of_small_list X {5, 7, 9, 11, 13, 19, 31} 37 (b i) hcut hsmall).trans hcounts
    · have hi8 : i = 8 := by apply Fin.ext; omega
      subst i
      exact sorted_last_lower X hc (by omega) 32769 (by
        obtain ⟨x, hxm, hx⟩ := hlarge
        exact ⟨x, hxm, by omega⟩)
  have hgap : componentRatio (2 ^ 12) * (∏ i : Fin 9, componentRatio (b i)) < 2 := by
    norm_num [b, componentRatio, Fin.prod_univ_succ]
  exact not_perfect_of_sorted_envelope a X hc b 12 ha12 hb hdom hgap

/-- Uniform nine-odd reduction: the full ordinary factorized unitary identity,
exactly nine distinct odd prime bases with positive exponents, and Wall's two
explicit bounds force actual component three with exponent one. The sourced
bounds remain hypotheses. No fixed core, bounded base range, or exponent cap
is assumed; this is not a global exclusion of nine odd bases. -/
theorem three_mem_and_exponent_one (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hc : P.card = 9) (hp : ∀ p ∈ P, p.Prime) (ho : ∀ p ∈ P, Odd p)
    (he : ∀ p ∈ P, 0 < e p) (ha : 11 ≤ a)
    (hlarge : ∃ p ∈ P, 32768 < p ^ e p)
    (hid : (2 ^ a + 1) * (∏ p ∈ P, (p ^ e p + 1)) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p)) : 3 ∈ P ∧ e 3 = 1 := by
  obtain ⟨h3, he3cases⟩ := three_exponent_one_or_two a P e hc hp ho he ha hlarge hid
  refine ⟨h3, ?_⟩
  rcases he3cases with he31 | he32
  · exact he31
  · obtain ⟨⟨h5, he5⟩, ⟨h7, he7⟩⟩ :=
      five_seven_exponent_one_of_three_exponent_two a P e hc hp ho he ha hlarge hid he32
    let X := P.image (fun p => p ^ e p)
    have hcX : X.card = 9 := (component_card P e hp he).trans hc
    have h5X : 5 ∈ X := Finset.mem_image.mpr ⟨5, h5, by rw [he5, pow_one]⟩
    have hratio : componentRatio (2 ^ a) * (∏ x ∈ X, componentRatio x) = 2 :=
      actual_component_ratio a P e hp he hid
    have hbudget : padicValNat 3 (2 ^ a + 1) + (∑ x ∈ X, padicValNat 3 (x + 1)) = 2 := by
      simpa only [he32] using actual_valuation_budget a P e hp he hid h3
    have hn3 : 3 ∉ X := by
      intro hm
      have hm' : 3 ^ 1 ∈ P.image (fun p => p ^ e p) := hm
      have hx := ((mem_component_prime_power_iff P e hp he 3 1 (by decide) (by omega)).mp hm').2
      omega
    have hn25 : 25 ∉ X := by
      intro hm
      have hm' : 5 ^ 2 ∈ P.image (fun p => p ^ e p) := hm
      have hx := ((mem_component_prime_power_iff P e hp he 5 2 (by decide) (by omega)).mp hm').2
      omega
    have hn27 : 27 ∉ X := by
      intro hm
      have hm' : 3 ^ 3 ∈ P.image (fun p => p ^ e p) := hm
      have hx := ((mem_component_prime_power_iff P e hp he 3 3 (by decide) (by omega)).mp hm').2
      omega
    have hlargeX : ∃ x ∈ X, 32768 < x := by
      obtain ⟨p, hpm, hpl⟩ := hlarge
      exact ⟨p ^ e p, Finset.mem_image.mpr ⟨p, hpm, rfl⟩, hpl⟩
    have hclass : ∀ x ∈ X, x < 37 →
        x ∈ ({3, 5, 7, 9, 11, 13, 17, 19, 23, 25, 27, 29, 31} : Finset ℕ) := by
      intro x hxm hx37
      obtain ⟨p, hpm, rfl⟩ := Finset.mem_image.mp hxm
      exact odd_prime_power_lt_thirty_seven p (e p) (hp p hpm) (ho p hpm) (he p hpm) hx37
    have hcop : ∀ x ∈ X, x ≠ 9 → ¬ 3 ∣ x := by
      intro x hxm hx9 hd
      obtain ⟨p, hpm, hpx⟩ := Finset.mem_image.mp hxm
      rw [← hpx] at hd
      have hbase := (by decide : Nat.Prime 3).dvd_of_dvd_pow hd
      have h3p := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) (hp p hpm)).mp hbase
      subst p
      rw [he32] at hpx
      exact hx9 hpx.symm
    have h11X := eleven_mem_of_two_budget a X hcX ha hlargeX hratio h5X hbudget hn3 hn25 hn27 hclass
    exact (not_perfect_of_two_budget_eleven a X hcX ha hlargeX h5X h11X hbudget hn25 hcop hclass hratio).elim

end Erdos1052.NineOdd
