/-
# Bajnok–Beatty: largest noncyclic abelian group with an `s`-spanning pair

B. Bajnok and W. K. Beatty, *On the Diameter of Undirected Cayley Graphs of
Finite Abelian Groups*, arXiv:2406.04045 (2024), Conjecture 1.6.

For `3 ≤ s`, this module proves the conjectured upper bound for every finite
noncyclic abelian group with an `s`-spanning pair, including the product form
`ℤ_c × ℤ_{ck}` for `2 ≤ c`. It also proves `|G| ≤ 2s² + 2s - 4`.
The general lower bounds of the paper's Theorem 1.7 are not formalized here;
sharpness is exhibited only at `s = 3`. The paper proves partial upper bounds
for `s`-regular groups (Theorems 3.1–3.3) and for `c = 2` (Theorem 4.2).

An `s`-spanning pair `{a₁, a₂}` means that every element is
`λ₁ a₁ + λ₂ a₂` with `λᵢ ∈ ℤ` and `|λ₁| + |λ₂| ≤ s`.

## Proof (elementary, two steps)

1. Fiber reduction (`le_classCount`).  Reduce `G = ℤ_c × ℤ_{ck}` onto
   `(ℤ/c)²` by `π (x, y) = (x, y mod c)`.  The map `l ↦ π (l₁ a₁ + l₂ a₂)`
   factors through `l mod c` via a map `ψ : (ℤ/c)² → (ℤ/c)²`, which is
   surjective (spanning) hence bijective.  Each fiber of `π` has `k`
   elements, and each must be hit by a distinct `l ∈ I(s)` lying in one fixed
   residue class mod `c`.  Hence `k ≤ classCount s c r` for EVERY class `r`;
   no `s`-regularity is needed.
2. Counting (`exists_classCount_le`).  Rotating `(u, v) = (l₁ + l₂, l₁ - l₂)`
   bounds a class count by products of one-dimensional counts of
   `[-s, s]` modulo `2c` (`classCount_le`).  With `s = c q + h`, `0 ≤ h < c`,
   an explicit class (`α = s + 1`, `β ∈ {0, ⌊c/2⌋}`) has
   `c² · count ≤ 2 s²`, except when `c ∣ 2s + 1`, where
   `c² · count ≤ 2s² + 2s - (c² - 1)/2 ≤ bbBound s` as `c ≥ minFac (2s+1)`.
-/
import Mathlib

set_option autoImplicit false

namespace BajnokBeattySpanningNoncyclic

open Finset

/-! ## Definitions -/

/-- `{a₁, a₂}` is an `s`-spanning pair of the abelian group `G`: every `g : G` is
`l₁ • a₁ + l₂ • a₂` for integers with `|l₁| + |l₂| ≤ s` (Bajnok–Beatty, Section 1–2).
Distinctness of `a₁, a₂` is not required; the upper bound below holds without it. -/
def IsSSpanning {G : Type*} [AddCommGroup G] (s : ℕ) (a₁ a₂ : G) : Prop :=
  ∀ g : G, ∃ l₁ l₂ : ℤ, |l₁| + |l₂| ≤ (s : ℤ) ∧ l₁ • a₁ + l₂ • a₂ = g

/-- The conjectured maximal order `B(s)` of Conjecture 1.6: `2 s²` if `2s + 1` is prime,
and `2s² + 2s - (p² - 1)/2` with `p` the least prime factor of `2s + 1` otherwise.
(The natural subtraction never truncates: `p² ≤ 2s + 1`, see `two_mul_sq_le_bbBound`.) -/
def bbBound (s : ℕ) : ℕ :=
  if (2 * s + 1).Prime then 2 * s ^ 2
  else 2 * s ^ 2 + 2 * s - ((2 * s + 1).minFac ^ 2 - 1) / 2

/-- The index set `I(s) = {(l₁, l₂) ∈ ℤ² : |l₁| + |l₂| ≤ s}` (paper, Lemma 2.1). -/
noncomputable def diamond (s : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(s : ℤ)) s ×ˢ Finset.Icc (-(s : ℤ)) s).filter (fun l => |l.1| + |l.2| ≤ s)

/-- The number of points of `I(s)` in the residue class `r` modulo `c`. -/
noncomputable def classCount (s c : ℕ) (r : ZMod c × ZMod c) : ℕ :=
  ((diamond s).filter (fun l => ((l.1 : ZMod c), (l.2 : ZMod c)) = r)).card

/-- The integers of `[-s, s]` congruent to `x` modulo `M`. -/
noncomputable def resSet (s : ℕ) (M x : ℤ) : Finset ℤ :=
  (Finset.Icc (-(s : ℤ)) s).filter (fun y => y ≡ x [ZMOD M])

/-! ## Examples -/

/-- `B(3) = 18` (`7` prime). -/
example : bbBound 3 = 18 := by decide
/-- `B(4) = 36` (`9 = 3²`). -/
example : bbBound 4 = 36 := by norm_num [bbBound]
/-- `B(7) = 108` (`15`, `p = 3`). -/
example : bbBound 7 = 108 := by norm_num [bbBound]
/-- `B(12) = 300` (`25`, `p = 5`). -/
example : bbBound 12 = 300 := by norm_num [bbBound]
/-- `|I(3)| = 2·3² + 2·3 + 1 = 25` (paper, Lemma 2.1(3)). -/
example : (diamond 3).card = 25 := by decide
/-- Class `(0,0)` mod `3` in `I(3)`: `(0,0), (±3,0), (0,±3)`. -/
example : classCount 3 3 (0, 0) = 5 := by decide

/-! ## One-dimensional counts -/


/-- A finset of integers in `[a, b]`, all congruent to `x` modulo `M > 0`, has at most `n`
elements when `b - a < M n`. -/
theorem card_le_of_modEq {T : Finset ℤ} {a b M x : ℤ} {n : ℕ} (hM : 0 < M)
    (hT : ∀ y ∈ T, a ≤ y ∧ y ≤ b ∧ y ≡ x [ZMOD M]) (hn : b - a < M * n) : T.card ≤ n := by
  have hmaps : Set.MapsTo (fun y => ((y - a) / M).toNat) (T : Set ℤ) (range n : Set ℕ) := by
    intro y hy
    obtain ⟨hay, hyb, -⟩ := hT y hy
    have h0 : 0 ≤ (y - a) / M := Int.ediv_nonneg (by omega) hM.le
    have h1 : (y - a) / M < n := by
      rw [Int.ediv_lt_iff_lt_mul hM]
      linarith
    simp only [coe_range, Set.mem_Iio]
    omega
  have hinj : Set.InjOn (fun y => ((y - a) / M).toNat) (T : Set ℤ) := by
    intro y hy y' hy' hyy
    obtain ⟨hay, -, hy⟩ := hT y hy
    obtain ⟨hay', -, hy'⟩ := hT y' hy'
    have h0 : 0 ≤ (y - a) / M := Int.ediv_nonneg (by omega) hM.le
    have h0' : 0 ≤ (y' - a) / M := Int.ediv_nonneg (by omega) hM.le
    have hq : (y - a) / M = (y' - a) / M := by
      simp only at hyy
      omega
    have hr : (y - a) % M = (y' - a) % M := by
      have hmod : y - a ≡ y' - a [ZMOD M] := Int.ModEq.sub_right a (hy.trans hy'.symm)
      exact hmod
    have e1 := Int.mul_ediv_add_emod (y - a) M
    have e2 := Int.mul_ediv_add_emod (y' - a) M
    rw [hq, hr] at e1
    linarith
  simpa using card_le_card_of_injOn _ hmaps hinj


/-- Every residue class modulo `2c` meets `[-s, s]` in at most `n + 1` points when
`s < c (n + 1)`. -/
theorem card_resSet_le_succ {s c n : ℕ} (x : ℤ) (hc : 0 < c) (hs : s < c * (n + 1)) :
    (resSet s (2 * c) x).card ≤ n + 1 := by
  refine card_le_of_modEq (a := -(s : ℤ)) (b := s) (M := 2 * c) (x := x) (by positivity) ?_ ?_
  · intro y hy
    simp only [resSet, mem_filter, Finset.mem_Icc] at hy
    exact ⟨hy.1.1, hy.1.2, hy.2⟩
  · push_cast
    have hs' : (s : ℤ) < c * (n + 1) := by exact_mod_cast hs
    linarith

/-- A residue class modulo `2c` represented by `x > s` meets `[-s, s]` in at most `n`
points when `x + s < 2c (n + 1)` (all its points are `≤ x - 2c`). -/
theorem card_resSet_le_of_lt {s c n : ℕ} {x : ℤ} (hc : 0 < c) (hx : (s : ℤ) < x)
    (hxs : x + s < 2 * c * (n + 1)) : (resSet s (2 * c) x).card ≤ n := by
  refine card_le_of_modEq (a := -(s : ℤ)) (b := x - 2 * c) (M := 2 * c) (x := x) (by positivity) ?_ ?_
  · intro y hy
    simp only [resSet, mem_filter, Finset.mem_Icc] at hy
    obtain ⟨⟨hy1, hy2⟩, hyx⟩ := hy
    refine ⟨hy1, ?_, hyx⟩
    have hdvd : (2 * (c : ℤ)) ∣ x - y := (Int.modEq_iff_dvd).1 hyx
    have hle : 2 * (c : ℤ) ≤ x - y := Int.le_of_dvd (by linarith) hdvd
    linarith
  · linarith

/-- Rotation bound: via `(u, v) = (l₁ + l₂, l₁ - l₂)`, the class `(α, β)` mod `c` of `I(s)`
has at most `n(α+β) n(α-β) + n(α+β+c) n(α-β+c)` points, `n(x) = #([-s, s] ∩ (x + 2cℤ))`. -/
theorem classCount_le (s c : ℕ) (α β : ℤ) :
    classCount s c ((α : ZMod c), (β : ZMod c)) ≤
      (resSet s (2 * c) (α + β)).card * (resSet s (2 * c) (α - β)).card +
      (resSet s (2 * c) (α + β + c)).card * (resSet s (2 * c) (α - β + c)).card := by
  set U := resSet s (2 * c) (α + β) ×ˢ resSet s (2 * c) (α - β) ∪
    resSet s (2 * c) (α + β + c) ×ˢ resSet s (2 * c) (α - β + c) with hU
  have hmaps : Set.MapsTo (fun l : ℤ × ℤ => (l.1 + l.2, l.1 - l.2))
      ((diamond s).filter (fun l => ((l.1 : ZMod c), (l.2 : ZMod c)) = ((α : ZMod c), (β : ZMod c))) : Set (ℤ × ℤ)) (U : Set (ℤ × ℤ)) := by
    rintro ⟨l₁, l₂⟩ hl
    simp only [coe_filter, diamond, mem_filter, mem_product, Finset.mem_Icc, Set.mem_ofPred_eq,
      Prod.mk.injEq] at hl
    obtain ⟨⟨-, hsum⟩, h₁, h₂⟩ := hl
    rw [ZMod.intCast_eq_intCast_iff] at h₁ h₂
    obtain ⟨a, ha⟩ := (Int.modEq_iff_dvd).1 h₁.symm
    obtain ⟨b, hb⟩ := (Int.modEq_iff_dvd).1 h₂.symm
    have hb1 := neg_abs_le l₁
    have hb2 := le_abs_self l₁
    have hb3 := neg_abs_le l₂
    have hb4 := le_abs_self l₂
    have hu1 : -(s : ℤ) ≤ l₁ + l₂ := by linarith
    have hu2 : l₁ + l₂ ≤ s := by linarith
    have hv1 : -(s : ℤ) ≤ l₁ - l₂ := by linarith
    have hv2 : l₁ - l₂ ≤ s := by linarith
    simp only [hU, coe_union, coe_product, Set.mem_union, Set.mem_prod, mem_coe, resSet,
      mem_filter, Finset.mem_Icc]
    rcases Int.even_or_odd (a + b) with ⟨m, hm⟩ | ⟨m, hm⟩
    · left
      refine ⟨⟨⟨hu1, hu2⟩, (Int.modEq_iff_dvd).2 ⟨-m, by linear_combination -ha - hb - (c : ℤ) * hm⟩⟩,
        ⟨⟨hv1, hv2⟩, (Int.modEq_iff_dvd).2 ⟨b - m, by linear_combination -ha + hb - (c : ℤ) * hm⟩⟩⟩
    · right
      refine ⟨⟨⟨hu1, hu2⟩, (Int.modEq_iff_dvd).2 ⟨-m, by linear_combination -ha - hb - (c : ℤ) * hm⟩⟩,
        ⟨⟨hv1, hv2⟩, (Int.modEq_iff_dvd).2 ⟨b - m, by linear_combination -ha + hb - (c : ℤ) * hm⟩⟩⟩
  have hinj : Set.InjOn (fun l : ℤ × ℤ => (l.1 + l.2, l.1 - l.2))
      ((diamond s).filter (fun l => ((l.1 : ZMod c), (l.2 : ZMod c)) = ((α : ZMod c), (β : ZMod c))) : Set (ℤ × ℤ)) := by
    rintro ⟨l₁, l₂⟩ - ⟨l₁', l₂'⟩ - hll
    simp only [Prod.mk.injEq] at hll ⊢
    omega
  calc classCount s c ((α : ZMod c), (β : ZMod c)) ≤ U.card := card_le_card_of_injOn _ hmaps hinj
    _ ≤ _ := by
      refine (card_union_le _ _).trans ?_
      rw [card_product, card_product]


/-- Fiber reduction: if `ℤ_c × ℤ_{ck}` (`c ≥ 2`) has an `s`-spanning pair, then EVERY
residue class `r` mod `c` contains at least `k` points of `I(s)`.  No `s`-regularity
hypothesis is needed. -/
theorem le_classCount {s c k : ℕ} (hc : 2 ≤ c) {a₁ a₂ : ZMod c × ZMod (c * k)}
    (h : IsSSpanning s a₁ a₂) (r : ZMod c × ZMod c) : k ≤ classCount s c r := by
  haveI : NeZero c := ⟨by omega⟩
  let π : ZMod c × ZMod (c * k) →+ ZMod c × ZMod c :=
    AddMonoidHom.prodMap (AddMonoidHom.id _)
      (ZMod.castHom (dvd_mul_right c k) (ZMod c)).toAddMonoidHom
  let ψ : ZMod c × ZMod c → ZMod c × ZMod c := fun m => m.1 • π a₁ + m.2 • π a₂
  have hπψ : ∀ l₁ l₂ : ℤ, π (l₁ • a₁ + l₂ • a₂) = ψ ((l₁ : ZMod c), (l₂ : ZMod c)) := by
    intro l₁ l₂
    simp only [ψ, map_add, map_zsmul, Int.cast_smul_eq_zsmul]
  have hπnat : ∀ (y : ZMod c) (n : ℕ), π (y, (n : ZMod (c * k))) = (y, (n : ZMod c)) := by
    intro y n
    simp [π]
  have hlift : ∀ y : ZMod c × ZMod c, π (y.1, ((y.2.val : ℕ) : ZMod (c * k))) = y := by
    rintro ⟨y₁, y₂⟩
    rw [hπnat, ZMod.natCast_zmod_val]
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨l₁, l₂, -, hl⟩ := h (y.1, ((y.2.val : ℕ) : ZMod (c * k)))
    exact ⟨_, by rw [← hπψ, hl, hlift]⟩
  have hinj : Function.Injective ψ := Finite.injective_iff_surjective.2 hsurj
  let x₀ : ZMod c × ZMod (c * k) := ((ψ r).1, (((ψ r).2.val : ℕ) : ZMod (c * k)))
  let g : ℕ → ZMod c × ZMod (c * k) := fun j => x₀ + (0, ((c * j : ℕ) : ZMod (c * k)))
  have hg : ∀ j, π (g j) = ψ r := by
    intro j
    have h0 : π (0, ((c * j : ℕ) : ZMod (c * k))) = 0 := by
      rw [hπnat]
      simp
    simp only [g, map_add, h0, add_zero, x₀, hlift]
  choose l₁ l₂ hb he using fun j => h (g j)
  have hmaps : Set.MapsTo (fun j => (l₁ j, l₂ j)) (range k : Set ℕ)
      ((diamond s).filter (fun l => ((l.1 : ZMod c), (l.2 : ZMod c)) = r) : Set (ℤ × ℤ)) := by
    intro j _
    have hb1 := neg_abs_le (l₁ j)
    have hb2 := le_abs_self (l₁ j)
    have hb3 := neg_abs_le (l₂ j)
    have hb4 := le_abs_self (l₂ j)
    have hcls : ψ ((l₁ j : ZMod c), (l₂ j : ZMod c)) = ψ r := by
      rw [← hπψ, he, hg]
    simp only [coe_filter, diamond, mem_filter, mem_product, Finset.mem_Icc, Set.mem_ofPred_eq]
    refine ⟨⟨⟨⟨by linarith [hb j], by linarith [hb j]⟩, ⟨by linarith [hb j], by linarith [hb j]⟩⟩, hb j⟩,
      hinj hcls⟩
  have hinjOn : Set.InjOn (fun j => (l₁ j, l₂ j)) (range k : Set ℕ) := by
    intro j hj j' hj' hjj
    simp only [Prod.mk.injEq] at hjj
    simp only [coe_range, Set.mem_Iio] at hj hj'
    have hgg : g j = g j' := by rw [← he, ← he, hjj.1, hjj.2]
    simp only [g, add_right_inj, Prod.mk.injEq, true_and] at hgg
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by nlinarith),
      Nat.mod_eq_of_lt (by nlinarith)] at hgg
    exact Nat.eq_of_mul_eq_mul_left (by omega) hgg
  have hcard := card_le_card_of_injOn _ hmaps hinjOn
  rw [card_range] at hcard
  exact hcard


/-! ## Arithmetic of the bound -/

/-- `2 s² ≤ B(s)`; in the composite case `(p² - 1)/2 ≤ s` because `p² ≤ 2s + 1`. -/
theorem two_mul_sq_le_bbBound (s : ℕ) : 2 * s ^ 2 ≤ bbBound s := by
  unfold bbBound
  split_ifs with hp
  · exact le_rfl
  · have hsq := Nat.minFac_sq_le_self (by omega : 0 < 2 * s + 1) hp
    omega

/-- Case `2h + 1 < c` (with `s = c q + h`): `c² (q² + q²) ≤ 2 s²`. -/
theorem arith_small {s c q h : ℕ} (hs : s = c * q + h) :
    c ^ 2 * (q * q + q * q) ≤ 2 * s ^ 2 := by
  subst hs
  nlinarith [Nat.zero_le (c * q * h), Nat.zero_le (h * h)]

/-- Case `h + 1 = c`, `c ≥ 3`, `s ≥ 3`: `c² (q² + (q+1)²) ≤ 2 s²`. -/
theorem arith_top {s c q h : ℕ} (hs : s = c * q + h) (hh : h + 1 = c) (hc : 3 ≤ c)
    (hs3 : 3 ≤ s) : c ^ 2 * (q * q + (q + 1) * (q + 1)) ≤ 2 * s ^ 2 := by
  subst hs
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    nlinarith
  · nlinarith [Nat.mul_le_mul hq (Nat.le_refl c), Nat.zero_le (c * q * (c - 3))]

/-- Case `c ≤ 2h`: `c² · 2q(q+1) ≤ 2 s²`. -/
theorem arith_mid {s c q h : ℕ} (hs : s = c * q + h) (hle : c ≤ 2 * h) :
    c ^ 2 * (q * (q + 1) + (q + 1) * q) ≤ 2 * s ^ 2 := by
  subst hs
  nlinarith [Nat.mul_le_mul_left (c * q) hle, Nat.zero_le (h * h)]

/-- Case `2h + 1 = c`, i.e. `c ∣ 2s + 1`: `c² · 2q(q+1) = 2s² + 2s - (c² - 1)/2 ≤ B(s)`,
using `c ≥ minFac (2s + 1)` (and `q = 0` if `2s + 1` is prime). -/
theorem arith_div {s c q h : ℕ} (hs : s = c * q + h) (hh : 2 * h + 1 = c) (hc : 2 ≤ c) :
    c ^ 2 * (q * (q + 1) + (q + 1) * q) ≤ bbBound s := by
  have hdvd : c ∣ 2 * s + 1 := ⟨2 * q + 1, by subst hs; linarith⟩
  have hkey : 2 * (c ^ 2 * (q * (q + 1) + (q + 1) * q)) + c ^ 2 = 4 * s ^ 2 + 4 * s + 1 := by
    subst hs; rw [← hh]; ring
  unfold bbBound
  split_ifs with hp
  · rcases hp.eq_one_or_self_of_dvd c hdvd with h1 | h1
    · omega
    · have hq : q = 0 := by
        subst hs
        nlinarith
      subst hq
      simp
  · have hpc : (2 * s + 1).minFac ≤ c := Nat.minFac_le_of_dvd hc hdvd
    have hp2 : (2 * s + 1).minFac ^ 2 ≤ c ^ 2 := Nat.pow_le_pow_left hpc 2
    have hp1 : 1 ≤ (2 * s + 1).minFac ^ 2 := Nat.one_le_pow _ _ (Nat.minFac_pos _)
    omega

/-- Case `c ≤ 2h + 1`: `c² · 2q(q+1) ≤ B(s)`. -/
theorem arith_large {s c q h : ℕ} (hs : s = c * q + h) (hle : c ≤ 2 * h + 1) (hc : 2 ≤ c) :
    c ^ 2 * (q * (q + 1) + (q + 1) * q) ≤ bbBound s := by
  rcases Nat.lt_or_ge (2 * h) c with hlt | hge
  · exact arith_div hs (by omega) hc
  · exact (arith_mid hs hge).trans (two_mul_sq_le_bbBound s)

/-! ## The counting lemma -/

/-- Counting lemma: for `s ≥ 3`, `c ≥ 2` some residue class `r` modulo `c` satisfies
`c² · #(I(s) ∩ r) ≤ B(s)`. -/
theorem exists_classCount_le (s c : ℕ) (hs : 3 ≤ s) (hc : 2 ≤ c) :
    ∃ r : ZMod c × ZMod c, c ^ 2 * classCount s c r ≤ bbBound s := by
  set q := s / c with hq
  set h := s % c with hh
  have hsq : s = c * q + h := (Nat.div_add_mod s c).symm
  have hhc : h < c := Nat.mod_lt s (by omega)
  have hsZ : (s : ℤ) = c * q + h := by exact_mod_cast hsq
  have hcZ : (2 : ℤ) ≤ c := by exact_mod_cast hc
  have hhcZ : (h : ℤ) < c := by exact_mod_cast hhc
  -- the two one-dimensional bounds
  have hP : ∀ x : ℤ, (s : ℤ) < x → x + s < 2 * c * (q + 1) →
      (resSet s (2 * c) x).card ≤ q :=
    fun x h1 h2 => card_resSet_le_of_lt (by omega) h1 h2
  have hP1 : ∀ x : ℤ, (resSet s (2 * c) x).card ≤ q + 1 :=
    fun x => card_resSet_le_succ x (by omega) (by nlinarith)
  by_cases hA : 2 * h + 1 < c
  · -- class `(s + 1, 0)`: all four one-dimensional counts are `≤ q`
    have hAZ : 2 * (h : ℤ) + 1 < c := by exact_mod_cast hA
    refine ⟨((((s : ℤ) + 1 : ℤ) : ZMod c), ((0 : ℤ) : ZMod c)), ?_⟩
    have e1 := hP ((s : ℤ) + 1 + 0) (by linarith) (by linarith)
    have e2 := hP ((s : ℤ) + 1 - 0) (by linarith) (by linarith)
    have e3 := hP ((s : ℤ) + 1 + 0 + c) (by linarith) (by linarith)
    have e4 := hP ((s : ℤ) + 1 - 0 + c) (by linarith) (by linarith)
    calc c ^ 2 * classCount s c _
        ≤ c ^ 2 * (q * q + q * q) :=
          Nat.mul_le_mul_left _ ((classCount_le s c _ _).trans
            (add_le_add (Nat.mul_le_mul e1 e2) (Nat.mul_le_mul e3 e4)))
      _ ≤ 2 * s ^ 2 := arith_small hsq
      _ ≤ bbBound s := two_mul_sq_le_bbBound s
  · have hAZ : (c : ℤ) ≤ 2 * h + 1 := by
      have hle : c ≤ 2 * h + 1 := by omega
      exact_mod_cast hle
    rcases Nat.even_or_odd' c with ⟨b, hb | hb⟩
    · -- `c = 2b`: class `(s + 1 - b, b)`
      have hbZ : (c : ℤ) = 2 * b := by exact_mod_cast hb
      refine ⟨((((s : ℤ) + 1 - b : ℤ) : ZMod c), (((b : ℤ) : ℤ) : ZMod c)), ?_⟩
      have e1 := hP ((s : ℤ) + 1 - b + b) (by linarith) (by linarith)
      have e2 := hP1 ((s : ℤ) + 1 - b - b)
      have e3 := hP1 ((s : ℤ) + 1 - b + b + c)
      have e4 := hP ((s : ℤ) + 1 - b - b + c) (by linarith) (by linarith)
      calc c ^ 2 * classCount s c _
          ≤ c ^ 2 * (q * (q + 1) + (q + 1) * q) :=
            Nat.mul_le_mul_left _ ((classCount_le s c _ _).trans
              (add_le_add (Nat.mul_le_mul e1 e2) (Nat.mul_le_mul e3 e4)))
        _ ≤ bbBound s := arith_large hsq (by omega) hc
    · have hbZ : (c : ℤ) = 2 * b + 1 := by exact_mod_cast hb
      by_cases htop : h + 1 = c
      · -- `c` odd, `h = c - 1`: class `(s + 1, 0)`
        have htopZ : (h : ℤ) + 1 = c := by exact_mod_cast htop
        refine ⟨((((s : ℤ) + 1 : ℤ) : ZMod c), ((0 : ℤ) : ZMod c)), ?_⟩
        have e1 := hP ((s : ℤ) + 1 + 0) (by linarith) (by linarith)
        have e2 := hP ((s : ℤ) + 1 - 0) (by linarith) (by linarith)
        have e3 := hP1 ((s : ℤ) + 1 + 0 + c)
        have e4 := hP1 ((s : ℤ) + 1 - 0 + c)
        calc c ^ 2 * classCount s c _
            ≤ c ^ 2 * (q * q + (q + 1) * (q + 1)) :=
              Nat.mul_le_mul_left _ ((classCount_le s c _ _).trans
                (add_le_add (Nat.mul_le_mul e1 e2) (Nat.mul_le_mul e3 e4)))
          _ ≤ 2 * s ^ 2 := arith_top hsq htop (by omega) hs
          _ ≤ bbBound s := two_mul_sq_le_bbBound s
      · -- `c = 2b + 1`, `h ≤ c - 2`: class `(s + 1 - b, b)`
        have htopZ : (h : ℤ) + 2 ≤ c := by
          have hle : h + 2 ≤ c := by omega
          exact_mod_cast hle
        refine ⟨((((s : ℤ) + 1 - b : ℤ) : ZMod c), (((b : ℤ) : ℤ) : ZMod c)), ?_⟩
        have e1 := hP ((s : ℤ) + 1 - b + b) (by linarith) (by linarith)
        have e2 := hP1 ((s : ℤ) + 1 - b - b)
        have e3 := hP1 ((s : ℤ) + 1 - b + b + c)
        have e4 := hP ((s : ℤ) + 1 - b - b + c) (by linarith) (by linarith)
        calc c ^ 2 * classCount s c _
            ≤ c ^ 2 * (q * (q + 1) + (q + 1) * q) :=
              Nat.mul_le_mul_left _ ((classCount_le s c _ _).trans
                (add_le_add (Nat.mul_le_mul e1 e2) (Nat.mul_le_mul e3 e4)))
          _ ≤ bbBound s := arith_large hsq (by omega) hc

/-! ## Main theorem -/

/-- **Upper bound of Bajnok–Beatty Conjecture 1.6** (arXiv:2406.04045).
Let `s ≥ 3` and `c ≥ 2`.  If `ℤ_c × ℤ_{ck}` has an `s`-spanning pair `{a₁, a₂}`, then its
order `c² k` is at most `B(s)`, where `B(s) = 2s²` if `2s + 1` is prime and
`B(s) = 2s² + 2s - (p² - 1)/2` (`p` the least prime factor of `2s + 1`) otherwise. -/
theorem bajnok_beatty_upper {s c k : ℕ} (hs : 3 ≤ s) (hc : 2 ≤ c)
    {a₁ a₂ : ZMod c × ZMod (c * k)} (h : IsSSpanning s a₁ a₂) : c ^ 2 * k ≤ bbBound s := by
  obtain ⟨r, hr⟩ := exists_classCount_le s c hs hc
  exact (Nat.mul_le_mul_left _ (le_classCount hc h r)).trans hr


/-- `B(s) ≤ 2s² + 2s - 4` for `s ≥ 3` (stated additively): the least prime factor of the
odd number `2s + 1` is at least `3`. -/
theorem bbBound_add_four_le {s : ℕ} (hs : 3 ≤ s) : bbBound s + 4 ≤ 2 * s ^ 2 + 2 * s := by
  unfold bbBound
  split_ifs with hp
  · nlinarith
  · have hsq := Nat.minFac_sq_le_self (by omega : 0 < 2 * s + 1) hp
    have hprime : (2 * s + 1).minFac.Prime := Nat.minFac_prime (by omega)
    have hne2 : (2 * s + 1).minFac ≠ 2 := by
      intro h2
      have hdvd := Nat.minFac_dvd (2 * s + 1)
      rw [h2] at hdvd
      omega
    have hp3 : 3 ≤ (2 * s + 1).minFac := by
      have := hprime.two_le
      omega
    have hp9 : 9 ≤ (2 * s + 1).minFac ^ 2 := by
      simpa using Nat.pow_le_pow_left hp3 2
    omega

/-- Order form of the main theorem: `|ℤ_c × ℤ_{ck}| ≤ B(s)` whenever the group has an
`s`-spanning pair, `s ≥ 3`, `c ≥ 2`. -/
theorem card_le_bbBound {s c k : ℕ} (hs : 3 ≤ s) (hc : 2 ≤ c)
    {a₁ a₂ : ZMod c × ZMod (c * k)} (h : IsSSpanning s a₁ a₂) :
    Nat.card (ZMod c × ZMod (c * k)) ≤ bbBound s := by
  have hcard : Nat.card (ZMod c × ZMod (c * k)) = c ^ 2 * k := by
    rw [Nat.card_prod, Nat.card_zmod, Nat.card_zmod]
    ring
  rw [hcard]
  exact bajnok_beatty_upper hs hc h

/-- The "in particular" clause of Conjecture 1.6: a group `ℤ_c × ℤ_{ck}` (`c ≥ 2`) with an
`s`-spanning pair, `s ≥ 3`, has order at most `2s² + 2s - 4` (stated additively). -/
theorem card_add_four_le {s c k : ℕ} (hs : 3 ≤ s) (hc : 2 ≤ c)
    {a₁ a₂ : ZMod c × ZMod (c * k)} (h : IsSSpanning s a₁ a₂) :
    Nat.card (ZMod c × ZMod (c * k)) + 4 ≤ 2 * s ^ 2 + 2 * s :=
  (Nat.add_le_add_right (card_le_bbBound hs hc h) 4).trans (bbBound_add_four_le hs)

/-! ## General finite noncyclic abelian groups -/


/-- `#G[p m] ≤ #G[p] · #G[m]`, where `G[n] = {x | n • x = 0}`: multiplication by `m` maps
`G[p m]` into `G[p]` with fibers translates of subsets of `G[m]`. -/
theorem card_torsion_mul_le {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] (p m : ℕ) :
    #{x : G | (p * m) • x = 0} ≤ #{x : G | p • x = 0} * #{x : G | m • x = 0} := by
  set s : Finset G := {x : G | (p * m) • x = 0} with hs
  have hfib : ∀ b ∈ s.image (fun x => m • x), #{x ∈ s | m • x = b} ≤ #{x : G | m • x = 0} := by
    intro b hb
    obtain ⟨x₀, -, rfl⟩ := Finset.mem_image.1 hb
    refine card_le_card_of_injOn (fun x => x - x₀) ?_ ?_
    · intro x hx
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
      rw [smul_sub, hx.2, sub_self]
    · intro x _ y _ hxy
      simpa using hxy
  have himg : s.image (fun x => m • x) ⊆ ({x : G | p • x = 0} : Finset G) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    simp only [hs, Finset.mem_filter, mem_univ, true_and] at hx ⊢
    rw [smul_smul]
    exact hx
  calc #s ≤ #{x : G | m • x = 0} * #(s.image (fun x => m • x)) := card_le_mul_card_image s _ hfib
    _ ≤ #{x : G | m • x = 0} * #{x : G | p • x = 0} := Nat.mul_le_mul_left _ (card_le_card himg)
    _ = _ := mul_comm _ _

/-- If `#G[p] ≤ p` for every prime `p`, then `#G[n] ≤ n` for every `n > 0`. -/
theorem card_torsion_le_of_prime {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hp : ∀ p : ℕ, p.Prime → #{x : G | p • x = 0} ≤ p) (n : ℕ) (hn : 0 < n) :
    #{x : G | n • x = 0} ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · obtain rfl : n = 1 := by omega
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, mem_univ, true_and, one_smul] at ha hb
    rw [ha, hb]
  · have hpp : n.minFac.Prime := Nat.minFac_prime (by omega)
    obtain ⟨m, hm⟩ := Nat.minFac_dvd n
    have hp2 := hpp.two_le
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0, mul_zero] at hm; omega
      · exact h0
    have hmn : m < n := by nlinarith
    calc #{x : G | n • x = 0} = #{x : G | (n.minFac * m) • x = 0} := by rw [← hm]
      _ ≤ #{x : G | n.minFac • x = 0} * #{x : G | m • x = 0} := card_torsion_mul_le _ _
      _ ≤ n.minFac * m := Nat.mul_le_mul (hp _ hpp) (ih m hmn hm0)
      _ = n := hm.symm

/-- A finite noncyclic abelian group has a prime `p` with more than `p` elements killed
by `p` (via Mathlib's cyclicity criterion `isAddCyclic_of_card_nsmul_eq_zero_le`). -/
theorem exists_prime_lt_card_torsion {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : ¬ IsAddCyclic G) : ∃ p : ℕ, p.Prime ∧ p < #{x : G | p • x = 0} := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  exact hG (isAddCyclic_of_card_nsmul_eq_zero_le (card_torsion_le_of_prime hcon))


/-- `|G / pG| = |G[p]|` for a finite abelian group. -/
theorem card_quotient_eq_card_torsion {G : Type*} [AddCommGroup G] [Finite G] (p : ℕ) :
    Nat.card (G ⧸ (nsmulAddMonoidHom (α := G) p).range) =
      Nat.card (nsmulAddMonoidHom (α := G) p).ker := by
  set f := nsmulAddMonoidHom (α := G) p
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.range
  have h2 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv] at h2
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have hmul : Nat.card (G ⧸ f.range) * Nat.card f.range = Nat.card f.ker * Nat.card f.range := by
    rw [← h1, h2, mul_comm]
  exact Nat.eq_of_mul_eq_mul_right hpos hmul

/-- Fiber reduction for an arbitrary finite abelian group: if `|G / pG| > p` (`p` prime) and
`G` has an `s`-spanning pair, then `G / pG ≅ (ℤ/p)²` and `|G| ≤ p² · #(I(s) ∩ r)` for EVERY
residue class `r` modulo `p`. -/
theorem card_le_of_spanning_of_lt_card_quotient {G : Type*} [AddCommGroup G] [Finite G]
    {s p : ℕ} (hp : p.Prime) {a₁ a₂ : G} (h : IsSSpanning s a₁ a₂)
    (hQ : p < Nat.card (G ⧸ (nsmulAddMonoidHom (α := G) p).range)) (r : ZMod p × ZMod p) :
    Nat.card G ≤ p ^ 2 * classCount s p r := by
  haveI : Fact p.Prime := ⟨hp⟩
  set H := (nsmulAddMonoidHom (α := G) p).range with hH
  have hkill : ∀ q : G ⧸ H, p • q = 0 := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
      exact ⟨x, rfl⟩
  letI : Module (ZMod p) (G ⧸ H) := AddCommGroup.zmodModule hkill
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  haveI : Fintype H := Fintype.ofFinite _
  let π : G →+ G ⧸ H := QuotientAddGroup.mk' H
  let ψ : ZMod p × ZMod p → G ⧸ H := fun m => m.1 • π a₁ + m.2 • π a₂
  have hπψ : ∀ l₁ l₂ : ℤ, π (l₁ • a₁ + l₂ • a₂) = ψ ((l₁ : ZMod p), (l₂ : ZMod p)) := by
    intro l₁ l₂
    simp only [ψ, map_add, map_zsmul, Int.cast_smul_eq_zsmul]
  have hπsurj : Function.Surjective π := QuotientAddGroup.mk'_surjective H
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := hπsurj y
    obtain ⟨l₁, l₂, -, hl⟩ := h x
    exact ⟨_, by rw [← hπψ, hl]⟩
  have hcardQ : Fintype.card (G ⧸ H) = p ^ 2 := by
    have hle : Fintype.card (G ⧸ H) ≤ p ^ 2 := by
      have hsurjcard := Fintype.card_le_of_surjective ψ hsurj
      simpa [ZMod.card, sq] using hsurjcard
    have hpow := Module.card_eq_pow_finrank (K := ZMod p) (V := G ⧸ H)
    rw [ZMod.card] at hpow
    have hlt : p ^ 1 < p ^ Module.finrank (ZMod p) (G ⧸ H) := by
      rw [pow_one, ← hpow, ← Nat.card_eq_fintype_card]
      exact hQ
    have hle' : p ^ Module.finrank (ZMod p) (G ⧸ H) ≤ p ^ 2 := hpow ▸ hle
    have h1 := (Nat.pow_lt_pow_iff_right hp.one_lt).1 hlt
    have h2 := (Nat.pow_le_pow_iff_right hp.one_lt).1 hle'
    rw [hpow, show Module.finrank (ZMod p) (G ⧸ H) = 2 by omega]
  have hbij : Function.Bijective ψ :=
    (Fintype.bijective_iff_surjective_and_card ψ).2
      ⟨hsurj, by rw [hcardQ, Fintype.card_prod, ZMod.card, sq]⟩
  obtain ⟨x₀, hx₀⟩ := hπsurj (ψ r)
  have hfib : ∀ y : H, π (x₀ + y) = ψ r := by
    intro y
    rw [map_add, hx₀, show π y = 0 from (QuotientAddGroup.eq_zero_iff (y : G)).2 y.2, add_zero]
  choose l₁ l₂ hb he using fun y : H => h (x₀ + y)
  have hmaps : Set.MapsTo (fun y => (l₁ y, l₂ y)) ((univ : Finset H) : Set H)
      ((diamond s).filter (fun l => ((l.1 : ZMod p), (l.2 : ZMod p)) = r) : Set (ℤ × ℤ)) := by
    intro y _
    have hb1 := neg_abs_le (l₁ y)
    have hb2 := le_abs_self (l₁ y)
    have hb3 := neg_abs_le (l₂ y)
    have hb4 := le_abs_self (l₂ y)
    have hcls : ψ ((l₁ y : ZMod p), (l₂ y : ZMod p)) = ψ r := by
      rw [← hπψ, he, hfib]
    simp only [coe_filter, diamond, mem_filter, mem_product, Finset.mem_Icc, Set.mem_ofPred_eq]
    exact ⟨⟨⟨⟨by linarith [hb y], by linarith [hb y]⟩, ⟨by linarith [hb y], by linarith [hb y]⟩⟩,
      hb y⟩, hbij.1 hcls⟩
  have hinjOn : Set.InjOn (fun y => (l₁ y, l₂ y)) ((univ : Finset H) : Set H) := by
    intro y _ y' _ hyy
    simp only [Prod.mk.injEq] at hyy
    have hxy : x₀ + (y : G) = x₀ + y' := by rw [← he, ← he, hyy.1, hyy.2]
    exact Subtype.ext (add_left_cancel hxy)
  have hcardH : Nat.card H ≤ classCount s p r := by
    have hcard := card_le_card_of_injOn _ hmaps hinjOn
    rwa [card_univ, ← Nat.card_eq_fintype_card] at hcard
  calc Nat.card G = Nat.card (G ⧸ H) * Nat.card H :=
        AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H
    _ = p ^ 2 * Nat.card H := by rw [Nat.card_eq_fintype_card (α := G ⧸ H), hcardQ]
    _ ≤ p ^ 2 * classCount s p r := Nat.mul_le_mul_left _ hcardH


/-- **Conjecture 1.6 upper bound, general form.**  For `s ≥ 3`, every finite NONCYCLIC abelian
group `G` with an `s`-spanning pair `{a₁, a₂}` has `|G| ≤ B(s)`, where `B(s) = 2s²` if
`2s + 1` is prime and `B(s) = 2s² + 2s - (p² - 1)/2` (`p` the least prime factor of `2s + 1`)
otherwise (Bajnok–Beatty, arXiv:2406.04045, Conjecture 1.6).  No structure
theorem is used: a prime `p` with `|G / pG| > p` replaces the invariant factor `c`. -/
theorem card_le_bbBound_of_not_isAddCyclic {G : Type*} [AddCommGroup G] [Finite G]
    (hG : ¬ IsAddCyclic G) {s : ℕ} (hs : 3 ≤ s) {a₁ a₂ : G} (h : IsSSpanning s a₁ a₂) :
    Nat.card G ≤ bbBound s := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  obtain ⟨p, hp, hlt⟩ := exists_prime_lt_card_torsion hG
  have hQ : p < Nat.card (G ⧸ (nsmulAddMonoidHom (α := G) p).range) := by
    rw [card_quotient_eq_card_torsion, Nat.card_eq_fintype_card, Fintype.card_subtype]
    simpa [AddMonoidHom.mem_ker] using hlt
  obtain ⟨r, hr⟩ := exists_classCount_le s p hs hp.two_le
  exact (card_le_of_spanning_of_lt_card_quotient hp h hQ r).trans hr

/-- The "in particular" clause of Conjecture 1.6 for every finite noncyclic abelian group:
`|G| ≤ 2s² + 2s - 4` when `s ≥ 3` (stated additively). -/
theorem card_add_four_le_of_not_isAddCyclic {G : Type*} [AddCommGroup G] [Finite G]
    (hG : ¬ IsAddCyclic G) {s : ℕ} (hs : 3 ≤ s) {a₁ a₂ : G} (h : IsSSpanning s a₁ a₂) :
    Nat.card G + 4 ≤ 2 * s ^ 2 + 2 * s :=
  (Nat.add_le_add_right (card_le_bbBound_of_not_isAddCyclic hG hs h) 4).trans
    (bbBound_add_four_le hs)

/-! ## Non-vacuity and sharpness -/

/-- Non-vacuity and sharpness at `s = 3`: `ℤ_3 × ℤ_6` (order `18 = B(3)`) has the
`3`-spanning pair `{(0, 1), (1, 1)}`, so all hypotheses of `bajnok_beatty_upper` hold
jointly and the bound is attained. -/
example : IsSSpanning 3 ((0, 1) : ZMod 3 × ZMod (3 * 2)) (1, 1) ∧
    3 ^ 2 * 2 = bbBound 3 := by
  refine ⟨?_, by decide⟩
  have hall : ∀ g : ZMod 3 × ZMod (3 * 2), ∃ l ∈ diamond 3,
      l.1 • ((0, 1) : ZMod 3 × ZMod (3 * 2)) + l.2 • (1, 1) = g := by
    decide
  intro g
  obtain ⟨⟨l₁, l₂⟩, hl, hg⟩ := hall g
  simp only [diamond, mem_filter] at hl
  exact ⟨l₁, l₂, hl.2, hg⟩


/-- Non-vacuity of the general form: `ℤ_3 × ℤ_6` is not cyclic (it has `9 > 3` elements
killed by `3`), so with the previous example it satisfies every hypothesis of
`card_le_bbBound_of_not_isAddCyclic` at `s = 3`, with `|G| = 18 = B(3)`. -/
example : ¬ IsAddCyclic (ZMod 3 × ZMod (3 * 2)) := by
  intro hcyc
  have hle := IsAddCyclic.card_nsmul_eq_zero_le (α := ZMod 3 × ZMod (3 * 2)) (n := 3)
    (by norm_num)
  have h9 : #{x : ZMod 3 × ZMod (3 * 2) | 3 • x = 0} = 9 := by decide
  omega

end BajnokBeattySpanningNoncyclic
