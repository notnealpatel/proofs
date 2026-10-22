/-
Order-3 perimeter-magic squares (OEIS A084569; R. J. Mathar, Mar 08 2025).

A084569(n) counts rotation classes of squares with eight positive entries,
three on each edge, and common side sum n+3. Entries need not be distinct;
reflections are not identified. Corners c(i) and edge middles e(i) use Fin 4,
with side i given by c(i), e(i), c(i+1).
Burnside counting gives the parity-dependent quartic formula. Two partial
sums identify it with A084569, via A084570 and A084263.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A084569MatharOrderPerimeter

/-! ## Definition layer -/

/-- A hollow square of order 3: corners `c` and edge middles `e`, each indexed by
`Fin 4` in counterclockwise order; side `i` is `c i, e i, c (i + 1)`. -/
abbrev Square := (Fin 4 → ℕ) × (Fin 4 → ℕ)

/-- `IsPerimeterMagic S c e`: every entry is at least `1` and each of the four
sides `c i, e i, c (i + 1)` (cyclically) sums to the magic sum `S`. -/
def IsPerimeterMagic (S : ℕ) (c e : Fin 4 → ℕ) : Prop :=
  (∀ i, 1 ≤ c i) ∧ (∀ i, 1 ≤ e i) ∧ ∀ i, c i + e i + c (i + 1) = S

instance (S : ℕ) (c e : Fin 4 → ℕ) : Decidable (IsPerimeterMagic S c e) := by
  unfold IsPerimeterMagic; infer_instance

/-- The finite set of order-3 perimeter-magic squares with magic sum `S`.  The
enumeration box (corners in `[1, S]`, edges computed from the corners) is only an
implementation device; `mem_squares` shows that membership is exactly
`IsPerimeterMagic S`. -/
def squares (S : ℕ) : Finset Square :=
  ((Fintype.piFinset fun _ => Finset.Icc 1 S).image
    fun c => (c, fun i => S - (c i + c (i + 1)))).filter fun p => IsPerimeterMagic S p.1 p.2

/-- The quarter turn of a square: corner `i + 1` moves to position `i`, and so
does edge `i + 1`. -/
def rotate (p : Square) : Square :=
  (fun i => p.1 (i + 1), fun i => p.2 (i + 1))

/-- The rotation class of a square: the set of its four rotations. -/
def rotationClass (p : Square) : Finset Square :=
  {p, rotate p, rotate (rotate p), rotate (rotate (rotate p))}

/-- The number of order-3 perimeter-magic squares with magic sum `S`, counted up
to rotation: the number of distinct rotation classes of such squares. -/
def numUpToRotation (S : ℕ) : ℕ :=
  ((squares S).image rotationClass).card

/-- OEIS A084263: `a(n) = (-1)^n/2 + (n^2 + n + 1)/2` (rational-valued
definition; the values are integers). -/
def a084263 (n : ℕ) : ℚ := (-1) ^ n / 2 + ((n : ℚ) ^ 2 + n + 1) / 2

/-- OEIS A084570: partial sums of A084263. -/
def a084570 (n : ℕ) : ℚ := ∑ j ∈ Finset.range (n + 1), a084263 j

/-- OEIS A084569: partial sums of A084570. -/
def a084569 (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), a084570 k

/-! ## Examples -/

/-- Membership in `squares S` is exactly the perimeter-magic condition. -/
theorem mem_squares {S : ℕ} {p : Square} : p ∈ squares S ↔ IsPerimeterMagic S p.1 p.2 := by
  constructor
  · intro hp
    exact (Finset.mem_filter.mp hp).2
  · intro hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨p.1, ?_, ?_⟩, hp⟩
    · refine Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr ⟨hp.1 i, ?_⟩
      have hside := hp.2.2 i
      omega
    · refine Prod.ext rfl (funext fun i => ?_)
      have hside := hp.2.2 i
      simp only
      omega

-- The first terms of A084569 from the DATA line: 1, 3, 9, 21, 44, 82.
example : a084569 0 = 1 ∧ a084569 1 = 3 ∧ a084569 2 = 9 ∧ a084569 3 = 21 ∧
    a084569 4 = 44 ∧ a084569 5 = 82 := by
  norm_num [a084569, a084570, a084263, Finset.sum_range_succ]

-- Magic sum 3: only the all-ones square (Mathar: "1 1 1 1 1 1 1 1").
example : numUpToRotation 3 = 1 := by decide

-- Mathar's three squares with magic sum 4, read ccw as `c0 e0 c1 e1 c2 e2 c3 e3`:
-- `1 1 2 1 1 1 2 1`, `1 1 2 1 1 2 1 2`, `1 2 1 2 1 2 1 2`; all are perimeter-magic.
example : IsPerimeterMagic 4 ![1, 2, 1, 2] ![1, 1, 1, 1] ∧
    IsPerimeterMagic 4 ![1, 2, 1, 1] ![1, 1, 2, 2] ∧
    IsPerimeterMagic 4 ![1, 1, 1, 1] ![2, 2, 2, 2] := by
  decide

-- Two of them lie in different rotation classes (a 4-cycle of corners
-- `1 2 1 2` is not a rotation of `1 2 1 1`).
example : rotationClass (![1, 2, 1, 2], ![1, 1, 1, 1]) ≠
    rotationClass (![1, 2, 1, 1], ![1, 1, 2, 2]) := by
  decide

/-! ## Burnside's lemma for an operator of order dividing 4 -/

/-- The orbit `{x, r x, r² x, r³ x}` of `x` under an operator `r`. -/
def orb {α : Type*} [DecidableEq α] (r : α → α) (x : α) : Finset α :=
  {x, r x, r (r x), r (r (r x))}

/-- Per-orbit Burnside identity: if `r⁴ = id`, then for every orbit `O`,
`|O| + |O ∩ Fix r²| + 2 |O ∩ Fix r| = 4`. -/
theorem orb_card_add {α : Type*} [DecidableEq α] (r : α → α) (hr4 : ∀ x, r (r (r (r x))) = x)
    (x : α) :
    (orb r x).card + ((orb r x).filter fun y => r (r y) = y).card
      + 2 * ((orb r x).filter fun y => r y = y).card = 4 := by
  have hinj : Function.Injective r := fun a b hab => by
    have h3 := congrArg (fun z => r (r (r z))) hab
    simpa only [hr4] using h3
  by_cases h1 : r x = x
  · simp [orb, h1, Finset.filter_singleton]
  by_cases h2 : r (r x) = x
  · have hne : x ≠ r x := fun h => h1 h.symm
    simp [orb, h2, Finset.filter_insert, h1, hne, Finset.filter_singleton]
  · have hc : r (r (r x)) ≠ x := fun h => h1 (by
      have h4 := congrArg r h
      rw [hr4] at h4
      exact h4.symm)
    have hd : r (r x) ≠ r x := fun h => h1 (hinj h)
    have he : r (r (r x)) ≠ r x := fun h => h2 (hinj h)
    have hf : r (r (r x)) ≠ r (r x) := fun h => h1 (hinj (hinj h))
    simp [orb, Finset.filter_insert, Finset.filter_singleton, hr4, h1, h2, hd, he, hf,
      Ne.symm h1, Ne.symm h2, Ne.symm hc, Ne.symm hd, Ne.symm he, Ne.symm hf]

/-- Rotating the base point does not change the orbit. -/
theorem orb_rot {α : Type*} [DecidableEq α] (r : α → α) (hr4 : ∀ x, r (r (r (r x))) = x)
    (x : α) : orb r (r x) = orb r x := by
  ext y
  simp only [orb, Finset.mem_insert, Finset.mem_singleton, hr4]
  tauto

/-- Every point of an orbit generates the same orbit. -/
theorem orb_eq_of_mem {α : Type*} [DecidableEq α] (r : α → α) (hr4 : ∀ x, r (r (r (r x))) = x)
    {x y : α} (hy : y ∈ orb r x) : orb r y = orb r x := by
  simp only [orb, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · rfl
  · exact orb_rot r hr4 x
  · rw [orb_rot r hr4, orb_rot r hr4]
  · rw [orb_rot r hr4, orb_rot r hr4, orb_rot r hr4]

/-- The fibre of `orb r` over the orbit of `x ∈ X`, restricted to `P`, is the
orbit restricted to `P` (for `X` closed under `r`). -/
theorem filter_orb_fiber {α : Type*} [DecidableEq α] (r : α → α)
    (hr4 : ∀ x, r (r (r (r x))) = x) (X : Finset α) (hX : ∀ x ∈ X, r x ∈ X)
    (P : α → Prop) [DecidablePred P] {x : α} (hx : x ∈ X) :
    ((X.filter P).filter fun y => orb r y = orb r x) = (orb r x).filter P := by
  have hsub : orb r x ⊆ X := by
    intro y hy
    simp only [orb, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact hx
    · exact hX _ hx
    · exact hX _ (hX _ hx)
    · exact hX _ (hX _ (hX _ hx))
  ext y
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨-, hPy⟩, hyo⟩
    refine ⟨?_, hPy⟩
    rw [← hyo]
    simp [orb]
  · rintro ⟨hyo, hPy⟩
    exact ⟨⟨hsub hyo, hPy⟩, orb_eq_of_mem r hr4 hyo⟩

/-- Counting `X ∩ P` orbit by orbit. -/
theorem card_filter_eq_sum_orb {α : Type*} [DecidableEq α] (r : α → α)
    (hr4 : ∀ x, r (r (r (r x))) = x) (X : Finset α) (hX : ∀ x ∈ X, r x ∈ X)
    (P : α → Prop) [DecidablePred P] :
    (X.filter P).card = ∑ O ∈ X.image (orb r), (O.filter P).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := orb r) (t := X.image (orb r))]
  · refine Finset.sum_congr rfl fun O hO => ?_
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hO
    rw [filter_orb_fiber r hr4 X hX P hx]
  · intro y hy
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mp hy).1

/-- Burnside's lemma for an operator `r` with `r⁴ = id` on a finite set `X`
closed under `r`: `4 · #orbits = |X| + |Fix r²| + 2 |Fix r|`. -/
theorem four_mul_card_image_orb {α : Type*} [DecidableEq α] (r : α → α)
    (hr4 : ∀ x, r (r (r (r x))) = x) (X : Finset α) (hX : ∀ x ∈ X, r x ∈ X) :
    4 * (X.image (orb r)).card
      = X.card + (X.filter fun y => r (r y) = y).card + 2 * (X.filter fun y => r y = y).card := by
  have hall : X.card = (X.filter fun _ => True).card := by simp
  rw [hall, card_filter_eq_sum_orb r hr4 X hX, card_filter_eq_sum_orb r hr4 X hX,
    card_filter_eq_sum_orb r hr4 X hX, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, Finset.card_eq_sum_ones, Finset.mul_sum]
  refine Finset.sum_congr rfl fun O hO => ?_
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hO
  rw [mul_one, Finset.filter_true_of_mem (fun _ _ => trivial), orb_card_add r hr4 x]

/-! ## The rotation on squares -/

/-- Four quarter turns are the identity. -/
theorem rotate_four (p : Square) : rotate (rotate (rotate (rotate p))) = p := by
  have h : ∀ i : Fin 4, i + 1 + 1 + 1 + 1 = i := by decide
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp only [rotate, h]

/-- A rotated perimeter-magic square is perimeter-magic with the same sum. -/
theorem rotate_mem {S : ℕ} {p : Square} (hp : p ∈ squares S) : rotate p ∈ squares S := by
  rw [mem_squares] at hp ⊢
  exact ⟨fun i => hp.1 (i + 1), fun i => hp.2.1 (i + 1), fun i => hp.2.2 (i + 1)⟩

/-- The defining constraints of a square in `squares S`, written out. -/
theorem squares_constraints {S : ℕ} {p : Square} (hp : p ∈ squares S) :
    1 ≤ p.1 0 ∧ 1 ≤ p.1 1 ∧ 1 ≤ p.1 2 ∧ 1 ≤ p.1 3 ∧
    1 ≤ p.2 0 ∧ 1 ≤ p.2 1 ∧ 1 ≤ p.2 2 ∧ 1 ≤ p.2 3 ∧
    p.1 0 + p.2 0 + p.1 1 = S ∧ p.1 1 + p.2 1 + p.1 2 = S ∧
    p.1 2 + p.2 2 + p.1 3 = S ∧ p.1 3 + p.2 3 + p.1 0 = S := by
  rw [mem_squares] at hp
  exact ⟨hp.1 0, hp.1 1, hp.1 2, hp.1 3, hp.2.1 0, hp.2.1 1, hp.2.1 2, hp.2.1 3,
    hp.2.2 0, hp.2.2 1, hp.2.2 2, hp.2.2 3⟩

/-! ## Fixed-point counts -/

/-- Squares fixed by the quarter turn (all corners equal, all edges equal) with
magic sum `n + 3`: there are `⌊n / 2⌋ + 1` of them. -/
theorem card_fix_rotate (n : ℕ) :
    ((squares (n + 3)).filter fun p => rotate p = p).card = n / 2 + 1 := by
  rw [← Finset.card_range (n / 2 + 1)]
  refine Finset.card_nbij' (fun p => p.1 0 - 1) (fun a => (fun _ => a + 1, fun _ => n + 1 - 2 * a))
    ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp
    obtain ⟨hp, hrot⟩ := hp
    have hc : p.1 1 = p.1 0 := congrFun (congrArg Prod.fst hrot) 0
    have hcon := squares_constraints hp
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  · intro a ha
    simp only [Finset.coe_range, Set.mem_Iio] at ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq]
    refine ⟨mem_squares.mpr ⟨fun _ => by dsimp only; omega, fun _ => by dsimp only; omega,
      fun _ => by dsimp only; omega⟩, rfl⟩
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp
    obtain ⟨hp, hrot⟩ := hp
    have hc : ∀ i, p.1 (i + 1) = p.1 i := fun i => congrFun (congrArg Prod.fst hrot) i
    have he : ∀ i, p.2 (i + 1) = p.2 i := fun i => congrFun (congrArg Prod.snd hrot) i
    have h1 := hc 0
    have h2 := hc 1
    have h3 := hc 2
    have h1' := he 0
    have h2' := he 1
    have h3' := he 2
    simp only [Fin.reduceAdd, zero_add] at h1 h2 h3 h1' h2' h3'
    have hcon := squares_constraints hp
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> fin_cases i <;>
      simp only [Fin.isValue, Fin.mk_one, Fin.zero_eta, Fin.reduceFinMk] <;> omega
  · intro a _
    simp

/-- Squares fixed by the half turn (`c 0 = c 2`, `c 1 = c 3`, all edges equal)
with magic sum `n + 3` correspond to pairs `(a, b)` with `a ≤ n`, `b < n + 1 - a`. -/
theorem card_fix_rotate_rotate (n : ℕ) :
    ((squares (n + 3)).filter fun p => rotate (rotate p) = p).card
      = ((Finset.range (n + 1)).sigma fun a => Finset.range (n + 1 - a)).card := by
  refine Finset.card_nbij' (fun p => ⟨p.1 0 - 1, p.1 1 - 1⟩)
    (fun x => (![x.1 + 1, x.2 + 1, x.1 + 1, x.2 + 1], fun _ => n + 1 - (x.1 + x.2)))
    ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp
    obtain ⟨hp, hrot⟩ := hp
    have hcon := squares_constraints hp
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_range, Set.mem_Iio]
    omega
  · rintro ⟨a, b⟩ hab
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_range, Set.mem_Iio] at hab
    simp only [Finset.coe_filter, Set.mem_ofPred_eq]
    refine ⟨mem_squares.mpr ⟨fun i => ?_, fun _ => by dsimp only; omega, fun i => ?_⟩, ?_⟩
    · fin_cases i <;> simp
    · fin_cases i <;>
      simp only [Fin.isValue, Fin.mk_one, Fin.zero_eta, Fin.reduceFinMk, Fin.reduceAdd, Matrix.cons_val,
        Matrix.cons_val_zero, Matrix.cons_val_one, zero_add] <;> omega
    · refine Prod.ext (funext fun i => ?_) rfl
      fin_cases i <;> rfl
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp
    obtain ⟨hp, hrot⟩ := hp
    have hc : ∀ i, p.1 (i + 1 + 1) = p.1 i := fun i => congrFun (congrArg Prod.fst hrot) i
    have he : ∀ i, p.2 (i + 1 + 1) = p.2 i := fun i => congrFun (congrArg Prod.snd hrot) i
    have h1 := hc 0
    have h2 := hc 1
    have h1' := he 0
    have h2' := he 1
    simp only [Fin.reduceAdd, zero_add] at h1 h2 h1' h2'
    have hcon := squares_constraints hp
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> fin_cases i <;>
      simp only [Fin.isValue, Fin.mk_one, Fin.zero_eta, Fin.reduceFinMk, Matrix.cons_val,
        Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega
  · rintro ⟨a, b⟩ _
    simp

/-- The box of shifted corners `(a, c), (b, d)` (corners `a+1, b+1, c+1, d+1`):
`a, c ≤ n` and `b, d < n + 1 - max a c`. -/
def cornerBox (n : ℕ) : Finset (Σ _ : ℕ × ℕ, ℕ × ℕ) :=
  (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).sigma
    fun ac => Finset.range (n + 1 - max ac.1 ac.2) ×ˢ Finset.range (n + 1 - max ac.1 ac.2)

/-- All squares with magic sum `n + 3` are in bijection with `cornerBox n`
(the edges are determined by the corners). -/
theorem card_squares_eq_cornerBox (n : ℕ) : (squares (n + 3)).card = (cornerBox n).card := by
  refine Finset.card_nbij' (fun p => ⟨(p.1 0 - 1, p.1 2 - 1), (p.1 1 - 1, p.1 3 - 1)⟩)
    (fun x => (![x.1.1 + 1, x.2.1 + 1, x.1.2 + 1, x.2.2 + 1],
      ![n + 1 - (x.1.1 + x.2.1), n + 1 - (x.2.1 + x.1.2), n + 1 - (x.1.2 + x.2.2),
        n + 1 - (x.2.2 + x.1.1)])) ?_ ?_ ?_ ?_
  · intro p hp
    have hcon := squares_constraints hp
    simp only [cornerBox, Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_product,
      Finset.coe_range, Set.mem_prod, Set.mem_Iio]
    omega
  · rintro ⟨⟨a, c⟩, ⟨b, d⟩⟩ hx
    simp only [cornerBox, Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_product,
      Finset.coe_range, Set.mem_prod, Set.mem_Iio] at hx
    refine Finset.mem_coe.mpr (mem_squares.mpr ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩) <;>
      fin_cases i <;>
      simp only [Fin.isValue, Fin.mk_one, Fin.zero_eta, Fin.reduceFinMk, Fin.reduceAdd, Matrix.cons_val,
        Matrix.cons_val_zero, Matrix.cons_val_one, zero_add] <;> omega
  · intro p hp
    have hcon := squares_constraints (Finset.mem_coe.mp hp)
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> fin_cases i <;>
      simp only [Fin.isValue, Fin.mk_one, Fin.zero_eta, Fin.reduceFinMk, Matrix.cons_val,
        Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega
  · rintro ⟨⟨a, c⟩, ⟨b, d⟩⟩ _
    simp

/-- `|cornerBox n| = Σ_{a, c ≤ n} (n + 1 - max a c)²`. -/
theorem card_cornerBox (n : ℕ) :
    (cornerBox n).card = ∑ a ∈ Finset.range (n + 1), ∑ c ∈ Finset.range (n + 1),
      (n + 1 - max a c) ^ 2 := by
  rw [cornerBox, Finset.card_sigma, Finset.sum_product]
  simp [Finset.card_product, sq]

/-- Summing a function of `max a c` over a square grid:
`Σ_{a, c < N} f (max a c) = Σ_{m < N} (2m + 1) f m`. -/
theorem sum_sum_max (f : ℕ → ℕ) (N : ℕ) :
    ∑ a ∈ Finset.range N, ∑ c ∈ Finset.range N, f (max a c)
      = ∑ m ∈ Finset.range N, (2 * m + 1) * f m := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h1 : ∑ a ∈ Finset.range N, f (max a N) = N * f N := by
      rw [Finset.sum_congr rfl fun a ha => by
        rw [max_eq_right (Finset.mem_range.mp ha).le], Finset.sum_const, Finset.card_range,
        smul_eq_mul]
    have h2 : ∑ c ∈ Finset.range N, f (max N c) = N * f N := by
      rw [Finset.sum_congr rfl fun c hc => by
        rw [max_eq_left (Finset.mem_range.mp hc).le], Finset.sum_const, Finset.card_range,
        smul_eq_mul]
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib, ih, h1, h2, max_self]
    ring

/-! ## Closed forms of the sums -/

/-- `6 Σ_{m ≤ n} (n + 1 - m)² = (n + 1)(n + 2)(2n + 3)`. -/
theorem six_mul_sum_sq (n : ℕ) :
    6 * ∑ m ∈ Finset.range (n + 1), (n + 1 - m) ^ 2 = (n + 1) * (n + 2) * (2 * n + 3) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_add_right, mul_add, ih, Nat.sub_zero]
    ring

/-- `2 Σ_{m ≤ n} (n + 1 - m) = (n + 1)(n + 2)`. -/
theorem two_mul_sum_lin (n : ℕ) :
    2 * ∑ m ∈ Finset.range (n + 1), (n + 1 - m) = (n + 1) * (n + 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_add_right, mul_add, ih, Nat.sub_zero]
    ring

/-- `6 Σ_{m ≤ n} (2m + 1)(n + 1 - m)² = (n + 1)(n + 2)(n² + 3n + 3)`. -/
theorem six_mul_sum_odd_mul_sq (n : ℕ) :
    6 * ∑ m ∈ Finset.range (n + 1), (2 * m + 1) * (n + 1 - m) ^ 2
      = (n + 1) * (n + 2) * (n ^ 2 + 3 * n + 3) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : ∀ m ∈ Finset.range (n + 1),
        (2 * (m + 1) + 1) * (n + 1 + 1 - (m + 1)) ^ 2
          = (2 * m + 1) * (n + 1 - m) ^ 2 + 2 * (n + 1 - m) ^ 2 := by
      intro m _
      rw [Nat.add_sub_add_right]
      ring
    rw [Finset.sum_range_succ', Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
      ← Finset.mul_sum, mul_add, mul_add, ih, mul_left_comm, six_mul_sum_sq]
    simp only [Nat.sub_zero]
    ring

/-! ## Assembly -/

/-- Burnside for the squares with magic sum `n + 3`:
`4 · #classes = Σ_{m ≤ n} (2m+1)(n+1-m)² + Σ_{m ≤ n} (n+1-m) + 2 (⌊n/2⌋ + 1)`. -/
theorem four_mul_numUpToRotation (n : ℕ) :
    4 * numUpToRotation (n + 3)
      = ∑ m ∈ Finset.range (n + 1), (2 * m + 1) * (n + 1 - m) ^ 2
        + ∑ m ∈ Finset.range (n + 1), (n + 1 - m) + 2 * (n / 2 + 1) := by
  have hb := four_mul_card_image_orb rotate rotate_four (squares (n + 3))
    (fun p hp => rotate_mem hp)
  have hmax := sum_sum_max (fun m => (n + 1 - m) ^ 2) (n + 1)
  have hclass : rotationClass = orb rotate := rfl
  rw [numUpToRotation, hclass, hb, card_fix_rotate, card_fix_rotate_rotate, Finset.card_sigma,
    card_squares_eq_cornerBox, card_cornerBox, hmax]
  simp

/-! ## The conjecture -/

/-- **Mathar's conjecture (A084569, R. J. Mathar, Mar 08 2025), closed form.**

For every `n ≥ 0`, the number of order-3 perimeter-magic hollow squares (eight
entries `≥ 1`, each side of three entries summing to `S`) with magic sum
`S = n + 3`, counted up to rotation, equals
`(3(-1)^n + n^4 + 6n^3 + 17n^2 + 30n + 21) / 24`.  Stated in `ℚ`, so the
division is exact. -/
theorem numUpToRotation_eq (n : ℕ) :
    (numUpToRotation (n + 3) : ℚ)
      = (3 * (-1) ^ n + (n : ℚ) ^ 4 + 6 * (n : ℚ) ^ 3 + 17 * (n : ℚ) ^ 2 + 30 * n + 21) / 24 := by
  have h4 := four_mul_numUpToRotation n
  have hT := six_mul_sum_odd_mul_sq n
  have hW := two_mul_sum_lin n
  generalize ∑ m ∈ Finset.range (n + 1), (2 * m + 1) * (n + 1 - m) ^ 2 = T at h4 hT
  generalize ∑ m ∈ Finset.range (n + 1), (n + 1 - m) = W at h4 hW
  generalize numUpToRotation (n + 3) = C at h4 ⊢
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hk : 2 * k / 2 = k := by omega
    rw [hk] at h4
    have e1 : (4 * C : ℚ) = T + W + 2 * (k + 1) := by exact_mod_cast h4
    have e2 : (6 * T : ℚ) = (2 * k + 1) * (2 * k + 2) * ((2 * k) ^ 2 + 3 * (2 * k) + 3) := by
      exact_mod_cast hT
    have e3 : (2 * W : ℚ) = (2 * k + 1) * (2 * k + 2) := by exact_mod_cast hW
    push_cast
    rw [pow_mul]
    norm_num
    linear_combination (1 / 4 : ℚ) * e1 + (1 / 24 : ℚ) * e2 + (1 / 8 : ℚ) * e3
  · have hk : (2 * k + 1) / 2 = k := by omega
    rw [hk] at h4
    have e1 : (4 * C : ℚ) = T + W + 2 * (k + 1) := by exact_mod_cast h4
    have e2 : (6 * T : ℚ) = (2 * k + 1 + 1) * (2 * k + 1 + 2)
        * ((2 * k + 1) ^ 2 + 3 * (2 * k + 1) + 3) := by
      exact_mod_cast hT
    have e3 : (2 * W : ℚ) = (2 * k + 1 + 1) * (2 * k + 1 + 2) := by exact_mod_cast hW
    push_cast
    rw [pow_succ, pow_mul]
    norm_num
    linear_combination (1 / 4 : ℚ) * e1 + (1 / 24 : ℚ) * e2 + (1 / 8 : ℚ) * e3

-- Consequence: magic sums 4 and 5 give 3 and 9 classes (Mathar lists the 3 for
-- sum 4), matching the DATA line `1, 3, 9, …`.
example : numUpToRotation 4 = 3 ∧ numUpToRotation 5 = 9 := by
  have h1 : (numUpToRotation (1 + 3) : ℚ) = 3 := by rw [numUpToRotation_eq]; norm_num
  have h2 : (numUpToRotation (2 + 3) : ℚ) = 9 := by rw [numUpToRotation_eq]; norm_num
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- Closed form of A084263 partial sums (A084570):
`a084570 n = (-1)^n / 4 + (2n³ + 6n² + 10n + 9) / 12`. -/
theorem a084570_eq (n : ℕ) :
    a084570 n = (-1) ^ n / 4 + (2 * (n : ℚ) ^ 3 + 6 * (n : ℚ) ^ 2 + 10 * n + 9) / 12 := by
  induction n with
  | zero => norm_num [a084570, a084263]
  | succ n ih =>
    rw [a084570, Finset.sum_range_succ, ← a084570, ih, a084263]
    push_cast
    ring

/-- The entry's closed form of A084569:
`a084569 n = (-1)^n / 8 + (n⁴ + 6n³ + 17n² + 30n + 21) / 24`. -/
theorem a084569_eq (n : ℕ) :
    a084569 n
      = (3 * (-1) ^ n + (n : ℚ) ^ 4 + 6 * (n : ℚ) ^ 3 + 17 * (n : ℚ) ^ 2 + 30 * n + 21) / 24 := by
  induction n with
  | zero => norm_num [a084569, a084570, a084263]
  | succ n ih =>
    rw [a084569, Finset.sum_range_succ, ← a084569, ih, a084570_eq]
    push_cast
    ring

/-- **Mathar's conjecture (A084569, R. J. Mathar, Mar 08 2025), as stated in the
entry.**  "a(n) is the number of perimeter-magic (hollow) squares of order 3 with
magic sum n+3 … squares obtained by rotations are counted only once", where
`a = A084569` (partial sums of A084570, which are partial sums of A084263). -/
theorem numUpToRotation_eq_a084569 (n : ℕ) :
    (numUpToRotation (n + 3) : ℚ) = a084569 n := by
  rw [numUpToRotation_eq, a084569_eq]

end Candidates.A084569MatharOrderPerimeter
