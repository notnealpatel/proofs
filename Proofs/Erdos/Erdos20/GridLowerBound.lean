import Erdos.Erdos20.SunflowerConjecture
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false

namespace Erdos20Grid

/-- The graph of a function on an `m` by `k` grid, encoded in `Fin (m * k)`. -/
def graph (m k : ℕ) (f : Fin m → Fin k) : Finset (Fin (m * k)) :=
  Finset.univ.image (fun i => finProdFinEquiv (i, f i))

/-- A grid point belongs to a graph exactly when its value is the function value. -/
@[simp] theorem mem_graph {m k : ℕ} (f : Fin m → Fin k) (i : Fin m) (v : Fin k) :
    finProdFinEquiv (i, v) ∈ graph m k f ↔ v = f i := by
  classical
  simp only [graph, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    have hp := finProdFinEquiv.injective hj
    have hi : j = i := congrArg Prod.fst hp
    subst j
    exact (congrArg Prod.snd hp).symm
  · intro hv
    subst v
    exact ⟨i, rfl⟩

/-- Each graph contains exactly one point at each coordinate. -/
@[simp] theorem graph_card {m k : ℕ} (f : Fin m → Fin k) :
    (graph m k f).card = m := by
  classical
  rw [graph, Finset.card_image_of_injective]
  · simp
  · intro i j hij
    exact congrArg Prod.fst (finProdFinEquiv.injective hij)

/-- Distinct functions have distinct encoded graphs. -/
theorem graph_injective (m k : ℕ) : Function.Injective (graph m k) := by
  intro f g hfg
  funext i
  have hi : finProdFinEquiv (i, f i) ∈ graph m k g := by
    rw [← hfg]
    exact (mem_graph f i (f i)).2 rfl
  exact (mem_graph g i (f i)).1 hi

/-- The complete family of graphs on the `m` by `k` grid. -/
def family (m k : ℕ) : Finset (Finset (Fin (m * k))) :=
  Finset.univ.image (graph m k)

/-- Membership in the grid family means being the graph of a function. -/
@[simp] theorem mem_family {m k : ℕ} (S : Finset (Fin (m * k))) :
    S ∈ family m k ↔ ∃ f : Fin m → Fin k, graph m k f = S := by
  classical
  simp [family]

/-- There are `k^m` distinct graphs in the grid family. -/
@[simp] theorem family_card (m k : ℕ) : (family m k).card = k ^ m := by
  classical
  rw [family, Finset.card_image_of_injective _ (graph_injective m k)]
  simp

/-- Every member of the grid family is an `m`-element set. -/
theorem family_uniform {m k : ℕ} {S : Finset (Fin (m * k))}
    (hS : S ∈ family m k) : S.card = m := by
  obtain ⟨f, rfl⟩ := (mem_family S).1 hS
  exact graph_card f

/-- A collision at one coordinate in an OEIS sunflower forces every graph
in that sunflower to have the same value at that coordinate. -/
private theorem collision_forces_value {m k : ℕ}
    {sub : Finset (Finset (Fin (m * k)))} (hsun : IsOeisSunflower sub)
    {f g u : Fin m → Fin k} (hf : graph m k f ∈ sub)
    (hg : graph m k g ∈ sub) (hu : graph m k u ∈ sub)
    (hfg : f ≠ g) (i : Fin m) (heq : f i = g i) : u i = f i := by
  classical
  obtain ⟨K, hK⟩ := hsun
  have hgraphs : graph m k f ≠ graph m k g := fun h => hfg (graph_injective m k h)
  have hpoint : finProdFinEquiv (i, f i) ∈ K := by
    rw [← hK _ hf _ hg hgraphs]
    exact Finset.mem_inter.mpr ⟨(mem_graph f i (f i)).2 rfl,
      (mem_graph g i (f i)).2 heq⟩
  by_cases hfu : f = u
  · subst u
    rfl
  · have hgraphs' : graph m k f ≠ graph m k u :=
      fun h => hfu (graph_injective m k h)
    have hmem : finProdFinEquiv (i, f i) ∈ graph m k u := by
      have hinter : finProdFinEquiv (i, f i) ∈ graph m k f ∩ graph m k u := by
        rw [hK _ hf _ hu hgraphs']
        exact hpoint
      exact (Finset.mem_inter.mp hinter).2
    exact ((mem_graph u i (f i)).1 hmem).symm

/-- The complete grid family has no OEIS sunflower with more members than
there are values, provided there are at least two selected members. -/
theorem no_sunflower {m k r : ℕ} (hkr : k < r) (hr : 2 ≤ r)
    {sub : Finset (Finset (Fin (m * k)))} (hsub : sub ⊆ family m k)
    (hcard : sub.card = r) : ¬ IsOeisSunflower sub := by
  classical
  intro hsun
  let t : Finset (Fin m → Fin k) := Finset.univ.filter (fun f => graph m k f ∈ sub)
  have ht (f : Fin m → Fin k) : f ∈ t ↔ graph m k f ∈ sub := by
    simp [t]
  have himage : t.image (graph m k) = sub := by
    ext S
    constructor
    · intro hS
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hS
      exact (ht f).1 hf
    · intro hS
      obtain ⟨f, rfl⟩ := (mem_family S).1 (hsub hS)
      exact Finset.mem_image.mpr ⟨f, (ht f).2 hS, rfl⟩
  have htcard : t.card = r := by
    rw [← hcard, ← himage, Finset.card_image_of_injective _ (graph_injective m k)]
  have hall : ∀ u ∈ t, ∀ v ∈ t, u = v := by
    intro u hu v hv
    funext i
    have hpigeon : (Finset.univ : Finset (Fin k)).card < t.card := by
      simpa only [Finset.card_univ, Fintype.card_fin, htcard] using hkr
    obtain ⟨f, hf, g, hg, hfg, heq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hpigeon
        (f := fun f : Fin m → Fin k => f i) (by intro f _; exact Finset.mem_univ _)
    have huval := collision_forces_value hsun ((ht f).1 hf) ((ht g).1 hg)
      ((ht u).1 hu) hfg i heq
    have hvval := collision_forces_value hsun ((ht f).1 hf) ((ht g).1 hg)
      ((ht v).1 hv) hfg i heq
    exact huval.trans hvval.symm
  have hsmall : t.card ≤ 1 := Finset.card_le_one.mpr hall
  omega

/-- The `(n-1)^m` graph construction excludes an `n`-member OEIS sunflower. -/
theorem family_no_oeis_sunflower {m n : ℕ} (hn : 2 ≤ n)
    {sub : Finset (Finset (Fin (m * (n - 1))))}
    (hsub : sub ⊆ family m (n - 1)) (hcard : sub.card = n) :
    ¬ IsOeisSunflower sub :=
  no_sunflower (by omega) hn hsub hcard

/-- The Erdős–Rado graph construction gives a strict lower bound on the
OEIS sunflower threshold for positive set size and at least two members. -/
theorem pow_lt_sunOeis {m n : ℕ} (_hm : 1 ≤ m) (hn : 2 ≤ n) :
    (n - 1) ^ m < SunOeis m n := by
  by_contra hnot
  have hle : SunOeis m n ≤ (family m (n - 1)).card := by
    rw [family_card]
    omega
  obtain ⟨sub, hsub, hcard, hsun⟩ :=
    oeisSunflowerProperty_sunOeis (m := m) (n := n) (by omega)
      (m * (n - 1)) (family m (n - 1))
      (fun S hS => (family_uniform hS).le) hle
  exact family_no_oeis_sunflower hn hsub hcard hsun

/-- The weak Erdős–Rado lower bound includes the one-member case. -/
theorem pow_le_sunOeis {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (n - 1) ^ m ≤ SunOeis m n := by
  by_cases hn1 : n = 1
  · subst n
    rw [sunOeis_one_petal hm]
    simp [Nat.ne_of_gt (by omega : 0 < m)]
  · exact (pow_lt_sunOeis hm (by omega)).le

/-- The strict grid lower bound transfers to the nonempty-petal threshold. -/
theorem pow_lt_sun {m n : ℕ} (hm : 1 ≤ m) (hn : 2 ≤ n) :
    (n - 1) ^ m < Sun m n :=
  lt_of_lt_of_le (pow_lt_sunOeis hm hn) (sunOeis_le_sun (by omega))

/-- The weak grid lower bound transfers to the nonempty-petal threshold. -/
theorem pow_le_sun {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (n - 1) ^ m ≤ Sun m n :=
  (pow_le_sunOeis hm hn).trans (sunOeis_le_sun hn)

/-- At `m = 2`, `n = 3`, the encoded grid is exactly the four advertised
actual two-element subsets of `Fin 4`. -/
theorem fixture_family :
    family 2 2 =
      ({({0, 2} : Finset (Fin 4)), {0, 3}, {1, 2}, {1, 3}} :
        Finset (Finset (Fin 4))) := by
  decide

/-- Joint nonvacuity fixture: the same four-graph family has four members,
all are two-element sets, it has a three-member subfamily but no such
subfamily is an OEIS sunflower, and it gives the strict threshold bound. -/
theorem fixture_joint :
    (family 2 2).card = 4 ∧
    (∀ S ∈ family 2 2, S.card = 2) ∧
    (∃ sub ⊆ family 2 2, sub.card = 3) ∧
    (∀ sub ⊆ family 2 2, sub.card = 3 → ¬ IsOeisSunflower sub) ∧
    4 < SunOeis 2 3 := by
  refine ⟨family_card 2 2, fun _ hS => family_uniform hS, ?_, ?_, ?_⟩
  · refine ⟨{({0, 2} : Finset (Fin 4)), {0, 3}, {1, 2}}, ?_, ?_⟩
    · decide
    · decide
  · intro sub hsub hcard
    exact no_sunflower (by decide : 2 < 3) (by decide : 2 ≤ 3) hsub hcard
  · exact pow_lt_sunOeis (by decide : 1 ≤ 2) (by decide : 2 ≤ 3)

end Erdos20Grid
