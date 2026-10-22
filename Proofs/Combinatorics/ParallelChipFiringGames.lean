/-
# Parallel chip-firing games in the band 2|E|-|V| < |σ| < 2|E| have activity 1/2

## Source

arXiv:2608.04153, "All parallel chip-firing games with 2|E|-|V| < |sigma| < 2|E|
have period 2" (proof of Ji–Li–Wang, arXiv:2408.10508, Conjecture 2; the paper
presents a proof found by GPT-5.6-Sol).  Statement: Theorem 1.2 (`thm:main`);
the part formalized here is the first paragraph of its proof, assembled from
Section 3: Lemma `lem:selection`, Lemma `lem:edge-charge`, Lemma
`lem:summation`, Lemma `lem:low-density`, Lemma `lem:high-density`, and the
common firing count Lemma `lem:common-count` (Jiang 2010, Prop. 2.5).

## What is formalized

The activity-one-half part: if `U^T σ = σ` for some `T ≥ 1` (any return length,
not only the minimal period) on a finite connected simple graph and
`2|E| - |V| < |σ| < 2|E|`, then every vertex fires in exactly `T/2` of the
rounds `0, …, T-1`; in particular `T` is even.  The final step of the paper
(activity 1/2 implies `T = 2`) uses the Jiang–Scully–Zhang no-clumpy-firing
theorem (SIAM J. Discrete Math. 2015, Thm 6.2) and is not formalized here.

Proof route.  The low-density side follows the paper (minimum prefix height,
edge charges).  For the high-density side the paper passes to the complement
game, which needs the Kominers–Kominers no-abundant-vertex lemma; here we use
instead the symmetric maximum-prefix-height argument (pick the round before a
maximum of `h_v(t) = T u_v(t) - q t`; there `v` fires, and each edge charge is
`≥ 0`). The common firing count is derived from
`SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_reachable`.
-/
import Mathlib

set_option autoImplicit false

namespace ParallelChipFiring

open Finset

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]


/-- The parallel chip-firing step operator `U`: every vertex `v` holding at least
`deg v` chips fires one chip to each neighbour; all others wait. -/
def step (σ : V → ℕ) : V → ℕ := fun v =>
  σ v - (if G.degree v ≤ σ v then G.degree v else 0) +
    #{w ∈ G.neighborFinset v | G.degree w ≤ σ w}

/-- `firings G σ v t = u_v(t)`: the number of rounds `s < t` in which `v` fires
(i.e. `deg v ≤ (U^s σ) v`). -/
def firings (σ : V → ℕ) (v : V) (t : ℕ) : ℕ :=
  #{s ∈ range t | G.degree v ≤ (step G)^[s] σ v}

/-- Recursion for the prefix firing count `u_v(t+1) = u_v(t) + F_t(v)`. -/
lemma firings_succ (σ : V → ℕ) (v : V) (t : ℕ) :
    firings G σ v (t + 1) =
      firings G σ v t + if G.degree v ≤ (step G)^[t] σ v then 1 else 0 := by
  simp only [firings, card_filter, sum_range_succ]

/-- The update rule `σ_{t+1} = σ_t - L F_t` at a vertex, read in `ℤ`. -/
lemma step_cast (σ : V → ℕ) (v : V) :
    ((step G σ v : ℕ) : ℤ) = σ v - G.degree v * (if G.degree v ≤ σ v then 1 else 0) +
      ∑ w ∈ G.neighborFinset v, (if G.degree w ≤ σ w then 1 else 0 : ℤ) := by
  unfold step
  rw [card_filter]
  split_ifs with h
  · push_cast [Nat.cast_sub h]; ring
  · rw [Nat.sub_zero]; push_cast; ring

/-- Telescoping (`σ_t = σ - L u(t)`) at a vertex, read in `ℤ`. -/
lemma iterate_cast (σ : V → ℕ) (v : V) (t : ℕ) :
    (((step G)^[t] σ v : ℕ) : ℤ) = σ v - G.degree v * (firings G σ v t : ℤ) +
      ∑ w ∈ G.neighborFinset v, (firings G σ w t : ℤ) := by
  induction t generalizing v with
  | zero => simp [firings]
  | succ t ih =>
    rw [Function.iterate_succ_apply', step_cast, ih]
    simp only [firings_succ]
    push_cast
    rw [sum_add_distrib]
    ring

/-- Common firing count (Jiang 2010, Prop. 2.5, the needed direction): on a
connected graph, if `U^T σ = σ` then every vertex fires equally often in rounds
`0, …, T-1`. -/
lemma firings_const (hG : G.Connected) (σ : V → ℕ) (T : ℕ) (hper : (step G)^[T] σ = σ)
    (v w : V) : firings G σ v T = firings G σ w T := by
  classical
  have hL : (G.lapMatrix ℝ).mulVec (fun x => (firings G σ x T : ℝ)) = 0 := by
    funext x
    rw [SimpleGraph.lapMatrix_mulVec_apply]
    have h := iterate_cast G σ x T
    rw [hper] at h
    have h' : (G.degree x : ℤ) * firings G σ x T = ∑ w ∈ G.neighborFinset x, (firings G σ w T : ℤ) := by
      linarith
    have h'' := congrArg (fun z : ℤ => (z : ℝ)) h'
    push_cast at h''
    simp [h'']
  have h := (SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_reachable G).1 hL v w (hG.preconnected v w)
  exact_mod_cast h


/-- Selection of a minimum of the prefix height `h_v(t) = T u_v(t) - q t` over
`1 ≤ t ≤ T`, written as `t = τ + 1` with `τ < T`; it is a minimum over all
`0 ≤ t ≤ T` because `h_v(0) = 0 = h_v(T)` when `u_v(T) = q`. -/
lemma exists_min_height (σ : V → ℕ) (T : ℕ) (hT : 0 < T) (q : ℤ) (v : V)
    (hq : (firings G σ v T : ℤ) = q) :
    ∃ τ < T, ∀ t ≤ T, (T : ℤ) * firings G σ v (τ + 1) - q * ((τ + 1 : ℕ) : ℤ) ≤
      (T : ℤ) * firings G σ v t - q * (t : ℤ) := by
  obtain ⟨τ, hτ, hmin⟩ := (range T).exists_min_image
    (fun s => (T : ℤ) * firings G σ v (s + 1) - q * ((s + 1 : ℕ) : ℤ)) ⟨0, by simp [hT]⟩
  refine ⟨τ, mem_range.1 hτ, fun t ht => ?_⟩
  rcases t with _ | t
  · have hlast := hmin (T - 1) (mem_range.2 (by omega))
    have hT1 : T - 1 + 1 = T := by omega
    simp only [hT1, hq] at hlast
    have h0 : firings G σ v 0 = 0 := rfl
    rw [h0, Nat.cast_zero, mul_zero, mul_zero, sub_zero]
    linarith
  · exact hmin t (mem_range.2 (by omega))

/-- Selection of a maximum of the prefix height `h_v(t) = T u_v(t) - q t` over
`1 ≤ t ≤ T`, written as `t = τ + 1` with `τ < T`; it is a maximum over all
`0 ≤ t ≤ T` because `h_v(0) = 0 = h_v(T)` when `u_v(T) = q`. -/
lemma exists_max_height (σ : V → ℕ) (T : ℕ) (hT : 0 < T) (q : ℤ) (v : V)
    (hq : (firings G σ v T : ℤ) = q) :
    ∃ τ < T, ∀ t ≤ T, (T : ℤ) * firings G σ v t - q * (t : ℤ) ≤
      (T : ℤ) * firings G σ v (τ + 1) - q * ((τ + 1 : ℕ) : ℤ) := by
  obtain ⟨τ, hτ, hmax⟩ := (range T).exists_max_image
    (fun s => (T : ℤ) * firings G σ v (s + 1) - q * ((s + 1 : ℕ) : ℤ)) ⟨0, by simp [hT]⟩
  refine ⟨τ, mem_range.1 hτ, fun t ht => ?_⟩
  rcases t with _ | t
  · have hlast := hmax (T - 1) (mem_range.2 (by omega))
    have hT1 : T - 1 + 1 = T := by omega
    simp only [hT1, hq] at hlast
    have h0 : firings G σ v 0 = 0 := rfl
    rw [h0, Nat.cast_zero, mul_zero, mul_zero, sub_zero]
    linarith
  · exact hmax t (mem_range.2 (by omega))

/-- Summing over ordered adjacent pairs is symmetric in the two endpoints. -/
lemma sum_neighbor_swap (f : V → V → ℤ) :
    ∑ v, ∑ w ∈ G.neighborFinset v, f v w = ∑ v, ∑ w ∈ G.neighborFinset v, f w v := by
  classical
  simp only [SimpleGraph.neighborFinset_eq_filter, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun v _ => sum_congr rfl fun w _ => ?_
  exact if_congr (G.adj_comm w v) rfl rfl

/-- Telescoping rearranged: `σ(v) = σ_τ(v) + Σ_{w ~ v} (u_v(τ) - u_w(τ))`. -/
lemma sigma_eq (σ : V → ℕ) (v : V) (τ : ℕ) :
    (σ v : ℤ) = ((step G)^[τ] σ v : ℕ) +
      ∑ w ∈ G.neighborFinset v, ((firings G σ v τ : ℤ) - firings G σ w τ) := by
  rw [iterate_cast, sum_sub_distrib, sum_const, SimpleGraph.card_neighborFinset_eq_degree,
    nsmul_eq_mul]
  ring


/-- Handshake lemma in `ℤ`: `Σ_v deg v = 2|E|`. -/
lemma sum_degree_int :
    ∑ v, (G.degree v : ℤ) = 2 * (#G.edgeFinset : ℤ) := by
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

/-- Lemma `lem:low-density` of arXiv:2608.04153: if every vertex fires `q` times in
rounds `0, …, T-1` with `2q < T`, then `|σ| ≤ 2|E| - |V|`. -/
lemma low_density (σ : V → ℕ) (T : ℕ) (hT : 0 < T) (q : ℕ)
    (hq : ∀ v, firings G σ v T = q) (h2q : 2 * q < T) :
    ∑ v, (σ v : ℤ) ≤ 2 * (#G.edgeFinset : ℤ) - Fintype.card V := by
  choose τ hτT hτmin using fun v => exists_min_height G σ T hT q v (by rw [hq v])
  have hwait : ∀ v, ¬ G.degree v ≤ (step G)^[τ v] σ v := by
    intro v hfire
    have h := hτmin v (τ v) (hτT v).le
    rw [firings_succ, if_pos hfire] at h
    push_cast at h
    have hTq : (T : ℤ) ≤ q := by linarith
    omega
  have hmin : ∀ v, ∀ t ≤ T, (T : ℤ) * firings G σ v (τ v) - q * (τ v : ℤ) - q ≤
      (T : ℤ) * firings G σ v t - q * (t : ℤ) := by
    intro v t ht
    have h := hτmin v t ht
    rw [firings_succ, if_neg (hwait v)] at h
    push_cast at h
    linarith
  have hcharge : ∀ v w, ((firings G σ v (τ v) : ℤ) - firings G σ w (τ v)) +
      ((firings G σ w (τ w) : ℤ) - firings G σ v (τ w)) ≤ 0 := by
    intro v w
    have h1 := hmin v (τ w) (hτT w).le
    have h2 := hmin w (τ v) (hτT v).le
    have hTK : (T : ℤ) * (((firings G σ v (τ v) : ℤ) - firings G σ w (τ v)) +
        ((firings G σ w (τ w) : ℤ) - firings G σ v (τ w))) ≤ 2 * q := by
      linarith
    by_contra hpos
    push Not at hpos
    have hTpos : (0 : ℤ) < T := by exact_mod_cast hT
    have h2qT : 2 * (q : ℤ) < T := by exact_mod_cast h2q
    nlinarith
  have hvertex : ∀ v, (σ v : ℤ) ≤ (G.degree v : ℤ) - 1 +
      ∑ w ∈ G.neighborFinset v, ((firings G σ v (τ v) : ℤ) - firings G σ w (τ v)) := by
    intro v
    rw [sigma_eq G σ v (τ v)]
    have h := hwait v
    push Not at h
    have h' : (((step G)^[τ v] σ v : ℕ) : ℤ) ≤ (G.degree v : ℤ) - 1 := by omega
    linarith
  set S := ∑ v, ∑ w ∈ G.neighborFinset v,
    ((firings G σ v (τ v) : ℤ) - firings G σ w (τ v)) with hS
  have hS2 : S + S ≤ 0 := by
    have hswap := sum_neighbor_swap G
      (fun v w => (firings G σ v (τ v) : ℤ) - firings G σ w (τ v))
    calc S + S = ∑ v, ∑ w ∈ G.neighborFinset v,
          ((((firings G σ v (τ v) : ℤ) - firings G σ w (τ v))) +
            ((firings G σ w (τ w) : ℤ) - firings G σ v (τ w))) := by
            conv_lhs => rw [hS]; arg 2; rw [hswap]
            rw [← sum_add_distrib]
            exact sum_congr rfl fun v _ => (sum_add_distrib).symm
      _ ≤ 0 := sum_nonpos fun v _ => sum_nonpos fun w _ => hcharge v w
  calc ∑ v, (σ v : ℤ)
      ≤ ∑ v, ((G.degree v : ℤ) - 1 + ∑ w ∈ G.neighborFinset v,
          ((firings G σ v (τ v) : ℤ) - firings G σ w (τ v))) := sum_le_sum fun v _ => hvertex v
    _ = ∑ v, (G.degree v : ℤ) - Fintype.card V + S := by
          rw [sum_add_distrib, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one]
    _ ≤ 2 * (#G.edgeFinset : ℤ) - Fintype.card V := by
          rw [sum_degree_int]
          linarith


/-- High-density bound (Lemma `lem:high-density` of arXiv:2608.04153, here by the
maximum-height argument): if every vertex fires `q` times in rounds `0, …, T-1`
with `T < 2q`, then `2|E| ≤ |σ|`. -/
lemma high_density (σ : V → ℕ) (T : ℕ) (hT : 0 < T) (q : ℕ)
    (hq : ∀ v, firings G σ v T = q) (h2q : T < 2 * q) :
    2 * (#G.edgeFinset : ℤ) ≤ ∑ v, (σ v : ℤ) := by
  choose τ hτT hτmax using fun v => exists_max_height G σ T hT q v (by rw [hq v])
  have hfire : ∀ v, G.degree v ≤ (step G)^[τ v] σ v := by
    intro v
    by_contra hwait
    have h := hτmax v (τ v) (hτT v).le
    rw [firings_succ, if_neg hwait] at h
    push_cast at h
    have hq0 : (q : ℤ) ≤ 0 := by linarith
    omega
  have hmax : ∀ v, ∀ t ≤ T, (T : ℤ) * firings G σ v t - q * (t : ℤ) ≤
      (T : ℤ) * firings G σ v (τ v) - q * (τ v : ℤ) + (T - q) := by
    intro v t ht
    have h := hτmax v t ht
    rw [firings_succ, if_pos (hfire v)] at h
    push_cast at h
    linarith
  have hcharge : ∀ v w, 0 ≤ ((firings G σ v (τ v) : ℤ) - firings G σ w (τ v)) +
      ((firings G σ w (τ w) : ℤ) - firings G σ v (τ w)) := by
    intro v w
    have h1 := hmax v (τ w) (hτT w).le
    have h2 := hmax w (τ v) (hτT v).le
    have hTK : -(2 * ((T : ℤ) - q)) ≤ (T : ℤ) * (((firings G σ v (τ v) : ℤ) -
        firings G σ w (τ v)) + ((firings G σ w (τ w) : ℤ) - firings G σ v (τ w))) := by
      linarith
    by_contra hneg
    push Not at hneg
    have hTpos : (0 : ℤ) < T := by exact_mod_cast hT
    have h2qT : (T : ℤ) < 2 * q := by exact_mod_cast h2q
    nlinarith
  have hvertex : ∀ v, (G.degree v : ℤ) +
      ∑ w ∈ G.neighborFinset v, ((firings G σ v (τ v) : ℤ) - firings G σ w (τ v)) ≤ σ v := by
    intro v
    rw [sigma_eq G σ v (τ v)]
    have h : ((G.degree v : ℕ) : ℤ) ≤ (((step G)^[τ v] σ v : ℕ) : ℤ) := by
      exact_mod_cast hfire v
    linarith
  set S := ∑ v, ∑ w ∈ G.neighborFinset v,
    ((firings G σ v (τ v) : ℤ) - firings G σ w (τ v)) with hS
  have hS2 : 0 ≤ S + S := by
    have hswap := sum_neighbor_swap G
      (fun v w => (firings G σ v (τ v) : ℤ) - firings G σ w (τ v))
    calc (0 : ℤ) ≤ ∑ v, ∑ w ∈ G.neighborFinset v,
          ((((firings G σ v (τ v) : ℤ) - firings G σ w (τ v))) +
            ((firings G σ w (τ w) : ℤ) - firings G σ v (τ w))) :=
          sum_nonneg fun v _ => sum_nonneg fun w _ => hcharge v w
      _ = S + S := by
            conv_rhs => rw [hS]; arg 2; rw [hswap]
            rw [← sum_add_distrib]
            exact sum_congr rfl fun v _ => sum_add_distrib
  calc 2 * (#G.edgeFinset : ℤ) ≤ ∑ v, (G.degree v : ℤ) + S := by
          rw [sum_degree_int]
          linarith
    _ = ∑ v, ((G.degree v : ℤ) + ∑ w ∈ G.neighborFinset v,
          ((firings G σ v (τ v) : ℤ) - firings G σ w (τ v))) := by
          rw [sum_add_distrib]
    _ ≤ ∑ v, (σ v : ℤ) := sum_le_sum fun v _ => hvertex v

/-- Activity one half (arXiv:2608.04153, Theorem 1.2, first paragraph of the proof):
on a finite connected simple graph, if `U^T σ = σ` with `T ≥ 1` and
`2|E| - |V| < |σ| < 2|E|`, then every vertex `v` fires in exactly half of the
rounds `0, …, T-1`. -/
theorem two_mul_card_fire_rounds_eq (hG : G.Connected) (σ : V → ℕ) (T : ℕ) (hT : 0 < T)
    (hper : (step G)^[T] σ = σ)
    (hlo : 2 * (#G.edgeFinset : ℤ) - Fintype.card V < ∑ v, (σ v : ℤ))
    (hhi : ∑ v, σ v < 2 * #G.edgeFinset) (v : V) :
    2 * #{t ∈ range T | G.degree v ≤ (step G)^[t] σ v} = T := by
  set q := firings G σ v T with hqdef
  have hq : ∀ w, firings G σ w T = q := fun w => firings_const G hG σ T hper w v
  rcases lt_trichotomy (2 * q) T with hlt | heq | hgt
  · have := low_density G σ T hT q hq hlt
    linarith
  · exact heq
  · have h := high_density G σ T hT q hq hgt
    have hhi' : ∑ v, (σ v : ℤ) < 2 * (#G.edgeFinset : ℤ) := by exact_mod_cast hhi
    linarith


/-- Corollary: under the hypotheses of `two_mul_card_fire_rounds_eq`, every return
length `T` of the game is even (on a graph with at least one vertex). -/
theorem even_of_periodic (hG : G.Connected) (σ : V → ℕ) (T : ℕ) (hT : 0 < T)
    (hper : (step G)^[T] σ = σ)
    (hlo : 2 * (#G.edgeFinset : ℤ) - Fintype.card V < ∑ v, (σ v : ℤ))
    (hhi : ∑ v, σ v < 2 * #G.edgeFinset) : Even T := by
  obtain ⟨v⟩ := hG.nonempty
  exact ⟨_, (two_mul_card_fire_rounds_eq G hG σ T hT hper hlo hhi v).symm.trans (two_mul _)⟩

/-! ### Examples

`K₂`: `(1,0) ↦ (0,1) ↦ (1,0)`, period 2.  `K₃`: the stable configurations
`σ = d - 1 = (1,1,1)` (activity 0, `|σ| = 2|E| - |V|`) and `σ = d = (2,2,2)`
(activity 1, `|σ| = 2|E|`) from the tightness remark after Lemma
`lem:high-density`, and the period-2 game `(2,2,0) ↦ (1,1,2) ↦ (2,2,0)`. -/

example : step (⊤ : SimpleGraph (Fin 2)) ![1, 0] = ![0, 1] := by decide
example : (step (⊤ : SimpleGraph (Fin 2)))^[2] ![1, 0] = ![1, 0] := by decide
example : step (⊤ : SimpleGraph (Fin 3)) ![1, 1, 1] = ![1, 1, 1] := by decide
example : step (⊤ : SimpleGraph (Fin 3)) ![2, 2, 2] = ![2, 2, 2] := by decide
example : step (⊤ : SimpleGraph (Fin 3)) ![2, 2, 0] = ![1, 1, 2] := by decide
example : (step (⊤ : SimpleGraph (Fin 3)))^[2] ![2, 2, 0] = ![2, 2, 0] := by decide
example : firings (⊤ : SimpleGraph (Fin 3)) ![2, 2, 0] 2 2 = 1 := by decide
example : #(⊤ : SimpleGraph (Fin 2)).edgeFinset = 1 := by decide
example : #(⊤ : SimpleGraph (Fin 3)).edgeFinset = 3 := by decide
example : #{t ∈ range 2 | (⊤ : SimpleGraph (Fin 2)).degree 0 ≤ (step ⊤)^[t] ![1, 0] 0} = 1 := by decide

/- Non-vacuity: all hypotheses of the main theorem hold jointly on `K₂`. -/
example : 2 * #{t ∈ range 2 | (⊤ : SimpleGraph (Fin 2)).degree 0 ≤ (step ⊤)^[t] ![1, 0] 0} = 2 :=
  two_mul_card_fire_rounds_eq ⊤ SimpleGraph.connected_top ![1, 0] 2 (by norm_num) (by decide)
    (by decide) (by decide) 0

end ParallelChipFiring
