/-
# King's conjecture on equivalence coverings of powers of cycles is false

## Source

Zhanping Yang, *Covering powers of cycles with equivalence subgraphs*,
arXiv:2610.15635 (retrieved 2026-10-21).

* Conjecture 1.1 (King, Open Problem Garden 2011), verbatim:
  "Given $k$ and $n$, the graph $C_n^k$ has equivalence covering number
  $\Omega(k)$."  The intended reading (abstract and Section 1 of the paper) is
  `eq(C_n^k) = Ω(k)` for `n` sufficiently large relative to `k`.
* Lemma 2.3 (`lem:comparison`, binary half-graph cover) and Theorem 2.4
  (`thm:main-divisible`), verbatim: "For all integers $k\ge1$ and $q\ge2$, we
  have $\operatorname{eq}(C_{q(k+1)}^k)=1+\lceil\log_2(k+1)\rceil$."
* Lemma 2.2 (`lem:lower`), verbatim: "If $n\ge2k+2$, then
  $\operatorname{eq}(C_n^k)\ge1+\lceil\log_2(k+1)\rceil$."

Status: proved in the paper (date of this formalization: 2026-10-21).  The
paper refutes King's conjecture: along `n = q(k+1)` the equivalence covering
number is logarithmic in `k`.

## Formal reading

* `C_n^k` is `cyclePower n k` on `Fin n`: distinct vertices are adjacent when
  their cyclic distance `min ((u - v) mod n) ((v - u) mod n)` is at most `k`.
  The ground-truth check `cyclePower 7 1 = SimpleGraph.cycleGraph 7` ties it to
  Mathlib's cycle graph.
* An equivalence subgraph of `G` (a spanning disjoint union of cliques of `G`,
  isolated vertices allowed) is recorded by its equivalence relation: a
  `Setoid` on the vertices whose distinct related pairs are edges of `G`.  The
  edges of the equivalence subgraph are exactly the distinct related pairs.
* `EqCoverable G t` says that `t` equivalence subgraphs cover `E(G)`, and
  `eqNumber G` is the least such `t`.
-/
import Mathlib

set_option autoImplicit false

namespace CyclePowerEquivalenceKing

/-! ## Definitions -/

/-- The cyclic distance between two vertices of the `n`-cycle on `Fin n`. -/
def cycDist {n : ℕ} (u v : Fin n) : ℕ := min (u - v).val (v - u).val

/-- The `k`th power `C_n^k` of the cycle `C_n`: distinct vertices are adjacent
when their cyclic distance is at most `k`. -/
def cyclePower (n k : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ cycDist u v ≤ k
  symm := ⟨fun u v h => ⟨h.1.symm, by unfold cycDist at *; omega⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Adjacency in `C_n^k` is decidable. -/
instance (n k : ℕ) : DecidableRel (cyclePower n k).Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ cycDist u v ≤ k))

/-- `r` is (the relation of) an equivalence subgraph of `G`: every class of `r`
is a clique of `G`.  Its edges are the pairs of distinct `r`-related vertices. -/
def IsEquivSubgraph {V : Type*} (G : SimpleGraph V) (r : Setoid V) : Prop :=
  ∀ u v, u ≠ v → r u v → G.Adj u v

/-- The edges of `G` are covered by `t` equivalence subgraphs of `G`. -/
def EqCoverable {V : Type*} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ r : Fin t → Setoid V, (∀ i, IsEquivSubgraph G (r i)) ∧
    ∀ u v, G.Adj u v → ∃ i, r i u v

/-- The equivalence covering number `eq(G)`: the least number of equivalence
subgraphs of `G` covering all edges of `G`. -/
noncomputable def eqNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {t | EqCoverable G t}

/-! ## Ground truth -/

example : cyclePower 7 1 = SimpleGraph.cycleGraph 7 := by
  ext u v; revert u v; decide

example : (cyclePower 8 3).Adj 0 3 ∧ (cyclePower 8 3).Adj 1 6 ∧
    ¬ (cyclePower 8 3).Adj 0 4 := by decide

/-- For `n ≤ 2k+1`, `C_n^k` is complete (paper, start of Section 2). -/
example : cyclePower 5 2 = ⊤ := by ext u v; revert u v; decide

/-! ## Arithmetic of `Fin n` subtraction -/

/-- The value of `v - u` in `Fin n`. -/
theorem val_sub_eq {n : ℕ} (u v : Fin n) :
    (v - u).val = if u.val ≤ v.val then v.val - u.val else n + v.val - u.val := by
  split_ifs with h
  · exact Fin.sub_val_of_le h
  · exact Fin.coe_sub_iff_lt.mpr (lt_of_not_ge h)

/-- If `v` is `d ≤ k` steps after `u` around the cycle, then `u v` is an edge
of `C_n^k` (for `u ≠ v`). -/
theorem adj_of_val {n k d : ℕ} {u v : Fin n} (hne : u ≠ v) (hd : d ≤ k)
    (h : v.val = u.val + d ∨ v.val + n = u.val + d) : (cyclePower n k).Adj u v := by
  refine ⟨hne, ?_⟩
  have hsub := val_sub_eq u v
  have hu := u.isLt
  have hv := v.isLt
  have hvu : (v - u).val ≤ k := by
    rw [hsub]; split_ifs <;> omega
  unfold cycDist; omega

/-- An edge of `C_n^k` joins `u` to a vertex `d ≤ k` steps ahead of it, or
`v` to a vertex `d ≤ k` steps ahead of it. -/
theorem val_of_adj {n k : ℕ} {u v : Fin n} (h : (cyclePower n k).Adj u v) :
    ∃ d ≤ k, (v.val = u.val + d ∨ v.val + n = u.val + d) ∨
      (u.val = v.val + d ∨ u.val + n = v.val + d) := by
  obtain ⟨-, hdist⟩ := h
  unfold cycDist at hdist
  have h1 := val_sub_eq u v
  have h2 := val_sub_eq v u
  have hu := u.isLt
  have hv := v.isLt
  rcases min_le_iff.mp hdist with hk | hk
  · refine ⟨(u - v).val, hk, Or.inr ?_⟩
    rw [h2]; split_ifs <;> omega
  · refine ⟨(v - u).val, hk, Or.inl ?_⟩
    rw [h1]; split_ifs <;> omega

/-! ## The binary half-graph cover (Lemma 2.3, Theorem 2.4 upper bound) -/

/-- Cyclic predecessor of a block index `j` among `q` blocks. -/
def predBlock (q j : ℕ) : ℕ := if j = 0 then q - 1 else j - 1

/-- The label of position `x = j(k+1) + a` in layer `l`.  With
`m = ⌊a / 2^l⌋ = 2p + ε`, the vertex lies in the clique `Q_{j,l,p}` when
`ε = 1` and in `Q_{j-1,l,p}` when `ε = 0` (paper, equation `Qjlp` and the
proof of Claim `disjoint`).  For `2^l > k` every `m` is `0`, and the layer is
the partition into the blocks `B_j`. -/
def layerLabel (q k l x : ℕ) : ℕ × ℕ :=
  let m := x % (k + 1) / 2 ^ l
  (if m % 2 = 1 then x / (k + 1) else predBlock q (x / (k + 1)), m / 2)

/-- The `l`th equivalence subgraph of the cover of `C_{q(k+1)}^k`. -/
def layerSetoid (q k l : ℕ) : Setoid (Fin (q * (k + 1))) :=
  Setoid.ker fun v => layerLabel q k l v.val

example : layerLabel 3 3 1 2 = (0, 0) ∧ layerLabel 3 3 1 3 = (0, 0) ∧
    layerLabel 3 3 1 4 = (0, 0) ∧ layerLabel 3 3 1 5 = (0, 0) ∧
    layerLabel 3 3 1 6 = (1, 0) := by decide

/-- Decomposition of a position into block index and offset. -/
theorem div_mod_of_eq {k j a x : ℕ} (hx : x = (k + 1) * j + a) (ha : a < k + 1) :
    x / (k + 1) = j ∧ x % (k + 1) = a := by
  subst hx
  constructor
  · rw [Nat.mul_add_div (Nat.succ_pos k), Nat.div_eq_of_lt ha, Nat.add_zero]
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt ha]

/-- The highest differing binary digit (proof of Lemma 2.3): for `b < a < 2^L`
there is a level `l ≤ L` at which `⌊a/2^l⌋ = 2p+1` and `⌊b/2^l⌋ = 2p`. -/
theorem exists_split_level {a b L : ℕ} (hba : b < a) (haL : a < 2 ^ L) :
    ∃ l ≤ L, (a / 2 ^ l) % 2 = 1 ∧ (b / 2 ^ l) % 2 = 0 ∧
      a / 2 ^ l / 2 = b / 2 ^ l / 2 := by
  classical
  have hP : ∃ l, a / 2 ^ l / 2 = b / 2 ^ l / 2 := by
    refine ⟨L, ?_⟩
    rw [Nat.div_eq_of_lt haL, Nat.div_eq_of_lt (hba.trans haL)]
  refine ⟨Nat.find hP, ?_, ?_⟩
  · refine Nat.find_min' hP ?_
    rw [Nat.div_eq_of_lt haL, Nat.div_eq_of_lt (hba.trans haL)]
  have hspec := Nat.find_spec hP
  have hne : a / 2 ^ Nat.find hP ≠ b / 2 ^ Nat.find hP := by
    rcases hfind : Nat.find hP with _ | l
    · simpa using hba.ne'
    · have hmin := Nat.find_min hP (show l < Nat.find hP by omega)
      rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
      exact hmin
  have hle : b / 2 ^ Nat.find hP ≤ a / 2 ^ Nat.find hP := Nat.div_le_div_right hba.le
  omega

/-- The layer label of `x = j(k+1) + a` in terms of `j` and `a`. -/
theorem layerLabel_of {q k l j a x : ℕ} (hx : x = (k + 1) * j + a) (ha : a < k + 1) :
    layerLabel q k l x =
      (if (a / 2 ^ l) % 2 = 1 then j else predBlock q j, a / 2 ^ l / 2) := by
  obtain ⟨hj, hr⟩ := div_mod_of_eq hx ha
  simp only [layerLabel, hj, hr]

/-- Every vertex of `C_{q(k+1)}^k` has a block index `j < q` and offset `a ≤ k`. -/
theorem exists_block {q k : ℕ} (u : Fin (q * (k + 1))) :
    ∃ j a, j < q ∧ a < k + 1 ∧ u.val = (k + 1) * j + a := by
  refine ⟨u.val / (k + 1), u.val % (k + 1), ?_, Nat.mod_lt _ (Nat.succ_pos k),
    (Nat.div_add_mod _ _).symm⟩
  exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos k)).mpr u.isLt

/-- Two distinct vertices of the same block `B_j` are adjacent in `C_{q(k+1)}^k`. -/
theorem adj_same_block {q k j a b : ℕ} {u v : Fin (q * (k + 1))} (hne : u ≠ v)
    (ha : a < k + 1) (hb : b < k + 1)
    (hu : u.val = (k + 1) * j + a) (hv : v.val = (k + 1) * j + b) :
    (cyclePower (q * (k + 1)) k).Adj u v := by
  rcases le_total a b with hab | hab
  · exact adj_of_val (d := b - a) hne (by omega) (Or.inl (by omega))
  · exact (adj_of_val (d := a - b) hne.symm (by omega) (Or.inl (by omega))).symm

/-- A vertex `A_a` of `B_j` and a vertex `B_b` of the next block `B_{j+1}`
(cyclically) are adjacent when `a > b` (proof of Theorem 2.4). -/
theorem adj_next_block {q k j j' a b : ℕ} {u v : Fin (q * (k + 1))}
    (hba : b < a) (ha : a < k + 1)
    (hj' : j' = j + 1 ∨ (j' = 0 ∧ j + 1 = q))
    (hu : u.val = (k + 1) * j + a) (hv : v.val = (k + 1) * j' + b) :
    (cyclePower (q * (k + 1)) k).Adj u v := by
  have hsucc : (k + 1) * (j + 1) = (k + 1) * j + (k + 1) := by ring
  rcases hj' with rfl | ⟨rfl, hq⟩
  · have hne : u ≠ v := by
      intro h; rw [h] at hu; omega
    exact adj_of_val (d := k + 1 + b - a) hne (by omega) (Or.inl (by omega))
  · have hn : q * (k + 1) = (k + 1) * j + (k + 1) := by rw [← hq]; ring
    have hne : u ≠ v := by
      intro h; rw [h] at hu; omega
    exact adj_of_val (d := k + 1 + b - a) hne (by omega) (Or.inr (by omega))

/-- `predBlock q` is injective on block indices `j < q`. -/
theorem predBlock_inj {q j j' : ℕ} (hj : j < q) (hj' : j' < q)
    (h : predBlock q j = predBlock q j') : j = j' := by
  unfold predBlock at h; split_ifs at h <;> omega

/-- `predBlock q j' = j` identifies `j'` as the cyclic successor of `j`. -/
theorem succ_of_predBlock {q j j' : ℕ} (hj' : j' < q) (h : predBlock q j' = j) :
    j' = j + 1 ∨ (j' = 0 ∧ j + 1 = q) := by
  unfold predBlock at h; split_ifs at h <;> omega

/-- Each layer is an equivalence subgraph of `C_{q(k+1)}^k`: its classes are the
cliques `Q_{j,l,p}` (Lemma 2.3 and Claim `disjoint` of Theorem 2.4). -/
theorem isEquivSubgraph_layerSetoid (q k l : ℕ) :
    IsEquivSubgraph (cyclePower (q * (k + 1)) k) (layerSetoid q k l) := by
  intro u v hne huv
  change layerLabel q k l u.val = layerLabel q k l v.val at huv
  obtain ⟨j, a, hj, ha, hu⟩ := exists_block u
  obtain ⟨j', b, hj', hb, hv⟩ := exists_block v
  rw [layerLabel_of hu ha, layerLabel_of hv hb, Prod.mk.injEq] at huv
  obtain ⟨h1, h2⟩ := huv
  have hcmp : ∀ x y : ℕ, (x / 2 ^ l) % 2 = 1 → (y / 2 ^ l) % 2 = 0 →
      x / 2 ^ l / 2 = y / 2 ^ l / 2 → y < x := by
    intro x y hx hy hxy
    by_contra hcon
    have := Nat.div_le_div_right (c := 2 ^ l) (not_lt.mp hcon)
    omega
  split_ifs at h1 with hpa hpb hpb
  · subst h1; exact adj_same_block hne ha hb hu hv
  · have hpb' : (b / 2 ^ l) % 2 = 0 := by omega
    exact adj_next_block (hcmp a b hpa hpb' h2) ha
      (succ_of_predBlock hj' h1.symm) hu hv
  · have hpa' : (a / 2 ^ l) % 2 = 0 := by omega
    exact (adj_next_block (hcmp b a hpb hpa' h2.symm) hb
      (succ_of_predBlock hj h1) hv hu).symm
  · have h1' := predBlock_inj hj hj' h1
    subst h1'; exact adj_same_block hne ha hb hu hv

/-- Directed cover step: if `v` is `d ≤ k` steps ahead of `u`, then some layer
`l ≤ L` (with `k + 1 ≤ 2^L`) puts `u` and `v` in a common class. -/
theorem exists_layer_of_ahead {q k L d : ℕ} (hL : k + 1 ≤ 2 ^ L) {u v : Fin (q * (k + 1))}
    (hd : d ≤ k) (h : v.val = u.val + d ∨ v.val + q * (k + 1) = u.val + d) :
    ∃ l ≤ L, layerLabel q k l u.val = layerLabel q k l v.val := by
  obtain ⟨j, a, hj, ha, hu⟩ := exists_block u
  have hvlt := v.isLt
  have hsucc : (k + 1) * (j + 1) = (k + 1) * j + (k + 1) := by ring
  have hjq : (k + 1) * (j + 1) ≤ q * (k + 1) := by
    rw [mul_comm q]; exact Nat.mul_le_mul_left _ hj
  rcases Nat.lt_or_ge (a + d) (k + 1) with had | had
  · -- same block: the top layer `L` is the block partition
    have hv : v.val = (k + 1) * j + (a + d) := by omega
    refine ⟨L, le_rfl, ?_⟩
    rw [layerLabel_of hu ha, layerLabel_of hv had,
      Nat.div_eq_of_lt (ha.trans_le hL), Nat.div_eq_of_lt (had.trans_le hL)]
  · -- next block: `v = B_b` with `b = a + d - (k + 1) < a`
    set b := a + d - (k + 1) with hbdef
    have hba : b < a := by omega
    have hb : b < k + 1 := by omega
    obtain ⟨j', hj', hv, hpred⟩ : ∃ j', j' < q ∧ v.val = (k + 1) * j' + b ∧
        predBlock q j' = j := by
      rcases Nat.lt_or_ge (j + 1) q with hjq' | hjq'
      · have hjq2 : (k + 1) * (j + 1 + 1) ≤ q * (k + 1) := by
          rw [mul_comm q]; exact Nat.mul_le_mul_left _ hjq'
        have hsucc2 : (k + 1) * (j + 1 + 1) = (k + 1) * (j + 1) + (k + 1) := by ring
        refine ⟨j + 1, hjq', by omega, ?_⟩
        simp [predBlock]
      · have hjq' : j + 1 = q := by omega
        have hn : q * (k + 1) = (k + 1) * j + (k + 1) := by rw [← hjq']; ring
        refine ⟨0, by omega, by omega, ?_⟩
        simp only [predBlock, if_true]; omega
    obtain ⟨l, hlL, hodd, heven, hhalf⟩ :=
      exists_split_level (L := L) hba (ha.trans_le hL)
    refine ⟨l, hlL, ?_⟩
    rw [layerLabel_of hu ha, layerLabel_of hv hb, if_pos hodd, if_neg (by omega), hpred,
      hhalf]

/-- The `1 + ⌈log₂(k+1)⌉` layers cover every edge of `C_{q(k+1)}^k`
(proof of Theorem 2.4). -/
theorem exists_layer_of_adj {q k L : ℕ} (hL : k + 1 ≤ 2 ^ L) {u v : Fin (q * (k + 1))}
    (h : (cyclePower (q * (k + 1)) k).Adj u v) :
    ∃ l ≤ L, layerLabel q k l u.val = layerLabel q k l v.val := by
  obtain ⟨d, hd, hfwd | hbwd⟩ := val_of_adj h
  · exact exists_layer_of_ahead hL hd hfwd
  · obtain ⟨l, hl, heq⟩ := exists_layer_of_ahead hL hd hbwd
    exact ⟨l, hl, heq.symm⟩

/-- **Theorem 2.4, upper bound** (arXiv:2610.15635): `C_{q(k+1)}^k` is covered by
`1 + ⌈log₂(k+1)⌉` equivalence subgraphs.  (The construction needs no
hypotheses on `q` and `k`.) -/
theorem eqCoverable_divisible (k q : ℕ) :
    EqCoverable (cyclePower (q * (k + 1)) k) (1 + Nat.clog 2 (k + 1)) := by
  have hL : k + 1 ≤ 2 ^ Nat.clog 2 (k + 1) := Nat.le_pow_clog (by norm_num) _
  refine ⟨fun i => layerSetoid q k i.val, fun i => isEquivSubgraph_layerSetoid q k i.val, ?_⟩
  intro u v huv
  obtain ⟨l, hl, heq⟩ := exists_layer_of_adj hL huv
  exact ⟨⟨l, by omega⟩, heq⟩

/-! ## King's conjecture is false -/

/-- For every `C > 0` and every `k₀` there is `k ≥ max k₀ 1` with
`1 + ⌈log₂(k+1)⌉ < C k`; one may take `k = 4^M - 1` with `M` large. -/
theorem exists_clog_lt (C : ℝ) (hC : 0 < C) (k₀ : ℕ) :
    ∃ k : ℕ, k₀ ≤ k ∧ 1 ≤ k ∧ ((1 + Nat.clog 2 (k + 1) : ℕ) : ℝ) < C * k := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (4 / C) (by norm_num : (1 : ℝ) < 2)
  set M := m + k₀ + 1 with hM
  have hpos : 2 ≤ 2 ^ M := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow : 4 ≤ 2 ^ (2 * M) := by
    rw [pow_mul']; nlinarith
  have h2M : 2 * M < 2 ^ (2 * M) := Nat.lt_two_pow_self
  refine ⟨2 ^ (2 * M) - 1, by omega, by omega, ?_⟩
  have hk1 : 2 ^ (2 * M) - 1 + 1 = 2 ^ M * 2 ^ M := by
    rw [← pow_add, ← two_mul]; omega
  have hclog : Nat.clog 2 (2 ^ (2 * M) - 1 + 1) = 2 * M := by
    rw [show 2 ^ (2 * M) - 1 + 1 = 2 ^ (2 * M) by omega, Nat.clog_pow 2 _ (by norm_num)]
  rw [hclog]
  have hMlt : M < 2 ^ M := Nat.lt_two_pow_self
  set X : ℝ := (2 : ℝ) ^ M with hX
  have hXM : (M : ℝ) + 1 ≤ X := by
    rw [hX]; exact_mod_cast hMlt
  have hX2 : (2 : ℝ) ≤ X := by rw [hX]; exact_mod_cast hpos
  have hkX : ((2 ^ (2 * M) - 1 : ℕ) : ℝ) = X * X - 1 := by
    have hcast : ((2 ^ (2 * M) - 1 : ℕ) : ℝ) + 1 = X * X := by
      rw [hX]; exact_mod_cast hk1
    linarith
  have hCX : 8 < C * X := by
    have h1 : 4 / C * C = 4 := div_mul_cancel₀ 4 hC.ne'
    have h2 : 2 * (2 : ℝ) ^ m ≤ X := by
      rw [hX, hM, pow_add, pow_add, pow_one]
      have h3 : (1 : ℝ) ≤ 2 ^ k₀ := one_le_pow₀ (by norm_num)
      have h4 : (0 : ℝ) < 2 ^ m := by positivity
      nlinarith
    nlinarith
  rw [hkX]
  push_cast
  nlinarith

/-- **King's conjecture is false**, asymptotic form (arXiv:2610.15635,
Conjecture 1.1 refuted by Theorem 2.4).  There are no `C > 0` and `k₀` such
that for every `k ≥ k₀`, every sufficiently large `n`, and every covering of
`C_n^k` by `t` equivalence subgraphs, `C k ≤ t`. -/
theorem king_conjecture_false_eventually :
    ¬ ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ t : ℕ, EqCoverable (cyclePower n k) t → C * k ≤ t := by
  rintro ⟨C, hC, k₀, hking⟩
  obtain ⟨k, hk₀, -, hlt⟩ := exists_clog_lt C hC k₀
  obtain ⟨N, hN⟩ := hking k hk₀
  have hn : N ≤ (N + 1) * (k + 1) := by nlinarith
  have hle := hN _ hn _ (eqCoverable_divisible k (N + 1))
  linarith

/-- **King's conjecture is false** (arXiv:2610.15635, Conjecture 1.1 refuted by
Theorem 2.4).  King conjectured `eq(C_n^k) = Ω(k)` for `n` large relative to
`k`: there is `C > 0` such that for every `k ≥ 1`, every sufficiently large `n`,
and every covering of `C_n^k` by `t` equivalence subgraphs, `C k ≤ t`.  This
fails: `C_{q(k+1)}^k` is covered by `1 + ⌈log₂(k+1)⌉` equivalence subgraphs for
every `q`. -/
theorem king_conjecture_false :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ t : ℕ, EqCoverable (cyclePower n k) t → C * k ≤ t := by
  rintro ⟨C, hC, hking⟩
  exact king_conjecture_false_eventually ⟨C, hC, 1, hking⟩

/-! ## The rank lower bound (Lemma 2.2) -/

/-- Vertices at cyclic distance exactly `k + 1` are not adjacent when
`2k + 2 ≤ n`. -/
theorem not_adj_of_val {n k : ℕ} (hn : 2 * k + 2 ≤ n) {u v : Fin n}
    (h : v.val = u.val + (k + 1) ∨ v.val + n = u.val + (k + 1)) :
    ¬ (cyclePower n k).Adj u v := by
  rintro ⟨-, hdist⟩
  unfold cycDist at hdist
  have h1 := val_sub_eq u v
  have h2 := val_sub_eq v u
  have hu := u.isLt
  have hv := v.isLt
  rw [h1, h2] at hdist
  split_ifs at hdist <;> omega

/-- An integer labelling of the classes of a setoid on `Fin n`: two vertices
get the same label exactly when they are related. -/
noncomputable def classLabel {n : ℕ} (r : Setoid (Fin n)) (v : Fin n) : ℚ :=
  ((Quotient.mk r v).out.val : ℚ)

/-- Labels of `classLabel r` agree exactly on `r`-related vertices. -/
theorem classLabel_eq_iff {n : ℕ} (r : Setoid (Fin n)) (u v : Fin n) :
    classLabel r u = classLabel r v ↔ r u v := by
  unfold classLabel
  rw [Nat.cast_inj, Fin.val_inj, Quotient.out_inj, Quotient.eq]

/-- **Lemma 2.2** (arXiv:2610.15635), rank form: if `C_n^k` with `k ≥ 1` and
`n ≥ 2k + 2` is covered by `t` equivalence subgraphs, then `2k + 2 ≤ 2^t`. -/
theorem two_mul_add_two_le_two_pow {n k t : ℕ} (hk : 1 ≤ k) (hn : 2 * k + 2 ≤ n)
    (h : EqCoverable (cyclePower n k) t) : 2 * k + 2 ≤ 2 ^ t := by
  classical
  obtain ⟨r, hr, hcov⟩ := h
  -- some layer exists, since `C_n^k` has an edge
  have h01 : (cyclePower n k).Adj ⟨0, by omega⟩ ⟨1, by omega⟩ :=
    adj_of_val (d := 1) (fun h => by simp [Fin.ext_iff] at h) hk (Or.inl rfl)
  obtain ⟨s₀, -⟩ := hcov _ _ h01
  set m := 2 * k + 2 with hm
  let c : Fin t → Fin n → ℚ := fun s v => classLabel (r s) v
  let x : Fin m → Fin n := fun i => ⟨i.val, by omega⟩
  let y : Fin m → Fin n := fun j => ⟨(j.val + k + 1) % n, Nat.mod_lt _ (by omega)⟩
  have hy : ∀ j : Fin m, (y j).val = j.val + k + 1 ∨ (y j).val + n = j.val + k + 1 := by
    intro j
    rcases Nat.lt_or_ge (j.val + k + 1) n with hlt | hge
    · exact Or.inl (Nat.mod_eq_of_lt hlt)
    · right
      have hj := j.isLt
      change (j.val + k + 1) % n + n = j.val + k + 1
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
      omega
  let M : Matrix (Fin m) (Fin m) ℚ := fun i j => ∏ s, (c s (x i) - c s (y j))
  let U : Matrix (Fin m) (Finset (Fin t)) ℚ := fun i S => ∏ s ∈ S, c s (x i)
  let W : Matrix (Finset (Fin t)) (Fin m) ℚ := fun S j =>
    ∏ s ∈ Finset.univ \ S, (-c s (y j))
  have hMUW : M = U * W := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [M, U, W, sub_eq_add_neg]
    rw [Finset.prod_add, Finset.powerset_univ]
  -- Claim `diagonal`
  have hdiag : ∀ i, M i i ≠ 0 := by
    intro i
    refine Finset.prod_ne_zero_iff.mpr fun s _ => sub_ne_zero.mpr fun heq => ?_
    have hrel := (classLabel_eq_iff (r s) _ _).mp heq
    have hval : (y i).val = (x i).val + (k + 1) ∨ (y i).val + n = (x i).val + (k + 1) := by
      rcases hy i with h1 | h1
      · exact Or.inl (by simp only [x]; omega)
      · exact Or.inr (by simp only [x]; omega)
    have hne : x i ≠ y i := by
      intro hxy; rw [hxy] at hval; omega
    exact not_adj_of_val hn hval (hr s _ _ hne hrel)
  -- Claim `triangular`
  have htri : M.BlockTriangular id := by
    intro i j hji
    simp only [id] at hji
    have hji' : j.val < i.val := hji
    have hi := i.isLt
    have hcase : x i = y j ∨ (cyclePower n k).Adj (x i) (y j) := by
      by_cases hxy : x i = y j
      · exact Or.inl hxy
      right
      rcases Nat.lt_or_ge (j.val + k + 1) i.val with hlt | hge
      · have hyv : (y j).val = j.val + k + 1 := by
          rcases hy j with h1 | h1
          · exact h1
          · omega
        exact (adj_of_val (d := i.val - (j.val + k + 1)) (Ne.symm hxy) (by omega)
          (Or.inl (by simp only [x]; omega))).symm
      · rcases hy j with h1 | h1
        · exact adj_of_val (d := j.val + k + 1 - i.val) hxy (by omega)
            (Or.inl (by simp only [x]; omega))
        · exact adj_of_val (d := j.val + k + 1 - i.val) hxy (by omega)
            (Or.inr (by simp only [x]; omega))
    obtain ⟨s, hs⟩ : ∃ s, r s (x i) (y j) := by
      rcases hcase with hxy | hadj
      · exact ⟨s₀, hxy ▸ (r s₀).refl' _⟩
      · exact hcov _ _ hadj
    exact Finset.prod_eq_zero (Finset.mem_univ s)
      (sub_eq_zero.mpr ((classLabel_eq_iff (r s) _ _).mpr hs))
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular htri]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hdiag i
  have hrank : M.rank = m := by
    rw [Matrix.rank_of_isUnit M ((Matrix.isUnit_iff_isUnit_det M).mpr hdet.isUnit),
      Fintype.card_fin]
  calc m = M.rank := hrank.symm
    _ = (U * W).rank := by rw [hMUW]
    _ ≤ U.rank := Matrix.rank_mul_le_left U W
    _ ≤ Fintype.card (Finset (Fin t)) := Matrix.rank_le_card_width U
    _ = 2 ^ t := by rw [Fintype.card_finset, Fintype.card_fin]

/-- **Lemma 2.2** (arXiv:2610.15635): for `k ≥ 1` and `n ≥ 2k + 2`, every covering
of `C_n^k` by `t` equivalence subgraphs has `1 + ⌈log₂(k+1)⌉ ≤ t`. -/
theorem one_add_clog_le_of_eqCoverable {n k t : ℕ} (hk : 1 ≤ k) (hn : 2 * k + 2 ≤ n)
    (h : EqCoverable (cyclePower n k) t) : 1 + Nat.clog 2 (k + 1) ≤ t := by
  have hpow := two_mul_add_two_le_two_pow hk hn h
  obtain _ | t' := t
  · simp at hpow
  · have hle : k + 1 ≤ 2 ^ t' := by rw [pow_succ] at hpow; omega
    have := Nat.clog_le_of_le_pow hle
    omega

/-- **Theorem 2.4** (arXiv:2610.15635): for all `k ≥ 1` and `q ≥ 2`,
`eq(C_{q(k+1)}^k) = 1 + ⌈log₂(k+1)⌉`. -/
theorem eqNumber_cyclePower_divisible {k q : ℕ} (hk : 1 ≤ k) (hq : 2 ≤ q) :
    eqNumber (cyclePower (q * (k + 1)) k) = 1 + Nat.clog 2 (k + 1) := by
  have hmem := eqCoverable_divisible k q
  have hn : 2 * k + 2 ≤ q * (k + 1) := by nlinarith
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ fun t ht => ?_)
  exact one_add_clog_le_of_eqCoverable hk hn ht

/-- Non-vacuity: the paper's smallest divisible instance `eq(C_8^3) = 3`
(`k = 3`, `q = 2`), with both hypotheses of Theorem 2.4 met. -/
example : eqNumber (cyclePower 8 3) = 3 := by
  have h := eqNumber_cyclePower_divisible (k := 3) (q := 2) (by norm_num) (by norm_num)
  have hclog : Nat.clog 2 (3 + 1) = 2 := by
    rw [show (3 + 1 : ℕ) = 2 ^ 2 by norm_num, Nat.clog_pow 2 2 (by norm_num)]
  rw [hclog] at h
  exact h

end CyclePowerEquivalenceKing
