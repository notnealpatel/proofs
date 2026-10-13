import Combinatorics.Sidon

set_option autoImplicit false

namespace SidonHypercube

/-- A Boolean vector embedded into natural vectors for ordinary addition. -/
def emb {n : ℕ} (v : Fin n → Bool) : Fin n → ℕ := fun i => if v i then 1 else 0

example : emb ![true] + emb ![true] = ![2] := by decide

/-- Only trivial reorderings have equal ordinary sums in a cube subset. -/
def IsSidonCube {n : ℕ} (S : Finset (Fin n → Bool)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    emb a + emb b = emb c + emb d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

instance {n : ℕ} (S : Finset (Fin n → Bool)) : Decidable (IsSidonCube S) := by
  unfold IsSidonCube; infer_instance

example : IsSidonCube (∅ : Finset (Fin 3 → Bool)) := by decide
example : IsSidonCube (Finset.univ : Finset (Fin 1 → Bool)) := by decide

/-- The maximum size of a Sidon subset of the Boolean `n`-cube. -/
noncomputable def a309370 (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ S : Finset (Fin n → Bool), IsSidonCube S ∧ S.card = k}

/-- The ordinary-addition embedding is injective. -/
theorem emb_injective {n : ℕ} : Function.Injective (@emb n) := by
  intro a b h
  funext i
  have hi := congrFun h i
  cases ha : a i <;> cases hb : b i <;> simp [emb, ha, hb] at hi ⊢

/-- The cube predicate agrees with the general predicate on its image. -/
theorem isSidonCube_iff {n : ℕ} (S : Finset (Fin n → Bool)) :
    IsSidonCube S ↔ Sidon.IsSidon (S.image emb) := by
  constructor
  · intro h a ha b hb c hc d hd heq
    obtain ⟨a, h_a, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b, h_b, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨c, h_c, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨d, h_d, rfl⟩ := Finset.mem_image.mp hd
    rcases h a h_a b h_b c h_c d h_d heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  · intro h a ha b hb c hc d hd heq
    rcases h _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
      _ (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
      _ (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
      _ (Finset.mem_image.mpr ⟨d, hd, rfl⟩) heq with hsame | hswap
    · exact Or.inl ⟨emb_injective hsame.1, emb_injective hsame.2⟩
    · exact Or.inr ⟨emb_injective hswap.1, emb_injective hswap.2⟩

/-- Counting sums in the ternary cube gives the diagonal-inclusive bound. -/
theorem IsSidonCube.card_mul_succ_le {n : ℕ} {S : Finset (Fin n → Bool)}
    (h : IsSidonCube S) : S.card * (S.card + 1) ≤ 2 * 3 ^ n := by
  let f : (Fin n → Fin 3) → (Fin n → ℕ) := fun v i => (v i : ℕ)
  let T := (Finset.univ : Finset (Fin n → Fin 3)).image f
  have hf : Function.Injective f := by
    intro a b hab
    funext i
    exact Fin.ext (congrFun hab i)
  have hcard : T.card = 3 ^ n := by
    rw [Finset.card_image_of_injective _ hf]
    simp
  have hT : ∀ a ∈ S.image emb, ∀ b ∈ S.image emb, a + b ∈ T := by
    intro a ha b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hb
    let v : Fin n → Fin 3 := fun i => ⟨emb a i + emb b i, by
      cases ha : a i <;> cases hb : b i <;> simp [emb, ha, hb]⟩
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩
  have hc := ((isSidonCube_iff S).mp h).card_mul_succ_le hT
  rw [Finset.card_image_of_injective _ emb_injective, hcard] at hc
  exact hc

/-- Empty cube subsets witness nonemptiness of the cardinality set. -/
theorem a309370_set_nonempty (n : ℕ) :
    {k : ℕ | ∃ S : Finset (Fin n → Bool), IsSidonCube S ∧ S.card = k}.Nonempty := by
  refine ⟨0, ∅, ?_, rfl⟩
  simp [IsSidonCube]

/-- All cube subset cardinalities are bounded by the finite ambient cube. -/
theorem a309370_bddAbove (n : ℕ) :
    BddAbove {k : ℕ | ∃ S : Finset (Fin n → Bool), IsSidonCube S ∧ S.card = k} := by
  refine ⟨2 ^ n, ?_⟩
  rintro k ⟨S, _, rfl⟩
  have hc := Finset.card_le_card (Finset.subset_univ S)
  simpa using hc

/-- A Sidon subset attains the maximum cardinality. -/
theorem a309370_attained (n : ℕ) :
    ∃ S : Finset (Fin n → Bool), IsSidonCube S ∧ S.card = a309370 n :=
  Nat.sSup_mem (a309370_set_nonempty n) (a309370_bddAbove n)

/-- The maximum obeys the diagonal-inclusive counting bound. -/
theorem a309370_strong_upper (n : ℕ) : a309370 n * (a309370 n + 1) ≤ 2 * 3 ^ n := by
  obtain ⟨S, hS, hcard⟩ := a309370_attained n
  simpa [hcard] using hS.card_mul_succ_le

/-- The original weaker counting bound follows, including at zero. -/
theorem a309370_trivial_upper (n : ℕ) : a309370 n * (a309370 n - 1) ≤ 2 * 3 ^ n := by
  exact (Nat.mul_le_mul_left (a309370 n) (by omega : a309370 n - 1 ≤ a309370 n + 1)).trans
    (a309370_strong_upper n)

/-- Every exhibited cube Sidon set gives a lower bound for the maximum. -/
theorem IsSidonCube.card_le_a309370 {n : ℕ} {S : Finset (Fin n → Bool)}
    (h : IsSidonCube S) : S.card ≤ a309370 n :=
  le_csSup (a309370_bddAbove n) ⟨S, h, rfl⟩

/-- The zero-dimensional cube has one point and its maximum is one. -/
theorem a309370_zero : a309370 0 = 1 := by
  apply Nat.le_antisymm
  · obtain ⟨S, hS, hcard⟩ := a309370_attained 0
    have hbound : ∀ S : Finset (Fin 0 → Bool), S.card ≤ 1 := by decide
    simpa [hcard] using hbound S
  · have hw : IsSidonCube (Finset.univ : Finset (Fin 0 → Bool)) := by decide
    simpa using hw.card_le_a309370

/-- The entire one-dimensional cube is Sidon and has two points. -/
theorem a309370_one : a309370 1 = 2 := by
  apply Nat.le_antisymm
  · obtain ⟨S, hS, hcard⟩ := a309370_attained 1
    have hbound : ∀ S : Finset (Fin 1 → Bool), S.card ≤ 2 := by decide
    simpa [hcard] using hbound S
  · have hw : IsSidonCube (Finset.univ : Finset (Fin 1 → Bool)) := by decide
    simpa using hw.card_le_a309370

/-- The square has a three-point Sidon subset but is not itself Sidon. -/
theorem a309370_two : a309370 2 = 3 := by
  apply Nat.le_antisymm
  · obtain ⟨S, hS, hcard⟩ := a309370_attained 2
    have hbound : ∀ S : Finset (Fin 2 → Bool), IsSidonCube S → S.card ≤ 3 := by
      decide
    simpa [hcard] using hbound S hS
  · have hw : IsSidonCube ({![false, false], ![false, true], ![true, false]} :
        Finset (Fin 2 → Bool)) := by decide
    have hc : ({![false, false], ![false, true], ![true, false]} :
        Finset (Fin 2 → Bool)).card = 3 := by decide
    simpa [hc] using hw.card_le_a309370

/-- A three-dimensional Sidon cube subset has at most five points. -/
theorem IsSidonCube.card_le_five {S : Finset (Fin 3 → Bool)}
    (h : IsSidonCube S) : S.card ≤ 5 := by
  let c : (Fin 3 → Bool) → (Fin 3 → Bool) := fun v i => !(v i)
  have hc : ∀ v, c (c v) = v := by
    intro v
    funext i
    simp [c]
  have hinj : Function.Injective c := by
    intro v w heq
    have heq' := congrArg c heq
    simpa only [hc] using heq'
  have hsum : ∀ v w, emb v + emb (c v) = emb w + emb (c w) := by
    intro v w
    funext i
    change emb v i + emb (c v) i = emb w i + emb (c w) i
    cases hv : v i <;> cases hw : w i <;> simp [emb, c, hv, hw]
  let T : Finset (Fin 3 → Bool) := Finset.univ.filter (fun v => v 0 = false)
  let A := S.filter (fun v => v 0 = false)
  let U := S.filter (fun v => v 0 = true)
  let B := U.image c
  have hT : T.card = 4 := by decide
  have hA : A ⊆ T := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩
  have hB : B ⊆ T := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simp [c, (Finset.mem_filter.mp hw).2]⟩
  have hpartition : A ∪ U = S := by
    ext v
    cases hv : v 0 <;> simp [A, U, hv]
  have hdisjoint : Disjoint A U := by
    apply Finset.disjoint_left.mpr
    intro v ha hu
    have ha0 := (Finset.mem_filter.mp ha).2
    have hu0 := (Finset.mem_filter.mp hu).2
    simp only [ha0, Bool.false_eq_true] at hu0
  have hcard : S.card = A.card + B.card := by
    rw [Finset.card_image_of_injective U hinj]
    rw [← Finset.card_union_of_disjoint hdisjoint, hpartition]
  have hinter : (A ∩ B).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro v hv w hw
    obtain ⟨hva, hvb⟩ := Finset.mem_inter.mp hv
    obtain ⟨hwa, hwb⟩ := Finset.mem_inter.mp hw
    have hvS := (Finset.mem_filter.mp hva).1
    have hwS := (Finset.mem_filter.mp hwa).1
    have hv0 := (Finset.mem_filter.mp hva).2
    have hw0 := (Finset.mem_filter.mp hwa).2
    have hcvS : c v ∈ S := by
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hvb
      simpa only [hc] using (Finset.mem_filter.mp hu).1
    have hcwS : c w ∈ S := by
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hwb
      simpa only [hc] using (Finset.mem_filter.mp hu).1
    rcases h v hvS (c v) hcvS w hwS (c w) hcwS (hsum v w) with hsame | hswap
    · exact hsame.1
    · have hzero := congrFun hswap.1 0
      simp [c, hv0, hw0] at hzero
  have hunion : (A ∪ B).card ≤ 4 := by
    rw [← hT]
    exact Finset.card_le_card (Finset.union_subset hA hB)
  have hid := Finset.card_union_add_card_inter A B
  omega

/-- Five explicit vertices attain the maximum in dimension three. -/
theorem a309370_three : a309370 3 = 5 := by
  let W : Finset (Fin 3 → Bool) :=
    {![false, false, false], ![false, false, true], ![false, true, false],
      ![true, false, false], ![true, true, true]}
  have hw : IsSidonCube W := by decide
  have hc : W.card = 5 := by decide
  apply Nat.le_antisymm
  · obtain ⟨S, hS, hcard⟩ := a309370_attained 3
    simpa [hcard] using hS.card_le_five
  · simpa [hc] using hw.card_le_a309370

end SidonHypercube
