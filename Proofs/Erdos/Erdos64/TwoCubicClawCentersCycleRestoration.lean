import Erdos.Erdos64.TwoCubicClawCentersCycleInsertion

set_option autoImplicit false

namespace Erdos64.TwoCubicClawCentersContraction

open SimpleGraph

universe u

/-- Away from the retained contraction root, every contracted edge is an unchanged original edge. -/
theorem adj_of_nonroots {A : Type u} (K : SimpleGraph A) (U V : A)
    {x y : {a : A // a ≠ V}} (hx : x.val ≠ U) (hy : y.val ≠ U)
    (he : (contracted K U V).Adj x y) : K.Adj x.val y.val := by
  rcases he.2 with he | he | he
  · exact he
  · exact (hx he.1).elim
  · exact (hy he.1).elim

/-- An edge into the retained contraction root originates at one of the two old endpoints. -/
theorem adj_into_root {A : Type u} (K : SimpleGraph A) (U V : A)
    {x y : {a : A // a ≠ V}} (hx : x.val ≠ U) (hy : y.val = U)
    (he : (contracted K U V).Adj x y) : K.Adj x.val U ∨ K.Adj x.val V := by
  rcases he.2 with he | he | he
  · exact Or.inl (hy ▸ he)
  · exact (hx he.1).elim
  · exact Or.inr he.2

/-- Restoring a cycle through the contracted root gives one simple cycle: equal
endpoint sides retain one root, while different sides insert the original root edge.
The nonroot predicate holds at exactly the unchanged tail vertices in either case. -/
theorem restore_at_root {A : Type u} (K : SimpleGraph A) (U V : A)
    (hUV : U ≠ V) (hEdge : K.Adj U V)
    (F : A → Prop) [DecidablePred F] (hFU : ¬ F U) (hFV : ¬ F V)
    (hF : ∀ a, a ≠ U → a ≠ V → F a)
    {m : ℕ} (hm : 4 ≤ m + 1) (c : Fin (m + 1) → {a : A // a ≠ V})
    (hc : Function.Injective c)
    (hadj : ∀ i, (contracted K U V).Adj (c i) (c (i + 1)))
    (h0 : (c 0).val = U) :
    ∃ t : ℕ, ∃ d : Fin (t + 1) → A, Function.Injective d ∧
      (∀ i, K.Adj (d i) (d (i + 1))) ∧
      ((t = m ∧ (Finset.univ.filter (fun i => F (d i))).card = m) ∨
       (t = m + 1 ∧ (Finset.univ.filter (fun i => F (d i))).card = m)) := by
  classical
  letI : NeZero m := ⟨by omega⟩
  have htailU (i : Fin (m + 1)) (hi : i ≠ 0) : (c i).val ≠ U := by
    intro he
    exact hi (hc (Subtype.ext (he.trans h0.symm)))
  have htailF (i : Fin (m + 1)) (hi : i ≠ 0) : F (c i).val :=
    hF _ (htailU i hi) (c i).property
  have h10 : (1 : Fin (m + 1)) ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    norm_num [Fin.val_one, Nat.mod_eq_of_lt (show 1 < m + 1 by omega)] at hv
  have hlast0 : (Fin.last m : Fin (m + 1)) ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_last, Fin.val_zero] at hv
    omega
  have hone : (1 : Fin (m + 1)).val = 1 := by
    change 1 % (m + 1) = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hwrap : (Fin.last m + 1 : Fin (m + 1)) = 0 := by
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_last, hone, Fin.val_zero, Nat.mod_self]
  have hin := adj_into_root K U V (htailU (Fin.last m) hlast0) h0
    (show (contracted K U V).Adj (c (Fin.last m)) (c 0) by simpa only [hwrap] using hadj (Fin.last m))
  have hout := adj_into_root K U V (htailU 1 h10) h0
    (show (contracted K U V).Adj (c 1) (c 0) by simpa only [zero_add] using (hadj 0).symm)
  obtain ⟨P, hP, hPin⟩ : ∃ P, (P = U ∨ P = V) ∧ K.Adj (c (Fin.last m)).val P := by
    rcases hin with he | he
    · exact ⟨U, Or.inl rfl, he⟩
    · exact ⟨V, Or.inr rfl, he⟩
  obtain ⟨Q, hQ, hQout⟩ : ∃ Q, (Q = U ∨ Q = V) ∧ K.Adj Q (c 1).val := by
    rcases hout with he | he
    · exact ⟨U, Or.inl rfl, he.symm⟩
    · exact ⟨V, Or.inr rfl, he.symm⟩
  have hFP : ¬ F P := by rcases hP with rfl | rfl; exact hFU; exact hFV
  have hFQ : ¬ F Q := by rcases hQ with rfl | rfl; exact hFU; exact hFV
  have htailP (i : Fin (m + 1)) (hi : i ≠ 0) : P ≠ (c i).val := by
    rcases hP with rfl | rfl
    · exact (htailU i hi).symm
    · exact (c i).property.symm
  have htailQ (i : Fin (m + 1)) (hi : i ≠ 0) : Q ≠ (c i).val := by
    rcases hQ with rfl | rfl
    · exact (htailU i hi).symm
    · exact (c i).property.symm
  let d : Fin (m + 1) → A := fun i => if i = 0 then Q else (c i).val
  have hd0 : d 0 = Q := by simp [d]
  have hdtail (i : Fin (m + 1)) (hi : i ≠ 0) : d i = (c i).val := by simp [d, hi]
  have hdinj : Function.Injective d := by
    intro i j he
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · exact hi.trans hj.symm
    · exact (htailQ j hj (by simpa only [hi, hd0, hdtail j hj] using he)).elim
    · exact (htailQ i hi (by simpa only [hj, hd0, hdtail i hi] using he.symm)).elim
    · exact hc (Subtype.ext (by simpa only [hdtail i hi, hdtail j hj] using he))
  have hdcard : (Finset.univ.filter (fun i => F (d i))).card = m := by
    rw [Fin.card_filter_univ_succ]
    have hn0 : ¬ F (d 0) := hd0.symm ▸ hFQ
    have hs (i : Fin m) : F (d i.succ) := by
      rw [hdtail i.succ (Fin.succ_ne_zero i)]
      exact htailF i.succ (Fin.succ_ne_zero i)
    simp [hn0, hs]
  by_cases hPQ : P = Q
  · have hdadj (i : Fin (m + 1)) : K.Adj (d i) (d (i + 1)) := by
      by_cases hi : i = 0
      · subst i
        simpa only [zero_add, hd0, hdtail 1 h10] using hQout
      · by_cases hn : i + 1 = 0
        · have hiLast : i = Fin.last m := by
            apply Fin.ext
            have hv := congrArg Fin.val hn
            simp only [Fin.val_add, hone, Fin.val_zero] at hv
            by_cases hb : i.val + 1 < m + 1
            · rw [Nat.mod_eq_of_lt hb] at hv
              omega
            · simp only [Fin.val_last]
              omega
          simpa only [hiLast, hwrap, hdtail (Fin.last m) hlast0, hd0, hPQ] using hPin
        · rw [hdtail i hi, hdtail (i + 1) hn]
          exact adj_of_nonroots K U V (htailU i hi) (htailU (i + 1) hn) (hadj i)
    exact ⟨m, d, hdinj, hdadj, Or.inl ⟨rfl, hdcard⟩⟩
  · have hKPQ : K.Adj P Q := by
      rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl
      · exact (hPQ rfl).elim
      · exact hEdge
      · exact hEdge.symm
      · exact (hPQ rfl).elim
    have hfresh (i : Fin (m + 1)) : P ≠ d i := by
      by_cases hi : i = 0
      · simpa only [hi, hd0] using hPQ
      · simpa only [hdtail i hi] using htailP i hi
    have hmid (i : Fin m) : K.Adj (d i.castSucc) (d i.succ) := by
      by_cases hi : i = 0
      · subst i
        have he1 : (0 : Fin m).succ = (1 : Fin (m + 1)) := by
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_zero, hone]
        simpa only [Fin.castSucc_zero, he1, hd0, hdtail 1 h10] using hQout
      · have hic : i.castSucc ≠ 0 := by
          intro he
          apply hi
          apply Fin.ext
          simpa only [Fin.val_castSucc, Fin.val_zero] using congrArg Fin.val he
        have he : (i.castSucc + 1 : Fin (m + 1)) = i.succ := by
          apply Fin.ext
          simp only [Fin.val_add, Fin.val_castSucc, hone, Fin.val_succ,
            Nat.mod_eq_of_lt (show i.val + 1 < m + 1 by omega)]
        rw [hdtail i.castSucc hic, hdtail i.succ (Fin.succ_ne_zero i)]
        exact adj_of_nonroots K U V (htailU i.castSucc hic) (htailU i.succ (Fin.succ_ne_zero i))
          (show (contracted K U V).Adj (c i.castSucc) (c i.succ) by simpa only [he] using hadj i.castSucc)
    let e : Fin (m + 2) → A := Fin.cons P d
    have hecard : (Finset.univ.filter (fun i => F (e i))).card = m := by
      rw [Fin.card_filter_univ_succ]
      simpa only [e, Fin.cons_zero, hFP, if_false, Fin.cons_succ] using hdcard
    refine ⟨m + 1, e, cons_injective P d hdinj hfresh, ?_, Or.inr ⟨rfl, hecard⟩⟩
    exact cons_cyclic_adj K P d (by simpa only [hd0] using hKPQ) hmid
      (by simpa only [hdtail (Fin.last m) hlast0] using hPin)

end Erdos64.TwoCubicClawCentersContraction
