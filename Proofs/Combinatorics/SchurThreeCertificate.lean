import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.Basic
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace SchurNumbers

private def badLatest (p : List (Fin 3)) : Prop :=
  ∃ x ∈ Finset.Icc 1 (p.length / 2),
    p[x - 1]? = p[p.length - x - 1]? ∧ p[x - 1]? = p[p.length - 1]?

private def latestB (p : List (Fin 3)) : Bool :=
  (List.range (p.length / 2)).any fun i =>
    (p[i]? == p[p.length - (i + 1) - 1]?) && (p[i]? == p[p.length - 1]?)

example : latestB ([0, 0] : List (Fin 3)) = true := rfl
example : latestB ([0] : List (Fin 3)) = false := rfl

private theorem latestB_iff (p : List (Fin 3)) : latestB p = true ↔ badLatest p := by
  simp only [latestB, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    beq_iff_eq, badLatest, Finset.mem_Icc]
  constructor
  · rintro ⟨i, hi, heq₁, heq₂⟩
    refine ⟨i + 1, ⟨by omega, by omega⟩, ?_, ?_⟩
    · simpa using heq₁
    · simpa using heq₂
  · rintro ⟨x, ⟨hx₁, hx₂⟩, heq₁, heq₂⟩
    refine ⟨x - 1, by omega, ?_, ?_⟩
    · simpa only [Nat.sub_add_cancel hx₁] using heq₁
    · exact heq₂

private def Dead : Nat → List (Fin 3) → Prop
  | 0, _ => False
  | fuel + 1, p => ∀ a : Fin 3, badLatest (p ++ [a]) ∨ Dead fuel (p ++ [a])

private def deadB : Nat → List (Fin 3) → Bool
  | 0, _ => false
  | fuel + 1, p => (List.finRange 3).all fun a =>
      if latestB (p ++ [a]) then true else deadB fuel (p ++ [a])

example : deadB 0 [] = false := rfl
example : ¬ Dead 0 [] := fun h => h

private theorem deadB_iff (fuel : Nat) (p : List (Fin 3)) :
    deadB fuel p = true ↔ Dead fuel p := by
  induction fuel generalizing p with
  | zero => simp [deadB, Dead]
  | succ fuel ih =>
    simp only [deadB, Dead, List.all_eq_true]
    constructor
    · intro hb a
      have ha := hb a (List.mem_finRange a)
      by_cases hl : latestB (p ++ [a]) = true
      · exact Or.inl ((latestB_iff _).mp hl)
      · exact Or.inr ((ih _).mp (by simpa [hl] using ha))
    · intro hd a _
      rcases hd a with hl | hr
      · simp [(latestB_iff _).mpr hl]
      · have hb := (ih _).mpr hr
        simp [hb]

private def Matches (p : List (Fin 3)) (c : Nat → Fin 3) : Prop :=
  ∀ i, i < p.length → p[i]? = some (c (i + 1))

example : Matches [] (fun _ => 0) := by simp [Matches]
example : Matches [0] (fun _ => 0) := by
  intro i hi
  have hi₀ : i = 0 := by simpa using hi
  subst i
  rfl

private theorem matches_append (p : List (Fin 3)) (c : Nat → Fin 3)
    (hm : Matches p c) : Matches (p ++ [c (p.length + 1)]) c := by
  intro i hi
  by_cases hlt : i < p.length
  · rw [List.getElem?_append_left hlt]
    exact hm i hlt
  · have heq : i = p.length := by simp only [List.length_append, List.length_singleton] at hi; omega
    subst i
    rw [List.getElem?_append_right (Nat.le_refl _)]
    simp

private theorem badLatest_false (p : List (Fin 3)) (c : Nat → Fin 3)
    (hm : Matches p c) (hlen : p.length ≤ 14)
    (h : ∀ x y : Nat, 1 ≤ x → 1 ≤ y → x + y ≤ 14 →
      c x = c y → c y ≠ c (x + y)) (hb : badLatest p) : False := by
  rcases hb with ⟨x, hx, heq₁, heq₂⟩
  rcases Finset.mem_Icc.mp hx with ⟨hx₁, hx₂⟩
  let y := p.length - x
  have hy₁ : 1 ≤ y := by dsimp [y]; omega
  have hsum : x + y = p.length := by dsimp [y]; omega
  have hxi : x - 1 < p.length := by omega
  have hyi : y - 1 < p.length := by omega
  have hli : p.length - 1 < p.length := by omega
  have hcx : p[x - 1]? = some (c x) := by
    simpa only [Nat.sub_add_cancel hx₁] using hm (x - 1) hxi
  have hcy : p[p.length - x - 1]? = some (c y) := by
    simpa only [Nat.sub_add_cancel hy₁] using hm (y - 1) hyi
  have hcl : p[p.length - 1]? = some (c p.length) := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ p.length by omega)] using hm (p.length - 1) hli
  rw [hcx, hcy] at heq₁
  rw [hcx, hcl] at heq₂
  have hcxy : c x = c y := Option.some.inj heq₁
  have hcxl : c x = c p.length := Option.some.inj heq₂
  have hcyl : c y = c (x + y) := by rw [hsum, ← hcxy]; exact hcxl
  exact h x y hx₁ hy₁ (by omega) hcxy hcyl

private theorem dead_false (fuel : Nat) (p : List (Fin 3)) (c : Nat → Fin 3)
    (hm : Matches p c) (hlen : p.length + fuel ≤ 14)
    (h : ∀ x y : Nat, 1 ≤ x → 1 ≤ y → x + y ≤ 14 →
      c x = c y → c y ≠ c (x + y)) (hd : Dead fuel p) : False := by
  induction fuel generalizing p with
  | zero => exact hd
  | succ fuel ih =>
    let p' := p ++ [c (p.length + 1)]
    have hm' : Matches p' c := matches_append p c hm
    have hlen' : p'.length + fuel ≤ 14 := by
      dsimp [p']
      simp only [List.length_append, List.length_singleton]
      omega
    rcases hd (c (p.length + 1)) with hb | hr
    · exact badLatest_false p' c hm' (by omega) h hb
    · exact ih p' hm' hlen' hr

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem booleanCertificate : deadB 14 [] = true := by decide

/-- There is no three-coloring of the positive integers through fourteen
without a monochromatic sum `x + y`, including the case `x = y`. -/
theorem no_three_coloring (c : ℕ → Fin 3)
    (h : ∀ x y : ℕ, 1 ≤ x → 1 ≤ y → x + y ≤ 14 →
      c x = c y → c y ≠ c (x + y)) : False := by
  have hm : Matches [] c := by simp [Matches]
  have hd : Dead 14 [] := (deadB_iff 14 []).mp booleanCertificate
  exact dead_false 14 [] c hm (by decide) h hd

end SchurNumbers
