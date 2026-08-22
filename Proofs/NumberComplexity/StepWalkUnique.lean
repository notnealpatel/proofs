import NumberComplexity.StepWalk

set_option autoImplicit false

open NumberComplexity

example : decisionPosition
    [WalkDecision.keep, WalkDecision.double, WalkDecision.keep] = 6 := rfl

example : Reach 4 6 2 :=
  reach_decisionWord [WalkDecision.keep, WalkDecision.double, WalkDecision.keep]

example : ∃! w : List WalkDecision,
    decisionPosition w = 6 ∧
      IsLeast {j : ℕ | Reachable 6 j} (w.length + 1) :=
  existsUnique_shortest_decisionWord 6 (by norm_num)

#print axioms NumberComplexity.existsUnique_shortest_decisionWord
