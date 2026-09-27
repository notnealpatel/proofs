import GroupTPP.STPPWreath

/-! Le1 axiom audit: every new declaration of the CU wreath TPP witness section
must depend on exactly `[propext, Classical.choice, Quot.sound]` — no `sorryAx`,
no `Lean.ofReduceBool` (`native_decide`). -/

open GroupTPP.STPPWreath

