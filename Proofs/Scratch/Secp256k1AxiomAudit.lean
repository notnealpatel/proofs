import ShearEC.ShearInversionLB

/-! # Axiom audit: secp256k1 primality certificate

Confirms the kernel-checked Pratt/Lucas certificate is axiom-clean: no
`Lean.ofReduceBool` (i.e. no `native_decide`), no `sorryAx` — only
`propext, Classical.choice, Quot.sound`. Also checks the downstream
instance-carrying theorem in `ShearEC.ShearInversionLB`.
-/


-- The `Fact` side condition is discharged by typeclass search alone:
example : Fact (Nat.Prime ShearEC.ShearInversionLB.secp256k1P) := inferInstance
