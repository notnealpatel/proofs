import Xlib.ShearInversionLB

/-! # Axiom audit: secp256k1 primality certificate

Confirms the kernel-checked Pratt/Lucas certificate is axiom-clean: no
`Lean.ofReduceBool` (i.e. no `native_decide`), no `sorryAx` — only
`propext, Classical.choice, Quot.sound`. Also checks the downstream
instance-carrying theorem in `Xlib.ShearInversionLB`.
-/

#print axioms Xlib.Secp256k1Prime.secp256k1P_prime
#print axioms Xlib.ShearInversionLB.secp256k1P_prime
#print axioms Xlib.ShearInversionLB.secp256k1_inversion_needs_256_shears

-- The `Fact` side condition is discharged by typeclass search alone:
example : Fact (Nat.Prime Xlib.ShearInversionLB.secp256k1P) := inferInstance
