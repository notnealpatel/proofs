import ShearEC.ShearInversionLB

/-!
# secp256k1 primality instance check

This leaf checks that typeclass search supplies the downstream `Fact` instance for the
kernel-checked secp256k1 primality certificate. It does not perform an axiom audit.
-/

set_option autoImplicit false

example : Fact (Nat.Prime ShearEC.ShearInversionLB.secp256k1P) := inferInstance
