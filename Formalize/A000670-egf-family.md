seq:     A000670
claim:   bala-egf-family-periodicity
status:  coefficient theorem proved; formal-series composition bridge pending
stmt:    L (original estimate; remaining bridge not yet implemented)
proof:   hard (original estimate); coefficient theorem complete;
         remaining composition bridge difficulty not reassessed
module:  Proofs/Enumerative/OrdinaryIntegralEGF.lean,
         Proofs/Enumerative/FubiniMod.lean
source:  OEIS A000670 comment, Peter Bala, 2022-07-08

EXACT SCOPE
  Let G(X) = sum a_m X^m with arbitrary ordinary integer coefficients
  a_m. Over rational formal power series put F(X) = G(exp(X) - 1),
  and b_n = n! * [X^n] F(X). The claim is that b_n are integers and,
  for every k >= 1, are eventually periodic modulo k with period
  dividing phi(k). It suffices to establish phi(k) as an eventual period.
  No analytic convergence, finite support, or positivity is assumed.

PROVED PREREQUISITE
  OrdinaryIntegralEGF.weightedStirlingTransform a n is the integer
    sum_{m=0}^n a_m * m! * StirlingS2(n,m).
  weightedStirlingTransform_eventuallyPeriodic proves that this sequence
  has eventual period phi(k) modulo every positive k. The finite
  alternating-power identity for m! * StirlingS2(n,m) is also proved.
  The Fubini specialization a_m = 1 is already covered by FubiniMod.

REMAINING BRIDGE
  Use genuine rational formal-series exponentiation and substitution to
  identify n! * [X^n] G(exp(X)-1) with the weighted Stirling transform.
  The inner series has zero constant coefficient, so every coefficient
  uses only finitely many outer coefficients. Prove the identity also
  at n=0, then transfer integrality and the existing periodicity theorem.
  The bridge is not supplied merely by naming the transform an EGF.

CORRECTION AND EVIDENCE
  Bala's source explicitly requires an integral power series G.
  G(X)=1/(1-X) gives Fubini numbers. The old card's Bell example
  G(X)=exp(X) is OUTSIDE this scope: its ordinary coefficient of X^2
  is 1/2. Integral divided-power coefficients are a different condition;
  the unrestricted divided-power version is not admitted. Touchard's
  Bell congruences are not a proof or instance of the stated generality.
  The original source also points to A002050 and A354242. Its conjectural
  wording is source history, not the current status of the proved
  weighted-coefficient theorem.
