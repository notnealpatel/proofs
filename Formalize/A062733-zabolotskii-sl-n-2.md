seq:     A062733
claim:   zabolotskii-closed-form
status:  refuted mathematically; formal counterexample pending
stmt:    M
proof:   L (representation-theory bridge)
module:  Proofs/GroupTPP/CharDegrees.lean,
         Proofs/GroupTPP/Wedderburn.lean (machinery)
source:  OEIS A062733 formula, Andrei Zabolotskii, 2025-05-27;
         Jordan decomposition background: arXiv:1808.07116, section 4

HISTORICAL CLAIM (NOT AN ASSUMPTION)
  a(n) is the maximal degree of a complex irreducible representation
  of SL(n,2) = GL(n,2). The source proposes, for n > 3,
    D_n = 2^((n-2)(n-3)/2) * (2^n - 1) * (2^(n-1) - 1) / 3,
  from apparent agreement with |column k=2 of A135950|.
  The listed OEIS terms and that agreement do not certify a maximum.

REFUTATION
  For n >= 8, a semisimple parameter with centralizer
    GL(n-4,2) x GL(2,4)
  and the Steinberg characters of both factors yields, by the standard
  Jordan character-degree correspondence, an irreducible degree
    E_n = 2^((n-4)(n-5)/2 + 2)
          * product_{j=n-3}^n (2^j - 1) / 45.
  In particular E_8 = 359810304 > D_8 = 353730560, with ratio 651/640.
  Thus the proposed universal maximum equality is false. This is a
  source-based mathematical argument, independently reviewed, NOT a
  Lean-checked counterexample or identification of the true maximum.
  No theorem asserting the refuted equality may be admitted.

REMAINING TARGET
  Formalize the n=8 character-degree witness and resulting strict lower
  bound, or the family a(n) >= E_n for n >= 8. Existing CharDegrees and
  Wedderburn infrastructure does not supply Jordan/Green parametrization,
  semisimple centralizers, Steinberg degrees, or their charDegrees bridge.
  The historical n=3 degree-8 example is distinct from this refutation;
  neither its formalization nor a novelty claim is established here.
