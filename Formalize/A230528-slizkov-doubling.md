seq:     A230528
claim:   slizkov-doubling-gap
status:  open (question)
stmt:    M
proof:   unknown; counterexample-searchable
module:  none (needs AdditionChain layer, see
         A003313-knuth-stolarsky.md)
source:  OEIS A230528 open question, Alexey Slizkov,
         2024-01-20

CLAIM
  A230528 lists k with l(2k) < l(k) (shortest addition
  chain gets SHORTER after doubling; smallest is
  k = 375494703, per entry family). Question: can
  l(2k) < l(k) - 1, i.e. can doubling save more than
  one step? Formalizable as the conjecture
    forall k, l(k) - l(2k) <= 1
  (either to prove or to refute by witness).

LEAN
  Same AdditionChain vocabulary as A003313 file.
  Trivial adjacent lemma for the def's sanity suite:
  l(2k) <= l(k) + 1 (append a doubling).

ROUTE
  No structural route known. Refutation would be an
  explicit chain pair — exactly the project's
  witness-first epistemics; a bounded search program
  is the natural first move (computational side, not
  this file's concern).

EVIDENCE
  Known examples achieve deficit exactly 1; none
  larger found.
