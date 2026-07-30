/-
  LANE HALTED (2026-07-29, quota stop) — stub only, no content written.

  Card: Formalize/A083207-ianakiev-tau-sigma.md. E4 release lane: the
  card's tau-sigma claims, attacked via the coprime closure engine.
  Writer was dispatched and killed minutes in (card-reading stage);
  nothing beyond this stub exists.

  Ready for re-dispatch: the shared def layer Enumerative.IsZumkeller is
  in-tree, fully reviewed, sorry-free. Engine signature (post-review,
  positivity hypotheses dropped as derivable):
    IsZumkeller.mul_of_coprime : IsZumkeller m → m.Coprime n → IsZumkeller (m * n)
    IsZumkeller.coprime_mul_left : IsZumkeller n → m.Coprime n → IsZumkeller (m * n)
  plus the half-σ characterisation isZumkeller_iff_two_mul_sum_eq_sum_divisors.
-/
import Mathlib

set_option autoImplicit false
