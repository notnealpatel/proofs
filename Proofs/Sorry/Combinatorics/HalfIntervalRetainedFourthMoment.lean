import Combinatorics.RetainedMoment

/-!
# Original half-interval retained fourth moment: remaining formalization

Provenance: `Plans/HalfIntervalRetainedFourthMoment.md` at revision
`8541812f37e99d0dae8f6bc3490d43aa56d7cc1c`. The corrected source argument has
been assessed in prose; this module archives its exact finite-field target,
not a completed Lean theorem or a novelty claim. It deliberately imports only the completed conditional consumer.

For every odd prime p and integer 1 ≤ q ≤ p, put h = (p - 1)/2,
C = {0,…,h} ⊂ ZMod p, m = (p + 1)/2, and ρ = m/p. For nonzero a and arbitrary
b in ZMod p define Y_a(b) = ∑_{0 ≤ j < q} 1_C(aj+b), f_a(b) = Y_a(b) - ρq,
S(a) = (1/p)∑_b |f_a(b)|², and F4(a) = (1/p)∑_b |f_a(b)|⁴.
Let avgS = (1/(p-1))∑_{a≠0} S(a), R = {a ≠ 0 : S(a) ≤ 2 avgS}, and
H_h = ∑_{r=1}^h 1/r. The exact target is

* avgS = m(p-m)q(p-q)/(p²(p-1)) = (p+1)q(p-q)/(4p²);
* |R| ≥ (p-1)/2 > 0 (indeed |R| > (p-1)/2 when q < p);
* (1/|R|)∑_{a∈R} F4(a) ≤ q² H_h² ≤ q²(1 + log h)².

These bounds concern only this original half-interval and the retained mean:
not an arbitrary C, a pointwise bound, a selected minimum, an enlarged interval,
or Erdős #711. At q=p, f=S=F4=0 and all nonzero directions are retained.
At q=1 all are retained and F4 = ρ(1-ρ)⁴ + (1-ρ)ρ⁴. Thus neither endpoint is
excluded, and nonemptiness at q=p must not be proved by division by avgS.

The established informal proof counts distinct affine pairs for the variance
identity and applies the full variance filter. With e_p(t)=exp(2πit/p), set
hat1C(k)=(1/p)∑_x 1_C(x)e_p(-kx) and D_q(t)=∑_{j<q}e_p(tj).
Normalized Fourier inversion gives f_a(b)=∑_{k≠0}hat1C(k)D_q(ak)e_p(kb).
For signed representatives 1 ≤ |k| ≤ h, the geometric-sum/sine estimate is
|hat1C(k)| ≤ 1/(2|k|), whence L=∑_{k≠0}|hat1C(k)| ≤ H_h ≤ 1+log h.
Orthogonality gives ∑_{a≠0}|D_q(ak)|²=q(p-q) for each nonzero k.
Finally B_a=∑_{k≠0}|hat1C(k)||D_q(ak)| bounds the supremum norm, and
F4(a) ≤ S(a) B_a² ≤ 2 avgS B_a² on R.

Already done in Lean: `RetainedMoment.retained_fourth_mean_le` consumes these
last two inequalities with D the nonzero directions, modes K the nonzero
frequencies, c_k=|hat1C(k)|, d(a,k)=|D_q(ak)|, T=q(p-q), and s=2 avgS.
Its conclusion is mean_R F4 ≤ (s T/|R|) L². The per-mode retained energy mean
and the weighted Cauchy–Schwarz/sum-interchange step are also kernel-checked
in that production module. Its `half_interval_fourth_mean_le` additionally
consumes p ≥ 3, 1 ≤ q ≤ p, |R| ≥ (p-1)/2, and L ≤ H to conclude mean_R F4 ≤ q² H²;
the half-interval application sets H=H_h. Keeping the full S filter plus conditional L²
removes the old extra q^(1/2) loss; the withdrawn claim that a coupled
four-frequency estimate was necessary is not a dependency.

What remains, and why: the concrete ZMod/complex-character implementation
and its bridges are not yet supplied. Formal obligations are the affine-pair
variance identity; retention cardinality and the separate zero-variance case;
character orthogonality and nonzero-mode energy; normalized Fourier inversion
and the supremum-norm/variance fourth-moment inequality; the signed-frequency
interval geometric/sine estimate; and harmonic integral comparison. These
are infrastructure gaps in formalizing the audited argument, not unresolved
mathematical conjectures. No assumption here asserts the final moment bound,
and production never imports this archive.
-/

set_option autoImplicit false
