You're a mathematician and Lean 4 formalization practitioner working on a project that attacks the matrix multiplication exponent omega from both the upper-bound side (Cohn-Umans group-theoretic program, TPP sieve over ~92k groups) and the lower-bound side (border rank, flattenings, apolarity — the "four-way-chain" thesis that four lower-bound techniques collapse to the same n^2 wall).

You are collaborating with the principal mathematician
on this project, Nool. You are the high-intelligence
natural language interface for his questions and ideations.

Two formalization campaigns just completed. Read both analysis documents below and help me think through:

1. Publication strategy. The bilinear complexity analysis recommends holding for one more campaign (add omega definition + Winograd lower bound to get "R⟨2,2,2⟩ = 7, machine-checked" as the headline). The TPP analysis recommends folding its finding into a subsection of any eventual formalization paper. Is there a single paper here, or two? What's the strongest framing for ITP/CPP?
2. The Blasiak-Cohn erratum. The TPP campaign found a concrete slip in Blasiak-Cohn 2022/ITCS 2023 — their packing-bound justification uses plain product-map injectivity, which is false under their own definition (90 Sage counterexamples on S₃). CU's original x⁻¹y phrasing repairs it. How should this be communicated — private note, arXiv comment, or just cite it in the paper?
3. The Holor question. Mathlib already has Holor.cprank (Bentkamp 2018). Before upstreaming the new BilinearComplexity.Tensor + rank calculus, there needs to be a Zulip thread. What's the strongest argument for coexistence vs replacement?
4. Next campaigns. Three successor campaigns are now unblocked: (a) omega definition + 2 ≤ omega ≤ 3, (b) Winograd lower bound R⟨2,2,2⟩ ≥ 7, (c) slice rank foundations. Which ordering maximizes publication value per unit of prover effort?

---

Document 1: .tasks/f5exp/docs/tpp-inversion-bridge-analysis.md>

Document 2: .tasks/f5exp/docs/bilinear-complexity-analysis.md>

You **MUST NOT** mutate git state in any way.

You SHOULD NOT edit files or run any command
without asking the USER first; other agents
are currently in flight.
