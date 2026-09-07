# A391599 — intersecting-family lower bounds

- **Mathematical status:** the source's former `3n+O(1)` premise is refuted; the classical and improved lower bounds are known theorems.
- **Work status:** unstarted for the substantive lower-bound mathematics.
- **Remaining target:** formalize the Erdős–Lovász lower bound (and ultimately Sivashankar's improvement) for the minimum size of the relevant maximal intersecting uniform family.
- **Existing formal progress:** `Proofs/Erdos/ErdosLovasz.lean` defines the covering-number formulation, and `erdosLovaszNum_four_le` proves `g(4) ≤ 9` from Tripathi's explicit nine-edge witness. The equality `g(4)=9`, Barát's `g(5)=13` and `g(6)≤18`, and the general Erdős–Lovász/Sivashankar bounds remain archived with `sorry`.
- **Existing correction:** the file also records the obsolete `3n+O(1)` asymptotic as a proposition and proves it incompatible with Sivashankar's theorem. Sivashankar gives `g(r)≥((41-√19)/12-ε)r`, whose coefficient is about `3.0534`, so `g(r)-3r→∞`.
- **Next obligation:** prove the lower bound `9 ≤ g(4)` or formalize one of the general lower-bound arguments, without consuming an archived `sorry`. Recording the asymptotic refutation and the proved upper witness is not a proof of those lower bounds.
- **Attribution:** the `g(5)=13` and `g(6)≤18` results are by J. Barát alone, not Barát–Wanless.
