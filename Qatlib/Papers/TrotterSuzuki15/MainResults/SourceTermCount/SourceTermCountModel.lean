/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterSourceBounds

set_option backward.isDefEq.respectTransparency false

/-!
# SourceTermCountModel — term-count vocabulary for arXiv:1512.03416v1

Fixed paper version: arXiv:1512.03416v1 (R. D. Somma, "A Trotter–Suzuki
approximation for Lie groups with applications to Hamiltonian simulation",
10 December 2015).

This module only records the paper's own scalar bookkeeping for the number of
exponentials, so that the claim files can state the paper's bounds verbatim:

* `N_p = 2 L 5^{p-1}` — the number of exponentials in a recursively built
  block of order `2p` (p. 2, text just below Eq. (4));
* Eq. (14) (p. 3) — the segment count
  `r = ⌈5^{p+2} L^{1+1/p} β y^{1/(2p)} t^{1+1/(2p)} / ε^{1/(2p)}⌉`,
  obtained in the proof by solving `r ε_{2p}(t/r) ≤ ε`;
* `N = r N_p` (p. 3) — the total number of exponentials of the product `W`;
* Eq. (5) (p. 2) and Eq. (17) (p. 4) — the two asymptotic bound shapes
  `5^{2p} L^{2+1/p} β y^{1/(2p)} t^{1+1/(2p)} / ε^{1/(2p)}` and
  `5^{3p} (m′)^{q/(4p)+q/4-1/2} t^{1+1/(2p)} / ε^{1/(2p)}`.

These are definitions only; every inequality used by the paper is proved in the
sibling claim files (`TermCountBound`, `QHOTermCount`, `CoupledQHOTermCount`,
`AnharmonicTermCount`).  The paper's asymptotic `O(·)` is formalised as a bound
with an explicit constant, since Lean's `IsBigO` is not needed for a bound of
this shape and the paper itself derives the explicit `r` of Eq. (14).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TrotterSuzuki15.MainResults.SourceTermCount

/-- `N_p = 2 L 5^{p-1}` (arXiv:1512.03416v1, p. 2, below Eq. (4)): the number of
exponentials in one recursively built Suzuki block of order `2p`, where `L` is
the number of summands `ĥ_k` of `X`. -/
noncomputable def sourceMacroCount (L : ℝ) (p : ℕ) : ℝ :=
  2 * L * (5 : ℝ) ^ (p - 1)

/-- The real (pre-ceiling) segment count of Eq. (14) (arXiv:1512.03416v1, p. 3):
`5^{p+2} L^{1+1/p} β y^{1/(2p)} t^{1+1/(2p)} / ε^{1/(2p)}`. -/
noncomputable def sourceSegmentReal (p : ℕ) (L β y t ε : ℝ) : ℝ :=
  (5 : ℝ) ^ (p + 2) * L ^ (1 + 1 / (p : ℝ)) * β *
      y ^ (1 / (2 * (p : ℝ))) * t ^ (1 + 1 / (2 * (p : ℝ))) /
    ε ^ (1 / (2 * (p : ℝ)))

/-- Eq. (14) (arXiv:1512.03416v1, p. 3): the number of segments
`r = ⌈5^{p+2} L^{1+1/p} β y^{1/(2p)} t^{1+1/(2p)} / ε^{1/(2p)}⌉`. -/
noncomputable def sourceSegments (p : ℕ) (L β y t ε : ℝ) : ℕ :=
  Nat.ceil (sourceSegmentReal p L β y t ε)

/-- `N = r N_p` (arXiv:1512.03416v1, p. 3): the total number of exponentials in
the product `W` obtained by splitting `t` into `r` segments. -/
noncomputable def sourceNumTerms (p : ℕ) (L β y t ε : ℝ) : ℝ :=
  (sourceSegments p L β y t ε : ℝ) * sourceMacroCount L p

/-- Eq. (5) (arXiv:1512.03416v1, p. 2): the bound shape
`5^{2p} L^{2+1/p} β y^{1/(2p)} t^{1+1/(2p)} / ε^{1/(2p)}`. -/
noncomputable def eq5Bound (p : ℕ) (L β y t ε : ℝ) : ℝ :=
  (5 : ℝ) ^ (2 * p) * L ^ (2 + 1 / (p : ℝ)) * β *
      y ^ (1 / (2 * (p : ℝ))) * t ^ (1 + 1 / (2 * (p : ℝ))) /
    ε ^ (1 / (2 * (p : ℝ)))

/-- Eq. (17) (arXiv:1512.03416v1, p. 4): the bound shape for `H = (p̂²+x̂^q)/2`,
`5^{3p} (m′)^{q/(4p)+q/4-1/2} t^{1+1/(2p)} / ε^{1/(2p)}`. -/
noncomputable def eq17Bound (p q : ℕ) (m' t ε : ℝ) : ℝ :=
  (5 : ℝ) ^ (3 * p) * m' ^ ((q : ℝ) / (4 * (p : ℝ)) + (q : ℝ) / 4 - 1 / 2) *
      t ^ (1 + 1 / (2 * (p : ℝ))) / ε ^ (1 / (2 * (p : ℝ)))

/-- The majorant Eq. (16) of the anharmonic error (arXiv:1512.03416v1, p. 4):
`Σ_{j=2p}^∞ (c λ N_p²)^{j+1} (m′)^{j(q-2)/4+q/2}`.  Terms with `j < 2p` are
set to zero; the infinite sum is `tsum` (the paper assumes it converges for
`2 ≤ q ≤ 6`). -/
noncomputable def anharmonicErrorBound (p q : ℕ) (c lam Np m' : ℝ) : ℝ :=
  ∑' j : ℕ,
    if j < 2 * p then 0
    else (c * lam * Np ^ 2) ^ (j + 1) * m' ^ ((j : ℝ) * ((q : ℝ) - 2) / 4 + (q : ℝ) / 2)

/-- The optimal order for the single QHO (arXiv:1512.03416v1, p. 4).  The exact
minimiser of the Eq. (15) shape `5^{2p}·exp(z/(2p))`, `z = log(m′t/ε)`, is
`p = ½√(z/log 5)` (setting the derivative `2 log 5 = z/(2p²)` to zero); the
paper quotes `p ≈ √(log(m′t/ε)/log 5)`, a constant factor `2` away, which gives
the same (subpolynomial) conclusion.  We use the exact minimiser so that the
resulting exponent `2√(z·log 5)` is correct. -/
noncomputable def qhoOptimalOrder (m' t ε : ℝ) : ℕ :=
  max 1 (Nat.ceil (Real.sqrt (Real.log (m' * t / ε) / Real.log 5) / 2))

/-- The optimal order for `M` coupled QHOs (arXiv:1512.03416v1, p. 4): the exact
minimiser `p = ½√(log(m′Mt/ε)/log 5)` of the Eq. (5) shape; the paper quotes
`p ≈ √(log(m′Mt/ε)/log 5)`. -/
noncomputable def coupledQHOOptimalOrder (M m' t ε : ℝ) : ℕ :=
  max 1 (Nat.ceil (Real.sqrt (Real.log (m' * M * t / ε) / Real.log 5) / 2))

end Qatlib.Papers.TrotterSuzuki15.MainResults.SourceTermCount
