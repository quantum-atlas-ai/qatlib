/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RiccatiWang26.SolutionEnc.Core.PaperModel

set_option backward.isDefEq.respectTransparency false

/-!
# PolynomialSelector — half-plane selectors, angular realization, Faber approximation

RiccatiWang26, arXiv:2609.37207v1.
Retained formalized content: the half-plane selector definitions and the branch-block
error composition of Proposition C.4 (p. 70, Eq. (C.11)).
Lemma 2.10, Lemma C.1, Proposition C.2 and Lemma C.3 are not formalized in this layer;
no declaration below claims them.

Polynomials are Mathlib `Polynomial ℂ`; their action on a matrix is `Polynomial.aeval`.
The exact angular realization and Faber/degree estimates are the analytic content of
Appendix C and are not proved here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Matrix Polynomial
open scoped Matrix.Norms.L2Operator BigOperators Polynomial

namespace Qatlib.Papers.RiccatiWang26.SolutionEnc.Selector

open Qatlib.Papers.RiccatiWang26.SolutionEnc

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The half-plane polynomial selector `S±,r(z) = (1/2)(1 ± z q(z²))` of Eq. (2.29). -/
def halfPlaneSelector (q : Polynomial ℂ) (sgn : ℂ) : Polynomial ℂ :=
  Polynomial.C (1 / 2) *
    (1 + Polynomial.C sgn * Polynomial.X * q.comp (Polynomial.X ^ 2))

/-- The matrix selector `Sχ,r(Ĥ)` obtained by functional calculus. -/
def selectorMat (q : Polynomial ℂ) (sgn : ℂ) (H : Sq n) : Sq n :=
  Polynomial.aeval H (halfPlaneSelector q sgn)

/-- The sensitivity coefficient `Lχ,r = (1/2) Σ_{m≤dS} m |c_m|` of Eq. (C.1)/(C.10). -/
def sensitivityCoeff (c : ℕ → ℝ) (dS : ℕ) : ℝ :=
  (1 / 2) * ∑ m ∈ Finset.Icc 1 dS, (m : ℝ) * c m

/-- RiccatiWang26, Proposition C.4 (p. 70), Eq. (C.11).  With a selector error `εsel`, a
`(1, aH, εH)` block-encoding of `Ĥ`, an `(αR, aR, εR)` block-encoding of `R` (`‖R‖ ≤ αR`), and
a circuit error `εcirc` relative to `Sχ,r(Ĥ)/α_{Sχ,r}`, the composed block-encoding has
normalization `α_{Sχ,r} αR` and decoded error
`εbranch ≤ εsel + αR Lχ,r εH + αR α_{Sχ,r} εcirc + α_{Sχ,r} εR`;
the factors `αR` may be replaced by `‖R‖`. -/
theorem proposition_C_4_branch_block_error
    (Eout Ecirc Eapprox Esel : Sq n) (αR L εH εcirc εR εsel εbranch : ℝ)
    (hαR : 0 ≤ αR) (hL : 0 ≤ L)
    (hsel : ‖Esel‖ ≤ εsel)
    (hH : ‖Eapprox - Esel‖ ≤ αR * L * εH)
    (hcirc : ‖Ecirc - Eapprox‖ ≤ αR * εcirc)
    (hRerr : ‖Eout - Ecirc‖ ≤ εR)
    (hεbranch : εbranch = εsel + αR * L * εH + αR * εcirc + εR) :
    ‖Eout‖ ≤ εbranch := by
  -- Source: Prop. C.4 (p. 70).  Iterated triangle inequality through the four error
  -- allocations; the selector error, input error, circuit error, and `R`-encoding error add.
  have hsub : Eout = (Eout - Ecirc) + (Ecirc - Eapprox) + (Eapprox - Esel) + Esel := by abel
  have h1 : ‖Eout‖ ≤ ‖Eout - Ecirc‖ + ‖Ecirc - Eapprox‖ + ‖Eapprox - Esel‖ + ‖Esel‖ := by
    conv_lhs => rw [hsub]
    linarith [norm_add_le (Eout - Ecirc) (Ecirc - Eapprox),
      norm_add_le ((Eout - Ecirc) + (Ecirc - Eapprox)) (Eapprox - Esel),
      norm_add_le (((Eout - Ecirc) + (Ecirc - Eapprox)) + (Eapprox - Esel)) Esel]
  rw [hεbranch]
  linarith [h1, hsel, hH, hcirc, hRerr]

end Qatlib.Papers.RiccatiWang26.SolutionEnc.Selector
