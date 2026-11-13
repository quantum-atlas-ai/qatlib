/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopyDrivenPhaseReadout
import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

/-!
# Good phase labels for self-tomography

This module defines the good QPE labels for an eigenvalue and the folded label decoder used in
self-tomography. `qpeSelfTomographyGoodProjector` selects good labels in the eigenbasis on the
false control branch.

The mathematical background is described in [LloydMohseniRebentrost2014].

## Main statements

* `qpeGoodLabels`: labels within circular phase distance `1 / M` of `-r / 2`.
* `qpeLabelDecode`: the folded phase estimate.
* `qpeSelfTomographyGoodProjector`: the spectral good-event matrix.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

open Qatlib.Foundations.PureStateMath

open Matrix

set_option autoImplicit false

namespace Qatlib.Concepts.CopyEvolution.SelfTomography

/-- The phase labels within circular distance `1 / M` of the eigenphase `-r / 2`. -/
noncomputable def qpeGoodLabels (M : ℕ) (r : ℝ) : Finset (Fin M) :=
  Finset.univ.filter (fun z => phaseDistance (-r / 2) ((z.val : ℝ) / M) ≤ 1 / (M : ℝ))

/-- The folded eigenvalue estimate `2 * min (z.val / M) (1 - z.val / M)`. -/
noncomputable def qpeLabelDecode (M : ℕ) (z : Fin M) : ℝ :=
  2 * min ((z.val : ℝ) / M) (1 - (z.val : ℝ) / M)

/-- The matrix selecting good label-eigenvector pairs on the false control branch, expressed
using the columns of `V`. -/
noncomputable def qpeSelfTomographyGoodProjector (D M : ℕ) (V : Operator D) (eig : Fin D → ℝ) :
    Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ :=
  Matrix.of fun p q =>
    if p.2.1 ∨ q.2.1 then 0
    else if p.1 = q.1 then
      ∑ j ∈ Finset.univ.filter (fun j => p.1 ∈ qpeGoodLabels M (eig j)),
        V p.2.2 j * star (V q.2.2 j)
    else 0
end Qatlib.Concepts.CopyEvolution.SelfTomography
