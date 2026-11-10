/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopyDrivenPhaseReadout
import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

open Qatlib.Foundations.PureStateMath

open Matrix

set_option autoImplicit false

namespace Qatlib.Concepts.CopyEvolution.SelfTomography

noncomputable def qpeGoodLabels (M : ℕ) (r : ℝ) : Finset (Fin M) :=
  Finset.univ.filter (fun z => phaseDistance (-r / 2) ((z.val : ℝ) / M) ≤ 1 / (M : ℝ))

noncomputable def qpeLabelDecode (M : ℕ) (z : Fin M) : ℝ :=
  2 * min ((z.val : ℝ) / M) (1 - (z.val : ℝ) / M)

noncomputable def qpeSelfTomographyGoodProjector (D M : ℕ) (V : Operator D) (eig : Fin D → ℝ) :
    Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ :=
  Matrix.of fun p q =>
    if p.2.1 ∨ q.2.1 then 0
    else if p.1 = q.1 then
      ∑ j ∈ Finset.univ.filter (fun j => p.1 ∈ qpeGoodLabels M (eig j)),
        V p.2.2 j * star (V q.2.2 j)
    else 0
end Qatlib.Concepts.CopyEvolution.SelfTomography
