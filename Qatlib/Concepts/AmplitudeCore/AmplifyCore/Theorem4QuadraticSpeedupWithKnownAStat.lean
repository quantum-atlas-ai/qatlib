/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Span.Defs
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Theorem2QuadraticSpeedupRestrictedQuan
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.InnerProductSpace.l2Space
import Qatlib.Concepts.AmplitudeCore.AmplifyCore.Theorem4QuadraticSpeedupWithKnownAAux

/-!
# Specification of exact amplification with known probability

`expected` specifies a uniform design that turns any known positive success probability into
certain success. The design returns an ancillary mixing parameter and a program whose
preparation call count is bounded by positive constant multiples of `1 / sqrt a`. See
[BrassardEtAl2002] for background.

## Main statements

* `expected`: The proposition asserting a uniform exact amplification design with valid mixing
  parameter, unit total norm, success probability one, and call count proportional to `1 / sqrt
  a`.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification

end Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification

namespace Qatlib.Concepts.AmplitudeCore.AmplifyCore.Theorem4KnownASpec
/-- The proposition asserting a uniform exact amplification design with valid mixing parameter,
unit total norm, success probability one, and call count proportional to `1 / sqrt a`. -/
def expected : Prop :=
  (∃ (design : ℝ → ℝ × List (Fin 6)) (c C : ℝ),
  0 < c ∧ 0 < C ∧
  ∀ (ι H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (b : HilbertBasis ι ℂ H) (i0 : ι)
    (label : ι → ℤ) (A : H ≃ₗᵢ[ℂ] H) (χ : ℤ → Bool) (a : ℝ),
    let P := Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.goodProjection b label χ;
    a = ‖P (A (b i0))‖ ^ 2 →
    0 < a →
    let d := design a;
    let v := Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.run A (b i0) P d.1 d.2;
    0 ≤ d.1 ∧ d.1 ≤ 1 ∧
    ‖v.1‖ ^ 2 + ‖v.2‖ ^ 2 = 1 ∧
    ‖P v.1‖ ^ 2 + ‖P v.2‖ ^ 2 = 1 ∧
    c / Real.sqrt a ≤ (Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.calls d.2 : ℝ) ∧
    (Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.calls d.2 : ℝ) ≤ C / Real.sqrt a)
end Qatlib.Concepts.AmplitudeCore.AmplifyCore.Theorem4KnownASpec
