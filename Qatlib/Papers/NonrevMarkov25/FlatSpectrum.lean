/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MarkovChains.FlatSpectrum
import Qatlib.Papers.NonrevMarkov25.SzegedyFrame

/-!
# Time-reversal invariance of the flat discriminant

For a transition matrix with a strictly positive stationary probability, `source_time_reversal`
proves that reversing the chain leaves its flat discriminant unchanged. The equality specializes
the flat-discriminant construction used in [ClaudonPiquemalMonmarche2025].

## Main statements

* `source_time_reversal`: The flat discriminant of the time-reversed transition matrix equals
  the flat discriminant of the original chain.

## References

* [Claudon et al., 2025][ClaudonPiquemalMonmarche2025]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Papers.NonrevMarkov25.FlatSpectrum

/-- The flat discriminant of the time-reversed transition matrix equals the flat discriminant of
the original chain [ClaudonPiquemalMonmarche2025]. -/
theorem source_time_reversal {I : Type*} [Fintype I] [DecidableEq I] (K : SzegedyFrame.Model I) :
    Qatlib.Foundations.MarkovChains.ReverseKernel.flat
      (Qatlib.Foundations.MarkovChains.ReverseKernel.reverse K.transition K.probability)=
    Qatlib.Foundations.MarkovChains.ReverseKernel.flat K.transition :=
  Qatlib.Foundations.MarkovChains.FlatSpectrum.flat_reverse _ _ K.positive
end Qatlib.Papers.NonrevMarkov25.FlatSpectrum
