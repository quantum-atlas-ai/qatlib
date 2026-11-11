/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Model.BornCurrentRecords

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.SCWFPrep24.Encoding

/-! OQ #141@44d4c95b9bcc0125a536ca5ccb06758090c5ace6 supplies this explicitly attributed extension/consumer of the Su et al. loss and encoding. It does not certify their entire training algorithm or a later analytical lower bound. -/
section
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open scoped BigOperators
open Qatlib

/-- Complete fixed-source statement `SCWFPreliminary.supplied_spin_state_normalized`; every original binder, hypothesis, and output is retained. -/
theorem uniform_spinor_encoding {S : Type*} [Fintype S] [Nonempty S]
    (a b c k : S → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) :
    Normalized (fun r : S × Bool => suppliedSpinState a b c k r.2 r.1) := by
  exact Qatlib.Concepts.SpinorSampling.Model.supplied_spin_state_normalized a b c k hz
end

end Qatlib.Papers.SCWFPrep24.Encoding
