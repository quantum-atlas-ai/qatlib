/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
open scoped BigOperators

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

noncomputable def mnrsDiscriminant {X : Type*}
    (P : Matrix X X ℝ) (π : X → ℝ) : Matrix X X ℂ :=
  fun x y => ((Real.sqrt (π x) * P x y / Real.sqrt (π y) : ℝ) : ℂ)

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
