/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib

noncomputable def sourceDifferenceGate (G : Type*) [Group G] [Fintype G] :
    Matrix (G × G) (G × G) ℂ := by
  classical
  exact permMatrix (fun p : G × G => (p.2⁻¹ * p.1, p.2))

noncomputable def sourceDiagonalLeft (G : Type*) [Group G] [Fintype G] (g : G) :
    Matrix (G × G) (G × G) ℂ := by
  classical
  exact permMatrix (fun p : G × G => (g * p.1, g * p.2))

noncomputable def sourceRightFactorLeft (G : Type*) [Group G] [Fintype G] (g : G) :
    Matrix (G × G) (G × G) ℂ := by
  classical
  exact permMatrix (fun p : G × G => (p.1, g * p.2))

end Qatlib.Concepts.HspRecovery.RecordExtract
