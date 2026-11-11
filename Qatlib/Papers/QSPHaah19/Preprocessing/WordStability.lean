/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeStandardPhaseStability

set_option backward.isDefEq.respectTransparency false

/-!
# Word Stability

The exact source convention or stability contract is consumed with all original parameters and hypotheses.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QSPHaah19.Preprocessing
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Matrix Polynomial
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data

/-- The exact source convention or stability contract is consumed with all original parameters and hypotheses. -/
theorem standardMatrixWord_error (base other : ℂ) (zs ws : List ℂ) (x s δ : ℝ)
    (hs : s*s=1-x*x) (hb : ‖base‖=1) (ho : ‖other‖=1)
    (hz : ∀ z∈zs,‖z‖=1) (hw : ∀ w∈ws,‖w‖=1)
    (hδ : 0≤δ) (hphases : List.Forall₂ (fun z w => ‖z-w‖≤δ) zs ws) :
    ‖standardMatrixWord base x s zs-standardMatrixWord other x s ws‖≤
      ‖base-other‖+(zs.length : ℝ)*δ :=
  Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.standardMatrixWord_error base other zs ws x s δ hs hb ho hz hw hδ hphases

end Qatlib.Papers.QSPHaah19.Preprocessing
