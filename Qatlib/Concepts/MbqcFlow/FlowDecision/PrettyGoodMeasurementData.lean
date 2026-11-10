/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import QuantumInfo.ForMathlib.HermitianMat.Sqrt
open Qatlib.Foundations.PureStateMath
set_option warningAsError false

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open Matrix
open scoped ComplexOrder MatrixOrder

variable {I : Type} [Fintype I] [DecidableEq I] {D : ℕ}

noncomputable def ensembleGram (W : Matrix (Fin D) I ℂ) : HermitianMat I ℂ :=
  ⟨Wᴴ * W, Matrix.isHermitian_conjTranspose_mul_self W⟩

omit [DecidableEq I] in

theorem ensembleGram_nonneg (W : Matrix (Fin D) I ℂ) : 0 ≤ ensembleGram W := by
  rw [HermitianMat.zero_le_iff]
  exact Matrix.posSemidef_conjTranspose_mul_self W

noncomputable def ensembleGramInvSqrt (W : Matrix (Fin D) I ℂ) : HermitianMat I ℂ :=
  (ensembleGram W).cfc (fun x : ℝ => (Real.sqrt x)⁻¹)

noncomputable def prettyGoodFrame (W : Matrix (Fin D) I ℂ) : Matrix (Fin D) I ℂ :=
  W * (ensembleGramInvSqrt W).mat

end Qatlib.Concepts.MbqcFlow.FlowDecision
