/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.PreparedRepeat
import Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.PureStateMath

/-!
# Basis Frame

Basis Frame constructions and identities for Query Complexity.
-/
open Qatlib Matrix
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol
open scoped BigOperators Classical ComplexOrder
set_option autoImplicit false
set_option maxRecDepth 2048
noncomputable section

namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor
/-- Construction for basis Frame in the basis frame model. -/
def basisFrame {D : ℕ} {I : Type} (φ : I → Fin D) : Matrix (Fin D) I ℂ :=
  fun h i => if h=φ i then 1 else 0

/-- The finite protocol identity or bound `basisFrame_compress` holds under exactly the displayed hypotheses. -/
theorem basisFrame_compress {D : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (φ : I → Fin D) (U : Operator D) (i j : I) :
    compress (basisFrame φ) U (basisFrame φ) i j=U (φ i) (φ j) := by
  simp [compress,basisFrame,Matrix.mul_apply,Matrix.conjTranspose_apply,mul_ite,ite_mul]


end Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor
