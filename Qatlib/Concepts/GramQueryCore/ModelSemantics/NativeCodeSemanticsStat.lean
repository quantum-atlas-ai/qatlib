/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.AdaptiveModels
import Qatlib.Concepts.BitWordCompiler.WordComposition.FiniteModels
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.BitWordCompiler.WordComposition

namespace Qatlib.Concepts.GramQueryCore.ModelSemantics
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

def NativeCodeSemantics : Prop :=
  Function.Injective sourceNativeProgramBits ∧ Function.Injective sourceProblemBits ∧
  ∀ (d : SourceRationalProblem) (p : SourceNativeProgram),
    sourceNativeLegal d p → ∀ x : Fin d.count,
    sourceNativeMatrix d x p ∈ Matrix.unitaryGroup (Reg p.width) ℂ ∧
    sourceNativeCalls p+sourceNativeGates p=p.steps.length ∧
    (sourceAddressBits d+sourceValueBits d+1+sourcePayloadBits d ≤ p.width →
      (sourceNativeFrame d p.width)ᴴ * sourceNativeFrame d p.width=1)
end Qatlib.Concepts.GramQueryCore.ModelSemantics
