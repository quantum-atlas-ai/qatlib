/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.AdaptiveModels
import Qatlib.Concepts.BitWordCompiler.WordComposition.FiniteModels
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels

/-!
# Native code semantics specification

Defines `NativeCodeSemantics`, combining injective bit encodings of programs and rational source
problems with the matrix semantics of legal native programs. It requires unitary evaluation and
exact accounting of calls and gates.

When the register contains the address, answer, Boolean tag, and payload bits, the clean source
frame must also be an isometry. These conditions specialize the standard finite-register circuit
model of [NielsenChuang2010] to the native instruction format.

## Main statements

* `NativeCodeSemantics`: specifies encoding injectivity, unitary evaluation, resource
  accounting, and frame isometry.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.BitWordCompiler.WordComposition

namespace Qatlib.Concepts.GramQueryCore.ModelSemantics
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

/-- The conjunction of injective native program and problem encodings with legal-program
unitarity, exact call-plus-gate accounting, and source-frame isometry whenever the register
width is sufficient. -/
def NativeCodeSemantics : Prop :=
  Function.Injective sourceNativeProgramBits ∧ Function.Injective sourceProblemBits ∧
  ∀ (d : SourceRationalProblem) (p : SourceNativeProgram),
    sourceNativeLegal d p → ∀ x : Fin d.count,
    sourceNativeMatrix d x p ∈ Matrix.unitaryGroup (Reg p.width) ℂ ∧
    sourceNativeCalls p+sourceNativeGates p=p.steps.length ∧
    (sourceAddressBits d+sourceValueBits d+1+sourcePayloadBits d ≤ p.width →
      (sourceNativeFrame d p.width)ᴴ * sourceNativeFrame d p.width=1)
end Qatlib.Concepts.GramQueryCore.ModelSemantics
