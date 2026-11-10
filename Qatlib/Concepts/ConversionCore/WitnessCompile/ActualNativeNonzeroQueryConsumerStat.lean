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
open Qatlib.Concepts.BitWordCompiler.WordComposition

namespace Qatlib.Concepts.ConversionCore.WitnessCompile
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

def ActualNativeNonzeroQueryConsumer : Prop :=
  ∃ (c e : ℕ) (build : SourceRationalProblem → ℕ → SourceNativeProgram),
    0<c ∧ 0<e ∧ sourceNativeCompilerTime build c e ∧ ∀ k : ℕ, 4 ≤ k →
    let d := sourceTwoLabelProblem
    let p := build d k
    sourceNativeLegal d p ∧ 0<sourceNativeCalls p ∧
    sourceNativeCalls p ≤ c*4^k*(k+1) ∧
    sourceNativeGates p ≤ c*(1+(sourceProblemBits d).length+k+sourceNativeCalls p)^e ∧
    sourceAddressBits d+sourceValueBits d+1+sourcePayloadBits d ≤ p.width ∧
    p.width ≤ c*(1+(sourceProblemBits d).length+k)^e ∧
    ∀ x, (∑ z, star ((sourceNativeMatrix d x p *ᵥ sourceNativeClean d p.width false
      (sourceRationalState (d.start x))) z)*
      sourceNativeClean d p.width true (sourceRationalState (d.target x)) z).re ≥
        Real.sqrt (1-(1/2 : ℝ)^k)
end Qatlib.Concepts.ConversionCore.WitnessCompile
