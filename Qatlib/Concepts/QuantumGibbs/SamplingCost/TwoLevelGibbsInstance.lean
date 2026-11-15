/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Foundations.QueryWordCore.HamiltonianQuery
public import Qatlib.Foundations.PureStateMath.Tensor
public import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates

@[expose] public section
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.HamiltonianQuery

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QuantumGibbs.SamplingCost

open Matrix

open scoped Matrix.Norms.L2Operator

noncomputable def twoLevelHamiltonian (Δ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal fun i => ((Δ * ((i : ℕ) : ℝ) : ℝ) : ℂ)

noncomputable def twoLevelHamiltonianLift (A : ℕ) (Δ : ℝ) :
    Matrix (Fin 2 × Fin A) (Fin 2 × Fin A) ℂ :=
  TensorGate (twoLevelHamiltonian Δ) 1

noncomputable def gibbsTwoLevel (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal fun i =>
    ((Real.exp (-s * ((i : ℕ) : ℝ)) / ∑ j : Fin 2, Real.exp (-s * ((j : ℕ) : ℝ)) : ℝ) : ℂ)

noncomputable def pureDensity {I : Type*} (ψ : I → ℂ) : Matrix I I ℂ :=
  Matrix.vecMulVec ψ (star ψ)

noncomputable def purifiedGibbsTwoLevel (s : ℝ) : QState (Fin 2 × Fin 2) :=
  fun p =>
    if p = (0, 0) then ((Real.sqrt (1 / (1 + Real.exp (-s))) : ℝ) : ℂ)
    else if p = (1, 1) then
      ((Real.sqrt (Real.exp (-s) / (1 + Real.exp (-s))) : ℝ) : ℂ)
    else 0

noncomputable def purifiedGibbsReflection (s : ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  2 * pureDensity (purifiedGibbsTwoLevel s) - 1

end Qatlib.Concepts.QuantumGibbs.SamplingCost
