/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.InteractionEvo.CayleyTransform
public import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
public import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
public import Qatlib.Concepts.BlockEncoding.EncodingCore.CoordinateFiber

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.InteractionEvo.CayleyTransform Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

set_option autoImplicit false

open Matrix
open scoped Matrix.Norms.L2Operator

variable {ιS ιA : Type} [Fintype ιS] [DecidableEq ιS] [Fintype ιA] [DecidableEq ιA]

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding.EncodingCore

namespace Qatlib.Concepts.InteractionEvo.TransducerCore

structure HamTOracle (a0 : ιA) (H : ℝ → Matrix ιS ιS ℂ) (T α : ℝ) (J : ℕ) where
  O : Fin J → Matrix (ιA × ιS) (ιA × ιS) ℂ
  hermitian : ∀ j, (O j).IsHermitian
  unitary : ∀ j, O j ∈ Matrix.unitaryGroup (ιA × ιS) ℂ
  block : ∀ j, compress (encodingFiber a0) (O j) (encodingFiber a0) =
    (((α⁻¹ : ℝ) : ℂ) • H ((j : ℝ) * T / J))

noncomputable def hamTMatrix {J : ℕ} (O : Fin J → Matrix (ιA × ιS) (ιA × ιS) ℂ) :
    Matrix ((ιA × ιS) × Fin J) ((ιA × ιS) × Fin J) ℂ :=
  Matrix.blockDiagonal O

noncomputable def gridCayleyStep (H : ℝ → Matrix ιS ιS ℂ) (α T : ℝ) (J : ℕ) (j : ℕ) :
    Matrix ιS ιS ℂ :=
  cayleyStep (((α⁻¹ : ℝ) : ℂ) • H ((j : ℝ) * T / J)) (α * T / J)

noncomputable def cayleyPartialProduct (H : ℝ → Matrix ιS ιS ℂ) (α T : ℝ) (J : ℕ)
    (j : ℕ) : Matrix ιS ιS ℂ :=
  ((List.range j).map (gridCayleyStep H α T J)).reverse.prod

noncomputable def cayleyProduct (H : ℝ → Matrix ιS ιS ℂ) (α T : ℝ) (J : ℕ) :
    Matrix ιS ιS ℂ :=
  cayleyPartialProduct H α T J J

noncomputable def oracleDirectSum {J : ℕ} (O : Fin J → Matrix (ιA × ιS) (ιA × ιS) ℂ) :
    Matrix (ιS ⊕ ((ιA × ιS) × Fin J)) (ιS ⊕ ((ιA × ιS) × Fin J)) ℂ :=
  Matrix.fromBlocks (1 : Matrix ιS ιS ℂ) (0 : Matrix ιS ((ιA × ιS) × Fin J) ℂ)
    (0 : Matrix ((ιA × ιS) × Fin J) ιS ℂ) (hamTMatrix O)
end Qatlib.Concepts.InteractionEvo.TransducerCore
