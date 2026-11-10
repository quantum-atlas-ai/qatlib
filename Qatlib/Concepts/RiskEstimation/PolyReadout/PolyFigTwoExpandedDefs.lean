/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyRotation.PolyRotationFigTwoCorrectedQuan
import Qatlib.Concepts.RiskEstimation.PolyReadout.PolyRotationDefs
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.RiskEstimation.PolyRotation
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.PolyReadout
open Matrix
open scoped Classical BigOperators

noncomputable def figTwoDataGate (n : ℕ) (A : Matrix (Reg n) (Reg n) ℂ) :
    Matrix (Reg (n+1+(n-1))) (Reg (n+1+(n-1))) ℂ :=
  relabelGate (multiKnownSplit n).symm
    (TensorGate (TensorGate A (1 : Matrix Bool Bool ℂ)) (1 : Matrix (Reg (n-1)) (Reg (n-1)) ℂ))

theorem figTwoDataGate_unitary {n : ℕ} {A : Matrix (Reg n) (Reg n) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Reg n) ℂ) :
    figTwoDataGate n A ∈ Matrix.unitaryGroup (Reg (n+1+(n-1))) ℂ :=
  relabelGate_mem_unitary
    (tensorGate_unitary (tensorGate_unitary hA (Matrix.unitaryGroup Bool ℂ).one_mem)
      (Matrix.unitaryGroup (Reg (n-1)) ℂ).one_mem) (multiKnownSplit n).symm

def figTwoAngleWord (n u : ℕ) (c : ℝ) (fp : Polynomial ℝ) :
    List (ReflectionGate (n+1+(n-1))) :=
  figTwoProgramCorrected (fp.natDegree*(2*u+1))
    (fun y => -(riskFigTwoAnglePoly u c fp).eval (figTwoRegEval y : ℝ))

theorem figTwoAngleWord_legal (n u : ℕ) (c : ℝ) (fp : Polynomial ℝ) :
    reflectionLegal (figTwoAngleWord n u c fp) :=
  (figTwoProgramCorrected_cost (n := n) (fp.natDegree*(2*u+1))
    (fun y => -(riskFigTwoAnglePoly u c fp).eval (figTwoRegEval y : ℝ))).1

theorem figTwoAngleWord_length (n u : ℕ) (c : ℝ) (fp : Polynomial ℝ) :
    (figTwoAngleWord n u c fp).length =
      ((figTwoTerms (n := n) (fp.natDegree*(2*u+1))).map
        fun l => multiKnownCost l.length).sum :=
  (figTwoProgramCorrected_cost (n := n) (fp.natDegree*(2*u+1))
    (fun y => -(riskFigTwoAnglePoly u c fp).eval (figTwoRegEval y : ℝ))).2

noncomputable def figTwoExpandedPreparation (n : ℕ) (A : Matrix (Reg n) (Reg n) ℂ)
    (u : ℕ) (c : ℝ) (fp : Polynomial ℝ) :
    Matrix (Reg (n+1+(n-1))) (Reg (n+1+(n-1))) ℂ :=
  reflectionProgramMatrix (figTwoAngleWord n u c fp)*figTwoDataGate n A

theorem figTwoExpandedPreparation_unitary {n : ℕ} {A : Matrix (Reg n) (Reg n) ℂ}
    {u : ℕ} {c : ℝ} {fp : Polynomial ℝ} (hA : A ∈ Matrix.unitaryGroup (Reg n) ℂ) :
    figTwoExpandedPreparation n A u c fp ∈ Matrix.unitaryGroup (Reg (n+1+(n-1))) ℂ :=
  (Matrix.unitaryGroup (Reg (n+1+(n-1))) ℂ).mul_mem
    (reflectionProgramMatrix_unitary (figTwoAngleWord n u c fp) (figTwoAngleWord_legal n u c fp))
    (figTwoDataGate_unitary hA)

def figTwoStart (n : ℕ) (j : Reg n) : Reg (n+1+(n-1)) :=
  (multiKnownSplit n).symm ((j,false),fun _ => false)

def figTwoGoodSet (n : ℕ) : Finset (Reg (n+1+(n-1))) :=
  Finset.univ.filter (fun q => q (figTwoTargetWire n))

noncomputable def figTwoExpandedLaw (n : ℕ) (A : Matrix (Reg n) (Reg n) ℂ) (j : Reg n)
    (u : ℕ) (c : ℝ) (fp : Polynomial ℝ) (M : ℕ)
    (hA : A ∈ Matrix.unitaryGroup (Reg n) ℂ) (hM : 2 ≤ M) : FinDist (Fin M) :=
  aeLaw M (figTwoExpandedPreparation n A u c fp) (figTwoStart n j) (figTwoGoodSet n)
    (figTwoExpandedPreparation_unitary hA) hM

end Qatlib.Concepts.RiskEstimation.PolyReadout
