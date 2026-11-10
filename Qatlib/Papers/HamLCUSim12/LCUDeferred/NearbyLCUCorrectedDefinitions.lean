/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.LCUDeferred.DeferredLCUContracts
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
set_option warningAsError false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.HamLCUSim12.LCUDeferred
open Matrix
open scoped Classical
variable {I : Type} [Fintype I] [DecidableEq I]

def vKappaSource (κ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun b b' =>
    ((if b=0 then
      (if b'=0 then Real.sqrt (κ/(κ+1)) else -(Real.sqrt (κ+1))⁻¹)
      else (if b'=0 then (Real.sqrt (κ+1))⁻¹ else Real.sqrt (κ/(κ+1))) : ℝ) : ℂ)

def splitLCUBit {k : ℕ} (i : Fin k) :
    ((Fin k→Bool)×I) ≃ (Fin 2×(({j : Fin k // j≠i}→Bool)×I)) :=
  ((Equiv.prodCongr ((Equiv.funSplitAt i Bool).trans
    (Equiv.prodCongr boolEquivFin2 (Equiv.refl _))) (Equiv.refl I)).trans
    (Equiv.prodAssoc _ _ _))

def rotGateCorrected (k : ℕ) (i : Fin k) (V : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ :=
  relabelGate (splitLCUBit (I := I) i).symm (TensorGate V 1)

def ctrlGateCorrected (k : ℕ) (i : Fin k)
    (Cx Cy : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ) :
    Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ :=
  Matrix.of fun p q => if p.1 i=q.1 i then (if p.1 i then Cy else Cx) p q else 0

def lcuLevelGateCorrected (k : ℕ) (i : Fin k) (V : Matrix (Fin 2) (Fin 2) ℂ)
    (Cx Cy : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ) :
    Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ :=
  rotGateCorrected k i Vᴴ*(ctrlGateCorrected k i Cx Cy*rotGateCorrected k i V)

def lemma2CircuitCorrected (κ : ℝ) (Ua Ub : Matrix I I ℂ) :
    Matrix ((Fin 1→Bool)×I) ((Fin 1→Bool)×I) ℂ :=
  lcuLevelGateCorrected 1 0 (vKappaSource κ) (liftSys 1 Ua) (liftSys 1 Ub)

def lemma2OutputCorrected (κ : ℝ) (Ua Ub : Matrix I I ℂ) (ψ : QState I) :
    QState ((Fin 1→Bool)×I) :=
  ApplyGate (lemma2CircuitCorrected κ Ua Ub) (TensorState (Ket (fun _=>false)) ψ)

def lemma2FailureProbCorrected (κ : ℝ) (Ua Ub : Matrix I I ℂ) (ψ : QState I) : ℝ :=
  MeasureProb (lemma2OutputCorrected κ Ua Ub ψ) (lemma2FailSet×ˢFinset.univ)

def chainGateCorrected (k : ℕ) (bit : Fin k) (W w : ℝ)
    (acc : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ) (U : Matrix I I ℂ) :
    Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ :=
  lcuLevelGateCorrected k bit (vKappaSource (W/w)) acc (liftSys k U)

def chainFoldCorrected (k : ℕ) (W : ℝ)
    (acc : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ) :
    List (Fin k×(ℝ×Matrix I I ℂ))→Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ
  | [] => acc
  | (bit,w,U)::rest => chainFoldCorrected k (W+w) (chainGateCorrected k bit W w acc U) rest

def chainCircuitCorrected (k : ℕ) :
    List (Fin k×(ℝ×Matrix I I ℂ))→Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ
  | [] => 1
  | (_bit,w,U)::rest => chainFoldCorrected k w (liftSys k U) rest

def cwProtocolCorrected (k : ℕ) (c : Fin (k+1)→ℝ) (U : Fin (k+1)→Matrix I I ℂ) :
    Matrix ((Fin (k+1)→Bool)×I) ((Fin (k+1)→Bool)×I) ℂ :=
  let a := (Finset.univ.filter fun q : Fin (k+1) => 0<c q).card
  let sPos := ∑ q : Fin (k+1),if 0<c q then c q else 0
  let sNeg := ∑ q : Fin (k+1),if c q<0 then |c q| else 0
  lcuLevelGateCorrected (k+1) ⟨a%(k+1),Nat.mod_lt _ (Nat.succ_pos k)⟩ (vKappaSource (sPos/sNeg))
    (chainCircuitCorrected (k+1) (cwChainList k 0 c U (Finset.univ.filter fun q=>0<c q)))
    (-(chainCircuitCorrected (k+1) (cwChainList k a (fun q=>|c q|) U (Finset.univ.filter fun q=>c q<0))))

def cwOutputCorrected (k : ℕ) (c : Fin (k+1)→ℝ) (U : Fin (k+1)→Matrix I I ℂ)
    (ψ : QState I) : QState ((Fin (k+1)→Bool)×I) :=
  ApplyGate (cwProtocolCorrected k c U) (TensorState (Ket (cwZero k)) ψ)

def cwFailureProbCorrected (k : ℕ) (c : Fin (k+1)→ℝ) (U : Fin (k+1)→Matrix I I ℂ)
    (ψ : QState I) : ℝ :=
  MeasureProb (cwOutputCorrected k c U ψ)
    (((Finset.univ (α:=Fin (k+1)→Bool)).erase (cwZero k))×ˢFinset.univ)
end Qatlib.Papers.HamLCUSim12.LCUDeferred
