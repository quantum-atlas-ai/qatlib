/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FiniteLocc.LOCCProgram.EntanglementDefs
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditResourceConverseAux
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.FiniteLocc.LOCCProgram

namespace Qatlib.Concepts.QuditTeleport.ResourceIff

open Matrix

variable {D E : ℕ}

noncomputable def teleportLoccJoint (n : ℕ) (ρ : Operator n)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    Matrix (Fin (n * n) × Fin n) (Fin (n * n) × Fin n) ℂ :=
  fun x y =>
    ρ ((finProdFinEquiv (m := n) (n := n)).symm x.1).1
      ((finProdFinEquiv (m := n) (n := n)).symm y.1).1 *
    ω (((finProdFinEquiv (m := n) (n := n)).symm x.1).2, x.2)
      (((finProdFinEquiv (m := n) (n := n)).symm y.1).2, y.2)

noncomputable def loccBobMarginal (n : ℕ)
    (X : Matrix (Fin (n * n) × Fin n) (Fin (n * n) × Fin n) ℂ) : Operator n :=
  PartialTrace (relabelGate (Equiv.prodComm (Fin (n * n)) (Fin n)) X)

def LoccTeleportSuccess (n : ℕ) (proto : LoccProtocol (n * n) n)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) : Prop :=
  LoccComplete proto ∧
  ∀ ρ : Operator n, IsDensityOperator ρ →
    loccBobMarginal n (LoccChannel proto (teleportLoccJoint n ρ ω)) = ρ

def LoccLeafCount : LoccProtocol D E → ℕ
  | .halt => 1
  | .stepA _ _ next => Finset.univ.sum fun i => LoccLeafCount (next i)
  | .stepB _ _ next => Finset.univ.sum fun i => LoccLeafCount (next i)

def MaxEntResourceShape (n : ℕ) (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    Prop :=
  ∃ u v : Fin n → QState (Fin n),
    Qatlib.Concepts.QuditTeleport.ResourceIff.QuditOrthonormalFamily n u ∧
      Qatlib.Concepts.QuditTeleport.ResourceIff.QuditOrthonormalFamily n v ∧
        ω = outerProduct (Qatlib.Concepts.QuditTeleport.ResourceIff.quditMaxEntResource n u v)

end Qatlib.Concepts.QuditTeleport.ResourceIff
