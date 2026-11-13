/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FiniteLocc.LOCCProgram.EntanglementDefs
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditResourceConverseAux

/-!
# LOCC teleportation success and resource shapes

This module defines the joint input and resource operator `teleportLoccJoint`, Bob's marginal
`loccBobMarginal`, and exact teleportation success for a complete LOCC protocol. These
definitions provide an operator formulation of the teleportation setting of
[BennettEtAl1993Teleportation].

`LoccLeafCount` records the number of terminal protocol branches, while `MaxEntResourceShape`
expresses a pure maximally entangled resource using two orthonormal families.

## Main definitions

* `LoccTeleportSuccess`: completeness and exact recovery of every density operator.
* `MaxEntResourceShape`: a resource outer product in maximally entangled form.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.FiniteLocc.LOCCProgram

namespace Qatlib.Concepts.QuditTeleport.ResourceIff

open Matrix

variable {D E : ℕ}

/-- The tensor product of an input operator and a bipartite resource, regrouped so that Alice
holds the input and the first resource register. -/
noncomputable def teleportLoccJoint (n : ℕ) (ρ : Operator n)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    Matrix (Fin (n * n) × Fin n) (Fin (n * n) × Fin n) ℂ :=
  fun x y =>
    ρ ((finProdFinEquiv (m := n) (n := n)).symm x.1).1
      ((finProdFinEquiv (m := n) (n := n)).symm y.1).1 *
    ω (((finProdFinEquiv (m := n) (n := n)).symm x.1).2, x.2)
      (((finProdFinEquiv (m := n) (n := n)).symm y.1).2, y.2)

/-- Bob's reduced operator, obtained by swapping the LOCC register order and taking the partial
trace over Alice. -/
noncomputable def loccBobMarginal (n : ℕ)
    (X : Matrix (Fin (n * n) × Fin n) (Fin (n * n) × Fin n) ℂ) : Operator n :=
  PartialTrace (relabelGate (Equiv.prodComm (Fin (n * n)) (Fin n)) X)

/-- Completeness of an LOCC protocol together with exact recovery of every input density
operator in Bob's marginal using resource `ω`. -/
def LoccTeleportSuccess (n : ℕ) (proto : LoccProtocol (n * n) n)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) : Prop :=
  LoccComplete proto ∧
  ∀ ρ : Operator n, IsDensityOperator ρ →
    loccBobMarginal n (LoccChannel proto (teleportLoccJoint n ρ ω)) = ρ

/-- The number of terminal branches of an LOCC protocol, summed recursively over each local
measurement outcome. -/
def LoccLeafCount : LoccProtocol D E → ℕ
  | .halt => 1
  | .stepA _ _ next => Finset.univ.sum fun i => LoccLeafCount (next i)
  | .stepB _ _ next => Finset.univ.sum fun i => LoccLeafCount (next i)

/-- The property that a resource operator is the outer product of a maximally entangled vector
formed from two orthonormal families. -/
def MaxEntResourceShape (n : ℕ) (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    Prop :=
  ∃ u v : Fin n → QState (Fin n),
    Qatlib.Concepts.QuditTeleport.ResourceIff.QuditOrthonormalFamily n u ∧
      Qatlib.Concepts.QuditTeleport.ResourceIff.QuditOrthonormalFamily n v ∧
        ω = outerProduct (Qatlib.Concepts.QuditTeleport.ResourceIff.quditMaxEntResource n u v)

end Qatlib.Concepts.QuditTeleport.ResourceIff
