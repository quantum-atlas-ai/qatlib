/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationProtocol
import Qatlib.Foundations.PureStateMath.BornBridge.PartialTraceCovariance
set_option warningAsError false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.QuditTeleport.ResourceIff

open Matrix

noncomputable def quditBobFirstEquiv (n : ℕ) :
    (Fin n × Fin n) × Fin n ≃ (Fin n × Fin (n * n)) :=
  (Equiv.prodComm (Fin n × Fin n) (Fin n)).trans
    (Equiv.prodCongr (Equiv.refl (Fin n)) (finProdFinEquiv (m := n) (n := n)))

noncomputable def quditBobBranchMarginal (n : ℕ)
    (K : Fin n × Fin n → Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (s : Fin n × Fin n) (ρ : Operator n) : Operator n :=
  PartialTrace (relabelGate (quditBobFirstEquiv n)
    ((TensorGate (K s) (1 : Operator n)) *
      (relabelGate (Equiv.prodAssoc (Fin n) (Fin n) (Fin n)).symm
        (TensorGate ρ ω)) *
      (TensorGate (K s) (1 : Operator n))ᴴ))

def QuditFixedCorrectionsTeleport (n : ℕ) [NeZero n]
    (K : Fin n × Fin n → Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (U : Fin n × Fin n → Operator n)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) : Prop :=
  (∀ s : Fin n × Fin n, U s ∈ Matrix.unitaryGroup (Fin n) ℂ) ∧
  (∑ s : Fin n × Fin n, (TensorGate (K s) (1 : Operator n))ᴴ
      * TensorGate (K s) (1 : Operator n) = 1) ∧
  ∀ ρ : Operator n,
    ∑ s : Fin n × Fin n, (U s) * quditBobBranchMarginal n K ω s ρ * (U s)ᴴ = ρ

def QuditOrthonormalFamily (n : ℕ) (U : Fin n → QState (Fin n)) : Prop :=
  ∀ i j, Inner (U i) (U j) = if i = j then 1 else 0

noncomputable def quditMaxEntResource (n : ℕ) (u v : Fin n → QState (Fin n)) :
    QState (Fin n × Fin n) :=
  fun x => ((Real.sqrt (n : ℝ) : ℂ)⁻¹) * ∑ j, u j x.1 * v j x.2

noncomputable def quditResourcePreparedFrame (n : ℕ) [NeZero n]
    (R : QState (Fin n × Fin n)) : Matrix (Fin (n * n * n)) (Fin n) ℂ :=
  fun r j =>
    if ((quditRegisterEquiv n).symm r).1.1 = j
      then R (((quditRegisterEquiv n).symm r).1.2, ((quditRegisterEquiv n).symm r).2)
      else 0

noncomputable def quditResourceBranchKraus (n : ℕ) [NeZero n]
    (R : QState (Fin n × Fin n)) (o : Fin n × Fin n) : Operator n :=
  fun k j =>
    (relabelGate (quditRegisterEquiv n) (quditHaInvB n * quditSUMabInvB n) *
      quditResourcePreparedFrame n R) ((quditRegisterEquiv n) (o, k)) j

end Qatlib.Concepts.QuditTeleport.ResourceIff
