/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.BellTeleportationInstrument
import Qatlib.Foundations.PureStateMath.BornBridge.PartialTraceCovariance

/-!
# Two-pair qubit resources and fixed corrections

`eq9Resource` and `eq9ResourceB` encode the equal superposition of two product vectors, with
predicates requiring orthonormal pairs. Preparation frames and branch Kraus operators connect
the Boolean version to the teleportation circuit.

`bobBranchMarginal` describes the receiver's reduced branch operator, and
`FourFixedCorrectionsTeleport` specifies completeness, unitary corrections, and exact total
recovery. The resource setting is the qubit teleportation protocol of
[BennettEtAl1993Teleportation].

## Main statements

* `eq9Resource`: The bipartite qubit vector `(u ⊗ p + v ⊗ q) / √2`, indexed by `Fin 2 × Fin 2`.
* `eq9OrthoPairs`: The condition that `u`, `v`, `p`, and `q` are normalized and the pairs `(u,
  v)` and `(p, q)` are orthogonal.
* `eq9BranchKraus`: The input-to-output Kraus matrix for outcome `o` after preparing the
  two-pair resource and applying `teleportDecodeGate`.
* `FourFixedCorrectionsTeleport`: The condition that four unitary corrections and a complete
  Alice-side Kraus family recover every input operator after summing the corrected branch
  marginals.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.QuditTeleport.ResourceIff

open Matrix

/-- The bipartite qubit vector `(u ⊗ p + v ⊗ q) / √2`, indexed by `Fin 2 × Fin 2`. -/
noncomputable def eq9Resource (u v p q : QState (Fin 2)) : QState (Fin 2 × Fin 2) :=
  fun x => ((1 / Real.sqrt 2 : ℝ) : ℂ) * (u x.1 * p x.2 + v x.1 * q x.2)

/-- The condition that `u`, `v`, `p`, and `q` are normalized and the pairs `(u, v)` and `(p, q)`
are orthogonal. -/
def eq9OrthoPairs (u v p q : QState (Fin 2)) : Prop :=
  Normalized u ∧ Normalized v ∧ Normalized p ∧ Normalized q ∧
    Inner u v = 0 ∧ Inner p q = 0

/-- The bipartite vector `(u ⊗ p + v ⊗ q) / √2`, indexed by Boolean pairs. -/
noncomputable def eq9ResourceB (u v p q : QState Bool) : QState (Bool × Bool) :=
  fun x => ((1 / Real.sqrt 2 : ℝ) : ℂ) * (u x.1 * p x.2 + v x.1 * q x.2)

/-- The Boolean-indexed condition that all four vectors are normalized and each of the pairs
`(u, v)` and `(p, q)` is orthogonal. -/
def eq9OrthoPairsB (u v p q : QState Bool) : Prop :=
  Normalized u ∧ Normalized v ∧ Normalized p ∧ Normalized q ∧
    Inner u v = 0 ∧ Inner p q = 0

/-- The preparation matrix tensoring the input qubit with `eq9ResourceB u v p q` in
teleportation register order. -/
noncomputable def eq9PreparedFrame (u v p q : QState Bool) : Matrix (Fin 8) (Fin 2) ℂ :=
  Matrix.of fun r i =>
    if (teleportRegisterEquiv.symm r).1.1 = boolEquivFin2.symm i
      then eq9ResourceB u v p q ((teleportRegisterEquiv.symm r).1.2,
        (teleportRegisterEquiv.symm r).2)
      else 0

/-- The input-to-output Kraus matrix for outcome `o` after preparing the two-pair resource and
applying `teleportDecodeGate`. -/
noncomputable def eq9BranchKraus (u v p q : QState Bool) (o : Bool × Bool) : Operator 2 :=
  Matrix.of fun c i =>
    (teleportDecodeGate * eq9PreparedFrame u v p q)
      (teleportRegisterEquiv ((o.1, o.2), boolEquivFin2.symm c)) i

/-- The register equivalence moving Bob's qubit first and combining Alice's two qubit indices
into `Fin 4`. -/
noncomputable def bobFirstEquiv :
    (Fin 2 × Fin 2) × Fin 2 ≃ (Fin 2 × Fin 4) :=
  (Equiv.prodComm (Fin 2 × Fin 2) (Fin 2)).trans
    (Equiv.prodCongr (Equiv.refl (Fin 2)) (finProdFinEquiv (m := 2) (n := 2)))

/-- Bob's unnormalized reduced operator in outcome `s` after Alice applies `K s` to the input
and her half of resource `ω`. -/
noncomputable def bobBranchMarginal
    (K : Fin 4 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (ω : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (s : Fin 4) (ρ : Operator 2) : Operator 2 :=
  PartialTrace (relabelGate bobFirstEquiv
    ((TensorGate (K s) (1 : Operator 2)) *
      (relabelGate (Equiv.prodAssoc (Fin 2) (Fin 2) (Fin 2)).symm
        (TensorGate ρ ω)) *
      (TensorGate (K s) (1 : Operator 2))ᴴ))

/-- The condition that four unitary corrections and a complete Alice-side Kraus family recover
every input operator after summing the corrected branch marginals. -/
def FourFixedCorrectionsTeleport
    (K : Fin 4 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (U : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ)
    (ω : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Prop :=
  (∀ s : Fin 4, U s ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
  (∑ s : Fin 4, (TensorGate (K s) (1 : Operator 2))ᴴ
      * TensorGate (K s) (1 : Operator 2) = 1) ∧
  ∀ ρ : Operator 2,
    ∑ s : Fin 4, (U s) * bobBranchMarginal K ω s ρ * (U s)ᴴ = ρ

end Qatlib.Concepts.QuditTeleport.ResourceIff
