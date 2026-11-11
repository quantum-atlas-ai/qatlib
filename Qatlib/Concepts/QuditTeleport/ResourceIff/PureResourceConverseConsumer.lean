/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.FourFixedCorrectionsMaxEntConverseTele
import Qatlib.Concepts.QuditTeleport.ResourceIff.Eq9MaxEntCharacterizationTele

/-!
# Pure qubit resources in the teleportation normal form

`pure_resource_teleportation_eq9` combines the fixed correction marginal converse with the pure
state characterization of maximal entanglement. It expresses a normalized pure resource
supporting four fixed corrections in the orthonormal pair form associated with Eq. (9) of
[BennettEtAl1993Teleportation].

## Main statements

* `pure_resource_teleportation_eq9`: constructs orthonormal pairs whose Eq. (9) resource vector
  equals the given resource.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge


namespace Qatlib.Concepts.QuditTeleport.ResourceIff
open Matrix
open scoped Classical BigOperators ComplexOrder

/-- A normalized pure two qubit resource supporting teleportation with four fixed unitary
corrections has the maximally entangled orthonormal pair form of [Bennett et al., Eq.
(9)][BennettEtAl1993Teleportation]. -/
theorem pure_resource_teleportation_eq9
    (K : Fin 4 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (U : Fin 4 → Operator 2) (Ψ : QState (Fin 2 × Fin 2)) (hΨ : Normalized Ψ)
    (htele : FourFixedCorrectionsTeleport K U (outerProduct Ψ)) :
    ∃ u v p q : QState (Fin 2), eq9OrthoPairs u v p q ∧ eq9Resource u v p q = Ψ := by
  let e := Equiv.prodComm (Fin 2) (Fin 2)
  let Φ := relabelState e Ψ
  have hΦ : Normalized Φ := normalized_relabelState e hΨ
  have hswap : outerProduct Φ = relabelGate e (outerProduct Ψ) := by ext i j; rfl
  have hb :=
      fourFixedCorrectionsMaxEntConverse K U (outerProduct Ψ) (outerProduct_posSemidef Ψ) htele
  have hΦb : PartialTrace (outerProduct Φ) = (1 / 2 : ℂ) • (1 : Operator 2) := by
    rw [hswap]
    exact hb
  obtain ⟨u, v, p, q, hON, he⟩ := eq9MaxEntCharacterization Φ hΦ hΦb
  obtain ⟨hu, hv, hp, hq, huv, hpq⟩ := hON
  refine ⟨p, q, u, v, ⟨hp, hq, hu, hv, hpq, huv⟩, ?_⟩
  funext x
  have hh := congrFun he (x.2, x.1)
  change ((1 / Real.sqrt 2 : ℝ) : ℂ) * (p x.1 * u x.2 + q x.1 * v x.2) = Ψ x
  change ((1 / Real.sqrt 2 : ℝ) : ℂ) * (u x.2 * p x.1 + v x.2 * q x.1) = Ψ x at hh
  simpa only [mul_comm] using hh

end Qatlib.Concepts.QuditTeleport.ResourceIff
