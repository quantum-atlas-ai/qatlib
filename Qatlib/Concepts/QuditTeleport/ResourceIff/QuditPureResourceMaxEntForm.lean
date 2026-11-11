/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditPureResourceMaxEntForm
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditResourceMarginalConverse
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditMaxEntCharacterization

/-!
# Maximally entangled form of pure teleportation resources

`quditPureResourceMaxEntForm` combines the resource marginal converse with the characterization
of pure vectors having maximally mixed marginals. A normalized pure resource supporting fixed
correction teleportation is therefore expressible as an equal weight sum of paired orthonormal
vectors.

This is the qudit resource form corresponding to the pure resource discussion in
[BennettEtAl1993Teleportation].

## Main statements

* `quditPureResourceMaxEntForm`: derives the orthonormal family form of a pure teleportation
  resource.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option warningAsError false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.QuditTeleport.QdLoccModel

namespace Qatlib.Concepts.QuditTeleport.ResourceIff
open Matrix
open scoped Classical BigOperators ComplexOrder

/-- A normalized pure qudit resource supporting fixed unitary correction teleportation can be
written as a maximally entangled vector built from two orthonormal families
[BennettEtAl1993Teleportation]. -/
theorem quditPureResourceMaxEntForm : QuditPureResourceMaxEntForm := by
  intro n _ K U Ψ hΨ htele
  let e := Equiv.prodComm (Fin n) (Fin n)
  let Φ := relabelState e Ψ
  have hΦ : Normalized Φ := normalized_relabelState e hΨ
  have hswap : outerProduct Φ = relabelGate e (outerProduct Ψ) := by ext i j; rfl
  have hb := quditResourceMarginalConverse n K U (outerProduct Ψ)
    (outerProduct_posSemidef Ψ) htele
  have hΦb : PartialTrace (outerProduct Φ) = (1 / (n : ℂ)) • (1 : Operator n) := by
    rw [hswap]
    exact hb
  obtain ⟨u,v,hu,hv,he⟩ := quditMaxEntCharacterization.2 n Φ hΦ hΦb
  refine ⟨v,u,hv,hu,?_⟩
  funext x
  have h := congrFun he (x.2,x.1)
  change (Real.sqrt (n : ℝ) : ℂ)⁻¹ * ∑ j, u j x.2 * v j x.1 = Ψ x at h
  simpa only [quditMaxEntResource, mul_comm] using h

end Qatlib.Concepts.QuditTeleport.ResourceIff
