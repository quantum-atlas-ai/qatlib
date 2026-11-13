/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditMaxEntCharacterization
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditMaxEntTools

/-!
# Maximally entangled qudit resource characterization

`quditMaxEntCharacterization` relates the orthonormal family form of a pure qudit resource to
its reduced operators. The forward direction gives maximally mixed marginals on both subsystems,
and the converse constructs such families from a normalized vector with maximally mixed first
marginal.

This is the finite dimensional resource characterization underlying the teleportation discussion
in [BennettEtAl1993Teleportation].

## Main statements

* `quditMaxEntCharacterization`: proves the bundled marginal and orthonormal family
  characterization.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.QuditTeleport.QdLoccModel

namespace Qatlib.Concepts.QuditTeleport.ResourceIff
open Matrix
open scoped Classical BigOperators

/-- Maximally entangled vectors formed from orthonormal families have maximally mixed marginals,
and a normalized pure vector with maximally mixed first marginal has this form. This is the
qudit version of the resource form in [Bennett et al., Eq.
(9)][BennettEtAl1993Teleportation]. -/
theorem quditMaxEntCharacterization : QuditMaxEntCharacterization := by
  constructor
  · intro n _ u v hu hv
    refine ⟨qudit_maxEnt_first_marginal hu hv, ?_⟩
    have hs : relabelGate (Equiv.prodComm (Fin n) (Fin n))
        (outerProduct (quditMaxEntResource n u v)) =
        outerProduct (quditMaxEntResource n v u) := by
      ext ⟨i,j⟩ ⟨k,l⟩
      simp [relabelGate, outerProduct_apply, quditMaxEntResource, mul_comm]
    rw [hs]
    exact qudit_maxEnt_first_marginal hv hu
  · intro n _ Ψ _ hΨ
    refine ⟨Ket, (fun j k => (Real.sqrt (n : ℝ) : ℂ) * Ψ (j,k)),
      inner_ket_ket, qudit_scaled_rows_orthonormal Ψ hΨ, ?_⟩
    funext x
    simp only [quditMaxEntResource, Ket, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← mul_assoc, inv_mul_cancel₀ (qudit_sqrt_ne_zero n), one_mul]

end Qatlib.Concepts.QuditTeleport.ResourceIff
