/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.SegmentProduct.SegmentProductPerturbation
import Qatlib.Concepts.LchsSimulation.TimeOrdered.TimeOrderedConsumers

/-!
# InteractionPictureIdentities — Eq. (12) and Eq. (18) of InteractPic18

Low--Wiebe, *Hamiltonian Simulation in the Interaction Picture*,
fixed arXiv:1805.00675v2.

This module records the two structural identities the paper relies on before
it discusses any truncation: the interaction-picture factorization of
Eq. (18) (Section IV, p. 7) and the product-perturbation bound of Eq. (12)
(Section III.B, p. 5). Both are proved by reusing the frozen matrix-level
results verbatim; no numerical algorithm cost is asserted here.

Boundary: these are exact matrix identities. They do not provide the
truncation error, the grid discretization error, or any gate/query count.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Matrix
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.InteractionEvo.SegmentProduct
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.InteractPic18.MainResults.InteractionPicture

/-- Fixed arXiv:1805.00675v2, Eq. (17): the interaction-picture generator
`H_I(s) = e^{iAs} B e^{-iAs}` of a time-independent perturbation `B`. -/
noncomputable def interactionPictureGenerator {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (s : ℝ) : Matrix I I ℂ :=
  HamiltonianEvolution A (-s) * B * HamiltonianEvolution A s

/-- The paper's generator `H_I(s)` is the frozen `interactionGenerator`. -/
theorem interactionPictureGenerator_eq {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) :
    interactionPictureGenerator A B = interactionGenerator A (fun _ => B) :=
  rfl

/-- Fixed arXiv:1805.00675v2, Eq. (18) (Section IV, p. 7): the exact
interaction-picture identity
`e^{-iAt} T[e^{-i ∫_0^t H_I(s) ds}] = e^{-i(A+B)t}`,
stated with the paper's `H_I` and the frozen time-ordered evolution. -/
theorem eq18_interaction_picture_identity {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) (t : ℝ) :
    HamiltonianEvolution (A + B) t =
      HamiltonianEvolution A t *
        orderedEvolution (fun u => Complex.I • interactionPictureGenerator A B u) 0 t := by
  have h := ordered_interaction_picture_identity I A (fun _ => B) hA continuous_const
    (fun _ => hB) t
  have hc : orderedEvolution (fun u => Complex.I • (A + (fun _ => B) u)) 0 t
      = HamiltonianEvolution (A + B) t := by
    simpa using orderedEvolution_constant_hamiltonian (A + B) 0 t
  rw [hc] at h
  exact h

/-- Fixed arXiv:1805.00675v2, Eq. (18), contrapositive reading: applying the
time-ordered interaction-picture evolution on the left by `e^{-iAt}` recovers
the full evolution. This is the form quoted in the algorithm analysis. -/
theorem eq18_interaction_picture_identity' {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) (t : ℝ) :
    HamiltonianEvolution A t *
        orderedEvolution (fun u => Complex.I • interactionPictureGenerator A B u) 0 t
      = HamiltonianEvolution (A + B) t :=
  (eq18_interaction_picture_identity A B hA hB t).symm

/-- Fixed arXiv:1805.00675v2, Eq. (12) (Section III.B, p. 5): for a product of
`M` contractive factors the perturbation of the ordered product is bounded by
the sum of the individual factor errors. `List.range M` product keeps the
first factor on the left, matching the paper's ordering. -/
theorem eq12_product_perturbation {I : Type} [Fintype I] [DecidableEq I]
    (U V : ℕ → Matrix I I ℂ) (M : ℕ)
    (hU : ∀ j < M, ‖U j‖ ≤ 1) (hV : ∀ j < M, ‖V j‖ ≤ 1) :
    ‖((List.range M).map U).prod - ((List.range M).map V).prod‖ ≤
      ∑ k ∈ Finset.range M, ‖U k - V k‖ :=
  segment_product_perturbation_contraction_sum I U V M hU hV

/-- Fixed arXiv:1805.00675v2, Eq. (12), refined "sandwich" form used in the
proof of Corollary 4: each factor is charged the norm of the already-applied
`U` suffix and the not-yet-applied `V` prefix. No contraction is required. -/
theorem eq12_product_perturbation_sandwich {I : Type} [Fintype I] [DecidableEq I]
    (U V : ℕ → Matrix I I ℂ) (M : ℕ) :
    ‖((List.range M).map U).prod - ((List.range M).map V).prod‖ ≤
      ∑ k ∈ Finset.range M,
        (∏ j ∈ Finset.filter (fun j => k < j) (Finset.range M), ‖U j‖) *
        ‖U k - V k‖ *
        (∏ j ∈ Finset.filter (fun j => j < k) (Finset.range M), ‖V j‖) :=
  segment_product_perturbation_sandwich I U V M

end Qatlib.Papers.InteractPic18.MainResults.InteractionPicture
