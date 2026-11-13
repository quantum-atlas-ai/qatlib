/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Papers.ChemDynamics08.MainResults.Readout.ReactionReadout

/-!
# State-to-state readout

`expandState` forms a finite linear combination of states. For an orthonormal family, the module
recovers the expansion coefficients as inner products and identifies their squared norms as
transition probabilities. It also supplies normalization and a scalar phase-estimation precision
bound.

These constructions support the treatment in [KassalEtAl2008].

## Main statements

* `state_to_state_probability`: identifies the squared transition amplitudes and their unit sum.
* `normalized_expandState`: proves normalization from orthonormality and normalized
  coefficients.

## References

* [Kassal et al., 2008][KassalEtAl2008]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Matrix
open scoped BigOperators
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.ChemDynamics08.MainResults.Readout

/-- The finite linear combination of the states `ξ v` with complex coefficients `α v`. -/
noncomputable def expandState {X ι : Type*} [Fintype ι]
    (ξ : ι → QState X) (α : ι → ℂ) : QState X :=
  fun x => ∑ v, α v * ξ v x

/-- The pointwise state expansion equals the sum of scalar multiples of the component states. -/
theorem expandState_eq_sum_smul {X ι : Type*} [Fintype ι]
    (ξ : ι → QState X) (α : ι → ℂ) :
    expandState ξ α = ∑ v, α v • ξ v := by
  funext x
  simp [expandState, Finset.sum_apply]

/-- Taking the inner product with a member of an orthonormal family recovers its coefficient in
the expansion [KassalEtAl2008]. -/
theorem inner_expandState {X ι : Type*} [Fintype X] [Fintype ι] [DecidableEq ι]
    (ξ : ι → QState X) (α : ι → ℂ)
    (horth : ∀ v w : ι, Inner (ξ v) (ξ w) = if v = w then 1 else 0) (w : ι) :
    Inner (ξ w) (expandState ξ α) = α w := by
  rw [expandState_eq_sum_smul]
  show star (ξ w) ⬝ᵥ (∑ v, α v • ξ v) = α w
  have h' : ∀ v w : ι, star (ξ v) ⬝ᵥ ξ w = if v = w then 1 else 0 := fun v w => horth v w
  rw [dotProduct_sum]
  rw [Finset.sum_eq_single w]
  · rw [dotProduct_smul, smul_eq_mul, h' w w, if_pos rfl, mul_one]
  · intro v _ hv
    rw [dotProduct_smul, smul_eq_mul, h' w v, if_neg (fun h : w = v => hv h.symm),
      mul_zero]
  · intro h
    exact absurd (Finset.mem_univ w) h

/-- For orthonormal component states and coefficients of total squared norm one, the squared
transition amplitudes equal the squared coefficient norms and sum to one [KassalEtAl2008]. -/
theorem state_to_state_probability {X ι : Type*} [Fintype X] [Fintype ι] [DecidableEq ι]
    (ξ : ι → QState X) (α : ι → ℂ)
    (horth : ∀ v w : ι, Inner (ξ v) (ξ w) = if v = w then 1 else 0)
    (hα : ∑ v, ‖α v‖ ^ 2 = 1) :
    (∀ v : ι, ‖Inner (ξ v) (expandState ξ α)‖ ^ 2 = ‖α v‖ ^ 2) ∧
    (∑ v : ι, ‖Inner (ξ v) (expandState ξ α)‖ ^ 2 = 1) := by
  refine ⟨fun v => by rw [inner_expandState ξ α horth v], ?_⟩
  calc ∑ v : ι, ‖Inner (ξ v) (expandState ξ α)‖ ^ 2
      = ∑ v : ι, ‖α v‖ ^ 2 :=
        Finset.sum_congr rfl fun v _ => by rw [inner_expandState ξ α horth v]
    _ = 1 := hα

/-- An expansion in an orthonormal family is normalized when its coefficients have total squared
norm one. -/
theorem normalized_expandState {X ι : Type} [Fintype X] [Fintype ι]
    [DecidableEq X] [DecidableEq ι]
    (ξ : ι → QState X) (α : ι → ℂ)
    (horth : ∀ v w : ι, Inner (ξ v) (ξ w) = if v = w then 1 else 0)
    (hα : ∑ v, ‖α v‖ ^ 2 = 1) :
    Normalized (expandState ξ α) := by

  have horth' : ∀ v w : ι,
      Inner (ξ v) (ξ w) = @ite ℂ (v = w) (Classical.propDecidable _) 1 0 := by
    intro v w
    rw [horth v w]
    by_cases h : v = w <;> simp [h]
  unfold Normalized
  have h := sum_norm_sq_orthonormal ξ α horth'
  rw [expandState_eq_sum_smul]
  exact h.trans hα

/-- For every positive tolerance, some positive integer `M` makes the scalar bound `2π / M + π²
/ M²` at most that tolerance [KassalEtAl2008]. -/
theorem state_to_state_phase_estimation_precision (eps : ℝ) (heps : 0 < eps) :
    ∃ M : ℕ, 0 < M ∧
      2 * Real.pi / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2 ≤ eps :=
  amplitude_estimation_precision_guarantee eps heps

end Qatlib.Papers.ChemDynamics08.MainResults.Readout
