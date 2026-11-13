/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Weighted Gram-state readout

This module defines `gramState`, the bipartite vector recording a state label together with its
real-weighted component state. `gramColumn` uses conjugated component amplitudes, and
`gramMatrix` is its adjoint-product Gram matrix, matching the first-register reduced operator.

For normalized component states and nonnegative weights whose squares sum to one,
`gramFirstRegisterDensity` proves normalization of the bipartite vector, identifies its reduced
matrix, and establishes the density-operator property. This supplies a Gram-state construction
associated with quantum principal component analysis [LloydMohseniRebentrost2014].

## Main statements

* `gramColumn`: the weighted conjugate-column matrix.
* `gramMatrix`: its adjoint-product Gram matrix.
* `gramFirstRegisterDensity`: normalization and the first-register density identity.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace Qatlib.Concepts.CopyEvolution.GramReadout
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Matrix
open scoped Classical BigOperators ComplexOrder

/-- The matrix whose `i`th column is the complex conjugate of `ψ i`, multiplied by the real
weight `w i`. -/
noncomputable def gramColumn {r d : ℕ} (ψ : Fin r → QState (Fin d)) (w : Fin r → ℝ) :
    Matrix (Fin d) (Fin r) ℂ := fun x i => (w i : ℂ) * (starRingEnd ℂ) (ψ i x)

/-- The weighted Gram matrix `(gramColumn ψ w)ᴴ * gramColumn ψ w`. -/
noncomputable def gramMatrix {r d : ℕ} (ψ : Fin r → QState (Fin d)) (w : Fin r → ℝ) :
    Operator r := (gramColumn ψ w)ᴴ * gramColumn ψ w

/-- The bipartite vector with amplitudes `w i * ψ i x`, recording a state label in the first
register. -/
noncomputable def gramState {r d : ℕ} (ψ : Fin r → QState (Fin d)) (w : Fin r → ℝ) :
    QState (Fin r × Fin d) := fun p => (w p.1 : ℂ) * ψ p.1 p.2

/-- For normalized component states and nonnegative weights with squared sum one, `gramState` is
normalized and its first-register reduced density matrix is `gramMatrix ψ w`. This gives the
Gram-state construction used in [LloydMohseniRebentrost2014]. -/
theorem gramFirstRegisterDensity :
  ∀ (r d : ℕ) (ψ : Fin r → QState (Fin d)), (∀ i, Normalized (ψ i)) →
    ∀ (w : Fin r → ℝ), (∀ i, 0 ≤ w i) → (∑ i, (w i) ^ 2 = 1) →
    Normalized (gramState ψ w) ∧
    PartialTrace (outerProduct (gramState ψ w)) = gramMatrix ψ w ∧
    IsDensityOperator (gramMatrix ψ w) := by
  intro r d ψ hψ w hw hsumw
  have hnψ (i : Fin r) : (∑ x : Fin d, ‖ψ i x‖^2) = 1 := hψ i
  have hterm (i : Fin r) (x : Fin d) : ‖gramState ψ w (i,x)‖^2 = (w i)^2*‖ψ i x‖^2 := by
    rw [gramState, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (hw i)]
  have hnormalized : Normalized (gramState ψ w) := by
    change (∑ p : Fin r × Fin d, ‖gramState ψ w p‖^2) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [hterm, ← Finset.mul_sum, hnψ, mul_one]
    exact hsumw
  have hmarginal : PartialTrace (outerProduct (gramState ψ w)) = gramMatrix ψ w := by
    ext i j
    simp only [PartialTrace, outerProduct, gramState, gramMatrix, gramColumn,
      Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    apply Finset.sum_congr rfl
    intro x _
    simp only [map_mul, RCLike.star_def, Complex.conj_ofReal, Complex.conj_conj]
  have htrace : Matrix.trace (gramMatrix ψ w) = 1 := by
    rw [← hmarginal, trace_partialTrace]
    change (∑ p : Fin r × Fin d, gramState ψ w p*(starRingEnd ℂ) (gramState ψ w p)) = 1
    have he (p : Fin r × Fin d) : gramState ψ w p*(starRingEnd ℂ) (gramState ψ w p) =
        ((‖gramState ψ w p‖^2 : ℝ) : ℂ) := by
      simpa only [Complex.normSq_eq_norm_sq] using Complex.mul_conj (gramState ψ w p)
    simp_rw [he]
    have hs : ((∑ p : Fin r × Fin d, ‖gramState ψ w p‖^2 : ℝ) : ℂ) = 1 := by
      have hn : (∑ p : Fin r × Fin d, ‖gramState ψ w p‖^2) = 1 := hnormalized
      exact_mod_cast hn
    simpa only [Complex.ofReal_sum] using hs
  exact ⟨hnormalized, hmarginal, Matrix.posSemidef_conjTranspose_mul_self (gramColumn ψ w), htrace⟩

end Qatlib.Concepts.CopyEvolution.GramReadout
