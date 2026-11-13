/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LinDynamics23.DiscreteObs.Proposition20HybridObservableBiasStat

/-!
# Sampling definitions for hybrid observables

`hybridObservableSampleDist` samples pairs of reconstruction indices in proportion to the
product of their coefficient norms. The corresponding real sample value
`hybridObservableSampleValue` removes these norm factors from the pairwise observable
expression, using zero at vanishing coefficients; `hybridObservableGroupDist` forms independent
finite sample groups. See [AnChildsLin2026] for the paper context.

## Main statements

* `hybridObservableSampleDist`: The finite distribution on index pairs with probability `‖c l‖ *
  ‖c j‖ / (∑ i, ‖c i‖) ^ 2`, defined when the coefficient-norm sum is positive.
* `hybridObservableSampleValue`: The real part of the coefficient-weighted pairwise observable
  matrix element divided by the product of coefficient norms, with value zero when that product
  vanishes.
* `hybridObservableGroupDist`: The product distribution of `L` independent samples from the
  finite distribution `p`.

## References

* [An et al., 2026][AnChildsLin2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

variable {N : ℕ}

namespace Qatlib.Papers.LinDynamics23.DiscreteObs

/-- The finite distribution on index pairs with probability `‖c l‖ * ‖c j‖ / (∑ i, ‖c i‖) ^ 2`,
defined when the coefficient-norm sum is positive. -/
noncomputable def hybridObservableSampleDist (c : Fin N → ℂ) (hγ : 0 < ∑ j, ‖c j‖) :
    FinDist (Fin N × Fin N) where
  prob x := ‖c x.1‖ * ‖c x.2‖ / (∑ j, ‖c j‖) ^ 2
  nonneg x := by positivity
  sum_one := by
    have hprod : (∑ x : Fin N × Fin N, ‖c x.1‖ * ‖c x.2‖) =
        (∑ j, ‖c j‖) * (∑ j, ‖c j‖) := by
      rw [Fintype.sum_prod_type]
      exact (Fintype.sum_mul_sum (fun j => ‖c j‖) (fun j => ‖c j‖)).symm
    rw [← Finset.sum_div, hprod, div_eq_one_iff_eq (ne_of_gt (pow_pos hγ 2))]
    ring

/-- The real part of the coefficient-weighted pairwise observable matrix element divided by the
product of coefficient norms, with value zero when that product vanishes. -/
noncomputable def hybridObservableSampleValue {I : Type} [Fintype I] [DecidableEq I]
    (c : Fin N → ℂ) (W : Fin N → Matrix I I ℂ) (O : Matrix I I ℂ)
    (x₀ : QState I) (x : Fin N × Fin N) : ℝ :=
  if ‖c x.1‖ * ‖c x.2‖ = 0 then 0
  else Complex.re (star (c x.1) * c x.2 *
      Inner (W x.1 *ᵥ x₀) (O.mulVec (W x.2 *ᵥ x₀))) / (‖c x.1‖ * ‖c x.2‖)

/-- The product distribution of `L` independent samples from the finite distribution `p`. -/
def hybridObservableGroupDist {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (L : ℕ) : FinDist (Fin L → X) :=
  ⟨p.probOf, fun _ => Finset.prod_nonneg fun _ _ => p.nonneg _, p.sum_probOf L⟩
end Qatlib.Papers.LinDynamics23.DiscreteObs
