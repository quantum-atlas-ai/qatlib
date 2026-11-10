/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LinDynamics23.DiscreteObs.Proposition20HybridObservableBiasStat
set_option warningAsError false
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

noncomputable def hybridObservableSampleValue {I : Type} [Fintype I] [DecidableEq I]
    (c : Fin N → ℂ) (W : Fin N → Matrix I I ℂ) (O : Matrix I I ℂ)
    (x₀ : QState I) (x : Fin N × Fin N) : ℝ :=
  if ‖c x.1‖ * ‖c x.2‖ = 0 then 0
  else Complex.re (star (c x.1) * c x.2 *
      Inner (W x.1 *ᵥ x₀) (O.mulVec (W x.2 *ᵥ x₀))) / (‖c x.1‖ * ‖c x.2‖)

def hybridObservableGroupDist {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (L : ℕ) : FinDist (Fin L → X) :=
  ⟨p.probOf, fun _ => Finset.prod_nonneg fun _ _ => p.nonneg _, p.sum_probOf L⟩
end Qatlib.Papers.LinDynamics23.DiscreteObs
