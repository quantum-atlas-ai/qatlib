/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.GridExactHHL.LinearSystem
import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation

/-!
# Restricted spectral HHL specification

`SpecRestrictedSubgoal` states exact phase-estimation readout for eigenvectors with grid-aligned
eigenphases and existence of a spectral inverse solution. It records the inverse coefficient
formula and its positive inverse-square lower bound in the setting motivated by
[HarrowHassidimLloyd2009].

## Main statements

* `SpecRestrictedSubgoal`: the exact readout and spectral-solution contract.

## References

* [Harrow, Hassidim, and Lloyd, 2009][HarrowHassidimLloyd2009]
-/

open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Matrix

namespace Qatlib.Concepts.HhlAlgorithms.GridExactHHL

/-- The exact-grid spectral contract asserting probability-one phase readout for each
eigenvector and a linear-system solution given by inverse-eigenvalue coefficients, whose
squared coefficient norm is positive and at least `1 / κ²`. -/
def SpecRestrictedSubgoal : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (p : LinearSystemProblem I)
    (M : ℕ), 0 < M →
    ∀ (U : Matrix I I ℂ), U ∈ Matrix.unitaryGroup I ℂ →
    ∀ (g : I → Fin M),
      (∀ i, U *ᵥ (p.eigvec i) = (primRoot M ^ ((g i).val : ℤ)) • (p.eigvec i)) →
      (∀ i, Complex.exp ((p.eigval i : ℂ) * Complex.I) = primRoot M ^ ((g i).val : ℤ)) →
    ∀ (β : I → ℂ), p.b = ∑ i, β i • p.eigvec i →
    (∀ i,
      ApplyGate (TensorGate (QFTMatrix M)ᴴ (1 : Matrix I I ℂ))
          (ControlledPowers U M *ᵥ TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹)
            (p.eigvec i))
        = TensorState (Ket (g i)) (p.eigvec i) ∧
      MeasureProb (ApplyGate (TensorGate (QFTMatrix M)ᴴ (1 : Matrix I I ℂ))
          (ControlledPowers U M *ᵥ TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹)
            (p.eigvec i)))
        ({(g i)} ×ˢ (Finset.univ : Finset I)) = 1) ∧
    ∃ (x : QState I) (s : ℝ), 0 < s ∧
      p.A *ᵥ x = p.b ∧
      1 / p.κ ^ 2 ≤ s ∧
      s = ∑ i, ‖β i / ((p.eigval i : ℂ))‖ ^ 2 ∧
      x = ∑ i, (β i / ((p.eigval i : ℂ))) • p.eigvec i

end Qatlib.Concepts.HhlAlgorithms.GridExactHHL
