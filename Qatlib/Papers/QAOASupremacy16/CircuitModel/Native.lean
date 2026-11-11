/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOASupremacy16.CircuitModel.Source
import Qatlib.Foundations.MatrixAlgebra.PhaseUnitary

/-!
# Normalization and uniformity at zero mixer angle

The cost phase gate is unitary for every real angle and natural-valued cost function. Applying
it to the uniform Hadamard input gives normalized `betaZeroState` with exactly uniform
computational-basis Born probabilities and total mass one.

This development accompanies the study of QAOA sampling and postselection in [FarhiHarrow2016].

## Main statements

* `betaZero_normalized`: The state obtained by applying the cost phase to the uniform Hadamard
  input is normalized.
* `betaZero_uniform_born`: Every computational-basis output of `betaZeroState` has Born
  probability `(2^n)⁻¹`.

## References

* [Farhi and Harrow, 2016][FarhiHarrow2016]
-/

set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Papers.QAOASupremacy16.CircuitDefs
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.MatrixAlgebra.PhaseUnitary
open scoped BigOperators

/-- The diagonal cost phase gate is unitary for every real angle and natural-valued cost
function. See [FarhiHarrow2016]. -/
theorem phaseGate_unitary {n : ℕ} (γ : ℝ) (C : Reg n→ℕ) :
    phaseGate γ C ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  simpa only [phaseGate,Complex.ofReal_neg,Complex.ofReal_mul] using
      real_phase_unitary (fun z=> -(γ*(C z:ℝ)))

/-- The state obtained by applying the cost phase to the uniform Hadamard input is normalized.
See [FarhiHarrow2016]. -/
theorem betaZero_normalized {n : ℕ} (γ : ℝ) (C : Reg n→ℕ) :
    Normalized (betaZeroState γ C) :=
  normalized_applyGate (phaseGate_unitary γ C)
    (normalized_applyGate (hadamardN_unitary n) (normalized_ket (ZeroStr n)))

/-- Every computational-basis output of `betaZeroState` has Born probability `(2^n)⁻¹`. See
[FarhiHarrow2016]. -/
theorem betaZero_uniform_born {n : ℕ} (γ : ℝ) (C : Reg n→ℕ) (z : Reg n) :
    BornProb (betaZeroState γ C) z = ((2:ℝ)^n)⁻¹ := by
  unfold BornProb
  have hp : ‖Complex.exp (-((γ:ℂ)*((C z:ℝ):ℂ))*Complex.I)‖=1 := by
    simpa only [Complex.ofReal_neg,Complex.ofReal_mul] using exp_phase_norm (-(γ*(C z:ℝ)))
  rw [betaZeroState_apply,norm_mul,hp,one_mul,norm_pow,norm_inv,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg 2)]
  rw [← pow_mul,show n*2=2*n by omega,pow_mul,inv_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  rw [inv_pow]

/-- The computational-basis Born probabilities of `betaZeroState` sum to one. See
[FarhiHarrow2016]. -/
theorem betaZero_born_total {n : ℕ} (γ : ℝ) (C : Reg n→ℕ) :
    ∑ z, BornProb (betaZeroState γ C) z = 1 := betaZero_normalized γ C
end Qatlib.Papers.QAOASupremacy16.CircuitDefs
