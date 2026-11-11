/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinearDE20.PolynomialStep.PolynomialForcingInteraction
import Qatlib.Papers.NonlinearDE20.PolynomialStep.PositiveNormalization

/-!
# Variance and normalized error of the polynomial program

The matrix `polynomialProgramReduced` is obtained by applying the affine lifted interaction,
selecting the original target coordinates, and tracing out the tensor-power environment. For
normalized input, its difference from the polynomial Euler outer product is a positive variance
term. The resulting exact noise mass and normalized error bound support the step analysis of
[LloydEtAl2020].

## Main statements

* `polynomialProgram_variance`: For normalized `x`, the polynomial program discrepancy equals
  `dt * star dt` times the reduced interaction variance.
* `polynomialProgram_traceNorm`: For normalized `x`, the polynomial program trace-norm
  discrepancy is exactly `polynomialNoiseMass`.
* `polynomialProgram_normalized_error`: For normalized input and positive target trace, the
  normalized polynomial program error is at most twice the noise mass divided by target mass
  plus noise mass.

## References

* [Lloyd et al., 2020][LloydEtAl2020]
-/

set_option warningAsError false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
open scoped BigOperators Classical ComplexOrder
open Matrix
open Qatlib.Papers.NonlinearDE20.AffineLift.Model

open Qatlib.Concepts.TensorRegisters.RegisterModel.EnvironmentFrame

namespace Qatlib.Papers.NonlinearDE20.PolynomialStep.Model

/-- The reduced outer product of the selected original target coordinates after the lifted
forced polynomial Euler update. -/
def polynomialProgramReduced {I : Type} [Fintype I] [DecidableEq I] (m : ℕ) (A : Matrix I I ℂ)
    (B : Matrix (I×(Fin m→I)) (I×(Fin m→I)) ℂ) (b x : I→ℂ) (dt : ℂ) : Matrix I I ℂ :=
  (outer (originalTargetSelector*ᵥ ((1+dt •forcedInteraction A B b)*ᵥ
    inflate (tensorPower m x) (homogenize x)))).traceRight

/-- The squared time-step modulus times the squared norm of the interaction residual relative to
the tensor-power environment. -/
def polynomialNoiseMass {I : Type} [Fintype I] (m : ℕ)
    (B : Matrix (I×(Fin m→I)) (I×(Fin m→I)) ℂ) (x : I→ℂ) (dt : ℂ) : ℝ :=
  Complex.normSq dt*∑ p : I×(Fin m→I),
    Complex.normSq (entanglingResidual (tensorPower m x) (B*ᵥ inflate (tensorPower m x) x) p)

/-- For normalized `x`, the polynomial program discrepancy equals `dt * star dt` times the
reduced interaction variance [LloydEtAl2020]. -/
theorem polynomialProgram_variance {I : Type} [Fintype I] [DecidableEq I] (m : ℕ) (A : Matrix I I ℂ)
    (B : Matrix (I×(Fin m→I)) (I×(Fin m→I)) ℂ) (b x : I→ℂ) (dt : ℂ)
    (hx : (∑ i : I,Complex.normSq (x i))=1) :
    polynomialProgramReduced m A B b x dt-outer (x+dt •polynomialField m A B b x)=
      (dt*star dt) •reducedVariance (tensorPower m x) (B*ᵥ inflate (tensorPower m x) x) := by
  rw [polynomialProgramReduced,forced_polynomial_program]
  exact polynomialEuler_variance m A B b x dt hx

/-- For normalized `x`, the polynomial program output minus the polynomial Euler outer product
is positive semidefinite [LloydEtAl2020]. -/
theorem polynomialProgram_difference_psd {I : Type} [Fintype I] [DecidableEq I] (m : ℕ) (A : Matrix I I ℂ)
    (B : Matrix (I×(Fin m→I)) (I×(Fin m→I)) ℂ) (b x : I→ℂ) (dt : ℂ)
    (hx : (∑ i : I,Complex.normSq (x i))=1) :
    (polynomialProgramReduced m A B b x dt-outer (x+dt •polynomialField m A B b x)).PosSemidef := by
  have hc : dt*star dt=(Complex.normSq dt:ℂ) :=Complex.mul_conj dt
  rw [polynomialProgram_variance m A B b x dt hx,hc]
  exact (reducedVariance_psd _ (environmentPower_normalized m x hx) _).smul
    (RCLike.ofReal_nonneg.mpr (Complex.normSq_nonneg dt))

/-- For normalized `x`, the polynomial program trace-norm discrepancy is exactly
`polynomialNoiseMass`. -/
theorem polynomialProgram_traceNorm {I : Type} [Fintype I] [DecidableEq I] (m : ℕ) (A : Matrix I I ℂ)
    (B : Matrix (I×(Fin m→I)) (I×(Fin m→I)) ℂ) (b x : I→ℂ) (dt : ℂ)
    (hx : (∑ i : I,Complex.normSq (x i))=1) :
    (polynomialProgramReduced m A B b x dt-outer (x+dt •polynomialField m A B b x)).traceNorm=
      polynomialNoiseMass m B x dt := by
  rw [polynomialProgram_variance m A B b x dt hx,Matrix.traceNorm_smul,
    reducedVariance_traceNorm _ (environmentPower_normalized m x hx),norm_mul,norm_star,← pow_two,Complex.sq_norm]
  rfl

/-- For normalized input and positive target trace, the normalized polynomial program error is
at most twice the noise mass divided by target mass plus noise mass [LloydEtAl2020]. -/
theorem polynomialProgram_normalized_error {I : Type} [Fintype I] [DecidableEq I] (m : ℕ) (A : Matrix I I ℂ)
    (B : Matrix (I×(Fin m→I)) (I×(Fin m→I)) ℂ) (b x : I→ℂ) (dt : ℂ)
    (hx : (∑ i : I,Complex.normSq (x i))=1) (hp : 0<(outer (x+dt •polynomialField m A B b x)).trace.re) :
    (normalizePositive (polynomialProgramReduced m A B b x dt)-
      normalizePositive (outer (x+dt •polynomialField m A B b x))).traceNorm≤
        2*polynomialNoiseMass m B x dt/
          ((outer (x+dt •polynomialField m A B b x)).trace.re+polynomialNoiseMass m B x dt) := by
  let P:=outer (x+dt •polynomialField m A B b x)
  let V:=polynomialProgramReduced m A B b x dt-P
  have hP : P.PosSemidef :=Matrix.posSemidef_vecMulVec_self_star _
  have hV : V.PosSemidef :=polynomialProgram_difference_psd m A B b x dt hx
  have hv : V.trace.re=polynomialNoiseMass m B x dt := by
    rw [← positive_traceNorm V hV]
    exact polynomialProgram_traceNorm m A B b x dt hx
  have he : polynomialProgramReduced m A B b x dt=P+V :=by dsimp [V];abel
  have h:=positive_add_normalization P V hP hV hp
  rw [← he,hv] at h
  exact h

end Qatlib.Papers.NonlinearDE20.PolynomialStep.Model
