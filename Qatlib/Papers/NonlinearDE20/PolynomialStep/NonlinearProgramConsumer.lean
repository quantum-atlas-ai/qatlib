/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinearDE20.PolynomialStep.PolynomialForcingInteraction
import Qatlib.Papers.NonlinearDE20.PolynomialStep.PositiveNormalization
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

def polynomialProgramReduced {I : Type} [Fintype I] [DecidableEq I] (m : ℕ) (A : Matrix I I ℂ)
    (B : Matrix (I×(Fin m→I)) (I×(Fin m→I)) ℂ) (b x : I→ℂ) (dt : ℂ) : Matrix I I ℂ :=
  (outer (originalTargetSelector*ᵥ ((1+dt •forcedInteraction A B b)*ᵥ
    inflate (tensorPower m x) (homogenize x)))).traceRight

def polynomialNoiseMass {I : Type} [Fintype I] (m : ℕ)
    (B : Matrix (I×(Fin m→I)) (I×(Fin m→I)) ℂ) (x : I→ℂ) (dt : ℂ) : ℝ :=
  Complex.normSq dt*∑ p : I×(Fin m→I),
    Complex.normSq (entanglingResidual (tensorPower m x) (B*ᵥ inflate (tensorPower m x) x) p)

theorem polynomialProgram_variance {I : Type} [Fintype I] [DecidableEq I] (m : ℕ) (A : Matrix I I ℂ)
    (B : Matrix (I×(Fin m→I)) (I×(Fin m→I)) ℂ) (b x : I→ℂ) (dt : ℂ)
    (hx : (∑ i : I,Complex.normSq (x i))=1) :
    polynomialProgramReduced m A B b x dt-outer (x+dt •polynomialField m A B b x)=
      (dt*star dt) •reducedVariance (tensorPower m x) (B*ᵥ inflate (tensorPower m x) x) := by
  rw [polynomialProgramReduced,forced_polynomial_program]
  exact polynomialEuler_variance m A B b x dt hx

theorem polynomialProgram_difference_psd {I : Type} [Fintype I] [DecidableEq I] (m : ℕ) (A : Matrix I I ℂ)
    (B : Matrix (I×(Fin m→I)) (I×(Fin m→I)) ℂ) (b x : I→ℂ) (dt : ℂ)
    (hx : (∑ i : I,Complex.normSq (x i))=1) :
    (polynomialProgramReduced m A B b x dt-outer (x+dt •polynomialField m A B b x)).PosSemidef := by
  have hc : dt*star dt=(Complex.normSq dt:ℂ) :=Complex.mul_conj dt
  rw [polynomialProgram_variance m A B b x dt hx,hc]
  exact (reducedVariance_psd _ (environmentPower_normalized m x hx) _).smul
    (RCLike.ofReal_nonneg.mpr (Complex.normSq_nonneg dt))

theorem polynomialProgram_traceNorm {I : Type} [Fintype I] [DecidableEq I] (m : ℕ) (A : Matrix I I ℂ)
    (B : Matrix (I×(Fin m→I)) (I×(Fin m→I)) ℂ) (b x : I→ℂ) (dt : ℂ)
    (hx : (∑ i : I,Complex.normSq (x i))=1) :
    (polynomialProgramReduced m A B b x dt-outer (x+dt •polynomialField m A B b x)).traceNorm=
      polynomialNoiseMass m B x dt := by
  rw [polynomialProgram_variance m A B b x dt hx,Matrix.traceNorm_smul,
    reducedVariance_traceNorm _ (environmentPower_normalized m x hx),norm_mul,norm_star,← pow_two,Complex.sq_norm]
  rfl

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
