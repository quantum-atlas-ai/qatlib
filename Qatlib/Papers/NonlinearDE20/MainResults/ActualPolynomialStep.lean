/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinearDE20.MainResults.ClassicalEuler
import Qatlib.Papers.NonlinearDE20.PolynomialStep.NonlinearProgramConsumer
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical ComplexOrder

open Qatlib.Concepts.TensorRegisters.RegisterModel.EnvironmentFrame

namespace Qatlib.Papers.NonlinearDE20.MainResults.ActualStep
open Qatlib.Papers.NonlinearDE20.MainResults.ClassicalEuler
open Qatlib.Papers.NonlinearDE20.PolynomialStep.Model
open Qatlib.Papers.NonlinearDE20.AffineLift.Model

theorem polynomialMatrix_neg {I : Type} [Fintype I] [DecidableEq I] (m : ℕ)
    (B : Matrix (I × (Fin m → I)) (I × (Fin m → I)) ℂ) (x : I → ℂ) :
    polynomialMatrix m (-B) x = -polynomialMatrix m B x := by
  simp only [polynomialMatrix, compression, Matrix.mul_neg, Matrix.neg_mul]

theorem polynomial_classical_euler {I : Type} [Fintype I] [DecidableEq I] (m : ℕ)
    (A : Matrix I I ℂ) (B : Matrix (I × (Fin m → I)) (I × (Fin m → I)) ℂ)
    (b x : I → ℂ) (dt : ℝ) :
    x + (dt : ℂ) • polynomialField m (-A) (-B) b x =
      eulerStep (fun z => A *ᵥ z + polynomialMatrix m B z *ᵥ z) dt b x := by
  simp only [polynomialField, polynomialMatrix_neg, Matrix.neg_mulVec, eulerStep]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Complex.real_smul,
    smul_eq_mul]
  ring

theorem actual_source_normalized_error {I : Type} [Fintype I] [DecidableEq I] (m : ℕ)
    (A : Matrix I I ℂ) (B : Matrix (I × (Fin m → I)) (I × (Fin m → I)) ℂ)
    (b x : I → ℂ) (dt : ℝ) (hx : (∑ i : I, Complex.normSq (x i)) = 1)
    (hp : 0 < (outer (eulerStep (fun z => A *ᵥ z + polynomialMatrix m B z *ᵥ z) dt b x)).trace.re) :
    (normalizePositive (polynomialProgramReduced m (-A) (-B) b x (dt : ℂ)) -
      normalizePositive (outer (eulerStep (fun z => A *ᵥ z + polynomialMatrix m B z *ᵥ z) dt b x))).traceNorm ≤
        2 * polynomialNoiseMass m (-B) x (dt : ℂ) /
          ((outer (eulerStep (fun z => A *ᵥ z + polynomialMatrix m B z *ᵥ z) dt b x)).trace.re +
            polynomialNoiseMass m (-B) x (dt : ℂ)) := by
  simpa only [polynomial_classical_euler] using
    polynomialProgram_normalized_error m (-A) (-B) b x (dt : ℂ) hx
      (by simpa only [polynomial_classical_euler] using hp)

end Qatlib.Papers.NonlinearDE20.MainResults.ActualStep
