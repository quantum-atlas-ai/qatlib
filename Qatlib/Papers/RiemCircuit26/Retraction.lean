/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.CommutatorExp.ExponentialWord
import Qatlib.Papers.RiemCircuit26.HessianGeometry.ExpTools
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace Qatlib.Papers.RiemCircuit26.Retraction.Word
open Qatlib.Papers.RiemCircuit26.HessianGeometry
open Qatlib.Foundations.MatrixAlgebra.CommutatorExp

def curve {p : ℕ} (ks : List (Mat p)) (U : Mat p) (t : ℝ) : Mat p := word ks t * U

theorem exp_unitary {p : ℕ} (Ω : Mat p) (hΩ : Ωᴴ = -Ω) (t : ℝ) :
    NormedSpace.exp (t • Ω) ∈ Matrix.unitaryGroup (Fin p) ℂ := by
  letI : NormedAlgebra ℚ (Mat p) := NormedAlgebra.restrictScalars ℚ ℝ (Mat p)
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  change star (t • Ω) = -(t • Ω)
  rw [star_smul, Matrix.star_eq_conjTranspose, hΩ, star_trivial, smul_neg]

theorem word_unitary {p : ℕ} (ks : List (Mat p))
    (hks : ∀ K ∈ ks, Kᴴ = -K) (t : ℝ) : word ks t ∈ Matrix.unitaryGroup (Fin p) ℂ := by
  induction ks with
  | nil => exact (Matrix.unitaryGroup (Fin p) ℂ).one_mem
  | cons K ks ih =>
    exact (Matrix.unitaryGroup (Fin p) ℂ).mul_mem (exp_unitary K (hks K (by simp)) t)
      (ih (fun J hJ => hks J (by simp [hJ])))

theorem generator_zero {p : ℕ} (ks : List (Mat p)) : generator ks 0 = ks.sum := by
  induction ks with
  | nil => rfl
  | cons K ks ih => simp only [generator, neg_zero, zero_smul, NormedSpace.exp_zero, one_mul,
      mul_one, List.sum_cons, ih]

theorem curve_zero {p : ℕ} (ks : List (Mat p)) (U : Mat p) : curve ks U 0 = U := by
  rw [curve, word_zero, Matrix.one_mul]

theorem curve_hasDerivAt_zero {p : ℕ} (ks : List (Mat p)) (U : Mat p) :
    HasDerivAt (curve ks U) (ks.sum * U) 0 := by
  simpa only [word_zero, generator_zero, Matrix.mul_one, curve] using!
    (word_hasDerivAt ks 0).mul_const U

theorem curve_unitary {p : ℕ} (ks : List (Mat p)) (U : Mat p)
    (hks : ∀ K ∈ ks, Kᴴ = -K) (hU : U ∈ Matrix.unitaryGroup (Fin p) ℂ) (t : ℝ) :
    curve ks U t ∈ Matrix.unitaryGroup (Fin p) ℂ :=
  (Matrix.unitaryGroup (Fin p) ℂ).mul_mem (word_unitary ks hks t) hU

theorem weighted_pauli_skew {p : ℕ} (P : Mat p) (hP : Pᴴ = P) (ω : ℝ) :
    (ω • (Complex.I • P))ᴴ = -(ω • (Complex.I • P)) := by
  simp only [Matrix.conjTranspose_smul, star_trivial, Complex.star_def,
    Complex.conj_I, hP, neg_smul, smul_neg]

def pauliLetters {p K : ℕ} (P : Fin K → Mat p) (ω : Fin K → ℝ) : List (Mat p) :=
  List.ofFn (fun j => ω j • (Complex.I • P j))

theorem pauli_curve_unitary {p K : ℕ} (P : Fin K → Mat p) (ω : Fin K → ℝ) (U : Mat p)
    (hP : ∀ j, (P j)ᴴ = P j) (hU : U ∈ Matrix.unitaryGroup (Fin p) ℂ) (t : ℝ) :
    curve (pauliLetters P ω) U t ∈ Matrix.unitaryGroup (Fin p) ℂ := by
  apply curve_unitary _ U _ hU t
  intro L hL
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hL
  exact weighted_pauli_skew (P j) (hP j) (ω j)

theorem exponential_curve_hasDerivAt_zero {p : ℕ} (Ω U : Mat p) :
    HasDerivAt (fun t : ℝ => evol Ω t * U) (Ω * U) 0 := by
  simpa only [evol_zero, Matrix.one_mul] using (evol_hasDerivAt Ω 0).mul_const U

theorem pauliLetters_length {p K : ℕ} (P : Fin K → Mat p) (ω : Fin K → ℝ) :
    (pauliLetters P ω).length = K := by
  exact List.length_ofFn

end Qatlib.Papers.RiemCircuit26.Retraction.Word
