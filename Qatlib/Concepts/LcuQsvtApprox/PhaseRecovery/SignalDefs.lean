/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PhaseGeometry.Phase
import Qatlib.Concepts.TrotterFormula.SuzukiFourth.QSP
import Qatlib.Concepts.CoherentSim.CoherentOAA.Qubitization
import Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
import Qatlib.Concepts.CoherentSim.CoherentOAA.QSVT
import Qatlib.Concepts.CoherentSim.CoherentOAA.OperatorResponse
import Qatlib.Concepts.QspSimulation.Achievability.RealPolynomial
import Qatlib.Concepts.OperatorErrors.Robustness
import Qatlib.Concepts.QsvtCore.LinearSystems.RealPolynomialCompletionClosed
import Qatlib.Concepts.CoherentSim.CoherentOAA.Realization
import Qatlib.Concepts.CoherentSim.CoherentOAA.SingularPolynomial
import Qatlib.Concepts.CoherentSim.CoherentOAA.BlockRobustness
import Qatlib.Concepts.QspSimulation.Achievability.ResponseFactorization
import Qatlib.Concepts.QspSimulation.Achievability.RealPartResponse
import Qatlib.Concepts.QspSimulation.Achievability.RealPartQSVT
import Qatlib.Concepts.CopyEvolution.Discriminate.ParallelQSVT
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Concepts.WalshMoment.Forrelation.CountedThresholdQSVT
import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.ThresholdOutputConsumers
import Qatlib.Concepts.QsvtCore.QsVtStability.ComplexBoundaryQsvt
import Qatlib.Concepts.QsvtCore.QsVtStability.ComplexBoundaryQsvtConsumers
import Qatlib.Concepts.QsvtCore.QsVtMain.CPPPhaseCompiler
import Qatlib.Concepts.QspSimulation.WordModel.CPPAdjointDefs
import Qatlib.Concepts.QsvtCore.QsVtMain.LengthQSVT
import Qatlib.Concepts.QsvtCore.QsVtMain.QSVTConsumers
import Qatlib.Concepts.NonNormalSpec.ResolventWord.ThresholdIntegralDefs
import Qatlib.Concepts.NonNormalSpec.ResolventWord.ThresholdIntegralAmplification
import Qatlib.Concepts.NonNormalSpec.ResolventWord.ThresholdIntegralConsumer
import Qatlib.Concepts.NonNormalSpec.ResolventWord.NativeThresholdIntegralDefs
import Qatlib.Concepts.NonNormalSpec.ResolventWord.NativeThresholdIntegralCoefficients
import Qatlib.Concepts.NonNormalSpec.ResolventWord.NativeThresholdIntegralCutoff
import Qatlib.Concepts.NonNormalSpec.ResolventWord.NativeThresholdIntegralConsumer
import Qatlib.Concepts.NativeNumerics.PhaseSynthesis.GaussianResponseData
import Qatlib.Concepts.NativeNumerics.PhaseSynthesis.FinitePhaseGrid
import Qatlib.Concepts.NativeNumerics.PhaseSynthesis.FinitePhaseSynthesis
import Qatlib.Concepts.SignalPrimitive.PhaseFrontend.ComputedPhaseQSVT
import Qatlib.Concepts.QspSimulation.WordModel.FinitePhaseConsumers
import Qatlib.Concepts.SignalPrimitive.HermitianQSVT
import Qatlib.Concepts.QsvtCore.QsVtStability.SquareRootQSVTRobustness
import Qatlib.Concepts.QsvtCore.QsVtStability.RootRobustQSVTConsumers
import Qatlib.Concepts.QsvtCore.QsVtStability.InteriorComplexQsvt
import Qatlib.Concepts.QsvtCore.QsVtMain.ConventionBridge
import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.ConventionBridgeConsumers
import Qatlib.Concepts.NativeNumerics.NlfftPipeline.NonlinearFourierSU2
import Qatlib.Concepts.NativeNumerics.NlfftPipeline.InverseNLFFTSU2
import Qatlib.Concepts.NativeNumerics.NlfftPipeline.FiniteFFTPolynomialMul
import Qatlib.Concepts.NativeNumerics.NlfftPipeline.InverseNLFFTSU2Finite

/-!
# Signal matrices and polynomial QSP form

`SignalMatrix`, `PhaseRotation`, and `QSPWord` fix a two-dimensional quantum signal-processing
convention and establish unitarity on `[-1, 1]`. Entrywise formulas identify each signal-phase
factor explicitly.

`EvalParity` tracks parity under evaluation. `qsp_function_form` represents diagonal word
entries by polynomials and off-diagonal entries by `i * √(1 - x^2)` times polynomials, with
degree and parity bounds determined by word length, as in [LowChuang2017].

## Main statements

* `qspWord_unitary`: prove unitarity of the signal word.
* `qsp_function_form_aux`: construct response polynomials with parity and empty-word
  information.
* `qsp_function_form`: expose polynomial entry formulas and degree bounds.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Matrix

set_option maxHeartbeats 4000000

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs

/-- The two-dimensional signal matrix with diagonal `x` and off-diagonal `i * √(1 - x^2)`. -/
noncomputable def SignalMatrix (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun a b => if a = b then ((x : ℂ))
    else ((Real.sqrt (1 - x ^ 2) : ℂ)) * Complex.I

/-- The entrywise formula for `SignalMatrix`. -/
theorem signalMatrix_apply (x : ℝ) (a b : Fin 2) :
    SignalMatrix x a b = if a = b then ((x : ℂ))
      else ((Real.sqrt (1 - x ^ 2) : ℂ)) * Complex.I := rfl

/-- The diagonal phase rotation with entries `exp(i * φ)` and `exp(-i * φ)`. -/
noncomputable def PhaseRotation (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal fun a => if a = 0 then Complex.exp ((φ : ℂ) * Complex.I)
    else Complex.exp ((-φ : ℂ) * Complex.I)

/-- The signal matrix is unitary for `-1 ≤ x ≤ 1`. -/
theorem signalMatrix_unitary {x : ℝ} (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    SignalMatrix x ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  have hs : (0 : ℝ) ≤ 1 - x ^ 2 := by nlinarith [hx1, hx2]
  have hd : ((x : ℂ)) * ((x : ℂ))
      + ((Real.sqrt (1 - x ^ 2) : ℂ)) * ((Real.sqrt (1 - x ^ 2) : ℂ)) = 1 := by
    have e1 : Real.sqrt (1 - x ^ 2) * Real.sqrt (1 - x ^ 2) = 1 - x ^ 2 :=
      Real.mul_self_sqrt hs
    have e2 : x * x = x ^ 2 := by ring
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, e1, e2]
    push_cast
    ring
  have h2 : ((Real.sqrt (1 - x ^ 2) : ℂ)) * Complex.I
      * (((Real.sqrt (1 - x ^ 2) : ℂ)) * Complex.I)
      = -(((Real.sqrt (1 - x ^ 2) : ℂ)) * ((Real.sqrt (1 - x ^ 2) : ℂ))) := by
    rw [show ((Real.sqrt (1 - x ^ 2) : ℂ)) * Complex.I
          * (((Real.sqrt (1 - x ^ 2) : ℂ)) * Complex.I)
        = (((Real.sqrt (1 - x ^ 2) : ℂ)) * ((Real.sqrt (1 - x ^ 2) : ℂ)))
          * (Complex.I * Complex.I) from by ring,
      Complex.I_mul_I]
    ring
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [SignalMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, RCLike.star_def, Fin.sum_univ_two, map_mul, Complex.conj_I,
      neg_mul, mul_neg, Matrix.one_apply] <;>
    norm_num
  · rw [h2, neg_neg]; exact hd
  · ring
  · ring
  · rw [h2, neg_neg, add_comm]
    exact hd

/-- Every real-angle phase rotation is unitary. -/
theorem phaseRotation_unitary (φ : ℝ) :
    PhaseRotation φ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  have hnorm : ∀ z : ℂ, ‖z‖ = 1 → (starRingEnd ℂ) z * z = 1 := by
    intro z hz
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hz, one_pow]
    norm_num
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [PhaseRotation, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.diagonal_apply, Matrix.one_apply, RCLike.star_def] <;>
    norm_num
  · exact hnorm _ (by rw [Complex.norm_exp_ofReal_mul_I])
  · exact hnorm _ (by
      have h1 : Complex.exp (-(↑(φ : ℝ) * Complex.I))
          = (Complex.exp (↑(φ : ℝ) * Complex.I))⁻¹ := by
        rw [Complex.exp_neg]
      rw [h1]
      simp [Complex.norm_exp_ofReal_mul_I])

/-- The product of signal matrices followed by the phase rotations listed in `phis`. -/
noncomputable def QSPWord (phis : List ℝ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (phis.map (fun φ => SignalMatrix x * PhaseRotation φ)).foldl (· * ·) 1

/-- A multiplicative left fold starting at `a` factors as `a` times the fold starting at one. -/
private theorem foldl_mul_prefix {M : Type*} [Monoid M] (l : List M) (a : M) :
    List.foldl (· * ·) a l = a * List.foldl (· * ·) 1 l := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, List.foldl_cons, ih (1 * x), one_mul, mul_assoc]

/-- A QSP word is unitary for signals in `[-1, 1]`. -/
theorem qspWord_unitary (phis : List ℝ) {x : ℝ} (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    QSPWord phis x ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  induction phis with
  | nil =>
    show (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ
    exact Submonoid.one_mem _
  | cons φ rest ih =>
    have hval : QSPWord (φ :: rest) x
        = (SignalMatrix x * PhaseRotation φ) * QSPWord rest x := by
      simp only [QSPWord, List.map_cons, List.foldl_cons, one_mul]
      exact foldl_mul_prefix _ _
    rw [hval]
    exact Submonoid.mul_mem _
      (Submonoid.mul_mem _ (signalMatrix_unitary hx1 hx2) (phaseRotation_unitary φ))
      ih
open Polynomial

/-- The empty QSP word is the identity matrix. -/
theorem qspWord_nil (x : ℝ) : QSPWord [] x = 1 := rfl

/-- A nonempty QSP word factors into its first signal-phase matrix and the remaining word. -/
theorem qspWord_cons (φ : ℝ) (rest : List ℝ) (x : ℝ) :
    QSPWord (φ :: rest) x = (SignalMatrix x * PhaseRotation φ) * QSPWord rest x := by
  simp only [QSPWord, List.map_cons, List.foldl_cons, one_mul]
  exact foldl_mul_prefix _ _

/-- The entrywise formula for a diagonal phase rotation. -/
theorem phaseRotation_apply (φ : ℝ) (a b : Fin 2) :
    PhaseRotation φ a b = if a = b then
      (if a = 0 then Complex.exp ((φ : ℂ) * Complex.I)
        else Complex.exp ((-φ : ℂ) * Complex.I)) else 0 := rfl

/-- Each entry of a signal-phase product is the signal entry times the phase rotation's
corresponding diagonal entry. -/
theorem signalMatrix_mul_phaseRotation_apply (x φ : ℝ) (a b : Fin 2) :
    (SignalMatrix x * PhaseRotation φ) a b
      = SignalMatrix x a b * PhaseRotation φ b b := by
  have hPR : PhaseRotation φ = Matrix.diagonal (fun a =>
      if a = 0 then Complex.exp ((φ : ℂ) * Complex.I)
        else Complex.exp ((-φ : ℂ) * Complex.I)) := rfl
  rw [hPR, Matrix.mul_diagonal, Matrix.diagonal_apply, if_pos rfl]

/-- The upper-left entry of a signal-phase factor is `x * exp(i * φ)`. -/
theorem signalMatrix_mul_phaseRotation_zero_zero (x φ : ℝ) :
    (SignalMatrix x * PhaseRotation φ) 0 0
      = (x : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) := by
  rw [signalMatrix_mul_phaseRotation_apply, signalMatrix_apply, phaseRotation_apply,
    if_pos rfl, if_pos rfl, if_pos rfl]

/-- The upper-right entry of a signal-phase factor is `i * √(1 - x^2) * exp(-i * φ)`. -/
theorem signalMatrix_mul_phaseRotation_zero_one (x φ : ℝ) :
    (SignalMatrix x * PhaseRotation φ) 0 1
      = (Real.sqrt (1 - x ^ 2) : ℂ) * Complex.I * Complex.exp ((-φ : ℂ) * Complex.I) := by
  rw [signalMatrix_mul_phaseRotation_apply, signalMatrix_apply, phaseRotation_apply,
    if_neg (by decide : ¬((0 : Fin 2) = 1)), if_pos rfl,
    if_neg (by decide : ¬((1 : Fin 2) = 0))]

/-- The lower-left entry of a signal-phase factor is `i * √(1 - x^2) * exp(i * φ)`. -/
theorem signalMatrix_mul_phaseRotation_one_zero (x φ : ℝ) :
    (SignalMatrix x * PhaseRotation φ) 1 0
      = (Real.sqrt (1 - x ^ 2) : ℂ) * Complex.I * Complex.exp ((φ : ℂ) * Complex.I) := by
  rw [signalMatrix_mul_phaseRotation_apply, signalMatrix_apply, phaseRotation_apply,
    if_neg (by decide : ¬((1 : Fin 2) = 0)), if_pos rfl, if_pos rfl]

/-- The lower-right entry of a signal-phase factor is `x * exp(-i * φ)`. -/
theorem signalMatrix_mul_phaseRotation_one_one (x φ : ℝ) :
    (SignalMatrix x * PhaseRotation φ) 1 1
      = (x : ℂ) * Complex.exp ((-φ : ℂ) * Complex.I) := by
  rw [signalMatrix_mul_phaseRotation_apply, signalMatrix_apply, phaseRotation_apply,
    if_pos rfl, if_pos rfl, if_neg (by decide : ¬((1 : Fin 2) = 0))]

/-- For `x` in `[-1, 1]`, the square of the complex-cast square root of `1 - x^2` equals `1 - (x
: ℂ)^2`. -/
theorem qsp_sqrt_mul_self {x : ℝ} (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    ((Real.sqrt (1 - x ^ 2) : ℂ)) * ((Real.sqrt (1 - x ^ 2) : ℂ))
      = 1 - (x : ℂ) ^ 2 := by
  have hs : (0 : ℝ) ≤ 1 - x ^ 2 := by nlinarith [hx1, hx2]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hs, Complex.ofReal_sub,
    Complex.ofReal_pow, Complex.ofReal_one]

/-- Evaluation parity `k` means that replacing the argument by its negative multiplies every
polynomial value by `(-1)^k`. -/
def EvalParity (P : Polynomial ℂ) (k : ℕ) : Prop :=
  ∀ t : ℂ, P.eval (-t) = ((-1 : ℂ) ^ k) * P.eval t

/-- The zero polynomial has every evaluation parity. -/
theorem evalParity_zero (k : ℕ) : EvalParity (0 : Polynomial ℂ) k := fun t => by simp

/-- The constant polynomial one has even evaluation parity. -/
theorem evalParity_one : EvalParity (1 : Polynomial ℂ) 0 := fun t => by simp

/-- Multiplication by a constant polynomial preserves evaluation parity. -/
theorem evalParity_C_mul (c : ℂ) {P : Polynomial ℂ} {k : ℕ} (h : EvalParity P k) :
    EvalParity (C c * P) k := fun t => by
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [h t]
  ring

/-- Multiplication by `X` increases the evaluation parity index by one. -/
theorem evalParity_X_mul {P : Polynomial ℂ} {k : ℕ} (h : EvalParity P k) :
    EvalParity (X * P) (k + 1) := fun t => by
  simp only [Polynomial.eval_mul, Polynomial.eval_X]
  rw [h t, pow_add]
  ring

/-- Multiplication by `X^2` preserves evaluation parity. -/
theorem evalParity_X_sq_mul {P : Polynomial ℂ} {k : ℕ} (h : EvalParity P k) :
    EvalParity (X ^ 2 * P) k := fun t => by
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  rw [h t]
  ring

/-- Adding polynomials with the same evaluation parity preserves that parity. -/
theorem evalParity_add {P Q : Polynomial ℂ} {k : ℕ} (hP : EvalParity P k)
    (hQ : EvalParity Q k) : EvalParity (P + Q) k := fun t => by
  simp only [Polynomial.eval_add]
  rw [hP t, hQ t]
  ring

/-- Subtracting polynomials with the same evaluation parity preserves that parity. -/
theorem evalParity_sub {P Q : Polynomial ℂ} {k : ℕ} (hP : EvalParity P k)
    (hQ : EvalParity Q k) : EvalParity (P - Q) k := fun t => by
  simp only [Polynomial.eval_sub]
  rw [hP t, hQ t]
  ring

/-- An evaluation parity index may be increased by two. -/
theorem evalParity_add_two {P : Polynomial ℂ} {k : ℕ} (h : EvalParity P k) :
    EvalParity P (k + 2) := fun t => by
  have h2 : ((-1 : ℂ) ^ 2) = 1 := by ring
  have hpow : ((-1 : ℂ) ^ (k + 2)) = ((-1 : ℂ) ^ k) := by
    rw [pow_add, h2, mul_one]
  rw [hpow]
  exact h t

/-- Constructs polynomial formulas for all QSP word entries with degree and evaluation-parity
bounds, and zero off-diagonal response polynomials for the empty word. -/
theorem qsp_function_form_aux (phis : List ℝ) :
    ∃ P Q₁ Q₂ S : Polynomial ℂ,
      P.natDegree ≤ phis.length ∧
      S.natDegree ≤ phis.length ∧
      Q₁.natDegree ≤ phis.length - 1 ∧
      Q₂.natDegree ≤ phis.length - 1 ∧
      (phis.length = 0 → Q₁ = 0) ∧
      (phis.length = 0 → Q₂ = 0) ∧
      EvalParity P phis.length ∧
      EvalParity S phis.length ∧
      EvalParity Q₁ (phis.length + 1) ∧
      EvalParity Q₂ (phis.length + 1) ∧
      (∀ x : ℝ, -1 ≤ x → x ≤ 1 → (QSPWord phis x) 0 0 = P.eval ((x : ℂ))) ∧
      (∀ x : ℝ, -1 ≤ x → x ≤ 1 → (QSPWord phis x) 1 1 = S.eval ((x : ℂ))) ∧
      (∀ x : ℝ, -1 ≤ x → x ≤ 1 → (QSPWord phis x) 0 1
        = Complex.I * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) * Q₁.eval ((x : ℂ))) ∧
      (∀ x : ℝ, -1 ≤ x → x ≤ 1 → (QSPWord phis x) 1 0
        = Complex.I * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) * Q₂.eval ((x : ℂ))) := by
  induction phis with
  | nil =>
    refine ⟨1, 0, 0, 1, by simp [Polynomial.natDegree_one],
      by simp [Polynomial.natDegree_one], by simp [Polynomial.natDegree_zero],
      by simp [Polynomial.natDegree_zero], fun _ => rfl, fun _ => rfl,
      evalParity_one, evalParity_one, evalParity_zero _, evalParity_zero _,
      ?_, ?_, ?_, ?_⟩
    · intro x _ _
      simp [qspWord_nil]
    · intro x _ _
      simp [qspWord_nil]
    · intro x _ _
      simp [qspWord_nil]
    · intro x _ _
      simp [qspWord_nil]
  | cons φ rest ih =>
    obtain ⟨P, Q₁, Q₂, S, hPd, hSd, hQ1d, hQ2d, hz1, hz2, hPp, hSp, hQ1p, hQ2p,
      hW00, hW11, hW01, hW10⟩ := ih

    have hXP : (X * P).natDegree ≤ rest.length + 1 := by
      have h := Polynomial.natDegree_mul_le (p := (X : Polynomial ℂ)) (q := P)
      rw [Polynomial.natDegree_X] at h
      omega
    have hXS : (X * S).natDegree ≤ rest.length + 1 := by
      have h := Polynomial.natDegree_mul_le (p := (X : Polynomial ℂ)) (q := S)
      rw [Polynomial.natDegree_X] at h
      omega
    have hXQ1 : (X * Q₁).natDegree ≤ rest.length := by
      by_cases hn0 : rest.length = 0
      · rw [hz1 hn0]
        simp [Polynomial.natDegree_zero]
      · have h := Polynomial.natDegree_mul_le (p := (X : Polynomial ℂ)) (q := Q₁)
        rw [Polynomial.natDegree_X] at h
        have hnpos : 0 < rest.length := Nat.pos_of_ne_zero hn0
        omega
    have hXQ2 : (X * Q₂).natDegree ≤ rest.length := by
      by_cases hn0 : rest.length = 0
      · rw [hz2 hn0]
        simp [Polynomial.natDegree_zero]
      · have h := Polynomial.natDegree_mul_le (p := (X : Polynomial ℂ)) (q := Q₂)
        rw [Polynomial.natDegree_X] at h
        have hnpos : 0 < rest.length := Nat.pos_of_ne_zero hn0
        omega
    have hX2Q1 : (X ^ 2 * Q₁).natDegree ≤ rest.length + 1 := by
      by_cases hn0 : rest.length = 0
      · rw [hz1 hn0]
        simp [Polynomial.natDegree_zero]
      · have h := Polynomial.natDegree_mul_le (p := (X : Polynomial ℂ) ^ 2) (q := Q₁)
        rw [Polynomial.natDegree_X_pow] at h
        have hnpos : 0 < rest.length := Nat.pos_of_ne_zero hn0
        omega
    have hX2Q2 : (X ^ 2 * Q₂).natDegree ≤ rest.length + 1 := by
      by_cases hn0 : rest.length = 0
      · rw [hz2 hn0]
        simp [Polynomial.natDegree_zero]
      · have h := Polynomial.natDegree_mul_le (p := (X : Polynomial ℂ) ^ 2) (q := Q₂)
        rw [Polynomial.natDegree_X_pow] at h
        have hnpos : 0 < rest.length := Nat.pos_of_ne_zero hn0
        omega
    have hQ1sub : (Q₁ - X ^ 2 * Q₁).natDegree ≤ rest.length + 1 :=
      le_trans (Polynomial.natDegree_sub_le _ _)
        (max_le (le_trans hQ1d (by omega)) hX2Q1)
    have hQ2sub : (Q₂ - X ^ 2 * Q₂).natDegree ≤ rest.length + 1 :=
      le_trans (Polynomial.natDegree_sub_le _ _)
        (max_le (le_trans hQ2d (by omega)) hX2Q2)
    simp only [List.length_cons]
    refine ⟨C (Complex.exp ((φ : ℂ) * Complex.I)) * (X * P)
        - C (Complex.exp ((-φ : ℂ) * Complex.I)) * (Q₂ - X ^ 2 * Q₂),
      C (Complex.exp ((φ : ℂ) * Complex.I)) * (X * Q₁)
        + C (Complex.exp ((-φ : ℂ) * Complex.I)) * S,
      C (Complex.exp ((φ : ℂ) * Complex.I)) * P
        + C (Complex.exp ((-φ : ℂ) * Complex.I)) * (X * Q₂),
      C (Complex.exp ((-φ : ℂ) * Complex.I)) * (X * S)
        - C (Complex.exp ((φ : ℂ) * Complex.I)) * (Q₁ - X ^ 2 * Q₁),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact le_trans (Polynomial.natDegree_sub_le _ _)
        (max_le (le_trans (Polynomial.natDegree_C_mul_le _ _) hXP)
          (le_trans (Polynomial.natDegree_C_mul_le _ _) hQ2sub))
    · exact le_trans (Polynomial.natDegree_sub_le _ _)
        (max_le (le_trans (Polynomial.natDegree_C_mul_le _ _) hXS)
          (le_trans (Polynomial.natDegree_C_mul_le _ _) hQ1sub))
    · show (C (Complex.exp ((φ : ℂ) * Complex.I)) * (X * Q₁)
          + C (Complex.exp ((-φ : ℂ) * Complex.I)) * S).natDegree ≤ rest.length
      exact le_trans (Polynomial.natDegree_add_le _ _)
        (max_le (le_trans (Polynomial.natDegree_C_mul_le _ _) hXQ1)
          (le_trans (Polynomial.natDegree_C_mul_le _ _) hSd))
    · show (C (Complex.exp ((φ : ℂ) * Complex.I)) * P
          + C (Complex.exp ((-φ : ℂ) * Complex.I)) * (X * Q₂)).natDegree ≤ rest.length
      exact le_trans (Polynomial.natDegree_add_le _ _)
        (max_le (le_trans (Polynomial.natDegree_C_mul_le _ _) hPd)
          (le_trans (Polynomial.natDegree_C_mul_le _ _) hXQ2))
    · intro hcon
      exact absurd hcon (Nat.succ_ne_zero _)
    · intro hcon
      exact absurd hcon (Nat.succ_ne_zero _)
    · exact evalParity_sub (evalParity_C_mul _ (evalParity_X_mul hPp))
        (evalParity_C_mul _ (evalParity_sub hQ2p (evalParity_X_sq_mul hQ2p)))
    · exact evalParity_sub (evalParity_C_mul _ (evalParity_X_mul hSp))
        (evalParity_C_mul _ (evalParity_sub hQ1p (evalParity_X_sq_mul hQ1p)))
    · exact evalParity_add (evalParity_C_mul _ (evalParity_X_mul hQ1p))
        (evalParity_C_mul _ (evalParity_add_two hSp))
    · exact evalParity_add (evalParity_C_mul _ (evalParity_add_two hPp))
        (evalParity_C_mul _ (evalParity_X_mul hQ2p))
    · intro x hx1 hx2
      have hy2 : ((Real.sqrt (1 - x ^ 2) : ℂ)) * ((Real.sqrt (1 - x ^ 2) : ℂ))
          = 1 - (x : ℂ) ^ 2 := qsp_sqrt_mul_self hx1 hx2
      rw [qspWord_cons, Matrix.mul_apply, Fin.sum_univ_two,
        signalMatrix_mul_phaseRotation_zero_zero, signalMatrix_mul_phaseRotation_zero_one,
        hW00 x hx1 hx2, hW10 x hx1 hx2]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      rw [show ((Real.sqrt (1 - x ^ 2) : ℂ)) * Complex.I
            * Complex.exp ((-φ : ℂ) * Complex.I)
            * (Complex.I * ((Real.sqrt (1 - x ^ 2) : ℂ)) * Q₂.eval (x : ℂ))
          = -(Complex.exp ((-φ : ℂ) * Complex.I)
            * ((((Real.sqrt (1 - x ^ 2) : ℂ)) * ((Real.sqrt (1 - x ^ 2) : ℂ)))
              * Q₂.eval (x : ℂ))) from by
        rw [show ((Real.sqrt (1 - x ^ 2) : ℂ)) * Complex.I
              * Complex.exp ((-φ : ℂ) * Complex.I)
              * (Complex.I * ((Real.sqrt (1 - x ^ 2) : ℂ)) * Q₂.eval (x : ℂ))
            = (((Real.sqrt (1 - x ^ 2) : ℂ)) * ((Real.sqrt (1 - x ^ 2) : ℂ)))
              * (Complex.I * Complex.I) * Complex.exp ((-φ : ℂ) * Complex.I)
              * Q₂.eval (x : ℂ) from by ring,
          Complex.I_mul_I]
        ring]
      rw [hy2]
      ring
    · intro x hx1 hx2
      have hy2 : ((Real.sqrt (1 - x ^ 2) : ℂ)) * ((Real.sqrt (1 - x ^ 2) : ℂ))
          = 1 - (x : ℂ) ^ 2 := qsp_sqrt_mul_self hx1 hx2
      rw [qspWord_cons, Matrix.mul_apply, Fin.sum_univ_two,
        signalMatrix_mul_phaseRotation_one_zero, signalMatrix_mul_phaseRotation_one_one,
        hW01 x hx1 hx2, hW11 x hx1 hx2]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      rw [show ((Real.sqrt (1 - x ^ 2) : ℂ)) * Complex.I
            * Complex.exp ((φ : ℂ) * Complex.I)
            * (Complex.I * ((Real.sqrt (1 - x ^ 2) : ℂ)) * Q₁.eval (x : ℂ))
          = -(Complex.exp ((φ : ℂ) * Complex.I)
            * ((((Real.sqrt (1 - x ^ 2) : ℂ)) * ((Real.sqrt (1 - x ^ 2) : ℂ)))
              * Q₁.eval (x : ℂ))) from by
        rw [show ((Real.sqrt (1 - x ^ 2) : ℂ)) * Complex.I
              * Complex.exp ((φ : ℂ) * Complex.I)
              * (Complex.I * ((Real.sqrt (1 - x ^ 2) : ℂ)) * Q₁.eval (x : ℂ))
            = (((Real.sqrt (1 - x ^ 2) : ℂ)) * ((Real.sqrt (1 - x ^ 2) : ℂ)))
              * (Complex.I * Complex.I) * Complex.exp ((φ : ℂ) * Complex.I)
              * Q₁.eval (x : ℂ) from by ring,
          Complex.I_mul_I]
        ring]
      rw [hy2]
      ring
    · intro x hx1 hx2
      rw [qspWord_cons, Matrix.mul_apply, Fin.sum_univ_two,
        signalMatrix_mul_phaseRotation_zero_zero, signalMatrix_mul_phaseRotation_zero_one,
        hW01 x hx1 hx2, hW11 x hx1 hx2]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      ring
    · intro x hx1 hx2
      rw [qspWord_cons, Matrix.mul_apply, Fin.sum_univ_two,
        signalMatrix_mul_phaseRotation_one_zero, signalMatrix_mul_phaseRotation_one_one,
        hW00 x hx1 hx2, hW10 x hx1 hx2]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      ring

/-- Every QSP word has polynomial diagonal entries and off-diagonal entries of the form `i * √(1
- x^2)` times a polynomial, with the stated degree and parity bounds [LowChuang2017]. -/
theorem qsp_function_form (phis : List ℝ) :
    ∃ P Q₁ Q₂ S : Polynomial ℂ,
      P.natDegree ≤ phis.length ∧
      S.natDegree ≤ phis.length ∧
      Q₁.natDegree ≤ phis.length - 1 ∧
      Q₂.natDegree ≤ phis.length - 1 ∧
      (∀ t : ℂ, P.eval (-t) = ((-1 : ℂ) ^ phis.length) * P.eval t) ∧
      (∀ t : ℂ, S.eval (-t) = ((-1 : ℂ) ^ phis.length) * S.eval t) ∧
      (∀ t : ℂ, Q₁.eval (-t) = ((-1 : ℂ) ^ (phis.length + 1)) * Q₁.eval t) ∧
      (∀ t : ℂ, Q₂.eval (-t) = ((-1 : ℂ) ^ (phis.length + 1)) * Q₂.eval t) ∧
      (∀ x : ℝ, -1 ≤ x → x ≤ 1 → (QSPWord phis x) 0 0 = P.eval ((x : ℂ))) ∧
      (∀ x : ℝ, -1 ≤ x → x ≤ 1 → (QSPWord phis x) 1 1 = S.eval ((x : ℂ))) ∧
      (∀ x : ℝ, -1 ≤ x → x ≤ 1 → (QSPWord phis x) 0 1
        = Complex.I * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) * Q₁.eval ((x : ℂ))) ∧
      (∀ x : ℝ, -1 ≤ x → x ≤ 1 → (QSPWord phis x) 1 0
        = Complex.I * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) * Q₂.eval ((x : ℂ))) := by
  obtain ⟨P, Q₁, Q₂, S, hPd, hSd, hQ1d, hQ2d, -, -, hPp, hSp, hQ1p, hQ2p,
    hW00, hW11, hW01, hW10⟩ := qsp_function_form_aux phis
  exact ⟨P, Q₁, Q₂, S, hPd, hSd, hQ1d, hQ2d, hPp, hSp, hQ1p, hQ2p,
    hW00, hW11, hW01, hW10⟩
end Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs
