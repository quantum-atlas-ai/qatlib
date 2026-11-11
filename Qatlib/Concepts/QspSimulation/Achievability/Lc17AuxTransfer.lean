/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.Lc17Support
import Qatlib.Concepts.QspSimulation.WordModel.Equation1WordBridgeLowc

/-!
# Transferring response polynomials to repository words

This module relates polynomial response recurrences to the repository matrix-word convention for
quantum signal processing [LowChuang2017]. The phase exponential `lcExp` is identified with
`anglePhase`, and elementary conjugation and matrix identities support the recursive matrix
construction `lcRespWord`.

For `x` in `[-1, 1]`, `lcRespWord_eq` expresses all four matrix entries through `responseP` and
`responseQ`. Rewriting this matrix as a repository word with shifted angles yields
`lcRepoAmp_of_response`, which extracts the real parts of the two response polynomials into the
desired scalar amplitude.

## Main statements

* `lcExp_eq_anglePhase` identifies the phase conventions.
* `lcRespWord_eq` gives the response-polynomial matrix representation.
* `lcRespWord_eq_repoWord` rewrites a nonempty response word using `lcQspTilde` and endpoint
  rotations.
* `lcRepoAmp_of_response` transfers the response polynomials to the repository amplitude.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

open Qatlib.Concepts.TrotterFormula.SuzukiFourth

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

namespace Qatlib.Concepts.QspSimulation.Achievability

open Matrix

/-- The complex phase exponential `Complex.exp (a * Complex.I)` of a real angle `a`. -/
noncomputable def lcExp (a : ℝ) : ℂ := Complex.exp (a * Complex.I)

/-- Rewrites the complex exponential of an embedded real angle times `Complex.I` as `lcExp`. -/
theorem lcExp_unfold (a : ℝ) :
    Complex.exp (((a : ℝ) : ℂ) * Complex.I) = lcExp a := rfl

/-- Rewrites the complex exponential of the negative embedded angle times `Complex.I` as `lcExp
(-a)`. -/
theorem lcExp_unfold_neg (a : ℝ) :
    Complex.exp (-(((a : ℝ) : ℂ)) * Complex.I) = lcExp (-a) := by
  show Complex.exp (-(((a : ℝ) : ℂ)) * Complex.I)
      = Complex.exp ((((-a : ℝ) : ℂ)) * Complex.I)
  rw [Complex.ofReal_neg]

/-- Multiplying the phase exponentials of `a` and `b` gives the phase exponential of `a + b`. -/
theorem lcExp_add (a b : ℝ) : lcExp a * lcExp b = lcExp (a + b) := by
  simp only [lcExp, ← Complex.exp_add]
  congr 1
  rw [Complex.ofReal_add]
  ring

/-- Complex conjugation of a phase exponential negates its angle. -/
theorem lcExp_conj (a : ℝ) : star (lcExp a) = lcExp (-a) := by
  rw [RCLike.star_def]
  simp only [lcExp]
  rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal,
    Complex.ofReal_neg, mul_neg, neg_mul]

/-- The phase exponential at `Real.pi / 2` equals `Complex.I`. -/
theorem lcExp_pi_half : lcExp (Real.pi / 2) = Complex.I := by
  apply Complex.ext <;>
    simp [lcExp, Complex.exp_re, Complex.exp_im, Complex.exp_zero, Real.cos_pi_div_two,
      Real.sin_pi_div_two, Complex.mul_re, Complex.mul_im]

/-- The exponential phase convention `lcExp` agrees with `anglePhase`. -/
theorem lcExp_eq_anglePhase (a : ℝ) :
    lcExp a = Qatlib.Concepts.PhaseGeometry.Phase.anglePhase a := by
  apply Complex.ext <;>
    simp [lcExp, Complex.exp_re, Complex.exp_im, Complex.exp_zero,
      Qatlib.Concepts.PhaseGeometry.Phase.anglePhase, Complex.mul_re, Complex.mul_im]

/-- Complex conjugation fixes a real number embedded in the complex numbers. -/
theorem lcStar_ofReal (r : ℝ) : star ((r : ℝ) : ℂ) = ((r : ℝ) : ℂ) := by
  simp [RCLike.star_def]

/-- Complex conjugation sends `Complex.I` to `-Complex.I`. -/
theorem lcStar_I : star (Complex.I) = -(Complex.I) := by
  rw [RCLike.star_def]
  exact Complex.conj_I

/-- The square of `Complex.I` equals `-1`. -/
theorem lcI_pow_two : Complex.I ^ 2 = -1 := by
  rw [pow_two, Complex.I_mul_I]

/-- The cube of `Complex.I` equals `-Complex.I`. -/
theorem lcI_pow_three : Complex.I ^ 3 = -Complex.I := by
  show Complex.I ^ (2 + 1) = -Complex.I
  rw [pow_add, lcI_pow_two]
  ring

/-- The fourth power of `Complex.I` equals one. -/
theorem lcI_pow_four : Complex.I ^ 4 = 1 := by
  show Complex.I ^ (2 * 2) = 1
  rw [pow_mul, lcI_pow_two]
  norm_num

/-- The sum of the conjugate of a complex number and the number itself is twice its embedded
real part. -/
theorem lcStar_add_self (z : ℂ) : star z + z = 2 * ((z.re : ℝ) : ℂ) := by
  rw [RCLike.star_def, add_comm, Complex.add_conj, Complex.ofReal_mul]
  push_cast
  ring

/-- The complex embedding of the real number `1 / 2` equals the complex number `1 / 2`. -/
theorem lcHalf_ofReal : (((1 : ℝ) / 2 : ℝ) : ℂ) = ((1 : ℂ) / 2) := by
  rw [Complex.ofReal_div, Complex.ofReal_one]
  push_cast
  ring

/-- Two complex matrices indexed by `Fin 2` are equal when their four corresponding entries are
equal. -/
private theorem lcMat2_eq_of_entries {M N : Matrix (Fin 2) (Fin 2) ℂ}
    (e00 : M 0 0 = N 0 0) (e01 : M 0 1 = N 0 1) (e10 : M 1 0 = N 1 0)
    (e11 : M 1 1 = N 1 1) : M = N := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11]

/-- A left multiplication fold with initial value `a` equals `a` multiplied by the same fold
with initial value one. -/
private theorem lcFoldl_mul_prefix {M : Type*} [Monoid M] (a : M) (l : List M) :
    List.foldl (· * ·) a l = a * List.foldl (· * ·) 1 l := by
  induction l generalizing a with
  | nil => simp
  | cons g l' ih =>
    rw [List.foldl_cons, ih, List.foldl_cons, ih (1 * g), one_mul, mul_assoc]

/-- Prepending a phase to `lcQspTilde` left-multiplies the remaining word by the adjoint signal
matrix followed by that phase rotation. -/
theorem lcQspTilde_cons (q : ℝ) (qs : List ℝ) (x : ℝ) :
    lcQspTilde (q :: qs) x =
      ((Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.SignalMatrix x).conjTranspose * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation q) *
        lcQspTilde qs x := by
  simp only [lcQspTilde, List.map_cons, List.foldl_cons, one_mul]
  exact lcFoldl_mul_prefix _ _

/-- The recursive response matrix word, with terminal rotation `PhaseRotation (-c)` and each
phase adding a shifted phase rotation, an adjoint signal matrix, and a final rotation by
`-Real.pi / 2`. -/
noncomputable def lcRespWord : List ℝ → ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ
  | [], c, _ => Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-c)
  | a :: as, c, x =>
      Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (Real.pi / 2 - a) *
        ((Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.SignalMatrix x).conjTranspose *
          (lcRespWord as c x * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(Real.pi / 2))))

/-- For `x` in `[-1, 1]`, the diagonal entries of `lcRespWord` are the conjugate and the value
of `responseP`, respectively. The off-diagonal entries are `Complex.I * sqrt (1 - x^2)`
times `responseQ` and its conjugate, using the phase exponentials of the supplied angles. -/
theorem lcRespWord_eq (x : ℝ) (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    ∀ (as : List ℝ) (c : ℝ),
      lcRespWord as c x =
        !![star ((Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseP (lcExp c) (as.map lcExp)).eval ((x : ℂ))),
           Complex.I * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) * ((Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseQ (lcExp c) (as.map lcExp)).eval ((x : ℂ)));
           Complex.I * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) * star ((Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseQ (lcExp c) (as.map lcExp)).eval ((x : ℂ))),
           ((Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseP (lcExp c) (as.map lcExp)).eval ((x : ℂ)))] := by
  intro as
  induction as with
  | nil =>
      intro c
      refine lcMat2_eq_of_entries ?_ ?_ ?_ ?_
      · show Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-c) 0 0 = _
        rw [Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.phaseRotation_apply, if_pos rfl, if_pos rfl, lcExp_unfold,
          List.map_nil, Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseP_nil, Polynomial.eval_C]
        simp only [Matrix.of_apply, Matrix.cons_val_zero]
        exact (lcExp_conj c).symm
      · show Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-c) 0 1 = _
        rw [Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.phaseRotation_apply, if_neg (by decide : ¬((0 : Fin 2) = 1)),
          List.map_nil, Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseQ_nil,
          Polynomial.eval_zero]
        simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, zero_mul, mul_zero]
      · show Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-c) 1 0 = _
        rw [Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.phaseRotation_apply, if_neg (by decide : ¬((1 : Fin 2) = 0)),
          List.map_nil, Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseQ_nil,
          Polynomial.eval_zero]
        simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, zero_mul, mul_zero, map_zero, star_zero]
      · show Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-c) 1 1 = _
        rw [Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.phaseRotation_apply, if_pos rfl,
          if_neg (by decide : ¬((1 : Fin 2) = 0)), lcExp_unfold_neg, neg_neg,
          List.map_nil, Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseP_nil, Polynomial.eval_C]
        simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
  | cons a as ih =>
      intro c
      have ht2 : ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ)
          = 1 - ((x : ℂ)) ^ 2 := by
        have h1 : (0 : ℝ) ≤ 1 - x ^ 2 := by nlinarith
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt h1, Complex.ofReal_sub,
          Complex.ofReal_one, Complex.ofReal_pow]
      have hph1 : lcExp (-(Real.pi / 2)) = -(Complex.I) := by
        rw [← lcExp_conj (Real.pi / 2), lcExp_pi_half, RCLike.star_def]
        exact Complex.conj_I
      have hz1 : lcExp (Real.pi / 2 - a) = Complex.I * star (lcExp a) := by
        rw [← lcExp_pi_half, lcExp_conj a, lcExp_add]
        rfl
      have hz2 : lcExp (-(Real.pi / 2 - a)) = -(Complex.I) * lcExp a := by
        rw [← hph1, lcExp_add]
        congr 1
        ring
      have hP' : (Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseP (lcExp c) ((a :: as).map lcExp)).eval ((x : ℂ))
          = lcExp a * (((x : ℂ)) * (Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseP (lcExp c) (as.map lcExp)).eval ((x : ℂ))
              + ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) * (Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseQ (lcExp c) (as.map lcExp)).eval ((x : ℂ))) := by
        simp only [List.map_cons, Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseP_cons,
          Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_pow]
        rw [ht2]
      have hQ' : (Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseQ (lcExp c) ((a :: as).map lcExp)).eval ((x : ℂ))
          = star (lcExp a) * ((Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseP (lcExp c) (as.map lcExp)).eval ((x : ℂ)) - ((x : ℂ)) * (Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseQ (lcExp c) (as.map lcExp)).eval ((x : ℂ))) := by
        simp only [List.map_cons, Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseQ_cons,
          Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
      have hcP : star (lcExp a * (((x : ℂ)) * (Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseP (lcExp c) (as.map lcExp)).eval ((x : ℂ))
              + ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) * (Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseQ (lcExp c) (as.map lcExp)).eval ((x : ℂ))))
          = star (lcExp a) * (((x : ℂ)) * star ((Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseP (lcExp c) (as.map lcExp)).eval ((x : ℂ)))
              + ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) * star ((Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseQ (lcExp c) (as.map lcExp)).eval ((x : ℂ)))) := by
        simp only [star_mul, star_add, star_neg, star_sub, star_star, lcStar_ofReal]
        ring
      have hcQ : star (star (lcExp a) * ((Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseP (lcExp c) (as.map lcExp)).eval ((x : ℂ)) - ((x : ℂ)) * (Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseQ (lcExp c) (as.map lcExp)).eval ((x : ℂ))))
          = lcExp a * (star ((Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseP (lcExp c) (as.map lcExp)).eval ((x : ℂ))) - ((x : ℂ)) * star ((Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseQ (lcExp c) (as.map lcExp)).eval ((x : ℂ)))) := by
        simp only [star_mul, star_add, star_neg, star_sub, star_star, lcStar_ofReal]
        ring
      show Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (Real.pi / 2 - a) *
          ((Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.SignalMatrix x).conjTranspose *
            (lcRespWord as c x * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(Real.pi / 2)))) = _
      rw [ih c, hP', hQ', hcP, hcQ]
      have hS00 : (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.SignalMatrix x).conjTranspose 0 0 = ((x : ℂ)) := by
        rw [Matrix.conjTranspose_apply, Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.signalMatrix_apply, if_pos rfl,
          lcStar_ofReal]
      have hS11 : (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.SignalMatrix x).conjTranspose 1 1 = ((x : ℂ)) := by
        rw [Matrix.conjTranspose_apply, Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.signalMatrix_apply, if_pos rfl,
          lcStar_ofReal]
      have hS01 : (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.SignalMatrix x).conjTranspose 0 1
          = -(Complex.I) * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) := by
        rw [Matrix.conjTranspose_apply, Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.signalMatrix_apply,
          if_neg (by decide : ¬((1 : Fin 2) = 0)), star_mul, lcStar_I, lcStar_ofReal]
      have hS10 : (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.SignalMatrix x).conjTranspose 1 0
          = -(Complex.I) * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) := by
        rw [Matrix.conjTranspose_apply, Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.signalMatrix_apply,
          if_neg (by decide : ¬((0 : Fin 2) = 1)), star_mul, lcStar_I, lcStar_ofReal]
      have hE00 : Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (Real.pi / 2 - a) 0 0
          = Complex.I * star (lcExp a) := by
        rw [Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.phaseRotation_apply, if_pos rfl,
            if_pos rfl, lcExp_unfold]
        exact hz1
      have hE01 : Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (Real.pi / 2 - a) 0 1 = 0 := by
        rw [Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.phaseRotation_apply,
            if_neg (by decide : ¬((0 : Fin 2) = 1))]
      have hE10 : Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (Real.pi / 2 - a) 1 0 = 0 := by
        rw [Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.phaseRotation_apply,
            if_neg (by decide : ¬((1 : Fin 2) = 0))]
      have hE11 : Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (Real.pi / 2 - a) 1 1
          = -(Complex.I) * lcExp a := by
        rw [Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.phaseRotation_apply, if_pos rfl,
          if_neg (by decide : ¬((1 : Fin 2) = 0)), lcExp_unfold_neg]
        exact hz2
      have hF00 : Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(Real.pi / 2)) 0 0 = -(Complex.I) := by
        rw [Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.phaseRotation_apply, if_pos rfl,
            if_pos rfl, lcExp_unfold]
        exact hph1
      have hF01 : Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(Real.pi / 2)) 0 1 = 0 := by
        rw [Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.phaseRotation_apply,
            if_neg (by decide : ¬((0 : Fin 2) = 1))]
      have hF10 : Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(Real.pi / 2)) 1 0 = 0 := by
        rw [Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.phaseRotation_apply,
            if_neg (by decide : ¬((1 : Fin 2) = 0))]
      have hF11 : Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(Real.pi / 2)) 1 1 = Complex.I := by
        rw [Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.phaseRotation_apply, if_pos rfl,
          if_neg (by decide : ¬((1 : Fin 2) = 0)), lcExp_unfold_neg, neg_neg]
        exact lcExp_pi_half
      have hM1 : Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (Real.pi / 2 - a)
          = !![Complex.I * star (lcExp a), 0; 0, -(Complex.I) * lcExp a] := by
        refine lcMat2_eq_of_entries ?_ ?_ ?_ ?_
        · rw [hE00]; rfl
        · rw [hE01]; rfl
        · rw [hE10]; rfl
        · rw [hE11]; rfl
      have hM2 : (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.SignalMatrix x).conjTranspose
          = !![((x : ℂ)), -(Complex.I) * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ);
              -(Complex.I) * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ), ((x : ℂ))] := by
        refine lcMat2_eq_of_entries ?_ ?_ ?_ ?_
        · rw [hS00]; rfl
        · rw [hS01]; rfl
        · rw [hS10]; rfl
        · rw [hS11]; rfl
      have hM4 : Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(Real.pi / 2))
          = !![-(Complex.I), 0; 0, Complex.I] := by
        refine lcMat2_eq_of_entries ?_ ?_ ?_ ?_
        · rw [hF00]; rfl
        · rw [hF01]; rfl
        · rw [hF10]; rfl
        · rw [hF11]; rfl
      rw [hM1, hM2, hM4]
      refine lcMat2_eq_of_entries ?_ ?_ ?_ ?_
      all_goals
        simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
          mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul]
      all_goals
        ring_nf
      all_goals
        simp only [lcI_pow_two, lcI_pow_three, lcI_pow_four,
          neg_one_mul, one_mul, neg_neg, mul_neg]
      all_goals ring

/-- The `lcQspTilde` word of an empty phase list is the identity matrix. -/
theorem lcQspTilde_nil (x : ℝ) : lcQspTilde [] x = 1 := rfl

/-- A nonempty response word equals a product of an initial shifted phase rotation, `lcQspTilde`
with each remaining angle replaced by `Real.pi / 2 - b`, an adjoint signal matrix, and the
stated terminal rotation. -/
theorem lcRespWord_eq_repoWord (x : ℝ) :
    ∀ (as : List ℝ) (a c : ℝ),
      lcRespWord (a :: as) c x =
        Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (Real.pi / 2 - a) *
          (lcQspTilde (as.map (fun b => Real.pi / 2 - b)) x *
            ((Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.SignalMatrix x).conjTranspose *
              Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-c - (((a :: as).length : ℝ)) * (Real.pi / 2)))) := by
  intro as
  induction as with
  | nil =>
      intro a c
      have h0 : Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-c) *
          Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(Real.pi / 2)) =
          Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-c - (((a :: [] : List ℝ).length : ℝ)) * (Real.pi / 2)) := by
        rw [lcPhaseRotation_mul]
        congr 1
        simp
        ring
      show Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (Real.pi / 2 - a) *
          ((Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.SignalMatrix x).conjTranspose *
            (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-c) *
              Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(Real.pi / 2)))) = _
      rw [h0]
      simp only [List.map_nil, lcQspTilde_nil, one_mul]
  | cons b bs ih =>
      intro a c
      have hlen : (((a :: b :: bs).length : ℝ)) = (((b :: bs).length : ℝ)) + 1 := by
        simp [Nat.cast_succ]
      have hmerge : Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-c - (((b :: bs).length : ℝ)) * (Real.pi / 2)) *
          Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(Real.pi / 2)) =
          Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-c - (((a :: b :: bs).length : ℝ)) * (Real.pi / 2)) := by
        rw [lcPhaseRotation_mul, hlen]
        congr 1
        ring
      show Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (Real.pi / 2 - a) *
          ((Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.SignalMatrix x).conjTranspose *
            (lcRespWord (b :: bs) c x * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(Real.pi / 2)))) = _
      rw [ih b c]
      simp only [Matrix.mul_assoc]
      rw [hmerge]
      simp only [List.map_cons, lcQspTilde_cons, Matrix.mul_assoc]

/-- For `x` in `[-1, 1]`, the repository amplitude with the specified shifted and endpoint
angles is the real part of `responseP` plus `Complex.I * sqrt (1 - x^2)` times the real part
of `responseQ`. Both response polynomials use base `lcExp c` and the phase exponentials of
`a :: as`. -/
theorem lcRepoAmp_of_response (a : ℝ) (as : List ℝ) (c x : ℝ)
    (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    lcRepoAmp (Real.pi / 2 - a) (-c - (((a :: as).length : ℝ)) * (Real.pi / 2))
        ((a :: as).tail.map (fun b => Real.pi / 2 - b)) x
      = ((Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseP (lcExp c) ((a :: as).map lcExp)).eval ((x : ℂ))).re
        + Complex.I * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) *
          ((Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseQ (lcExp c) ((a :: as).map lcExp)).eval ((x : ℂ))).re := by
  have hW := lcRespWord_eq_repoWord x as a c
  have hI := lcRespWord_eq x hx1 hx2 (a :: as) c
  show (lcHad * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (Real.pi / 2 - a) *
        lcQspTilde ((a :: as).tail.map (fun b => Real.pi / 2 - b)) x *
        (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.SignalMatrix x).conjTranspose *
        Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-c - (((a :: as).length : ℝ)) * (Real.pi / 2)) * lcHad) 0 0 = _
  have hshape : lcHad * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (Real.pi / 2 - a) *
        lcQspTilde ((a :: as).tail.map (fun b => Real.pi / 2 - b)) x *
        (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.SignalMatrix x).conjTranspose *
        Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-c - (((a :: as).length : ℝ)) * (Real.pi / 2)) * lcHad
      = lcHad * (lcRespWord (a :: as) c x * lcHad) := by
    rw [List.tail_cons, hW]
    simp only [Matrix.mul_assoc]
  rw [hshape, hI]
  have hreal : ((Real.sqrt 2 : ℝ)⁻¹) * ((Real.sqrt 2 : ℝ)⁻¹) = 1 / 2 := by
    rw [← _root_.mul_inv_rev, Real.mul_self_sqrt (by norm_num), one_div]
  have hsq3 : (((Real.sqrt 2 : ℝ)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2 : ℝ)⁻¹ : ℝ) : ℂ)
      = (((1 : ℝ) / 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hreal]
  have hextract : ∀ M : Matrix (Fin 2) (Fin 2) ℂ,
      (lcHad * M * lcHad) 0 0
        = ((1 : ℂ) / 2) * (M 0 0 + M 0 1 + M 1 0 + M 1 1) := by
    intro M
    have hH00 : lcHad 0 0 = (((Real.sqrt 2 : ℝ)⁻¹ : ℝ) : ℂ) := by simp [lcHad]
    have hH01 : lcHad 0 1 = (((Real.sqrt 2 : ℝ)⁻¹ : ℝ) : ℂ) := by simp [lcHad]
    have hH10 : lcHad 1 0 = (((Real.sqrt 2 : ℝ)⁻¹ : ℝ) : ℂ) := by simp [lcHad]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    rw [hH00, hH01, hH10]
    linear_combination (M 0 0 + M 0 1 + M 1 0 + M 1 1) * (hsq3 + lcHalf_ofReal)
  rw [← Matrix.mul_assoc, hextract]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.of_apply]
  have hP2 := lcStar_add_self
    ((Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseP (lcExp c) ((a :: as).map lcExp)).eval ((x : ℂ)))
  have hQ2 := lcStar_add_self
    ((Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseQ (lcExp c) ((a :: as).map lcExp)).eval ((x : ℂ)))
  linear_combination ((1 : ℂ) / 2) * hP2
    + ((1 : ℂ) / 2) * (Complex.I * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ)) * hQ2

end Qatlib.Concepts.QspSimulation.Achievability
