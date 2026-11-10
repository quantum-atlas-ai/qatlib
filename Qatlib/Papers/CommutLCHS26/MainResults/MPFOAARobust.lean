/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.MPFOAAScalar
import Qatlib.Papers.CommutLCHS26.MainResults.TwoSpectra
import Qatlib.Papers.CommutLCHS26.MainResults.MPFOAALCU
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.MPFOAARobust

open Matrix Polynomial Set
open scoped Classical Matrix.Norms.L2Operator NNReal
open MPFOAAChoice PolynomialSecant
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Foundations.PureStateMath
set_option warningAsError false

variable {I H : Type} [Fintype I] [DecidableEq I] [Fintype H] [DecidableEq H]

omit [Fintype H] [DecidableEq H] in

theorem dilation_square (V : Matrix I I ℂ) (hV : V ∈ unitaryGroup I ℂ) :
    hermitianDilation V * hermitianDilation V = 1 := by
  have hl : Vᴴ * V = 1 := hV.1
  have hr : V * Vᴴ = 1 := hV.2
  simp only [hermitianDilation, Matrix.fromBlocks_multiply, Matrix.zero_mul,
    Matrix.mul_zero, zero_add, add_zero, hl, hr]
  exact Matrix.fromBlocks_one

omit [Fintype H] [DecidableEq H] in

theorem dilation_unitary (V : Matrix I I ℂ) (hV : V ∈ unitaryGroup I ℂ) :
    hermitianDilation V ∈ unitaryGroup (I ⊕ I) ℂ := by
  constructor <;> simpa only [Matrix.star_eq_conjTranspose, hermitianDilation_adjoint]
    using! dilation_square V hV

omit [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I] in

theorem dilation_smul (s : ℝ) (C : Matrix I I ℂ) :
    hermitianDilation ((s : ℂ) • C) = (s : ℂ) • hermitianDilation C := by
  ext i j
  cases i <;> cases j <;> simp [hermitianDilation, Matrix.conjTranspose_smul]

theorem sine_le_half (A : ℝ) (hn : 0 < rounds A) :
    Real.sin (angle (queries A)) ≤ 1 / 2 := by
  have hq : 3 ≤ queries A := by unfold queries; omega
  have hqR : (3 : ℝ) ≤ (queries A : ℝ) := by exact_mod_cast hq
  have ha : angle (queries A) ≤ Real.pi / 6 :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by linarith)
  have h := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [(angle_bounds _ (queries_pos A)).1, Real.pi_pos])
    (by linarith [Real.pi_pos] : Real.pi / 6 ≤ Real.pi / 2) ha
  simpa only [Real.sin_pi_div_six] using! h

omit [Fintype H] [DecidableEq H] in

theorem target_endpoints (A : ℝ) :
    (MPFOAAScalar.poly (rounds A)).eval (Real.sin (angle (queries A)) : ℂ) = 1 ∧
      (MPFOAAScalar.poly (rounds A)).eval (-(Real.sin (angle (queries A)) : ℂ)) = -1 := by
  have hp := MPFOAAWord.response_exact A
  have hm := (response_parity (-Complex.I) (List.replicate (queries A) Complex.I)
    (Real.sin (angle (queries A)) : ℂ)).1
  rw [hp] at hm
  simpa [MPFOAAScalar.poly, queries, pow_add, pow_mul] using! And.intro hp hm

omit [Fintype H] [DecidableEq H] in

theorem polynomial_bound (A : ℝ) (hn : 0 < rounds A) (C V : Matrix I I ℂ)
    (hV : V ∈ unitaryGroup I ℂ) (hd : ‖C - V‖ ≤ 1 / 5) :
    ‖aeval (hermitianDilation ((Real.sin (angle (queries A)) : ℂ) • C))
        (MPFOAAScalar.poly (rounds A)) - hermitianDilation V‖ ≤
      2 * (queries A : ℝ) * Real.sin (angle (queries A)) * ‖C - V‖ := by
  let s := Real.sin (angle (queries A))
  let B := hermitianDilation ((s : ℂ) • C)
  let T := hermitianDilation V
  let p := MPFOAAScalar.poly (rounds A)
  let L : ℝ≥0 := ⟨(5 / 4 : ℝ) * (queries A : ℝ), by positivity⟩
  have hs : 0 ≤ s := (sin_pos _ (queries_pos A)).le
  have hs1 : s ≤ 1 / 2 := sine_le_half A hn
  have hC : ‖C‖ ≤ 6 / 5 := by
    have h := norm_add_le (C - V) V
    rw [sub_add_cancel] at h
    linarith [unitary_norm_le_one hV]
  have hX : ‖B‖ ≤ (3 / 5 : ℝ) := by
    dsimp only [B]
    rw [hermitianDilation_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
    nlinarith [norm_nonneg C]
  have hXh : B.IsHermitian := hermitianDilation_adjoint _
  have hsp : s ∈ Ioo (-(3 / 5) : ℝ) (3 / 5) := by constructor <;> linarith
  have hsm : -s ∈ Ioo (-(3 / 5) : ℝ) (3 / 5) := by constructor <;> linarith
  have hl : LipschitzOnWith L (fun y : ℝ => p.eval (y : ℂ)) (Icc (-(3 / 5) : ℝ) (3 / 5)) :=
    MPFOAAScalar.eval_lipschitz (rounds A)
  have hp := norm_secant_le B hXh p (3 / 5) s L hX hsp hl
  have hm := norm_secant_le B hXh p (3 / 5) (-s) L hX hsm hl
  have he : ‖B - (s : ℂ) • T‖ = s * ‖C - V‖ := by
    dsimp only [B, T]
    rw [dilation_smul s C, ← smul_sub, norm_smul, hermitianDilation_sub_norm,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
  have ht : aeval ((s : ℂ) • T) p = T :=
    TwoSpectra.target_polynomial T (dilation_square V hV) (s : ℂ) p
      (target_endpoints A).1 (target_endpoints A).2
  calc
    _ = ‖aeval B p - aeval ((s : ℂ) • T) p‖ := by rw [ht]
    _ ≤ (3 / 2 : ℝ) * (L : ℝ) * ‖B - (s : ℂ) • T‖ := by
      rw [TwoSpectra.decomposition B T (dilation_square V hV)]
      exact TwoSpectra.two_sector_bound T _ _ _ (dilation_unitary V hV) L L.2 hp
        (by simpa only [Complex.ofReal_neg] using! hm)
    _ ≤ _ := by
      rw [he]
      change (3 / 2 : ℝ) * ((5 / 4 : ℝ) * (queries A : ℝ)) * (s * ‖C - V‖) ≤
        2 * (queries A : ℝ) * s * ‖C - V‖
      nlinarith [mul_nonneg (Nat.cast_nonneg (queries A)) (mul_nonneg hs (norm_nonneg (C - V)))]

omit [Fintype I] [DecidableEq I] [Fintype H] [DecidableEq H] in

theorem poly_zero : MPFOAAScalar.poly 0 = (Polynomial.X : Polynomial ℂ) := by
  change responseP (-Complex.I) [Complex.I] = Polynomial.X
  rw [responseP_singleton]
  norm_num

omit [Fintype H] [DecidableEq H] in

theorem polynomial_bound_all (A : ℝ) (C V : Matrix I I ℂ)
    (hV : V ∈ unitaryGroup I ℂ) (hd : ‖C - V‖ ≤ 1 / 5) :
    ‖aeval (hermitianDilation ((Real.sin (angle (queries A)) : ℂ) • C))
        (MPFOAAScalar.poly (rounds A)) - hermitianDilation V‖ ≤
      2 * (queries A : ℝ) * Real.sin (angle (queries A)) * ‖C - V‖ := by
  by_cases hn : rounds A = 0
  · have hq : queries A = 1 := by simp [queries, hn]
    simp only [hq, hn, poly_zero, angle, Nat.cast_one, mul_one, Real.sin_pi_div_two,
      Complex.ofReal_one, one_smul, Polynomial.aeval_X, hermitianDilation_sub_norm]
    nlinarith [norm_nonneg (C - V)]
  · exact polynomial_bound A (Nat.pos_of_ne_zero hn) C V hV hd

theorem word_error (A : ℝ) (C V : Matrix I I ℂ) (U : Matrix H H ℂ) (R : Matrix H I ℂ)
    (hV : V ∈ unitaryGroup I ℂ) (hd : ‖C - V‖ ≤ 1 / 5)
    (h : ProjectedUnitaryEncoding ((Real.sin (angle (queries A)) : ℂ) • C) U R R) :
    ‖compress R (evaluate U (MPFOAAWord.word A R)) R - V‖ ≤
      2 * (queries A : ℝ) * Real.sin (angle (queries A)) * ‖C - V‖ := by
  have he := qsvt_odd_eq_dilation h (-Complex.I) (List.replicate (queries A) Complex.I)
    (by simp only [List.length_replicate, queries]; omega)
  have he' : compress R (evaluate U (MPFOAAWord.word A R)) R =
      (aeval (hermitianDilation ((Real.sin (angle (queries A)) : ℂ) • C))
        (MPFOAAScalar.poly (rounds A))).toBlocks₁₂ := by
    simpa only [MPFOAAWord.word, evaluate_compileQSVT, MPFOAAScalar.poly, queries] using! he
  rw [he']
  have hb := dilation_block12_sub_norm_le
    (aeval (hermitianDilation ((Real.sin (angle (queries A)) : ℂ) • C))
      (MPFOAAScalar.poly (rounds A))) (hermitianDilation V)
  apply le_trans ?_ (polynomial_bound_all A C V hV hd)
  simpa only [show (hermitianDilation V).toBlocks₁₂ = V from rfl] using! hb

theorem amplification_factor (A : ℝ) :
    2 * (queries A : ℝ) * Real.sin (angle (queries A)) ≤ Real.pi := by
  have hq : 0 < (queries A : ℝ) := by exact_mod_cast queries_pos A
  calc
    _ ≤ 2 * (queries A : ℝ) * angle (queries A) :=
      mul_le_mul_of_nonneg_left (Real.sin_le (angle_bounds _ (queries_pos A)).1.le) (by positivity)
    _ = Real.pi := by unfold angle; field_simp

theorem word_error_pi (A : ℝ) (C V : Matrix I I ℂ) (U : Matrix H H ℂ) (R : Matrix H I ℂ)
    (hV : V ∈ unitaryGroup I ℂ) (hd : ‖C - V‖ ≤ 1 / 5)
    (h : ProjectedUnitaryEncoding ((Real.sin (angle (queries A)) : ℂ) • C) U R R) :
    ‖compress R (evaluate U (MPFOAAWord.word A R)) R - V‖ ≤ Real.pi * ‖C - V‖ :=
  (word_error A C V U R hV hd h).trans
    (mul_le_mul_of_nonneg_right (amplification_factor A) (norm_nonneg _))

theorem expanded_error_pi (O : Matrix H H ℂ) (A : ℝ) (hA : 1 ≤ A)
    (C V : Matrix I I ℂ) (hV : V ∈ unitaryGroup I ℂ) (hd : ‖C - V‖ ≤ 1 / 5)
    (R : Matrix H I ℂ) (cs : List (AdjointStep H))
    (h : ProjectedUnitaryEncoding ((A : ℂ)⁻¹ • C) (evaluate O cs) R R) :
    ‖compress (scaleEightFrame R)
        (evaluate (TensorGate (1 : Matrix Bool Bool ℂ) O) (MPFOAAWord.expanded A R cs))
        (scaleEightFrame R) - V‖ ≤ Real.pi * ‖C - V‖ := by
  rw [MPFOAAWord.expanded, (substitute_adjoint_evaluate_cost (TensorGate (1 : Matrix Bool Bool ℂ) O)
    (MPFOAAPadding.body A cs) (MPFOAAWord.word A (scaleEightFrame R))).1]
  exact word_error_pi A C V _ _ hV hd (MPFOAAPadding.body_encoding O A hA C R cs h)

end Qatlib.Papers.CommutLCHS26.MainResults.MPFOAARobust
