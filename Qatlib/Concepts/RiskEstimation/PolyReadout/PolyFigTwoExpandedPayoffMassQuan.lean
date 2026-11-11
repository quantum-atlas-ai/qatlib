/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyReadout.PolyFigTwoExpandedPayoffMassStat
import Qatlib.Concepts.RiskEstimation.PolyRotation.PolyRotationFigTwoDepthCorrectedQuan
import Qatlib.Concepts.BlockEncoding.LinearCombination

/-!
# Flag mass of expanded polynomial preparation

This module computes the basis amplitudes of expanded payoff preparation and identifies its
target-flag mass. The identity connects the compiled corrected rotation word with the
Born-weighted squared-sine payoff.

The quantum risk-analysis setting is described in [WoernerEgger2019].

## Main statements

* `polyFigTwoExpandedPayoffMass`: The expanded preparation's good-flag probability equals the
  Born-weighted squared-sine polynomial payoff; see [WoernerEgger2019].

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ChannelTheory.Stinespring

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.RiskEstimation.PolyRotation
open Qatlib.Concepts.BlockEncoding.LinearCombination

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace Qatlib.Concepts.RiskEstimation.PolyReadout
open Matrix Polynomial
open scoped Classical BigOperators

/-- The extended data gate maps an expanded initial ket to the data-matrix column with flag and
work bits false. -/
private theorem data_gate_columns (n : ℕ) (A : Matrix (Reg n) (Reg n) ℂ) (j : Reg n) :
    figTwoDataGate n A *ᵥ Qatlib.Foundations.PureStateMath.Ket (figTwoStart n j) =
      ∑ x : Reg n, A x j • Qatlib.Foundations.PureStateMath.Ket (figTwoStart n x) := by
  funext q
  obtain ⟨⟨⟨x,b⟩,w⟩,rfl⟩ := (multiKnownSplit n).symm.surjective q
  rw [mulVec_ket_apply]
  simp only [figTwoDataGate, figTwoStart, relabelGate, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
    tensorGate_apply, Matrix.one_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Qatlib.Foundations.PureStateMath.Ket, Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases hb : b = false <;> by_cases hw : w = (fun _ => false) <;>
    simp [hb, hw, ite_mul, mul_ite, ite_and]

/-- The expanded angle word rotates the flag by the negated doubled payoff angle while restoring
the work register. -/
private theorem word_columns (n u : ℕ) (c : ℝ) (fp : Polynomial ℝ) (x : Reg n) :
    reflectionProgramMatrix (figTwoAngleWord n u c fp) *ᵥ Qatlib.Foundations.PureStateMath.Ket (figTwoStart n x) =
      ∑ b : Bool,
        ((qubitEulerRotation (-2*(c*riskSinTaylor u c (fp.eval (figTwoRegEval x : ℝ))+Real.pi/4))) *ᵥ Qatlib.Foundations.PureStateMath.Ket false) b •
          Qatlib.Foundations.PureStateMath.Ket ((multiKnownSplit n).symm ((x,b),fun _ => false)) := by
  have hp : (-riskFigTwoAnglePoly u c fp).natDegree ≤ fp.natDegree*(2*u+1) := by
    simpa only [Polynomial.natDegree_neg] using!
        riskFigTwoAnglePoly_degree u c fp fp.natDegree le_rfl
  have hs := (riskPolyRotationFigTwoCorrected n (fp.natDegree*(2*u+1))
    (-riskFigTwoAnglePoly u c fp) hp).2.1 x
  simp only [Polynomial.eval_neg] at hs
  have he : -(riskFigTwoAnglePoly u c fp).eval (figTwoRegEval x : ℝ) =
      -2*(c*riskSinTaylor u c (fp.eval (figTwoRegEval x : ℝ))+Real.pi/4) := by
    rw [riskFigTwoAnglePoly_eval]
    ring
  rw [he] at hs
  simpa only [run_reflectionCompile, ApplyGate, figTwoAngleWord, figTwoStart] using! hs

/-- An expanded preparation amplitude factors into the data amplitude and flag-rotation
amplitude when the work register is zero, and vanishes otherwise. -/
private theorem preparation_entry (n : ℕ) (A : Matrix (Reg n) (Reg n) ℂ)
    (j : Reg n) (u : ℕ) (c : ℝ) (fp : Polynomial ℝ)
    (x : Reg n) (b : Bool) (w : Reg (n-1)) :
    (figTwoExpandedPreparation n A u c fp *ᵥ Qatlib.Foundations.PureStateMath.Ket (figTwoStart n j))
      ((multiKnownSplit n).symm ((x,b),w)) =
      if w = (fun _ => false) then
        A x j * ((qubitEulerRotation (-2*(c*riskSinTaylor u c
          (fp.eval (figTwoRegEval x : ℝ))+Real.pi/4))) *ᵥ Qatlib.Foundations.PureStateMath.Ket false) b else 0 := by
  rw [figTwoExpandedPreparation, ← Matrix.mulVec_mulVec, data_gate_columns,
    Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul, word_columns]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Qatlib.Foundations.PureStateMath.Ket,
    Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases hw : w = (fun _ => false) <;>
    simp [hw, ite_and, ite_mul, mul_ite, Finset.mul_sum]

/-- The expanded preparation's good-flag probability equals the Born-weighted squared-sine
polynomial payoff; see [WoernerEgger2019]. -/
theorem polyFigTwoExpandedPayoffMass : PolyFigTwoExpandedPayoffMass := by
  intro n A j u c fp _
  unfold MeasureProb figTwoGoodSet
  rw [Finset.sum_filter, ← (multiKnownSplit n).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  have ht (x : Reg n) (b : Bool) (w : Reg (n-1)) :
      ((multiKnownSplit n).symm ((x,b),w)) (figTwoTargetWire n) = b :=
    multiKnownJoin_target n x b w
  simp only [ht, BornProb, preparation_entry]
  have hrot (x : Reg n) :
      ((qubitEulerRotation (-2*(c*riskSinTaylor u c (fp.eval (figTwoRegEval x : ℝ))+Real.pi/4))) *ᵥ Qatlib.Foundations.PureStateMath.Ket false) true =
        (Real.sin (c*riskSinTaylor u c (fp.eval (figTwoRegEval x : ℝ))+Real.pi/4) : ℂ) := by
    rw [mulVec_ket_apply]
    have he : (-2*(c*riskSinTaylor u c (fp.eval (figTwoRegEval x : ℝ))+Real.pi/4))/2 =
        -(c*riskSinTaylor u c (fp.eval (figTwoRegEval x : ℝ))+Real.pi/4) := by ring
    change -(Real.sin ((-2*(c*riskSinTaylor u c (fp.eval (figTwoRegEval x : ℝ))+Real.pi/4))/2) : ℂ) = _
    rw [he, Real.sin_neg, Complex.ofReal_neg, neg_neg]
  have hn (z : ℂ) (w : Reg (n-1)) :
      ‖(if w = (fun _ => false) then z else 0)‖^2 =
        if w = (fun _ => false) then ‖z‖^2 else 0 := by
    split_ifs <;> simp
  simp only [Fintype.sum_bool, Bool.false_eq_true, if_true, if_false,
    Finset.sum_const_zero, add_zero, zero_add]
  apply Finset.sum_congr rfl
  intro x _
  rw [hrot x]
  simp only [hn, Finset.sum_ite_eq', Finset.mem_univ, if_true, norm_mul,
    mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, mulVec_ket_apply]

end Qatlib.Concepts.RiskEstimation.PolyReadout
