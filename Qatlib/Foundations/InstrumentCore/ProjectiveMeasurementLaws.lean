/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
import Qatlib.Foundations.InstrumentCore.Measurement.MeasurementLaws
import Qatlib.Foundations.PureStateMath.Qubit
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement

namespace Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws

open Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem measureProb_applyGate_univ {U : Matrix I I ℂ}
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (ψ : QState I) :
    MeasureProb (ApplyGate U ψ) Finset.univ = MeasureProb ψ Finset.univ := by
  change (∑ i, ‖(U *ᵥ ψ) i‖ ^ 2) = ∑ i, ‖ψ i‖ ^ 2
  simp_rw [← Complex.normSq_eq_norm_sq]
  exact sum_normSq_mulVec_of_mem_unitaryGroup hU ψ

theorem isOrthogonalProjector_compl {P : Matrix I I ℂ}
    (hP : IsOrthogonalProjector P) : IsOrthogonalProjector (1 - P) := by
  have hid : P * P = P := hP.1
  have hstar : Pᴴ = P := hP.2
  refine ⟨?_, ?_⟩
  · change (1 - P) * (1 - P) = 1 - P
    simp only [sub_mul, mul_sub, one_mul, mul_one, hid]
    abel
  · change (1 - P)ᴴ = 1 - P
    simp [hstar]
omit [DecidableEq I] in

private theorem inner_projector {P : Matrix I I ℂ}
    (hP : IsOrthogonalProjector P) (ψ : QState I) :
    Inner (ApplyGate P ψ) (ApplyGate P ψ) = Inner ψ (ApplyGate P ψ) := by
  have hPP : P.conjTranspose * P = P := by
    have hstar : P.conjTranspose = P := hP.2
    rw [hstar]
    exact hP.1
  simp only [Qatlib.Foundations.PureStateMath.Inner, ApplyGate]
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hPP,
    Matrix.dotProduct_mulVec]

omit [DecidableEq I] in

private theorem inner_add_right (ψ φ χ : QState I) :
    Inner ψ (φ + χ) = Inner ψ φ + Inner ψ χ := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.add_apply, mul_add,
      Finset.sum_add_distrib]

private theorem inner_self_re (ψ : QState I) :
    (Inner ψ ψ).re = MeasureProb ψ Finset.univ := by
  rw [inner_self, ← Complex.ofReal_sum]
  simp only [Complex.ofReal_re, MeasureProb, BornProb]

theorem projectiveBranchMass_add {P : Matrix I I ℂ}
    (hP : IsOrthogonalProjector P) (ψ : QState I) :
    ProjectiveBranchMass P false ψ + ProjectiveBranchMass P true ψ =
      MeasureProb ψ Finset.univ := by
  change MeasureProb (ApplyGate (1 - P) ψ) Finset.univ +
    MeasureProb (ApplyGate P ψ) Finset.univ = MeasureProb ψ Finset.univ
  rw [← inner_self_re, ← inner_self_re, ← inner_self_re,
    inner_projector (isOrthogonalProjector_compl hP), inner_projector hP,
    ← Complex.add_re, ← inner_add_right]
  have hsum : ApplyGate (1 - P) ψ + ApplyGate P ψ = ψ := by
    simp [ApplyGate, Matrix.sub_mulVec]
  rw [hsum]

theorem sum_measureProb_collapse_partition (ψ : QState I) {n : ℕ}
    (label : I → Fin n) :
    (∑ o : Fin n, MeasureProb
      (Collapse ψ (Finset.univ.filter (fun i => label i = o))) Finset.univ) =
      MeasureProb ψ Finset.univ := by
  simp_rw [measureProb_collapse, Finset.inter_univ]
  simp only [MeasureProb, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

end Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
