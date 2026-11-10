/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.Postselection
import Qatlib.Concepts.MatrixAccess.FrameFilterProd
import Qatlib.Concepts.QsvtCore.QsVtMain.CPPPhaseCompiler
import Qatlib.Concepts.OperatorErrors.Robustness
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalConsumers
import Qatlib.Concepts.MatrixAccess.FrameFilterUse
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ImplementationBackendDefs
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ImplementationBackend
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.MatrixAccess.FrameFilterProd
open Qatlib.Concepts.MatrixAccess.FrameFilterUse
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.QsvtCore.QsVtStability
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
namespace ConstructionStageA
namespace WalkSpectral4

open Matrix
open Qatlib
open scoped BigOperators Classical Matrix.Norms.L2Operator

structure FiniteComplex where

  re : ℚ

  im : ℚ
  deriving DecidableEq, Repr

def FiniteComplex.toComplex (z : FiniteComplex) : ℂ :=
  (z.re : ℂ) + (z.im : ℂ) * Complex.I

structure FiniteFrameData (n m : ℕ) where

  bits : ℕ

  entries : Fin m → Reg n → FiniteComplex

  entryError : ℝ

  entryError_nonneg : 0 ≤ entryError

noncomputable def FiniteFrameData.realize {n m : ℕ} (d : FiniteFrameData n m) :
    Matrix (Reg n) (Fin m) ℂ :=
  fun x j => (d.entries j x).toComplex

@[simp] theorem FiniteFrameData.realize_apply {n m : ℕ} (d : FiniteFrameData n m)
    (x : Reg n) (j : Fin m) : d.realize x j = (d.entries j x).toComplex := rfl

structure FrameDataFidelity {n m : ℕ} (d : FiniteFrameData n m)
    (F : Matrix (Reg n) (Fin m) ℂ) : Prop where

  entrywise : ∀ x j, ‖F x j - d.realize x j‖ ≤ d.entryError

@[simp] theorem stateVector_eq_toEuclidean_fromVec {I : Type} [Fintype I] [DecidableEq I]
    (v : QState I) : stateVector v = toEuclidean_fromVec v := rfl

def finiteFrameBitCost {n m : ℕ} (d : FiniteFrameData n m) : ℕ :=
  d.bits * (2 ^ n * m)

def finiteFrameOpError {n m : ℕ} (d : FiniteFrameData n m) : ℝ :=
  d.entryError * (((2 ^ n : ℕ) : ℝ) * (m : ℝ))

def finiteFrameProjectorError {n m : ℕ} (d : FiniteFrameData n m) : ℝ :=
  2 * finiteFrameOpError d + (finiteFrameOpError d) ^ 2

noncomputable def finiteFrameProjector {n m : ℕ} (d : FiniteFrameData n m) :
    Matrix (Reg n) (Reg n) ℂ := rangeProjector d.realize

def finiteFrameTarget {n m : ℕ} (d : FiniteFrameData n m) (ψ : QState (Fin m)) :
    QState (Reg n) := d.realize *ᵥ ψ

noncomputable def finiteFramePrepared {n m : ℕ} (d : FiniteFrameData n m)
    (ψ : QState (Fin m)) : QState (Reg n) :=
  toVec_fromEuclidean (NormedSpace.normalize (stateVector (finiteFrameTarget d ψ)))

theorem card_le_sq (n : ℕ) : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · have h1 : n ≤ n ^ 2 := by simpa [pow_two] using! (Nat.mul_le_mul_right n h)
    exact_mod_cast h1

theorem comp_le_norm {C : Type} [Fintype C] [DecidableEq C] (v : C → ℂ) (j : C) :
    ‖v j‖ ≤ ‖toEuclidean_fromVec v‖ := by
  have h1 : ‖v j‖ ^ 2 ≤ ∑ i, ‖v i‖ ^ 2 := by
    simpa using! (Finset.single_le_sum (f := fun i : C => ‖v i‖ ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j))
  have h2 : ‖v j‖ ^ 2 ≤ ‖toEuclidean_fromVec v‖ ^ 2 := by
    rw [norm_toEuclidean_fromVec_sq]
    exact h1
  exact le_of_sq_le_sq h2 (norm_nonneg _)

theorem entrywise_opNorm_le {R C : Type} [Fintype R] [DecidableEq R] [Fintype C]
    [DecidableEq C] {A : Matrix R C ℂ} {ε : ℝ} (h : ∀ i j, ‖A i j‖ ≤ ε)
    (hε : 0 ≤ ε) (rows cols : ℕ) (hrows : Fintype.card R = rows)
    (hcols : Fintype.card C = cols) :
    ‖A‖ ≤ ε * ((rows : ℝ) * (cols : ℝ)) := by
  have hmul : ∀ v : C → ℂ,
      ‖toEuclidean_fromVec (A *ᵥ v)‖ ≤ (ε * ((rows : ℝ) * (cols : ℝ))) *
        ‖toEuclidean_fromVec v‖ := by
    intro v
    have hrow : ∀ i, ‖(A *ᵥ v) i‖ ≤ ε * (cols : ℝ) * ‖toEuclidean_fromVec v‖ := by
      intro i
      show ‖∑ j, A i j * v j‖ ≤ _
      calc ‖∑ j, A i j * v j‖ ≤ ∑ j, ‖A i j * v j‖ :=
            norm_sum_le Finset.univ (fun j => A i j * v j)
        _ ≤ ∑ j, (ε * ‖v j‖) := by
            refine Finset.sum_le_sum fun j _ => ?_
            exact (norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right (h i j) (norm_nonneg (v j)))
        _ ≤ ∑ j, (ε * ‖toEuclidean_fromVec v‖) := by
            refine Finset.sum_le_sum fun j _ => ?_
            exact mul_le_mul_of_nonneg_left (comp_le_norm v j) hε
        _ = ε * (cols : ℝ) * ‖toEuclidean_fromVec v‖ := by
            rw [Finset.sum_const, Finset.card_univ, hcols, nsmul_eq_mul]
            ring
    have hsq : ‖toEuclidean_fromVec (A *ᵥ v)‖ ^ 2
        ≤ (ε * ((rows : ℝ) * (cols : ℝ)) * ‖toEuclidean_fromVec v‖) ^ 2 := by
      rw [norm_toEuclidean_fromVec_sq]
      calc ∑ i, ‖(A *ᵥ v) i‖ ^ 2
          ≤ ∑ i, (ε * (cols : ℝ) * ‖toEuclidean_fromVec v‖) ^ 2 := by
              refine Finset.sum_le_sum fun i _ => ?_
              have hh := mul_self_le_mul_self (norm_nonneg _) (hrow i)
              simpa [pow_two] using! hh
        _ = (rows : ℝ) * (ε * (cols : ℝ) * ‖toEuclidean_fromVec v‖) ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, hrows, nsmul_eq_mul]
        _ ≤ (ε * ((rows : ℝ) * (cols : ℝ)) * ‖toEuclidean_fromVec v‖) ^ 2 := by
              have hN : (rows : ℝ) ≤ (rows : ℝ) ^ 2 := card_le_sq rows
              have hK2 : 0 ≤ (ε * (cols : ℝ) * ‖toEuclidean_fromVec v‖) ^ 2 := sq_nonneg _
              calc (rows : ℝ) *
                    (ε * (cols : ℝ) * ‖toEuclidean_fromVec v‖) ^ 2
                  ≤ ((rows : ℝ)) ^ 2 *
                    (ε * (cols : ℝ) * ‖toEuclidean_fromVec v‖) ^ 2 :=
                      mul_le_mul_of_nonneg_right hN hK2
                _ = ((rows : ℝ) *
                      (ε * (cols : ℝ) * ‖toEuclidean_fromVec v‖)) ^ 2 := by ring
                _ = (ε * ((rows : ℝ) * (cols : ℝ)) *
                      ‖toEuclidean_fromVec v‖) ^ 2 := by ring
    exact le_of_sq_le_sq hsq (by positivity)
  exact l2_opNorm_le_of_mulVec_le (by positivity) A hmul

theorem matrix_smul_norm_le {I : Type} [Fintype I] [DecidableEq I] (r : ℂ)
    (A : Matrix I I ℂ) : ‖r • A‖ ≤ ‖r‖ * ‖A‖ := by
  refine l2_opNorm_le_of_mulVec_le (by positivity) (r • A) ?_
  intro v
  rw [Matrix.smul_mulVec]
  have hsm : toEuclidean_fromVec (r • (A *ᵥ v)) = r • toEuclidean_fromVec (A *ᵥ v) := rfl
  rw [hsm]
  calc ‖r • toEuclidean_fromVec (A *ᵥ v)‖ = ‖r‖ * ‖toEuclidean_fromVec (A *ᵥ v)‖ := by
        rw [norm_smul]
      _ ≤ ‖r‖ * (‖A‖ * ‖toEuclidean_fromVec v‖) := by
        gcongr
        exact l2_norm_mulVec_fromVec_le A v
      _ = (‖r‖ * ‖A‖) * ‖toEuclidean_fromVec v‖ := by ring

theorem finiteFrame_opError {n m : ℕ} {d : FiniteFrameData n m}
    {F : Matrix (Reg n) (Fin m) ℂ} (hf : FrameDataFidelity d F) :
    ‖d.realize - F‖ ≤ finiteFrameOpError d := by
  have hA : ∀ i j, ‖(d.realize - F) i j‖ ≤ d.entryError := by
    intro i j
    have h := hf.entrywise i j
    rw [Matrix.sub_apply]
    exact (le_of_eq (norm_sub_rev _ _)).trans h
  have h1 := entrywise_opNorm_le hA d.entryError_nonneg (2 ^ n) m (card_reg n)
    (Fintype.card_fin m)
  calc ‖d.realize - F‖ ≤ d.entryError * (((2 ^ n : ℕ) : ℝ) * (m : ℝ)) := h1
    _ = finiteFrameOpError d := rfl

theorem toEuclidean_fromVec_add {I : Type} [Fintype I] [DecidableEq I] (a b : QState I) :
    toEuclidean_fromVec (a + b) = toEuclidean_fromVec a + toEuclidean_fromVec b := by
  rfl

theorem finiteFrame_realize_norm_le {n m : ℕ} {d : FiniteFrameData n m}
    {F : Matrix (Reg n) (Fin m) ℂ} (hF : IsIsometry F) (hf : FrameDataFidelity d F) :
    ‖d.realize‖ ≤ 1 + finiteFrameOpError d := by
  have hFn : ‖F‖ ≤ 1 := Qatlib.Concepts.BlockEncoding.Encoding.IsIsometry.norm_le_one hF
  have hG : ‖d.realize - F‖ ≤ finiteFrameOpError d := finiteFrame_opError hf
  have hδ0 : 0 ≤ finiteFrameOpError d := by
    unfold finiteFrameOpError
    exact mul_nonneg d.entryError_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _))
  refine l2_opNorm_le_of_mulVec_le (by linarith) d.realize ?_
  intro v
  have hdecomp : toEuclidean_fromVec (d.realize *ᵥ v)
      = toEuclidean_fromVec (F *ᵥ v) + toEuclidean_fromVec ((d.realize - F) *ᵥ v) := by
    have hid : d.realize = F + (d.realize - F) := by
      ext i j
      simp [Matrix.sub_apply, Matrix.add_apply]
    rw [hid, Matrix.add_mulVec, ← hid]
    exact toEuclidean_fromVec_add _ _
  rw [hdecomp]
  calc ‖toEuclidean_fromVec (F *ᵥ v) + toEuclidean_fromVec ((d.realize - F) *ᵥ v)‖
      ≤ ‖toEuclidean_fromVec (F *ᵥ v)‖
        + ‖toEuclidean_fromVec ((d.realize - F) *ᵥ v)‖ := norm_add_le _ _
    _ ≤ ‖F‖ * ‖toEuclidean_fromVec v‖
        + ‖d.realize - F‖ * ‖toEuclidean_fromVec v‖ := by
        refine add_le_add ?_ ?_
        · exact l2_norm_mulVec_fromVec_le F v
        · exact l2_norm_mulVec_fromVec_le (d.realize - F) v
    _ ≤ 1 * ‖toEuclidean_fromVec v‖ + finiteFrameOpError d * ‖toEuclidean_fromVec v‖ := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_right hFn (norm_nonneg _)
        · exact mul_le_mul_of_nonneg_right hG (norm_nonneg _)
    _ = (1 + finiteFrameOpError d) * ‖toEuclidean_fromVec v‖ := by ring

theorem finiteFrame_target_diff_le {n m : ℕ} {d : FiniteFrameData n m}
    {F : Matrix (Reg n) (Fin m) ℂ} {ψ : QState (Fin m)}
    (hf : FrameDataFidelity d F) :
    ‖stateVector (d.realize *ᵥ ψ) - stateVector (F *ᵥ ψ)‖
      ≤ finiteFrameOpError d * ‖stateVector ψ‖ := by
  have hG : ‖d.realize - F‖ ≤ finiteFrameOpError d := finiteFrame_opError hf
  have hstate : stateVector ((d.realize - F) *ᵥ ψ)
      = stateVector (d.realize *ᵥ ψ) - stateVector (F *ᵥ ψ) := by
    rw [Matrix.sub_mulVec]
    rfl
  rw [← hstate]
  have h := l2_norm_mulVec_fromVec_le (d.realize - F) ψ
  simp only [stateVector_eq_toEuclidean_fromVec] at h ⊢
  calc ‖toEuclidean_fromVec ((d.realize - F) *ᵥ ψ)‖
      ≤ ‖d.realize - F‖ * ‖toEuclidean_fromVec ψ‖ := h
    _ ≤ finiteFrameOpError d * ‖toEuclidean_fromVec ψ‖ :=
      mul_le_mul_of_nonneg_right hG (norm_nonneg _)

theorem finiteFrame_target_norm_lower {n m : ℕ} {d : FiniteFrameData n m}
    {F : Matrix (Reg n) (Fin m) ℂ} {ψ : QState (Fin m)}
    (hF : IsIsometry F) (hψ : Normalized ψ) (hf : FrameDataFidelity d F) :
    1 - finiteFrameOpError d ≤ ‖stateVector (d.realize *ᵥ ψ)‖ := by
  have hFnψ : ‖stateVector (F *ᵥ ψ)‖ = 1 := by
    rw [Qatlib.Concepts.BlockEncoding.Postselection.Encoding.IsIsometry.stateVector_norm hF]
    exact (normalized_iff_stateVector_norm ψ).mp hψ
  have hdiff : ‖stateVector (d.realize *ᵥ ψ) - stateVector (F *ᵥ ψ)‖
      ≤ finiteFrameOpError d := by
    have h := finiteFrame_target_diff_le (ψ := ψ) hf
    calc ‖stateVector (d.realize *ᵥ ψ) - stateVector (F *ᵥ ψ)‖
        ≤ finiteFrameOpError d * ‖stateVector ψ‖ := h
      _ = finiteFrameOpError d := by
          rw [(normalized_iff_stateVector_norm ψ).mp hψ]
          ring
  have habs : |‖stateVector (d.realize *ᵥ ψ)‖ - ‖stateVector (F *ᵥ ψ)‖|
      ≤ ‖stateVector (d.realize *ᵥ ψ) - stateVector (F *ᵥ ψ)‖ :=
    abs_norm_sub_norm_le _ _
  have h1 := (abs_le.mp habs).1
  have h2 : -finiteFrameOpError d ≤ ‖stateVector (d.realize *ᵥ ψ)‖ - 1 := by
    have h3 : -‖stateVector (d.realize *ᵥ ψ) - stateVector (F *ᵥ ψ)‖
        ≤ ‖stateVector (d.realize *ᵥ ψ)‖ - 1 := by linarith [h1, hFnψ]
    linarith [h3, hdiff]
  linarith

theorem finiteFrame_prepared_normalized {n m : ℕ} {d : FiniteFrameData n m}
    {F : Matrix (Reg n) (Fin m) ℂ} {ψ : QState (Fin m)}
    (hF : IsIsometry F) (hψ : Normalized ψ) (hf : FrameDataFidelity d F)
    (hδ : finiteFrameOpError d < 1) :
    Normalized (finiteFramePrepared d ψ) := by
  have hlow : 1 - finiteFrameOpError d ≤ ‖stateVector (finiteFrameTarget d ψ)‖ :=
    finiteFrame_target_norm_lower hF hψ hf
  have hne : stateVector (finiteFrameTarget d ψ) ≠ 0 := by
    intro hz
    have hz' : ‖stateVector (finiteFrameTarget d ψ)‖ = 0 := by rw [hz, norm_zero]
    linarith
  have hprep : stateVector (finiteFramePrepared d ψ)
      = NormedSpace.normalize (stateVector (finiteFrameTarget d ψ)) := by
    simp [finiteFramePrepared, stateVector, toVec_fromEuclidean]
  have hnorm : ‖stateVector (finiteFramePrepared d ψ)‖ = 1 := by
    rw [hprep]
    exact NormedSpace.norm_normalize hne
  exact (normalized_iff_stateVector_norm _).mpr hnorm

theorem real_norm_eq_abs (r : ℝ) : ‖r‖ = |r| := by
  by_cases h : 0 ≤ r
  · rw [Real.norm_of_nonneg h, abs_of_nonneg h]
  · have hr : r < 0 := lt_of_not_ge h
    rw [← norm_neg, Real.norm_of_nonneg (le_of_lt (neg_pos.mpr hr)), abs_of_neg hr]

theorem real_norm_le_abs {r c : ℝ} (h : |r| ≤ c) : ‖r‖ ≤ c := by
  by_cases h0 : 0 ≤ r
  · rw [Real.norm_of_nonneg h0]
    have h2 : |r| = r := abs_of_nonneg h0
    rw [h2] at h
    exact h
  · have hr : r < 0 := lt_of_not_ge h0
    rw [← norm_neg, Real.norm_of_nonneg (le_of_lt (neg_pos.mpr hr))]
    have h2 : |r| = -r := abs_of_neg hr
    rw [h2] at h
    linarith

theorem finiteFrame_prepared_error {n m : ℕ} {d : FiniteFrameData n m}
    {F : Matrix (Reg n) (Fin m) ℂ} {ψ : QState (Fin m)}
    (hF : IsIsometry F) (hψ : Normalized ψ) (hf : FrameDataFidelity d F)
    (hδ : finiteFrameOpError d < 1) :
    ‖stateVector (finiteFramePrepared d ψ) - stateVector (F *ᵥ ψ)‖
      ≤ 2 * finiteFrameOpError d * ‖stateVector (d.realize *ᵥ ψ)‖⁻¹ := by
  set δ := finiteFrameOpError d with hδdef
  set s : ℝ := ‖stateVector (d.realize *ᵥ ψ)‖ with hsdef
  set w : EuclideanSpace ℂ (Reg n) := stateVector (d.realize *ᵥ ψ) with hwdef
  set v : EuclideanSpace ℂ (Reg n) := stateVector (F *ᵥ ψ) with hvdef
  have hδ0 : 0 ≤ δ := by
    unfold δ
    exact mul_nonneg d.entryError_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _))
  have hlow : 1 - δ ≤ s := by
    have h := finiteFrame_target_norm_lower hF hψ hf
    exact h
  have hs : 0 < s := by linarith
  have hFnψ : ‖v‖ = 1 := by
    rw [hvdef,
      Qatlib.Concepts.BlockEncoding.Postselection.Encoding.IsIsometry.stateVector_norm hF]
    exact (normalized_iff_stateVector_norm ψ).mp hψ
  have hdiff : ‖w - v‖ ≤ δ := by
    have h := finiteFrame_target_diff_le (ψ := ψ) hf
    have h2 : ‖w - v‖ = ‖stateVector (d.realize *ᵥ ψ) - stateVector (F *ᵥ ψ)‖ := by
      rw [hwdef, hvdef]
    rw [h2]
    calc ‖stateVector (d.realize *ᵥ ψ) - stateVector (F *ᵥ ψ)‖
        ≤ δ * ‖stateVector ψ‖ := h
      _ = δ := by rw [(normalized_iff_stateVector_norm ψ).mp hψ]; ring
  have hsn : |s - 1| ≤ δ := by
    have habs : |‖stateVector (d.realize *ᵥ ψ)‖ - ‖stateVector (F *ᵥ ψ)‖|
        ≤ ‖stateVector (d.realize *ᵥ ψ) - stateVector (F *ᵥ ψ)‖ := abs_norm_sub_norm_le _ _
    have h1 := (abs_le.mp habs).1
    have h2 := (abs_le.mp habs).2
    rw [abs_le]
    constructor
    · linarith [h1, hFnψ, hdiff]
    · linarith [h2, hFnψ, hdiff]
  have hinv : |s⁻¹ - 1| ≤ δ / s := by
    have hform : s⁻¹ - 1 = (1 - s) / s := by
      have h1 : s⁻¹ * s = 1 := by field_simp
      rw [div_eq_mul_inv]
      calc s⁻¹ - 1 = s⁻¹ - s⁻¹ * s := by rw [h1]
        _ = s⁻¹ * (1 - s) := by ring
        _ = (1 - s) * s⁻¹ := by ring
    rw [hform, abs_div, abs_of_pos hs]
    have h1 : |1 - s| ≤ δ := by
      rw [abs_sub_comm]
      exact hsn
    have h3 : |1 - s| / s ≤ δ / s := by
      exact div_le_div_of_nonneg_right h1 (le_of_lt hs)
    exact h3
  have hprep : stateVector (finiteFramePrepared d ψ) = s⁻¹ • w := by
    have h1 : stateVector (finiteFramePrepared d ψ)
        = NormedSpace.normalize (stateVector (d.realize *ᵥ ψ)) := by
      simp only [finiteFramePrepared, finiteFrameTarget]
      exact (show stateVector (toVec_fromEuclidean _) = _ from rfl)
    rw [h1, hsdef, hwdef]
    rfl
  rw [hprep]
  change ‖s⁻¹ • w - v‖ ≤ 2 * δ * ‖stateVector (d.realize *ᵥ ψ)‖⁻¹
  have hdecomp : s⁻¹ • w - v = s⁻¹ • (w - v) + (s⁻¹ - 1) • v := by
    simp only [smul_sub, sub_smul, one_smul]
    module
  rw [hdecomp]
  calc ‖s⁻¹ • (w - v) + (s⁻¹ - 1) • v‖
      ≤ ‖s⁻¹ • (w - v)‖ + ‖(s⁻¹ - 1) • v‖ := norm_add_le _ _
    _ ≤ s⁻¹ * ‖w - v‖ + (δ / s) * ‖v‖ := by
        refine add_le_add ?_ ?_
        · calc ‖s⁻¹ • (w - v)‖ = ‖s⁻¹‖ * ‖w - v‖ := by rw [norm_smul]
            _ ≤ s⁻¹ * ‖w - v‖ := by
                have h1 : ‖s⁻¹‖ ≤ s⁻¹ := by
                  refine real_norm_le_abs ?_
                  rw [abs_of_nonneg (inv_nonneg.mpr (le_of_lt hs))]
                exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        · calc ‖(s⁻¹ - 1) • v‖ = ‖s⁻¹ - 1‖ * ‖v‖ := by rw [norm_smul]
            _ ≤ (δ / s) * ‖v‖ := by
                have h1 : ‖s⁻¹ - 1‖ ≤ δ / s := by
                  refine real_norm_le_abs hinv
                exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ ≤ 2 * (δ * s⁻¹) := by
        have h1 : s⁻¹ * ‖w - v‖ ≤ s⁻¹ * δ :=
          mul_le_mul_of_nonneg_left hdiff (by positivity)
        have h2 : (δ / s) * ‖v‖ = δ * s⁻¹ := by
          rw [div_eq_mul_inv, hFnψ]
          ring
        rw [h2]
        calc s⁻¹ * ‖w - v‖ + δ * s⁻¹ ≤ s⁻¹ * δ + δ * s⁻¹ := add_le_add h1 (le_refl _)
          _ = 2 * (δ * s⁻¹) := by ring
    _ = 2 * δ * ‖stateVector (d.realize *ᵥ ψ)‖⁻¹ := by rw [hsdef, hwdef]; ring

theorem finiteFrame_projector_deviation {n m : ℕ} {d : FiniteFrameData n m}
    {F : Matrix (Reg n) (Fin m) ℂ} (hF : IsIsometry F) (hf : FrameDataFidelity d F) :
    ‖finiteFrameProjector d - rangeProjector F‖ ≤ finiteFrameProjectorError d := by
  have hδ : 0 ≤ finiteFrameOpError d :=
    mul_nonneg d.entryError_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hG : ‖d.realize - F‖ ≤ finiteFrameOpError d := finiteFrame_opError hf
  have hFn : ‖F‖ ≤ 1 := Qatlib.Concepts.BlockEncoding.Encoding.IsIsometry.norm_le_one hF
  have hGn : ‖d.realize‖ ≤ 1 + finiteFrameOpError d := finiteFrame_realize_norm_le hF hf
  have hDstar : ‖d.realizeᴴ - Fᴴ‖ = ‖d.realize - F‖ := by
    rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
  have hFstar : ‖Fᴴ‖ = ‖F‖ := Matrix.l2_opNorm_conjTranspose F
  have hDstar' : ‖d.realizeᴴ - Fᴴ‖ ≤ finiteFrameOpError d := hDstar.le.trans hG
  have key : finiteFrameProjector d - rangeProjector F
      = d.realize * (d.realizeᴴ - Fᴴ) + (d.realize - F) * Fᴴ := by
    simp only [finiteFrameProjector, rangeProjector]
    rw [Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [key]
  calc ‖d.realize * (d.realizeᴴ - Fᴴ) + (d.realize - F) * Fᴴ‖
      ≤ ‖d.realize * (d.realizeᴴ - Fᴴ)‖ + ‖(d.realize - F) * Fᴴ‖ := norm_add_le _ _
    _ ≤ ‖d.realize‖ * ‖d.realizeᴴ - Fᴴ‖ + ‖d.realize - F‖ * ‖Fᴴ‖ := by
        refine add_le_add ?_ ?_
        · exact Matrix.l2_opNorm_mul _ _
        · exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 + finiteFrameOpError d) * finiteFrameOpError d
        + finiteFrameOpError d * 1 := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul hGn hDstar' (by positivity) (by positivity)
        · calc ‖d.realize - F‖ * ‖Fᴴ‖ ≤ finiteFrameOpError d * ‖F‖ :=
              mul_le_mul hG hFstar.le (by positivity) (by positivity)
            _ ≤ finiteFrameOpError d * 1 :=
              mul_le_mul_of_nonneg_left hFn (by positivity)
    _ = 2 * finiteFrameOpError d + (finiteFrameOpError d) ^ 2 := by ring
    _ = finiteFrameProjectorError d := rfl

theorem isPhase_norm_one {z : ℂ} (hz : IsPhase z) : ‖z‖ = 1 := by
  have hstar : ‖star z‖ = ‖z‖ := by simp
  have hone : ‖z‖ * ‖z‖ = 1 := by
    calc ‖z‖ * ‖z‖ = ‖star z‖ * ‖z‖ := by rw [hstar]
      _ = ‖star z * z‖ := by rw [norm_mul]
      _ = ‖(1 : ℂ)‖ := by rw [hz]
      _ = 1 := by simp
  nlinarith [norm_nonneg z]

theorem finiteFrame_phase_deviation {n m : ℕ} {d : FiniteFrameData n m}
    {F : Matrix (Reg n) (Fin m) ℂ} (hF : IsIsometry F) (hf : FrameDataFidelity d F)
    (z : ℂ) (hz : IsPhase z) :
    ‖phaseRotation (finiteFrameProjector d) z - phaseRotation (rangeProjector F) z‖
      ≤ 2 * finiteFrameProjectorError d := by
  have hρ : 0 ≤ finiteFrameProjectorError d := by
    unfold finiteFrameProjectorError
    have hδ : 0 ≤ finiteFrameOpError d :=
      mul_nonneg d.entryError_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _))
    nlinarith
  have hD : ‖finiteFrameProjector d - rangeProjector F‖ ≤ finiteFrameProjectorError d :=
    finiteFrame_projector_deviation hF hf
  have hz1 : ‖z‖ = 1 := isPhase_norm_one hz
  have hzstar : ‖star z‖ = 1 := by
    rw [show ‖star z‖ = ‖z‖ from by simp]
    exact hz1
  have hdiff : phaseRotation (finiteFrameProjector d) z - phaseRotation (rangeProjector F) z
      = z • (finiteFrameProjector d - rangeProjector F)
        - star z • (finiteFrameProjector d - rangeProjector F) := by
    ext i j
    simp [phaseRotation, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply]
    ring
  rw [hdiff]
  calc ‖z • (finiteFrameProjector d - rangeProjector F)
        - star z • (finiteFrameProjector d - rangeProjector F)‖
      = ‖z • (finiteFrameProjector d - rangeProjector F)
          + (-(star z • (finiteFrameProjector d - rangeProjector F)))‖ := by
          rw [sub_eq_add_neg]
      _ ≤ ‖z • (finiteFrameProjector d - rangeProjector F)‖
          + ‖-(star z • (finiteFrameProjector d - rangeProjector F))‖ := norm_add_le _ _
      _ = ‖z • (finiteFrameProjector d - rangeProjector F)‖
          + ‖star z • (finiteFrameProjector d - rangeProjector F)‖ := by rw [norm_neg]
      _ ≤ ‖z‖ * ‖finiteFrameProjector d - rangeProjector F‖
          + ‖star z‖ * ‖finiteFrameProjector d - rangeProjector F‖ := by
          refine add_le_add ?_ ?_
          · exact matrix_smul_norm_le _ _
          · exact matrix_smul_norm_le _ _
      _ = 2 * ‖finiteFrameProjector d - rangeProjector F‖ := by rw [hz1, hzstar]; ring
      _ ≤ 2 * finiteFrameProjectorError d := by gcongr

theorem cpp_call_ledger_of_phases {J : Type} (fs : List (J → ℝ)) :
    cppCounts (cppCompile fs) = (fs.length, 2 * (fs.length / 2), 2 * ((fs.length + 1) / 2),
      fs.length) :=
  cppCompile_counts fs

noncomputable def callerFilteredProgram {H M : Type} [Fintype H] [DecidableEq H]
    [Fintype M] [DecidableEq M] (F : Matrix H M ℂ) (ca cb : List (AdjointStep H)) :
    List (AdjointStep (Bool × H)) :=
  frameFilteredWord F ca cb

theorem caller_filtered_sector_blocks {H M : Type} [Fintype H] [DecidableEq H]
    [Fintype M] [DecidableEq M] (F : Matrix H M ℂ) (U V : Matrix H H ℂ) :
    frameFilteredProduct F U V =
      TensorGate (1 : Matrix Bool Bool ℂ) (V * rangeProjector F * U) +
        TensorGate PauliX (V * (1 - rangeProjector F) * U) := by
  rw [frameFilteredProduct, frameFlagFilter]
  simp only [Matrix.add_mul, Matrix.mul_add, tensorGate_mul]
  simp only [Matrix.one_mul, Matrix.mul_one]

theorem caller_filtered_false_block {H M : Type} [Fintype H] [DecidableEq H]
    [Fintype M] [DecidableEq M] (F : Matrix H M ℂ) (U V : Matrix H H ℂ) (x y : H) :
    frameFilteredProduct F U V (false, x) (false, y) = (V * rangeProjector F * U) x y := by
  rw [caller_filtered_sector_blocks]
  show (TensorGate (1 : Matrix Bool Bool ℂ) (V * rangeProjector F * U) (false, x) (false, y) +
      TensorGate PauliX (V * (1 - rangeProjector F) * U) (false, x) (false, y)) = _
  rw [tensorGate_apply, tensorGate_apply]
  simp [PauliX, permMatrix]

theorem caller_filtered_true_block {H M : Type} [Fintype H] [DecidableEq H]
    [Fintype M] [DecidableEq M] (F : Matrix H M ℂ) (U V : Matrix H H ℂ) (x y : H) :
    frameFilteredProduct F U V (false, x) (true, y)
      = (V * (1 - rangeProjector F) * U) x y := by
  rw [caller_filtered_sector_blocks]
  show (TensorGate (1 : Matrix Bool Bool ℂ) (V * rangeProjector F * U) (false, x) (true, y) +
      TensorGate PauliX (V * (1 - rangeProjector F) * U) (false, x) (true, y)) = _
  rw [tensorGate_apply, tensorGate_apply]
  simp [PauliX, permMatrix]

theorem caller_filtered_corner {H I M O : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]
    (R : Matrix H I ℂ) (F : Matrix H M ℂ) (L : Matrix H O ℂ) (U V : Matrix H H ℂ) :
    compress (flagFrame L) (frameFilteredProduct F U V) (flagFrame R)
      = compress L V F * compress F U R :=
  frame_filtered_rectangular_corner_product H I M O R F L U V

theorem caller_filtered_cost {H M : Type} [Fintype H] [DecidableEq H]
    [Fintype M] [DecidableEq M] (F : Matrix H M ℂ) (O : Matrix H H ℂ)
    (ca cb : List (AdjointStep H)) :
    adjointQueryCount (callerFilteredProgram F ca cb)
        = adjointQueryCount ca + adjointQueryCount cb ∧
      adjointGateCount (callerFilteredProgram F ca cb)
        = adjointGateCount ca + adjointGateCount cb + 1 := by
  have h := frame_filter_actual_body_substitution_and_cost H M F O ca cb
  exact ⟨h.2.1, h.2.2⟩

theorem caller_filtered_evaluation {H M : Type} [Fintype H] [DecidableEq H]
    [Fintype M] [DecidableEq M] (F : Matrix H M ℂ) (O : Matrix H H ℂ)
    (ca cb : List (AdjointStep H)) :
    evaluate (parallelOracle (J := Bool) O) (callerFilteredProgram F ca cb)
      = frameFilteredProduct F (evaluate O ca) (evaluate O cb) := by
  have h := frame_filter_actual_body_substitution_and_cost H M F O ca cb
  exact h.1

def isReadEvent (e : MemEvent) : Bool := if e matches .read _ _ then true else false

def stepOracleEvent {H : Type} : AdjointStep H → Option MemEvent
  | .forward => some (.oracle .forward)
  | .backward => some (.oracle .inverse)
  | .gate _ => none

def bodyOracleEvents {H : Type} (cs : List (AdjointStep H)) : List MemEvent :=
  cs.flatMap (fun s => (stepOracleEvent s).toList)

def callerFilteredEvents {n m : ℕ} (d : FiniteFrameData n m)
    (ca cb : List (AdjointStep (Reg n))) (err : ℚ) : List MemEvent :=
  readEntry 0 (finiteFrameBitCost d) ++
    bodyOracleEvents ca ++
    bodyOracleEvents cb ++
    [MemEvent.alloc 1 1, MemEvent.approx err, MemEvent.release 1]

theorem countEvent_append (p : MemEvent → Bool) (a b : List MemEvent) :
    countEvent p (a ++ b) = countEvent p a + countEvent p b := by
  induction a with
  | nil => simp [countEvent]
  | cons e a ih =>
      simp only [countEvent, List.cons_append, ih]
      omega

theorem bodyOracleEvents_noRead {H : Type} (cs : List (AdjointStep H)) :
    countEvent isReadEvent (bodyOracleEvents cs) = 0 := by
  induction cs with
  | nil => simp [bodyOracleEvents, countEvent]
  | cons s cs ih =>
      rw [bodyOracleEvents, List.flatMap_cons, countEvent_append]
      have h0 : countEvent isReadEvent ((stepOracleEvent s).toList) = 0 := by
        cases s with
        | forward => simp [countEvent, isReadEvent, stepOracleEvent]
        | backward => simp [countEvent, isReadEvent, stepOracleEvent]
        | gate g => simp [countEvent, stepOracleEvent]
      have htail : countEvent isReadEvent
          (List.flatMap (fun s => (stepOracleEvent s).toList) cs) = 0 := by
        simpa only [bodyOracleEvents] using! ih
      omega

theorem caller_filtered_events_reads {n m : ℕ} (d : FiniteFrameData n m)
    (ca cb : List (AdjointStep (Reg n))) (err : ℚ) :
    countEvent isReadEvent (callerFilteredEvents d ca cb err) = finiteFrameBitCost d := by
  rw [callerFilteredEvents, countEvent_append, countEvent_append, countEvent_append]
  have hread : countEvent isReadEvent (readEntry 0 (finiteFrameBitCost d))
      = finiteFrameBitCost d := by
    have h := clause11_readEntry_count 0 (finiteFrameBitCost d)
    simpa only [isReadEvent, List.length_range] using! h.symm
  have hca : countEvent isReadEvent (bodyOracleEvents ca) = 0 := bodyOracleEvents_noRead ca
  have hcb : countEvent isReadEvent (bodyOracleEvents cb) = 0 := bodyOracleEvents_noRead cb
  have hanc : countEvent isReadEvent [MemEvent.alloc 1 1, MemEvent.approx err,
      MemEvent.release 1] = 0 := by
    simp [countEvent, isReadEvent]
  omega

theorem errOf_readEntry (r : RegId) (b : ℕ) : errOf (readEntry r b) = 0 := by
  have key : ∀ l : List ℕ, errOf (l.map fun i => MemEvent.read r i) = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih => simp [errOf, ih]
  simpa [readEntry] using! key (List.range b)

theorem errOf_bodyOracleEvents {H : Type} (cs : List (AdjointStep H)) :
    errOf (bodyOracleEvents cs) = 0 := by
  induction cs with
  | nil => simp [bodyOracleEvents, errOf]
  | cons s cs ih =>
      rw [bodyOracleEvents, List.flatMap_cons, clause11_errOf_append]
      have h0 : errOf ((stepOracleEvent s).toList) = 0 := by
        cases s with
        | forward => simp [errOf, stepOracleEvent]
        | backward => simp [errOf, stepOracleEvent]
        | gate g => simp [errOf, stepOracleEvent]
      have htail : errOf (List.flatMap (fun s => (stepOracleEvent s).toList) cs) = 0 := by
        simpa only [bodyOracleEvents] using! ih
      rw [h0, htail]
      ring

theorem caller_filtered_events_error {n m : ℕ} (d : FiniteFrameData n m)
    (ca cb : List (AdjointStep (Reg n))) (err : ℚ) :
    errOf (callerFilteredEvents d ca cb err) = err := by
  rw [callerFilteredEvents, clause11_errOf_append, clause11_errOf_append, clause11_errOf_append]
  have h1 := errOf_readEntry 0 (finiteFrameBitCost d)
  have h2 := errOf_bodyOracleEvents ca
  have h3 := errOf_bodyOracleEvents cb
  have h4 : errOf [MemEvent.alloc 1 1, MemEvent.approx err, MemEvent.release 1] = err := by
    simp [errOf]
  rw [h1, h2, h3, h4]
  ring

end WalkSpectral4
end ConstructionStageA
end Qatlib.Concepts.AdversaryBounds.AdvDuality
