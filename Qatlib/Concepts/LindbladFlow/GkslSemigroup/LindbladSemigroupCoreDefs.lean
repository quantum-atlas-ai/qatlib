/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.MeasuredMetropolisChannel
import Qatlib.Foundations.DirichletForm.KmsDirichlet.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.DirichletForm.KmsDirichlet

namespace Qatlib.Concepts.LindbladFlow.GkslSemigroup

open Matrix

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ENNReal

variable {D : ℕ}

structure GKSL (D : ℕ) where

  ham : Operator D

  hamHermitian : ham.IsHermitian

  jumps : Fin (D * D) → Operator D

noncomputable def lindbladApply {D : ℕ} (G : GKSL D) (ρ : Operator D) : Operator D :=
  (-Complex.I) • (G.ham * ρ - ρ * G.ham) +
    ∑ j, (G.jumps j * ρ * (G.jumps j)ᴴ -
      (1 / 2 : ℂ) • ((G.jumps j)ᴴ * G.jumps j * ρ + ρ * (G.jumps j)ᴴ * G.jumps j))

noncomputable def lindbladMap {D : ℕ} (G : GKSL D) : Operator D →ₗ[ℂ] Operator D where
  toFun := lindbladApply G
  map_add' := by
    intro ρ σ
    have hcomm : (-Complex.I) • (G.ham * (ρ + σ) - (ρ + σ) * G.ham)
        = (-Complex.I) • (G.ham * ρ - ρ * G.ham)
          + (-Complex.I) • (G.ham * σ - σ * G.ham) := by
      simp only [Matrix.mul_add, Matrix.add_mul, smul_add, smul_sub]
      abel
    have hjump : ∀ j : Fin (D * D),
        G.jumps j * (ρ + σ) * (G.jumps j)ᴴ
          - (1 / 2 : ℂ) • ((G.jumps j)ᴴ * G.jumps j * (ρ + σ)
              + (ρ + σ) * (G.jumps j)ᴴ * G.jumps j)
        = (G.jumps j * ρ * (G.jumps j)ᴴ
            - (1 / 2 : ℂ) • ((G.jumps j)ᴴ * G.jumps j * ρ
                + ρ * (G.jumps j)ᴴ * G.jumps j))
          + (G.jumps j * σ * (G.jumps j)ᴴ
            - (1 / 2 : ℂ) • ((G.jumps j)ᴴ * G.jumps j * σ
                + σ * (G.jumps j)ᴴ * G.jumps j)) := by
      intro j
      simp only [Matrix.mul_add, Matrix.add_mul, smul_add]
      abel
    simp only [lindbladApply, hcomm, hjump, Finset.sum_add_distrib]
    abel
  map_smul' := by
    intro c ρ
    have hcomm : (-Complex.I) • (G.ham * (c • ρ) - (c • ρ) * G.ham)
        = c • ((-Complex.I) • (G.ham * ρ - ρ * G.ham)) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_smul, mul_comm]
    have hjump : ∀ j : Fin (D * D),
        G.jumps j * (c • ρ) * (G.jumps j)ᴴ
          - (1 / 2 : ℂ) • ((G.jumps j)ᴴ * G.jumps j * (c • ρ)
              + (c • ρ) * (G.jumps j)ᴴ * G.jumps j)
        = c • (G.jumps j * ρ * (G.jumps j)ᴴ
          - (1 / 2 : ℂ) • ((G.jumps j)ᴴ * G.jumps j * ρ
              + ρ * (G.jumps j)ᴴ * G.jumps j)) := by
      intro j
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_add, smul_smul, mul_comm]
    simp only [lindbladApply, hcomm, hjump]
    rw [RingHom.id_apply, smul_add, Finset.smul_sum]

noncomputable def lindbladSemigroup {D : ℕ} (G : GKSL D) (t : ℝ) :
    Operator D → Operator D :=
  fun ρ => ∑' k : ℕ, ((t : ℂ) ^ k / k.factorial) • ((⇑(lindbladMap G))^[k]) ρ

def HasKrausFamily {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) : Prop :=
  ∃ K : Fin (D * D * E * E) → Matrix (Fin E) (Fin D) ℂ,
    ∀ ρ : Operator D, T ρ = ∑ j, K j * ρ * (K j)ᴴ

def matrixUnit {D : ℕ} (i j : Fin D) : Operator D :=
  Matrix.of fun r c => if (r, c) = (i, j) then 1 else 0

noncomputable def ChoiMatrix {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    Matrix (Fin (D * E)) (Fin (D * E)) ℂ :=
  Matrix.of fun p q =>
    T (matrixUnit (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm q).1)
      (finProdFinEquiv.symm p).2 (finProdFinEquiv.symm q).2

noncomputable def gibbsDensity {D : ℕ} (H : Operator D) (β : ℝ) : Operator D :=
  (Matrix.trace (NormedSpace.exp (-(β : ℂ) • H)))⁻¹ •
    NormedSpace.exp (-(β : ℂ) • H)

def KMSNormalForm {D : ℕ} (G : GKSL D) (ρ : Operator D) : Prop :=
  IsDensityOperator ρ ∧ ρ.PosDef ∧
    ∃ (H : Operator D) (β : ℝ), ρ = gibbsDensity H β ∧
      KmsSelfAdjoint ρ (lindbladMap G) ∧
      ∀ O : Operator D, kmsDirichlet ρ (lindbladMap G) O
        = kmsDirichlet ρ (kmsGeneratorFam ρ (G.jumps)) O

noncomputable def traceDistance {D : ℕ} (ρ σ : Operator D) : ℝ :=
  Matrix.traceNorm (ρ - σ) / 2

def IsStationary {D : ℕ} (G : GKSL D) (ρ : Operator D) : Prop :=
  ∀ t : ℝ, 0 ≤ t → lindbladSemigroup G t ρ = ρ

def SpectralGapPositive {D : ℕ} (G : GKSL D) (ρ : Operator D) (γ : ℝ) : Prop :=
  0 < γ ∧ KmsGapAtLeast ρ (lindbladMap G) γ ∧
    ∀ O : Operator D, kmsDirichlet ρ (lindbladMap G) O
      = kmsDirichlet ρ (kmsGeneratorFam ρ (G.jumps)) O

noncomputable def mixingTime {D : ℕ} (G : GKSL D) (ρ : Operator D) (γ : ℝ) : ℝ≥0∞ :=
  sInf { t : ℝ≥0∞ | ∀ σ : Operator D, IsDensityOperator σ →
    traceDistance (lindbladSemigroup G (ENNReal.toReal t) σ) ρ ≤ γ }

noncomputable def matrixLog {D : ℕ} (ρ : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D) (Fin D) ℂ :=
  @CFC.log (Matrix (Fin D) (Fin D) ℂ)
    (inferInstanceAs (NormedRing (Matrix (Fin D) (Fin D) ℂ)))
    (inferInstanceAs (StarRing (Matrix (Fin D) (Fin D) ℂ)))
    (inferInstanceAs (NormedAlgebra ℝ (Matrix (Fin D) (Fin D) ℂ)))
    (inferInstanceAs (ContinuousFunctionalCalculus ℝ (Matrix (Fin D) (Fin D) ℂ) IsSelfAdjoint)) ρ

noncomputable def relativeEntropy {D : ℕ} (ρ σ : Matrix (Fin D) (Fin D) ℂ) : ℝ :=
  (Matrix.trace (ρ * (matrixLog ρ - matrixLog σ))).re

def TraceMixingFromGap : Prop :=
  ∀ (D : ℕ) (G : GKSL D) (ρ : Operator D) (γ : ℝ),
    KMSNormalForm G ρ → SpectralGapPositive G ρ γ →
      ∀ σ : Operator D, IsDensityOperator σ → ∀ t : ℝ, 0 ≤ t →
        traceDistance (lindbladSemigroup G t σ) ρ
          ≤ Real.exp (-γ * t) * Real.sqrt (2 * relativeEntropy σ ρ) ∧
        relativeEntropy (lindbladSemigroup G t σ) ρ ≤ relativeEntropy σ ρ

noncomputable def measuredMetropolisChannel {D : ℕ} (E : Fin D → ℝ) (β : ℝ) :
    Operator D →ₗ[ℂ] Operator D where
  toFun ρ := ∑ o : Fin D × Fin D × Bool,
    thermalKraus D E β o * ρ * (thermalKraus D E β o)ᴴ
  map_add' := by
    intro ρ σ
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' := by
    intro c ρ
    simp only [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul]

def QuantumMetropolisConsumerSpec {D : ℕ} (G : GKSL D) (E : Fin D → ℝ)
    (β t ε : ℝ) (cost : ℕ) : Prop :=
  ∃ n : ℕ, n * (D * 2 * 2) ≤ cost ∧ ∀ ρ : Operator D,
    Matrix.traceNorm (((measuredMetropolisChannel E β : Module.End ℂ (Operator D)) ^ n) ρ
      - lindbladSemigroup G t ρ) ≤ ε

end Qatlib.Concepts.LindbladFlow.GkslSemigroup
