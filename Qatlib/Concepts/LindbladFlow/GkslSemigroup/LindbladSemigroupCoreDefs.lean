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

/-!
# Definitions for finite GKSL evolution and mixing

`GKSL` packages a Hermitian Hamiltonian and a fixed finite jump family, while `lindbladApply`
and `lindbladSemigroup` define the generator and its exponential-series evolution.
`HasKrausFamily` and `ChoiMatrix` fix the finite-dimensional channel conventions used for the
complete-positivity results of [Lindblad1976] and [Choi1975].

The module also defines Gibbs references, KMS normal forms and gaps, trace distance, mixing
time, and real-valued relative entropy. `TraceMixingFromGap` and `QuantumMetropolisConsumerSpec`
state quantitative interfaces to be established or supplied by later results.

## Main statements

* `lindbladSemigroup`: define exponential-series evolution.
* `KMSNormalForm` and `SpectralGapPositive`: specify reference and Dirichlet-form conditions.
* `TraceMixingFromGap`: state a trace-mixing and entropy-monotonicity specification.
* `QuantumMetropolisConsumerSpec`: state a cost-bounded measured-channel approximation
  specification.

## References

* [Lindblad, 1976][Lindblad1976]
* [Choi, 1975][Choi1975]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.DirichletForm.KmsDirichlet

namespace Qatlib.Concepts.LindbladFlow.GkslSemigroup

open Matrix

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ENNReal

variable {D : ℕ}

/-- A finite-dimensional GKSL generator specified by a Hermitian Hamiltonian and `D^2` jump
operators. -/
structure GKSL (D : ℕ) where

  ham : Operator D

  hamHermitian : ham.IsHermitian

  jumps : Fin (D * D) → Operator D

/-- The Schrödinger-picture generator consisting of the Hamiltonian commutator and the sum of
jump dissipators. -/
noncomputable def lindbladApply {D : ℕ} (G : GKSL D) (ρ : Operator D) : Operator D :=
  (-Complex.I) • (G.ham * ρ - ρ * G.ham) +
    ∑ j, (G.jumps j * ρ * (G.jumps j)ᴴ -
      (1 / 2 : ℂ) • ((G.jumps j)ᴴ * G.jumps j * ρ + ρ * (G.jumps j)ᴴ * G.jumps j))

/-- The complex-linear map associated with `lindbladApply`. -/
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

/-- The exponential-series evolution `∑ k, t^k / k!` times the `k`th iterate of the Lindblad
generator. -/
noncomputable def lindbladSemigroup {D : ℕ} (G : GKSL D) (t : ℝ) :
    Operator D → Operator D :=
  fun ρ => ∑' k : ℕ, ((t : ℂ) ^ k / k.factorial) • ((⇑(lindbladMap G))^[k]) ρ

/-- A finite Kraus-sum representation of a complex-linear map, using a family indexed by `Fin (D
* D * E * E)`. -/
def HasKrausFamily {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) : Prop :=
  ∃ K : Fin (D * D * E * E) → Matrix (Fin E) (Fin D) ℂ,
    ∀ ρ : Operator D, T ρ = ∑ j, K j * ρ * (K j)ᴴ

/-- The matrix unit with its sole nonzero entry equal to one at `(i, j)`. -/
def matrixUnit {D : ℕ} (i j : Fin D) : Operator D :=
  Matrix.of fun r c => if (r, c) = (i, j) then 1 else 0

/-- The Choi matrix formed from images of matrix units with flattened input-output indices. -/
noncomputable def ChoiMatrix {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    Matrix (Fin (D * E)) (Fin (D * E)) ℂ :=
  Matrix.of fun p q =>
    T (matrixUnit (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm q).1)
      (finProdFinEquiv.symm p).2 (finProdFinEquiv.symm q).2

/-- The Gibbs exponential `exp(-β • H)` divided by its trace. -/
noncomputable def gibbsDensity {D : ℕ} (H : Operator D) (β : ℝ) : Operator D :=
  (Matrix.trace (NormedSpace.exp (-(β : ℂ) • H)))⁻¹ •
    NormedSpace.exp (-(β : ℂ) • H)

/-- A full-rank density reference of Gibbs form for which the Lindblad map is KMS-self-adjoint
and has the same KMS Dirichlet form as its jump-family generator. -/
def KMSNormalForm {D : ℕ} (G : GKSL D) (ρ : Operator D) : Prop :=
  IsDensityOperator ρ ∧ ρ.PosDef ∧
    ∃ (H : Operator D) (β : ℝ), ρ = gibbsDensity H β ∧
      KmsSelfAdjoint ρ (lindbladMap G) ∧
      ∀ O : Operator D, kmsDirichlet ρ (lindbladMap G) O
        = kmsDirichlet ρ (kmsGeneratorFam ρ (G.jumps)) O

/-- Half the trace norm of the operator difference `ρ - σ`. -/
noncomputable def traceDistance {D : ℕ} (ρ σ : Operator D) : ℝ :=
  Matrix.traceNorm (ρ - σ) / 2

/-- Stationarity under Lindblad evolution at every nonnegative real time. -/
def IsStationary {D : ℕ} (G : GKSL D) (ρ : Operator D) : Prop :=
  ∀ t : ℝ, 0 ≤ t → lindbladSemigroup G t ρ = ρ

/-- A positive KMS gap lower bound together with equality of the Lindblad and jump-family KMS
Dirichlet forms. -/
def SpectralGapPositive {D : ℕ} (G : GKSL D) (ρ : Operator D) (γ : ℝ) : Prop :=
  0 < γ ∧ KmsGapAtLeast ρ (lindbladMap G) γ ∧
    ∀ O : Operator D, kmsDirichlet ρ (lindbladMap G) O
      = kmsDirichlet ρ (kmsGeneratorFam ρ (G.jumps)) O

/-- The infimum of extended nonnegative times whose real-valued evolution sends every density
operator within tolerance `γ` of `ρ` in trace distance. -/
noncomputable def mixingTime {D : ℕ} (G : GKSL D) (ρ : Operator D) (γ : ℝ) : ℝ≥0∞ :=
  sInf { t : ℝ≥0∞ | ∀ σ : Operator D, IsDensityOperator σ →
    traceDistance (lindbladSemigroup G (ENNReal.toReal t) σ) ρ ≤ γ }

/-- The matrix logarithm defined by real continuous functional calculus. -/
noncomputable def matrixLog {D : ℕ} (ρ : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D) (Fin D) ℂ :=
  @CFC.log (Matrix (Fin D) (Fin D) ℂ)
    (inferInstanceAs (NormedRing (Matrix (Fin D) (Fin D) ℂ)))
    (inferInstanceAs (StarRing (Matrix (Fin D) (Fin D) ℂ)))
    (inferInstanceAs (NormedAlgebra ℝ (Matrix (Fin D) (Fin D) ℂ)))
    (inferInstanceAs (ContinuousFunctionalCalculus ℝ (Matrix (Fin D) (Fin D) ℂ) IsSelfAdjoint)) ρ

/-- The real part of `trace (ρ * (matrixLog ρ - matrixLog σ))`. -/
noncomputable def relativeEntropy {D : ℕ} (ρ σ : Matrix (Fin D) (Fin D) ℂ) : ℝ :=
  (Matrix.trace (ρ * (matrixLog ρ - matrixLog σ))).re

/-- The specification that KMS normal form and a positive spectral gap imply the stated
exponential trace-distance bound and relative-entropy monotonicity. -/
def TraceMixingFromGap : Prop :=
  ∀ (D : ℕ) (G : GKSL D) (ρ : Operator D) (γ : ℝ),
    KMSNormalForm G ρ → SpectralGapPositive G ρ γ →
      ∀ σ : Operator D, IsDensityOperator σ → ∀ t : ℝ, 0 ≤ t →
        traceDistance (lindbladSemigroup G t σ) ρ
          ≤ Real.exp (-γ * t) * Real.sqrt (2 * relativeEntropy σ ρ) ∧
        relativeEntropy (lindbladSemigroup G t σ) ρ ≤ relativeEntropy σ ρ

/-- The complex-linear channel expressed as the sum over the thermal Kraus family. -/
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

/-- The existence of a measured Metropolis channel power within trace-norm error `ε` of time-`t`
evolution on every operator, using at most `cost` in the specified step-cost model. -/
def QuantumMetropolisConsumerSpec {D : ℕ} (G : GKSL D) (E : Fin D → ℝ)
    (β t ε : ℝ) (cost : ℕ) : Prop :=
  ∃ n : ℕ, n * (D * 2 * 2) ≤ cost ∧ ∀ ρ : Operator D,
    Matrix.traceNorm (((measuredMetropolisChannel E β : Module.End ℂ (Operator D)) ^ n) ρ
      - lindbladSemigroup G t ρ) ≤ ε

end Qatlib.Concepts.LindbladFlow.GkslSemigroup
