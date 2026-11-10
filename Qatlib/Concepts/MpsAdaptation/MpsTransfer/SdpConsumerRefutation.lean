/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.SdpConsumerTransportDefs
import Qatlib.Concepts.SdpDuality.StrongDuality.SdpDuality
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.SdpDuality.StrongDuality

set_option autoImplicit false

open Qatlib.Concepts.DyadicFloor.FloorRounding Qatlib.Concepts.SdpDuality.StrongDuality
open scoped Matrix.Norms.L2Operator BigOperators ENNReal

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.DyadicFloor.FloorRounding
open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer

theorem diamondProgram_zero_objective :
    (diamondProgram (0 : Operator 1 →ₗ[ℂ] Operator 1)).objective = 0 := by
  show directSum (0 : HermitianMat (Fin 1 ⊕ Fin 1) ℂ)
    ((1 / 2 : ℝ) • offDiagonal (MatrixMap.choi_matrix (0 : Operator 1 →ₗ[ℂ] Operator 1))) = 0
  have hj : MatrixMap.choi_matrix (0 : Operator 1 →ₗ[ℂ] Operator 1) = 0 := by
    ext i j
    simp [MatrixMap.choi_matrix]
  have ho : offDiagonal (MatrixMap.choi_matrix (0 : Operator 1 →ₗ[ℂ] Operator 1)) = 0 := by
    rw [hj]
    apply HermitianMat.ext
    ext i j
    cases i <;> cases j <;> simp [offDiagonal]
  rw [ho, smul_zero]
  apply HermitianMat.ext
  ext i j
  cases i <;> cases j <;> simp [directSum]

theorem zero_primalScore (M : HermitianMat (DiamondRegister 1 1) ℂ) :
    (diamondProgram (0 : Operator 1 →ₗ[ℂ] Operator 1)).primalScore M = 0 := by
  unfold Program.primalScore
  rw [diamondProgram_zero_objective]
  exact inner_zero_left _

theorem zero_dualScore_nonneg {y : DiamondConstraints 1 1}
    (hy : (diamondProgram (0 : Operator 1 →ₗ[ℂ] Operator 1)).DualFeasible y) :
    (0:ℝ) ≤ (diamondProgram (0 : Operator 1 →ₗ[ℂ] Operator 1)).dualScore y := by
  obtain ⟨α, M, y', hM, -, -, -, -, -⟩ :=
    diamondProgram_both_optimizers (by norm_num : (0:ℕ) < 1)
      (0 : Operator 1 →ₗ[ℂ] Operator 1)
  have hwd :=
      Qatlib.Concepts.SdpDuality.StrongDuality.Program.weak_duality
      (diamondProgram (0 : Operator 1 →ₗ[ℂ] Operator 1)) hM hy
  rw [zero_primalScore] at hwd
  exact hwd

theorem clause5_conj5_refuted :
    ¬ diamondEllipsoidBridge (0 : Operator 1 →ₗ[ℂ] Operator 1)
        (0 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) GaussianRational) := by
  intro hbr
  have h := hbr 1 (by norm_num) (-1)
  rcases h.2 with hfeas | hexh
  · obtain ⟨-, hy, hsc⟩ := hfeas
    have hge := zero_dualScore_nonneg hy
    have h1 := hge.trans hsc
    norm_num at h1
  · obtain ⟨-, hall⟩ := hexh
    have hz := hall (-3) (by simp)
    norm_num at hz

theorem clause5_refuted : ¬
  ∃ G : WitnessGenerator,
    G.sound ∧

    (∀ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (n : ℕ)
        (Ar : Matrix X X GaussianRational) (Zr : Fin n → Matrix X X GaussianRational),
      ∃ (N k : ℕ) (I : RationalSDPInput N k)
          (P : Program (Fin N) (EuclideanSpace ℝ (Fin k)))
          (φ : HermitianMat (Fin N) ℂ → Gamma2FixedFamily X n × ℝ)
          (ψ : EuclideanSpace ℝ (Fin k) → (X → ℝ) × (X → ℝ) × Matrix X X ℂ),
        I.realizes P ∧
        filteredGamma2Realizes (gaussianRationalMatrix Ar)
          (fun j => gaussianRationalMatrix (Zr j)) P φ ψ ∧
        slaterOrRegularization P ∧
        generationDelivers G I P) ∧

    (∀ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (n : ℕ)
        (inp : X → Fin n → Bool) (δr : ℚ) (ρr σr : Matrix X X GaussianRational),
      ∃ (N k : ℕ) (I : RationalSDPInput N k)
          (P : Program (Fin N) (EuclideanSpace ℝ (Fin k)))
          (φ : HermitianMat (Fin N) ℂ → Matrix X X ℂ × Gamma2FixedFamily X n × ℝ),
        I.realizes P ∧
        stateConversionRealizes inp (δr : ℝ) (gaussianRationalMatrix ρr)
          (gaussianRationalMatrix σr) P φ ∧
        (∀ σ'r : Matrix X X GaussianRational,
          ∃ (N' k' : ℕ) (I' : RationalSDPInput N' k')
              (P' : Program (Fin N') (EuclideanSpace ℝ (Fin k')))
              (φ' : HermitianMat (Fin N') ℂ → Gamma2FixedFamily X n × ℝ)
              (ψ' : EuclideanSpace ℝ (Fin k') → (X → ℝ) × (X → ℝ) × Matrix X X ℂ),
            I'.realizes P' ∧
            filteredGamma2Realizes
              (gaussianRationalMatrix ρr - gaussianRationalMatrix σ'r)
              (gramFilterDelta inp) P' φ' ψ' ∧
            stateConversionLayerTransport inp (δr : ℝ) (gaussianRationalMatrix ρr)
              (gaussianRationalMatrix σr) (gaussianRationalMatrix σ'r) P φ P' φ') ∧
        slaterOrRegularization P ∧
        generationDelivers G I P) ∧

    (∀ (D E : ℕ) (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
        (T : Operator D →ₗ[ℂ] Operator E),
      gaussianRationalMatrix J = MatrixMap.choi_matrix T →
      ∃ (N k : ℕ) (I : RationalSDPInput N k)
          (P : Program (Fin N) (EuclideanSpace ℝ (Fin k))),
        I.realizes P ∧
        diamondConsumerRealizes T J P ∧
        slaterOrRegularization P ∧
        generationDelivers G I P) ∧

    (∀ (Ar : Matrix (Fin 0) (Fin 0) GaussianRational)
        (Zr : Fin 0 → Matrix (Fin 0) (Fin 0) GaussianRational),
      ∃ (N k : ℕ) (I : RationalSDPInput N k)
          (P : Program (Fin N) (EuclideanSpace ℝ (Fin k)))
          (φ : HermitianMat (Fin N) ℂ → Gamma2FixedFamily (Fin 0) 0 × ℝ)
          (ψ : EuclideanSpace ℝ (Fin k) →
            (Fin 0 → ℝ) × (Fin 0 → ℝ) × Matrix (Fin 0) (Fin 0) ℂ),
        I.realizes P ∧
        filteredGamma2Realizes (gaussianRationalMatrix Ar)
          (fun j => gaussianRationalMatrix (Zr j)) P φ ψ ∧
        generationDelivers G I P) ∧
    (∀ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (Ar : Matrix X X GaussianRational),
      ∃ (N k : ℕ) (I : RationalSDPInput N k)
          (P : Program (Fin N) (EuclideanSpace ℝ (Fin k)))
          (φ : HermitianMat (Fin N) ℂ → Gamma2FixedFamily X 0 × ℝ)
          (ψ : EuclideanSpace ℝ (Fin k) → (X → ℝ) × (X → ℝ) × Matrix X X ℂ),
        I.realizes P ∧
        filteredGamma2Realizes (gaussianRationalMatrix Ar)
          (fun _ : Fin 0 => (0 : Matrix X X ℂ)) P φ ψ ∧
        generationDelivers G I P) ∧
    (∀ (J : Matrix (Fin 0 × Fin 0) (Fin 0 × Fin 0) GaussianRational)
        (T : Operator 0 →ₗ[ℂ] Operator 0),
      gaussianRationalMatrix J = MatrixMap.choi_matrix T →
      ∃ (N k : ℕ) (I : RationalSDPInput N k)
          (P : Program (Fin N) (EuclideanSpace ℝ (Fin k))),
        I.realizes P ∧ diamondConsumerRealizes T J P ∧ generationDelivers G I P) ∧

    (∀ (D E : ℕ) (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
        (T : Operator D →ₗ[ℂ] Operator E),
      gaussianRationalMatrix J = MatrixMap.choi_matrix T →
      diamondEllipsoidBridge T J) := by
  intro hex
  obtain ⟨G, -, -, -, -, -, -, -, hbr⟩ := hex
  have hj : gaussianRationalMatrix
        (0 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) GaussianRational) =
      MatrixMap.choi_matrix (0 : Operator 1 →ₗ[ℂ] Operator 1) := by
    have h1 : gaussianRationalMatrix
        (0 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) GaussianRational) = 0 := by
      unfold gaussianRationalMatrix
      simp
    have h2 : MatrixMap.choi_matrix (0 : Operator 1 →ₗ[ℂ] Operator 1) = 0 := by
      ext i j
      simp [MatrixMap.choi_matrix]
    rw [h1, h2]
  exact clause5_conj5_refuted (hbr 1 1 0 0 hj)

def soundRefuteInput : RationalSDPInput 1 0 where
  constraints := fun i => Fin.elim0 i
  rhs := fun i => Fin.elim0 i
  objective := (1 : Matrix (Fin 1) (Fin 1) GaussianRational)

noncomputable def soundRefuteProgram : Program (Fin 1) (EuclideanSpace ℝ (Fin 0)) where
  constraint := 0
  rhs := 0
  objective := roundedHermitianDecode soundRefuteInput.objective

theorem soundRefuteInput_realizes : soundRefuteInput.realizes soundRefuteProgram := by
  refine ⟨?_, ?_, rfl⟩
  · intro X
    apply Subsingleton.elim
  · apply Subsingleton.elim

theorem gaussianRationalMatrix_one :
    gaussianRationalMatrix (1 : Matrix (Fin 1) (Fin 1) GaussianRational) =
      (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  apply Matrix.ext
  intro i j
  fin_cases i
  fin_cases j
  simp [gaussianRationalMatrix, Matrix.map_apply, gaussianRationalEmbed,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  rfl

theorem soundRefuteProgram_objective_one : soundRefuteProgram.objective = (1 : HermitianMat (Fin 1) ℂ) := by
  show roundedHermitianDecode soundRefuteInput.objective = 1
  unfold soundRefuteInput
  apply HermitianMat.ext
  show (1/2 : ℝ) • (gaussianRationalMatrix (1 : Matrix (Fin 1) (Fin 1) GaussianRational) +
      Matrix.conjTranspose (gaussianRationalMatrix (1 : Matrix (Fin 1) (Fin 1) GaussianRational))) =
    (1 : Matrix (Fin 1) (Fin 1) ℂ)
  rw [gaussianRationalMatrix_one, Matrix.conjTranspose_one]
  apply Matrix.ext
  intro i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply]
  split_ifs <;> norm_num

theorem soundRefuteProgram_primalScore_smul_one (c : ℝ) :
    soundRefuteProgram.primalScore (c • (1 : HermitianMat (Fin 1) ℂ)) = c := by
  unfold Program.primalScore
  rw [soundRefuteProgram_objective_one, HermitianMat.inner_smul_right, HermitianMat.one_inner]
  have htr : ((1 : HermitianMat (Fin 1) ℂ)).trace = 1 := by
    simp [HermitianMat.trace]
  rw [htr]
  ring

theorem soundRefuteProgram_primalFeasible_smul_one {c : ℝ} (hc : 0 ≤ c) :
    soundRefuteProgram.PrimalFeasible (c • (1 : HermitianMat (Fin 1) ℂ)) := by
  refine ⟨?_, Subsingleton.elim _ _⟩
  have h01 : (0 : HermitianMat (Fin 1) ℂ) ≤ 1 := zero_le_one
  exact smul_nonneg hc h01

theorem witnessGenerator_sound_unsatisfiable (G : WitnessGenerator) :
    ¬ WitnessGenerator.sound G := by
  intro hs
  have hε : (0:ℚ) < 1 := by norm_num
  have hcert := (hs 1 0 soundRefuteInput soundRefuteProgram 1 hε soundRefuteInput_realizes).1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hprimal, -⟩ := hcert
  set W := G.run 1 0 soundRefuteInput 1
  set d := soundRefuteProgram.primalScore W.decode
  have hX : soundRefuteProgram.PrimalFeasible ((|d| + 2) • (1 : HermitianMat (Fin 1) ℂ)) :=
    soundRefuteProgram_primalFeasible_smul_one (by positivity)
  have hnear := hprimal _ hX
  rw [soundRefuteProgram_primalScore_smul_one] at hnear
  have hcast : (((1:ℚ) : ℝ)) = 1 := by norm_num
  rw [hcast] at hnear
  have habs : d ≤ |d| := le_abs_self d
  linarith

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
