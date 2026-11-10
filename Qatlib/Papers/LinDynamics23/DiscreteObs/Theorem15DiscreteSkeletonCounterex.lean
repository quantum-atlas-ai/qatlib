/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.WindowLchs.TimeDependentLCHSWindowConsumers
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

namespace Qatlib.Papers.LinDynamics23.DiscreteObs

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator
set_option warningAsError false

def Theorem15DiscreteSkeletonV1 : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (N : ℕ) (c : Fin N → ℂ)
    (V : Fin N → Matrix I I ℂ) (B : Matrix I I ℂ) (i₀ : I) (E : Matrix I I ℂ)
    (ε : ℝ),
    (∀ j, V j ∈ 𝐔[I]) → B ∈ 𝐔[I] →
    0 < Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass c → 0 < ε →
    let x₀ := B.mulVec (Ket i₀)
    let v := E.mulVec x₀
    let τ := ‖toEuclidean_fromVec v‖
    let α := Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass c
    0 < τ →
    ∀ η : ℝ, η ≤ τ * ε / 8 → η < τ →
      (∀ j₀ : Fin N,
          let S := Finset.univ.filter (fun x : Fin N × I => x.1 = j₀)
          let y := staticLchsDataBranch j₀
            (Run (preparedMark S)
              (staticLchsCompile c V B j₀ i₀ 0)
              (Ket (j₀, i₀)))
          0 < MeasureProb
            (Run (preparedMark S)
              (staticLchsCompile c V B j₀ i₀ 0)
              (Ket (j₀, i₀))) S →
          (staticLchsOutputDensity y -
              staticLchsOutputDensity v).traceNorm ≤
            4 * η / τ) ∧
      (∀ j₀ : Fin N, ∀ k : ℕ,
          IsUnitaryCircuit
            (staticLchsCompile c V B j₀ i₀ k) ∧
          QueryCount
            (staticLchsCompile c V B j₀ i₀ k) = k ∧
          (staticLchsWord k).length = 10 * k + 4) ∧
      (∀ j₀ : Fin N,
          let S := Finset.univ.filter (fun x : Fin N × I => x.1 = j₀)
          let m := staticLchsWindow α τ
          1 ≤ m ∧ ((m : ℝ) ≤ 2 * α / τ + 1 ∧
            1 / 8 ≤ ∑ j : Fin m,
              staticLchsIterationWeight m j *
                MeasureProb
                  (Run (preparedMark S)
                    (staticLchsCompile c V B j₀ i₀ j.val)
                    (Ket (j₀, i₀))) S))

private def cancellingCoefficients (j : Fin 2) : ℂ := if j = 0 then 1 else -1

private theorem cancelling_mass : coefficientMass cancellingCoefficients = 2 := by
  norm_num [coefficientMass, cancellingCoefficients, Fin.sum_univ_two]

private theorem cancelling_success (k : ℕ) :
    let S := Finset.univ.filter (fun x : Fin 2 × Fin 1 => x.1 = 0)
    MeasureProb (Run (preparedMark S)
      (staticLchsCompile cancellingCoefficients (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ))
        1 0 0 k) (Ket (0, 0))) S = 0 := by
  (try dsimp only)
  obtain ⟨b, hb⟩ := static_lchs_actual_data_branch_collinear (Fin 1) 2 cancellingCoefficients
    (fun _ => 1) 1 0 0 k (by rw [cancelling_mass]; norm_num)
    (fun _ => (unitaryGroup (Fin 1) ℂ).one_mem) (unitaryGroup (Fin 1) ℂ).one_mem
  rw [static_lchs_label_probability, hb,
    static_lchs_actual_initial_data_branch (Fin 1) 2 cancellingCoefficients (fun _ => 1) 1 0 0
      (by rw [cancelling_mass]; norm_num) (fun _ => (unitaryGroup (Fin 1) ℂ).one_mem)
      (unitaryGroup (Fin 1) ℂ).one_mem]
  norm_num [Fin.sum_univ_two, cancellingCoefficients, cancelling_mass, Matrix.add_mulVec,
    MeasureProb, BornProb]

theorem theorem15DiscreteSkeleton_counterexample : ¬ Theorem15DiscreteSkeletonV1 := by
  intro h
  have hn : ‖toEuclidean_fromVec (Ket (0 : Fin 1))‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket _)
  have hτ : 0 < ‖toEuclidean_fromVec
      ((1 : Matrix (Fin 1) (Fin 1) ℂ).mulVec ((1 : Matrix (Fin 1) (Fin 1) ℂ).mulVec (Ket 0)))‖ := by
    simp [hn]
  have hs := h (Fin 1) 2 cancellingCoefficients (fun _ => 1) 1 0 1 1
    (fun _ => (unitaryGroup (Fin 1) ℂ).one_mem) (unitaryGroup (Fin 1) ℂ).one_mem
    (by rw [cancelling_mass]; norm_num) (by norm_num) hτ 0
    (by positivity) (by simpa using! hτ)
  have hw := (hs.2.2 (0 : Fin 2)).2.2
  simp only [cancelling_success, mul_zero, Finset.sum_const_zero] at hw
  norm_num at hw

end Qatlib.Papers.LinDynamics23.DiscreteObs
