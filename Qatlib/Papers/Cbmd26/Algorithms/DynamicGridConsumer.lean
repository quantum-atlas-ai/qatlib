/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.DysonGridSegments
import Qatlib.Papers.Cbmd26.Algorithms.DysonGridCircuitBridge
import Qatlib.Papers.Cbmd26.Algorithms.DynamicCBMDParameters
import Qatlib.Papers.Cbmd26.Algorithms.PiecewiseGridDysonError

/-!
# Counted simulation on supplied time grids

Chooses `dynamicGridFineCount` and `dynamicGridDegree` to approximate an evolution supplied on a
monotone time grid. The segment coefficients `dynamicGridCoefficients` define the fresh-register
word `dynamicGridWord`, with freezing and truncation error bounds leading to a counted
simulation guarantee. These results support the contour-based algorithms of [WangEtAl2026].

## Main statements

* `dynamicGridCoefficients_error`: controls each compiled segment approximation.
* `dynamic_grid_simulation_counted`: gives a scale-one simulation encoding, circuit counts, and
  a frame-action bound.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.InteractionEvo.DysonGrid
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonMeanDerivativeGrid
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SharedAncilla.AncillaProduct
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.CoherentSim.TaylorEncoding

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace CBMD
open Matrix
open scoped Matrix.Norms.L2Operator

/-- Defines the Euler error constant from the normalization and chosen segment duration. -/
def dynamicGridEulerConstant (Λ T : ℝ) : ℝ :=
  Real.exp (Λ * (T / dynamicSegmentCount Λ T)) * Λ ^ 2 *
    (T / dynamicSegmentCount Λ T) ^ 2 / 2

/-- Chooses a fine-grid size large enough for both the Euler segment error and the supplied-grid
freezing error. -/
def dynamicGridFineCount (Λ T : ℝ) (N : ℕ) (ζ : ℝ) : ℕ :=
  max (dynamicFineGridSize (dynamicGridEulerConstant Λ T)
    (dynamicSegmentAccuracy (dynamicSegmentCount Λ T) (ζ / 2)))
    (max 1 ⌈4 * Λ * N * T / ((dynamicSegmentCount Λ T : ℝ) * ζ)⌉₊)

/-- Chooses the Dyson degree using half the requested simulation accuracy. -/
def dynamicGridDegree (Λ T ζ : ℝ) : ℕ :=
  dynamicDysonDegree (dynamicSegmentCount Λ T) (ζ / 2)

/-- The chosen dynamic fine-grid count is positive. -/
theorem dynamicGridFineCount_pos (Λ T : ℝ) (N : ℕ) (ζ : ℝ) :
    0 < dynamicGridFineCount Λ T N ζ := by
  have h1 : 1 ≤ dynamicGridFineCount Λ T N ζ :=
    (le_max_left 1 _).trans (le_max_right _ _)
  omega

/-- The Euler constant divided by the chosen fine-grid count is at most half the segment
accuracy at `ζ / 2`. -/
theorem dynamicGridFineCount_euler_error {Λ T ζ : ℝ} (hΛ : 0 ≤ Λ) (hT : 0 ≤ T)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (N : ℕ) :
    dynamicGridEulerConstant Λ T / dynamicGridFineCount Λ T N ζ ≤
      dynamicSegmentAccuracy (dynamicSegmentCount Λ T) (ζ / 2) / 2 := by
  have hS := (dynamicSegmentCount_bounds hΛ hT).1
  have hδ := (dynamicSegmentAccuracy_bounds hS (by positivity : 0 < ζ / 2)
    (by linarith : ζ / 2 ≤ 1)).1
  have hC : 0 ≤ dynamicGridEulerConstant Λ T := by unfold dynamicGridEulerConstant; positivity
  have he := dynamicFineGridSize_error hC hδ
  have hmax : (dynamicFineGridSize (dynamicGridEulerConstant Λ T)
      (dynamicSegmentAccuracy (dynamicSegmentCount Λ T) (ζ/2)) : ℝ) ≤
      dynamicGridFineCount Λ T N ζ := by
    exact_mod_cast (le_max_left _ _ : dynamicFineGridSize _ _ ≤ dynamicGridFineCount Λ T N ζ)
  exact (div_le_div_of_nonneg_left hC (Nat.cast_pos.mpr he.1) hmax).trans he.2

/-- The chosen fine-grid count makes the displayed supplied-grid freezing error at most `ζ / 2`. -/
theorem dynamicGridFineCount_freezing_error {Λ T ζ : ℝ} (hΛ : 0 ≤ Λ) (hT : 0 ≤ T)
    (hζ : 0 < ζ) (N : ℕ) :
    2 * Λ * N * (T / ((dynamicSegmentCount Λ T : ℝ) * dynamicGridFineCount Λ T N ζ)) ≤ ζ / 2 := by
  have hS : (0 : ℝ) < dynamicSegmentCount Λ T :=
      Nat.cast_pos.mpr (dynamicSegmentCount_bounds hΛ hT).1
  have hM : (0 : ℝ) < dynamicGridFineCount Λ T N ζ :=
      Nat.cast_pos.mpr (dynamicGridFineCount_pos Λ T N ζ)
  have hc : 4 * Λ * N * T / ((dynamicSegmentCount Λ T : ℝ) * ζ) ≤
      dynamicGridFineCount Λ T N ζ :=
    (Nat.le_ceil _).trans (by exact_mod_cast ((le_max_right 1 _).trans (le_max_right _ _)))
  have hx := (div_le_iff₀ (mul_pos hS hζ)).mp hc
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have he : 2 * Λ * N * (T / ((dynamicSegmentCount Λ T : ℝ) * dynamicGridFineCount Λ T N ζ)) * 2 =
      (4 * Λ * N * T) / ((dynamicSegmentCount Λ T : ℝ) * dynamicGridFineCount Λ T N ζ) := by ring
  rw [he]
  apply (div_le_iff₀ (mul_pos hS hM)).mpr
  nlinarith

/-- Combines a segment index and a local fine-grid index into a single global fine-grid address. -/
def dynamicGridAddress (S M : ℕ) (q : Fin S) (j : Fin M) : Fin (S * M) :=
  ⟨q.val * M + j.val, by
    have hqM := Nat.mul_le_mul_right M (Nat.succ_le_of_lt q.isLt)
    rw [Nat.succ_mul] at hqM
    omega⟩

/-- Defines the truncated grid-word coefficients for a segment, using reversed segment order and
the chosen fine-grid addresses. -/
def dynamicGridCoefficients (Λ T : ℝ) (N : ℕ) (ζ : ℝ)
    (i : Fin (dynamicSegmentCount Λ T)) :
    (Σ l : Fin (dynamicGridDegree Λ T ζ + 1),
      Fin l.val → Fin (dynamicSegmentCount Λ T * dynamicGridFineCount Λ T N ζ)) → ℂ :=
  gridWordCoefficients
    (List.ofFn (dynamicGridAddress (dynamicSegmentCount Λ T)
      (dynamicGridFineCount Λ T N ζ) i.rev))
    (dynamicGridDegree Λ T ζ)
    (gridStepCoefficient (T / dynamicSegmentCount Λ T) Λ (dynamicGridFineCount Λ T N ζ))

/-- Each chosen segment coefficient family has absolute mass at most two for nonnegative
normalization and time. -/
theorem dynamicGridCoefficients_mass {Λ T ζ : ℝ} (hΛ : 0 ≤ Λ) (hT : 0 ≤ T)
    (N : ℕ) (i : Fin (dynamicSegmentCount Λ T)) :
    coefficientMass (dynamicGridCoefficients Λ T N ζ i) ≤ 2 := by
  unfold dynamicGridCoefficients
  apply sampled_grid_coefficients_mass_le_two _ _ _ _ _ (by positivity) hΛ
    (dynamicGridFineCount_pos Λ T N ζ)
  exact (dynamicSegmentCount_bounds hΛ hT).2.2.2.trans (by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h)

/-- Defines the zero address in the positive global dynamic fine grid. -/
def dynamicGridZeroAddress (Λ T : ℝ) (N : ℕ) (ζ : ℝ) :
    Fin (dynamicSegmentCount Λ T * dynamicGridFineCount Λ T N ζ) :=
  ⟨0, Nat.mul_pos (by unfold dynamicSegmentCount; omega) (dynamicGridFineCount_pos Λ T N ζ)⟩

section Circuit
variable {A I : Type} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]

private instance dynamicFreshWorkspaceDecEq (J : Type) [DecidableEq J] (K : ℕ) :
    DecidableEq (FreshQueryWorkspace A J I K) :=
  @instDecidableEqProd (FreshSignals A K) (Bool × (J × (A × I)))
    (freshSignalsDecidableEq A K) inferInstance

private instance dynamicFreshLabelWorkspaceDecEq (J : Type) [Fintype J] [DecidableEq J] (K : ℕ) :
    DecidableEq (TaylorWordLabel J K × FreshQueryWorkspace A J I K) :=
  @instDecidableEqProd (TaylorWordLabel J K) (FreshQueryWorkspace A J I K)
    inferInstance (dynamicFreshWorkspaceDecEq J K)

/-- Constructs the segmented fresh-register Dyson word from the chosen grid coefficients and
clean address. -/
def dynamicGridWord (a₀ : A) (Λ T : ℝ) (N : ℕ) (ζ : ℝ) :
    List (AdjointStep
      (TaylorWordLabel (Fin (dynamicSegmentCount Λ T * dynamicGridFineCount Λ T N ζ))
        (dynamicGridDegree Λ T ζ) ×
      FreshQueryWorkspace A (Fin (dynamicSegmentCount Λ T * dynamicGridFineCount Λ T N ζ)) I
        (dynamicGridDegree Λ T ζ))) :=
  freshDysonSegmentedWord (dynamicGridZeroAddress Λ T N ζ) a₀ (dynamicGridDegree Λ T ζ)
    (dynamicGridCoefficients Λ T N ζ)

end Circuit

section Samples
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Samples the supplied-grid field at a global uniform fine-grid time. -/
def dynamicGridSample (τ : ℕ → ℝ) (B : ℕ → Matrix I I ℂ)
    (Λ T : ℝ) (N : ℕ) (ζ : ℝ) (j : ℕ) : Matrix I I ℂ :=
  suppliedGridField τ B N
    (T * (j : ℝ) / (dynamicSegmentCount Λ T * dynamicGridFineCount Λ T N ζ : ℕ))

/-- Hermitian supplied matrices of norm at most `Λ` give Hermitian dynamic grid samples with the
same norm bound. -/
theorem dynamicGridSample_bound (τ : ℕ → ℝ) (B : ℕ → Matrix I I ℂ)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (T : ℝ) (N : ℕ) (ζ : ℝ)
    (hB : ∀ j < N, (B j).IsHermitian ∧ ‖B j‖ ≤ Λ) (j : ℕ) :
    (dynamicGridSample τ B Λ T N ζ j).IsHermitian ∧
      ‖dynamicGridSample τ B Λ T N ζ j‖ ≤ Λ :=
  suppliedGridField_bound τ B N hΛ hB _

omit [Fintype I] [DecidableEq I] in

/-- A global dynamic grid sample at index `q * M + j` equals the supplied field at the
corresponding segment offset and local sample time. -/
theorem dynamicGridSample_coarse (τ : ℕ → ℝ) (B : ℕ → Matrix I I ℂ)
    (Λ T : ℝ) (N : ℕ) (ζ : ℝ) (q j : ℕ) :
    dynamicGridSample τ B Λ T N ζ (q * dynamicGridFineCount Λ T N ζ + j) =
      suppliedGridField τ B N
        ((q : ℝ) * (T / dynamicSegmentCount Λ T) +
          (T / dynamicSegmentCount Λ T) * j / dynamicGridFineCount Λ T N ζ) := by
  unfold dynamicGridSample
  congr 1
  have hS : (dynamicSegmentCount Λ T : ℝ) ≠ 0 := by
    have hn : 0 < dynamicSegmentCount Λ T := by unfold dynamicSegmentCount; omega
    exact (Nat.cast_pos.mpr hn).ne'
  have hM : (dynamicGridFineCount Λ T N ζ : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (dynamicGridFineCount_pos Λ T N ζ)).ne'
  push_cast
  field_simp

/-- The uniform fine-grid evolution approximates the supplied-grid evolution within operator
error `ζ / 2` under the stated grid and matrix bounds. -/
theorem dynamicGridSample_target_error {τ : ℕ → ℝ} (hτ : Monotone τ) (hτ0 : τ 0 = 0)
    (B : ℕ → Matrix I I ℂ) {Λ T ζ : ℝ} (hΛ : 0 ≤ Λ) (hT : 0 < T)
    (hζ : 0 < ζ) (N : ℕ) (hτN : τ N = T)
    (hB : ∀ j < N, (B j).IsHermitian ∧ ‖B j‖ ≤ Λ) :
    ‖suppliedGridEvolution τ B N -
      suppliedGridEvolution
        (fun j => (j : ℝ) * (T /
          (dynamicSegmentCount Λ T * dynamicGridFineCount Λ T N ζ : ℕ)))
        (dynamicGridSample τ B Λ T N ζ)
        (dynamicSegmentCount Λ T * dynamicGridFineCount Λ T N ζ)‖ ≤ ζ / 2 := by
  let Q := dynamicSegmentCount Λ T * dynamicGridFineCount Λ T N ζ
  have hQ : 0 < Q := Nat.mul_pos (dynamicSegmentCount_bounds hΛ hT.le).1
    (dynamicGridFineCount_pos Λ T N ζ)
  have hl := suppliedGridField_sample_list hτ hτ0 B N Q hτN hT hQ
  have he := congrArg (fun l : List (Matrix I I ℂ) =>
    ((l.map (fun X => HamiltonianEvolution X (T / Q))).reverse).prod) hl
  simp only [List.map_ofFn, Function.comp_def] at he
  have hfn (f : ℕ → Matrix I I ℂ) : List.ofFn (fun j : Fin Q => f j.val) =
      (List.range Q).map f := by
    apply List.ext_getElem (by simp)
    intro j hj hj'
    simp
  rw [hfn (fun j => HamiltonianEvolution (suppliedGridField τ B N (T * (j : ℝ) / Q)) (T / Q))] at he
  have he' : suppliedGridEvolution (fun j => (j : ℝ)*(T/Q))
      (dynamicGridSample τ B Λ T N ζ) Q =
      (((suppliedFrozenTable τ B (T/Q) N).map
        (fun X => HamiltonianEvolution X (T/Q))).reverse).prod := by
    rw [suppliedGridEvolution_uniform, piecewiseLeftProduct_eq_reverse_prod]
    exact he
  change ‖suppliedGridEvolution τ B N - suppliedGridEvolution _ _ Q‖ ≤ _
  rw [he']
  have hf := suppliedGridEvolution_freezing_error hτ hτ0 B N
    (div_pos hT (Nat.cast_pos.mpr hQ)) hΛ hB
  apply hf.trans
  simpa only [Q, Nat.cast_mul] using! dynamicGridFineCount_freezing_error hΛ hT.le hζ N

/-- Divides a dynamic grid sample by the normalization `Λ`. -/
def dynamicGridNormalizedSample (τ : ℕ → ℝ) (B : ℕ → Matrix I I ℂ)
    (Λ T : ℝ) (N : ℕ) (ζ : ℝ)
    (j : Fin (dynamicSegmentCount Λ T * dynamicGridFineCount Λ T N ζ)) : Matrix I I ℂ :=
  (Λ : ℂ)⁻¹ • dynamicGridSample τ B Λ T N ζ j.val

/-- Restricts the supplied-grid field to a segment by shifting its time argument by the segment
start. -/
def dynamicGridCoarseField (τ : ℕ → ℝ) (B : ℕ → Matrix I I ℂ)
    (Λ T : ℝ) (N : ℕ) (q : ℕ) (u : ℝ) : Matrix I I ℂ :=
  suppliedGridField τ B N ((q : ℝ) * (T / dynamicSegmentCount Λ T) + u)

omit [Fintype I] [DecidableEq I] in

/-- Multiplying a normalized global sample by positive `Λ` recovers the corresponding
coarse-segment field sample. -/
theorem dynamicGridNormalizedSample_coarse (τ : ℕ → ℝ) (B : ℕ → Matrix I I ℂ)
    {Λ : ℝ} (hΛ : 0 < Λ) (T : ℝ) (N : ℕ) (ζ : ℝ)
    (q : Fin (dynamicSegmentCount Λ T)) (j : Fin (dynamicGridFineCount Λ T N ζ)) :
    (Λ : ℂ) • dynamicGridNormalizedSample τ B Λ T N ζ
      (dynamicGridAddress (dynamicSegmentCount Λ T) (dynamicGridFineCount Λ T N ζ) q j) =
      dynamicGridCoarseField τ B Λ T N q.val
        ((T / dynamicSegmentCount Λ T) * j.val / dynamicGridFineCount Λ T N ζ) := by
  have hΛc : (Λ : ℂ) ≠ 0 := by exact_mod_cast hΛ.ne'
  rw [dynamicGridNormalizedSample, smul_smul, mul_inv_cancel₀ hΛc, one_smul]
  exact dynamicGridSample_coarse τ B Λ T N ζ q.val j.val

/-- The sampled evolution product on a coarse segment equals its global-indexed Dyson grid
segment. -/
theorem dynamicGridCoarse_sampledEvolution (τ : ℕ → ℝ) (B : ℕ → Matrix I I ℂ)
    (Λ T : ℝ) (N : ℕ) (ζ : ℝ) (q : ℕ) :
    sampledEvolutionProduct (dynamicGridCoarseField τ B Λ T N q)
      (T / dynamicSegmentCount Λ T) (dynamicGridFineCount Λ T N ζ) =
      dysonGridSegment (dynamicGridSample τ B Λ T N ζ)
        (T / (dynamicSegmentCount Λ T * dynamicGridFineCount Λ T N ζ : ℕ))
        (dynamicGridFineCount Λ T N ζ) q := by
  let M := dynamicGridFineCount Λ T N ζ
  have hh : (T / dynamicSegmentCount Λ T) / M =
      T / (dynamicSegmentCount Λ T * M : ℕ) := by rw [Nat.cast_mul]; ring
  have he : (fun j : Fin M => HamiltonianEvolution
      (dynamicGridCoarseField τ B Λ T N q ((T / dynamicSegmentCount Λ T) * j.val / M))
      ((T / dynamicSegmentCount Λ T) / M)) =
      (fun j : Fin M => HamiltonianEvolution (dynamicGridSample τ B Λ T N ζ (q*M+j.val))
        (T / (dynamicSegmentCount Λ T * M : ℕ))) := by
    funext j
    rw [show dynamicGridCoarseField τ B Λ T N q
        ((T / dynamicSegmentCount Λ T) * j.val / M) =
        dynamicGridSample τ B Λ T N ζ (q*M+j.val) from
      (dynamicGridSample_coarse τ B Λ T N ζ q j.val).symm, hh]
  unfold sampledEvolutionProduct
  rw [he, dysonGridSegment, piecewiseLeftProduct_eq_reverse_prod]
  have hfn (f : ℕ → Matrix I I ℂ) : List.ofFn (fun j : Fin M => f j.val) =
      (List.range M).map f := by
    apply List.ext_getElem (by simp)
    intro j hj hj'
    simp
  rw [hfn (fun j => HamiltonianEvolution (dynamicGridSample τ B Λ T N ζ (q*M+j))
    (T / (dynamicSegmentCount Λ T * M : ℕ)))]

/-- The weighted Taylor branch sum from the chosen coefficients equals the truncated Dyson grid
sum for the corresponding reversed segment. -/
theorem dynamicGridCoefficients_target (τ : ℕ → ℝ) (B : ℕ → Matrix I I ℂ)
    {Λ : ℝ} (hΛ : 0 < Λ) (T : ℝ) (N : ℕ) (ζ : ℝ)
    (i : Fin (dynamicSegmentCount Λ T)) :
    (∑ w, dynamicGridCoefficients Λ T N ζ i w •
      taylorBranchWord (dynamicGridNormalizedSample τ B Λ T N ζ)
        (dynamicGridDegree Λ T ζ) (dynamicGridDegree Λ T ζ) le_rfl (.inl w)) =
      dysonGridTruncatedSum (dynamicGridCoarseField τ B Λ T N i.rev.val)
        (T / dynamicSegmentCount Λ T) (dynamicGridFineCount Λ T N ζ) (dynamicGridDegree Λ T ζ) := by
  exact gridWordCoefficients_dyson_target _ _ _ _ _ _ _
    (dynamicGridNormalizedSample_coarse τ B hΛ T N ζ i.rev)

/-- The weighted branch sum approximates its Dyson grid segment within the shared segment
accuracy under the stated normalization and accuracy bounds. -/
theorem dynamicGridCoefficients_error (τ : ℕ → ℝ) (B : ℕ → Matrix I I ℂ)
    {Λ T ζ : ℝ} (hΛ : 0 < Λ) (hT : 0 ≤ T) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (N : ℕ) (hB : ∀ j < N, (B j).IsHermitian ∧ ‖B j‖ ≤ Λ)
    (i : Fin (dynamicSegmentCount Λ T)) :
    ‖dysonGridSegment (dynamicGridSample τ B Λ T N ζ)
        (T / (dynamicSegmentCount Λ T * dynamicGridFineCount Λ T N ζ : ℕ))
        (dynamicGridFineCount Λ T N ζ) i.rev.val -
      ∑ w, dynamicGridCoefficients Λ T N ζ i w •
        taylorBranchWord (dynamicGridNormalizedSample τ B Λ T N ζ)
          (dynamicGridDegree Λ T ζ) (dynamicGridDegree Λ T ζ) le_rfl (.inl w)‖ ≤
        dysonSharedSegmentAccuracy (dynamicSegmentCount Λ T) (ζ / 2) := by
  rw [dynamicGridCoefficients_target τ B hΛ T N ζ i,
    ← dynamicGridCoarse_sampledEvolution τ B Λ T N ζ i.rev.val, norm_sub_rev]
  have hs := dynamicSegmentCount_bounds hΛ.le hT
  have hd : 0 ≤ T / dynamicSegmentCount Λ T := by positivity
  have hlog : Λ * (T / dynamicSegmentCount Λ T) ≤ Real.log 2 := hs.2.2.2.trans (by
    have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hl ⊢
    exact hl)
  have he := dyson_grid_truncation_sample_error_discontinuous
    (dynamicGridCoarseField τ B Λ T N i.rev.val) (T / dynamicSegmentCount Λ T) Λ
    (dynamicGridFineCount Λ T N ζ) (dynamicGridDegree Λ T ζ) hd hΛ.le
    (dynamicGridFineCount_pos Λ T N ζ)
    (fun u _ => suppliedGridField_bound τ B N hΛ.le hB _) hlog
  have hEuler := dynamicGridFineCount_euler_error hΛ.le hT hζ hζ1 N
  have hTail := dynamicDysonDegree_tail hs.1 (by positivity : 0 < ζ / 2)
    (by linarith : ζ / 2 ≤ 1) (mul_nonneg hΛ.le hd) hs.2.2.2
  have hEuler' : Real.exp (Λ * (T / dynamicSegmentCount Λ T)) * Λ ^ 2 *
      (T / dynamicSegmentCount Λ T) ^ 2 / (2 * dynamicGridFineCount Λ T N ζ) ≤
      dynamicSegmentAccuracy (dynamicSegmentCount Λ T) (ζ/2) / 2 := by
    convert! hEuler using 1
    unfold dynamicGridEulerConstant
    ring
  have hTail' : 2 * (Λ * (T / dynamicSegmentCount Λ T)) ^ (dynamicGridDegree Λ T ζ + 1) /
      ((dynamicGridDegree Λ T ζ + 1).factorial : ℝ) ≤
      dynamicSegmentAccuracy (dynamicSegmentCount Λ T) (ζ/2) / 2 := hTail
  apply he.trans
  change _ ≤ dynamicSegmentAccuracy (dynamicSegmentCount Λ T) (ζ/2)
  linarith

end Samples

section CompleteCircuit
variable {A I : Type} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]

/-- Exact encodings of normalized samples yield a well-formed scale-one encoding of the
supplied-grid evolution with error `ζ`, `3 * S * K` queries, `S * (6 * K + 13)` gates, and
frame-action error at most `ζ` [WangEtAl2026]. -/
theorem dynamic_grid_simulation_counted (a₀ : A) {τ : ℕ → ℝ}
    (hτ : Monotone τ) (hτ0 : τ 0 = 0) (B : ℕ → Matrix I I ℂ)
    {Λ T ζ : ℝ} (hΛ : 0 < Λ) (hT : 0 < T) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (N : ℕ) (hτN : τ N = T)
    (hB : ∀ j < N, (B j).IsHermitian ∧ ‖B j‖ ≤ Λ)
    (U : Fin (dynamicSegmentCount Λ T * dynamicGridFineCount Λ T N ζ) →
      Matrix (A × I) (A × I) ℂ)
    (henc : ∀ j, ProjectedUnitaryEncoding (dynamicGridNormalizedSample τ B Λ T N ζ j)
      (U j) (encodingFiber a₀) (encodingFiber a₀)) :
    let S := dynamicSegmentCount Λ T
    let M := dynamicGridFineCount Λ T N ζ
    let K := dynamicGridDegree Λ T ζ
    let O := parallelOracle (J := TaylorWordLabel (Fin (S*M)) K) (freshPrimitiveQuery K U)
    let R := tagFrame (taylorEmptyLabel (Fin (S*M)) K)
      (freshWordFrame (I := I) (dynamicGridZeroAddress Λ T N ζ) a₀ K)
    let cs := dynamicGridWord (I := I) a₀ Λ T N ζ
    WellFormedAdjointCircuit cs ∧ O ∈ Matrix.unitaryGroup _ ℂ ∧
    BlockEncoding (suppliedGridEvolution τ B N) (evaluate O cs) R R 1 ζ ∧
    adjointQueryCount cs = 3 * S * K ∧ adjointGateCount cs = S * (6*K+13) ∧
    ‖evaluate O cs * R - R * suppliedGridEvolution τ B N‖ ≤ ζ := by
  let S := dynamicSegmentCount Λ T
  let M := dynamicGridFineCount Λ T N ζ
  let K := dynamicGridDegree Λ T ζ
  let F := dynamicGridSample τ B Λ T N ζ
  let V := fun i : Fin S => dysonGridSegment F (T / (S*M : ℕ)) M i.rev.val
  have hS : 0 < S := (dynamicSegmentCount_bounds hΛ.le hT.le).1
  have hV : ∀ i, V i ∈ Matrix.unitaryGroup I ℂ := fun i =>
    dysonGridSegment_unitary F (T / (S*M : ℕ)) M S i.rev.val i.rev.isLt
      (fun j _ => (dynamicGridSample_bound τ B hΛ.le T N ζ hB j).1)
  have hraw := fresh_dyson_segments_counted (dynamicGridZeroAddress Λ T N ζ) a₀ K hS
    (dynamicGridCoefficients Λ T N ζ) (dynamicGridNormalizedSample τ B Λ T N ζ)
    U V (by positivity : 0 < ζ / 2) (by linarith : ζ / 2 ≤ 1)
    (dynamicGridCoefficients_mass hΛ.le hT.le N) henc hV
    (dynamicGridCoefficients_error τ B hΛ hT.le hζ hζ1 N hB)
  obtain ⟨hw, hO, hb, hq, hg, he⟩ := hraw
  have hproduct : unitaryFamilyEvaluate V (unitaryFamilyWord S) =
      suppliedGridEvolution (fun j => (j : ℝ)*(T/(S*M : ℕ))) F (S*M) :=
    dysonGridSegment_product F (T/(S*M : ℕ)) M S
  rw [hproduct] at hb he
  have hf := dynamicGridSample_target_error hτ hτ0 B hΛ.le hT hζ N hτN hB
  have hp := hb.perturb (by positivity : 0 ≤ ζ / 2) hf
  have hb' :=
      hp.mono (show (ζ / 2) ^ 2 / 2 + ζ / 2 ≤ ζ by nlinarith [mul_nonneg hζ.le (sub_nonneg.mpr hζ1)])
  (try dsimp only)
  refine ⟨hw, hO, hb', hq, hg, ?_⟩
  let O := parallelOracle (J := TaylorWordLabel (Fin (S*M)) K) (freshPrimitiveQuery K U)
  let R := tagFrame (taylorEmptyLabel (Fin (S*M)) K)
    (freshWordFrame (I := I) (dynamicGridZeroAddress Λ T N ζ) a₀ K)
  let cs := dynamicGridWord (I := I) a₀ Λ T N ζ
  let G := suppliedGridEvolution (fun j => (j : ℝ)*(T/(S*M : ℕ))) F (S*M)
  change ‖evaluate O cs * R - R * suppliedGridEvolution τ B N‖ ≤ ζ
  have hR : ‖R‖ ≤ 1 := isometry_norm_le hb.right_isometry
  have hfg : ‖G - suppliedGridEvolution τ B N‖ ≤ ζ/2 := by
    simpa only [norm_sub_rev] using! hf
  calc
    _ ≤ ‖evaluate O cs * R - R * G‖ + ‖R * G - R * suppliedGridEvolution τ B N‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ζ/2 + ζ/2 := by
      apply add_le_add he
      rw [← Matrix.mul_sub]
      exact (Matrix.l2_opNorm_mul _ _).trans
        ((mul_le_mul hR hfg (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
    _ = ζ := by ring

end CompleteCircuit
end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
