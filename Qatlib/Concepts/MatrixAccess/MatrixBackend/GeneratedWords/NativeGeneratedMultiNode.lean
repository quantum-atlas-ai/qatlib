/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.FreshFlagWord
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeGeneratedShiftBudget
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeGroupedNeumannConsumer
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeRationalColumnCertificate
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.HouseholderTableConsumer
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.BlockEncoding.LCU

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann

open Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding
/-! Generated node precision in the actual table-weighted shared query word.
The outer table is supplied rational data: its grouped residual is computed,
not an assumed operator error. Logical rotations, phases, SELECT and frame
reflections are charged instructions, not synthesized elementary gates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

variable {J H I : Type} [Fintype J] [DecidableEq J]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- The generated single-node theorem bounds the actual clean polynomial
used by the shared word, with no b² degradation of the logarithmic budget. -/
theorem native_generated_clean_node_error
    (K k : ℕ) (hK : 2 ≤ K) (α B x y : ℚ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2)
    (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (r : ℝ) (hbe : BlockEncoding A U F F (α : ℝ) 0) (hr : 0<r)
    (hsep : ∀ w ∈ matrixNumericalRange A, r ≤ ‖gaussianRatComplex (x,y)-w‖)
    (hcondition : jointResolventCondition (B : ℝ) r ≤ (K : ℝ)) :
    let p := nativeShiftBudgetPrecision K k
    let b := nativeShiftBudgetCutoff K k
    ‖matrixResolvent A (gaussianRatComplex (x,y)) - ((b : ℝ)/(B : ℝ)) •
      cleanEndpointBlock b A (α : ℝ)
        (fun _ : Unit => nativeShiftCircles α B x y p)
        (fun _ => nativePhaseCircle x y p) (fun _ => nativeShiftSlack α B x y) ()‖ ≤
      ((2 : ℝ)⁻¹)^k/(B : ℝ) := by
  obtain ⟨hb, _, he, _, _⟩ := native_generated_neumann_log_precision K k hK α B x y
    hα hB hz A U F r hbe hr hsep hcondition
  have hp := (native_original_neumann_encoding _ hb
    (nativeShiftCircles α B x y (nativeShiftBudgetPrecision K k))
    (nativePhaseCircle x y (nativeShiftBudgetPrecision K k))
    (nativeShiftSlack α B x y) A U F (α : ℝ) hbe).2.1
  have hh := he.error_le
  rw [hp.encoded] at hh
  exact hh

/-- Typeclass instance for generated Multi Inner Dec Eq in the native generated multi node model. -/
local instance generatedMultiInnerDecEq (b : ℕ) : DecidableEq
    (NeumannBranchSpace (b-1) (Fin b × (Reg 6 × H))) := Classical.decEq _
/-- Typeclass instance for generated Multi Outer Dec Eq in the native generated multi node model. -/
local instance generatedMultiOuterDecEq (n b : ℕ) : DecidableEq
    (Option (Fin n) × NeumannBranchSpace (b-1) (Fin b × (Reg 6 × H))) := Classical.decEq _

/-- Same original input and frame at all nodes. The outer normalization is
the checked coordinate mass L, with duplicate slack labels grouped before D.
All error and count conclusions concern this one expanded logical word. -/
theorem native_generated_multinode_checked
    {n : ℕ} (K k : ℕ) (hK : 2 ≤ K)
    (node : Option (Fin n) → J) (hnode : Function.Surjective node)
    (rs : List (Fin n × Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)) (phase : Option (Fin n) → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (weights : J → GaussianRat) (L D : ℚ)
    (hmass : rationalWeightMassCheck weights L=true)
    (hcolumn : rationalColumnCheck node rs phase weights L D=true)
    (α B : ℚ) (x y : J → ℚ) (hα : 0<α) (hB : α ≤ B)
    (hz : ∀ j, x j*x j+y j*y j ≤ (B-α)^2)
    (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (r : J → ℝ) (hbe : BlockEncoding A U F F (α : ℝ) 0) (hr : ∀ j, 0<r j)
    (hsep : ∀ j, ∀ w ∈ matrixNumericalRange A, r j ≤ ‖gaussianRatComplex (x j,y j)-w‖)
    (hcondition : ∀ j, jointResolventCondition (B : ℝ) (r j) ≤ (K : ℝ)) :
    let p := nativeShiftBudgetPrecision K k
    let b := nativeShiftBudgetCutoff K k
    let ps := fun j => nativeShiftCircles α B (x j) (y j) p
    let q := fun j => nativePhaseCircle (x j) (y j) p
    let slack := fun j => nativeShiftSlack α B (x j) (y j)
    ∃ hb : 0<b,
      let W := householderInputWord rs (fun a => phaseScalar (phase a))
        (cleanEndpointBody b hb F (fun a => ps (node a))
          (fun a => q (node a)) (fun a => slack (node a)))
      WellFormedAdjointCircuit W ∧
      BlockEncoding (∑ j, gaussianRatComplex (weights j) •
          matrixResolvent A (gaussianRatComplex (x j,y j)))
        (evaluate (cleanEndpointOracle (J := Option (Fin n)) b U) W)
        (tagFrame none (cleanEndpointFrame b hb F))
        (tagFrame none (cleanEndpointFrame b hb F))
        ((L : ℝ)*((b : ℝ)/(B : ℝ)))
        ((L : ℝ)*(((2 : ℝ)⁻¹)^k/(B : ℝ))+
          (L : ℝ)*((b : ℝ)/(B : ℝ))*(D : ℝ)) ∧
      adjointQueryCount W=2*b-1 ∧
      adjointGateCount W=2*b+(2*b-1)*3+4*rs.length+3 := by
  let p := nativeShiftBudgetPrecision K k
  let b := nativeShiftBudgetCutoff K k
  let ps := fun j => nativeShiftCircles α B (x j) (y j) p
  let q := fun j => nativePhaseCircle (x j) (y j) p
  let slack := fun j => nativeShiftSlack α B (x j) (y j)
  have hb : 0<b := by
    dsimp [b, nativeShiftBudgetCutoff]
    have : 0<K := by omega
    positivity
  let Y := cleanEndpointBlock b A (α : ℝ) ps q slack
  let body := cleanEndpointBody b hb F (fun a => ps (node a))
    (fun a => q (node a)) (fun a => slack (node a))
  let O := cleanEndpointOracle (J := Option (Fin n)) b U
  let φ := fun a => phaseScalar (phase a)
  have hφ (a : Option (Fin n)) : star (φ a)*φ a=1 := by
    simpa only [φ, RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_one]
      using congrArg (fun t : ℝ => (t : ℂ)) (phaseScalar_norm (phase a))
  have hLq := (rationalWeightMassCheck_iff weights L).mp hmass
  have hL : (0 : ℝ)<L := by exact_mod_cast hLq.2
  have hB0 : (0 : ℝ)<B := by exact_mod_cast hα.trans_le hB
  have hs : 0<(b : ℝ)/(B : ℝ) := div_pos (by exact_mod_cast hb) hB0
  have hF := endpoint_frame_isometry b hb F hbe.left_isometry
  have hW := endpoint_word_unitary b hb F A U (α : ℝ) hbe
    (fun a => ps (node a)) (fun a => q (node a)) (fun a => slack (node a))
  have hblock := endpoint_block b hb F A U (α : ℝ) hbe
    (fun a => ps (node a)) (fun a => q (node a)) (fun a => slack (node a))
  have hε (j : J) : ‖matrixResolvent A (gaussianRatComplex (x j,y j))-
      ((b : ℝ)/(B : ℝ)) • Y j‖ ≤ ((2 : ℝ)⁻¹)^k/(B : ℝ) :=
    native_generated_clean_node_error K k hK α B (x j) (y j) hα hB (hz j)
      A U F (r j) hbe (hr j) (hsep j) (hcondition j)
  have hpost := grouped_column_word_error node hnode (cleanEndpointFrame b hb F) O body
    Y (fun j => matrixResolvent A (gaussianRatComplex (x j,y j)))
    (tableHouseholder rs) φ none (fun j => gaussianRatComplex (weights j))
    (L : ℝ) ((b : ℝ)/(B : ℝ)) (D : ℝ) (fun _ => ((2 : ℝ)⁻¹)^k/(B : ℝ))
    hF (tableHouseholder_unitary rs) hφ hW hblock hL hs
    (rationalColumnCheck_sound node rs phase weights L D hcolumn) hε
  have hinput := inputColumnPhaseWord_transfer _ (cleanEndpointFrame b hb F) O body
    (fun a => Y (node a)) (tableHouseholder rs) φ none _ _
    (tableHouseholder_unitary rs) hφ hW hblock hpost
  have hmassbound : (∑ j, ‖gaussianRatComplex (weights j)‖) ≤ (L : ℝ) := by
    rw [hLq.1]
    exact rationalWeightMass_majorizes weights
  have herror : (∑ j, ‖gaussianRatComplex (weights j)‖ * (((2 : ℝ)⁻¹)^k/(B : ℝ)))+
      (L : ℝ)*((b : ℝ)/(B : ℝ))*(D : ℝ) ≤
      (L : ℝ)*(((2 : ℝ)⁻¹)^k/(B : ℝ))+(L : ℝ)*((b : ℝ)/(B : ℝ))*(D : ℝ) := by
    rw [← Finset.sum_mul]
    exact add_le_add (mul_le_mul_of_nonneg_right hmassbound
      (show 0 ≤ ((2 : ℝ)⁻¹)^k/(B : ℝ) by positivity)) le_rfl
  refine ⟨hb, ?_, ?_, ?_, ?_⟩
  · exact householderInputWord_legal rs φ body hφ
      (experiment_relabeled_legal b hb F _ _ _ hbe.left_isometry)
  · rw [householderInputWord_evaluate]
    exact hinput.mono herror
  · exact (householderInputWord_counts rs φ body).1.trans
      (nativeMultiNodeRelabeledWord_cost b hb F _ _ _ U).1
  · rw [(householderInputWord_counts rs φ body).2]
    exact congrArg (fun t => t+4*rs.length+3)
      (nativeMultiNodeRelabeledWord_cost b hb F _ _ _ U).2

/-- Canonical coordinate mass and residual are computed from the supplied
table. No L/D certificate, PREP completion or per-node budget is an input.
This does not assert a universal accuracy rate for the outer producer. -/
theorem native_generated_multinode
    {n : ℕ} (K k : ℕ) (hK : 2 ≤ K)
    (node : Option (Fin n) → J) (hnode : Function.Surjective node)
    (rs : List (Fin n × Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)) (phase : Option (Fin n) → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (weights : J → GaussianRat) (hmass : 0<rationalWeightMass weights)
    (α B : ℚ) (x y : J → ℚ) (hα : 0<α) (hB : α ≤ B)
    (hz : ∀ j, x j*x j+y j*y j ≤ (B-α)^2)
    (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (r : J → ℝ) (hbe : BlockEncoding A U F F (α : ℝ) 0) (hr : ∀ j, 0<r j)
    (hsep : ∀ j, ∀ w ∈ matrixNumericalRange A, r j ≤ ‖gaussianRatComplex (x j,y j)-w‖)
    (hcondition : ∀ j, jointResolventCondition (B : ℝ) (r j) ≤ (K : ℝ)) :
    let L := rationalWeightMass weights
    let D := rationalColumnD node rs phase weights L
    let p := nativeShiftBudgetPrecision K k
    let b := nativeShiftBudgetCutoff K k
    let ps := fun j => nativeShiftCircles α B (x j) (y j) p
    let q := fun j => nativePhaseCircle (x j) (y j) p
    let slack := fun j => nativeShiftSlack α B (x j) (y j)
    ∃ hb : 0<b,
      let W := householderInputWord rs (fun a => phaseScalar (phase a))
        (cleanEndpointBody b hb F (fun a => ps (node a))
          (fun a => q (node a)) (fun a => slack (node a)))
      WellFormedAdjointCircuit W ∧
      BlockEncoding (∑ j, gaussianRatComplex (weights j) •
          matrixResolvent A (gaussianRatComplex (x j,y j)))
        (evaluate (cleanEndpointOracle (J := Option (Fin n)) b U) W)
        (tagFrame none (cleanEndpointFrame b hb F))
        (tagFrame none (cleanEndpointFrame b hb F))
        ((L : ℝ)*((b : ℝ)/(B : ℝ)))
        ((L : ℝ)*(((2 : ℝ)⁻¹)^k/(B : ℝ))+
          (L : ℝ)*((b : ℝ)/(B : ℝ))*(D : ℝ)) ∧
      adjointQueryCount W=2*b-1 ∧
      adjointGateCount W=2*b+(2*b-1)*3+4*rs.length+3 := by
  exact native_generated_multinode_checked K k hK node hnode rs phase weights
    (rationalWeightMass weights) (rationalColumnD node rs phase weights (rationalWeightMass weights))
    ((rationalWeightMassCheck_iff _ _).mpr ⟨rfl, hmass⟩)
    (by simp only [rationalColumnCheck, le_refl, decide_true])
    α B x y hα hB hz A U F r hbe hr hsep hcondition

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
