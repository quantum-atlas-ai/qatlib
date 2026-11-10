/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.TaylorEncoding.TaylorLCUProgram
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.CoherentSim.TaylorEncoding

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Concepts.CoherentSim.TaylorBounds

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false
set_option linter.unusedSectionVars false

def taylorSegments (Λ T : ℕ) : ℕ := max 1 (2 * Λ * T)

def taylorCutoff (s k : ℕ) : ℕ := 2 * (k + s + 4)

theorem taylor_actual_segment_parameters (Λ T k : ℕ) :
    taylorSegments Λ T = max 1 (2 * Λ * T) ∧ 0 < taylorSegments Λ T ∧
      taylorCutoff (taylorSegments Λ T) k = 2 * (k + taylorSegments Λ T + 4) :=
  ⟨rfl, lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _), rfl⟩

section Simulation

variable {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

noncomputable def taylorSimulationWord (h : J → ℝ) (j0 : J) (t : ℝ) (Λ T k : ℕ) :
    List (AdjointStep (TaylorWordLabel J (taylorCutoff (taylorSegments Λ T) k) ×
      (Bool × (J × I)))) :=
  let s := taylorSegments Λ T
  let K := taylorCutoff s k
  repeatAdjointWord (substituteAdjointCircuit (taylorLCUWord h j0 (t / s) K)
    (coherentOAAWord (taylorFrame j0 K))) s

theorem taylor_actual_oaa_expansion_and_segment_cost (h : J → ℝ) (j0 : J)
    (t : ℝ) (Λ T k : ℕ) :
    let s := taylorSegments Λ T
    let K := taylorCutoff s k
    adjointQueryCount (taylorSimulationWord (I := I) h j0 t Λ T k) = 3 * s * K ∧
      adjointGateCount (taylorSimulationWord (I := I) h j0 t Λ T k) = s * (6 * K + 13) := by
  let s := taylorSegments Λ T
  let K := taylorCutoff s k
  let body := taylorLCUWord (I := I) h j0 (t / s) K
  let R := taylorFrame (I := I) j0 K
  let O : Matrix (TaylorWordLabel J K × (Bool × (J × I)))
      (TaylorWordLabel J K × (Bool × (J × I))) ℂ := 1
  obtain ⟨_, hq, hg, _, _⟩ := coherent_oaa_word_correct O R
    (taylorFrame_isIsometry j0 K) (Matrix.unitaryGroup _ ℂ).one_mem
  obtain ⟨_, eqc, egc, _⟩ := substitute_adjoint_evaluate_cost O body (coherentOAAWord R)
  obtain ⟨_, rqc, rgc, _⟩ := repeat_adjoint_word_semantics_cost O
    (substituteAdjointCircuit body (coherentOAAWord R)) s
  obtain ⟨bqc, bgc⟩ := taylorLCUWord_counts (I := I) h j0 (t / s) K
  change adjointQueryCount (repeatAdjointWord (substituteAdjointCircuit body (coherentOAAWord R)) s)
      = 3 * s * K ∧
    adjointGateCount (repeatAdjointWord (substituteAdjointCircuit body (coherentOAAWord R)) s)
      = s * (6 * K + 13)
  rw [rqc, rgc, eqc, egc, hq, hg, bqc, bgc]
  constructor <;> ring

private theorem taylor_segment_small (h : J → ℝ) (t : ℝ) (Λ T : ℕ)
    (hΛ : (∑ j, |h j|) ≤ Λ) (hT : |t| ≤ T) :
    (∑ j, |h j|) * |t / (taylorSegments Λ T : ℝ)| ≤ 1 / 2 := by
  have hs : 0 < (taylorSegments Λ T : ℝ) := by
    exact_mod_cast (taylor_actual_segment_parameters Λ T 0).2.1
  have hb : 2 * (Λ : ℝ) * (T : ℝ) ≤ (taylorSegments Λ T : ℝ) := by
    exact_mod_cast (le_max_right 1 (2 * Λ * T))
  rw [abs_div, abs_of_pos hs, ← mul_div_assoc, div_le_iff₀ hs]
  have hp : (∑ j, |h j|) * |t| ≤ (Λ : ℝ) * T :=
    mul_le_mul hΛ hT (abs_nonneg _) (Nat.cast_nonneg _)
  linarith

private theorem taylor_ideal_power (H : Matrix I I ℂ) (t : ℝ) (s : ℕ) (hs : 0 < s) :
    (hamiltonianEvolution H (t / s)) ^ s = hamiltonianEvolution H t := by
  have hp : ∀ n : ℕ, (hamiltonianEvolution H (t / s)) ^ n =
      hamiltonianEvolution H ((n : ℝ) * (t / s)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, ih]
        change HamiltonianEvolution H ((n : ℝ) * (t / s)) *
          HamiltonianEvolution H (t / s) = _
        rw [← hamiltonianEvolution_add]
        congr 1
        push_cast
        ring
  rw [hp]
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [mul_div_cancel₀ _ hs0]

private theorem taylor_coherent_precision (s k : ℕ) :
    (s : ℝ) * Real.sqrt (2 * coherentOAAError ((1 / 2 : ℝ) ^ taylorCutoff s k)) ≤
      (1 / 2 : ℝ) ^ k := by
  let a : ℝ := (1 / 2 : ℝ) ^ (k + s + 4)
  have ha : 0 ≤ a := by positivity
  have he : (1 / 2 : ℝ) ^ taylorCutoff s k = a ^ 2 := by
    dsimp only [taylorCutoff, a]
    rw [Nat.mul_comm 2 (k + s + 4), pow_mul]
  have he1 : (1 / 2 : ℝ) ^ taylorCutoff s k ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have he0 : 0 ≤ (1 / 2 : ℝ) ^ taylorCutoff s k := by positivity
  have hc : coherentOAAError ((1 / 2 : ℝ) ^ taylorCutoff s k) ≤
      5 * ((1 / 2 : ℝ) ^ taylorCutoff s k) := by
    unfold coherentOAAError
    have he2 : ((1 / 2 : ℝ) ^ taylorCutoff s k) ^ 2 ≤ 1 :=
      pow_le_one₀ he0 he1
    nlinarith
  have hsqrt : Real.sqrt (2 * coherentOAAError ((1 / 2 : ℝ) ^ taylorCutoff s k)) ≤
      4 * a := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [he] at hc ⊢
    nlinarith [sq_nonneg a]
  have hs : (s : ℝ) ≤ (2 : ℝ) ^ s := by
    exact_mod_cast (show s < 2 ^ s from Nat.lt_two_pow_self).le
  have hsp : (s : ℝ) * (1 / 2 : ℝ) ^ s ≤ 1 := by
    have hp : (2 : ℝ) ^ s * (1 / 2 : ℝ) ^ s = 1 := by
      rw [← mul_pow]
      norm_num
    exact (mul_le_mul_of_nonneg_right hs (by positivity)).trans hp.le
  calc
    _ ≤ (s : ℝ) * (4 * a) := mul_le_mul_of_nonneg_left hsqrt (Nat.cast_nonneg _)
    _ = (1 / 2 : ℝ) ^ k * ((s : ℝ) * (1 / 2 : ℝ) ^ s) / 4 := by
      dsimp only [a]
      simp only [pow_add]
      norm_num
      ring
    _ ≤ (1 / 2 : ℝ) ^ k := by
      have hp : 0 ≤ (1 / 2 : ℝ) ^ k := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hsp hp]

theorem taylor_computed_coherent_full_simulation_error (h : J → ℝ)
    (U : J → Matrix I I ℂ) (j0 : J) (t : ℝ) (Λ T k : ℕ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ ∧ (U j).IsHermitian)
    (hΛ : (∑ j, |h j|) ≤ Λ) (hT : |t| ≤ T) :
    let K := taylorCutoff (taylorSegments Λ T) k
    let cs := taylorSimulationWord h j0 t Λ T k
    WellFormedAdjointCircuit cs ∧ ∀ ψ : QState I,
      ‖toEuclidean_fromVec (evaluate (taylorQuery U K) cs *ᵥ (taylorFrame j0 K *ᵥ ψ) -
        taylorFrame j0 K *ᵥ (hamiltonianEvolution (∑ j, (h j : ℂ) • U j) t *ᵥ ψ))‖ ≤
        (1 / 2 : ℝ) ^ k * ‖toEuclidean_fromVec ψ‖ := by
  let s := taylorSegments Λ T
  let K := taylorCutoff s k
  let H : Matrix I I ℂ := ∑ j, (h j : ℂ) • U j
  let R := taylorFrame (I := I) j0 K
  let body := taylorLCUWord (I := I) h j0 (t / s) K
  let O := taylorQuery U K
  let V := hamiltonianEvolution H (t / s)
  have hs : 0 < s := (taylor_actual_segment_parameters Λ T k).2.1
  have hsmall := taylor_segment_small h t Λ T hΛ hT
  have hb := (taylor_lcu_actual_prepare_select_and_counts (I := I) h j0 (t / s) K hsmall).2.1
  have hH : H.IsHermitian := by
    apply isSelfAdjoint_sum
    intro j _
    exact (hU j).2.smul (by simp [IsSelfAdjoint])
  have hV : V ∈ Matrix.unitaryGroup I ℂ := hamiltonianEvolution_unitary hH _
  have hO : O ∈ Matrix.unitaryGroup _ ℂ := taylorQuery_unitary U (fun j => (hU j).1) K
  have henc : BlockEncoding V (evaluate O body) R R 2 ((1 / 2 : ℝ) ^ K) :=
    taylor_actual_scale_two_evolution_encoding h U j0 (t / s) K hU hsmall
  have hexp := coherent_oaa_expanded_subroutine O body R hb henc.right_isometry
  have hrep := repeat_adjoint_word_semantics_cost O
    (substituteAdjointCircuit body (coherentOAAWord R)) s
  refine ⟨hrep.2.2.2 hexp.2.2.2, ?_⟩
  intro ψ
  have herr := (coherent_oaa_expanded_repeat_error_and_cost O body V R
    ((1 / 2 : ℝ) ^ K) hO hb hV henc s ψ).2.2
  have hideal : V ^ s = hamiltonianEvolution H t := taylor_ideal_power H t s hs
  rw [hideal] at herr
  exact herr.trans (mul_le_mul_of_nonneg_right (taylor_coherent_precision s k) (norm_nonneg _))

end Simulation

theorem taylor_actual_noncommuting_xz_consumer :
    let h : Bool → ℝ := fun _ => 1
    let U : Bool → Matrix Bool Bool ℂ := fun b => if b then PauliZ else PauliX
    let cs := taylorSimulationWord (I := Bool) h false 1 2 1 1
    let K := taylorCutoff (taylorSegments 2 1) 1
    adjointQueryCount cs = 216 ∧ adjointGateCount cs = 484 ∧
      ‖toEuclidean_fromVec (evaluate (taylorQuery U K) cs *ᵥ (taylorFrame false K *ᵥ Ket false) -
        taylorFrame false K *ᵥ (hamiltonianEvolution (PauliX + PauliZ) 1 *ᵥ Ket false))‖ ≤ 1 / 2 := by
  let h : Bool → ℝ := fun _ => 1
  let U : Bool → Matrix Bool Bool ℂ := fun b => if b then PauliZ else PauliX
  have hU : ∀ b, U b ∈ Matrix.unitaryGroup Bool ℂ ∧ (U b).IsHermitian := by
    intro b
    cases b
    · refine ⟨pauliX_unitary, ?_⟩
      ext i j
      cases i <;> cases j <;> simp [U, Matrix.conjTranspose_apply, PauliX, permMatrix]
    · exact ⟨pauliZ_unitary, pauliZ_conjTranspose⟩
  have hH : (∑ b, (h b : ℂ) • U b) = PauliX + PauliZ := by
    simp [h, U, add_comm]
  have hΛ : (∑ b, |h b|) ≤ (2 : ℕ) := by norm_num [h, Fintype.sum_bool]
  have hT : |(1 : ℝ)| ≤ (1 : ℕ) := by norm_num
  obtain ⟨hq, hg⟩ := taylor_actual_oaa_expansion_and_segment_cost (I := Bool) h false 1 2 1 1
  have herr := (taylor_computed_coherent_full_simulation_error h U false 1 2 1 1 hU hΛ hT).2
    (Ket false)
  rw [hH] at herr
  have hn : ‖toEuclidean_fromVec (Ket false : QState Bool)‖ = 1 := by
    rw [← normalized_iff_norm_toEuclidean_fromVec]
    exact normalized_ket false
  rw [hn] at herr
  exact ⟨hq, hg, by simpa using herr⟩

end Qatlib.Concepts.CoherentSim.TaylorBounds
