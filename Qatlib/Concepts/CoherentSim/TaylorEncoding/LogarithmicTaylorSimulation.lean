/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.TaylorBounds
import Mathlib.Data.Nat.Log

/-!
# Taylor simulation with logarithmic segment overhead

`logTaylorCutoff` replaces the linear segment-count precision overhead by a binary logarithmic
overhead. The resulting circuits have explicit forward and adjoint costs and dyadic coherent
error bounds, giving a refined parameter choice for truncated Taylor simulation
[BerryEtAl2015Taylor].

## Main statements

* `log_taylor_computed_precision`: A comparison with the earlier cutoff and the coherent error
  budget.
* `log_taylor_actual_program_and_inverse_cost`: The well-formed circuit and its forward and
  adjoint costs.
* `log_taylor_coherent_full_workspace_error`: The full-workspace dyadic simulation bound.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.CoherentSim.TaylorBounds

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Concepts.CoherentSim.TaylorEncoding

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false

/-- The Taylor cutoff `2 * (k + Nat.clog 2 (max 1 s) + 4)` with logarithmic overhead in the
segment count. -/
def logTaylorCutoff (s k : ℕ) : ℕ := 2 * (k + Nat.clog 2 (max 1 s) + 4)

section Simulation

variable {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

/-- The repeated coherently amplified Taylor LCU word using `logTaylorCutoff`. -/
noncomputable def logTaylorWord (h : J → ℝ) (j0 : J) (t : ℝ) (Λ T k : ℕ) :
    List (AdjointStep (TaylorWordLabel J (logTaylorCutoff (taylorSegments Λ T) k) ×
      (Bool × (J × I)))) :=
  let s := taylorSegments Λ T
  let K := logTaylorCutoff s k
  repeatAdjointWord (substituteAdjointCircuit (taylorLCUWord h j0 (t / s) K)
    (coherentOAAWord (taylorFrame j0 K))) s

/-- The logarithmic-cutoff Taylor word uses `3 * s * K` queries and `s * (6 * K + 13)` gates. -/
theorem logTaylor_word_counts (h : J → ℝ) (j0 : J)
    (t : ℝ) (Λ T k : ℕ) :
    let s := taylorSegments Λ T
    let K := logTaylorCutoff s k
    adjointQueryCount (logTaylorWord (I := I) h j0 t Λ T k) = 3 * s * K ∧
      adjointGateCount (logTaylorWord (I := I) h j0 t Λ T k) = s * (6 * K + 13) := by
  let s := taylorSegments Λ T
  let K := logTaylorCutoff s k
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

omit [DecidableEq J] in

/-- The chosen segment duration makes coefficient mass times absolute duration at most `1 / 2`. -/
private theorem logTaylor_segment_small (h : J → ℝ) (t : ℝ) (Λ T : ℕ)
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

/-- For positive `s`, the `s`th power of exact evolution for duration `t / s` equals evolution
for duration `t`. -/
private theorem logTaylor_ideal_power (H : Matrix I I ℂ) (t : ℝ) (s : ℕ) (hs : 0 < s) :
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

/-- The logarithmic Taylor cutoff bounds accumulated coherent amplification error over `s`
segments by `2⁻ᵏ`. -/
private theorem logTaylor_precision (s k : ℕ) :
    (s : ℝ) * Real.sqrt (2 * coherentOAAError ((1 / 2 : ℝ) ^ logTaylorCutoff s k)) ≤
      (1 / 2 : ℝ) ^ k := by
  let a : ℝ := (1 / 2 : ℝ) ^ (k + Nat.clog 2 (max 1 s) + 4)
  have ha : 0 ≤ a := by positivity
  have he : (1 / 2 : ℝ) ^ logTaylorCutoff s k = a ^ 2 := by
    dsimp only [logTaylorCutoff, a]
    rw [Nat.mul_comm 2 (k + Nat.clog 2 (max 1 s) + 4), pow_mul]
  have he1 : (1 / 2 : ℝ) ^ logTaylorCutoff s k ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have he0 : 0 ≤ (1 / 2 : ℝ) ^ logTaylorCutoff s k := by positivity
  have hc : coherentOAAError ((1 / 2 : ℝ) ^ logTaylorCutoff s k) ≤
      5 * ((1 / 2 : ℝ) ^ logTaylorCutoff s k) := by
    unfold coherentOAAError
    have he2 : ((1 / 2 : ℝ) ^ logTaylorCutoff s k) ^ 2 ≤ 1 :=
      pow_le_one₀ he0 he1
    nlinarith
  have hsqrt : Real.sqrt (2 * coherentOAAError ((1 / 2 : ℝ) ^ logTaylorCutoff s k)) ≤
      4 * a := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [he] at hc ⊢
    nlinarith [sq_nonneg a]
  have hs : (s : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 (max 1 s) := by
    exact_mod_cast (le_max_right 1 s).trans (Nat.le_pow_clog (by norm_num) (max 1 s))
  have hsp : (s : ℝ) * (1 / 2 : ℝ) ^ Nat.clog 2 (max 1 s) ≤ 1 := by
    have hp : (2 : ℝ) ^ Nat.clog 2 (max 1 s) * (1 / 2 : ℝ) ^ Nat.clog 2 (max 1 s) = 1 := by
      rw [← mul_pow]
      norm_num
    exact (mul_le_mul_of_nonneg_right hs (by positivity)).trans hp.le
  calc
    _ ≤ (s : ℝ) * (4 * a) := mul_le_mul_of_nonneg_left hsqrt (Nat.cast_nonneg _)
    _ = (1 / 2 : ℝ) ^ k * ((s : ℝ) * (1 / 2 : ℝ) ^ Nat.clog 2 (max 1 s)) / 4 := by
      dsimp only [a]
      simp only [pow_add]
      norm_num
      ring
    _ ≤ (1 / 2 : ℝ) ^ k := by
      have hp : 0 ≤ (1 / 2 : ℝ) ^ k := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hsp hp]

/-- For Hermitian unitary summands under the supplied bounds, the logarithmic-cutoff word is
well formed and has embedded vector error at most `2⁻ᵏ` times the input norm. -/
theorem logTaylor_full_error (h : J → ℝ)
    (U : J → Matrix I I ℂ) (j0 : J) (t : ℝ) (Λ T k : ℕ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ ∧ (U j).IsHermitian)
    (hΛ : (∑ j, |h j|) ≤ Λ) (hT : |t| ≤ T) :
    let K := logTaylorCutoff (taylorSegments Λ T) k
    let cs := logTaylorWord h j0 t Λ T k
    WellFormedAdjointCircuit cs ∧ ∀ ψ : QState I,
      ‖toEuclidean_fromVec (evaluate (taylorQuery U K) cs *ᵥ (taylorFrame j0 K *ᵥ ψ) -
        taylorFrame j0 K *ᵥ (hamiltonianEvolution (∑ j, (h j : ℂ) • U j) t *ᵥ ψ))‖ ≤
        (1 / 2 : ℝ) ^ k * ‖toEuclidean_fromVec ψ‖ := by
  let s := taylorSegments Λ T
  let K := logTaylorCutoff s k
  let H : Matrix I I ℂ := ∑ j, (h j : ℂ) • U j
  let R := taylorFrame (I := I) j0 K
  let body := taylorLCUWord (I := I) h j0 (t / s) K
  let O := taylorQuery U K
  let V := hamiltonianEvolution H (t / s)
  have hs : 0 < s := (taylor_actual_segment_parameters Λ T k).2.1
  have hsmall := logTaylor_segment_small h t Λ T hΛ hT
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
  have hideal : V ^ s = hamiltonianEvolution H t := logTaylor_ideal_power H t s hs
  rw [hideal] at herr
  exact herr.trans (mul_le_mul_of_nonneg_right (logTaylor_precision s k) (norm_nonneg _))

end Simulation

variable {J : Type} [Fintype J] [DecidableEq J]

/-- The logarithmic-cutoff coherent Taylor simulation word specialized to data operators indexed
by `Fin D`. -/
noncomputable def logTaylorSimulationWord {D : ℕ} (h : J → ℝ) (j0 : J)
    (t : ℝ) (Lambda T k : ℕ) :=
  let s := taylorSegments Lambda T
  let K := logTaylorCutoff s k
  repeatAdjointWord (substituteAdjointCircuit (taylorLCUWord (I := Fin D) h j0 (t/s) K)
    (coherentOAAWord (taylorFrame (I := Fin D) j0 K))) s

/-- The logarithmic cutoff is at most `taylorCutoff s k` and meets the dyadic accumulated
coherent error budget. -/
theorem log_taylor_computed_precision : ∀ s k : ℕ,
  logTaylorCutoff s k ≤ taylorCutoff s k ∧
  (s:ℝ)*Real.sqrt (2*coherentOAAError ((1/2:ℝ)^logTaylorCutoff s k)) ≤ (1/2:ℝ)^k := by
  intro s k
  refine ⟨?_, logTaylor_precision s k⟩
  have hc : Nat.clog 2 (max 1 s) ≤ s := Nat.clog_le_of_le_pow
    (max_le (Nat.succ_le_of_lt (pow_pos (by norm_num : 0 < (2:ℕ)) s))
      (show s ≤ 2^s from Nat.lt_two_pow_self.le))
  dsimp [logTaylorCutoff, taylorCutoff]
  omega

/-- Under the stated simulation assumptions, the logarithmic Taylor program is well formed. It
and its adjoint each use `3 * s * K` queries and `s * (6 * K + 13)` gates. -/
theorem log_taylor_actual_program_and_inverse_cost : ∀ (D : ℕ) (h : J → ℝ) (U : J → Operator D) (j0 : J)
    (t : ℝ) (Lambda T k : ℕ),
  (∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ ∧ (U j).IsHermitian) →
  (∑ j, |h j|) ≤ Lambda → |t| ≤ T →
  let s := taylorSegments Lambda T
  let K := logTaylorCutoff s k
  let cs := logTaylorSimulationWord (D := D) h j0 t Lambda T k
  WellFormedAdjointCircuit cs ∧ adjointQueryCount cs = 3*s*K ∧
  adjointGateCount cs = s*(6*K+13) ∧
  adjointQueryCount (adjointCircuit cs) = 3*s*K ∧
  adjointGateCount (adjointCircuit cs) = s*(6*K+13) := by
  intro D h U j0 t Lambda T k hU hL hT
  have hf := logTaylor_full_error h U j0 t Lambda T k hU hL hT
  obtain ⟨hq, hg⟩ := logTaylor_word_counts (I := Fin D) h j0 t Lambda T k
  exact ⟨hf.1, hq, hg, by simpa using! hq, by simpa using! hg⟩

/-- For the stated Hermitian unitary decomposition and parameter bounds, the full-workspace
logarithmic Taylor output differs from the embedded ideal evolution by at most `2⁻ᵏ` times
the input norm. -/
theorem log_taylor_coherent_full_workspace_error : ∀ (D : ℕ) (h : J → ℝ) (U : J → Operator D) (j0 : J)
    (t : ℝ) (Lambda T k : ℕ),
  (∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ ∧ (U j).IsHermitian) →
  (∑ j, |h j|) ≤ Lambda → |t| ≤ T →
  let s := taylorSegments Lambda T
  let K := logTaylorCutoff s k
  let cs := logTaylorSimulationWord (D := D) h j0 t Lambda T k
  (∀ psi : QState (Fin D), ‖toEuclidean_fromVec
    (evaluate (taylorQuery U K) cs *ᵥ (taylorFrame j0 K *ᵥ psi) -
      taylorFrame j0 K *ᵥ (hamiltonianEvolution (∑ j, (h j:ℂ) • U j) t *ᵥ psi))‖ ≤
      (1/2:ℝ)^k*‖toEuclidean_fromVec psi‖)
 := by
  intro D h U j0 t Lambda T k hU hL hT
  exact (logTaylor_full_error h U j0 t Lambda T k hU hL hT).2

end Qatlib.Concepts.CoherentSim.TaylorEncoding
