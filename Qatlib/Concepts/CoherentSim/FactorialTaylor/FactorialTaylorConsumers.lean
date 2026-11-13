/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.FactorialTaylor.FactorialTaylorSimulation
import Qatlib.Concepts.QspSimulation.Achievability.OraclePerturbation
import Qatlib.Concepts.OperatorErrors.Robustness
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws

/-!
# Factorial Taylor simulation consumers

`factorialTaylorWord` repeats amplified Taylor segments using a cutoff selected by a factorial
tail bound. The module establishes coherent simulation accuracy, the costs of the word and its
adjoint, and stability under unitary oracle perturbations, developing the truncated Taylor
method [BerryEtAl2015Taylor].

## Main statements

* `factorial_taylor_actual_simulation_and_paid_inverse`: Coherent simulation with forward and
  adjoint resource counts.
* `factorial_taylor_same_program_oracle_noise`: Simulation accuracy with perturbed summand
  oracles.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

open Qatlib.Concepts.OperatorErrors.Robustness
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.CoherentSim.TaylorBounds
open Qatlib.Concepts.CoherentSim.TaylorEncoding
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Concepts.CoherentSim.FactorialTaylor
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped BigOperators Matrix.Norms.L2Operator
set_option autoImplicit false
set_option maxHeartbeats 800000
attribute [local irreducible] factorialTaylorCutoff factorialTaylorPrecision

/-- The repeated coherently amplified Taylor circuit with segment count `taylorSegments` and a
factorially chosen truncation cutoff. -/
noncomputable def factorialTaylorWord {J I : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (h : J → ℝ) (j₀ : J) (t : ℝ) (Λ T k : ℕ) :=
  let s := taylorSegments Λ T
  let K := factorialTaylorCutoff (factorialTaylorPrecision s k)
  repeatAdjointWord (substituteAdjointCircuit (taylorLCUWord (I:=I) h j₀ (t/s) K)
    (coherentOAAWord (taylorFrame (I:=I) j₀ K))) s

variable {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

/-- The factorial Taylor word uses `3 * s * K` queries and `s * (6 * K + 13)` gates for the
selected segment count and cutoff. -/
theorem factorialTaylor_word_counts (h : J → ℝ) (j0 : J)
    (t : ℝ) (Λ T k : ℕ) :
    let s := taylorSegments Λ T
    let K := factorialTaylorCutoff (factorialTaylorPrecision s k)
    adjointQueryCount (factorialTaylorWord (I := I) h j0 t Λ T k) = 3 * s * K ∧
      adjointGateCount (factorialTaylorWord (I := I) h j0 t Λ T k) = s * (6 * K + 13) := by
  let s := taylorSegments Λ T
  let K := factorialTaylorCutoff (factorialTaylorPrecision s k)
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

/-- The coefficient mass times the absolute segment duration is at most `1 / 2` under the
supplied coefficient and time bounds. -/
private theorem factorialTaylor_segment_small (h : J → ℝ) (t : ℝ) (Λ T : ℕ)
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

/-- Repeating exact Hamiltonian evolution for duration `t / s` a positive number `s` of times
gives evolution for duration `t`. -/
private theorem factorialTaylor_ideal_power (H : Matrix I I ℂ) (t : ℝ) (s : ℕ) (hs : 0 < s) :
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

/-- For Hermitian unitary summands, the factorial Taylor word is well formed and approximates
the embedded evolution with relative vector error at most `2⁻ᵏ`. It and its adjoint have the
displayed query and gate counts. See [BerryEtAl2015Taylor]. -/
theorem factorial_taylor_actual_simulation_and_paid_inverse :
  ∀ (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (h : J → ℝ) (U : J → Matrix I I ℂ) (j₀ : J) (t : ℝ) (Λ T k : ℕ),
    (∀ j, U j ∈ unitaryGroup I ℂ ∧ (U j).IsHermitian) →
    (∑ j, |h j|) ≤ Λ → |t| ≤ T →
    let s := taylorSegments Λ T
    let K := factorialTaylorCutoff (factorialTaylorPrecision s k)
    let cs := factorialTaylorWord (I:=I) h j₀ t Λ T k
    WellFormedAdjointCircuit cs ∧
    adjointQueryCount cs = 3*s*K ∧ adjointGateCount cs = s*(6*K+13) ∧
    adjointQueryCount (adjointCircuit cs) = 3*s*K ∧
    adjointGateCount (adjointCircuit cs) = s*(6*K+13) ∧
    (∀ ψ : QState I, ‖toEuclidean_fromVec
      (evaluate (taylorQuery U K) cs *ᵥ (taylorFrame j₀ K *ᵥ ψ) -
        taylorFrame j₀ K *ᵥ (hamiltonianEvolution (∑ j, (h j : ℂ) • U j) t *ᵥ ψ))‖ ≤
      (1/2:ℝ)^k * ‖toEuclidean_fromVec ψ‖) := by
  intro J I _ _ _ _ h U j₀ t Λ T k hU hΛ hT
  let s := taylorSegments Λ T
  let K := factorialTaylorCutoff (factorialTaylorPrecision s k)
  let H : Matrix I I ℂ := ∑ j, (h j : ℂ) • U j
  let R := taylorFrame (I := I) j₀ K
  let body := taylorLCUWord (I := I) h j₀ (t / s) K
  let O := taylorQuery U K
  let V := hamiltonianEvolution H (t / s)
  have hs : 0 < s := (taylor_actual_segment_parameters Λ T k).2.1
  have hsmall := factorialTaylor_segment_small h t Λ T hΛ hT
  have hb := (taylor_lcu_actual_prepare_select_and_counts (I := I) h j₀ (t / s) K hsmall).2.1
  have hH : H.IsHermitian := by
    apply isSelfAdjoint_sum
    intro j _
    exact (hU j).2.smul (by simp [IsSelfAdjoint])
  have hV : V ∈ Matrix.unitaryGroup I ℂ := hamiltonianEvolution_unitary hH _
  have hO : O ∈ Matrix.unitaryGroup _ ℂ := taylorQuery_unitary U (fun j => (hU j).1) K
  let ε : ℝ := 2/((K+1).factorial : ℝ)
  have henc : BlockEncoding V (evaluate O body) R R 2 ε := by
    refine ⟨hb.evaluate_unitary hO, taylorFrame_isIsometry j₀ K,
      taylorFrame_isIsometry j₀ K, by norm_num, by dsimp [ε]; positivity, ?_⟩
    dsimp only [O, body, R, V]
    rw [taylor_actual_lcu_corner_polynomial h U j₀ (t/s) K (fun j => (hU j).1) hsmall,
      RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
    norm_num
    rw [norm_sub_rev]
    exact factorialTaylor_matrix_remainder h U (t/s) K hU hsmall
  have hexp := coherent_oaa_expanded_subroutine O body R hb henc.right_isometry
  have hrep := repeat_adjoint_word_semantics_cost O
    (substituteAdjointCircuit body (coherentOAAWord R)) s
  obtain ⟨hq, hg⟩ := factorialTaylor_word_counts (I := I) h j₀ t Λ T k
  refine ⟨hrep.2.2.2 hexp.2.2.2, hq, hg, by simpa using! hq, by simpa using! hg, ?_⟩
  intro ψ
  have herr := (coherent_oaa_expanded_repeat_error_and_cost O body V R
    ε hO hb hV henc s ψ).2.2
  have hideal : V ^ s = hamiltonianEvolution H t := factorialTaylor_ideal_power H t s hs
  rw [hideal] at herr
  exact herr.trans
      (mul_le_mul_of_nonneg_right (factorial_taylor_tail_and_coherent_precision.2 s k) (norm_nonneg _))

/-- A uniform nonnegative norm bound on the blocks bounds the norm of their SELECT operator. -/
theorem factorialTaylor_select_norm_le (A : J → Matrix I I ℂ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hA : ∀ j, ‖A j‖ ≤ δ) : ‖select A‖ ≤ δ := by
  apply l2_opNorm_le_of_mulVec_le hδ
  intro ψ
  have he : ∀ j i, (select A *ᵥ ψ) (j,i) = (A j *ᵥ (fun i => ψ (j,i))) i := by
    intro j i
    simp [select, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_mul]
  have hb : ∀ j, ‖toEuclidean_fromVec (A j *ᵥ (fun i => ψ (j,i)))‖^2 ≤
      δ^2 * ‖toEuclidean_fromVec (fun i => ψ (j,i))‖^2 := by
    intro j
    have h := (l2_norm_mulVec_fromVec_le (A j) (fun i => ψ (j,i))).trans
      (mul_le_mul_of_nonneg_right (hA j) (norm_nonneg _))
    nlinarith [norm_nonneg (toEuclidean_fromVec (A j *ᵥ (fun i => ψ (j,i)))),
      norm_nonneg (toEuclidean_fromVec (fun i => ψ (j,i)))]
  have hs : ‖toEuclidean_fromVec (select A *ᵥ ψ)‖^2 ≤
      δ^2 * ‖toEuclidean_fromVec ψ‖^2 := by
    simp only [norm_toEuclidean_fromVec_sq, Fintype.sum_prod_type, he] at hb ⊢
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hb j
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hδ (norm_nonneg _))).mp
  simpa only [mul_pow] using! hs

/-- A uniform norm perturbation of the summand operators bounds the corresponding Taylor-query
perturbation by the same amount. -/
theorem factorialTaylor_query_noise (U V : J → Matrix I I ℂ) (K : ℕ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hUV : ∀ j, ‖U j-V j‖ ≤ δ) :
    ‖taylorQuery V K-taylorQuery U K‖ ≤ δ := by
  let A : Bool → Matrix (J×I) (J×I) ℂ :=
    fun b => if b then select (fun j => V j-U j) else 0
  have hA : ∀ b, ‖A b‖ ≤ δ := by
    intro b
    cases b
    · simpa [A] using! hδ
    · change ‖select (fun j => V j-U j)‖ ≤ δ
      apply factorialTaylor_select_norm_le _ δ hδ
      intro j
      simpa [norm_sub_rev] using! hUV j
  have he : controlOracle (select V)-controlOracle (select U) = select A := by
    ext ⟨b,⟨j,i⟩⟩ ⟨c,⟨l,k⟩⟩
    cases b <;> cases c <;> by_cases hj : j=l <;>
      simp [controlOracle,select,A,Matrix.of_apply,hj]
  rw [taylorQuery,taylorQuery,TensorGate,TensorGate,kronecker_sub_right,he,
    l2_norm_kronecker]
  exact (mul_le_mul (matrix_one_norm_le) (factorialTaylor_select_norm_le A δ hδ hA)
    (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul _)

/-- Replacing the summand oracles by unitary operators within `δ` gives relative vector error at
most `2⁻ᵏ + 3 * s * K * δ` for the same factorial Taylor program. See [BerryEtAl2015Taylor]. -/
theorem factorial_taylor_same_program_oracle_noise :
  ∀ (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (h : J → ℝ) (U V : J → Matrix I I ℂ) (j₀ : J) (t δ : ℝ) (Λ T k : ℕ),
    (∀ j, U j ∈ unitaryGroup I ℂ ∧ (U j).IsHermitian) →
    (∀ j, V j ∈ unitaryGroup I ℂ) → 0 ≤ δ → (∀ j, ‖U j - V j‖ ≤ δ) →
    (∑ j, |h j|) ≤ Λ → |t| ≤ T →
    let s := taylorSegments Λ T
    let K := factorialTaylorCutoff (factorialTaylorPrecision s k)
    let cs := factorialTaylorWord (I:=I) h j₀ t Λ T k
    ∀ ψ : QState I, ‖toEuclidean_fromVec
      (evaluate (taylorQuery V K) cs *ᵥ (taylorFrame j₀ K *ᵥ ψ) -
        taylorFrame j₀ K *ᵥ (hamiltonianEvolution (∑ j, (h j : ℂ) • U j) t *ᵥ ψ))‖ ≤
      ((1/2:ℝ)^k + 3*s*K*δ) * ‖toEuclidean_fromVec ψ‖ := by
  intro J I _ _ _ _ h U V j₀ t δ Λ T k hU hV hδ hUV hΛ hT
  let s := taylorSegments Λ T
  let K := factorialTaylorCutoff (factorialTaylorPrecision s k)
  let cs := factorialTaylorWord (I:=I) h j₀ t Λ T k
  let R := taylorFrame (I:=I) j₀ K
  let OU := taylorQuery U K
  let OV := taylorQuery V K
  obtain ⟨hwf,hq,_,_,_,herr⟩ := factorial_taylor_actual_simulation_and_paid_inverse
    J I h U j₀ t Λ T k hU hΛ hT
  have hOU := taylorQuery_unitary U (fun j => (hU j).1) K
  have hOV := taylorQuery_unitary V hV K
  have hop : ‖evaluate OV cs-evaluate OU cs‖ ≤ (adjointQueryCount cs:ℝ)*δ :=
    evaluate_operator_error_le_queries cs OU OV δ hwf hOU hOV hδ
      (factorialTaylor_query_noise U V K δ hδ hUV)
  (try dsimp only)
  intro ψ
  have hdiff := l2_norm_mulVec_fromVec_le (evaluate OV cs-evaluate OU cs) (R*ᵥψ)
  rw [Matrix.sub_mulVec,isometry_mulVec_norm (taylorFrame_isIsometry j₀ K) ψ] at hdiff
  have hdiff' := hdiff.trans (mul_le_mul_of_nonneg_right hop (norm_nonneg _))
  have hsplit : evaluate OV cs*ᵥ(R*ᵥψ)-R*ᵥ(hamiltonianEvolution (∑ j, (h j:ℂ) • U j) t*ᵥψ) =
      (evaluate OV cs*ᵥ(R*ᵥψ)-evaluate OU cs*ᵥ(R*ᵥψ)) +
      (evaluate OU cs*ᵥ(R*ᵥψ)-R*ᵥ(hamiltonianEvolution (∑ j, (h j:ℂ) • U j) t*ᵥψ)) := by abel
  change ‖toEuclidean_fromVec (evaluate OV cs*ᵥ(R*ᵥψ)-
    R*ᵥ(hamiltonianEvolution (∑ j, (h j:ℂ) • U j) t*ᵥψ))‖ ≤ _
  rw [hsplit]
  have hadd : ∀ a b : QState (TaylorWordLabel J K × (Bool × (J × I))), toEuclidean_fromVec (a+b) =
      toEuclidean_fromVec a + toEuclidean_fromVec b := by intros; rfl
  rw [hadd]
  have hbound := (norm_add_le _ _).trans (add_le_add hdiff' (herr ψ))
  rw [hq] at hbound
  exact hbound.trans_eq (by push_cast; ring)

end Qatlib.Concepts.CoherentSim.FactorialTaylor
