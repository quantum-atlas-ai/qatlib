/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.ResourceBoundsDefs
import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2Value
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.PreparedSearchConsumers
import Qatlib.Concepts.QueryComplexity.AdversarySearch.CountedParityAlgorithm
import Qatlib.Concepts.NativeNumerics.PhaseSynthesis.FinitePhaseGrid
import Qatlib.Foundations.OperatorErrors.OperatorError
import Qatlib.Concepts.SearchStopping.PaidRestart.ActualRestartExpectedReceiptTigh
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.QueryDistanceLowerBound

/-!
# Circuit resource bounds and local allocation laws

Develops local-program composition, allocation-stack invariants, matrix products, and
accumulated gate-error bounds. Balanced fresh-copy and restart programs use peak space at most
one, and `g1` through `g4` collect circuit budgets, query lower bounds, parity complexity, phase
grids, and receipt laws.

The circuit framework is described in [NielsenChuang2010], and the state-conversion bounds use
the framework of [LeeEtAl2011].

## Main statements

* `g1`: Collects exact resource identities for circuit composition, parallel circuits,
  compilation, adjoint and Hamiltonian programs, and several fresh-copy phase-estimation
  constructions, together with their stated channel and error properties.
* `g2`: Collects sufficient conditions for implementation within a resource budget, an exact
  quarter-amplitude amplification example, adversary and state-conversion lower bounds, and
  oracle independence of zero-query circuits.
* `g3`: Collects the tight parity query bound, its linear asymptotic growth, and explicit
  numerical phase-table correctness, covering, precision, and comparison-cost estimates. See
  [BealsEtAl2001].
* `g4`: Collects local-program composition and error bounds, balanced fresh-copy and restart
  space bounds, fresh-copy ledger identities, and the expected paid-restart receipt law.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Foundations.QueryWordCore.HamiltonianQuery

namespace Qatlib.Concepts.SearchStopping.PaidRestart

open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel Qatlib.Concepts.NonNormalSpec.ResolventWord Matrix
open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.L2Operator
set_option warningAsError false

set_option autoImplicit false

/-- Concatenates two local programs by placing the second after the operation list of the first. -/
private def localOpAppend {I : Type} : LocalProgram I → LocalProgram I → LocalProgram I
  | .nil, q => q
  | .op o rest, q => .op o (localOpAppend rest q)

/-- The sum of the allocation sizes `localOpSpace` over all operations in a local program. -/
private def localAllocTotal {I : Type} : LocalProgram I → ℕ
  | .nil => 0
  | .op o rest => localOpSpace o + localAllocTotal rest

/-- The matrix product obtained from a local program by replacing each unitary-operation matrix
`U` with `r U` and ignoring other operations. -/
private noncomputable def localProgramRefMatrix {I : Type} [Fintype I] [DecidableEq I]
    (r : Matrix I I ℂ → Matrix I I ℂ) : LocalProgram I → Matrix I I ℂ
  | .nil => 1
  | .op (.applyU U) rest => localProgramRefMatrix r rest * r U
  | .op _ rest => localProgramRefMatrix r rest

/-- The sum of the matrix-norm errors `‖U - r U‖` over the unitary operations of a local
program. -/
private noncomputable def localProgramErrorSum {I : Type} [Fintype I] [DecidableEq I]
    (r : Matrix I I ℂ → Matrix I I ℂ) : LocalProgram I → ℝ
  | .nil => 0
  | .op (.applyU U) rest => localProgramErrorSum r rest + ‖U - r U‖
  | .op _ rest => localProgramErrorSum r rest

/-- A local program that allocates one unit, applies the partial-swap matrix at angle `θ`, and
discards the allocation. -/
private noncomputable def freshCopyStepProgram (D : ℕ) (θ : ℝ) :
    LocalProgram (Fin D × Fin D) :=
  .op (.alloc 1) (.op (.applyU (partialSwapMatrix D θ)) (.op .discard .nil))

/-- Concatenates one fresh-copy partial-swap step for each angle in the given list. -/
private noncomputable def freshCopyScheduleProgram (D : ℕ) :
    List ℝ → LocalProgram (Fin D × Fin D)
  | [] => .nil
  | θ :: rest => localOpAppend (freshCopyStepProgram D θ) (freshCopyScheduleProgram D rest)

/-- A local restart-round program that allocates one unit, applies `U`, and discards the
allocation. -/
private def restartRoundProgram {I : Type} (U : Matrix I I ℂ) : LocalProgram I :=
  .op (.alloc 1) (.op (.applyU U) (.op .discard .nil))

/-- Repeats the allocate-apply-discard restart round `r` times. -/
private def restartLoopProgram {I : Type} (U : Matrix I I ℂ) : ℕ → LocalProgram I
  | 0 => .nil
  | r + 1 => localOpAppend (restartRoundProgram U) (restartLoopProgram U r)

/-- The predicate requiring every circuit selected by a matrix-indexed program family to be
unitary and to achieve real input-to-target overlap at least `Real.sqrt (1 - ε)` for each
input's workspace Boolean oracle. -/
private def stateConversionFamilySpec {X : Type} [Fintype X] [DecidableEq X] {n R : ℕ}
    (input : X → Fin n → Bool) (ε : ℝ) (ρ σ : X → QState ((Fin n × Bool) × Fin R)) :
    (Matrix ((Fin n × Bool) × Fin R) ((Fin n × Bool) × Fin R) ℂ →
      Circuit ((Fin n × Bool) × Fin R)) → Prop :=
  fun prog => ∀ oracle, IsUnitaryCircuit (prog oracle) ∧
    ∀ x : X, Real.sqrt (1 - ε) ≤ Complex.re
      (Qatlib.Foundations.PureStateMath.Inner (Run (workspaceBitOracle (W := Fin R) (input x)) (prog oracle) (ρ x)) (σ x))

/-- For `0 < ε ≤ 1`, a unitary circuit using `T` queries and achieving the stated overlap on
normalized input and target states bounds `stateConversionSDP` at tolerance `2 * Real.sqrt
(2 * ε)` by `2 * T`. See [LeeEtAl2011]. -/
private theorem stateConversionSDP_lower_bound_of_actual_circuit (X : Type) [Fintype X] [DecidableEq X]
    (n T R : ℕ) (input : X → Fin n → Bool) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ σ : X → QState ((Fin n × Bool) × Fin R))
    (hρ : ∀ x, Normalized (ρ x)) (hσ : ∀ x, Normalized (σ x))
    (C : Circuit ((Fin n × Bool) × Fin R)) (hT : QueryCount C = T) (hC : IsUnitaryCircuit C)
    (hov : ∀ x, Real.sqrt (1 - ε) ≤
      Complex.re (Qatlib.Foundations.PureStateMath.Inner (Run (workspaceBitOracle (W := Fin R) (input x)) C (ρ x)) (σ x))) :
    stateConversionSDP input (2 * Real.sqrt (2 * ε)) (gramStateMatrix ρ) (gramStateMatrix σ)
      ≤ ((2 * T : ℕ) : ℝ≥0∞) := by
  let τ (x : X) := Run (workspaceBitOracle (W := Fin R) (input x)) C (ρ x)
  have hτ (x : X) : Normalized (τ x) :=
    hC.normalized_run (workspaceBitOracle_unitary (input x)) (hρ x)
  have hp : (gramStateMatrix τ).PosSemidef := by
    let V : Matrix ((Fin n × Bool) × Fin R) X ℂ := fun i x => τ x i
    have heq : gramStateMatrix τ = Vᴴ * V := by ext x y; rfl
    rw [heq]
    exact Matrix.posSemidef_conjTranspose_mul_self V
  have hc := gramFilteredCert_mono
    (gramFilteredCert_of_realPart_overlap hε.le hε1 τ σ hτ hσ hov)
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith : ε ≤ 2 * ε))
      (by norm_num : (0 : ℝ) ≤ 2))
  have hd := gram_exact_state_conversion_filteredCert input ρ τ C hT hC hρ (fun _ _ => rfl)
  refine le_trans (iInf_le (fun σ' : {σ' : Matrix X X ℂ // σ'.PosSemidef ∧
      gramFilteredCert (σ' - gramStateMatrix σ)
        (fun _ : Fin 1 => gramFilterAllOnes) (2 * Real.sqrt (2 * ε))} =>
      filteredGamma2 (gramStateMatrix ρ - σ'.1) (gramFilterDelta input))
      ⟨gramStateMatrix τ,hp,hc⟩) ?_
  have h := filteredGamma2_le_of_gramFilteredCert hd
  have heq : ENNReal.ofReal (2 * (T : ℝ)) = ((2 * T : ℕ) : ℝ≥0∞) := by
    rw [show 2 * (T : ℝ) = ((2 * T : ℕ) : ℝ) by push_cast; rfl, ENNReal.ofReal_natCast]
  rwa [heq] at h

/-- Assigning the zero step profile to every gate gives a derived basic-gate cost of zero. -/
private theorem zeroProfile_basicGates {I : Type} [Fintype I] [DecidableEq I]
    (C : Circuit I) : (derive (fun _ => StepProfile.zero) C).basicGates = 0 := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [derive, ih]

/-- Assigning the zero step profile to every gate gives a derived peak-space cost of zero. -/
private theorem zeroProfile_peakSpace {I : Type} [Fintype I] [DecidableEq I]
    (C : Circuit I) : (derive (fun _ => StepProfile.zero) C).peakSpace = 0 := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [derive, ih]

/-- Assigning the zero step profile to every gate gives a derived Hamiltonian-time cost of zero. -/
private theorem zeroProfile_hamiltonianTime {I : Type} [Fintype I] [DecidableEq I]
    (C : Circuit I) : (derive (fun _ => StepProfile.zero) C).hamiltonianTime = 0 := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [derive, ih]

/-- The real-valued function given by natural division `(n + 1) / 2` has resource growth Θ(n). -/
private theorem parity_query_growth_theta :
    IsResourceBigTheta (fun n : ℕ => (((n + 1) / 2 : ℕ) : ℝ)) (fun n : ℕ => (n : ℝ)) := by
  refine ⟨⟨1, 0, by norm_num, ?_⟩, ⟨1 / 2, 0, by norm_num, ?_⟩⟩
  · intro n _
    have h : ((n + 1) / 2 : ℕ) ≤ n := by omega
    have hR : (((n + 1) / 2 : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast h
    simpa using! hR
  · intro n _
    have h : n ≤ 2 * ((n + 1) / 2 : ℕ) := by omega
    have hR : ((n : ℕ) : ℝ) ≤ ((2 * ((n + 1) / 2 : ℕ) : ℕ) : ℝ) := by exact_mod_cast h
    have hE : ((2 * ((n + 1) / 2 : ℕ) : ℕ) : ℝ) = 2 * (((n + 1) / 2 : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hE] at hR
    linarith

/-- For `n ≥ 1`, the specified dyadic phase-grid error is at most `9 / (2 * n)` and the grid
contains at most `4 * n` points. -/
private theorem phase_grid_precision (n : ℕ) (hn : 1 ≤ n) :
    8 / ((2 : ℝ) ^ (Nat.log 2 n + 2)) +
        ((2 : ℝ) ^ (Nat.log 2 n + 2)) * ((2 : ℝ) ⁻¹) ^ (2 * (Nat.log 2 n + 2))
      ≤ (9 / 2 : ℝ) / n ∧
    2 ^ (Nat.log 2 n + 2) ≤ 4 * n := by
  have h1 : (2 : ℕ) ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h2 : n < (2 : ℕ) ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hpowl : ((2 : ℕ) ^ Nat.log 2 n : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
  have hc : ((2 : ℕ) ^ (Nat.log 2 n + 1) : ℝ) = ((2 : ℕ) ^ Nat.log 2 n : ℝ) * 2 := by
    rw [pow_succ]
    push_cast
    ring
  have hnlt : (n : ℝ) < 2 * ((2 : ℕ) ^ Nat.log 2 n : ℝ) := by
    have hlt : ((n : ℕ) : ℝ) < ((2 : ℕ) ^ (Nat.log 2 n + 1) : ℝ) := by exact_mod_cast h2
    rw [hc] at hlt
    linarith
  have hcastA : (2 : ℝ) ^ Nat.log 2 n = ((2 : ℕ) ^ Nat.log 2 n : ℝ) := by
    push_cast
    norm_num
  have hxdef : (2 : ℝ) ^ (Nat.log 2 n + 2) = 4 * ((2 : ℕ) ^ Nat.log 2 n : ℝ) := by
    rw [pow_add, hcastA, pow_two]
    ring
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (Nat.log 2 n + 2) := by positivity
  have hsplit : ((2 : ℝ) ^ (Nat.log 2 n + 2)) * ((2 : ℝ) ⁻¹) ^ (2 * (Nat.log 2 n + 2))
      = ((2 : ℝ) ⁻¹) ^ (Nat.log 2 n + 2) := by
    have hexp2 : ((2 : ℝ) ⁻¹) ^ (2 * (Nat.log 2 n + 2))
        = ((2 : ℝ) ⁻¹) ^ (Nat.log 2 n + 2) * ((2 : ℝ) ⁻¹) ^ (Nat.log 2 n + 2) := by
      rw [show 2 * (Nat.log 2 n + 2) = Nat.log 2 n + 2 + (Nat.log 2 n + 2) from by ring,
        pow_add]
    rw [hexp2, ← mul_assoc, inv_pow,
      mul_inv_cancel₀ (by positivity : (2 : ℝ) ^ (Nat.log 2 n + 2) ≠ 0), one_mul]
  have hLHS : 8 / ((2 : ℝ) ^ (Nat.log 2 n + 2))
      + ((2 : ℝ) ^ (Nat.log 2 n + 2)) * ((2 : ℝ) ⁻¹) ^ (2 * (Nat.log 2 n + 2))
      = 9 / ((2 : ℝ) ^ (Nat.log 2 n + 2)) := by
    rw [hsplit, inv_pow, inv_eq_one_div, ← add_div]
    norm_num
  have hA : (0 : ℝ) < ((2 : ℕ) ^ Nat.log 2 n : ℝ) := by
    exact_mod_cast Nat.pow_pos (by norm_num)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  refine ⟨?_, ?_⟩
  · rw [hLHS, hxdef]
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hA) hnR]
    have h2n : (2 : ℝ) * (n : ℝ) < 4 * ((2 : ℕ) ^ Nat.log 2 n : ℝ) := by linarith
    linarith
  · have hexp : (2 : ℕ) ^ (Nat.log 2 n + 2) = 4 * (2 : ℕ) ^ Nat.log 2 n := by
      rw [pow_add]
      norm_num
      ring
    rw [hexp]
    omega

/-- For fixed `d`, the function `(d + 1) * (Nat.log 2 n + 3)` is resource O((Nat.log 2 n + 2)³). -/
private theorem comparison_word_bit_growth (d : ℕ) : IsResourceBigO
    (fun n : ℕ => ((d : ℝ) + 1) * ((Nat.log 2 n : ℝ) + 3))
    (fun n : ℕ => (((Nat.log 2 n + 2) ^ 3 : ℕ) : ℝ)) := by
  refine ⟨(d : ℝ) + 1, 0, by positivity, ?_⟩
  intro n _
  have hm : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
  have hkey : ((Nat.log 2 n : ℝ) + 3) ≤ (((Nat.log 2 n + 2) ^ 3 : ℕ) : ℝ) := by
    push_cast
    have hsq : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) ^ 2 := sq_nonneg _
    have h4 : (4 : ℝ) ≤ ((Nat.log 2 n : ℝ) + 2) ^ 2 := by nlinarith [hsq, hm]
    have h5 : (4 : ℝ) * ((Nat.log 2 n : ℝ) + 2) ≤ ((Nat.log 2 n : ℝ) + 2) ^ 3 := by
      rw [show ((Nat.log 2 n : ℝ) + 2) ^ 3
            = ((Nat.log 2 n : ℝ) + 2) ^ 2 * ((Nat.log 2 n : ℝ) + 2) from by ring]
      exact mul_le_mul_of_nonneg_right h4 (by linarith)
    linarith
  exact mul_le_mul_of_nonneg_left hkey (by positivity)

/-- The sum of the tail of a list of natural numbers is at most the sum of the whole list. -/
private theorem list_tail_sum_le (t : List ℕ) : t.tail.sum ≤ t.sum := by
  cases t with
  | nil => rfl
  | cons a t =>
    simp only [List.tail, List.sum_cons]
    omega

/-- Running the concatenation of two local programs on an allocation state equals running the
first and then the second. -/
private theorem localProgramState_append {I : Type} (p q : LocalProgram I)
    (st : LocalAllocState) :
    localProgramState (localOpAppend p q) st = localProgramState q (localProgramState p st) := by
  induction p generalizing st with
  | nil => rfl
  | op o rest ih => exact ih (localOpStep o st)

/-- Executing a local program cannot decrease the recorded peak allocation. -/
private theorem localProgramState_peak_ge {I : Type} (p : LocalProgram I)
    (st : LocalAllocState) : st.peak ≤ (localProgramState p st).peak := by
  induction p generalizing st with
  | nil => exact le_rfl
  | op o rest ih =>
    cases o with
    | alloc w =>
      exact (Nat.le_max_left st.peak (w + st.allocs.sum)).trans
        (ih ⟨w :: st.allocs, max st.peak (w + st.allocs.sum)⟩)
    | applyU => exact ih st
    | release => exact ih ⟨st.allocs.tail, st.peak⟩
    | reset => exact ih ⟨st.allocs.tail, st.peak⟩
    | discard => exact ih ⟨st.allocs.tail, st.peak⟩

/-- For a fixed initial allocation list, the final allocation list is independent of the initial
recorded peak. -/
private theorem localProgramState_allocs_irrelevant {I : Type} (p : LocalProgram I) :
    ∀ (l : List ℕ) (a b : ℕ),
      (localProgramState p ⟨l, a⟩).allocs = (localProgramState p ⟨l, b⟩).allocs := by
  induction p with
  | nil => intro _ _ _; rfl
  | op o rest ih =>
    intro l a b
    cases o <;> exact ih _ _ _

/-- Starting with recorded peak `max a b` gives final peak `max a` of the final peak obtained by
starting with `b`. -/
private theorem localProgramState_peak_max {I : Type} (p : LocalProgram I) :
    ∀ (l : List ℕ) (a b : ℕ),
      (localProgramState p ⟨l, max a b⟩).peak = max a (localProgramState p ⟨l, b⟩).peak := by
  induction p with
  | nil => intro _ _ _; rfl
  | op o rest ih =>
    intro l a b
    cases o with
    | applyU => exact ih l a b
    | release => exact ih l.tail a b
    | reset => exact ih l.tail a b
    | discard => exact ih l.tail a b
    | alloc w =>
      simp only [localProgramState]
      have hgoal : localOpStep (I := I) (LocalOp.alloc w) ⟨l, max a b⟩
          = ⟨w :: l, max a (max b (w + l.sum))⟩ := by
        simp only [localOpStep, Nat.max_assoc]
      rw [hgoal]
      exact ih (w :: l) a (max b (w + l.sum))

/-- Starting with an empty allocation list and recorded peak `a` gives final peak `max a
(localPeakSpace p)`. -/
private theorem localProgramState_peak_empty {I : Type} (p : LocalProgram I) (a : ℕ) :
    (localProgramState p ⟨[], a⟩).peak = max a (localPeakSpace p) := by
  have h := localProgramState_peak_max p [] a 0
  rw [Nat.max_zero] at h
  exact h

/-- Appending a fixed allocation tail to the initial stack increases the final peak by at most
the tail's total allocation, subject to the initial recorded peak. -/
private theorem localProgramState_frame {I : Type} (p : LocalProgram I) :
    ∀ (l t : List ℕ) (a b : ℕ),
      (localProgramState p ⟨l ++ t, a⟩).peak
        ≤ max a (t.sum + (localProgramState p ⟨l, b⟩).peak) := by
  induction p with
  | nil => intro _ _ a _; exact Nat.le_max_left a _
  | op o rest ih =>
    intro l t a b
    cases o with
    | applyU => exact ih l t a b
    | release =>
      cases l with
      | nil =>
        have h := ih [] t.tail a b
        rw [List.nil_append] at h
        have hle := list_tail_sum_le t
        show (localProgramState rest ⟨t.tail, a⟩).peak
            ≤ max a (t.sum + (localProgramState rest ⟨[], b⟩).peak)
        omega
      | cons x l => exact ih l t a b
    | reset =>
      cases l with
      | nil =>
        have h := ih [] t.tail a b
        rw [List.nil_append] at h
        have hle := list_tail_sum_le t
        show (localProgramState rest ⟨t.tail, a⟩).peak
            ≤ max a (t.sum + (localProgramState rest ⟨[], b⟩).peak)
        omega
      | cons x l => exact ih l t a b
    | discard =>
      cases l with
      | nil =>
        have h := ih [] t.tail a b
        rw [List.nil_append] at h
        have hle := list_tail_sum_le t
        show (localProgramState rest ⟨t.tail, a⟩).peak
            ≤ max a (t.sum + (localProgramState rest ⟨[], b⟩).peak)
        omega
      | cons x l => exact ih l t a b
    | alloc w =>
      have h := ih (w :: l) t (max a (w + (l ++ t).sum)) (max b (w + l.sum))
      rw [List.sum_append, List.cons_append] at h
      have hge : w + l.sum ≤ (localProgramState rest ⟨w :: l, max b (w + l.sum)⟩).peak :=
        (Nat.le_max_right b (w + l.sum)).trans
          (localProgramState_peak_ge rest ⟨w :: l, max b (w + l.sum)⟩)
      show (localProgramState rest ⟨w :: (l ++ t), max a (w + (l ++ t).sum)⟩).peak
          ≤ max a (t.sum + (localProgramState rest ⟨w :: l, max b (w + l.sum)⟩).peak)
      rw [List.sum_append]
      omega

/-- The final peak is at most the maximum of the initial peak and the initial total allocation
plus `localPeakSpace p`. -/
private theorem localProgramState_peak_le {I : Type} (p : LocalProgram I)
    (l : List ℕ) (a : ℕ) :
    (localProgramState p ⟨l, a⟩).peak ≤ max a (l.sum + localPeakSpace p) := by
  have h := localProgramState_frame p [] l a 0
  rw [List.nil_append] at h
  exact h

/-- If the initial allocation total is bounded by the recorded peak, this invariant remains true
after executing a local program. -/
private theorem localProgramState_sum_le_peak {I : Type} (p : LocalProgram I) :
    ∀ st : LocalAllocState, st.allocs.sum ≤ st.peak →
      (localProgramState p st).allocs.sum ≤ (localProgramState p st).peak := by
  induction p with
  | nil => intro st h; exact h
  | op o rest ih =>
    intro st h
    cases o with
    | alloc w =>
      refine ih ⟨w :: st.allocs, max st.peak (w + st.allocs.sum)⟩ ?_
      show w + st.allocs.sum ≤ max st.peak (w + st.allocs.sum)
      exact Nat.le_max_right _ _
    | applyU => exact ih st h
    | release =>
      refine ih ⟨st.allocs.tail, st.peak⟩ ?_
      exact (list_tail_sum_le st.allocs).trans h
    | reset =>
      refine ih ⟨st.allocs.tail, st.peak⟩ ?_
      exact (list_tail_sum_le st.allocs).trans h
    | discard =>
      refine ih ⟨st.allocs.tail, st.peak⟩ ?_
      exact (list_tail_sum_le st.allocs).trans h

/-- The peak space of a concatenated local program is at most the sum of the component peak
spaces. -/
private theorem localPeakSpace_append_le {I : Type} (p q : LocalProgram I) :
    localPeakSpace (localOpAppend p q) ≤ localPeakSpace p + localPeakSpace q := by
  have hq' : localPeakSpace q = (localProgramState q ⟨[], 0⟩).peak := rfl
  have hp' : localPeakSpace p = (localProgramState p ⟨[], 0⟩).peak := rfl
  have happ : localProgramState (localOpAppend p q) ⟨[], 0⟩
      = localProgramState q (localProgramState p ⟨[], 0⟩) :=
    localProgramState_append p q ⟨[], 0⟩
  have hle := localProgramState_peak_le q (localProgramState p ⟨[], 0⟩).allocs
    (localProgramState p ⟨[], 0⟩).peak
  rw [show (⟨(localProgramState p ⟨[], 0⟩).allocs, (localProgramState p ⟨[], 0⟩).peak⟩ :
      LocalAllocState) = localProgramState p ⟨[], 0⟩ from rfl] at hle
  rw [hq'] at hle
  have hsum := localProgramState_sum_le_peak p ⟨[], 0⟩ (by simp)
  rw [show localPeakSpace (localOpAppend p q)
      = (localProgramState (localOpAppend p q) ⟨[], 0⟩).peak from rfl,
    hp', hq', happ]
  omega

/-- Concatenating balanced local programs preserves balance and gives peak space equal to the
maximum of their peak spaces. -/
private theorem localOpAppend_balanced {I : Type} (p q : LocalProgram I)
    (hp : localProgramBalanced p) (hq : localProgramBalanced q) :
    localProgramBalanced (localOpAppend p q) ∧
      localPeakSpace (localOpAppend p q) = max (localPeakSpace p) (localPeakSpace q) := by
  have happ : localProgramState (localOpAppend p q) ⟨[], 0⟩
      = localProgramState q (localProgramState p ⟨[], 0⟩) :=
    localProgramState_append p q ⟨[], 0⟩
  have hst : localProgramState p ⟨[], 0⟩
      = ⟨[], (localProgramState p ⟨[], 0⟩).peak⟩ := by
    have heta : localProgramState p ⟨[], 0⟩
        = ⟨(localProgramState p ⟨[], 0⟩).allocs, (localProgramState p ⟨[], 0⟩).peak⟩ := rfl
    rw [heta, hp]
  constructor
  · show (localProgramState (localOpAppend p q) ⟨[], 0⟩).allocs = []
    rw [happ, hst]
    exact (localProgramState_allocs_irrelevant q [] _ 0).trans hq
  · show (localProgramState (localOpAppend p q) ⟨[], 0⟩).peak
        = max (localProgramState p ⟨[], 0⟩).peak (localProgramState q ⟨[], 0⟩).peak
    rw [happ, hst, localProgramState_peak_empty q ((localProgramState p ⟨[], 0⟩).peak)]
    rfl

/-- The gate list of concatenated local programs is the concatenation of their gate lists. -/
private theorem localProgramGates_append {I : Type} (p q : LocalProgram I) :
    localProgramGates (localOpAppend p q) = localProgramGates p ++ localProgramGates q := by
  induction p with
  | nil => rfl
  | op o rest ih =>
    cases o with
    | applyU U =>
      show U :: localProgramGates (localOpAppend rest q)
          = (U :: localProgramGates rest) ++ localProgramGates q
      rw [ih]
      rfl
    | alloc _ => exact ih
    | release => exact ih
    | reset => exact ih
    | discard => exact ih

/-- The matrix of concatenated local programs is the matrix of the second multiplied by that of
the first. -/
private theorem localProgramMatrix_append {I : Type} [Fintype I] [DecidableEq I]
    (p q : LocalProgram I) :
    localProgramMatrix (localOpAppend p q) = localProgramMatrix q * localProgramMatrix p := by
  induction p with
  | nil =>
    show localProgramMatrix q = localProgramMatrix q * (1 : Matrix I I ℂ)
    rw [Matrix.mul_one]
  | op o rest ih =>
    cases o with
    | applyU U =>
      show localProgramMatrix (localOpAppend rest q) * U
          = localProgramMatrix q * (localProgramMatrix rest * U)
      rw [ih, Matrix.mul_assoc]
    | alloc _ => exact ih
    | release => exact ih
    | reset => exact ih
    | discard => exact ih

/-- The matrix of a local program is the product of its gate matrices in reverse list order. -/
private theorem localProgramMatrix_eq_prod {I : Type} [Fintype I] [DecidableEq I]
    (p : LocalProgram I) :
    localProgramMatrix p = (localProgramGates p).reverse.prod := by
  induction p with
  | nil => rfl
  | op o rest ih =>
    cases o with
    | applyU U =>
      show localProgramMatrix rest * U = (U :: localProgramGates rest).reverse.prod
      rw [List.reverse_cons, List.prod_append, List.prod_singleton, ih]
    | alloc _ => exact ih
    | release => exact ih
    | reset => exact ih
    | discard => exact ih

/-- The reference matrix is the reverse-order product of the program's gate matrices after
applying `r` to each gate. -/
private theorem localProgramRefMatrix_eq_prod {I : Type} [Fintype I] [DecidableEq I]
    (r : Matrix I I ℂ → Matrix I I ℂ) (p : LocalProgram I) :
    localProgramRefMatrix r p = ((localProgramGates p).map r).reverse.prod := by
  induction p with
  | nil => rfl
  | op o rest ih =>
    cases o with
    | applyU U =>
      show localProgramRefMatrix r rest * r U
          = (r U :: (localProgramGates rest).map r).reverse.prod
      rw [List.reverse_cons, List.prod_append, List.prod_singleton, ih]
    | alloc _ => exact ih
    | release => exact ih
    | reset => exact ih
    | discard => exact ih

/-- The reference-error sum equals the sum of `‖U - r U‖` over the extracted gate list. -/
private theorem localProgramErrorSum_eq {I : Type} [Fintype I] [DecidableEq I]
    (r : Matrix I I ℂ → Matrix I I ℂ) (p : LocalProgram I) :
    localProgramErrorSum r p = ((localProgramGates p).map (fun U => ‖U - r U‖)).sum := by
  induction p with
  | nil => rfl
  | op o rest ih =>
    cases o with
    | applyU U =>
      show localProgramErrorSum r rest + ‖U - r U‖
          = ‖U - r U‖ + ((localProgramGates rest).map (fun U => ‖U - r U‖)).sum
      rw [ih]
      exact add_comm _ _
    | alloc _ => exact ih
    | release => exact ih
    | reset => exact ih
    | discard => exact ih

/-- When every program gate and its reference replacement are unitary, the matrix error of the
full program is at most the sum of the individual gate errors. -/
private theorem localProgram_refError_le {I : Type} [Fintype I] [DecidableEq I]
    (p : LocalProgram I) (r : Matrix I I ℂ → Matrix I I ℂ)
    (hU : ∀ U ∈ localProgramGates p, U ∈ Matrix.unitaryGroup I ℂ
      ∧ r U ∈ Matrix.unitaryGroup I ℂ) :
    ‖localProgramMatrix p - localProgramRefMatrix r p‖ ≤ localProgramErrorSum r p := by
  have hmain := l2_norm_list_prod_sub_prod_le (I := I)
    ((localProgramGates p).reverse.map (fun U => (U, r U)))
    (fun pr hpr => by
      obtain ⟨U, hUmem, rfl⟩ := List.mem_map.mp hpr
      have hU' : U ∈ localProgramGates p := List.mem_reverse.mp hUmem
      exact ⟨l2_norm_unitary_le_one (hU U hU').1, l2_norm_unitary_le_one (hU U hU').2⟩)
  have h1 : (((localProgramGates p).reverse.map (fun U => (U, r U))).map Prod.fst).prod
      = (localProgramGates p).reverse.prod := by
    simp only [List.map_map, Function.comp_def]
    exact congrArg List.prod (List.map_id _)
  have h2 : (((localProgramGates p).reverse.map (fun U => (U, r U))).map Prod.snd).prod
      = ((localProgramGates p).map r).reverse.prod := by
    simp only [List.map_map, Function.comp_def, List.map_reverse]
  have h3 : ((((localProgramGates p).reverse.map (fun U => (U, r U))).map
      (fun pr => ‖pr.1 - pr.2‖)).sum)
      = ((localProgramGates p).map (fun U => ‖U - r U‖)).sum := by
    simp only [List.map_map, Function.comp_def]
    rw [List.map_reverse, List.sum_reverse]
  rw [h1, h2, h3] at hmain
  rw [localProgramMatrix_eq_prod, localProgramRefMatrix_eq_prod,
    localProgramErrorSum_eq]
  exact hmain

/-- A fresh-copy partial-swap step is balanced and has peak space exactly one. -/
private theorem freshCopyStepProgram_balanced (D : ℕ) (θ : ℝ) :
    localProgramBalanced (freshCopyStepProgram D θ) ∧
      localPeakSpace (freshCopyStepProgram D θ) = 1 :=
  ⟨rfl, rfl⟩

/-- Every fresh-copy schedule program is balanced and has peak space at most one. -/
private theorem freshCopyScheduleProgram_bal (D : ℕ) (angles : List ℝ) :
    localProgramBalanced (freshCopyScheduleProgram D angles) ∧
      localPeakSpace (freshCopyScheduleProgram D angles) ≤ 1 := by
  induction angles with
  | nil => exact ⟨rfl, Nat.zero_le 1⟩
  | cons θ rest ih =>
    have h := localOpAppend_balanced (freshCopyStepProgram D θ)
      (freshCopyScheduleProgram D rest) (freshCopyStepProgram_balanced D θ).1 ih.1
    have h1 : localPeakSpace (freshCopyStepProgram D θ) = 1 :=
      (freshCopyStepProgram_balanced D θ).2
    refine ⟨h.1, ?_⟩
    show localPeakSpace (localOpAppend (freshCopyStepProgram D θ)
        (freshCopyScheduleProgram D rest)) ≤ 1
    rw [h.2]
    omega

/-- The gate list of a fresh-copy schedule consists of the partial-swap matrices at its listed
angles. -/
private theorem freshCopyScheduleProgram_gates (D : ℕ) (angles : List ℝ) :
    localProgramGates (freshCopyScheduleProgram D angles)
      = angles.map (fun θ => partialSwapMatrix D θ) := by
  induction angles with
  | nil => rfl
  | cons θ rest ih =>
    rw [freshCopyScheduleProgram, localProgramGates_append, ih]
    rfl

/-- The matrix of a fresh-copy schedule is the left fold that successively multiplies its
partial-swap matrices onto the identity. -/
private theorem freshCopyScheduleProgram_matrix (D : ℕ) (angles : List ℝ) :
    localProgramMatrix (freshCopyScheduleProgram D angles)
      = angles.foldl (fun M θ => partialSwapMatrix D θ * M)
          (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) := by
  have key : ∀ (M : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) (angles : List ℝ),
      angles.foldl (fun M θ => partialSwapMatrix D θ * M) M
        = localProgramMatrix (freshCopyScheduleProgram D angles) * M := by
    intro M angles
    induction angles generalizing M with
    | nil => exact (Matrix.one_mul _).symm
    | cons θ rest ih =>
      rw [freshCopyScheduleProgram, localProgramMatrix_append]
      have hstep : localProgramMatrix (freshCopyStepProgram D θ)
          = partialSwapMatrix D θ := by
        show (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) * partialSwapMatrix D θ = _
        exact Matrix.one_mul _
      rw [hstep, List.foldl_cons, ih (partialSwapMatrix D θ * M)]
      exact (Matrix.mul_assoc _ _ _).symm
  have h := key 1 angles
  rw [Matrix.mul_one] at h
  exact h.symm

/-- A single allocate-apply-discard restart round is balanced and has peak space exactly one. -/
private theorem restartRoundProgram_balanced {I : Type} (U : Matrix I I ℂ) :
    localProgramBalanced (restartRoundProgram U) ∧
      localPeakSpace (restartRoundProgram U) = 1 :=
  ⟨rfl, rfl⟩

/-- Every finite repetition of the restart-round program is balanced and has peak space at most
one. -/
private theorem restartLoopProgram_bal {I : Type} (U : Matrix I I ℂ) (r : ℕ) :
    localProgramBalanced (restartLoopProgram U r) ∧
      localPeakSpace (restartLoopProgram U r) ≤ 1 := by
  induction r with
  | zero => exact ⟨rfl, Nat.zero_le 1⟩
  | succ r ih =>
    rw [restartLoopProgram]
    have h := localOpAppend_balanced (restartRoundProgram U) (restartLoopProgram U r)
      (restartRoundProgram_balanced U).1 ih.1
    have h1 : localPeakSpace (restartRoundProgram U) = 1 :=
      (restartRoundProgram_balanced U).2
    refine ⟨h.1, ?_⟩
    rw [h.2]
    omega

/-- The peak space of a local program is at most the sum of its allocation sizes. -/
private theorem localPeakSpace_le_allocTotal {I : Type} (p : LocalProgram I) :
    localPeakSpace p ≤ localAllocTotal p := by
  induction p with
  | nil => rfl
  | op o rest ih =>
    cases o with
    | alloc w =>
      show (localProgramState rest ⟨[w], max 0 (w + 0)⟩).peak
          ≤ w + localAllocTotal rest
      have h := localProgramState_peak_le rest [w] (max 0 (w + 0))
      simp only [List.sum_cons, List.sum_nil] at h
      omega
    | applyU _ =>
      show localPeakSpace rest ≤ localAllocTotal (LocalProgram.op (LocalOp.applyU _) rest)
      rw [show localAllocTotal (LocalProgram.op (LocalOp.applyU _) rest) = localAllocTotal rest
          from by simp [localAllocTotal, localOpSpace]]
      exact ih
    | release =>
      show localPeakSpace rest ≤ localAllocTotal (LocalProgram.op LocalOp.release rest)
      rw [show localAllocTotal (LocalProgram.op LocalOp.release rest) = localAllocTotal rest
          from by simp [localAllocTotal, localOpSpace]]
      exact ih
    | reset =>
      show localPeakSpace rest ≤ localAllocTotal (LocalProgram.op LocalOp.reset rest)
      rw [show localAllocTotal (LocalProgram.op LocalOp.reset rest) = localAllocTotal rest
          from by simp [localAllocTotal, localOpSpace]]
      exact ih
    | discard =>
      show localPeakSpace rest ≤ localAllocTotal (LocalProgram.op LocalOp.discard rest)
      rw [show localAllocTotal (LocalProgram.op LocalOp.discard rest) = localAllocTotal rest
          from by simp [localAllocTotal, localOpSpace]]
      exact ih

/-- Collects exact resource identities for circuit composition, parallel circuits, compilation,
adjoint and Hamiltonian programs, and several fresh-copy phase-estimation constructions,
together with their stated channel and error properties. -/
theorem g1 :
  (∀ (I : Type) [Fintype I] [DecidableEq I] (κ : Matrix I I ℂ → StepProfile)
      (C D : Circuit I) (k : ℕ),
    derive κ (C ++ D) = derive κ C + derive κ D ∧
      derive κ (RepeatCircuit C k) = repeatCost (derive κ C) k ∧
      (derive κ C).queries = QueryCount C ∧ (derive κ C).macroGates = GateCount C ∧
      (derive κ C).depth = Size C ∧
      (∀ (J : Type) [Fintype J] [DecidableEq J] (κI : Matrix I I ℂ → StepProfile)
          (κJ : Matrix J J ℂ → StepProfile) (L : ParCircuit I J),
        (derivePar κI κJ L).queries = QueryCount (parToCircuit L) ∧
          (derivePar κI κJ L).depth = max (Size (parLeft L)) (Size (parRight L)) ∧
          (derivePar κI κJ L).peakSpace
            ≤ (derive κI (parLeft L)).peakSpace + (derive κJ (parRight L)).peakSpace) ∧
      (∀ c : GateCompiler I, ∀ C' : Circuit I,
        (derive c.profile C').basicGates = GateCount (compileCircuit c C')) ∧
      (∀ (U : Matrix I I ℂ) (c : GateCompilation U) (ψ : QState I),
        ApplyGate U ψ ≠ ψ → 0 < GateCount c.circuit)) ∧
  (∀ (H : Type) (κg : Matrix H H ℂ → StepProfile) (W : List (AdjointStep H)),
    (adjointWordResourceCost κg W).queries = adjointQueryCount W ∧
      (adjointWordResourceCost κg W).macroGates = adjointGateCount W) ∧
  (∀ (I : Type) (κg : Matrix I I ℂ → StepProfile) (P : List (HamiltonianQueryStep I)),
    (hamiltonianProgramResourceCost κg P).queries = HamiltonianQueryCount P ∧
      ∀ _hκ : ∀ U, (κg U).evolve = 0,
        (hamiltonianProgramResourceCost κg P).hamiltonianTime
          = ENNReal.ofReal (HamiltonianEvolutionTime P)) ∧
  (∀ (I : Type) (n : ℕ) (C : Circuit I),
    copyQPELedgerAdapter n C = FreshCopyLedger.ofProd (copyQPEProgramResources n C) ∧
      copyQPEProgramResources n C =
        (QueryCount C * n, QueryCount C * n, QueryCount C * n, 0)) ∧
  (∀ (D M n : ℕ), 2 ≤ M → 0 < n →
    copyQPEResources D M n = ((M - 1) * n, (M - 1) * n, (M - 1) * n, 0) ∧
      copyQPEFixedMacros D M = 2 * (M - 1) + 2) ∧
  (∀ (I : Type) (n s : ℕ) (C : Circuit I),
    localCopyQPELedgerAdapter n s C
      = FreshCopyLedger.ofProd (localCopyQPEProgramResources n s C) ∧
      localCopyQPEProgramResources n s C =
        (QueryCount C * s * (36 * n + 7), QueryCount C * s, QueryCount C * s, 0)) ∧
  (∀ (n : ℕ) (ρ : Operator (2 ^ n)) (t : ℝ) (s : ℕ),
      localCopyRunMap n ρ t s = controlledCopyRunMap ρ t s) ∧
  (∀ (n M s : ℕ) (ρ : Operator (2 ^ n)), 2 ≤ M → 0 < s →
      localCopyQPEOutput n M s ρ = copyQPEOutput (2 ^ n) M s ρ ∧
      localCopyQPEResources n M s =
        ((M - 1) * s * (36 * n + 7), (M - 1) * s, (M - 1) * s, 0) ∧
      copyQPEFixedMacros (2 ^ n) M = 2 * (M - 1) + 2) ∧
  (∀ (I : Type) (n b : ℕ) (C : Circuit I),
    numericCopyLedgerAdapter n b C = FreshCopyLedger.ofProd (numericCopyResources n b C) ∧
      numericCopyResources n b C =
        (QueryCount C * 2 ^ b * (36 * n + 4), QueryCount C * 2 ^ b, QueryCount C * 2 ^ b, 0)) ∧
  (∀ (n M b k : ℕ) (rho : Operator (2 ^ n)) (hrho : IsDensityOperator rho),
      ∀ X : Matrix (Fin M × (Bool × Fin (2 ^ n))) (Fin M × (Bool × Fin (2 ^ n))) ℂ,
      numericCopyQPEQuery n M b k rho X = numericChannelQuery (2 ^ n) M
          (copyChannelPower (controlledCopyChannel rho hrho
            (copyPhaseEffectiveAngle b k)) (2 ^ b)) X ∧
        localCopyQPEQuery n M (2 ^ b) rho X = numericChannelQuery (2 ^ n) M
          (copyChannelPower (controlledCopyChannel rho hrho
            (Real.pi / (2 ^ b : ℕ))) (2 ^ b)) X) ∧
  (∀ (n M b : ℕ), 2 ≤ M →
      numericCopyResources n b (countedPhaseCircuit (I := Fin (2 ^ n)) M) =
        ((M - 1) * 2 ^ b * (36 * n + 4), (M - 1) * 2 ^ b, (M - 1) * 2 ^ b, 0)) ∧
  (∀ (D M n : ℕ), 0 < M →
    twoSpeciesLedgerAdapter M n = FreshCopyLedger.ofProd (twoSpeciesQPEResources M n) ∧
      twoSpeciesQPEResources M n
        = copyQPEProgramResources (2 * n) (countedPhaseCircuit (I := Fin D) M)) ∧
  (∀ (D M n : ℕ) (ρ σ χ : Operator D), 2 ≤ M → 0 < n → IsDensityOperator ρ →
      IsDensityOperator σ → IsDensityOperator χ →
      (twoSpeciesQPEOutput D M n ρ σ χ).PosSemidef ∧
        Matrix.trace (twoSpeciesQPEOutput D M n ρ σ χ) = 1 ∧
        Matrix.traceNorm (twoSpeciesQPEOutput D M n ρ σ χ
          - twoSpeciesQPEIdealOutput D M ρ σ χ)
          ≤ 32 * (M - 1 : ℕ) * Real.pi ^ 2 / (n : ℝ)) ∧
  (∀ (D : ℕ) (angles : List ℝ),
    freshCopyCompositionLedgerAdapter D angles
      = FreshCopyLedger.ofProd (freshCopyResourceCounts D angles) ∧
      freshCopyResourceCounts D angles = (angles.length, angles.length, angles.length, 0)) ∧
  (∀ (D : ℕ) (ρ σ : Operator D) (xs ys : List ℝ),
    freshCopyRun ρ (xs ++ ys) σ = freshCopyRun ρ ys (freshCopyRun ρ xs σ) ∧
      freshCopyResourceCounts D (xs ++ ys) =
        (xs.length + ys.length, xs.length + ys.length, xs.length + ys.length, 0) ∧
      freshCopyResourceCounts D xs = (xs.length, xs.length, xs.length, 0))
  :=
  ⟨fun I _ _ κ C D k =>
    ⟨derive_append κ C D, derive_repeatCircuit κ C k, derive_queries κ C,
      derive_macroGates κ C, derive_depth κ C,
      fun J _ _ κI κJ L =>
        ⟨derivePar_queries κI κJ L, depth_par_eq_max κI κJ L,
          peakSpace_par_le_add κI κJ L⟩,
      fun c C' => c.profile_basicGates_eq C',
      fun U c ψ hψ => c.gateCount_pos_of_changes_state hψ⟩,
    fun H κg W =>
      ⟨adjointWordResourceCost_queries κg W, adjointWordResourceCost_macroGates κg W⟩,
    fun I κg P =>
      ⟨hamiltonianProgramResourceCost_queries κg P,
        fun _hκ => hamiltonianProgramResourceCost_hamiltonianTime κg P _hκ⟩,
    fun I n C => ⟨rfl, copyQPEProgramResources_eq n C⟩,
    fun D M n hM hn =>
      ⟨copy_qpe_same_path_fresh_resource_counts D M n hM hn,
        copyQPEFixedMacros_eq D M (by omega)⟩,
    fun I n s C => ⟨rfl, localCopyQPEProgramResources_eq n s C⟩,
    fun n ρ t s => localCopyRunMap_eq n ρ t s,
    fun n M s ρ hM hs => local_copy_qpe_same_program_output_and_resources n M s ρ hM hs,
    fun I n b C => ⟨rfl, numericCopyResources_eq n b C⟩,
    fun n M b k rho hrho X =>
      ⟨numericCopyQPEQuery_channel n M b k rho hrho X,
        localCopyQPEQuery_channel n M b rho hrho X⟩,
    fun n M b hM => by
      have h := counted_offgrid_qpe_clean_flag M (by omega) (1 : Operator (2 ^ n))
        (0 : QState (Fin (2 ^ n)))
      rw [numericCopyResources_eq n b (countedPhaseCircuit (I := Fin (2 ^ n)) M), h.2.1],
    fun D M n hM => ⟨rfl, twoSpeciesQPEResources_same_path D M n hM⟩,
    fun D M n ρ σ χ hM hn hρ hσ hχ =>
      two_species_qpe_actual_program_state_error D M n hM hn ρ σ χ hρ hσ hχ,
    fun D angles => ⟨rfl, freshCopyResourceCounts_eq D angles⟩,
    fun D ρ σ xs ys => fresh_copy_schedule_composition_cost ρ σ xs ys⟩

/-- Collects sufficient conditions for implementation within a resource budget, an exact
quarter-amplitude amplification example, adversary and state-conversion lower bounds, and
oracle independence of zero-query circuits. -/
theorem g2 :
  (∀ (I : Type) [Fintype I] [DecidableEq I] (κ : Matrix I I ℂ → StepProfile)
      (oracle : Matrix I I ℂ) (C : Circuit I) (target : QState I → QState I)
      (ε : ℝ) (B : ResourceCost),
    (∀ ψ, Normalized ψ → ‖Run oracle C ψ - target ψ‖ ≤ ε) → IsUnitaryCircuit C →
    QueryCount C ≤ B.queries → GateCount C ≤ B.macroGates → Size C ≤ B.depth →
    (derive κ C).basicGates ≤ B.basicGates → (derive κ C).peakSpace ≤ B.peakSpace →
    (derive κ C).hamiltonianTime ≤ B.hamiltonianTime →
    (derive κ C).classicalBits ≤ B.classicalBits →
    ImplementsWithBudget κ oracle C target ε B) ∧
  (∀ ζ : ℂ, ‖ζ‖ = 1 →
    (preparedQuarterA ζ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      MeasureProb (preparedAAState (preparedQuarterA ζ) (0 : Fin 2))
          ({1} : Finset (Fin 2)) = 1 / 4 ∧
      Run (preparedMark ({1} : Finset (Fin 2))) (preparedAACircuit (preparedQuarterA ζ) 0 1)
          (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)) = ζ • Qatlib.Foundations.PureStateMath.Ket (1 : Fin 2) ∧
      QueryCount (preparedAACircuit (preparedQuarterA ζ) 0 1) = 1 ∧
      GateCount (preparedAACircuit (preparedQuarterA ζ) 0 1) = 4) ∧
    ImplementsWithBudget (fun _ => StepProfile.zero)
      (preparedMark ({1} : Finset (Fin 2))) (preparedAACircuit (preparedQuarterA ζ) 0 1)
      (fun ψ => Run (preparedMark ({1} : Finset (Fin 2)))
        (preparedAACircuit (preparedQuarterA ζ) 0 1) ψ) 0 ⟨1, 4, 0, 5, 0, 0, 0⟩) ∧
  ((∀ (X : Type) [Fintype X] [DecidableEq X] (E : Type) [Fintype E] [DecidableEq E]
      (n : ℕ) (input : X → Fin n → Bool) (f : X → E) (Γ : Matrix X X ℂ),
    (∀ x y, f x = f y → Γ x y = 0) → (∀ j, ‖gramFilterDelta input j ⊙ Γ‖ ≤ 1) →
    ENNReal.ofReal ‖Γ‖
        ≤ filteredGamma2 (gramFunctionEvaluationMatrix f) (gramFilterDelta input)) ∧
    (∀ (X : Type) [Fintype X] [DecidableEq X] (n R : ℕ) (input : X → Fin n → Bool)
        (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ (ρ σ : X → QState ((Fin n × Bool) × Fin R)),
        (∀ x, Normalized (ρ x)) → (∀ x, Normalized (σ x)) →
        QueryLowerBound (stateConversionFamilySpec input ε ρ σ)
          (Nat.ceil ((stateConversionSDP input (2 * Real.sqrt (2 * ε))
            (gramStateMatrix ρ) (gramStateMatrix σ)).toReal / 2)))) ∧
  (∀ (C : Circuit Bool) (ψ : QState Bool), QueryCount C = 0 →
    Run (1 : Matrix Bool Bool ℂ) C ψ = Run PauliX C ψ ∧
      ∀ b : Bool,
        BornProb (Run (1 : Matrix Bool Bool ℂ) C ψ) b = BornProb (Run PauliX C ψ) b)
  := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro I _ _ κ oracle C target ε B hsem hC hq hg hd hbg hps hht hcb
    refine ⟨hsem, hC, ?_, ?_, hbg, ?_, hps, hht, hcb⟩
    · rw [derive_queries]; exact hq
    · rw [derive_macroGates]; exact hg
    · rw [derive_depth]; exact hd
  · intro ζ hζ
    have hc := prepared_search_quarter_mass_consumer ζ hζ
    refine ⟨hc, ?_⟩
    have hunit := (prepared_aa_actual_circuit (preparedQuarterA ζ) (0 : Fin 2)
      ({1} : Finset (Fin 2)) 1 hc.1).1
    have hQC := hc.2.2.2.1
    have hGC := hc.2.2.2.2
    refine ⟨fun ψ _ => by simp, hunit, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [derive_queries, hQC]
    · rw [derive_macroGates, hGC]
    · rw [zeroProfile_basicGates]
    · rw [derive_depth, size_eq_gateCount_add_queryCount, hQC, hGC]
    · rw [zeroProfile_peakSpace]
    · rw [zeroProfile_hamiltonianTime]
    · rw [derive_zeroProfile]
  · refine ⟨?_, ?_⟩
    · intro X _ _ E _ _ n input f Γ hzero hfeas
      exact adversary_le_filteredGamma2_queryDelta input f Γ hzero hfeas
    · intro X _ _ n R input ε hε1 hε2 ρ σ hρ hσ prog hspec oracle
      have hSDP := stateConversionSDP_lower_bound_of_actual_circuit
        X n (QueryCount (prog oracle)) R input ε hε1 hε2 ρ σ hρ hσ (prog oracle) rfl
        (hspec oracle).1 (hspec oracle).2
      have hfin : ((2 * QueryCount (prog oracle) : ℕ) : ℝ≥0∞) ≠ ⊤ :=
        ENNReal.natCast_ne_top _
      have hSDPne : (stateConversionSDP input (2 * Real.sqrt (2 * ε))
          (gramStateMatrix ρ) (gramStateMatrix σ)) ≠ ⊤ := by
        intro h
        rw [h] at hSDP
        exact hfin (top_le_iff.mp hSDP)
      have h2 := (ENNReal.toReal_le_toReal hSDPne hfin).mpr hSDP
      rw [ENNReal.toReal_natCast] at h2
      have h3 : ((2 * QueryCount (prog oracle) : ℕ) : ℝ)
          = 2 * ((QueryCount (prog oracle) : ℕ) : ℝ) := by
        push_cast
        ring
      rw [h3] at h2
      refine (Nat.ceil_le).mpr ?_
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      linarith
  · intro C ψ h
    have hrun := run_eq_of_queryCount_eq_zero (1 : Matrix Bool Bool ℂ) PauliX C h ψ
    exact ⟨hrun, fun b => congrArg (fun φ => BornProb φ b) hrun⟩

/-- Collects the tight parity query bound, its linear asymptotic growth, and explicit numerical
phase-table correctness, covering, precision, and comparison-cost estimates. See
[BealsEtAl2001]. -/
theorem g3 :
  (∀ (N : ℕ) (hN : 0 < N),
    (∀ f : Fin N → Bool,
      MeasureProb (Run (TensorGate (BitOracleOn f)
          (1 : Matrix (Reg N × Bool) (Reg N × Bool) ℂ)) (countedParityCircuit N)
        (countedParityInitial N hN)) (countedParityAccept N) =
      if (Finset.univ.filter (fun i => f i = true)).card % 2 = 1 then 1 else 0) ∧
    QueryCount (countedParityCircuit N) = (N + 1) / 2 ∧
    GateCount (countedParityCircuit N) ≤ 12 * N + 12 ∧
    (∀ (C : Circuit (PolynomialWorkspace (Fin N) (Reg N × Bool)))
        (ψ : QState (PolynomialWorkspace (Fin N) (Reg N × Bool)))
        (E : Finset (PolynomialWorkspace (Fin N) (Reg N × Bool))),
      IsUnitaryCircuit C → Normalized ψ →
      (∀ f : Fin N → Bool,
        |MeasureProb (Run (TensorGate (BitOracleOn f)
            (1 : Matrix (Reg N × Bool) (Reg N × Bool) ℂ)) C ψ) E
          - (if (Finset.univ.filter (fun i => f i = true)).card % 2 = 1
              then (1 : ℝ) else 0)| ≤ 1 / 3) →
      (N + 1) / 2 ≤ QueryCount C)) ∧
  IsResourceBigTheta (fun n : ℕ => (((n + 1) / 2 : ℕ) : ℝ)) (fun n : ℕ => (n : ℝ)) ∧
  (∀ (r q : ℕ),
    (phaseTable (numericalDyadicPhase r false q) (2 ^ r)).1.length = 2 ^ r ∧
      (phaseTable (numericalDyadicPhase r false q) (2 ^ r)).2 = 2 ^ r - 1 ∧
      (∀ j : ℕ, j < 2 ^ r →
        gaussianRatComplex
            ((phaseTable (numericalDyadicPhase r false q) (2 ^ r)).1.getD j gone)
          = (gaussianRatComplex (numericalDyadicPhase r false q)) ^ j ∧
        ‖gaussianRatComplex
            ((phaseTable (numericalDyadicPhase r false q) (2 ^ r)).1.getD j gone)‖ = 1) ∧
      (∀ v : ℂ, ‖v‖ = 1 → ∃ j : ℕ, j < 2 ^ r ∧
        ‖gaussianRatComplex
            ((phaseTable (numericalDyadicPhase r false q) (2 ^ r)).1.getD j gone) - v‖
          ≤ 8 / (2 ^ r : ℝ) + (2 ^ r : ℝ) * ((2 : ℝ) ⁻¹) ^ q)) ∧
  (∀ n : ℕ, 1 ≤ n →
    8 / ((2 : ℝ) ^ (Nat.log 2 n + 2)) +
        ((2 : ℝ) ^ (Nat.log 2 n + 2)) * ((2 : ℝ) ⁻¹) ^ (2 * (Nat.log 2 n + 2))
      ≤ (9 / 2 : ℝ) / n ∧
    2 ^ (Nat.log 2 n + 2) ≤ 4 * n) ∧
  (∀ d : ℕ, IsResourceBigO
      (fun n : ℕ => ((d : ℝ) + 1) * ((Nat.log 2 n : ℝ) + 3))
      (fun n : ℕ => (((Nat.log 2 n + 2) ^ 3 : ℕ) : ℝ)))
  :=
  ⟨fun N hN => parity_query_complexity_tight N hN,
    parity_query_growth_theta,
    fun r q => by
      have h := phase_grid_actual_cover_and_table_cost r q
      refine ⟨h.1, h.2.1, fun j hj => h.2.2.1 j hj, ?_⟩
      intro v hv
      obtain ⟨j, hj, hd⟩ := h.2.2.2 v hv
      refine ⟨j, hj, ?_⟩
      have hcast : (((2 ^ r : ℕ) : ℝ)) = (2 : ℝ) ^ r := Nat.cast_pow 2 r
      rw [hcast] at hd
      exact hd,
    phase_grid_precision,
    comparison_word_bit_growth⟩

/-- Collects local-program composition and error bounds, balanced fresh-copy and restart space
bounds, fresh-copy ledger identities, and the expected paid-restart receipt law. -/
theorem g4 :
  (∀ (I : Type) (p q : LocalProgram I),
      localPeakSpace (localOpAppend p q) ≤ localPeakSpace p + localPeakSpace q) ∧
    (∀ (I : Type) (p q : LocalProgram I), localProgramBalanced p → localProgramBalanced q →
      localProgramBalanced (localOpAppend p q) ∧
        localPeakSpace (localOpAppend p q) = max (localPeakSpace p) (localPeakSpace q) ∧
        localPeakSpace (localOpAppend p q) = localPeakSpace (localOpAppend q p)) ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I] (p q : LocalProgram I),
      localProgramMatrix (localOpAppend p q) = localProgramMatrix q * localProgramMatrix p) ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I] (p : LocalProgram I)
        (r : Matrix I I ℂ → Matrix I I ℂ),
      (∀ U ∈ localProgramGates p, U ∈ Matrix.unitaryGroup I ℂ
          ∧ r U ∈ Matrix.unitaryGroup I ℂ) →
      ‖localProgramMatrix p - localProgramRefMatrix r p‖ ≤ localProgramErrorSum r p) ∧
    (∀ (D : ℕ) (angles : List ℝ),
      localProgramBalanced (freshCopyScheduleProgram D angles) ∧
        localPeakSpace (freshCopyScheduleProgram D angles) ≤ 1 ∧
        localProgramGates (freshCopyScheduleProgram D angles)
          = angles.map (fun θ => partialSwapMatrix D θ) ∧
        localProgramMatrix (freshCopyScheduleProgram D angles)
          = angles.foldl (fun M θ => partialSwapMatrix D θ * M)
              (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) ∧
        freshCopyCompositionLedgerAdapter D angles
          = FreshCopyLedger.ofProd (freshCopyResourceCounts D angles) ∧
        freshCopyResourceCounts D angles
          = (angles.length, angles.length, angles.length, 0)) ∧
    (∀ (D : ℕ) (ρ σ : Operator D) (xs ys : List ℝ),
      freshCopyRun ρ (xs ++ ys) σ = freshCopyRun ρ ys (freshCopyRun ρ xs σ) ∧
        freshCopyResourceCounts D (xs ++ ys) =
          (xs.length + ys.length, xs.length + ys.length, xs.length + ys.length, 0) ∧
        freshCopyResourceCounts D xs = (xs.length, xs.length, xs.length, 0)) ∧
    Qatlib.Concepts.SearchStopping.PaidRestart.ActualRestartExpectedReceipt ∧
    (∀ (I : Type) (U : Matrix I I ℂ) (r : ℕ),
      localProgramBalanced (restartLoopProgram U r) ∧
        localPeakSpace (restartLoopProgram U r) ≤ 1) ∧
    (∀ (I : Type) (p : LocalProgram I), localPeakSpace p ≤ localAllocTotal p) ∧
    (∀ (D : ℕ) (angles : List ℝ), 2 ≤ D → angles ≠ [] →
      localPeakSpace (freshCopyScheduleProgram D angles) ≤ 1 ∧ 1 < D * D)
  := by
  refine ⟨fun I p q => localPeakSpace_append_le p q, ?_, fun I _ _ p q =>
    localProgramMatrix_append p q, fun I _ _ p r hU => localProgram_refError_le p r hU,
    ?_, fun D ρ σ xs ys => fresh_copy_schedule_composition_cost ρ σ xs ys,
    Qatlib.Concepts.SearchStopping.PaidRestart.actualRestartExpectedReceipt,
    fun I U r => restartLoopProgram_bal U r,
    fun I p => localPeakSpace_le_allocTotal p, ?_⟩
  · intro I p q hp hq
    have h := localOpAppend_balanced p q hp hq
    exact ⟨h.1, h.2, h.2.trans
      ((Nat.max_comm (localPeakSpace p) (localPeakSpace q)).trans
        (localOpAppend_balanced q p hq hp).2.symm)⟩
  · intro D angles
    exact ⟨(freshCopyScheduleProgram_bal D angles).1,
      (freshCopyScheduleProgram_bal D angles).2,
      freshCopyScheduleProgram_gates D angles,
      freshCopyScheduleProgram_matrix D angles, rfl, freshCopyResourceCounts_eq D angles⟩
  · intro D angles hD _hne
    have h : (2 : ℕ) * 2 ≤ D * D := Nat.mul_le_mul hD hD
    exact ⟨(freshCopyScheduleProgram_bal D angles).2, by omega⟩

end Qatlib.Concepts.SearchStopping.PaidRestart
