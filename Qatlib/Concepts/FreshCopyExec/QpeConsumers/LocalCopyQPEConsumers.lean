/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FreshCopyExec.QpeConsumers.LocalControlledCopyBridge
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopyDrivenPhaseReadout
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopyPureReadout
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopySpectralReadout

/-!
# Local fresh-copy phase estimation

`localCopyQPEProgram` executes query circuits using locally compiled controlled partial swaps on
fresh copies. Its output agrees with the abstract copy-driven phase estimation program, while
its resource ledger records the compiled gate count and copy use.

The spectral event bound transfers the density matrix exponentiation interpretation of
[LloydMohseniRebentrost2014] to this local implementation. The final examples retain the
control-dependent phase and the phase accompanying a one-qubit swap.

## Main statements

* `local_copy_qpe_same_program_output_and_resources`: identifies the output and gives the exact
  resource tuple.
* `local_copy_qpe_actual_spectral_event_consumer`: bounds spectral event error by `8 * (M - 1) *
  π² / s`.
* `local_copy_global_phase_and_qubit_swap_consumers`: checks scalar coherence and the compiled
  one-qubit swap action.

## References

* [Lloyd et al., 2014][LloydMohseniRebentrost2014]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Matrix
open scoped Classical BigOperators
set_option autoImplicit false

/-- The `s`-fold composition of the local controlled-copy channel with time step `t / s`. -/
noncomputable def localCopyRunMap (n : ℕ) (ρ : Operator (2^n)) (t : ℝ) :
    ℕ → MatrixMap (Fin (2*(2^n))) (Fin (2*(2^n))) ℂ
  | s => copyMapPower (localControlledCopyChannelMap n ρ (t / (s : ℝ))) s

/-- A local controlled-copy run at time `π`, amplified over the phase register and transported
to the QPE register layout. -/
noncomputable def localCopyQPEQuery (n M s : ℕ) (ρ : Operator (2^n))
    (X : Matrix (Fin M × (Bool × Fin (2^n))) (Fin M × (Bool × Fin (2^n))) ℂ) :
    Matrix (Fin M × (Bool × Fin (2^n))) (Fin M × (Bool × Fin (2^n))) ℂ :=
  relabelGate (copyQPERegisterEquiv (2^n) M).symm
    (ChannelAmplification (localCopyRunMap n ρ Real.pi s) M
      (relabelGate (copyQPERegisterEquiv (2^n) M) X))

/-- Executes a circuit on matrices, interpreting gates by conjugation and queries by
`localCopyQPEQuery`. -/
noncomputable def localCopyQPEProgram (n M s : ℕ) (ρ : Operator (2^n)) :
    Circuit (Fin M × (Bool × Fin (2^n))) →
      Matrix (Fin M × (Bool × Fin (2^n))) (Fin M × (Bool × Fin (2^n))) ℂ →
      Matrix (Fin M × (Bool × Fin (2^n))) (Fin M × (Bool × Fin (2^n))) ℂ
  | [], X => X
  | Step.gate U :: C, X => localCopyQPEProgram n M s ρ C (MatrixMap.conj U X)
  | Step.query :: C, X => localCopyQPEProgram n M s ρ C (localCopyQPEQuery n M s ρ X)

/-- The output of the counted phase estimation circuit on `copyQPEInput`, using local
controlled-copy queries. -/
noncomputable def localCopyQPEOutput (n M s : ℕ) (ρ : Operator (2^n)) :
    Matrix (Fin M × (Bool × Fin (2^n))) (Fin M × (Bool × Fin (2^n))) ℂ :=
  localCopyQPEProgram n M s ρ (countedPhaseCircuit M) (copyQPEInput (2^n) M ρ)

/-- The four-coordinate resource ledger for local copy queries, charging `(s * (36 * n + 7), s,
s, 0)` per query and ignoring fixed gates. -/
def localCopyQPEProgramResources {I : Type*} (n s : ℕ) : Circuit I → ℕ × ℕ × ℕ × ℕ
  | [] => (0,0,0,0)
  | Step.gate _ :: C => localCopyQPEProgramResources n s C
  | Step.query :: C =>
      let r := localCopyQPEProgramResources n s C
      (r.1 + s*(36*n+7), r.2.1+s, r.2.2.1+s, r.2.2.2)

/-- The local copy resource ledger evaluated on the counted phase estimation circuit. -/
noncomputable def localCopyQPEResources (n M s : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  localCopyQPEProgramResources n s (countedPhaseCircuit (I := Fin (2^n)) M)

/-- The local resource ledger equals the query count times `(s * (36 * n + 7), s, s, 0)`. -/
theorem localCopyQPEProgramResources_eq {I : Type*} (n s : ℕ) (C : Circuit I) :
    localCopyQPEProgramResources n s C =
      (QueryCount C * s * (36*n+7), QueryCount C*s, QueryCount C*s, 0) := by
  induction C with
  | nil => simp [localCopyQPEProgramResources, QueryCount]
  | cons g C ih =>
    cases g <;> simp [localCopyQPEProgramResources, QueryCount, ih, Nat.add_mul]

/-- For `M ≥ 2`, local QPE uses `M - 1` queries' worth of resources and has `2 * (M - 1) + 2`
fixed macros. -/
theorem localCopyQPEResources_eq (n M s : ℕ) (hM : 2 ≤ M) :
    localCopyQPEResources n M s =
      ((M-1)*s*(36*n+7), (M-1)*s, (M-1)*s, 0) ∧
      copyQPEFixedMacros (2^n) M = 2*(M-1)+2 := by
  have h := counted_offgrid_qpe_clean_flag M (by omega)
    (1 : Operator (2^n)) (0 : QState (Fin (2^n)))
  constructor
  · rw [localCopyQPEResources, localCopyQPEProgramResources_eq, h.2.1]
  · exact copyQPEFixedMacros_eq (2^n) M (by omega)

/-- A local controlled-copy run with zero steps is the identity map. -/
theorem localCopyRunMap_zero (n : ℕ) (ρ : Operator (2^n)) (t : ℝ) :
    localCopyRunMap n ρ t 0 = LinearMap.id := rfl

/-- For `M ≥ 2`, the first resource coordinate is `(M - 1) * s` times the actual gate count of
the compiled controlled-swap word. -/
theorem localCopyQPEResources_actual_gate_count (n M s : ℕ) (hM : 2 ≤ M) :
    (localCopyQPEResources n M s).1 = (M-1)*s*
      GateCount (reflectionCompile (localControlledSwapSteps n (Real.pi / (s : ℝ)))) := by
  rw [(localCopyQPEResources_eq n M s hM).1, gateCount_reflectionCompile,
    localControlledSwapSteps_length]

/-- The locally compiled controlled-copy run equals `controlledCopyRunMap` for every step count. -/
theorem localCopyRunMap_eq (n : ℕ) (ρ : Operator (2^n)) (t : ℝ) (s : ℕ) :
    localCopyRunMap n ρ t s = controlledCopyRunMap ρ t s := by
  dsimp only [localCopyRunMap,controlledCopyRunMap]
  rw [(local_controlled_copy_actual_discard_and_reference_bridge n ρ (t/(s : ℝ))).2.1]

/-- The local and abstract copy-driven QPE query maps agree on every matrix. -/
theorem localCopyQPEQuery_eq (n M s : ℕ) (ρ : Operator (2^n))
    (X : Matrix (Fin M × (Bool × Fin (2^n))) (Fin M × (Bool × Fin (2^n))) ℂ) :
    localCopyQPEQuery n M s ρ X = copyQPEQuery (2^n) M s ρ X := by
  unfold localCopyQPEQuery copyQPEQuery
  rw [localCopyRunMap_eq]

/-- The local and abstract copy-driven circuit interpreters agree on every circuit and input
matrix. -/
theorem localCopyQPEProgram_eq (n M s : ℕ) (ρ : Operator (2^n))
    (C : Circuit (Fin M × (Bool × Fin (2^n))))
    (X : Matrix (Fin M × (Bool × Fin (2^n))) (Fin M × (Bool × Fin (2^n))) ℂ) :
    localCopyQPEProgram n M s ρ C X = copyQPEProgram (2^n) M s ρ C X := by
  induction C generalizing X with
  | nil => rfl
  | cons g C ih =>
    cases g <;> simp only [localCopyQPEProgram,copyQPEProgram,localCopyQPEQuery_eq,ih]

/-- The local QPE output equals the abstract copy-driven QPE output. -/
theorem localCopyQPEOutput_eq (n M s : ℕ) (ρ : Operator (2^n)) :
    localCopyQPEOutput n M s ρ = copyQPEOutput (2^n) M s ρ :=
  localCopyQPEProgram_eq n M s ρ _ _

/-- For `M ≥ 2` and positive `s`, the local QPE output agrees with the abstract output and has
the stated exact resource tuple and fixed macro count. -/
theorem local_copy_qpe_same_program_output_and_resources :
    ∀ (n M s : ℕ) (ρ : Operator (2^n)), 2 ≤ M → 0 < s →
      localCopyQPEOutput n M s ρ = copyQPEOutput (2^n) M s ρ ∧
      localCopyQPEResources n M s = ((M-1)*s*(36*n+7),(M-1)*s,(M-1)*s,0) ∧
      copyQPEFixedMacros (2^n) M = 2*(M-1)+2 := by
  intro n M s ρ hM _hs
  exact ⟨localCopyQPEOutput_eq n M s ρ,localCopyQPEResources_eq n M s hM⟩

/-- For a density operator with the given unitary diagonalization, the local QPE event mass
differs from its eigenvalue-weighted kernel law by at most `8 * (M - 1) * π² / s`, when `M ≥
2` and `s > 0`. -/
theorem local_copy_qpe_actual_spectral_event_consumer :
    ∀ (n M s : ℕ) (ρ V : Operator (2^n)) (eig : Fin (2^n) → ℝ) (E : Finset (Fin M)),
      2 ≤ M → 0 < s → IsDensityOperator ρ → V ∈ Matrix.unitaryGroup (Fin (2^n)) ℂ →
      ρ = V * Matrix.diagonal (fun i => (eig i : ℂ)) * Vᴴ → (∀ i, 0 ≤ eig i) →
      |(∑ z ∈ E,copyQPELabelMass (2^n) M (localCopyQPEOutput n M s ρ) z) -
        (∑ i,eig i * (∑ z ∈ E,‖qpeKernel M (-eig i/2) z‖^2))| ≤
        8*(M-1 : ℕ)*Real.pi^2/(s : ℝ) := by
  intro n M s ρ V eig E hM hs hρ hV hdiag heig
  rw [(local_copy_qpe_same_program_output_and_resources n M s ρ hM hs).1]
  exact copy_qpe_actual_spectral_label_event (2^n) M s hM hs ρ V eig hρ hV hdiag heig E

/-- Applying a matrix to a basis ket selects the corresponding matrix column. -/
private theorem localCopyGate_ket_column {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (p x : I) : ApplyGate A (Qatlib.Foundations.PureStateMath.Ket p) x = A x p := by
  simp [ApplyGate,Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket]

/-- At angle `π / 2`, the controlled partial swap exchanges the two qubit labels on the
true-control branch and multiplies the ket by `-i`. -/
private theorem localCopyControlledSwap_pi_basis (i j : Fin 2) :
    ApplyGate (controlledSwapRawGate 2 (Real.pi/2)) (Qatlib.Foundations.PureStateMath.Ket (true,(i,j))) =
      (-Complex.I) • Qatlib.Foundations.PureStateMath.Ket (true,(j,i)) := by
  ext ⟨b,k,l⟩
  rw [localCopyGate_ket_column]
  cases b <;>
    simp [controlledSwapRawGate,Qatlib.Concepts.BlockEncoding.LCU.select,partialSwapMatrix_apply,
      Real.cos_pi_div_two,Real.sin_pi_div_two,Qatlib.Foundations.PureStateMath.Ket,Prod.ext_iff]
  split_ifs <;> ring

/-- Computes the scalar control coherence and the framed one-qubit swap action, including its
factor `-i`. The compiled one-qubit swap word has exactly 43 gates. -/
theorem local_copy_global_phase_and_qubit_swap_consumers :
    (∀ θ : ℝ, localControlledCopyRawMap 0 (1 : Operator 1) θ
      (fun _ _ => (1/2 : ℂ)) (false,0) (true,0) =
      Complex.exp (Complex.I*(θ : ℂ))/2) ∧
    (∀ i j : Fin 2, ApplyGate (reflectionProgramMatrix (localControlledSwapSteps 1 (Real.pi/2)))
      (localCopyFrame 1 *ᵥ Qatlib.Foundations.PureStateMath.Ket (true,(i,j))) =
      (-Complex.I) • (localCopyFrame 1 *ᵥ Qatlib.Foundations.PureStateMath.Ket (true,(j,i)))) ∧
    GateCount (reflectionCompile (localControlledSwapSteps 1 (Real.pi/2))) = 43 := by
  constructor
  · intro θ
    rw [localControlledCopyRawMap_eq]
    have h := controlledCopyRawMap_ft (1 : Operator 1) θ (fun _ _ => (1/2 : ℂ)) 0 0 (by simp)
    rw [Matrix.mul_one] at h
    change controlledCopyRawMap (1 : Operator 1) θ (fun _ _ => (1/2 : ℂ)) (false,0) (true,0) =
      (Real.cos θ) • (1/2 : ℂ) + (Complex.I*(Real.sin θ : ℂ)) • (1/2 : ℂ) at h
    change controlledCopyRawMap (1 : Operator 1) θ (fun _ _ => (1/2 : ℂ)) (false,0) (true,0) =
      Complex.exp (Complex.I*(θ : ℂ))/2
    rw [h,mul_comm Complex.I (θ : ℂ),Complex.exp_ofReal_mul_I]
    simp only [smul_eq_mul,Complex.real_smul]
    push_cast
    ring
  · constructor
    · intro i j
      change reflectionProgramMatrix (localControlledSwapSteps 1 (Real.pi/2)) *ᵥ
        (localCopyFrame 1 *ᵥ Qatlib.Foundations.PureStateMath.Ket (true,(i,j))) = _
      rw [Matrix.mulVec_mulVec,local_controlled_partial_swap_clean_intertwining,
        ← Matrix.mulVec_mulVec]
      have h := localCopyControlledSwap_pi_basis i j
      change controlledSwapRawGate 2 (Real.pi/2) *ᵥ Qatlib.Foundations.PureStateMath.Ket
          (true,(i,j)) = _ at h
      change localCopyFrame 1 *ᵥ
          (controlledSwapRawGate 2 (Real.pi/2) *ᵥ Qatlib.Foundations.PureStateMath.Ket (true,(i,j))) = _
      rw [h,Matrix.mulVec_smul]
    · exact (local_controlled_swap_actual_gate_table_and_inverse 1 (Real.pi/2)).2.2.2.2.1

end Qatlib.Concepts.FreshCopyExec.QpeConsumers
