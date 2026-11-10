/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuitCompile
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedRelabel
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedPurification
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge


namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix

noncomputable def embedKrausMixedTrace {d s n : ℕ}
    (e : (Fin d × Fin s) ≃ Fin n) (zero : Fin s)
    (t : MixedBranchTrace d) : MixedBranchTrace n where
  state := relabelGate e (TensorGate t.state (outerProduct (Qatlib.Foundations.PureStateMath.Ket zero)))
  accepted := t.accepted
  queries := t.queries
  gates := t.gates
  measurements := t.measurements
  outcomes := t.outcomes

private theorem mixedCompiler_relabel_star {I J : Type*} (e : I ≃ J)
    (M : Matrix I I ℂ) :
    relabelGate e M.conjTranspose = (relabelGate e M).conjTranspose := by
  ext i j
  rfl

private theorem mixedCompiler_relabel_sandwich {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (M X : Matrix I I ℂ) :
    relabelGate e (M * X * M.conjTranspose) =
      relabelGate e M * relabelGate e X * (relabelGate e M).conjTranspose := by
  rw [Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_mul, Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_mul,
    mixedCompiler_relabel_star]

private theorem mixedCompiler_relabel_projector {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) {s : ℕ} (label : I → Fin s) (a : Fin s) :
    Projector (Finset.univ.filter (fun j : J => label (e.symm j) = a)) =
      relabelGate e (Projector (Finset.univ.filter (fun i : I => label i = a))) := by
  ext i j
  simp only [Projector, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.diagonal_apply, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : i = j
  · subst j
    simp
  · have h' : e.symm i ≠ e.symm j := fun hh => h (e.symm.injective hh)
    simp [h, h']

private theorem mixedCompiler_gate {d s n : ℕ}
    (e : (Fin d × Fin s) ≃ Fin n) (zero : Fin s) (G rho : Operator d) :
    conjBranch (relabelGate e (TensorGate G (1 : Operator s)))
        (relabelGate e (TensorGate rho (outerProduct (Qatlib.Foundations.PureStateMath.Ket zero)))) =
      relabelGate e (TensorGate (conjBranch G rho) (outerProduct (Qatlib.Foundations.PureStateMath.Ket zero))) := by
  simp only [conjBranch_apply, ← mixedCompiler_relabel_sandwich,
    tensorGate_conjTranspose, tensorGate_mul, Matrix.conjTranspose_one,
    Matrix.one_mul, Matrix.mul_one]

private theorem mixedCompiler_instrument {d s n : ℕ}
    (e : (Fin d × Fin s) ≃ Fin n) (K : Fin s → Operator d)
    (hK : ∑ a, (K a).conjTranspose * K a = 1) (zero a : Fin s)
    (rho : Operator d) :
    conjBranch (relabelGate e (krausMemoryReset zero a))
      (conjBranch
        (Projector (Finset.univ.filter
          (fun x : Fin n => (e.symm x).2 = a)))
        (conjBranch (relabelGate e (chosenKrausUnitary K hK zero))
          (relabelGate e (TensorGate rho (outerProduct (Qatlib.Foundations.PureStateMath.Ket zero)))))) =
      relabelGate e (TensorGate (conjBranch (K a) rho) (outerProduct (Qatlib.Foundations.PureStateMath.Ket zero))) := by
  rw [mixedCompiler_relabel_projector e Prod.snd a]
  simp only [conjBranch_apply, ← mixedCompiler_relabel_sandwich]
  simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using
    congrArg (relabelGate e)
      (kraus_memory_reset_mixed_branch K zero a (chosenKrausUnitary K hK zero)
        (chosenKrausUnitary_spec K hK zero).2 rho)

theorem kraus_compiled_mixed_traces {d s n : ℕ}
    (e : (Fin d × Fin s) ≃ Fin n) (zero : Fin s)
    (O : Operator d) (P : KrausCircuit d s) (hP : krausCircuitWellFormed P)
    (rho : Operator d) :
    observedMixedTraces (relabelGate e (TensorGate O (1 : Operator s)))
      (relabelObserved e (compileKrausCircuit zero P hP))
      (relabelGate e (TensorGate rho (outerProduct (Qatlib.Foundations.PureStateMath.Ket zero)))) =
      (krausCircuitMixedTraces O P rho).map (embedKrausMixedTrace e zero) := by
  induction P generalizing rho with
  | halt b => rfl
  | step action P ih =>
      cases action with
      | gate G =>
          simp only [compileKrausCircuit, relabelObserved, observedMixedTraces,
            mixedCompiler_gate, ih, krausCircuitMixedTraces, List.map_map,
            Function.comp_def, embedKrausMixedTrace]
      | query =>
          simp only [compileKrausCircuit, relabelObserved, observedMixedTraces,
            mixedCompiler_gate, ih, krausCircuitMixedTraces, List.map_map,
            Function.comp_def, embedKrausMixedTrace]
  | instrument K next ih =>
      simp only [compileKrausCircuit, relabelObserved, observedMixedTraces,
        Function.comp_apply, mixedCompiler_instrument, ih, krausCircuitMixedTraces,
        List.map_flatten, List.map_ofFn, List.map_map, Function.comp_def,
        embedKrausMixedTrace, Nat.add_assoc]

theorem mixedMass_embedKrausMixedTrace {d s n : ℕ}
    (e : (Fin d × Fin s) ≃ Fin n) (zero : Fin s) (t : MixedBranchTrace d) :
    mixedMass (embedKrausMixedTrace e zero t) = mixedMass t := by
  have hrelabel (X : Matrix (Fin d × Fin s) (Fin d × Fin s) ℂ) :
      Matrix.trace (relabelGate e X) = Matrix.trace X := by
    change (∑ i : Fin n, X (e.symm i) (e.symm i)) =
      ∑ j : Fin d × Fin s, X j j
    exact e.symm.sum_comp (fun j => X j j)
  have hket : Matrix.trace (outerProduct (Qatlib.Foundations.PureStateMath.Ket zero)) = (1 : ℂ) := by
    simp [Matrix.trace, outerProduct_apply, ket_apply]
  unfold mixedMass embedKrausMixedTrace
  (try dsimp only)
  rw [hrelabel]
  rw [TensorGate, Matrix.trace_kronecker, hket, mul_one]

theorem kraus_compiled_event {d s n : ℕ}
    (e : (Fin d × Fin s) ≃ Fin n) (zero : Fin s)
    (O : Operator d) (P : KrausCircuit d s) (hP : krausCircuitWellFormed P)
    (rho : Operator d) (event : Bool → List (ℕ × ℕ) → Bool) :
    mixedObservedEventMass (relabelGate e (TensorGate O (1 : Operator s)))
      (relabelObserved e (compileKrausCircuit zero P hP))
      (relabelGate e (TensorGate rho (outerProduct (Qatlib.Foundations.PureStateMath.Ket zero)))) event =
      krausCircuitEventMass O P rho event := by
  simp only [mixedObservedEventMass, kraus_compiled_mixed_traces,
    krausCircuitEventMass, List.map_map, Function.comp_def,
    mixedMass_embedKrausMixedTrace]
  rfl

theorem kraus_compiled_expected {d s n : ℕ}
    (e : (Fin d × Fin s) ≃ Fin n) (zero : Fin s)
    (O : Operator d) (P : KrausCircuit d s) (hP : krausCircuitWellFormed P)
    (rho : Operator d) :
    mixedExpectedQueries (relabelGate e (TensorGate O (1 : Operator s)))
      (relabelObserved e (compileKrausCircuit zero P hP))
      (relabelGate e (TensorGate rho (outerProduct (Qatlib.Foundations.PureStateMath.Ket zero)))) =
      krausCircuitExpectedQueries O P rho := by
  simp only [mixedExpectedQueries, kraus_compiled_mixed_traces,
    krausCircuitExpectedQueries, List.map_map, Function.comp_def,
    mixedMass_embedKrausMixedTrace]
  rfl

end Qatlib.Concepts.AdversaryBounds.AdvDuality
