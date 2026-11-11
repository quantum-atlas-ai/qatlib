/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralReadout.PhaseReadout.QmaCompletenessNoBound
import Qatlib.Concepts.QmaCompleteness.HistoryHam.QmaCompletenessRefined

/-!
# Physical realization of the history Hamiltonian

The spaces `Phys` and `Abs` represent the physical unary clock register and the abstract history
register. The paired terms in `termPairs` intertwine through the history frame, and their
physical sum extends to `fullHamiltonian` by a clock penalty. The module transports completeness
witnesses into the physical space. See [KempeKitaevRegev2006].

## Main statements

* `rest_frame`: The history frame intertwines the physical remainder with the abstract legal
  history Hamiltonian.
* `full_frame`: The history frame intertwines the full physical Hamiltonian with the abstract
  legal history Hamiltonian.
* `actual_full_yes`: A legal normalized witness accepted with probability at least `a` yields a
  normalized physical state whose energy is at most `qmaClause2YesBound C a`.

## References

* [Kempe et al., 2006][KempeKitaevRegev2006]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription

namespace Qatlib.Papers.LocalHam06.MainResults
open Qatlib  Qatlib.Concepts.QmaCompleteness.HistoryHam Matrix
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open scoped Classical BigOperators Kronecker
set_option autoImplicit false
noncomputable section

/-- The product of the physical clock configurations and the data register of `C`. -/
abbrev Phys (C : QmaHistoryCircuit) := Clock C.gates.length×Reg C.qubits
/-- The abstract history register with `C.gates.length + 1` clock labels and the data register
of `C`. -/
abbrev Abs (C : QmaHistoryCircuit) := Fin (C.gates.length+1)×Reg C.qubits

/-- The list pairing physical propagation and boundary matrices with their abstract history
counterparts. -/
def termPairs (C : QmaHistoryCircuit) :
    List (Matrix (Phys C) (Phys C) ℂ×Matrix (Abs C) (Abs C) ℂ) :=
  ((List.finRange C.gates.length).map fun i =>
    (physicalPropagation i (qmaRoundedGates C (qmaClause2Bits C) i),
     qmaPropTerm C.qubits C.gates.length (qmaRoundedGates C (qmaClause2Bits C)) i)) ++
  (C.initZeroWires.toList.map fun j =>
    (physicalInput (m:=C.gates.length) j,qmaInTerm C.qubits C.gates.length j)) ++
  [(physicalOutput (m:=C.gates.length) C.outputWire,
    qmaOutTerm C.qubits C.gates.length C.outputWire)]

/-- The sum of a list of matrices, defined by a right fold starting at zero. -/
def matrixSum {I : Type} [Fintype I] [DecidableEq I]
    (ts : List (Matrix I I ℂ)) : Matrix I I ℂ := ts.foldr (·+·) 0

/-- The sum of the physical components of `termPairs C`. -/
def rest (C : QmaHistoryCircuit) := matrixSum ((termPairs C).map Prod.fst)
/-- The abstract history Hamiltonian built from the rounded circuit gates at precision
`qmaClause2Bits C`. -/
def legalHamiltonian (C : QmaHistoryCircuit) :=
  qmaHistoryHamiltonian C (qmaRoundedGates C (qmaClause2Bits C))

/-- The number `C.gates.length + C.initZeroWires.card + 1` of propagation and boundary terms. -/
def restLength (C : QmaHistoryCircuit) : ℕ := C.gates.length+C.initZeroWires.card+1
/-- The real bound `32 * restLength C` associated with the physical remainder. -/
def restK (C : QmaHistoryCircuit) : ℝ := 32*restLength C
/-- The real clock penalty weight `restK C + 1`. -/
def clockJ (C : QmaHistoryCircuit) : ℝ := restK C+1

/-- The physical remainder plus the clock penalty tensored with the data identity and weighted
by `clockJ C`. -/
def fullHamiltonian (C : QmaHistoryCircuit) :=
  rest C+(clockJ C:ℂ) • TensorGate (clockPenalty C.gates.length)
    (1:Matrix (Reg C.qubits) (Reg C.qubits) ℂ)

/-- The abstract clock matrix unit `timeUnit` agrees with `qmaClockTerm`. -/
theorem timeUnit_eq_qmaClockTerm {m : ℕ} (t s : Fin (m+1)) :
    timeUnit t s=qmaClockTerm m t s := by
  ext u v
  by_cases hu : u=t <;> by_cases hv : v=s <;>
    simp [timeUnit,qmaClockTerm,Qatlib.Foundations.PureStateMath.Ket,hu,hv,eq_comm] <;> tauto

/-- The abstract propagation matrix equals the corresponding `qmaPropTerm`. -/
theorem abstractPropagation_eq {m n : ℕ}
    (U : Fin m→Matrix (Reg n) (Reg n) ℂ) (i : Fin m) :
    abstractPropagation i (U i)=qmaPropTerm n m U i := by
  simp only [abstractPropagation,qmaPropTerm,timeUnit_eq_qmaClockTerm]

/-- If each pair of matrices intertwines through `V`, the sums of their first and second
components also intertwine through `V`. -/
theorem matrixSum_frame {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (V : Matrix J I ℂ)
    (ps : List (Matrix J J ℂ×Matrix I I ℂ))
    (h : ∀p∈ps,p.1*V=V*p.2) :
    matrixSum (ps.map Prod.fst)*V=V*matrixSum (ps.map Prod.snd) := by
  induction ps with
  | nil => simp [matrixSum]
  | cons p ps ih =>
    have hp:=h p (by simp)
    have ht : ∀q∈ps,q.1*V=V*q.2 := by intro q hq; exact h q (by simp [hq])
    simpa only [List.map_cons,matrixSum,List.foldr_cons,Matrix.add_mul,Matrix.mul_add]
      using! congrArg₂ (·+·) hp (ih ht)

/-- Each physical and abstract term pair intertwines through the history frame. -/
theorem termPairs_frame (C : QmaHistoryCircuit) :
    ∀p∈termPairs C,p.1*historyFrame C.gates.length C.qubits=
      historyFrame C.gates.length C.qubits*p.2 := by
  intro p hp
  simp only [termPairs,List.mem_append,List.mem_map,List.mem_singleton] at hp
  rcases hp with (⟨i,_,rfl⟩|⟨j,_,rfl⟩)|rfl
  · simpa only [abstractPropagation_eq] using!
      physicalPropagation_frame i (qmaRoundedGates C (qmaClause2Bits C) i)
  · simpa only [qmaInTerm,timeUnit_eq_qmaClockTerm] using!
      physicalInput_frame (m:=C.gates.length) j
  · simpa only [qmaOutTerm,timeUnit_eq_qmaClockTerm] using!
      physicalOutput_frame (m:=C.gates.length) C.outputWire

/-- The sum of the abstract components of `termPairs C` is `legalHamiltonian C`. -/
theorem termPairs_abstract (C : QmaHistoryCircuit) :
    matrixSum ((termPairs C).map Prod.snd)=legalHamiltonian C := by
  simp only [termPairs,List.map_append,List.map_map,Function.comp_def,
    List.map_cons,List.map_nil,legalHamiltonian,qmaHistoryHamiltonian,qmaHistoryTerms,
    qmaHistoryPropTerms,qmaHistoryInTerms,qmaHistoryOutTerm,matrixSum,List.foldr_append,
    List.foldr_map,List.foldr_cons,List.foldr_nil]

/-- The history frame intertwines the physical remainder with the abstract legal history
Hamiltonian. -/
theorem rest_frame (C : QmaHistoryCircuit) :
    rest C*historyFrame C.gates.length C.qubits=
      historyFrame C.gates.length C.qubits*legalHamiltonian C := by
  rw [rest,← termPairs_abstract]
  exact matrixSum_frame _ _ (termPairs_frame C)

/-- Every physical component in `termPairs C` preserves the clock sectors. -/
theorem termPairs_sector (C : QmaHistoryCircuit) :
    ∀p∈termPairs C,SectorPreserving p.1 := by
  intro p hp
  simp only [termPairs,List.mem_append,List.mem_map,List.mem_singleton] at hp
  rcases hp with (⟨i,_,rfl⟩|⟨j,_,rfl⟩)|rfl
  · exact propagation_sector _ _
  · exact input_sector _
  · exact output_sector _

/-- A matrix sum of sector-preserving operators is sector-preserving. -/
theorem matrixSum_sector {m n : ℕ}
    (ts : List (Matrix (Clock m×Reg n) (Clock m×Reg n) ℂ))
    (h : ∀H∈ts,SectorPreserving H) : SectorPreserving (matrixSum ts) := by
  induction ts with
  | nil => exact sector_zero
  | cons H ts ih =>
    exact sector_add H (matrixSum ts) (h H (by simp))
      (ih (by intro K hK; exact h K (by simp [hK])))

/-- The physical remainder preserves the clock sectors. -/
theorem rest_sector (C : QmaHistoryCircuit) : SectorPreserving (rest C) := by
  apply matrixSum_sector
  intro H hH
  obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hH
  exact termPairs_sector C p hp

/-- The length of `termPairs C` is exactly `restLength C`. -/
theorem restLength_exact (C : QmaHistoryCircuit) : (termPairs C).length=restLength C := by
  simp [termPairs,restLength]
  omega

/-- The number of remainder terms is at most `C.gates.length + C.qubits + 1`. -/
theorem restLength_le (C : QmaHistoryCircuit) : restLength C≤C.gates.length+C.qubits+1 := by
  have h:=Finset.card_le_univ C.initZeroWires
  simp only [Fintype.card_fin] at h
  unfold restLength
  omega

/-- The history frame intertwines the full physical Hamiltonian with the abstract legal history
Hamiltonian. -/
theorem full_frame (C : QmaHistoryCircuit) :
    fullHamiltonian C*historyFrame C.gates.length C.qubits=
      historyFrame C.gates.length C.qubits*legalHamiltonian C := by
  simp only [fullHamiltonian,Matrix.add_mul,Matrix.smul_mul,rest_frame,
    lifted_clockPenalty_annihilates_history,smul_zero,add_zero]

/-- A legal normalized witness accepted with probability at least `a` yields a normalized
physical state whose energy is at most `qmaClause2YesBound C a`. -/
theorem actual_full_yes (C : QmaHistoryCircuit) (a : ℝ)
    (hyes : ∃φ : QState (Reg C.qubits),
      QmaInitLegal C φ ∧ Normalized φ ∧ a≤qmaHistoryAcceptProb C φ) :
    ∃η : QState (Phys C),Normalized η ∧ energy (fullHamiltonian C) η≤qmaClause2YesBound C a := by
  obtain ⟨ψ,hψ,hE⟩:=(clause2Aux_twoWay C).1 a hyes
  refine ⟨historyFrame C.gates.length C.qubits*ᵥψ,?_,?_⟩
  · change mass (historyFrame C.gates.length C.qubits*ᵥψ)=1
    rw [historyFrame_mass]
    exact hψ
  · rw [intertwine_energy _ (historyFrame_isometry _ _) _ _ (full_frame C)]
    exact hE

/-- If each listed matrix has energy at least `-32` times state mass, their sum has energy at
least `-32 * ts.length` times state mass. -/
theorem matrixSum_lower {I : Type} [Fintype I] [DecidableEq I]
    (ts : List (Matrix I I ℂ))
    (h : ∀H∈ts,∀ψ : QState I,-(32:ℝ)*mass ψ ≤ energy H ψ)
    (ψ : QState I) :
    -(32*(ts.length:ℝ))*mass ψ ≤ energy (matrixSum ts) ψ := by
  induction ts with
  | nil => simp [matrixSum,energy,Qatlib.Foundations.PureStateMath.inner_apply]
  | cons H ts ih =>
    have hH:=h H (by simp) ψ
    have ht : ∀K∈ts,∀φ : QState I,-(32:ℝ)*mass φ ≤ energy K φ := by
      intro K hK φ
      exact h K (by simp [hK]) φ
    have hT:=ih ht
    simp only [matrixSum,List.foldr_cons,energy_add]
    dsimp only [matrixSum] at hT
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith

end
end Qatlib.Papers.LocalHam06.MainResults
