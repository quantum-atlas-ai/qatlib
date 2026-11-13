/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LocalHam06.MainResults.QmaCompletenessNative
import Qatlib.Papers.LocalHam06.MainResults.QmaCompletenessPhysical
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QmaCompletenessNativeBoundary
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QmaCompletenessNativeEnergy
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QmaCompletenessEntryBounds
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Sort

/-!
# Semantics of generated history Hamiltonians

The list `physicalList` enumerates propagation, boundary, and weighted clock penalty matrices.
The results identify the values of the generated integer terms with this list after flattening
and show in `outputTerms_value_sum` that their sum represents `fullHamiltonian`. See
[KempeKitaevRegev2006].

## Main statements

* `output_values_list`: The dyadic values of the generated output terms equal the physical
  matrix list reindexed by the inverse flattening equivalence.
* `physicalList_sum`: The sum of the matrices in `physicalList C` is `fullHamiltonian C`.
* `outputTerms_value_sum`: The sum of the generated dyadic term values equals the flattened full
  physical Hamiltonian.

## References

* [Kempe et al., 2006][KempeKitaevRegev2006]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Papers.LocalHam06.MainResults.NativeOutput

namespace Qatlib.Papers.LocalHam06.MainResults
open Qatlib  Qatlib.Concepts.QmaCompleteness.HistoryHam Matrix
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open scoped Classical BigOperators
set_option autoImplicit false
noncomputable section

/-- The matrix sum of a concatenation is the sum of the two matrix sums. -/
theorem matrixSum_append {I : Type} [Fintype I] [DecidableEq I]
    (xs ys : List (Matrix I I ℂ)) :
    matrixSum (xs ++ ys) = matrixSum xs + matrixSum ys := by
  induction xs with
  | nil => simp [matrixSum]
  | cons a xs ih =>
      change a + matrixSum (xs ++ ys) = (a + matrixSum xs) + matrixSum ys
      rw [ih]
      exact (add_assoc _ _ _).symm

/-- The sum of a singleton matrix list is its sole matrix. -/
theorem matrixSum_singleton {I : Type} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) : matrixSum [M] = M := by simp [matrixSum]

/-- Summing a flattened list of matrix lists equals summing the matrix sums of the individual
lists. -/
theorem matrixSum_flatMap {A I : Type} [Fintype I] [DecidableEq I]
    (xs : List A) (f : A → List (Matrix I I ℂ)) :
    matrixSum (xs.flatMap f) = matrixSum (xs.map (fun a => matrixSum (f a))) := by
  induction xs with
  | nil => simp [matrixSum]
  | cons a xs ih =>
      simp only [List.flatMap_cons, List.map_cons, matrixSum_append]
      change matrixSum (f a) + matrixSum (xs.flatMap f) =
        matrixSum (f a) + matrixSum (xs.map (fun a => matrixSum (f a)))
      rw [ih]

/-- Summing matrices over `List.finRange m` agrees with the finite sum over `Fin m`. -/
theorem matrixSum_finRange {I : Type} [Fintype I] [DecidableEq I]
    (m : ℕ) (f : Fin m → Matrix I I ℂ) :
    matrixSum ((List.finRange m).map f) = ∑ i, f i := by
  change ((List.finRange m).map f).sum = ∑ i, f i
  exact (Fin.sum_univ_def f).symm

/-- Summing a matrix list enumerated over all ordered pairs in `Fin m` agrees with the
corresponding double finite sum. -/
theorem matrixSum_allPairs {I : Type} [Fintype I] [DecidableEq I]
    (m : ℕ) (f : Fin m → Fin m → Matrix I I ℂ) :
    matrixSum ((List.finRange m).flatMap (fun i => (List.finRange m).map (f i))) =
      ∑ i, ∑ j, f i j := by
  rw [matrixSum_flatMap]
  calc
    matrixSum ((List.finRange m).map (fun i =>
        matrixSum ((List.finRange m).map (f i)))) =
        matrixSum ((List.finRange m).map (fun i => ∑ j, f i j)) := by
      apply congrArg matrixSum
      apply List.map_congr_left
      intro i _
      exact matrixSum_finRange m (f i)
    _ = ∑ i, ∑ j, f i j := matrixSum_finRange m _

/-- Summing matrices over the sorted elements of a finite set agrees with summing over its list
representation. -/
theorem matrixSum_sort_toList {A I : Type} [LinearOrder A]
    [Fintype I] [DecidableEq I] (s : Finset A) (f : A → Matrix I I ℂ) :
    matrixSum (s.sort.map f) = matrixSum (s.toList.map f) := by
  change (s.sort.map f).sum = (s.toList.map f).sum
  exact ((Finset.sort_perm_toList s (· ≤ ·)).map f).sum_eq

/-- Reindexing every matrix in a list commutes with taking the matrix sum. -/
theorem matrixSum_reindex {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (xs : List (Matrix I I ℂ)) :
    matrixSum (xs.map (Matrix.reindex e e)) = Matrix.reindex e e (matrixSum xs) := by
  induction xs with
  | nil => rfl
  | cons M xs ih =>
      change Matrix.reindex e e M + matrixSum (xs.map (Matrix.reindex e e)) =
        Matrix.reindex e e (M + matrixSum xs)
      rw [ih]
      rfl

/-- The natural clock penalty weight `32 * (C.gates.length + C.initZeroWires.card + 1) + 1`. -/
def nativeJ (C : QmaHistoryCircuit) : ℕ :=
  32 * (C.gates.length + C.initZeroWires.card + 1) + 1

/-- The complex casts of the natural penalty `nativeJ C` and real penalty `clockJ C` coincide. -/
theorem nativeJ_cast (C : QmaHistoryCircuit) : (nativeJ C : ℂ) = (clockJ C : ℂ) := by
  unfold nativeJ clockJ restK restLength
  push_cast
  ring

/-- Rounding the gate at index `i` agrees with evaluating the circuit family `qmaRoundedGates`
at that index. -/
theorem rounded_get_eq (C : QmaHistoryCircuit) (b : ℕ) (i : Fin C.gates.length) :
    qmaRoundedGate C.qubits b (C.gates.get i) = qmaRoundedGates C b i := by
  unfold qmaRoundedGates
  congr 1
  change C.gates[i.val] = qmaGateAt C.gates i.val
  exact (clause2Aux_qmaGateAt_getElem C.gates i.val i.isLt).symm

/-- The ordered list of physical propagation terms, input penalties, output penalty, and
weighted clock pair penalties. -/
def physicalList (C : QmaHistoryCircuit) : List (Matrix (Phys C) (Phys C) ℂ) :=
  ((List.finRange C.gates.length).map fun i =>
    physicalPropagation i (qmaRoundedGates C (qmaClause2Bits C) i)) ++
  (C.initZeroWires.sort.map fun j => physicalInput (m:=C.gates.length) j) ++
  [physicalOutput (m:=C.gates.length) C.outputWire] ++
  ((List.finRange C.gates.length).flatMap fun i =>
    (List.finRange C.gates.length).map fun j =>
      (nativeJ C : ℂ) • TensorGate (pairPenalty i j)
        (1 : Matrix (Reg C.qubits) (Reg C.qubits) ℂ))

/-- The dyadic values of the generated output terms equal the physical matrix list reindexed by
the inverse flattening equivalence. -/
theorem output_values_list (C : QmaHistoryCircuit) :
    (outputTerms C.qubits (qmaClause2Bits C) C.gates C.initZeroWires C.outputWire).map
      (value (qmaClause2Bits C + 1)) =
    (physicalList C).map (Matrix.reindex (flattenEquiv C.gates.length C.qubits).symm
      (flattenEquiv C.gates.length C.qubits).symm) := by
  simp only [outputTerms, physicalList, List.map_append, List.map_map,
    List.map_cons, List.map_nil, List.map_flatMap, Function.comp_def]
  apply congrArg₂ (· ++ ·)
  · apply congrArg₂ (· ++ ·)
    · apply congrArg₂ (· ++ ·)
      · apply List.map_congr_left
        intro i _
        simpa only [rounded_get_eq] using
          propagationTerm_value C.qubits (qmaClause2Bits C) i (C.gates.get i)
      · apply List.map_congr_left
        intro j _
        simpa only [boundaryTarget, Bool.false_eq_true, if_false] using
          boundaryTerm_value C.gates.length C.qubits (qmaClause2Bits C) false j
    · exact congrArg (fun M => [M]) (by
        simpa only [boundaryTarget, if_true] using
          boundaryTerm_value C.gates.length C.qubits (qmaClause2Bits C) true C.outputWire)
  · apply congrArg (fun f : Fin C.gates.length →
        List (Matrix (Reg (C.gates.length+C.qubits)) (Reg (C.gates.length+C.qubits)) ℂ) =>
          (List.finRange C.gates.length).flatMap f)
    funext i
    apply List.map_congr_left
    intro j _
    exact clockPairTerm_value C.qubits (qmaClause2Bits C) (nativeJ C) i j

/-- The physical remainder is the sum of the propagation matrices, the input penalties in sorted
wire order, and the output penalty. -/
theorem rest_sorted (C : QmaHistoryCircuit) :
    rest C =
      matrixSum ((List.finRange C.gates.length).map fun i =>
        physicalPropagation i (qmaRoundedGates C (qmaClause2Bits C) i)) +
      matrixSum (C.initZeroWires.sort.map fun j => physicalInput (m:=C.gates.length) j) +
      physicalOutput (m:=C.gates.length) C.outputWire := by
  simp only [rest, termPairs, List.map_append, List.map_map, Function.comp_def,
    List.map_cons, List.map_nil, matrixSum_append, matrixSum_singleton]
  rw [matrixSum_sort_toList]

/-- The sum of all weighted clock pair penalties tensored with the data identity equals the
weighted full clock penalty tensor. -/
theorem pair_sum (m n J : ℕ) :
    matrixSum ((List.finRange m).flatMap fun i => (List.finRange m).map fun j =>
      (J:ℂ) • TensorGate (pairPenalty i j) (1 : Matrix (Reg n) (Reg n) ℂ)) =
      (J:ℂ) • TensorGate (clockPenalty m) (1 : Matrix (Reg n) (Reg n) ℂ) := by
  rw [matrixSum_allPairs, clockPenalty_eq_pair_sum]
  ext ⟨c,x⟩ ⟨d,y⟩
  simp only [Fintype.sum_prod_type, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    tensorGate_apply, Finset.mul_sum, Finset.sum_mul]

/-- The sum of the matrices in `physicalList C` is `fullHamiltonian C`. -/
theorem physicalList_sum (C : QmaHistoryCircuit) :
    matrixSum (physicalList C) = fullHamiltonian C := by
  unfold physicalList
  rw [matrixSum_append, matrixSum_append, matrixSum_append, matrixSum_singleton, pair_sum]
  rw [nativeJ_cast]
  rw [← rest_sorted]
  rfl

/-- The sum of the generated dyadic term values equals the flattened full physical Hamiltonian. -/
theorem outputTerms_value_sum (C : QmaHistoryCircuit) :
    matrixSum ((outputTerms C.qubits (qmaClause2Bits C) C.gates C.initZeroWires C.outputWire).map
      (value (qmaClause2Bits C + 1))) =
    Matrix.reindex (flattenEquiv C.gates.length C.qubits).symm
      (flattenEquiv C.gates.length C.qubits).symm (fullHamiltonian C) := by
  rw [output_values_list, matrixSum_reindex, physicalList_sum]

end
end Qatlib.Papers.LocalHam06.MainResults
