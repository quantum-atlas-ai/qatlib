/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedQueryCircuit
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Fresh-register trials and product measurement laws

This module compiles prepared circuits onto separate tensor registers and tracks their
data-query, input-query, and fixed-gate costs. It constructs repeated states, projective
measurement histories, and a probability mass function for fresh outcomes, with selection of the
first successful trial. The tensor-product measurement background is given in
[NielsenChuang2010].

The family construction permits different prepared circuits and binary Kraus operators in each
register. Outcome masses factor into products, and componentwise Kraus completeness implies
completeness of the tensor family.

## Main statements

* `compileFresh_counts` and `compileFreshFamily_counts`: exact resource counts.
* `freshHistoryMass_eq_prod` and `freshMeasurementLaw`: product masses and their probability
  law.
* `freshFamilyMass_eq_prod` and `freshFamilyKraus_complete`: family factorization and
  completeness.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false


open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.HhlAlgorithms.Postselection

universe u

open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib

/-- The recursively nested product of `k` registers of type `H`, with a one-point register at `k
= 0`. -/
@[reducible] def FreshRegister (H : Type u) : ℕ → Type u
  | 0 => PUnit
  | k + 1 => H × FreshRegister H k

instance instFintypeFreshRegister {H : Type*} [Fintype H] : (k : ℕ) → Fintype (FreshRegister H k)
  | 0 => inferInstanceAs (Fintype PUnit)
  | k + 1 => letI := instFintypeFreshRegister (H := H) k
             inferInstanceAs (Fintype (H × FreshRegister H k))

instance instDecidableEqFreshRegister {H : Type*} [DecidableEq H] :
    (k : ℕ) → DecidableEq (FreshRegister H k)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | k + 1 => letI := instDecidableEqFreshRegister (H := H) k
             inferInstanceAs (DecidableEq (H × FreshRegister H k))

/-- The fresh-register basis label with every component equal to the chosen label `zero`. -/
def freshZero {H : Type*} (zero : H) : (k : ℕ) → FreshRegister H k
  | 0 => PUnit.unit
  | k + 1 => (zero, freshZero zero k)

/-- A prepared instruction assigned to one register of a nonempty fresh-register product, using
`first` for the first factor and `later` for the remaining factors. -/
inductive FreshStep (H : Type u) : ℕ → Type u
  | first {k : ℕ} : PreparedStep H → FreshStep H (k + 1)
  | later {k : ℕ} : FreshStep H k → FreshStep H (k + 1)

/-- The underlying prepared instruction of a fresh-register instruction, forgetting its register
placement. -/
def FreshStep.source {H : Type*} : {k : ℕ} → FreshStep H k → PreparedStep H
  | _, .first c => c
  | _, .later c => c.source

/-- Compile the same prepared circuit onto each of `k` separate fresh registers. -/
noncomputable def compileFresh {H : Type*} (cs : List (PreparedStep H)) :
    (k : ℕ) → List (FreshStep H k)
  | 0 => []
  | k + 1 => cs.map FreshStep.first ++ (compileFresh cs k).map FreshStep.later

/-- The data-query count of a fresh-register word, computed from its underlying prepared
instructions. -/
def freshDataQueries {H : Type*} {k : ℕ} (cs : List (FreshStep H k)) : ℕ :=
  preparedDataQueries (cs.map FreshStep.source)

/-- The input-preparation query count of a fresh-register word. -/
def freshInputQueries {H : Type*} {k : ℕ} (cs : List (FreshStep H k)) : ℕ :=
  preparedInputQueries (cs.map FreshStep.source)

/-- The fixed-gate count of a fresh-register word. -/
def freshFixedGates {H : Type*} {k : ℕ} (cs : List (FreshStep H k)) : ℕ :=
  preparedFixedGates (cs.map FreshStep.source)

/-- Compiling `k` fresh copies multiplies each data-query, input-query, and fixed-gate count by
`k`. -/
theorem compileFresh_counts {H : Type*} (cs : List (PreparedStep H)) (k : ℕ) :
    freshDataQueries (compileFresh cs k) = k * preparedDataQueries cs ∧
    freshInputQueries (compileFresh cs k) = k * preparedInputQueries cs ∧
    freshFixedGates (compileFresh cs k) = k * preparedFixedGates cs := by
  induction k with
  | zero => simp [compileFresh, freshDataQueries, freshInputQueries, freshFixedGates,
      preparedDataQueries, preparedInputQueries, preparedFixedGates]
  | succ k ih =>
    have hm : (compileFresh cs (k + 1)).map FreshStep.source =
        cs ++ (compileFresh cs k).map FreshStep.source := by
      simp [compileFresh, List.map_map, Function.comp_def, FreshStep.source]
    unfold freshDataQueries freshInputQueries freshFixedGates at ih ⊢
    rw [hm]
    rcases preparedCounts_append cs ((compileFresh cs k).map FreshStep.source) with ⟨hu, hb, hg⟩
    constructor
    · calc
        _ = _ := hu
        _ = _ := by rw [ih.1]; ring
    constructor
    · calc
        _ = _ := hb
        _ = _ := by rw [ih.2.1]; ring
    · calc
        _ = _ := hg
        _ = _ := by rw [ih.2.2]; ring

section CircuitSemantics
variable {H : Type*} [Fintype H] [DecidableEq H]

/-- The matrix interpreting a fresh-register instruction as its prepared operation on the
designated factor and the identity on all other factors. -/
noncomputable def freshInstruction (U B : Matrix H H ℂ) :
    {k : ℕ} → FreshStep H k → Matrix (FreshRegister H k) (FreshRegister H k) ℂ
  | _, .first c => TensorGate (preparedInstruction U B c) 1
  | _, .later c => TensorGate 1 (freshInstruction U B c)

/-- The matrix product interpreting a fresh-register instruction list, with the empty word
interpreted as the identity. -/
noncomputable def evaluateFresh (U B : Matrix H H ℂ) {k : ℕ} :
    List (FreshStep H k) → Matrix (FreshRegister H k) (FreshRegister H k) ℂ
  | [] => 1
  | c :: cs => freshInstruction U B c * evaluateFresh U B cs

/-- A fresh-register instruction is unitary when its underlying prepared instruction is valid
and the data and input-preparation matrices are unitary. -/
theorem freshInstruction_unitary {U B : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hB : B ∈ Matrix.unitaryGroup H ℂ)
    {k : ℕ} (c : FreshStep H k) (hc : PreparedInstructionValid c.source) :
    freshInstruction U B c ∈ Matrix.unitaryGroup (FreshRegister H k) ℂ := by
  induction c with
  | first c => exact tensorGate_unitary (preparedInstruction_unitary hU hB hc) (Submonoid.one_mem _)
  | later c ih => exact tensorGate_unitary (Submonoid.one_mem _) (ih hc)

/-- Evaluation of concatenated fresh-register words is the product of their evaluations. -/
theorem evaluateFresh_append (U B : Matrix H H ℂ) {k : ℕ} (cs ds : List (FreshStep H k)) :
    evaluateFresh U B (cs ++ ds) = evaluateFresh U B cs * evaluateFresh U B ds := by
  induction cs with
  | nil => simp [evaluateFresh]
  | cons c cs ih => simp [evaluateFresh, ih, Matrix.mul_assoc]

/-- A prepared word placed on the first register evaluates to its prepared matrix tensored with
the identity on the remaining registers. -/
theorem evaluateFresh_first (U B : Matrix H H ℂ) (cs : List (PreparedStep H)) (k : ℕ) :
    evaluateFresh U B (cs.map (FreshStep.first (k := k))) =
      TensorGate (evaluatePrepared U B cs) (1 : Matrix (FreshRegister H k) (FreshRegister H k) ℂ) := by
  induction cs with
  | nil => simp [evaluateFresh, evaluatePrepared, tensorGate_one]
  | cons c cs ih =>
    simp only [List.map_cons, evaluateFresh, evaluatePrepared, freshInstruction, ih]
    simpa only [Matrix.one_mul] using
      tensorGate_mul (preparedInstruction U B c) (evaluatePrepared U B cs)
        (1 : Matrix (FreshRegister H k) (FreshRegister H k) ℂ) 1

/-- Moving every instruction to the later registers tensors the evaluated word with the identity
on the first register. -/
theorem evaluateFresh_later (U B : Matrix H H ℂ) {k : ℕ} (cs : List (FreshStep H k)) :
    evaluateFresh U B (cs.map FreshStep.later) = TensorGate (1 : Matrix H H ℂ) (evaluateFresh U B cs) := by
  induction cs with
  | nil => simp [evaluateFresh, tensorGate_one]
  | cons c cs ih =>
    simp only [List.map_cons, evaluateFresh, freshInstruction, ih]
    simpa only [Matrix.one_mul] using tensorGate_mul (1 : Matrix H H ℂ) 1
      (freshInstruction U B c) (evaluateFresh U B cs)

/-- Evaluation of `k + 1` fresh copies is the tensor product of one prepared evaluation and the
evaluation of `k` fresh copies. -/
theorem evaluateFresh_compile_succ (U B : Matrix H H ℂ) (cs : List (PreparedStep H)) (k : ℕ) :
    evaluateFresh U B (compileFresh cs (k + 1)) =
      TensorGate (evaluatePrepared U B cs) (evaluateFresh U B (compileFresh cs k)) := by
  rw [compileFresh, evaluateFresh_append, evaluateFresh_first, evaluateFresh_later, tensorGate_mul]
  simp

/-- Compiling fresh copies of a valid prepared circuit gives a unitary matrix when the data and
input-preparation matrices are unitary. -/
theorem evaluateFresh_compile_unitary {U B : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hB : B ∈ Matrix.unitaryGroup H ℂ)
    {cs : List (PreparedStep H)} (hcs : PreparedCircuitValid cs) (k : ℕ) :
    evaluateFresh U B (compileFresh cs k) ∈ Matrix.unitaryGroup (FreshRegister H k) ℂ := by
  induction k with
  | zero => exact (Matrix.unitaryGroup _ ℂ).one_mem
  | succ k ih =>
    rw [evaluateFresh_compile_succ]
    exact tensorGate_unitary (hcs.evaluate_unitary hU hB) ih

/-- The tensor product of `k` copies of a state, with the one-point basis state for zero copies. -/
noncomputable def freshState (ψ : QState H) : (k : ℕ) → QState (FreshRegister H k)
  | 0 => Ket PUnit.unit
  | k + 1 => TensorState ψ (freshState ψ k)

/-- Running a freshly compiled circuit on the all-zero basis label produces the tensor product
of the individual prepared output states. -/
theorem evaluateFresh_apply_zero (U B : Matrix H H ℂ) (cs : List (PreparedStep H))
    (zero : H) (k : ℕ) :
    ApplyGate (evaluateFresh U B (compileFresh cs k)) (Ket (freshZero zero k)) =
      freshState (ApplyGate (evaluatePrepared U B cs) (Ket zero)) k := by
  induction k with
  | zero => simp [compileFresh, evaluateFresh, freshZero, freshState, applyGate_one]
  | succ k ih =>
    rw [evaluateFresh_compile_succ]
    change ApplyGate _ (Ket (zero, freshZero zero k)) = _
    rw [← tensorState_ket_ket, applyGate_tensorGate, ih]
    rfl

/-- A tensor product of any finite number of copies of a normalized state is normalized. -/
theorem freshState_normalized {ψ : QState H} (hψ : Normalized ψ) (k : ℕ) :
    Normalized (freshState ψ k) := by
  induction k with
  | zero => exact normalized_ket PUnit.unit
  | succ k ih => exact normalized_tensorState hψ ih

end CircuitSemantics

section ProjectiveLifts
variable {H K : Type*} [Fintype H] [Fintype K] [DecidableEq H] [DecidableEq K]

omit [Fintype H] [Fintype K] [DecidableEq H] [DecidableEq K] in

/-- Taking a tensor product with a fixed right matrix preserves subtraction in the left matrix. -/
private theorem tensorGate_sub_left (P Q : Matrix H H ℂ) (R : Matrix K K ℂ) :
    TensorGate (P - Q) R = TensorGate P R - TensorGate Q R := by
  ext ⟨i, j⟩ ⟨l, m⟩
  exact sub_mul _ _ _

omit [Fintype H] [Fintype K] [DecidableEq H] [DecidableEq K] in

/-- Taking a tensor product with a fixed left matrix preserves subtraction in the right matrix. -/
private theorem tensorGate_sub_right (P : Matrix H H ℂ) (Q R : Matrix K K ℂ) :
    TensorGate P (Q - R) = TensorGate P Q - TensorGate P R := by
  ext ⟨i, j⟩ ⟨l, m⟩
  exact mul_sub _ _ _

/-- The tensor product of two orthogonal projectors is an orthogonal projector. -/
theorem tensorProjector {P : Matrix H H ℂ} {Q : Matrix K K ℂ}
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q) :
    IsOrthogonalProjector (TensorGate P Q) := by
  have hp : P * P = P := hP.1
  have hq : Q * Q = Q := hQ.1
  have hp' : Pᴴ = P := hP.2
  have hq' : Qᴴ = Q := hQ.2
  constructor
  · change TensorGate P Q * TensorGate P Q = TensorGate P Q
    rw [tensorGate_mul, hp, hq]
  · change (TensorGate P Q)ᴴ = TensorGate P Q
    rw [tensorGate_conjTranspose, hp', hq']

/-- A projective branch acting on the left tensor factor affects only the left state. -/
theorem projectiveBranch_tensor_left (P : Matrix H H ℂ) (o : Bool)
    (ψ : QState H) (χ : QState K) :
    ProjectiveBranch (TensorGate P (1 : Matrix K K ℂ)) o (TensorState ψ χ) =
      TensorState (ProjectiveBranch P o ψ) χ := by
  cases o
  · have he : (1 : Matrix (H × K) (H × K) ℂ) - TensorGate P 1 = TensorGate (1 - P) 1 := by
      rw [tensorGate_sub_left, tensorGate_one]
    simp only [ProjectiveBranch, Bool.false_eq_true, ↓reduceIte, he]
    rw [applyGate_tensorGate, applyGate_one]
  · simp only [ProjectiveBranch, ↓reduceIte, applyGate_tensorGate, applyGate_one]

/-- A projective branch acting on the right tensor factor affects only the right state. -/
theorem projectiveBranch_tensor_right (P : Matrix K K ℂ) (o : Bool)
    (ψ : QState H) (χ : QState K) :
    ProjectiveBranch (TensorGate (1 : Matrix H H ℂ) P) o (TensorState ψ χ) =
      TensorState ψ (ProjectiveBranch P o χ) := by
  cases o
  · have he : (1 : Matrix (H × K) (H × K) ℂ) - TensorGate 1 P = TensorGate 1 (1 - P) := by
      rw [tensorGate_sub_right, tensorGate_one]
    simp only [ProjectiveBranch, Bool.false_eq_true, ↓reduceIte, he]
    rw [applyGate_tensorGate, applyGate_one]
  · simp only [ProjectiveBranch, ↓reduceIte, applyGate_tensorGate, applyGate_one]

/-- A projective history lifted to the right tensor factor acts only on the right state. -/
theorem projectiveHistory_tensor_right (hs : List (Matrix K K ℂ × Bool))
    (ψ : QState H) (χ : QState K) :
    ProjectiveHistoryState (hs.map (fun h => (TensorGate (1 : Matrix H H ℂ) h.1, h.2)))
      (TensorState ψ χ) = TensorState ψ (ProjectiveHistoryState hs χ) := by
  induction hs generalizing χ with
  | nil => rfl
  | cons h hs ih =>
    simp only [List.map_cons, ProjectiveHistoryState, List.foldl_cons]
    rw [projectiveBranch_tensor_right]
    exact ih _

end ProjectiveLifts

/-- The nested product of `k` Boolean measurement outcomes. -/
abbrev FreshOutcomes (k : ℕ) := FreshRegister Bool k

/-- The fresh-outcome tuple in which every outcome is false. -/
def allFailed (k : ℕ) : FreshOutcomes k := freshZero false k

/-- The index of the first true fresh outcome, or `none` if no outcome is true. -/
def firstFreshSuccess : (k : ℕ) → FreshOutcomes k → Option (Fin k)
  | 0, _ => none
  | k + 1, (o, os) => if o then some 0 else (firstFreshSuccess k os).map Fin.succ

/-- The Boolean outcome at a specified index of a fresh-outcome tuple. -/
def freshOutcomeAt : {k : ℕ} → FreshOutcomes k → Fin k → Bool
  | _ + 1, (o, os), i => Fin.cases o (freshOutcomeAt os) i

/-- There is no first fresh success exactly when every fresh outcome is false. -/
theorem firstFreshSuccess_none (k : ℕ) (os : FreshOutcomes k) :
    firstFreshSuccess k os = none ↔ os = allFailed k := by
  induction k with
  | zero => cases os; simp [firstFreshSuccess, allFailed, freshZero]
  | succ k ih =>
    rcases os with ⟨o, os⟩
    cases o
    · change (firstFreshSuccess k os).map Fin.succ = none ↔ (false, os) = (false, allFailed k)
      rw [Option.map_eq_none_iff, ih]
      exact ⟨fun h => by rw [h], fun h => congrArg Prod.snd h⟩
    · change some (0 : Fin (k + 1)) = none ↔ (true, os) = (false, allFailed k)
      constructor
      · intro h; cases h
      · intro h
        have he := congrArg Prod.fst h
        cases he

/-- The outcome at the index returned by `firstFreshSuccess` is true. -/
theorem firstFreshSuccess_true {k : ℕ} {os : FreshOutcomes k} {i : Fin k}
    (h : firstFreshSuccess k os = some i) : freshOutcomeAt os i = true := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    rcases os with ⟨o, os⟩
    cases o
    · simp only [firstFreshSuccess, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨j, hj, rfl⟩ := h
      exact ih hj
    · simp only [firstFreshSuccess, ↓reduceIte, Option.some.injEq] at h
      subst i
      rfl

/-- The identity matrix on a finite register is an orthogonal projector. -/
private theorem fresh_identity_projector (K : Type*) [Fintype K] [DecidableEq K] :
    IsOrthogonalProjector (1 : Matrix K K ℂ) := by
  constructor
  · change (1 : Matrix K K ℂ) * 1 = 1
    simp
  · change (1 : Matrix K K ℂ)ᴴ = 1
    simp

section Histories
variable {H : Type*} [Fintype H] [DecidableEq H]

/-- The sequence measuring `P` on each fresh register with the prescribed Boolean outcomes. -/
noncomputable def freshProjectiveHistory (P : Matrix H H ℂ) :
    (k : ℕ) → FreshOutcomes k → List (Matrix (FreshRegister H k) (FreshRegister H k) ℂ × Bool)
  | 0, _ => []
  | k + 1, (o, os) => (TensorGate P 1, o) ::
      (freshProjectiveHistory P k os).map (fun h => (TensorGate 1 h.1, h.2))

/-- The tensor product of the unnormalized projective branch states associated with a
fresh-outcome tuple. -/
noncomputable def freshOutcomeState (P : Matrix H H ℂ) (ψ : QState H) :
    (k : ℕ) → FreshOutcomes k → QState (FreshRegister H k)
  | 0, _ => Ket PUnit.unit
  | k + 1, (o, os) => TensorState (ProjectiveBranch P o ψ) (freshOutcomeState P ψ k os)

/-- Applying the fresh projective history to a repeated tensor state gives the tensor product of
its individual branch states. -/
theorem freshHistory_state (P : Matrix H H ℂ) (ψ : QState H) (k : ℕ) (os : FreshOutcomes k) :
    ProjectiveHistoryState (freshProjectiveHistory P k os) (freshState ψ k) =
      freshOutcomeState P ψ k os := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rcases os with ⟨o, os⟩
    simp only [freshProjectiveHistory, freshState, ProjectiveHistoryState, List.foldl_cons]
    rw [projectiveBranch_tensor_left]
    change ProjectiveHistoryState _ _ = _
    rw [projectiveHistory_tensor_right, ih]
    rfl

/-- Every matrix in a fresh projective history is an orthogonal projector when `P` is an
orthogonal projector. -/
theorem freshHistory_valid {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P)
    (k : ℕ) (os : FreshOutcomes k) :
    ∀ h ∈ freshProjectiveHistory P k os, IsOrthogonalProjector h.1 := by
  induction k with
  | zero => simp [freshProjectiveHistory]
  | succ k ih =>
    rcases os with ⟨o, os⟩
    intro h hh
    rcases List.mem_cons.mp hh with rfl | hh
    · exact tensorProjector hP (fresh_identity_projector _)
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hh
      exact tensorProjector (fresh_identity_projector _) (ih os g hg)

/-- The Born mass of the projective history for a specified outcome tuple on a repeated tensor
state. -/
noncomputable def freshHistoryMass (P : Matrix H H ℂ) (ψ : QState H)
    (k : ℕ) (os : FreshOutcomes k) : ℝ :=
  ProjectiveHistoryMass (freshProjectiveHistory P k os) (freshState ψ k)

/-- Every fresh projective-history mass is nonnegative. -/
theorem freshHistoryMass_nonneg (P : Matrix H H ℂ) (ψ : QState H)
    (k : ℕ) (os : FreshOutcomes k) : 0 ≤ freshHistoryMass P ψ k os := measureProb_nonneg _ _

/-- The mass of a fresh history with a leading outcome is the mass of that single branch times
the remaining history mass. -/
theorem freshHistoryMass_succ (P : Matrix H H ℂ) (ψ : QState H)
    (k : ℕ) (o : Bool) (os : FreshOutcomes k) :
    freshHistoryMass P ψ (k + 1) (o, os) =
      ProjectiveBranchMass P o ψ * freshHistoryMass P ψ k os := by
  unfold freshHistoryMass ProjectiveHistoryMass
  rw [freshHistory_state, freshHistory_state]
  change MeasureProb (TensorState (ProjectiveBranch P o ψ) (freshOutcomeState P ψ k os)) _ = _
  simpa only [Finset.univ_product_univ] using!
    measureProb_tensorState_prod (ProjectiveBranch P o ψ) (freshOutcomeState P ψ k os)
      Finset.univ Finset.univ

/-- The mass of the empty fresh history is one. -/
@[simp] theorem freshHistoryMass_zero (P : Matrix H H ℂ) (ψ : QState H) (os : FreshOutcomes 0) :
    freshHistoryMass P ψ 0 os = 1 := by
  exact measureProb_univ (normalized_ket PUnit.unit)

/-- The mass of a fresh history is the product of its individual projective branch masses. -/
theorem freshHistoryMass_eq_prod (P : Matrix H H ℂ) (ψ : QState H)
    (k : ℕ) (os : FreshOutcomes k) :
    freshHistoryMass P ψ k os = ∏ i : Fin k, ProjectiveBranchMass P (freshOutcomeAt os i) ψ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rcases os with ⟨o, os⟩
    rw [freshHistoryMass_succ, Fin.prod_univ_succ, ih]
    rfl

/-- The mass of the all-failure outcome tuple is the single-trial failure mass raised to the
number of trials. -/
theorem freshHistoryMass_allFailed (P : Matrix H H ℂ) (ψ : QState H) (k : ℕ) :
    freshHistoryMass P ψ k (allFailed k) = ProjectiveBranchMass P false ψ ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    change freshHistoryMass P ψ (k + 1) (false, allFailed k) = _
    rw [freshHistoryMass_succ, ih, pow_succ]
    ring

/-- For an orthogonal projector and normalized input state, the fresh-history masses sum to one
over all outcome tuples. -/
theorem freshHistoryMass_sum {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P)
    {ψ : QState H} (hψ : Normalized ψ) (k : ℕ) :
    ∑ os : FreshOutcomes k, freshHistoryMass P ψ k os = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    change ∑ os : Bool × FreshOutcomes k, freshHistoryMass P ψ (k + 1) os = 1
    simp only [Fintype.sum_prod_type, freshHistoryMass_succ, ← Finset.mul_sum, ih, mul_one,
      Fintype.sum_bool]
    have he := projectiveBranchMass_add hP ψ
    rw [measureProb_univ hψ] at he
    linarith

/-- The probability mass function on fresh outcomes obtained from projective-history masses for
an orthogonal projector and normalized input. -/
noncomputable def freshMeasurementLaw {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P)
    {ψ : QState H} (hψ : Normalized ψ) (k : ℕ) : PMF (FreshOutcomes k) :=
  PMF.ofFintype (fun os => ENNReal.ofReal (freshHistoryMass P ψ k os)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun os _ => freshHistoryMass_nonneg P ψ k os),
      freshHistoryMass_sum hP hψ, ENNReal.ofReal_one])

/-- The probability assigned to an outcome tuple is `ENNReal.ofReal` of its fresh-history mass. -/
theorem freshMeasurementLaw_apply {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P)
    {ψ : QState H} (hψ : Normalized ψ) (k : ℕ) (os : FreshOutcomes k) :
    freshMeasurementLaw hP hψ k os = ENNReal.ofReal (freshHistoryMass P ψ k os) := rfl

/-- The optional conditional state from the first successful fresh outcome, with no state
selected when no success occurs. -/
noncomputable def selectedFreshState (P : Matrix H H ℂ) (ψ : QState H)
    (k : ℕ) (os : FreshOutcomes k) : Option (QState H) :=
  (firstFreshSuccess k os).bind (fun i => ProjectiveConditionalState P (freshOutcomeAt os i) ψ)

/-- If a successful projective branch has conditional state `φ` and the outcome tuple contains a
first success, the selected fresh state is `φ`. -/
theorem selectedFreshState_eq {P : Matrix H H ℂ} {ψ φ : QState H}
    (hφ : ProjectiveConditionalState P true ψ = some φ) {k : ℕ} {os : FreshOutcomes k}
    {i : Fin k} (hi : firstFreshSuccess k os = some i) :
    selectedFreshState P ψ k os = some φ := by
  rw [selectedFreshState, hi, Option.bind_some, firstFreshSuccess_true hi]
  exact hφ

/-- The measurement-history mass after a freshly compiled prepared circuit equals the
fresh-history mass formed from its single-trial output state. -/
theorem preparedFresh_history_mass (U B : Matrix H H ℂ) (cs : List (PreparedStep H))
    (zero : H) (P : Matrix H H ℂ) (k : ℕ) (os : FreshOutcomes k) :
    ProjectiveHistoryMass (freshProjectiveHistory P k os)
      (ApplyGate (evaluateFresh U B (compileFresh cs k)) (Ket (freshZero zero k))) =
      freshHistoryMass P (ApplyGate (evaluatePrepared U B cs) (Ket zero)) k os := by
  rw [evaluateFresh_apply_zero]
  rfl

end Histories
end Qatlib.Concepts.HhlAlgorithms.Postselection

namespace Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing

set_option autoImplicit false

/-- Compile an indexed family of prepared circuits onto separate fresh registers, assigning one
circuit to each register. -/
noncomputable def compileFreshFamily {H : Type*} :
    (n : ℕ) → (Fin n → List (PreparedStep H)) → List (FreshStep H n)
  | 0, _ => []
  | n + 1, cs => (cs 0).map FreshStep.first ++
      (compileFreshFamily n (fun i => cs i.succ)).map FreshStep.later

/-- The data-query, input-query, and fixed-gate counts of a compiled family are the sums of the
corresponding component counts. -/
theorem compileFreshFamily_counts {H : Type*} (n : ℕ)
    (cs : Fin n → List (PreparedStep H)) :
    freshDataQueries (compileFreshFamily n cs) = ∑ i, preparedDataQueries (cs i) ∧
    freshInputQueries (compileFreshFamily n cs) = ∑ i, preparedInputQueries (cs i) ∧
    freshFixedGates (compileFreshFamily n cs) = ∑ i, preparedFixedGates (cs i) := by
  induction n with
  | zero => simp [compileFreshFamily, freshDataQueries, freshInputQueries,
      freshFixedGates, preparedDataQueries, preparedInputQueries, preparedFixedGates]
  | succ n ih =>
    have hm : (compileFreshFamily (n + 1) cs).map FreshStep.source =
        cs 0 ++ (compileFreshFamily n (fun i => cs i.succ)).map FreshStep.source := by
      simp [compileFreshFamily, List.map_map, Function.comp_def, FreshStep.source]
    have ht := ih (fun i => cs i.succ)
    unfold freshDataQueries freshInputQueries freshFixedGates at ht ⊢
    rw [hm]
    rcases preparedCounts_append (cs 0)
      ((compileFreshFamily n (fun i => cs i.succ)).map FreshStep.source) with ⟨hu, hb, hg⟩
    exact ⟨by rw [hu, ht.1, Fin.sum_univ_succ],
      by rw [hb, ht.2.1, Fin.sum_univ_succ],
      by rw [hg, ht.2.2, Fin.sum_univ_succ]⟩

/-- Every instruction in a compiled fresh family comes from one of the component prepared
circuits. -/
theorem compileFreshFamily_source {H : Type*} (n : ℕ)
    (cs : Fin n → List (PreparedStep H)) :
    ∀ s ∈ compileFreshFamily n cs, ∃ i, s.source ∈ cs i := by
  induction n with
  | zero => simp [compileFreshFamily]
  | succ n ih =>
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
      exact ⟨0, hc⟩
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
      obtain ⟨i, hi⟩ := ih (fun i => cs i.succ) c hc
      exact ⟨i.succ, hi⟩

section FreshFamilies
variable {H : Type*} [Fintype H] [DecidableEq H]

/-- The evaluated compiled family splits as the tensor product of the first circuit evaluation
and the evaluated remaining family. -/
theorem evaluateFreshFamily_succ (U B : Matrix H H ℂ) (n : ℕ)
    (cs : Fin (n + 1) → List (PreparedStep H)) :
    evaluateFresh U B (compileFreshFamily (n + 1) cs) =
      TensorGate (evaluatePrepared U B (cs 0))
        (evaluateFresh U B (compileFreshFamily n (fun i => cs i.succ))) := by
  rw [compileFreshFamily, evaluateFresh_append, evaluateFresh_first,
    evaluateFresh_later, tensorGate_mul]
  simp

/-- The tensor product of an indexed family of states, with the one-point basis state for an
empty family. -/
noncomputable def familyState : (n : ℕ) → (Fin n → QState H) → QState (FreshRegister H n)
  | 0, _ => Ket PUnit.unit
  | n + 1, psi => TensorState (psi 0) (familyState n (fun i => psi i.succ))

/-- A compiled family acting on the all-zero basis label produces the tensor product of the
individual prepared output states. -/
theorem evaluateFreshFamily_apply_zero (U B : Matrix H H ℂ) (n : ℕ)
    (cs : Fin n → List (PreparedStep H)) (zero : H) :
    ApplyGate (evaluateFresh U B (compileFreshFamily n cs)) (Ket (freshZero zero n)) =
      familyState n (fun i => ApplyGate (evaluatePrepared U B (cs i)) (Ket zero)) := by
  induction n with
  | zero => simp [compileFreshFamily, evaluateFresh, freshZero, familyState, applyGate_one]
  | succ n ih =>
    rw [evaluateFreshFamily_succ]
    change ApplyGate _ (Ket (zero, freshZero zero n)) = _
    rw [← tensorState_ket_ket, applyGate_tensorGate, ih]
    rfl

/-- A compiled family of valid prepared circuits is unitary when the data and input-preparation
matrices are unitary. -/
theorem evaluateFreshFamily_unitary {U B : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hB : B ∈ Matrix.unitaryGroup H ℂ)
    (n : ℕ) (cs : Fin n → List (PreparedStep H))
    (hcs : ∀ i, PreparedCircuitValid (cs i)) :
    evaluateFresh U B (compileFreshFamily n cs) ∈ Matrix.unitaryGroup (FreshRegister H n) ℂ := by
  induction n with
  | zero => exact (Matrix.unitaryGroup _ ℂ).one_mem
  | succ n ih =>
    rw [evaluateFreshFamily_succ]
    exact tensorGate_unitary ((hcs 0).evaluate_unitary hU hB)
      (ih (fun i => cs i.succ) (fun i => hcs i.succ))

/-- The tensor product of the component binary Kraus matrices selected by a fresh-outcome tuple. -/
noncomputable def freshFamilyKraus : (n : ℕ) →
    (Fin n → Bool → Matrix H H ℂ) → FreshOutcomes n →
      Matrix (FreshRegister H n) (FreshRegister H n) ℂ
  | 0, _, _ => 1
  | n + 1, K, (b, bs) => TensorGate (K 0 b)
      (freshFamilyKraus n (fun i => K i.succ) bs)

/-- The tensor family Kraus matrix acts componentwise on a tensor family of states. -/
theorem freshFamilyKraus_apply (n : ℕ) (K : Fin n → Bool → Matrix H H ℂ)
    (psi : Fin n → QState H) (os : FreshOutcomes n) :
    ApplyGate (freshFamilyKraus n K os) (familyState n psi) =
      familyState n (fun i => ApplyGate (K i (freshOutcomeAt os i)) (psi i)) := by
  induction n with
  | zero => simp [freshFamilyKraus, familyState, applyGate_one]
  | succ n ih =>
    rcases os with ⟨b, bs⟩
    simp only [freshFamilyKraus, familyState]
    rw [applyGate_tensorGate, ih]
    rfl

/-- The total Born mass of a tensor family state is the product of the total masses of its
component states. -/
theorem familyState_mass (n : ℕ) (psi : Fin n → QState H) :
    MeasureProb (familyState n psi) Finset.univ =
      ∏ i, MeasureProb (psi i) Finset.univ := by
  induction n with
  | zero =>
    change MeasureProb (Ket PUnit.unit) Finset.univ = 1
    exact measureProb_univ (normalized_ket PUnit.unit)
  | succ n ih =>
    rw [familyState, Fin.prod_univ_succ]
    calc
      _ = MeasureProb (psi 0) Finset.univ *
          MeasureProb (familyState n (fun i => psi i.succ)) Finset.univ := by
        simpa only [Finset.univ_product_univ] using
          measureProb_tensorState_prod (psi 0) (familyState n (fun i => psi i.succ))
            Finset.univ Finset.univ
      _ = _ := by rw [ih]

/-- The total Born mass after preparing a fresh circuit family and applying the Kraus matrices
selected by its outcome tuple. -/
noncomputable def freshFamilyMass (U B : Matrix H H ℂ) {n : ℕ}
    (cs : Fin n → List (PreparedStep H)) (zero : H)
    (K : Fin n → Bool → Matrix H H ℂ) (os : FreshOutcomes n) : ℝ :=
  MeasureProb (ApplyGate (freshFamilyKraus n K os)
    (ApplyGate (evaluateFresh U B (compileFreshFamily n cs)) (Ket (freshZero zero n))))
      Finset.univ

/-- The mass of a prepared fresh-family outcome is the product of the masses of its component
prepared Kraus branches. -/
theorem freshFamilyMass_eq_prod (U B : Matrix H H ℂ) (n : ℕ)
    (cs : Fin n → List (PreparedStep H)) (zero : H)
    (K : Fin n → Bool → Matrix H H ℂ) (os : FreshOutcomes n) :
    freshFamilyMass U B cs zero K os =
      ∏ i, MeasureProb (ApplyGate (K i (freshOutcomeAt os i))
        (ApplyGate (evaluatePrepared U B (cs i)) (Ket zero))) Finset.univ := by
  rw [freshFamilyMass, evaluateFreshFamily_apply_zero, freshFamilyKraus_apply, familyState_mass]

/-- Every prepared fresh-family outcome mass is nonnegative. -/
theorem freshFamilyMass_nonneg (U B : Matrix H H ℂ) {n : ℕ}
    (cs : Fin n → List (PreparedStep H)) (zero : H)
    (K : Fin n → Bool → Matrix H H ℂ) (os : FreshOutcomes n) :
    0 ≤ freshFamilyMass U B cs zero K os := measureProb_nonneg _ _

/-- If each binary Kraus family satisfies the completeness identity, the tensor family summed
over all fresh outcomes also satisfies that identity. -/
theorem freshFamilyKraus_complete (n : ℕ) (K : Fin n → Bool → Matrix H H ℂ)
    (hK : ∀ i, ∑ b, (K i b).conjTranspose * K i b = 1) :
    ∑ os, (freshFamilyKraus n K os).conjTranspose * freshFamilyKraus n K os = 1 := by
  induction n with
  | zero => simp [freshFamilyKraus]
  | succ n ih =>
    let L := freshFamilyKraus n (fun i => K i.succ)
    have hs : (∑ b : Bool, ∑ bs : FreshOutcomes n,
        TensorGate ((K 0 b).conjTranspose * K 0 b) ((L bs).conjTranspose * L bs)) =
        TensorGate (∑ b : Bool, (K 0 b).conjTranspose * K 0 b)
          (∑ bs : FreshOutcomes n, (L bs).conjTranspose * L bs) := by
      ext ⟨i, j⟩ ⟨k, l⟩
      simp [Matrix.sum_apply, tensorGate_apply, Finset.mul_sum, add_mul, Finset.sum_add_distrib]
    change (∑ os : Bool × FreshOutcomes n,
      (TensorGate (K 0 os.1) (L os.2)).conjTranspose *
        TensorGate (K 0 os.1) (L os.2)) = 1
    simp only [Fintype.sum_prod_type, tensorGate_conjTranspose, tensorGate_mul]
    rw [hs, hK 0, ih (fun i => K i.succ) (fun i => hK i.succ), tensorGate_one]

end FreshFamilies
end Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
