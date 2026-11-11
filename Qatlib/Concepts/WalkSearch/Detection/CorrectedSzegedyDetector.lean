/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.ProjectorCS
import Qatlib.Concepts.WalkSearch.Spectral.CompleteCSDecomposition
import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit

/-!
# Corrected Szegedy detector and resource bounds

`correctedMarkedWalk` is built from the unmarked row-frame reflection and register swaps. The
module defines a detector with control and marker flags, proves its unitary circuit semantics,
and computes exact row-access, marker, and fixed-gate counts.

The interference analysis gives zero acceptance for empty marked sets and constant average
acceptance over a sufficiently long range of positive walk powers under a symmetric-chain gap
assumption. The estimates formalize the detection mechanism of [Szegedy2004].

## Main statements

* `corrected_szegedy_actual_detector_and_counts`: unitary semantics and exact instruction
  counts.
* `corrected_szegedy_empty_mark_one_sided`: zero acceptance for empty marks.
* `corrected_szegedy_busy_random_power_difference`: average displacement of the unmarked state.
* `corrected_szegedy_actual_random_power_detection`: constant average success and resource
  bounds.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
namespace Qatlib.Concepts.WalkSearch.Detection
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.WalkSearch.CountedWalk
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open scoped Classical BigOperators Kronecker Matrix.Norms.L2Operator

/-- The constant state with amplitude equal to the reciprocal square root of the cardinality of
the finite index type. -/
noncomputable def chainUniform {I : Type} [Fintype I] : QState I :=
  fun _=>(Real.sqrt (Fintype.card I:ℝ):ℂ)⁻¹
/-- The detector's initial pair-register state, obtained by applying `SzegedyIsometry P` to
`chainUniform`. -/
noncomputable def detectionInitial {I : Type} [Fintype I] [DecidableEq I] (P : I→I→ℝ) :
    QState (I×I) := SzegedyIsometry P *ᵥ chainUniform
/-- The restriction of `detectionInitial P` to pairs whose first coordinate is unmarked, defined
using `Collapse`. -/
noncomputable def detectionUnmarkedInitial {I : Type} [Fintype I] [DecidableEq I]
    (P : I→I→ℝ) (S : Finset I) : QState (I×I) :=
  Collapse (detectionInitial P) {xy | xy.1∉S}
/-- The product `SwapGate * R * SwapGate * R`, where `R` is the reflection about the unmarked
row-frame projector. -/
noncomputable def correctedMarkedWalk {I : Type} [Fintype I] [DecidableEq I]
    (P : I→I→ℝ) (S : Finset I) : Matrix (I×I) (I×I) ℂ :=
  let F:= unmarkedRowFrame P S;
  let R:= ReflectionAbout (F*Fᴴ);
  SwapGate*R*SwapGate*R

/-- The detector state index consisting of a Boolean control flag, a Boolean marker flag, and
two walk-register indices. -/
abbrev DetectionSpace (I : Type) := Bool×(Bool×(I×I))
/-- The permutation that XORs membership of the first walk-register index in `S` into the marker
flag, preserving the other indices. -/
def detectionMarkPermutation {I : Type} [DecidableEq I] (S : Finset I)
    (v : DetectionSpace I) : DetectionSpace I :=
  (v.1,(v.2.1 ^^ decide (v.2.2.1∈S),v.2.2))
/-- The permutation matrix implementing `detectionMarkPermutation S` on the detector state
space. -/
noncomputable def detectionMarkGate {I : Type} [DecidableEq I] (S : Finset I) :
    Matrix (DetectionSpace I) (DetectionSpace I) ℂ := permMatrix (detectionMarkPermutation S)
/-- The diagonal gate that acts trivially when the control flag is false and, when it is true,
assigns sign 1 exactly to states with false marker flag and second walk register equal to
`j`. -/
noncomputable def detectionPhase {I : Type} [DecidableEq I] (j : I) :
    Matrix (DetectionSpace I) (DetectionSpace I) ℂ := diagonal (fun v=>
  if v.1 then if v.2.1= false ∧ v.2.2.2= j then 1 else -1 else 1)
/-- The gate that swaps the two walk registers when the control flag is true, while preserving
the marker flag. -/
noncomputable def detectionControlledSwap {I : Type} [DecidableEq I] :
    Matrix (DetectionSpace I) (DetectionSpace I) ℂ :=
  Qatlib.Concepts.BlockEncoding.LCU.select (fun b : Bool=> if b then (1:Matrix Bool Bool ℂ)⊗ₖ
    (SwapGate:Matrix (I×I) (I×I) ℂ) else 1)
/-- The Hadamard gate on the control flag tensored with the identity on the remaining detector
registers. -/
noncomputable def detectionHadamard {I : Type} [DecidableEq I] :
    Matrix (DetectionSpace I) (DetectionSpace I) ℂ := Hadamard⊗ₖ(1:Matrix (Bool×(I×I)) (Bool×(I×I)) ℂ)
/-- The detector instruction type, with constructors for controlled forward and adjoint row
access, initial row preparation, marking, and a specified fixed gate. -/
inductive DetectionStep (I : Type) where
  | rowForward | rowBackward | rowInitial | marker
  | fixed : Matrix (DetectionSpace I) (DetectionSpace I) ℂ → DetectionStep I
/-- The matrix interpretation of a detector instruction using row-access matrix `U`, its
adjoint, the marker gate for `S`, or the specified fixed gate. -/
noncomputable def detectionInstruction {I : Type} [DecidableEq I] (U : Matrix (I×I) (I×I) ℂ)
    (S : Finset I) : DetectionStep I→Matrix (DetectionSpace I) (DetectionSpace I) ℂ
  | .rowForward => select (fun b : Bool=> if b then (1:Matrix Bool Bool ℂ)⊗ₖU else 1)
  | .rowBackward => select (fun b : Bool=> if b then (1:Matrix Bool Bool ℂ)⊗ₖUᴴ else 1)
  | .rowInitial => (1:Matrix Bool Bool ℂ)⊗ₖ((1:Matrix Bool Bool ℂ)⊗ₖU)
  | .marker => detectionMarkGate S
  | .fixed V => V
/-- The ordered matrix product interpreting a list of detector instructions, with the empty list
evaluated as the identity. -/
noncomputable def detectionEvaluate {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix (I×I) (I×I) ℂ) (S : Finset I) :
    List (DetectionStep I)→Matrix (DetectionSpace I) (DetectionSpace I) ℂ
  | [] => 1
  | s::ss => detectionInstruction U S s*detectionEvaluate U S ss
/-- The triple counting row-access instructions, marker instructions, and fixed-gate
instructions in a detector word. -/
def detectionCounts {I : Type} : List (DetectionStep I)→ℕ×ℕ×ℕ
  | [] => (0,0,0)
  | s::ss => let c:= detectionCounts ss; match s with
    | .rowForward | .rowBackward | .rowInitial => (c.1+1,c.2.1,c.2.2)
    | .marker => (c.1,c.2.1+1,c.2.2)
    | .fixed _ => (c.1,c.2.1,c.2.2+1)
/-- The instruction word implementing the controlled unmarked reflection using row access, two
marker calls, and the anchor-dependent phase gate. -/
noncomputable def detectionReflectionWord {I : Type} [DecidableEq I] (j : I) : List (DetectionStep I) :=
  [.rowForward,.marker,.fixed (detectionPhase j),.marker,.rowBackward]
/-- The detector walk word built from two controlled swaps and two copies of
`detectionReflectionWord j`. -/
noncomputable def detectionWalkWord {I : Type} [DecidableEq I] (j : I) : List (DetectionStep I) :=
  [.fixed detectionControlledSwap]++detectionReflectionWord j++
    [.fixed detectionControlledSwap]++detectionReflectionWord j
/-- The detector word combining initial row preparation, Hadamard interference around `K` walk
words, and a final marker call. -/
noncomputable def detectionProgram {I : Type} [DecidableEq I] (j : I) (K : ℕ) : List (DetectionStep I) :=
  [.marker,.fixed detectionHadamard]++(List.replicate K (detectionWalkWord j)).flatten++
    [.fixed detectionHadamard,.rowInitial]
/-- The initial detector state with both flags false, second walk register fixed at `j`, and
first walk register in `chainUniform`. -/
noncomputable def detectionStart {I : Type} [Fintype I] [DecidableEq I] (j : I) : QState (DetectionSpace I) :=
  fun v=> if v.1= false ∧ v.2.1= false ∧ v.2.2.2= j then chainUniform v.2.2.1 else 0
/-- The state with marker flag false and control branches `(u + W ^ K *ᵥ u) / 2` and `(u - W ^ K
*ᵥ u) / 2`. -/
noncomputable def detectionInterference {I : Type} [Fintype I] [DecidableEq I]
    (W : Matrix (I×I) (I×I) ℂ) (u : QState (I×I)) (K : ℕ) : QState (DetectionSpace I) :=
  fun v=> if v.2.1 then 0 else if v.1 then (u v.2.2-(W^K*ᵥu) v.2.2)/2
    else (u v.2.2+(W^K*ᵥu) v.2.2)/2
/-- The accepting detector indices for which either the control flag or the marker flag is true. -/
noncomputable def detectionAccept {I : Type} [Fintype I] : Finset (DetectionSpace I) :=
  {v | v.1= true ∨ v.2.1= true}
/-- The measurement weight of `detectionAccept` after applying the evaluated detector program to
`detectionStart j`. -/
noncomputable def detectionProbability {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix (I×I) (I×I) ℂ) (S : Finset I) (j : I) (K : ℕ) : ℝ :=
  MeasureProb (detectionEvaluate U S (detectionProgram j K)*ᵥdetectionStart j) detectionAccept

/-- Concatenating detector instruction lists adds their three resource counts componentwise. -/
private theorem detectionCounts_append {I : Type} (xs ys : List (DetectionStep I)) :
    detectionCounts (xs++ys)=((detectionCounts xs).1+(detectionCounts ys).1,
      (detectionCounts xs).2.1+(detectionCounts ys).2.1,(detectionCounts xs).2.2+(detectionCounts ys).2.2) := by
  induction xs with
  | nil => simp [detectionCounts]
  | cons x xs ih => cases x <;> simp [detectionCounts,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- Concatenating `K` copies of a detector word multiplies each of its three resource counts by
`K`. -/
private theorem detectionCounts_replicate {I : Type} (xs : List (DetectionStep I)) (K : ℕ) :
    detectionCounts (List.replicate K xs).flatten=(K*(detectionCounts xs).1,
      K*(detectionCounts xs).2.1,K*(detectionCounts xs).2.2) := by
  induction K with
  | zero => simp [detectionCounts]
  | succ K ih => simp [List.replicate_succ,detectionCounts_append,ih,Nat.add_mul,Nat.add_comm,Nat.add_left_comm]

/-- The power-`K` detector program has `4 * K + 1` row-access instructions, `4 * K + 1` marker
instructions, and `4 * K + 2` fixed gates. -/
theorem detectionProgram_actual_counts {I : Type} [DecidableEq I] (j : I) (K : ℕ) :
    detectionCounts (detectionProgram j K)=(4*K+1,4*K+1,4*K+2) := by
  simp [detectionProgram,detectionCounts_append,detectionCounts_replicate,detectionWalkWord,
    detectionReflectionWord,detectionCounts]
  simp [Nat.mul_comm]

/-- Applying the marker permutation twice returns the original detector index. -/
theorem detectionMarkPermutation_involutive {I : Type} [DecidableEq I] (S : Finset I) :
    Function.Involutive (detectionMarkPermutation S) := by
  intro v
  rcases v with ⟨b,c,i,j⟩
  cases c <;> by_cases h : i∈S <;> simp [detectionMarkPermutation,h]

/-- The detector marker gate is unitary. -/
theorem detectionMarkGate_unitary {I : Type} [Fintype I] [DecidableEq I] (S : Finset I) :
    detectionMarkGate S∈unitaryGroup (DetectionSpace I) ℂ := permMatrix_unitary (detectionMarkPermutation_involutive S)

/-- The controlled forward row-access instruction is unitary whenever `U` is unitary. -/
theorem detectionRowForward_unitary {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix (I×I) (I×I) ℂ) (S : Finset I) (hU : U∈unitaryGroup (I×I) ℂ) :
    detectionInstruction U S .rowForward∈unitaryGroup (DetectionSpace I) ℂ := by
  apply Qatlib.Concepts.BlockEncoding.LCU.select_unitary
  intro b
  cases b
  · exact (unitaryGroup _ _).one_mem
  · exact tensorGate_unitary ((unitaryGroup _ _).one_mem) hU

/-- The anchor-dependent detector phase gate is unitary. -/
theorem detectionPhase_unitary {I : Type} [Fintype I] [DecidableEq I] (j : I) :
    detectionPhase j∈unitaryGroup (DetectionSpace I) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
  unfold detectionPhase
  rw [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
  ext v w
  by_cases hv : v.1
  · by_cases h : v.2.1=false ∧ v.2.2.2=j <;> simp [Matrix.diagonal_apply,Matrix.one_apply,hv,h]
  · simp [Matrix.diagonal_apply,Matrix.one_apply,hv]

/-- The detector's controlled swap gate is unitary. -/
theorem detectionControlledSwap_unitary {I : Type} [Fintype I] [DecidableEq I] :
    (detectionControlledSwap : Matrix (DetectionSpace I) (DetectionSpace I) ℂ)∈
      unitaryGroup (DetectionSpace I) ℂ := by
  apply Qatlib.Concepts.BlockEncoding.LCU.select_unitary
  intro b
  cases b
  · exact (unitaryGroup _ _).one_mem
  · exact tensorGate_unitary ((unitaryGroup _ _).one_mem) swapGate_unitary

/-- A detector word evaluates to a unitary matrix if the matrix interpretation of every
instruction in the word is unitary. -/
private theorem detectionEvaluate_unitary {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix (I×I) (I×I) ℂ) (S : Finset I) (xs : List (DetectionStep I))
    (h : ∀ x∈xs,detectionInstruction U S x∈unitaryGroup (DetectionSpace I) ℂ) :
    detectionEvaluate U S xs∈unitaryGroup (DetectionSpace I) ℂ := by
  induction xs with
  | nil => exact (unitaryGroup _ _).one_mem
  | cons x xs ih =>
    exact (unitaryGroup _ _).mul_mem (h x (by simp)) (ih (by intro y hy; exact h y (by simp [hy])))

/-- For unitary row access `U`, the full detector program evaluates to a unitary matrix for
every anchor, marked set, and power. -/
theorem detectionProgram_unitary {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix (I×I) (I×I) ℂ) (S : Finset I) (j : I) (K : ℕ)
    (hU : U∈unitaryGroup (I×I) ℂ) :
    detectionEvaluate U S (detectionProgram j K)∈unitaryGroup (DetectionSpace I) ℂ := by
  apply detectionEvaluate_unitary
  intro x hx
  have hmem : x∈[DetectionStep.rowForward, .rowBackward, .rowInitial, .marker,
      .fixed (detectionPhase j), .fixed detectionControlledSwap, .fixed detectionHadamard] := by
    simp [detectionProgram,detectionWalkWord,detectionReflectionWord,List.mem_flatten,
      List.mem_replicate] at hx ⊢
    aesop
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact detectionRowForward_unitary U S hU
  · exact detectionRowForward_unitary Uᴴ S (adjoint_unitary hU)
  · exact tensorGate_unitary ((unitaryGroup _ _).one_mem)
      (tensorGate_unitary ((unitaryGroup _ _).one_mem) hU)
  · exact detectionMarkGate_unitary S
  · exact detectionPhase_unitary j
  · exact detectionControlledSwap_unitary
  · exact tensorGate_unitary hadamard_unitary ((unitaryGroup _ _).one_mem)

/-- The initial amplitude at `(x, y)` equals `sqrt (P x y)` times the uniform amplitude at `x`. -/
theorem detectionInitial_apply {I : Type} [Fintype I] [DecidableEq I]
    (P : I→I→ℝ) (xy : I×I) :
    detectionInitial P xy=(Real.sqrt (P xy.1 xy.2):ℂ)*chainUniform xy.1 := by
  simp [detectionInitial,Matrix.mulVec,dotProduct,SzegedyIsometry,ite_mul]

/-- For a transition matrix on a nonempty finite type, the unmarked initial state's squared
Euclidean norm is `1 - markedFraction S`. -/
theorem detectionUnmarkedInitial_norm_sq {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I→I→ℝ) (S : Finset I) (hP : IsTransitionMatrix P) :
    ‖toEuclidean_fromVec (detectionUnmarkedInitial P S)‖^2=1-markedFraction S := by
  have hn : (0:ℝ)<Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hc : ∀ i : I,‖chainUniform (I:=I) i‖^2=(Fintype.card I:ℝ)⁻¹ := by
    intro i
    simp only [chainUniform,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),inv_pow,Real.sq_sqrt hn.le]
  rw [norm_toEuclidean_fromVec_sq,Fintype.sum_prod_type]
  have hrow : ∀ i : I,(∑ j : I,‖detectionUnmarkedInitial P S (i,j)‖^2)=
      if i∉S then (Fintype.card I:ℝ)⁻¹ else 0 := by
    intro i
    simp only [detectionUnmarkedInitial,collapse_apply,Finset.mem_filter,Finset.mem_univ,
      true_and,detectionInitial_apply]
    by_cases hi : i∉S
    · simp only [hi,not_false_eq_true,if_true,norm_mul,mul_pow,hc,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      simp_rw [Real.sq_sqrt (hP.1 i _)]
      rw [← Finset.sum_mul,hP.2,one_mul]
    · simp [hi]
  simp_rw [hrow]
  have hs : (∑ i : I,if i∉S then (Fintype.card I:ℝ)⁻¹ else 0)=
      ((Fintype.card I:ℝ)-(S.card:ℝ))*(Fintype.card I:ℝ)⁻¹ := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
    congr 1
    have he : Finset.univ.filter (fun i : I=>i∉S)=Finset.univ\S := by ext i; simp
    rw [he,Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,
      Nat.cast_sub S.card_le_univ]
  rw [hs]
  unfold markedFraction
  field_simp

/-- The detector state with marker flag false and control-branch amplitudes supplied by `f`. -/
noncomputable def detectionCleanState {I : Type} (f : Bool → QState (I×I)) :
    QState (DetectionSpace I) := fun v => if v.2.1 then 0 else f v.1 v.2.2

/-- Controlled application of `A` to a clean detector state applies `A` to the true-control
branch and preserves the false-control branch. -/
private theorem detection_select_clean {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix (I×I) (I×I) ℂ) (f : Bool → QState (I×I)) :
    select (fun b : Bool => if b then (1 : Matrix Bool Bool ℂ)⊗ₖA else 1) *ᵥ
      detectionCleanState f =
    detectionCleanState (fun b => if b then A *ᵥ f true else f false) := by
  funext v
  rcases v with ⟨b,c,x,y⟩
  cases b <;> cases c <;>
    simp [select,detectionCleanState,Matrix.mulVec,dotProduct,
      Fintype.sum_prod_type,Matrix.kroneckerMap,Matrix.one_apply,ite_mul,ite_and]

/-- Uncontrolled application of `A` on the walk registers applies `A` to both control branches
of a clean detector state. -/
private theorem detection_row_initial_clean {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix (I×I) (I×I) ℂ) (f : Bool → QState (I×I)) :
    ((1 : Matrix Bool Bool ℂ)⊗ₖ((1 : Matrix Bool Bool ℂ)⊗ₖA)) *ᵥ
      detectionCleanState f = detectionCleanState (fun b => A *ᵥ f b) := by
  funext v
  rcases v with ⟨b,c,x,y⟩
  cases b <;> cases c <;>
    simp [detectionCleanState,Matrix.mulVec,dotProduct,
      Fintype.sum_prod_type,Matrix.kroneckerMap,Matrix.one_apply,ite_mul,ite_and]

/-- The detector Hadamard maps clean branch amplitudes to their normalized sum and difference. -/
private theorem detection_hadamard_clean {I : Type} [Fintype I] [DecidableEq I]
    (f : Bool → QState (I×I)) :
    detectionHadamard *ᵥ detectionCleanState f =
      detectionCleanState (fun b => (Real.sqrt 2 : ℂ)⁻¹ •
        (if b then f false-f true else f false+f true)) := by
  funext v
  rcases v with ⟨b,c,x,y⟩
  cases b <;> cases c <;>
    simp [detectionHadamard,detectionCleanState,Hadamard,Matrix.mulVec,dotProduct,
      Fintype.sum_prod_type,Matrix.kroneckerMap,Matrix.one_apply,ite_mul,ite_and] <;> ring

/-- On a clean state, conjugating the detector phase by the marker gate applies the diagonal
unmarked-anchor reflection to the true-control branch and preserves the false-control
branch. -/
private theorem detection_marker_phase_clean {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (j : I) (f : Bool → QState (I×I)) :
    detectionMarkGate S *ᵥ (detectionPhase j *ᵥ
      (detectionMarkGate S *ᵥ detectionCleanState f)) =
    detectionCleanState (fun b => if b then
      (diagonal (fun xy : I×I => if xy.1∉S ∧ xy.2=j then (1:ℂ) else -1)) *ᵥ f true
      else f false) := by
  funext v
  rw [show (detectionMarkGate S *ᵥ _ ) v = _ from
    applyGate_permMatrix (detectionMarkPermutation_involutive S) _ v]
  rw [detectionPhase,Matrix.mulVec_diagonal]
  rw [show (detectionMarkGate S *ᵥ _ ) (detectionMarkPermutation S v) = _ from
    applyGate_permMatrix (detectionMarkPermutation_involutive S) _ _]
  rw [detectionMarkPermutation_involutive S v]
  rcases v with ⟨b,c,x,y⟩
  cases b <;> cases c <;> by_cases hx : x∈S <;> by_cases hy : y=j <;>
    simp [detectionCleanState,detectionMarkPermutation,hx,hy,Matrix.mulVec_diagonal]

/-- The basis embedding of unmarked indices into pair states with second coordinate fixed at the
anchor `j`. -/
private noncomputable def detectionSourceFrame {I : Type} [DecidableEq I]
    (S : Finset I) (j : I) : Matrix (I×I) (Unmarked I S) ℂ :=
  fun xy i => if xy=(i.1,j) then 1 else 0

/-- The source-frame projector is the diagonal indicator of pairs with unmarked first coordinate
and second coordinate equal to `j`. -/
private theorem detection_source_projector {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (j : I) :
    detectionSourceFrame S j * (detectionSourceFrame S j)ᴴ =
      diagonal (fun xy : I×I => if xy.1∉S ∧ xy.2=j then (1:ℂ) else 0) := by
  ext xy zw
  rcases xy with ⟨x,y⟩
  rcases zw with ⟨z,w⟩
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,detectionSourceFrame]
  have hs := Finset.sum_subtype (F:=inferInstance) (p:=fun i : I => i∉S)
    (Finset.univ.filter (fun i => i∉S)) (by intro i; simp)
    (fun i => (if (x,y)=(i,j) then (1:ℂ) else 0) *
      star (if (z,w)=(i,j) then (1:ℂ) else 0))
  rw [← hs,Finset.sum_filter,Finset.sum_eq_single x]
  · by_cases hx : x∈S <;> by_cases hy : y=j <;> by_cases hz : x=z <;> by_cases hw : w=j <;>
      simp [Prod.mk.injEq,Matrix.diagonal_apply,hx,hy,hz,hw,eq_comm] <;> aesop
  · intro i _ hi
    simp [Prod.mk.injEq,Ne.symm hi]
  · simp

/-- For a unitary row preparation, conjugating the diagonal unmarked-anchor reflection by `U`
yields the reflection about the unmarked row-frame projector. -/
theorem detection_prepared_unmarked_reflection {I : Type} [Fintype I] [DecidableEq I]
    (P : I→I→ℝ) (S : Finset I) (j : I) (U : Matrix (I×I) (I×I) ℂ)
    (hU : U∈unitaryGroup (I×I) ℂ)
    (hp : ∀ i,U*ᵥTensorState (Ket i) (Ket j)=SzegedyIsometry P*ᵥKet i) :
    U * diagonal (fun xy : I×I => if xy.1∉S ∧ xy.2=j then (1:ℂ) else -1) * Uᴴ =
      ReflectionAbout (unmarkedRowFrame P S * (unmarkedRowFrame P S)ᴴ) := by
  let E := detectionSourceFrame S j
  have hUE : U*E=unmarkedRowFrame P S := by
    ext xy i
    have hu := congrFun (hp i.1) xy
    rw [tensorState_ket_ket,mulVec_ket_column,mulVec_ket_column] at hu
    simpa [E,detectionSourceFrame,Matrix.mul_apply,mul_ite] using! hu
  have hD : diagonal (fun xy : I×I => if xy.1∉S ∧ xy.2=j then (1:ℂ) else -1)=
      ReflectionAbout (E*Eᴴ) := by
    rw [detection_source_projector]
    ext xy zw
    by_cases h : xy=zw
    · subst zw
      by_cases hxy : xy.1∉S ∧ xy.2=j <;>
        simp [ReflectionAbout,Matrix.diagonal_apply,Matrix.one_apply,hxy] <;> ring
    · simp [ReflectionAbout,Matrix.diagonal_apply,Matrix.one_apply,h]
  have hUU : U*Uᴴ=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! hU.2
  rw [hD,ReflectionAbout,Matrix.mul_sub,Matrix.mul_smul,Matrix.sub_mul,Matrix.smul_mul,
    Matrix.mul_one,hUU]
  have hprod : U*(E*Eᴴ)*Uᴴ=(U*E)*(U*E)ᴴ := by
    simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [hprod,hUE]
  rfl

/-- For a unitary row preparation, the reflection word applies the unmarked row-frame reflection
to the true-control branch of a clean state and preserves its false-control branch. -/
theorem detectionReflectionWord_clean {I : Type} [Fintype I] [DecidableEq I]
    (P : I→I→ℝ) (S : Finset I) (j : I) (U : Matrix (I×I) (I×I) ℂ)
    (hU : U∈unitaryGroup (I×I) ℂ)
    (hp : ∀ i,U*ᵥTensorState (Ket i) (Ket j)=SzegedyIsometry P*ᵥKet i)
    (f : Bool → QState (I×I)) :
    detectionEvaluate U S (detectionReflectionWord j) *ᵥ detectionCleanState f =
      detectionCleanState (fun b => if b then
        ReflectionAbout (unmarkedRowFrame P S * (unmarkedRowFrame P S)ᴴ) *ᵥ f true
        else f false) := by
  simp only [detectionReflectionWord,detectionEvaluate,detectionInstruction,
    Matrix.mul_one,← Matrix.mulVec_mulVec]
  rw [detection_select_clean,detection_marker_phase_clean,detection_select_clean]
  congr 1
  funext b
  cases b
  · rfl
  · simp only [Bool.true_eq,if_true,Matrix.mulVec_mulVec]
    rw [← Matrix.mul_assoc,detection_prepared_unmarked_reflection P S j U hU hp]

/-- The evaluation of concatenated detector words is the product of their evaluations. -/
private theorem detectionEvaluate_append {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix (I×I) (I×I) ℂ) (S : Finset I) (xs ys : List (DetectionStep I)) :
    detectionEvaluate U S (xs++ys)=detectionEvaluate U S xs*detectionEvaluate U S ys := by
  induction xs with
  | nil => simp [detectionEvaluate]
  | cons x xs ih => simp only [List.cons_append,detectionEvaluate,ih,Matrix.mul_assoc]

/-- For a unitary row preparation, the walk word applies `correctedMarkedWalk P S` to the
true-control branch of a clean state and preserves its false-control branch. -/
theorem detectionWalkWord_clean {I : Type} [Fintype I] [DecidableEq I]
    (P : I→I→ℝ) (S : Finset I) (j : I) (U : Matrix (I×I) (I×I) ℂ)
    (hU : U∈unitaryGroup (I×I) ℂ)
    (hp : ∀ i,U*ᵥTensorState (Ket i) (Ket j)=SzegedyIsometry P*ᵥKet i)
    (f : Bool → QState (I×I)) :
    detectionEvaluate U S (detectionWalkWord j) *ᵥ detectionCleanState f =
      detectionCleanState (fun b => if b then correctedMarkedWalk P S *ᵥ f true
        else f false) := by
  simp only [detectionWalkWord,detectionEvaluate_append,detectionEvaluate,detectionInstruction,
    Matrix.mul_one,← Matrix.mulVec_mulVec]
  rw [detectionReflectionWord_clean P S j U hU hp]
  rw [show detectionControlledSwap=select (fun b : Bool =>
    if b then (1 : Matrix Bool Bool ℂ)⊗ₖ(SwapGate : Matrix (I×I) (I×I) ℂ) else 1) from rfl,
    detection_select_clean,detectionReflectionWord_clean P S j U hU hp,detection_select_clean]
  congr 1
  funext b
  cases b
  · rfl
  · simp only [if_true,Matrix.mulVec_mulVec,correctedMarkedWalk,Matrix.mul_assoc]

/-- For a unitary row preparation, `K` repeated walk words apply the `K`th power of the
corrected marked walk to the true-control branch of a clean state. -/
private theorem detection_repeated_walk_clean {I : Type} [Fintype I] [DecidableEq I]
    (P : I→I→ℝ) (S : Finset I) (j : I) (U : Matrix (I×I) (I×I) ℂ)
    (hU : U∈unitaryGroup (I×I) ℂ)
    (hp : ∀ i,U*ᵥTensorState (Ket i) (Ket j)=SzegedyIsometry P*ᵥKet i)
    (K : ℕ) (f : Bool → QState (I×I)) :
    detectionEvaluate U S (List.replicate K (detectionWalkWord j)).flatten *ᵥ
      detectionCleanState f =
      detectionCleanState (fun b => if b then (correctedMarkedWalk P S)^K *ᵥ f true
        else f false) := by
  induction K with
  | zero =>
    simp only [List.replicate_zero,List.flatten_nil,detectionEvaluate,pow_zero,Matrix.one_mulVec]
    congr 1
    funext b
    cases b <;> rfl
  | succ K ih =>
    rw [List.replicate_succ,List.flatten_cons,detectionEvaluate_append,← Matrix.mulVec_mulVec,
      ih,detectionWalkWord_clean P S j U hU hp]
    congr 1
    funext b
    cases b
    · rfl
    · simp only [if_true,Matrix.mulVec_mulVec,pow_succ']

/-- If `U` prepares the Szegedy row states from anchor `j`, its initial instruction maps
`detectionStart j` to the clean state with false-control branch `detectionInitial P` and
zero true-control branch. -/
private theorem detection_initial_word {I : Type} [Fintype I] [DecidableEq I]
    (P : I→I→ℝ) (S : Finset I) (j : I) (U : Matrix (I×I) (I×I) ℂ)
    (hp : ∀ i,U*ᵥTensorState (Ket i) (Ket j)=SzegedyIsometry P*ᵥKet i) :
    detectionInstruction U S .rowInitial *ᵥ detectionStart j =
      detectionCleanState (fun b => if b then 0 else detectionInitial P) := by
  have hstart : detectionStart j=detectionCleanState (fun b =>
      if b then 0 else szegedyFrame j *ᵥ chainUniform) := by
    funext v
    rcases v with ⟨b,c,x,y⟩
    cases b <;> cases c <;>
      simp [detectionStart,detectionCleanState,szegedyFrame,Matrix.mulVec,dotProduct,
        Fintype.sum_prod_type,ite_mul,ite_and]
  rw [hstart]
  change ((1 : Matrix Bool Bool ℂ)⊗ₖ((1 : Matrix Bool Bool ℂ)⊗ₖU)) *ᵥ _ = _
  rw [detection_row_initial_clean]
  congr 1
  funext b
  cases b
  · simp only [Bool.false_eq_true,if_false,Matrix.mulVec_mulVec,szegedyPreparation_mul_frame U hp]
    rfl
  · simp

/-- For a transition matrix and a unitary row preparation, the detector is unitary, produces the
marked interference state, and has exact counts `(4 * K + 1, 4 * K + 1, 4 * K + 2)`. See
[Szegedy2004]. -/
theorem corrected_szegedy_actual_detector_and_counts :
    ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (P : I→I→ℝ) (S : Finset I) (j : I) (U : Matrix (I×I) (I×I) ℂ) (K : ℕ),
    IsTransitionMatrix P → U∈unitaryGroup (I×I) ℂ →
    (∀ i,U*ᵥTensorState (Ket i) (Ket j)=SzegedyIsometry P*ᵥKet i) →
    detectionEvaluate U S (detectionProgram j K)∈unitaryGroup (DetectionSpace I) ℂ ∧
    detectionEvaluate U S (detectionProgram j K)*ᵥdetectionStart j=
      detectionMarkGate S*ᵥdetectionInterference (correctedMarkedWalk P S) (detectionInitial P) K ∧
    detectionCounts (detectionProgram j K)=(4*K+1,4*K+1,4*K+2) := by
  intro I _ _ _ P S j U K _ hU hp
  refine ⟨detectionProgram_unitary U S j K hU,?_,detectionProgram_actual_counts j K⟩
  simp only [detectionProgram,detectionEvaluate_append,detectionEvaluate,
    Matrix.mul_one,← Matrix.mulVec_mulVec]
  change detectionMarkGate S *ᵥ (detectionHadamard *ᵥ
    (detectionEvaluate U S (List.replicate K (detectionWalkWord j)).flatten *ᵥ
      (detectionHadamard *ᵥ (detectionInstruction U S .rowInitial *ᵥ detectionStart j)))) = _
  rw [detection_initial_word P S j U hp,detection_hadamard_clean,
    detection_repeated_walk_clean P S j U hU hp,detection_hadamard_clean]
  congr 1
  have hs : (Real.sqrt 2 : ℂ)⁻¹*(Real.sqrt 2 : ℂ)⁻¹=(1/2:ℂ) := by
    rw [← pow_two,inv_pow,sqrt2_sq]
    norm_num
  funext v
  rcases v with ⟨b,c,xy⟩
  cases b <;> cases c <;>
    simp [detectionCleanState,detectionInterference,Matrix.mulVec_smul,
      Pi.smul_apply,smul_eq_mul,mul_add,mul_sub,← mul_assoc,hs,div_eq_mul_inv] <;> ring

/-- The unmarked row-frame projector entry is the product of the two transition square roots
when the first register indices agree and are unmarked, and is zero otherwise. -/
theorem detection_unmarked_projector_entry {I : Type} [Fintype I] [DecidableEq I]
    (P : I→I→ℝ) (S : Finset I) (xy zw : I×I) :
    (unmarkedRowFrame P S * (unmarkedRowFrame P S)ᴴ) xy zw =
      if xy.1=zw.1 ∧ xy.1∉S then
        (Real.sqrt (P xy.1 xy.2):ℂ)*(Real.sqrt (P zw.1 zw.2):ℂ) else 0 := by
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,unmarkedRowFrame]
  have hs := Finset.sum_subtype (F:=inferInstance) (p:=fun i : I => i∉S)
    (Finset.univ.filter (fun i => i∉S)) (by intro i; simp)
    (fun i => SzegedyIsometry P xy i * star (SzegedyIsometry P zw i))
  rw [← hs,Finset.sum_filter,Finset.sum_eq_single xy.1]
  · by_cases hx : xy.1∈S <;> by_cases h : xy.1=zw.1 <;>
      simp [SzegedyIsometry,hx,h,eq_comm]
  · intro i _ hi
    simp [SzegedyIsometry,Ne.symm hi]
  · simp

/-- With no marked states, the unmarked row-frame projector equals the full Szegedy isometry
projector. -/
private theorem detection_empty_projector {I : Type} [Fintype I] [DecidableEq I]
    (P : I→I→ℝ) :
    unmarkedRowFrame P ∅ * (unmarkedRowFrame P ∅)ᴴ =
      SzegedyIsometry P * (SzegedyIsometry P)ᴴ := by
  ext xy zw
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,unmarkedRowFrame]
  have hs := Finset.sum_subtype (F:=inferInstance) (p:=fun i : I => i∉(∅:Finset I))
    Finset.univ (by intro i; simp)
    (fun i => SzegedyIsometry P xy i * star (SzegedyIsometry P zw i))
  exact hs.symm

/-- For a symmetric transition matrix, the corrected marked walk with an empty marked set fixes
`detectionInitial P`. -/
theorem correctedMarkedWalk_empty_fixed {I : Type} [Fintype I] [DecidableEq I]
    (P : I→I→ℝ) (hP : IsTransitionMatrix P) (hSym : ∀ i l,P i l=P l i) :
    correctedMarkedWalk P ∅ *ᵥ detectionInitial P = detectionInitial P := by
  have hR : ReflectionAbout (unmarkedRowFrame P ∅ * (unmarkedRowFrame P ∅)ᴴ) *ᵥ
      detectionInitial P = detectionInitial P := by
    change ApplyGate _ _ = _
    apply applyGate_reflectionAbout_of_fixed
    rw [detection_empty_projector]
    change (SzegedyIsometry P * (SzegedyIsometry P)ᴴ) *ᵥ
      (SzegedyIsometry P *ᵥ chainUniform) = _
    rw [Matrix.mulVec_mulVec,Matrix.mul_assoc,
      szegedyIsometry_conjTranspose_mul P hP,Matrix.mul_one]
    rfl
  have hS : (SwapGate : Matrix (I×I) (I×I) ℂ) *ᵥ detectionInitial P=detectionInitial P := by
    funext xy
    change (SwapGate *ᵥ detectionInitial P) xy = _
    rw [applyGate_swapGate]
    change detectionInitial P (xy.2,xy.1)=detectionInitial P xy
    rw [detectionInitial_apply,detectionInitial_apply,hSym xy.2 xy.1]
    rfl
  simp only [correctedMarkedWalk,← Matrix.mulVec_mulVec,hR,hS]

/-- For a symmetric transition matrix and a unitary row preparation, the detector has acceptance
probability zero for an empty marked set at every power. See [Szegedy2004]. -/
theorem corrected_szegedy_empty_mark_one_sided :
    ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (P : I→I→ℝ) (j : I) (U : Matrix (I×I) (I×I) ℂ) (K : ℕ),
    IsTransitionMatrix P → (∀ i l,P i l=P l i) → U∈unitaryGroup (I×I) ℂ →
    (∀ i,U*ᵥTensorState (Ket i) (Ket j)=SzegedyIsometry P*ᵥKet i) →
    detectionProbability U ∅ j K=0 := by
  intro I _ _ _ P j U K hP hSym hU hp
  have hfix : (correctedMarkedWalk P ∅)^K *ᵥ detectionInitial P=detectionInitial P := by
    induction K with
    | zero => simp
    | succ K ih => rw [pow_succ',← Matrix.mulVec_mulVec,ih,correctedMarkedWalk_empty_fixed P hP hSym]
  unfold detectionProbability
  rw [(corrected_szegedy_actual_detector_and_counts I P ∅ j U K hP hU hp).2.1]
  unfold MeasureProb
  apply Finset.sum_eq_zero
  intro v hv
  have ha : v.1=true ∨ v.2.1=true := by simpa [detectionAccept] using! hv
  have hz : (detectionMarkGate ∅ *ᵥ
      detectionInterference (correctedMarkedWalk P ∅) (detectionInitial P) K) v=0 := by
    change ApplyGate (permMatrix (detectionMarkPermutation ∅)) _ v=0
    rw [applyGate_permMatrix (detectionMarkPermutation_involutive ∅)]
    rcases ha with hb | hc
    · simp [detectionInterference,detectionMarkPermutation,hb,hfix]
    · simp [detectionInterference,detectionMarkPermutation,hc]
  simp [BornProb,hz]

/-- The pure-state Hermitian inner product is additive in its first argument. -/
private theorem detection_inner_add_left {H : Type} [Fintype H] (u v w : QState H) :
    Qatlib.Foundations.PureStateMath.Inner (u+v) w=Qatlib.Foundations.PureStateMath.Inner u w+Qatlib.Foundations.PureStateMath.Inner v w := by simp only [Qatlib.Foundations.PureStateMath.Inner,star_add,add_dotProduct]

/-- The pure-state Hermitian inner product is additive in its second argument. -/
private theorem detection_inner_add_right {H : Type} [Fintype H] (u v w : QState H) :
    Qatlib.Foundations.PureStateMath.Inner u (v+w)=Qatlib.Foundations.PureStateMath.Inner u v+Qatlib.Foundations.PureStateMath.Inner u w := by simp only [Qatlib.Foundations.PureStateMath.Inner,dotProduct_add]

/-- A unitary matrix preserves the Euclidean norm of a finite complex state. -/
private theorem detection_unitary_norm {H : Type} [Fintype H] [DecidableEq H]
    {W : Matrix H H ℂ} (hW : W∈unitaryGroup H ℂ) (u : QState H) :
    ‖toEuclidean_fromVec (W*ᵥu)‖=‖toEuclidean_fromVec u‖ := by
  apply isometry_mulVec_norm
  simpa only [IsIsometry,Matrix.star_eq_conjTranspose] using! hW.1

/-- If `A` is an isometry, `Aᴴ * B = 0`, and `Bᴴ * B` is a diagonal indicator, then the squared
norm of `A *ᵥ x + B *ᵥ y` is at most the sum of the input squared norms. -/
private theorem detection_synthesis_norm_sq_le {H J : Type} [Fintype H] [DecidableEq H]
    [Fintype J] [DecidableEq J] (A B : Matrix H J ℂ) (p : J→Prop) [DecidablePred p]
    (hA : IsIsometry A) (hAB : Aᴴ*B=0)
    (hB : Bᴴ*B=diagonal (fun i=>if p i then (1:ℂ) else 0)) (x y : QState J) :
    ‖toEuclidean_fromVec (A*ᵥx+B*ᵥy)‖^2 ≤
      ‖toEuclidean_fromVec x‖^2+‖toEuclidean_fromVec y‖^2 := by
  have hBA : Bᴴ*A=0 := by
    have hs := congrArg Matrix.conjTranspose hAB
    simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.conjTranspose_zero] using! hs
  have hin : Qatlib.Foundations.PureStateMath.Inner (A*ᵥx+B*ᵥy) (A*ᵥx+B*ᵥy)=
      Qatlib.Foundations.PureStateMath.Inner x x+Qatlib.Foundations.PureStateMath.Inner y ((diagonal (fun i=>if p i then (1:ℂ) else 0))*ᵥy) := by
    rw [detection_inner_add_left,detection_inner_add_right,detection_inner_add_right]
    simp only [inner_mulVec_left_rect,Matrix.mulVec_mulVec,show Aᴴ*A=1 from hA,
      hAB,hBA,hB,Matrix.one_mulVec,Matrix.zero_mulVec]
    simp [Qatlib.Foundations.PureStateMath.Inner]
  rw [norm_toEuclidean_sq_eq_re_inner,hin,Complex.add_re,
    ← norm_toEuclidean_sq_eq_re_inner]
  apply add_le_add_right
  rw [norm_toEuclidean_fromVec_sq]
  simp only [Qatlib.Foundations.PureStateMath.Inner,dotProduct,Complex.re_sum,Matrix.mulVec_diagonal]
  apply Finset.sum_le_sum
  intro i _
  by_cases hp : p i
  · simp only [if_pos hp,one_mul,Pi.star_apply,Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
    exact le_rfl
  · simp [hp]

/-- If `u = r - W *ᵥ r`, then summing `W ^ (k + 1) *ᵥ u` for `k < L` telescopes to `W *ᵥ r - W ^
(L + 1) *ᵥ r`. -/
private theorem detection_power_sum_telescope {H : Type} [Fintype H] [DecidableEq H]
    (W : Matrix H H ℂ) (u r : QState H) (hu : u=r-W*ᵥr) (L : ℕ) :
    (∑ k∈Finset.range L,W^(k+1)*ᵥu)=W*ᵥr-W^(L+1)*ᵥr := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ,ih,hu,Matrix.mulVec_sub,Matrix.mulVec_mulVec,← pow_succ]
    abel

/-- For unitary `W`, positive `g`, and `u = r - W *ᵥ r` with `4 * g * ‖r‖² ≤ ‖u‖²`, the mean
squared displacement over powers 1 through positive `L` is at least `2 * (1 - 1 / (L * sqrt
g)) * ‖u‖²`. -/
theorem detection_busy_difference_of_right_inverse {H : Type} [Fintype H] [DecidableEq H]
    (W : Matrix H H ℂ) (hW : W∈unitaryGroup H ℂ) (u r : QState H)
    (g : ℝ) (hg : 0<g) (hu : u=r-W*ᵥr)
    (hr : 4*g*‖toEuclidean_fromVec r‖^2 ≤ ‖toEuclidean_fromVec u‖^2)
    (L : ℕ) (hL : 0<L) :
    (∑ k : Fin L,‖toEuclidean_fromVec (W^(k.val+1)*ᵥu-u)‖^2)/(L:ℝ) ≥
      2*(1-1/((L:ℝ)*Real.sqrt g))*‖toEuclidean_fromVec u‖^2 := by
  let s : QState H := ∑ k∈Finset.range L,W^(k+1)*ᵥu
  have hs : s=W*ᵥr-W^(L+1)*ᵥr := detection_power_sum_telescope W u r hu L
  have hp (k : ℕ) : W^k∈unitaryGroup H ℂ := (unitaryGroup H ℂ).pow_mem hW k
  have hsn : ‖toEuclidean_fromVec s‖ ≤ 2*‖toEuclidean_fromVec r‖ := by
    rw [hs]
    change ‖toEuclidean_fromVec (W*ᵥr)-toEuclidean_fromVec (W^(L+1)*ᵥr)‖ ≤ _
    exact (norm_sub_le _ _).trans (by
      rw [detection_unitary_norm hW,detection_unitary_norm (hp (L+1))]
      ring_nf
      rfl)
  have hsqrt := Real.sq_sqrt hg.le
  have hsqrtp : 0<Real.sqrt g := Real.sqrt_pos.mpr hg
  have hprod : Real.sqrt g*‖toEuclidean_fromVec s‖ ≤ ‖toEuclidean_fromVec u‖ := by
    have hsq : ‖toEuclidean_fromVec s‖^2 ≤ 4*‖toEuclidean_fromVec r‖^2 := by
      nlinarith [norm_nonneg (toEuclidean_fromVec s),norm_nonneg (toEuclidean_fromVec r)]
    have hmul := mul_le_mul_of_nonneg_left hsq hg.le
    have hh : (Real.sqrt g*‖toEuclidean_fromVec s‖)^2 ≤ ‖toEuclidean_fromVec u‖^2 := by
      nlinarith [hsqrt]
    nlinarith [norm_nonneg (toEuclidean_fromVec s),norm_nonneg (toEuclidean_fromVec u),
      mul_nonneg hsqrtp.le (norm_nonneg (toEuclidean_fromVec s))]
  have hin : (Qatlib.Foundations.PureStateMath.Inner u s).re ≤ ‖toEuclidean_fromVec u‖^2/Real.sqrt g := by
    have hcs := re_inner_le_norm (𝕜:=ℂ) (toEuclidean_fromVec u) (toEuclidean_fromVec s)
    rw [inner_euclidean_fromVec] at hcs
    apply (le_div_iff₀ hsqrtp).mpr
    change (Qatlib.Foundations.PureStateMath.Inner u s).re ≤ ‖toEuclidean_fromVec u‖*‖toEuclidean_fromVec s‖ at hcs
    have hm := mul_le_mul_of_nonneg_left hprod (norm_nonneg (toEuclidean_fromVec u))
    have hc := mul_le_mul_of_nonneg_right hcs hsqrtp.le
    nlinarith
  have hdiff (k : ℕ) : ‖toEuclidean_fromVec (W^(k+1)*ᵥu-u)‖^2 =
      2*‖toEuclidean_fromVec u‖^2-2*(Qatlib.Foundations.PureStateMath.Inner u (W^(k+1)*ᵥu)).re := by
    change ‖toEuclidean_fromVec (W^(k+1)*ᵥu)-toEuclidean_fromVec u‖^2 = _
    rw [norm_sub_sq (𝕜:=ℂ),detection_unitary_norm (hp (k+1)),inner_euclidean_fromVec]
    have hsre : (Qatlib.Foundations.PureStateMath.Inner (W^(k+1)*ᵥu) u).re=(Qatlib.Foundations.PureStateMath.Inner u (W^(k+1)*ᵥu)).re := by
      have hh : star (Qatlib.Foundations.PureStateMath.Inner u (W^(k+1)*ᵥu))=Qatlib.Foundations.PureStateMath.Inner (W^(k+1)*ᵥu) u :=
        (star_dotProduct (v:=W^(k+1)*ᵥu) (w:=u)).symm
      have hr := congrArg Complex.re hh
      simpa only [Complex.star_def,Complex.conj_re] using! hr.symm
    change ‖toEuclidean_fromVec u‖^2-2*(Qatlib.Foundations.PureStateMath.Inner (W^(k+1)*ᵥu) u).re+
      ‖toEuclidean_fromVec u‖^2 = _
    rw [hsre]
    ring
  have he : (∑ k : Fin L,‖toEuclidean_fromVec (W^(k.val+1)*ᵥu-u)‖^2)=
      2*(L:ℝ)*‖toEuclidean_fromVec u‖^2-2*(Qatlib.Foundations.PureStateMath.Inner u s).re := by
    have hfin := Fin.sum_univ_eq_sum_range
      (fun k : ℕ=>‖toEuclidean_fromVec (W^(k+1)*ᵥu-u)‖^2) L
    rw [hfin]
    simp only [hdiff,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,
      ← Finset.mul_sum]
    have hi : (Qatlib.Foundations.PureStateMath.Inner u s).re=∑ k∈Finset.range L,(Qatlib.Foundations.PureStateMath.Inner u (W^(k+1)*ᵥu)).re := by
      simp only [s,Qatlib.Foundations.PureStateMath.Inner,dotProduct,Finset.sum_apply,Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [Complex.re_sum]
    rw [hi]
    ring
  rw [he]
  have hLR : 0<(L:ℝ) := by exact_mod_cast hL
  apply (le_div_iff₀ hLR).mpr
  field_simp
  nlinarith [(le_div_iff₀ hsqrtp).mp hin]

/-- For an isometry `A` and orthogonal projector `Q` whose compression `Aᴴ * Q * A` is diagonal
with entries in `[0, 1 - g]`, constructs `r` satisfying `A *ᵥ x = r - (ReflectionAbout Q *
ReflectionAbout (A * Aᴴ)) *ᵥ r` and the stated squared-norm bound, when `0 < g ≤ 1`. -/
private theorem detection_frame_right_inverse {H J : Type} [Fintype H] [DecidableEq H]
    [Fintype J] [DecidableEq J] (Q : Matrix H H ℂ) (hQ : IsOrthogonalProjector Q)
    (A : Matrix H J ℂ) (t : J→ℝ) (hA : IsIsometry A)
    (ht : Aᴴ*Q*A=diagonal (fun i=>(t i:ℂ))) (hb : ∀ i,t i∈Set.Icc 0 1)
    (g : ℝ) (hg : 0<g) (hg1 : g≤1) (hgap : ∀ i,t i≤1-g) (x : QState J) :
    ∃ r : QState H,
      A*ᵥx = r-(ReflectionAbout Q*ReflectionAbout (A*Aᴴ))*ᵥr ∧
      4*g*‖toEuclidean_fromVec r‖^2 ≤ ‖toEuclidean_fromVec (A*ᵥx)‖^2 := by
  let B := csCrossNormalized Q A t
  let s : J→ℝ := fun i=>Real.sqrt (t i*(1-t i))
  let β : J→ℝ := fun i=>s i/(2*(1-t i))
  let half : QState J := (1/2:ℂ) • x
  let y : QState J := fun i=>(β i:ℂ)*x i
  let r : QState H := A*ᵥhalf+B*ᵥy
  have hpos (i : J) : 0<1-t i := by linarith [hgap i]
  have hs (i : J) : (s i)^2=t i*(1-t i) :=
    Real.sq_sqrt (mul_nonneg (hb i).1 (hpos i).le)
  have hc1 (i : J) : s i*β i=t i/2 := by
    dsimp only [β]
    apply (eq_div_iff (by norm_num : (2:ℝ)≠0)).mpr
    field_simp [(hpos i).ne']
    nlinarith only [hs i]
  have hc2 (i : J) : (1-t i)*β i=s i/2 := by
    dsimp only [β]
    field_simp [(hpos i).ne']
  have hAB : Aᴴ*B=0 := (cs_cross_normalized_grams Q hQ A t hA ht hb).1
  have hBB : Bᴴ*B=diagonal (fun i=>if 0<t i ∧ t i<1 then (1:ℂ) else 0) :=
    (cs_cross_normalized_grams Q hQ A t hA ht hb).2
  have hQA : Q*A=A*diagonal (fun i=>(t i:ℂ))+B*diagonal (fun i=>(s i:ℂ)) :=
    (cs_cross_Q_actions Q hQ A t hA ht hb).1
  have hQB : Q*B=A*diagonal (fun i=>(s i:ℂ))+B*diagonal (fun i=>((1-t i:ℝ):ℂ)) :=
    (cs_cross_Q_actions Q hQ A t hA ht hb).2
  have hsy : diagonal (fun i=>(s i:ℂ))*ᵥy=diagonal (fun i=>(t i:ℂ))*ᵥhalf := by
    funext i
    simp only [Matrix.mulVec_diagonal,y,half,Pi.smul_apply,smul_eq_mul]
    have hh : (s i:ℂ)*(β i:ℂ)=(t i:ℂ)/2 := by exact_mod_cast hc1 i
    rw [← mul_assoc,hh]
    ring
  have hcy : diagonal (fun i=>((1-t i:ℝ):ℂ))*ᵥy=diagonal (fun i=>(s i:ℂ))*ᵥhalf := by
    funext i
    simp only [Matrix.mulVec_diagonal,y,half,Pi.smul_apply,smul_eq_mul]
    have hh : ((1-t i:ℝ):ℂ)*(β i:ℂ)=(s i:ℂ)/2 := by exact_mod_cast hc2 i
    rw [← mul_assoc,hh]
    ring
  have hQzero : Q*ᵥ(A*ᵥhalf-B*ᵥy)=0 := by
    rw [Matrix.mulVec_sub,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,hQA,hQB,
      Matrix.add_mulVec,Matrix.add_mulVec]
    simp only [← Matrix.mulVec_mulVec]
    rw [hsy,hcy,sub_self]
  have hPfix : (A*Aᴴ)*ᵥ(A*ᵥhalf)=A*ᵥhalf := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_assoc,show Aᴴ*A=1 from hA,Matrix.mul_one]
  have hPzero : (A*Aᴴ)*ᵥ(B*ᵥy)=0 := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_assoc,hAB,Matrix.mul_zero,Matrix.zero_mulVec]
  have hPr : ReflectionAbout (A*Aᴴ)*ᵥr=A*ᵥhalf-B*ᵥy := by
    simp only [ReflectionAbout,r,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.mulVec_add,
      hPfix,hPzero,Matrix.one_mulVec,add_zero]
    module
  have hWr : (ReflectionAbout Q*ReflectionAbout (A*Aᴴ))*ᵥr=-(A*ᵥhalf-B*ᵥy) := by
    rw [← Matrix.mulVec_mulVec,hPr]
    exact applyGate_reflectionAbout_of_zero hQzero
  refine ⟨r,?_,?_⟩
  · rw [hWr]
    dsimp only [r,half]
    rw [Matrix.mulVec_smul]
    module
  · let C : ℝ := (1-g)/(4*g)
    have hβ (i : J) : (β i)^2 ≤ C := by
      have he : (β i)^2=t i/(4*(1-t i)) := by
        dsimp only [β]
        rw [div_pow,mul_pow,hs]
        field_simp [(hpos i).ne']
        ring
      rw [he]
      change t i/(4*(1-t i))≤(1-g)/(4*g)
      have hpi := hpos i
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [hgap i]
    have hy : ‖toEuclidean_fromVec y‖^2 ≤ C*‖toEuclidean_fromVec x‖^2 := by
      rw [norm_toEuclidean_fromVec_sq,norm_toEuclidean_fromVec_sq,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      simp only [y,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
      exact mul_le_mul_of_nonneg_right (hβ i) (sq_nonneg _)
    have hh : ‖toEuclidean_fromVec half‖^2=(1/4:ℝ)*‖toEuclidean_fromVec x‖^2 := by
      change ‖(1/2:ℂ) • toEuclidean_fromVec x‖^2 = _
      rw [norm_smul,mul_pow]
      norm_num
    have hnr := detection_synthesis_norm_sq_le A B (fun i=>0<t i ∧ t i<1) hA hAB hBB half y
    change ‖toEuclidean_fromVec r‖^2 ≤ _ at hnr
    rw [hh] at hnr
    rw [isometry_mulVec_norm hA]
    have hcoef : 4*g*((1/4:ℝ)+C)=1 := by dsimp only [C]; field_simp; ring
    have hm := mul_le_mul_of_nonneg_left (hnr.trans (add_le_add_right hy _))
      (show 0≤4*g by positivity)
    nlinarith [hcoef]

/-- Matrix multiplication over a finite intermediate index type, with the multiplication
instance specified explicitly. -/
private noncomputable abbrev detectionMM {M N K : Type} [Fintype N]
    (A : Matrix M N ℂ) (B : Matrix N K ℂ) : Matrix M K ℂ :=
  @HMul.hMul (Matrix M N ℂ) (Matrix N K ℂ) (Matrix M K ℂ)
    Matrix.instHMulOfFintypeOfMulOfAddCommMonoid A B

/-- The matrix multiplication operation `detectionMM` is associative. -/
private theorem detectionMM_assoc {M N K L : Type} [Fintype N] [Fintype K]
    (A : Matrix M N ℂ) (B : Matrix N K ℂ) (C : Matrix K L ℂ) :
    detectionMM (detectionMM A B) C=detectionMM A (detectionMM B C) := Matrix.mul_assoc A B C

/-- If isometries `A` and `F` have the same range projector and `S` is Hermitian with `‖Fᴴ * S *
F‖ ≤ c` for `c ≥ 0`, then the stated compression of `(S * F) * (S * F)ᴴ` by `A` has norm at
most `c²`. -/
private theorem detection_frame_compression_bound {H J K : Type}
    [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
    (F : Matrix H J ℂ) (A : Matrix H K ℂ) (S : Matrix H H ℂ)
    (hF : IsIsometry F) (hA : IsIsometry A) (hAP : A*Aᴴ=F*Fᴴ)
    (hS : Sᴴ=S) (c : ℝ) (hc : 0≤c) (hG : ‖Fᴴ*S*F‖≤c) :
    ‖Aᴴ*(detectionMM S F*(detectionMM S F)ᴴ)*A‖ ≤ c^2 := by
  let X : Matrix J K ℂ := detectionMM Fᴴ A
  let G : Matrix J J ℂ := Fᴴ*S*F
  let Y : Matrix J K ℂ := detectionMM (detectionMM Fᴴ S) A
  have hFA : detectionMM (F*Fᴴ) A=A := by
    calc
      _ = detectionMM (A*Aᴴ) A := congrArg (fun Z : Matrix H H ℂ => detectionMM Z A) hAP.symm
      _ = A := by simp only [detectionMM,Matrix.mul_assoc,show Aᴴ*A=1 from hA,Matrix.mul_one]
  have hX : IsIsometry X := by
    change Xᴴ*X=1
    calc
      _ = detectionMM Aᴴ (detectionMM (F*Fᴴ) A) := by
        simp only [X,detectionMM,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]
      _ = 1 := by rw [hFA]; exact hA
  have hY : Y=detectionMM G X := by
    calc
      _ = detectionMM (detectionMM Fᴴ S) (detectionMM (F*Fᴴ) A) := by rw [hFA]
      _ = _ := by simp only [Y,G,X,detectionMM,Matrix.mul_assoc]
  have hYn : ‖Y‖≤c := by
    rw [hY]
    exact (Matrix.l2_opNorm_mul G X).trans
      ((mul_le_mul hG (isometry_norm_le hX) (norm_nonneg X) hc).trans (by simp))
  have he : Aᴴ*(detectionMM S F*(detectionMM S F)ᴴ)*A=Yᴴ*Y := by
    simp only [Y,detectionMM,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hS,Matrix.mul_assoc]
  rw [he]
  have hn := Matrix.l2_opNorm_mul Yᴴ Y
  rw [Matrix.l2_opNorm_conjTranspose] at hn
  exact hn.trans (by nlinarith [norm_nonneg Y])

/-- Each nonnegative real diagonal entry is at most the operator norm of the corresponding
complex diagonal matrix. -/
private theorem detection_diagonal_eigenvalue_le_norm {J : Type} [Fintype J] [DecidableEq J]
    (t : J→ℝ) (ht : ∀ i,0≤t i) (i : J) :
    t i ≤ ‖diagonal (fun j=>(t j:ℂ))‖ := by
  have he : diagonal (fun j=>(t j:ℂ))*ᵥKet i=(t i:ℂ) • Ket i := by
    funext j
    by_cases hj : j=i <;> simp [Matrix.mulVec_diagonal,Ket,hj]
  have hh := l2_norm_mulVec_fromVec_le (diagonal (fun j=>(t j:ℂ))) (Ket i)
  rw [he] at hh
  change ‖(t i:ℂ) • toEuclidean_fromVec (Ket i)‖ ≤ _ at hh
  have hsq : ‖toEuclidean_fromVec (Ket i)‖^2=1 := by
    rw [norm_toEuclidean_sq_eq_re_inner,(normalized_iff_inner_self _).mp (normalized_ket i)]
    rfl
  have hk : ‖toEuclidean_fromVec (Ket i)‖=1 := by
    nlinarith [norm_nonneg (toEuclidean_fromVec (Ket i))]
  simpa only [norm_smul,hk,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (ht i),mul_one] using! hh

/-- The unmarked row frame applied to the restriction of `chainUniform` equals
`detectionUnmarkedInitial P S`. -/
theorem detectionUnmarkedInitial_in_frame {I : Type} [Fintype I] [DecidableEq I]
    (P : I→I→ℝ) (S : Finset I) :
    unmarkedRowFrame P S *ᵥ (fun i : Unmarked I S => chainUniform i.1)=
      detectionUnmarkedInitial P S := by
  funext xy
  simp only [Matrix.mulVec,dotProduct,unmarkedRowFrame]
  have hs := Finset.sum_subtype (F:=inferInstance) (p:=fun i : I=>i∉S)
    (Finset.univ.filter (fun i=>i∉S)) (by intro i; simp)
    (fun i=>SzegedyIsometry P xy i*chainUniform i)
  rw [← hs,Finset.sum_filter,Finset.sum_eq_single xy.1]
  · by_cases hx : xy.1∈S <;>
      simp [detectionUnmarkedInitial,collapse_apply,detectionInitial_apply,SzegedyIsometry,hx]
  · intro i _ hi
    simp [SzegedyIsometry,Ne.symm hi]
  · simp

/-- Under the stated gap and positivity assumptions, the unmarked initial state has squared norm
`1 - markedFraction S` and mean squared displacement at least `2 * (1 - 1 / (L * sqrt (δ *
markedFraction S))) * (1 - markedFraction S)`. See [Szegedy2004]. -/
theorem corrected_szegedy_busy_random_power_difference :
    ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (P : I→I→ℝ) (S : Finset I) (δ : ℝ) (L : ℕ),
    0<δ → δ≤1 → SymmetricChainGap P δ → 0 < markedFraction S → 0<L →
    ‖toEuclidean_fromVec (detectionUnmarkedInitial P S)‖^2=1-markedFraction S ∧
    (∑ k : Fin L,‖toEuclidean_fromVec
      ((correctedMarkedWalk P S)^(k.val+1)*ᵥdetectionUnmarkedInitial P S-
        detectionUnmarkedInitial P S)‖^2)/(L:ℝ) ≥
      2*(1-1/((L:ℝ)*Real.sqrt (δ*markedFraction S)))*(1-markedFraction S) := by
  intro I _ _ _ P S δ L hδ hδ1 hP hp hL
  have hmass := detectionUnmarkedInitial_norm_sq P S hP.1
  refine ⟨hmass,?_⟩
  let F := unmarkedRowFrame P S
  let M : Matrix (I×I) (I×I) ℂ := F*Fᴴ
  let T : Matrix (I×I) (I×I) ℂ := SwapGate
  let Z := detectionMM T F
  let Q : Matrix (I×I) (I×I) ℂ := Z*Zᴴ
  let g := δ*markedFraction S
  let c := 1-g
  have hg : 0<g := mul_pos hδ hp
  have hg1 : g≤1 := (mul_le_mul hδ1 (markedFraction_mem_Icc S).2
    (markedFraction_mem_Icc S).1 (by norm_num)).trans (by norm_num)
  have hc : 0≤c := by dsimp [c]; linarith
  have hF : IsIsometry F := unmarkedRowFrame_isIsometry P S hP.1
  have hT : IsIsometry T := by
    simpa only [IsIsometry,Matrix.star_eq_conjTranspose] using!
      (swapGate_unitary (I:=I)).1
  have hZ : IsIsometry Z := Qatlib.Concepts.BlockEncoding.EncodingCore.IsIsometry.mul hT hF
  have hM : IsOrthogonalProjector M := rangeProjector_isOrthogonalProjector hF
  have hQ : IsOrthogonalProjector Q := rangeProjector_isOrthogonalProjector hZ
  have hTs : Tᴴ=T := permMatrix_conjTranspose Prod.swap_swap
  have hTT : T*T=1 := permMatrix_mul_self Prod.swap_swap
  have hconj : Q=T*M*T := by
    simp only [Q,Z,M,detectionMM,Matrix.conjTranspose_mul,hTs,Matrix.mul_assoc]
  have hwalk : correctedMarkedWalk P S=ReflectionAbout Q*ReflectionAbout M := by
    have hR : T*ReflectionAbout M*T=ReflectionAbout Q := by
      simp only [ReflectionAbout,Matrix.mul_sub,Matrix.mul_smul,Matrix.sub_mul,
        Matrix.smul_mul,Matrix.mul_one,hTT]
      rw [← hconj]
    exact congrArg (fun X : Matrix (I×I) (I×I) ℂ => X*ReflectionAbout M) hR
  have hW : correctedMarkedWalk P S∈unitaryGroup (I×I) ℂ := by
    rw [hwalk]
    exact (unitaryGroup _ _).mul_mem (reflectionAbout_unitary hQ) (reflectionAbout_unitary hM)
  obtain ⟨A,t,hb,hA,hAP,ht⟩ := cs_projector_compressed_eigenframe M Q hM hQ
  have hG : ‖Fᴴ*T*F‖≤c := by
    have hh := unmarked_principal_gram_and_gap I P S δ hδ hδ1 hP
    rw [hh.2.1]
    exact hh.2.2
  have hAn : ‖Aᴴ*Q*A‖≤c^2 := detection_frame_compression_bound F A T hF hA hAP hTs c hc hG
  have htn : ∀ i,t i≤1-g := by
    intro i
    have hd : ‖diagonal (fun i=>(t i:ℂ))‖≤c^2 := by simpa only [ht] using! hAn
    have hi := (detection_diagonal_eigenvalue_le_norm t (fun i=>(hb i).1) i).trans hd
    dsimp only [c] at hi
    nlinarith
  let u := detectionUnmarkedInitial P S
  have hMu : M*ᵥu=u := by
    dsimp only [u]
    rw [← detectionUnmarkedInitial_in_frame P S]
    change (F*Fᴴ)*ᵥ(F*ᵥ_) = _
    rw [Matrix.mulVec_mulVec,Matrix.mul_assoc,show Fᴴ*F=1 from hF,Matrix.mul_one]
  let x := Aᴴ*ᵥu
  have hux : A*ᵥx=u := by
    change A*ᵥ(Aᴴ*ᵥu)=u
    rw [Matrix.mulVec_mulVec,hAP]
    exact hMu
  obtain ⟨r,hr,hnr⟩ := detection_frame_right_inverse Q hQ A t hA ht hb g hg hg1 htn x
  have hru : u=r-(correctedMarkedWalk P S)*ᵥr := by
    simpa only [hux,hAP,← hwalk] using! hr
  have hnr' : 4*g*‖toEuclidean_fromVec r‖^2 ≤ ‖toEuclidean_fromVec u‖^2 := by
    simpa only [hux] using! hnr
  have hd :=
      detection_busy_difference_of_right_inverse (correctedMarkedWalk P S) hW u r g hg hru hnr' L hL
  simpa only [u,g,hmass] using! hd

/-- The corrected marked walk is unitary for every transition matrix and marked set. -/
theorem correctedMarkedWalk_unitary {I : Type} [Fintype I] [DecidableEq I]
    (P : I→I→ℝ) (S : Finset I) (hP : IsTransitionMatrix P) :
    correctedMarkedWalk P S∈unitaryGroup (I×I) ℂ := by
  have hR := reflectionAbout_unitary
    (rangeProjector_isOrthogonalProjector (unmarkedRowFrame_isIsometry P S hP))
  exact (unitaryGroup _ _).mul_mem
    ((unitaryGroup _ _).mul_mem ((unitaryGroup _ _).mul_mem swapGate_unitary hR) swapGate_unitary) hR

/-- The marked interference state's acceptance weight is the sum of the squared half-difference
amplitudes and, on marked first-register indices, the squared half-sum amplitudes. -/
private theorem detection_interference_accept_formula {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (W : Matrix (I×I) (I×I) ℂ) (u : QState (I×I)) (K : ℕ) :
    MeasureProb (detectionMarkGate S*ᵥdetectionInterference W u K) detectionAccept =
      ∑ xy : I×I,(‖(u xy-(W^K*ᵥu) xy)/2‖^2+
        (if xy.1∈S then ‖(u xy+(W^K*ᵥu) xy)/2‖^2 else 0)) := by
  have hcoord (b c : Bool) (xy : I×I) :
      (detectionMarkGate S*ᵥdetectionInterference W u K) (b,(c,xy)) =
      if c=decide (xy.1∈S) then
        (if b then (u xy-(W^K*ᵥu) xy)/2 else (u xy+(W^K*ᵥu) xy)/2) else 0 := by
    change ApplyGate (permMatrix (detectionMarkPermutation S)) _ _ = _
    rw [applyGate_permMatrix (detectionMarkPermutation_involutive S)]
    cases b <;> cases c <;> by_cases hx : xy.1∈S <;>
      simp [detectionMarkPermutation,detectionInterference,hx]
  simp only [MeasureProb,detectionAccept,Finset.sum_filter,BornProb,Fintype.sum_prod_type,
    Fintype.sum_bool,Finset.mem_filter,Finset.mem_univ,true_and]
  simp only [hcoord]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : x∈S <;> simp [hx] <;> ring

/-- The marked interference state's acceptance weight is at least one quarter of the squared
walk displacement and at least one half of the input's marked measurement weight. -/
private theorem detection_interference_accept_lower {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (W : Matrix (I×I) (I×I) ℂ) (u : QState (I×I)) (K : ℕ) :
    ‖toEuclidean_fromVec (W^K*ᵥu-u)‖^2/4 ≤
      MeasureProb (detectionMarkGate S*ᵥdetectionInterference W u K) detectionAccept ∧
    MeasureProb u {xy | xy.1∈S}/2 ≤
      MeasureProb (detectionMarkGate S*ᵥdetectionInterference W u K) detectionAccept := by
  rw [detection_interference_accept_formula]
  constructor
  · rw [norm_toEuclidean_fromVec_sq,Finset.sum_div]
    apply Finset.sum_le_sum
    intro xy _
    simp only [Pi.sub_apply,norm_div,Complex.norm_ofNat,div_pow]
    have hn : 0 ≤ if xy.1∈S then ‖(u xy+(W^K*ᵥu) xy)/2‖^2 else 0 := by
      split_ifs <;> positivity
    rw [norm_sub_rev]
    simp only [norm_div,Complex.norm_ofNat,div_pow] at hn
    norm_num at hn ⊢
    linarith
  · rw [MeasureProb,Finset.sum_filter,Finset.sum_div]
    apply Finset.sum_le_sum
    intro xy _
    by_cases hx : xy.1∈S
    · simp only [Finset.mem_filter,Finset.mem_univ,true_and,hx,if_true,BornProb]
      let a : ℂ := (u xy+(W^K*ᵥu) xy)/2
      let b : ℂ := (u xy-(W^K*ᵥu) xy)/2
      have he : a+b=u xy := by dsimp [a,b]; ring
      have ht := norm_add_le a b
      rw [he] at ht
      change ‖u xy‖^2/2 ≤ ‖b‖^2+‖a‖^2
      nlinarith [norm_nonneg a,norm_nonneg b,norm_nonneg (u xy),sq_nonneg (‖a‖-‖b‖)]
    · simp [hx]
      positivity

/-- For a transition matrix on a nonempty finite type, both the squared norm of the marked part
of `detectionInitial P` and its marked measurement weight equal `markedFraction S`. -/
theorem detection_marked_initial_mass {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I→I→ℝ) (S : Finset I) (hP : IsTransitionMatrix P) :
    ‖toEuclidean_fromVec (detectionInitial P-detectionUnmarkedInitial P S)‖^2=markedFraction S ∧
      MeasureProb (detectionInitial P) {xy | xy.1∈S}=markedFraction S := by
  have hn : ‖toEuclidean_fromVec (detectionInitial P)‖^2=1 := by
    have he : detectionUnmarkedInitial P (∅:Finset I)=detectionInitial P := by
      funext xy
      simp [detectionUnmarkedInitial,collapse_apply]
    have hh := detectionUnmarkedInitial_norm_sq P ∅ hP
    rw [he] at hh
    simpa [markedFraction] using! hh
  have hsplit : ‖toEuclidean_fromVec (detectionInitial P-detectionUnmarkedInitial P S)‖^2+
      ‖toEuclidean_fromVec (detectionUnmarkedInitial P S)‖^2=
      ‖toEuclidean_fromVec (detectionInitial P)‖^2 := by
    simp only [norm_toEuclidean_fromVec_sq,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro xy _
    by_cases hx : xy.1∈S <;>
      simp [detectionUnmarkedInitial,collapse_apply,hx]
  have hm : ‖toEuclidean_fromVec (detectionInitial P-detectionUnmarkedInitial P S)‖^2=markedFraction S := by
    rw [detectionUnmarkedInitial_norm_sq P S hP,hn] at hsplit
    linarith
  refine ⟨hm,?_⟩
  rw [← hm,norm_toEuclidean_fromVec_sq,MeasureProb,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro xy _
  by_cases hx : xy.1∈S <;>
    simp [detectionUnmarkedInitial,collapse_apply,BornProb,hx]

/-- For a transition matrix and a unitary row preparation, detection probability is at least one
eighth of the unmarked initial state's squared displacement after `K` corrected walk steps,
minus `markedFraction S`. -/
private theorem detection_difference_sparse_lower {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I→I→ℝ) (S : Finset I) (j : I) (U : Matrix (I×I) (I×I) ℂ) (K : ℕ)
    (hP : IsTransitionMatrix P) (hU : U∈unitaryGroup (I×I) ℂ)
    (hp : ∀ i,U*ᵥTensorState (Ket i) (Ket j)=SzegedyIsometry P*ᵥKet i) :
    ‖toEuclidean_fromVec ((correctedMarkedWalk P S)^K*ᵥdetectionUnmarkedInitial P S-
      detectionUnmarkedInitial P S)‖^2/8-markedFraction S ≤ detectionProbability U S j K := by
  let W := correctedMarkedWalk P S
  let u := detectionInitial P
  let z := detectionUnmarkedInitial P S
  let m := u-z
  let a := W^K*ᵥz-z
  let b := W^K*ᵥm-m
  let d := W^K*ᵥu-u
  have hW : W^K∈unitaryGroup (I×I) ℂ :=
    (unitaryGroup _ _).pow_mem (correctedMarkedWalk_unitary P S hP) K
  have hmass : ‖toEuclidean_fromVec m‖^2=markedFraction S :=
    (detection_marked_initial_mass P S hP).1
  have hb : ‖toEuclidean_fromVec b‖^2 ≤ 4*markedFraction S := by
    have hh : ‖toEuclidean_fromVec b‖ ≤ 2*‖toEuclidean_fromVec m‖ := by
      change ‖toEuclidean_fromVec (W^K*ᵥm)-toEuclidean_fromVec m‖ ≤ _
      exact (norm_sub_le _ _).trans (by rw [detection_unitary_norm hW]; linarith)
    nlinarith [norm_nonneg (toEuclidean_fromVec b),norm_nonneg (toEuclidean_fromVec m)]
  have he : a=d-b := by dsimp only [a,b,d,m]; rw [Matrix.mulVec_sub]; abel
  have htri : ‖toEuclidean_fromVec a‖≤‖toEuclidean_fromVec d‖+‖toEuclidean_fromVec b‖ := by
    rw [he]
    exact norm_sub_le (toEuclidean_fromVec d) (toEuclidean_fromVec b)
  have hlo : ‖toEuclidean_fromVec a‖^2 ≤ 2*‖toEuclidean_fromVec d‖^2+2*‖toEuclidean_fromVec b‖^2 := by
    nlinarith [norm_nonneg (toEuclidean_fromVec a),norm_nonneg (toEuclidean_fromVec d),
      norm_nonneg (toEuclidean_fromVec b),sq_nonneg (‖toEuclidean_fromVec d‖-‖toEuclidean_fromVec b‖)]
  have hprob : ‖toEuclidean_fromVec d‖^2/4 ≤ detectionProbability U S j K := by
    unfold detectionProbability
    rw [(corrected_szegedy_actual_detector_and_counts I P S j U K hP hU hp).2.1]
    exact (detection_interference_accept_lower S W u K).1
  change ‖toEuclidean_fromVec a‖^2/8-markedFraction S ≤ _
  linarith

/-- Under the stated gap, marked-fraction, and unitary-preparation assumptions, a range `L ≥
1000 / sqrt (δ * ε)` gives average acceptance at least `1 / 32`, with row-query and marker
counts at most `4 * L + 1` and fixed-gate count at most `4 * L + 2`. See [Szegedy2004]. -/
theorem corrected_szegedy_actual_random_power_detection :
    ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (P : I→I→ℝ) (S : Finset I) (δ ε : ℝ) (L : ℕ) (j : I)
      (U : Matrix (I×I) (I×I) ℂ),
    0<δ → δ≤1 → SymmetricChainGap P δ → 0<ε → ε ≤ markedFraction S →
    0<L → 1000/Real.sqrt (δ*ε)≤(L:ℝ) → U∈unitaryGroup (I×I) ℂ →
    (∀ i,U*ᵥTensorState (Ket i) (Ket j)=SzegedyIsometry P*ᵥKet i) →
    (1/32:ℝ)≤(∑ k : Fin L,detectionProbability U S j (k.val+1))/(L:ℝ) ∧
    (∀ k : Fin L,(detectionCounts (detectionProgram j (k.val+1))).1≤4*L+1 ∧
      (detectionCounts (detectionProgram j (k.val+1))).2.1≤4*L+1 ∧
      (detectionCounts (detectionProgram j (k.val+1))).2.2≤4*L+2) := by
  intro I _ _ _ P S δ ε L j U hδ hδ1 hP hε hεp hL hscale hU hp
  have hLR : 0<(L:ℝ) := by exact_mod_cast hL
  let p := markedFraction S
  have hpp : 0<p := lt_of_lt_of_le hε hεp
  have hp1 : p≤1 := (markedFraction_mem_Icc S).2
  let η : ℝ := 1/((L:ℝ)*Real.sqrt (δ*p))
  have hg : 0<δ*p := mul_pos hδ hpp
  have hgp : 0<Real.sqrt (δ*p) := Real.sqrt_pos.mpr hg
  have hη : η≤(1/1000:ℝ) := by
    have he : 0<Real.sqrt (δ*ε) := Real.sqrt_pos.mpr (mul_pos hδ hε)
    have hs : 1000≤(L:ℝ)*Real.sqrt (δ*ε) := (div_le_iff₀ he).mp hscale
    have hsq : Real.sqrt (δ*ε)≤Real.sqrt (δ*p) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hεp hδ.le)
    have hh : 1000≤(L:ℝ)*Real.sqrt (δ*p) :=
      hs.trans (mul_le_mul_of_nonneg_left hsq hLR.le)
    dsimp only [η]
    apply (div_le_div_iff₀ (mul_pos hLR hgp) (by norm_num)).mpr
    linarith
  have hdense (K : ℕ) : p/2 ≤ detectionProbability U S j K := by
    unfold detectionProbability
    rw [(corrected_szegedy_actual_detector_and_counts I P S j U K hP.1 hU hp).2.1]
    have hh := (detection_interference_accept_lower S (correctedMarkedWalk P S)
      (detectionInitial P) K).2
    rw [(detection_marked_initial_mass P S hP.1).2] at hh
    exact hh
  constructor
  · by_cases hbig : (1/16:ℝ)≤p
    · have hs : (∑ k : Fin L,p/2) ≤ ∑ k : Fin L,detectionProbability U S j (k.val+1) :=
        Finset.sum_le_sum (fun k _=>hdense (k.val+1))
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
      apply (le_div_iff₀ hLR).mpr
      have hm := mul_le_mul_of_nonneg_left hbig hLR.le
      nlinarith
    · let N : ℝ := ∑ k : Fin L,‖toEuclidean_fromVec
        ((correctedMarkedWalk P S)^(k.val+1)*ᵥdetectionUnmarkedInitial P S-
          detectionUnmarkedInitial P S)‖^2
      have hbusy : 2*(1-η)*(1-p)≤N/(L:ℝ) :=
        (corrected_szegedy_busy_random_power_difference I P S δ L hδ hδ1 hP hpp hL).2
      have hs : (∑ k : Fin L,(‖toEuclidean_fromVec
          ((correctedMarkedWalk P S)^(k.val+1)*ᵥdetectionUnmarkedInitial P S-
            detectionUnmarkedInitial P S)‖^2/8-p)) ≤
          ∑ k : Fin L,detectionProbability U S j (k.val+1) :=
        Finset.sum_le_sum (fun k _=>detection_difference_sparse_lower P S j U (k.val+1) hP.1 hU hp)
      have hs' : N/8-(L:ℝ)*p ≤ ∑ k : Fin L,detectionProbability U S j (k.val+1) := by
        simpa only [Finset.sum_sub_distrib,← Finset.sum_div,Finset.sum_const,
          Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,N] using! hs
      have havg : N/(L:ℝ)/8-p ≤
          (∑ k : Fin L,detectionProbability U S j (k.val+1))/(L:ℝ) := by
        apply (le_div_iff₀ hLR).mpr
        have he : (N/(L:ℝ)/8-p)*(L:ℝ)=N/8-(L:ℝ)*p := by field_simp
        rw [he]
        exact hs'
      have hpn : (15/16:ℝ)≤1-p := by linarith
      have hen : (999/1000:ℝ)≤1-η := by linarith
      have hm := mul_le_mul hen hpn (by norm_num : (0:ℝ)≤15/16) (by linarith : 0≤1-η)
      nlinarith
  · intro k
    rw [detectionProgram_actual_counts]
    have hk := k.isLt
    simp only [Prod.fst,Prod.snd]
    omega

end Qatlib.Concepts.WalkSearch.Detection
