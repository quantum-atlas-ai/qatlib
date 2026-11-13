/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.NumericalDyadicPhase
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.LocalControlledSwap
import Qatlib.Concepts.BlockEncoding.LinearCombination
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.LocalCopyCleanFrame
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.LocalCopyLayout
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.LocalCopyWordSemantics

/-!
# Dyadic Controlled Partial Swaps

The four gate phase gadget `fastCopyPhaseSteps` yields the optimized clean partial swap word
`fastControlledSwapSteps`. This construction supplies local controlled interactions for the
fresh copy evolution framework of [LloydMohseniRebentrost2014].

The rational phase data in `copyPhaseData` define exactly unitary numerical gates, and
`numericControlledSwapSteps` implements a clean partial swap at their effective angle. The
numerical word has an operator norm error bound relative to the target angle `Real.pi / 2^b`.

## Main statements

* `direct_parity_controlled_swap_clean_word` gives legality, clean frame semantics, adjoint
  semantics, and length `36*n+4`.
- `numericControlledSwap_error` bounds the numerical word error by `(2⁻¹)^k`.
* `numerical_controlled_swap_clean_and_error` also records that every gate acts on at most two
  wires.

## References

- [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The four gate parity phase gadget using two opposite parity wire rotations and two CNOT
gates from the control wire. -/
noncomputable def fastCopyPhaseSteps (n : ℕ) (theta : ℝ) : List (ReflectionGate (3*n+2)) :=
  [.inl (localCopyParityWire n,Rz theta),
   .inr (localCopyControlWire n,localCopyParityWire n),
   .inl (localCopyParityWire n,Rz (-theta)),
   .inr (localCopyControlWire n,localCopyParityWire n)]
/-- The optimized controlled partial swap word obtained by conjugating the parity phase gadget
with Bell basis and parity computation words. -/
noncomputable def fastControlledSwapSteps (n : ℕ) (theta : ℝ) : List (ReflectionGate (3*n+2)) :=
  reflectionAdjoint (localCopyBellSteps n) ++ localCopyComputeAndParity n ++
    fastCopyPhaseSteps n theta ++ reflectionAdjoint (localCopyComputeAndParity n) ++ localCopyBellSteps n

/-- Gaussian rational phase data approximating the unit complex number at angle `Real.pi / 2^b`,
with precision parameter `k`. -/
def copyPhaseData (b k : ℕ) : GaussianRat := numericalDyadicPhase (b+1) false k
/-- Gaussian rational data obtained by conjugating `copyPhaseData b k`. -/
def copyPhaseAdjData (b k : ℕ) : GaussianRat := ((copyPhaseData b k).1,-(copyPhaseData b k).2)
/-- The real angle whose complex exponential equals the rational phase represented by
`copyPhaseData b k`. -/
noncomputable def copyPhaseEffectiveAngle (b k : ℕ) : ℝ :=
  8*rationalCayleyAngle (((numericalPhaseRat (b+1) false k / 8):ℚ):ℝ) (k+4)

/-- The rational phase has unit norm, its adjoint data represent its complex conjugate, and its
effective angle represents it exactly. Its distance from the target phase at angle `Real.pi
/ 2^b` is at most `(2⁻¹)^k`. -/
theorem copy_dyadic_actual_phase_data : ∀ b k : ℕ,
  gaussianRatComplex (copyPhaseAdjData b k) = star (gaussianRatComplex (copyPhaseData b k)) ∧
  ‖gaussianRatComplex (copyPhaseData b k)‖ = 1 ∧
  gaussianRatComplex (copyPhaseData b k) = Complex.exp ((copyPhaseEffectiveAngle b k:ℂ)*Complex.I) ∧
  ‖gaussianRatComplex (copyPhaseData b k)-Complex.exp (((Real.pi/(2^b:ℕ):ℝ):ℂ)*Complex.I)‖ ≤
    ((2:ℝ)⁻¹)^k := by
  intro b k
  have h := numerical_dyadic_phase_exact_unitarity_and_error (b+1) k false
  refine ⟨?_,h.1,?_,?_⟩
  · simp [copyPhaseAdjData,gaussianRatComplex]
  · unfold copyPhaseData numericalDyadicPhase copyPhaseEffectiveAngle
    rw [(squareLoop_value_and_counts _ 3).1,gaussianRatComplex_countedCayleyPhase_eq_exp,
      ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  · have ht : dyadicPhaseAngle (b+1) false = Real.pi/(2^b:ℕ) := by
      simp only [dyadicPhaseAngle,Bool.false_eq_true,ite_false]
      field_simp
      push_cast
      rw [pow_succ]
      ring
    simpa only [copyPhaseData,ht] using! h.2

/-- The four gate parity phase gadget using the rational phase data and their conjugates in
place of real angle rotations. -/
noncomputable def numericCopyPhaseSteps (n b k : ℕ) : List (ReflectionGate (3*n+2)) :=
  [.inl (localCopyParityWire n,rationalPhaseGate (copyPhaseData b k)),
   .inr (localCopyControlWire n,localCopyParityWire n),
   .inl (localCopyParityWire n,rationalPhaseGate (copyPhaseAdjData b k)),
   .inr (localCopyControlWire n,localCopyParityWire n)]
/-- The numerical controlled partial swap word built from Bell basis changes, parity
computation, the rational phase gadget, and uncomputation. -/
noncomputable def numericControlledSwapSteps (n b k : ℕ) : List (ReflectionGate (3*n+2)) :=
  reflectionAdjoint (localCopyBellSteps n) ++ localCopyComputeAndParity n ++ numericCopyPhaseSteps n b k ++
    reflectionAdjoint (localCopyComputeAndParity n) ++ localCopyBellSteps n

/-- The two-CNOT phase gadget equals a controlled rotation by twice the angle followed by the
opposite rotation on the control qubit. -/
theorem fastCopyPhase_two_wire (theta : ℝ) :
    CNOT * (TensorGate (1:Matrix Bool Bool ℂ) (Rz (-theta))) * CNOT *
      TensorGate (1:Matrix Bool Bool ℂ) (Rz theta) =
    TensorGate (Rz (-theta)) (1:Matrix Bool Bool ℂ) * ControlledGate (Rz (2*theta)) := by
  have hp : Complex.exp (((2*theta:ℝ):ℂ)*Complex.I) =
      Complex.exp ((theta:ℂ)*Complex.I)*Complex.exp ((theta:ℂ)*Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  push_cast at hp
  ext ⟨a,b⟩ ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [Matrix.mul_apply,Fintype.sum_prod_type,TensorGate,Matrix.kroneckerMap_apply,
      CNOT,permMatrix,cnotFlip,Rz,Matrix.diagonal_apply,ControlledGate,BlockDiag,Complex.ofReal_neg,hp,Complex.exp_neg]

/-- The parity computation matrix commutes with every diagonal matrix depending only on the
control wire. -/
theorem copyCompute_control_commute (n : ℕ) (a : Bool → ℂ) :
    reflectionProgramMatrix (localCopyComputeAndParity n)*localCopyControlDiagonal n a =
      localCopyControlDiagonal n a*reflectionProgramMatrix (localCopyComputeAndParity n) := by
  ext x y
  have he : ApplyGate (reflectionProgramMatrix (localCopyComputeAndParity n)*localCopyControlDiagonal n a) (Ket y) =
      ApplyGate (localCopyControlDiagonal n a*reflectionProgramMatrix (localCopyComputeAndParity n)) (Ket y) := by
    have hsm (V : Matrix (Reg (3*n+2)) (Reg (3*n+2)) ℂ) (c : ℂ) (ψ : QState (Reg (3*n+2))) :
        ApplyGate V (c • ψ) = c • ApplyGate V ψ := Matrix.mulVec_smul _ _ _
    rw [applyGate_mul,applyGate_mul,localCopyControlDiagonal,applyGate_diagonal_ket,
      hsm,localCopyComputeAndParity_basis,
      applyGate_diagonal_ket,localCopyComputeAndParity_control]
  simpa only [ApplyGate,mulVec_ket_apply] using! congrFun he x

/-- The adjoint parity computation matrix commutes with every diagonal matrix depending only on
the control wire. -/
theorem copyCompute_adjoint_control_commute (n : ℕ) (a : Bool → ℂ) :
    (reflectionProgramMatrix (localCopyComputeAndParity n))ᴴ*localCopyControlDiagonal n a =
      localCopyControlDiagonal n a*(reflectionProgramMatrix (localCopyComputeAndParity n))ᴴ := by
  have hd : (localCopyControlDiagonal n (fun b => star (a b)))ᴴ = localCopyControlDiagonal n a := by
    unfold localCopyControlDiagonal
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext x
    exact star_star _
  have he := congrArg Matrix.conjTranspose (copyCompute_control_commute n (fun b => star (a b)))
  simpa only [Matrix.conjTranspose_mul,hd] using! he.symm

/-- The optimized phase gadget equals the standard controlled-phase word followed by a control
wire rotation through the negative angle. -/
theorem fastCopyPhase_matrix (n : ℕ) (theta : ℝ) :
    reflectionProgramMatrix (fastCopyPhaseSteps n theta) =
      wireGate (3*n+2) (localCopyControlWire n) (Rz (-theta))*
        reflectionProgramMatrix (localCopyControlledPhaseSteps n theta) := by
  have hw (t : ℝ) := localCopyPhaseWireGate n false (Rz t)
  have hc := localCopyPhaseWireGate n true (Rz (-theta))
  simp only [Bool.false_eq_true,ite_false,ite_true] at hw hc
  simp only [fastCopyPhaseSteps,reflectionProgramMatrix,reflectionGateMatrix,Matrix.one_mul]
  rw [localCopyPhaseCnotGate,hw,hw]
  simp only [localCopyPhaseLift_mul]
  rw [fastCopyPhase_two_wire,localCopyControlledPhaseSteps_matrix,hc,localCopyPhaseLift_mul]

/-- The optimized and standard local controlled partial swap words have the same matrix. -/
theorem fastControlledSwap_matrix (n : ℕ) (theta : ℝ) :
    reflectionProgramMatrix (fastControlledSwapSteps n theta) =
      reflectionProgramMatrix (localControlledSwapSteps n theta) := by
  let a : Bool → ℂ := fun b => if b then Complex.exp (((-theta:ℝ):ℂ)*Complex.I) else 1
  have hc := localCopyControlRz_matrix n (-theta)
  have hb := localCopyBell_control_commute n a
  have hk := copyCompute_adjoint_control_commute n a
  simp only [fastControlledSwapSteps,localControlledSwapSteps,reflectionProgramMatrix_append,
    fastCopyPhase_matrix,reflectionProgramMatrix,reflectionGateMatrix,Matrix.one_mul,
    reflectionAdjoint_matrix _ (localCopyBellSteps_legal n),
    reflectionAdjoint_matrix _ (localCopyComputeAndParity_legal n),hc]
  change _ = _
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (reflectionProgramMatrix (localCopyComputeAndParity n))ᴴ
    (localCopyControlDiagonal n a),hk]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (reflectionProgramMatrix (localCopyBellSteps n)) (localCopyControlDiagonal n a),← hb]
  simp only [Matrix.mul_assoc]
  rfl

/-- Every gate in the optimized controlled partial swap word satisfies the reflection-gate
legality conditions. -/
theorem fastControlledSwap_legal (n : ℕ) (theta : ℝ) : reflectionLegal (fastControlledSwapSteps n theta) := by
  have hd : localCopyControlWire n ≠ localCopyParityWire n := by
    intro he; have hv := congrArg Fin.val he; dsimp [localCopyControlWire,localCopyParityWire] at hv; omega
  have hp : reflectionLegal (fastCopyPhaseSteps n theta) := by
    intro g hg
    simp only [fastCopyPhaseSteps,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact rz_unitary theta
    · exact hd
    · exact rz_unitary (-theta)
    · exact hd
  intro g hg
  simp only [fastControlledSwapSteps,List.mem_append] at hg
  rcases hg with (((h | h) | h) | h) | h
  · exact reflectionAdjoint_legal _ (localCopyBellSteps_legal n) g h
  · exact localCopyComputeAndParity_legal n g h
  · exact hp g h
  · exact reflectionAdjoint_legal _ (localCopyComputeAndParity_legal n) g h
  · exact localCopyBellSteps_legal n g h

/-- The optimized controlled partial swap word is legal, has length `36*n+4`, and implements the
logical controlled partial swap through the clean frame. Its syntactic adjoint denotes the
conjugate transpose of its matrix. -/
theorem direct_parity_controlled_swap_clean_word : ∀ (n : ℕ) (theta : ℝ),
  reflectionLegal (fastControlledSwapSteps n theta) ∧
  (fastControlledSwapSteps n theta).length = 36*n+4 ∧
  reflectionProgramMatrix (fastControlledSwapSteps n theta) * localCopyFrame n =
    localCopyFrame n * controlledSwapRawGate (2^n) theta ∧
  reflectionProgramMatrix (reflectionAdjoint (fastControlledSwapSteps n theta)) =
    (reflectionProgramMatrix (fastControlledSwapSteps n theta))ᴴ := by
  intro n theta
  refine ⟨fastControlledSwap_legal n theta,?_,?_,reflectionAdjoint_matrix _ (fastControlledSwap_legal n theta)⟩
  · simp only [fastControlledSwapSteps,List.length_append,reflectionAdjoint_length,
      localCopyBellSteps_length,localCopyComputeAndParity_length,fastCopyPhaseSteps,List.length_cons,List.length_nil]
    omega
  · rw [fastControlledSwap_matrix]
    exact local_controlled_partial_swap_clean_intertwining n theta

/-- Complex conjugation of a real angle phase exponential negates its angle. -/
theorem copy_phase_conj (t : ℝ) : star (Complex.exp ((t:ℂ)*Complex.I)) =
    Complex.exp (((-t:ℝ):ℂ)*Complex.I) := by
  change (starRingEnd ℂ) _ = _
  rw [← Complex.exp_conj]
  congr 1
  simp

/-- The optimized phase gadget is diagonal, with phase one when the control is false and
conjugate phase choices determined by the parity wire when the control is true. -/
theorem fastCopyPhase_diagonal (n : ℕ) (theta : ℝ) :
    reflectionProgramMatrix (fastCopyPhaseSteps n theta) = Matrix.diagonal (fun x =>
      if x (localCopyControlWire n) then
        if x (localCopyParityWire n) then Complex.exp ((theta:ℂ)*Complex.I)
        else star (Complex.exp ((theta:ℂ)*Complex.I)) else 1) := by
  rw [fastCopyPhase_matrix,localCopyControlRz_matrix,localCopyControlledPhaseSteps_diagonal]
  unfold localCopyControlDiagonal
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  have hp : Complex.exp ((2*(theta:ℂ))*Complex.I) =
      Complex.exp ((theta:ℂ)*Complex.I)*Complex.exp ((theta:ℂ)*Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  cases hc : x (localCopyControlWire n) <;> cases hh : x (localCopyParityWire n) <;>
    simp [copy_phase_conj,Complex.ofReal_neg,Complex.ofReal_mul,hp,Complex.exp_neg]

/-- The rational phase gate and its conjugate are exactly the rotations at the effective angle
and its negative. -/
theorem numericCopyPhase_effective (b k : ℕ) :
    rationalPhaseGate (copyPhaseData b k) = Rz (copyPhaseEffectiveAngle b k) ∧
    rationalPhaseGate (copyPhaseAdjData b k) = Rz (-copyPhaseEffectiveAngle b k) := by
  have h := copy_dyadic_actual_phase_data b k
  have hn : gaussianRatComplex (copyPhaseAdjData b k) =
      Complex.exp (((-copyPhaseEffectiveAngle b k:ℝ):ℂ)*Complex.I) := by
    rw [h.1,h.2.2.1,copy_phase_conj]
  constructor
  · unfold rationalPhaseGate Rz
    congr 1
    funext a
    cases a <;> simp [h.2.2.1]
  · unfold rationalPhaseGate Rz
    congr 1
    funext a
    cases a <;> simp [hn]

/-- The numerical controlled partial swap word is exactly the optimized word evaluated at the
rational phase's effective angle. -/
theorem numericControlledSwap_effective (n b k : ℕ) :
    numericControlledSwapSteps n b k = fastControlledSwapSteps n (copyPhaseEffectiveAngle b k) := by
  simp only [numericControlledSwapSteps,fastControlledSwapSteps,numericCopyPhaseSteps,fastCopyPhaseSteps,
    (numericCopyPhase_effective b k).1,(numericCopyPhase_effective b k).2]

/-- A nonnegative bound on the distance between two phase exponentials also bounds the operator
norm distance between their optimized parity phase gadgets. -/
theorem fastCopyPhase_error (n : ℕ) (a t : ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (he : ‖Complex.exp ((a:ℂ)*Complex.I)-Complex.exp ((t:ℂ)*Complex.I)‖ ≤ δ) :
    ‖reflectionProgramMatrix (fastCopyPhaseSteps n a)-reflectionProgramMatrix (fastCopyPhaseSteps n t)‖ ≤ δ := by
  rw [fastCopyPhase_diagonal,fastCopyPhase_diagonal,Matrix.diagonal_sub,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hδ).mpr
  intro x
  cases hc : x (localCopyControlWire n) <;> cases hp : x (localCopyParityWire n) <;>
    simp only [Bool.false_eq_true,ite_false,ite_true,sub_self,norm_zero]
  · exact hδ
  · exact hδ
  · simpa only [← star_sub,norm_star] using! he
  · exact he

/-- Multiplying two matrices on the left and right by fixed unitary matrices does not increase
their operator norm distance. -/
theorem copy_middle_error {H : Type} [Fintype H] [DecidableEq H]
    (L R A B : Matrix H H ℂ) (hL : L ∈ Matrix.unitaryGroup H ℂ) (hR : R ∈ Matrix.unitaryGroup H ℂ) :
    ‖L*A*R-L*B*R‖ ≤ ‖A-B‖ := by
  rw [← Matrix.sub_mul,← Matrix.mul_sub]
  calc
    _ ≤ ‖L*(A-B)‖*‖R‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖L‖*‖A-B‖)*‖R‖ := mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (1*‖A-B‖)*1 := by gcongr <;> exact l2_norm_unitary_le_one (by assumption)
    _ = _ := by ring

/-- The numerical controlled partial swap matrix differs from the optimized matrix at target
angle `Real.pi / 2^b` by at most `(2⁻¹)^k` in operator norm. -/
theorem numericControlledSwap_error (n b k : ℕ) :
    ‖reflectionProgramMatrix (numericControlledSwapSteps n b k)-
      reflectionProgramMatrix (fastControlledSwapSteps n (Real.pi/(2^b:ℕ)))‖ ≤ ((2:ℝ)⁻¹)^k := by
  have he := (copy_dyadic_actual_phase_data b k).2.2.2
  rw [(copy_dyadic_actual_phase_data b k).2.2.1] at he
  have hm :=
      fastCopyPhase_error n (copyPhaseEffectiveAngle b k) (Real.pi/(2^b:ℕ)) (((2:ℝ)⁻¹)^k)
      (by positivity) he
  let L := reflectionProgramMatrix (localCopyBellSteps n)*
    reflectionProgramMatrix (reflectionAdjoint (localCopyComputeAndParity n))
  let R := reflectionProgramMatrix (localCopyComputeAndParity n)*
    reflectionProgramMatrix (reflectionAdjoint (localCopyBellSteps n))
  have hl : L ∈ Matrix.unitaryGroup (Reg (3*n+2)) ℂ :=
    (Matrix.unitaryGroup _ ℂ).mul_mem (reflectionProgramMatrix_unitary _ (localCopyBellSteps_legal n))
      (reflectionProgramMatrix_unitary _ (reflectionAdjoint_legal _ (localCopyComputeAndParity_legal n)))
  have hr : R ∈ Matrix.unitaryGroup (Reg (3*n+2)) ℂ :=
    (Matrix.unitaryGroup _ ℂ).mul_mem (reflectionProgramMatrix_unitary _ (localCopyComputeAndParity_legal n))
      (reflectionProgramMatrix_unitary _ (reflectionAdjoint_legal _ (localCopyBellSteps_legal n)))
  have hfac (t : ℝ) : reflectionProgramMatrix (fastControlledSwapSteps n t) =
      L*reflectionProgramMatrix (fastCopyPhaseSteps n t)*R := by
    simp only [fastControlledSwapSteps,reflectionProgramMatrix_append,L,R,Matrix.mul_assoc]
  rw [numericControlledSwap_effective,hfac,hfac]
  exact (copy_middle_error _ _ _ _ hl hr).trans hm

/-- The numerical word is legal, has length `36*n+4`, uses gates on at most two wires, and
implements a clean controlled partial swap at its effective angle. Its operator norm error
relative to the target angle optimized word is at most `2*(2⁻¹)^k`. -/
theorem numerical_controlled_swap_clean_and_error : ∀ n b k : ℕ,
  reflectionLegal (numericControlledSwapSteps n b k) ∧
  (numericControlledSwapSteps n b k).length = 36*n+4 ∧
  (∀ g ∈ numericControlledSwapSteps n b k, (reflectionGateWires g).card ≤ 2) ∧
  reflectionProgramMatrix (numericControlledSwapSteps n b k) * localCopyFrame n =
    localCopyFrame n * controlledSwapRawGate (2^n) (copyPhaseEffectiveAngle b k) ∧
  ‖reflectionProgramMatrix (numericControlledSwapSteps n b k)-
    reflectionProgramMatrix (fastControlledSwapSteps n (Real.pi/(2^b:ℕ)))‖ ≤ 2*((2:ℝ)⁻¹)^k := by
  intro n b k
  have h := direct_parity_controlled_swap_clean_word n (copyPhaseEffectiveAngle b k)
  refine ⟨by simpa only [numericControlledSwap_effective] using! h.1,
    by simpa only [numericControlledSwap_effective] using! h.2.1,?_,
    by simpa only [numericControlledSwap_effective] using! h.2.2.1,?_⟩
  · intro g hg
    cases g with
    | inl p => simp [reflectionGateWires]
    | inr p => simpa only [reflectionGateWires,Finset.card_singleton] using! Finset.card_insert_le p.1 ({p.2}:Finset (Fin (3*n+2)))
  · have hp : (0:ℝ) ≤ ((2:ℝ)⁻¹)^k := by positivity
    exact (numericControlledSwap_error n b k).trans (by linarith)

end Qatlib.Concepts.FreshCopyExec.QpeConsumers
