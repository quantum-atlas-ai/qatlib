/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeShiftedBody
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.RawShiftedBody
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CircuitImpl.SqrtApprox
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.BlockEncoding.EncodingCore.IsIsometry
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.CopyEvolution.Discriminate

/-! Six native auxiliary wires with an arbitrary finite data space.
The actual oracle and its original common isometric frame are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix

open Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep
open scoped BigOperators Matrix.Norms.L2Operator Kronecker

variable {H : Type} [Fintype H] [DecidableEq H]


/-- Construction for effective Selector in the native data body model. -/
def effectiveSelector (U : Matrix H H ℂ) (j : Fin 8) : Matrix H H ℂ :=
  if j.val < 4 then 1 else U

/-- Construction for inner Body Logical in the native data body model. -/
def innerBodyLogical (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (slack : Bool) (U : Matrix H H ℂ) : Matrix (Fin 8 × H) (Fin 8 × H) ℂ :=
  TensorGate (prepLogical ps) (1 : Matrix H H ℂ) *
    TensorGate (phaseLogical p slack) (1 : Matrix H H ℂ) *
    BlockDiag (effectiveSelector U) * TensorGate (prepLogical ps) (1 : Matrix H H ℂ)

/-- Construction for effective Block in the native data body model. -/
def effectiveBlock (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (slack : Bool) (U : Matrix H H ℂ) : Matrix H H ℂ :=
  ∑ l : Fin 8, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.effectiveCoefficients ps p slack l • effectiveSelector U l

/-- Construction for body Clean Frame in the native data body model. -/
def bodyCleanFrame : Matrix (Reg 6 × H) (Fin 8 × H) ℂ :=
  cleanFrame ⊗ₖ (1 : Matrix H H ℂ)

/-- Construction for native Data Query in the native data body model. -/
def nativeDataQuery (U : Matrix H H ℂ) :
    Matrix (Reg 6 × H) (Reg 6 × H) ℂ :=
  BlockDiag (fun x : Reg 6 => if x 2 then U else 1)

/-- Expose the physical control wire, retaining all other wires as spectators. -/
def bodyQueryWireEquiv : (Reg 6 × H) ≃
    (ElementaryWireLabel (2 : Fin 6) × (Bool × H)) :=
  ((elementaryWireSplit (2 : Fin 6)).prodCongr (Equiv.refl H)).trans
    (Equiv.prodAssoc _ _ _)

omit [Fintype H] in
/-- The finite construction in `NativeDataBody` satisfies `nativeDataQuery_relabel` under the displayed hypotheses. -/
theorem nativeDataQuery_relabel (U : Matrix H H ℂ) :
    relabelGate (bodyQueryWireEquiv (H := H)) (nativeDataQuery U) =
      parallelOracle (J := ElementaryWireLabel (2 : Fin 6)) (controlOracle U) := by
  ext ⟨x,b,d⟩ ⟨y,c,e⟩
  simp [relabelGate, bodyQueryWireEquiv, nativeDataQuery, elementaryWireSplit,
    BlockDiag, parallelOracle, controlOracle, Qatlib.Concepts.BlockEncoding.LCU.select]
  have hxy : Function.update (x : Reg 6) (2 : Fin 6) b = Function.update (y : Reg 6) (2 : Fin 6) c ↔ x = y ∧ b = c := by
    change (elementaryWireSplit (2 : Fin 6)).symm (x,b) =
      (elementaryWireSplit (2 : Fin 6)).symm (y,c) ↔ _
    simp only [Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases hx : x = y <;> by_cases hb : b = c <;> simp_all

/-- The finite construction in `NativeDataBody` satisfies `bodyCleanFrame_isometry` under the displayed hypotheses. -/
theorem bodyCleanFrame_isometry : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (bodyCleanFrame (H := H)) := by
  change (bodyCleanFrame (H := H))ᴴ * bodyCleanFrame (H := H) = 1
  rw [bodyCleanFrame, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    cleanFrame_isometry, Matrix.conjTranspose_one, Matrix.one_mul,
    Matrix.one_kronecker_one]

/-- The actual finite word or frame satisfies `body_known_transport` with all displayed legality, input and workspace hypotheses. -/
theorem body_known_transport (P : Matrix (Reg 6) (Reg 6) ℂ)
    (Q : Matrix (Fin 8) (Fin 8) ℂ)
    (h : P * cleanFrame = cleanFrame * Q) :
    TensorGate P (1 : Matrix H H ℂ) * bodyCleanFrame (H := H) =
      bodyCleanFrame (H := H) * TensorGate Q (1 : Matrix H H ℂ) := by
  simp only [TensorGate, bodyCleanFrame, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, h]

/-- The actual finite word or frame satisfies `nativeDataQuery_transport` with all displayed legality, input and workspace hypotheses. -/
theorem nativeDataQuery_transport (U : Matrix H H ℂ) :
    nativeDataQuery U * bodyCleanFrame (H := H) =
      bodyCleanFrame (H := H) * BlockDiag (fun j : Fin 8 => effectiveSelector U j) := by
  ext ⟨x,d⟩ ⟨j,e⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, nativeDataQuery,
    bodyCleanFrame, Matrix.kronecker_apply, BlockDiag, cleanFrame,
    Matrix.one_apply]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, one_mul, mul_one]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq]
  rw [Finset.sum_eq_single j]
  · by_cases hx : x = seed j
    · subst x
      fin_cases j <;> simp [effectiveSelector, seed]
    · simp [hx]
  · intro l _ hlj
    simp [hlj]
  · simp

/-- The actual finite word or frame satisfies `nativeDataQuery_unitary` with all displayed legality, input and workspace hypotheses. -/
theorem nativeDataQuery_unitary (U : Matrix H H ℂ)
    (hU : U ∈ unitaryGroup H ℂ) :
    nativeDataQuery U ∈ unitaryGroup (Reg 6 × H) ℂ := by
  apply blockDiag_unitary
  intro x
  split <;> first | exact hU | exact (unitaryGroup _ ℂ).one_mem

/-- Product order; the unknown U is absent from every known instruction. -/
def nativeBodyWord (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) :
    List (AdjointStep (Reg 6 × H)) :=
  [.gate (TensorGate (program (invWord (prepWord ps))) (1 : Matrix H H ℂ)),
   .gate (TensorGate (program (phaseWord p slack)) (1 : Matrix H H ℂ)),
   .forward,
   .gate (TensorGate (program (prepWord ps)) (1 : Matrix H H ℂ))]

/-- The actual finite word or frame satisfies `nativeBodyWord_transport` with all displayed legality, input and workspace hypotheses. -/
theorem nativeBodyWord_transport (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (slack : Bool) (U : Matrix H H ℂ) :
    evaluate (nativeDataQuery U) (nativeBodyWord (H := H) ps p slack) * bodyCleanFrame (H := H) =
      bodyCleanFrame (H := H) * innerBodyLogical ps p slack U := by
  have hp := body_known_transport (H := H) _ _ (prepWord_transport ps)
  have hi := body_known_transport (H := H) _ _ (prepWord_inverse_transport ps)
  rw [prepLogical_conjTranspose] at hi
  have hh := body_known_transport (H := H) _ _ (phaseWord_transport p slack)
  have hq := nativeDataQuery_transport U
  simp only [nativeBodyWord, evaluate, instructionMatrix, Matrix.mul_one]
  simp only [Matrix.mul_assoc]
  rw [hp, ← Matrix.mul_assoc (nativeDataQuery U), hq]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (TensorGate (program (phaseWord p slack)) _), hh]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (TensorGate (program (invWord (prepWord ps))) _), hi]
  simp only [innerBodyLogical, effectiveSelector, Matrix.mul_assoc]
  rfl

omit [Fintype H] in
/-- The same emitted instruction list satisfies `nativeBodyWord_cost` with the displayed gate and query accounting. -/
theorem nativeBodyWord_cost (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) :
    adjointQueryCount (nativeBodyWord (H := H) ps p slack) = 1 ∧
    adjointGateCount (nativeBodyWord (H := H) ps p slack) = 3 ∧
    (prepWord ps).length + (phaseWord p slack).length +
      (invWord (prepWord ps)).length = 436 + (if slack then 1 else 0) := by
  have hp := prepWord_counts ps
  have hh := phaseWord_counts p slack
  simp [nativeBodyWord, adjointQueryCount, adjointGateCount, invWord, hp.1, hh.1]
  omega

/-- The actual finite word or frame satisfies `nativeBodyWord_legal` with all displayed legality, input and workspace hypotheses. -/
theorem nativeBodyWord_legal (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) :
    WellFormedAdjointCircuit (nativeBodyWord (H := H) ps p slack) := by
  have hp := tensorGate_unitary (program_unitary _ (prepWord_legal ps))
    (unitaryGroup H ℂ).one_mem
  have hi := tensorGate_unitary
    (program_unitary _ (invWord_legal _ (prepWord_legal ps)))
    (unitaryGroup H ℂ).one_mem
  have hh := tensorGate_unitary (program_unitary _ (phaseWord_legal p slack))
    (unitaryGroup H ℂ).one_mem
  simpa only [nativeBodyWord, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff,
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.forward_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil,
    and_true] using And.intro hi (And.intro hh hp)

/-- Expand a time-order native list into product-order known instructions. -/
def nativeKnownWord (gs : List Op) : List (AdjointStep (Reg 6 × H)) :=
  gs.reverse.map (fun g => .gate (TensorGate (matrix g) (1 : Matrix H H ℂ)))

/-- The finite construction in `NativeDataBody` satisfies `nativeKnownWord_evaluate` under the displayed hypotheses. -/
theorem nativeKnownWord_evaluate (U : Matrix (Reg 6 × H) (Reg 6 × H) ℂ)
    (gs : List Op) :
    evaluate U (nativeKnownWord (H := H) gs) = TensorGate (program gs) (1 : Matrix H H ℂ) := by
  induction gs with
  | nil => simp [nativeKnownWord, evaluate, program, tensorGate_one]
  | cons g gs ih =>
    simp only [nativeKnownWord, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, evaluate_append] at *
    rw [ih]
    simp only [evaluate, instructionMatrix, Matrix.mul_one, program, tensorGate_mul]

omit [Fintype H] in
/-- The same emitted instruction list satisfies `nativeKnownWord_cost` with the displayed gate and query accounting. -/
theorem nativeKnownWord_cost (gs : List Op) :
    adjointQueryCount (nativeKnownWord (H := H) gs) = 0 ∧
      adjointGateCount (nativeKnownWord (H := H) gs) = gs.length := by
  induction gs with
  | nil => simp [nativeKnownWord, adjointQueryCount, adjointGateCount]
  | cons g gs ih =>
    simp [nativeKnownWord, List.reverse_cons, adjointQueryCount_append,
      adjointGateCount_append, adjointQueryCount, adjointGateCount] at *
    exact ih

/-- The actual finite word or frame satisfies `nativeKnownWord_legal` with all displayed legality, input and workspace hypotheses. -/
theorem nativeKnownWord_legal (gs : List Op) (hgs : ∀ g ∈ gs, legal g) :
    WellFormedAdjointCircuit (nativeKnownWord (H := H) gs) := by
  intro V hV
  obtain ⟨g, hg, h⟩ := List.mem_map.mp hV
  cases h
  exact tensorGate_unitary (matrix_unitary g (hgs g (by simpa using hg)))
    (unitaryGroup H ℂ).one_mem

/-- Every known opcode is explicit; no PREP or phase matrix macro remains. -/
def nativeExpandedBodyWord (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) :
    List (AdjointStep (Reg 6 × H)) :=
  nativeKnownWord (H := H) (invWord (prepWord ps)) ++ nativeKnownWord (H := H) (phaseWord p slack) ++
    [.forward] ++ nativeKnownWord (H := H) (prepWord ps)

/-- The actual finite word or frame satisfies `nativeExpandedBody_legal` with all displayed legality, input and workspace hypotheses. -/
theorem nativeExpandedBody_legal (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) :
    WellFormedAdjointCircuit (nativeExpandedBodyWord (H := H) ps p slack) := by
  simp only [nativeExpandedBodyWord, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.append_iff]
  exact ⟨⟨⟨nativeKnownWord_legal (H := H) _ (invWord_legal _ (prepWord_legal ps)),
    nativeKnownWord_legal (H := H) _ (phaseWord_legal p slack)⟩,
    (by simp)⟩, nativeKnownWord_legal (H := H) _ (prepWord_legal ps)⟩

/-- The finite construction in `NativeDataBody` satisfies `nativeExpandedBody_evaluate` under the displayed hypotheses. -/
theorem nativeExpandedBody_evaluate (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (slack : Bool) (U : Matrix H H ℂ) :
    evaluate (nativeDataQuery U) (nativeExpandedBodyWord (H := H) ps p slack) =
      evaluate (nativeDataQuery U) (nativeBodyWord (H := H) ps p slack) := by
  simp only [nativeExpandedBodyWord, evaluate_append, nativeKnownWord_evaluate,
    nativeBodyWord, evaluate, instructionMatrix, Matrix.mul_one, Matrix.mul_assoc]

omit [Fintype H] in
/-- The same emitted instruction list satisfies `nativeExpandedBody_cost` with the displayed gate and query accounting. -/
theorem nativeExpandedBody_cost (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) :
    adjointQueryCount (nativeExpandedBodyWord (H := H) ps p slack) = 1 ∧
      adjointGateCount (nativeExpandedBodyWord (H := H) ps p slack) =
        436 + (if slack then 1 else 0) := by
  have h₁ := nativeKnownWord_cost (H := H) (invWord (prepWord ps))
  have h₂ := nativeKnownWord_cost (H := H) (phaseWord p slack)
  have h₃ := nativeKnownWord_cost (H := H) (prepWord ps)
  have hcost := (nativeBodyWord_cost (H := H) ps p slack).2.2
  simp only [nativeExpandedBodyWord, adjointQueryCount_append, adjointGateCount_append]
  simp only [h₁.1, h₂.1, h₃.1, h₁.2, h₂.2, h₃.2,
    adjointQueryCount, adjointGateCount]
  constructor
  · trivial
  · omega

/-- The finite construction in `NativeDataBody` satisfies `tensor_block_entry` under the displayed hypotheses. -/
theorem tensor_block_entry (A B : Matrix (Fin 8) (Fin 8) ℂ)
    (D : Fin 8 → Matrix H H ℂ) (j k : Fin 8) (d e : H) :
    (TensorGate A (1 : Matrix H H ℂ) *
      BlockDiag D * TensorGate B (1 : Matrix H H ℂ)) (j,d) (k,e) =
      ∑ l : Fin 8, A j l * D l d e * B l k := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, TensorGate, BlockDiag,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.of_apply]
  simp

/-- The finite construction in `NativeDataBody` satisfies `innerBodyLogical_entry` under the displayed hypotheses. -/
theorem innerBodyLogical_entry (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool)
    (U : Matrix H H ℂ) (j k : Fin 8) (d e : H) :
    innerBodyLogical ps p slack U (j,d) (k,e) =
      ∑ l : Fin 8, prepLogical ps j l * phaseCoefficient p slack l *
        (if l.val < 4 then (if d = e then 1 else 0) else U d e) * prepLogical ps l k := by
  rw [innerBodyLogical]
  rw [show TensorGate (prepLogical ps) (1 : Matrix H H ℂ) *
      TensorGate (phaseLogical p slack) (1 : Matrix H H ℂ) =
      TensorGate (prepLogical ps * phaseLogical p slack) (1 : Matrix H H ℂ) by
    rw [tensorGate_mul]
    simp]
  rw [tensor_block_entry]
  congr 1
  funext l
  have hphase : (prepLogical ps * phaseLogical p slack) j l =
      prepLogical ps j l * phaseCoefficient p slack l := by
    simp [Matrix.mul_apply, phaseLogical, Matrix.diagonal_apply]
  rw [hphase]
  by_cases hl : l.val < 4
  · by_cases hde : d = e <;> simp [effectiveSelector, hl, Matrix.one_apply, hde]
  · simp [effectiveSelector, hl]


/-- The finite construction in `NativeDataBody` satisfies `innerBodyLogical_corner` under the displayed hypotheses. -/
theorem innerBodyLogical_corner (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (slack : Bool) (U : Matrix H H ℂ) :
    compress (encodingFiber (I := H) (0 : Fin 8)) (innerBodyLogical ps p slack U)
      (encodingFiber (I := H) (0 : Fin 8)) = effectiveBlock ps p slack U := by
  ext d e
  rw [compress_encodingFiber_eq, innerBodyLogical_entry]
  simp only [effectiveBlock, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.effectiveCoefficients,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro l _
  rw [prepLogical_entry_adjoint]
  change star (prepAxis ps l) * phaseCoefficient p slack l *
      (if l.val < 4 then (if d=e then 1 else 0) else U d e) * prepAxis ps l = _
  by_cases hl : l.val < 4
  · simp [effectiveSelector, hl, Matrix.one_apply]
  · simp [effectiveSelector, hl]
    ring

/-- Construction for identity Coefficient in the native data body model. -/
def identityCoefficient (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (slack : Bool) : ℂ :=
  ∑ l : Fin 8, if l.val < 4 then Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.effectiveCoefficients ps p slack l else 0

/-- Construction for oracle Coefficient in the native data body model. -/
def oracleCoefficient (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (slack : Bool) : ℂ :=
  ∑ l : Fin 8, if l.val < 4 then 0 else Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.effectiveCoefficients ps p slack l

omit [Fintype H] in
/-- The finite construction in `NativeDataBody` satisfies `effectiveBlock_affine` under the displayed hypotheses. -/
theorem effectiveBlock_affine (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (slack : Bool) (U : Matrix H H ℂ) :
    effectiveBlock ps p slack U =
      identityCoefficient ps p slack • (1 : Matrix H H ℂ) + oracleCoefficient ps p slack • U := by
  ext d e
  simp only [effectiveBlock, identityCoefficient, oracleCoefficient,
    Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : l.val < 4 <;> simp [effectiveSelector, hl]

/-- Explicit standard Matrix multiplication keeps the rectangular frame out of
the default CStarMatrix wrapper instance during elaboration. -/
def nativeBaseFrame : Matrix (Reg 6 × H) H ℂ :=
  @HMul.hMul (Matrix (Reg 6 × H) (Fin 8 × H) ℂ) (Matrix (Fin 8 × H) H ℂ)
    (Matrix (Reg 6 × H) H ℂ) Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
    (bodyCleanFrame (H := H)) (encodingFiber (I := H) (0 : Fin 8))

/-- The finite construction in `NativeDataBody` satisfies `nativeBaseFrame_isometry` under the displayed hypotheses. -/
theorem nativeBaseFrame_isometry : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (nativeBaseFrame (H := H)) :=
  Qatlib.Concepts.BlockEncoding.EncodingCore.IsIsometry.mul bodyCleanFrame_isometry (encodingFiber_isIsometry _)

/-- The actual finite word or frame satisfies `nativeBaseFrame_compress` with all displayed legality, input and workspace hypotheses. -/
theorem nativeBaseFrame_compress (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (slack : Bool) (U : Matrix H H ℂ) :
    compress nativeBaseFrame (evaluate (nativeDataQuery U) (nativeExpandedBodyWord ps p slack))
      nativeBaseFrame = effectiveBlock ps p slack U := by
  have hJ : compress bodyCleanFrame
      (evaluate (nativeDataQuery U) (nativeExpandedBodyWord ps p slack)) bodyCleanFrame =
      innerBodyLogical ps p slack U := by
    simp only [compress, Matrix.mul_assoc]
    rw [nativeExpandedBody_evaluate, nativeBodyWord_transport]
    rw [← Matrix.mul_assoc, bodyCleanFrame_isometry, Matrix.one_mul]
  calc
    _ = compress (encodingFiber (I := H) (0 : Fin 8))
      (compress bodyCleanFrame
        (evaluate (nativeDataQuery U) (nativeExpandedBodyWord ps p slack)) bodyCleanFrame)
      (encodingFiber (I := H) (0 : Fin 8)) := by
        simp only [nativeBaseFrame, compress, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hJ, innerBodyLogical_corner]

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The original common frame is retained after the fixed auxiliary seed. -/
def nativeDataFrame (F : Matrix H I ℂ) : Matrix (Reg 6 × H) I ℂ :=
  @HMul.hMul (Matrix (Reg 6 × H) H ℂ) (Matrix H I ℂ) (Matrix (Reg 6 × H) I ℂ)
    Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (nativeBaseFrame (H := H)) F

/-- The finite construction in `NativeDataBody` satisfies `nativeDataFrame_isometry` under the displayed hypotheses. -/
theorem nativeDataFrame_isometry (F : Matrix H I ℂ) (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F) :
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (nativeDataFrame F) := Qatlib.Concepts.BlockEncoding.EncodingCore.IsIsometry.mul nativeBaseFrame_isometry hF

omit [Fintype I] in
/-- The actual finite word or frame satisfies `nativeDataFrame_compress` with all displayed legality, input and workspace hypotheses. -/
theorem nativeDataFrame_compress (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (slack : Bool) (U : Matrix H H ℂ) (F : Matrix H I ℂ) (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F) :
    compress (nativeDataFrame F)
      (evaluate (nativeDataQuery U) (nativeExpandedBodyWord ps p slack)) (nativeDataFrame F) =
      identityCoefficient ps p slack • (1 : Matrix I I ℂ) +
        oracleCoefficient ps p slack • compress F U F := by
  have h := congrArg (fun M : Matrix H H ℂ =>
    @HMul.hMul (Matrix I H ℂ) (Matrix H I ℂ) (Matrix I I ℂ)
      Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
      (@HMul.hMul (Matrix I H ℂ) (Matrix H H ℂ) (Matrix I H ℂ)
        Matrix.instHMulOfFintypeOfMulOfAddCommMonoid Fᴴ M) F)
    (nativeBaseFrame_compress ps p slack U)
  have hFF : Fᴴ * F = 1 := hF
  rw [effectiveBlock_affine] at h
  simpa only [nativeDataFrame, compress, Matrix.conjTranspose_mul, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hFF,
    Matrix.mul_assoc] using h

/-- Actual native output for the original exact/common-frame input. No normality
or coefficientPrepare identity is assumed. Frame synthesis remains separate. -/
theorem native_original_input_encoding (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (slack : Bool) (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (α : ℝ) (hbe : BlockEncoding A U F F α 0) :
    ProjectedUnitaryEncoding
      (identityCoefficient ps p slack • (1 : Matrix I I ℂ) +
        (oracleCoefficient ps p slack / (α : ℂ)) • A)
      (evaluate (nativeDataQuery U) (nativeExpandedBodyWord ps p slack))
      (nativeDataFrame F) (nativeDataFrame F) := by
  have hAreal : A = α • compress F U F := sub_eq_zero.mp (norm_eq_zero.mp
    (le_antisymm hbe.error_le (norm_nonneg _)))
  have hA : A = (α : ℂ) • compress F U F := by
    rwa [RCLike.real_smul_eq_coe_smul (K := ℂ)] at hAreal
  have hα : (α : ℂ) ≠ 0 := by exact_mod_cast hbe.normalization_pos.ne'
  refine ⟨(nativeExpandedBody_legal ps p slack).evaluate_unitary
      (nativeDataQuery_unitary U hbe.unitary),
    nativeDataFrame_isometry F hbe.left_isometry,
    nativeDataFrame_isometry F hbe.left_isometry, ?_⟩
  rw [nativeDataFrame_compress ps p slack U F hbe.left_isometry, hA]
  simp only [smul_smul, div_mul_cancel₀ _ hα]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
