/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.RawShiftedBody
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.DefectPolynomial
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.FreshFlagWord
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.UniformEncoding
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CircuitImpl.SqrtApprox
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding.EncodingCore.IsIsometry
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.CopyEvolution.Discriminate

/-! Physical seven-wire inner body. Known instructions are the actual six-wire
native programs with an untouched data wire. The single query is the original
data oracle controlled by slot wire 2, with all scratch wires retained. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix

open scoped BigOperators Matrix.Norms.L2Operator Kronecker

/-- Construction for body Clean Frame in the native shifted body model. -/
def bodyCleanFrame : Matrix (Reg 6 × Bool) (Fin 8 × Bool) ℂ :=
  cleanFrame ⊗ₖ (1 : Matrix Bool Bool ℂ)

/-- Construction for native Data Query in the native shifted body model. -/
def nativeDataQuery (U : Matrix Bool Bool ℂ) :
    Matrix (Reg 6 × Bool) (Reg 6 × Bool) ℂ :=
  BlockDiag (fun x : Reg 6 => if x 2 then U else 1)

/-- Expose the physical control wire, retaining all other wires as spectators. -/
def bodyQueryWireEquiv : (Reg 6 × Bool) ≃
    (ElementaryWireLabel (2 : Fin 6) × (Bool × Bool)) :=
  ((elementaryWireSplit (2 : Fin 6)).prodCongr (Equiv.refl Bool)).trans
    (Equiv.prodAssoc _ _ _)

/-- The finite construction in `NativeShiftedBody` satisfies `nativeDataQuery_relabel` under the displayed hypotheses. -/
theorem nativeDataQuery_relabel (U : Matrix Bool Bool ℂ) :
    relabelGate bodyQueryWireEquiv (nativeDataQuery U) =
      parallelOracle (J := ElementaryWireLabel (2 : Fin 6)) (controlOracle U) := by
  ext ⟨x,b,d⟩ ⟨y,c,e⟩
  simp [relabelGate, bodyQueryWireEquiv, nativeDataQuery, elementaryWireSplit,
    BlockDiag, parallelOracle, controlOracle, Qatlib.Concepts.BlockEncoding.LCU.select]
  have hxy : Function.update (x : Reg 6) (2 : Fin 6) b = Function.update (y : Reg 6) (2 : Fin 6) c ↔ x = y ∧ b = c := by
    change (elementaryWireSplit (2 : Fin 6)).symm (x,b) =
      (elementaryWireSplit (2 : Fin 6)).symm (y,c) ↔ _
    simp only [Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases hx : x = y <;> by_cases hb : b = c <;> simp_all

/-- The finite construction in `NativeShiftedBody` satisfies `bodyCleanFrame_isometry` under the displayed hypotheses. -/
theorem bodyCleanFrame_isometry : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry bodyCleanFrame := by
  change bodyCleanFrameᴴ * bodyCleanFrame = 1
  rw [bodyCleanFrame, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    cleanFrame_isometry, Matrix.conjTranspose_one, Matrix.one_mul,
    Matrix.one_kronecker_one]

/-- The actual finite word or frame satisfies `body_known_transport` with all displayed legality, input and workspace hypotheses. -/
theorem body_known_transport (P : Matrix (Reg 6) (Reg 6) ℂ)
    (Q : Matrix (Fin 8) (Fin 8) ℂ)
    (h : P * cleanFrame = cleanFrame * Q) :
    TensorGate P (1 : Matrix Bool Bool ℂ) * bodyCleanFrame =
      bodyCleanFrame * TensorGate Q (1 : Matrix Bool Bool ℂ) := by
  simp only [TensorGate, bodyCleanFrame, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, h]

/-- The actual finite word or frame satisfies `nativeDataQuery_transport` with all displayed legality, input and workspace hypotheses. -/
theorem nativeDataQuery_transport (U : Matrix Bool Bool ℂ) :
    nativeDataQuery U * bodyCleanFrame =
      bodyCleanFrame * BlockDiag (fun j : Fin 8 => effectiveSelector U j) := by
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
theorem nativeDataQuery_unitary (U : Matrix Bool Bool ℂ)
    (hU : U ∈ unitaryGroup Bool ℂ) :
    nativeDataQuery U ∈ unitaryGroup (Reg 6 × Bool) ℂ := by
  apply blockDiag_unitary
  intro x
  split <;> first | exact hU | exact (unitaryGroup _ ℂ).one_mem

/-- The finite construction in `NativeShiftedBody` satisfies `prepLogical_conjTranspose` under the displayed hypotheses. -/
theorem prepLogical_conjTranspose (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) :
    (prepLogical ps)ᴴ = prepLogical ps := by
  ext i j
  exact (prepLogical_entry_adjoint ps i j).symm

/-- Product order; the unknown U is absent from every known instruction. -/
def nativeBodyWord (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) :
    List (AdjointStep (Reg 6 × Bool)) :=
  [.gate (TensorGate (program (invWord (prepWord ps))) (1 : Matrix Bool Bool ℂ)),
   .gate (TensorGate (program (phaseWord p slack)) (1 : Matrix Bool Bool ℂ)),
   .forward,
   .gate (TensorGate (program (prepWord ps)) (1 : Matrix Bool Bool ℂ))]

/-- The actual finite word or frame satisfies `nativeBodyWord_transport` with all displayed legality, input and workspace hypotheses. -/
theorem nativeBodyWord_transport (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (slack : Bool) (U : Matrix Bool Bool ℂ) :
    evaluate (nativeDataQuery U) (nativeBodyWord ps p slack) * bodyCleanFrame =
      bodyCleanFrame * innerBodyLogical ps p slack U := by
  have hp := body_known_transport _ _ (prepWord_transport ps)
  have hi := body_known_transport _ _ (prepWord_inverse_transport ps)
  rw [prepLogical_conjTranspose] at hi
  have hh := body_known_transport _ _ (phaseWord_transport p slack)
  have hq := nativeDataQuery_transport U
  simp only [nativeBodyWord, evaluate, instructionMatrix, Matrix.mul_one]
  simp only [Matrix.mul_assoc]
  rw [hp, ← Matrix.mul_assoc (nativeDataQuery U), hq]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (TensorGate (program (phaseWord p slack)) _), hh]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (TensorGate (program (invWord (prepWord ps))) _), hi]
  simp only [innerBodyLogical, effectiveSelector, Matrix.mul_assoc]

/-- The same emitted instruction list satisfies `nativeBodyWord_cost` with the displayed gate and query accounting. -/
theorem nativeBodyWord_cost (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) :
    adjointQueryCount (nativeBodyWord ps p slack) = 1 ∧
    adjointGateCount (nativeBodyWord ps p slack) = 3 ∧
    (prepWord ps).length + (phaseWord p slack).length +
      (invWord (prepWord ps)).length = 436 + (if slack then 1 else 0) := by
  have hp := prepWord_counts ps
  have hh := phaseWord_counts p slack
  simp [nativeBodyWord, adjointQueryCount, adjointGateCount, invWord, hp.1, hh.1]
  omega

/-- The actual finite word or frame satisfies `nativeBodyWord_legal` with all displayed legality, input and workspace hypotheses. -/
theorem nativeBodyWord_legal (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) :
    WellFormedAdjointCircuit (nativeBodyWord ps p slack) := by
  have hp := tensorGate_unitary (program_unitary _ (prepWord_legal ps))
    (unitaryGroup Bool ℂ).one_mem
  have hi := tensorGate_unitary
    (program_unitary _ (invWord_legal _ (prepWord_legal ps)))
    (unitaryGroup Bool ℂ).one_mem
  have hh := tensorGate_unitary (program_unitary _ (phaseWord_legal p slack))
    (unitaryGroup Bool ℂ).one_mem
  simpa only [nativeBodyWord, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff,
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.forward_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil,
    and_true] using And.intro hi (And.intro hh hp)

/-- Expand a time-order native list into product-order known instructions. -/
def nativeKnownWord (gs : List Op) : List (AdjointStep (Reg 6 × Bool)) :=
  gs.reverse.map (fun g => .gate (TensorGate (matrix g) (1 : Matrix Bool Bool ℂ)))

/-- The finite construction in `NativeShiftedBody` satisfies `nativeKnownWord_evaluate` under the displayed hypotheses. -/
theorem nativeKnownWord_evaluate (U : Matrix (Reg 6 × Bool) (Reg 6 × Bool) ℂ)
    (gs : List Op) :
    evaluate U (nativeKnownWord gs) = TensorGate (program gs) (1 : Matrix Bool Bool ℂ) := by
  induction gs with
  | nil => simp [nativeKnownWord, evaluate, program, tensorGate_one]
  | cons g gs ih =>
    simp only [nativeKnownWord, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, evaluate_append] at *
    rw [ih]
    simp only [evaluate, instructionMatrix, Matrix.mul_one, program, tensorGate_mul]

/-- The same emitted instruction list satisfies `nativeKnownWord_cost` with the displayed gate and query accounting. -/
theorem nativeKnownWord_cost (gs : List Op) :
    adjointQueryCount (nativeKnownWord gs) = 0 ∧
      adjointGateCount (nativeKnownWord gs) = gs.length := by
  induction gs with
  | nil => simp [nativeKnownWord, adjointQueryCount, adjointGateCount]
  | cons g gs ih =>
    simp [nativeKnownWord, List.reverse_cons, adjointQueryCount_append,
      adjointGateCount_append, adjointQueryCount, adjointGateCount] at *
    exact ih

/-- The actual finite word or frame satisfies `nativeKnownWord_legal` with all displayed legality, input and workspace hypotheses. -/
theorem nativeKnownWord_legal (gs : List Op) (hgs : ∀ g ∈ gs, legal g) :
    WellFormedAdjointCircuit (nativeKnownWord gs) := by
  intro V hV
  obtain ⟨g, hg, h⟩ := List.mem_map.mp hV
  cases h
  exact tensorGate_unitary (matrix_unitary g (hgs g (by simpa using hg)))
    (unitaryGroup Bool ℂ).one_mem

/-- Every known opcode is explicit; no PREP or phase matrix macro remains. -/
def nativeExpandedBodyWord (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) :
    List (AdjointStep (Reg 6 × Bool)) :=
  nativeKnownWord (invWord (prepWord ps)) ++ nativeKnownWord (phaseWord p slack) ++
    [.forward] ++ nativeKnownWord (prepWord ps)

/-- The actual finite word or frame satisfies `nativeExpandedBody_legal` with all displayed legality, input and workspace hypotheses. -/
theorem nativeExpandedBody_legal (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) :
    WellFormedAdjointCircuit (nativeExpandedBodyWord ps p slack) := by
  simp only [nativeExpandedBodyWord, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.append_iff]
  exact ⟨⟨⟨nativeKnownWord_legal _ (invWord_legal _ (prepWord_legal ps)),
    nativeKnownWord_legal _ (phaseWord_legal p slack)⟩,
    (by simp)⟩, nativeKnownWord_legal _ (prepWord_legal ps)⟩

/-- The finite construction in `NativeShiftedBody` satisfies `nativeExpandedBody_evaluate` under the displayed hypotheses. -/
theorem nativeExpandedBody_evaluate (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (slack : Bool) (U : Matrix Bool Bool ℂ) :
    evaluate (nativeDataQuery U) (nativeExpandedBodyWord ps p slack) =
      evaluate (nativeDataQuery U) (nativeBodyWord ps p slack) := by
  simp only [nativeExpandedBodyWord, evaluate_append, nativeKnownWord_evaluate,
    nativeBodyWord, evaluate, instructionMatrix, Matrix.mul_one, Matrix.mul_assoc]

/-- The same emitted instruction list satisfies `nativeExpandedBody_cost` with the displayed gate and query accounting. -/
theorem nativeExpandedBody_cost (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) :
    adjointQueryCount (nativeExpandedBodyWord ps p slack) = 1 ∧
      adjointGateCount (nativeExpandedBodyWord ps p slack) =
        436 + (if slack then 1 else 0) := by
  have h₁ := nativeKnownWord_cost (invWord (prepWord ps))
  have h₂ := nativeKnownWord_cost (phaseWord p slack)
  have h₃ := nativeKnownWord_cost (prepWord ps)
  have hcost := (nativeBodyWord_cost ps p slack).2.2
  simp only [nativeExpandedBodyWord, adjointQueryCount_append, adjointGateCount_append]
  simp only [h₁.1, h₂.1, h₃.1, h₁.2, h₂.2, h₃.2,
    adjointQueryCount, adjointGateCount]
  constructor
  · trivial
  · omega

/-- Construction for native Physical Frame in the native shifted body model. -/
def nativePhysicalFrame : Matrix (Reg 6 × Bool) Bool ℂ :=
  bodyCleanFrame * cleanSlotFrame

/-- The actual finite word or frame satisfies `nativeBodyWord_compress` with all displayed legality, input and workspace hypotheses. -/
theorem nativeBodyWord_compress (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (slack : Bool) (U : Matrix Bool Bool ℂ) :
    compress nativePhysicalFrame
      (evaluate (nativeDataQuery U) (nativeBodyWord ps p slack)) nativePhysicalFrame =
      effectiveBlock ps p slack U := by
  have h := nativeBodyWord_transport ps p slack U
  simp only [compress, nativePhysicalFrame, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc _ bodyCleanFrame cleanSlotFrame, h]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc bodyCleanFrameᴴ bodyCleanFrame, bodyCleanFrame_isometry,
    Matrix.one_mul]
  simpa only [compress, Matrix.mul_assoc] using innerBodyLogical_clean_compress ps p slack U

/-- The finite construction in `NativeShiftedBody` satisfies `nativePhysicalFrame_isometry` under the displayed hypotheses. -/
theorem nativePhysicalFrame_isometry : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry nativePhysicalFrame := by
  apply Qatlib.Concepts.BlockEncoding.EncodingCore.IsIsometry.mul bodyCleanFrame_isometry
  change cleanSlotFrameᴴ * cleanSlotFrame = 1
  ext d e
  simp [cleanSlotFrame, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, eq_comm]

/-- The actual native body encodes its actual effective block without an
extra coefficient-mass factor or an abstract coefficientPrepare replacement. -/
theorem nativeBodyWord_encoding (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (slack : Bool) (U : Matrix Bool Bool ℂ) (hU : U ∈ unitaryGroup Bool ℂ) :
    ProjectedUnitaryEncoding (effectiveBlock ps p slack U)
      (evaluate (nativeDataQuery U) (nativeBodyWord ps p slack))
      nativePhysicalFrame nativePhysicalFrame := by
  exact ⟨(nativeBodyWord_legal ps p slack).evaluate_unitary
      (nativeDataQuery_unitary U hU),
    nativePhysicalFrame_isometry, nativePhysicalFrame_isometry,
    nativeBodyWord_compress ps p slack U⟩

/-- The actual finite word or frame satisfies `nativeExpandedBody_encoding` with all displayed legality, input and workspace hypotheses. -/
theorem nativeExpandedBody_encoding (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (slack : Bool) (U : Matrix Bool Bool ℂ) (hU : U ∈ unitaryGroup Bool ℂ) :
    ProjectedUnitaryEncoding (effectiveBlock ps p slack U)
      (evaluate (nativeDataQuery U) (nativeExpandedBodyWord ps p slack))
      nativePhysicalFrame nativePhysicalFrame := by
  rw [nativeExpandedBody_evaluate]
  exact nativeBodyWord_encoding ps p slack U hU

/-- Consume the physical body in the same shared Neumann word. Outer known
macros and the expansion of this body's queries through the outer word are
separate refinement obligations. -/
theorem nativeBody_neumann_encoding (b : ℕ) (hb : 0 < b)
    (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool)
    (U : Matrix Bool Bool ℂ) (hU : U ∈ unitaryGroup Bool ℂ) :
    ProjectedUnitaryEncoding
      (((b : ℂ)⁻¹) • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann (effectiveBlock ps p slack U) b)
      (evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle (b-1) (parallelOracle (J := Fin b)
        (evaluate (nativeDataQuery U) (nativeExpandedBodyWord ps p slack))))
        (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannWord b hb (rangeProjector nativePhysicalFrame)))
      (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb nativePhysicalFrame)
      (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb nativePhysicalFrame) := by
  rw [nativeExpandedBody_evaluate]
  have hbody := nativeBodyWord_encoding ps p slack U hU
  have h := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniform_neumann_word_encoding b hb _ nativePhysicalFrame
    hbody.unitary nativePhysicalFrame_isometry
  rw [nativeBodyWord_compress] at h
  exact h

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep
