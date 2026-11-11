/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.SqrtApprox.ControlledWireNorm
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.UniformEncoding
import Mathlib.Tactic.FinCases
import Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
import Qatlib.Concepts.SharedAncilla.AncillaProduct.SharedAncillaUnitaryProduct
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.DefectPolynomial
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.FreshFlagWord
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NeumannResolvent
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.ShiftCoefficients
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CircuitImpl.SqrtApprox
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.SharedAncilla.AncillaProduct
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.CopyEvolution.Discriminate

/-! Native rational Householder/phase inner program for the fixed eight-slot backend.
This OQ layer proves the actual six-wire Boolean/QuantumAlgorithmDev.Concepts.MatrixAccess.MatrixBackend.NativeWords.rotation table on its clean frame;
finite parameter generation and outer shared-word refinement remain separate. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix

open scoped BigOperators Matrix.Norms.L2Operator

/-- The target wire is split off using the pinned physical register equivalence. -/
def controlled (c t : Fin 6) (B : Matrix Bool Bool ℂ) : Matrix (Reg 6) (Reg 6) ℂ :=
  relabelGate (elementaryWireSplit t).symm
    (BlockDiag (fun x : ElementaryWireLabel t => if x.1 c then B else 1))

/-- The actual finite word or frame satisfies `controlled_unitary` with all displayed legality, input and workspace hypotheses. -/
theorem controlled_unitary (c t : Fin 6) (B : Matrix Bool Bool ℂ)
    (hB : B ∈ unitaryGroup Bool ℂ) : controlled c t B ∈ unitaryGroup (Reg 6) ℂ := by
  apply relabelGate_mem_unitary (e := (elementaryWireSplit t).symm)
  apply blockDiag_unitary
  intro x
  split <;> first | exact hB | exact (unitaryGroup Bool ℂ).one_mem

/-- The finite construction in `NativeHouseholder` satisfies `apply_ket` under the displayed hypotheses. -/
private theorem apply_ket {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (x y : I) : ApplyGate A (Qatlib.Foundations.PureStateMath.Ket x) y=A y x := by
  simp [ApplyGate, Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket, mul_ite]

/-- The finite construction in `NativeHouseholder` satisfies `rect_ket` under the displayed hypotheses. -/
private theorem rect_ket {I J : Type} [Fintype I] [DecidableEq I]
    (A : Matrix J I ℂ) (x : I) (y : J) : (A *ᵥ Qatlib.Foundations.PureStateMath.Ket x) y=A y x := by
  simp [Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket,mul_ite]

/-- The finite construction in `NativeHouseholder` satisfies `controlled_ket` under the displayed hypotheses. -/
theorem controlled_ket (c t : Fin 6) (hct : c ≠ t) (B : Matrix Bool Bool ℂ) (x : Reg 6) :
    ApplyGate (controlled c t B) (Qatlib.Foundations.PureStateMath.Ket x) =
      if x c then B false (x t) • Qatlib.Foundations.PureStateMath.Ket (Function.update x t false)+
        B true (x t) • Qatlib.Foundations.PureStateMath.Ket (Function.update x t true) else Qatlib.Foundations.PureStateMath.Ket x := by
  funext y
  rw [apply_ket]
  simp only [controlled, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm]
  change (if (elementaryWireSplit t y).1=(elementaryWireSplit t x).1 then
      (if (Function.update x t false) c then B else 1) (y t) (x t) else 0) = _
  rw [Function.update_of_ne hct]
  have he (b : Bool) : y=Function.update x t b ↔
      (elementaryWireSplit t y).1=(elementaryWireSplit t x).1 ∧ y t=b := by
    constructor
    · intro h
      constructor
      · apply Subtype.ext
        change Function.update y t false=Function.update x t false
        rw [h, Function.update_idem]
      · rw [h, Function.update_self]
    · rintro ⟨h,hb⟩
      have h' := congrArg (fun z : ElementaryWireLabel t => Function.update z.1 t b) h
      simpa [elementaryWireSplit, Function.update_idem, ← hb] using h'
  have hyx : y=x ↔ (elementaryWireSplit t y).1=(elementaryWireSplit t x).1 ∧ y t=x t := by
    simpa using he (x t)
  cases hc : x c <;> cases hx : x t <;> cases ht : y t <;>
    by_cases hs : (elementaryWireSplit t y).1=(elementaryWireSplit t x).1 <;>
    simp only [hx, ht, hs, Bool.false_eq_true, ↓reduceIte, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Qatlib.Foundations.PureStateMath.Ket, he false, he true, hyx, Matrix.one_apply,
      and_true, and_false, Bool.true_eq_false,
      mul_zero, mul_one, add_zero, zero_add]


/-- Construction for ccx Update in the native householder model. -/
def ccxUpdate (a b t : Fin 6) (x : Reg 6) : Reg 6 :=
  Function.update x t (x t ^^ (x a && x b))

/-- The finite construction in `NativeHouseholder` satisfies `ccx_involutive` under the displayed hypotheses. -/
theorem ccx_involutive (a b t : Fin 6) (hat : a ≠ t) (hbt : b ≠ t) :
    Function.Involutive (ccxUpdate a b t) := by
  intro x
  funext k
  by_cases hkt : k=t
  · subst k
    simp only [ccxUpdate, Function.update_self, Function.update_of_ne hat,
      Function.update_of_ne hbt, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  · simp [ccxUpdate, Function.update_of_ne hkt]

/-- Construction for ccx Matrix in the native householder model. -/
def ccxMatrix (a b t : Fin 6) : Matrix (Reg 6) (Reg 6) ℂ := permMatrix (ccxUpdate a b t)

/-- Native CCX has the exact pinned fifteen-local-gate table, not an assumed oracle. -/
theorem ccx_exact_table (a b t : Fin 6) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    ccxMatrix a b t = reflectionProgramMatrix (toffoliLocalSteps a b t) := by
  ext x y
  have h := (local_toffoli_fifteen_exact 6 a b t hab hat hbt).2.2 y
  rw [run_reflectionCompile] at h
  have hh := congrFun h x
  simpa only [apply_ket, ccxMatrix, permMatrix, Matrix.of_apply, Qatlib.Foundations.PureStateMath.Ket, ccxUpdate] using hh.symm

/-- Constructors for Op in the native householder model. -/
inductive Op where
  | x : Fin 6 → Op
  | z : Fin 6 → Op
  | cx : Fin 6 → Fin 6 → Op
  | ccx : Fin 6 → Fin 6 → Fin 6 → Op
  | cry : Fin 6 → Fin 6 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle → Op
  | phase : Fin 6 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle → Op

/-- Construction for legal in the native householder model. -/
def legal : Op → Prop
  | .x _ | .z _ | .phase _ _ => True
  | .cx c t | .cry c t _ => c ≠ t
  | .ccx a b t => a ≠ b ∧ a ≠ t ∧ b ≠ t

/-- Construction for matrix in the native householder model. -/
def matrix : Op → Matrix (Reg 6) (Reg 6) ℂ
  | .x w => wireGate 6 w PauliX
  | .z w => wireGate 6 w PauliZ
  | .cx c t => cnotGate 6 c t
  | .ccx a b t => ccxMatrix a b t
  | .cry c t p => controlled c t (Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.rotation p)
  | .phase w p => wireGate 6 w (phaseMatrix p)

/-- The actual finite word or frame satisfies `matrix_unitary` with all displayed legality, input and workspace hypotheses. -/
theorem matrix_unitary (g : Op) (hg : legal g) : matrix g ∈ unitaryGroup (Reg 6) ℂ := by
  cases g with
  | x w => exact wireGate_unitary _ _ _ pauliX_unitary
  | z w => exact wireGate_unitary _ _ _ pauliZ_unitary
  | cx c t => exact cnotGate_unitary _ _ _ hg
  | ccx a b t => exact permMatrix_unitary (ccx_involutive a b t hg.2.1 hg.2.2)
  | cry c t p => exact controlled_unitary _ _ _ (rotation_unitary p)
  | phase w p => exact wireGate_unitary _ _ _ (phaseMatrix_unitary p)

/-- Construction for program in the native householder model. -/
def program : List Op → Matrix (Reg 6) (Reg 6) ℂ
  | [] => 1
  | g :: gs => program gs * matrix g

/-- Construction for run in the native householder model. -/
def run : List Op → Qatlib.Foundations.PureStateMath.QState (Reg 6) → Qatlib.Foundations.PureStateMath.QState (Reg 6)
  | [], ψ => ψ
  | g :: gs, ψ => run gs (ApplyGate (matrix g) ψ)

/-- The finite construction in `NativeHouseholder` satisfies `run_eq` under the displayed hypotheses. -/
theorem run_eq (gs : List Op) (ψ : Qatlib.Foundations.PureStateMath.QState (Reg 6)) : run gs ψ=ApplyGate (program gs) ψ := by
  induction gs generalizing ψ with
  | nil => simp [run, program, ApplyGate]
  | cons g gs ih => simp only [run, program, ih, ApplyGate, Matrix.mulVec_mulVec]

/-- The finite construction in `NativeHouseholder` satisfies `run_add` under the displayed hypotheses. -/
@[simp] theorem run_add (gs : List Op) (ψ φ : Qatlib.Foundations.PureStateMath.QState (Reg 6)) :
    run gs (ψ+φ)=run gs ψ+run gs φ := by simp [run_eq, ApplyGate, Matrix.mulVec_add]

/-- The finite construction in `NativeHouseholder` satisfies `run_smul` under the displayed hypotheses. -/
@[simp] theorem run_smul (gs : List Op) (z : ℂ) (ψ : Qatlib.Foundations.PureStateMath.QState (Reg 6)) :
    run gs (z • ψ)=z • run gs ψ := by simp [run_eq, ApplyGate, Matrix.mulVec_smul]

/-- The actual finite word or frame satisfies `program_unitary` with all displayed legality, input and workspace hypotheses. -/
theorem program_unitary (gs : List Op) (hgs : ∀ g ∈ gs, legal g) :
    program gs ∈ unitaryGroup (Reg 6) ℂ := by
  induction gs with
  | nil => exact (unitaryGroup _ ℂ).one_mem
  | cons g gs ih =>
    exact (unitaryGroup (Reg 6) ℂ).mul_mem
      (ih (fun a ha => hgs a (List.mem_cons_of_mem g ha))) (matrix_unitary g (hgs g List.mem_cons_self))

/-- The finite construction in `NativeHouseholder` satisfies `act_x` under the displayed hypotheses. -/
@[simp] theorem act_x (w : Fin 6) (x : Reg 6) :
    ApplyGate (matrix (.x w)) (Qatlib.Foundations.PureStateMath.Ket x)=Qatlib.Foundations.PureStateMath.Ket (Function.update x w (!x w)) := by
  rw [matrix, applyGate_wireGate_ket]
  cases x w <;> simp [PauliX, permMatrix]

/-- The finite construction in `NativeHouseholder` satisfies `act_z` under the displayed hypotheses. -/
@[simp] theorem act_z (w : Fin 6) (x : Reg 6) :
    ApplyGate (matrix (.z w)) (Qatlib.Foundations.PureStateMath.Ket x)=(if x w then (-1:ℂ) else 1) • Qatlib.Foundations.PureStateMath.Ket x := by
  rw [matrix, applyGate_wireGate_ket]
  have hu : Function.update x w (x w)=x := by simp
  cases hx : x w with
  | false =>
    have hf : Function.update x w false=x := by simpa only [hx] using hu
    simp [PauliZ, hf]
  | true =>
    have ht : Function.update x w true=x := by simpa only [hx] using hu
    simp [PauliZ, ht]

/-- The finite construction in `NativeHouseholder` satisfies `act_cx` under the displayed hypotheses. -/
@[simp] theorem act_cx (c t : Fin 6) (hct : c ≠ t) (x : Reg 6) :
    ApplyGate (matrix (.cx c t)) (Qatlib.Foundations.PureStateMath.Ket x)=Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ x c)) :=
  applyGate_cnotGate_ket _ _ _ hct x

/-- The finite construction in `NativeHouseholder` satisfies `act_ccx` under the displayed hypotheses. -/
@[simp] theorem act_ccx (a b t : Fin 6) (hat : a ≠ t) (hbt : b ≠ t) (x : Reg 6) :
    ApplyGate (matrix (.ccx a b t)) (Qatlib.Foundations.PureStateMath.Ket x)=Qatlib.Foundations.PureStateMath.Ket (ccxUpdate a b t x) :=
  applyGate_permMatrix_ket (ccx_involutive a b t hat hbt) x

/-- The finite construction in `NativeHouseholder` satisfies `act_cry` under the displayed hypotheses. -/
@[simp] theorem act_cry (c t : Fin 6) (hct : c ≠ t) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (x : Reg 6) :
    ApplyGate (matrix (.cry c t p)) (Qatlib.Foundations.PureStateMath.Ket x)=
      if x c then Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.rotation p false (x t) • Qatlib.Foundations.PureStateMath.Ket (Function.update x t false)+
        Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.rotation p true (x t) • Qatlib.Foundations.PureStateMath.Ket (Function.update x t true) else Qatlib.Foundations.PureStateMath.Ket x :=
  controlled_ket c t hct _ x

/-- The finite construction in `NativeHouseholder` satisfies `act_phase` under the displayed hypotheses. -/
@[simp] theorem act_phase (w : Fin 6) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (x : Reg 6) :
    ApplyGate (matrix (.phase w p)) (Qatlib.Foundations.PureStateMath.Ket x)=
      (if x w then phaseScalar p else 1) • Qatlib.Foundations.PureStateMath.Ket x := by
  rw [matrix,applyGate_wireGate_ket]
  have hu : Function.update x w (x w)=x := by simp
  cases hx : x w with
  | false =>
    have hf : Function.update x w false=x := by simpa only [hx] using hu
    simp [phaseMatrix,rationalPhaseGate,hf]
  | true =>
    have ht : Function.update x w true=x := by simpa only [hx] using hu
    simp [phaseMatrix,rationalPhaseGate,ht,← phaseScalar_as_gaussian]

/-- The finite construction in `NativeHouseholder` satisfies `act_neg` under the displayed hypotheses. -/
@[simp] theorem act_neg (g : Op) (ψ : Qatlib.Foundations.PureStateMath.QState (Reg 6)) :
    ApplyGate (matrix g) (-ψ) = -ApplyGate (matrix g) ψ := by
  simp [ApplyGate, Matrix.mulVec_neg]

/-- The finite construction in `NativeHouseholder` satisfies `act_add` under the displayed hypotheses. -/
@[simp] theorem act_add (g : Op) (ψ φ : Qatlib.Foundations.PureStateMath.QState (Reg 6)) :
    ApplyGate (matrix g) (ψ+φ)=ApplyGate (matrix g) ψ+ApplyGate (matrix g) φ := by
  simp [ApplyGate, Matrix.mulVec_add]

/-- The finite construction in `NativeHouseholder` satisfies `act_smul` under the displayed hypotheses. -/
@[simp] theorem act_smul (g : Op) (z : ℂ) (ψ : Qatlib.Foundations.PureStateMath.QState (Reg 6)) :
    ApplyGate (matrix g) (z • ψ)=z • ApplyGate (matrix g) ψ := by
  simp [ApplyGate, Matrix.mulVec_smul]

/-- The finite construction in `NativeHouseholder` satisfies `update_six` under the displayed hypotheses. -/
@[simp] theorem update_six (a b c d e f z : Bool) (w : Fin 6) :
    Function.update ![a,b,c,d,e,f] w z =
      ![if w=0 then z else a,if w=1 then z else b,if w=2 then z else c,
        if w=3 then z else d,if w=4 then z else e,if w=5 then z else f] := by
  funext i
  fin_cases i <;> simp [Function.update, eq_comm]

/-- Construction for seed in the native householder model. -/
def seed (i : Fin 8) : Reg 6 :=
  ![![false,false,false,false,false,true],![true,false,false,false,false,true],
    ![false,true,false,false,false,true],![true,true,false,false,false,true],
    ![false,false,true,false,false,true],![true,false,true,false,false,true],
    ![false,true,true,false,false,true],![true,true,true,false,false,true]] i

/-- The finite construction in `NativeHouseholder` satisfies `seed_injective` under the displayed hypotheses. -/
theorem seed_injective : Function.Injective seed := by decide

/-- Construction for other in the native householder model. -/
def other (p : Fin 3) : Fin 6 × Fin 6 :=
  if p=0 then (1,2) else if p=1 then (0,2) else (0,1)

/-- Construction for zero Pair in the native householder model. -/
def zeroPair (p : Fin 3) : List Op :=
  let ab := other p; [Op.x ab.1,Op.x ab.2,Op.ccx ab.1 ab.2 3,Op.x ab.2,Op.x ab.1]

/-- Construction for pivot in the native householder model. -/
def pivot : Fin 7 → Fin 3 := ![0,1,0,2,0,1,0]

/-- Construction for moves in the native householder model. -/
def moves : Fin 7 → List Op :=
  ![[],[],[.cx 0 1],[],[.cx 0 2],[.cx 1 2],[.cx 0 1,.cx 0 2]]

/-- Construction for pair Word in the native householder model. -/
def pairWord (i : Fin 7) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) : List Op :=
  moves i ++ zeroPair (pivot i) ++ [.cry 3 ⟨(pivot i).val,by omega⟩ p] ++
    zeroPair (pivot i) ++ (moves i).reverse

/-- The actual finite word or frame satisfies `pairWord_legal` with all displayed legality, input and workspace hypotheses. -/
theorem pairWord_legal (i : Fin 7) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) : ∀ g ∈ pairWord i p, legal g := by
  fin_cases i <;> simp [pairWord,moves,pivot,zeroPair,other,legal]

/-- The finite construction in `NativeHouseholder` satisfies `pairWord_action` under the displayed hypotheses. -/
theorem pairWord_action (i : Fin 7) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (j : Fin 8) :
    run (pairWord i p) (Qatlib.Foundations.PureStateMath.Ket (seed j)) =
      if j=0 then (p.c:ℂ) • Qatlib.Foundations.PureStateMath.Ket (seed 0)+(p.s:ℂ) • Qatlib.Foundations.PureStateMath.Ket (seed ⟨i.val+1,by omega⟩)
      else if j.val=i.val+1 then -(p.s:ℂ) • Qatlib.Foundations.PureStateMath.Ket (seed 0)+(p.c:ℂ) • Qatlib.Foundations.PureStateMath.Ket (seed j)
      else Qatlib.Foundations.PureStateMath.Ket (seed j) := by
  fin_cases i <;> fin_cases j <;>
    simp [pairWord,moves,pivot,zeroPair,other,run,act_x,act_cx,act_ccx,
      act_cry,ccxUpdate,seed,Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.rotation]


/-- Construction for inv Op in the native householder model. -/
def invOp : Op → Op
  | .cry c t p => .cry c t p.inv
  | .phase w p => .phase w p.inv
  | g => g

/-- Construction for inv Word in the native householder model. -/
def invWord (gs : List Op) : List Op := gs.reverse.map invOp

/-- The finite construction in `NativeHouseholder` satisfies `controlled_adjoint` under the displayed hypotheses. -/
theorem controlled_adjoint (c t : Fin 6) (B : Matrix Bool Bool ℂ) :
    (controlled c t B)ᴴ=controlled c t Bᴴ := by
  unfold controlled
  have he : (BlockDiag (fun x : ElementaryWireLabel t => if x.1 c then B else 1))ᴴ =
      BlockDiag (fun x : ElementaryWireLabel t => if x.1 c then Bᴴ else 1) := by
    ext ⟨x,a⟩ ⟨y,b⟩
    by_cases h : x=y
    · subst y
      cases hx : x.1 c <;>
        simp only [BlockDiag,Matrix.of_apply,Matrix.conjTranspose_apply,hx,↓reduceIte]
      · change ((1 : Matrix Bool Bool ℂ)ᴴ) a b=(1 : Matrix Bool Bool ℂ) a b
        rw [Matrix.conjTranspose_one]
    · simp [BlockDiag, Matrix.conjTranspose_apply, h, Ne.symm h]
  simpa only [relabelGate, Matrix.conjTranspose_reindex] using
    congrArg (relabelGate (elementaryWireSplit t).symm) he

/-- The finite construction in `NativeHouseholder` satisfies `matrix_invOp` under the displayed hypotheses. -/
theorem matrix_invOp (g : Op) (hg : legal g) : matrix (invOp g)=(matrix g)ᴴ := by
  have hx : PauliXᴴ=PauliX := permMatrix_conjTranspose (fun b => by cases b <;> rfl)
  cases g with
  | x w => simp [invOp,matrix,wireGate_conjTranspose,hx]
  | z w => simp [invOp,matrix,wireGate_conjTranspose,pauliZ_conjTranspose]
  | cx c t => exact (permMatrix_conjTranspose (cnotUpdate_involutive 6 c t hg)).symm
  | ccx a b t => exact (permMatrix_conjTranspose (ccx_involutive a b t hg.2.1 hg.2.2)).symm
  | cry c t p => simp [invOp,matrix,controlled_adjoint]
  | phase w p => simp [invOp,matrix,wireGate_conjTranspose]

/-- The actual finite word or frame satisfies `invOp_legal` with all displayed legality, input and workspace hypotheses. -/
theorem invOp_legal (g : Op) (hg : legal g) : legal (invOp g) := by
  cases g <;> exact hg

/-- The finite construction in `NativeHouseholder` satisfies `program_append` under the displayed hypotheses. -/
theorem program_append (gs hs : List Op) : program (gs++hs)=program hs*program gs := by
  induction gs with
  | nil => simp [program]
  | cons g gs ih => simp only [List.cons_append,program,ih,Matrix.mul_assoc]

/-- The finite construction in `NativeHouseholder` satisfies `program_invWord` under the displayed hypotheses. -/
theorem program_invWord (gs : List Op) (hgs : ∀ g ∈ gs, legal g) :
    program (invWord gs)=(program gs)ᴴ := by
  induction gs with
  | nil => simp [program,invWord]
  | cons g gs ih =>
    have ht : ∀ a ∈ gs, legal a := fun a ha => hgs a (List.mem_cons_of_mem g ha)
    simp only [invWord,List.reverse_cons,List.map_append,List.map_cons,List.map_nil]
    rw [program_append]
    simp only [program,Matrix.one_mul]
    change matrix (invOp g)*program (invWord gs)=(program gs*matrix g)ᴴ
    rw [matrix_invOp g (hgs g List.mem_cons_self),ih ht,Matrix.conjTranspose_mul]

/-- The actual finite word or frame satisfies `invWord_legal` with all displayed legality, input and workspace hypotheses. -/
theorem invWord_legal (gs : List Op) (hgs : ∀ g ∈ gs, legal g) :
    ∀ g ∈ invWord gs, legal g := by
  intro g hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  exact invOp_legal a (hgs a (List.mem_reverse.mp ha))

/-- Construction for clean Frame in the native householder model. -/
def cleanFrame : Matrix (Reg 6) (Fin 8) ℂ := fun x j => if x=seed j then 1 else 0

/-- The finite construction in `NativeHouseholder` satisfies `cleanFrame_ket` under the displayed hypotheses. -/
@[simp] theorem cleanFrame_ket (j : Fin 8) : cleanFrame *ᵥ Qatlib.Foundations.PureStateMath.Ket j=Qatlib.Foundations.PureStateMath.Ket (seed j) := by
  funext x
  simp [cleanFrame,Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket,mul_ite]

/-- The finite construction in `NativeHouseholder` satisfies `cleanFrame_isometry` under the displayed hypotheses. -/
theorem cleanFrame_isometry : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry cleanFrame := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,cleanFrame]
  rw [Finset.sum_eq_single (seed i)]
  · simp [seed_injective.eq_iff,Matrix.one_apply]
  · intro x _ hx
    simp [hx]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- Construction for pair Logical in the native householder model. -/
def pairLogical (i : Fin 7) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) : Matrix (Fin 8) (Fin 8) ℂ :=
  twoLevelMatrix (.pair 0 ⟨i.val+1,by omega⟩ (Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.rotation p))

/-- The finite construction in `NativeHouseholder` satisfies `zero_ne_succ` under the displayed hypotheses. -/
private theorem zero_ne_succ (i : Fin 7) : (0 : Fin 8) ≠ ⟨i.val+1,by omega⟩ := by
  intro h
  have hh := congrArg Fin.val h
  change 0=i.val+1 at hh
  omega

/-- The actual finite word or frame satisfies `pairLogical_unitary` with all displayed legality, input and workspace hypotheses. -/
theorem pairLogical_unitary (i : Fin 7) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) :
    pairLogical i p ∈ unitaryGroup (Fin 8) ℂ :=
  twoLevel_pair_unitary _ _ _ (zero_ne_succ i)
    (rotation_unitary p)

/-- The finite construction in `NativeHouseholder` satisfies `pairLogical_ket` under the displayed hypotheses. -/
theorem pairLogical_ket (i : Fin 7) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (j : Fin 8) :
    pairLogical i p *ᵥ Qatlib.Foundations.PureStateMath.Ket j =
      if j=0 then (p.c:ℂ) • Qatlib.Foundations.PureStateMath.Ket 0+(p.s:ℂ) • Qatlib.Foundations.PureStateMath.Ket ⟨i.val+1,by omega⟩
      else if j.val=i.val+1 then -(p.s:ℂ) • Qatlib.Foundations.PureStateMath.Ket 0+(p.c:ℂ) • Qatlib.Foundations.PureStateMath.Ket j else Qatlib.Foundations.PureStateMath.Ket j := by
  funext k
  rw [pairLogical,twoLevel_pair_mulVec _ _ _ (zero_ne_succ i)]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [Qatlib.Foundations.PureStateMath.Ket,Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.rotation]

/-- The actual finite word or frame satisfies `pairWord_transport` with all displayed legality, input and workspace hypotheses. -/
theorem pairWord_transport (i : Fin 7) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) :
    program (pairWord i p)*cleanFrame=cleanFrame*pairLogical i p := by
  ext x j
  have h := pairWord_action i p j
  rw [run_eq] at h
  have hr : ApplyGate (program (pairWord i p)) (cleanFrame *ᵥ Qatlib.Foundations.PureStateMath.Ket j) =
      cleanFrame *ᵥ (pairLogical i p *ᵥ Qatlib.Foundations.PureStateMath.Ket j) := by
    rw [cleanFrame_ket,pairLogical_ket]
    split_ifs at h ⊢ <;> simpa only [Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_neg,cleanFrame_ket,neg_smul] using h
  have hh := congrFun hr x
  simp only [ApplyGate,Matrix.mulVec_mulVec] at hh
  simpa only [rect_ket] using hh


/-- Construction for pair Ops in the native householder model. -/
def pairOps (is : List (Fin 7)) (p : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) : List Op :=
  is.flatMap (fun i => pairWord i (p i))

/-- Construction for pair Product in the native householder model. -/
def pairProduct (p : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) : List (Fin 7) → Matrix (Fin 8) (Fin 8) ℂ
  | [] => 1
  | i :: is => pairProduct p is * pairLogical i (p i)

/-- The actual finite word or frame satisfies `pairOps_legal` with all displayed legality, input and workspace hypotheses. -/
theorem pairOps_legal (is : List (Fin 7)) (p : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) :
    ∀ g ∈ pairOps is p, legal g := by
  intro g hg
  obtain ⟨i,hi,hg⟩ := List.mem_flatMap.mp hg
  exact pairWord_legal i (p i) g hg

/-- The actual finite word or frame satisfies `pairProduct_unitary` with all displayed legality, input and workspace hypotheses. -/
theorem pairProduct_unitary (is : List (Fin 7)) (p : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) :
    pairProduct p is ∈ unitaryGroup (Fin 8) ℂ := by
  induction is with
  | nil => exact (unitaryGroup _ ℂ).one_mem
  | cons i is ih => exact (unitaryGroup _ ℂ).mul_mem ih (pairLogical_unitary i (p i))

/-- The actual finite word or frame satisfies `pairOps_transport` with all displayed legality, input and workspace hypotheses. -/
theorem pairOps_transport (is : List (Fin 7)) (p : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) :
    program (pairOps is p)*cleanFrame=cleanFrame*pairProduct p is := by
  induction is with
  | nil => simp [pairOps,pairProduct,program]
  | cons i is ih =>
    simp only [pairOps] at ih
    simp only [pairOps,List.flatMap_cons,program_append,pairProduct]
    rw [Matrix.mul_assoc,pairWord_transport,← Matrix.mul_assoc,ih,Matrix.mul_assoc]

/-- Construction for v Word in the native householder model. -/
def vWord (p : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) : List Op := pairOps (List.finRange 7).reverse p

/-- Construction for v Logical in the native householder model. -/
def vLogical (p : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) : Matrix (Fin 8) (Fin 8) ℂ :=
  pairProduct p (List.finRange 7).reverse

/-- Construction for mcx Zero in the native householder model. -/
def mcxZero : List Op :=
  [.x 0,.x 1,.x 2,.ccx 0 1 4,.ccx 4 2 3,.ccx 0 1 4,.x 2,.x 1,.x 0]

/-- Construction for zero Word in the native householder model. -/
def zeroWord : List Op := mcxZero ++ [.z 3] ++ mcxZero ++ [.z 5]

/-- Construction for zero Logical in the native householder model. -/
def zeroLogical : Matrix (Fin 8) (Fin 8) ℂ := diagonal (fun i => if i=0 then 1 else -1)

/-- The actual finite word or frame satisfies `zeroWord_legal` with all displayed legality, input and workspace hypotheses. -/
theorem zeroWord_legal : ∀ g ∈ zeroWord, legal g := by
  simp [zeroWord,mcxZero,legal]

/-- The finite construction in `NativeHouseholder` satisfies `zeroWord_action` under the displayed hypotheses. -/
theorem zeroWord_action (j : Fin 8) : run zeroWord (Qatlib.Foundations.PureStateMath.Ket (seed j))=
    (if j=0 then (1:ℂ) else -1) • Qatlib.Foundations.PureStateMath.Ket (seed j) := by
  fin_cases j <;> simp [zeroWord,mcxZero,run,act_x,act_z,act_ccx,ccxUpdate,seed]

/-- The actual finite word or frame satisfies `zeroLogical_unitary` with all displayed legality, input and workspace hypotheses. -/
theorem zeroLogical_unitary : zeroLogical ∈ unitaryGroup (Fin 8) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zeroLogical,Matrix.mul_apply,Matrix.diagonal_apply]

/-- The finite construction in `NativeHouseholder` satisfies `zeroLogical_ket` under the displayed hypotheses. -/
theorem zeroLogical_ket (j : Fin 8) : zeroLogical *ᵥ Qatlib.Foundations.PureStateMath.Ket j=
    (if j=0 then (1:ℂ) else -1) • Qatlib.Foundations.PureStateMath.Ket j := by
  funext k
  simp only [zeroLogical,Matrix.mulVec_diagonal]
  by_cases h : k=j
  · subst k
    simp [Qatlib.Foundations.PureStateMath.Ket]
  · simp [Qatlib.Foundations.PureStateMath.Ket,h]

/-- The actual finite word or frame satisfies `zeroWord_transport` with all displayed legality, input and workspace hypotheses. -/
theorem zeroWord_transport : program zeroWord*cleanFrame=cleanFrame*zeroLogical := by
  ext x j
  have h := zeroWord_action j
  rw [run_eq] at h
  have hr : ApplyGate (program zeroWord) (cleanFrame *ᵥ Qatlib.Foundations.PureStateMath.Ket j)=
      cleanFrame *ᵥ (zeroLogical *ᵥ Qatlib.Foundations.PureStateMath.Ket j) := by
    rw [cleanFrame_ket,zeroLogical_ket,Matrix.mulVec_smul,cleanFrame_ket]
    exact h
  have hh := congrFun hr x
  simp only [ApplyGate,Matrix.mulVec_mulVec] at hh
  simpa only [rect_ket] using hh

/-- Construction for prep Word in the native householder model. -/
def prepWord (p : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) : List Op := invWord (vWord p) ++ zeroWord ++ vWord p

/-- Construction for prep Logical in the native householder model. -/
def prepLogical (p : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) : Matrix (Fin 8) (Fin 8) ℂ :=
  vLogical p * zeroLogical * (vLogical p)ᴴ

/-- The actual finite word or frame satisfies `prepWord_legal` with all displayed legality, input and workspace hypotheses. -/
theorem prepWord_legal (p : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) : ∀ g ∈ prepWord p, legal g := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · rcases List.mem_append.mp hg with hg | hg
    · exact invWord_legal _ (pairOps_legal _ _) g hg
    · exact zeroWord_legal g hg
  · exact pairOps_legal _ _ g hg

/-- The actual finite word or frame satisfies `prepLogical_unitary` with all displayed legality, input and workspace hypotheses. -/
theorem prepLogical_unitary (p : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) : prepLogical p ∈ unitaryGroup (Fin 8) ℂ := by
  have hv := pairProduct_unitary (List.finRange 7).reverse p
  exact (unitaryGroup _ ℂ).mul_mem ((unitaryGroup _ ℂ).mul_mem hv zeroLogical_unitary) (adjoint_unitary hv)

/-- All three scratch bits return to their specified seed for every label input. -/
theorem prepWord_transport (p : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) :
    program (prepWord p)*cleanFrame=cleanFrame*prepLogical p := by
  have hleg : ∀ g ∈ vWord p, legal g := pairOps_legal _ _
  have hvu : program (vWord p) ∈ unitaryGroup (Reg 6) ℂ := program_unitary _ hleg
  have hvl : vLogical p ∈ unitaryGroup (Fin 8) ℂ := pairProduct_unitary _ _
  have hv : program (vWord p)*cleanFrame=cleanFrame*vLogical p := pairOps_transport _ _
  have hc : Qatlib.Concepts.Execution.WorkspaceCP.compress cleanFrame (program (vWord p)) cleanFrame=vLogical p := by
    dsimp [Qatlib.Concepts.Execution.WorkspaceCP.compress]
    rw [Matrix.mul_assoc, hv, ← Matrix.mul_assoc, cleanFrame_isometry, Matrix.one_mul]
  have he : Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
      (vLogical p) (program (vWord p)) cleanFrame cleanFrame :=
    ⟨hvu,cleanFrame_isometry,cleanFrame_isometry,hc⟩
  have had := shared_encoding_adjoint (Qatlib.Concepts.BlockEncoding.ProjectedUnitaryEncoding.toBlockEncoding he)
  have hd := shared_frame_defect (vLogical p)ᴴ (program (vWord p))ᴴ cleanFrame 0
    (adjoint_unitary hvl) had
  have hinv : (program (vWord p))ᴴ*cleanFrame=cleanFrame*(vLogical p)ᴴ := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa using hd) (norm_nonneg _)
  simp only [prepWord,program_append,program_invWord _ hleg,prepLogical]
  simp only [Matrix.mul_assoc]
  rw [hinv,← Matrix.mul_assoc (program zeroWord),zeroWord_transport]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (program (vWord p)),hv]
  simp only [Matrix.mul_assoc]

/-- The actual finite word or frame satisfies `prepWord_inverse_transport` with all displayed legality, input and workspace hypotheses. -/
theorem prepWord_inverse_transport (p : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) :
    program (invWord (prepWord p)) * cleanFrame =
      cleanFrame * (prepLogical p)ᴴ := by
  have hleg : ∀ g ∈ prepWord p, legal g := prepWord_legal p
  have hu : program (prepWord p) ∈ unitaryGroup (Reg 6) ℂ :=
    program_unitary _ hleg
  have hl : prepLogical p ∈ unitaryGroup (Fin 8) ℂ :=
    prepLogical_unitary p
  have hc : compress cleanFrame (program (prepWord p)) cleanFrame =
      prepLogical p := by
    dsimp [Qatlib.Concepts.Execution.WorkspaceCP.compress]
    rw [Matrix.mul_assoc, prepWord_transport, ← Matrix.mul_assoc,
      cleanFrame_isometry, Matrix.one_mul]
  have he : Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
      (prepLogical p) (program (prepWord p)) cleanFrame cleanFrame :=
    ⟨hu, cleanFrame_isometry, cleanFrame_isometry, hc⟩
  have had := shared_encoding_adjoint (Qatlib.Concepts.BlockEncoding.ProjectedUnitaryEncoding.toBlockEncoding he)
  have hd := shared_frame_defect (prepLogical p)ᴴ
      (program (prepWord p))ᴴ cleanFrame 0
      (adjoint_unitary hl) had
  have hinv : (program (prepWord p))ᴴ * cleanFrame =
      cleanFrame * (prepLogical p)ᴴ := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa using hd) (norm_nonneg _)
  rw [program_invWord _ hleg]
  exact hinv

/-- The same emitted instruction list satisfies `prepWord_counts` with the displayed gate and query accounting. -/
theorem prepWord_counts (p : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) :
    (prepWord p).length=194 ∧
      ((prepWord p).filter (fun g => match g with | .cry _ _ _ => true | _ => false)).length=14 := by
  constructor <;> rfl

/-- An explicit axis projector, used to identify the entire logical reflection. -/
def seedProjector : Matrix (Fin 8) (Fin 8) ℂ := fun i j => if i=0 then if j=0 then 1 else 0 else 0

/-- The finite construction in `NativeHouseholder` satisfies `zeroLogical_reflection` under the displayed hypotheses. -/
theorem zeroLogical_reflection : zeroLogical=(2:ℂ) • seedProjector-1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [zeroLogical,seedProjector]

/-- Full matrix identity, stronger than merely preparing the right first column. -/
theorem prepLogical_entries (p : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (i j : Fin 8) :
    prepLogical p i j=2*(vLogical p i 0)*star (vLogical p j 0)-(if i=j then 1 else 0) := by
  have hv : vLogical p*(vLogical p)ᴴ=1 := (pairProduct_unitary _ p).2
  have hp : vLogical p*seedProjector*(vLogical p)ᴴ=
      (fun i j : Fin 8 => vLogical p i 0*star (vLogical p j 0)) := by
    ext i j
    simp [Matrix.mul_apply,seedProjector,Matrix.conjTranspose_apply,mul_ite,ite_mul]
  simp only [prepLogical,zeroLogical_reflection,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,hv,hp,Matrix.sub_apply,Matrix.smul_apply,
    Matrix.one_apply,smul_eq_mul]
  ring

/-! The first column below is the vector actually prepared by the logical
Householder.  It is kept separate from `vLogical` because the reflection
axis is `2 * v₀ * v - e₀`, and the LCU weights therefore come from this
column rather than from the intermediate QuantumAlgorithmDev.Concepts.MatrixAccess.MatrixBackend.NativeWords.rotation axis. -/
/-- Construction for prep Axis in the native householder model. -/
def prepAxis (p : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) : Fin 8 → ℂ :=
  fun i => prepLogical p i 0

/-- The finite construction in `NativeHouseholder` satisfies `prepAxis_entries` under the displayed hypotheses. -/
theorem prepAxis_entries (p : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (i : Fin 8) :
    prepAxis p i = 2 * (vLogical p i 0) * star (vLogical p 0 0) -
      (if i = 0 then 1 else 0) := by
  exact prepLogical_entries p i 0

/-- The finite construction in `NativeHouseholder` satisfies `prepLogical_entry_adjoint` under the displayed hypotheses. -/
theorem prepLogical_entry_adjoint (p : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (i j : Fin 8) :
    prepLogical p i j = star (prepLogical p j i) := by
  rw [prepLogical_entries, prepLogical_entries]
  rw [star_sub, StarMul.star_mul]
  simp only [star_star]
  by_cases h : i = j
  · subst j
    simp
    ring
  · have h' : j ≠ i := Ne.symm h
    simp [h, h']
    ring

/-- The finite construction in `NativeHouseholder` satisfies `prepAxis_norm` under the displayed hypotheses. -/
theorem prepAxis_norm (p : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) :
    ∑ i : Fin 8, star (prepAxis p i) * prepAxis p i = 1 := by
  have h := (Matrix.mem_unitaryGroup_iff').mp (prepLogical_unitary p)
  have h00 := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℂ => M 0 0) h
  simpa only [Matrix.star_eq_conjTranspose, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply, RCLike.star_def,
    prepAxis,ite_true] using h00


/-- Construction for mcx Slot2 in the native householder model. -/
def mcxSlot2 : List Op :=
  [.x 0,.x 2,.ccx 0 1 4,.ccx 4 2 3,.ccx 0 1 4,.x 2,.x 0]

/-- Construction for mcx Slot4 in the native householder model. -/
def mcxSlot4 : List Op :=
  [.x 0,.x 1,.ccx 0 1 4,.ccx 4 2 3,.ccx 0 1 4,.x 1,.x 0]

/-- Construction for phase Word in the native householder model. -/
def phaseWord (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) : List Op :=
  mcxZero ++ [.phase 3 p] ++ mcxZero ++ mcxSlot2 ++
    (if slack then [.z 3] else []) ++ mcxSlot2 ++ mcxSlot4 ++ [.z 3] ++ mcxSlot4

/-- Construction for phase Coefficient in the native householder model. -/
def phaseCoefficient (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) : Fin 8 → ℂ :=
  ![phaseScalar p,1,if slack then -1 else 1,1,-1,1,1,1]

/-- Construction for phase Logical in the native householder model. -/
def phaseLogical (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) : Matrix (Fin 8) (Fin 8) ℂ :=
  diagonal (phaseCoefficient p slack)

/-- The actual finite word or frame satisfies `phaseWord_legal` with all displayed legality, input and workspace hypotheses. -/
theorem phaseWord_legal (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) :
    ∀ g ∈ phaseWord p slack, legal g := by
  cases slack <;> simp [phaseWord,mcxZero,mcxSlot2,mcxSlot4,legal]

/-- The finite construction in `NativeHouseholder` satisfies `phaseWord_action` under the displayed hypotheses. -/
theorem phaseWord_action (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) (j : Fin 8) :
    run (phaseWord p slack) (Qatlib.Foundations.PureStateMath.Ket (seed j))=phaseCoefficient p slack j • Qatlib.Foundations.PureStateMath.Ket (seed j) := by
  fin_cases j <;> cases slack <;>
    simp [phaseWord,mcxZero,mcxSlot2,mcxSlot4,phaseCoefficient,run,seed,ccxUpdate]

/-- The finite construction in `NativeHouseholder` satisfies `phaseLogical_ket` under the displayed hypotheses. -/
theorem phaseLogical_ket (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) (j : Fin 8) :
    phaseLogical p slack *ᵥ Qatlib.Foundations.PureStateMath.Ket j=phaseCoefficient p slack j • Qatlib.Foundations.PureStateMath.Ket j := by
  funext k
  simp only [phaseLogical,Matrix.mulVec_diagonal]
  by_cases h : k=j
  · subst k; simp [Qatlib.Foundations.PureStateMath.Ket]
  · simp [Qatlib.Foundations.PureStateMath.Ket,h]

/-- The actual finite word or frame satisfies `phaseWord_transport` with all displayed legality, input and workspace hypotheses. -/
theorem phaseWord_transport (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) :
    program (phaseWord p slack)*cleanFrame=cleanFrame*phaseLogical p slack := by
  ext x j
  have h := phaseWord_action p slack j
  rw [run_eq] at h
  have hr : ApplyGate (program (phaseWord p slack)) (cleanFrame *ᵥ Qatlib.Foundations.PureStateMath.Ket j)=
      cleanFrame *ᵥ (phaseLogical p slack *ᵥ Qatlib.Foundations.PureStateMath.Ket j) := by
    rw [cleanFrame_ket,phaseLogical_ket,Matrix.mulVec_smul,cleanFrame_ket]
    exact h
  have hh := congrFun hr x
  simp only [ApplyGate,Matrix.mulVec_mulVec] at hh
  simpa only [rect_ket] using hh

/-- The actual finite word or frame satisfies `phaseLogical_unitary` with all displayed legality, input and workspace hypotheses. -/
theorem phaseLogical_unitary (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) :
    phaseLogical p slack ∈ unitaryGroup (Fin 8) ℂ := by
  have hn := phaseScalar_norm p
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
  unfold phaseLogical
  rw [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal,← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> cases slack <;>
    simp [phaseCoefficient,RCLike.star_def,← Complex.normSq_eq_conj_mul_self,hn]

/-- The actual finite word or frame satisfies `phaseWord_inverse_transport` with all displayed legality, input and workspace hypotheses. -/
theorem phaseWord_inverse_transport (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) :
    program (invWord (phaseWord p slack)) * cleanFrame =
      cleanFrame * (phaseLogical p slack)ᴴ := by
  have hleg : ∀ g ∈ phaseWord p slack, legal g := phaseWord_legal p slack
  have hu : program (phaseWord p slack) ∈ unitaryGroup (Reg 6) ℂ :=
    program_unitary _ hleg
  have hl : phaseLogical p slack ∈ unitaryGroup (Fin 8) ℂ :=
    phaseLogical_unitary p slack
  have hc : compress cleanFrame (program (phaseWord p slack)) cleanFrame =
      phaseLogical p slack := by
    dsimp [Qatlib.Concepts.Execution.WorkspaceCP.compress]
    rw [Matrix.mul_assoc, phaseWord_transport, ← Matrix.mul_assoc,
      cleanFrame_isometry, Matrix.one_mul]
  have he : Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
      (phaseLogical p slack) (program (phaseWord p slack)) cleanFrame cleanFrame :=
    ⟨hu, cleanFrame_isometry, cleanFrame_isometry, hc⟩
  have had := shared_encoding_adjoint (Qatlib.Concepts.BlockEncoding.ProjectedUnitaryEncoding.toBlockEncoding he)
  have hd := shared_frame_defect (phaseLogical p slack)ᴴ
      (program (phaseWord p slack))ᴴ cleanFrame 0
      (adjoint_unitary hl) had
  have hinv : (program (phaseWord p slack))ᴴ * cleanFrame =
      cleanFrame * (phaseLogical p slack)ᴴ := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa using hd) (norm_nonneg _)
  rw [program_invWord _ hleg]
  exact hinv

/-- The actual finite word or frame satisfies `known_inverse_transport` with all displayed legality, input and workspace hypotheses. -/
theorem known_inverse_transport (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) :
    program (invWord (phaseWord p slack)) *
      program (invWord (prepWord ps)) * cleanFrame =
      cleanFrame * (phaseLogical p slack)ᴴ * (prepLogical ps)ᴴ := by
  rw [Matrix.mul_assoc, prepWord_inverse_transport]
  rw [← Matrix.mul_assoc, phaseWord_inverse_transport]

/-- The same emitted instruction list satisfies `phaseWord_counts` with the displayed gate and query accounting. -/
theorem phaseWord_counts (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) :
    (phaseWord p slack).length=48+(if slack then 1 else 0) ∧
      ((phaseWord p slack).filter (fun g => match g with | .phase _ _ => true | _ => false)).length=1 := by
  cases slack <;> constructor <;> rfl

/-- The exact native inner body matrix on the clean seed, including its fixed phase convention. -/
def innerBodyLogical (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) (U : Matrix Bool Bool ℂ) :
    Matrix (Fin 8 × Bool) (Fin 8 × Bool) ℂ :=
  (TensorGate (prepLogical ps) (1 : Matrix Bool Bool ℂ)) *
    (TensorGate (phaseLogical p slack) (1 : Matrix Bool Bool ℂ)) *
    BlockDiag (fun j : Fin 8 => if j.val < 4 then 1 else U) *
    TensorGate (prepLogical ps) (1 : Matrix Bool Bool ℂ)

/-- The finite construction in `NativeHouseholder` satisfies `tensor_block_entry` under the displayed hypotheses. -/
theorem tensor_block_entry (A B : Matrix (Fin 8) (Fin 8) ℂ)
    (D : Fin 8 → Matrix Bool Bool ℂ) (j k : Fin 8) (d e : Bool) :
    (TensorGate A (1 : Matrix Bool Bool ℂ) *
      BlockDiag D * TensorGate B (1 : Matrix Bool Bool ℂ)) (j,d) (k,e) =
      ∑ l : Fin 8, A j l * D l d e * B l k := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, TensorGate, BlockDiag,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.of_apply]
  simp

/-- The finite construction in `NativeHouseholder` satisfies `innerBodyLogical_entry` under the displayed hypotheses. -/
theorem innerBodyLogical_entry (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool)
    (U : Matrix Bool Bool ℂ) (j k : Fin 8) (d e : Bool) :
    innerBodyLogical ps p slack U (j,d) (k,e) =
      ∑ l : Fin 8, prepLogical ps j l * phaseCoefficient p slack l *
        (if l.val < 4 then (if d = e then 1 else 0) else U d e) * prepLogical ps l k := by
  rw [innerBodyLogical]
  rw [show TensorGate (prepLogical ps) (1 : Matrix Bool Bool ℂ) *
      TensorGate (phaseLogical p slack) (1 : Matrix Bool Bool ℂ) =
      TensorGate (prepLogical ps * phaseLogical p slack) (1 : Matrix Bool Bool ℂ) by
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
  · by_cases hde : d = e <;> simp [hl, Matrix.one_apply, hde]
  · simp [hl]

/-- Construction for clean Slot Frame in the native householder model. -/
def cleanSlotFrame : Matrix (Fin 8 × Bool) Bool ℂ :=
  fun x b => if x = (0,b) then 1 else 0

/-- The finite construction in `NativeHouseholder` satisfies `phaseCoefficient_nonzero` under the displayed hypotheses. -/
theorem phaseCoefficient_nonzero (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) (l : Fin 8) :
    phaseCoefficient p slack l ≠ 0 := by
  have hp : phaseScalar p ≠ 0 := by
    intro h
    have hn := phaseScalar_norm p
    rw [h] at hn
    norm_num at hn
  fin_cases l <;> cases slack <;> simp [phaseCoefficient, hp]

/-- Construction for effective Coefficients in the native householder model. -/
def effectiveCoefficients (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) : Fin 8 → ℂ :=
  fun l => star (prepAxis ps l) * phaseCoefficient p slack l * prepAxis ps l

/-- Construction for effective Selector in the native householder model. -/
def effectiveSelector (U : Matrix Bool Bool ℂ) : Fin 8 → Matrix Bool Bool ℂ :=
  fun l => if l.val < 4 then 1 else U

/-- Construction for effective Block in the native householder model. -/
def effectiveBlock (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool)
    (U : Matrix Bool Bool ℂ) : Matrix Bool Bool ℂ :=
  ∑ l : Fin 8, effectiveCoefficients ps p slack l • effectiveSelector U l

/-- The finite construction in `NativeHouseholder` satisfies `effectiveCoefficients_mass_pos` under the displayed hypotheses. -/
theorem effectiveCoefficients_mass_pos (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) :
    0 < coefficientMass (effectiveCoefficients ps p slack) := by
  rw [coefficientMass_pos_iff]
  have hu : ∃ l : Fin 8, prepAxis ps l ≠ 0 := by
    by_contra h
    have hzero : ∀ l : Fin 8, prepAxis ps l = 0 := by
      intro l
      by_contra hl
      exact h ⟨l, hl⟩
    have hn := prepAxis_norm ps
    simp [hzero] at hn
  obtain ⟨l, hl⟩ := hu
  refine ⟨l, ?_⟩
  simp only [effectiveCoefficients]
  exact mul_ne_zero (mul_ne_zero ((star_ne_zero).mpr hl)
    (phaseCoefficient_nonzero p slack l)) hl

/-- The actual finite word or frame satisfies `effectiveBlock_lcu_compress` with all displayed legality, input and workspace hypotheses. -/
theorem effectiveBlock_lcu_compress (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool)
    (U : Matrix Bool Bool ℂ)
    (hm : 0 < coefficientMass (effectiveCoefficients ps p slack)) :
    compress (prepareLift (I := Bool) (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 8)))
      (coefficientLCUUnitary (effectiveCoefficients ps p slack)
        (effectiveSelector U) 0)
      (prepareLift (I := Bool) (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 8))) =
      ((coefficientMass (effectiveCoefficients ps p slack) : ℂ)⁻¹) •
        effectiveBlock ps p slack U := by
  rw [coefficientLCUUnitary_compress _ _ _ hm]
  simp only [effectiveBlock, effectiveCoefficients, effectiveSelector,
    Finset.smul_sum, smul_smul]
  congr 1
  funext l
  simp [div_eq_mul_inv, mul_comm, mul_left_comm]

/-- The actual finite word or frame satisfies `effectiveBlock_lcu_compress_auto` with all displayed legality, input and workspace hypotheses. -/
theorem effectiveBlock_lcu_compress_auto (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool)
    (U : Matrix Bool Bool ℂ) :
    compress (prepareLift (I := Bool) (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 8)))
      (coefficientLCUUnitary (effectiveCoefficients ps p slack)
        (effectiveSelector U) 0)
      (prepareLift (I := Bool) (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 8))) =
      ((coefficientMass (effectiveCoefficients ps p slack) : ℂ)⁻¹) •
        effectiveBlock ps p slack U := by
  exact effectiveBlock_lcu_compress ps p slack U
    (effectiveCoefficients_mass_pos ps p slack)

/-- The actual finite word or frame satisfies `effectiveSelector_unitary` with all displayed legality, input and workspace hypotheses. -/
theorem effectiveSelector_unitary (U : Matrix Bool Bool ℂ)
    (hU : U ∈ unitaryGroup Bool ℂ) (l : Fin 8) :
    effectiveSelector U l ∈ unitaryGroup Bool ℂ := by
  by_cases hl : l.val < 4 <;> simp [effectiveSelector, hl, hU]

/-- The actual finite word or frame satisfies `effectiveBlock_projectedEncoding` with all displayed legality, input and workspace hypotheses. -/
theorem effectiveBlock_projectedEncoding (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool)
    (U : Matrix Bool Bool ℂ) (hU : U ∈ unitaryGroup Bool ℂ) :
    ProjectedUnitaryEncoding
      (((coefficientMass (effectiveCoefficients ps p slack) : ℂ)⁻¹) •
        effectiveBlock ps p slack U)
      (coefficientLCUUnitary (effectiveCoefficients ps p slack)
        (effectiveSelector U) 0)
      (prepareLift (I := Bool) (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 8)))
      (prepareLift (I := Bool) (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 8))) := by
  have hm := effectiveCoefficients_mass_pos ps p slack
  have h := coefficientLCUUnitary_projectedEncoding
    (effectiveCoefficients ps p slack) (effectiveSelector U) 0 hm
    (effectiveSelector_unitary U hU)
  refine ⟨h.unitary, h.left_isometry, h.right_isometry, ?_⟩
  rw [h.encoded]
  simp only [effectiveBlock, Finset.smul_sum, effectiveCoefficients,
    effectiveSelector, smul_smul]
  congr 1
  funext l
  simp [div_eq_mul_inv, mul_comm, mul_left_comm]

/-- The actual finite word or frame satisfies `effectiveBlock_neumann_encoding` with all displayed legality, input and workspace hypotheses. -/
theorem effectiveBlock_neumann_encoding (b : ℕ) (hb : 0 < b)
    (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool)
    (Udata : Matrix Bool Bool ℂ) (hUdata : Udata ∈ unitaryGroup Bool ℂ) :
    ProjectedUnitaryEncoding
      (((b : ℂ)⁻¹) • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann
        (((coefficientMass (effectiveCoefficients ps p slack) : ℂ)⁻¹) •
          effectiveBlock ps p slack Udata) b)
      (evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle (b-1)
        (parallelOracle (J := Fin b)
          (coefficientLCUUnitary (effectiveCoefficients ps p slack)
            (effectiveSelector Udata) 0)))
        (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannWord b hb (rangeProjector
          (prepareLift (I := Bool) (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 8))))))
      (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb
        (prepareLift (I := Bool) (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 8))))
      (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb
        (prepareLift (I := Bool) (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 8)))) := by
  let F : Matrix (Fin 8 × Bool) Bool ℂ :=
    prepareLift (I := Bool) (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 8))
  let V : Matrix (Fin 8 × Bool) (Fin 8 × Bool) ℂ :=
    coefficientLCUUnitary (effectiveCoefficients ps p slack)
      (effectiveSelector Udata) 0
  have hV : V ∈ unitaryGroup (Fin 8 × Bool) ℂ :=
    (effectiveBlock_projectedEncoding ps p slack Udata hUdata).unitary
  have hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F :=
    (effectiveBlock_projectedEncoding ps p slack Udata hUdata).right_isometry
  have hN := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniform_neumann_word_encoding
    (H := Fin 8 × Bool) (I := Bool) b hb V F hV hF
  have hcorner := (effectiveBlock_projectedEncoding ps p slack Udata hUdata).encoded
  rw [hcorner] at hN
  simpa [F, V] using hN

/-- The actual finite word or frame satisfies `cleanSlotFrame_compress` with all displayed legality, input and workspace hypotheses. -/
theorem cleanSlotFrame_compress (A : Matrix (Fin 8 × Bool) (Fin 8 × Bool) ℂ)
    (d e : Bool) : compress cleanSlotFrame A cleanSlotFrame d e = A (0,d) (0,e) := by
  classical
  simp [compress, cleanSlotFrame, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- The actual finite word or frame satisfies `innerBodyLogical_clean_compress` with all displayed legality, input and workspace hypotheses. -/
theorem innerBodyLogical_clean_compress (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool)
    (U : Matrix Bool Bool ℂ) :
    compress cleanSlotFrame (innerBodyLogical ps p slack U) cleanSlotFrame =
      effectiveBlock ps p slack U := by
  have hadj (l : Fin 8) : prepLogical ps 0 l = star (prepAxis ps l) := by
    rw [prepLogical_entry_adjoint, prepAxis]
  have hcol (l : Fin 8) : prepLogical ps l 0 = prepAxis ps l := rfl
  ext d e
  rw [cleanSlotFrame_compress, innerBodyLogical_entry]
  simp only [effectiveBlock, effectiveCoefficients, effectiveSelector,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [hadj]
  simp_rw [hcol]
  apply Finset.sum_congr rfl
  intro l
  by_cases hl : l.val < 4
  · by_cases hde : d = e <;> simp [hl, Matrix.one_apply, hde]
  · simp [hl]
    ring

/-- The actual finite word or frame satisfies `innerBodyLogical_unitary` with all displayed legality, input and workspace hypotheses. -/
theorem innerBodyLogical_unitary (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool)
    (U : Matrix Bool Bool ℂ) (hU : U ∈ unitaryGroup Bool ℂ) :
    innerBodyLogical ps p slack U ∈ unitaryGroup (Fin 8 × Bool) ℂ := by
  have hp : TensorGate (prepLogical ps) (1 : Matrix Bool Bool ℂ)
      ∈ unitaryGroup (Fin 8 × Bool) ℂ :=
    tensorGate_unitary (prepLogical_unitary ps) (unitaryGroup _ ℂ).one_mem
  have hh : TensorGate (phaseLogical p slack) (1 : Matrix Bool Bool ℂ)
      ∈ unitaryGroup (Fin 8 × Bool) ℂ :=
    tensorGate_unitary (phaseLogical_unitary p slack) (unitaryGroup _ ℂ).one_mem
  have hs : BlockDiag (fun j : Fin 8 => if j.val < 4 then 1 else U)
      ∈ unitaryGroup (Fin 8 × Bool) ℂ := by
    apply blockDiag_unitary
    intro j
    split <;> first | exact (unitaryGroup _ ℂ).one_mem | exact hU
  exact (unitaryGroup _ ℂ).mul_mem
    ((unitaryGroup _ ℂ).mul_mem ((unitaryGroup _ ℂ).mul_mem hp hh) hs) hp

/-- Little-endian slot bits agree with the pinned Bool x Fin4 representation. -/
def slotEquiv : Fin 8 ≃ (Bool × Fin 4) where
  toFun := ![(false,0),(false,1),(false,2),(false,3),(true,0),(true,1),(true,2),(true,3)]
  invFun x := if x.1 then ⟨x.2.val+4,by omega⟩ else ⟨x.2.val,by omega⟩
  left_inv i := by fin_cases i <;> rfl
  right_inv x := by obtain ⟨b,i⟩ := x; cases b <;> fin_cases i <;> rfl

/-- The finite construction in `NativeHouseholder` satisfies `effectiveSelector_slotEquiv` under the displayed hypotheses. -/
theorem effectiveSelector_slotEquiv (U : Matrix Bool Bool ℂ) (s : Bool × Fin 4) :
    effectiveSelector U (slotEquiv.symm s) =
      Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftSlotMatrix U s := by
  obtain ⟨b, i⟩ := s
  cases b <;> fin_cases i <;> simp [effectiveSelector,
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftSlotMatrix, slotEquiv]

/-- Construction for native Shift Slot Equiv in the native householder model. -/
def nativeShiftSlotEquiv : (Fin 8 × Bool) ≃
    (Unit × ((Bool × Fin 4) × Bool)) where
  toFun x := ((), (slotEquiv x.1, x.2))
  invFun y := (slotEquiv.symm y.2.1, y.2.2)
  left_inv x := by cases x; simp
  right_inv y := by obtain ⟨u, s, b⟩ := y; cases u; simp

/-- The finite construction in `NativeHouseholder` satisfies `effectiveSelector_relabel_shiftedSelect` under the displayed hypotheses. -/
theorem effectiveSelector_relabel_shiftedSelect (U : Matrix Bool Bool ℂ) :
    relabelGate nativeShiftSlotEquiv
      (BlockDiag (fun j : Fin 8 => effectiveSelector U j)) =
      Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.shiftedSelect (L := Unit) U := by
  ext x y
  obtain ⟨u, s, b⟩ := x
  obtain ⟨v, t, c⟩ := y
  cases u; cases v
  simp [relabelGate, nativeShiftSlotEquiv, BlockDiag,
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.shiftedSelect,
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftSlotMatrix,
    Qatlib.Concepts.BlockEncoding.LCU.select]
  rw [effectiveSelector_slotEquiv]
  by_cases h : s = t
  · subst t
    simp [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shiftSlotMatrix]
  · simp [h]

/-- The finite construction in `NativeHouseholder` satisfies `seed_control` under the displayed hypotheses. -/
theorem seed_control (i : Fin 8) : seed i 2=(slotEquiv i).1 := by fin_cases i <;> rfl

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep
