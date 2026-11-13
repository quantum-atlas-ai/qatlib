/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Execution.WorkspaceCP.WorkspaceCircuit
import Qatlib.Concepts.AdversaryBounds.AdvDuality.WorkspaceMachine
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ResourceBoundsTransportLiveWire
import Qatlib.Concepts.ReferenceError.DensityToRaw.ChannelTraceContraction
import Qatlib.Concepts.QsvtCore.QueryLowerBound.ScalarSignalConsumers

/-!
# Clean auxiliary release and workspace accounting

This module implements clean phase operations by allocating an auxiliary qubit, applying a
four-gate compute-phase-uncompute sequence, and releasing the auxiliary register. It proves the
resulting data action, including with a reference register, and extends workspace traces with
gate, instrument, and peak auxiliary-use records. The gate and instrument constructions follow
the standard framework of [NielsenChuang2010].

Compiled clean-operation words have unique specified traces and exact resource costs. Further
examples realize Chebyshev responses using repeated scalar-signal queries and a bounded stopping
program whose rejected mass decays geometrically for unitary oracles.

## Main statements

* `cleanPhase_reference`: the clean phase implements the data action on joint states with a
  reference.
* `compileWord_measured`: compiled words have the specified measured trace.
* `wordTrace_resources`: trace resources agree with the word's declared cost.
* `chebyshevOps_response`: the scalar response equals a Chebyshev polynomial.
* `stoppingProgram_failed_mass`: rejected mass is `2⁻ʰ` times the input's real trace.
* `frontier1` and `frontier2`: collect the word-compilation and bounded-stopping guarantees.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.ReferenceError.DensityToRaw
open Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.BlockEncoding.EncodingCore

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.WorkspaceCleanRelease
open Matrix
open scoped Classical ComplexOrder BigOperators Kronecker Matrix.Norms.L2Operator
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

/-- The column vector for a computational basis state of a two-dimensional auxiliary register. -/
def auxiliaryKet (b : Fin 2) : Matrix (Fin 2) (Fin 1) ℂ :=
  fun a _ => if a=b then 1 else 0

/-- Each auxiliary basis column is an isometry from the one-dimensional space. -/
theorem auxiliaryKet_isometry (b : Fin 2) : (auxiliaryKet b)ᴴ*auxiliaryKet b = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  fin_cases b <;> norm_num [auxiliaryKet, Matrix.mul_apply, Fin.sum_univ_two]

/-- The outer products of the two auxiliary basis columns sum to the identity. -/
theorem auxiliaryKet_complete : (∑ b : Fin 2, auxiliaryKet b*(auxiliaryKet b)ᴴ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [auxiliaryKet, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_one]

/-- The reindexed tensor-product frame that attaches the chosen auxiliary basis state to a data
register. -/
def allocationFrame (d : ℕ) (b : Fin 2) : Matrix (Fin (d*2)) (Fin (d*1)) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv ((1 : Operator d) ⊗ₖ auxiliaryKet b)

/-- Attaching a fixed auxiliary basis state defines an isometry. -/
theorem allocationFrame_isometry (d : ℕ) (b : Fin 2) :
    (allocationFrame d b)ᴴ*allocationFrame d b = 1 := by
  unfold allocationFrame
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_one, Matrix.one_mul,
    auxiliaryKet_isometry, Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

/-- The projections onto the two auxiliary-state frames sum to the identity on the enlarged
space. -/
theorem allocationFrame_complete (d : ℕ) :
    (∑ b : Fin 2, allocationFrame d b*(allocationFrame d b)ᴴ) = 1 := by
  unfold allocationFrame
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_one, Matrix.one_mul]
  have hsum : (∑ b : Fin 2, (1 : Operator d) ⊗ₖ (auxiliaryKet b*(auxiliaryKet b)ᴴ)) =
      (1 : Operator d) ⊗ₖ (∑ b : Fin 2, auxiliaryKet b*(auxiliaryKet b)ᴴ) := by
    ext i j
    simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, mul_add]
  calc
    _ = (∑ b : Fin 2, (1 : Operator d) ⊗ₖ (auxiliaryKet b*(auxiliaryKet b)ᴴ)).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm := by
      ext i j
      simp only [Matrix.sum_apply, Matrix.submatrix_apply]
    _ = _ := by rw [hsum, auxiliaryKet_complete, Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

/-- The single-outcome instrument that allocates an auxiliary qubit in basis state zero. -/
def allocate (d : ℕ) : Instrument (Fin 1) (d*1) (d*2) :=
  Instrument.ofKraus (fun _ => allocationFrame d 0)
    (by simpa only [Fin.sum_univ_one] using! allocationFrame_isometry d 0)

/-- The instrument that reads the auxiliary computational basis value and removes the auxiliary
register. -/
def readRelease (d : ℕ) : Instrument (Fin 2) (d*2) (d*1) :=
  Instrument.ofKraus (fun b => (allocationFrame d b)ᴴ)
    (by simpa only [Matrix.conjTranspose_conjTranspose] using! allocationFrame_complete d)

/-- The single-outcome release instrument obtained by forgetting the read-release outcome. -/
def release (d : ℕ) : Instrument (Fin 1) (d*2) (d*1) :=
  (readRelease d).coarsen (fun _ => (0 : Fin 1))

/-- The allocation branch conjugates the input by the zero-state allocation frame. -/
@[simp] theorem allocate_branch (d : ℕ) (ρ : Operator (d*1)) :
    (allocate d).branch 0 ρ = allocationFrame d 0*ρ*(allocationFrame d 0)ᴴ := rfl

/-- A read-release branch conjugates the input by the adjoint of the selected allocation frame. -/
@[simp] theorem readRelease_branch (d : ℕ) (b : Fin 2) (ρ : Operator (d*2)) :
    (readRelease d).branch b ρ = (allocationFrame d b)ᴴ*ρ*allocationFrame d b := by
  rw [readRelease, Instrument.ofKraus_branch, Matrix.conjTranspose_conjTranspose]

/-- The release branch is the sum of the two read-release branch conjugations. -/
theorem release_branch (d : ℕ) (ρ : Operator (d*2)) :
    (release d).branch 0 ρ = ∑ b : Fin 2, (allocationFrame d b)ᴴ*ρ*allocationFrame d b := by
  simp only [release, Instrument.coarsen, LinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun b _ => readRelease_branch d b ρ)

/-- The auxiliary basis columns for one and zero are orthogonal. -/
theorem auxiliaryKet_one_zero : (auxiliaryKet 1)ᴴ*auxiliaryKet 0 = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [auxiliaryKet, Matrix.mul_apply, Fin.sum_univ_two]

/-- The allocation frames for auxiliary states one and zero have zero cross product. -/
theorem allocationFrame_one_zero (d : ℕ) :
    (allocationFrame d 1)ᴴ*allocationFrame d 0 = 0 := by
  unfold allocationFrame
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_one, Matrix.one_mul,
    auxiliaryKet_one_zero, Matrix.kronecker_zero, Matrix.submatrix_zero]
  rfl

/-- Reading and releasing a freshly allocated zero auxiliary qubit returns the input in outcome
zero and yields zero in outcome one. -/
theorem readRelease_clean (d : ℕ) (ρ : Operator (d*1)) :
    (readRelease d).branch 0 ((allocate d).branch 0 ρ) = ρ ∧
    (readRelease d).branch 1 ((allocate d).branch 0 ρ) = 0 := by
  have he (b : Fin 2) :
      (allocationFrame d b)ᴴ * (allocationFrame d 0*ρ*(allocationFrame d 0)ᴴ) * allocationFrame d b =
      ((allocationFrame d b)ᴴ*allocationFrame d 0)*ρ*((allocationFrame d b)ᴴ*allocationFrame d 0)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  constructor
  · rw [allocate_branch, readRelease_branch, he 0, allocationFrame_isometry]
    simp
  · rw [allocate_branch, readRelease_branch, he 1, allocationFrame_one_zero]
    simp

/-- Releasing a freshly allocated zero auxiliary qubit returns the original input. -/
theorem release_clean (d : ℕ) (ρ : Operator (d*1)) :
    (release d).branch 0 ((allocate d).branch 0 ρ) = ρ := by
  rw [release_branch, Fin.sum_univ_two]
  rw [← readRelease_branch d 0, ← readRelease_branch d 1]
  rw [(readRelease_clean d ρ).1, (readRelease_clean d ρ).2, _root_.add_zero]

/-- Identifies an `n`-bit register with the native data space carrying a one-dimensional
auxiliary factor. -/
def baseLayout (n : ℕ) : Reg n ≃ Fin ((2^n)*1) where
  toFun x := finProdFinEquiv (bitVecEquiv n x, (0 : Fin 1))
  invFun a := (bitVecEquiv n).symm (finProdFinEquiv.symm a).1
  left_inv x := by simp
  right_inv a := by
    apply finProdFinEquiv.symm.injective
    apply Prod.ext
    · simp
    · exact Subsingleton.elim _ _

/-- Identifies an `(n + 1)`-bit register with the native data space carrying a two-dimensional
auxiliary factor. -/
def registerLayout (n : ℕ) : Reg (n+1) ≃ Fin ((2^n)*2) :=
  (regSuccEquiv n).trans
    ((Equiv.prodCongr (bitVecEquiv n) boolEquivFin2).trans finProdFinEquiv)

/-- Under the successor-register decomposition, each original register coordinate retains its
value. -/
@[simp] theorem split_front (n : ℕ) (x : Reg n) (b : Bool) (i : Fin n) :
    (regSuccEquiv n).symm (x,b) i.castSucc = x i := by
  have h := (regSuccEquiv n).apply_symm_apply (x,b)
  exact congrArg (fun p : Reg n × Bool => p.1 i) h

/-- Under the successor-register decomposition, the final coordinate equals the appended Boolean
value. -/
@[simp] theorem split_last (n : ℕ) (x : Reg n) (b : Bool) :
    (regSuccEquiv n).symm (x,b) (Fin.last n) = b := by
  have h := (regSuccEquiv n).apply_symm_apply (x,b)
  exact congrArg (fun p : Reg n × Bool => p.2) h

/-- In register coordinates, the zero-state allocation frame is the indicator of matching data
and a false auxiliary bit. -/
theorem allocationFrame_register (n : ℕ) (p : Reg (n+1)) (x : Reg n) :
    allocationFrame (2^n) 0 (registerLayout n p) (baseLayout n x) =
      if (regSuccEquiv n p).1=x ∧ (regSuccEquiv n p).2=false then 1 else 0 := by
  simp only [allocationFrame, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, baseLayout, Equiv.coe_fn_mk, registerLayout,
    Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.symm_apply_apply,
    Matrix.one_apply, auxiliaryKet, Prod.map_fst, Prod.map_snd]
  have hx : (bitVecEquiv n (regSuccEquiv n p).1 = bitVecEquiv n x) ↔ (regSuccEquiv n p).1=x :=
    (bitVecEquiv n).injective.eq_iff
  simp only [hx]
  by_cases hb : (regSuccEquiv n p).2=false
  · by_cases hp : (regSuccEquiv n p).1=x <;> simp [boolEquivFin2,hb,hp]
  · have ht : (regSuccEquiv n p).2=true := Bool.eq_true_of_not_eq_false hb
    by_cases hp : (regSuccEquiv n p).1=x <;> simp [boolEquivFin2,ht,hp]

/-- The four-code sequence consisting of a controlled X, two auxiliary T gates, and a second
controlled X. -/
def phaseCodes (n : ℕ) (i : Fin n) : List FiniteGateCode :=
  [.cx i.val n, .t n, .t n, .cx i.val n]

/-- The four-code phase sequence is legal on the enlarged register. -/
theorem phaseCodes_legal (n : ℕ) (i : Fin n) : finiteWordLegal (n+1) (phaseCodes n i) = true := by
  simp [finiteWordLegal, phaseCodes, finiteCodeLegal]
  omega

/-- The controlled-X matrix that copies the selected data bit into the final auxiliary bit by
Boolean addition. -/
def computeReg (n : ℕ) (i : Fin n) : Matrix (Reg (n+1)) (Reg (n+1)) ℂ :=
  cnotGate (n+1) i.castSucc (Fin.last n)

/-- The controlled-X finite gate code evaluates to `computeReg`. -/
theorem computeReg_code (n : ℕ) (i : Fin n) :
    finiteCodeMatrix (n+1) (.cx i.val n) = computeReg n i := by
  have h : i.val < n+1 ∧ n < n+1 ∧ i.val ≠ n := by omega
  rw [finiteCodeMatrix, dif_pos h]
  rfl

/-- Updating the final register bit by exclusive-or with a selected data bit changes only the
auxiliary component of the split register. -/
theorem compute_split (n : ℕ) (i : Fin n) (x : Reg n) (b : Bool) :
    Function.update ((regSuccEquiv n).symm (x,b)) (Fin.last n)
        (((regSuccEquiv n).symm (x,b)) (Fin.last n) ^^ ((regSuccEquiv n).symm (x,b)) i.castSucc) =
      (regSuccEquiv n).symm (x,b ^^ x i) := by
  funext k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · simp
  · simp [Fin.castSucc_ne_last]

/-- Embeds a data-state vector into the subspace with auxiliary bit false. -/
def cleanReg (n : ℕ) (ψ : QState (Reg n)) : QState (Reg (n+1)) :=
  fun p => if (regSuccEquiv n p).2 then 0 else ψ (regSuccEquiv n p).1

/-- The controlled-X matrix acts on amplitudes by toggling the auxiliary coordinate according to
the selected data bit. -/
theorem computeReg_apply (n : ℕ) (i : Fin n) (ψ : QState (Reg (n+1))) (x : Reg n) (b : Bool) :
    ApplyGate (computeReg n i) ψ ((regSuccEquiv n).symm (x,b)) =
      ψ ((regSuccEquiv n).symm (x,b ^^ x i)) := by
  rw [computeReg, cnotGate, applyGate_permMatrix (cnotUpdate_involutive _ _ _ (Fin.castSucc_ne_last i)),
    compute_split]

/-- Embedding a diagonal one-qubit gate on a wire yields the diagonal matrix obtained by reading
that wire. -/
theorem wireGate_diagonal (n : ℕ) (i : Fin n) (f : Bool → ℂ) :
    wireGate n i (diagonal f) = diagonal (fun x : Reg n => f (x i)) := by
  ext x y
  rw [wireGate_apply]
  by_cases hxy : x=y
  · subst y
    simp
  · have h : ¬((∀ j : Fin n, j ≠ i → x j=y j) ∧ x i=y i) := by
      rintro ⟨hr,hi⟩
      apply hxy
      funext j
      by_cases hj : j=i
      · simpa only [hj] using! hi
      · exact hr j hj
    by_cases hr : ∀ j : Fin n, j ≠ i → x j=y j
    · have hi : x i ≠ y i := fun hi => h ⟨hr,hi⟩
      simp [hi,hxy]
    · simp [hr,hxy]

/-- A diagonal wire gate multiplies each amplitude by the diagonal entry selected by that wire's
bit. -/
theorem diagonal_wire_apply (n : ℕ) (i : Fin n) (f : Bool → ℂ) (ψ : QState (Reg n)) (x : Reg n) :
    ApplyGate (wireGate n i (diagonal f)) ψ x = f (x i)*ψ x := by
  rw [wireGate_diagonal]
  simp [ApplyGate, Matrix.mulVec_diagonal]

/-- The diagonal T-gate phase, equal to `exp (i * pi / 4)` on true and one on false. -/
def tScalar (b : Bool) : ℂ := if b then Complex.exp (((Real.pi/4 : ℝ) : ℂ)*Complex.I) else 1

/-- The enlarged-register matrix for computing a data bit into the auxiliary bit, applying two T
gates, and uncomputing. -/
def phaseReg (n : ℕ) (i : Fin n) : Matrix (Reg (n+1)) (Reg (n+1)) ℂ :=
  computeReg n i * wireGate (n+1) (Fin.last n) tGate *
    wireGate (n+1) (Fin.last n) tGate * computeReg n i

/-- The data-register matrix that applies the square of the T gate to the selected wire. -/
def dataPhaseReg (n : ℕ) (i : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  wireGate n i (tGate*tGate)

/-- On a clean auxiliary register, the four-gate phase construction implements the data phase
and restores the auxiliary bit to false. -/
theorem phaseReg_clean (n : ℕ) (i : Fin n) (ψ : QState (Reg n)) :
    ApplyGate (phaseReg n i) (cleanReg n ψ) = cleanReg n (ApplyGate (dataPhaseReg n i) ψ) := by
  funext p
  obtain ⟨⟨x,b⟩,rfl⟩ := (regSuccEquiv n).symm.surjective p
  simp only [phaseReg, ApplyGate, ← Matrix.mulVec_mulVec]
  change ApplyGate (computeReg n i)
    (ApplyGate (wireGate (n+1) (Fin.last n) tGate)
      (ApplyGate (wireGate (n+1) (Fin.last n) tGate)
        (ApplyGate (computeReg n i) (cleanReg n ψ)))) ((regSuccEquiv n).symm (x,b)) = _
  rw [computeReg_apply]
  change ApplyGate (wireGate (n+1) (Fin.last n) (diagonal tScalar))
    (ApplyGate (wireGate (n+1) (Fin.last n) (diagonal tScalar))
      (ApplyGate (computeReg n i) (cleanReg n ψ))) ((regSuccEquiv n).symm (x,b ^^ x i)) = _
  rw [diagonal_wire_apply, diagonal_wire_apply, computeReg_apply]
  have hd : dataPhaseReg n i = wireGate n i (diagonal (fun b => tScalar b*tScalar b)) := by
    simp only [dataPhaseReg, tGate, Rz, Matrix.diagonal_mul_diagonal]
    rfl
  rw [hd]
  simp only [cleanReg, Equiv.apply_symm_apply, split_last, Bool.xor_assoc,
    Bool.xor_self, Bool.xor_false]
  change _ = if b then 0 else ApplyGate (wireGate n i (diagonal (fun b => tScalar b*tScalar b))) ψ x
  rw [diagonal_wire_apply]
  cases b <;> cases x i <;> simp [tScalar, mul_assoc]

/-- The reverse-ordered matrix product implementing a finite list of gate codes. -/
def codeProduct (n : ℕ) : List FiniteGateCode → Matrix (Reg n) (Reg n) ℂ
  | [] => 1
  | g::gs => codeProduct n gs * finiteCodeMatrix n g

/-- The product of the four phase gate codes equals the enlarged-register phase matrix. -/
theorem phaseReg_codes (n : ℕ) (i : Fin n) : codeProduct (n+1) (phaseCodes n i) = phaseReg n i := by
  have ht : finiteCodeMatrix (n+1) (.t n) = wireGate (n+1) (Fin.last n) tGate := by
    rw [finiteCodeMatrix, dif_pos (show n<n+1 by omega)]
    rfl
  simp only [phaseCodes, codeProduct, Matrix.one_mul, computeReg_code, ht, phaseReg,
      Matrix.mul_assoc]

/-- The matrix product of a legal finite gate-code word is unitary. -/
theorem codeProduct_unitary (n : ℕ) (gs : List FiniteGateCode) (hg : finiteWordLegal n gs=true) :
    codeProduct n gs ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  induction gs with
  | nil => exact (Matrix.unitaryGroup _ _).one_mem
  | cons g gs ih =>
    have hh : finiteCodeLegal n g=true ∧ finiteWordLegal n gs=true := by
      simpa [finiteWordLegal] using! hg
    exact (Matrix.unitaryGroup _ _).mul_mem (ih hh.2) (finiteCodeMatrix_unitary n g hh.1)

/-- The register-coordinate embedding frame for appending a false auxiliary bit. -/
def regFrame (n : ℕ) : Matrix (Reg (n+1)) (Reg n) ℂ :=
  fun p x => if (regSuccEquiv n p).1=x ∧ (regSuccEquiv n p).2=false then 1 else 0

/-- Multiplication by the register frame is the clean-state embedding. -/
theorem regFrame_mulVec (n : ℕ) (ψ : QState (Reg n)) :
    (regFrame n).mulVec ψ = cleanReg n ψ := by
  ext p
  by_cases hb : (regSuccEquiv n p).2=false
  · simp [Matrix.mulVec, dotProduct, regFrame, cleanReg, hb]
  · have ht : (regSuccEquiv n p).2=true := Bool.eq_true_of_not_eq_false hb
    simp [Matrix.mulVec, dotProduct, regFrame, cleanReg, ht]

/-- The register frame intertwines the enlarged-register phase construction with the data phase. -/
theorem phaseReg_intertwine (n : ℕ) (i : Fin n) :
    phaseReg n i * regFrame n = regFrame n * dataPhaseReg n i := by
  have h (ψ : QState (Reg n)) :
      (phaseReg n i * regFrame n).mulVec ψ = (regFrame n * dataPhaseReg n i).mulVec ψ := by
    simp only [← Matrix.mulVec_mulVec, regFrame_mulVec]
    exact phaseReg_clean n i ψ
  ext p x
  have hh := congrFun (h (Pi.single x 1)) p
  simpa [Matrix.mulVec_single] using! hh

/-- The enlarged-register phase construction transported to the native data-plus-auxiliary
layout. -/
def nativePhase (n : ℕ) (i : Fin n) : Operator ((2^n)*2) :=
  relabelGate (registerLayout n) (phaseReg n i)

/-- The data phase transported to the native layout with a one-dimensional auxiliary factor. -/
def nativeDataPhase (n : ℕ) (i : Fin n) : Operator ((2^n)*1) :=
  relabelGate (baseLayout n) (dataPhaseReg n i)

/-- The zero-state allocation frame intertwines the native enlarged-register phase with the
native data phase. -/
theorem nativePhase_intertwine (n : ℕ) (i : Fin n) :
    nativePhase n i * allocationFrame (2^n) 0 =
      allocationFrame (2^n) 0 * nativeDataPhase n i := by
  have he : allocationFrame (2^n) 0 = Matrix.reindex (registerLayout n) (baseLayout n) (regFrame n) := by
    ext a b
    obtain ⟨p,rfl⟩ := (registerLayout n).surjective a
    obtain ⟨x,rfl⟩ := (baseLayout n).surjective b
    simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] using!
      allocationFrame_register n p x
  rw [he]
  simp only [nativePhase, nativeDataPhase, relabelGate, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, phaseReg_intertwine]

/-- A workspace execution trace augmented with visited auxiliary dimensions and gate and
instrument counts. -/
structure MeasuredTrace (d : ℕ) where
  native : WorkspaceTrace d
  widths : List ℕ
  gates : ℕ
  instruments : ℕ

/-- The maximum base-two ceiling logarithm of the visited auxiliary dimensions. -/
def MeasuredTrace.peakAux {d : ℕ} (t : MeasuredTrace d) : ℕ :=
  (t.widths.map (Nat.clog 2)).foldr max 0

/-- Forms a resource cost from the query, gate, instrument, and peak auxiliary-qubit counts and
the specified data-register size. -/
def MeasuredTrace.resources {d : ℕ} (dataQubits : ℕ) (t : MeasuredTrace d) : ResourceCost :=
  ⟨t.native.queries, t.gates, t.gates, t.native.queries+t.gates+t.instruments,
    dataQubits+t.peakAux, 0, 0⟩

/-- Executes a workspace circuit while recording branch outcomes, query counts, visited
auxiliary dimensions, and gate and instrument counts. -/
def measuredTraces {d : ℕ} (U : Operator d) :
    {k : ℕ} → WorkspaceCircuit d k → Operator (d*k) → List (MeasuredTrace d)
  | k, .halt b, ρ => [⟨⟨k,ρ,b,0,[]⟩,[k],0,0⟩]
  | k, .gate G next, ρ =>
    (measuredTraces U next (conjBranch G ρ)).map fun t =>
      {t with widths := k::t.widths, gates := t.gates+1}
  | k, .query next, ρ =>
    (measuredTraces U next (conjBranch (forwardWorkspaceOracle k U) ρ)).map fun t =>
      {t with native := {t.native with queries := t.native.queries+1}, widths := k::t.widths}
  | k, .instrument s _ I next, ρ =>
    (List.ofFn fun o : Fin s => (measuredTraces U (next o) (I.branch o ρ)).map fun t =>
      ⟨{t.native with outcomes := (s,o.val)::t.native.outcomes},
        k::t.widths, t.gates, t.instruments+1⟩).flatten

/-- Forgetting the added measurements of resource use from measured traces yields the native
workspace traces. -/
theorem measuredTraces_forget {d k : ℕ} (U : Operator d) (P : WorkspaceCircuit d k)
    (ρ : Operator (d*k)) : (measuredTraces U P ρ).map MeasuredTrace.native = workspaceTraces U P ρ := by
  induction P with
  | halt b => rfl
  | gate G next ih => simpa only [measuredTraces, List.map_map, Function.comp_def, workspaceTraces] using! ih _
  | query next ih =>
    simp only [measuredTraces, List.map_map, Function.comp_def, workspaceTraces]
    simpa only [List.map_map, Function.comp_def] using!
      congrArg (List.map fun t : WorkspaceTrace d => {t with queries := t.queries+1}) (ih _)
  | instrument s l I next ih =>
    simp only [measuredTraces, workspaceTraces, List.map_flatten, List.map_ofFn,
      List.map_map, Function.comp_def]
    congr 1
    apply congrArg List.ofFn
    funext o
    simpa only [List.map_map, Function.comp_def] using!
      congrArg (List.map fun t : WorkspaceTrace d => {t with outcomes := (s,o.val)::t.outcomes}) (ih o _)

/-- Prefixes a workspace continuation by the native gates represented by a finite code list on
the enlarged register. -/
def nativeCodes (n : ℕ) (gs : List FiniteGateCode) (next : WorkspaceCircuit (2^n) 2) :
    WorkspaceCircuit (2^n) 2 :=
  gs.foldr (fun g p => .gate (relabelGate (registerLayout n) (finiteCodeMatrix (n+1) g)) p) next

/-- Executing a native code prefix equals applying its product conjugation and then executing
the continuation. -/
theorem nativeCodes_traces (n : ℕ) (gs : List FiniteGateCode)
    (next : WorkspaceCircuit (2^n) 2) (U : Operator (2^n)) (ρ : Operator ((2^n)*2)) :
    workspaceTraces U (nativeCodes n gs next) ρ =
      workspaceTraces U next (conjBranch (relabelGate (registerLayout n) (codeProduct (n+1) gs)) ρ) := by
  induction gs generalizing ρ with
  | nil => simp [nativeCodes, codeProduct, relabelGate, Matrix.reindex_apply,
      Matrix.submatrix_one_equiv, conjBranch]
  | cons g gs ih =>
    simp only [nativeCodes, List.foldr_cons, workspaceTraces]
    rw [← nativeCodes, ih]
    rw [show conjBranch (relabelGate (registerLayout n) (codeProduct (n+1) gs))
        (conjBranch (relabelGate (registerLayout n) (finiteCodeMatrix (n+1) g)) ρ) =
        conjBranch (relabelGate (registerLayout n) (codeProduct (n+1) gs * finiteCodeMatrix (n+1) g)) ρ by
      rw [CircuitRelabel.relabelGate_mul]
      exact congrArg (fun T => T ρ) (conjBranch_comp _ _)]
    rfl

/-- Allocates a zero auxiliary qubit, executes the four-code phase construction, releases the
auxiliary register, and continues. -/
def cleanPhase (n : ℕ) (i : Fin n) (next : WorkspaceCircuit (2^n) 1) : WorkspaceCircuit (2^n) 1 :=
  .instrument 1 2 (allocate (2^n)) fun _ => nativeCodes n (phaseCodes n i)
    (.instrument 1 1 (release (2^n)) fun _ => next)

/-- Allocation, native phase conjugation, and release compose to conjugation by the native data
phase. -/
theorem nativePhase_release (n : ℕ) (i : Fin n) (ρ : Operator ((2^n)*1)) :
    (release (2^n)).branch 0 (conjBranch (nativePhase n i) ((allocate (2^n)).branch 0 ρ)) =
      conjBranch (nativeDataPhase n i) ρ := by
  have hh : conjBranch (nativePhase n i) ((allocate (2^n)).branch 0 ρ) =
      (allocate (2^n)).branch 0 (conjBranch (nativeDataPhase n i) ρ) := by
    change (conjBranch (nativePhase n i) ∘ₗ conjBranch (allocationFrame (2^n) 0)) ρ =
      (conjBranch (allocationFrame (2^n) 0) ∘ₗ conjBranch (nativeDataPhase n i)) ρ
    rw [conjBranch_comp, conjBranch_comp, nativePhase_intertwine]
  rw [hh, release_clean]

/-- Executing a clean phase applies the data phase before the continuation and prepends the two
single-outcome instrument reports. -/
theorem cleanPhase_traces (n : ℕ) (i : Fin n) (next : WorkspaceCircuit (2^n) 1)
    (U : Operator (2^n)) (ρ : Operator ((2^n)*1)) :
    workspaceTraces U (cleanPhase n i next) ρ =
      (workspaceTraces U next (conjBranch (nativeDataPhase n i) ρ)).map fun t =>
        {t with outcomes := (1,0)::(1,0)::t.outcomes} := by
  simp only [cleanPhase, workspaceTraces, List.ofFn_succ, List.ofFn_zero, List.flatten_cons,
    List.flatten_nil, List.append_nil, nativeCodes_traces, phaseReg_codes]
  change ((workspaceTraces U next
    ((release (2^n)).branch 0 (conjBranch (nativePhase n i) ((allocate (2^n)).branch 0 ρ)))).map
    (fun t => {t with outcomes := (1,0)::t.outcomes})).map
    (fun t => {t with outcomes := (1,0)::t.outcomes}) = _
  rw [nativePhase_release n i ρ]
  simp only [List.map_map, Function.comp_def]

/-- A native code prefix applies its product conjugation, adds its length to the gate count, and
records dimension two once per prefixed gate. -/
theorem nativeCodes_measured (n : ℕ) (gs : List FiniteGateCode)
    (next : WorkspaceCircuit (2^n) 2) (U : Operator (2^n)) (ρ : Operator ((2^n)*2)) :
    measuredTraces U (nativeCodes n gs next) ρ =
      (measuredTraces U next (conjBranch (relabelGate (registerLayout n) (codeProduct (n+1) gs)) ρ)).map
        (fun t => {t with widths := List.replicate gs.length 2 ++ t.widths, gates := t.gates+gs.length}) := by
  induction gs generalizing ρ with
  | nil => simp [nativeCodes, codeProduct, relabelGate, Matrix.reindex_apply,
      Matrix.submatrix_one_equiv, conjBranch]
  | cons g gs ih =>
    simp only [nativeCodes, List.foldr_cons, measuredTraces]
    rw [← nativeCodes, ih]
    have hc : conjBranch (relabelGate (registerLayout n) (codeProduct (n+1) gs))
        (conjBranch (relabelGate (registerLayout n) (finiteCodeMatrix (n+1) g)) ρ) =
        conjBranch (relabelGate (registerLayout n) (codeProduct (n+1) (g::gs))) ρ := by
      rw [codeProduct, CircuitRelabel.relabelGate_mul]
      exact congrArg (fun T => T ρ) (conjBranch_comp _ _)
    rw [hc]
    simp only [List.map_map, Function.comp_def, List.length_cons, List.replicate_succ,
      List.cons_append, Nat.add_assoc]

/-- Adds the outcome reports, auxiliary dimensions, four gates, and two instrument uses of a
clean phase to a measured trace. -/
def phaseMark {d : ℕ} (t : MeasuredTrace d) : MeasuredTrace d :=
  ⟨{t.native with outcomes := (1,0)::(1,0)::t.native.outcomes},
    1::List.replicate 5 2 ++ t.widths, t.gates+4, t.instruments+2⟩

/-- The measured traces of a clean phase are obtained by applying the data phase before the
continuation and marking each trace with `phaseMark`. -/
theorem cleanPhase_measured (n : ℕ) (i : Fin n) (next : WorkspaceCircuit (2^n) 1)
    (U : Operator (2^n)) (ρ : Operator ((2^n)*1)) :
    measuredTraces U (cleanPhase n i next) ρ =
      (measuredTraces U next (conjBranch (nativeDataPhase n i) ρ)).map phaseMark := by
  simp only [cleanPhase, measuredTraces, List.ofFn_succ, List.ofFn_zero, List.flatten_cons,
    List.flatten_nil, List.append_nil, nativeCodes_measured, phaseReg_codes]
  have hrel := nativePhase_release n i ρ
  unfold nativePhase at hrel
  rw [hrel]
  simp only [List.map_map, Function.comp_def, phaseCodes, List.length_cons,
    List.length_nil, List.replicate_succ, List.replicate_zero, List.cons_append,
    List.nil_append, Nat.add_assoc]
  congr 1

/-- The quantum channel given by the single branch of the release instrument. -/
def releaseChannel (d : ℕ) : QuantumChannel (d*2) (d*1) where
  map := (release d).branch 0
  completelyPositive := (release d).cp 0
  tracePreserving ρ := by simpa only [Fin.sum_univ_one] using! (release d).total ρ

/-- Release extended by an arbitrary reference register contracts the trace norm of every
Hermitian input. -/
theorem release_reference_error (d r : ℕ)
    (X : Matrix (Fin r × Fin (d*2)) (Fin r × Fin (d*2)) ℂ) (hX : X.IsHermitian) :
    (ChannelAmplification ((release d).branch 0) r X).traceNorm ≤ X.traceNorm :=
  channel_reference_hermitian_trace_contraction (releaseChannel d) hX

/-- Allocation, phase, and release implement the data-phase conjugation even when extended by a
reference register. -/
theorem cleanPhase_reference (n : ℕ) (i : Fin n) (R : ℕ)
    (X : Matrix (Fin ((2^n)*1) × Fin R) (Fin ((2^n)*1) × Fin R) ℂ) :
    tensorLeft ((release (2^n)).branch 0)
      (tensorLeft (conjBranch (nativePhase n i)) (tensorLeft ((allocate (2^n)).branch 0) X)) =
      tensorLeft (conjBranch (nativeDataPhase n i)) X := by
  ext a b
  exact congrFun (congrFun (nativePhase_release n i (fun u v => X (u,a.2) (v,b.2))) a.1) b.1

/-- An operation consisting of a clean phase on a selected wire, a certified legal data gate, or
an oracle query. -/
inductive CleanOp (n : ℕ) where
  | phase (i : Fin n)
  | data (g : FiniteGateCode) (legal : finiteCodeLegal n g=true)
  | query

/-- Compiles a list of clean operations into a workspace circuit that ends by accepting. -/
def compileWord (n : ℕ) : List (CleanOp n) → WorkspaceCircuit (2^n) 1
  | [] => .halt true
  | .phase i::w => cleanPhase n i (compileWord n w)
  | .data g _::w => .gate (relabelGate (baseLayout n) (finiteCodeMatrix n g)) (compileWord n w)
  | .query::w => .query (compileWord n w)

/-- The native matrix implementing a clean phase, data gate, or forward oracle query on the base
auxiliary space. -/
def opMatrix {n : ℕ} (U : Operator (2^n)) : CleanOp n → Operator ((2^n)*1)
  | .phase i => nativeDataPhase n i
  | .data g _ => relabelGate (baseLayout n) (finiteCodeMatrix n g)
  | .query => forwardWorkspaceOracle 1 U

/-- The reverse-ordered product of the native matrices implementing a clean-operation word. -/
def wordMatrix {n : ℕ} (U : Operator (2^n)) : List (CleanOp n) → Operator ((2^n)*1)
  | [] => 1
  | op::w => wordMatrix U w * opMatrix U op

/-- The number of query operations in a clean-operation word. -/
def wordQueries {n : ℕ} : List (CleanOp n) → ℕ
  | [] => 0
  | .query::w => wordQueries w+1
  | _::w => wordQueries w

/-- The gate count of a compiled clean-operation word, assigning four gates to each phase and
one to each data gate. -/
def wordGates {n : ℕ} : List (CleanOp n) → ℕ
  | [] => 0
  | .phase _::w => wordGates w+4
  | .data _ _::w => wordGates w+1
  | .query::w => wordGates w

/-- The number of clean phase operations in a word. -/
def wordPhases {n : ℕ} : List (CleanOp n) → ℕ
  | [] => 0
  | .phase _::w => wordPhases w+1
  | _::w => wordPhases w

/-- The auxiliary-dimension history of a compiled word, including the temporary dimension-two
stages of each clean phase. -/
def wordWidths {n : ℕ} : List (CleanOp n) → List ℕ
  | [] => [1]
  | .phase _::w => 1::List.replicate 5 2 ++ wordWidths w
  | _::w => 1::wordWidths w

/-- The list of instrument outcome reports contributed by allocation and release in each clean
phase. -/
def wordReports {n : ℕ} : List (CleanOp n) → List (ℕ×ℕ)
  | [] => []
  | .phase _::w => (1,0)::(1,0)::wordReports w
  | _::w => wordReports w

/-- The accepting measured trace specified by the word matrix, its operation counts, auxiliary
dimensions, and instrument reports. -/
def wordTrace {n : ℕ} (U : Operator (2^n)) (w : List (CleanOp n)) (ρ : Operator ((2^n)*1)) :
    MeasuredTrace (2^n) :=
  ⟨⟨1,conjBranch (wordMatrix U w) ρ,true,wordQueries w,wordReports w⟩,
    wordWidths w,wordGates w,2*wordPhases w⟩

/-- Conjugating first by an operation matrix and then by the remaining word matrix equals
conjugation by the full word matrix. -/
theorem wordMatrix_cons_conj {n : ℕ} (U : Operator (2^n)) (op : CleanOp n) (w : List (CleanOp n))
    (ρ : Operator ((2^n)*1)) :
    conjBranch (wordMatrix U w) (conjBranch (opMatrix U op) ρ) = conjBranch (wordMatrix U (op::w)) ρ :=
  congrArg (fun T : Operator ((2^n)*1) →ₗ[ℂ] Operator ((2^n)*1) => T ρ)
    (conjBranch_comp (wordMatrix U w) (opMatrix U op))

/-- A compiled clean-operation word has exactly the measured trace specified by `wordTrace`. -/
theorem compileWord_measured {n : ℕ} (U : Operator (2^n)) (w : List (CleanOp n))
    (ρ : Operator ((2^n)*1)) : measuredTraces U (compileWord n w) ρ = [wordTrace U w ρ] := by
  induction w generalizing ρ with
  | nil => simp [compileWord, measuredTraces, wordTrace, wordMatrix, conjBranch,
      wordWidths,wordGates,wordQueries,wordReports,wordPhases]
  | cons op w ih =>
    cases op with
    | phase i =>
      rw [compileWord, cleanPhase_measured, ih]
      simp only [List.map_cons, List.map_nil]
      congr 1
      simp only [phaseMark, wordTrace, wordWidths, wordGates, wordQueries, wordReports, wordPhases]
      rw [← wordMatrix_cons_conj U (.phase i)]
      simp only [Nat.mul_add, Nat.mul_one, opMatrix]
    | data g hg =>
      rw [compileWord, measuredTraces, ih]
      simp only [List.map_cons, List.map_nil]
      congr 1
      simp only [wordTrace, wordWidths, wordGates, wordQueries, wordReports, wordPhases]
      rw [← wordMatrix_cons_conj U (.data g hg)]
      rfl
    | query =>
      rw [compileWord, measuredTraces, ih]
      simp only [List.map_cons, List.map_nil]
      congr 1
      simp only [wordTrace, wordWidths, wordGates, wordQueries, wordReports, wordPhases]
      rw [← wordMatrix_cons_conj U .query]
      rfl

/-- A compiled clean-operation word has exactly the native component of its specified word
trace. -/
theorem compileWord_traces {n : ℕ} (U : Operator (2^n)) (w : List (CleanOp n))
    (ρ : Operator ((2^n)*1)) :
    workspaceTraces U (compileWord n w) ρ = [(wordTrace U w ρ).native] := by
  rw [← measuredTraces_forget, compileWord_measured]
  rfl

/-- Prefixing a well-formed continuation with a legal native gate-code word preserves
workspace-circuit well-formedness. -/
theorem nativeCodes_wellFormed (n : ℕ) (gs : List FiniteGateCode) (hg : finiteWordLegal (n+1) gs=true)
    (next : WorkspaceCircuit (2^n) 2) (hn : workspaceCircuitWellFormed next) :
    workspaceCircuitWellFormed (nativeCodes n gs next) := by
  induction gs with
  | nil => exact hn
  | cons g gs ih =>
    have hh : finiteCodeLegal (n+1) g=true ∧ finiteWordLegal (n+1) gs=true := by
      simpa [finiteWordLegal] using! hg
    exact ⟨relabelGate_mem_unitary (finiteCodeMatrix_unitary (n+1) g hh.1) _, ih hh.2⟩

/-- Every compiled clean-operation word is a well-formed workspace circuit. -/
theorem compileWord_wellFormed {n : ℕ} (w : List (CleanOp n)) :
    workspaceCircuitWellFormed (compileWord n w) := by
  induction w with
  | nil => trivial
  | cons op w ih =>
    cases op with
    | phase i => exact fun _ => nativeCodes_wellFormed n (phaseCodes n i) (phaseCodes_legal n i) _ (fun _ => ih)
    | data g hg => exact ⟨relabelGate_mem_unitary (finiteCodeMatrix_unitary n g hg) _, ih⟩
    | query => exact ih

/-- The recorded peak auxiliary-qubit count is zero when a word has no phases and one otherwise. -/
theorem wordWidths_peak {n : ℕ} (w : List (CleanOp n)) :
    ((wordWidths w).map (Nat.clog 2)).foldr max 0 = if wordPhases w=0 then 0 else 1 := by
  have h1 : Nat.clog 2 1=0 := by decide
  have h2 : Nat.clog 2 2=1 := by decide
  induction w with
  | nil => simp [wordWidths,wordPhases,h1]
  | cons op w ih =>
    cases op with
    | phase i =>
      simp only [wordWidths, List.map_cons, List.map_append, List.foldr_cons,
        List.foldr_append, List.replicate_succ, List.replicate_zero, List.map_nil,
        List.foldr_nil, h1,h2, wordPhases, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, if_false, zero_max]
      rw [ih]
      split_ifs <;> decide
    | data g hg => simpa only [wordWidths,wordPhases,List.map_cons,List.foldr_cons,h1,zero_max] using! ih
    | query => simpa only [wordWidths,wordPhases,List.map_cons,List.foldr_cons,h1,zero_max] using! ih

/-- The resource cost specified by a clean-operation word's queries, compiled gates, phase
instruments, and peak auxiliary use. -/
def wordResources (n : ℕ) (w : List (CleanOp n)) : ResourceCost :=
  ⟨wordQueries w,wordGates w,wordGates w,wordQueries w+wordGates w+2*wordPhases w,
    n+(if wordPhases w=0 then 0 else 1),0,0⟩

/-- The resources extracted from the specified measured word trace equal the word's resource
cost. -/
theorem wordTrace_resources {n : ℕ} (U : Operator (2^n)) (w : List (CleanOp n))
    (ρ : Operator ((2^n)*1)) : (wordTrace U w ρ).resources n = wordResources n w := by
  simp only [MeasuredTrace.resources, MeasuredTrace.peakAux, wordTrace, wordWidths_peak,
      wordResources]

/-- The matrix of concatenated clean-operation words is the product of their matrices in reverse
concatenation order. -/
theorem wordMatrix_append {n : ℕ} (U : Operator (2^n)) (v w : List (CleanOp n)) :
    wordMatrix U (v++w) = wordMatrix U w * wordMatrix U v := by
  induction v with
  | nil => simp [wordMatrix]
  | cons op v ih => simp only [List.cons_append, wordMatrix, ih, Matrix.mul_assoc]

/-- Query, gate, and phase counts add under concatenation of clean-operation words. -/
theorem wordCounts_append {n : ℕ} (v w : List (CleanOp n)) :
    wordQueries (v++w)=wordQueries v+wordQueries w ∧
    wordGates (v++w)=wordGates v+wordGates w ∧
    wordPhases (v++w)=wordPhases v+wordPhases w := by
  induction v with
  | nil => simp [wordQueries,wordGates,wordPhases]
  | cons op v ih =>
    cases op <;> simp only [List.cons_append,wordQueries,wordGates,wordPhases,ih.1,ih.2.1,ih.2.2] <;>
      (repeat' constructor) <;> omega

/-- The resource cost of concatenated clean-operation words equals the sum of their resource
costs. -/
theorem wordResources_append {n : ℕ} (v w : List (CleanOp n)) :
    wordResources n (v++w) = wordResources n v+wordResources n w := by
  obtain ⟨hq,hg,hp⟩ := wordCounts_append v w
  ext <;> simp only [wordResources,ResourceCost.add_queries,ResourceCost.add_macroGates,
    ResourceCost.add_basicGates,ResourceCost.add_depth,ResourceCost.add_peakSpace,
    ResourceCost.add_hamiltonianTime,ResourceCost.add_classicalBits,hq,hg,hp,_root_.add_zero]
  · omega
  · split_ifs <;> omega

/-- Concatenates a clean-operation word with itself the specified number of times. -/
def repeatWord {n : ℕ} (w : List (CleanOp n)) : ℕ → List (CleanOp n)
  | 0 => []
  | k+1 => w ++ repeatWord w k

/-- The matrix of a repeated clean-operation word is the corresponding power of its matrix. -/
theorem repeatWord_matrix {n : ℕ} (U : Operator (2^n)) (w : List (CleanOp n)) (k : ℕ) :
    wordMatrix U (repeatWord w k) = wordMatrix U w ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [repeatWord,wordMatrix_append,ih,pow_succ]

/-- Query, gate, and phase counts of a repeated word are multiplied by the repetition count. -/
theorem repeatWord_counts {n : ℕ} (w : List (CleanOp n)) (k : ℕ) :
    wordQueries (repeatWord w k)=k*wordQueries w ∧ wordGates (repeatWord w k)=k*wordGates w ∧
    wordPhases (repeatWord w k)=k*wordPhases w := by
  induction k with
  | zero => simp [repeatWord,wordQueries,wordGates,wordPhases]
  | succ k ih =>
    obtain ⟨hq,hg,hp⟩ := wordCounts_append w (repeatWord w k)
    simp only [repeatWord,hq,hg,hp,ih.1,ih.2.1,ih.2.2,Nat.add_mul,Nat.one_mul,Nat.add_comm]
    trivial

/-- The equivalence between a Boolean value and a one-bit register. -/
def qubitReg : Bool ≃ Reg 1 where
  toFun b := fun _ => b
  invFun x := x 0
  left_inv _ := rfl
  right_inv x := by funext i; fin_cases i; rfl

/-- A gate on the unique wire of a one-bit register is its relabeling along `qubitReg`. -/
theorem wireGate_one (A : Matrix Bool Bool ℂ) : wireGate 1 0 A = relabelGate qubitReg A := by
  ext x y
  rw [wireGate_apply, if_pos (by intro j hj; fin_cases j; exact (hj rfl).elim)]
  rfl

/-- Four T gates, grouped into two squares, multiply to Pauli Z. -/
theorem tGate_four : (tGate*tGate)*(tGate*tGate) = PauliZ := by
  have he : (Complex.exp (((Real.pi/4 : ℝ) : ℂ)*Complex.I)*
      Complex.exp (((Real.pi/4 : ℝ) : ℂ)*Complex.I))*
      (Complex.exp (((Real.pi/4 : ℝ) : ℂ)*Complex.I)*
      Complex.exp (((Real.pi/4 : ℝ) : ℂ)*Complex.I)) = -1 := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    have ha : (((Real.pi/4 : ℝ) : ℂ)*Complex.I+((Real.pi/4 : ℝ) : ℂ)*Complex.I)+
        (((Real.pi/4 : ℝ) : ℂ)*Complex.I+((Real.pi/4 : ℝ) : ℂ)*Complex.I) = (Real.pi : ℂ)*Complex.I := by
      push_cast
      ring
    rw [ha,Complex.exp_pi_mul_I]
  simp only [Complex.ofReal_div,Complex.ofReal_ofNat] at he
  ext b c
  cases b <;> cases c <;>
    simp [tGate,Rz,Matrix.diagonal_mul_diagonal,PauliZ,he]

/-- At auxiliary dimension one, a relabeled register oracle agrees with its relabeling in the
base workspace layout. -/
theorem forwardWorkspaceOracle_reg (n : ℕ) (A : Matrix (Reg n) (Reg n) ℂ) :
    forwardWorkspaceOracle 1 (relabelGate (bitVecEquiv n) A) = relabelGate (baseLayout n) A := by
  ext a b
  obtain ⟨x,rfl⟩ := (baseLayout n).surjective a
  obtain ⟨y,rfl⟩ := (baseLayout n).surjective b
  have hdiv (z : Reg n) : (finProdFinEquiv (bitVecEquiv n z,(0:Fin 1))).divNat = bitVecEquiv n z := by
    change (finProdFinEquiv.symm (finProdFinEquiv (bitVecEquiv n z,(0:Fin 1)))).1 = _
    simp only [Equiv.symm_apply_apply]
  simp [forwardWorkspaceOracle, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
    TensorGate, Matrix.kroneckerMap_apply, baseLayout,hdiv]

/-- The scalar-signal reflection transported to the native one-qubit data space. -/
def signalOracle (x : ℝ) : Operator (2^1) :=
  relabelGate (qubitReg.trans (bitVecEquiv 1)) (scalarSignalReflection x)

/-- The equivalence from a Boolean qubit basis to the native one-qubit base workspace layout. -/
def signalLayout : Bool ≃ Fin ((2^1)*1) := qubitReg.trans (baseLayout 1)

/-- Repeats a one-query block preceded by two clean phase operations on the unique data wire. -/
def chebyshevOps : ℕ → List (CleanOp 1)
  | 0 => []
  | k+1 => [.phase 0,.phase 0,.query] ++ chebyshevOps k

/-- Two native data phases on the one-qubit register multiply to the relabeled Pauli Z matrix. -/
theorem nativeDataPhase_pair : nativeDataPhase 1 0 * nativeDataPhase 1 0 = relabelGate signalLayout PauliZ := by
  rw [nativeDataPhase, ← CircuitRelabel.relabelGate_mul]
  have hh : dataPhaseReg 1 0 * dataPhaseReg 1 0 = wireGate 1 0 PauliZ := by
    rw [dataPhaseReg, wireGate_mul, tGate_four]
  rw [hh,wireGate_one, relabelGate_trans]
  rfl

/-- The forward workspace action of the signal oracle is the scalar-signal reflection relabeled
by `signalLayout`. -/
theorem signalOracle_forward (x : ℝ) :
    forwardWorkspaceOracle 1 (signalOracle x) = relabelGate signalLayout (scalarSignalReflection x) := by
  rw [signalOracle, ← relabelGate_trans, forwardWorkspaceOracle_reg, relabelGate_trans]
  rfl

/-- The Chebyshev operation word implements the relabeled power of the scalar-signal reflection
multiplied by Pauli Z. -/
theorem chebyshevOps_matrix (x : ℝ) (k : ℕ) :
    wordMatrix (signalOracle x) (chebyshevOps k) =
      relabelGate signalLayout ((scalarSignalReflection x*PauliZ)^k) := by
  induction k with
  | zero => simp [chebyshevOps,wordMatrix,relabelGate,Matrix.reindex_apply,Matrix.submatrix_one_equiv]
  | succ k ih =>
    rw [chebyshevOps,wordMatrix_append,ih]
    simp only [wordMatrix,opMatrix,Matrix.one_mul]
    rw [signalOracle_forward, Matrix.mul_assoc, nativeDataPhase_pair,
      ← CircuitRelabel.relabelGate_mul, ← CircuitRelabel.relabelGate_mul, ← pow_succ]

/-- For a signal in `[-1, 1]`, the false-basis diagonal response of the operation word is the
degree-`k` Chebyshev polynomial of the first kind. -/
theorem chebyshevOps_response (x : ℝ) (hx : x∈Set.Icc (-1) 1) (k : ℕ) :
    wordMatrix (signalOracle x) (chebyshevOps k) (signalLayout false) (signalLayout false) =
      Complex.ofReal ((Polynomial.Chebyshev.T ℝ (k:ℤ)).eval x) := by
  rw [chebyshevOps_matrix]
  have hh := scalar_signal_chebyshev_actual_word k x hx
  simpa only [relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply,hh.2.2.2.1] using! hh.2.2.2.2.1

/-- The degree-`k` Chebyshev operation word uses `k` queries, `8 * k` gates, and `2 * k` clean
phases. -/
theorem chebyshevOps_counts (k : ℕ) : wordQueries (chebyshevOps k)=k ∧
    wordGates (chebyshevOps k)=8*k ∧ wordPhases (chebyshevOps k)=2*k := by
  induction k with
  | zero => simp [chebyshevOps,wordQueries,wordGates,wordPhases]
  | succ k ih =>
    rw [chebyshevOps]
    obtain ⟨hq,hg,hp⟩ :=
        wordCounts_append ([.phase 0,.phase 0,.query] : List (CleanOp 1)) (chebyshevOps k)
    simp only [wordQueries,wordGates,wordPhases] at hq hg hp
    rw [hq,hg,hp,ih.1,ih.2.1,ih.2.2]
    omega

/-- The two-outcome instrument with identical Kraus operators that produces a fair coin while
scaling each branch state by one half. -/
def stopCoin (d : ℕ) : Instrument (Fin 2) d d :=
  Instrument.ofKraus (fun _ => ((Real.sqrt 2 : ℂ)⁻¹) • (1 : Operator d)) (by
    have hc : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by simp
    simp only [Fin.sum_univ_two, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,smul_smul,hc,inv_sqrt2_mul_self]
    rw [← add_smul]
    norm_num)

/-- Either branch of the stopping coin returns one half of the input operator. -/
theorem stopCoin_branch (d : ℕ) (b : Fin 2) (ρ : Operator d) :
    (stopCoin d).branch b ρ = (1/2 : ℂ) • ρ := by
  have hc : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by simp
  simp only [stopCoin,Instrument.ofKraus_branch,Matrix.conjTranspose_smul,Matrix.conjTranspose_one,
    Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,Matrix.mul_one,smul_smul,hc,inv_sqrt2_mul_self,one_div]

/-- The native matrix for a forward query followed by the selected data phase. -/
def stopRound {n : ℕ} (U : Operator (2^n)) (i : Fin n) : Operator ((2^n)*1) :=
  nativeDataPhase n i * forwardWorkspaceOracle 1 U

/-- The input update for one stopping round, given by half the conjugation by `stopRound`. -/
def stopInput {n : ℕ} (U : Operator (2^n)) (i : Fin n) (ρ : Operator ((2^n)*1)) : Operator ((2^n)*1) :=
  (1/2 : ℂ) • conjBranch (stopRound U i) ρ

/-- A bounded retry program that queries, performs a clean phase, and tosses a fair stopping
coin, rejecting if its round budget is exhausted. -/
def stoppingProgram (n : ℕ) (i : Fin n) : ℕ → WorkspaceCircuit (2^n) 1
  | 0 => .halt false
  | h+1 => .query (cleanPhase n i (.instrument 2 1 (stopCoin ((2^n)*1))
      fun b => if b=0 then .halt true else stoppingProgram n i h))

/-- The measured trace of immediate halting, with the specified acceptance flag and no query,
gate, or instrument use. -/
def haltMeasured {d : ℕ} (b : Bool) (ρ : Operator (d*1)) : MeasuredTrace d :=
  ⟨⟨1,ρ,b,0,[]⟩,[1],0,0⟩

/-- Prepends a binary coin outcome and a dimension-one visit to a measured trace and increments
its instrument count. -/
def coinMark {d : ℕ} (b : Fin 2) (t : MeasuredTrace d) : MeasuredTrace d :=
  ⟨{t.native with outcomes := (2,b.val)::t.native.outcomes},1::t.widths,t.gates,t.instruments+1⟩

/-- Adds one query and a dimension-one visit to a measured trace. -/
def queryMark {d : ℕ} (t : MeasuredTrace d) : MeasuredTrace d :=
  ⟨{t.native with queries := t.native.queries+1},1::t.widths,t.gates,t.instruments⟩

/-- Adds the query, clean phase, and coin records for one stopping round to a measured trace. -/
def roundMark {d : ℕ} (b : Fin 2) (t : MeasuredTrace d) : MeasuredTrace d :=
  queryMark (phaseMark (coinMark b t))

/-- The recursively specified measured traces of the bounded stopping program, including
immediate acceptance and continuation branches. -/
def stopMeasured {n : ℕ} (U : Operator (2^n)) (i : Fin n) : ℕ → Operator ((2^n)*1) → List (MeasuredTrace (2^n))
  | 0,ρ => [haltMeasured false ρ]
  | h+1,ρ => roundMark 0 (haltMeasured true (stopInput U i ρ)) ::
      (stopMeasured U i h (stopInput U i ρ)).map (roundMark 1)

/-- The measured execution traces of the stopping program equal its recursive specification
`stopMeasured`. -/
theorem stoppingProgram_measured {n : ℕ} (U : Operator (2^n)) (i : Fin n) (h : ℕ)
    (ρ : Operator ((2^n)*1)) : measuredTraces U (stoppingProgram n i h) ρ = stopMeasured U i h ρ := by
  induction h generalizing ρ with
  | zero => rfl
  | succ h ih =>
    rw [stoppingProgram,measuredTraces,cleanPhase_measured]
    have hc : conjBranch (nativeDataPhase n i) (conjBranch (forwardWorkspaceOracle 1 U) ρ) =
        conjBranch (stopRound U i) ρ :=
      congrArg (fun T : Operator ((2^n)*1) →ₗ[ℂ] Operator ((2^n)*1) => T ρ)
        (conjBranch_comp (nativeDataPhase n i) (forwardWorkspaceOracle 1 U))
    rw [hc]
    simp only [measuredTraces,List.ofFn_succ,List.ofFn_zero,List.flatten_cons,List.flatten_nil,
      List.append_nil,Fin.val_zero,Fin.succ_ne_zero,reduceIte,stopCoin_branch]
    rw [ih]
    simp only [stopMeasured,stopInput,List.map_cons,List.map_nil,List.map_append,List.map_map,Function.comp_def]
    rfl

/-- The bounded stopping program is a well-formed workspace circuit. -/
theorem stoppingProgram_wellFormed (n : ℕ) (i : Fin n) (h : ℕ) :
    workspaceCircuitWellFormed (stoppingProgram n i h) := by
  induction h with
  | zero => trivial
  | succ h ih =>
    intro _
    apply nativeCodes_wellFormed n (phaseCodes n i) (phaseCodes_legal n i)
    intro _ b
    (try dsimp only)
    split_ifs <;> trivial

/-- A stopping program with round budget `h` has `h + 1` specified measured traces. -/
theorem stopMeasured_length {n : ℕ} (U : Operator (2^n)) (i : Fin n) (h : ℕ) (ρ : Operator ((2^n)*1)) :
    (stopMeasured U i h ρ).length = h+1 := by
  induction h generalizing ρ with
  | zero => rfl
  | succ h ih => simp only [stopMeasured,List.length_cons,List.length_map,ih]

/-- One further stopping-input update increments the power of `stopRound` and contributes
another factor of one half. -/
theorem stopInput_iterate {n : ℕ} (U : Operator (2^n)) (i : Fin n) (k : ℕ)
    (ρ : Operator ((2^n)*1)) :
    (1/2 : ℂ)^k • conjBranch (stopRound U i ^ k) (stopInput U i ρ) =
      (1/2 : ℂ)^(k+1) • conjBranch (stopRound U i ^ (k+1)) ρ := by
  rw [stopInput,map_smul,smul_smul,pow_succ]
  have hc : conjBranch (stopRound U i ^ k) (conjBranch (stopRound U i) ρ) =
      conjBranch (stopRound U i ^ (k+1)) ρ := by
    rw [pow_succ]
    exact congrArg (fun T : Operator ((2^n)*1) →ₗ[ℂ] Operator ((2^n)*1) => T ρ)
      (conjBranch_comp (stopRound U i ^ k) (stopRound U i))
  rw [hc]

/-- Adding a stopping-round mark changes the peak auxiliary-qubit count to the maximum of one
and its previous value. -/
theorem roundMark_peak {d : ℕ} (b : Fin 2) (t : MeasuredTrace d) :
    (roundMark b t).peakAux = max 1 t.peakAux := by
  have h1 : Nat.clog 2 1=0 := by decide
  have h2 : Nat.clog 2 2=1 := by decide
  simp only [roundMark,queryMark,phaseMark,coinMark,MeasuredTrace.peakAux,List.map_cons,
    List.map_append,List.foldr_cons,List.foldr_append,List.replicate_succ,List.replicate_zero,
    List.map_nil,List.foldr_nil,h1,h2,zero_max,← max_assoc,max_self]

/-- An immediate halting trace has peak auxiliary-qubit count zero. -/
theorem haltMeasured_peak {d : ℕ} (b : Bool) (ρ : Operator (d*1)) :
    (haltMeasured b ρ).peakAux=0 := by
  have h1 : Nat.clog 2 1=0 := by decide
  simp only [haltMeasured,MeasuredTrace.peakAux,List.map_cons,List.map_nil,List.foldr_cons,
    List.foldr_nil,h1,max_self]

/-- Every specified stopping trace uses some `k ≤ h` rounds, has state `2⁻ᵏ` times conjugation
by `stopRound ^ k`, and uses `k` queries, `4 * k` gates, and `3 * k` instruments. Its peak
auxiliary use is zero for `k = 0` and one otherwise. -/
theorem stopMeasured_invariant {n : ℕ} (U : Operator (2^n)) (i : Fin n) (h : ℕ)
    (ρ : Operator ((2^n)*1)) (t : MeasuredTrace (2^n)) (ht : t∈stopMeasured U i h ρ) :
    ∃ k≤h,
      t.native = ⟨1,(1/2 : ℂ)^k • conjBranch (stopRound U i ^ k) ρ,
        t.native.accepted,k,t.native.outcomes⟩ ∧
      t.gates=4*k ∧ t.instruments=3*k ∧ t.peakAux=(if k=0 then 0 else 1) := by
  induction h generalizing ρ t with
  | zero =>
    simp only [stopMeasured,List.mem_singleton] at ht
    subst t
    refine ⟨0,by omega,?_,rfl,rfl,haltMeasured_peak _ _⟩
    simp only [pow_zero,conjBranch_apply,Matrix.one_mul,Matrix.conjTranspose_one,Matrix.mul_one,
      one_smul,haltMeasured]
  | succ h ih =>
    simp only [stopMeasured,List.mem_cons,List.mem_map] at ht
    rcases ht with rfl | ⟨u,hu,rfl⟩
    · refine ⟨1,by omega,?_,rfl,rfl,?_⟩
      · simp only [roundMark,queryMark,phaseMark,coinMark,haltMeasured,stopInput,pow_one]
      · rw [roundMark_peak,haltMeasured_peak]
        rfl
    · obtain ⟨k,hk,hn,hg,hi,hp⟩ := ih (stopInput U i ρ) u hu
      refine ⟨k+1,by omega,?_,?_,?_,?_⟩
      · change {u.native with queries := u.native.queries+1, outcomes := (1,0)::(1,0)::(2,1)::u.native.outcomes} = _
        rw [hn]
        simp only [roundMark,queryMark,phaseMark,coinMark,stopInput_iterate,Fin.val_one]
      · change u.gates+4=4*(k+1)
        omega
      · change u.instruments+1+2=3*(k+1)
        omega
      · rw [roundMark_peak,hp]
        by_cases hk0 : k=0 <;> simp [hk0]

/-- The measured trace that continues at every stopping coin and rejects when the round budget
is exhausted. -/
def rejectedTrace {n : ℕ} (U : Operator (2^n)) (i : Fin n) : ℕ → Operator ((2^n)*1) → MeasuredTrace (2^n)
  | 0,ρ => haltMeasured false ρ
  | h+1,ρ => roundMark 1 (rejectedTrace U i h (stopInput U i ρ))

/-- The acceptance flag of the designated rejected trace is false. -/
@[simp] theorem rejectedTrace_accepted {n : ℕ} (U : Operator (2^n)) (i : Fin n) (h : ℕ)
    (ρ : Operator ((2^n)*1)) : (rejectedTrace U i h ρ).native.accepted=false := by
  induction h generalizing ρ with
  | zero => rfl
  | succ h ih => exact ih _

/-- Filtering the specified stopping traces for rejection yields exactly the designated rejected
trace. -/
theorem stopMeasured_rejected {n : ℕ} (U : Operator (2^n)) (i : Fin n) (h : ℕ)
    (ρ : Operator ((2^n)*1)) :
    (stopMeasured U i h ρ).filter (fun t => !t.native.accepted) = [rejectedTrace U i h ρ] := by
  induction h generalizing ρ with
  | zero => rfl
  | succ h ih =>
    have hf (xs : List (MeasuredTrace (2^n))) :
        (xs.map (roundMark 1)).filter (fun t => !t.native.accepted) =
          (xs.filter (fun t => !t.native.accepted)).map (roundMark 1) := by
      induction xs with
      | nil => rfl
      | cons x xs ihx =>
        simp only [List.map_cons,List.filter_cons,roundMark,queryMark,phaseMark,coinMark] at *
        split_ifs <;> simp_all only [List.map_cons]
        all_goals rfl
    change ((stopMeasured U i h (stopInput U i ρ)).map (roundMark 1)).filter
      (fun t => !t.native.accepted) = [roundMark 1 (rejectedTrace U i h (stopInput U i ρ))]
    rw [hf,ih]
    rfl

/-- The native rejected trace has auxiliary dimension one, `h` queries, and state `2⁻ʰ` times
conjugation by `stopRound ^ h`. -/
theorem rejectedTrace_native {n : ℕ} (U : Operator (2^n)) (i : Fin n) (h : ℕ)
    (ρ : Operator ((2^n)*1)) :
    (rejectedTrace U i h ρ).native =
      ⟨1,(1/2 : ℂ)^h • conjBranch (stopRound U i ^ h) ρ,false,h,
        (rejectedTrace U i h ρ).native.outcomes⟩ := by
  induction h generalizing ρ with
  | zero => simp only [rejectedTrace,haltMeasured,pow_zero,conjBranch_apply,Matrix.one_mul,
      Matrix.conjTranspose_one,Matrix.mul_one,one_smul]
  | succ h ih =>
    change { (rejectedTrace U i h (stopInput U i ρ)).native with
      queries := (rejectedTrace U i h (stopInput U i ρ)).native.queries+1,
      outcomes := (1,0)::(1,0)::(2,1)::(rejectedTrace U i h (stopInput U i ρ)).native.outcomes} = _
    rw [ih]
    simp only [stopInput_iterate,roundMark,queryMark,phaseMark,coinMark,rejectedTrace,Fin.val_one]

/-- For a unitary oracle, the matrix of a stopping round is unitary. -/
theorem stopRound_unitary {n : ℕ} (U : Operator (2^n))
    (hU : U∈Matrix.unitaryGroup (Fin (2^n)) ℂ) (i : Fin n) :
    stopRound U i∈Matrix.unitaryGroup (Fin ((2^n)*1)) ℂ := by
  apply (Matrix.unitaryGroup _ _).mul_mem
  · exact relabelGate_mem_unitary (wireGate_unitary n i (tGate*tGate)
      ((Matrix.unitaryGroup _ _).mul_mem tGate_mem_unitary tGate_mem_unitary)) _
  · exact forwardWorkspaceOracle_unitary 1 U hU

/-- For a unitary oracle, the rejected trace has mass `2⁻ʰ` times the real trace of the input. -/
theorem rejectedTrace_mass {n : ℕ} (U : Operator (2^n))
    (hU : U∈Matrix.unitaryGroup (Fin (2^n)) ℂ) (i : Fin n) (h : ℕ) (ρ : Operator ((2^n)*1)) :
    workspaceMass (rejectedTrace U i h ρ).native = (1/2 : ℝ)^h * (Matrix.trace ρ).re := by
  rw [rejectedTrace_native]
  change (Matrix.trace ((1/2 : ℂ)^h • conjBranch (stopRound U i ^ h) ρ)).re = _
  rw [Matrix.trace_smul,trace_conjBranch_unitary _ ((Matrix.unitaryGroup _ _).pow_mem (stopRound_unitary U hU i) h)]
  have hs : (1/2 : ℂ)^h = (((1/2 : ℝ)^h : ℝ) : ℂ) := by push_cast; rfl
  rw [hs]
  simp only [smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

/-- For a unitary oracle, the total rejected mass of the stopping program is `2⁻ʰ` times the
real trace of the input. -/
theorem stoppingProgram_failed_mass {n : ℕ} (U : Operator (2^n))
    (hU : U∈Matrix.unitaryGroup (Fin (2^n)) ℂ) (i : Fin n) (h : ℕ) (ρ : Operator ((2^n)*1)) :
    (((workspaceTraces U (stoppingProgram n i h) ρ).filter (fun t => !t.accepted)).map workspaceMass).sum =
      (1/2 : ℝ)^h * (Matrix.trace ρ).re := by
  have hm := measuredTraces_forget U (stoppingProgram n i h) ρ
  rw [stoppingProgram_measured] at hm
  rw [← hm]
  have hf (xs : List (MeasuredTrace (2^n))) :
      (xs.map MeasuredTrace.native).filter (fun t => !t.accepted) =
        (xs.filter (fun t => !t.native.accepted)).map MeasuredTrace.native := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons,List.filter_cons]
      split_ifs <;> simp_all only [List.map_cons]
  rw [hf,stopMeasured_rejected]
  simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,_root_.add_zero] using!
      rejectedTrace_mass U hU i h ρ

/-- Combines well-formedness of a compiled clean-operation word with its unique measured and
native traces and its exact resource accounting. -/
theorem frontier1 {n : ℕ} (U : Operator (2^n)) (w : List (CleanOp n)) (ρ : Operator ((2^n)*1)) :
    workspaceCircuitWellFormed (compileWord n w) ∧
    measuredTraces U (compileWord n w) ρ = [wordTrace U w ρ] ∧
    workspaceTraces U (compileWord n w) ρ = [(wordTrace U w ρ).native] ∧
    (wordTrace U w ρ).resources n = wordResources n w :=
  ⟨compileWord_wellFormed w,compileWord_measured U w ρ,compileWord_traces U w ρ,wordTrace_resources U w ρ⟩

/-- Combines well-formedness of the stopping program with its measured-trace specification, its
`h + 1` trace count, and uniqueness of the rejected trace. -/
theorem frontier2 {n : ℕ} (U : Operator (2^n)) (i : Fin n) (h : ℕ) (ρ : Operator ((2^n)*1)) :
    workspaceCircuitWellFormed (stoppingProgram n i h) ∧
    measuredTraces U (stoppingProgram n i h) ρ = stopMeasured U i h ρ ∧
    (stopMeasured U i h ρ).length=h+1 ∧
    (stopMeasured U i h ρ).filter (fun t => !t.native.accepted) = [rejectedTrace U i h ρ] :=
  ⟨stoppingProgram_wellFormed n i h,stoppingProgram_measured U i h ρ,
    stopMeasured_length U i h ρ,stopMeasured_rejected U i h ρ⟩

end
end Qatlib.Concepts.QueryComplexity.DegreeMethod.WorkspaceCleanRelease
