/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# A genuine counterexample to the printed complex-phase LCU sandwich

Fixed arXiv:2511.10267v3, equations (6)--(9), pp.8--9. The same phase-bearing
PREPARE on both sides cancels its coefficient phases. The scalar unitary A=i,
s=1, H=1, L=0 gives an exact counterexample: the actual vacuum block is zero,
whereas the claimed block is 1/sqrt(2). The input normalization is alpha_A=1
and the input encoding is exact, so approximation error cannot explain it.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ContourSim25.LcuCircuit
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open scoped BigOperators

/-- The printed one-bit phase preparation, with theta=arctan(s) in equation (6). -/
def phaseDiagonal (θ : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal (fun b => Complex.exp ((if b then θ else -θ) * Complex.I))

/-- A concrete unitary extending exactly the prepared state in the source. -/
def printedPrepare (θ : ℝ) : Matrix Bool Bool ℂ := phaseDiagonal θ * Hadamard

/-- A diagonal unit-phase matrix is a genuine unitary gate. -/
theorem phaseDiagonal_unitary (θ : ℝ) : phaseDiagonal θ ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose,
    phaseDiagonal,Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
  have h : (fun b : Bool => (star (fun b : Bool =>
      Complex.exp ((if b then θ else -θ)*Complex.I))) b *
      Complex.exp ((if b then θ else -θ)*Complex.I)) = (fun _ => (1 : ℂ)) := by
    funext b
    rw [Pi.star_apply,show star (Complex.exp ((if b then θ else -θ)*Complex.I))=
      (starRingEnd ℂ) (Complex.exp ((if b then θ else -θ)*Complex.I)) from rfl,
      ← Complex.normSq_eq_conj_mul_self]
    have hn := Complex.norm_exp_ofReal_mul_I (if b then θ else -θ)
    rw [Complex.normSq_eq_norm_sq,hn]
    norm_num
  rw [h,Matrix.diagonal_one]

/-- The printed preparation is unitary for every phase, including arctan(1). -/
theorem printedPrepare_unitary (θ : ℝ) :
    printedPrepare θ ∈ Matrix.unitaryGroup Bool ℂ :=
  mul_mem (phaseDiagonal_unitary θ) hadamard_unitary

/-- SELECT for the exact zero-system-qubit input oracle A=i and its inverse A*=-i. -/
def scalarSelect : Matrix Bool Bool ℂ := Complex.I • PauliZ

/-- The controlled input-oracle selection is a genuine unitary. -/
theorem scalarSelect_unitary : scalarSelect ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
  ext b c
  cases b <;> cases c <;>
    simp [scalarSelect,PauliZ,Matrix.mul_apply,Matrix.conjTranspose,
      Matrix.diagonal]

/-- The source scheme is an actual three-gate word, not an assumed output matrix. -/
def printedWord (θ : ℝ) : Circuit Bool :=
  [.gate (printedPrepare θ),.gate scalarSelect,.gate (printedPrepare θ)ᴴ]

/-- All three printed operations are unitary; the same word pays three gates and no queries. -/
theorem printedWord_resources (θ : ℝ) :
    IsUnitaryCircuit (printedWord θ) ∧ GateCount (printedWord θ)=3 ∧
    QueryCount (printedWord θ)=0 := by
  have hP := printedPrepare_unitary θ
  have hPs : (printedPrepare θ)ᴴ ∈ Matrix.unitaryGroup Bool ℂ := by
    rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff).mp hP
  refine ⟨?_,rfl,rfl⟩
  simp only [printedWord,isUnitaryCircuit_gate,isUnitaryCircuit_nil,and_true]
  exact ⟨hP,scalarSelect_unitary,hPs⟩

/-- The phase diagonal cancels around this SELECT, as it does for every scalar SELECT. -/
theorem phase_cancels (θ : ℝ) :
    (phaseDiagonal θ)ᴴ * scalarSelect * phaseDiagonal θ = scalarSelect := by
  have hcomm : scalarSelect * phaseDiagonal θ = phaseDiagonal θ * scalarSelect := by
    unfold scalarSelect PauliZ phaseDiagonal
    rw [← Matrix.diagonal_smul,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
    congr 1
    funext b
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  rw [Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc]
  have hp := (Matrix.mem_unitaryGroup_iff').mp (phaseDiagonal_unitary θ)
  rw [Matrix.star_eq_conjTranspose] at hp
  rw [hp,Matrix.one_mul]

/-- The real printed sandwich is i X independently of the phase argument. -/
theorem printed_sandwich (θ : ℝ) :
    (printedPrepare θ)ᴴ * scalarSelect * printedPrepare θ = Complex.I • PauliX := by
  unfold printedPrepare
  rw [Matrix.conjTranspose_mul]
  have h := phase_cancels θ
  calc
    Hadamardᴴ * (phaseDiagonal θ)ᴴ * scalarSelect * (phaseDiagonal θ * Hadamard) =
        Hadamardᴴ * ((phaseDiagonal θ)ᴴ * scalarSelect * phaseDiagonal θ) * Hadamard := by
      simp only [Matrix.mul_assoc]
    _ = Hadamardᴴ * scalarSelect * Hadamard := by rw [h]
    _ = Complex.I • PauliX := by
      have hsq : (Real.sqrt 2 : ℂ)*(Real.sqrt 2 : ℂ)=2 := by
        exact_mod_cast Real.mul_self_sqrt (by norm_num : (0:ℝ)≤2)
      have hinv : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1/2 := by
        rw [← _root_.mul_inv_rev,hsq]
        norm_num
      ext b c
      cases b <;> cases c <;>
        norm_num [scalarSelect,Hadamard,PauliX,PauliZ,permMatrix,
          Matrix.mul_apply,Fintype.sum_bool,Matrix.conjTranspose,Matrix.diagonal]
      all_goals calc
        _ = Complex.I * (2*((Real.sqrt 2 : ℂ)⁻¹*(Real.sqrt 2 : ℂ)⁻¹)) := by ring
        _ = Complex.I := by rw [hinv]; norm_num

/-- For A=i and s=1 the claimed successful block is nonzero. -/
def claimedBlock : ℂ := (Real.sqrt 2 : ℂ)⁻¹

/-- The actual source vacuum block differs from the claimed block at its prescribed phase. -/
theorem printed_inner_counterexample :
    ((printedPrepare (Real.arctan 1))ᴴ * scalarSelect *
      printedPrepare (Real.arctan 1)) false false ≠ claimedBlock := by
  rw [printed_sandwich]
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<2)))
  simpa [PauliX,permMatrix,claimedBlock] using (inv_ne_zero hs).symm
/-- The controlled oracle branches really are A=i and its conjugate adjoint -i. -/
theorem scalarSelect_branches :
    scalarSelect false false=Complex.I ∧ scalarSelect true true= -Complex.I := by
  simp [scalarSelect,PauliZ,Matrix.diagonal]

/-- The whole printed word actually sends the initialized selector to the failing branch. -/
theorem printedWord_run (θ : ℝ) : Run 1 (printedWord θ) (Ket false) = Complex.I • Ket true := by
  change (printedPrepare θ)ᴴ *ᵥ (scalarSelect *ᵥ (printedPrepare θ *ᵥ Ket false)) = _
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,printed_sandwich]
  funext b
  cases b <;> simp [PauliX,permMatrix,Ket,Matrix.mulVec,dotProduct]

end Qatlib.Papers.ContourSim25.LcuCircuit
