/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.KnownGatePerturbation
import Qatlib.Concepts.QsvtCore.QsVtMain.ConventionBridge
import Qatlib.Concepts.QspSimulation.WordModel.CPPAdjointDefs
import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
import Qatlib.Concepts.QspSimulation.Achievability.OraclePerturbation
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
import Qatlib.Concepts.CoherentSim.CoherentOAA.OddApproximation
import QuantumInfo.ForMathlib.Isometry
import Qatlib.Concepts.QsvtCore.QsVtMain.LengthQSVT
import Qatlib.Concepts.SignalPrimitive.HermitianQSVT
import Qatlib.Concepts.HspRecovery.SieveLaw.PaidAdjointCompilation
import Mathlib.Algebra.Polynomial.Eval.SMul
set_option warningAsError false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Polynomial Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open scoped Classical BigOperators Matrix.Norms.L2Operator Kronecker
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Foundations.CircuitReversal.ReversalAlgebra
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.HspRecovery.SieveLaw
open Qatlib.Concepts.MatrixAccess.RitzPipeline

namespace Qatlib.Concepts.NonNormalSpec.ResolventWord
open Polynomial Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib
open Qatlib
open scoped Classical BigOperators Matrix.Norms.L2Operator

def realPolynomial (P : Polynomial ℂ) : Polynomial ℝ :=
  ⟨⟨P.toFinsupp.coeff.mapRange Complex.re rfl⟩⟩

def imagPolynomial (P : Polynomial ℂ) : Polynomial ℝ :=
  ⟨⟨P.toFinsupp.coeff.mapRange Complex.im rfl⟩⟩

@[simp] theorem real_coeff (P : Polynomial ℂ) (n : ℕ) :
    (realPolynomial P).coeff n = (P.coeff n).re := rfl

@[simp] theorem imag_coeff (P : Polynomial ℂ) (n : ℕ) :
    (imagPolynomial P).coeff n = (P.coeff n).im := rfl

theorem complex_reconstruct (P : Polynomial ℂ) :
    P = (realPolynomial P).map Complex.ofRealHom +
      C Complex.I * (imagPolynomial P).map Complex.ofRealHom := by
  ext n
  simp only [coeff_add,coeff_C_mul,coeff_map,real_coeff,imag_coeff]
  simpa only [mul_comm] using! (Complex.re_add_im (P.coeff n)).symm

theorem component_eval (P : Polynomial ℂ) (x : ℝ) :
    (realPolynomial P).eval x = (P.eval (x : ℂ)).re ∧
    (imagPolynomial P).eval x = (P.eval (x : ℂ)).im := by
  have h := congrArg (fun q : Polynomial ℂ => q.eval (x : ℂ)) (complex_reconstruct P)
  simp only [eval_add,eval_mul,eval_C] at h
  have he (q : Polynomial ℝ) : (q.map Complex.ofRealHom).eval (x : ℂ) = ((q.eval x : ℝ) : ℂ) :=
    Polynomial.eval_map_apply Complex.ofRealHom x
  rw [he,he] at h
  exact ⟨by simpa using! (congrArg Complex.re h).symm,
    by simpa using! (congrArg Complex.im h).symm⟩

def evenPart (p : Polynomial ℝ) : Polynomial ℝ := C (1/2) * (p + p.comp (-X))
def oddPart (p : Polynomial ℝ) : Polynomial ℝ := C (1/2) * (p - p.comp (-X))

theorem parity_reconstruct (p : Polynomial ℝ) : evenPart p + oddPart p = p := by
  ext n
  simp only [evenPart,oddPart,coeff_add,coeff_C_mul,coeff_sub]
  ring

theorem evenPart_parity (p : Polynomial ℝ) : HasRealParity 0 (evenPart p) := by
  simp only [HasRealParity,evenPart,mul_comp,C_comp,add_comp,comp_assoc,neg_comp,X_comp,
    neg_neg,comp_X,pow_zero,C_1,one_mul]
  ring

theorem oddPart_parity (p : Polynomial ℝ) : HasRealParity 1 (oddPart p) := by
  simp only [HasRealParity,oddPart,mul_comp,C_comp,sub_comp,comp_assoc,neg_comp,X_comp,
    neg_neg,comp_X,pow_one,C_neg,C_1,neg_one_mul]
  ring

theorem even_eval (p : Polynomial ℝ) (x : ℝ) :
    (evenPart p).eval x = (p.eval x+p.eval (-x))/2 := by
  simp [evenPart]
  ring

theorem odd_eval (p : Polynomial ℝ) (x : ℝ) :
    (oddPart p).eval x = (p.eval x-p.eval (-x))/2 := by
  simp [oddPart]
  ring

def component (P : Polynomial ℂ) (imag odd : Bool) : Polynomial ℝ :=
  let p := if imag then imagPolynomial P else realPolynomial P
  if odd then oddPart p else evenPart p

def routePolynomial (P : Polynomial ℂ) (imag odd : Bool) : Polynomial ℝ :=
  C 4 * component P imag odd

def routePhase (imag : Bool) : ℂ := if imag then Complex.I else 1

theorem four_reconstruct (P : Polynomial ℂ) :
    (1/4 : ℂ) • (∑ b : Bool, ∑ c : Bool,
      C (routePhase b) * (routePolynomial P b c).map Complex.ofRealHom) = P := by
  ext n
  simp [routePolynomial,component,evenPart,oddPart,routePhase]
  conv_rhs => rw [← Complex.re_add_im (P.coeff n)]
  ring

theorem component_bound (P : Polynomial ℂ)
    (hP : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖P.eval (x : ℂ)‖ ≤ 1/4)
    (b c : Bool) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(component P b c).eval x| ≤ 1/4 := by
  let q := if b then imagPolynomial P else realPolynomial P
  have hq (y : ℝ) (hy : y ∈ Set.Icc (-1 : ℝ) 1) : |q.eval y| ≤ 1/4 := by
    cases b
    · change |(realPolynomial P).eval y| ≤ _
      rw [(component_eval P y).1]
      exact (Complex.abs_re_le_norm _).trans (hP y hy)
    · change |(imagPolynomial P).eval y| ≤ _
      rw [(component_eval P y).2]
      exact (Complex.abs_im_le_norm _).trans (hP y hy)
  have hneg : -x ∈ Set.Icc (-1 : ℝ) 1 := by constructor <;> linarith [hx.1,hx.2]
  have h₁ := hq x hx
  have h₂ := hq (-x) hneg
  cases c
  · change |(evenPart q).eval x| ≤ _
    rw [even_eval,abs_div]
    rw [abs_of_pos (by norm_num : (0 : ℝ)<2)]
    have ht := abs_add_le (q.eval x) (q.eval (-x))
    apply (div_le_iff₀ (by norm_num : (0 : ℝ)<2)).mpr
    linarith
  · change |(oddPart q).eval x| ≤ _
    rw [odd_eval,abs_div]
    rw [abs_of_pos (by norm_num : (0 : ℝ)<2)]
    have ht : |q.eval x-q.eval (-x)| ≤ |q.eval x|+|q.eval (-x)| := by
      simpa using! abs_sub_le (q.eval x) 0 (q.eval (-x))
    apply (div_le_iff₀ (by norm_num : (0 : ℝ)<2)).mpr
    linarith

theorem route_bound (P : Polynomial ℂ)
    (hP : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖P.eval (x : ℂ)‖ ≤ 1/4)
    (b c : Bool) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(routePolynomial P b c).eval x| ≤ 1 := by
  have hb := component_bound P hP b c x hx
  simp only [routePolynomial,eval_mul,eval_C,abs_mul]
  rw [abs_of_pos (by norm_num : (0 : ℝ)<4)]
  linarith

theorem component_parity (P : Polynomial ℂ) (b c : Bool) :
    HasRealParity (if c then 1 else 0) (component P b c) := by
  cases c
  · simpa only [component,Bool.false_eq_true,if_false] using!
      evenPart_parity (if b then imagPolynomial P else realPolynomial P)
  · simpa only [component,if_true] using!
      oddPart_parity (if b then imagPolynomial P else realPolynomial P)

theorem route_parity (P : Polynomial ℂ) (b c : Bool) :
    HasRealParity (if c then 1 else 0) (routePolynomial P b c) := by
  have hp := component_parity P b c
  unfold HasRealParity at hp ⊢
  simp only [routePolynomial,mul_comp,C_comp]
  rw [hp]
  ring

end Qatlib.Concepts.NonNormalSpec.ResolventWord

namespace Qatlib.Concepts.NonNormalSpec.ResolventWord.Hermitian
variable {I H : Type} [Fintype I] [DecidableEq I] [Fintype H] [DecidableEq H]

omit [Fintype H] [DecidableEq H] in

theorem odd_polynomial_target (A : Matrix I I ℂ) (hA : A.IsHermitian)
    (p : Polynomial ℝ) (d : ℕ) (hp : HasRealParity d p) (hd : d%2=1) :
    oddSingularTransform A (fun x => ((p.eval x : ℝ) : ℂ)) = aeval A (p.map Complex.ofRealHom) := by
  have ha : Aᴴ=A := hA
  obtain ⟨q,hq⟩ := hermitian_odd_polynomial_factor hp hd
  have hf : (fun x : ℝ => ((p.eval x : ℝ) : ℂ)) =
      (fun x : ℝ => (x : ℂ) * (q.map Complex.ofRealHom).eval ((x : ℂ)^2)) := by
    funext x
    rw [hq, eval_mul, eval_X, eval_comp, eval_pow, eval_X, Complex.ofReal_mul]
    congr 1
    simpa only [← Complex.ofReal_pow] using!
      (Polynomial.eval_map_apply Complex.ofRealHom (x^2)).symm
  rw [hf, ← mul_gram_aeval_eq_oddSingularTransform, hq]
  simp only [Polynomial.map_mul, Polynomial.map_X, Polynomial.map_comp, Polynomial.map_pow,
    Polynomial.aeval_mul, Polynomial.aeval_X, Polynomial.aeval_comp, Polynomial.aeval_X_pow, ha]
  rw [pow_two]

omit [Fintype H] [DecidableEq H] in

theorem even_polynomial_target (A : Matrix I I ℂ) (hA : A.IsHermitian)
    (p : Polynomial ℝ) (d : ℕ) (hp : HasRealParity d p) (hd : d%2=0) :
    rightSingularTransform A (fun x => ((p.eval x : ℝ) : ℂ)) = aeval A (p.map Complex.ofRealHom) := by
  have ha : Aᴴ=A := hA
  have he : Even d := Nat.even_iff.mpr hd
  have heven : p.comp (-X)=p := by
    simpa only [HasRealParity,he.neg_one_pow,Polynomial.C_1,one_mul] using! hp
  let q := contract 2 p
  have hq : q.comp (X^2)=p := comp_square_contract_of_even heven
  have hf : (fun x : ℝ => ((p.eval x : ℝ) : ℂ)) =
      (fun x : ℝ => (q.map Complex.ofRealHom).eval ((x : ℂ)^2)) := by
    funext x
    rw [← hq, eval_comp, eval_pow, eval_X]
    simpa only [← Complex.ofReal_pow] using!
      (Polynomial.eval_map_apply Complex.ofRealHom (x^2)).symm
  rw [hf, ← gram_aeval_eq_rightSingularTransform, ← hq]
  simp only [Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.aeval_comp, Polynomial.aeval_X_pow, ha]
  rw [pow_two]

theorem source_same_frame_polynomial
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (p : Polynomial ℝ) (Φ : List ℝ) (hp : HasRealParity Φ.length p)
    (h : ProjectedUnitaryEncoding A U F F)
    (hre : ∀ x : ℝ, ((sourcePhaseResponse Φ).eval (x : ℂ)).re = p.eval x) :
    ProjectedUnitaryEncoding (aeval A (p.map Complex.ofRealHom))
      (sourceRealWord U (rangeProjector F) (rangeProjector F) Φ)
      (sourceAverageClean F) (sourceAverageClean F) := by
  have hs := source_cpp_real_singular_transform_of_response H I I A U F F p Φ h hre
  by_cases ho : Φ.length%2=1
  · have ht := hs.1 ho
    rw [odd_polynomial_target A hA p Φ.length hp ho] at ht
    exact ht
  · have he : Φ.length%2=0 := by omega
    have ht := hs.2.1 he
    rw [even_polynomial_target A hA p Φ.length hp he] at ht
    exact ht

end Qatlib.Concepts.NonNormalSpec.ResolventWord.Hermitian

namespace Qatlib.Concepts.NonNormalSpec.ResolventWord.Words
variable {H : Type} [Fintype H] [DecidableEq H]

omit [Fintype H] in

theorem cppDataOracle_adjoint {J : Type} [DecidableEq J] (U : Matrix H H ℂ) :
    (cppDataOracle (J:=J) U)ᴴ = cppDataOracle (J:=J) Uᴴ := by
  simp [cppDataOracle, parallelOracle_adjoint, Matrix.conjTranspose_kronecker]

theorem cppWord_eval {J : Type} [Fintype J] [DecidableEq J]
    (U P Q : Matrix H H ℂ) (ss : List (CPPStep J)) :
    evaluate (cppDataOracle U) (cppAdjointWord P Q ss) = cppEvaluate U P Q ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    change instructionMatrix (cppDataOracle U) (cppAdjointStep P Q s) *
      evaluate (cppDataOracle U) (cppAdjointWord P Q ss) =
      cppInstruction U P Q s * cppEvaluate U P Q ss
    rw [ih]
    congr 1
    cases s <;> simp [cppAdjointStep, instructionMatrix, cppInstruction, cppDataOracle,
      parallel_select_adjoint, Matrix.conjTranspose_kronecker, parallelOracle]

omit [Fintype H] in

theorem cppWord_counts {J : Type} [DecidableEq J]
    (P Q : Matrix H H ℂ) (ss : List (CPPStep J)) :
    adjointQueryCount (cppAdjointWord P Q ss) = (cppCounts ss).1 ∧
    adjointGateCount (cppAdjointWord P Q ss) =
      (cppCounts ss).2.1 + (cppCounts ss).2.2.1 + (cppCounts ss).2.2.2 := by
  induction ss with
  | nil => simp [cppAdjointWord, cppCounts, adjointQueryCount, adjointGateCount]
  | cons s ss ih =>
    cases s <;> simp only [cppAdjointWord, List.map_cons, cppAdjointStep, cppCounts,
      adjointQueryCount, adjointGateCount] at * <;> omega

theorem sourceWord_eval (U P Q : Matrix H H ℂ) (Φ : List ℝ) :
    evaluate (cppDataOracle (J:=Bool) U) (sourceCppAdjointWord P Q Φ)
      = sourceRealWord U P Q Φ := by
  unfold sourceCppAdjointWord sourceRealWord
  split_ifs
  · exact cppWord_eval U P Q _
  · rw [evaluate_swapQueries, cppDataOracle_adjoint, cppWord_eval, ← cppEvaluate_swapData]

omit [Fintype H] in

theorem sourceWord_counts (P Q : Matrix H H ℂ) (Φ : List ℝ) :
    adjointQueryCount (sourceCppAdjointWord P Q Φ) = Φ.length ∧
    adjointGateCount (sourceCppAdjointWord P Q Φ) = 3 * Φ.length := by
  have h := cppWord_counts P Q (cppCompile (sourceRealFamily Φ))
  have h' := cppWord_counts Q P (cppCompile (sourceRealFamily Φ))
  rw [cppCompile_counts] at h h'
  have hl : (sourceRealFamily Φ).length = Φ.length := by simp [sourceRealFamily]
  rw [hl] at h h'
  (try dsimp only at h h')
  unfold sourceCppAdjointWord
  split_ifs
  · exact ⟨h.1, by omega⟩
  · rw [adjointQueryCount_swapQueries, adjointGateCount_swapQueries]
    exact ⟨h'.1, by omega⟩

noncomputable def fourWord (cs : Bool → Bool → List (AdjointStep H)) :
    List (AdjointStep (Bool × (Bool × H))) :=
  compileSelected (compileSelected (cs true true) (cs true false))
    (compileSelected (cs false true) (cs false false))

theorem fourWord_eval (U : Matrix H H ℂ) (cs : Bool → Bool → List (AdjointStep H)) :
    evaluate (controlOracle (controlOracle U)) (fourWord cs) =
      select (fun b : Bool => select (fun c : Bool => evaluate U (cs b c))) := by
  simp only [fourWord, evaluate_compileSelected]
  congr 1
  funext b
  cases b <;> simp <;> congr 1 <;> funext c <;> cases c <;> simp

omit [Fintype H] in

theorem fourWord_counts (cs : Bool → Bool → List (AdjointStep H)) :
    adjointQueryCount (fourWord cs) = ∑ b : Bool, ∑ c : Bool, adjointQueryCount (cs b c) ∧
    adjointGateCount (fourWord cs) = (∑ b : Bool, ∑ c : Bool, adjointGateCount (cs b c)) + 6 := by
  simp [fourWord, queryCount_compileSelected, gateCount_compileSelected]
  omega

end Qatlib.Concepts.NonNormalSpec.ResolventWord.Words

namespace Qatlib.Concepts.NonNormalSpec.ResolventWord.Blocks
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib.Concepts.NonNormalSpec.ResolventWord.Words
open scoped BigOperators
variable {H : Type} [Fintype H] [DecidableEq H]

def assoc : Bool × (Bool × H) ≃ (Bool × Bool) × H := (Equiv.prodAssoc Bool Bool H).symm

omit [Fintype H] [DecidableEq H] in

theorem nested_select (V : Bool × Bool → Matrix H H ℂ) :
    select (fun b : Bool => select (fun c : Bool => V (b,c))) =
      (select V).submatrix (assoc (H:=H)) assoc := by
  ext ⟨b,c,i⟩ ⟨b',c',j⟩
  by_cases hb : b=b' <;> by_cases hc : c=c' <;>
    simp [select, assoc, Matrix.submatrix_apply, hb, hc, Prod.ext_iff]

theorem four_word_block (O : Matrix H H ℂ) (cs : Bool → Bool → List (AdjointStep H))
    (a b : Bool × Bool → ℂ) :
    compress ((prepareLift a).submatrix (assoc (H:=H)) id)
      (evaluate (controlOracle (controlOracle O)) (fourWord cs))
      ((prepareLift b).submatrix (assoc (H:=H)) id)
    = ∑ j : Bool × Bool, (star (a j) * b j) • evaluate O (cs j.1 j.2) := by
  rw [fourWord_eval, nested_select (fun j : Bool × Bool => evaluate O (cs j.1 j.2))]
  unfold compress
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  simpa only [Matrix.submatrix_id_id] using!
    (prepare_select_compress_bilinear a b (fun j : Bool × Bool => evaluate O (cs j.1 j.2)))

noncomputable def leftAmp : Bool × Bool → ℂ := fun _ => 1/2

noncomputable def rightAmp : Bool × Bool → ℂ := fun j => if j.1 then Complex.I/2 else 1/2

theorem leftAmp_normalized : ∑ j : Bool × Bool, star (leftAmp j) * leftAmp j = 1 := by
  norm_num [leftAmp, Fintype.sum_prod_type, Fintype.sum_bool]

theorem rightAmp_normalized : ∑ j : Bool × Bool, star (rightAmp j) * rightAmp j = 1 := by
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ _
  norm_num [rightAmp, Fintype.sum_prod_type, Fintype.sum_bool, h2]
  ring_nf
  norm_num [Complex.I_sq]

theorem actual_four_word_unitary (O : Matrix H H ℂ)
    (hO : O ∈ unitaryGroup H ℂ) (cs : Bool → Bool → List (AdjointStep H))
    (hcs : ∀ b c, WellFormedAdjointCircuit (cs b c)) :
    evaluate (controlOracle (controlOracle O)) (fourWord cs) ∈ unitaryGroup (Bool × (Bool × H)) ℂ := by
  apply WellFormedAdjointCircuit.evaluate_unitary
  · exact compileSelected_wellFormed
      (compileSelected_wellFormed (hcs true true) (hcs true false))
      (compileSelected_wellFormed (hcs false true) (hcs false false))
  · exact controlOracle_unitary (controlOracle_unitary hO)

theorem cppWord_wellFormed {J : Type} [Fintype J] [DecidableEq J]
    (P Q : Matrix H H ℂ) (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    (ss : List (CPPStep J)) : WellFormedAdjointCircuit (cppAdjointWord P Q ss) := by
  have hg (s : CPPStep J) : cppInstruction (1 : Matrix H H ℂ) P Q s ∈
      unitaryGroup (J × (Bool × H)) ℂ := by
    have hs := cppEvaluate_unitary (J:=J) (unitaryGroup H ℂ).one_mem hP hQ [s]
    simpa only [cppEvaluate, Matrix.mul_one] using! hs
  induction ss with
  | nil => exact WellFormedAdjointCircuit.nil
  | cons s ss ih =>
    cases s <;> simp only [cppAdjointWord, List.map_cons, cppAdjointStep,
      WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.forward_cons_iff,
      WellFormedAdjointCircuit.backward_cons_iff]
    · exact ⟨hg .projectorP, ih⟩
    · exact ⟨hg .projectorQ, ih⟩
    · exact ih
    · exact ih
    · exact ⟨hg (.phase _), ih⟩

theorem sourceWord_wellFormed (P Q : Matrix H H ℂ)
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q) (Φ : List ℝ) :
    WellFormedAdjointCircuit (sourceCppAdjointWord P Q Φ) := by
  unfold sourceCppAdjointWord
  split_ifs
  · exact cppWord_wellFormed P Q hP hQ _
  · exact (cppWord_wellFormed Q P hQ hP _).swapQueries

end Qatlib.Concepts.NonNormalSpec.ResolventWord.Blocks

namespace Qatlib.Concepts.NonNormalSpec.ResolventWord.Physical
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib.Concepts.NonNormalSpec.ResolventWord.Words
open Qatlib.Concepts.NonNormalSpec.ResolventWord.Blocks
open scoped BigOperators
variable {K I : Type} [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]

noncomputable def hOuter : Matrix (Bool × (Bool × K)) (Bool × (Bool × K)) ℂ := TensorGate Hadamard 1
noncomputable def hInner : Matrix (Bool × (Bool × K)) (Bool × (Bool × K)) ℂ :=
  TensorGate 1 (TensorGate Hadamard 1)
noncomputable def prep : Matrix (Bool × (Bool × K)) (Bool × (Bool × K)) ℂ :=
  TensorGate Hadamard (TensorGate Hadamard 1)
noncomputable def imagPhase : Matrix (Bool × (Bool × K)) (Bool × (Bool × K)) ℂ :=
  TensorGate (Matrix.diagonal (fun b : Bool => if b then Complex.I else 1)) 1
noncomputable def routeFrame (F : Matrix K I ℂ) : Matrix (Bool × (Bool × K)) I ℂ :=
  cppCleanFrame (cppCleanFrame F)

omit [Fintype I] [DecidableEq I] in

theorem hOuter_hInner : hOuter (K:=K) * hInner = prep := by
  simp [hOuter, hInner, prep, tensorGate_mul]
omit [Fintype I] [DecidableEq I] in

theorem hInner_hOuter : hInner (K:=K) * hOuter = prep := by
  simp [hOuter, hInner, prep, tensorGate_mul]
omit [Fintype I] [DecidableEq I] in

theorem prep_adjoint : (prep (K:=K))ᴴ = prep := by
  simp [prep, tensorGate_conjTranspose, hadamard_conjTranspose]

omit [Fintype I] [DecidableEq I] in

theorem prep_routeFrame (F : Matrix K I ℂ) :
    prep * routeFrame F = ((prepareLift leftAmp).submatrix (assoc (H:=K)) id) * F := by
  have hh : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1/2 := by
    rw [← mul_inv, ← pow_two, sqrt2_sq]
    simp [one_div]
  ext ⟨b,c,k⟩ i
  simp [prep, routeFrame, cppCleanFrame, TensorGate, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.one_apply, prepareLift,
    Matrix.submatrix_apply, leftAmp, assoc, hadamard_apply_false, hh]

omit [Fintype I] [DecidableEq I] in

theorem phase_liftAmp (F : Matrix K I ℂ) :
    imagPhase * (((prepareLift leftAmp).submatrix (assoc (H:=K)) id) * F)
      = ((prepareLift rightAmp).submatrix (assoc (H:=K)) id) * F := by
  ext ⟨b,c,k⟩ i
  cases b <;> simp [imagPhase, TensorGate, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.diagonal_apply, Matrix.one_apply, prepareLift,
    Matrix.submatrix_apply, leftAmp, rightAmp, assoc, div_eq_mul_inv, mul_assoc]

noncomputable def physicalWord (cs : Bool → Bool → List (AdjointStep K)) :
    List (AdjointStep (Bool × (Bool × K))) :=
  [.gate hInner, .gate hOuter] ++ fourWord cs ++ [.gate imagPhase, .gate hOuter, .gate hInner]

omit [Fintype I] [DecidableEq I] in

theorem physicalWord_eval (O : Matrix K K ℂ) (cs : Bool → Bool → List (AdjointStep K)) :
    evaluate (controlOracle (controlOracle O)) (physicalWord cs)
      = prep * evaluate (controlOracle (controlOracle O)) (fourWord cs) * imagPhase * prep := by
  simp only [physicalWord, evaluate_append, evaluate, instructionMatrix, Matrix.mul_one]
  rw [hInner_hOuter]
  have h := hOuter_hInner (K:=K)
  simp only [Matrix.mul_assoc] at h ⊢
  rw [h]

omit [Fintype K] [Fintype I] [DecidableEq I] in

theorem physicalWord_counts (cs : Bool → Bool → List (AdjointStep K)) :
    adjointQueryCount (physicalWord cs) = ∑ b : Bool, ∑ c : Bool, adjointQueryCount (cs b c) ∧
    adjointGateCount (physicalWord cs) = (∑ b : Bool, ∑ c : Bool, adjointGateCount (cs b c)) + 11 := by
  have h := fourWord_counts cs
  simp only [physicalWord, adjointQueryCount_append, adjointGateCount_append,
    adjointQueryCount, adjointGateCount]
  omega

omit [Fintype I] [DecidableEq I] in

theorem physicalWord_block (O : Matrix K K ℂ)
    (cs : Bool → Bool → List (AdjointStep K)) (F : Matrix K I ℂ) :
    compress (routeFrame F) (evaluate (controlOracle (controlOracle O)) (physicalWord cs)) (routeFrame F)
      = ∑ j : Bool × Bool, (star (leftAmp j) * rightAmp j) • compress F (evaluate O (cs j.1 j.2)) F := by
  rw [physicalWord_eval]
  have hm : compress (routeFrame F)
      (prep * evaluate (controlOracle (controlOracle O)) (fourWord cs) * imagPhase * prep) (routeFrame F)
    = compress (prep * routeFrame F) (evaluate (controlOracle (controlOracle O)) (fourWord cs))
        (imagPhase * (prep * routeFrame F)) := by
    simp [compress, Matrix.conjTranspose_mul, prep_adjoint, Matrix.mul_assoc]
  rw [hm, prep_routeFrame, phase_liftAmp]
  have hc : compress
      (((prepareLift leftAmp).submatrix (assoc (H:=K)) id) * F)
      (evaluate (controlOracle (controlOracle O)) (fourWord cs))
      (((prepareLift rightAmp).submatrix (assoc (H:=K)) id) * F)
    = compress F (compress ((prepareLift leftAmp).submatrix (assoc (H:=K)) id)
      (evaluate (controlOracle (controlOracle O)) (fourWord cs))
      ((prepareLift rightAmp).submatrix (assoc (H:=K)) id)) F := by
    simp [compress, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hc, four_word_block]
  simp [compress, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

omit [Fintype I] [DecidableEq I] in

theorem physicalWord_block_phase (O : Matrix K K ℂ)
    (cs : Bool → Bool → List (AdjointStep K)) (F : Matrix K I ℂ) :
    compress (routeFrame F) (evaluate (controlOracle (controlOracle O)) (physicalWord cs)) (routeFrame F)
      = (1/4 : ℂ) • ∑ j : Bool × Bool,
        (if j.1 then Complex.I else 1) • compress F (evaluate O (cs j.1 j.2)) F := by
  rw [physicalWord_block, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_smul]
  congr 1
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ _
  rcases j with ⟨b,c⟩
  cases b with
  | false => norm_num [leftAmp, rightAmp, h2]
  | true =>
    norm_num [leftAmp, rightAmp, h2]
    ring

omit [Fintype K] [Fintype I] [DecidableEq I] in

theorem physical_source_counts (P Q : Matrix K K ℂ) (Φ : Bool → Bool → List ℝ) :
    adjointQueryCount (physicalWord (fun b c => sourceCppAdjointWord P Q (Φ b c)))
        = ∑ b : Bool, ∑ c : Bool, (Φ b c).length ∧
    adjointGateCount (physicalWord (fun b c => sourceCppAdjointWord P Q (Φ b c)))
        = 3 * (∑ b : Bool, ∑ c : Bool, (Φ b c).length) + 11 := by
  have h := physicalWord_counts (fun b c => sourceCppAdjointWord P Q (Φ b c))
  have hq (b c : Bool) := (sourceWord_counts P Q (Φ b c)).1
  have hg (b c : Bool) := (sourceWord_counts P Q (Φ b c)).2
  simpa only [hq, hg, ← Finset.mul_sum] using! h

end Qatlib.Concepts.NonNormalSpec.ResolventWord.Physical

namespace Qatlib.Concepts.NonNormalSpec.ResolventWord.Canonical
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib.Concepts.NonNormalSpec.ResolventWord.Words
open Qatlib.Concepts.NonNormalSpec.ResolventWord.Physical
open scoped BigOperators
variable {H I : Type} [Fintype H] [DecidableEq H]

abbrev SourceSpace (H : Type) := Bool × (Bool × H)
abbrev CanonSpace (H : Type) := Bool × (Bool × SourceSpace H)

noncomputable def realavgGate : Matrix (SourceSpace H) (SourceSpace H) ℂ := TensorGate Hadamard 1
noncomputable def allZeroSource (F : Matrix H I ℂ) : Matrix (SourceSpace H) I ℂ :=
  cppCleanFrame (cppCleanFrame F)

noncomputable def avgPhase : ℂ := (Real.sqrt 2 : ℂ)⁻¹ * (1-Complex.I)

theorem avgPhase_amplitude (b : Bool) :
    avgPhase * realPartAmplitude b = (Real.sqrt 2 : ℂ)⁻¹ := by
  unfold avgPhase realPartAmplitude
  ring_nf
  norm_num [Complex.I_sq]
  ring

theorem avgPhase_unit : star avgPhase * avgPhase = 1 := by
  have hh : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1/2 := by
    rw [← mul_inv, ← pow_two, sqrt2_sq]
    simp [one_div]
  calc
    star avgPhase * avgPhase = ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) * 2 := by
      simp only [avgPhase, star_mul, star_sub, star_one, Complex.star_def, Complex.conj_I]
      ring_nf
      norm_num [Complex.I_sq, ← inv_pow]
      ring
    _ = 1 := by rw [hh]; norm_num

theorem realavg_prepare (F : Matrix H I ℂ) :
    realavgGate * allZeroSource F = avgPhase • sourceAverageClean F := by
  ext ⟨b,c,h⟩ i
  have hc := avgPhase_amplitude b
  cases c <;> simp [realavgGate, allZeroSource, sourceAverageClean, averageFrame,
    cppCleanFrame, TensorGate, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.one_apply, prepareLift, Matrix.smul_apply, hadamard_apply_false, ← mul_assoc, hc]

noncomputable def spectatorAvgGate : Matrix (CanonSpace H) (CanonSpace H) ℂ :=
  TensorGate 1 (TensorGate 1 (realavgGate (H:=H)))
noncomputable def canonicalFrame (F : Matrix H I ℂ) : Matrix (CanonSpace H) I ℂ :=
  routeFrame (allZeroSource F)

omit [DecidableEq H] in

theorem spectator_route_action (V : Matrix (SourceSpace H) (SourceSpace H) ℂ)
    (F : Matrix (SourceSpace H) I ℂ) :
    TensorGate 1 (TensorGate 1 V) * routeFrame F = routeFrame (V*F) := by
  ext ⟨b,c,h⟩ i
  cases b <;> cases c <;> simp [routeFrame, cppCleanFrame, TensorGate,
    Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply]

omit [Fintype H] [DecidableEq H] in

theorem routeFrame_smul (z : ℂ) (F : Matrix (SourceSpace H) I ℂ) :
    routeFrame (z • F) = z • routeFrame F := by
  ext ⟨b,c,h⟩ i
  cases b <;> cases c <;> simp [routeFrame, cppCleanFrame, Matrix.smul_apply]

theorem canonical_prepare (F : Matrix H I ℂ) :
    spectatorAvgGate * canonicalFrame F = avgPhase • routeFrame (sourceAverageClean F) := by
  rw [spectatorAvgGate, canonicalFrame, spectator_route_action, realavg_prepare, routeFrame_smul]

omit [DecidableEq H] in

theorem compress_phase_frame (z : ℂ) (F : Matrix (CanonSpace H) I ℂ)
    (W : Matrix (CanonSpace H) (CanonSpace H) ℂ) (hz : star z*z=1) :
    compress (z • F) W (z • F) = compress F W F := by
  have hz' : z * star z = 1 := (mul_comm z (star z)).trans hz
  simp only [compress, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  exact (congrArg (fun c : ℂ => c • (Fᴴ * W * F)) hz').trans (one_smul ℂ _)

omit I in

theorem spectatorAvgGate_adjoint : (spectatorAvgGate (H:=H))ᴴ = spectatorAvgGate := by
  simp [spectatorAvgGate, realavgGate, tensorGate_conjTranspose, hadamard_conjTranspose]

noncomputable def canonicalWord (cs : Bool → Bool → List (AdjointStep (SourceSpace H))) :
    List (AdjointStep (CanonSpace H)) :=
  [.gate spectatorAvgGate] ++ physicalWord cs ++ [.gate spectatorAvgGate]

theorem canonical_block (O : Matrix (SourceSpace H) (SourceSpace H) ℂ)
    (cs : Bool → Bool → List (AdjointStep (SourceSpace H))) (F : Matrix H I ℂ) :
    compress (canonicalFrame F)
      (evaluate (controlOracle (controlOracle O)) (canonicalWord cs)) (canonicalFrame F)
      = compress (routeFrame (sourceAverageClean F))
        (evaluate (controlOracle (controlOracle O)) (physicalWord cs))
        (routeFrame (sourceAverageClean F)) := by
  have he : evaluate (controlOracle (controlOracle O)) (canonicalWord cs) =
      spectatorAvgGate * evaluate (controlOracle (controlOracle O)) (physicalWord cs) * spectatorAvgGate := by
    simp [canonicalWord, evaluate_append, evaluate, instructionMatrix, Matrix.mul_assoc]
  rw [he]
  have hc : compress (canonicalFrame F)
      (spectatorAvgGate * evaluate (controlOracle (controlOracle O)) (physicalWord cs) * spectatorAvgGate)
      (canonicalFrame F) = compress (spectatorAvgGate * canonicalFrame F)
        (evaluate (controlOracle (controlOracle O)) (physicalWord cs))
        (spectatorAvgGate * canonicalFrame F) := by
    simp [compress, Matrix.conjTranspose_mul, spectatorAvgGate_adjoint, Matrix.mul_assoc]
  rw [hc, canonical_prepare, compress_phase_frame avgPhase _ _ avgPhase_unit]

omit I [Fintype H] in

theorem canonical_source_counts (P Q : Matrix H H ℂ) (Φ : Bool → Bool → List ℝ) :
    adjointQueryCount (canonicalWord (fun b c => sourceCppAdjointWord P Q (Φ b c)))
      = ∑ b : Bool, ∑ c : Bool, (Φ b c).length ∧
    adjointGateCount (canonicalWord (fun b c => sourceCppAdjointWord P Q (Φ b c)))
      = 3 * (∑ b : Bool, ∑ c : Bool, (Φ b c).length) + 13 := by
  have h := physical_source_counts P Q Φ
  simp only [canonicalWord, adjointQueryCount_append, adjointGateCount_append,
    adjointQueryCount, adjointGateCount]
  omega

omit I [DecidableEq H] in

theorem canonical_four_flags : Fintype.card (CanonSpace H) = 2^4 * Fintype.card H := by
  simp [CanonSpace, SourceSpace, Fintype.card_prod]
  ring

omit [Fintype H] [DecidableEq H] in

theorem canonicalFrame_apply (F : Matrix H I ℂ) (r₁ r₂ avg cpp : Bool) (h : H) (i : I) :
    canonicalFrame F (r₁,(r₂,(avg,(cpp,h)))) i =
      if r₁ || r₂ || avg || cpp then 0 else F h i := by
  cases r₁ <;> cases r₂ <;> cases avg <;> cases cpp <;> rfl

end Qatlib.Concepts.NonNormalSpec.ResolventWord.Canonical

namespace Qatlib.Concepts.NonNormalSpec.ResolventWord.ComplexFourRouteLcu
open Polynomial Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib
open Qatlib
open Words Hermitian Physical Canonical
open scoped Classical BigOperators Matrix.Norms.L2Operator

structure PhaseTables (P : Polynomial ℂ) where
  phases : Bool → Bool → List ℝ
  parity : ∀ b c, HasRealParity (phases b c).length (routePolynomial P b c)
  response : ∀ b c (x : ℝ), ((sourcePhaseResponse (phases b c)).eval (x : ℂ)).re =
    (routePolynomial P b c).eval x

variable {I H : Type} [Fintype I] [DecidableEq I] [Fintype H] [DecidableEq H]

def idealWord (F : Matrix H I ℂ) {P : Polynomial ℂ} (tables : PhaseTables P) :
    List (AdjointStep (CanonSpace H)) :=
  canonicalWord (fun b c => sourceCppAdjointWord (rangeProjector F) (rangeProjector F)
    (tables.phases b c))

theorem idealWord_block (A : Matrix I I ℂ) (hA : A.IsHermitian)
    (U : Matrix H H ℂ) (F : Matrix H I ℂ) (h : ProjectedUnitaryEncoding A U F F)
    (P : Polynomial ℂ) (tables : PhaseTables P) :
    compress (canonicalFrame F)
      (evaluate (controlOracle (controlOracle (cppDataOracle (J:=Bool) U))) (idealWord F tables))
      (canonicalFrame F) = aeval A P := by
  rw [idealWord,canonical_block,physicalWord_block_phase]
  have hr (b c : Bool) : compress (sourceAverageClean F)
      (evaluate (cppDataOracle (J:=Bool) U)
        (sourceCppAdjointWord (rangeProjector F) (rangeProjector F) (tables.phases b c)))
      (sourceAverageClean F) = aeval A ((routePolynomial P b c).map Complex.ofRealHom) := by
    rw [sourceWord_eval]
    exact (source_same_frame_polynomial A hA U F (routePolynomial P b c) _
      (tables.parity b c) h (tables.response b c)).encoded
  simp only [Fintype.sum_prod_type,hr]
  have hp := congrArg (aeval A) (four_reconstruct P)
  simpa only [map_smul,map_sum,map_mul,aeval_C,Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc,Matrix.one_mul,routePhase] using! hp

omit [DecidableEq I] [Fintype H] in

theorem idealWord_counts (F : Matrix H I ℂ) {P : Polynomial ℂ} (tables : PhaseTables P) :
    adjointQueryCount (idealWord F tables) = ∑ b : Bool, ∑ c : Bool, (tables.phases b c).length ∧
    adjointGateCount (idealWord F tables) =
      3 * (∑ b : Bool, ∑ c : Bool, (tables.phases b c).length) + 13 :=
  canonical_source_counts _ _ _

end Qatlib.Concepts.NonNormalSpec.ResolventWord.ComplexFourRouteLcu

open Qatlib.Concepts.NonNormalSpec.ResolventWord.ComplexFourRouteLcu

namespace Qatlib.Concepts.NonNormalSpec.ResolventWord.SingleControl
variable {J H : Type} [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]
abbrev Base (J H : Type) := J × H
abbrev Work (J H : Type) := J × (Bool × H)

abbrev multiply {M N K : Type} [Fintype N] (A : Matrix M N ℂ) (B : Matrix N K ℂ) : Matrix M K ℂ :=
  @HMul.hMul (Matrix M N ℂ) (Matrix N K ℂ) (Matrix M K ℂ)
    Matrix.instHMulOfFintypeOfMulOfAddCommMonoid A B

private theorem mm_assoc {L M N K : Type} [Fintype M] [Fintype N]
    (A : Matrix L M ℂ) (B : Matrix M N ℂ) (C : Matrix N K ℂ) :
    multiply (multiply A B) C = multiply A (multiply B C) := Matrix.mul_assoc A B C

def insert (w : Bool) (x : Base J H) : Work J H := (x.1,(w,x.2))
def clean : Matrix (Work J H) (Base J H) ℂ :=
  (1 : Matrix (Work J H) (Work J H) ℂ).submatrix id (insert false)

local notation "E" => (clean (J:=J) (H:=H))

theorem clean_isometry : multiply Eᴴ E = 1 := by
  apply Matrix.submatrix_one_id_right_isometry
  intro x y he
  have hh := congrArg (fun z : Work J H => (z.1,z.2.2)) he
  exact hh

theorem mul_clean (M : Matrix (Work J H) (Work J H) ℂ) (a : Work J H) (b : Base J H) :
    (multiply M E) a b = M a (insert false b) := by
  simp [multiply,Matrix.mul_apply,clean,Matrix.submatrix_apply,Matrix.one_apply]

theorem clean_mul (M : Matrix (Base J H) (Base J H) ℂ) (a : Work J H) (b : Base J H) :
    (multiply E M) a b = if a.2.1=false then M (a.1,a.2.2) b else 0 := by
  rcases a with ⟨j,w,h⟩
  cases w <;> simp [multiply,Matrix.mul_apply,clean,insert,Matrix.submatrix_apply,Matrix.one_apply,
    Fintype.sum_prod_type,ite_and]

def workEquiv : Work J H ≃ Bool × Base J H where
  toFun z := (z.2.1,(z.1,z.2.2))
  invFun z := (z.2.1,(z.1,z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def liftFixed (G : Matrix (Base J H) (Base J H) ℂ) : Matrix (Work J H) (Work J H) ℂ :=
  relabelGate (workEquiv (J:=J) (H:=H)).symm (parallelOracle (J:=Bool) G)

theorem liftFixed_unitary {G : Matrix (Base J H) (Base J H) ℂ}
    (hG : G ∈ Matrix.unitaryGroup (Base J H) ℂ) : liftFixed G ∈ Matrix.unitaryGroup (Work J H) ℂ :=
  (relabelGate_mem_unitaryGroup _ _).mpr (parallelOracle_unitary hG)

theorem liftFixed_clean (G : Matrix (Base J H) (Base J H) ℂ) : multiply (liftFixed G) E = multiply E G := by
  ext a b
  rw [mul_clean,clean_mul]
  simp [liftFixed,relabelGate,Matrix.reindex_apply,workEquiv,parallelOracle,select,insert]

def flipWork (p : J → Bool) (a : Work J H) : Work J H := (a.1,(a.2.1 ^^ p a.1,a.2.2))
omit [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H] in

theorem flipWork_involutive (p : J → Bool) : Function.Involutive (flipWork (H:=H) p) := by
  intro a
  simp [flipWork]

def toggle (p : J → Bool) : Matrix (Work J H) (Work J H) ℂ := permMatrix (flipWork p)

theorem toggle_unitary (p : J → Bool) : toggle (H:=H) p ∈ Matrix.unitaryGroup (Work J H) ℂ :=
  permMatrix_unitary (flipWork_involutive p)

theorem toggle_mul (p : J → Bool) (M : Matrix (Work J H) (Work J H) ℂ) (a b : Work J H) :
    (multiply (toggle (H:=H) p) M) a b = M (flipWork p a) b := by
  change ApplyGate (permMatrix (flipWork p)) (fun x => M x b) a = _
  exact applyGate_permMatrix (flipWork_involutive p) _ _

theorem mul_toggle (p : J → Bool) (M : Matrix (Work J H) (Work J H) ℂ) (a b : Work J H) :
    (multiply M (toggle (H:=H) p)) a b = M a (flipWork p b) := by
  simp [multiply,Matrix.mul_apply,toggle,permMatrix]

def conditional (p : J → Bool) (U : Matrix H H ℂ) : Matrix (Base J H) (Base J H) ℂ :=
  select (fun j => if p j then U else 1)

theorem routed_query (p : J → Bool) (U : Matrix H H ℂ) :
    multiply (multiply (multiply (toggle (H:=H) p) (parallelOracle (J:=J) (controlOracle U))) (toggle (H:=H) p)) E = multiply E (conditional p U) := by
  ext ⟨j,w,h⟩ ⟨k,l⟩
  rw [mul_clean,mul_toggle,toggle_mul,clean_mul]
  by_cases he : j=k
  · subst k
    cases w <;> cases hp : p j <;>
      simp [parallelOracle,controlOracle,conditional,select,flipWork,insert,hp,Matrix.one_apply]
  · simp [parallelOracle,controlOracle,conditional,select,flipWork,insert,he]

def compileStep (p : J → Bool) : AdjointStep (Base J H) → List (AdjointStep (Work J H))
  | .gate G => [.gate (liftFixed G)]
  | .forward => [.gate (toggle p), .forward, .gate (toggle p)]
  | .backward => [.gate (toggle p), .backward, .gate (toggle p)]
def compile (p : J → Bool) (cs : List (AdjointStep (Base J H))) :
    List (AdjointStep (Work J H)) := cs.flatMap (compileStep p)

omit [Fintype J] [Fintype H] in

theorem conditional_adjoint (p : J → Bool) (U : Matrix H H ℂ) :
    (conditional p U)ᴴ = conditional p Uᴴ := by
  rw [conditional, parallel_select_adjoint]
  congr 1
  funext j
  cases p j <;> simp

theorem compileStep_clean (p : J → Bool) (U : Matrix H H ℂ) (s : AdjointStep (Base J H)) :
    multiply (evaluate (parallelOracle (J:=J) (controlOracle U)) (compileStep p s)) E =
      multiply E (instructionMatrix (conditional p U) s) := by
  cases s with
  | gate G => simpa [compileStep,evaluate,instructionMatrix] using! liftFixed_clean G
  | forward => simpa [compileStep,evaluate,instructionMatrix,Matrix.mul_assoc] using! routed_query p U
  | backward =>
    simpa [compileStep,evaluate,instructionMatrix,Matrix.mul_assoc,
      parallelOracle_adjoint,controlOracle_adjoint,conditional_adjoint] using! routed_query p Uᴴ

theorem compile_clean (p : J → Bool) (U : Matrix H H ℂ) (cs : List (AdjointStep (Base J H))) :
    multiply (evaluate (parallelOracle (J:=J) (controlOracle U)) (compile p cs)) E =
      multiply E (evaluate (conditional p U) cs) := by
  induction cs with
  | nil => simp [compile,evaluate,multiply]
  | cons s cs ih =>
    change multiply (evaluate _ (compileStep p s ++ compile p cs)) E = _
    rw [evaluate_append]
    change multiply (_ * _) E = multiply E (instructionMatrix (conditional p U) s * _)
    rw [show multiply (evaluate (parallelOracle (J:=J) (controlOracle U)) (compileStep p s) *
      evaluate (parallelOracle (J:=J) (controlOracle U)) (compile p cs)) E =
      multiply (evaluate (parallelOracle (J:=J) (controlOracle U)) (compileStep p s))
        (multiply (evaluate (parallelOracle (J:=J) (controlOracle U)) (compile p cs)) E) from
          Matrix.mul_assoc _ _ _]
    rw [ih, ← mm_assoc, compileStep_clean, mm_assoc]

omit [Fintype J] [Fintype H] in

theorem compile_counts (p : J → Bool) (cs : List (AdjointStep (Base J H))) :
    adjointQueryCount (compile p cs) = adjointQueryCount cs ∧
    adjointGateCount (compile p cs) = adjointGateCount cs + 2 * adjointQueryCount cs := by
  induction cs with
  | nil => simp [compile,adjointQueryCount,adjointGateCount]
  | cons s cs ih =>
    cases s <;> simp
        [compile,List.flatMap_cons,compileStep,adjointQueryCount,adjointGateCount] at * <;> omega

theorem compile_wellFormed (p : J → Bool) (cs : List (AdjointStep (Base J H)))
    (hcs : WellFormedAdjointCircuit cs) : WellFormedAdjointCircuit (compile p cs) := by
  induction cs with
  | nil => exact WellFormedAdjointCircuit.nil
  | cons s cs ih =>
    have ht : WellFormedAdjointCircuit cs := by
      intro G hG
      exact hcs G (List.mem_cons_of_mem s hG)
    have hc := ih ht
    cases s with
    | gate G =>
      have hg : G ∈ unitaryGroup (Base J H) ℂ := hcs G (by simp)
      simpa only [compile,List.flatMap_cons,compileStep,List.singleton_append] using!
        (WellFormedAdjointCircuit.gate_cons_iff _ _).mpr ⟨liftFixed_unitary hg,hc⟩
    | forward =>
      simp only [compile,List.flatMap_cons,compileStep,List.cons_append,List.nil_append,
        WellFormedAdjointCircuit.gate_cons_iff,WellFormedAdjointCircuit.forward_cons_iff]
      exact ⟨toggle_unitary p,toggle_unitary p,hc⟩
    | backward =>
      simp only [compile,List.flatMap_cons,compileStep,List.cons_append,List.nil_append,
        WellFormedAdjointCircuit.gate_cons_iff,WellFormedAdjointCircuit.backward_cons_iff]
      exact ⟨toggle_unitary p,toggle_unitary p,hc⟩
end Qatlib.Concepts.NonNormalSpec.ResolventWord.SingleControl

namespace Qatlib.Concepts.NonNormalSpec.ResolventWord.Native
open Canonical SingleControl

abbrev Header := Bool × (Bool × (Bool × Bool))

def pack {H : Type} : CanonSpace H ≃ Header × H where
  toFun z := ((z.1,(z.2.1,(z.2.2.1,z.2.2.2.1))),z.2.2.2.2)
  invFun z := (z.1.1,(z.1.2.1,(z.1.2.2.1,(z.1.2.2.2,z.2))))
  left_inv _ := rfl
  right_inv _ := rfl

def routeEnabled (j : Header) : Bool := j.1 && j.2.1

noncomputable def relabelAdjointStep {K L : Type} (e : K ≃ L) : AdjointStep K → AdjointStep L
  | .gate G => .gate (relabelGate e G)
  | .forward => .forward
  | .backward => .backward
noncomputable def relabelWord {K L : Type} (e : K ≃ L) (cs : List (AdjointStep K)) :
    List (AdjointStep L) := cs.map (relabelAdjointStep e)

theorem relabel_adjoint {K L : Type} (e : K ≃ L) (U : Matrix K K ℂ) :
    (relabelGate e U)ᴴ = relabelGate e Uᴴ := by
  ext i j
  rfl

theorem relabel_eval {K L : Type} [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
    (e : K ≃ L) (O : Matrix K K ℂ) (cs : List (AdjointStep K)) :
    evaluate (relabelGate e O) (relabelWord e cs) = relabelGate e (evaluate O cs) := by
  induction cs with
  | nil => exact (CircuitRelabel.relabelGate_one e).symm
  | cons s cs ih =>
    change instructionMatrix (relabelGate e O) (relabelAdjointStep e s) *
      evaluate (relabelGate e O) (relabelWord e cs) =
        relabelGate e (instructionMatrix O s * evaluate O cs)
    rw [ih,CircuitRelabel.relabelGate_mul]
    congr 1
    cases s <;> simp [relabelAdjointStep,instructionMatrix,relabel_adjoint]

theorem relabel_counts {K L : Type} (e : K ≃ L) (cs : List (AdjointStep K)) :
    adjointQueryCount (relabelWord e cs) = adjointQueryCount cs ∧
    adjointGateCount (relabelWord e cs) = adjointGateCount cs := by
  induction cs with
  | nil => exact ⟨rfl,rfl⟩
  | cons s cs ih =>
    cases s <;> simp only [relabelWord,List.map_cons,relabelAdjointStep,
      adjointQueryCount,adjointGateCount] at * <;> omega

theorem relabel_wellFormed {K L : Type} [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
    (e : K ≃ L) (cs : List (AdjointStep K)) (hcs : WellFormedAdjointCircuit cs) :
    WellFormedAdjointCircuit (relabelWord e cs) := by
  intro G hG
  obtain ⟨s,hs,he⟩ := List.mem_map.mp hG
  cases s with
  | gate V =>
    have he' : relabelGate e V = G := by simpa [relabelAdjointStep] using! he
    rw [← he']
    exact (relabelGate_mem_unitaryGroup e V).mpr (hcs V hs)
  | forward => simp [relabelAdjointStep] at he
  | backward => simp [relabelAdjointStep] at he

variable {I H : Type} [Fintype I] [DecidableEq I] [Fintype H] [DecidableEq H]

omit [Fintype H] in

theorem packed_oracle (U : Matrix H H ℂ) :
    relabelGate (pack (H:=H)) (controlOracle (controlOracle (cppDataOracle (J:=Bool) U))) =
      conditional routeEnabled U := by
  ext ⟨⟨r,s,a,c⟩,h⟩ ⟨⟨r',s',a',c'⟩,h'⟩
  cases r <;> cases s <;> cases r' <;> cases s' <;>
    simp [relabelGate,Matrix.reindex_apply,pack,conditional,routeEnabled,controlOracle,
      cppDataOracle,parallelOracle,select,Matrix.one_apply,Prod.ext_iff,
      and_left_comm,and_comm,ite_and] <;> split_ifs <;> simp_all

def word (F : Matrix H I ℂ) {P : Polynomial ℂ} (tables : PhaseTables P) :
    List (AdjointStep (Work Header H)) := compile routeEnabled (relabelWord pack (idealWord F tables))

def frame (F : Matrix H I ℂ) : Matrix (Work Header H) I ℂ :=
  multiply (clean (J:=Header) (H:=H)) ((canonicalFrame F).submatrix pack.symm id)

omit [DecidableEq I] [Fintype H] in

theorem word_counts (F : Matrix H I ℂ) {P : Polynomial ℂ} (tables : PhaseTables P) :
    adjointQueryCount (word F tables) = ∑ b : Bool, ∑ c : Bool, (tables.phases b c).length ∧
    adjointGateCount (word F tables) = 5 * (∑ b : Bool, ∑ c : Bool, (tables.phases b c).length) + 13 := by
  have hc := compile_counts routeEnabled (relabelWord pack (idealWord F tables))
  have hr := relabel_counts pack (idealWord F tables)
  have hi := idealWord_counts F tables
  simp only [word]
  constructor <;> omega

omit I [DecidableEq I] [DecidableEq H] in

theorem five_flags : Fintype.card (Work Header H) = 2^5 * Fintype.card H := by
  simp [Work,Header,Fintype.card_prod]
  ring

end Qatlib.Concepts.NonNormalSpec.ResolventWord.Native

namespace Qatlib.Concepts.NonNormalSpec.ResolventWord.SingleControl
variable {J H : Type} [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]

theorem compile_compress (p : J → Bool) (U : Matrix H H ℂ)
    (cs : List (AdjointStep (Base J H))) :
    compress (clean (J:=J) (H:=H))
      (evaluate (parallelOracle (J:=J) (controlOracle U)) (compile p cs)) clean =
      evaluate (conditional p U) cs := by
  change multiply (multiply (clean (J:=J) (H:=H))ᴴ _) clean = _
  rw [mm_assoc,compile_clean,← mm_assoc,clean_isometry]
  exact Matrix.one_mul _
end Qatlib.Concepts.NonNormalSpec.ResolventWord.SingleControl

namespace Qatlib.Concepts.NonNormalSpec.ResolventWord.Native
open Canonical Physical Words Blocks SingleControl
variable {I H : Type} [Fintype I] [DecidableEq I] [Fintype H] [DecidableEq H]

omit [Fintype I] [DecidableEq I] [DecidableEq H] in

theorem relabel_compress (F : Matrix (CanonSpace H) I ℂ)
    (V : Matrix (CanonSpace H) (CanonSpace H) ℂ) :
    compress (F.submatrix pack.symm id) (relabelGate pack V) (F.submatrix pack.symm id) =
      compress F V F := by
  change multiply (multiply (F.submatrix pack.symm id)ᴴ
    (V.submatrix pack.symm pack.symm)) (F.submatrix pack.symm id) = _
  rw [Matrix.conjTranspose_submatrix]
  dsimp only [multiply]
  rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
  rfl

theorem word_block (A : Matrix I I ℂ) (hA : A.IsHermitian)
    (U : Matrix H H ℂ) (F : Matrix H I ℂ) (h : ProjectedUnitaryEncoding A U F F)
    (P : Polynomial ℂ) (tables : PhaseTables P) :
    compress (frame F) (evaluate (parallelOracle (J:=Header) (controlOracle U)) (word F tables))
      (frame F) = aeval A P := by
  have hc : compress (frame F)
      (evaluate (parallelOracle (J:=Header) (controlOracle U)) (word F tables)) (frame F) =
      compress ((canonicalFrame F).submatrix pack.symm id)
        (compress (clean (J:=Header) (H:=H))
          (evaluate (parallelOracle (J:=Header) (controlOracle U)) (word F tables)) clean)
        ((canonicalFrame F).submatrix pack.symm id) := by
    simp only [frame,multiply,compress,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [hc,word,compile_compress,← packed_oracle,relabel_eval,relabel_compress]
  exact idealWord_block A hA U F h P tables

theorem physicalWord_wellFormed {K : Type} [Fintype K] [DecidableEq K]
    (cs : Bool → Bool → List (AdjointStep K)) (hcs : ∀ b c, WellFormedAdjointCircuit (cs b c)) :
    WellFormedAdjointCircuit (physicalWord cs) := by
  have ho : hOuter (K:=K) ∈ unitaryGroup _ ℂ :=
      tensorGate_unitary hadamard_unitary (unitaryGroup _ ℂ).one_mem
  have hi : hInner (K:=K) ∈ unitaryGroup _ ℂ := tensorGate_unitary (unitaryGroup _ ℂ).one_mem
    (tensorGate_unitary hadamard_unitary (unitaryGroup _ ℂ).one_mem)
  have hp : imagPhase (K:=K) ∈ unitaryGroup _ ℂ := by
    apply tensorGate_unitary _ (unitaryGroup _ ℂ).one_mem
    apply diagonal_mem_unitaryGroup
    intro b
    cases b <;> norm_num
  have hs := compileSelected_wellFormed
    (compileSelected_wellFormed (hcs true true) (hcs true false))
    (compileSelected_wellFormed (hcs false true) (hcs false false))
  have hpre : WellFormedAdjointCircuit ([.gate hInner,.gate hOuter] : List (AdjointStep (Bool × (Bool × K)))) := by
    simp only [WellFormedAdjointCircuit.gate_cons_iff,WellFormedAdjointCircuit.nil,and_true]
    exact ⟨hi,ho⟩
  have hpost : WellFormedAdjointCircuit ([.gate imagPhase,.gate hOuter,.gate hInner] : List (AdjointStep (Bool × (Bool × K)))) := by
    simp only [WellFormedAdjointCircuit.gate_cons_iff,WellFormedAdjointCircuit.nil,and_true]
    exact ⟨hp,ho,hi⟩
  exact (hpre.append hs).append hpost

theorem idealWord_wellFormed (F : Matrix H I ℂ) (hF : IsIsometry F)
    {P : Polynomial ℂ} (tables : PhaseTables P) : WellFormedAdjointCircuit (idealWord F tables) := by
  have hproj := rangeProjector_isOrthogonalProjector hF
  have hs := physicalWord_wellFormed
    (fun b c => sourceCppAdjointWord (rangeProjector F) (rangeProjector F) (tables.phases b c))
    (fun b c => sourceWord_wellFormed _ _ hproj hproj _)
  have hh : spectatorAvgGate (H:=H) ∈ unitaryGroup _ ℂ :=
    tensorGate_unitary (unitaryGroup _ ℂ).one_mem (tensorGate_unitary (unitaryGroup _ ℂ).one_mem
      (tensorGate_unitary hadamard_unitary (unitaryGroup _ ℂ).one_mem))
  have hg : WellFormedAdjointCircuit ([.gate spectatorAvgGate] : List (AdjointStep (CanonSpace H))) := by
    simpa using! hh
  exact (hg.append hs).append hg

theorem word_wellFormed (F : Matrix H I ℂ) (hF : IsIsometry F)
    {P : Polynomial ℂ} (tables : PhaseTables P) : WellFormedAdjointCircuit (word F tables) :=
  compile_wellFormed _ _ (relabel_wellFormed _ _ (idealWord_wellFormed F hF tables))

theorem frame_isometry (F : Matrix H I ℂ) (hF : IsIsometry F) : IsIsometry (frame F) := by
  have hc : IsIsometry (canonicalFrame F) :=
    cppCleanFrame_isIsometry (cppCleanFrame_isIsometry (cppCleanFrame_isIsometry (cppCleanFrame_isIsometry hF)))
  have hp : IsIsometry ((canonicalFrame F).submatrix pack.symm id) := by
    change multiply ((canonicalFrame F).submatrix pack.symm id)ᴴ
      ((canonicalFrame F).submatrix pack.symm id) = 1
    dsimp only [multiply]
    rw [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv]
    exact hc
  let K := (canonicalFrame F).submatrix pack.symm id
  let E := clean (J:=Header) (H:=H)
  change multiply (multiply E K)ᴴ (multiply E K) = 1
  calc
    _ = multiply (multiply Kᴴ (multiply Eᴴ E)) K := by
      simp only [multiply,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = multiply Kᴴ K := by
      rw [clean_isometry]
      simp only [multiply,Matrix.mul_one]
    _ = 1 := hp

end Qatlib.Concepts.NonNormalSpec.ResolventWord.Native

namespace Qatlib.Concepts.NonNormalSpec.ResolventWord.Hardware
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord Matrix
open scoped Matrix.Norms.L2Operator Kronecker
variable {J H I O : Type} [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]
  [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]

omit [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O] in

theorem parallel_dist_le (C D : Matrix H H ℂ) :
    ‖parallelOracle (J:=J) C - parallelOracle (J:=J) D‖ ≤ ‖C-D‖ := by
  have he : parallelOracle (J:=J) C - parallelOracle (J:=J) D
      = (1 : Matrix J J ℂ) ⊗ₖ (C-D) := by
    rw [parallelOracle_eq_kronecker, parallelOracle_eq_kronecker, kronecker_sub_right]
  rw [he, l2_norm_kronecker]
  exact (mul_le_mul_of_nonneg_right
    (unitary_norm_le_one (U := (1 : Matrix J J ℂ)) (unitaryGroup J ℂ).one_mem)
    (norm_nonneg (C-D))).trans_eq (one_mul _)

theorem compressed_parallel_hardware_error
    (cs : List (AdjointStep (J × H))) (Cideal C : Matrix H H ℂ) (δ : ℝ)
    (hcs : WellFormedAdjointCircuit cs)
    (hideal : Cideal ∈ unitaryGroup H ℂ) (hC : C ∈ unitaryGroup H ℂ)
    (hδ : 0 ≤ δ) (hnear : ‖C-Cideal‖ ≤ δ)
    (L : Matrix (J × H) O ℂ) (R : Matrix (J × H) I ℂ)
    (hL : IsIsometry L) (hR : IsIsometry R) :
    ‖compress L (evaluate (parallelOracle (J:=J) C) cs) R -
      compress L (evaluate (parallelOracle (J:=J) Cideal) cs) R‖
      ≤ (adjointQueryCount cs : ℝ) * δ := by
  have hnear' : ‖parallelOracle (J:=J) C - parallelOracle (J:=J) Cideal‖ ≤ δ :=
    (parallel_dist_le C Cideal).trans hnear
  exact (compress_sub_norm_le hL hR _ _).trans
    (evaluate_operator_error_le_queries cs _ _ δ hcs
      (parallelOracle_unitary hideal) (parallelOracle_unitary hC) hδ hnear')

end Qatlib.Concepts.NonNormalSpec.ResolventWord.Hardware

namespace Qatlib.Concepts.NonNormalSpec.ResolventWord.ComplexFourRouteLcu
open Native SingleControl Hardware
variable {I H : Type} [Fintype I] [DecidableEq I] [Fintype H] [DecidableEq H]

theorem frontier1 (A : Matrix I I ℂ) (hA : A.IsHermitian)
    (U : Matrix H H ℂ) (F : Matrix H I ℂ) (h : ProjectedUnitaryEncoding A U F F)
    (P : Polynomial ℂ) (tables : PhaseTables P)
    (C : Matrix (Bool × H) (Bool × H) ℂ) (hC : C ∈ unitaryGroup (Bool × H) ℂ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hnear : ‖C-controlOracle U‖ ≤ δ) :
    let cs := word F tables
    let W := evaluate (parallelOracle (J:=Header) C) cs
    W ∈ unitaryGroup (Work Header H) ℂ ∧
    IsIsometry (frame F) ∧
    ‖compress (frame F) W (frame F) - aeval A P‖ ≤
      ((∑ b : Bool, ∑ c : Bool, (tables.phases b c).length : ℕ) : ℝ) * δ ∧
    adjointQueryCount cs = ∑ b : Bool, ∑ c : Bool, (tables.phases b c).length ∧
    adjointGateCount cs = 5 * (∑ b : Bool, ∑ c : Bool, (tables.phases b c).length) + 13 ∧
    Fintype.card (Work Header H) = 2^5 * Fintype.card H := by
  (try dsimp only)
  have hw := word_wellFormed F h.right_isometry tables
  have hf := frame_isometry F h.right_isometry
  have he := compressed_parallel_hardware_error (word F tables) (controlOracle U) C δ hw
    (controlOracle_unitary h.unitary) hC hδ hnear (frame F) (frame F) hf hf
  rw [word_block A hA U F h P tables,(word_counts F tables).1] at he
  exact ⟨hw.evaluate_unitary (parallelOracle_unitary hC),hf,he,
    (word_counts F tables).1,(word_counts F tables).2,five_flags⟩

omit [DecidableEq I] in

theorem paid_word_cost (F : Matrix H I ℂ) {P : Polynomial ℂ} (tables : PhaseTables P)
    (C : Matrix (Bool × H) (Bool × H) ℂ)
    (body : GateCompilation (parallelOracle (J:=Header) C))
    (compiler : GateCompiler (Work Header H)) :
    GateCount (paidAdjointCircuit body compiler (word F tables)) =
      paidAdjointFixedGateCost compiler (word F tables) +
        (∑ b : Bool, ∑ c : Bool, (tables.phases b c).length) * GateCount body.circuit := by
  rw [paid_adjoint_compiler_gate_count,(word_counts F tables).1]

omit [DecidableEq I] in

theorem paid_word_reverse_cost (F : Matrix H I ℂ) {P : Polynomial ℂ} (tables : PhaseTables P)
    (C : Matrix (Bool × H) (Bool × H) ℂ)
    (body : GateCompilation (parallelOracle (J:=Header) C))
    (compiler : GateCompiler (Work Header H)) :
    GateCount (ReverseCircuit (paidAdjointCircuit body compiler (word F tables))) =
      paidAdjointFixedGateCost compiler (word F tables) +
        (∑ b : Bool, ∑ c : Bool, (tables.phases b c).length) * GateCount body.circuit := by
  rw [gateCount_reverseCircuit,paid_word_cost]

end Qatlib.Concepts.NonNormalSpec.ResolventWord.ComplexFourRouteLcu

namespace Qatlib.Concepts.NonNormalSpec.ResolventWord.ComplexFourRouteLcu
open Native SingleControl Hardware
variable {I H : Type} [Fintype I] [DecidableEq I] [Fintype H] [DecidableEq H]

theorem numerical_word_error (A : Matrix I I ℂ) (hA : A.IsHermitian)
    (U : Matrix H H ℂ) (F : Matrix H I ℂ) (h : ProjectedUnitaryEncoding A U F F)
    (P : Polynomial ℂ) (tables : PhaseTables P)
    (C : Matrix (Bool × H) (Bool × H) ℂ) (hC : C ∈ unitaryGroup (Bool × H) ℂ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hnear : ‖C-controlOracle U‖ ≤ δ)
    (f : Matrix (Work Header H) (Work Header H) ℂ → Matrix (Work Header H) (Work Header H) ℂ)
    (η : ℝ) (hf : KnownGateApproximation (word F tables) f η) :
    ‖compress (frame F)
        (evaluate (parallelOracle (J:=Header) C) (replaceKnownGates f (word F tables))) (frame F) -
      aeval A P‖ ≤
      ((∑ b : Bool, ∑ c : Bool, (tables.phases b c).length : ℕ) : ℝ) * δ +
      ((5 * (∑ b : Bool, ∑ c : Bool, (tables.phases b c).length) + 13 : ℕ) : ℝ) * η := by
  have hw := word_wellFormed F h.right_isometry tables
  have hF := frame_isometry F h.right_isometry
  have hg := (compress_sub_norm_le hF hF _ _).trans
    (evaluate_known_gate_error _ f η (parallelOracle (J:=Header) C) hw (parallelOracle_unitary hC) hf)
  have hb := (frontier1 A hA U F h P tables C hC δ hδ hnear).2.2.1
  have ht := (norm_sub_le_norm_sub_add_norm_sub
    (compress (frame F) (evaluate (parallelOracle (J:=Header) C) (replaceKnownGates f (word F tables))) (frame F))
    (compress (frame F) (evaluate (parallelOracle (J:=Header) C) (word F tables)) (frame F))
    (aeval A P)).trans (add_le_add hg hb)
  rw [(word_counts F tables).2] at ht
  exact ht.trans_eq (_root_.add_comm _ _)

end Qatlib.Concepts.NonNormalSpec.ResolventWord.ComplexFourRouteLcu

namespace Qatlib.Concepts.NonNormalSpec.ResolventWord.ComplexFourRouteLcu
open Native SingleControl Hardware
variable {I H : Type} [Fintype I] [DecidableEq I] [Fintype H] [DecidableEq H]

theorem numerical_block_encoding (A : Matrix I I ℂ) (hA : A.IsHermitian)
    (U : Matrix H H ℂ) (F : Matrix H I ℂ) (h : ProjectedUnitaryEncoding A U F F)
    (P : Polynomial ℂ) (tables : PhaseTables P)
    (C : Matrix (Bool × H) (Bool × H) ℂ) (hC : C ∈ unitaryGroup (Bool × H) ℂ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hnear : ‖C-controlOracle U‖ ≤ δ)
    (f : Matrix (Work Header H) (Work Header H) ℂ → Matrix (Work Header H) (Work Header H) ℂ)
    (η : ℝ) (hη : 0 ≤ η) (hf : KnownGateApproximation (word F tables) f η) :
    BlockEncoding (aeval A P)
      (evaluate (parallelOracle (J:=Header) C) (replaceKnownGates f (word F tables)))
      (frame F) (frame F) 1
      (((∑ b : Bool, ∑ c : Bool, (tables.phases b c).length : ℕ) : ℝ) * δ +
        ((5 * (∑ b : Bool, ∑ c : Bool, (tables.phases b c).length) + 13 : ℕ) : ℝ) * η) := by
  have hF := frame_isometry F h.right_isometry
  refine ⟨(replaceKnownGates_wellFormed _ f η hf).evaluate_unitary (parallelOracle_unitary hC),
    hF,hF,by norm_num,by positivity,?_⟩
  rw [one_smul,norm_sub_rev]
  exact numerical_word_error A hA U F h P tables C hC δ hδ hnear f η hf

omit [DecidableEq I] in

theorem paid_word_semantics (F : Matrix H I ℂ) {P : Polynomial ℂ} (tables : PhaseTables P)
    (C : Matrix (Bool × H) (Bool × H) ℂ) (hC : C ∈ unitaryGroup (Bool × H) ℂ)
    (body : GateCompilation (parallelOracle (J:=Header) C))
    (hbody : IsUnitaryCircuit body.circuit) (compiler : GateCompiler (Work Header H))
    (ψ : QState (Work Header H)) :
    Run 1 (paidAdjointCircuit body compiler (word F tables)) ψ =
      ApplyGate (evaluate (parallelOracle (J:=Header) C) (word F tables)) ψ :=
  paid_adjoint_compiler_semantics body compiler (parallelOracle_unitary hC) hbody _ ψ

end Qatlib.Concepts.NonNormalSpec.ResolventWord.ComplexFourRouteLcu
